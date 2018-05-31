#!/usr/bin/env python

from __future__ import print_function

try:
    import pybullet as p
except ImportError:
    raise ImportError('This example requires PyBullet (https://pypi.org/project/pybullet/)')

import cProfile
import pstats
import time

from pddlstream.focused import solve_focused
from pddlstream.stream import from_fn, from_gen_fn, from_list_fn
from pddlstream.utils import print_solution, read, INF, get_file_path

from examples.pybullet.utils.pr2_utils import set_arm_conf, REST_LEFT_ARM, open_arm, \
    close_arm, get_carry_conf, arm_conf, get_other_arm, visible_base_generator, PR2_GROUPS, \
    get_kinect_registrations, get_visual_detections, inverse_visibility, HEAD_LINK_NAME, get_cone_mesh, \
    MAX_VISUAL_DISTANCE, MAX_KINECT_DISTANCE, get_detection_cone
from examples.pybullet.utils.utils import set_base_values, set_pose, get_pose, get_bodies, load_model, point_from_pose, \
    pairwise_collision, joints_from_names, get_body_name, plan_joint_motion, connect, is_placement, clone_world, \
    disconnect, set_client, user_input, add_data_path, WorldSaver, link_from_name, create_mesh, get_link_pose, \
    remove_body, wait_for_duration, wait_for_interrupt, get_name
from examples.pybullet.utils.pr2_primitives import Pose, Conf, get_ik_ir_gen, get_motion_gen, get_stable_gen, \
    get_grasp_gen, step_commands, get_fixed_bodies, Attach, Detach, Trajectory, State, apply_commands, \
    Command
from examples.pybullet.utils.pr2_problems import create_kitchen, create_pr2


def get_vis_gen(problem, max_attempts=25, base_range=(0.5, 1.5)):
    robot = problem.robot
    fixed = get_fixed_bodies(problem)
    #base_joints = joints_from_names(robot, PR2_GROUPS['base'])
    head_joints = joints_from_names(robot, PR2_GROUPS['head'])

    def gen(o, p):
        # default_conf = arm_conf(a, g.carry)
        # joints = get_arm_joints(robot, a)
        # TODO: check collisions with fixed links
        target_point = point_from_pose(p.value)
        base_generator = visible_base_generator(robot, target_point, base_range)
        while True:
            for _ in range(max_attempts):
                set_pose(o, p.value)
                base_conf = next(base_generator)
                set_base_values(robot, base_conf)  # TODO: use pose or joint?
                # set_joint_positions(robot, base_joints, base_conf)
                if any(pairwise_collision(robot, b) for b in fixed):
                    continue
                head_conf = inverse_visibility(robot, target_point)
                if head_conf is None:  # TODO: test if visible
                    continue
                bp = Pose(robot, get_pose(robot))
                hq = Conf(robot, head_joints, head_conf)
                yield (bp, hq)
                break
            else:
                yield None

    return gen


#######################################################

def pddlstream_from_problem(problem, initial, teleport=False):
    robot = problem.robot
    # TODO: infer from task as well

    domain_pddl = read(get_file_path(__file__, 'domain.pddl'))
    stream_pddl = read(get_file_path(__file__, 'stream.pddl'))
    constant_map = {}

    initial_poses = {body: Pose(body, get_pose(body)) for body in get_bodies()}
    init = [
        ('BConf', initial_poses[robot]),
        ('AtBConf', initial_poses[robot]),
    ]
    # for arm in ARM_JOINT_NAMES:
    # for arm in problem.arms:
    #    joints = get_arm_joints(robot, arm)
    #    conf = Conf(robot, joints, get_joint_positions(robot, joints))
    #    init += [('Arm', arm), ('AConf', arm, conf),
    #             ('HandEmpty', arm), ('AtAConf', arm, conf)]
    #    if arm in problem.arms:
    #        init += [('Controllable', arm)]
    for body in problem.movable + problem.surfaces:
        pose = initial_poses[body]
        init += [('Pose', body, pose), ('AtPose', body, pose)]

    for body in problem.movable:
        init += [('Graspable', body)]
        for surface in problem.surfaces:
            init += [('Stackable', body, surface)]
            if is_placement(body, surface):
                init += [('Supported', body, initial_poses[body], surface)]
    for body in (problem.movable + problem.surfaces):
        if body in initial.localized:
            init.append(('Localized', body))
        else:
            init.append(('Unknown', body))

    goal = ['and'] + \
           [('Holding', a, b) for a, b in problem.goal_holding] + \
           [('On', b, s) for b, s in problem.goal_on] + \
           [('Localized', b) for b in problem.goal_localized] + \
           [('Registered', b) for b in problem.goal_registered]

    stream_map = {
        'sample-pose': get_stable_gen(problem),
        'sample-grasp': from_list_fn(get_grasp_gen(problem)),
        'inverse-kinematics': from_gen_fn(get_ik_ir_gen(problem, teleport=teleport)),
        'inverse-visibility': from_gen_fn(get_vis_gen(problem)),
        'plan-base-motion': from_fn(get_motion_gen(problem, teleport=teleport)),
    }

    return domain_pddl, constant_map, stream_pddl, stream_map, init, goal


#######################################################

class BeliefTask(object):
    def __init__(self, robot, arms=tuple(), grasp_types=tuple(),
                 class_from_body={}, movable=tuple(), surfaces=tuple(),
                 goal_localized=tuple(), goal_registered=tuple(),
                 goal_holding=tuple(), goal_on=tuple()):
        self.robot = robot
        self.arms = arms
        self.grasp_types = grasp_types
        self.class_from_body = class_from_body
        self.movable = movable
        self.surfaces = surfaces
        self.goal_holding = goal_holding
        self.goal_on = goal_on
        self.goal_localized = goal_localized
        self.goal_registered = goal_registered


class BeliefState(State):
    def __init__(self, localized=tuple(), registered=tuple(), **kwargs):
        super(BeliefState, self).__init__(**kwargs)
        self.localized = set(localized)
        self.registered = set(registered)
    def __repr__(self):
        return '{}({},{})'.format(self.__class__.__name__,
                                  list(map(get_name, self.localized)),
                                  list(map(get_name, self.registered)))

def get_localized_rooms(problem):
    raise NotImplementedError()


def get_localized_surfaces(problem):
    return BeliefState(localized=problem.surfaces)


def get_localized_movable(problem):
    return BeliefState(localized=problem.surfaces + problem.movable)


def get_problem(arm='left', grasp_type='top'):
    table, cabbage, sink, stove = create_kitchen()
    # TODO: bug if I change the order?

    pr2 = create_pr2()
    set_arm_conf(pr2, arm, get_carry_conf(arm, grasp_type))
    open_arm(pr2, arm)

    other_arm = get_other_arm(arm)
    set_arm_conf(pr2, other_arm, arm_conf(other_arm, REST_LEFT_ARM))
    close_arm(pr2, other_arm)

    class_from_body = {
        table: 'table',
        cabbage: 'cabbage',
        sink: 'sink',
        stove: 'stove',
    }

    task = BeliefTask(robot=pr2, arms=[arm], grasp_types=[grasp_type],
                         class_from_body=class_from_body, movable=[cabbage],  surfaces=[table, sink, stove],
                         goal_registered=[cabbage])

    # initial = get_localized_rooms(task)
    initial = get_localized_surfaces(task)
    # initial = get_localized_movable(task)

    return task, initial


#######################################################

# TODO: make a class for other detected things

class Detect(Command):
    def __init__(self, robot):
        self.robot = robot
        self.link = link_from_name(robot, HEAD_LINK_NAME)

    def step(self):
        # TODO: draw cone
        return get_visual_detections(self.robot)

    def apply(self, state, **kwargs):
        #state.localized.add()
        #raise NotImplementedError()
        cones = []
        head_pose = get_link_pose(self.robot, self.link)
        for detection in get_visual_detections(self.robot):
            mesh = get_cone_mesh()
            assert(mesh is not None)
            cone = create_mesh(mesh, color=(1, 0, 0, 0.5))
            set_pose(cone, head_pose)
            cones.append(cone)
        wait_for_duration(1.0)
        #time.sleep(1.0)
        for cone in cones:
            remove_body(cone)

    control = step

    def __repr__(self):
        return '{}({})'.format(self.__class__.__name__, get_body_name(self.robot))

class Register(Command):
    def __init__(self, robot, body):
        self.robot = robot
        self.body = body
        self.link = link_from_name(robot, HEAD_LINK_NAME)

    def step(self):
        # TODO: filter for target object and location?
        return get_kinect_registrations(self.robot)

    def apply(self, state, **kwargs):
        mesh, _ = get_detection_cone(self.robot, self.body, depth=MAX_KINECT_DISTANCE)
        assert(mesh is not None)
        cone = create_mesh(mesh, color=(0, 1, 0, 0.5))
        set_pose(cone, get_link_pose(self.robot, self.link))
        wait_for_duration(1.0)
        # time.sleep(1.0)
        remove_body(cone)
        state.registered.add(self.body)

    control = step

    def __repr__(self):
        return '{}({},{})'.format(self.__class__.__name__, get_body_name(self.robot),
                                  get_name(self.body))

#######################################################

def plan_head_traj(robot, head_conf):
    # head_conf = get_joint_positions(robot, head_joints)
    # head_path = [head_conf, hq.values]
    head_joints = joints_from_names(robot, PR2_GROUPS['head'])
    head_path = plan_joint_motion(robot, head_joints, head_conf,
                                  obstacles=None, self_collisions=False, direct=True)
    return Trajectory(Conf(robot, head_joints, q) for q in head_path)


def post_process(problem, plan):
    if plan is None:
        return None
    # TODO: refine
    robot = problem.robot
    commands = []
    for i, (name, args) in enumerate(plan):
        print(i, name, args)
        if name == 'move_base':
            t = args[-1]
            new_commands = [t]
        elif name == 'pick':
            a, b, p, g, _, t = args
            attach = Attach(robot, a, g, b)
            new_commands = [t, attach, t.reverse()]
        elif name == 'place':
            a, b, p, g, _, t = args
            detach = Detach(robot, a, b)
            new_commands = [t, detach, t.reverse()]
        elif name == 'scan':
            o, p, bq, hq = args
            ht = plan_head_traj(robot, hq.values)
            detect = Detect(robot)
            new_commands = [ht, detect]
        elif name == 'localize':
            new_commands = []
        elif name == 'register':
            o, p, bq, hq = args
            ht = plan_head_traj(robot, hq.values)
            register = Register(robot, o)
            new_commands = [ht, register]
        else:
            raise ValueError(name)
        # TODO: execute these here?
        commands += new_commands
    return commands


#######################################################

def plan_commands(task, initial, teleport=False):
    sim_world = connect(use_gui=False)
    clone_world(client=sim_world, exclude=[task.robot])
    set_client(sim_world)
    pr2 = load_model(pr2_urdf, fixed_base=True)
    # user_input('Plan?')
    saved_world = WorldSaver()  # StateSaver()

    pddlstream_problem = pddlstream_from_problem(task, initial, teleport=teleport)
    _, _, _, stream_map, init, goal = pddlstream_problem
    print('Init:', init)
    print('Goal:', goal)
    print('Streams:', stream_map.keys())

    pr = cProfile.Profile()
    pr.enable()
    solution = solve_focused(pddlstream_problem, max_cost=INF)
    print_solution(solution)
    plan, cost, evaluations = solution
    pr.disable()
    pstats.Stats(pr).sort_stats('tottime').print_stats(10)

    saved_world.restore()
    commands = post_process(task, plan)
    disconnect()
    return commands


#######################################################

pr2_urdf = "models/drake/pr2_description/urdf/pr2_simplified.urdf"


def main():
    # TODO: closed world and open world
    real_world = connect(use_gui=True)
    add_data_path()
    task, initial = get_problem()
    print(initial)

    commands = plan_commands(task, initial)
    if commands is None:
        print('Failed to produce a plan')
        disconnect()
        return

    set_client(real_world)
    # user_input('Execute?')
    time_step = 0.01
    #step_commands(commands, time_step=time_step)
    apply_commands(initial, commands, time_step=time_step)
    print(initial)
    wait_for_interrupt()
    disconnect()


if __name__ == '__main__':
    main()
