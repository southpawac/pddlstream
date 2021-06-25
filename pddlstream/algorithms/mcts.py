from collections import Counter

import time

from pddlstream.algorithms.algorithm import parse_problem
from pddlstream.algorithms.common import add_facts, add_certified, SolutionStore, UNKNOWN_EVALUATION
from pddlstream.algorithms.constraints import PlanConstraints
from pddlstream.algorithms.downward import get_problem, task_from_domain_problem
from pddlstream.algorithms.instantiate_task import sas_from_pddl, instantiate_task
from pddlstream.algorithms.instantiation import Instantiator
from pddlstream.algorithms.search import abstrips_solve_from_task
from pddlstream.language.constants import is_plan
from pddlstream.language.conversion import obj_from_pddl_plan
from pddlstream.language.attachments import has_attachments, compile_fluents_as_attachments, solve_pyplanners
from pddlstream.language.statistics import load_stream_statistics, write_stream_statistics
from pddlstream.language.temporal import solve_tfd, SimplifiedDomain
from pddlstream.language.write_pddl import get_problem_pddl
from pddlstream.utils import INF, Verbose, str_from_object, elapsed_time
from GeneralizedTAMP.genqnp.tamp_feature_pool import encode_state_kb, populate_state_prolog, \
    create_kb, get_object_list, get_query, findall_query_raw, get_all_concept_args, infer_object_type
from GeneralizedTAMP.genqnp.database import Transition, TState
from GeneralizedTAMP.genqnp.utils import objectify_expression
from pddl import Atom, NegatedAtom, Conjunction, UniversalCondition, \
    ExistentialCondition, TypedObject
from collections import defaultdict
from GeneralizedTAMP.genqnp.language.planner import apply_action, t_get_action_instance
import itertools
import copy

UPDATE_STATISTICS = False

def solve_temporal(evaluations, goal_exp, domain, debug=False, **kwargs):
    assert isinstance(domain, SimplifiedDomain)
    problem = get_problem_pddl(evaluations, goal_exp, domain.pddl)
    return solve_tfd(domain.pddl, problem, debug=debug)

def solve_sequential(evaluations, goal_exp, domain, unit_costs=False, debug=False, **search_args):
    problem = get_problem(evaluations, goal_exp, domain, unit_costs)
    task = task_from_domain_problem(domain, problem)
    if has_attachments(domain):
        with Verbose(debug):
            instantiated = instantiate_task(task)
        return solve_pyplanners(instantiated, **search_args)
    sas_task = sas_from_pddl(task, debug=debug)
    return abstrips_solve_from_task(sas_task, debug=debug, **search_args)

def solve_finite(evaluations, goal_exp, domain, **kwargs):
    if isinstance(domain, SimplifiedDomain):
        pddl_plan, cost = solve_temporal(evaluations, goal_exp, domain, **kwargs)
    else:
        pddl_plan, cost = solve_sequential(evaluations, goal_exp, domain, **kwargs)
    plan = obj_from_pddl_plan(pddl_plan)
    return plan, cost

##################################################

def process_instance(instantiator, store, instance, verbose=False): #, **complexity_args):
    if instance.enumerated:
        return []
    start_time = time.time()
    new_results, new_facts = instance.next_results(verbose=verbose)
    store.sample_time += elapsed_time(start_time)

    evaluations = store.evaluations
    #remove_blocked(evaluations, instance, new_results)
    for result in new_results:
        complexity = result.compute_complexity(evaluations)
        #complexity = instantiator.compute_complexity(instance)
        for evaluation in add_certified(evaluations, result):
            instantiator.add_atom(evaluation, complexity)
    fact_complexity = 0 # TODO: record the instance or treat as initial?
    for evaluation in add_facts(evaluations, new_facts, result=UNKNOWN_EVALUATION, complexity=fact_complexity):
        instantiator.add_atom(evaluation, fact_complexity)
    if not instance.enumerated:
        instantiator.push_instance(instance)
    return new_results

def process_stream_queue(instantiator, store, complexity_limit=INF, verbose=False):
    instances = []
    results = []
    num_successes = 0
    while not store.is_terminated() and instantiator and (instantiator.min_complexity() <= complexity_limit):
        instance = instantiator.pop_stream()
        if instance.enumerated:
            continue
        instances.append(instance)
        new_results = process_instance(instantiator, store, instance, verbose=verbose)
        results.extend(new_results)
        num_successes += bool(new_results) # TODO: max_results?
    if verbose:
        print('Eager Calls: {} | Successes: {} | Results: {} | Counts: {}'.format(
            len(instances), num_successes, len(results),
            str_from_object(Counter(instance.external.name for instance in instances))))
    return len(instances)

##################################################


def row_join(row1, row2):

    # Join the two rows, returns none if they cannot be joined
    new_row = {}
    for row in [row1, row2]:
        for k, v in row.items():
            if (k in new_row.keys() and new_row[k] != v):
                return None
            else:
                new_row[k] = v
    return new_row


def join(current_db, joining_db, negated=True):
    new_db = []
    # Todo: can be more efficient
    if (current_db is None):
        return joining_db
    elif (joining_db is None):
        return current_db
    else:
        for row1, row2 in itertools.product(current_db, joining_db):
            joined_row = row_join(row1, row2)
            if (joined_row != None):
                new_db.append(joined_row)
    return new_db


def get_successor_gen(ground_atoms, parameters, preconditions, current_db=None):
    

    ground_atoms_dict = defaultdict(list)
    ground_negated_atoms_dict = defaultdict(list)
    for ground_atom in ground_atoms:
        if (isinstance(ground_atom, Atom)):
            ground_atoms_dict[ground_atom.predicate].append(ground_atom.args)
        elif (isinstance(ground_atom, NegatedAtom)):
            ground_negated_atoms_dict[ground_atom.predicate].append(ground_atom.args)
        else:
            raise NotImplementedError

    preconditions.parts = sorted(list(preconditions.parts), key=lambda x: len(x.args), reverse=False)
    variable_map = defaultdict(list)

    for precondition_part in list(preconditions.parts):
        # For this precondition part, find every object combination which exists in the ground atoms
        if (isinstance(precondition_part, Atom)):
            pre_part_db = [{precondition_part.args[i]: args[i] for i in range(len(args))} for args in
                           ground_atoms_dict[precondition_part.predicate]]
        elif (isinstance(precondition_part, NegatedAtom)):
            pre_part_db = [{precondition_part.args[i]: args[i] for i in range(len(args))} for args in
                           ground_negated_atoms_dict[precondition_part.predicate]]
        else:
            raise NotImplementedError


        current_db = join(current_db, pre_part_db)

    def successor_gen():
        for row in current_db:
            yield row

    return successor_gen


def remove_new_axiom(cond):
    if(isinstance(cond, Conjunction)):
        new_parts = []
        for cond_part in cond.parts:
            if(not cond_part.predicate.startswith("new-axiom")):
                new_parts.append(cond_part)
        return Conjunction(new_parts)
    else:
        raise NotImplementedError

class MCTSNode():
    def __init__(self, state, action_name, action_args, next_state):
        self.state = state
        self.action_name = action_name
        self.action_args = action_args
        self.next_state = next_state


def evaluate_axioms(atoms, domain, task_domain_predicates, state_index):
    atoms = sorted(atoms, key=lambda x: x.predicate)
    kb_lines = encode_state_kb(atoms, state_index)
    kb_lines = populate_state_prolog(domain, state_index) + kb_lines
    kb = create_kb(kb_lines)

    value_map = None
    tstate = TState(atoms, value_map)
    object_set = get_object_list([tstate], task_domain_predicates)
    typed_object_set = [TypedObject(obj.name, infer_object_type(domain, obj, [atoms])) for obj in list(set(object_set))]
    transition = Transition(None, atoms, value_map, typed_object_set, domain, index=state_index) # TODO atoms is the state  

    for axiom in domain.axioms:
        c = objectify_expression(axiom.condition)
        results, valmap = findall_query_raw(axiom.parameters, transition, c, kb)
        for result in results:
            atoms.append(Atom(axiom.name, [valmap[obj] for obj in result]))
    return atoms

def check_goal(atoms, goal_atoms):
    # First convert to hashable format
    atom_tuples = [tuple([at.predicate]+[str(a.name) for a in at.args]) for at in atoms]
    goal_tuples = [tuple([at.predicate]+[str(a.name) for a in at.args]) for at in goal_atoms]
    non_goals = len([gt for gt in goal_tuples if gt not in atom_tuples])
    return non_goals


def solve_mcts(problem, constraints=PlanConstraints(),
                      unit_costs=False, success_cost=INF,
                      parsed_domain=None,
                      max_iterations=INF, max_time=INF, max_memory=INF,
                      initial_complexity=0, complexity_step=1, max_complexity=INF,
                      verbose=False, **search_kwargs):
    """
    Solves a PDDLStream problem by alternating between applying all possible streams and searching
    :param problem: a PDDLStream problem
    :param constraints: PlanConstraints on the set of legal solutions

    :param unit_costs: use unit action costs rather than numeric costs
    :param success_cost: the exclusive (strict) upper bound on plan cost to successfully terminate

    :param max_time: the maximum runtime
    :param max_iterations: the maximum number of search iterations
    :param max_memory: the maximum amount of memory

    :param initial_complexity: the initial stream complexity limit
    :param complexity_step: the increase in the stream complexity limit per iteration
    :param max_complexity: the maximum stream complexity limit

    :param verbose: if True, print the result of each stream application
    :param search_kwargs: keyword args for the search subroutine

    :return: a tuple (plan, cost, evaluations) where plan is a sequence of actions
        (or None), cost is the cost of the plan (INF if no plan), and evaluations is init expanded
        using stream applications
    """
    # max_complexity = 0 => current
    # complexity_step = INF => exhaustive
    # success_cost = terminate_cost = decision_cost
    # TODO: warning if optimizers are present


    evaluations, goal_expression, domain, externals = parse_problem(
        problem, constraints=constraints, unit_costs=unit_costs)

    problem = get_problem(evaluations, goal_expression, domain, unit_costs)

    store = SolutionStore(evaluations, max_time, success_cost, verbose, max_memory=max_memory) # TODO: include other info here?

    static_externals = compile_fluents_as_attachments(domain, externals)
    instantiator = Instantiator(static_externals, evaluations) 

    complexity = 4
    process_stream_queue(instantiator, store, complexity, verbose=verbose)


    # Create the state in prolog
    atoms = []
    for evaluation in evaluations:
        if(evaluation.head.function.islower() and "-" not in evaluation.head.function):
            atoms.append(Atom(evaluation.head.function, [TypedObject(a, "object") for a in evaluation.head.args]))

    # goal expresion to formula
    goal_atoms = []
    assert goal_expression[0] == "and"
    for goal_tuple in goal_expression[1:]:
        if(goal_tuple[0].islower() and "-" not in goal_tuple[0]):
            goal_atoms.append(Atom(goal_tuple[0], [TypedObject(a, "object") for a in goal_tuple[1:]]))
    
    edges = defaultdict(list) # state: takable actions

    atoms = sorted(atoms, key = lambda x: x.predicate) 

    state_index = 0
    
    # Evaluate the preconditions of each action for this state in prolog
    task_domain_predicates = [p.name for p in parsed_domain.predicates]

    task = task_from_domain_problem(domain, problem)
    axiom_atoms = evaluate_axioms(atoms, parsed_domain, task_domain_predicates, 0)
    non_goal = check_goal(atoms, goal_atoms)
    if(non_goal == 0):
        return [], None

    parent = defaultdict(lambda: None)
    Q = [MCTSNode(None, None, None, atoms)]
    print("Bfs start")
    state_index = 1
    evaluated = []
    it = 0 
    while(len(Q)>0):
        print("Iteration {}".format(it))
        q = Q.pop(0)
        # Evaluate the preconditions of each action for this state in prolog
        for action in parsed_domain.actions:
            c = objectify_expression(action.precondition)
            c = remove_new_axiom(c)
            atoms = copy.copy(q.next_state)
            successors = get_successor_gen(q.next_state, action.parameters, c)()
            for successor_action in successors:
                # Take an action
                st = time.time()
                successor_action_simp = {k.name: v for k, v in successor_action.items()}
                val_map = {str(v.name): v for v in successor_action.values()}
                instance = t_get_action_instance(task, action.name, [successor_action_simp[param.name].name for param in action.parameters])
                new_atoms = apply_action(atoms, instance, val_map=val_map)
                print(st-time.time())
                print("Add: {}".format(new_atoms-set(atoms)))
                print("Del: {}".format(set(atoms)-new_atoms))
                objectified_atoms = [Atom(a.predicate, [TypedObject(str(arg.name), "object") for arg in a.args]) for a in new_atoms]

                if(frozenset(objectified_atoms) not in evaluated):
                    evaluated.append(frozenset(objectified_atoms))
                    axiom_objectified_atoms = evaluate_axioms(objectified_atoms, parsed_domain, task_domain_predicates, state_index)

                    goal_atoms_rem = check_goal(axiom_objectified_atoms, goal_atoms)
                    new_node = MCTSNode(atoms, action.name, [successor_action_simp[param.name].name.value for param in action.parameters], new_atoms)
                    edges[q].append((successor_action, new_node))
                    state_index+=1
                    Q.append(new_node)
                    parent[new_node] = q
                    print("Goals left: "+str(goal_atoms_rem))
                    if(goal_atoms_rem == 0):
                        # GOAL                 
                        plan  = [new_node]
                        parent_node = parent[new_node]
                        while(parent_node != None):
                            plan.append(parent_node)
                            parent_node = parent[parent_node]

                        plan_nodes = [(plan_node.action_name, plan_node.action_args) for plan_node in list(reversed(plan))]
                        return (plan_nodes[1:], 0, evaluations), None


        # if(it == 5):
        #     import sys
        #     sys.exit(1)
        it+=1

    assert False, "No plan found"



