(define (domain pick-and-place)
  (:requirements :strips :equality)
  (:predicates
    (Stackable ?o ?s)
    (Sink ?r)
    (Stove ?r)

    (Robot ?r)
    (Grasp ?o ?g)
    (Kin ?r ?o ?p ?g ?q ?t)
    (Motion ?r ?q1 ?q2 ?t)
    (Pull ?r ?rq1 ?rq2 ?d ?dq1 ?dq2 ?t)
    (Supported ?o ?p ?s)
    (TrajCollision ?t ?o2 ?p2)

    (AtPose ?o ?p)
    (AtGrasp ?r ?o ?g)
    (HandEmpty ?r)
    (AtConf ?r ?q)
    (CanMove ?r)
    (Cleaned ?o)
    (Cooked ?o)

    (On ?o ?s)
    (Holding ?o)
    (UnsafeTraj ?t)
  )

  (:action move
    :parameters (?r ?q1 ?q2 ?t)
    :precondition (and (Motion ?r ?q1 ?q2 ?t)
                       (AtConf ?r ?q1) (CanMove ?r)) ; (not (UnsafeTraj ?t)))
    :effect (and (AtConf ?r ?q2)
                 (not (AtConf ?r ?q1)) (not (CanMove ?r)))
  )

  (:action pick
    :parameters (?r ?o ?p ?g ?q ?t)
    :precondition (and (Kin ?r ?o ?p ?g ?q ?t)
                       (AtPose ?o ?p) (HandEmpty ?r) (AtConf ?r ?q) (not (UnsafeTraj ?t)))
    :effect (and (AtGrasp ?r ?o ?g) (CanMove ?r)
                 (not (AtPose ?o ?p)) (not (HandEmpty ?r)))
  )
  (:action place
    :parameters (?r ?o ?p ?g ?q ?t)
    :precondition (and (Kin ?r ?o ?p ?g ?q ?t)
                       (AtGrasp ?r ?o ?g) (AtConf ?r ?q) (not (UnsafeTraj ?t)))
    :effect (and (AtPose ?o ?p) (HandEmpty ?r) (CanMove ?r)
                 (not (AtGrasp ?r ?o ?g)))
  )
  (:action pull
    :parameters (?r ?rq1 ?rq2 ?d ?dq1 ?dq2 ?t)
    :precondition (and (Pull ?r ?rq1 ?rq2 ?d ?dq1 ?dq2 ?t)
                       (HandEmpty ?r) (AtConf ?r ?rq1) (AtConf ?d ?dq1) (not (UnsafeTraj ?t)))
    :effect (and (AtConf ?r ?rq2) (AtConf ?d ?dq2) (CanMove ?r)
                 (not (AtConf ?r ?rq1)) (not (AtConf ?d ?dq2)))
  )

  (:action clean
    :parameters (?o ?s)
    :precondition (and (Stackable ?o ?s) (Sink ?s)
                       (On ?o ?s))
    :effect (Cleaned ?o)
  )
  (:action cook
    :parameters (?o ?s)
    :precondition (and (Stackable ?o ?s) (Stove ?s)
                       (On ?o ?s) (Cleaned ?o))
    :effect (and (Cooked ?o)
                 (not (Cleaned ?o)))
  )

  (:derived (On ?o ?s)
    (exists (?p) (and (Supported ?o ?p ?s)
                      (AtPose ?o ?p)))
  )
  (:derived (Holding ?r ?o)
    (exists (?g) (and (Robot ?r) (Grasp ?o ?g)
                      (AtGrasp ?r ?o ?g)))
  )
  ;(:derived (UnsafeTraj ?t)
  ;  (exists (?o2 ?p2) (and (TrajCollision ?t ?o2 ?p2)
  ;                         (AtPose ?o2 ?p2)))
  ;)
)