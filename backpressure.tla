---- MODULE backpressure ----

EXTENDS FiniteSets, Integers, Sequences, TLC

Null == 0
Cowns == 1..3
BehaviourLimit == 3
OverloadThreshold == 2
PriorityLevels == {2, 1, 0}

Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Max(s) == CHOOSE x \in s: \A y \in s \ {x}: y < x
Range(f) == {f[x]: x \in DOMAIN f}

VARIABLES fuel, queue, scheduled, running, priority, blocker, mutor
vars == <<fuel, queue, scheduled, running, priority, blocker, mutor>>

Messages == UNION {Range(queue[c]): c \in Cowns}
EmptyQueue(c) == Len(queue[c]) = 0

Init ==
  /\ fuel = BehaviourLimit
  /\ queue = [c \in Cowns |-> <<{c}>>]
  /\ scheduled = [c \in Cowns |-> TRUE]
  /\ running = [c \in Cowns |-> FALSE]
  /\ priority = [c \in Cowns |-> 0]
  /\ blocker = [c \in Cowns |-> Null]
  /\ mutor = [c \in Cowns |-> Null]

Terminating ==
  /\ \A c \in Cowns: EmptyQueue(c)
  /\ UNCHANGED vars

Acquire(cown) ==
  \*# Preconditions
  /\ scheduled[cown]
  /\ ~running[cown]
  /\ ~EmptyQueue(cown)
  /\ cown < Max(Head(queue[cown]))
  \*# Forward the message to the next cown.
  /\ LET
      msg == Head(queue[cown])
      next == Min({c \in msg: c > cown})
    IN
      queue' =
        (next :> Append(queue[next], msg)) @@
        (cown :> Tail(queue[cown])) @@
        queue

  /\ UNCHANGED <<fuel, scheduled, running, priority, blocker, mutor>>

PreRun(c) ==
  \*# Preconditions
  /\ scheduled[c]
  /\ ~running[c]
  /\ ~EmptyQueue(c)
  /\ c = Max(Head(queue[c]))
  \*# Set max cown in current message to running
  /\ running' = (c :> TRUE) @@ running
  /\ UNCHANGED <<fuel, queue, scheduled, priority, blocker, mutor>>

Send(c) ==
  \*# Preconditions
  /\ running[c]
  /\ fuel > 0
  \*# Select set of receivers
  /\ \E receivers \in {cs \in SUBSET Cowns: Cardinality(cs) > 1}:
    \*# place message for receivers in the first receiver's queue
    LET next == Min(receivers) IN
    queue' = (next :> Append(queue[next], receivers)) @@ queue

  /\ fuel' = fuel - 1
  /\ UNCHANGED <<scheduled, running, priority, blocker, mutor>>

PostRun(c) ==
  \*# Preconditions
  /\ running[c]
  \*# Transition
  /\ running' = (c :> FALSE) @@ running
  \*# Remove message from queue
  /\ queue' = (c :> Tail(queue[c])) @@ queue
  /\ UNCHANGED <<fuel, scheduled, priority, blocker, mutor>>

RunStep(c) ==
  \/ Acquire(c)
  \/ PreRun(c)
  \/ Send(c)
  \/ PostRun(c)

Next == \E c \in Cowns: RunStep(c)

Spec ==
  /\ Init
  /\ [][Next \/ Terminating]_vars
  /\ \A c \in Cowns: WF_vars(RunStep(c))

\*# Properties

\*# Ensure that the termination condition is reached by the model.
Termination == <>[](\A c \in Cowns: EmptyQueue(c))

\*# Invariants

\*# Ensure that the model produces finite messages.
MessageLimit == Cardinality(Messages) <= (Cardinality(Cowns) + BehaviourLimit)

\*# A message must contain at least one cown.
MessagesAreNonEmpty == \A m \in Messages: m /= {}

\*# A running cown must be scheduled and be the max cown in the message at the head of its queue.
RunningImplication ==
  \A c \in Cowns: running[c] => scheduled[c] /\ (c = Max(Head(queue[c])))

====
