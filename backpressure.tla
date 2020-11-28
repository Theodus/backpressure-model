---- MODULE backpressure ----

EXTENDS FiniteSets, Integers, Sequences, TLC

Null == 0
Cowns == 1..4
MaxMessageCount == 4
MaxMessageSize == 3
OverloadThreshold == 2
PriorityLevels == {2, 1, 0}

Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Max(s) == CHOOSE x \in s: \A y \in s \ {x}: y < x
Range(f) == {f[x]: x \in DOMAIN f}
Subsets(s, min, max) ==
  {x \in SUBSET s: (Cardinality(x) >= min) /\ (Cardinality(x) <= max)}

VARIABLES fuel, queue, scheduled, running, priority, blocker, mutor
vars == <<fuel, queue, scheduled, running, priority, blocker, mutor>>

Messages == UNION {Range(queue[c]): c \in Cowns}
EmptyQueue(c) == Len(queue[c]) = 0

Init ==
  /\ fuel = MaxMessageCount
  /\ queue = [c \in Cowns |-> <<{c}>>]
  /\ scheduled = [c \in Cowns |-> TRUE]
  /\ running = [c \in Cowns |-> FALSE]
  /\ priority = [c \in Cowns |-> 0]
  /\ blocker = [c \in Cowns |-> Null]
  /\ mutor = [c \in Cowns |-> Null]

Terminating ==
  /\ \A c \in Cowns: EmptyQueue(c)
  \* -----
  /\ UNCHANGED vars

ExternalReceive(cown) ==
  /\ fuel > 0
  \* -----
  /\ UNCHANGED <<scheduled, running, priority, blocker, mutor>>
  /\ fuel' = fuel - 1
  \*# Receive a message from an external source
  /\ \E others \in Subsets({c \in Cowns: c > cown}, 0, MaxMessageSize - 1):
    LET msg == {cown} \union others IN
    queue' = (cown :> Append(queue[cown], msg)) @@ queue

Acquire(cown) ==
  /\ scheduled[cown]
  /\ ~running[cown]
  /\ ~EmptyQueue(cown)
  /\ cown < Max(Head(queue[cown]))
  \* -----
  /\ UNCHANGED <<fuel, scheduled, running, priority, blocker, mutor>>
  \*# Forward the message to the next cown.
  /\ LET
      msg == Head(queue[cown])
      next == Min({c \in msg: c > cown})
      q == (cown :> Tail(queue[cown])) @@ queue
    IN
      queue' = (next :> Append(queue[next], msg)) @@ q

PreRun(c) ==
  /\ scheduled[c]
  /\ ~running[c]
  /\ ~EmptyQueue(c)
  /\ c = Max(Head(queue[c]))
  \* -----
  /\ UNCHANGED <<fuel, queue, scheduled, priority, blocker, mutor>>
  \*# Set max cown in current message to running
  /\ running' = (c :> TRUE) @@ running

Send(c) ==
  /\ running[c]
  /\ fuel > 0
  \* -----
  /\ UNCHANGED <<scheduled, running, priority, blocker, mutor>>
  /\ fuel' = fuel - 1
  \*# Select set of receivers
  /\ \E receivers \in Subsets(Cowns, 1, MaxMessageSize):
    \*# place message for receivers in the first receiver's queue
    LET next == Min(receivers) IN
    queue' = (next :> Append(queue[next], receivers)) @@ queue

PostRun(c) ==
  /\ running[c]
  \* -----
  /\ UNCHANGED <<fuel, scheduled, priority, blocker, mutor>>
  /\ running' = (c :> FALSE) @@ running
  \*# Remove message from queue
  /\ queue' = (c :> Tail(queue[c])) @@ queue

RunStep(c) ==
  \* \/ ExternalReceive(c) \*# Very expensive check
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
MessageLimit == Cardinality(Messages) <= (Cardinality(Cowns) + MaxMessageCount)

\*# A message must contain at least one cown.
MessagesAreNonEmpty == \A m \in Messages: m /= {}

\*# A running cown must be scheduled and be the max cown in the message at the head of its queue.
RunningImplication ==
  \A c \in Cowns: running[c] => scheduled[c] /\ (c = Max(Head(queue[c])))

====
