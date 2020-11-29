---- MODULE backpressure ----

EXTENDS FiniteSets, Integers, Sequences, TLC

Null == 0
Cowns == 1..3 \*# TODO: 4
MaxMessageCount == 3 \*# TODO: 4
MaxMessageSize == 3
OverloadThreshold == 2
PriorityLevels == {2, 1, 0}

Pick(s) == CHOOSE x \in s: TRUE
Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Max(s) == CHOOSE x \in s: \A y \in s \ {x}: y < x
Range(f) == {f[x]: x \in DOMAIN f}
Subsets(s, min, max) ==
  {x \in SUBSET s: (Cardinality(x) >= min) /\ (Cardinality(x) <= max)}
RECURSIVE Concat(_)
Concat(s) == IF s = {} THEN <<>> ELSE LET x == Pick(s) IN x \o Concat(s \ {x})

VARIABLES fuel, queue, scheduled, running, mutor, blocker
vars == <<fuel, queue, scheduled, running, mutor, blocker>>

Messages == UNION {Range(queue[c]): c \in Cowns}
EmptyQueue(c) == Len(queue[c]) = 0
Overloaded(c) == Len(queue[c]) >= OverloadThreshold
Enqueue(c, m) == c :> Append(queue[c], m)
Dequeue(c) == c :> Tail(queue[c])

Init ==
  /\ fuel = MaxMessageCount
  /\ queue = [c \in Cowns |-> <<{c}>>]
  /\ scheduled = [c \in Cowns |-> TRUE]
  /\ running = [c \in Cowns |-> FALSE]
  /\ mutor = [c \in Cowns |-> Null]
  /\ blocker = [c \in Cowns |-> Null]

Terminating ==
  /\ \A c \in Cowns: EmptyQueue(c)
  \* -----
  /\ UNCHANGED vars

ExternalReceive(cown) ==
  /\ fuel > 0
  \* -----
  /\ UNCHANGED <<scheduled, running, mutor, blocker>>
  /\ fuel' = fuel - 1
  \*# Receive a message from an external source
  /\ \E others \in Subsets({c \in Cowns: c > cown}, 0, MaxMessageSize - 1):
    queue' = Enqueue(cown, {cown} \union others) @@ queue

Acquire(cown) ==
  /\ scheduled[cown]
  /\ ~running[cown]
  /\ ~EmptyQueue(cown)
  /\ cown \in Head(queue[cown])
  /\ cown < Max(Head(queue[cown]))
  \* -----
  /\ UNCHANGED <<fuel, running, mutor, blocker>>
  \*# Unschedule and forward the message to the next cown.
  /\ LET
      msg == Head(queue[cown])
      next == Min({c \in msg: c > cown})
    IN
      /\ scheduled' = (cown :> FALSE) @@ scheduled
      /\ queue' = Enqueue(next, msg) @@ Dequeue(cown) @@ queue

Unmute(cown) ==
  /\ scheduled[cown]
  /\ ~running[cown]
  /\ ~EmptyQueue(cown)
  /\ cown \notin Head(queue[cown])
  \* -----
  /\ UNCHANGED <<fuel, running, mutor, blocker>>
  \*# Remove message from queue.
  /\ queue' = Dequeue(cown) @@ queue
  \*# Reschedule muted cowns.
  /\ scheduled' = [c \in Head(queue[cown]) |-> TRUE] @@ scheduled

PreRun(cown) ==
  /\ scheduled[cown]
  /\ ~running[cown]
  /\ ~EmptyQueue(cown)
  /\ cown = Max(Head(queue[cown]))
  \* -----
  /\ UNCHANGED <<fuel, queue, scheduled, mutor, blocker>>
  \*# Set max cown in current message to running
  /\ running' = (cown :> TRUE) @@ running

Send(cown) ==
  /\ running[cown]
  /\ fuel > 0
  \* -----
  /\ UNCHANGED <<scheduled, running, blocker>>
  /\ fuel' = fuel - 1
  \*# Select set of receivers
  /\ \E receivers \in Subsets(Cowns, 1, MaxMessageSize):
    LET
      next == Min(receivers)
      senders == Head(queue[cown])
      mutors == {c \in receivers: Overloaded(c)}
    IN
    \*# Place message for receivers in the first receiver's queue.
    /\ queue' = Enqueue(next, receivers) @@ queue
    \*# Set mutor if any receiver is overloaded and there are no receivers in the set of senders.
    /\ IF
      /\ mutors /= {}
      /\ mutor[cown] = Null
      /\ (senders \intersect receivers) = {}
      THEN mutor' = (cown :> Min(mutors)) @@ mutor
      ELSE UNCHANGED <<mutor>>

PostRun(cown) ==
  /\ running[cown]
  \* -----
  /\ UNCHANGED <<fuel, blocker>>
  /\ running' = (cown :> FALSE) @@ running
  /\ mutor' = (cown :> Null) @@ mutor
  /\ LET msg == Head(queue[cown]) IN
    \*# Mute if mutor is set.
    IF (mutor[cown] /= Null) /\ (\A c \in msg: ~Overloaded(c)) THEN
      /\ scheduled' = [c \in msg |-> FALSE] @@ scheduled
      \*# Send unmute message to mutor
      /\ queue' = Enqueue(mutor[cown], msg) @@ Dequeue(cown) @@ queue
    ELSE
      /\ scheduled' = [c \in msg |-> TRUE] @@ scheduled
      /\ queue' = Dequeue(cown) @@ queue

RunStep(cown) ==
  \* \/ ExternalReceive(cown) \*# Very expensive check
  \/ Acquire(cown)
  \/ Unmute(cown)
  \/ PreRun(cown)
  \/ Send(cown)
  \/ PostRun(cown)

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

\*# Cowns are acquired by one running message at a time.
UniqueAcquisition ==
  LET msgs == Concat({<<Head(queue[c])>>: c \in {k \in Cowns: running[k]}})
  IN Cardinality(Range(msgs)) = Len(msgs)

\*# Each queue has at most one token message.
LoneToken == \A c \in Cowns: Len(SelectSeq(queue[c], LAMBDA m: m = {})) <= 1

\*# A running cown must be scheduled and be the max cown in the message at the head of its queue.
RunningImplication == \A c \in Cowns: running[c] =>
    /\ scheduled[c]
    /\ c = Max(Head(queue[c]))
    /\ \A k \in Head(queue[c]): (k < c) => ~scheduled[k]

\* https://github.com/tlaplus/Examples/blob/master/specifications/TransitiveClosure/TransitiveClosure.tla#L114
TC(R) ==
  LET
    S == {r[1]: r \in R} \cup {r[2]: r \in R}
    RECURSIVE TCR(_)
    TCR(T) ==
      IF T = {} THEN R
      ELSE
        LET
          r == CHOOSE s \in T: TRUE
          RR == TCR(T \ {r})
        IN
          RR \cup {<<s, t>> \in S \X S: <<s, r>> \in RR /\ <<r, t>> \in RR}
  IN
    TCR(S)

CylcicTransitiveClosure(R(_, _)) ==
  LET s == {<<a, b>> \in Cowns \X Cowns: R(a, b)}
  IN \E c \in Cowns: <<c, c>> \in TC(s)

AcquiredBy(a, b) ==
  /\ a < b
  /\ \E c \in Cowns: a \in UNION Range(queue[b])
  /\ b = Min({c \in Cowns: a \in UNION Range(queue[b])})
Acquired(c) == \E k \in Cowns: AcquiredBy(c, k)

MutedBy(a, b) ==
  /\ ~scheduled[a]
  /\ \E m \in Range(queue[b]): (b \notin m) /\ (a \in m)
Muted(c) == \E k \in Cowns: MutedBy(c, k)

\*# A muted cown exists in an unmute message in the queue of exatly one mutor.
MutedOnce ==
  \A m \in {c \in Cowns: Muted(c)}:
    Cardinality({c \in Cowns: MutedBy(m, c)}) = 1

\*# A cown may only be acqiured by one message.
AcquiredOnce ==
  \A a \in {c \in Cowns: Acquired(c)}:
    Cardinality({c \in Cowns: AcquiredBy(a, c)}) = 1

\*# An overloaded cown doesn't exist in a muted cown's queue.
OverloadedNotInMutedQueue == \A <<o, m>> \in Cowns \X Cowns:
  Overloaded(o) /\ Muted(m) => o \notin UNION Range(queue[m])

====
