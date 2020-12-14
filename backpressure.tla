---- MODULE backpressure ----

EXTENDS FiniteSets, Integers, Sequences, TLC

Null == 0
Cowns == 1..2 \*# TODO: 4
MaxMessageCount == 1 \*# TODO: 4
MaxMessageSize == 3
OverloadThreshold == 2
PriorityLevels == {-1, 0, 1}

Pick(s) == CHOOSE x \in s: TRUE
Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Max(s) == CHOOSE x \in s: \A y \in s \ {x}: y < x
Range(f) == {f[x]: x \in DOMAIN f}
Subsets(s, min, max) ==
  {x \in SUBSET s: (Cardinality(x) >= min) /\ (Cardinality(x) <= max)}
RECURSIVE Concat(_)
Concat(s) == IF s = {} THEN <<>> ELSE LET x == Pick(s) IN x \o Concat(s \ {x})

VARIABLES fuel, queue, scheduled, running, mutor, priority, blocker
vars == <<fuel, queue, scheduled, running, mutor, priority, blocker>>

Messages == UNION {Range(queue[c]): c \in Cowns}
EmptyQueue(c) == Len(queue[c]) = 0
Overloaded(c) == Len(queue[c]) >= OverloadThreshold
Enqueue(c, m) == c :> Append(queue[c], m)
Dequeue(c) == c :> Tail(queue[c])

RECURSIVE Blockers(_)
Blockers(c) ==
  IF blocker[c] = Null THEN {}
  ELSE {blocker[c]} \union Blockers(blocker[c])

Running(c) == \E k \in Cowns: running[k] /\ c \in Head(queue[k])

AcquiredBy(a, b) ==
  /\ a < b
  /\ \E c \in Cowns: a \in UNION Range(queue[b])
  /\ b = Min({c \in Cowns: a \in UNION Range(queue[b])})
Acquired(c) == \E k \in Cowns: AcquiredBy(c, k)

Normal(c) == priority[c] = 0
Prioritized(c) == priority[c] = 1
Muted(c) == priority[c] = -1

MutedBy(a, b) ==
  /\ Muted(a)
  /\ \E m \in Range(queue[b]): (b \notin m) /\ (a \in m)

Init ==
  /\ fuel = MaxMessageCount
  /\ queue = [c \in Cowns |-> <<{c}>>]
  /\ scheduled = [c \in Cowns |-> TRUE]
  /\ running = [c \in Cowns |-> FALSE]
  /\ mutor = [c \in Cowns |-> Null]
  /\ priority = [c \in Cowns |-> 0]
  /\ blocker = [c \in Cowns |-> Null]

Terminating ==
  /\ \A c \in Cowns: EmptyQueue(c)
  \* -----
  /\ UNCHANGED vars

ExternalReceive(cown) ==
  /\ fuel > 0
  \* -----
  /\ UNCHANGED <<scheduled, running, mutor, priority, blocker>>
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
  /\ UNCHANGED <<fuel, running, mutor>>
  \*# Unschedule and forward the message to the next cown.
  /\ LET
      msg == Head(queue[cown])
      next == Min({c \in msg: c > cown})
    IN
    /\ queue' = Enqueue(next, msg) @@ Dequeue(cown) @@ queue
    /\ blocker' = (cown :> next) @@ blocker
    \*# Prioritize this cown and next if either are prioritized. Unmute next.
    /\ IF \E c \in {cown, next}: Prioritized(c) THEN
      /\ priority' = (next :> 1) @@ priority
      /\ scheduled' = (next :> TRUE) @@ (cown :> FALSE) @@ scheduled
      ELSE
      /\ UNCHANGED <<priority>>
      /\ scheduled' = (cown :> FALSE) @@ scheduled

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
  /\ LET muted == {c \in Head(queue[cown]): Muted(c)} IN
    /\ priority' = [c \in muted |-> 0] @@ priority
    /\ scheduled' = [c \in muted |-> TRUE] @@ scheduled

PreRun(cown) ==
  /\ scheduled[cown]
  /\ ~running[cown]
  /\ ~EmptyQueue(cown)
  /\ cown = Max(Head(queue[cown]))
  \* -----
  /\ UNCHANGED <<fuel, queue, scheduled, mutor, priority>>
  \*# Set max cown in current message to running
  /\ running' = (cown :> TRUE) @@ running
  /\ blocker' = [c \in Head(queue[cown]) |-> Null] @@ blocker

Send(cown) ==
  /\ running[cown]
  /\ fuel > 0
  \*# -----
  /\ UNCHANGED <<running, blocker>>
  /\ fuel' = fuel - 1
  /\ \E receivers \in Subsets(Cowns, 1, MaxMessageSize):
    LET
      next == Min(receivers)
      senders == Head(queue[cown])
      mutors == {c \in receivers: Overloaded(c)}
    IN
    \*# Place message for receivers in the first receiver's queue.
    /\ queue' = Enqueue(next, receivers) @@ queue
    /\ IF (\E c \in receivers: Prioritized(c)) \/ Overloaded(next) THEN
      \*# Prioritize next.
      /\ priority' = (next :> 1) @@ priority
      \*# Reschdeule next if it was muted.
      /\ scheduled' = (next :> (Muted(next) \/ scheduled[next])) @@ scheduled
      \*# Set mutor if any receiver is overloaded and there are no receivers in the set of senders.
      /\ IF
        /\ mutors /= {}
        /\ mutor[cown] = Null
        /\ (senders \intersect receivers) = {}
        THEN mutor' = (cown :> Min(mutors)) @@ mutor
        ELSE UNCHANGED <<mutor>>
      ELSE
      /\ UNCHANGED <<scheduled, mutor, priority>>

PostRun(cown) ==
  /\ running[cown]
  \* -----
  /\ UNCHANGED <<fuel, blocker>>
  /\ running' = (cown :> FALSE) @@ running
  /\ mutor' = (cown :> Null) @@ mutor
  /\ LET msg == Head(queue[cown]) IN
    \*# Mute if mutor is set and no running cowns are overloaded.
    /\ IF (mutor[cown] /= Null) /\ (\A c \in msg: ~Overloaded(c)) THEN
      /\ priority' = [c \in msg |-> -1] @@ priority
      /\ scheduled' = [c \in msg |-> FALSE] @@ scheduled
      \*# Send unmute message to mutor
      /\ queue' = Enqueue(mutor[cown], msg) @@ Dequeue(cown) @@ queue
      ELSE
      /\ UNCHANGED <<priority>>
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
  /\ \A k \in Head(queue[c]): (k < c) => AcquiredBy(k, c)

\*# An acquired cown is not scheduled.
AcquiredImplication == \A c \in Cowns: Acquired(c) =>
  /\ ~scheduled[c]

\*# A muted cown is not scheduled or running.
MutedImplication == \A c \in Cowns: Muted(c) <=>
  /\ \E k \in Cowns: MutedBy(c, k)
  /\ ~scheduled[c]
  /\ ~Running(c)

\*# A muted cown exists in an unmute message in the queue of at least one mutor.
MutedInUnmuteMsg ==
  \A m \in {c \in Cowns: Muted(c)}:
    Cardinality({c \in Cowns: MutedBy(m, c)}) > 0

\*# A cown may be acqiured by at most one message.
AcquiredOnce ==
  \A a \in {c \in Cowns: Acquired(c)}:
    Cardinality({c \in Cowns: AcquiredBy(a, c)}) = 1

\*# An acquired cown is acquired by a cown in its blocker set.
AcquiredByBlocker == \A <<a, b>> \in Cowns \X Cowns:
  AcquiredBy(a, b) => b \in Blockers(a)

\*# An overloaded cown doesn't exist in a muted cown's queue.
OverloadedNotInMutedQueue == \A <<o, m>> \in Cowns \X Cowns:
  Overloaded(o) /\ Muted(m) => o \notin UNION Range(queue[m])

====

(*
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
*)
