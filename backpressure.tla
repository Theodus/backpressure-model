---- MODULE backpressure ----

EXTENDS FiniteSets, Integers, Sequences, TLC

Null == 0
Cowns == 1..3
BehaviourLimit == 4
OverloadThreshold == 2
PriorityLevels == {-1, 0, 1}

Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Max(s) == CHOOSE x \in s: \A y \in s \ {x}: y < x

Range(f) == {f[x]: x \in DOMAIN f}

Pick(s) == CHOOSE x \in s: TRUE
ReduceSet(op(_, _), set, acc) ==
  LET f[s \in SUBSET set] ==
    IF s = {} THEN acc ELSE LET x == Pick(s) IN op(x, f[s \ {x}])
  IN f[set]
RECURSIVE ForallSeq(_, _)
ForallSeq(p(_), s) ==
  IF Len(s) = 0 THEN TRUE ELSE p(Head(s)) /\ ForallSeq(p, Tail(s))

VARIABLES fuel, queue, scheduled, running, priority, mutor, mute
vars == <<fuel, queue, scheduled, running, priority, mutor, mute>>

Sleeping(c) == scheduled[c] /\ (Len(queue[c]) = 0)
Available(c) == scheduled[c] /\ (Len(queue[c]) > 0)
Overloaded(c) == Len(queue[c]) > OverloadThreshold
Muted(c) == c \in UNION Range(mute)

Init ==
  /\ fuel = BehaviourLimit
  /\ queue = [c \in Cowns |-> <<{c}>>]
  /\ scheduled = [c \in Cowns |-> TRUE]
  /\ running = [c \in Cowns |-> FALSE]
  /\ priority = [c \in Cowns |-> 0]
  /\ mutor = [c \in Cowns |-> Null]
  /\ mute = [c \in Cowns |-> {}]

Terminating ==
  /\ \A c \in Cowns: Sleeping(c)
  /\ UNCHANGED vars

Acquire(cown) ==
  /\ Available(cown)
  /\ LET msg == Head(queue[cown]) IN
    /\ cown < Max(msg)
    /\ IF \E c \in msg: priority[c] = 1 THEN
        LET prioritizing == {c \in msg: (c > cown) /\ (priority[c] < 1)} IN
        \* TODO: eventually reduce priority
        /\ priority' = [c \in prioritizing |-> 1] @@ priority
        \* TODO: mute map kept in sync
        /\ mute' = [k \in DOMAIN mute |-> mute[k] \ prioritizing] @@ mute
        /\ scheduled' = (cown :> FALSE) @@ [c \in prioritizing |-> TRUE] @@ scheduled
      ELSE
        /\ scheduled' = (cown :> FALSE) @@ scheduled
        /\ UNCHANGED <<priority, mute>>
    /\ LET next == Min({c \in msg: c > cown}) IN
      LET q == (cown :> Tail(queue[cown])) @@ queue IN
      queue' = (next :> Append(queue[next], msg)) @@ q
  /\ UNCHANGED <<fuel, running, mutor>>

Prerun(cown) ==
  /\ scheduled[cown]
  /\ IF Len(queue[cown]) = 0 THEN FALSE ELSE cown = Max(Head(queue[cown]))
  /\ priority' = (cown :> IF Overloaded(cown) THEN 1 ELSE 0) @@ priority
  /\ running' = (cown :> TRUE) @@ running
  /\ UNCHANGED <<fuel, queue, scheduled, mutor, mute>>

Send(cown) ==
  /\ running[cown]
  /\ fuel > 0
  /\ \E msg \in SUBSET Cowns:
    /\ Cardinality(msg) > 0
    /\ Cardinality(msg) <= 3 \* cut state space
    /\ queue' = (Min(msg) :> Append(queue[Min(msg)], msg)) @@ queue
    /\ LET mutors == {c \in msg \ Head(queue[cown]): priority[c] = 1} IN
      IF (mutor[cown] = Null) /\ (mutors /= {}) THEN
        /\ mutor' = (cown :> Min(mutors)) @@ mutor
      ELSE
        /\ TRUE
        /\ UNCHANGED <<mutor>>
  /\ fuel' = fuel - 1
  /\ UNCHANGED <<running, scheduled, priority, mute>>

Complete(cown) ==
  /\ running[cown]
  /\ LET msg == Head(queue[cown]) IN
    /\ IF mutor[cown] /= Null THEN
        LET muting == {c \in msg: priority[c] = 0} IN
        /\ priority' = [c \in muting |-> -1] @@ priority
        /\ mute' = (mutor[cown] :> mute[mutor[cown]] \union muting) @@ mute
        /\ scheduled' = [c \in msg |-> c \notin muting] @@ scheduled
      ELSE
        /\ scheduled' = [c \in msg |-> TRUE] @@ scheduled
        /\ UNCHANGED <<priority, mute>>
  /\ queue' = (cown :> Tail(queue[cown])) @@ queue
  /\ running' = (cown :> FALSE) @@ running
  /\ mutor' = (cown :> Null) @@ mutor
  /\ UNCHANGED <<fuel>>

Run(cown) ==
  \/ Acquire(cown)
  \/ Prerun(cown)
  \/ Send(cown)
  \/ Complete(cown)

Next == Terminating \/ \E c \in Cowns: Run(c)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Cowns: WF_vars(Run(c))

MessageLimit ==
  LET msgs == ReduceSet(LAMBDA c, sum: sum + Len(queue[c]), Cowns, 0) IN
  msgs <= (BehaviourLimit + Max(Cowns))
RunningIsScheduled ==
  \A c \in Cowns: running[c] => scheduled[c]
LowPriorityNotScheduled ==
  \A c \in Cowns: (priority[c] = -1) => ~scheduled[c]
LowPriorityMuted ==
  \A c \in Cowns: (priority[c] = -1) <=> Muted(c)
BehaviourAcquisition ==
  \A c \in Cowns: scheduled[c] =>
    ~(\E k \in Cowns: (k > c) /\ (c \in UNION Range(queue[k])))

InvalidPriorityMix(msg) ==
  /\ \E c \in msg: priority[c] = -1
  /\ \E c \in msg: priority[c] = 1
Prioritization ==
  \A c \in Cowns: ForallSeq(LAMBDA msg: ~InvalidPriorityMix(msg), queue[c])

\* Bad == \A c \in Cowns: blocker[c] \notin mute[c]

Termination == <>[](\A c \in Cowns: Sleeping(c))
OverloadRaisesPriority ==
  \A c \in Cowns: (scheduled[c] /\ Overloaded(c)) => (priority[c] = 1)

\* TODO: no message from overloaded cown is in muted queue

====
