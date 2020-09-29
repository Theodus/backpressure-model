---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS Null
BehaviourLimit == 4
Cowns == 1..3
OverloadThreshold == 2

Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Max(s) == CHOOSE x \in s: \A y \in s \ {x}: y < x

Range(f) == {f[x]: x \in DOMAIN f}

Pick(s) == CHOOSE x \in s: TRUE
ReduceSet(op(_, _), set, acc) ==
  LET f[s \in SUBSET set] ==
    IF s = {} THEN acc ELSE LET x == Pick(s) IN op(x, f[s \ {x}])
  IN f[set]

VARIABLES fuel, queue, scheduled, mute, mutor, protected, blocker
vars == <<fuel, queue, scheduled, mute, mutor, protected, blocker>>

Sleeping(c) == scheduled[c] /\ (Len(queue[c]) = 0)
Available(c) == scheduled[c] /\ (Len(queue[c]) > 0)
Running(c) ==
  /\ scheduled[c]
  /\ IF Len(queue[c]) = 0 THEN FALSE ELSE c = Max(Head(queue[c]))

Overloaded(c) == Len(queue[c]) >= OverloadThreshold
Muted(c) == c \in UNION Range(mute)
TriggersMuting(c) == Overloaded(c) \/ Muted(c)
TriggersProtection(c) == Overloaded(c) \/ protected[c]

Init ==
  /\ fuel = BehaviourLimit
  /\ queue = [c \in Cowns |-> <<{c}>>]
  /\ scheduled = [c \in Cowns |-> TRUE]
  /\ mute = [c \in Cowns |-> {}]
  /\ mutor = [c \in Cowns |-> Null]
  /\ protected = [c \in Cowns |-> FALSE]
  /\ blocker = [c \in Cowns |-> Null]

Terminating ==
  /\ \A c \in Cowns: Sleeping(c)
  /\ UNCHANGED vars

Acquire(cown) ==
  /\ Available(cown)
  /\ LET msg == Head(queue[cown]) IN
    /\ cown < Max(msg)
    /\ LET next == Min({c \in msg: c > cown}) IN
      LET q == (cown :> Tail(queue[cown])) @@ queue IN
      /\ queue' = (next :> Append(queue[next], msg)) @@ q
      /\ blocker' = (cown :> next) @@ blocker
    /\ IF \E c \in msg: TriggersProtection(c) THEN
        LET p == {c \in msg: c > cown} IN
        /\ protected' = [c \in p |-> TRUE] @@ protected
        \* Note: mute map is kept up-to-date
        /\ mute' = [k \in DOMAIN mute |-> mute[k] \ p] @@ mute
        /\ scheduled' = (cown :> FALSE) @@ [c \in p |-> TRUE] @@ scheduled
      ELSE
        /\ scheduled' = (cown :> FALSE) @@ scheduled
        /\ UNCHANGED <<mute, protected>>
  /\ UNCHANGED <<fuel, mutor>>

ScanMsg(cown, senders, receivers) ==
  IF \E r \in receivers: TriggersMuting(r) THEN
    LET m == Min({r \in receivers: TriggersMuting(r)}) IN
    mutor' = (cown :> m) @@ mutor
  ELSE
    UNCHANGED <<mutor>>

Send(cown) ==
  /\ Running(cown)
  /\ fuel > 0
  /\ \E msg \in SUBSET Cowns:
    /\ Cardinality(msg) > 0
    /\ Cardinality(msg) <= 3 \* cut state space
    /\ ScanMsg(cown, Head(queue[cown]), msg)
    /\ queue' = (Min(msg) :> Append(queue[Min(msg)], msg)) @@ queue
  /\ fuel' = fuel - 1
  /\ UNCHANGED <<scheduled, mute, protected, blocker>>

Complete(cown) ==
  /\ Running(cown)
  /\ LET msg == Head(queue[cown]) IN
    /\ IF mutor[cown] /= Null THEN
      LET muting == {c \in msg: ~TriggersProtection(c)} IN
        /\ scheduled' = [c \in msg |-> c \notin muting] @@ scheduled
        /\ mute' = (mutor[cown] :> mute[mutor[cown]] \union muting) @@ mute
      ELSE
        /\ scheduled' = [c \in msg |-> TRUE] @@ scheduled
        /\ UNCHANGED <<mute>>
    /\ blocker' = [c \in msg |-> Null] @@ blocker
  /\ queue' = (cown :> Tail(queue[cown])) @@ queue
  /\ mutor' = (cown :> Null) @@ mutor
  /\ UNCHANGED <<fuel, protected>>

Unmute ==
  \* TODO: muted key is valid
  LET invalid_keys == {k \in DOMAIN mute: ~Overloaded(k)} IN
  LET unmuting == UNION Range([k \in invalid_keys |-> mute[k]]) IN
  /\ unmuting /= {}
  /\ mute' = [k \in invalid_keys |-> {}] @@ mute
  /\ scheduled' = [c \in unmuting |-> TRUE] @@ scheduled
  /\ UNCHANGED <<fuel, queue, mutor, protected, blocker>>

Run(cown) ==
  \/ Acquire(cown)
  \/ Send(cown)
  \/ Complete(cown)

Next == Terminating \/ \E c \in Cowns: Run(c) \/ Unmute

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Cowns: WF_vars(Run(c))
  /\ WF_vars(Unmute)

MessageLimit ==
  LET msgs == ReduceSet(LAMBDA c, sum: sum + Len(queue[c]), Cowns, 0) IN
  msgs <= (BehaviourLimit + Max(Cowns))

MutedNotScheduled == \A c \in Cowns: Muted(c) => ~scheduled[c]

ProtectedNotMuted == \A c \in Cowns: protected[c] => ~Muted(c)

Termination == <>[](\A c \in Cowns: Sleeping(c))
\* implies \A c \in Cowns: Overloaded(c) ~> scheduled[c]

\* TODO: no message from overloaded cown is in muted queue
\* PriorityMessageUnblocked ==
\*   \A c \in Cowns: Muted(c) => ...

====
