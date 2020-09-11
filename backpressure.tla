---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS Null
MessageLimit == 3
Cowns == 1..5
Schedulers == 1..3

\* Range(f) == {f[x]: x \in DOMAIN f}
\* Intersects(a, b) == a \intersect b /= {}
Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Max(s) == CHOOSE x \in s: \A y \in s \ {x}: y < x
Subsets(s, min, max) ==
  {cs \in SUBSET s: (Cardinality(cs) >= min) /\ (Cardinality(cs) <= max)}

(* --algorithm backpressure

variables
  message_fuel = MessageLimit,
  initial_msg \in {cowns \in Subsets(Cowns, 1, 3): TRUE},
  queue = (Min(initial_msg) :> <<initial_msg>>) @@ [c \in Cowns |-> <<>>],
  acquired = [c \in Cowns |-> FALSE],

define
  Sleeping(cown) == queue[cown] = <<>>
  Available(cown) == ~Sleeping(cown) /\ ~acquired[cown]
  Quiescent(cowns) == \A c \in cowns: Sleeping(c)
end define;

fair process scheduler \in Schedulers
variables running = Null
begin
Acquire:
  await (\E c \in Cowns: Available(c)) \/ Quiescent(Cowns);
  if Quiescent(Cowns) then
    goto Done;
  else
    with c \in {c \in Cowns: Available(c)} do running := c; end with;
    acquired := (running :> TRUE) @@ acquired;
  end if;
Run:
  with
    \* Pop the head of its message queue
    msg = Head(queue[running]),
    \* Dequeue msg
    queue_update = (running :> Tail(queue[running])) @@ queue,
  do
    assert running \in msg;
    assert \A c \in msg: acquired[c] \/ (c > running);

    if running = Max(msg) then
      \* TODO: run behaviour: create new messages, overload, mute, etc.
      skip;
      queue := queue_update;
      \* Release any acquired cowns from this behaviour.
      acquired := [c \in msg |-> FALSE] @@ acquired;
    else
      \* Forward message to the next cown.
      with next = Min({c \in msg: c > running}) do
        queue := (next :> Append(queue[next], msg)) @@ queue_update;
      end with;
    end if;

    running := Null;
    goto Acquire;
  end with;
end process;

end algorithm; *)

====
