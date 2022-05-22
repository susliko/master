---- MODULE crossroads ----
EXTENDS Sequences, Integers, TLC, FiniteSets, Helpers
CONSTANTS Cars

Directions == {"N", "E", "S", "W"}

RightTo[x \in Directions] == 
  CASE x = "N" -> "W"
    [] x = "W" -> "S"
    [] x = "S" -> "E"
    [] x = "E" -> "N"

MkCar(f, t, s) == [from |-> f, to |-> t, state |-> s]
Crashing(car1, car2) == 
  car1.state = "Passing" /\
  car2.state = "Passing" /\
  car1.to = car2.to \* TODO more conflicts

(*--algorithm crossroadPass
variables
  queue = [d \in Directions |-> <<>>],
  wantsTo = [d \in Directions |-> {}],
  wantsFrom = [d \in Directions |-> {}],
  passing = [d \in Directions |-> {}];
define
  Candidates == {Head(q): q \in {q \in Range(queue): Len(q) > 0}}
  MovingTo(t) == wantsTo[t] \intersect Candidates
  MovingFrom(f) == wantsFrom[f] \intersect Candidates
  Reversing(d) == MovingTo(d) \intersect MovingFrom(d) 
  Conflicts(f, t) == 
    ((MovingTo(t) \intersect MovingFrom(RightTo[f])) \ Reversing(t)) \union passing[t]
  Reversal(f, t) == (f = t) => Cardinality(MovingTo(t)) = 1 \* reversing car itself
  CanMove(car, f, t) == 
    car \in Candidates /\
    Cardinality(Conflicts(f, t)) = 0 /\
    Reversal(f, t)
end define;

fair process car \in Cars
variables
  from \in Directions, to \in Directions, state = "Initial";
begin
  Action:
    either
      await state = "Initial";
      state := "Waiting";
      queue[from] := Append(queue[from], self);
      wantsTo[to] := wantsTo[to] \union {self};
      wantsFrom[from] := wantsFrom[from] \union {self};
    or
      await state = "Waiting";
      await CanMove(self, from, to);
      state := "Passing";
      passing[to] := passing[to] \union {self};
    or
      await state = "Passing";
      state := "Initial";
      queue[from] := Tail(queue[from]);
      wantsTo[to] := wantsTo[to] \ {self};
      wantsFrom[from] := wantsFrom[from] \ {self};
      passing[to] := passing[to] \ {self};
    end either;
    goto Action;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "5d6ba981" /\ chksum(tla) = "180bb17e")
VARIABLES queue, wantsTo, wantsFrom, passing, pc

(* define statement *)
Candidates == {Head(q): q \in {q \in Range(queue): Len(q) > 0}}
MovingTo(t) == wantsTo[t] \intersect Candidates
MovingFrom(f) == wantsFrom[f] \intersect Candidates
Reversing(d) == MovingTo(d) \intersect MovingFrom(d)
Conflicts(f, t) ==
  ((MovingTo(t) \intersect MovingFrom(RightTo[f])) \ Reversing(t)) \union passing[t]
Reversal(f, t) == (f = t) => Cardinality(MovingTo(t)) = 1
CanMove(car, f, t) ==
  car \in Candidates /\
  Cardinality(Conflicts(f, t)) = 0 /\
  Reversal(f, t)

VARIABLES from, to, state

vars == << queue, wantsTo, wantsFrom, passing, pc, from, to, state >>

ProcSet == (Cars)

Init == (* Global variables *)
        /\ queue = [d \in Directions |-> <<>>]
        /\ wantsTo = [d \in Directions |-> {}]
        /\ wantsFrom = [d \in Directions |-> {}]
        /\ passing = [d \in Directions |-> {}]
        (* Process car *)
        /\ from \in [Cars -> Directions]
        /\ to \in [Cars -> Directions]
        /\ state = [self \in Cars |-> "Initial"]
        /\ pc = [self \in ProcSet |-> "Action"]

Action(self) == /\ pc[self] = "Action"
                /\ \/ /\ state[self] = "Initial"
                      /\ state' = [state EXCEPT ![self] = "Waiting"]
                      /\ queue' = [queue EXCEPT ![from[self]] = Append(queue[from[self]], self)]
                      /\ wantsTo' = [wantsTo EXCEPT ![to[self]] = wantsTo[to[self]] \union {self}]
                      /\ wantsFrom' = [wantsFrom EXCEPT ![from[self]] = wantsFrom[from[self]] \union {self}]
                      /\ UNCHANGED passing
                   \/ /\ state[self] = "Waiting"
                      /\ CanMove(self, from[self], to[self])
                      /\ state' = [state EXCEPT ![self] = "Passing"]
                      /\ passing' = [passing EXCEPT ![to[self]] = passing[to[self]] \union {self}]
                      /\ UNCHANGED <<queue, wantsTo, wantsFrom>>
                   \/ /\ state[self] = "Passing"
                      /\ state' = [state EXCEPT ![self] = "Initial"]
                      /\ queue' = [queue EXCEPT ![from[self]] = Tail(queue[from[self]])]
                      /\ wantsTo' = [wantsTo EXCEPT ![to[self]] = wantsTo[to[self]] \ {self}]
                      /\ wantsFrom' = [wantsFrom EXCEPT ![from[self]] = wantsFrom[from[self]] \ {self}]
                      /\ passing' = [passing EXCEPT ![to[self]] = passing[to[self]] \ {self}]
                /\ pc' = [pc EXCEPT ![self] = "Action"]
                /\ UNCHANGED << from, to >>

car(self) == Action(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Cars: car(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Cars : WF_vars(car(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

TypeOK ==
 \A c1, c2 \in Cars:
   (from[c1] = from[c2]) => 
     c1 = c2 \/ 
     (state[c1] /= "Passing" \/
      state[c2] /= "Passing")
     
NoCrash == 
  \A c1,c2 \in Cars:
  c1 = c2 \/
  ~Crashing(
    MkCar(from[c1], to[c1], state[c1]), 
    MkCar(from[c2], to[c2], state[c2])
  )

EveryonePasses ==
  \A c \in Cars: <>(state[c] = "Passing")

=====
