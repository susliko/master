---- MODULE crossroads ----
EXTENDS Sequences, Integers, TLC, FiniteSets, Helpers
CONSTANTS Cars

DirsSeq == <<"N", "E", "S", "W">>
Dirs == Range(DirsSeq)

IndOf(dir) == Matching(DirsSeq, dir)

RightTo[x \in Dirs] == 
  LET RightInd == (IndOf(x) % 4) + 1
  IN DirsSeq[RightInd]
OppTo[x \in Dirs] ==
  LET OppInd == ((IndOf(x) + 1) % 4) + 1
  IN DirsSeq[OppInd]
LeftTo[x \in Dirs] == 
  LET LeftInd == ((IndOf(x) + 2) % 4) + 1
  IN DirsSeq[LeftInd] 

MkCar(f, t, s) == [from |-> f, to |-> t, state |-> s]
Straight(car) == Abs(IndOf(car.from) - IndOf(car.to)) = 2
Left(car) == Abs(IndOf(car.from) - IndOf(car.to)) = 3
Reverse(car) == car.from = car.to
  
Crashing(car1, car2) == 
  /\ car1.state = "Passing" 
  /\ car2.state = "Passing" 
  /\ \/ car1.to = car2.to  
     \/ /\ Straight(car1) 
        /\ \/ car2.from = RightTo[car1.from] 
           \/ Straight(car2)
     \/ /\ Left(car1)
        /\ \/ car2.from = RightTo[car1.from]
           \/ car2.from = OppTo[car1.from]
           \/ /\ car2.from = LeftTo[car1.from]
              /\ Left(car2) \/ Straight(car2)
     \/ /\ Reverse(car1)
             
(*--algorithm crossroadPass
variables
  queue = [d \in Dirs |-> <<>>],
  wantTo = [d \in Dirs |-> {}],
  wantFrom = [d \in Dirs |-> {}],
  passing = [d \in Dirs |-> {}];
define
  CanMove(car, from, to) == 
    LET
      Candidates == Heads(queue)
      To(t) == wantTo[t] \intersect Candidates
      From(f) == wantFrom[f] \intersect Candidates
      Reversing(d) == To(d) \intersect From(d) 
      Conflicts(f, t) == ((To(t) \intersect From(RightTo[f])) \ Reversing(t)) \union passing[t]
      Reversal(f, t) == (f = t) => Cardinality(To(t)) = 1 \* reversing car itself
    IN
    car \in Candidates /\
    Cardinality(Conflicts(from, to)) = 0 /\
    Reversal(from, to)
end define;

fair process car \in Cars
variables
  from \in Dirs, to \in Dirs, state = "Initial";
begin
  Action:
    either
      await state = "Initial";
      state := "Waiting";
      queue[from] := Append(queue[from], self);
      wantTo[to] := wantTo[to] \union {self};
      wantFrom[from] := wantFrom[from] \union {self};
    or
      await state = "Waiting";
      await CanMove(self, from, to);
      state := "Passing";
      passing[to] := passing[to] \union {self};
    or
      await state = "Passing";
      state := "Initial";
      queue[from] := Tail(queue[from]);
      wantTo[to] := wantTo[to] \ {self};
      wantFrom[from] := wantFrom[from] \ {self};
      passing[to] := passing[to] \ {self};
    end either;
    goto Action;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "3425e6a1" /\ chksum(tla) = "65466f39")
VARIABLES queue, wantTo, wantFrom, passing, pc

(* define statement *)
CanMove(car, from, to) ==
  LET
    Candidates == Heads(queue)
    To(t) == wantTo[t] \intersect Candidates
    From(f) == wantFrom[f] \intersect Candidates
    Reversing(d) == To(d) \intersect From(d)
    Conflicts(f, t) == ((To(t) \intersect From(RightTo[f])) \ Reversing(t)) \union passing[t]
    Reversal(f, t) == (f = t) => Cardinality(To(t)) = 1
  IN
  car \in Candidates /\
  Cardinality(Conflicts(from, to)) = 0 /\
  Reversal(from, to)

VARIABLES from, to, state

vars == << queue, wantTo, wantFrom, passing, pc, from, to, state >>

ProcSet == (Cars)

Init == (* Global variables *)
        /\ queue = [d \in Dirs |-> <<>>]
        /\ wantTo = [d \in Dirs |-> {}]
        /\ wantFrom = [d \in Dirs |-> {}]
        /\ passing = [d \in Dirs |-> {}]
        (* Process car *)
        /\ from \in [Cars -> Dirs]
        /\ to \in [Cars -> Dirs]
        /\ state = [self \in Cars |-> "Initial"]
        /\ pc = [self \in ProcSet |-> "Action"]

Action(self) == /\ pc[self] = "Action"
                /\ \/ /\ state[self] = "Initial"
                      /\ state' = [state EXCEPT ![self] = "Waiting"]
                      /\ queue' = [queue EXCEPT ![from[self]] = Append(queue[from[self]], self)]
                      /\ wantTo' = [wantTo EXCEPT ![to[self]] = wantTo[to[self]] \union {self}]
                      /\ wantFrom' = [wantFrom EXCEPT ![from[self]] = wantFrom[from[self]] \union {self}]
                      /\ UNCHANGED passing
                   \/ /\ state[self] = "Waiting"
                      /\ CanMove(self, from[self], to[self])
                      /\ state' = [state EXCEPT ![self] = "Passing"]
                      /\ passing' = [passing EXCEPT ![to[self]] = passing[to[self]] \union {self}]
                      /\ UNCHANGED <<queue, wantTo, wantFrom>>
                   \/ /\ state[self] = "Passing"
                      /\ state' = [state EXCEPT ![self] = "Initial"]
                      /\ queue' = [queue EXCEPT ![from[self]] = Tail(queue[from[self]])]
                      /\ wantTo' = [wantTo EXCEPT ![to[self]] = wantTo[to[self]] \ {self}]
                      /\ wantFrom' = [wantFrom EXCEPT ![from[self]] = wantFrom[from[self]] \ {self}]
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
  \A c1, c2 \in Cars:
  (c1 /= c2) => ~Crashing(
    MkCar(from[c1], to[c1], state[c1]), 
    MkCar(from[c2], to[c2], state[c2])
  )

EveryonePasses ==
  \A c \in Cars: <>(state[c] = "Passing")

=====
