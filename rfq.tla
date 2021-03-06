---- MODULE rfq ----
EXTENDS FiniteSets, Sequences, TLC, Integers
CONSTANTS suppliers, maxPrice, NULL


(*
--algorithm rfq
  variables
    requests = [s \in suppliers |-> FALSE],
    proposals = [s \in suppliers |-> NULL],
    deadline = FALSE;
    winner = NULL;
  define
    Responded == {el \in DOMAIN proposals: proposals[el] /= NULL}

    ReachableDeadline == <>[]deadline
    NoProposalsAfterDeadline == [][deadline => UNCHANGED proposals]_<<deadline, proposals>>
    WinnerExists == <>[]((Cardinality(Responded) > 0) => winner /= NULL)
    WinnerHasBestPrice == [](winner /= NULL => \A s \in Responded: proposals[winner] <= proposals[s])
  end define;
  
  fair process supplier \in suppliers
  begin
  Receive:
    await requests[self];
  Respond:
    with price \in 1..maxPrice \union {NULL} do
      if ~deadline then
        proposals[self] := price;
      end if;
    end with;
  end process;

  fair process requester = "requester"
  begin
  Request:
    requests := [s \in suppliers |-> TRUE];
  Proceed:
    deadline := TRUE;
  Decide:                  
    if Cardinality(Responded) > 0 then
      winner := 
        CHOOSE s1 \in Responded: 
        \A s2 \in Responded: 
        proposals[s1] <= proposals[s2]
    end if;
  end process;
end algorithm;
*)

\* BEGIN TRANSLATION (chksum(pcal) = "6fc7853a" /\ chksum(tla) = "4ba57d82")
VARIABLES requests, proposals, deadline, winner, pc

(* define statement *)
Responded == {el \in DOMAIN proposals: proposals[el] /= NULL}

ReachableDeadline == <>[]deadline
NoProposalsAfterDeadline == [][deadline => UNCHANGED proposals]_<<deadline, proposals>>
WinnerExists == <>[]((Cardinality(Responded) > 0) => winner /= NULL)
WinnerHasBestPrice == [](winner /= NULL => \A s \in (Responded \ {winner}): proposals[winner] < proposals[s])


vars == << requests, proposals, deadline, winner, pc >>

ProcSet == (suppliers) \cup {"requester"}

Init == (* Global variables *)
        /\ requests = [s \in suppliers |-> FALSE]
        /\ proposals = [s \in suppliers |-> NULL]
        /\ deadline = FALSE
        /\ winner = NULL
        /\ pc = [self \in ProcSet |-> CASE self \in suppliers -> "Receive"
                                        [] self = "requester" -> "Request"]

Receive(self) == /\ pc[self] = "Receive"
                 /\ requests[self]
                 /\ pc' = [pc EXCEPT ![self] = "Respond"]
                 /\ UNCHANGED << requests, proposals, deadline, winner >>

Respond(self) == /\ pc[self] = "Respond"
                 /\ \E price \in 1..maxPrice \union {NULL}:
                      IF ~deadline
                         THEN /\ proposals' = [proposals EXCEPT ![self] = price]
                         ELSE /\ TRUE
                              /\ UNCHANGED proposals
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << requests, deadline, winner >>

supplier(self) == Receive(self) \/ Respond(self)

Request == /\ pc["requester"] = "Request"
           /\ requests' = [s \in suppliers |-> TRUE]
           /\ pc' = [pc EXCEPT !["requester"] = "Proceed"]
           /\ UNCHANGED << proposals, deadline, winner >>

Proceed == /\ pc["requester"] = "Proceed"
           /\ deadline' = TRUE
           /\ pc' = [pc EXCEPT !["requester"] = "Decide"]
           /\ UNCHANGED << requests, proposals, winner >>

Decide == /\ pc["requester"] = "Decide"
          /\ IF Cardinality(Responded) > 0
                THEN /\ winner' = (CHOOSE s1 \in Responded:
                                   \A s2 \in Responded:
                                   proposals[s1] <= proposals[s2])
                ELSE /\ TRUE
                     /\ UNCHANGED winner
          /\ pc' = [pc EXCEPT !["requester"] = "Done"]
          /\ UNCHANGED << requests, proposals, deadline >>

requester == Request \/ Proceed \/ Decide

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == requester
           \/ (\E self \in suppliers: supplier(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in suppliers : WF_vars(supplier(self))
        /\ WF_vars(requester)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
======
