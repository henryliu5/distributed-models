---- MODULE 2pc ----
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT Participants

\* There are two types of messages, those from Participants and those from
\* the Coordinator. Participants can only send "Prepared", and Coordinator
\* can only tell all the Participants to commit or abort. 
\* Note:
\*     - Particpant failure is the same as not sending a "Prepared"
\*     - Only the Coordinator will send an abort or commit, so it doesn't need a sender field
msg == [type: {"Prepared"}, sender: Participants] \cup [type: {"Abort", "Commit"}]


(*--algorithm 2PC {
    variables
        \* 
        prepared_participants = {};
        all_msgs = {};
        \* This is a FUNCTION, mapping participants to their state
        participant_state = [p \in Participants |-> "working"];
        coordinator_state = "init";


    define {
        \* --------- Invariants ----------
        TypeOK == 
            \* The RHS is a FUNCTION SET, i.e. is the domain and range correct
            /\ participant_state \in [Participants -> {"working", "prepared", "committed", "aborted", "failed"}]
            /\ coordinator_state \in {"init", "committed", "aborted", "failed"}
            /\ all_msgs \subseteq msg
            /\ prepared_participants \subseteq Participants
        
        \* All participants should be in committed or aborted
        ParticipantsConsistent == \A p1, p2 \in Participants: 
            ~ (/\ participant_state[p1] = "committed"
               /\ participant_state[p2] = "aborted")
        
        CoordinatorDecision == <>(coordinator_state # "init")
        EndInCommitOrAbort == [][\A p \in Participants: 
            /\ participant_state[p] = "committed" => participant_state[p]' = "committed"
            /\ participant_state[p] = "aborted" => participant_state[p]' = "aborted"
            /\ participant_state[p] = "failed" => participant_state[p]' = "failed"]_participant_state
        CommitConsistent == coordinator_state = "committed" ~> \A p \in Participants: participant_state[p] = "committed"
        AbortConsistent == coordinator_state = "aborted" ~> \A p \in Participants: participant_state[p] \in {"aborted", "failed"}
    }

    fair process (Coordinator = "Coordinator") {
        CoordinatorMain:
        \* TODO find condition where you need this loop
        \* probably will be if the messages all have commit ~> coordinator commit
        while(coordinator_state = "init"){
            CoordinatorUpdate:
            \* Update prepared_participants based on messages
            with(particpate_msgs = {x \in all_msgs: x.type = "Prepared"}) {
                \* await ({x.sender: x \in particpate_msgs} \ prepared_participants) # {};
                prepared_participants := {x.sender: x \in particpate_msgs};
            };

            either {
                if(prepared_participants = Participants){
                    CoordinatorCommit:
                    \* Send Commit if everyone is ready
                    all_msgs := all_msgs \cup {[type |-> "Commit"]};
                    coordinator_state := "committed";
                } else {
                    CoordinatorAbort:
                    \* Coordinator can always abort (implementation detail: e.g. timeout)
                    all_msgs := all_msgs \cup {[type |-> "Abort"]};
                    coordinator_state := "aborted";
                }
            } 
            or {
                CoordinatorFailure:
                \* Explicit failure
                coordinator_state := "failed";
            }
        }
    };

    fair process (Participant \in Participants){
        ParticipantWorking:
        either {
            ParticipantPrepare:
            \* Prepare
            participant_state[self] := "prepared";
            all_msgs := all_msgs \cup {[type |-> "Prepared", sender |-> self]};
        } or {
            ParticipantFailure:
            \* Can fail, same as abort but no message
            participant_state[self] := "failed";
        };

        ParticipantDecision:
        while(participant_state[self] = "prepared"){
            if(\E x \in all_msgs: x.type = "Commit"){
                participant_state[self] := "committed";
            } else if(\E x \in all_msgs: x.type = "Abort"){
                participant_state[self] := "aborted";
            }
        }
    }

} *)
\* BEGIN TRANSLATION (chksum(pcal) = "58cd5f5" /\ chksum(tla) = "9ea5d0f5")
VARIABLES prepared_participants, all_msgs, participant_state, 
          coordinator_state, pc

(* define statement *)
TypeOK ==

    /\ participant_state \in [Participants -> {"working", "prepared", "committed", "aborted", "failed"}]
    /\ coordinator_state \in {"init", "committed", "aborted", "failed"}
    /\ all_msgs \subseteq msg
    /\ prepared_participants \subseteq Participants


ParticipantsConsistent == \A p1, p2 \in Participants:
    ~ (/\ participant_state[p1] = "committed"
       /\ participant_state[p2] = "aborted")

CoordinatorDecision == <>(coordinator_state # "init")
EndInCommitOrAbort == [][\A p \in Participants:
    /\ participant_state[p] = "committed" => participant_state[p]' = "committed"
    /\ participant_state[p] = "aborted" => participant_state[p]' = "aborted"
    /\ participant_state[p] = "failed" => participant_state[p]' = "failed"]_participant_state
CommitConsistent == coordinator_state = "committed" ~> \A p \in Participants: participant_state[p] = "committed"
AbortConsistent == coordinator_state = "aborted" ~> \A p \in Participants: participant_state[p] \in {"aborted", "failed"}


vars == << prepared_participants, all_msgs, participant_state, 
           coordinator_state, pc >>

ProcSet == {"Coordinator"} \cup (Participants)

Init == (* Global variables *)
        /\ prepared_participants = {}
        /\ all_msgs = {}
        /\ participant_state = [p \in Participants |-> "working"]
        /\ coordinator_state = "init"
        /\ pc = [self \in ProcSet |-> CASE self = "Coordinator" -> "CoordinatorMain"
                                        [] self \in Participants -> "ParticipantWorking"]

CoordinatorMain == /\ pc["Coordinator"] = "CoordinatorMain"
                   /\ IF coordinator_state = "init"
                         THEN /\ pc' = [pc EXCEPT !["Coordinator"] = "CoordinatorUpdate"]
                         ELSE /\ pc' = [pc EXCEPT !["Coordinator"] = "Done"]
                   /\ UNCHANGED << prepared_participants, all_msgs, 
                                   participant_state, coordinator_state >>

CoordinatorUpdate == /\ pc["Coordinator"] = "CoordinatorUpdate"
                     /\ LET particpate_msgs == {x \in all_msgs: x.type = "Prepared"} IN
                          prepared_participants' = {x.sender: x \in particpate_msgs}
                     /\ \/ /\ IF prepared_participants' = Participants
                                 THEN /\ pc' = [pc EXCEPT !["Coordinator"] = "CoordinatorCommit"]
                                 ELSE /\ pc' = [pc EXCEPT !["Coordinator"] = "CoordinatorAbort"]
                        \/ /\ pc' = [pc EXCEPT !["Coordinator"] = "CoordinatorFailure"]
                     /\ UNCHANGED << all_msgs, participant_state, 
                                     coordinator_state >>

CoordinatorCommit == /\ pc["Coordinator"] = "CoordinatorCommit"
                     /\ all_msgs' = (all_msgs \cup {[type |-> "Commit"]})
                     /\ coordinator_state' = "committed"
                     /\ pc' = [pc EXCEPT !["Coordinator"] = "CoordinatorMain"]
                     /\ UNCHANGED << prepared_participants, participant_state >>

CoordinatorAbort == /\ pc["Coordinator"] = "CoordinatorAbort"
                    /\ all_msgs' = (all_msgs \cup {[type |-> "Abort"]})
                    /\ coordinator_state' = "aborted"
                    /\ pc' = [pc EXCEPT !["Coordinator"] = "CoordinatorMain"]
                    /\ UNCHANGED << prepared_participants, participant_state >>

CoordinatorFailure == /\ pc["Coordinator"] = "CoordinatorFailure"
                      /\ coordinator_state' = "failed"
                      /\ pc' = [pc EXCEPT !["Coordinator"] = "CoordinatorMain"]
                      /\ UNCHANGED << prepared_participants, all_msgs, 
                                      participant_state >>

Coordinator == CoordinatorMain \/ CoordinatorUpdate \/ CoordinatorCommit
                  \/ CoordinatorAbort \/ CoordinatorFailure

ParticipantWorking(self) == /\ pc[self] = "ParticipantWorking"
                            /\ \/ /\ pc' = [pc EXCEPT ![self] = "ParticipantPrepare"]
                               \/ /\ pc' = [pc EXCEPT ![self] = "ParticipantFailure"]
                            /\ UNCHANGED << prepared_participants, all_msgs, 
                                            participant_state, 
                                            coordinator_state >>

ParticipantPrepare(self) == /\ pc[self] = "ParticipantPrepare"
                            /\ participant_state' = [participant_state EXCEPT ![self] = "prepared"]
                            /\ all_msgs' = (all_msgs \cup {[type |-> "Prepared", sender |-> self]})
                            /\ pc' = [pc EXCEPT ![self] = "ParticipantDecision"]
                            /\ UNCHANGED << prepared_participants, 
                                            coordinator_state >>

ParticipantFailure(self) == /\ pc[self] = "ParticipantFailure"
                            /\ participant_state' = [participant_state EXCEPT ![self] = "failed"]
                            /\ pc' = [pc EXCEPT ![self] = "ParticipantDecision"]
                            /\ UNCHANGED << prepared_participants, all_msgs, 
                                            coordinator_state >>

ParticipantDecision(self) == /\ pc[self] = "ParticipantDecision"
                             /\ IF participant_state[self] = "prepared"
                                   THEN /\ IF \E x \in all_msgs: x.type = "Commit"
                                              THEN /\ participant_state' = [participant_state EXCEPT ![self] = "committed"]
                                              ELSE /\ IF \E x \in all_msgs: x.type = "Abort"
                                                         THEN /\ participant_state' = [participant_state EXCEPT ![self] = "aborted"]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED participant_state
                                        /\ pc' = [pc EXCEPT ![self] = "ParticipantDecision"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                        /\ UNCHANGED participant_state
                             /\ UNCHANGED << prepared_participants, all_msgs, 
                                             coordinator_state >>

Participant(self) == ParticipantWorking(self) \/ ParticipantPrepare(self)
                        \/ ParticipantFailure(self)
                        \/ ParticipantDecision(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Coordinator
           \/ (\E self \in Participants: Participant(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Coordinator)
        /\ \A self \in Participants : WF_vars(Participant(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
