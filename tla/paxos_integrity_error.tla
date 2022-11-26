\* This implementation of Paxos is intentionally wrong
\* It decides consensus based on a learner receiving "accepted" messages
\* from a majority of acceptors (but with potentially different ballot ids).
\* FakeInit in Acceptor sets up this state. The integrity violation can be triggered
\* by just having 1 additional proposal hit the system.

---- MODULE paxos_integrity_error ----
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANT NULL, NumProposers, NumAcceptors, MaxRetry
Proposers == 1..NumProposers
Acceptors == NumProposers + 1..NumProposers + NumAcceptors
LearnerNum == NumProposers + NumAcceptors + 1

prepare_msg == [id: Nat]
promise_msg == [id: Nat, acceptor_id: Nat, accepted_id: Int, accepted_val: SUBSET Int]
propose_msg == [id: Nat, val: SUBSET Int]
accept_msg == [sender: Nat, accepted_id: Int, accepted_val: SUBSET Int]

(*--algorithm Paxos {
    variables
        prepare_msgs = {};
        promise_msgs = {};
        propose_msgs = {};
        accept_msgs = {};
        final_decision = {};

    define {
        \* In Phase 2A a Proposer will gather reponses from Acceptors and need to know
        \* if any acceptors have already accepted a different proposal. QuorumMax
        \* gives a way to decide which of the responses to use if there has already been an acceptance
        QuorumMax(msgs) == CHOOSE x \in msgs: \A y \in msgs: x.accepted_id >= y.accepted_id

        \* In Phase 3 a learner will need to know what the acceptors decided, this is a utility
        \* to count how often element 'a' appears in set 's'
        Count(a, s) == Cardinality({x \in s: x = a})

        \* Type invariant
        TypeOK == 
            /\ prepare_msgs \subseteq prepare_msg
            /\ promise_msgs \subseteq promise_msg
            /\ propose_msgs \subseteq propose_msg
            /\ accept_msgs \subseteq accept_msg
        
        \* Since the rest of the invariants use process variables, they will be below the translation
    }

    \* Helper macros for sending to queues
    macro SendPrepare(send_id){
        prepare_msgs := prepare_msgs \cup {[id |-> send_id]};
    }

    macro SendPromise(s_id, s_accepted_id, s_accepted_val){
        promise_msgs := promise_msgs \cup {[id |-> s_id, acceptor_id |-> self, accepted_id |-> s_accepted_id, accepted_val |-> s_accepted_val]};
    }

    macro SendPropose(send_id, send_val){
        propose_msgs := propose_msgs \cup {[id |-> send_id, val |-> send_val]};
    }

    macro SendAccept(sender, id, val){
        \* Since an Acceptor can send out multiple acceptances, make sure to clean up the message board
        accept_msgs := {msg \in accept_msgs: msg.sender # self} \cup {[sender |-> sender, accepted_id |-> id, accepted_val |-> val]};
    }

    fair process (Proposer \in Proposers) 
    variables
        ballot_count = 1;
        id = self;
    {
        1A_Prepare:
        \* Create a unique ID by basically doing a bit shift (base NumProposers) + setting low order bits
        id := 6;
        SendPrepare(id);

        2A_Propose:
        with (responses = {msg \in promise_msgs: msg.id = id}) {
            \* See if we got a response from a quorum
            if(2 * Cardinality(responses) > NumAcceptors){
                \* Need to choose the largest ACCEPTED ballot id from the quorum
                with (max = QuorumMax(responses)) {
                    if(max.accepted_id > 0){
                        SendPropose(id, max.accepted_val);
                    } else {
                        \* Use id % 2 as the value to send
                        SendPropose(id, {id % 2});
                    };
                }
            }
            \* NOTE This retry isn't actually necessary since it's the same as a 
            \* new Proposer being created and starting a new proposal "now". Setting
            \* the retry leads to the same behavior as increasing the nubmer of Proposers
             else {
                \* Update ballot count (so id is different next time), send Prepare
                \* ballot_count := ballot_count + 1;
                \*  NOTE If we have an unbounded retry here, we can't even say anything about invariants
                \*  since we are causing an infinite loop (with infinite states), as ballot_count always changes
                \* if(ballot_count <= MaxRetry) goto 1A_Prepare;
                skip;
            }
        }
        
    }

    fair process (Acceptor \in Acceptors) 
    variables
        max_id = -1;
        accepted_id = -1;
        accepted_value = {};
    {
        FakeInit:
        if(self = NumProposers + 1){
            max_id := 1;
            accepted_id := 1;
            accepted_value := {100};
        } else if(self = NumProposers + 2){
            max_id := 2;
            accepted_id := 2;
            accepted_value := {300};
        } else if(self = NumProposers + 3){
            max_id := 3;
            accepted_id := 3;
            accepted_value := {100};
        };
        SendAccept(self, accepted_id, accepted_value);


        AcceptorLoop:
        while(TRUE){
            either {
                \* Phase 1B (PROMISE)
                1B_Promise:
                with(recv_prepare \in prepare_msgs){
                    await(recv_prepare.id > max_id);
                    \* Received a higher ballot number than we have seen before
                    max_id := recv_prepare.id;
                    SendPromise(recv_prepare.id, accepted_id, accepted_value)

                    \* Note: we can nack by not doing anything since we are modeling safety
                }
            } or {
                2B_Accept:
                with(recv_propose \in propose_msgs){
                    \* Received a proposal that is the highest we've seen
                    await (recv_propose.id >= max_id);
                        max_id := recv_propose.id;
                        accepted_id := recv_propose.id;
                        accepted_value := recv_propose.val;
                        
                        SendAccept(self, accepted_id, accepted_value);
                }
            }
        }
        
    }

    \* Represents a "distinguished learner", a learner that propagates acceptances to the rest
    \* In reality this could be elected by something like a bully algorithm
    \* This same procedure can be replicated in the Proposer as well
    fair process (DistinguishedLearer = LearnerNum){
        LearnerLoop:
        while(TRUE){
            3_RecvAccept:
            await accept_msgs # {};
            with(accepted_vals = {x.accepted_val: x \in accept_msgs},
                majority_decision = CHOOSE x \in accepted_vals: \A y \in accepted_vals: 
                    Cardinality({accepted \in accept_msgs: accepted.accepted_val = x}) >=
                    Cardinality({accepted \in accept_msgs: accepted.accepted_val = y})
                \* Some fancy stuff to say "figure out where there is a quorum" -> that is majority_decision
                ){
                \* We can show that this state is indeed reached with this await clause, since the model checker output
                \* will tell us how many times 3_RecvAccept actually occured.
                await(Cardinality({accepted \in accept_msgs: accepted.accepted_val = majority_decision}) * 2 > NumAcceptors);
                final_decision := final_decision \cup majority_decision;
            }
        }
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "f6d544b2" /\ chksum(tla) = "b16c9904")
VARIABLES prepare_msgs, promise_msgs, propose_msgs, accept_msgs, 
          final_decision, pc

(* define statement *)
QuorumMax(msgs) == CHOOSE x \in msgs: \A y \in msgs: x.accepted_id >= y.accepted_id



Count(a, s) == Cardinality({x \in s: x = a})


TypeOK ==
    /\ prepare_msgs \subseteq prepare_msg
    /\ promise_msgs \subseteq promise_msg
    /\ propose_msgs \subseteq propose_msg
    /\ accept_msgs \subseteq accept_msg

VARIABLES ballot_count, id, max_id, accepted_id, accepted_value

vars == << prepare_msgs, promise_msgs, propose_msgs, accept_msgs, 
           final_decision, pc, ballot_count, id, max_id, accepted_id, 
           accepted_value >>

ProcSet == (Proposers) \cup (Acceptors) \cup {LearnerNum}

Init == (* Global variables *)
        /\ prepare_msgs = {}
        /\ promise_msgs = {}
        /\ propose_msgs = {}
        /\ accept_msgs = {}
        /\ final_decision = {}
        (* Process Proposer *)
        /\ ballot_count = [self \in Proposers |-> 1]
        /\ id = [self \in Proposers |-> self]
        (* Process Acceptor *)
        /\ max_id = [self \in Acceptors |-> -1]
        /\ accepted_id = [self \in Acceptors |-> -1]
        /\ accepted_value = [self \in Acceptors |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Proposers -> "1A_Prepare"
                                        [] self \in Acceptors -> "FakeInit"
                                        [] self = LearnerNum -> "LearnerLoop"]

1A_Prepare(self) == /\ pc[self] = "1A_Prepare"
                    /\ id' = [id EXCEPT ![self] = 6]
                    /\ prepare_msgs' = (prepare_msgs \cup {[id |-> id'[self]]})
                    /\ pc' = [pc EXCEPT ![self] = "2A_Propose"]
                    /\ UNCHANGED << promise_msgs, propose_msgs, accept_msgs, 
                                    final_decision, ballot_count, max_id, 
                                    accepted_id, accepted_value >>

2A_Propose(self) == /\ pc[self] = "2A_Propose"
                    /\ LET responses == {msg \in promise_msgs: msg.id = id[self]} IN
                         IF 2 * Cardinality(responses) > NumAcceptors
                            THEN /\ LET max == QuorumMax(responses) IN
                                      IF max.accepted_id > 0
                                         THEN /\ propose_msgs' = (propose_msgs \cup {[id |-> id[self], val |-> (max.accepted_val)]})
                                         ELSE /\ propose_msgs' = (propose_msgs \cup {[id |-> id[self], val |-> ({id[self] % 2})]})
                            ELSE /\ TRUE
                                 /\ UNCHANGED propose_msgs
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << prepare_msgs, promise_msgs, accept_msgs, 
                                    final_decision, ballot_count, id, max_id, 
                                    accepted_id, accepted_value >>

Proposer(self) == 1A_Prepare(self) \/ 2A_Propose(self)

FakeInit(self) == /\ pc[self] = "FakeInit"
                  /\ IF self = NumProposers + 1
                        THEN /\ max_id' = [max_id EXCEPT ![self] = 1]
                             /\ accepted_id' = [accepted_id EXCEPT ![self] = 1]
                             /\ accepted_value' = [accepted_value EXCEPT ![self] = {100}]
                        ELSE /\ IF self = NumProposers + 2
                                   THEN /\ max_id' = [max_id EXCEPT ![self] = 2]
                                        /\ accepted_id' = [accepted_id EXCEPT ![self] = 2]
                                        /\ accepted_value' = [accepted_value EXCEPT ![self] = {300}]
                                   ELSE /\ IF self = NumProposers + 3
                                              THEN /\ max_id' = [max_id EXCEPT ![self] = 3]
                                                   /\ accepted_id' = [accepted_id EXCEPT ![self] = 3]
                                                   /\ accepted_value' = [accepted_value EXCEPT ![self] = {100}]
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED << max_id, 
                                                                   accepted_id, 
                                                                   accepted_value >>
                  /\ accept_msgs' = ({msg \in accept_msgs: msg.sender # self} \cup {[sender |-> self, accepted_id |-> accepted_id'[self], accepted_val |-> accepted_value'[self]]})
                  /\ pc' = [pc EXCEPT ![self] = "AcceptorLoop"]
                  /\ UNCHANGED << prepare_msgs, promise_msgs, propose_msgs, 
                                  final_decision, ballot_count, id >>

AcceptorLoop(self) == /\ pc[self] = "AcceptorLoop"
                      /\ \/ /\ pc' = [pc EXCEPT ![self] = "1B_Promise"]
                         \/ /\ pc' = [pc EXCEPT ![self] = "2B_Accept"]
                      /\ UNCHANGED << prepare_msgs, promise_msgs, propose_msgs, 
                                      accept_msgs, final_decision, 
                                      ballot_count, id, max_id, accepted_id, 
                                      accepted_value >>

1B_Promise(self) == /\ pc[self] = "1B_Promise"
                    /\ \E recv_prepare \in prepare_msgs:
                         /\ (recv_prepare.id > max_id[self])
                         /\ max_id' = [max_id EXCEPT ![self] = recv_prepare.id]
                         /\ promise_msgs' = (promise_msgs \cup {[id |-> (recv_prepare.id), acceptor_id |-> self, accepted_id |-> accepted_id[self], accepted_val |-> accepted_value[self]]})
                    /\ pc' = [pc EXCEPT ![self] = "AcceptorLoop"]
                    /\ UNCHANGED << prepare_msgs, propose_msgs, accept_msgs, 
                                    final_decision, ballot_count, id, 
                                    accepted_id, accepted_value >>

2B_Accept(self) == /\ pc[self] = "2B_Accept"
                   /\ \E recv_propose \in propose_msgs:
                        /\ (recv_propose.id >= max_id[self])
                        /\ max_id' = [max_id EXCEPT ![self] = recv_propose.id]
                        /\ accepted_id' = [accepted_id EXCEPT ![self] = recv_propose.id]
                        /\ accepted_value' = [accepted_value EXCEPT ![self] = recv_propose.val]
                        /\ accept_msgs' = ({msg \in accept_msgs: msg.sender # self} \cup {[sender |-> self, accepted_id |-> accepted_id'[self], accepted_val |-> accepted_value'[self]]})
                   /\ pc' = [pc EXCEPT ![self] = "AcceptorLoop"]
                   /\ UNCHANGED << prepare_msgs, promise_msgs, propose_msgs, 
                                   final_decision, ballot_count, id >>

Acceptor(self) == FakeInit(self) \/ AcceptorLoop(self) \/ 1B_Promise(self)
                     \/ 2B_Accept(self)

LearnerLoop == /\ pc[LearnerNum] = "LearnerLoop"
               /\ pc' = [pc EXCEPT ![LearnerNum] = "3_RecvAccept"]
               /\ UNCHANGED << prepare_msgs, promise_msgs, propose_msgs, 
                               accept_msgs, final_decision, ballot_count, id, 
                               max_id, accepted_id, accepted_value >>

3_RecvAccept == /\ pc[LearnerNum] = "3_RecvAccept"
                /\ accept_msgs # {}
                /\ LET accepted_vals == {x.accepted_val: x \in accept_msgs} IN
                     LET majority_decision ==                 CHOOSE x \in accepted_vals: \A y \in accepted_vals:
                                              Cardinality({accepted \in accept_msgs: accepted.accepted_val = x}) >=
                                              Cardinality({accepted \in accept_msgs: accepted.accepted_val = y}) IN
                       /\ (Cardinality({accepted \in accept_msgs: accepted.accepted_val = majority_decision}) * 2 > NumAcceptors)
                       /\ final_decision' = (final_decision \cup majority_decision)
                /\ pc' = [pc EXCEPT ![LearnerNum] = "LearnerLoop"]
                /\ UNCHANGED << prepare_msgs, promise_msgs, propose_msgs, 
                                accept_msgs, ballot_count, id, max_id, 
                                accepted_id, accepted_value >>

DistinguishedLearer == LearnerLoop \/ 3_RecvAccept

Next == DistinguishedLearer
           \/ (\E self \in Proposers: Proposer(self))
           \/ (\E self \in Acceptors: Acceptor(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proposers : WF_vars(Proposer(self))
        /\ \A self \in Acceptors : WF_vars(Acceptor(self))
        /\ WF_vars(DistinguishedLearer)

\* END TRANSLATION 

\* !! Can't say this! This says there always will exist a majority decision
\* !! It's very difficult to reason about only having N failures out of 2N + 1 nodes
\* !! Even if we went through that annoying process, there can still be livelock
AlwaysAgreement == <>[](Cardinality(final_decision > 0))

\* Once a value has been decided (consensus), it will not change
Integrity == Cardinality(final_decision) <= 1

\* Acceptors only take on valid values (obvious)
AtMostOneAgreement == \A a \in Acceptors: 
                                        \*  /\ accepted_value[a] \subseteq 0..1
                                         /\ Cardinality(accepted_value[a]) <= 1

\* If there was a decision reached by the distinguished learner, it was a majority
DecisionIsMajority == 
    TRUE
    \* final_decision # {} => 
    \*                 2 * Cardinality({a \in Acceptors: accepted_value[a] = final_decision}) > NumAcceptors

====

