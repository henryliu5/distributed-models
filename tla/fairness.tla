---- MODULE fairness ----
EXTENDS TLC, Integers
CONSTANT NumThreads
(*--algorithm fairness {
    fair process (Thread \in 1..NumThreads)
    variables
        state = 0;
    {
        Loop:
        while(TRUE){
            either {
                Set_1:
                state := 1;
            } or {
                Set_2:
                state := 2;

            } or {
                Set_3:
                state := 3;
            }
        }
        
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "a82a8aa7" /\ chksum(tla) = "f80343a8")
VARIABLES pc, state

vars == << pc, state >>

ProcSet == (1..NumThreads)

Init == (* Process Thread *)
        /\ state = [self \in 1..NumThreads |-> 0]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ \/ /\ pc' = [pc EXCEPT ![self] = "Set_1"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "Set_2"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "Set_3"]
              /\ state' = state

Set_1(self) == /\ pc[self] = "Set_1"
               /\ state' = [state EXCEPT ![self] = 1]
               /\ pc' = [pc EXCEPT ![self] = "Loop"]

Set_2(self) == /\ pc[self] = "Set_2"
               /\ state' = [state EXCEPT ![self] = 2]
               /\ pc' = [pc EXCEPT ![self] = "Loop"]

Set_3(self) == /\ pc[self] = "Set_3"
               /\ state' = [state EXCEPT ![self] = 3]
               /\ pc' = [pc EXCEPT ![self] = "Loop"]

Thread(self) == Loop(self) \/ Set_1(self) \/ Set_2(self) \/ Set_3(self)

Next == (\E self \in 1..NumThreads: Thread(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NumThreads : WF_vars(Thread(self))

\* END TRANSLATION 

\* We need to way to say that the either.. or block can't always just choose one branch
\* if the others are available, this is where fairness comes in. This example requires
\* strong fairness since we also can't just ping-pong between 2 actions if the third is also available
Fairness == /\ \A self \in 1..NumThreads: SF_vars(Loop(self) /\ pc' = [pc EXCEPT ![self] = "Set_1"])
            /\ \A self \in 1..NumThreads: SF_vars(Loop(self) /\ pc' = [pc EXCEPT ![self] = "Set_2"])
            /\ \A self \in 1..NumThreads: SF_vars(Loop(self) /\ pc' = [pc EXCEPT ![self] = "Set_3"])
FairnessSpec == Spec /\ Fairness

Eventually1 == \A self \in 1..NumThreads: <>(state[self] = 1)
Eventually2 == \A self \in 1..NumThreads: <>(state[self] = 2)
Eventually3 == \A self \in 1..NumThreads: <>(state[self] = 3)
====
