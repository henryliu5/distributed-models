// Note: this does not model membership changes or log compaction

// RequestVote RPC - sent from candidate to everyone else
type tVoteReq = (term: int, candidate: RaftMachine, lastLogIndex: int, lastLogTerm: int);
event eVoteReq: tVoteReq;
type tVoteResp = (term: int, voteGranted: bool);
event eVoteResp: tVoteResp;

// AppendEntries RPC - sent from leaders to everyone else
type tAppendReq = (term: int, leader: RaftMachine, prevLogIndex: int, prevLogTerm: int, entries: seq[LogEntry], leaderCommit: int);
event eAppendReq: tAppendReq;
type tAppendResp = (follower: RaftMachine, term: int, success: bool);
event eAppendResp: tAppendResp;

type LogEntry = (command: int, term: int, executed: bool);

// A single server in Raft
// See Figure 2 in Raft paper for high-level overview of all states, "rules", RPCs
machine RaftMachine {
    // Need to know about other machines in cluster
    var otherMachines: set[RaftMachine];
    // Baked in here for convenience
    var client: machine;
    // For measuring the election timeout
    // NOTE: in this model there will be no retries - it makes modeling a bit more annoying and in the end,
    // what's the difference between all timeouts occurring/running out of retries and dropping a msg?
    var electionTimer: Timer;

    // Below is all state according to Figure 2, note in this model persistent/volatile doesn't actually matter
    // Persistent state
    var currentTerm: int;
    var votedFor: RaftMachine;
    var log: seq[LogEntry];

    // Volatile state for all servers
    var commitIndex: int;
    var lastApplied: int;

    // Volatile state on leaders
    var nextIndex: map[RaftMachine, int];
    var matchIndex: map[RaftMachine, int];

    // If we can apply log[lastApplied] to the state machine, do so
    fun checkApply(){
        while(commitIndex > lastApplied) {
            lastApplied = lastApplied + 1;
            log[lastApplied].executed = true;
            announce eApply, (index = lastApplied, command = log[lastApplied].command);
        }
    }

    // If someone has a higher term than us, we should become a follower
    fun checkTerm(otherTerm: int){
        if(otherTerm > currentTerm){
            currentTerm = otherTerm;
            // not explicit in paper: https://stackoverflow.com/questions/50425312/in-raft-distributed-consensus-what-do-i-set-votedfor-to
            votedFor = default(RaftMachine);
            goto Follower;
        }
    }

    start state Init {
        entry (client_: machine){
            client = client_;
            // Don't really need, just defaults anyways
            currentTerm = 0;
            votedFor = default(RaftMachine);
            commitIndex = 0;
            lastApplied = 0;
            electionTimer = CreateTimer(this);

            // The original paper has the log 1-indexed, I shall do the same just in case
            log += (0, default(LogEntry));
            assert sizeof(log) == 1;

            receive {
                // Learn about cluster so we can broadcast correctly later
                case eGetMachines: (allMachines: set[RaftMachine]) {
                    otherMachines = allMachines;
                    otherMachines -= (this);
                }
            }
            // All machines start in Follower state, an election timeout will allow for a leader to appear
            goto Follower;
        }
        ignore eClientReq;
    }

    var voteDecision: bool;
    var i: int;
    state Follower {
        entry {
            StartTimer(electionTimer);
        }

        // Respond to VoteRequest RPCs
        on eVoteReq do (voteReq: tVoteReq) {
            print format("{0} received votereq {1}, my term is {2}, votedFor {3}", this, voteReq, currentTerm, votedFor);
            voteDecision = false;
            // A little painful, but this says reply true if the candidate's log is at least as up to date as ours
            if(voteReq.term >= currentTerm &&
               (votedFor == default(RaftMachine) || votedFor == voteReq.candidate) &&
               (voteReq.lastLogTerm > log[sizeof(log) - 1].term ||
                    (voteReq.lastLogTerm == log[sizeof(log) - 1].term && voteReq.lastLogIndex >= sizeof(log) - 1)
               )){
                voteDecision = true;
                votedFor = voteReq.candidate;
                currentTerm = voteReq.term;
            }

            UnReliableSend(voteReq.candidate, eVoteResp, (term = currentTerm, voteGranted = voteDecision));
        }

        // Respond to AppendEntries RPCs
        on eAppendReq do (appendReq: tAppendReq) {
            CancelTimer(electionTimer);
            StartTimer(electionTimer);
            print format("request {0} log size {1} currentTerm {2}", appendReq, sizeof(log), currentTerm);
            if(appendReq.term < currentTerm ||
               appendReq.prevLogIndex >= sizeof(log) ||
               log[appendReq.prevLogIndex].term != appendReq.prevLogTerm) {
               // Reject leader's append
               UnReliableSend(appendReq.leader, eAppendResp, (follower = this, term = currentTerm, success = false));
            } else {

                // Not good for performance but easy to make sure its right
                // Clear out our log above prevLogIndex
                i = appendReq.prevLogIndex + 1;
                while(i < sizeof(log)){
                    log -= (i);
                }
                // Add in stuff sent to us
                i = 0;
                while(i < sizeof(appendReq.entries)){
                    log += (sizeof(log), appendReq.entries[i]);
                    i = i + 1;
                }
                announce eLogUpdate, (server = this, log = log);

                // Update my commit index, apply state machine updates if possible
                if(appendReq.leaderCommit > commitIndex){
                    commitIndex = min(appendReq.leaderCommit, sizeof(log) - 1);
                    checkApply();
                }
                // Agree to leader's append
                UnReliableSend(appendReq.leader, eAppendResp, (follower = this, term = currentTerm, success = true));
            }
            checkTerm(appendReq.term);
        }

        on eTimeOut goto Candidate;

        // Ignore client requests (for leader), and voting responses from the past
        ignore eClientReq, eVoteResp, eAppendResp;
    }

    var entries: seq[LogEntry];
    fun sendAppendEntryRPC(target: RaftMachine){
        print format("sending append rpc next index {0} {1}", nextIndex[target], target);
        // nextIndex[i] is the index at which it wants to start an append for follower i
        if(sizeof(log) - 1 >= nextIndex[target]){
            i = nextIndex[target];
            entries = default(seq[LogEntry]);
            while(i < sizeof(log)){
                entries += (sizeof(entries), log[i]);
                i = i + 1;
            }

            UnReliableSend(target, eAppendReq,
                                            (term = currentTerm,
                                             leader = this,
                                             prevLogIndex = nextIndex[target] - 1,
                                             prevLogTerm = log[nextIndex[target] - 1].term,
                                             entries = entries,
                                             leaderCommit = commitIndex
                                            ));
        }
    }

    var tryIndex: int;
    var matches: int;
    var otherMachine: RaftMachine;
    fun updateCommitIndex(){
        tryIndex = commitIndex;

        while(tryIndex < sizeof(log)){
            matches = 0;
            foreach(otherMachine in otherMachines){
                if(matchIndex[otherMachine] >= tryIndex) matches = matches + 1;
            }
            if(matches * 2 > sizeof(otherMachines) + 1 && log[tryIndex].term == currentTerm){
                commitIndex = tryIndex;
                send client, eClientResp, true;
            }

            tryIndex = tryIndex + 1;
        }
    }

    state Leader {
        // Not modeling periodic heartbeats, not necessary and probably not helpful in this context
        // since its just 1 state transition to a timeout anyways.
        entry {
            // Initialize nextIndex, matchIndex
            foreach(otherMachine in otherMachines){
                print format("nextIndex starting at {0}", sizeof(log));
                nextIndex[otherMachine] = sizeof(log); // just trying
                matchIndex[otherMachine] = 0; // actually written to follower
            }
            // Dummy heartbeat so everyone knows about this new leader
            UnReliableBroadCast(otherMachines, eAppendReq,
                (term = currentTerm,
                 leader = this,
                 prevLogIndex = 0,
                 prevLogTerm = 0,
                 entries = default(seq[LogEntry]),
                 leaderCommit = commitIndex));
        }

        on eClientReq do (command: int) {
            // Leader has master log
            log += (sizeof(log), (command = command, term = currentTerm, executed = false));
            announce eLogUpdate, (server = this, log = log);
            foreach(otherMachine in otherMachines){
                sendAppendEntryRPC(otherMachine);
            }
        }

        on eAppendResp do (resp: tAppendResp) {
            checkTerm(resp.term);
            if(resp.success){
                nextIndex[resp.follower] = sizeof(log);
                matchIndex[resp.follower] = sizeof(log);
                updateCommitIndex();
            } else {
                // Try again
                nextIndex[resp.follower] = nextIndex[resp.follower] - 1;
                print format ("{0} needing to retry for {1}, decremening nextIndex to {2}", this, resp.follower, nextIndex[resp.follower]);
                sendAppendEntryRPC(resp.follower);
            }
        }

        on eAppendReq do (req: tAppendReq) {
            checkTerm(req.term);
        }

        // Ignore everything related to a previous election
        ignore eVoteReq, eVoteResp, eTimeOut;
    }

    var votesReceived: int;
    state Candidate {
        entry {
            currentTerm = currentTerm + 1;
            votesReceived = 1; // vote for self
            CancelTimer(electionTimer);
            StartTimer(electionTimer);
            UnReliableBroadCast(otherMachines, eVoteReq, (term = currentTerm,
                                                          candidate = this,
                                                          lastLogIndex = sizeof(log) - 1,
                                                          lastLogTerm = log[sizeof(log) - 1].term));
        }

        on eVoteResp do (resp: tVoteResp) {
            print format("{0} current term {1}", this, currentTerm);
            checkTerm(resp.term);
            if(resp.voteGranted){
                votesReceived = votesReceived + 1;
                // Check if enough votes received
                if(votesReceived * 2 > sizeof(otherMachines) + 1){
                    announce eNewLeader, (leader = this, term = currentTerm);
                    goto Leader;
                }
            }
        }

        on eAppendReq goto Follower; // Someone else became leader, cede election
        on eTimeOut goto Candidate;

        ignore eVoteReq, eClientReq;
        ignore eAppendResp; // can happen if a really late message comes
    }
}

fun min(a: int, b: int) : int {
    if(a <= b) return a;
    return b;
}