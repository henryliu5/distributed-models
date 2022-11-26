event eNewLeader: (leader: RaftMachine, term: int);

spec ElectionSafety observes eNewLeader {
    var termToLeader: map[int, RaftMachine];
    // "At most one leader can be elected in a given term"
    start state Init {
        on eNewLeader do (p: (leader: RaftMachine, term: int)){
            if(p.term in termToLeader){
                assert termToLeader[p.term] == p.leader,
                    format("Both {0} and {1} elected as leader in term {2}", termToLeader[p.term], p.leader, p.term);
            }
            termToLeader[p.term] = p.leader;
        }
    }
}

event eLogUpdate: (server: RaftMachine, log: seq[LogEntry]);

spec LogMatching observes eLogUpdate {
    // "If two logs contain an entry with the same index and term, then the logs are
    //  identical in all entries up through the given index"
    // Tracks logs globally
    var logs: map[RaftMachine, seq[LogEntry]];

    start state Init {
        on eLogUpdate do (msg: (server: RaftMachine, log: seq[LogEntry])) {
            logs[msg.server] = msg.log;
            print format("got log update: {0} log is {1}", msg.server, msg.log);
        }
    }
}

event eApply: (index: int, command: int);

spec StateMachineSafety observes eApply {
    // "If a server has applied a log entry at a given index to its state machine,
    //  no other server will ever apply a different log entry for the same index
    var commands: map[int, int];
    start state Init {
        on eApply do (msg: (index: int, command: int)) {
            if(msg.index in commands){
                assert commands[msg.index] == msg.command, format("Executed command {0} and {1} at index {2}", commands[msg.index], msg.command, msg.index);
            }
            commands[msg.index] = msg.command;
        }
    }
}