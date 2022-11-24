// Paxos module
module Paxos = union { Proposer, Acceptor, Learner }, Timer;