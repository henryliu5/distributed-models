
// A "realistic" situation with limited retries, message loss, acceptor failures
test basicTest [main = BasicTest]: assert Integrity in (union Paxos, FailureInjector, { BasicTest });

// Indeed, with guaranteed message delivery and no failures, consensus is always reached
test noFailures [main = NoFailures]: assert Integrity, AlwaysReachesConsensus in (union Paxos, FailureInjector, { NoFailures });
// Similarly, if there is no message loss and there are enough nodes that remain up, we have liveness
test noMessageLoss[main = NoMessageLoss]: assert Integrity, AlwaysReachesConsensus in (union Paxos, FailureInjector, { NoMessageLoss });


// Below are test cases that should FAIL.

// 1. AlwaysReachConsensus should be false if more than N/2 nodes go down
// However, its actually not false as often as you would imagine with the default P FailureInjector machine.
// I modified FailureInjector so that each time it is ready to send a failure, it nondeterministically picks some number of nodes to bring down
// By default each time it only takes down 1 node - there should be a schedule in which this causes a problem, but I wasn't able to find it
test tooMuchFailure[main = TooMuchFailure]: assert Integrity, AlwaysReachesConsensus in (union Paxos, FailureInjector, { TooMuchFailure });

// With unlimited retries, its actually not a guarantee that AlwaysReachesConsensus is true! However, this will almost always pass
// Have to do a lot of iterations with an unfair schedule (I used sch-portfolio)
test noFailuresUR [main = NoFailuresUnlimitedRetry]: assert Integrity, AlwaysReachesConsensus in (union Paxos, FailureInjector, { NoFailuresUnlimitedRetry });
