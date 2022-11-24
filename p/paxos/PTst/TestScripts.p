//// checks that all events are handled correctly and also the local assertions in the P machines.
//test tcSingleClientNoFailure [main = SingleClientNoFailure]:
//  union Paxos, TwoPCClient, FailureInjector, { SingleClientNoFailure };
//
//// asserts the liveness monitor along with the default properties
//test tcMultipleClientsNoFailure [main = MultipleClientsNoFailure]:
//  assert AtomicityInvariant, Progress in
//    (union Paxos, TwoPCClient, FailureInjector, { MultipleClientsNoFailure });
//
//// asserts the liveness monitor along with the default properties
//test tcMultipleClientsWithFailure [main = MultipleClientsWithFailure]:
//  assert Progress in (union Paxos, TwoPCClient, FailureInjector, { MultipleClientsWithFailure });

test basicTest [main = BasicTest]: assert Progress, Integrity in (union Paxos, { BasicTest });