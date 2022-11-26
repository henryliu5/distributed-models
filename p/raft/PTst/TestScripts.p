
// A "realistic" situation with limited retries, message loss, acceptor failures
test basicTest [main = BasicTest]: assert ElectionSafety, StateMachineSafety, LogMatching in (union Raft, FailureInjector, { BasicTest });
