
// A "realistic" situation with limited retries, message loss, acceptor failures
test basicTest [main = BasicTest]: assert ElectionSafety, StateMachineSafety in (union Raft, FailureInjector, { BasicTest });
