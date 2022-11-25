// type that represents the configuration of the system under test
type sysConfig = (
  numProposers: int,
  numAcceptors: int,
  failAcceptors: int,
  reliableMessages: bool,
  maxRetry: int // How many times a Proposer can restart
);

// function that creates the two phase commit system along with the machines in its
// environment (test harness)
fun SetUpPaxosSystem(config: sysConfig)
{
    var acceptors : set[Acceptor];
    var proposers: set[Proposer];
    var learner: Learner;
    var i : int;
    print format("setting up {0} acceptors", config.numAcceptors);
    learner = new Learner(config.numAcceptors);

    // create acceptors
    i = 0;
    while (i < config.numAcceptors) {
        acceptors += (new Acceptor((myId = i, learner = learner, reliableMessages = config.reliableMessages)));
        i = i + 1;
    }

    // create proposers
    i = 0;
    while (i < config.numProposers) {
        proposers += (new Proposer((acceptors = acceptors,
                                    proposerId = i,
                                    numProposers = config.numProposers,
                                    reliableMessages = config.reliableMessages,
                                    maxRetry = config.maxRetry)));
        i = i + 1;
    }

  // create the failure injector if we want to inject failures
    if(config.failAcceptors > 0) {
        CreateFailureInjector((nodes = acceptors, nFailures = config.failAcceptors));
    }
}

// Ideal world where there is no failures and no message loss
machine NoFailures {
    start state Init {
        entry {
            var config: sysConfig;
            config = (
                numProposers = 2,
                numAcceptors = 3,
                failAcceptors = 0, // failures must be < numAcceptors (assertion in FailureInjector)
                reliableMessages = true,
                maxRetry = 3
            );
            SetUpPaxosSystem(config);
        }
    }
}

// Ideal world where there is no failures and no message loss BUT there is unlimited retries
machine NoFailuresUnlimitedRetry {
    start state Init {
        entry {
            var config: sysConfig;
            config = (
                numProposers = 2,
                numAcceptors = 3,
                failAcceptors = 0, // failures must be < numAcceptors (assertion in FailureInjector)
                reliableMessages = true,
                maxRetry = -1
            );
            SetUpPaxosSystem(config);
        }
    }
}

// World where there is no message loss and less than half of machines can go down
 machine NoMessageLoss {
     start state Init {
         entry {
             var config: sysConfig;
             config = (
                 numProposers = 2,
                 numAcceptors = 5,
                 failAcceptors = 2, // failures must be < numAcceptors (assertion in FailureInjector)
                 reliableMessages = true,
                 maxRetry = 1
             );
             SetUpPaxosSystem(config);
         }
     }
 }

 // World where there is no message loss and more than than half of machines can go down
machine TooMuchFailure {
    start state Init {
        entry {
            var config: sysConfig;
            config = (
                numProposers = 3,
                numAcceptors = 5,
                failAcceptors = 4, // failures must be < numAcceptors (assertion in FailureInjector)
                reliableMessages = true,
                maxRetry = 1
            );
            SetUpPaxosSystem(config);
        }
    }
}


machine BasicTest {
    start state Init {
        entry {
            var config: sysConfig;
            config = (
                numProposers = 3,
                numAcceptors = 3,
                failAcceptors = 2, // failures must be < numAcceptors (assertion in FailureInjector)
                reliableMessages = false,
                maxRetry = 3
            );
            SetUpPaxosSystem(config);
        }
    }
}