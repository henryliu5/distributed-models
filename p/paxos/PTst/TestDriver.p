// type that represents the configuration of the system under test
type sysConfig = (
  numProposers: int,
  numAcceptors: int,
  failAcceptors: int,
  reliableMessages: bool
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
        proposers += (new Proposer((acceptors = acceptors, proposerId = i, numProposers = config.numProposers, reliableMessages = config.reliableMessages)));
        i = i + 1;
    }

//  // initialize the monitors (specifications)
//  InitializeTwoPhaseCommitSpecifications(config.numParticipants);
//
//  // create the coordinator
//  coordinator = new Coordinator(participants);
//
//  // create the clients
//  i = 0;
//  while(i < config.numClients)
//  {
//    new Client((coordinator = coordinator, n = config.numTransPerClient, id = i + 1));
//    i = i + 1;
//  }
//
  // create the failure injector if we want to inject failures
    if(config.failAcceptors > 0) {
        CreateFailureInjector((nodes = acceptors, nFailures = config.failAcceptors));
    }
}
//
//fun InitializeTwoPhaseCommitSpecifications(numParticipants: int) {
//  // inform the monitor the number of participants in the system
//  announce eMonitor_AtomicityInitialize, numParticipants;
//}
//
///*
//This machine creates the 3 participants, 1 coordinator, and 1 clients
//*/
//machine SingleClientNoFailure {
//  start state Init {
//    entry {
//      var config: t2PCConfig;
//
//      config = (numClients = 1,
//                      numParticipants = 3,
//                      numTransPerClient = 2,
//                      failParticipants = 0);
//
//            SetUpTwoPhaseCommitSystem(config);
//    }
//  }
//}
//
///*
//This machine creates the 3 participants, 1 coordinator, and 1 clients
//*/
//machine MultipleClientsNoFailure {
//  start state Init {
//    entry {
//      var config: t2PCConfig;
//      config =
//        (numClients = 2,
//        numParticipants = 3,
//        numTransPerClient = 2,
//        failParticipants = 0);
//
//        SetUpTwoPhaseCommitSystem(config);
//    }
//  }
//}
//
///*
//This machine creates the 3 participants, 1 coordinator, 1 Failure injector, and 2 clients
//*/
//machine MultipleClientsWithFailure {
//  start state Init {
//    entry {
//      var config: t2PCConfig;
//      config =
//        (numClients = 2,
//        numParticipants = 3,
//        numTransPerClient = 2,
//        failParticipants = 1);
//
//      SetUpTwoPhaseCommitSystem(config);
//    }
//  }
//}

machine NoFailures {
    start state Init {
        entry {
            var config: sysConfig;
            config = (
                numProposers = 2,
                numAcceptors = 3,
                failAcceptors = 0, // failures must be < numAcceptors (assertion in FailureInjector)
                reliableMessages = true
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
                reliableMessages = false
            );
            SetUpPaxosSystem(config);
        }
    }
}