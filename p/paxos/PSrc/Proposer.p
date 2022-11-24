// Sent by Proposer to Acceptor
type tPrepare = (proposer: Proposer, ballotId: int);
event ePrepare: tPrepare;

// Sent by Acceptor to Proposer
//type tPromise = (acceptorId: int, ballotId: int, acceptedBallotId: int, acceptedVal: int);
type tPromise = (ballotId: int, acceptedBallotId: int, acceptedVal: int);
event ePromise: tPromise;

// Sent by Proposer to Acceptor
type tPropose = (proposerId: Proposer, ballotId: int, value: int);
event ePropose: tPropose;

// Sent by Acceptor to Learner/Proposers
type tAccept = (acceptorId: int, acceptedVal: int);
event eAccept: tAccept;

machine Proposer
{
    var acceptors: set[Acceptor];

    var round: int;
    var proposerId: int;
    var curBallotId: int;
    var numProposers: int;
    var maxRetry: int;

    start state Init {
        // Set up initial state, who the acceptors are, which proposer are we
        entry (args : (acceptors: set[Acceptor], proposerId: int, numProposers: int)) {
            proposerId = args.proposerId;
            acceptors = args.acceptors;
            numProposers = args.numProposers;
            round = 0;
            curBallotId = proposerId;

            // Manually set the maximum retry limit
            maxRetry = -1;

            goto PreparePhase;
        }
    }

    // Phase 1A - broadcast messages to acceptors
    state PreparePhase {
        entry {
            curBallotId = proposerId + round * numProposers;
            // Next time increase the ballot id
            round = round + 1;
            if(round == maxRetry){
                raise halt;
            }

            UnReliableBroadCast(acceptors, ePrepare, (proposer = this, ballotId = curBallotId));
            goto WaitForPromises;
        }
    }

    var receivedPromises: int;
    // This is how we track if an Acceptor sent back a promise saying it had already accepted something
    var largestAcceptedBallotId: int;
    var sendValue: int;

    // Collect promises from the Acceptors
    state WaitForPromises {
        entry {
            // TODO Start timer?
            receivedPromises = 0;
            largestAcceptedBallotId = -1;
            // Just some random value we want to propose, for each round of ballots this is different
            sendValue = curBallotId * -100;
        }

        // An Acceptor responded saying it can accept our value
        on ePromise do (promise: tPromise){
            if(promise.ballotId == curBallotId){
                // Count the number of promises for us
                receivedPromises = receivedPromises + 1;

                if(promise.acceptedBallotId > largestAcceptedBallotId){
                    largestAcceptedBallotId = promise.acceptedBallotId;
                    sendValue = promise.acceptedVal;
                }

                if(receivedPromises * 2 > sizeof(acceptors)){
                    // Reached a majority
                    UnReliableBroadCast(acceptors, ePropose, (proposer = this, ballotId = curBallotId, value = sendValue));
                    goto PreparePhase;
                }
            }
        }
    }
}



