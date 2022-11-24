
machine Acceptor {
    // Largest ballot id received so far
    var maxId: int;
    // Ballot id that we accepted
    var acceptedId: int;
    // Value corresponding to the above ballot
    var acceptedValue: int;
    var myId: int;
    var learner: Learner;

    start state Init {
        entry (args: (myId: int, learner: Learner)){
            maxId = -1;
            acceptedId = -1;
            acceptedValue = -1;
            learner = args.learner;
            myId = args.myId;

            goto WaitForRequests;
        }
    }

    state WaitForRequests {
        // Prepare requests
        on ePrepare do (prepareMsg: tPrepare){
            // Received a prepare request that we didn't promise to ignore
            if(prepareMsg.ballotId > maxId){
                // Update the largest ID we've seen
                maxId = prepareMsg.ballotId;

                UnReliableSend(prepareMsg.proposer, ePromise, (ballotId = prepareMsg.ballotId, \
                                                     acceptedBallotId = acceptedId, \
                                                     acceptedVal = acceptedValue));
            }
            // Sending back a failure isn't really necessary, its a performance optimization
        }
        // Propose requests
        on ePropose do (proposeMsg: tPropose){
            if(proposeMsg.ballotId >= maxId){
                maxId = proposeMsg.ballotId;
                acceptedId = proposeMsg.ballotId;
                acceptedValue = proposeMsg.value;
                UnReliableSend(learner, eAccept, (acceptorId = myId, acceptedVal = acceptedValue));
            }
        }
    }
 }

