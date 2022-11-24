
machine Acceptor {
    // Largest ballot id received so far
    var maxId: int;
    // Ballot id that we accepted
    var acceptedId: int;
    // Value corresponding to the above ballot
    var acceptedValue: int;
    var myId: int;
    var learner: Learner;
    var reliableMessages: bool;

    start state Init {
        entry (args: (myId: int, learner: Learner, reliableMessages: bool)){
            maxId = -1;
            acceptedId = -1;
            acceptedValue = -1;
            learner = args.learner;
            myId = args.myId;
            reliableMessages = args.reliableMessages;

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

                if(reliableMessages){
                    send prepareMsg.proposer, ePromise, (acceptor = this, \
                                                         ballotId = prepareMsg.ballotId, \
                                                         acceptedBallotId = acceptedId, \
                                                         acceptedVal = acceptedValue);
                } else {
                    UnReliableSend(prepareMsg.proposer, ePromise, (acceptor = this, \
                                                         ballotId = prepareMsg.ballotId, \
                                                         acceptedBallotId = acceptedId, \
                                                         acceptedVal = acceptedValue));
                }
            }
            // Sending back a failure isn't really necessary, its a performance optimization
        }
        // Propose requests
        on ePropose do (proposeMsg: tPropose){
            if(proposeMsg.ballotId >= maxId){
                maxId = proposeMsg.ballotId;
                acceptedId = proposeMsg.ballotId;
                acceptedValue = proposeMsg.value;
                print format("Acceptor_id {0} accepted proposal ballot_id {1}, value {2}", myId, acceptedId, acceptedValue);
                // Tell learner about our decision
                if(reliableMessages){
                    send learner, eAccept, (acceptorId = myId, acceptedId = acceptedId, acceptedVal = acceptedValue);
                } else {
                    UnReliableSend(learner, eAccept, (acceptorId = myId, acceptedId = acceptedId, acceptedVal = acceptedValue));
                }
            }
        }

        on eShutDown do {
            raise halt;
        }
    }
 }

