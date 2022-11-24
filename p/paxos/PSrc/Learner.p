// We assume there exists some distinguished learner
machine Learner {
    var numAcceptors: int;
    // acceptedIds[i] = j means Acceptor i accepted ballot ID j
    var acceptedIds: map[int, int];
    var idToValue: map[int, int];
    var decided: bool;
    var decidedVal: int;

    var idCount: map[int, int];
    var id: int;
    var i: int;
    start state Init {
        entry (numAcceptors_: int){
            numAcceptors = numAcceptors_;
            decided = false;
        }

        on eAccept do (acceptMsg: tAccept) {
            idToValue[acceptMsg.acceptedId] = acceptMsg.acceptedVal;
            acceptedIds[acceptMsg.acceptorId] = acceptMsg.acceptedId;

            // Reset this every single time just to be careful, pretty sure could do just do decrement of old (bound 0), increment of new
            idCount = default(map[int, int]);

            i = 0;
            // See if the a quorum of Acceptors accepted the same ballot ID
            while(i < numAcceptors){
                if(i in acceptedIds) {
                    id = acceptedIds[i];
                    if(id in idCount){
                        idCount[id] = idCount[id] + 1;
                    } else {
                        idCount[id] = 1;
                    }
                    print format("Seen id {0} {1} times, numAcceptors = {2}", id, idCount[id], numAcceptors);

                    if(2 * idCount[id] > numAcceptors){
                        if(decided && decidedVal != idToValue[id]){
                            assert false, format("Had consensus on {0} but changed mind to {1}", decidedVal, idToValue[id]);
                        }
                        // Woohoo got majority
                        decided = true;
                        decidedVal = idToValue[id];
                        announce eValueDecided, decidedVal;
                    }
                }
                i = i + 1;
            }
        }
    }
}