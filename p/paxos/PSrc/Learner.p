// We assume there exists some distinguished learner
machine Learner {
    var numAcceptors: int;
    // acceptedValues[i] = j means Acceptor i accepted value j
    var acceptedValues: map[int, int];
    var decided: bool;
    var decidedVal: int;

    var valCount: map[int, int];
    var val: int;
    var i: int;
    start state Init {
        entry (numAcceptors_: int){
            numAcceptors = numAcceptors_;
            decided = false;
        }

        on eAccept do (acceptMsg: tAccept) {
            acceptedValues[acceptMsg.acceptorId] = acceptMsg.acceptedVal;

            // Reset this every single time just to be careful, pretty sure could do just do decrement of old (bound 0), increment of new
            valCount = default(map[int, int]);

            i = 0;
            while(i < numAcceptors){
                if(i in acceptedValues) {
                    val = acceptedValues[i];
                    if(val in valCount){
                        valCount[val] = valCount[val] + 1;
                    } else {
                        valCount[val] = 1;
                    }
                    print format("Seen val {0} {1} time, numAcceptors = {2}", val, valCount[val], numAcceptors);

                    if(2 * valCount[val] > numAcceptors){
                        if(decided && decidedVal != val){
                            assert false, format("Had consensus on {0} but changed mind to {1}", decidedVal, val);
                        }
                        // Woohoo got majority
                        decided = true;
                        decidedVal = val;
                    }
                }
                i = i + 1;
            }
        }
    }
}