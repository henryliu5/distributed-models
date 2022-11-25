/**************************************************************************
Every received transaction from a client must be eventually responded back.
Note, the usage of hot and cold states.
***************************************************************************/
event eValueDecided: int;

// Once consensus is reached, the value should not change
spec Integrity observes eValueDecided {
    var observedValue: int;
    start state Init {
        on eValueDecided do (val: int) {
            observedValue = val;
            goto SeenValue;
        }
    }

    state SeenValue {
        on eValueDecided do (val: int) {
            assert observedValue == val, format("Previously decided on value {0}, but came to new consensus {1}", observedValue, val);
        }
    }
}

// This spec fails assertion if a value is ever decided
spec FailIfConsensus observes eValueDecided {
    start state Init {
        on eValueDecided do (val: int) {
            assert false, format("Consensus was reached during a behavior - is this expected?");
        }
    }
}

// This spec makes indecision a hot state
spec AlwaysReachesConsensus observes eValueDecided {
    start hot state WaitingForDecision {
        on eValueDecided goto ValueDecided;
    }

    cold state ValueDecided {
        ignore eValueDecided;
    }
}