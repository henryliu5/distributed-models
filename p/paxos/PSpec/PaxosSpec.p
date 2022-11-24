/**************************************************************************
Every received transaction from a client must be eventually responded back.
Note, the usage of hot and cold states.
***************************************************************************/
event eValueDecided: int;

// Once consensus is reached, the value should not change (this is single-decree Paxos)
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
            assert false, format("Previously decided on value {0}, but came to new consensus {1}", observedValue, val);
        }
    }
}

spec Progress observes ePrepare, ePromise, ePropose, eAccept {
//  var pendingTransactions: int;
    start state Init {
//    on eWriteTransReq goto WaitForResponses with { pendingTransactions = pendingTransactions + 1; }
        ignore ePrepare, ePromise, ePropose, eAccept;
    }

//
//  hot state WaitForResponses
//  {
//    on eWriteTransResp do {
//      pendingTransactions = pendingTransactions - 1;
//      if(pendingTransactions == 0)
//      {
//        goto AllTransactionsFinished;
//      }
//    }
//
//    on eWriteTransReq do { pendingTransactions = pendingTransactions + 1; }
//  }
//
//  cold state AllTransactionsFinished {
//    on eWriteTransReq goto WaitForResponses with { pendingTransactions = pendingTransactions + 1; }
//  }
}
