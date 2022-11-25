/*
The failure injector machine randomly selects a replica machine and enqueues the special event "halt".
*/
event eDelayNodeFailure;
// event: event sent by the failure injector to shutdown a node
event eShutDown: machine;

machine FailureInjector {
  var nFailures: int;
  var nodes: set[machine];

  start state Init {
    entry (config: (nodes: set[machine], nFailures: int)) {
      nFailures = config.nFailures;
      nodes = config.nodes;
      assert nFailures < sizeof(nodes);
      goto FailOneNode;
    }
  }

  state FailOneNode {
    entry {
      var fail: machine;
      var failCount: int;
      var num: int;
      if(nFailures == 0)
        raise halt; // done with all failures
      else
      {
        if($)
        {
          num = choose(nFailures);
          // Modify failure injector to be able to halt multiple nodes at a time
          while(failCount < num){
              fail = choose(nodes);
              send fail, eShutDown, fail;
              nodes -= (fail);
              nFailures = nFailures - 1;
              failCount = failCount + 1;
          }
//          fail = choose(nodes);
//          send fail, eShutDown, fail;
//          nodes -= (fail);
//          nFailures = nFailures - 1;
////          goto FailOneNode;
        }
        else {
          send this, eDelayNodeFailure;
        }
      }
    }

    on eDelayNodeFailure goto FailOneNode;
  }
}

// function to create the failure injection
fun CreateFailureInjector(config: (nodes: set[machine], nFailures: int)) {
  new FailureInjector(config);
}

// failure injector module
module FailureInjector = { FailureInjector };