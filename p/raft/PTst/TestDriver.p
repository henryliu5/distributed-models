event eGetMachines: set[RaftMachine];
event eClientReq: int;
event eClientResp: bool;

fun setupRaft(sender: machine, numMachines: int) : set[RaftMachine]
{
    var machines: set[RaftMachine];
    var i: int;

    while(i < numMachines){
        machines += (new RaftMachine(sender));
        i = i + 1;
    }
    ReliableBroadCast(machines, eGetMachines, machines);
    return machines;
}

machine BasicTest {
    var numMessages: int;
    var timer: Timer;
    var machines: set[RaftMachine];
    start state Init{
        entry {
            numMessages = 3;
            machines = setupRaft(this, 3);
            timer = CreateTimer(this);
            StartTimer(timer);
        }

        on eTimeOut do {
            if(numMessages > 0){
                StartTimer(timer);
                ReliableBroadCast(machines, eClientReq, choose(10));

            }
        }

        on eClientResp do (status: bool) {
            numMessages = numMessages - 1;
            print format("our command was executed");
        }
    }

}