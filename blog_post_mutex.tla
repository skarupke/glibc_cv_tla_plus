-------------------------- MODULE blog_post_mutex --------------------------

EXTENDS Integers, FiniteSets, Sequences
CONSTANTS NumProcs

Procs == 0 .. (NumProcs - 1)

(*
--algorithm futex_mutex
{
variables 
  futex_state = 0;
  futex_sleepers = {};

procedure futex_wait(val = 0)
{
  check_state:
    if (futex_state /= val)
        return;
    else
    {
        futex_sleepers := futex_sleepers \union {self};
      wait_for_wake:
        await ~ (self \in futex_sleepers);
        return;
    };
}
procedure futex_wake_single()
{
  check_for_sleepers:
    if (futex_sleepers = {})
        return;
    else
    {
        with (x \in futex_sleepers)
        {
            futex_sleepers := futex_sleepers \ {x};
        };
        return;
    };
}
procedure futex_wake_all()
{
  futex_wake_all:
    futex_sleepers := {};
    return;
}

procedure lock_mutex()
variable old_state = 0;
{
  exchange_lock:
    old_state := futex_state;
    futex_state := 1;
  check:
    if (old_state = 0)
    {
      return;
    };
  sleep_loop:
    while (TRUE)
    {
        old_state := futex_state;
        futex_state := 2;
      sleep_check:
        if (old_state = 0)
          return;
        else
          call futex_wait(2);
    };
};

procedure unlock_mutex ()
variable old_state = 0;
{
  exchange_unlock:
    old_state := futex_state;
    futex_state := 0;
  check_if_sleeper:
    if (old_state = 2)
    {
        call futex_wake_single();
        return;
    }
    else
        return;
}


fair process (WorkerProc \in Procs)
{
    start:- while (TRUE)
    {
      call lock_mutex();
      cs: skip;
      call unlock_mutex();
    }
}
}
*)

\* BEGIN TRANSLATION
\* Label futex_wake_all of procedure futex_wake_all at line 45 col 5 changed to futex_wake_all_
\* Procedure variable old_state of procedure lock_mutex at line 50 col 10 changed to old_state_
VARIABLES futex_state, futex_sleepers, pc, stack, val, old_state_, old_state

vars == << futex_state, futex_sleepers, pc, stack, val, old_state_, old_state
        >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ futex_state = 0
        /\ futex_sleepers = {}
        (* Procedure futex_wait *)
        /\ val = [ self \in ProcSet |-> 0]
        (* Procedure lock_mutex *)
        /\ old_state_ = [ self \in ProcSet |-> 0]
        (* Procedure unlock_mutex *)
        /\ old_state = [ self \in ProcSet |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start"]

check_state(self) == /\ pc[self] = "check_state"
                     /\ IF futex_state /= val[self]
                           THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED futex_sleepers
                           ELSE /\ futex_sleepers' = (futex_sleepers \union {self})
                                /\ pc' = [pc EXCEPT ![self] = "wait_for_wake"]
                                /\ UNCHANGED << stack, val >>
                     /\ UNCHANGED << futex_state, old_state_, old_state >>

wait_for_wake(self) == /\ pc[self] = "wait_for_wake"
                       /\ ~ (self \in futex_sleepers)
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << futex_state, futex_sleepers, old_state_, 
                                       old_state >>

futex_wait(self) == check_state(self) \/ wait_for_wake(self)

check_for_sleepers(self) == /\ pc[self] = "check_for_sleepers"
                            /\ IF futex_sleepers = {}
                                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                       /\ UNCHANGED futex_sleepers
                                  ELSE /\ \E x \in futex_sleepers:
                                            futex_sleepers' = futex_sleepers \ {x}
                                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << futex_state, val, old_state_, 
                                            old_state >>

futex_wake_single(self) == check_for_sleepers(self)

futex_wake_all_(self) == /\ pc[self] = "futex_wake_all_"
                         /\ futex_sleepers' = {}
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << futex_state, val, old_state_, 
                                         old_state >>

futex_wake_all(self) == futex_wake_all_(self)

exchange_lock(self) == /\ pc[self] = "exchange_lock"
                       /\ old_state_' = [old_state_ EXCEPT ![self] = futex_state]
                       /\ futex_state' = 1
                       /\ pc' = [pc EXCEPT ![self] = "check"]
                       /\ UNCHANGED << futex_sleepers, stack, val, old_state >>

check(self) == /\ pc[self] = "check"
               /\ IF old_state_[self] = 0
                     THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ old_state_' = [old_state_ EXCEPT ![self] = Head(stack[self]).old_state_]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "sleep_loop"]
                          /\ UNCHANGED << stack, old_state_ >>
               /\ UNCHANGED << futex_state, futex_sleepers, val, old_state >>

sleep_loop(self) == /\ pc[self] = "sleep_loop"
                    /\ old_state_' = [old_state_ EXCEPT ![self] = futex_state]
                    /\ futex_state' = 2
                    /\ pc' = [pc EXCEPT ![self] = "sleep_check"]
                    /\ UNCHANGED << futex_sleepers, stack, val, old_state >>

sleep_check(self) == /\ pc[self] = "sleep_check"
                     /\ IF old_state_[self] = 0
                           THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ old_state_' = [old_state_ EXCEPT ![self] = Head(stack[self]).old_state_]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ val' = val
                           ELSE /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                            pc        |->  "sleep_loop",
                                                                            val       |->  val[self] ] >>
                                                                        \o stack[self]]
                                   /\ val' = [val EXCEPT ![self] = 2]
                                /\ pc' = [pc EXCEPT ![self] = "check_state"]
                                /\ UNCHANGED old_state_
                     /\ UNCHANGED << futex_state, futex_sleepers, old_state >>

lock_mutex(self) == exchange_lock(self) \/ check(self) \/ sleep_loop(self)
                       \/ sleep_check(self)

exchange_unlock(self) == /\ pc[self] = "exchange_unlock"
                         /\ old_state' = [old_state EXCEPT ![self] = futex_state]
                         /\ futex_state' = 0
                         /\ pc' = [pc EXCEPT ![self] = "check_if_sleeper"]
                         /\ UNCHANGED << futex_sleepers, stack, val, 
                                         old_state_ >>

check_if_sleeper(self) == /\ pc[self] = "check_if_sleeper"
                          /\ IF old_state[self] = 2
                                THEN /\ /\ old_state' = [old_state EXCEPT ![self] = Head(stack[self]).old_state]
                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_single",
                                                                                 pc        |->  Head(stack[self]).pc ] >>
                                                                             \o Tail(stack[self])]
                                     /\ pc' = [pc EXCEPT ![self] = "check_for_sleepers"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ old_state' = [old_state EXCEPT ![self] = Head(stack[self]).old_state]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << futex_state, futex_sleepers, val, 
                                          old_state_ >>

unlock_mutex(self) == exchange_unlock(self) \/ check_if_sleeper(self)

start(self) == /\ pc[self] = "start"
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock_mutex",
                                                        pc        |->  "cs",
                                                        old_state_ |->  old_state_[self] ] >>
                                                    \o stack[self]]
               /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "exchange_lock"]
               /\ UNCHANGED << futex_state, futex_sleepers, val, old_state >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock_mutex",
                                                     pc        |->  "start",
                                                     old_state |->  old_state[self] ] >>
                                                 \o stack[self]]
            /\ old_state' = [old_state EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "exchange_unlock"]
            /\ UNCHANGED << futex_state, futex_sleepers, val, old_state_ >>

WorkerProc(self) == start(self) \/ cs(self)

Next == (\E self \in ProcSet:  \/ futex_wait(self)
                               \/ futex_wake_single(self)
                               \/ futex_wake_all(self) \/ lock_mutex(self)
                               \/ unlock_mutex(self))
           \/ (\E self \in Procs: WorkerProc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : /\ WF_vars((pc[self] # "start") /\ WorkerProc(self))
                               /\ WF_vars(lock_mutex(self))
                               /\ WF_vars(unlock_mutex(self))
                               /\ WF_vars(futex_wait(self))
                               /\ WF_vars(futex_wake_single(self))

\* END TRANSLATION


MutualExclusion == \A i, j \in Procs : 
                     (i # j) => ~ /\ pc[i] = "cs"
                                  /\ pc[j] = "cs"

Trying(i) == pc[i] \in { "exchange_lock", "check", "sleep_loop", "sleep_check", "check_state", "wait_for_wake" }

DeadlockFree == \A i \in Procs : 
                     Trying(i) ~> (\E j \in Procs : pc[j] = "cs")
                     
DeadlockFreedom == \A i \in Procs : 
                     pc[i] \in { "exchange_lock", "check", "sleep_loop",
                                 "sleep_check", "check_state", "wait_for_wake" }
                       ~> (\E j \in Procs : pc[j] = "cs")


=============================================================================
\* Modification History
\* Last modified Sun Oct 25 09:57:39 EDT 2020 by malte
\* Created Mon Oct 12 21:12:21 EDT 2020 by malte
