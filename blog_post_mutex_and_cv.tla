(* Copyright (C) 2020 Malte Skarupke

   This is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   See https://www.gnu.org/licenses/.  *)

-------------------------- MODULE blog_post_mutex_and_cv --------------------------

EXTENDS Integers, FiniteSets, Sequences
CONSTANTS WorkerProcs
CONSTANTS GeneratorProcs
CONSTANTS MaxNumLoops

(*
--algorithm futex_mutex
{
variables 
  mutex_index = 0;
  cv_index = 1;
  futexes = [i \in {mutex_index, cv_index} |-> [state |-> 0, sleepers |-> {}]];
  
  work_to_do = 0;
  num_work_started = 0;
  work_done = 0;
  all_done = {}

procedure futex_wait(index = 0, val = 0)
{
  check_state:
    if (futexes[index].state /= val)
        return;
    else
    {
        futexes[index].sleepers := futexes[index].sleepers \union {self};
      wait_for_wake:
        await ~ (self \in futexes[index].sleepers);
        return;
    };
}
procedure futex_wake_single(index = 0)
{
  check_for_sleepers:
    if (futexes[index].sleepers = {})
        return;
    else
    {
        with (x \in futexes[index].sleepers)
        {
            futexes[index].sleepers := futexes[index].sleepers \ {x};
        };
        return;
    };
}
procedure futex_wake_all(index = 0)
{
  futex_wake_all:
    futexes[index].sleepers := {};
    return;
}

procedure lock_mutex()
variable old_state = 0;
{
  exchange_lock:
    old_state := futexes[mutex_index].state;
    futexes[mutex_index].state := 1;
  check:
    if (old_state = 0)
    {
      return;
    };
  sleep_loop:
    while (TRUE)
    {
        old_state := futexes[mutex_index].state;
        futexes[mutex_index].state := 2;
      sleep_check:
        if (old_state = 0)
          return;
        else
          call futex_wait(mutex_index, 2);
    };
};
procedure unlock_mutex ()
variable old_state = 0;
{
  exchange_unlock:
    old_state := futexes[mutex_index].state;
    futexes[mutex_index].state := 0;
  check_if_sleeper:
    if (old_state = 2)
    {
        call futex_wake_single(mutex_index);
        return;
    }
    else
        return;
};
procedure cv_wait()
variable old_state = 0;
{
  cv_wait_start:
    old_state := futexes[cv_index].state;
    call unlock_mutex();
  cv_wait_sleep:
    call futex_wait(cv_index, old_state);
  cv_wait_relock:
    call lock_mutex();
    return;
};
procedure cv_signal()
{
  cv_signal_start:
    futexes[cv_index].state := futexes[cv_index].state + 1;
    call futex_wake_single(cv_index);
    return;
};
procedure cv_broadcast()
{
  cv_broadcast_start:
    futexes[cv_index].state := futexes[cv_index].state + 1;
    call futex_wake_all(cv_index);
    return;
};

procedure add_work()
{
  add_work_start:
    call lock_mutex();
  generate_work:
    work_to_do := work_to_do + 1;
    num_work_started := num_work_started + 1;
    call unlock_mutex();
  notify_worker:
    call cv_signal();
    return;
};

procedure broadcast_all_done()
{
  generator_all_done:
    call lock_mutex();
  notify_all_done:
    all_done := all_done \union {self};
    call unlock_mutex();
  broadcast_all_done:
    call cv_broadcast();
    return;
};

fair process (GeneratorProc \in GeneratorProcs)
variable num_loops = MaxNumLoops;
{
  generate_work_loop:-
    while (num_loops > 0)
    {
      num_loops := num_loops - 1;
      call add_work();
    };
    call broadcast_all_done();
}

fair process (WorkerProc \in WorkerProcs)
{
  work_loop:
    while (TRUE)
    {
      call lock_mutex();
    wait_for_work:
      while (work_to_do = 0 /\ all_done /= GeneratorProcs)
      {
        call cv_wait();
      };
    take_work:
      if (work_to_do /= 0)
      {
        work_to_do := work_to_do - 1;
        call unlock_mutex();
      }
      else
      {
        call unlock_mutex();
        goto worker_done;
      };
    do_work:
      work_done := work_done + 1;
    };
    worker_done: skip;
}

}
*)

\* BEGIN TRANSLATION
\* Label futex_wake_all of procedure futex_wake_all at line 51 col 5 changed to futex_wake_all_
\* Label broadcast_all_done of procedure broadcast_all_done at line 141 col 5 changed to broadcast_all_done_
\* Procedure variable old_state of procedure lock_mutex at line 56 col 10 changed to old_state_
\* Procedure variable old_state of procedure unlock_mutex at line 79 col 10 changed to old_state_u
\* Parameter index of procedure futex_wait at line 21 col 22 changed to index_
\* Parameter index of procedure futex_wake_single at line 34 col 29 changed to index_f
VARIABLES mutex_index, cv_index, futexes, work_to_do, num_work_started, 
          work_done, all_done, pc, stack, index_, val, index_f, index, 
          old_state_, old_state_u, old_state, num_loops

vars == << mutex_index, cv_index, futexes, work_to_do, num_work_started, 
           work_done, all_done, pc, stack, index_, val, index_f, index, 
           old_state_, old_state_u, old_state, num_loops >>

ProcSet == (GeneratorProcs) \cup (WorkerProcs)

Init == (* Global variables *)
        /\ mutex_index = 0
        /\ cv_index = 1
        /\ futexes = [i \in {mutex_index, cv_index} |-> [state |-> 0, sleepers |-> {}]]
        /\ work_to_do = 0
        /\ num_work_started = 0
        /\ work_done = 0
        /\ all_done = {}
        (* Procedure futex_wait *)
        /\ index_ = [ self \in ProcSet |-> 0]
        /\ val = [ self \in ProcSet |-> 0]
        (* Procedure futex_wake_single *)
        /\ index_f = [ self \in ProcSet |-> 0]
        (* Procedure futex_wake_all *)
        /\ index = [ self \in ProcSet |-> 0]
        (* Procedure lock_mutex *)
        /\ old_state_ = [ self \in ProcSet |-> 0]
        (* Procedure unlock_mutex *)
        /\ old_state_u = [ self \in ProcSet |-> 0]
        (* Procedure cv_wait *)
        /\ old_state = [ self \in ProcSet |-> 0]
        (* Process GeneratorProc *)
        /\ num_loops = [self \in GeneratorProcs |-> MaxNumLoops]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in GeneratorProcs -> "generate_work_loop"
                                        [] self \in WorkerProcs -> "work_loop"]

check_state(self) == /\ pc[self] = "check_state"
                     /\ IF futexes[index_[self]].state /= val[self]
                           THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ index_' = [index_ EXCEPT ![self] = Head(stack[self]).index_]
                                /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED futexes
                           ELSE /\ futexes' = [futexes EXCEPT ![index_[self]].sleepers = futexes[index_[self]].sleepers \union {self}]
                                /\ pc' = [pc EXCEPT ![self] = "wait_for_wake"]
                                /\ UNCHANGED << stack, index_, val >>
                     /\ UNCHANGED << mutex_index, cv_index, work_to_do, 
                                     num_work_started, work_done, all_done, 
                                     index_f, index, old_state_, old_state_u, 
                                     old_state, num_loops >>

wait_for_wake(self) == /\ pc[self] = "wait_for_wake"
                       /\ ~ (self \in futexes[index_[self]].sleepers)
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ index_' = [index_ EXCEPT ![self] = Head(stack[self]).index_]
                       /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                       work_to_do, num_work_started, work_done, 
                                       all_done, index_f, index, old_state_, 
                                       old_state_u, old_state, num_loops >>

futex_wait(self) == check_state(self) \/ wait_for_wake(self)

check_for_sleepers(self) == /\ pc[self] = "check_for_sleepers"
                            /\ IF futexes[index_f[self]].sleepers = {}
                                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ index_f' = [index_f EXCEPT ![self] = Head(stack[self]).index_f]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                       /\ UNCHANGED futexes
                                  ELSE /\ \E x \in futexes[index_f[self]].sleepers:
                                            futexes' = [futexes EXCEPT ![index_f[self]].sleepers = futexes[index_f[self]].sleepers \ {x}]
                                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ index_f' = [index_f EXCEPT ![self] = Head(stack[self]).index_f]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << mutex_index, cv_index, work_to_do, 
                                            num_work_started, work_done, 
                                            all_done, index_, val, index, 
                                            old_state_, old_state_u, old_state, 
                                            num_loops >>

futex_wake_single(self) == check_for_sleepers(self)

futex_wake_all_(self) == /\ pc[self] = "futex_wake_all_"
                         /\ futexes' = [futexes EXCEPT ![index[self]].sleepers = {}]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ index' = [index EXCEPT ![self] = Head(stack[self]).index]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << mutex_index, cv_index, work_to_do, 
                                         num_work_started, work_done, all_done, 
                                         index_, val, index_f, old_state_, 
                                         old_state_u, old_state, num_loops >>

futex_wake_all(self) == futex_wake_all_(self)

exchange_lock(self) == /\ pc[self] = "exchange_lock"
                       /\ old_state_' = [old_state_ EXCEPT ![self] = futexes[mutex_index].state]
                       /\ futexes' = [futexes EXCEPT ![mutex_index].state = 1]
                       /\ pc' = [pc EXCEPT ![self] = "check"]
                       /\ UNCHANGED << mutex_index, cv_index, work_to_do, 
                                       num_work_started, work_done, all_done, 
                                       stack, index_, val, index_f, index, 
                                       old_state_u, old_state, num_loops >>

check(self) == /\ pc[self] = "check"
               /\ IF old_state_[self] = 0
                     THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ old_state_' = [old_state_ EXCEPT ![self] = Head(stack[self]).old_state_]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "sleep_loop"]
                          /\ UNCHANGED << stack, old_state_ >>
               /\ UNCHANGED << mutex_index, cv_index, futexes, work_to_do, 
                               num_work_started, work_done, all_done, index_, 
                               val, index_f, index, old_state_u, old_state, 
                               num_loops >>

sleep_loop(self) == /\ pc[self] = "sleep_loop"
                    /\ old_state_' = [old_state_ EXCEPT ![self] = futexes[mutex_index].state]
                    /\ futexes' = [futexes EXCEPT ![mutex_index].state = 2]
                    /\ pc' = [pc EXCEPT ![self] = "sleep_check"]
                    /\ UNCHANGED << mutex_index, cv_index, work_to_do, 
                                    num_work_started, work_done, all_done, 
                                    stack, index_, val, index_f, index, 
                                    old_state_u, old_state, num_loops >>

sleep_check(self) == /\ pc[self] = "sleep_check"
                     /\ IF old_state_[self] = 0
                           THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ old_state_' = [old_state_ EXCEPT ![self] = Head(stack[self]).old_state_]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << index_, val >>
                           ELSE /\ /\ index_' = [index_ EXCEPT ![self] = mutex_index]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                            pc        |->  "sleep_loop",
                                                                            index_    |->  index_[self],
                                                                            val       |->  val[self] ] >>
                                                                        \o stack[self]]
                                   /\ val' = [val EXCEPT ![self] = 2]
                                /\ pc' = [pc EXCEPT ![self] = "check_state"]
                                /\ UNCHANGED old_state_
                     /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                     work_to_do, num_work_started, work_done, 
                                     all_done, index_f, index, old_state_u, 
                                     old_state, num_loops >>

lock_mutex(self) == exchange_lock(self) \/ check(self) \/ sleep_loop(self)
                       \/ sleep_check(self)

exchange_unlock(self) == /\ pc[self] = "exchange_unlock"
                         /\ old_state_u' = [old_state_u EXCEPT ![self] = futexes[mutex_index].state]
                         /\ futexes' = [futexes EXCEPT ![mutex_index].state = 0]
                         /\ pc' = [pc EXCEPT ![self] = "check_if_sleeper"]
                         /\ UNCHANGED << mutex_index, cv_index, work_to_do, 
                                         num_work_started, work_done, all_done, 
                                         stack, index_, val, index_f, index, 
                                         old_state_, old_state, num_loops >>

check_if_sleeper(self) == /\ pc[self] = "check_if_sleeper"
                          /\ IF old_state_u[self] = 2
                                THEN /\ /\ index_f' = [index_f EXCEPT ![self] = mutex_index]
                                        /\ old_state_u' = [old_state_u EXCEPT ![self] = Head(stack[self]).old_state_u]
                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_single",
                                                                                 pc        |->  Head(stack[self]).pc,
                                                                                 index_f   |->  index_f[self] ] >>
                                                                             \o Tail(stack[self])]
                                     /\ pc' = [pc EXCEPT ![self] = "check_for_sleepers"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ old_state_u' = [old_state_u EXCEPT ![self] = Head(stack[self]).old_state_u]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                     /\ UNCHANGED index_f
                          /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                          work_to_do, num_work_started, 
                                          work_done, all_done, index_, val, 
                                          index, old_state_, old_state, 
                                          num_loops >>

unlock_mutex(self) == exchange_unlock(self) \/ check_if_sleeper(self)

cv_wait_start(self) == /\ pc[self] = "cv_wait_start"
                       /\ old_state' = [old_state EXCEPT ![self] = futexes[cv_index].state]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock_mutex",
                                                                pc        |->  "cv_wait_sleep",
                                                                old_state_u |->  old_state_u[self] ] >>
                                                            \o stack[self]]
                       /\ old_state_u' = [old_state_u EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "exchange_unlock"]
                       /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                       work_to_do, num_work_started, work_done, 
                                       all_done, index_, val, index_f, index, 
                                       old_state_, num_loops >>

cv_wait_sleep(self) == /\ pc[self] = "cv_wait_sleep"
                       /\ /\ index_' = [index_ EXCEPT ![self] = cv_index]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                   pc        |->  "cv_wait_relock",
                                                                   index_    |->  index_[self],
                                                                   val       |->  val[self] ] >>
                                                               \o stack[self]]
                          /\ val' = [val EXCEPT ![self] = old_state[self]]
                       /\ pc' = [pc EXCEPT ![self] = "check_state"]
                       /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                       work_to_do, num_work_started, work_done, 
                                       all_done, index_f, index, old_state_, 
                                       old_state_u, old_state, num_loops >>

cv_wait_relock(self) == /\ pc[self] = "cv_wait_relock"
                        /\ /\ old_state' = [old_state EXCEPT ![self] = Head(stack[self]).old_state]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock_mutex",
                                                                    pc        |->  Head(stack[self]).pc,
                                                                    old_state_ |->  old_state_[self] ] >>
                                                                \o Tail(stack[self])]
                        /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
                        /\ pc' = [pc EXCEPT ![self] = "exchange_lock"]
                        /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                        work_to_do, num_work_started, 
                                        work_done, all_done, index_, val, 
                                        index_f, index, old_state_u, num_loops >>

cv_wait(self) == cv_wait_start(self) \/ cv_wait_sleep(self)
                    \/ cv_wait_relock(self)

cv_signal_start(self) == /\ pc[self] = "cv_signal_start"
                         /\ futexes' = [futexes EXCEPT ![cv_index].state = futexes[cv_index].state + 1]
                         /\ /\ index_f' = [index_f EXCEPT ![self] = cv_index]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_single",
                                                                     pc        |->  Head(stack[self]).pc,
                                                                     index_f   |->  index_f[self] ] >>
                                                                 \o Tail(stack[self])]
                         /\ pc' = [pc EXCEPT ![self] = "check_for_sleepers"]
                         /\ UNCHANGED << mutex_index, cv_index, work_to_do, 
                                         num_work_started, work_done, all_done, 
                                         index_, val, index, old_state_, 
                                         old_state_u, old_state, num_loops >>

cv_signal(self) == cv_signal_start(self)

cv_broadcast_start(self) == /\ pc[self] = "cv_broadcast_start"
                            /\ futexes' = [futexes EXCEPT ![cv_index].state = futexes[cv_index].state + 1]
                            /\ /\ index' = [index EXCEPT ![self] = cv_index]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_all",
                                                                        pc        |->  Head(stack[self]).pc,
                                                                        index     |->  index[self] ] >>
                                                                    \o Tail(stack[self])]
                            /\ pc' = [pc EXCEPT ![self] = "futex_wake_all_"]
                            /\ UNCHANGED << mutex_index, cv_index, work_to_do, 
                                            num_work_started, work_done, 
                                            all_done, index_, val, index_f, 
                                            old_state_, old_state_u, old_state, 
                                            num_loops >>

cv_broadcast(self) == cv_broadcast_start(self)

add_work_start(self) == /\ pc[self] = "add_work_start"
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock_mutex",
                                                                 pc        |->  "generate_work",
                                                                 old_state_ |->  old_state_[self] ] >>
                                                             \o stack[self]]
                        /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
                        /\ pc' = [pc EXCEPT ![self] = "exchange_lock"]
                        /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                        work_to_do, num_work_started, 
                                        work_done, all_done, index_, val, 
                                        index_f, index, old_state_u, old_state, 
                                        num_loops >>

generate_work(self) == /\ pc[self] = "generate_work"
                       /\ work_to_do' = work_to_do + 1
                       /\ num_work_started' = num_work_started + 1
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock_mutex",
                                                                pc        |->  "notify_worker",
                                                                old_state_u |->  old_state_u[self] ] >>
                                                            \o stack[self]]
                       /\ old_state_u' = [old_state_u EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "exchange_unlock"]
                       /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                       work_done, all_done, index_, val, 
                                       index_f, index, old_state_, old_state, 
                                       num_loops >>

notify_worker(self) == /\ pc[self] = "notify_worker"
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "cv_signal",
                                                                pc        |->  Head(stack[self]).pc ] >>
                                                            \o Tail(stack[self])]
                       /\ pc' = [pc EXCEPT ![self] = "cv_signal_start"]
                       /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                       work_to_do, num_work_started, work_done, 
                                       all_done, index_, val, index_f, index, 
                                       old_state_, old_state_u, old_state, 
                                       num_loops >>

add_work(self) == add_work_start(self) \/ generate_work(self)
                     \/ notify_worker(self)

generator_all_done(self) == /\ pc[self] = "generator_all_done"
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock_mutex",
                                                                     pc        |->  "notify_all_done",
                                                                     old_state_ |->  old_state_[self] ] >>
                                                                 \o stack[self]]
                            /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
                            /\ pc' = [pc EXCEPT ![self] = "exchange_lock"]
                            /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                            work_to_do, num_work_started, 
                                            work_done, all_done, index_, val, 
                                            index_f, index, old_state_u, 
                                            old_state, num_loops >>

notify_all_done(self) == /\ pc[self] = "notify_all_done"
                         /\ all_done' = (all_done \union {self})
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock_mutex",
                                                                  pc        |->  "broadcast_all_done_",
                                                                  old_state_u |->  old_state_u[self] ] >>
                                                              \o stack[self]]
                         /\ old_state_u' = [old_state_u EXCEPT ![self] = 0]
                         /\ pc' = [pc EXCEPT ![self] = "exchange_unlock"]
                         /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                         work_to_do, num_work_started, 
                                         work_done, index_, val, index_f, 
                                         index, old_state_, old_state, 
                                         num_loops >>

broadcast_all_done_(self) == /\ pc[self] = "broadcast_all_done_"
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "cv_broadcast",
                                                                      pc        |->  Head(stack[self]).pc ] >>
                                                                  \o Tail(stack[self])]
                             /\ pc' = [pc EXCEPT ![self] = "cv_broadcast_start"]
                             /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                             work_to_do, num_work_started, 
                                             work_done, all_done, index_, val, 
                                             index_f, index, old_state_, 
                                             old_state_u, old_state, num_loops >>

broadcast_all_done(self) == generator_all_done(self)
                               \/ notify_all_done(self)
                               \/ broadcast_all_done_(self)

generate_work_loop(self) == /\ pc[self] = "generate_work_loop"
                            /\ IF num_loops[self] > 0
                                  THEN /\ num_loops' = [num_loops EXCEPT ![self] = num_loops[self] - 1]
                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "add_work",
                                                                                pc        |->  "generate_work_loop" ] >>
                                                                            \o stack[self]]
                                       /\ pc' = [pc EXCEPT ![self] = "add_work_start"]
                                  ELSE /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast_all_done",
                                                                                pc        |->  "Done" ] >>
                                                                            \o stack[self]]
                                       /\ pc' = [pc EXCEPT ![self] = "generator_all_done"]
                                       /\ UNCHANGED num_loops
                            /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                            work_to_do, num_work_started, 
                                            work_done, all_done, index_, val, 
                                            index_f, index, old_state_, 
                                            old_state_u, old_state >>

GeneratorProc(self) == generate_work_loop(self)

work_loop(self) == /\ pc[self] = "work_loop"
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock_mutex",
                                                            pc        |->  "wait_for_work",
                                                            old_state_ |->  old_state_[self] ] >>
                                                        \o stack[self]]
                   /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
                   /\ pc' = [pc EXCEPT ![self] = "exchange_lock"]
                   /\ UNCHANGED << mutex_index, cv_index, futexes, work_to_do, 
                                   num_work_started, work_done, all_done, 
                                   index_, val, index_f, index, old_state_u, 
                                   old_state, num_loops >>

wait_for_work(self) == /\ pc[self] = "wait_for_work"
                       /\ IF work_to_do = 0 /\ all_done /= GeneratorProcs
                             THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "cv_wait",
                                                                           pc        |->  "wait_for_work",
                                                                           old_state |->  old_state[self] ] >>
                                                                       \o stack[self]]
                                  /\ old_state' = [old_state EXCEPT ![self] = 0]
                                  /\ pc' = [pc EXCEPT ![self] = "cv_wait_start"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "take_work"]
                                  /\ UNCHANGED << stack, old_state >>
                       /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                       work_to_do, num_work_started, work_done, 
                                       all_done, index_, val, index_f, index, 
                                       old_state_, old_state_u, num_loops >>

take_work(self) == /\ pc[self] = "take_work"
                   /\ IF work_to_do /= 0
                         THEN /\ work_to_do' = work_to_do - 1
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock_mutex",
                                                                       pc        |->  "do_work",
                                                                       old_state_u |->  old_state_u[self] ] >>
                                                                   \o stack[self]]
                              /\ old_state_u' = [old_state_u EXCEPT ![self] = 0]
                              /\ pc' = [pc EXCEPT ![self] = "exchange_unlock"]
                         ELSE /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock_mutex",
                                                                       pc        |->  "worker_done",
                                                                       old_state_u |->  old_state_u[self] ] >>
                                                                   \o stack[self]]
                              /\ old_state_u' = [old_state_u EXCEPT ![self] = 0]
                              /\ pc' = [pc EXCEPT ![self] = "exchange_unlock"]
                              /\ UNCHANGED work_to_do
                   /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                   num_work_started, work_done, all_done, 
                                   index_, val, index_f, index, old_state_, 
                                   old_state, num_loops >>

do_work(self) == /\ pc[self] = "do_work"
                 /\ work_done' = work_done + 1
                 /\ pc' = [pc EXCEPT ![self] = "work_loop"]
                 /\ UNCHANGED << mutex_index, cv_index, futexes, work_to_do, 
                                 num_work_started, all_done, stack, index_, 
                                 val, index_f, index, old_state_, old_state_u, 
                                 old_state, num_loops >>

worker_done(self) == /\ pc[self] = "worker_done"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << mutex_index, cv_index, futexes, 
                                     work_to_do, num_work_started, work_done, 
                                     all_done, stack, index_, val, index_f, 
                                     index, old_state_, old_state_u, old_state, 
                                     num_loops >>

WorkerProc(self) == work_loop(self) \/ wait_for_work(self)
                       \/ take_work(self) \/ do_work(self)
                       \/ worker_done(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ futex_wait(self)
                               \/ futex_wake_single(self)
                               \/ futex_wake_all(self) \/ lock_mutex(self)
                               \/ unlock_mutex(self) \/ cv_wait(self)
                               \/ cv_signal(self) \/ cv_broadcast(self)
                               \/ add_work(self) \/ broadcast_all_done(self))
           \/ (\E self \in GeneratorProcs: GeneratorProc(self))
           \/ (\E self \in WorkerProcs: WorkerProc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in GeneratorProcs : /\ WF_vars((pc[self] # "generate_work_loop") /\ GeneratorProc(self))
                                        /\ WF_vars(add_work(self))
                                        /\ WF_vars(broadcast_all_done(self))
                                        /\ WF_vars(futex_wait(self))
                                        /\ WF_vars(futex_wake_single(self))
                                        /\ WF_vars(lock_mutex(self))
                                        /\ WF_vars(unlock_mutex(self))
                                        /\ WF_vars(cv_signal(self))
                                        /\ WF_vars(futex_wake_all(self))
                                        /\ WF_vars(cv_broadcast(self))
        /\ \A self \in WorkerProcs : /\ WF_vars(WorkerProc(self))
                                     /\ WF_vars(lock_mutex(self))
                                     /\ WF_vars(cv_wait(self))
                                     /\ WF_vars(unlock_mutex(self))
                                     /\ WF_vars(futex_wait(self))
                                     /\ WF_vars(futex_wake_single(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


MutualExclusion == \A i, j \in WorkerProcs : 
                     (i # j) => ~ /\ pc[i] = "cs"
                                  /\ pc[j] = "cs"

Trying(i) == pc[i] \in { "exchange_lock", "check", "sleep_loop", "sleep_check", "check_state", "wait_for_wake" }

DeadlockFree == \A i \in WorkerProcs : 
                     Trying(i) ~> (\E j \in WorkerProcs : pc[j] = "cs")
                     
DeadlockFreedom == \A i \in WorkerProcs : 
                     pc[i] \in { "exchange_lock", "check", "sleep_loop",
                                 "sleep_check", "check_state", "wait_for_wake" }
                       ~> (\E j \in WorkerProcs : pc[j] = "cs")

WorkGetsTaken == work_to_do > 0 ~> work_to_do = 0
WorkGetsDone == <>(num_work_started = work_done)
AllFinish == all_done = GeneratorProcs ~> (\A i \in (WorkerProcs \union GeneratorProcs) : pc[i] = "Done")

=============================================================================
\* Modification History
\* Last modified Sun Oct 25 18:34:26 EDT 2020 by malte
\* Created Mon Oct 12 21:12:21 EDT 2020 by malte
