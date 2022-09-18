(* Copyright (C) 2022 Malte Skarupke

   This is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   See https://www.gnu.org/licenses/.  *)

-------------------------- MODULE ocaml_mutex --------------------------

EXTENDS Integers, FiniteSets, Sequences
CONSTANT Procs
CONSTANT UseSpinlockForMutex
CONSTANT UseSpinlockForCVMutex
CONSTANT UsePatch
CONSTANT AlwaysSetGRefs
CONSTANT MaxNumLoops

Bit(i) == 2 ^ i
ClearBit(i, b) == (i % Bit(b)) + (i \div Bit(b+1)) * Bit(b+1)
SetBit(i, b) == ClearBit(i, b) + Bit(b)
Xor1(i) == IF (i % 2) = 0 THEN i + 1 ELSE i - 1

AllProcs == Procs

(*
--algorithm lll_mutex_and_cv
{
variables 
  mutex_index = 0;
  g1_orig_size_index = 1;
  wrefs_index = 2;
  g_signals_index = [i \in {0,1} |-> i + 3];
  g_refs_index = [i \in {0,1} |-> i + 5];
  futexes = [i \in {mutex_index, g1_orig_size_index, wrefs_index, g_signals_index[0], g_signals_index[1], g_refs_index[0], g_refs_index[1]}
              |-> [state |-> 0, sleepers |-> {}]];
  wseq = 0;
  g1_start = 0;
  g_size = [i \in {0, 1} |-> 0];
  
  did_switch_g1 = [i \in AllProcs |-> FALSE];
  g1index = [i \in AllProcs |-> 0];
  
  waiters = 0;
  busy = FALSE;
    
  spinlock_locked = FALSE;
  cv_spinlock_locked = FALSE;

procedure futex_wait(wait_index = 0, val = 0)
{
  check_state:
    if (futexes[wait_index].state /= val)
    {
        return;
    }
    else
    {
        val := 0;
        futexes[wait_index].sleepers := futexes[wait_index].sleepers \union {self};
      wait_for_wake:
        await ~ (self \in futexes[wait_index].sleepers);
        return;
    };
}
procedure futex_wake_single(wake_index = 0)
{
  check_for_sleepers:
    if (futexes[wake_index].sleepers = {})
    {
        return;
    }
    else
    {
        with (x \in futexes[wake_index].sleepers)
        {
            futexes[wake_index].sleepers := futexes[wake_index].sleepers \ {x};
        };
        return;
    };
}

procedure futex_wake_all(wake_all_index = 0)
{
  futex_wake_all:
    futexes[wake_all_index].sleepers := {};
    return;
}

procedure lock_mutex()
variable old_state = 0;
{
lock_mutex_start:
  if (UseSpinlockForMutex)
  {
    await ~spinlock_locked;
    spinlock_locked := TRUE;
    return;
  }
  else
  {
    if (futexes[mutex_index].state = 0)
    {
      futexes[mutex_index].state := 1;
      return;
    };
  lll_lock_wait:
    if (futexes[mutex_index].state = 2)
    {
        goto futex_wait;
    };
  exchange_lock:
    while (TRUE)
    {
        old_state := futexes[mutex_index].state;
        futexes[mutex_index].state := 2;
      check_for_locked:
        if (old_state = 0)
        {
            return;
        }
        else
        {
            old_state := 0;
        };
      futex_wait:
        call futex_wait(mutex_index, 2);
    };
  }
};

procedure unlock_mutex ()
variable old_state = 0;
{
unlock_mutex_start:
  if (UseSpinlockForMutex)
  {
    spinlock_locked := FALSE;
    return;
  }
  else
  {
    old_state := futexes[mutex_index].state;
    futexes[mutex_index].state := 0;
  check_if_sleeper:
    if (old_state > 1)
    {
      call futex_wake_single(mutex_index);
      return;
    }
    else
    {
      return;
    };
  };
}

procedure condvar_dec_grefs(g = 0)
{
dec_refs:
  futexes[g_refs_index[g]].state := futexes[g_refs_index[g]].state - 2;
  if (futexes[g_refs_index[g]].state = 1)
  {
  clear_wake_up_flag:
    futexes[g_refs_index[g]].state := ClearBit(futexes[g_refs_index[g]].state, 0);
    call futex_wake_all(g_refs_index[g]);
    return;
  }
  else
  {
  done_with_dec_refs:
    return;
  }
}

procedure condvar_acquire_lock()
variable orig_size = 0;
{
cv_acquire_lock:
  if (UseSpinlockForCVMutex)
  {
    await ~cv_spinlock_locked;
    cv_spinlock_locked := TRUE;
    return;
  }
  else
  {
    orig_size := futexes[g1_orig_size_index].state;
  cv_acquire_unlocked:
    while ((orig_size % 4) = 0)
    {
    cv_acquire_lock_exchange:
      if (futexes[g1_orig_size_index].state = orig_size)
      {
        futexes[g1_orig_size_index].state := SetBit(orig_size, 0);
        return;
      }
      else
        orig_size := futexes[g1_orig_size_index].state;
    };
  cv_acquire_lock_sleep_loop:
    while (TRUE)
    {
    cv_acquire_lock_loop_to_set_sleeper:
      while ((orig_size % 4) /= 2)
      {
      cv_acquire_lock_exchange_2:
        if (futexes[g1_orig_size_index].state = orig_size)
        {
          futexes[g1_orig_size_index].state := SetBit(ClearBit(orig_size, 0), 1);

          if ((orig_size % 4) = 0)
          {
            return;
          }
          else
          {
            goto cv_acquire_lock_sleeper_flag_set;
          };
        }
        else
        {
          orig_size := futexes[g1_orig_size_index].state;
        };
      };
    cv_acquire_lock_sleeper_flag_set:
      call futex_wait(g1_orig_size_index, SetBit(ClearBit(orig_size, 0), 1));
    cv_acquire_re_read_state:
      orig_size := futexes[g1_orig_size_index].state;
    };
  };
};

procedure condvar_release_lock()
variable old_state = 0;
{
cv_release_lock:
  if (UseSpinlockForCVMutex)
  {
    cv_spinlock_locked := FALSE;
    return;
  }
  else
  {
    old_state := futexes[g1_orig_size_index].state;
    futexes[g1_orig_size_index].state := ClearBit(ClearBit(old_state, 0), 1);
  cv_release_lock_maybe_notify:
    if ((old_state % 4) > 1)
    {
      old_state := 0;
      call futex_wake_single(g1_orig_size_index);
    }
    else
    {
      old_state := 0;
    };
  cv_release_lock_done:
    return;
  };
}

procedure condvar_quiesce_and_switch_g1(local_wseq = 0, g1 = 0)
variables old_orig_size = 0;
          old_g1_start = 0;
          r = 0;
          s = 0;
{
quiesce_and_switch_start:
  g1index[self] := g1;
  old_orig_size := futexes[g1_orig_size_index].state \div 4;
quiesce_and_switch_start2:
  old_g1_start := g1_start \div 2;
quiesce_and_switch_check_for_no_reader:
  if (((local_wseq - old_g1_start - old_orig_size) + g_size[Xor1(g1)]) = 0)
  {
    did_switch_g1[self] := FALSE;
    return;
  };
close_signal_g1:
  futexes[g_signals_index[g1]].state := SetBit(futexes[g_signals_index[g1]].state, 0);
wait_for_no_refs:
  r := futexes[g_refs_index[g1]].state;
wait_for_no_refs_loop:
  while ((r \div 2) > 0)
  {
  wait_for_no_refs_fetch_or:
    futexes[g_refs_index[g1]].state := SetBit(futexes[g_refs_index[g1]].state, 0);
    r := futexes[g_refs_index[g1]].state;
  wait_for_no_refs_maybe_sleep:
    if ((r \div 2) > 0)
    {
      call futex_wait(g_refs_index[g1], r);
    };
  wait_for_no_refs_reload:
    r := futexes[g_refs_index[g1]].state;
  };
quiesce_update_g1_start:
  g1_start := g1_start + (old_orig_size * 2) + (IF g1 = 1 THEN 1 ELSE -1);
quiesce_reopen_group:
  futexes[g_signals_index[g1]].state := 0;
quiesce_flip_wseq:
  wseq := Xor1(wseq);
  local_wseq := wseq \div 2;
quiesce_flip_g1:
  g1 := Xor1(g1);
  g1index[self] := Xor1(g1index[self]);
quiesce_update_orig_size:
  old_orig_size := local_wseq - (old_g1_start + old_orig_size);
  s := (futexes[g1_orig_size_index].state % 4) + (old_orig_size * 4);
  r := futexes[g1_orig_size_index].state;
  futexes[g1_orig_size_index].state := s;
quiesce_check_orig_size:
  if ((r % 4) /= (s % 4))
  {
    futexes[g1_orig_size_index].state := (old_orig_size * 4) + 2;
  };

quiesce_update_size:
  g_size[g1] := g_size[g1] + old_orig_size;
  did_switch_g1[self] := g_size[g1] /= 0;
  return;
}

procedure cv_wait()
variables local_wseq = 0;
          g = 0;
          seq = 0;
          signals = 0;
          local_g1_start = 0;
{
cv_wait_fetch_seq:
  local_wseq := wseq;
  wseq := wseq + 2;
  g := local_wseq % 2;
  seq := local_wseq \div 2;
cv_wait_incr_wrefs:
  futexes[wrefs_index].state := futexes[wrefs_index].state + 8;
    cv_wait_incr_grefs:
      if (AlwaysSetGRefs)
      {
        futexes[g_refs_index[g]].state := futexes[g_refs_index[g]].state + 2;
      };
  call unlock_mutex();
  
cv_wait_load_signals:
  signals := futexes[g_signals_index[g]].state;
cv_wait_loop:
  while (TRUE)
  {
  cv_wait_inner_loop:
    while (TRUE)
    {
    cv_wait_spin_wait:
      if (signals = 0)
      {
        if (seq < (g1_start \div 2))
        {
          goto cv_wait_done
        };
      cv_wait_reload_signals:
        signals := futexes[g_signals_index[g]].state;
      };
    cv_wait_check_group_closed:
      if ((signals % 2) = 1)
      {
        goto cv_wait_done
      }
      else if (signals /= 0)
      {
        goto cv_wait_inner_loop_done;
      };
      
    cv_wait_prepare_to_block:
      if (~AlwaysSetGRefs)
      {
        futexes[g_refs_index[g]].state := futexes[g_refs_index[g]].state + 2;
      };
    cv_wait_check_for_closed_group:
      if ((futexes[g_signals_index[g]].state % 2) = 1 \/ seq < (g1_start \div 2))
      {
        if (~AlwaysSetGRefs)
        {
          call condvar_dec_grefs(g);
        goto cv_wait_done;
        }
        else
        {
        goto cv_wait_done;
        };
      }
      else
      {
        call futex_wait(g_signals_index[g], 0);
      };
    cv_wait_after_woken_up_dec_grefs:
      if (~AlwaysSetGRefs)
      {
        call condvar_dec_grefs(g);
      };
    cv_wait_after_woken_up_reload_signals:
      signals := futexes[g_signals_index[g]].state;
    };
  cv_wait_inner_loop_done:
    if (futexes[g_signals_index[g]].state = signals)
    {
      futexes[g_signals_index[g]].state := signals - 2;
      goto cv_wait_outer_loop_done;
    }
    else
      signals := futexes[g_signals_index[g]].state;
  };
cv_wait_outer_loop_done:
  local_g1_start := g1_start;
  if (seq < (g1_start \div 2) /\ (local_g1_start % 2) /= g)
  {
  cv_wait_potential_steal:
    signals := futexes[g_signals_index[g]].state;
  cv_wait_potential_steal_loop:
    while (g1_start = local_g1_start)
    {
      if (signals % 2 /= 0)
      {
        goto cv_wait_after_steal_wake;
      };

    cv_wait_potential_steal_cmp_exchg:
      if (futexes[g_signals_index[g]].state = signals)
      {
        futexes[g_signals_index[g]].state := signals + 2;
        goto cv_wait_after_steal_wake;
      }
      else
      {
        signals := futexes[g_signals_index[g]].state;
      };
    };
  cv_wait_after_steal_wake:
    call futex_wake_single(g_signals_index[g]);
  cv_wait_after_steal_patch:
    if (UsePatch)
    {
      call cv_broadcast();
    };
  };
  
cv_wait_done:
      if (AlwaysSetGRefs)
      {
        call condvar_dec_grefs(g);
      };
    cv_wait_after_done_dec_grefs:
  futexes[wrefs_index].state := futexes[wrefs_index].state - 8;
  if (futexes[wrefs_index].state \div 4 = 1)
  {
    call futex_wake_all(wrefs_index);
  };
  
cv_wait_retake_mutex:
  call lock_mutex();
  
  return;
}

procedure cv_signal()
variables local_wseq = 0;
          g1 = 0;
          do_futex_wake = FALSE;
{
check_for_waiters:
  if (futexes[wrefs_index].state \div 8 = 0)
  {
    return;
  }
  else
  {
    call condvar_acquire_lock();
  };

cv_signal_load_wseq:
  local_wseq := wseq \div 2;
  g1 := Xor1(wseq % 2);

cv_signal_check_size:
  if (g_size[g1] = 0)
  {
    call condvar_quiesce_and_switch_g1(local_wseq, g1);
  cv_signal_after_switch:
    g1 := g1index[self];
  cv_signal_check_for_early_out:
    if (~did_switch_g1[self])
    {
      call condvar_release_lock();
      return;
      (*goto cv_signal_release_lock;*)
    };
  };
cv_signal_add_signal:
  futexes[g_signals_index[g1]].state := futexes[g_signals_index[g1]].state + 2;
cv_signal_decrease_size:
  g_size[g1] := g_size[g1] - 1;
  do_futex_wake := TRUE;
  
(*cv_signal_release_lock:*)
  call condvar_release_lock();
  
cv_signal_maybe_wake:
  if (do_futex_wake)
  {
    call futex_wake_single(g_signals_index[g1]);
    return;
  }
  else
  {
    return;
  };
}

procedure cv_broadcast()
variables local_wseq = 0;
          g1 = 0;
          do_futex_wake = FALSE;
{
check_for_waiters:
  if (futexes[wrefs_index].state \div 8 = 0)
  {
    return;
  }
  else
  {
    call condvar_acquire_lock();
  };

cv_broadcast_load_wseq:
  local_wseq := wseq \div 2;
  g1 := Xor1(wseq % 2);
  
cv_broacast_check_size1:
  if (g_size[g1] /= 0)
  {
  cv_broadcast_signal_g1:
    futexes[g_signals_index[g1]].state := futexes[g_signals_index[g1]].state + (g_size[g1] * 2);
  cv_broadcast_clear_size1:
    g_size[g1] := 0;
    call futex_wake_all(g_signals_index[g1]);
  };

cv_broadcast_switch_g1:
  call condvar_quiesce_and_switch_g1(local_wseq, g1);
cv_broadcast_after_switch:
  g1 := g1index[self];
  if (did_switch_g1[self])
  {
  cv_broadcast_signal_g2:
    futexes[g_signals_index[g1]].state := futexes[g_signals_index[g1]].state + (g_size[g1] * 2);
  cv_broadcast_clear_size2:
    g_size[g1] := 0;
    do_futex_wake := TRUE;
  };
  
cv_broadcast_release_lock:
  call condvar_release_lock();
  
cv_broadcast_maybe_wake:
  if (do_futex_wake)
  {
    call futex_wake_all(g_signals_index[g1]);
    return;
  }
  else
  {
    return;
  };
}

procedure acquire_masterlock()
{
acquire_masterlock_start:
  call lock_mutex();
acquire_masterlock_loop:
  while (busy)
  {
    waiters := waiters + 1;
    call cv_wait();
  acquire_lock_after_wait:
    waiters := waiters - 1;
  };
acquire_masterlock_after_loop:
  busy := TRUE;
  call unlock_mutex();
  return;
}

procedure release_masterlock()
{
release_masterlock_start:
  call lock_mutex();
release_masterlock_after_lock:
  busy := FALSE;
  call unlock_mutex();
release_masterlock_signal:
  call cv_signal();
  return;
};

procedure yield_masterlock()
{
yield_start:
  call lock_mutex();
yield_after_lock:
  if (waiters = 0)
  {
    call unlock_mutex();
    return;
  };
yield_after_waiter_check:
  busy := FALSE;
  call cv_signal();
yield_after_signal:
  waiters := waiters + 1;
yield_loop:
  while (TRUE)
  {
    call cv_wait();
    yield_after_wait:
    if (~busy)
      goto yield_after_loop;
  };
yield_after_loop:
  busy := TRUE;
yield_dec_waiters:
  waiters := waiters - 1;
yield_done:
  call unlock_mutex();
  return;
};

fair process (Proc \in Procs)
variable num_loops = MaxNumLoops;
{
proc_start:
  while (num_loops > 0)
  {
    num_loops := num_loops - 1;
    either
    {
      call acquire_masterlock();
    }
    or
    {
      goto proc_done;
    };
    (*proc_loop:
    while (num_loops > 0)
    {
      either
      {
        num_loops := num_loops - 1;
        call yield_masterlock();
      }
      or
      {
        goto proc_loop_done;
      }
    };*)
    proc_loop_done:
    call release_masterlock();
  };
proc_done:
  skip;
}
}
*)

\* BEGIN TRANSLATION (chksum(pcal) = "7a1daec4" /\ chksum(tla) = "5710279e")
\* Label futex_wake_all of procedure futex_wake_all at line 87 col 5 changed to futex_wake_all_
\* Label futex_wait of procedure lock_mutex at line 128 col 9 changed to futex_wait_
\* Label check_for_waiters of procedure cv_signal at line 471 col 3 changed to check_for_waiters_
\* Procedure variable old_state of procedure lock_mutex at line 92 col 10 changed to old_state_
\* Procedure variable old_state of procedure unlock_mutex at line 134 col 10 changed to old_state_u
\* Procedure variable local_wseq of procedure cv_wait at line 326 col 11 changed to local_wseq_
\* Procedure variable g of procedure cv_wait at line 327 col 11 changed to g_
\* Procedure variable local_wseq of procedure cv_signal at line 466 col 11 changed to local_wseq_c
\* Procedure variable g1 of procedure cv_signal at line 467 col 11 changed to g1_
\* Procedure variable do_futex_wake of procedure cv_signal at line 468 col 11 changed to do_futex_wake_
\* Procedure variable local_wseq of procedure cv_broadcast at line 520 col 11 changed to local_wseq_cv
\* Procedure variable g1 of procedure cv_broadcast at line 521 col 11 changed to g1_c
VARIABLES mutex_index, g1_orig_size_index, wrefs_index, g_signals_index, 
          g_refs_index, futexes, wseq, g1_start, g_size, did_switch_g1, 
          g1index, waiters, busy, spinlock_locked, cv_spinlock_locked, pc, 
          stack, wait_index, val, wake_index, wake_all_index, old_state_, 
          old_state_u, g, orig_size, old_state, local_wseq, g1, old_orig_size, 
          old_g1_start, r, s, local_wseq_, g_, seq, signals, local_g1_start, 
          local_wseq_c, g1_, do_futex_wake_, local_wseq_cv, g1_c, 
          do_futex_wake, num_loops

vars == << mutex_index, g1_orig_size_index, wrefs_index, g_signals_index, 
           g_refs_index, futexes, wseq, g1_start, g_size, did_switch_g1, 
           g1index, waiters, busy, spinlock_locked, cv_spinlock_locked, pc, 
           stack, wait_index, val, wake_index, wake_all_index, old_state_, 
           old_state_u, g, orig_size, old_state, local_wseq, g1, 
           old_orig_size, old_g1_start, r, s, local_wseq_, g_, seq, signals, 
           local_g1_start, local_wseq_c, g1_, do_futex_wake_, local_wseq_cv, 
           g1_c, do_futex_wake, num_loops >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ mutex_index = 0
        /\ g1_orig_size_index = 1
        /\ wrefs_index = 2
        /\ g_signals_index = [i \in {0,1} |-> i + 3]
        /\ g_refs_index = [i \in {0,1} |-> i + 5]
        /\ futexes = [i \in {mutex_index, g1_orig_size_index, wrefs_index, g_signals_index[0], g_signals_index[1], g_refs_index[0], g_refs_index[1]}
                       |-> [state |-> 0, sleepers |-> {}]]
        /\ wseq = 0
        /\ g1_start = 0
        /\ g_size = [i \in {0, 1} |-> 0]
        /\ did_switch_g1 = [i \in AllProcs |-> FALSE]
        /\ g1index = [i \in AllProcs |-> 0]
        /\ waiters = 0
        /\ busy = FALSE
        /\ spinlock_locked = FALSE
        /\ cv_spinlock_locked = FALSE
        (* Procedure futex_wait *)
        /\ wait_index = [ self \in ProcSet |-> 0]
        /\ val = [ self \in ProcSet |-> 0]
        (* Procedure futex_wake_single *)
        /\ wake_index = [ self \in ProcSet |-> 0]
        (* Procedure futex_wake_all *)
        /\ wake_all_index = [ self \in ProcSet |-> 0]
        (* Procedure lock_mutex *)
        /\ old_state_ = [ self \in ProcSet |-> 0]
        (* Procedure unlock_mutex *)
        /\ old_state_u = [ self \in ProcSet |-> 0]
        (* Procedure condvar_dec_grefs *)
        /\ g = [ self \in ProcSet |-> 0]
        (* Procedure condvar_acquire_lock *)
        /\ orig_size = [ self \in ProcSet |-> 0]
        (* Procedure condvar_release_lock *)
        /\ old_state = [ self \in ProcSet |-> 0]
        (* Procedure condvar_quiesce_and_switch_g1 *)
        /\ local_wseq = [ self \in ProcSet |-> 0]
        /\ g1 = [ self \in ProcSet |-> 0]
        /\ old_orig_size = [ self \in ProcSet |-> 0]
        /\ old_g1_start = [ self \in ProcSet |-> 0]
        /\ r = [ self \in ProcSet |-> 0]
        /\ s = [ self \in ProcSet |-> 0]
        (* Procedure cv_wait *)
        /\ local_wseq_ = [ self \in ProcSet |-> 0]
        /\ g_ = [ self \in ProcSet |-> 0]
        /\ seq = [ self \in ProcSet |-> 0]
        /\ signals = [ self \in ProcSet |-> 0]
        /\ local_g1_start = [ self \in ProcSet |-> 0]
        (* Procedure cv_signal *)
        /\ local_wseq_c = [ self \in ProcSet |-> 0]
        /\ g1_ = [ self \in ProcSet |-> 0]
        /\ do_futex_wake_ = [ self \in ProcSet |-> FALSE]
        (* Procedure cv_broadcast *)
        /\ local_wseq_cv = [ self \in ProcSet |-> 0]
        /\ g1_c = [ self \in ProcSet |-> 0]
        /\ do_futex_wake = [ self \in ProcSet |-> FALSE]
        (* Process Proc *)
        /\ num_loops = [self \in Procs |-> MaxNumLoops]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "proc_start"]

check_state(self) == /\ pc[self] = "check_state"
                     /\ IF futexes[wait_index[self]].state /= val[self]
                           THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ wait_index' = [wait_index EXCEPT ![self] = Head(stack[self]).wait_index]
                                /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED futexes
                           ELSE /\ val' = [val EXCEPT ![self] = 0]
                                /\ futexes' = [futexes EXCEPT ![wait_index[self]].sleepers = futexes[wait_index[self]].sleepers \union {self}]
                                /\ pc' = [pc EXCEPT ![self] = "wait_for_wake"]
                                /\ UNCHANGED << stack, wait_index >>
                     /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                     wrefs_index, g_signals_index, 
                                     g_refs_index, wseq, g1_start, g_size, 
                                     did_switch_g1, g1index, waiters, busy, 
                                     spinlock_locked, cv_spinlock_locked, 
                                     wake_index, wake_all_index, old_state_, 
                                     old_state_u, g, orig_size, old_state, 
                                     local_wseq, g1, old_orig_size, 
                                     old_g1_start, r, s, local_wseq_, g_, seq, 
                                     signals, local_g1_start, local_wseq_c, 
                                     g1_, do_futex_wake_, local_wseq_cv, g1_c, 
                                     do_futex_wake, num_loops >>

wait_for_wake(self) == /\ pc[self] = "wait_for_wake"
                       /\ ~ (self \in futexes[wait_index[self]].sleepers)
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ wait_index' = [wait_index EXCEPT ![self] = Head(stack[self]).wait_index]
                       /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                       wrefs_index, g_signals_index, 
                                       g_refs_index, futexes, wseq, g1_start, 
                                       g_size, did_switch_g1, g1index, waiters, 
                                       busy, spinlock_locked, 
                                       cv_spinlock_locked, wake_index, 
                                       wake_all_index, old_state_, old_state_u, 
                                       g, orig_size, old_state, local_wseq, g1, 
                                       old_orig_size, old_g1_start, r, s, 
                                       local_wseq_, g_, seq, signals, 
                                       local_g1_start, local_wseq_c, g1_, 
                                       do_futex_wake_, local_wseq_cv, g1_c, 
                                       do_futex_wake, num_loops >>

futex_wait(self) == check_state(self) \/ wait_for_wake(self)

check_for_sleepers(self) == /\ pc[self] = "check_for_sleepers"
                            /\ IF futexes[wake_index[self]].sleepers = {}
                                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ wake_index' = [wake_index EXCEPT ![self] = Head(stack[self]).wake_index]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                       /\ UNCHANGED futexes
                                  ELSE /\ \E x \in futexes[wake_index[self]].sleepers:
                                            futexes' = [futexes EXCEPT ![wake_index[self]].sleepers = futexes[wake_index[self]].sleepers \ {x}]
                                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ wake_index' = [wake_index EXCEPT ![self] = Head(stack[self]).wake_index]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                            wrefs_index, g_signals_index, 
                                            g_refs_index, wseq, g1_start, 
                                            g_size, did_switch_g1, g1index, 
                                            waiters, busy, spinlock_locked, 
                                            cv_spinlock_locked, wait_index, 
                                            val, wake_all_index, old_state_, 
                                            old_state_u, g, orig_size, 
                                            old_state, local_wseq, g1, 
                                            old_orig_size, old_g1_start, r, s, 
                                            local_wseq_, g_, seq, signals, 
                                            local_g1_start, local_wseq_c, g1_, 
                                            do_futex_wake_, local_wseq_cv, 
                                            g1_c, do_futex_wake, num_loops >>

futex_wake_single(self) == check_for_sleepers(self)

futex_wake_all_(self) == /\ pc[self] = "futex_wake_all_"
                         /\ futexes' = [futexes EXCEPT ![wake_all_index[self]].sleepers = {}]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ wake_all_index' = [wake_all_index EXCEPT ![self] = Head(stack[self]).wake_all_index]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                         wrefs_index, g_signals_index, 
                                         g_refs_index, wseq, g1_start, g_size, 
                                         did_switch_g1, g1index, waiters, busy, 
                                         spinlock_locked, cv_spinlock_locked, 
                                         wait_index, val, wake_index, 
                                         old_state_, old_state_u, g, orig_size, 
                                         old_state, local_wseq, g1, 
                                         old_orig_size, old_g1_start, r, s, 
                                         local_wseq_, g_, seq, signals, 
                                         local_g1_start, local_wseq_c, g1_, 
                                         do_futex_wake_, local_wseq_cv, g1_c, 
                                         do_futex_wake, num_loops >>

futex_wake_all(self) == futex_wake_all_(self)

lock_mutex_start(self) == /\ pc[self] = "lock_mutex_start"
                          /\ IF UseSpinlockForMutex
                                THEN /\ ~spinlock_locked
                                     /\ spinlock_locked' = TRUE
                                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ old_state_' = [old_state_ EXCEPT ![self] = Head(stack[self]).old_state_]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                     /\ UNCHANGED futexes
                                ELSE /\ IF futexes[mutex_index].state = 0
                                           THEN /\ futexes' = [futexes EXCEPT ![mutex_index].state = 1]
                                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                /\ old_state_' = [old_state_ EXCEPT ![self] = Head(stack[self]).old_state_]
                                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "lll_lock_wait"]
                                                /\ UNCHANGED << futexes, stack, 
                                                                old_state_ >>
                                     /\ UNCHANGED spinlock_locked
                          /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                          wrefs_index, g_signals_index, 
                                          g_refs_index, wseq, g1_start, g_size, 
                                          did_switch_g1, g1index, waiters, 
                                          busy, cv_spinlock_locked, wait_index, 
                                          val, wake_index, wake_all_index, 
                                          old_state_u, g, orig_size, old_state, 
                                          local_wseq, g1, old_orig_size, 
                                          old_g1_start, r, s, local_wseq_, g_, 
                                          seq, signals, local_g1_start, 
                                          local_wseq_c, g1_, do_futex_wake_, 
                                          local_wseq_cv, g1_c, do_futex_wake, 
                                          num_loops >>

lll_lock_wait(self) == /\ pc[self] = "lll_lock_wait"
                       /\ IF futexes[mutex_index].state = 2
                             THEN /\ pc' = [pc EXCEPT ![self] = "futex_wait_"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "exchange_lock"]
                       /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                       wrefs_index, g_signals_index, 
                                       g_refs_index, futexes, wseq, g1_start, 
                                       g_size, did_switch_g1, g1index, waiters, 
                                       busy, spinlock_locked, 
                                       cv_spinlock_locked, stack, wait_index, 
                                       val, wake_index, wake_all_index, 
                                       old_state_, old_state_u, g, orig_size, 
                                       old_state, local_wseq, g1, 
                                       old_orig_size, old_g1_start, r, s, 
                                       local_wseq_, g_, seq, signals, 
                                       local_g1_start, local_wseq_c, g1_, 
                                       do_futex_wake_, local_wseq_cv, g1_c, 
                                       do_futex_wake, num_loops >>

exchange_lock(self) == /\ pc[self] = "exchange_lock"
                       /\ old_state_' = [old_state_ EXCEPT ![self] = futexes[mutex_index].state]
                       /\ futexes' = [futexes EXCEPT ![mutex_index].state = 2]
                       /\ pc' = [pc EXCEPT ![self] = "check_for_locked"]
                       /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                       wrefs_index, g_signals_index, 
                                       g_refs_index, wseq, g1_start, g_size, 
                                       did_switch_g1, g1index, waiters, busy, 
                                       spinlock_locked, cv_spinlock_locked, 
                                       stack, wait_index, val, wake_index, 
                                       wake_all_index, old_state_u, g, 
                                       orig_size, old_state, local_wseq, g1, 
                                       old_orig_size, old_g1_start, r, s, 
                                       local_wseq_, g_, seq, signals, 
                                       local_g1_start, local_wseq_c, g1_, 
                                       do_futex_wake_, local_wseq_cv, g1_c, 
                                       do_futex_wake, num_loops >>

check_for_locked(self) == /\ pc[self] = "check_for_locked"
                          /\ IF old_state_[self] = 0
                                THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ old_state_' = [old_state_ EXCEPT ![self] = Head(stack[self]).old_state_]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                ELSE /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
                                     /\ pc' = [pc EXCEPT ![self] = "futex_wait_"]
                                     /\ stack' = stack
                          /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                          wrefs_index, g_signals_index, 
                                          g_refs_index, futexes, wseq, 
                                          g1_start, g_size, did_switch_g1, 
                                          g1index, waiters, busy, 
                                          spinlock_locked, cv_spinlock_locked, 
                                          wait_index, val, wake_index, 
                                          wake_all_index, old_state_u, g, 
                                          orig_size, old_state, local_wseq, g1, 
                                          old_orig_size, old_g1_start, r, s, 
                                          local_wseq_, g_, seq, signals, 
                                          local_g1_start, local_wseq_c, g1_, 
                                          do_futex_wake_, local_wseq_cv, g1_c, 
                                          do_futex_wake, num_loops >>

futex_wait_(self) == /\ pc[self] = "futex_wait_"
                     /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                 pc        |->  "exchange_lock",
                                                                 wait_index |->  wait_index[self],
                                                                 val       |->  val[self] ] >>
                                                             \o stack[self]]
                        /\ val' = [val EXCEPT ![self] = 2]
                        /\ wait_index' = [wait_index EXCEPT ![self] = mutex_index]
                     /\ pc' = [pc EXCEPT ![self] = "check_state"]
                     /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                     wrefs_index, g_signals_index, 
                                     g_refs_index, futexes, wseq, g1_start, 
                                     g_size, did_switch_g1, g1index, waiters, 
                                     busy, spinlock_locked, cv_spinlock_locked, 
                                     wake_index, wake_all_index, old_state_, 
                                     old_state_u, g, orig_size, old_state, 
                                     local_wseq, g1, old_orig_size, 
                                     old_g1_start, r, s, local_wseq_, g_, seq, 
                                     signals, local_g1_start, local_wseq_c, 
                                     g1_, do_futex_wake_, local_wseq_cv, g1_c, 
                                     do_futex_wake, num_loops >>

lock_mutex(self) == lock_mutex_start(self) \/ lll_lock_wait(self)
                       \/ exchange_lock(self) \/ check_for_locked(self)
                       \/ futex_wait_(self)

unlock_mutex_start(self) == /\ pc[self] = "unlock_mutex_start"
                            /\ IF UseSpinlockForMutex
                                  THEN /\ spinlock_locked' = FALSE
                                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ old_state_u' = [old_state_u EXCEPT ![self] = Head(stack[self]).old_state_u]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                       /\ UNCHANGED futexes
                                  ELSE /\ old_state_u' = [old_state_u EXCEPT ![self] = futexes[mutex_index].state]
                                       /\ futexes' = [futexes EXCEPT ![mutex_index].state = 0]
                                       /\ pc' = [pc EXCEPT ![self] = "check_if_sleeper"]
                                       /\ UNCHANGED << spinlock_locked, stack >>
                            /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                            wrefs_index, g_signals_index, 
                                            g_refs_index, wseq, g1_start, 
                                            g_size, did_switch_g1, g1index, 
                                            waiters, busy, cv_spinlock_locked, 
                                            wait_index, val, wake_index, 
                                            wake_all_index, old_state_, g, 
                                            orig_size, old_state, local_wseq, 
                                            g1, old_orig_size, old_g1_start, r, 
                                            s, local_wseq_, g_, seq, signals, 
                                            local_g1_start, local_wseq_c, g1_, 
                                            do_futex_wake_, local_wseq_cv, 
                                            g1_c, do_futex_wake, num_loops >>

check_if_sleeper(self) == /\ pc[self] = "check_if_sleeper"
                          /\ IF old_state_u[self] > 1
                                THEN /\ /\ old_state_u' = [old_state_u EXCEPT ![self] = Head(stack[self]).old_state_u]
                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_single",
                                                                                 pc        |->  Head(stack[self]).pc,
                                                                                 wake_index |->  wake_index[self] ] >>
                                                                             \o Tail(stack[self])]
                                        /\ wake_index' = [wake_index EXCEPT ![self] = mutex_index]
                                     /\ pc' = [pc EXCEPT ![self] = "check_for_sleepers"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ old_state_u' = [old_state_u EXCEPT ![self] = Head(stack[self]).old_state_u]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                     /\ UNCHANGED wake_index
                          /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                          wrefs_index, g_signals_index, 
                                          g_refs_index, futexes, wseq, 
                                          g1_start, g_size, did_switch_g1, 
                                          g1index, waiters, busy, 
                                          spinlock_locked, cv_spinlock_locked, 
                                          wait_index, val, wake_all_index, 
                                          old_state_, g, orig_size, old_state, 
                                          local_wseq, g1, old_orig_size, 
                                          old_g1_start, r, s, local_wseq_, g_, 
                                          seq, signals, local_g1_start, 
                                          local_wseq_c, g1_, do_futex_wake_, 
                                          local_wseq_cv, g1_c, do_futex_wake, 
                                          num_loops >>

unlock_mutex(self) == unlock_mutex_start(self) \/ check_if_sleeper(self)

dec_refs(self) == /\ pc[self] = "dec_refs"
                  /\ futexes' = [futexes EXCEPT ![g_refs_index[g[self]]].state = futexes[g_refs_index[g[self]]].state - 2]
                  /\ IF futexes'[g_refs_index[g[self]]].state = 1
                        THEN /\ pc' = [pc EXCEPT ![self] = "clear_wake_up_flag"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "done_with_dec_refs"]
                  /\ UNCHANGED << mutex_index, g1_orig_size_index, wrefs_index, 
                                  g_signals_index, g_refs_index, wseq, 
                                  g1_start, g_size, did_switch_g1, g1index, 
                                  waiters, busy, spinlock_locked, 
                                  cv_spinlock_locked, stack, wait_index, val, 
                                  wake_index, wake_all_index, old_state_, 
                                  old_state_u, g, orig_size, old_state, 
                                  local_wseq, g1, old_orig_size, old_g1_start, 
                                  r, s, local_wseq_, g_, seq, signals, 
                                  local_g1_start, local_wseq_c, g1_, 
                                  do_futex_wake_, local_wseq_cv, g1_c, 
                                  do_futex_wake, num_loops >>

clear_wake_up_flag(self) == /\ pc[self] = "clear_wake_up_flag"
                            /\ futexes' = [futexes EXCEPT ![g_refs_index[g[self]]].state = ClearBit(futexes[g_refs_index[g[self]]].state, 0)]
                            /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_all",
                                                                        pc        |->  Head(stack[self]).pc,
                                                                        wake_all_index |->  wake_all_index[self] ] >>
                                                                    \o Tail(stack[self])]
                               /\ wake_all_index' = [wake_all_index EXCEPT ![self] = g_refs_index[g[self]]]
                            /\ pc' = [pc EXCEPT ![self] = "futex_wake_all_"]
                            /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                            wrefs_index, g_signals_index, 
                                            g_refs_index, wseq, g1_start, 
                                            g_size, did_switch_g1, g1index, 
                                            waiters, busy, spinlock_locked, 
                                            cv_spinlock_locked, wait_index, 
                                            val, wake_index, old_state_, 
                                            old_state_u, g, orig_size, 
                                            old_state, local_wseq, g1, 
                                            old_orig_size, old_g1_start, r, s, 
                                            local_wseq_, g_, seq, signals, 
                                            local_g1_start, local_wseq_c, g1_, 
                                            do_futex_wake_, local_wseq_cv, 
                                            g1_c, do_futex_wake, num_loops >>

done_with_dec_refs(self) == /\ pc[self] = "done_with_dec_refs"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ g' = [g EXCEPT ![self] = Head(stack[self]).g]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                            wrefs_index, g_signals_index, 
                                            g_refs_index, futexes, wseq, 
                                            g1_start, g_size, did_switch_g1, 
                                            g1index, waiters, busy, 
                                            spinlock_locked, 
                                            cv_spinlock_locked, wait_index, 
                                            val, wake_index, wake_all_index, 
                                            old_state_, old_state_u, orig_size, 
                                            old_state, local_wseq, g1, 
                                            old_orig_size, old_g1_start, r, s, 
                                            local_wseq_, g_, seq, signals, 
                                            local_g1_start, local_wseq_c, g1_, 
                                            do_futex_wake_, local_wseq_cv, 
                                            g1_c, do_futex_wake, num_loops >>

condvar_dec_grefs(self) == dec_refs(self) \/ clear_wake_up_flag(self)
                              \/ done_with_dec_refs(self)

cv_acquire_lock(self) == /\ pc[self] = "cv_acquire_lock"
                         /\ IF UseSpinlockForCVMutex
                               THEN /\ ~cv_spinlock_locked
                                    /\ cv_spinlock_locked' = TRUE
                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ orig_size' = [orig_size EXCEPT ![self] = Head(stack[self]).orig_size]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               ELSE /\ orig_size' = [orig_size EXCEPT ![self] = futexes[g1_orig_size_index].state]
                                    /\ pc' = [pc EXCEPT ![self] = "cv_acquire_unlocked"]
                                    /\ UNCHANGED << cv_spinlock_locked, stack >>
                         /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                         wrefs_index, g_signals_index, 
                                         g_refs_index, futexes, wseq, g1_start, 
                                         g_size, did_switch_g1, g1index, 
                                         waiters, busy, spinlock_locked, 
                                         wait_index, val, wake_index, 
                                         wake_all_index, old_state_, 
                                         old_state_u, g, old_state, local_wseq, 
                                         g1, old_orig_size, old_g1_start, r, s, 
                                         local_wseq_, g_, seq, signals, 
                                         local_g1_start, local_wseq_c, g1_, 
                                         do_futex_wake_, local_wseq_cv, g1_c, 
                                         do_futex_wake, num_loops >>

cv_acquire_unlocked(self) == /\ pc[self] = "cv_acquire_unlocked"
                             /\ IF (orig_size[self] % 4) = 0
                                   THEN /\ pc' = [pc EXCEPT ![self] = "cv_acquire_lock_exchange"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "cv_acquire_lock_sleep_loop"]
                             /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                             wrefs_index, g_signals_index, 
                                             g_refs_index, futexes, wseq, 
                                             g1_start, g_size, did_switch_g1, 
                                             g1index, waiters, busy, 
                                             spinlock_locked, 
                                             cv_spinlock_locked, stack, 
                                             wait_index, val, wake_index, 
                                             wake_all_index, old_state_, 
                                             old_state_u, g, orig_size, 
                                             old_state, local_wseq, g1, 
                                             old_orig_size, old_g1_start, r, s, 
                                             local_wseq_, g_, seq, signals, 
                                             local_g1_start, local_wseq_c, g1_, 
                                             do_futex_wake_, local_wseq_cv, 
                                             g1_c, do_futex_wake, num_loops >>

cv_acquire_lock_exchange(self) == /\ pc[self] = "cv_acquire_lock_exchange"
                                  /\ IF futexes[g1_orig_size_index].state = orig_size[self]
                                        THEN /\ futexes' = [futexes EXCEPT ![g1_orig_size_index].state = SetBit(orig_size[self], 0)]
                                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                             /\ orig_size' = [orig_size EXCEPT ![self] = Head(stack[self]).orig_size]
                                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                        ELSE /\ orig_size' = [orig_size EXCEPT ![self] = futexes[g1_orig_size_index].state]
                                             /\ pc' = [pc EXCEPT ![self] = "cv_acquire_unlocked"]
                                             /\ UNCHANGED << futexes, stack >>
                                  /\ UNCHANGED << mutex_index, 
                                                  g1_orig_size_index, 
                                                  wrefs_index, g_signals_index, 
                                                  g_refs_index, wseq, g1_start, 
                                                  g_size, did_switch_g1, 
                                                  g1index, waiters, busy, 
                                                  spinlock_locked, 
                                                  cv_spinlock_locked, 
                                                  wait_index, val, wake_index, 
                                                  wake_all_index, old_state_, 
                                                  old_state_u, g, old_state, 
                                                  local_wseq, g1, 
                                                  old_orig_size, old_g1_start, 
                                                  r, s, local_wseq_, g_, seq, 
                                                  signals, local_g1_start, 
                                                  local_wseq_c, g1_, 
                                                  do_futex_wake_, 
                                                  local_wseq_cv, g1_c, 
                                                  do_futex_wake, num_loops >>

cv_acquire_lock_sleep_loop(self) == /\ pc[self] = "cv_acquire_lock_sleep_loop"
                                    /\ pc' = [pc EXCEPT ![self] = "cv_acquire_lock_loop_to_set_sleeper"]
                                    /\ UNCHANGED << mutex_index, 
                                                    g1_orig_size_index, 
                                                    wrefs_index, 
                                                    g_signals_index, 
                                                    g_refs_index, futexes, 
                                                    wseq, g1_start, g_size, 
                                                    did_switch_g1, g1index, 
                                                    waiters, busy, 
                                                    spinlock_locked, 
                                                    cv_spinlock_locked, stack, 
                                                    wait_index, val, 
                                                    wake_index, wake_all_index, 
                                                    old_state_, old_state_u, g, 
                                                    orig_size, old_state, 
                                                    local_wseq, g1, 
                                                    old_orig_size, 
                                                    old_g1_start, r, s, 
                                                    local_wseq_, g_, seq, 
                                                    signals, local_g1_start, 
                                                    local_wseq_c, g1_, 
                                                    do_futex_wake_, 
                                                    local_wseq_cv, g1_c, 
                                                    do_futex_wake, num_loops >>

cv_acquire_lock_loop_to_set_sleeper(self) == /\ pc[self] = "cv_acquire_lock_loop_to_set_sleeper"
                                             /\ IF (orig_size[self] % 4) /= 2
                                                   THEN /\ pc' = [pc EXCEPT ![self] = "cv_acquire_lock_exchange_2"]
                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "cv_acquire_lock_sleeper_flag_set"]
                                             /\ UNCHANGED << mutex_index, 
                                                             g1_orig_size_index, 
                                                             wrefs_index, 
                                                             g_signals_index, 
                                                             g_refs_index, 
                                                             futexes, wseq, 
                                                             g1_start, g_size, 
                                                             did_switch_g1, 
                                                             g1index, waiters, 
                                                             busy, 
                                                             spinlock_locked, 
                                                             cv_spinlock_locked, 
                                                             stack, wait_index, 
                                                             val, wake_index, 
                                                             wake_all_index, 
                                                             old_state_, 
                                                             old_state_u, g, 
                                                             orig_size, 
                                                             old_state, 
                                                             local_wseq, g1, 
                                                             old_orig_size, 
                                                             old_g1_start, r, 
                                                             s, local_wseq_, 
                                                             g_, seq, signals, 
                                                             local_g1_start, 
                                                             local_wseq_c, g1_, 
                                                             do_futex_wake_, 
                                                             local_wseq_cv, 
                                                             g1_c, 
                                                             do_futex_wake, 
                                                             num_loops >>

cv_acquire_lock_exchange_2(self) == /\ pc[self] = "cv_acquire_lock_exchange_2"
                                    /\ IF futexes[g1_orig_size_index].state = orig_size[self]
                                          THEN /\ futexes' = [futexes EXCEPT ![g1_orig_size_index].state = SetBit(ClearBit(orig_size[self], 0), 1)]
                                               /\ IF (orig_size[self] % 4) = 0
                                                     THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                          /\ orig_size' = [orig_size EXCEPT ![self] = Head(stack[self]).orig_size]
                                                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "cv_acquire_lock_sleeper_flag_set"]
                                                          /\ UNCHANGED << stack, 
                                                                          orig_size >>
                                          ELSE /\ orig_size' = [orig_size EXCEPT ![self] = futexes[g1_orig_size_index].state]
                                               /\ pc' = [pc EXCEPT ![self] = "cv_acquire_lock_loop_to_set_sleeper"]
                                               /\ UNCHANGED << futexes, stack >>
                                    /\ UNCHANGED << mutex_index, 
                                                    g1_orig_size_index, 
                                                    wrefs_index, 
                                                    g_signals_index, 
                                                    g_refs_index, wseq, 
                                                    g1_start, g_size, 
                                                    did_switch_g1, g1index, 
                                                    waiters, busy, 
                                                    spinlock_locked, 
                                                    cv_spinlock_locked, 
                                                    wait_index, val, 
                                                    wake_index, wake_all_index, 
                                                    old_state_, old_state_u, g, 
                                                    old_state, local_wseq, g1, 
                                                    old_orig_size, 
                                                    old_g1_start, r, s, 
                                                    local_wseq_, g_, seq, 
                                                    signals, local_g1_start, 
                                                    local_wseq_c, g1_, 
                                                    do_futex_wake_, 
                                                    local_wseq_cv, g1_c, 
                                                    do_futex_wake, num_loops >>

cv_acquire_lock_sleeper_flag_set(self) == /\ pc[self] = "cv_acquire_lock_sleeper_flag_set"
                                          /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                                      pc        |->  "cv_acquire_re_read_state",
                                                                                      wait_index |->  wait_index[self],
                                                                                      val       |->  val[self] ] >>
                                                                                  \o stack[self]]
                                             /\ val' = [val EXCEPT ![self] = SetBit(ClearBit(orig_size[self], 0), 1)]
                                             /\ wait_index' = [wait_index EXCEPT ![self] = g1_orig_size_index]
                                          /\ pc' = [pc EXCEPT ![self] = "check_state"]
                                          /\ UNCHANGED << mutex_index, 
                                                          g1_orig_size_index, 
                                                          wrefs_index, 
                                                          g_signals_index, 
                                                          g_refs_index, 
                                                          futexes, wseq, 
                                                          g1_start, g_size, 
                                                          did_switch_g1, 
                                                          g1index, waiters, 
                                                          busy, 
                                                          spinlock_locked, 
                                                          cv_spinlock_locked, 
                                                          wake_index, 
                                                          wake_all_index, 
                                                          old_state_, 
                                                          old_state_u, g, 
                                                          orig_size, old_state, 
                                                          local_wseq, g1, 
                                                          old_orig_size, 
                                                          old_g1_start, r, s, 
                                                          local_wseq_, g_, seq, 
                                                          signals, 
                                                          local_g1_start, 
                                                          local_wseq_c, g1_, 
                                                          do_futex_wake_, 
                                                          local_wseq_cv, g1_c, 
                                                          do_futex_wake, 
                                                          num_loops >>

cv_acquire_re_read_state(self) == /\ pc[self] = "cv_acquire_re_read_state"
                                  /\ orig_size' = [orig_size EXCEPT ![self] = futexes[g1_orig_size_index].state]
                                  /\ pc' = [pc EXCEPT ![self] = "cv_acquire_lock_sleep_loop"]
                                  /\ UNCHANGED << mutex_index, 
                                                  g1_orig_size_index, 
                                                  wrefs_index, g_signals_index, 
                                                  g_refs_index, futexes, wseq, 
                                                  g1_start, g_size, 
                                                  did_switch_g1, g1index, 
                                                  waiters, busy, 
                                                  spinlock_locked, 
                                                  cv_spinlock_locked, stack, 
                                                  wait_index, val, wake_index, 
                                                  wake_all_index, old_state_, 
                                                  old_state_u, g, old_state, 
                                                  local_wseq, g1, 
                                                  old_orig_size, old_g1_start, 
                                                  r, s, local_wseq_, g_, seq, 
                                                  signals, local_g1_start, 
                                                  local_wseq_c, g1_, 
                                                  do_futex_wake_, 
                                                  local_wseq_cv, g1_c, 
                                                  do_futex_wake, num_loops >>

condvar_acquire_lock(self) == cv_acquire_lock(self)
                                 \/ cv_acquire_unlocked(self)
                                 \/ cv_acquire_lock_exchange(self)
                                 \/ cv_acquire_lock_sleep_loop(self)
                                 \/ cv_acquire_lock_loop_to_set_sleeper(self)
                                 \/ cv_acquire_lock_exchange_2(self)
                                 \/ cv_acquire_lock_sleeper_flag_set(self)
                                 \/ cv_acquire_re_read_state(self)

cv_release_lock(self) == /\ pc[self] = "cv_release_lock"
                         /\ IF UseSpinlockForCVMutex
                               THEN /\ cv_spinlock_locked' = FALSE
                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ old_state' = [old_state EXCEPT ![self] = Head(stack[self]).old_state]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                    /\ UNCHANGED futexes
                               ELSE /\ old_state' = [old_state EXCEPT ![self] = futexes[g1_orig_size_index].state]
                                    /\ futexes' = [futexes EXCEPT ![g1_orig_size_index].state = ClearBit(ClearBit(old_state'[self], 0), 1)]
                                    /\ pc' = [pc EXCEPT ![self] = "cv_release_lock_maybe_notify"]
                                    /\ UNCHANGED << cv_spinlock_locked, stack >>
                         /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                         wrefs_index, g_signals_index, 
                                         g_refs_index, wseq, g1_start, g_size, 
                                         did_switch_g1, g1index, waiters, busy, 
                                         spinlock_locked, wait_index, val, 
                                         wake_index, wake_all_index, 
                                         old_state_, old_state_u, g, orig_size, 
                                         local_wseq, g1, old_orig_size, 
                                         old_g1_start, r, s, local_wseq_, g_, 
                                         seq, signals, local_g1_start, 
                                         local_wseq_c, g1_, do_futex_wake_, 
                                         local_wseq_cv, g1_c, do_futex_wake, 
                                         num_loops >>

cv_release_lock_maybe_notify(self) == /\ pc[self] = "cv_release_lock_maybe_notify"
                                      /\ IF (old_state[self] % 4) > 1
                                            THEN /\ old_state' = [old_state EXCEPT ![self] = 0]
                                                 /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_single",
                                                                                             pc        |->  "cv_release_lock_done",
                                                                                             wake_index |->  wake_index[self] ] >>
                                                                                         \o stack[self]]
                                                    /\ wake_index' = [wake_index EXCEPT ![self] = g1_orig_size_index]
                                                 /\ pc' = [pc EXCEPT ![self] = "check_for_sleepers"]
                                            ELSE /\ old_state' = [old_state EXCEPT ![self] = 0]
                                                 /\ pc' = [pc EXCEPT ![self] = "cv_release_lock_done"]
                                                 /\ UNCHANGED << stack, 
                                                                 wake_index >>
                                      /\ UNCHANGED << mutex_index, 
                                                      g1_orig_size_index, 
                                                      wrefs_index, 
                                                      g_signals_index, 
                                                      g_refs_index, futexes, 
                                                      wseq, g1_start, g_size, 
                                                      did_switch_g1, g1index, 
                                                      waiters, busy, 
                                                      spinlock_locked, 
                                                      cv_spinlock_locked, 
                                                      wait_index, val, 
                                                      wake_all_index, 
                                                      old_state_, old_state_u, 
                                                      g, orig_size, local_wseq, 
                                                      g1, old_orig_size, 
                                                      old_g1_start, r, s, 
                                                      local_wseq_, g_, seq, 
                                                      signals, local_g1_start, 
                                                      local_wseq_c, g1_, 
                                                      do_futex_wake_, 
                                                      local_wseq_cv, g1_c, 
                                                      do_futex_wake, num_loops >>

cv_release_lock_done(self) == /\ pc[self] = "cv_release_lock_done"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ old_state' = [old_state EXCEPT ![self] = Head(stack[self]).old_state]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                              wrefs_index, g_signals_index, 
                                              g_refs_index, futexes, wseq, 
                                              g1_start, g_size, did_switch_g1, 
                                              g1index, waiters, busy, 
                                              spinlock_locked, 
                                              cv_spinlock_locked, wait_index, 
                                              val, wake_index, wake_all_index, 
                                              old_state_, old_state_u, g, 
                                              orig_size, local_wseq, g1, 
                                              old_orig_size, old_g1_start, r, 
                                              s, local_wseq_, g_, seq, signals, 
                                              local_g1_start, local_wseq_c, 
                                              g1_, do_futex_wake_, 
                                              local_wseq_cv, g1_c, 
                                              do_futex_wake, num_loops >>

condvar_release_lock(self) == cv_release_lock(self)
                                 \/ cv_release_lock_maybe_notify(self)
                                 \/ cv_release_lock_done(self)

quiesce_and_switch_start(self) == /\ pc[self] = "quiesce_and_switch_start"
                                  /\ g1index' = [g1index EXCEPT ![self] = g1[self]]
                                  /\ old_orig_size' = [old_orig_size EXCEPT ![self] = futexes[g1_orig_size_index].state \div 4]
                                  /\ pc' = [pc EXCEPT ![self] = "quiesce_and_switch_start2"]
                                  /\ UNCHANGED << mutex_index, 
                                                  g1_orig_size_index, 
                                                  wrefs_index, g_signals_index, 
                                                  g_refs_index, futexes, wseq, 
                                                  g1_start, g_size, 
                                                  did_switch_g1, waiters, busy, 
                                                  spinlock_locked, 
                                                  cv_spinlock_locked, stack, 
                                                  wait_index, val, wake_index, 
                                                  wake_all_index, old_state_, 
                                                  old_state_u, g, orig_size, 
                                                  old_state, local_wseq, g1, 
                                                  old_g1_start, r, s, 
                                                  local_wseq_, g_, seq, 
                                                  signals, local_g1_start, 
                                                  local_wseq_c, g1_, 
                                                  do_futex_wake_, 
                                                  local_wseq_cv, g1_c, 
                                                  do_futex_wake, num_loops >>

quiesce_and_switch_start2(self) == /\ pc[self] = "quiesce_and_switch_start2"
                                   /\ old_g1_start' = [old_g1_start EXCEPT ![self] = g1_start \div 2]
                                   /\ pc' = [pc EXCEPT ![self] = "quiesce_and_switch_check_for_no_reader"]
                                   /\ UNCHANGED << mutex_index, 
                                                   g1_orig_size_index, 
                                                   wrefs_index, 
                                                   g_signals_index, 
                                                   g_refs_index, futexes, wseq, 
                                                   g1_start, g_size, 
                                                   did_switch_g1, g1index, 
                                                   waiters, busy, 
                                                   spinlock_locked, 
                                                   cv_spinlock_locked, stack, 
                                                   wait_index, val, wake_index, 
                                                   wake_all_index, old_state_, 
                                                   old_state_u, g, orig_size, 
                                                   old_state, local_wseq, g1, 
                                                   old_orig_size, r, s, 
                                                   local_wseq_, g_, seq, 
                                                   signals, local_g1_start, 
                                                   local_wseq_c, g1_, 
                                                   do_futex_wake_, 
                                                   local_wseq_cv, g1_c, 
                                                   do_futex_wake, num_loops >>

quiesce_and_switch_check_for_no_reader(self) == /\ pc[self] = "quiesce_and_switch_check_for_no_reader"
                                                /\ IF ((local_wseq[self] - old_g1_start[self] - old_orig_size[self]) + g_size[Xor1(g1[self])]) = 0
                                                      THEN /\ did_switch_g1' = [did_switch_g1 EXCEPT ![self] = FALSE]
                                                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                           /\ old_orig_size' = [old_orig_size EXCEPT ![self] = Head(stack[self]).old_orig_size]
                                                           /\ old_g1_start' = [old_g1_start EXCEPT ![self] = Head(stack[self]).old_g1_start]
                                                           /\ r' = [r EXCEPT ![self] = Head(stack[self]).r]
                                                           /\ s' = [s EXCEPT ![self] = Head(stack[self]).s]
                                                           /\ local_wseq' = [local_wseq EXCEPT ![self] = Head(stack[self]).local_wseq]
                                                           /\ g1' = [g1 EXCEPT ![self] = Head(stack[self]).g1]
                                                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "close_signal_g1"]
                                                           /\ UNCHANGED << did_switch_g1, 
                                                                           stack, 
                                                                           local_wseq, 
                                                                           g1, 
                                                                           old_orig_size, 
                                                                           old_g1_start, 
                                                                           r, 
                                                                           s >>
                                                /\ UNCHANGED << mutex_index, 
                                                                g1_orig_size_index, 
                                                                wrefs_index, 
                                                                g_signals_index, 
                                                                g_refs_index, 
                                                                futexes, wseq, 
                                                                g1_start, 
                                                                g_size, 
                                                                g1index, 
                                                                waiters, busy, 
                                                                spinlock_locked, 
                                                                cv_spinlock_locked, 
                                                                wait_index, 
                                                                val, 
                                                                wake_index, 
                                                                wake_all_index, 
                                                                old_state_, 
                                                                old_state_u, g, 
                                                                orig_size, 
                                                                old_state, 
                                                                local_wseq_, 
                                                                g_, seq, 
                                                                signals, 
                                                                local_g1_start, 
                                                                local_wseq_c, 
                                                                g1_, 
                                                                do_futex_wake_, 
                                                                local_wseq_cv, 
                                                                g1_c, 
                                                                do_futex_wake, 
                                                                num_loops >>

close_signal_g1(self) == /\ pc[self] = "close_signal_g1"
                         /\ futexes' = [futexes EXCEPT ![g_signals_index[g1[self]]].state = SetBit(futexes[g_signals_index[g1[self]]].state, 0)]
                         /\ pc' = [pc EXCEPT ![self] = "wait_for_no_refs"]
                         /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                         wrefs_index, g_signals_index, 
                                         g_refs_index, wseq, g1_start, g_size, 
                                         did_switch_g1, g1index, waiters, busy, 
                                         spinlock_locked, cv_spinlock_locked, 
                                         stack, wait_index, val, wake_index, 
                                         wake_all_index, old_state_, 
                                         old_state_u, g, orig_size, old_state, 
                                         local_wseq, g1, old_orig_size, 
                                         old_g1_start, r, s, local_wseq_, g_, 
                                         seq, signals, local_g1_start, 
                                         local_wseq_c, g1_, do_futex_wake_, 
                                         local_wseq_cv, g1_c, do_futex_wake, 
                                         num_loops >>

wait_for_no_refs(self) == /\ pc[self] = "wait_for_no_refs"
                          /\ r' = [r EXCEPT ![self] = futexes[g_refs_index[g1[self]]].state]
                          /\ pc' = [pc EXCEPT ![self] = "wait_for_no_refs_loop"]
                          /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                          wrefs_index, g_signals_index, 
                                          g_refs_index, futexes, wseq, 
                                          g1_start, g_size, did_switch_g1, 
                                          g1index, waiters, busy, 
                                          spinlock_locked, cv_spinlock_locked, 
                                          stack, wait_index, val, wake_index, 
                                          wake_all_index, old_state_, 
                                          old_state_u, g, orig_size, old_state, 
                                          local_wseq, g1, old_orig_size, 
                                          old_g1_start, s, local_wseq_, g_, 
                                          seq, signals, local_g1_start, 
                                          local_wseq_c, g1_, do_futex_wake_, 
                                          local_wseq_cv, g1_c, do_futex_wake, 
                                          num_loops >>

wait_for_no_refs_loop(self) == /\ pc[self] = "wait_for_no_refs_loop"
                               /\ IF (r[self] \div 2) > 0
                                     THEN /\ pc' = [pc EXCEPT ![self] = "wait_for_no_refs_fetch_or"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "quiesce_update_g1_start"]
                               /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                               wrefs_index, g_signals_index, 
                                               g_refs_index, futexes, wseq, 
                                               g1_start, g_size, did_switch_g1, 
                                               g1index, waiters, busy, 
                                               spinlock_locked, 
                                               cv_spinlock_locked, stack, 
                                               wait_index, val, wake_index, 
                                               wake_all_index, old_state_, 
                                               old_state_u, g, orig_size, 
                                               old_state, local_wseq, g1, 
                                               old_orig_size, old_g1_start, r, 
                                               s, local_wseq_, g_, seq, 
                                               signals, local_g1_start, 
                                               local_wseq_c, g1_, 
                                               do_futex_wake_, local_wseq_cv, 
                                               g1_c, do_futex_wake, num_loops >>

wait_for_no_refs_fetch_or(self) == /\ pc[self] = "wait_for_no_refs_fetch_or"
                                   /\ futexes' = [futexes EXCEPT ![g_refs_index[g1[self]]].state = SetBit(futexes[g_refs_index[g1[self]]].state, 0)]
                                   /\ r' = [r EXCEPT ![self] = futexes'[g_refs_index[g1[self]]].state]
                                   /\ pc' = [pc EXCEPT ![self] = "wait_for_no_refs_maybe_sleep"]
                                   /\ UNCHANGED << mutex_index, 
                                                   g1_orig_size_index, 
                                                   wrefs_index, 
                                                   g_signals_index, 
                                                   g_refs_index, wseq, 
                                                   g1_start, g_size, 
                                                   did_switch_g1, g1index, 
                                                   waiters, busy, 
                                                   spinlock_locked, 
                                                   cv_spinlock_locked, stack, 
                                                   wait_index, val, wake_index, 
                                                   wake_all_index, old_state_, 
                                                   old_state_u, g, orig_size, 
                                                   old_state, local_wseq, g1, 
                                                   old_orig_size, old_g1_start, 
                                                   s, local_wseq_, g_, seq, 
                                                   signals, local_g1_start, 
                                                   local_wseq_c, g1_, 
                                                   do_futex_wake_, 
                                                   local_wseq_cv, g1_c, 
                                                   do_futex_wake, num_loops >>

wait_for_no_refs_maybe_sleep(self) == /\ pc[self] = "wait_for_no_refs_maybe_sleep"
                                      /\ IF (r[self] \div 2) > 0
                                            THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                                             pc        |->  "wait_for_no_refs_reload",
                                                                                             wait_index |->  wait_index[self],
                                                                                             val       |->  val[self] ] >>
                                                                                         \o stack[self]]
                                                    /\ val' = [val EXCEPT ![self] = r[self]]
                                                    /\ wait_index' = [wait_index EXCEPT ![self] = g_refs_index[g1[self]]]
                                                 /\ pc' = [pc EXCEPT ![self] = "check_state"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "wait_for_no_refs_reload"]
                                                 /\ UNCHANGED << stack, 
                                                                 wait_index, 
                                                                 val >>
                                      /\ UNCHANGED << mutex_index, 
                                                      g1_orig_size_index, 
                                                      wrefs_index, 
                                                      g_signals_index, 
                                                      g_refs_index, futexes, 
                                                      wseq, g1_start, g_size, 
                                                      did_switch_g1, g1index, 
                                                      waiters, busy, 
                                                      spinlock_locked, 
                                                      cv_spinlock_locked, 
                                                      wake_index, 
                                                      wake_all_index, 
                                                      old_state_, old_state_u, 
                                                      g, orig_size, old_state, 
                                                      local_wseq, g1, 
                                                      old_orig_size, 
                                                      old_g1_start, r, s, 
                                                      local_wseq_, g_, seq, 
                                                      signals, local_g1_start, 
                                                      local_wseq_c, g1_, 
                                                      do_futex_wake_, 
                                                      local_wseq_cv, g1_c, 
                                                      do_futex_wake, num_loops >>

wait_for_no_refs_reload(self) == /\ pc[self] = "wait_for_no_refs_reload"
                                 /\ r' = [r EXCEPT ![self] = futexes[g_refs_index[g1[self]]].state]
                                 /\ pc' = [pc EXCEPT ![self] = "wait_for_no_refs_loop"]
                                 /\ UNCHANGED << mutex_index, 
                                                 g1_orig_size_index, 
                                                 wrefs_index, g_signals_index, 
                                                 g_refs_index, futexes, wseq, 
                                                 g1_start, g_size, 
                                                 did_switch_g1, g1index, 
                                                 waiters, busy, 
                                                 spinlock_locked, 
                                                 cv_spinlock_locked, stack, 
                                                 wait_index, val, wake_index, 
                                                 wake_all_index, old_state_, 
                                                 old_state_u, g, orig_size, 
                                                 old_state, local_wseq, g1, 
                                                 old_orig_size, old_g1_start, 
                                                 s, local_wseq_, g_, seq, 
                                                 signals, local_g1_start, 
                                                 local_wseq_c, g1_, 
                                                 do_futex_wake_, local_wseq_cv, 
                                                 g1_c, do_futex_wake, 
                                                 num_loops >>

quiesce_update_g1_start(self) == /\ pc[self] = "quiesce_update_g1_start"
                                 /\ g1_start' = g1_start + (old_orig_size[self] * 2) + (IF g1[self] = 1 THEN 1 ELSE -1)
                                 /\ pc' = [pc EXCEPT ![self] = "quiesce_reopen_group"]
                                 /\ UNCHANGED << mutex_index, 
                                                 g1_orig_size_index, 
                                                 wrefs_index, g_signals_index, 
                                                 g_refs_index, futexes, wseq, 
                                                 g_size, did_switch_g1, 
                                                 g1index, waiters, busy, 
                                                 spinlock_locked, 
                                                 cv_spinlock_locked, stack, 
                                                 wait_index, val, wake_index, 
                                                 wake_all_index, old_state_, 
                                                 old_state_u, g, orig_size, 
                                                 old_state, local_wseq, g1, 
                                                 old_orig_size, old_g1_start, 
                                                 r, s, local_wseq_, g_, seq, 
                                                 signals, local_g1_start, 
                                                 local_wseq_c, g1_, 
                                                 do_futex_wake_, local_wseq_cv, 
                                                 g1_c, do_futex_wake, 
                                                 num_loops >>

quiesce_reopen_group(self) == /\ pc[self] = "quiesce_reopen_group"
                              /\ futexes' = [futexes EXCEPT ![g_signals_index[g1[self]]].state = 0]
                              /\ pc' = [pc EXCEPT ![self] = "quiesce_flip_wseq"]
                              /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                              wrefs_index, g_signals_index, 
                                              g_refs_index, wseq, g1_start, 
                                              g_size, did_switch_g1, g1index, 
                                              waiters, busy, spinlock_locked, 
                                              cv_spinlock_locked, stack, 
                                              wait_index, val, wake_index, 
                                              wake_all_index, old_state_, 
                                              old_state_u, g, orig_size, 
                                              old_state, local_wseq, g1, 
                                              old_orig_size, old_g1_start, r, 
                                              s, local_wseq_, g_, seq, signals, 
                                              local_g1_start, local_wseq_c, 
                                              g1_, do_futex_wake_, 
                                              local_wseq_cv, g1_c, 
                                              do_futex_wake, num_loops >>

quiesce_flip_wseq(self) == /\ pc[self] = "quiesce_flip_wseq"
                           /\ wseq' = Xor1(wseq)
                           /\ local_wseq' = [local_wseq EXCEPT ![self] = wseq' \div 2]
                           /\ pc' = [pc EXCEPT ![self] = "quiesce_flip_g1"]
                           /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                           wrefs_index, g_signals_index, 
                                           g_refs_index, futexes, g1_start, 
                                           g_size, did_switch_g1, g1index, 
                                           waiters, busy, spinlock_locked, 
                                           cv_spinlock_locked, stack, 
                                           wait_index, val, wake_index, 
                                           wake_all_index, old_state_, 
                                           old_state_u, g, orig_size, 
                                           old_state, g1, old_orig_size, 
                                           old_g1_start, r, s, local_wseq_, g_, 
                                           seq, signals, local_g1_start, 
                                           local_wseq_c, g1_, do_futex_wake_, 
                                           local_wseq_cv, g1_c, do_futex_wake, 
                                           num_loops >>

quiesce_flip_g1(self) == /\ pc[self] = "quiesce_flip_g1"
                         /\ g1' = [g1 EXCEPT ![self] = Xor1(g1[self])]
                         /\ g1index' = [g1index EXCEPT ![self] = Xor1(g1index[self])]
                         /\ pc' = [pc EXCEPT ![self] = "quiesce_update_orig_size"]
                         /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                         wrefs_index, g_signals_index, 
                                         g_refs_index, futexes, wseq, g1_start, 
                                         g_size, did_switch_g1, waiters, busy, 
                                         spinlock_locked, cv_spinlock_locked, 
                                         stack, wait_index, val, wake_index, 
                                         wake_all_index, old_state_, 
                                         old_state_u, g, orig_size, old_state, 
                                         local_wseq, old_orig_size, 
                                         old_g1_start, r, s, local_wseq_, g_, 
                                         seq, signals, local_g1_start, 
                                         local_wseq_c, g1_, do_futex_wake_, 
                                         local_wseq_cv, g1_c, do_futex_wake, 
                                         num_loops >>

quiesce_update_orig_size(self) == /\ pc[self] = "quiesce_update_orig_size"
                                  /\ old_orig_size' = [old_orig_size EXCEPT ![self] = local_wseq[self] - (old_g1_start[self] + old_orig_size[self])]
                                  /\ s' = [s EXCEPT ![self] = (futexes[g1_orig_size_index].state % 4) + (old_orig_size'[self] * 4)]
                                  /\ r' = [r EXCEPT ![self] = futexes[g1_orig_size_index].state]
                                  /\ futexes' = [futexes EXCEPT ![g1_orig_size_index].state = s'[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "quiesce_check_orig_size"]
                                  /\ UNCHANGED << mutex_index, 
                                                  g1_orig_size_index, 
                                                  wrefs_index, g_signals_index, 
                                                  g_refs_index, wseq, g1_start, 
                                                  g_size, did_switch_g1, 
                                                  g1index, waiters, busy, 
                                                  spinlock_locked, 
                                                  cv_spinlock_locked, stack, 
                                                  wait_index, val, wake_index, 
                                                  wake_all_index, old_state_, 
                                                  old_state_u, g, orig_size, 
                                                  old_state, local_wseq, g1, 
                                                  old_g1_start, local_wseq_, 
                                                  g_, seq, signals, 
                                                  local_g1_start, local_wseq_c, 
                                                  g1_, do_futex_wake_, 
                                                  local_wseq_cv, g1_c, 
                                                  do_futex_wake, num_loops >>

quiesce_check_orig_size(self) == /\ pc[self] = "quiesce_check_orig_size"
                                 /\ IF (r[self] % 4) /= (s[self] % 4)
                                       THEN /\ futexes' = [futexes EXCEPT ![g1_orig_size_index].state = (old_orig_size[self] * 4) + 2]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED futexes
                                 /\ pc' = [pc EXCEPT ![self] = "quiesce_update_size"]
                                 /\ UNCHANGED << mutex_index, 
                                                 g1_orig_size_index, 
                                                 wrefs_index, g_signals_index, 
                                                 g_refs_index, wseq, g1_start, 
                                                 g_size, did_switch_g1, 
                                                 g1index, waiters, busy, 
                                                 spinlock_locked, 
                                                 cv_spinlock_locked, stack, 
                                                 wait_index, val, wake_index, 
                                                 wake_all_index, old_state_, 
                                                 old_state_u, g, orig_size, 
                                                 old_state, local_wseq, g1, 
                                                 old_orig_size, old_g1_start, 
                                                 r, s, local_wseq_, g_, seq, 
                                                 signals, local_g1_start, 
                                                 local_wseq_c, g1_, 
                                                 do_futex_wake_, local_wseq_cv, 
                                                 g1_c, do_futex_wake, 
                                                 num_loops >>

quiesce_update_size(self) == /\ pc[self] = "quiesce_update_size"
                             /\ g_size' = [g_size EXCEPT ![g1[self]] = g_size[g1[self]] + old_orig_size[self]]
                             /\ did_switch_g1' = [did_switch_g1 EXCEPT ![self] = g_size'[g1[self]] /= 0]
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ old_orig_size' = [old_orig_size EXCEPT ![self] = Head(stack[self]).old_orig_size]
                             /\ old_g1_start' = [old_g1_start EXCEPT ![self] = Head(stack[self]).old_g1_start]
                             /\ r' = [r EXCEPT ![self] = Head(stack[self]).r]
                             /\ s' = [s EXCEPT ![self] = Head(stack[self]).s]
                             /\ local_wseq' = [local_wseq EXCEPT ![self] = Head(stack[self]).local_wseq]
                             /\ g1' = [g1 EXCEPT ![self] = Head(stack[self]).g1]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                             wrefs_index, g_signals_index, 
                                             g_refs_index, futexes, wseq, 
                                             g1_start, g1index, waiters, busy, 
                                             spinlock_locked, 
                                             cv_spinlock_locked, wait_index, 
                                             val, wake_index, wake_all_index, 
                                             old_state_, old_state_u, g, 
                                             orig_size, old_state, local_wseq_, 
                                             g_, seq, signals, local_g1_start, 
                                             local_wseq_c, g1_, do_futex_wake_, 
                                             local_wseq_cv, g1_c, 
                                             do_futex_wake, num_loops >>

condvar_quiesce_and_switch_g1(self) == quiesce_and_switch_start(self)
                                          \/ quiesce_and_switch_start2(self)
                                          \/ quiesce_and_switch_check_for_no_reader(self)
                                          \/ close_signal_g1(self)
                                          \/ wait_for_no_refs(self)
                                          \/ wait_for_no_refs_loop(self)
                                          \/ wait_for_no_refs_fetch_or(self)
                                          \/ wait_for_no_refs_maybe_sleep(self)
                                          \/ wait_for_no_refs_reload(self)
                                          \/ quiesce_update_g1_start(self)
                                          \/ quiesce_reopen_group(self)
                                          \/ quiesce_flip_wseq(self)
                                          \/ quiesce_flip_g1(self)
                                          \/ quiesce_update_orig_size(self)
                                          \/ quiesce_check_orig_size(self)
                                          \/ quiesce_update_size(self)

cv_wait_fetch_seq(self) == /\ pc[self] = "cv_wait_fetch_seq"
                           /\ local_wseq_' = [local_wseq_ EXCEPT ![self] = wseq]
                           /\ wseq' = wseq + 2
                           /\ g_' = [g_ EXCEPT ![self] = local_wseq_'[self] % 2]
                           /\ seq' = [seq EXCEPT ![self] = local_wseq_'[self] \div 2]
                           /\ pc' = [pc EXCEPT ![self] = "cv_wait_incr_wrefs"]
                           /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                           wrefs_index, g_signals_index, 
                                           g_refs_index, futexes, g1_start, 
                                           g_size, did_switch_g1, g1index, 
                                           waiters, busy, spinlock_locked, 
                                           cv_spinlock_locked, stack, 
                                           wait_index, val, wake_index, 
                                           wake_all_index, old_state_, 
                                           old_state_u, g, orig_size, 
                                           old_state, local_wseq, g1, 
                                           old_orig_size, old_g1_start, r, s, 
                                           signals, local_g1_start, 
                                           local_wseq_c, g1_, do_futex_wake_, 
                                           local_wseq_cv, g1_c, do_futex_wake, 
                                           num_loops >>

cv_wait_incr_wrefs(self) == /\ pc[self] = "cv_wait_incr_wrefs"
                            /\ futexes' = [futexes EXCEPT ![wrefs_index].state = futexes[wrefs_index].state + 8]
                            /\ pc' = [pc EXCEPT ![self] = "cv_wait_incr_grefs"]
                            /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                            wrefs_index, g_signals_index, 
                                            g_refs_index, wseq, g1_start, 
                                            g_size, did_switch_g1, g1index, 
                                            waiters, busy, spinlock_locked, 
                                            cv_spinlock_locked, stack, 
                                            wait_index, val, wake_index, 
                                            wake_all_index, old_state_, 
                                            old_state_u, g, orig_size, 
                                            old_state, local_wseq, g1, 
                                            old_orig_size, old_g1_start, r, s, 
                                            local_wseq_, g_, seq, signals, 
                                            local_g1_start, local_wseq_c, g1_, 
                                            do_futex_wake_, local_wseq_cv, 
                                            g1_c, do_futex_wake, num_loops >>

cv_wait_incr_grefs(self) == /\ pc[self] = "cv_wait_incr_grefs"
                            /\ IF AlwaysSetGRefs
                                  THEN /\ futexes' = [futexes EXCEPT ![g_refs_index[g_[self]]].state = futexes[g_refs_index[g_[self]]].state + 2]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED futexes
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock_mutex",
                                                                     pc        |->  "cv_wait_load_signals",
                                                                     old_state_u |->  old_state_u[self] ] >>
                                                                 \o stack[self]]
                            /\ old_state_u' = [old_state_u EXCEPT ![self] = 0]
                            /\ pc' = [pc EXCEPT ![self] = "unlock_mutex_start"]
                            /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                            wrefs_index, g_signals_index, 
                                            g_refs_index, wseq, g1_start, 
                                            g_size, did_switch_g1, g1index, 
                                            waiters, busy, spinlock_locked, 
                                            cv_spinlock_locked, wait_index, 
                                            val, wake_index, wake_all_index, 
                                            old_state_, g, orig_size, 
                                            old_state, local_wseq, g1, 
                                            old_orig_size, old_g1_start, r, s, 
                                            local_wseq_, g_, seq, signals, 
                                            local_g1_start, local_wseq_c, g1_, 
                                            do_futex_wake_, local_wseq_cv, 
                                            g1_c, do_futex_wake, num_loops >>

cv_wait_load_signals(self) == /\ pc[self] = "cv_wait_load_signals"
                              /\ signals' = [signals EXCEPT ![self] = futexes[g_signals_index[g_[self]]].state]
                              /\ pc' = [pc EXCEPT ![self] = "cv_wait_loop"]
                              /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                              wrefs_index, g_signals_index, 
                                              g_refs_index, futexes, wseq, 
                                              g1_start, g_size, did_switch_g1, 
                                              g1index, waiters, busy, 
                                              spinlock_locked, 
                                              cv_spinlock_locked, stack, 
                                              wait_index, val, wake_index, 
                                              wake_all_index, old_state_, 
                                              old_state_u, g, orig_size, 
                                              old_state, local_wseq, g1, 
                                              old_orig_size, old_g1_start, r, 
                                              s, local_wseq_, g_, seq, 
                                              local_g1_start, local_wseq_c, 
                                              g1_, do_futex_wake_, 
                                              local_wseq_cv, g1_c, 
                                              do_futex_wake, num_loops >>

cv_wait_loop(self) == /\ pc[self] = "cv_wait_loop"
                      /\ pc' = [pc EXCEPT ![self] = "cv_wait_inner_loop"]
                      /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                      wrefs_index, g_signals_index, 
                                      g_refs_index, futexes, wseq, g1_start, 
                                      g_size, did_switch_g1, g1index, waiters, 
                                      busy, spinlock_locked, 
                                      cv_spinlock_locked, stack, wait_index, 
                                      val, wake_index, wake_all_index, 
                                      old_state_, old_state_u, g, orig_size, 
                                      old_state, local_wseq, g1, old_orig_size, 
                                      old_g1_start, r, s, local_wseq_, g_, seq, 
                                      signals, local_g1_start, local_wseq_c, 
                                      g1_, do_futex_wake_, local_wseq_cv, g1_c, 
                                      do_futex_wake, num_loops >>

cv_wait_inner_loop(self) == /\ pc[self] = "cv_wait_inner_loop"
                            /\ pc' = [pc EXCEPT ![self] = "cv_wait_spin_wait"]
                            /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                            wrefs_index, g_signals_index, 
                                            g_refs_index, futexes, wseq, 
                                            g1_start, g_size, did_switch_g1, 
                                            g1index, waiters, busy, 
                                            spinlock_locked, 
                                            cv_spinlock_locked, stack, 
                                            wait_index, val, wake_index, 
                                            wake_all_index, old_state_, 
                                            old_state_u, g, orig_size, 
                                            old_state, local_wseq, g1, 
                                            old_orig_size, old_g1_start, r, s, 
                                            local_wseq_, g_, seq, signals, 
                                            local_g1_start, local_wseq_c, g1_, 
                                            do_futex_wake_, local_wseq_cv, 
                                            g1_c, do_futex_wake, num_loops >>

cv_wait_spin_wait(self) == /\ pc[self] = "cv_wait_spin_wait"
                           /\ IF signals[self] = 0
                                 THEN /\ IF seq[self] < (g1_start \div 2)
                                            THEN /\ pc' = [pc EXCEPT ![self] = "cv_wait_done"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "cv_wait_reload_signals"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "cv_wait_check_group_closed"]
                           /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                           wrefs_index, g_signals_index, 
                                           g_refs_index, futexes, wseq, 
                                           g1_start, g_size, did_switch_g1, 
                                           g1index, waiters, busy, 
                                           spinlock_locked, cv_spinlock_locked, 
                                           stack, wait_index, val, wake_index, 
                                           wake_all_index, old_state_, 
                                           old_state_u, g, orig_size, 
                                           old_state, local_wseq, g1, 
                                           old_orig_size, old_g1_start, r, s, 
                                           local_wseq_, g_, seq, signals, 
                                           local_g1_start, local_wseq_c, g1_, 
                                           do_futex_wake_, local_wseq_cv, g1_c, 
                                           do_futex_wake, num_loops >>

cv_wait_reload_signals(self) == /\ pc[self] = "cv_wait_reload_signals"
                                /\ signals' = [signals EXCEPT ![self] = futexes[g_signals_index[g_[self]]].state]
                                /\ pc' = [pc EXCEPT ![self] = "cv_wait_check_group_closed"]
                                /\ UNCHANGED << mutex_index, 
                                                g1_orig_size_index, 
                                                wrefs_index, g_signals_index, 
                                                g_refs_index, futexes, wseq, 
                                                g1_start, g_size, 
                                                did_switch_g1, g1index, 
                                                waiters, busy, spinlock_locked, 
                                                cv_spinlock_locked, stack, 
                                                wait_index, val, wake_index, 
                                                wake_all_index, old_state_, 
                                                old_state_u, g, orig_size, 
                                                old_state, local_wseq, g1, 
                                                old_orig_size, old_g1_start, r, 
                                                s, local_wseq_, g_, seq, 
                                                local_g1_start, local_wseq_c, 
                                                g1_, do_futex_wake_, 
                                                local_wseq_cv, g1_c, 
                                                do_futex_wake, num_loops >>

cv_wait_check_group_closed(self) == /\ pc[self] = "cv_wait_check_group_closed"
                                    /\ IF (signals[self] % 2) = 1
                                          THEN /\ pc' = [pc EXCEPT ![self] = "cv_wait_done"]
                                          ELSE /\ IF signals[self] /= 0
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "cv_wait_inner_loop_done"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "cv_wait_prepare_to_block"]
                                    /\ UNCHANGED << mutex_index, 
                                                    g1_orig_size_index, 
                                                    wrefs_index, 
                                                    g_signals_index, 
                                                    g_refs_index, futexes, 
                                                    wseq, g1_start, g_size, 
                                                    did_switch_g1, g1index, 
                                                    waiters, busy, 
                                                    spinlock_locked, 
                                                    cv_spinlock_locked, stack, 
                                                    wait_index, val, 
                                                    wake_index, wake_all_index, 
                                                    old_state_, old_state_u, g, 
                                                    orig_size, old_state, 
                                                    local_wseq, g1, 
                                                    old_orig_size, 
                                                    old_g1_start, r, s, 
                                                    local_wseq_, g_, seq, 
                                                    signals, local_g1_start, 
                                                    local_wseq_c, g1_, 
                                                    do_futex_wake_, 
                                                    local_wseq_cv, g1_c, 
                                                    do_futex_wake, num_loops >>

cv_wait_prepare_to_block(self) == /\ pc[self] = "cv_wait_prepare_to_block"
                                  /\ IF ~AlwaysSetGRefs
                                        THEN /\ futexes' = [futexes EXCEPT ![g_refs_index[g_[self]]].state = futexes[g_refs_index[g_[self]]].state + 2]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED futexes
                                  /\ pc' = [pc EXCEPT ![self] = "cv_wait_check_for_closed_group"]
                                  /\ UNCHANGED << mutex_index, 
                                                  g1_orig_size_index, 
                                                  wrefs_index, g_signals_index, 
                                                  g_refs_index, wseq, g1_start, 
                                                  g_size, did_switch_g1, 
                                                  g1index, waiters, busy, 
                                                  spinlock_locked, 
                                                  cv_spinlock_locked, stack, 
                                                  wait_index, val, wake_index, 
                                                  wake_all_index, old_state_, 
                                                  old_state_u, g, orig_size, 
                                                  old_state, local_wseq, g1, 
                                                  old_orig_size, old_g1_start, 
                                                  r, s, local_wseq_, g_, seq, 
                                                  signals, local_g1_start, 
                                                  local_wseq_c, g1_, 
                                                  do_futex_wake_, 
                                                  local_wseq_cv, g1_c, 
                                                  do_futex_wake, num_loops >>

cv_wait_check_for_closed_group(self) == /\ pc[self] = "cv_wait_check_for_closed_group"
                                        /\ IF (futexes[g_signals_index[g_[self]]].state % 2) = 1 \/ seq[self] < (g1_start \div 2)
                                              THEN /\ IF ~AlwaysSetGRefs
                                                         THEN /\ /\ g' = [g EXCEPT ![self] = g_[self]]
                                                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "condvar_dec_grefs",
                                                                                                          pc        |->  "cv_wait_done",
                                                                                                          g         |->  g[self] ] >>
                                                                                                      \o stack[self]]
                                                              /\ pc' = [pc EXCEPT ![self] = "dec_refs"]
                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "cv_wait_done"]
                                                              /\ UNCHANGED << stack, 
                                                                              g >>
                                                   /\ UNCHANGED << wait_index, 
                                                                   val >>
                                              ELSE /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                                               pc        |->  "cv_wait_after_woken_up_dec_grefs",
                                                                                               wait_index |->  wait_index[self],
                                                                                               val       |->  val[self] ] >>
                                                                                           \o stack[self]]
                                                      /\ val' = [val EXCEPT ![self] = 0]
                                                      /\ wait_index' = [wait_index EXCEPT ![self] = g_signals_index[g_[self]]]
                                                   /\ pc' = [pc EXCEPT ![self] = "check_state"]
                                                   /\ g' = g
                                        /\ UNCHANGED << mutex_index, 
                                                        g1_orig_size_index, 
                                                        wrefs_index, 
                                                        g_signals_index, 
                                                        g_refs_index, futexes, 
                                                        wseq, g1_start, g_size, 
                                                        did_switch_g1, g1index, 
                                                        waiters, busy, 
                                                        spinlock_locked, 
                                                        cv_spinlock_locked, 
                                                        wake_index, 
                                                        wake_all_index, 
                                                        old_state_, 
                                                        old_state_u, orig_size, 
                                                        old_state, local_wseq, 
                                                        g1, old_orig_size, 
                                                        old_g1_start, r, s, 
                                                        local_wseq_, g_, seq, 
                                                        signals, 
                                                        local_g1_start, 
                                                        local_wseq_c, g1_, 
                                                        do_futex_wake_, 
                                                        local_wseq_cv, g1_c, 
                                                        do_futex_wake, 
                                                        num_loops >>

cv_wait_after_woken_up_dec_grefs(self) == /\ pc[self] = "cv_wait_after_woken_up_dec_grefs"
                                          /\ IF ~AlwaysSetGRefs
                                                THEN /\ /\ g' = [g EXCEPT ![self] = g_[self]]
                                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "condvar_dec_grefs",
                                                                                                 pc        |->  "cv_wait_after_woken_up_reload_signals",
                                                                                                 g         |->  g[self] ] >>
                                                                                             \o stack[self]]
                                                     /\ pc' = [pc EXCEPT ![self] = "dec_refs"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "cv_wait_after_woken_up_reload_signals"]
                                                     /\ UNCHANGED << stack, g >>
                                          /\ UNCHANGED << mutex_index, 
                                                          g1_orig_size_index, 
                                                          wrefs_index, 
                                                          g_signals_index, 
                                                          g_refs_index, 
                                                          futexes, wseq, 
                                                          g1_start, g_size, 
                                                          did_switch_g1, 
                                                          g1index, waiters, 
                                                          busy, 
                                                          spinlock_locked, 
                                                          cv_spinlock_locked, 
                                                          wait_index, val, 
                                                          wake_index, 
                                                          wake_all_index, 
                                                          old_state_, 
                                                          old_state_u, 
                                                          orig_size, old_state, 
                                                          local_wseq, g1, 
                                                          old_orig_size, 
                                                          old_g1_start, r, s, 
                                                          local_wseq_, g_, seq, 
                                                          signals, 
                                                          local_g1_start, 
                                                          local_wseq_c, g1_, 
                                                          do_futex_wake_, 
                                                          local_wseq_cv, g1_c, 
                                                          do_futex_wake, 
                                                          num_loops >>

cv_wait_after_woken_up_reload_signals(self) == /\ pc[self] = "cv_wait_after_woken_up_reload_signals"
                                               /\ signals' = [signals EXCEPT ![self] = futexes[g_signals_index[g_[self]]].state]
                                               /\ pc' = [pc EXCEPT ![self] = "cv_wait_inner_loop"]
                                               /\ UNCHANGED << mutex_index, 
                                                               g1_orig_size_index, 
                                                               wrefs_index, 
                                                               g_signals_index, 
                                                               g_refs_index, 
                                                               futexes, wseq, 
                                                               g1_start, 
                                                               g_size, 
                                                               did_switch_g1, 
                                                               g1index, 
                                                               waiters, busy, 
                                                               spinlock_locked, 
                                                               cv_spinlock_locked, 
                                                               stack, 
                                                               wait_index, val, 
                                                               wake_index, 
                                                               wake_all_index, 
                                                               old_state_, 
                                                               old_state_u, g, 
                                                               orig_size, 
                                                               old_state, 
                                                               local_wseq, g1, 
                                                               old_orig_size, 
                                                               old_g1_start, r, 
                                                               s, local_wseq_, 
                                                               g_, seq, 
                                                               local_g1_start, 
                                                               local_wseq_c, 
                                                               g1_, 
                                                               do_futex_wake_, 
                                                               local_wseq_cv, 
                                                               g1_c, 
                                                               do_futex_wake, 
                                                               num_loops >>

cv_wait_inner_loop_done(self) == /\ pc[self] = "cv_wait_inner_loop_done"
                                 /\ IF futexes[g_signals_index[g_[self]]].state = signals[self]
                                       THEN /\ futexes' = [futexes EXCEPT ![g_signals_index[g_[self]]].state = signals[self] - 2]
                                            /\ pc' = [pc EXCEPT ![self] = "cv_wait_outer_loop_done"]
                                            /\ UNCHANGED signals
                                       ELSE /\ signals' = [signals EXCEPT ![self] = futexes[g_signals_index[g_[self]]].state]
                                            /\ pc' = [pc EXCEPT ![self] = "cv_wait_loop"]
                                            /\ UNCHANGED futexes
                                 /\ UNCHANGED << mutex_index, 
                                                 g1_orig_size_index, 
                                                 wrefs_index, g_signals_index, 
                                                 g_refs_index, wseq, g1_start, 
                                                 g_size, did_switch_g1, 
                                                 g1index, waiters, busy, 
                                                 spinlock_locked, 
                                                 cv_spinlock_locked, stack, 
                                                 wait_index, val, wake_index, 
                                                 wake_all_index, old_state_, 
                                                 old_state_u, g, orig_size, 
                                                 old_state, local_wseq, g1, 
                                                 old_orig_size, old_g1_start, 
                                                 r, s, local_wseq_, g_, seq, 
                                                 local_g1_start, local_wseq_c, 
                                                 g1_, do_futex_wake_, 
                                                 local_wseq_cv, g1_c, 
                                                 do_futex_wake, num_loops >>

cv_wait_outer_loop_done(self) == /\ pc[self] = "cv_wait_outer_loop_done"
                                 /\ local_g1_start' = [local_g1_start EXCEPT ![self] = g1_start]
                                 /\ IF seq[self] < (g1_start \div 2) /\ (local_g1_start'[self] % 2) /= g_[self]
                                       THEN /\ pc' = [pc EXCEPT ![self] = "cv_wait_potential_steal"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "cv_wait_done"]
                                 /\ UNCHANGED << mutex_index, 
                                                 g1_orig_size_index, 
                                                 wrefs_index, g_signals_index, 
                                                 g_refs_index, futexes, wseq, 
                                                 g1_start, g_size, 
                                                 did_switch_g1, g1index, 
                                                 waiters, busy, 
                                                 spinlock_locked, 
                                                 cv_spinlock_locked, stack, 
                                                 wait_index, val, wake_index, 
                                                 wake_all_index, old_state_, 
                                                 old_state_u, g, orig_size, 
                                                 old_state, local_wseq, g1, 
                                                 old_orig_size, old_g1_start, 
                                                 r, s, local_wseq_, g_, seq, 
                                                 signals, local_wseq_c, g1_, 
                                                 do_futex_wake_, local_wseq_cv, 
                                                 g1_c, do_futex_wake, 
                                                 num_loops >>

cv_wait_potential_steal(self) == /\ pc[self] = "cv_wait_potential_steal"
                                 /\ signals' = [signals EXCEPT ![self] = futexes[g_signals_index[g_[self]]].state]
                                 /\ pc' = [pc EXCEPT ![self] = "cv_wait_potential_steal_loop"]
                                 /\ UNCHANGED << mutex_index, 
                                                 g1_orig_size_index, 
                                                 wrefs_index, g_signals_index, 
                                                 g_refs_index, futexes, wseq, 
                                                 g1_start, g_size, 
                                                 did_switch_g1, g1index, 
                                                 waiters, busy, 
                                                 spinlock_locked, 
                                                 cv_spinlock_locked, stack, 
                                                 wait_index, val, wake_index, 
                                                 wake_all_index, old_state_, 
                                                 old_state_u, g, orig_size, 
                                                 old_state, local_wseq, g1, 
                                                 old_orig_size, old_g1_start, 
                                                 r, s, local_wseq_, g_, seq, 
                                                 local_g1_start, local_wseq_c, 
                                                 g1_, do_futex_wake_, 
                                                 local_wseq_cv, g1_c, 
                                                 do_futex_wake, num_loops >>

cv_wait_potential_steal_loop(self) == /\ pc[self] = "cv_wait_potential_steal_loop"
                                      /\ IF g1_start = local_g1_start[self]
                                            THEN /\ IF signals[self] % 2 /= 0
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "cv_wait_after_steal_wake"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "cv_wait_potential_steal_cmp_exchg"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "cv_wait_after_steal_wake"]
                                      /\ UNCHANGED << mutex_index, 
                                                      g1_orig_size_index, 
                                                      wrefs_index, 
                                                      g_signals_index, 
                                                      g_refs_index, futexes, 
                                                      wseq, g1_start, g_size, 
                                                      did_switch_g1, g1index, 
                                                      waiters, busy, 
                                                      spinlock_locked, 
                                                      cv_spinlock_locked, 
                                                      stack, wait_index, val, 
                                                      wake_index, 
                                                      wake_all_index, 
                                                      old_state_, old_state_u, 
                                                      g, orig_size, old_state, 
                                                      local_wseq, g1, 
                                                      old_orig_size, 
                                                      old_g1_start, r, s, 
                                                      local_wseq_, g_, seq, 
                                                      signals, local_g1_start, 
                                                      local_wseq_c, g1_, 
                                                      do_futex_wake_, 
                                                      local_wseq_cv, g1_c, 
                                                      do_futex_wake, num_loops >>

cv_wait_potential_steal_cmp_exchg(self) == /\ pc[self] = "cv_wait_potential_steal_cmp_exchg"
                                           /\ IF futexes[g_signals_index[g_[self]]].state = signals[self]
                                                 THEN /\ futexes' = [futexes EXCEPT ![g_signals_index[g_[self]]].state = signals[self] + 2]
                                                      /\ pc' = [pc EXCEPT ![self] = "cv_wait_after_steal_wake"]
                                                      /\ UNCHANGED signals
                                                 ELSE /\ signals' = [signals EXCEPT ![self] = futexes[g_signals_index[g_[self]]].state]
                                                      /\ pc' = [pc EXCEPT ![self] = "cv_wait_potential_steal_loop"]
                                                      /\ UNCHANGED futexes
                                           /\ UNCHANGED << mutex_index, 
                                                           g1_orig_size_index, 
                                                           wrefs_index, 
                                                           g_signals_index, 
                                                           g_refs_index, wseq, 
                                                           g1_start, g_size, 
                                                           did_switch_g1, 
                                                           g1index, waiters, 
                                                           busy, 
                                                           spinlock_locked, 
                                                           cv_spinlock_locked, 
                                                           stack, wait_index, 
                                                           val, wake_index, 
                                                           wake_all_index, 
                                                           old_state_, 
                                                           old_state_u, g, 
                                                           orig_size, 
                                                           old_state, 
                                                           local_wseq, g1, 
                                                           old_orig_size, 
                                                           old_g1_start, r, s, 
                                                           local_wseq_, g_, 
                                                           seq, local_g1_start, 
                                                           local_wseq_c, g1_, 
                                                           do_futex_wake_, 
                                                           local_wseq_cv, g1_c, 
                                                           do_futex_wake, 
                                                           num_loops >>

cv_wait_after_steal_wake(self) == /\ pc[self] = "cv_wait_after_steal_wake"
                                  /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_single",
                                                                              pc        |->  "cv_wait_after_steal_patch",
                                                                              wake_index |->  wake_index[self] ] >>
                                                                          \o stack[self]]
                                     /\ wake_index' = [wake_index EXCEPT ![self] = g_signals_index[g_[self]]]
                                  /\ pc' = [pc EXCEPT ![self] = "check_for_sleepers"]
                                  /\ UNCHANGED << mutex_index, 
                                                  g1_orig_size_index, 
                                                  wrefs_index, g_signals_index, 
                                                  g_refs_index, futexes, wseq, 
                                                  g1_start, g_size, 
                                                  did_switch_g1, g1index, 
                                                  waiters, busy, 
                                                  spinlock_locked, 
                                                  cv_spinlock_locked, 
                                                  wait_index, val, 
                                                  wake_all_index, old_state_, 
                                                  old_state_u, g, orig_size, 
                                                  old_state, local_wseq, g1, 
                                                  old_orig_size, old_g1_start, 
                                                  r, s, local_wseq_, g_, seq, 
                                                  signals, local_g1_start, 
                                                  local_wseq_c, g1_, 
                                                  do_futex_wake_, 
                                                  local_wseq_cv, g1_c, 
                                                  do_futex_wake, num_loops >>

cv_wait_after_steal_patch(self) == /\ pc[self] = "cv_wait_after_steal_patch"
                                   /\ IF UsePatch
                                         THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "cv_broadcast",
                                                                                       pc        |->  "cv_wait_done",
                                                                                       local_wseq_cv |->  local_wseq_cv[self],
                                                                                       g1_c      |->  g1_c[self],
                                                                                       do_futex_wake |->  do_futex_wake[self] ] >>
                                                                                   \o stack[self]]
                                              /\ local_wseq_cv' = [local_wseq_cv EXCEPT ![self] = 0]
                                              /\ g1_c' = [g1_c EXCEPT ![self] = 0]
                                              /\ do_futex_wake' = [do_futex_wake EXCEPT ![self] = FALSE]
                                              /\ pc' = [pc EXCEPT ![self] = "check_for_waiters"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "cv_wait_done"]
                                              /\ UNCHANGED << stack, 
                                                              local_wseq_cv, 
                                                              g1_c, 
                                                              do_futex_wake >>
                                   /\ UNCHANGED << mutex_index, 
                                                   g1_orig_size_index, 
                                                   wrefs_index, 
                                                   g_signals_index, 
                                                   g_refs_index, futexes, wseq, 
                                                   g1_start, g_size, 
                                                   did_switch_g1, g1index, 
                                                   waiters, busy, 
                                                   spinlock_locked, 
                                                   cv_spinlock_locked, 
                                                   wait_index, val, wake_index, 
                                                   wake_all_index, old_state_, 
                                                   old_state_u, g, orig_size, 
                                                   old_state, local_wseq, g1, 
                                                   old_orig_size, old_g1_start, 
                                                   r, s, local_wseq_, g_, seq, 
                                                   signals, local_g1_start, 
                                                   local_wseq_c, g1_, 
                                                   do_futex_wake_, num_loops >>

cv_wait_done(self) == /\ pc[self] = "cv_wait_done"
                      /\ IF AlwaysSetGRefs
                            THEN /\ /\ g' = [g EXCEPT ![self] = g_[self]]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "condvar_dec_grefs",
                                                                             pc        |->  "cv_wait_after_done_dec_grefs",
                                                                             g         |->  g[self] ] >>
                                                                         \o stack[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "dec_refs"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "cv_wait_after_done_dec_grefs"]
                                 /\ UNCHANGED << stack, g >>
                      /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                      wrefs_index, g_signals_index, 
                                      g_refs_index, futexes, wseq, g1_start, 
                                      g_size, did_switch_g1, g1index, waiters, 
                                      busy, spinlock_locked, 
                                      cv_spinlock_locked, wait_index, val, 
                                      wake_index, wake_all_index, old_state_, 
                                      old_state_u, orig_size, old_state, 
                                      local_wseq, g1, old_orig_size, 
                                      old_g1_start, r, s, local_wseq_, g_, seq, 
                                      signals, local_g1_start, local_wseq_c, 
                                      g1_, do_futex_wake_, local_wseq_cv, g1_c, 
                                      do_futex_wake, num_loops >>

cv_wait_after_done_dec_grefs(self) == /\ pc[self] = "cv_wait_after_done_dec_grefs"
                                      /\ futexes' = [futexes EXCEPT ![wrefs_index].state = futexes[wrefs_index].state - 8]
                                      /\ IF futexes'[wrefs_index].state \div 4 = 1
                                            THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_all",
                                                                                             pc        |->  "cv_wait_retake_mutex",
                                                                                             wake_all_index |->  wake_all_index[self] ] >>
                                                                                         \o stack[self]]
                                                    /\ wake_all_index' = [wake_all_index EXCEPT ![self] = wrefs_index]
                                                 /\ pc' = [pc EXCEPT ![self] = "futex_wake_all_"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "cv_wait_retake_mutex"]
                                                 /\ UNCHANGED << stack, 
                                                                 wake_all_index >>
                                      /\ UNCHANGED << mutex_index, 
                                                      g1_orig_size_index, 
                                                      wrefs_index, 
                                                      g_signals_index, 
                                                      g_refs_index, wseq, 
                                                      g1_start, g_size, 
                                                      did_switch_g1, g1index, 
                                                      waiters, busy, 
                                                      spinlock_locked, 
                                                      cv_spinlock_locked, 
                                                      wait_index, val, 
                                                      wake_index, old_state_, 
                                                      old_state_u, g, 
                                                      orig_size, old_state, 
                                                      local_wseq, g1, 
                                                      old_orig_size, 
                                                      old_g1_start, r, s, 
                                                      local_wseq_, g_, seq, 
                                                      signals, local_g1_start, 
                                                      local_wseq_c, g1_, 
                                                      do_futex_wake_, 
                                                      local_wseq_cv, g1_c, 
                                                      do_futex_wake, num_loops >>

cv_wait_retake_mutex(self) == /\ pc[self] = "cv_wait_retake_mutex"
                              /\ /\ g_' = [g_ EXCEPT ![self] = Head(stack[self]).g_]
                                 /\ local_g1_start' = [local_g1_start EXCEPT ![self] = Head(stack[self]).local_g1_start]
                                 /\ local_wseq_' = [local_wseq_ EXCEPT ![self] = Head(stack[self]).local_wseq_]
                                 /\ seq' = [seq EXCEPT ![self] = Head(stack[self]).seq]
                                 /\ signals' = [signals EXCEPT ![self] = Head(stack[self]).signals]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock_mutex",
                                                                          pc        |->  Head(stack[self]).pc,
                                                                          old_state_ |->  old_state_[self] ] >>
                                                                      \o Tail(stack[self])]
                              /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
                              /\ pc' = [pc EXCEPT ![self] = "lock_mutex_start"]
                              /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                              wrefs_index, g_signals_index, 
                                              g_refs_index, futexes, wseq, 
                                              g1_start, g_size, did_switch_g1, 
                                              g1index, waiters, busy, 
                                              spinlock_locked, 
                                              cv_spinlock_locked, wait_index, 
                                              val, wake_index, wake_all_index, 
                                              old_state_u, g, orig_size, 
                                              old_state, local_wseq, g1, 
                                              old_orig_size, old_g1_start, r, 
                                              s, local_wseq_c, g1_, 
                                              do_futex_wake_, local_wseq_cv, 
                                              g1_c, do_futex_wake, num_loops >>

cv_wait(self) == cv_wait_fetch_seq(self) \/ cv_wait_incr_wrefs(self)
                    \/ cv_wait_incr_grefs(self)
                    \/ cv_wait_load_signals(self) \/ cv_wait_loop(self)
                    \/ cv_wait_inner_loop(self) \/ cv_wait_spin_wait(self)
                    \/ cv_wait_reload_signals(self)
                    \/ cv_wait_check_group_closed(self)
                    \/ cv_wait_prepare_to_block(self)
                    \/ cv_wait_check_for_closed_group(self)
                    \/ cv_wait_after_woken_up_dec_grefs(self)
                    \/ cv_wait_after_woken_up_reload_signals(self)
                    \/ cv_wait_inner_loop_done(self)
                    \/ cv_wait_outer_loop_done(self)
                    \/ cv_wait_potential_steal(self)
                    \/ cv_wait_potential_steal_loop(self)
                    \/ cv_wait_potential_steal_cmp_exchg(self)
                    \/ cv_wait_after_steal_wake(self)
                    \/ cv_wait_after_steal_patch(self)
                    \/ cv_wait_done(self)
                    \/ cv_wait_after_done_dec_grefs(self)
                    \/ cv_wait_retake_mutex(self)

check_for_waiters_(self) == /\ pc[self] = "check_for_waiters_"
                            /\ IF futexes[wrefs_index].state \div 8 = 0
                                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ local_wseq_c' = [local_wseq_c EXCEPT ![self] = Head(stack[self]).local_wseq_c]
                                       /\ g1_' = [g1_ EXCEPT ![self] = Head(stack[self]).g1_]
                                       /\ do_futex_wake_' = [do_futex_wake_ EXCEPT ![self] = Head(stack[self]).do_futex_wake_]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                       /\ UNCHANGED orig_size
                                  ELSE /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "condvar_acquire_lock",
                                                                                pc        |->  "cv_signal_load_wseq",
                                                                                orig_size |->  orig_size[self] ] >>
                                                                            \o stack[self]]
                                       /\ orig_size' = [orig_size EXCEPT ![self] = 0]
                                       /\ pc' = [pc EXCEPT ![self] = "cv_acquire_lock"]
                                       /\ UNCHANGED << local_wseq_c, g1_, 
                                                       do_futex_wake_ >>
                            /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                            wrefs_index, g_signals_index, 
                                            g_refs_index, futexes, wseq, 
                                            g1_start, g_size, did_switch_g1, 
                                            g1index, waiters, busy, 
                                            spinlock_locked, 
                                            cv_spinlock_locked, wait_index, 
                                            val, wake_index, wake_all_index, 
                                            old_state_, old_state_u, g, 
                                            old_state, local_wseq, g1, 
                                            old_orig_size, old_g1_start, r, s, 
                                            local_wseq_, g_, seq, signals, 
                                            local_g1_start, local_wseq_cv, 
                                            g1_c, do_futex_wake, num_loops >>

cv_signal_load_wseq(self) == /\ pc[self] = "cv_signal_load_wseq"
                             /\ local_wseq_c' = [local_wseq_c EXCEPT ![self] = wseq \div 2]
                             /\ g1_' = [g1_ EXCEPT ![self] = Xor1(wseq % 2)]
                             /\ pc' = [pc EXCEPT ![self] = "cv_signal_check_size"]
                             /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                             wrefs_index, g_signals_index, 
                                             g_refs_index, futexes, wseq, 
                                             g1_start, g_size, did_switch_g1, 
                                             g1index, waiters, busy, 
                                             spinlock_locked, 
                                             cv_spinlock_locked, stack, 
                                             wait_index, val, wake_index, 
                                             wake_all_index, old_state_, 
                                             old_state_u, g, orig_size, 
                                             old_state, local_wseq, g1, 
                                             old_orig_size, old_g1_start, r, s, 
                                             local_wseq_, g_, seq, signals, 
                                             local_g1_start, do_futex_wake_, 
                                             local_wseq_cv, g1_c, 
                                             do_futex_wake, num_loops >>

cv_signal_check_size(self) == /\ pc[self] = "cv_signal_check_size"
                              /\ IF g_size[g1_[self]] = 0
                                    THEN /\ /\ g1' = [g1 EXCEPT ![self] = g1_[self]]
                                            /\ local_wseq' = [local_wseq EXCEPT ![self] = local_wseq_c[self]]
                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "condvar_quiesce_and_switch_g1",
                                                                                     pc        |->  "cv_signal_after_switch",
                                                                                     old_orig_size |->  old_orig_size[self],
                                                                                     old_g1_start |->  old_g1_start[self],
                                                                                     r         |->  r[self],
                                                                                     s         |->  s[self],
                                                                                     local_wseq |->  local_wseq[self],
                                                                                     g1        |->  g1[self] ] >>
                                                                                 \o stack[self]]
                                         /\ old_orig_size' = [old_orig_size EXCEPT ![self] = 0]
                                         /\ old_g1_start' = [old_g1_start EXCEPT ![self] = 0]
                                         /\ r' = [r EXCEPT ![self] = 0]
                                         /\ s' = [s EXCEPT ![self] = 0]
                                         /\ pc' = [pc EXCEPT ![self] = "quiesce_and_switch_start"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "cv_signal_add_signal"]
                                         /\ UNCHANGED << stack, local_wseq, g1, 
                                                         old_orig_size, 
                                                         old_g1_start, r, s >>
                              /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                              wrefs_index, g_signals_index, 
                                              g_refs_index, futexes, wseq, 
                                              g1_start, g_size, did_switch_g1, 
                                              g1index, waiters, busy, 
                                              spinlock_locked, 
                                              cv_spinlock_locked, wait_index, 
                                              val, wake_index, wake_all_index, 
                                              old_state_, old_state_u, g, 
                                              orig_size, old_state, 
                                              local_wseq_, g_, seq, signals, 
                                              local_g1_start, local_wseq_c, 
                                              g1_, do_futex_wake_, 
                                              local_wseq_cv, g1_c, 
                                              do_futex_wake, num_loops >>

cv_signal_after_switch(self) == /\ pc[self] = "cv_signal_after_switch"
                                /\ g1_' = [g1_ EXCEPT ![self] = g1index[self]]
                                /\ pc' = [pc EXCEPT ![self] = "cv_signal_check_for_early_out"]
                                /\ UNCHANGED << mutex_index, 
                                                g1_orig_size_index, 
                                                wrefs_index, g_signals_index, 
                                                g_refs_index, futexes, wseq, 
                                                g1_start, g_size, 
                                                did_switch_g1, g1index, 
                                                waiters, busy, spinlock_locked, 
                                                cv_spinlock_locked, stack, 
                                                wait_index, val, wake_index, 
                                                wake_all_index, old_state_, 
                                                old_state_u, g, orig_size, 
                                                old_state, local_wseq, g1, 
                                                old_orig_size, old_g1_start, r, 
                                                s, local_wseq_, g_, seq, 
                                                signals, local_g1_start, 
                                                local_wseq_c, do_futex_wake_, 
                                                local_wseq_cv, g1_c, 
                                                do_futex_wake, num_loops >>

cv_signal_check_for_early_out(self) == /\ pc[self] = "cv_signal_check_for_early_out"
                                       /\ IF ~did_switch_g1[self]
                                             THEN /\ /\ do_futex_wake_' = [do_futex_wake_ EXCEPT ![self] = Head(stack[self]).do_futex_wake_]
                                                     /\ g1_' = [g1_ EXCEPT ![self] = Head(stack[self]).g1_]
                                                     /\ local_wseq_c' = [local_wseq_c EXCEPT ![self] = Head(stack[self]).local_wseq_c]
                                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "condvar_release_lock",
                                                                                              pc        |->  Head(stack[self]).pc,
                                                                                              old_state |->  old_state[self] ] >>
                                                                                          \o Tail(stack[self])]
                                                  /\ old_state' = [old_state EXCEPT ![self] = 0]
                                                  /\ pc' = [pc EXCEPT ![self] = "cv_release_lock"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "cv_signal_add_signal"]
                                                  /\ UNCHANGED << stack, 
                                                                  old_state, 
                                                                  local_wseq_c, 
                                                                  g1_, 
                                                                  do_futex_wake_ >>
                                       /\ UNCHANGED << mutex_index, 
                                                       g1_orig_size_index, 
                                                       wrefs_index, 
                                                       g_signals_index, 
                                                       g_refs_index, futexes, 
                                                       wseq, g1_start, g_size, 
                                                       did_switch_g1, g1index, 
                                                       waiters, busy, 
                                                       spinlock_locked, 
                                                       cv_spinlock_locked, 
                                                       wait_index, val, 
                                                       wake_index, 
                                                       wake_all_index, 
                                                       old_state_, old_state_u, 
                                                       g, orig_size, 
                                                       local_wseq, g1, 
                                                       old_orig_size, 
                                                       old_g1_start, r, s, 
                                                       local_wseq_, g_, seq, 
                                                       signals, local_g1_start, 
                                                       local_wseq_cv, g1_c, 
                                                       do_futex_wake, 
                                                       num_loops >>

cv_signal_add_signal(self) == /\ pc[self] = "cv_signal_add_signal"
                              /\ futexes' = [futexes EXCEPT ![g_signals_index[g1_[self]]].state = futexes[g_signals_index[g1_[self]]].state + 2]
                              /\ pc' = [pc EXCEPT ![self] = "cv_signal_decrease_size"]
                              /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                              wrefs_index, g_signals_index, 
                                              g_refs_index, wseq, g1_start, 
                                              g_size, did_switch_g1, g1index, 
                                              waiters, busy, spinlock_locked, 
                                              cv_spinlock_locked, stack, 
                                              wait_index, val, wake_index, 
                                              wake_all_index, old_state_, 
                                              old_state_u, g, orig_size, 
                                              old_state, local_wseq, g1, 
                                              old_orig_size, old_g1_start, r, 
                                              s, local_wseq_, g_, seq, signals, 
                                              local_g1_start, local_wseq_c, 
                                              g1_, do_futex_wake_, 
                                              local_wseq_cv, g1_c, 
                                              do_futex_wake, num_loops >>

cv_signal_decrease_size(self) == /\ pc[self] = "cv_signal_decrease_size"
                                 /\ g_size' = [g_size EXCEPT ![g1_[self]] = g_size[g1_[self]] - 1]
                                 /\ do_futex_wake_' = [do_futex_wake_ EXCEPT ![self] = TRUE]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "condvar_release_lock",
                                                                          pc        |->  "cv_signal_maybe_wake",
                                                                          old_state |->  old_state[self] ] >>
                                                                      \o stack[self]]
                                 /\ old_state' = [old_state EXCEPT ![self] = 0]
                                 /\ pc' = [pc EXCEPT ![self] = "cv_release_lock"]
                                 /\ UNCHANGED << mutex_index, 
                                                 g1_orig_size_index, 
                                                 wrefs_index, g_signals_index, 
                                                 g_refs_index, futexes, wseq, 
                                                 g1_start, did_switch_g1, 
                                                 g1index, waiters, busy, 
                                                 spinlock_locked, 
                                                 cv_spinlock_locked, 
                                                 wait_index, val, wake_index, 
                                                 wake_all_index, old_state_, 
                                                 old_state_u, g, orig_size, 
                                                 local_wseq, g1, old_orig_size, 
                                                 old_g1_start, r, s, 
                                                 local_wseq_, g_, seq, signals, 
                                                 local_g1_start, local_wseq_c, 
                                                 g1_, local_wseq_cv, g1_c, 
                                                 do_futex_wake, num_loops >>

cv_signal_maybe_wake(self) == /\ pc[self] = "cv_signal_maybe_wake"
                              /\ IF do_futex_wake_[self]
                                    THEN /\ /\ do_futex_wake_' = [do_futex_wake_ EXCEPT ![self] = Head(stack[self]).do_futex_wake_]
                                            /\ g1_' = [g1_ EXCEPT ![self] = Head(stack[self]).g1_]
                                            /\ local_wseq_c' = [local_wseq_c EXCEPT ![self] = Head(stack[self]).local_wseq_c]
                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_single",
                                                                                     pc        |->  Head(stack[self]).pc,
                                                                                     wake_index |->  wake_index[self] ] >>
                                                                                 \o Tail(stack[self])]
                                            /\ wake_index' = [wake_index EXCEPT ![self] = g_signals_index[g1_[self]]]
                                         /\ pc' = [pc EXCEPT ![self] = "check_for_sleepers"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                         /\ local_wseq_c' = [local_wseq_c EXCEPT ![self] = Head(stack[self]).local_wseq_c]
                                         /\ g1_' = [g1_ EXCEPT ![self] = Head(stack[self]).g1_]
                                         /\ do_futex_wake_' = [do_futex_wake_ EXCEPT ![self] = Head(stack[self]).do_futex_wake_]
                                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                         /\ UNCHANGED wake_index
                              /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                              wrefs_index, g_signals_index, 
                                              g_refs_index, futexes, wseq, 
                                              g1_start, g_size, did_switch_g1, 
                                              g1index, waiters, busy, 
                                              spinlock_locked, 
                                              cv_spinlock_locked, wait_index, 
                                              val, wake_all_index, old_state_, 
                                              old_state_u, g, orig_size, 
                                              old_state, local_wseq, g1, 
                                              old_orig_size, old_g1_start, r, 
                                              s, local_wseq_, g_, seq, signals, 
                                              local_g1_start, local_wseq_cv, 
                                              g1_c, do_futex_wake, num_loops >>

cv_signal(self) == check_for_waiters_(self) \/ cv_signal_load_wseq(self)
                      \/ cv_signal_check_size(self)
                      \/ cv_signal_after_switch(self)
                      \/ cv_signal_check_for_early_out(self)
                      \/ cv_signal_add_signal(self)
                      \/ cv_signal_decrease_size(self)
                      \/ cv_signal_maybe_wake(self)

check_for_waiters(self) == /\ pc[self] = "check_for_waiters"
                           /\ IF futexes[wrefs_index].state \div 8 = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                      /\ local_wseq_cv' = [local_wseq_cv EXCEPT ![self] = Head(stack[self]).local_wseq_cv]
                                      /\ g1_c' = [g1_c EXCEPT ![self] = Head(stack[self]).g1_c]
                                      /\ do_futex_wake' = [do_futex_wake EXCEPT ![self] = Head(stack[self]).do_futex_wake]
                                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                      /\ UNCHANGED orig_size
                                 ELSE /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "condvar_acquire_lock",
                                                                               pc        |->  "cv_broadcast_load_wseq",
                                                                               orig_size |->  orig_size[self] ] >>
                                                                           \o stack[self]]
                                      /\ orig_size' = [orig_size EXCEPT ![self] = 0]
                                      /\ pc' = [pc EXCEPT ![self] = "cv_acquire_lock"]
                                      /\ UNCHANGED << local_wseq_cv, g1_c, 
                                                      do_futex_wake >>
                           /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                           wrefs_index, g_signals_index, 
                                           g_refs_index, futexes, wseq, 
                                           g1_start, g_size, did_switch_g1, 
                                           g1index, waiters, busy, 
                                           spinlock_locked, cv_spinlock_locked, 
                                           wait_index, val, wake_index, 
                                           wake_all_index, old_state_, 
                                           old_state_u, g, old_state, 
                                           local_wseq, g1, old_orig_size, 
                                           old_g1_start, r, s, local_wseq_, g_, 
                                           seq, signals, local_g1_start, 
                                           local_wseq_c, g1_, do_futex_wake_, 
                                           num_loops >>

cv_broadcast_load_wseq(self) == /\ pc[self] = "cv_broadcast_load_wseq"
                                /\ local_wseq_cv' = [local_wseq_cv EXCEPT ![self] = wseq \div 2]
                                /\ g1_c' = [g1_c EXCEPT ![self] = Xor1(wseq % 2)]
                                /\ pc' = [pc EXCEPT ![self] = "cv_broacast_check_size1"]
                                /\ UNCHANGED << mutex_index, 
                                                g1_orig_size_index, 
                                                wrefs_index, g_signals_index, 
                                                g_refs_index, futexes, wseq, 
                                                g1_start, g_size, 
                                                did_switch_g1, g1index, 
                                                waiters, busy, spinlock_locked, 
                                                cv_spinlock_locked, stack, 
                                                wait_index, val, wake_index, 
                                                wake_all_index, old_state_, 
                                                old_state_u, g, orig_size, 
                                                old_state, local_wseq, g1, 
                                                old_orig_size, old_g1_start, r, 
                                                s, local_wseq_, g_, seq, 
                                                signals, local_g1_start, 
                                                local_wseq_c, g1_, 
                                                do_futex_wake_, do_futex_wake, 
                                                num_loops >>

cv_broacast_check_size1(self) == /\ pc[self] = "cv_broacast_check_size1"
                                 /\ IF g_size[g1_c[self]] /= 0
                                       THEN /\ pc' = [pc EXCEPT ![self] = "cv_broadcast_signal_g1"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "cv_broadcast_switch_g1"]
                                 /\ UNCHANGED << mutex_index, 
                                                 g1_orig_size_index, 
                                                 wrefs_index, g_signals_index, 
                                                 g_refs_index, futexes, wseq, 
                                                 g1_start, g_size, 
                                                 did_switch_g1, g1index, 
                                                 waiters, busy, 
                                                 spinlock_locked, 
                                                 cv_spinlock_locked, stack, 
                                                 wait_index, val, wake_index, 
                                                 wake_all_index, old_state_, 
                                                 old_state_u, g, orig_size, 
                                                 old_state, local_wseq, g1, 
                                                 old_orig_size, old_g1_start, 
                                                 r, s, local_wseq_, g_, seq, 
                                                 signals, local_g1_start, 
                                                 local_wseq_c, g1_, 
                                                 do_futex_wake_, local_wseq_cv, 
                                                 g1_c, do_futex_wake, 
                                                 num_loops >>

cv_broadcast_signal_g1(self) == /\ pc[self] = "cv_broadcast_signal_g1"
                                /\ futexes' = [futexes EXCEPT ![g_signals_index[g1_c[self]]].state = futexes[g_signals_index[g1_c[self]]].state + (g_size[g1_c[self]] * 2)]
                                /\ pc' = [pc EXCEPT ![self] = "cv_broadcast_clear_size1"]
                                /\ UNCHANGED << mutex_index, 
                                                g1_orig_size_index, 
                                                wrefs_index, g_signals_index, 
                                                g_refs_index, wseq, g1_start, 
                                                g_size, did_switch_g1, g1index, 
                                                waiters, busy, spinlock_locked, 
                                                cv_spinlock_locked, stack, 
                                                wait_index, val, wake_index, 
                                                wake_all_index, old_state_, 
                                                old_state_u, g, orig_size, 
                                                old_state, local_wseq, g1, 
                                                old_orig_size, old_g1_start, r, 
                                                s, local_wseq_, g_, seq, 
                                                signals, local_g1_start, 
                                                local_wseq_c, g1_, 
                                                do_futex_wake_, local_wseq_cv, 
                                                g1_c, do_futex_wake, num_loops >>

cv_broadcast_clear_size1(self) == /\ pc[self] = "cv_broadcast_clear_size1"
                                  /\ g_size' = [g_size EXCEPT ![g1_c[self]] = 0]
                                  /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_all",
                                                                              pc        |->  "cv_broadcast_switch_g1",
                                                                              wake_all_index |->  wake_all_index[self] ] >>
                                                                          \o stack[self]]
                                     /\ wake_all_index' = [wake_all_index EXCEPT ![self] = g_signals_index[g1_c[self]]]
                                  /\ pc' = [pc EXCEPT ![self] = "futex_wake_all_"]
                                  /\ UNCHANGED << mutex_index, 
                                                  g1_orig_size_index, 
                                                  wrefs_index, g_signals_index, 
                                                  g_refs_index, futexes, wseq, 
                                                  g1_start, did_switch_g1, 
                                                  g1index, waiters, busy, 
                                                  spinlock_locked, 
                                                  cv_spinlock_locked, 
                                                  wait_index, val, wake_index, 
                                                  old_state_, old_state_u, g, 
                                                  orig_size, old_state, 
                                                  local_wseq, g1, 
                                                  old_orig_size, old_g1_start, 
                                                  r, s, local_wseq_, g_, seq, 
                                                  signals, local_g1_start, 
                                                  local_wseq_c, g1_, 
                                                  do_futex_wake_, 
                                                  local_wseq_cv, g1_c, 
                                                  do_futex_wake, num_loops >>

cv_broadcast_switch_g1(self) == /\ pc[self] = "cv_broadcast_switch_g1"
                                /\ /\ g1' = [g1 EXCEPT ![self] = g1_c[self]]
                                   /\ local_wseq' = [local_wseq EXCEPT ![self] = local_wseq_cv[self]]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "condvar_quiesce_and_switch_g1",
                                                                            pc        |->  "cv_broadcast_after_switch",
                                                                            old_orig_size |->  old_orig_size[self],
                                                                            old_g1_start |->  old_g1_start[self],
                                                                            r         |->  r[self],
                                                                            s         |->  s[self],
                                                                            local_wseq |->  local_wseq[self],
                                                                            g1        |->  g1[self] ] >>
                                                                        \o stack[self]]
                                /\ old_orig_size' = [old_orig_size EXCEPT ![self] = 0]
                                /\ old_g1_start' = [old_g1_start EXCEPT ![self] = 0]
                                /\ r' = [r EXCEPT ![self] = 0]
                                /\ s' = [s EXCEPT ![self] = 0]
                                /\ pc' = [pc EXCEPT ![self] = "quiesce_and_switch_start"]
                                /\ UNCHANGED << mutex_index, 
                                                g1_orig_size_index, 
                                                wrefs_index, g_signals_index, 
                                                g_refs_index, futexes, wseq, 
                                                g1_start, g_size, 
                                                did_switch_g1, g1index, 
                                                waiters, busy, spinlock_locked, 
                                                cv_spinlock_locked, wait_index, 
                                                val, wake_index, 
                                                wake_all_index, old_state_, 
                                                old_state_u, g, orig_size, 
                                                old_state, local_wseq_, g_, 
                                                seq, signals, local_g1_start, 
                                                local_wseq_c, g1_, 
                                                do_futex_wake_, local_wseq_cv, 
                                                g1_c, do_futex_wake, num_loops >>

cv_broadcast_after_switch(self) == /\ pc[self] = "cv_broadcast_after_switch"
                                   /\ g1_c' = [g1_c EXCEPT ![self] = g1index[self]]
                                   /\ IF did_switch_g1[self]
                                         THEN /\ pc' = [pc EXCEPT ![self] = "cv_broadcast_signal_g2"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "cv_broadcast_release_lock"]
                                   /\ UNCHANGED << mutex_index, 
                                                   g1_orig_size_index, 
                                                   wrefs_index, 
                                                   g_signals_index, 
                                                   g_refs_index, futexes, wseq, 
                                                   g1_start, g_size, 
                                                   did_switch_g1, g1index, 
                                                   waiters, busy, 
                                                   spinlock_locked, 
                                                   cv_spinlock_locked, stack, 
                                                   wait_index, val, wake_index, 
                                                   wake_all_index, old_state_, 
                                                   old_state_u, g, orig_size, 
                                                   old_state, local_wseq, g1, 
                                                   old_orig_size, old_g1_start, 
                                                   r, s, local_wseq_, g_, seq, 
                                                   signals, local_g1_start, 
                                                   local_wseq_c, g1_, 
                                                   do_futex_wake_, 
                                                   local_wseq_cv, 
                                                   do_futex_wake, num_loops >>

cv_broadcast_signal_g2(self) == /\ pc[self] = "cv_broadcast_signal_g2"
                                /\ futexes' = [futexes EXCEPT ![g_signals_index[g1_c[self]]].state = futexes[g_signals_index[g1_c[self]]].state + (g_size[g1_c[self]] * 2)]
                                /\ pc' = [pc EXCEPT ![self] = "cv_broadcast_clear_size2"]
                                /\ UNCHANGED << mutex_index, 
                                                g1_orig_size_index, 
                                                wrefs_index, g_signals_index, 
                                                g_refs_index, wseq, g1_start, 
                                                g_size, did_switch_g1, g1index, 
                                                waiters, busy, spinlock_locked, 
                                                cv_spinlock_locked, stack, 
                                                wait_index, val, wake_index, 
                                                wake_all_index, old_state_, 
                                                old_state_u, g, orig_size, 
                                                old_state, local_wseq, g1, 
                                                old_orig_size, old_g1_start, r, 
                                                s, local_wseq_, g_, seq, 
                                                signals, local_g1_start, 
                                                local_wseq_c, g1_, 
                                                do_futex_wake_, local_wseq_cv, 
                                                g1_c, do_futex_wake, num_loops >>

cv_broadcast_clear_size2(self) == /\ pc[self] = "cv_broadcast_clear_size2"
                                  /\ g_size' = [g_size EXCEPT ![g1_c[self]] = 0]
                                  /\ do_futex_wake' = [do_futex_wake EXCEPT ![self] = TRUE]
                                  /\ pc' = [pc EXCEPT ![self] = "cv_broadcast_release_lock"]
                                  /\ UNCHANGED << mutex_index, 
                                                  g1_orig_size_index, 
                                                  wrefs_index, g_signals_index, 
                                                  g_refs_index, futexes, wseq, 
                                                  g1_start, did_switch_g1, 
                                                  g1index, waiters, busy, 
                                                  spinlock_locked, 
                                                  cv_spinlock_locked, stack, 
                                                  wait_index, val, wake_index, 
                                                  wake_all_index, old_state_, 
                                                  old_state_u, g, orig_size, 
                                                  old_state, local_wseq, g1, 
                                                  old_orig_size, old_g1_start, 
                                                  r, s, local_wseq_, g_, seq, 
                                                  signals, local_g1_start, 
                                                  local_wseq_c, g1_, 
                                                  do_futex_wake_, 
                                                  local_wseq_cv, g1_c, 
                                                  num_loops >>

cv_broadcast_release_lock(self) == /\ pc[self] = "cv_broadcast_release_lock"
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "condvar_release_lock",
                                                                            pc        |->  "cv_broadcast_maybe_wake",
                                                                            old_state |->  old_state[self] ] >>
                                                                        \o stack[self]]
                                   /\ old_state' = [old_state EXCEPT ![self] = 0]
                                   /\ pc' = [pc EXCEPT ![self] = "cv_release_lock"]
                                   /\ UNCHANGED << mutex_index, 
                                                   g1_orig_size_index, 
                                                   wrefs_index, 
                                                   g_signals_index, 
                                                   g_refs_index, futexes, wseq, 
                                                   g1_start, g_size, 
                                                   did_switch_g1, g1index, 
                                                   waiters, busy, 
                                                   spinlock_locked, 
                                                   cv_spinlock_locked, 
                                                   wait_index, val, wake_index, 
                                                   wake_all_index, old_state_, 
                                                   old_state_u, g, orig_size, 
                                                   local_wseq, g1, 
                                                   old_orig_size, old_g1_start, 
                                                   r, s, local_wseq_, g_, seq, 
                                                   signals, local_g1_start, 
                                                   local_wseq_c, g1_, 
                                                   do_futex_wake_, 
                                                   local_wseq_cv, g1_c, 
                                                   do_futex_wake, num_loops >>

cv_broadcast_maybe_wake(self) == /\ pc[self] = "cv_broadcast_maybe_wake"
                                 /\ IF do_futex_wake[self]
                                       THEN /\ /\ do_futex_wake' = [do_futex_wake EXCEPT ![self] = Head(stack[self]).do_futex_wake]
                                               /\ g1_c' = [g1_c EXCEPT ![self] = Head(stack[self]).g1_c]
                                               /\ local_wseq_cv' = [local_wseq_cv EXCEPT ![self] = Head(stack[self]).local_wseq_cv]
                                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_all",
                                                                                        pc        |->  Head(stack[self]).pc,
                                                                                        wake_all_index |->  wake_all_index[self] ] >>
                                                                                    \o Tail(stack[self])]
                                               /\ wake_all_index' = [wake_all_index EXCEPT ![self] = g_signals_index[g1_c[self]]]
                                            /\ pc' = [pc EXCEPT ![self] = "futex_wake_all_"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                            /\ local_wseq_cv' = [local_wseq_cv EXCEPT ![self] = Head(stack[self]).local_wseq_cv]
                                            /\ g1_c' = [g1_c EXCEPT ![self] = Head(stack[self]).g1_c]
                                            /\ do_futex_wake' = [do_futex_wake EXCEPT ![self] = Head(stack[self]).do_futex_wake]
                                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                            /\ UNCHANGED wake_all_index
                                 /\ UNCHANGED << mutex_index, 
                                                 g1_orig_size_index, 
                                                 wrefs_index, g_signals_index, 
                                                 g_refs_index, futexes, wseq, 
                                                 g1_start, g_size, 
                                                 did_switch_g1, g1index, 
                                                 waiters, busy, 
                                                 spinlock_locked, 
                                                 cv_spinlock_locked, 
                                                 wait_index, val, wake_index, 
                                                 old_state_, old_state_u, g, 
                                                 orig_size, old_state, 
                                                 local_wseq, g1, old_orig_size, 
                                                 old_g1_start, r, s, 
                                                 local_wseq_, g_, seq, signals, 
                                                 local_g1_start, local_wseq_c, 
                                                 g1_, do_futex_wake_, 
                                                 num_loops >>

cv_broadcast(self) == check_for_waiters(self)
                         \/ cv_broadcast_load_wseq(self)
                         \/ cv_broacast_check_size1(self)
                         \/ cv_broadcast_signal_g1(self)
                         \/ cv_broadcast_clear_size1(self)
                         \/ cv_broadcast_switch_g1(self)
                         \/ cv_broadcast_after_switch(self)
                         \/ cv_broadcast_signal_g2(self)
                         \/ cv_broadcast_clear_size2(self)
                         \/ cv_broadcast_release_lock(self)
                         \/ cv_broadcast_maybe_wake(self)

acquire_masterlock_start(self) == /\ pc[self] = "acquire_masterlock_start"
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock_mutex",
                                                                           pc        |->  "acquire_masterlock_loop",
                                                                           old_state_ |->  old_state_[self] ] >>
                                                                       \o stack[self]]
                                  /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
                                  /\ pc' = [pc EXCEPT ![self] = "lock_mutex_start"]
                                  /\ UNCHANGED << mutex_index, 
                                                  g1_orig_size_index, 
                                                  wrefs_index, g_signals_index, 
                                                  g_refs_index, futexes, wseq, 
                                                  g1_start, g_size, 
                                                  did_switch_g1, g1index, 
                                                  waiters, busy, 
                                                  spinlock_locked, 
                                                  cv_spinlock_locked, 
                                                  wait_index, val, wake_index, 
                                                  wake_all_index, old_state_u, 
                                                  g, orig_size, old_state, 
                                                  local_wseq, g1, 
                                                  old_orig_size, old_g1_start, 
                                                  r, s, local_wseq_, g_, seq, 
                                                  signals, local_g1_start, 
                                                  local_wseq_c, g1_, 
                                                  do_futex_wake_, 
                                                  local_wseq_cv, g1_c, 
                                                  do_futex_wake, num_loops >>

acquire_masterlock_loop(self) == /\ pc[self] = "acquire_masterlock_loop"
                                 /\ IF busy
                                       THEN /\ waiters' = waiters + 1
                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "cv_wait",
                                                                                     pc        |->  "acquire_lock_after_wait",
                                                                                     local_wseq_ |->  local_wseq_[self],
                                                                                     g_        |->  g_[self],
                                                                                     seq       |->  seq[self],
                                                                                     signals   |->  signals[self],
                                                                                     local_g1_start |->  local_g1_start[self] ] >>
                                                                                 \o stack[self]]
                                            /\ local_wseq_' = [local_wseq_ EXCEPT ![self] = 0]
                                            /\ g_' = [g_ EXCEPT ![self] = 0]
                                            /\ seq' = [seq EXCEPT ![self] = 0]
                                            /\ signals' = [signals EXCEPT ![self] = 0]
                                            /\ local_g1_start' = [local_g1_start EXCEPT ![self] = 0]
                                            /\ pc' = [pc EXCEPT ![self] = "cv_wait_fetch_seq"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "acquire_masterlock_after_loop"]
                                            /\ UNCHANGED << waiters, stack, 
                                                            local_wseq_, g_, 
                                                            seq, signals, 
                                                            local_g1_start >>
                                 /\ UNCHANGED << mutex_index, 
                                                 g1_orig_size_index, 
                                                 wrefs_index, g_signals_index, 
                                                 g_refs_index, futexes, wseq, 
                                                 g1_start, g_size, 
                                                 did_switch_g1, g1index, busy, 
                                                 spinlock_locked, 
                                                 cv_spinlock_locked, 
                                                 wait_index, val, wake_index, 
                                                 wake_all_index, old_state_, 
                                                 old_state_u, g, orig_size, 
                                                 old_state, local_wseq, g1, 
                                                 old_orig_size, old_g1_start, 
                                                 r, s, local_wseq_c, g1_, 
                                                 do_futex_wake_, local_wseq_cv, 
                                                 g1_c, do_futex_wake, 
                                                 num_loops >>

acquire_lock_after_wait(self) == /\ pc[self] = "acquire_lock_after_wait"
                                 /\ waiters' = waiters - 1
                                 /\ pc' = [pc EXCEPT ![self] = "acquire_masterlock_loop"]
                                 /\ UNCHANGED << mutex_index, 
                                                 g1_orig_size_index, 
                                                 wrefs_index, g_signals_index, 
                                                 g_refs_index, futexes, wseq, 
                                                 g1_start, g_size, 
                                                 did_switch_g1, g1index, busy, 
                                                 spinlock_locked, 
                                                 cv_spinlock_locked, stack, 
                                                 wait_index, val, wake_index, 
                                                 wake_all_index, old_state_, 
                                                 old_state_u, g, orig_size, 
                                                 old_state, local_wseq, g1, 
                                                 old_orig_size, old_g1_start, 
                                                 r, s, local_wseq_, g_, seq, 
                                                 signals, local_g1_start, 
                                                 local_wseq_c, g1_, 
                                                 do_futex_wake_, local_wseq_cv, 
                                                 g1_c, do_futex_wake, 
                                                 num_loops >>

acquire_masterlock_after_loop(self) == /\ pc[self] = "acquire_masterlock_after_loop"
                                       /\ busy' = TRUE
                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock_mutex",
                                                                                pc        |->  Head(stack[self]).pc,
                                                                                old_state_u |->  old_state_u[self] ] >>
                                                                            \o Tail(stack[self])]
                                       /\ old_state_u' = [old_state_u EXCEPT ![self] = 0]
                                       /\ pc' = [pc EXCEPT ![self] = "unlock_mutex_start"]
                                       /\ UNCHANGED << mutex_index, 
                                                       g1_orig_size_index, 
                                                       wrefs_index, 
                                                       g_signals_index, 
                                                       g_refs_index, futexes, 
                                                       wseq, g1_start, g_size, 
                                                       did_switch_g1, g1index, 
                                                       waiters, 
                                                       spinlock_locked, 
                                                       cv_spinlock_locked, 
                                                       wait_index, val, 
                                                       wake_index, 
                                                       wake_all_index, 
                                                       old_state_, g, 
                                                       orig_size, old_state, 
                                                       local_wseq, g1, 
                                                       old_orig_size, 
                                                       old_g1_start, r, s, 
                                                       local_wseq_, g_, seq, 
                                                       signals, local_g1_start, 
                                                       local_wseq_c, g1_, 
                                                       do_futex_wake_, 
                                                       local_wseq_cv, g1_c, 
                                                       do_futex_wake, 
                                                       num_loops >>

acquire_masterlock(self) == acquire_masterlock_start(self)
                               \/ acquire_masterlock_loop(self)
                               \/ acquire_lock_after_wait(self)
                               \/ acquire_masterlock_after_loop(self)

release_masterlock_start(self) == /\ pc[self] = "release_masterlock_start"
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock_mutex",
                                                                           pc        |->  "release_masterlock_after_lock",
                                                                           old_state_ |->  old_state_[self] ] >>
                                                                       \o stack[self]]
                                  /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
                                  /\ pc' = [pc EXCEPT ![self] = "lock_mutex_start"]
                                  /\ UNCHANGED << mutex_index, 
                                                  g1_orig_size_index, 
                                                  wrefs_index, g_signals_index, 
                                                  g_refs_index, futexes, wseq, 
                                                  g1_start, g_size, 
                                                  did_switch_g1, g1index, 
                                                  waiters, busy, 
                                                  spinlock_locked, 
                                                  cv_spinlock_locked, 
                                                  wait_index, val, wake_index, 
                                                  wake_all_index, old_state_u, 
                                                  g, orig_size, old_state, 
                                                  local_wseq, g1, 
                                                  old_orig_size, old_g1_start, 
                                                  r, s, local_wseq_, g_, seq, 
                                                  signals, local_g1_start, 
                                                  local_wseq_c, g1_, 
                                                  do_futex_wake_, 
                                                  local_wseq_cv, g1_c, 
                                                  do_futex_wake, num_loops >>

release_masterlock_after_lock(self) == /\ pc[self] = "release_masterlock_after_lock"
                                       /\ busy' = FALSE
                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock_mutex",
                                                                                pc        |->  "release_masterlock_signal",
                                                                                old_state_u |->  old_state_u[self] ] >>
                                                                            \o stack[self]]
                                       /\ old_state_u' = [old_state_u EXCEPT ![self] = 0]
                                       /\ pc' = [pc EXCEPT ![self] = "unlock_mutex_start"]
                                       /\ UNCHANGED << mutex_index, 
                                                       g1_orig_size_index, 
                                                       wrefs_index, 
                                                       g_signals_index, 
                                                       g_refs_index, futexes, 
                                                       wseq, g1_start, g_size, 
                                                       did_switch_g1, g1index, 
                                                       waiters, 
                                                       spinlock_locked, 
                                                       cv_spinlock_locked, 
                                                       wait_index, val, 
                                                       wake_index, 
                                                       wake_all_index, 
                                                       old_state_, g, 
                                                       orig_size, old_state, 
                                                       local_wseq, g1, 
                                                       old_orig_size, 
                                                       old_g1_start, r, s, 
                                                       local_wseq_, g_, seq, 
                                                       signals, local_g1_start, 
                                                       local_wseq_c, g1_, 
                                                       do_futex_wake_, 
                                                       local_wseq_cv, g1_c, 
                                                       do_futex_wake, 
                                                       num_loops >>

release_masterlock_signal(self) == /\ pc[self] = "release_masterlock_signal"
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "cv_signal",
                                                                            pc        |->  Head(stack[self]).pc,
                                                                            local_wseq_c |->  local_wseq_c[self],
                                                                            g1_       |->  g1_[self],
                                                                            do_futex_wake_ |->  do_futex_wake_[self] ] >>
                                                                        \o Tail(stack[self])]
                                   /\ local_wseq_c' = [local_wseq_c EXCEPT ![self] = 0]
                                   /\ g1_' = [g1_ EXCEPT ![self] = 0]
                                   /\ do_futex_wake_' = [do_futex_wake_ EXCEPT ![self] = FALSE]
                                   /\ pc' = [pc EXCEPT ![self] = "check_for_waiters_"]
                                   /\ UNCHANGED << mutex_index, 
                                                   g1_orig_size_index, 
                                                   wrefs_index, 
                                                   g_signals_index, 
                                                   g_refs_index, futexes, wseq, 
                                                   g1_start, g_size, 
                                                   did_switch_g1, g1index, 
                                                   waiters, busy, 
                                                   spinlock_locked, 
                                                   cv_spinlock_locked, 
                                                   wait_index, val, wake_index, 
                                                   wake_all_index, old_state_, 
                                                   old_state_u, g, orig_size, 
                                                   old_state, local_wseq, g1, 
                                                   old_orig_size, old_g1_start, 
                                                   r, s, local_wseq_, g_, seq, 
                                                   signals, local_g1_start, 
                                                   local_wseq_cv, g1_c, 
                                                   do_futex_wake, num_loops >>

release_masterlock(self) == release_masterlock_start(self)
                               \/ release_masterlock_after_lock(self)
                               \/ release_masterlock_signal(self)

yield_start(self) == /\ pc[self] = "yield_start"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock_mutex",
                                                              pc        |->  "yield_after_lock",
                                                              old_state_ |->  old_state_[self] ] >>
                                                          \o stack[self]]
                     /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "lock_mutex_start"]
                     /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                     wrefs_index, g_signals_index, 
                                     g_refs_index, futexes, wseq, g1_start, 
                                     g_size, did_switch_g1, g1index, waiters, 
                                     busy, spinlock_locked, cv_spinlock_locked, 
                                     wait_index, val, wake_index, 
                                     wake_all_index, old_state_u, g, orig_size, 
                                     old_state, local_wseq, g1, old_orig_size, 
                                     old_g1_start, r, s, local_wseq_, g_, seq, 
                                     signals, local_g1_start, local_wseq_c, 
                                     g1_, do_futex_wake_, local_wseq_cv, g1_c, 
                                     do_futex_wake, num_loops >>

yield_after_lock(self) == /\ pc[self] = "yield_after_lock"
                          /\ IF waiters = 0
                                THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock_mutex",
                                                                              pc        |->  Head(stack[self]).pc,
                                                                              old_state_u |->  old_state_u[self] ] >>
                                                                          \o Tail(stack[self])]
                                     /\ old_state_u' = [old_state_u EXCEPT ![self] = 0]
                                     /\ pc' = [pc EXCEPT ![self] = "unlock_mutex_start"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "yield_after_waiter_check"]
                                     /\ UNCHANGED << stack, old_state_u >>
                          /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                          wrefs_index, g_signals_index, 
                                          g_refs_index, futexes, wseq, 
                                          g1_start, g_size, did_switch_g1, 
                                          g1index, waiters, busy, 
                                          spinlock_locked, cv_spinlock_locked, 
                                          wait_index, val, wake_index, 
                                          wake_all_index, old_state_, g, 
                                          orig_size, old_state, local_wseq, g1, 
                                          old_orig_size, old_g1_start, r, s, 
                                          local_wseq_, g_, seq, signals, 
                                          local_g1_start, local_wseq_c, g1_, 
                                          do_futex_wake_, local_wseq_cv, g1_c, 
                                          do_futex_wake, num_loops >>

yield_after_waiter_check(self) == /\ pc[self] = "yield_after_waiter_check"
                                  /\ busy' = FALSE
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "cv_signal",
                                                                           pc        |->  "yield_after_signal",
                                                                           local_wseq_c |->  local_wseq_c[self],
                                                                           g1_       |->  g1_[self],
                                                                           do_futex_wake_ |->  do_futex_wake_[self] ] >>
                                                                       \o stack[self]]
                                  /\ local_wseq_c' = [local_wseq_c EXCEPT ![self] = 0]
                                  /\ g1_' = [g1_ EXCEPT ![self] = 0]
                                  /\ do_futex_wake_' = [do_futex_wake_ EXCEPT ![self] = FALSE]
                                  /\ pc' = [pc EXCEPT ![self] = "check_for_waiters_"]
                                  /\ UNCHANGED << mutex_index, 
                                                  g1_orig_size_index, 
                                                  wrefs_index, g_signals_index, 
                                                  g_refs_index, futexes, wseq, 
                                                  g1_start, g_size, 
                                                  did_switch_g1, g1index, 
                                                  waiters, spinlock_locked, 
                                                  cv_spinlock_locked, 
                                                  wait_index, val, wake_index, 
                                                  wake_all_index, old_state_, 
                                                  old_state_u, g, orig_size, 
                                                  old_state, local_wseq, g1, 
                                                  old_orig_size, old_g1_start, 
                                                  r, s, local_wseq_, g_, seq, 
                                                  signals, local_g1_start, 
                                                  local_wseq_cv, g1_c, 
                                                  do_futex_wake, num_loops >>

yield_after_signal(self) == /\ pc[self] = "yield_after_signal"
                            /\ waiters' = waiters + 1
                            /\ pc' = [pc EXCEPT ![self] = "yield_loop"]
                            /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                            wrefs_index, g_signals_index, 
                                            g_refs_index, futexes, wseq, 
                                            g1_start, g_size, did_switch_g1, 
                                            g1index, busy, spinlock_locked, 
                                            cv_spinlock_locked, stack, 
                                            wait_index, val, wake_index, 
                                            wake_all_index, old_state_, 
                                            old_state_u, g, orig_size, 
                                            old_state, local_wseq, g1, 
                                            old_orig_size, old_g1_start, r, s, 
                                            local_wseq_, g_, seq, signals, 
                                            local_g1_start, local_wseq_c, g1_, 
                                            do_futex_wake_, local_wseq_cv, 
                                            g1_c, do_futex_wake, num_loops >>

yield_loop(self) == /\ pc[self] = "yield_loop"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "cv_wait",
                                                             pc        |->  "yield_after_wait",
                                                             local_wseq_ |->  local_wseq_[self],
                                                             g_        |->  g_[self],
                                                             seq       |->  seq[self],
                                                             signals   |->  signals[self],
                                                             local_g1_start |->  local_g1_start[self] ] >>
                                                         \o stack[self]]
                    /\ local_wseq_' = [local_wseq_ EXCEPT ![self] = 0]
                    /\ g_' = [g_ EXCEPT ![self] = 0]
                    /\ seq' = [seq EXCEPT ![self] = 0]
                    /\ signals' = [signals EXCEPT ![self] = 0]
                    /\ local_g1_start' = [local_g1_start EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "cv_wait_fetch_seq"]
                    /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                    wrefs_index, g_signals_index, g_refs_index, 
                                    futexes, wseq, g1_start, g_size, 
                                    did_switch_g1, g1index, waiters, busy, 
                                    spinlock_locked, cv_spinlock_locked, 
                                    wait_index, val, wake_index, 
                                    wake_all_index, old_state_, old_state_u, g, 
                                    orig_size, old_state, local_wseq, g1, 
                                    old_orig_size, old_g1_start, r, s, 
                                    local_wseq_c, g1_, do_futex_wake_, 
                                    local_wseq_cv, g1_c, do_futex_wake, 
                                    num_loops >>

yield_after_wait(self) == /\ pc[self] = "yield_after_wait"
                          /\ IF ~busy
                                THEN /\ pc' = [pc EXCEPT ![self] = "yield_after_loop"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "yield_loop"]
                          /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                          wrefs_index, g_signals_index, 
                                          g_refs_index, futexes, wseq, 
                                          g1_start, g_size, did_switch_g1, 
                                          g1index, waiters, busy, 
                                          spinlock_locked, cv_spinlock_locked, 
                                          stack, wait_index, val, wake_index, 
                                          wake_all_index, old_state_, 
                                          old_state_u, g, orig_size, old_state, 
                                          local_wseq, g1, old_orig_size, 
                                          old_g1_start, r, s, local_wseq_, g_, 
                                          seq, signals, local_g1_start, 
                                          local_wseq_c, g1_, do_futex_wake_, 
                                          local_wseq_cv, g1_c, do_futex_wake, 
                                          num_loops >>

yield_after_loop(self) == /\ pc[self] = "yield_after_loop"
                          /\ busy' = TRUE
                          /\ pc' = [pc EXCEPT ![self] = "yield_dec_waiters"]
                          /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                          wrefs_index, g_signals_index, 
                                          g_refs_index, futexes, wseq, 
                                          g1_start, g_size, did_switch_g1, 
                                          g1index, waiters, spinlock_locked, 
                                          cv_spinlock_locked, stack, 
                                          wait_index, val, wake_index, 
                                          wake_all_index, old_state_, 
                                          old_state_u, g, orig_size, old_state, 
                                          local_wseq, g1, old_orig_size, 
                                          old_g1_start, r, s, local_wseq_, g_, 
                                          seq, signals, local_g1_start, 
                                          local_wseq_c, g1_, do_futex_wake_, 
                                          local_wseq_cv, g1_c, do_futex_wake, 
                                          num_loops >>

yield_dec_waiters(self) == /\ pc[self] = "yield_dec_waiters"
                           /\ waiters' = waiters - 1
                           /\ pc' = [pc EXCEPT ![self] = "yield_done"]
                           /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                           wrefs_index, g_signals_index, 
                                           g_refs_index, futexes, wseq, 
                                           g1_start, g_size, did_switch_g1, 
                                           g1index, busy, spinlock_locked, 
                                           cv_spinlock_locked, stack, 
                                           wait_index, val, wake_index, 
                                           wake_all_index, old_state_, 
                                           old_state_u, g, orig_size, 
                                           old_state, local_wseq, g1, 
                                           old_orig_size, old_g1_start, r, s, 
                                           local_wseq_, g_, seq, signals, 
                                           local_g1_start, local_wseq_c, g1_, 
                                           do_futex_wake_, local_wseq_cv, g1_c, 
                                           do_futex_wake, num_loops >>

yield_done(self) == /\ pc[self] = "yield_done"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock_mutex",
                                                             pc        |->  Head(stack[self]).pc,
                                                             old_state_u |->  old_state_u[self] ] >>
                                                         \o Tail(stack[self])]
                    /\ old_state_u' = [old_state_u EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "unlock_mutex_start"]
                    /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                    wrefs_index, g_signals_index, g_refs_index, 
                                    futexes, wseq, g1_start, g_size, 
                                    did_switch_g1, g1index, waiters, busy, 
                                    spinlock_locked, cv_spinlock_locked, 
                                    wait_index, val, wake_index, 
                                    wake_all_index, old_state_, g, orig_size, 
                                    old_state, local_wseq, g1, old_orig_size, 
                                    old_g1_start, r, s, local_wseq_, g_, seq, 
                                    signals, local_g1_start, local_wseq_c, g1_, 
                                    do_futex_wake_, local_wseq_cv, g1_c, 
                                    do_futex_wake, num_loops >>

yield_masterlock(self) == yield_start(self) \/ yield_after_lock(self)
                             \/ yield_after_waiter_check(self)
                             \/ yield_after_signal(self)
                             \/ yield_loop(self) \/ yield_after_wait(self)
                             \/ yield_after_loop(self)
                             \/ yield_dec_waiters(self) \/ yield_done(self)

proc_start(self) == /\ pc[self] = "proc_start"
                    /\ IF num_loops[self] > 0
                          THEN /\ num_loops' = [num_loops EXCEPT ![self] = num_loops[self] - 1]
                               /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "acquire_masterlock",
                                                                              pc        |->  "proc_loop_done" ] >>
                                                                          \o stack[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "acquire_masterlock_start"]
                                  \/ /\ pc' = [pc EXCEPT ![self] = "proc_done"]
                                     /\ stack' = stack
                          ELSE /\ pc' = [pc EXCEPT ![self] = "proc_done"]
                               /\ UNCHANGED << stack, num_loops >>
                    /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                    wrefs_index, g_signals_index, g_refs_index, 
                                    futexes, wseq, g1_start, g_size, 
                                    did_switch_g1, g1index, waiters, busy, 
                                    spinlock_locked, cv_spinlock_locked, 
                                    wait_index, val, wake_index, 
                                    wake_all_index, old_state_, old_state_u, g, 
                                    orig_size, old_state, local_wseq, g1, 
                                    old_orig_size, old_g1_start, r, s, 
                                    local_wseq_, g_, seq, signals, 
                                    local_g1_start, local_wseq_c, g1_, 
                                    do_futex_wake_, local_wseq_cv, g1_c, 
                                    do_futex_wake >>

proc_loop_done(self) == /\ pc[self] = "proc_loop_done"
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "release_masterlock",
                                                                 pc        |->  "proc_start" ] >>
                                                             \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "release_masterlock_start"]
                        /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                        wrefs_index, g_signals_index, 
                                        g_refs_index, futexes, wseq, g1_start, 
                                        g_size, did_switch_g1, g1index, 
                                        waiters, busy, spinlock_locked, 
                                        cv_spinlock_locked, wait_index, val, 
                                        wake_index, wake_all_index, old_state_, 
                                        old_state_u, g, orig_size, old_state, 
                                        local_wseq, g1, old_orig_size, 
                                        old_g1_start, r, s, local_wseq_, g_, 
                                        seq, signals, local_g1_start, 
                                        local_wseq_c, g1_, do_futex_wake_, 
                                        local_wseq_cv, g1_c, do_futex_wake, 
                                        num_loops >>

proc_done(self) == /\ pc[self] = "proc_done"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << mutex_index, g1_orig_size_index, 
                                   wrefs_index, g_signals_index, g_refs_index, 
                                   futexes, wseq, g1_start, g_size, 
                                   did_switch_g1, g1index, waiters, busy, 
                                   spinlock_locked, cv_spinlock_locked, stack, 
                                   wait_index, val, wake_index, wake_all_index, 
                                   old_state_, old_state_u, g, orig_size, 
                                   old_state, local_wseq, g1, old_orig_size, 
                                   old_g1_start, r, s, local_wseq_, g_, seq, 
                                   signals, local_g1_start, local_wseq_c, g1_, 
                                   do_futex_wake_, local_wseq_cv, g1_c, 
                                   do_futex_wake, num_loops >>

Proc(self) == proc_start(self) \/ proc_loop_done(self) \/ proc_done(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ futex_wait(self)
                               \/ futex_wake_single(self)
                               \/ futex_wake_all(self) \/ lock_mutex(self)
                               \/ unlock_mutex(self)
                               \/ condvar_dec_grefs(self)
                               \/ condvar_acquire_lock(self)
                               \/ condvar_release_lock(self)
                               \/ condvar_quiesce_and_switch_g1(self)
                               \/ cv_wait(self) \/ cv_signal(self)
                               \/ cv_broadcast(self)
                               \/ acquire_masterlock(self)
                               \/ release_masterlock(self)
                               \/ yield_masterlock(self))
           \/ (\E self \in Procs: Proc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : /\ WF_vars(Proc(self))
                               /\ WF_vars(acquire_masterlock(self))
                               /\ WF_vars(release_masterlock(self))
                               /\ WF_vars(futex_wait(self))
                               /\ WF_vars(futex_wake_single(self))
                               /\ WF_vars(futex_wake_all(self))
                               /\ WF_vars(lock_mutex(self))
                               /\ WF_vars(unlock_mutex(self))
                               /\ WF_vars(condvar_dec_grefs(self))
                               /\ WF_vars(condvar_acquire_lock(self))
                               /\ WF_vars(condvar_release_lock(self))
                               /\ WF_vars(condvar_quiesce_and_switch_g1(self))
                               /\ WF_vars(cv_wait(self))
                               /\ WF_vars(cv_broadcast(self))
                               /\ WF_vars(cv_signal(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TestClearBit == /\ ClearBit(0, 0) = 0
                /\ ClearBit(1, 0) = 0
                /\ ClearBit(2, 0) = 2
                /\ ClearBit(3, 0) = 2
                /\ ClearBit(4, 0) = 4
                /\ ClearBit(0, 1) = 0
                /\ ClearBit(1, 1) = 1
                /\ ClearBit(2, 1) = 0
                /\ ClearBit(3, 1) = 1
                /\ ClearBit(4, 1) = 4
                /\ ClearBit(5, 1) = 5
                /\ ClearBit(6, 1) = 4
                /\ ClearBit(7, 1) = 5
                /\ ClearBit(8, 1) = 8

\*MutualExclusion == \A i, j \in WorkerProcs : 
\*                     (i # j) => ~ /\ pc[i] = "take_work"
\*                                  /\ pc[j] = "take_work"
\*
\*Trying(i) == stack[i] /= <<>> /\ Head(stack[i]).procedure = "lock_mutex"
\*
\*DeadlockFree == \A i \in WorkerProcs : 
\*                     Trying(i) ~> (\E j \in WorkerProcs : pc[j] = "cs")
\*
\*StarvationFree == \A i \in WorkerProcs : 
\*                     Trying(i) ~> (pc[i] = "cs")
\*
\*WorkGetsTaken == work_to_do > 0 ~> work_to_do = 0
\*WorkGetsDone == work_to_do > 0 ~> work_done
\*
\*ShutdownCorrectly == done = GeneratorProcs ~> (\A self \in ProcSet : pc[self] = "Done")
\*
\*NotInPotentialSteal == \A i \in WorkerProcs : pc[i] /= "cv_wait_potential_steal_cmp_exchg"
\*MutualExclusion2 == \A i, j \in WorkerProcs : 
\*                     (i # j) => ~ /\ pc[i] = "cv_wait_potential_steal_cmp_exchg"
\*                                  /\ pc[j] = "cv_wait_potential_steal_cmp_exchg"
\*                                  
\*WorkDoneAtEnd == (\A i \in WorkerProcs : pc[i] = "Done") => work_done \/ work_to_do = 0
\*
\*InPotentialStealAndAdds == \E i \in WorkerProcs: pc[i] = "cv_wait_potential_steal_cmp_exchg" /\ futexes[g_signals_index[g_[i]]].state = signals[i]
\*
\*PotentialStealThenWorkGetsDone == (\E i \in WorkerProcs: pc[i] = "cv_wait_potential_steal_cmp_exchg" /\ futexes[g_signals_index[g_[i]]].state = signals[i]) ~> (\A i \in WorkerProcs : pc[i] = "Done")

SomeoneGetsTheLock == (\E i \in Procs: pc[i] = "acquire_masterlock_start") ~> (\E i \in Procs: pc[i] = "proc_loop")
YieldingWorks == (\E i \in Procs: pc[i] = "yield_loop") ~> (\E i \in Procs: pc[i] = "proc_loop")

=============================================================================
\* Modification History
\* Last modified Sat Sep 17 10:25:00 EDT 2022 by malte
\* Created Mon Oct 12 21:12:21 EDT 2020 by malte
