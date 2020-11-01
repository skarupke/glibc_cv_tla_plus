(* Copyright (C) 2020 Malte Skarupke

   This is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   See https://www.gnu.org/licenses/.  *)

------------------------- MODULE spinlock_blog_post -------------------------

EXTENDS Integers, Sequences

CONSTANT Proc 

(*

--algorithm Spinlock 
{
variables locked = FALSE;

procedure lock()
variable old_value = FALSE;
{
exchange:
  old_value := locked;
  locked := TRUE;
check:
  if (old_value)
  {
    goto exchange;
  }
  else
  {
    return;
  };
};

procedure unlock()
{
reset_state:
  locked := FALSE;
  return;
}

fair process (P \in Proc)
{
loop:-
  while (TRUE)
  {
    call lock();
  cs:
    skip;
    call unlock();
  };
}
}
*)
\* BEGIN TRANSLATION
VARIABLES locked, pc, stack, old_value

vars == << locked, pc, stack, old_value >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ locked = FALSE
        (* Procedure lock *)
        /\ old_value = [ self \in ProcSet |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "loop"]

exchange(self) == /\ pc[self] = "exchange"
                  /\ old_value' = [old_value EXCEPT ![self] = locked]
                  /\ locked' = TRUE
                  /\ pc' = [pc EXCEPT ![self] = "check"]
                  /\ stack' = stack

check(self) == /\ pc[self] = "check"
               /\ IF old_value[self]
                     THEN /\ pc' = [pc EXCEPT ![self] = "exchange"]
                          /\ UNCHANGED << stack, old_value >>
                     ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ old_value' = [old_value EXCEPT ![self] = Head(stack[self]).old_value]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED locked

lock(self) == exchange(self) \/ check(self)

reset_state(self) == /\ pc[self] = "reset_state"
                     /\ locked' = FALSE
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED old_value

unlock(self) == reset_state(self)

loop(self) == /\ pc[self] = "loop"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                       pc        |->  "cs",
                                                       old_value |->  old_value[self] ] >>
                                                   \o stack[self]]
              /\ old_value' = [old_value EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "exchange"]
              /\ UNCHANGED locked

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                     pc        |->  "loop" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "reset_state"]
            /\ UNCHANGED << locked, old_value >>

P(self) == loop(self) \/ cs(self)

Next == (\E self \in ProcSet: lock(self) \/ unlock(self))
           \/ (\E self \in Proc: P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proc : /\ WF_vars((pc[self] # "loop") /\ P(self))
                              /\ WF_vars(lock(self))
                              /\ WF_vars(unlock(self))

\* END TRANSLATION

MutualExclusion == \A i, j \in Proc : 
                     (i # j) => ~ /\ pc[i] = "cs"
                                  /\ pc[j] = "cs"

DeadlockFreedom == 
    \A i \in Proc : 
      (pc[i] = "exchange") ~> (\E j \in Proc : pc[j] = "cs")


=============================================================================
\* Modification History
\* Last modified Sun Oct 25 00:30:17 EDT 2020 by malte
\* Last modified Sun Oct 25 00:18:46 EDT 2020 by malte
\* Last modified Sat Jan 01 12:14:14 PST 2011 by lamport
\* Created Fri Dec 31 14:14:14 PST 2010 by lamport
