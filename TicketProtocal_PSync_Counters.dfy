//============================================================
// Protocol Specification
//============================================================

//============================================================
// Process behaviors
//============================================================

type Process = nat
datatype CState = Idle | Waiting | Critical
const P : set<Process>;
const pNull := 0;
const Phi: nat;

datatype PState = PState( ticket: nat,
                          serving: nat,
                          cs: map<Process, CState>,
                          hasTicket: map<Process, nat>,
                            task_no: map<Process, nat>,
                            done: map<Process, nat>
)

datatype SState = SState(
    pState: PState,
    timer: map<Process, nat>,
    scheduled: map<Process, bool>,
    busyCriticalArea: bool,
    clock: nat
)

predicate IsProcess(p: Process)
{
    p in P
}

predicate InitPState(s: PState) 
{
    && s.cs.Keys == s.hasTicket.Keys == s.task_no.Keys == s.done.Keys == P
    && s.ticket == s.serving == 1
    && (forall p :: IsProcess(p) ==> s.cs[p] == Idle)
    && (forall p :: IsProcess(p) ==> s.hasTicket[p] == 0)
    && (forall p :: IsProcess(p) ==> s.task_no[p] == 0)
    && (forall p :: IsProcess(p) ==> s.done[p] == 0)
}

predicate Init(s: SState)   
{
    && !IsProcess(pNull)
    && Phi > 0
    && s.timer.Keys == s.scheduled.Keys == P
    && (forall p :: IsProcess(p) ==> s.timer[p] == 1)
    && (forall p :: IsProcess(p) ==> !s.scheduled[p])
    && !s.busyCriticalArea
    && InitPState(s.pState)
}

predicate Next(s: SState, s': SState)
{
    && Valid(s)
    && ( || (SetTimer(s, s'))
         || (exists p | IsProcess(p) :: NextP(s, p, s')) )
}

predicate SetTimer(s: SState, s': SState)
requires Valid(s)
{
    && (forall p :: IsProcess(p) ==> !s.scheduled[p])
    //
    && s'.pState == s.pState
    //
    && s'.timer.Keys == s'.scheduled.Keys == P
    && (forall p :: IsProcess(p) ==> (s'.timer[p] == 0 || s'.timer[p] == s.timer[p] + 1))
    && (forall p :: IsProcess(p) ==> (s'.timer[p] <= Phi))
    && (forall p :: IsProcess(p) ==> (s'.scheduled[p] <==> (s'.timer[p] == 0)))
    && (s'.busyCriticalArea <==> (exists p: Process :: IsProcess(p) && s'.pState.cs[p] == Critical))
    
}

predicate NextP(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    || Request(s, p, s')
    || Wait(s, p, s')
    || Enter(s, p, s')
    || Leave(s, p, s')
    || CreateTasks(s, p, s')   
    || FinishOneTask(s, p, s')  
}

predicate Request(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    && s.scheduled[p]
    && s.pState.cs[p] == Idle    
    //
    && s'.timer == s.timer
    && s'.scheduled == s.scheduled[p := false]
    && s'.busyCriticalArea == s.busyCriticalArea
    //    
    && s'.pState.hasTicket == s.pState.hasTicket[p := s.pState.ticket]
    && s'.pState.ticket == s.pState.ticket + 1
    && s'.pState.serving == s.pState.serving
    && s'.pState.cs == s.pState.cs[p := Waiting]
    //
    && s'.pState.task_no == s.pState.task_no
    && s'.pState.done == s.pState.done
}

predicate Wait(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    && s.scheduled[p]
    && s.pState.hasTicket[p] > s.pState.serving
    && s.pState.cs[p] == Waiting
    //
    && s'.timer == s.timer
    && s'.scheduled == s.scheduled[p := false]
    && s'.busyCriticalArea == s.busyCriticalArea
    //
    && s'.pState.ticket == s.pState.ticket
    && s'.pState.serving == s.pState.serving
    && s'.pState.hasTicket == s.pState.hasTicket
    && s'.pState.cs == s.pState.cs
    //
    && s'.pState.task_no == s.pState.task_no
    && s'.pState.done == s.pState.done
}


predicate Enter(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    && s.scheduled[p]
    && s.pState.cs[p] == Waiting
    && s.pState.hasTicket[p] == s.pState.serving
    //
    && s'.timer == s.timer
    && s'.scheduled == s.scheduled[p := false]
    && s'.busyCriticalArea 
    //    
    && s'.pState.ticket == s.pState.ticket
    && s'.pState.serving == s.pState.serving
    && s'.pState.hasTicket == s.pState.hasTicket
    && s'.pState.cs == s.pState.cs[p := Critical]
    //
    && s'.pState.task_no == s.pState.task_no
    && s'.pState.done == s.pState.done
}

predicate CreateTasks(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{      
    var k :| k > 0;

    && s.scheduled[p]
    && s.pState.cs[p] == Critical
    && s.pState.task_no[p] == 0 
    //
    && s'.timer == s.timer
    && s'.scheduled == s.scheduled[p := false]
    && s'.busyCriticalArea == s.busyCriticalArea
    //   
    && s'.pState.ticket == s.pState.ticket
    && s'.pState.serving == s.pState.serving 
    && s'.pState.cs == s.pState.cs
    && s'.pState.hasTicket== s.pState.hasTicket
    && s'.pState.task_no == s.pState.task_no[p := k]
    && s'.pState.done == s.pState.done      
}

predicate FinishOneTask(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{   
    && s.scheduled[p]
    //
    && s.pState.cs[p] == Critical
    && 0 < s.pState.task_no[p]
    && s.pState.done[p] < s.pState.task_no[p] 
    //
    && s'.timer == s.timer
    && s'.scheduled == s.scheduled[p := false]
    && s'.busyCriticalArea == s.busyCriticalArea   
    // 
    && s'.pState.ticket == s.pState.ticket
    && s'.pState.serving == s.pState.serving  
    && s'.pState.cs == s.pState.cs
    && s'.pState.hasTicket== s.pState.hasTicket
    && s'.pState.task_no == s.pState.task_no
    && s'.pState.done == s.pState.done[p := s.pState.done[p] + 1]      
}


predicate Leave(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    && s.scheduled[p]
    && s.pState.cs[p] == Critical
    && s.pState.task_no[p] == s.pState.done[p]
    && s.pState.task_no[p] > 0
    //
    && s'.timer == s.timer
    && s'.scheduled == s.scheduled[p := false]
    && s'.busyCriticalArea == s.busyCriticalArea
    //
    && s'.pState.ticket == s.pState.ticket
    && s'.pState.serving == s.pState.serving + 1    
    && s'.pState.cs == s.pState.cs[p := Idle]
    && s'.pState.hasTicket == s.pState.hasTicket[p := 0]
    //
    && s'.pState.task_no == s.pState.task_no[p := 0]
    && s'.pState.done == s.pState.done[p := 0]
}

//============================================================
// Safety Property - Mutual Exclusion
//============================================================

predicate TicketIsInUseBy(s: PState, i: nat, p:Process)
requires IsProcess(p)
requires s.cs.Keys == s.hasTicket.Keys == P
{
    s.cs[p] != Idle && s.hasTicket[p] == i
}

predicate TicketIsInUse(s: PState, i: nat)
requires s.cs.Keys == s.hasTicket.Keys == P
{
    exists p :: IsProcess(p) && s.cs[p] != Idle && s.hasTicket[p] == i
}

predicate ValidPState(s: PState)
{
    && s.cs.Keys == s.hasTicket.Keys == P
    && 1 <= s.serving <= s.ticket
    && (forall p :: (IsProcess(p) && s.cs[p] != Idle)
                        ==> s.serving <= s.hasTicket[p] < s.ticket)  
    && (forall p, q :: (IsProcess(p) && IsProcess(q) && p != q && s.cs[p] != Idle && s.cs[q] != Idle) 
                        ==>  s.hasTicket[p] != s.hasTicket[q])                          
    && (forall p :: (IsProcess(p) && s.cs[p] == Critical) 
                        ==> s.hasTicket[p] == s.serving)
    && (forall i :: s.serving <= i < s.ticket ==> TicketIsInUse(s,i))    
    && (forall p :: (IsProcess(p) && s.cs[p] == Idle)
                        ==>  s.hasTicket[p] == 0)                         
    && (forall p, q :: (IsProcess(p) && IsProcess(q) && p != q && (s.hasTicket[p] > 0 || s.hasTicket[q] > 0))
                        ==>  s.hasTicket[p] != s.hasTicket[q])   
    //                        
    && (forall p :: (IsProcess(p) && s.cs[p] != Idle)
                        ==> s.hasTicket[p] > 0)
                        && (forall p :: (IsProcess(p) && s.cs[p] == Idle)
                        ==>  s.hasTicket[p] == 0)                         
    && (forall p, q :: (IsProcess(p) && IsProcess(q) && p != q && (s.hasTicket[p] > 0 || s.hasTicket[q] > 0))
                        ==>  s.hasTicket[p] != s.hasTicket[q])   
    && (forall p :: (IsProcess(p) && s.cs[p] != Idle)
                        ==> s.hasTicket[p] > 0)
    //
    && s.task_no.Keys == s.done.Keys == P    
        && (forall p :: IsProcess(p) ==> s.task_no[p] >= 0) 
    && (forall p :: IsProcess(p) ==> 0 <= s.done[p] <= s.task_no[p]) 
    && (forall p :: (IsProcess(p) && s.cs[p] != Critical) ==> 0 == s.done[p] == s.task_no[p]) 
    && (forall p :: (IsProcess(p) && s.task_no[p] > 0)
                        ==>  s.cs[p] == Critical)                        
}

predicate Valid(s: SState)
{
    && ValidPState(s.pState)
    //
    && !IsProcess(pNull)
    && s.timer.Keys == s.scheduled.Keys == P
    && (forall p :: IsProcess(p) ==> 0 <= s.timer[p] <= Phi)    
    && ((exists p :: IsProcess(p) && s.pState.cs[p] == Critical) ==> s.busyCriticalArea)    
}

lemma MutualExclusion(s: SState, p:Process, q:Process)
requires Valid(s)
requires IsProcess(p) && IsProcess(q) 
requires s.pState.cs[p] == s.pState.cs[q] == Critical 
ensures p == q
{
}


//============================================================
// Valid is an inductive invariant 
//============================================================


lemma InitPreservesValid(s: SState)
ensures Init(s) ==> Valid(s)
{
}

lemma ExistingOwnerOfTicket(s: PState, i: nat) 
requires ValidPState(s)
requires s.serving <= i < s.ticket
ensures exists q :: IsProcess(q) && TicketIsInUseBy(s, i, q); 
{
    assert TicketIsInUse(s, i);
    var q :| IsProcess(q) && TicketIsInUseBy(s, i, q); 
}


lemma RequestPreservesValid(s: SState, p: Process, s': SState)
requires IsProcess(p)
ensures Valid(s) && Request(s, p, s') ==> Valid(s')             
{
    if Valid(s) && Request(s, p, s') 
    {
        assert s'.pState.ticket == s.pState.ticket + 1;

        assert TicketIsInUseBy(s'.pState, s.pState.ticket, p);
        assert TicketIsInUse(s'.pState, s.pState.ticket);

        forall i | s'.pState.serving <= i < s.pState.ticket         
            ensures TicketIsInUse(s'.pState, i)
        {            
            ExistingOwnerOfTicket(s.pState, i);
            var q :| IsProcess(q) && TicketIsInUseBy(s.pState, i, q); 
            assert TicketIsInUseBy(s.pState, i, q);
            assert TicketIsInUseBy(s'.pState, i, q);          
        }                 
    }
}

lemma WaitPreservesValid(s: SState, p: Process, s': SState)
requires IsProcess(p)
ensures Valid(s) && Wait(s, p, s') ==> Valid(s')             
{
    if Valid(s) && Wait(s, p, s') 
    {
        forall i | s'.pState.serving  <= i < s.pState.ticket         
            ensures TicketIsInUse(s'.pState, i)
        {            
            ExistingOwnerOfTicket(s.pState, i);
            var q :| IsProcess(q) && TicketIsInUseBy(s.pState, i, q); 
            assert TicketIsInUseBy(s.pState, i, q);
            assert TicketIsInUseBy(s'.pState, i, q);          
        }                 
    }
}

lemma EnterPreservesValid(s: SState, p: Process, s': SState)
requires IsProcess(p)
ensures Valid(s) && Enter(s, p, s') ==> Valid(s')             
{
    if Valid(s) && Enter(s, p, s') 
    {
        assert s'.pState.ticket == s.pState.ticket;

        forall i | s'.pState.serving  <= i < s.pState.ticket         
            ensures TicketIsInUse(s'.pState, i)
        {            
            ExistingOwnerOfTicket(s.pState, i);
            var q :| IsProcess(q) && TicketIsInUseBy(s.pState, i, q); 
            assert TicketIsInUseBy(s.pState, i, q);
            assert TicketIsInUseBy(s'.pState, i, q);          
        }                 
    }
}

lemma CreateTasksPreservesValid(s: SState, p: Process, s': SState)
requires IsProcess(p)
ensures Valid(s) && CreateTasks(s, p, s') ==> Valid(s')             
{
    if Valid(s) && CreateTasks(s, p, s') 
    {
        assert s'.pState.ticket == s.pState.ticket;

        forall i | s'.pState.serving  <= i < s.pState.ticket         
            ensures TicketIsInUse(s'.pState, i)
        {            
            ExistingOwnerOfTicket(s.pState, i);
            var q :| IsProcess(q) && TicketIsInUseBy(s.pState, i, q); 
            assert TicketIsInUseBy(s.pState, i, q);
            assert TicketIsInUseBy(s'.pState, i, q);          
        }                 
    }
}

lemma FinishOneTaskPreservesValid(s: SState, p: Process, s': SState)
requires IsProcess(p)
ensures Valid(s) && FinishOneTask(s, p, s') ==> Valid(s')             
{
    if Valid(s) && FinishOneTask(s, p, s') 
    {
        assert s'.pState.ticket == s.pState.ticket;

        forall i | s'.pState.serving  <= i < s.pState.ticket         
            ensures TicketIsInUse(s'.pState, i)
        {            
            ExistingOwnerOfTicket(s.pState, i);
            var q :| IsProcess(q) && TicketIsInUseBy(s.pState, i, q); 
            assert TicketIsInUseBy(s.pState, i, q);
            assert TicketIsInUseBy(s'.pState, i, q);          
        }                        
    }
}

lemma LeavePreservesValid(s: SState, p: Process, s': SState)
requires IsProcess(p)
ensures Valid(s) && Leave(s, p, s') ==> Valid(s')             
{
    if Valid(s) && Leave(s, p, s') 
    {
        assert s'.pState.ticket == s.pState.ticket;

        forall i | s'.pState.serving  <= i < s.pState.ticket         
            ensures TicketIsInUse(s'.pState, i)
        {            
            ExistingOwnerOfTicket(s.pState, i);
            var q :| IsProcess(q) && TicketIsInUseBy(s.pState, i, q); 
            assert TicketIsInUseBy(s.pState, i, q);
            assert TicketIsInUseBy(s'.pState, i, q);          
        }                 
    }
}

lemma SetTimerPreservesValid(s: SState, s': SState)
ensures Valid(s) && SetTimer(s, s') ==> Valid(s')             
{
    if Valid(s) && SetTimer(s, s')
    {
        assert s.pState == s'.pState;
    }    
}

lemma TransPreservesValid(s: SState, s': SState)
ensures Valid(s) && Next(s, s') ==> Valid(s')   
{
    if Valid(s) && Next(s, s') 
    {
        if SetTimer(s, s') {
            SetTimerPreservesValid(s, s');
        }
        else {
            var p :| IsProcess(p) && ( || Request(s, p, s') 
                                       || Wait(s, p, s')
                                       || Enter(s, p, s')
                                       || CreateTasks(s, p, s')
                                       || FinishOneTask(s, p, s')
                                       || Leave(s, p, s'));
        
            if Request(s, p, s') {
                RequestPreservesValid(s, p, s');            
            }

            if Wait(s, p, s') {
                WaitPreservesValid(s, p, s');            
            }

            if Enter(s, p, s') {
                EnterPreservesValid(s, p, s');            
            }

            if CreateTasks(s, p, s') {
                CreateTasksPreservesValid(s, p, s');            
            }

            if FinishOneTask(s, p, s') {
                FinishOneTaskPreservesValid(s, p, s');            
            }
    
            if Leave(s, p, s') {
                LeavePreservesValid(s, p, s');            
            }

            assert Valid(s');
        }        
    }
}


lemma ValidIsInductive(s: SState, s': SState)
ensures Init(s) ==> Valid(s)
ensures Valid(s) && Next(s,s') ==> Valid(s')             
{
    InitPreservesValid(s);
    TransPreservesValid(s, s');
}


//============================================================
// Trace
//============================================================


type Schedule = nat -> Process

predicate IsSchedule(sched: Schedule)
{
    // forall t :: IsProcess(sched(t)) 
    forall t :: IsProcess(sched(t)) || sched(t) == pNull
}

type Trace = nat -> SState

predicate IsTrace(tr: Trace, sched: Schedule)
requires IsSchedule(sched)
{
    && Init(tr(0))
    && (forall i: nat ::  
            && Valid(tr(i))
            && ( || ( && IsProcess(sched(i))
                      && NextP(tr(i), sched(i), tr(i+1)))
                 || ( && sched(i) == pNull
                      && SetTimer(tr(i), tr(i + 1)))))
}



predicate EventuallyTakeStep(sched: Schedule, p: Process, t: nat)
requires IsSchedule(sched)
requires IsProcess(p)
{
    exists t' | t' >= t :: sched(t')  == p
}


predicate IsFairSchedule(sched: Schedule)
{
    && IsSchedule(sched)
    && forall p,n | IsProcess(p) :: EventuallyTakeStep(sched, p, n)
}

//============================================================
// Safety property - validity in traces
//============================================================

lemma ValidInTrace(tr: Trace, sched: Schedule)
requires IsSchedule(sched) && IsTrace(tr, sched)
ensures forall t :: Valid(tr(t))
{ 
    forall t | t >= 0
        ensures Valid(tr(t))
    {
        InitPreservesValid(tr(0));

        var k := 0;
        while k < t 
            invariant 0 <= k <= t
            invariant Valid(tr(k))
        {
            var k0 := k;
            k := k0 + 1;
            TransPreservesValid(tr(k0), tr(t));
        }

        assert k == t && Valid(tr(t));
    }

}

//============================================================
// Safety properties used in proofs of liveness
//============================================================


lemma NonservedWaitingProcessCannotWorkInCriticalArea(tr: Trace, sched: Schedule, p: Process, n: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p) 
requires tr(n).pState.cs[p] == Waiting && tr(n).pState.hasTicket[p] > tr(n).pState.serving
requires sched(n) == p
ensures !Enter(tr(n), p, tr(n + 1))
ensures !CreateTasks(tr(n), p, tr(n + 1))
ensures !FinishOneTask(tr(n), p, tr(n + 1))
ensures !Leave(tr(n), p, tr(n + 1))
{
    if tr(n).pState.hasTicket[p] != tr(n).pState.serving
    {
        assert !Leave(tr(n), p, tr(n + 1));
        assert !CreateTasks(tr(n), p, tr(n + 1));
        assert !FinishOneTask(tr(n), p, tr(n + 1));
        assert !Enter(tr(n), p, tr(n + 1));
    } 
}

lemma IdleProcessCannotWorkInCriticalArea(tr: Trace, sched: Schedule, p: Process, n: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p) 
requires tr(n).pState.cs[p] == Idle
requires sched(n) == p
ensures !Enter(tr(n), p, tr(n + 1))
ensures !CreateTasks(tr(n), p, tr(n + 1))
ensures !FinishOneTask(tr(n), p, tr(n + 1))
ensures !Leave(tr(n), p, tr(n + 1))
{
    if tr(n).pState.cs[p] == Idle
    {
        assert !Leave(tr(n), p, tr(n + 1));
        assert !CreateTasks(tr(n), p, tr(n + 1));
        assert !FinishOneTask(tr(n), p, tr(n + 1));
        assert !Enter(tr(n), p, tr(n + 1));
    } 
}

lemma NonservedProcessCanOnlyRequestOrWait(tr: Trace, sched: Schedule, p: Process, n: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p) 
requires || (tr(n).pState.cs[p] == Idle)
         || (tr(n).pState.cs[p] == Waiting && tr(n).pState.hasTicket[p] > tr(n).pState.serving)
requires sched(n) == p
ensures Request(tr(n), sched(n), tr(n + 1)) || Wait(tr(n), sched(n), tr(n + 1))
ensures !Enter(tr(n), p, tr(n + 1))
ensures !CreateTasks(tr(n), p, tr(n + 1))
ensures !FinishOneTask(tr(n), p, tr(n + 1))
ensures !Leave(tr(n), p, tr(n + 1))
{
    if tr(n).pState.cs[p] == Idle {
        IdleProcessCannotWorkInCriticalArea(tr, sched, p, n);        
    }
    else {
        NonservedWaitingProcessCannotWorkInCriticalArea(tr, sched, p, n);
    }
}

lemma TicketOfNonservedWaitingProcessIsGreaterThanServingTicket(s: SState, nonserved: Process) 
requires Valid(s) && IsProcess(nonserved)
requires s.pState.cs[nonserved] == Waiting
requires s.pState.hasTicket[nonserved] != s.pState.serving
ensures s.pState.hasTicket[nonserved] > s.pState.serving
{ }

lemma NonservedProcessIsNotCritical(s: SState, nonserved: Process) 
requires Valid(s) && IsProcess(nonserved)
requires s.pState.hasTicket[nonserved] != s.pState.serving
ensures || (s.pState.cs[nonserved] == Idle)
        || (s.pState.cs[nonserved] == Waiting && s.pState.hasTicket[nonserved] > s.pState.serving)
{ }

predicate InvariantsInPeriodWithFrozenServedProcess(tr: Trace, sched: Schedule, served: Process, 
            n: nat, n': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) 
{
    //
    && tr(n').pState.task_no == tr(n).pState.task_no
    && tr(n').pState.done == tr(n).pState.done  
    //
    && tr(n').pState.serving == tr(n).pState.serving
    && tr(n').pState.cs[served] == tr(n).pState.cs[served]
    && tr(n').pState.hasTicket[served] == tr(n).pState.hasTicket[served]
    && tr(n').pState.serving == tr(n').pState.hasTicket[served]
    && ( forall q :: (IsProcess(q) && tr(n).pState.cs[q] == Waiting && q != served) 
                ==> ( && tr(n').pState.cs[q] == Waiting 
                      && tr(n').pState.hasTicket[q] == tr(n).pState.hasTicket[q] ) )
}


lemma InvariantsWhenWaitingProcessWaits(tr: Trace, sched: Schedule, served: Process, 
            nonserved: Process, t: nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) && IsProcess(nonserved)
requires tr(t).pState.hasTicket[nonserved] > tr(t).pState.serving 
requires tr(t).pState.cs[nonserved] == Waiting
requires tr(t).pState.hasTicket[served] == tr(t).pState.serving 
requires sched(t) == nonserved 
requires Wait(tr(t), nonserved, tr(t + 1))
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, t, t + 1)
{ }

lemma InvariantsWhenIdleProcessRequestsTicket(tr: Trace, sched: Schedule, served: Process, 
            nonserved: Process, t: nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) && IsProcess(nonserved)
requires tr(t).pState.cs[nonserved] == Idle
requires tr(t).pState.hasTicket[served] == tr(t).pState.serving 
requires sched(t) == nonserved 
requires Request(tr(t), nonserved, tr(t + 1))
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, t, t + 1)
{ 
    var t1 := t + 1;
    assert tr(t1).pState.serving == tr(t).pState.serving;
    assert tr(t1).pState.cs[served] == tr(t).pState.cs[served];
    assert tr(t1).pState.hasTicket[served] == tr(t).pState.hasTicket[served];
    assert forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting)
                ==> ( && tr(t1).pState.cs[q] == Waiting 
                      && tr(t1).pState.hasTicket[q] == tr(t).pState.hasTicket[q] );
    assert tr(t1).pState.task_no == tr(t).pState.task_no;
    assert tr(t1).pState.done == tr(t).pState.done;
}

lemma InvariantsWhenNonservedProcessRequestsTicketOrWaits(tr: Trace, sched: Schedule, served: Process,
            nonserved: Process, t: nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) && IsProcess(nonserved)
requires sched(t) == nonserved
requires served != nonserved
requires tr(t).pState.serving == tr(t).pState.hasTicket[served]
requires Request(tr(t), nonserved, tr(t + 1)) || Wait(tr(t), nonserved, tr(t + 1))
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, t, t + 1)
{
    assert tr(t).pState.hasTicket[nonserved] != tr(t).pState.hasTicket[served];
    NonservedProcessIsNotCritical(tr(t), nonserved);
    if (tr(t).pState.cs[nonserved] == Idle) {
        InvariantsWhenIdleProcessRequestsTicket(tr, sched, served, nonserved, t);
    }
    if (tr(t).pState.cs[nonserved] == Waiting && tr(t).pState.hasTicket[nonserved] > tr(t).pState.serving) {
        InvariantsWhenWaitingProcessWaits(tr, sched, served, nonserved, t);
    }
}


lemma InvariantsWhenNonservedProcessMoves(tr: Trace, sched: Schedule, served: Process,
            nonserved: Process, t: nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) && IsProcess(nonserved)
requires tr(t).pState.hasTicket[served] == tr(t).pState.serving 
requires sched(t) == nonserved 
requires served != nonserved
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, t, t + 1)
{
    NonservedProcessCanOnlyRequestOrWait(tr, sched, nonserved, t);
    InvariantsWhenNonservedProcessRequestsTicketOrWaits(tr, sched, served, nonserved, t);
}

lemma ServedProcessIsNotIdle(s: SState, p: Process)
requires Valid(s) && IsProcess(p)
requires s.pState.hasTicket[p] == s.pState.serving
ensures s.pState.cs[p] != Idle
{
    assert s.pState.hasTicket[p] > 0;
}

lemma InvariantsAfterSettingTimer(tr: Trace, sched: Schedule, served: Process, t: nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served)
requires sched(t) == pNull
requires tr(t).pState.serving == tr(t).pState.hasTicket[served]
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, t, t + 1)
{
    var t1 := t + 1;
    assert sched(t) == pNull ==> SetTimer(tr(t), tr(t1));    
    assert tr(t).pState == tr(t1).pState;
}

lemma InvariantsInTransitionWhenServedProcessIsFrozen(tr: Trace, sched: Schedule, 
            served: Process, t: nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) 
requires tr(t).pState.hasTicket[served] == tr(t).pState.serving 
requires sched(t) != served
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, t, t + 1)
{
    var nonserved: Process :| sched(t) == nonserved;   
    if IsProcess(nonserved) {
        assert IsProcess(nonserved) && sched(t) == nonserved && nonserved != served;
        InvariantsWhenNonservedProcessMoves(tr, sched, served, nonserved, t);
    }
    else {
        InvariantsAfterSettingTimer(tr, sched, served, t);
    }
}

lemma InvariantsInNextStateWhenServedProcessIsFrozen(tr: Trace, sched: Schedule, 
        served: Process, t: nat, t': nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) 
requires tr(t).pState.hasTicket[served] == tr(t).pState.serving 
requires sched(t) != served
requires t' == t + 1
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, t, t')
{
    InvariantsInTransitionWhenServedProcessIsFrozen(tr, sched, served, t);
}        

lemma MergeInvariantsInTwoConsecutivePeriodsWithSameFrozenServedProcess(tr: Trace, sched: Schedule, 
        served: Process, k0: nat, k1: nat, k2: nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) 
requires InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, k0, k1)        
requires InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, k1, k2)
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, k0, k2)
{ }   

lemma ExtendPeriodWithFrozenServedProcess(tr: Trace, sched: Schedule, 
            served: Process, n: nat, k: nat, k': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served)
requires InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, n, k)                        
requires sched(k) != served
requires k' == k + 1
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, n, k')           
{
    InvariantsInNextStateWhenServedProcessIsFrozen(tr, sched, served, k, k');
    MergeInvariantsInTwoConsecutivePeriodsWithSameFrozenServedProcess(tr, sched, served, n, k, k');
    assert InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, n, k');
}    

lemma FindNextStepOfServedProcess(tr: Trace, sched: Schedule, served: Process, 
        n: nat, u: nat) returns (k: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served)
requires tr(n).pState.cs[served] != Idle 
requires tr(n).pState.hasTicket[served] == tr(n).pState.serving
requires n <= u
requires sched(u) == served
requires InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, n, n)
ensures n <= k <= u
ensures sched(k) == served
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, n, k)
{
    k := n;
    // assert InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, n, k);

    while sched(k) != served // k == u ==> sched(k) == sched(u) 
        invariant n <= k <= u
        invariant sched(u) == served
        invariant sched(k) != served ==> k < u
        invariant InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, n, k);
        decreases u - k
    {    
        var t := k;
        k := k + 1;
        ExtendPeriodWithFrozenServedProcess(tr, sched, served, n, t, k);
        assert k == u ==> sched(k) == sched(u);
    }
}

lemma GetNextStepOfServedProcess(tr: Trace, sched: Schedule, served: Process, 
            n: nat) returns (n': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served)
requires tr(n).pState.cs[served] != Idle 
requires tr(n).pState.hasTicket[served] == tr(n).pState.serving
ensures n <= n' 
ensures sched(n') == served
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, n, n')
{
    assert EventuallyTakeStep(sched, served, n);
    var u :| n <= u && sched(u) == served;
    assert sched(u) == served;
    
    n' := FindNextStepOfServedProcess(tr, sched, served, n, u);    
}

/// Liveness

lemma ServedWaitingProcessCanOnlyEnterCriticalArea(tr: Trace, sched: Schedule, 
            p: Process, t: nat, t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires sched(t) == p 
requires tr(t).pState.cs[p] == Waiting 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires t' == t + 1
ensures Enter(tr(t), p, tr(t'))
{
    assert !Request(tr(t), p, tr(t + 1));
    assert !Wait(tr(t), p, tr(t + 1));
    assert !CreateTasks(tr(t), p, tr(t + 1));
    assert !FinishOneTask(tr(t), p, tr(t + 1));
    assert !Leave(tr(t), p, tr(t + 1));
}

lemma ServedProcessHasEnteredCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat, t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires sched(t) == p 
requires tr(t).pState.cs[p] == Waiting 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires t' == t + 1
ensures tr(t').pState.cs[p] == Critical
ensures tr(t').pState.hasTicket[p] == tr(t').pState.serving 
ensures tr(t').pState.serving == tr(t).pState.serving 
ensures tr(t').pState.done[p] == tr(t).pState.done[p]
ensures tr(t').pState.task_no[p] == tr(t).pState.task_no[p]
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )                  
{
    ServedWaitingProcessCanOnlyEnterCriticalArea(tr, sched, p, t, t');
    assert Enter(tr(t), p, tr(t'));    
}

lemma ServedWaitingProcessEventuallyEntersCriticalArea(tr: Trace, sched: Schedule, 
            p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] == Waiting
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving
ensures t <= t'
ensures tr(t').pState.cs[p] == Critical 
ensures tr(t').pState.hasTicket[p] == tr(t').pState.serving 
ensures tr(t').pState.serving == tr(t).pState.serving 
ensures tr(t').pState.done[p] == tr(t).pState.done[p]
ensures tr(t').pState.task_no[p] == tr(t).pState.task_no[p]
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )                  
{    
    var k := GetNextStepOfServedProcess(tr, sched, p, t);  
    t' := k + 1;  
    assert InvariantsInPeriodWithFrozenServedProcess(tr, sched, p, t, k);
    ServedProcessHasEnteredCriticalArea(tr, sched, p, k, t');       
}

lemma ServedProcessEventuallyEntersCriticalArea(tr: Trace, sched: Schedule, 
            p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] != Idle
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving
ensures t <= t'
ensures tr(t').pState.cs[p] == Critical 
ensures tr(t').pState.hasTicket[p] == tr(t').pState.serving 
ensures tr(t').pState.serving == tr(t).pState.serving 
////
ensures tr(t').pState.done[p] == tr(t).pState.done[p]
ensures tr(t').pState.task_no[p] == tr(t).pState.task_no[p]
////
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] ) 
{    
    if tr(t).pState.cs[p] == Critical { 
        t' := t;        
    }
    else {
        assert tr(t).pState.cs[p] == Waiting;
        var k := GetNextStepOfServedProcess(tr, sched, p, t);
        t' := k + 1;
        ServedProcessHasEnteredCriticalArea(tr, sched, p, k, t');
    }
}

lemma AvailableStepForFreshCriticalProcess(tr: Trace, sched: Schedule, p: Process, t: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires sched(t) == p
requires tr(t).pState.cs[p] == Critical 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires tr(t).pState.task_no[p] == tr(t).pState.done[p] == 0
ensures Next(tr(t), tr(t + 1)) <==> CreateTasks(tr(t), p, tr(t + 1))
{
    assert tr(t).pState.task_no[p] == tr(t).pState.done[p] == 0 
                    ==> (!FinishOneTask(tr(t), p, tr(t + 1)) && !Leave(tr(t), p, tr(t + 1))) ;
    assert tr(t).pState.cs[p] == Critical 
                    ==> ( && !Request(tr(t), p, tr(t + 1))
                          && !Wait(tr(t), p, tr(t + 1)) 
                          && !Enter(tr(t), p, tr(t + 1)) );
    assert (sched(t) == p && IsProcess(p)) ==> !SetTimer(tr(t), tr(t + 1));
    assert sched(t) == p ==> !SetTimer(tr(t), tr(t + 1));
    assert Next(tr(t), tr(t + 1));
    assert Next(tr(t), tr(t + 1)) <==> CreateTasks(tr(t), p, tr(t + 1));
}

lemma ServedProcessHasCreatedTasks(tr: Trace, sched: Schedule, p: Process, t: nat, t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires sched(t) == p 
requires tr(t).pState.cs[p] == Critical 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires tr(t).pState.task_no[p] == 0
requires tr(t).pState.done[p] == 0
requires t' == t + 1
ensures tr(t').pState.task_no[p] > 0 
ensures tr(t').pState.done[p] == 0
ensures tr(t').pState.cs[p] == Critical
ensures tr(t').pState.hasTicket[p] == tr(t').pState.serving 
ensures tr(t').pState.serving == tr(t).pState.serving 
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )                  
{
    AvailableStepForFreshCriticalProcess(tr, sched, p, t);    
    assert CreateTasks(tr(t), p, tr(t'));    
}

lemma ServedProcessEventuallyCreatesTasksAfterEnteringTheCriticalArea(tr: Trace, sched: Schedule, 
        served: Process, t0: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served)
requires tr(t0).pState.cs[served] == Critical 
requires tr(t0).pState.hasTicket[served] == tr(t0).pState.serving 
requires tr(t0).pState.task_no[served] == 0
requires tr(t0).pState.done[served] == 0
ensures t0 <= t' 
ensures tr(t').pState.serving == tr(t0).pState.serving
ensures tr(t').pState.cs[served] == tr(t0).pState.cs[served]
ensures tr(t').pState.hasTicket[served] == tr(t0).pState.hasTicket[served]
ensures tr(t').pState.task_no[served] > 0 && tr(t').pState.done[served] == 0
ensures forall q :: (IsProcess(q) && tr(t0).pState.cs[q] == Waiting && q != served) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t0).pState.hasTicket[q] )
{
    var t := GetNextStepOfServedProcess(tr, sched, served, t0);
    AvailableStepForFreshCriticalProcess(tr, sched, served, t);        
    t' := t + 1;                         
    ServedProcessHasCreatedTasks(tr, sched, served, t, t');    
}

lemma ServedProcessEventuallyCreatesNewTasks(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] != Idle && tr(t).pState.hasTicket[p] == tr(t).pState.serving
ensures t <= t'
ensures tr(t').pState.cs[p] == Critical && tr(t').pState.hasTicket[p] == tr(t').pState.serving
ensures tr(t').pState.task_no[p] > 0 
ensures tr(t').pState.serving == tr(t).pState.serving 
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )
{    
    if tr(t).pState.task_no[p] > 0 { 
        t' := t;        
    }
    else {       
        assert tr(t).pState.task_no[p] == tr(t).pState.done[p] == 0;  
        var k0 := ServedProcessEventuallyEntersCriticalArea(tr, sched, p, t); 
        t' := ServedProcessEventuallyCreatesTasksAfterEnteringTheCriticalArea(tr, sched, p, k0);
    }
}

lemma BusyServedProcess(tr: Trace, sched: Schedule, p: Process, 
            t: nat, t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] == Critical 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires tr(t).pState.task_no[p] > tr(t).pState.done[p] 
requires tr(t).pState.task_no[p] > 0
requires sched(t) == p
requires t' == t + 1
ensures !SetTimer(tr(t), tr(t'))
ensures !Request(tr(t), p, tr(t'))
ensures !Enter(tr(t), p, tr(t'))
ensures !CreateTasks(tr(t), p, tr(t'))
ensures !Leave(tr(t), p, tr(t'))
{   
    assert sched(t) == p ==> !SetTimer(tr(t), tr(t'));
    assert tr(t).pState.cs[p] == Critical ==> !Request(tr(t), p, tr(t'));
    assert tr(t).pState.cs[p] == Critical ==> !Enter(tr(t), p, tr(t'));
    assert tr(t).pState.task_no[p] > 0 ==> !CreateTasks(tr(t), p, tr(t'));                
    assert tr(t).pState.task_no[p] > tr(t).pState.done[p] ==> !Leave(tr(t), p, tr(t'));
}

lemma ServedProcessNeedsToFinishOneTask(tr: Trace, sched: Schedule, p: Process, 
            t: nat, t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] == Critical 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires tr(t).pState.task_no[p] > tr(t).pState.done[p] 
requires tr(t).pState.task_no[p] > 0
requires sched(t) == p
requires t' == t + 1
ensures FinishOneTask(tr(t), p, tr(t'))
{   
    BusyServedProcess(tr, sched, p, t, t');
    assert FinishOneTask(tr(t), p, tr(t'));
}

lemma ServedProcessHasFinishedOneTask(tr: Trace, sched: Schedule, p: Process, t: nat, t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] == Critical 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires tr(t).pState.task_no[p] > tr(t).pState.done[p] 
requires tr(t).pState.task_no[p] > 0
requires t' == t + 1
requires sched(t) == p 
ensures tr(t').pState.task_no[p] == tr(t).pState.task_no[p]
ensures tr(t').pState.done[p] == tr(t).pState.done[p] + 1
ensures tr(t').pState.task_no[p] >= tr(t').pState.done[p]
ensures tr(t').pState.cs[p] == Critical
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )                  
{
    ServedProcessNeedsToFinishOneTask(tr, sched, p, t, t');    
    assert FinishOneTask(tr(t), p, tr(t'));    
    assert forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] );
}

lemma BusyServedProcessEventuallyFinishesOneMoreTask(tr: Trace, sched: Schedule, 
            p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] == Critical 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires tr(t).pState.task_no[p] > tr(t).pState.done[p] 
requires tr(t).pState.task_no[p] > 0
ensures t' > t
ensures tr(t').pState.cs[p] == Critical
ensures tr(t').pState.hasTicket[p] == tr(t').pState.serving 
ensures tr(t').pState.task_no[p] == tr(t).pState.task_no[p]
ensures tr(t').pState.done[p] == tr(t).pState.done[p] + 1
ensures tr(t').pState.task_no[p] >= tr(t').pState.done[p]
ensures tr(t').pState.task_no[p] - tr(t').pState.done[p] < tr(t).pState.task_no[p] - tr(t).pState.done[p]
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )   

ensures tr(t').pState.serving == tr(t).pState.serving;
ensures tr(t').pState.hasTicket[p] == tr(t).pState.hasTicket[p];
ensures tr(t').pState.task_no[p] > 0 
{
    var k := GetNextStepOfServedProcess(tr, sched, p, t);
    assert InvariantsInPeriodWithFrozenServedProcess(tr, sched, p, t, k);
    t' := k + 1;
    ServedProcessNeedsToFinishOneTask(tr, sched, p, k, t');    
    ServedProcessHasFinishedOneTask(tr, sched, p, k, t');    
}

lemma EventuallyFinishAllTasksAfterCreatingTasks(tr: Trace, sched: Schedule, 
            p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] == Critical && tr(t).pState.hasTicket[p] == tr(t).pState.serving
requires tr(t).pState.task_no[p] > 0 && tr(t).pState.done[p] >= 0
requires tr(t).pState.task_no[p] >= tr(t).pState.done[p]
ensures t <= t' 
ensures tr(t').pState.serving == tr(t).pState.serving
ensures tr(t').pState.cs[p] == tr(t).pState.cs[p] == Critical
ensures tr(t').pState.hasTicket[p] == tr(t).pState.hasTicket[p]
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )
ensures tr(t').pState.task_no[p] > 0
ensures tr(t').pState.task_no[p] == tr(t').pState.done[p]
{
    if tr(t).pState.done[p] == tr(t).pState.task_no[p]
    {
        t' := t;
        return;
    }
    
    t' := t;
    while true
        invariant t <= t'
        invariant tr(t').pState.serving == tr(t).pState.serving
        invariant tr(t').pState.cs[p] == tr(t).pState.cs[p] == Critical
        invariant tr(t').pState.hasTicket[p] == tr(t).pState.hasTicket[p]
        invariant forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p)
                    ==> ( && tr(t').pState.cs[q] == Waiting 
                          && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )
        invariant tr(t').pState.task_no[p] > 0 
        invariant tr(t').pState.task_no[p] == tr(t).pState.task_no[p]
        invariant tr(t').pState.done[p] <= tr(t').pState.task_no[p]
        decreases tr(t').pState.task_no[p] - tr(t').pState.done[p]
    {       
        if tr(t').pState.done[p] == tr(t').pState.task_no[p] 
        {
            return;
        }
        else {
            var k := t';
            t' := BusyServedProcessEventuallyFinishesOneMoreTask(tr, sched, p, k);
        }
    }
    
}


lemma ServedProcessEventuallyFinishAllTasks(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] != Idle && tr(t).pState.hasTicket[p] == tr(t).pState.serving
ensures t <= t' && tr(t').pState.cs[p] == Critical 
ensures tr(t').pState.hasTicket[p] == tr(t').pState.serving
ensures tr(t').pState.task_no[p] > 0 && tr(t').pState.task_no[p] == tr(t').pState.done[p]
ensures tr(t).pState.serving == tr(t').pState.serving 
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==>( && tr(t').pState.cs[q] == Waiting 
                 && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )
{        
    var k0 := ServedProcessEventuallyCreatesNewTasks(tr, sched, p, t);             
    t':= EventuallyFinishAllTasksAfterCreatingTasks(tr, sched, p, k0);
}

lemma ServedProcessCanOnlyLeaveAfterFinishingAllTasks(tr: Trace, sched: Schedule, p: Process, 
            t: nat, t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] == Critical 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires tr(t).pState.task_no[p] == tr(t).pState.done[p] 
requires tr(t).pState.task_no[p] > 0
requires sched(t) == p
requires t' == t + 1
ensures !SetTimer(tr(t), tr(t'))
ensures !Request(tr(t), p, tr(t'))
ensures !Enter(tr(t), p, tr(t'))
ensures !CreateTasks(tr(t), p, tr(t'))
ensures !FinishOneTask(tr(t), p, tr(t'))
ensures Leave(tr(t), p, tr(t'))
{   
    
    assert sched(t) == p ==> !SetTimer(tr(t), tr(t'));
    assert tr(t).pState.cs[p] == Critical 
                ==> (!Request(tr(t), p, tr(t')) && !Enter(tr(t), p, tr(t')));
    assert tr(t).pState.task_no[p] > 0 ==> !CreateTasks(tr(t), p, tr(t'));                
    assert tr(t).pState.task_no[p] == tr(t).pState.done[p] ==> !FinishOneTask(tr(t), p, tr(t'));
    assert Next(tr(t), tr(t'));
    assert Leave(tr(t), p, tr(t'));
}

lemma ServedProcessHasLeaved(tr: Trace, sched: Schedule, p: Process, t: nat, t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] == Critical 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires tr(t).pState.done[p] == tr(t).pState.task_no[p]
requires tr(t).pState.task_no[p] > 0
requires t' == t + 1
requires sched(t) == p 
ensures tr(t').pState.task_no[p] == 0 
ensures tr(t').pState.done[p] == 0
ensures tr(t').pState.cs[p] == Idle
ensures tr(t').pState.hasTicket[p] == 0
ensures tr(t').pState.serving == tr(t).pState.serving + 1
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )                  
{
    ServedProcessCanOnlyLeaveAfterFinishingAllTasks(tr, sched, p, t, t');    
    assert Leave(tr(t), p, tr(t'));    
    assert forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] );
}


lemma EventuallyLeavesTheCriticalAreaAfterFinishingAllTasks(tr: Trace, sched: Schedule, 
            p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] == Critical && tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires tr(t).pState.task_no[p] == tr(t).pState.done[p] && tr(t).pState.task_no[p] > 0
ensures t <= t' 
ensures tr(t').pState.serving == tr(t).pState.serving + 1
ensures tr(t').pState.task_no[p] == 0 
ensures tr(t').pState.done[p] == 0
ensures tr(t').pState.hasTicket[p] == 0 
ensures tr(t').pState.cs[p] == Idle
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p)
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )
{
    var k := GetNextStepOfServedProcess(tr, sched, p, t);    
    assert InvariantsInPeriodWithFrozenServedProcess(tr, sched, p, t, k);
    assert sched(k) == p;
    t' := k + 1;    
    ServedProcessHasLeaved(tr, sched, p, k, t');
}

lemma ServedProcessEventuallyLeavesCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] != Idle && tr(t).pState.hasTicket[p] == tr(t).pState.serving
ensures t <= t'
ensures tr(t').pState.task_no[p] == 0 
ensures tr(t').pState.done[p] == 0
ensures tr(t').pState.hasTicket[p] == 0 
ensures tr(t').pState.cs[p] == Idle
ensures tr(t).pState.serving < tr(t').pState.serving 
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )
{        
    var k0 := ServedProcessEventuallyFinishAllTasks(tr, sched, p, t);             
    t' := EventuallyLeavesTheCriticalAreaAfterFinishingAllTasks(tr, sched, p, k0); 
}

/*
lemma ServedProcessEventuallyLeavesCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] != Idle && tr(t).pState.hasTicket[p] == tr(t).pState.serving
ensures t <= t' && tr(t').pState.cs[p] != Critical 
ensures tr(t).pState.serving < tr(t').pState.serving 
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )
{        
    var k0 := ServedProcessEventuallyFinishAllTasks(tr, sched, p, t);             
    t' := EventuallyLeavesTheCriticalAreaAfterFinishingAllTasks(tr, sched, p, k0); 
}
*/
function CurrentlyServedProcess(s: SState): Process
requires Valid(s)
requires exists p | IsProcess(p) :: s.pState.cs[p] == Waiting
{
    assert TicketIsInUse(s.pState, s.pState.serving);
    var q :| IsProcess(q) && s.pState.cs[q] != Idle && s.pState.hasTicket[q] == s.pState.serving;
    q
}

lemma Liveness(tr: Trace, sched: Schedule, p: Process, n: nat) returns (n': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(n).pState.cs[p] == Waiting
ensures n <= n' && tr(n').pState.cs[p] == Critical
{
    n' := n;
    while true
        invariant n <= n' && tr(n').pState.cs[p] == Waiting
        decreases tr(n').pState.hasTicket[p] - tr(n').pState.serving
    {
        var k := n';
        var q := CurrentlyServedProcess(tr(n'));        
        if p == q {
            n' := ServedProcessEventuallyEntersCriticalArea(tr, sched, q, k);
            return;
        }
        else {
            n' := ServedProcessEventuallyLeavesCriticalArea(tr, sched, q, k);
        }        
    }
}

