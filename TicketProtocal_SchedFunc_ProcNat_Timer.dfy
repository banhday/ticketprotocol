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
                          hasTicket: map<Process, nat>
)

datatype SState = SState(
    pState: PState,
    timer: map<Process, nat>,
    available: map<Process, bool>,
    busyCriticalArea: bool,
    clock: nat
)

predicate IsProcess(p: Process)
{
    p in P
}

predicate InitPState(s: PState) 
// ensures InitPState(s) ==> s.cs.Keys == s.hasTicket.Keys == P
// ensures InitPState(s) ==> (forall p | IsProcess(p) :: s.cs[p] == Idle)
{
    && s.cs.Keys == s.hasTicket.Keys == P
    && s.ticket == s.serving == 1
    && (forall p :: IsProcess(p) ==> s.cs[p] == Idle)
    && (forall p :: IsProcess(p) ==> s.hasTicket[p] == 0)
}

predicate Init(s: SState)   
// ensures Init(s) ==> s.pState.cs.Keys == s.pState.hasTicket.Keys == P
// ensures Init(s) ==> (forall p | IsProcess(p) :: s.pState.cs[p] == Idle)
{
    && pNull !in P
    && Phi > 0
    && s.timer.Keys == s.available.Keys == P
    && (forall p :: IsProcess(p) ==> s.timer[p] == 1)
    && (forall p :: IsProcess(p) ==> !s.available[p])
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
    && (forall p :: IsProcess(p) ==> !s.available[p])
    //
    && s'.pState == s.pState
    //
    && s'.timer.Keys == s'.available.Keys == P
    && (forall p :: IsProcess(p) ==> (s'.timer[p] == 0 || s'.timer[p] == s.timer[p] + 1))
    && (forall p :: IsProcess(p) ==> (s'.timer[p] <= Phi))
    && (forall p :: IsProcess(p) ==> (s'.available[p] <==> (s'.timer[p] == 0)))
    && (s'.busyCriticalArea <==> (exists p: Process :: IsProcess(p) && s'.pState.cs[p] == Critical))
    
}

predicate NextP(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    || RequestP(s, p, s')
    || WaitP(s, p, s')
    || EnterP(s, p, s')
    || LeaveP(s, p, s')
}

predicate RequestP(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    && s.timer[p] == 0
    && s.available[p]
    && s.pState.cs[p] == Idle    
    //
    && s'.timer == s.timer
    && s'.available == s.available[p := false]
    && s'.busyCriticalArea == s.busyCriticalArea
    //    
    && s'.pState.hasTicket == s.pState.hasTicket[p := s.pState.ticket]
    && s'.pState.ticket == s.pState.ticket + 1
    && s'.pState.serving == s.pState.serving
    && s'.pState.cs == s.pState.cs[p := Waiting]
}

predicate WaitP(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    && s.timer[p] == 0
    && s.available[p]
    && s.pState.hasTicket[p] > s.pState.serving
    && s.pState.cs[p] == Waiting
    //
    && s'.timer == s.timer
    && s'.available == s.available[p := false]
    && s'.busyCriticalArea == s.busyCriticalArea
    //
    && s.pState.cs[p] == Waiting
    && s'.pState.ticket == s.pState.ticket
    && s'.pState.serving == s.pState.serving
    && s'.pState.hasTicket == s.pState.hasTicket
    && s'.pState.cs == s.pState.cs
}

predicate EnterP(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    && s.timer[p] == 0
    && s.available[p]
    && s.pState.cs[p] == Waiting
    && s.pState.hasTicket[p] == s.pState.serving
    //
    && s'.timer == s.timer
    && s'.available == s.available[p := false]
    && s'.busyCriticalArea 
    //    
    && s'.pState.ticket == s.pState.ticket
    && s'.pState.serving == s.pState.serving
    && s'.pState.hasTicket == s.pState.hasTicket
    && s'.pState.cs == s.pState.cs[p := Critical]
}

predicate LeaveP(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    && s.timer[p] == 0
    && s.available[p]
    && s'.timer == s.timer
    && s'.available == s.available[p := false]
    && s'.busyCriticalArea == s.busyCriticalArea
    //
    && s.pState.cs[p] == Critical
    && s.pState.hasTicket[p] == s.pState.serving 
    && s'.pState.ticket == s.pState.ticket
    && s'.pState.serving == s.pState.serving + 1    
    && s'.pState.cs == s.pState.cs[p := Idle]
    && s'.pState.hasTicket== s.pState.hasTicket[p := 0]
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
    && (forall p :: (IsProcess(p) && s.cs[p] != Idle)
                        ==> s.hasTicket[p] > 0)
}

predicate Valid(s: SState)
{
    && ValidPState(s.pState)
    //
    && pNull !in P
    && s.timer.Keys == s.available.Keys == P
    && (forall p :: p in P ==> 0 <= s.timer[p] <= Phi)    
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


lemma RequestPPreservesValid(s: SState, p: Process, s': SState)
requires IsProcess(p)
ensures Valid(s) && RequestP(s, p, s') ==> Valid(s')             
{
    if Valid(s) && RequestP(s, p, s') 
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

lemma WaitPPreservesValid(s: SState, p: Process, s': SState)
requires IsProcess(p)
ensures Valid(s) && WaitP(s, p, s') ==> Valid(s')             
{
    if Valid(s) && WaitP(s, p, s') 
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

lemma EnterPPreservesValid(s: SState, p: Process, s': SState)
requires IsProcess(p)
ensures Valid(s) && EnterP(s, p, s') ==> Valid(s')             
{
    if Valid(s) && EnterP(s, p, s') 
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


lemma LeavePPreservesValid(s: SState, p: Process, s': SState)
requires IsProcess(p)
ensures Valid(s) && LeaveP(s, p, s') ==> Valid(s')             
{
    if Valid(s) && LeaveP(s, p, s') 
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
{ }

lemma TransPreservesValid(s: SState, s': SState)
ensures Valid(s) && Next(s, s') ==> Valid(s')   
{
    if Valid(s) && Next(s, s') 
    {
        if SetTimer(s, s') {
            SetTimerPreservesValid(s, s');
        }
        else {
            var p :| IsProcess(p) && ( || RequestP(s, p, s') 
                                       || WaitP(s, p, s')
                                       || EnterP(s, p, s')
                                       || LeaveP(s, p, s'));
        
            if RequestP(s, p, s') {
                RequestPPreservesValid(s, p, s');            
            }

            if WaitP(s, p, s') {
                WaitPPreservesValid(s, p, s');            
            }

            if EnterP(s, p, s') {
                EnterPPreservesValid(s, p, s');            
            }
    
            if LeaveP(s, p, s') {
                LeavePPreservesValid(s, p, s');            
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
    // forall t :: sched(t) in P 
    forall t :: sched(t) in P || sched(t) == pNull
}

// clock
// lastSched
// timer[p] == clock - lastSched[p]

type Trace = nat -> SState

predicate IsTrace(tr: Trace, sched: Schedule)
requires IsSchedule(sched)
{
    && Init(tr(0))
    && (forall i: nat ::  
            && Valid(tr(i))
            && ( || ( && sched(i) in P 
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
{ }

//============================================================
// Liveness
//============================================================


lemma NonservedWaitingProcessCannotWorkInTheCriticalArea(tr: Trace, sched: Schedule, p: Process, n: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p) 
requires tr(n).pState.cs[p] == Waiting && tr(n).pState.hasTicket[p] > tr(n).pState.serving
requires sched(n) == p
ensures !LeaveP(tr(n), p, tr(n + 1))
ensures !EnterP(tr(n), p, tr(n + 1))
{
    assert tr(n).pState.hasTicket[p] != tr(n).pState.serving ==> !LeaveP(tr(n), p, tr(n + 1));
    assert tr(n).pState.hasTicket[p] != tr(n).pState.serving ==> !EnterP(tr(n), p, tr(n + 1));
}

lemma IdleProcessCannotWorkInTheCriticalArea(tr: Trace, sched: Schedule, p: Process, n: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p) 
requires tr(n).pState.cs[p] == Idle
requires sched(n) == p
ensures !LeaveP(tr(n), p, tr(n + 1))
ensures !EnterP(tr(n), p, tr(n + 1))
{
    assert tr(n).pState.cs[p] == Idle ==> tr(n).pState.cs[p] != Waiting;
    assert tr(n).pState.cs[p] != Critical ==> !LeaveP(tr(n), p, tr(n + 1));
    assert tr(n).pState.cs[p] != Critical ==> !EnterP(tr(n), p, tr(n + 1));
}

lemma IdleProcessDoesnotWait(tr: Trace, sched: Schedule, p: Process, n: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p) 
requires tr(n).pState.cs[p] == Idle
requires sched(n) == p
ensures !WaitP(tr(n), p, tr(n + 1))
{
    assert tr(n).pState.cs[p] == Idle ==> tr(n).pState.cs[p] != Waiting;
    assert tr(n).pState.cs[p] != Waiting ==> !WaitP(tr(n), p, tr(n + 1));
}

lemma OnlyRequestPAndWaitPAreAvailableForNonservedProcess(tr: Trace, sched: Schedule, p: Process, n: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p) 
requires || (tr(n).pState.cs[p] == Idle)
         || (tr(n).pState.cs[p] == Waiting && tr(n).pState.hasTicket[p] > tr(n).pState.serving)
requires sched(n) == p
ensures RequestP(tr(n), sched(n), tr(n + 1)) || WaitP(tr(n), sched(n), tr(n + 1))
ensures !LeaveP(tr(n), p, tr(n + 1))
ensures !EnterP(tr(n), p, tr(n + 1))
{
    if tr(n).pState.cs[p] == Idle {
        IdleProcessCannotWorkInTheCriticalArea(tr, sched, p, n);
        IdleProcessDoesnotWait(tr, sched, p, n);
    }
    else {
        assert tr(n).pState.hasTicket[p] > tr(n).pState.serving;
        NonservedWaitingProcessCannotWorkInTheCriticalArea(tr, sched, p, n);
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
    && tr(n').pState.serving == tr(n).pState.serving
    && tr(n').pState.cs[served] == tr(n).pState.cs[served]
    && tr(n').pState.hasTicket[served] == tr(n).pState.hasTicket[served]
    && tr(n').pState.serving == tr(n').pState.hasTicket[served]
    && forall q :: (IsProcess(q) && tr(n).pState.cs[q] == Waiting) 
                ==> ( && tr(n').pState.cs[q] == Waiting 
                      && tr(n').pState.hasTicket[q] == tr(n).pState.hasTicket[q] )
}

lemma InvariantsWhenWaitingProcessWaits(tr: Trace, sched: Schedule, served: Process, 
            nonserved: Process, t: nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) && IsProcess(nonserved)
requires tr(t).pState.hasTicket[nonserved] > tr(t).pState.serving 
requires tr(t).pState.cs[nonserved] == Waiting
requires tr(t).pState.hasTicket[served] == tr(t).pState.serving 
requires sched(t) == nonserved 
requires WaitP(tr(t), nonserved, tr(t + 1))
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, t, t + 1)
{ }

lemma InvariantsWhenIdleProcessRequestsTicket(tr: Trace, sched: Schedule, served: Process, 
            nonserved: Process, t: nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) && IsProcess(nonserved)
requires tr(t).pState.cs[nonserved] == Idle
requires tr(t).pState.hasTicket[served] == tr(t).pState.serving 
requires sched(t) == nonserved 
requires RequestP(tr(t), nonserved, tr(t + 1))
ensures InvariantsInPeriodWithFrozenServedProcess(tr, sched, served, t, t + 1)
{ 
    assert tr(t + 1).pState.serving == tr(t).pState.serving;
    assert tr(t + 1).pState.cs[served] == tr(t).pState.cs[served];
    assert tr(t + 1).pState.hasTicket[served] == tr(t).pState.hasTicket[served];
    assert forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting)
                ==> ( && tr(t + 1).pState.cs[q] == Waiting 
                      && tr(t + 1).pState.hasTicket[q] == tr(t).pState.hasTicket[q] );
}

lemma InvariantsWhenNonservedProcessRequestsTicketOrWaits(tr: Trace, sched: Schedule, served: Process,
            nonserved: Process, t: nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) && IsProcess(nonserved)
requires sched(t) == nonserved
requires served != nonserved
requires tr(t).pState.serving == tr(t).pState.hasTicket[served]
requires RequestP(tr(t), nonserved, tr(t + 1)) || WaitP(tr(t), nonserved, tr(t + 1))
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
    OnlyRequestPAndWaitPAreAvailableForNonservedProcess(tr, sched, nonserved, t);
    InvariantsWhenNonservedProcessRequestsTicketOrWaits(tr, sched, served, nonserved, t);
}

lemma ServedProcessIsNotIdle(s: SState, p: Process)
requires Valid(s) && IsProcess(p)
requires s.pState.hasTicket[p] == s.pState.serving
ensures s.pState.cs[p] != Idle
{
    assert s.pState.hasTicket[p] > 0;
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
        // SetTimer(tr(t), tr(t + 1));
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




/*
lemma InvariantsInPeriodWhenServedProcessIsFrozen(tr: Trace, sched: Schedule, 
        served: Process, n: nat, t: nat, t': nat) 
// requires PreCondition(tr, sched, served, n, t, t')  
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) 
requires Valid(tr(n)) && Valid(tr(t)) && Valid(tr(t')) 
//
requires n <= t
requires tr(t).pState.serving == tr(n).pState.serving
requires tr(t).pState.cs[served] == tr(n).pState.cs[served]
requires tr(t).pState.hasTicket[served] == tr(n).pState.hasTicket[served]
requires forall q :: (IsProcess(q) && tr(n).pState.cs[q] == Waiting) ==> tr(t).pState.cs[q] == Waiting && tr(t).pState.hasTicket[q] == tr(n).pState.hasTicket[q]
//
requires tr(t).pState.hasTicket[served] == tr(t).pState.serving 
requires sched(t) != served
requires t' == t + 1
//
// ensures PostCondition(tr, sched, served, n, t')
ensures n <= t'
ensures tr(t').pState.serving == tr(n).pState.serving
ensures tr(t').pState.cs[served] == tr(n).pState.cs[served]
ensures tr(t').pState.hasTicket[served] == tr(n).pState.hasTicket[served]
ensures forall q :: (IsProcess(q) && tr(n).pState.cs[q] == Waiting) ==> tr(t').pState.cs[q] == Waiting && tr(t').pState.hasTicket[q] == tr(n).pState.hasTicket[q]
{
    InvariantsInNextStateWhenServedProcessIsFrozen(tr, sched, served, t, t + 1);
    //
    assert t <= t';
    assert tr(t').pState.serving == tr(t).pState.serving;
    assert tr(t').pState.cs[served] == tr(t).pState.cs[served];
    assert tr(t').pState.hasTicket[served] == tr(t).pState.hasTicket[served];
    assert forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting) ==> tr(t').pState.cs[q] == Waiting && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q];
    assert t' == t + 1;
    //
    BridgeForInvariants(tr, sched, served, n, t, t + 1);
}
*/

/*
predicate PostCondition(tr: Trace, sched: Schedule, served: Process, n: nat, n': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served) 
{
    && tr(n').pState.serving == tr(n).pState.serving
    && tr(n').pState.cs[served] == tr(n).pState.cs[served]
    && tr(n').pState.hasTicket[served] == tr(n).pState.hasTicket[served]
    && forall q :: (IsProcess(q) && tr(n).pState.cs[q] == Waiting) 
            ==> ( && tr(n').pState.cs[q] == Waiting 
                  && tr(n').pState.hasTicket[q] == tr(n).pState.hasTicket[q] )
}
*/

/*
lemma GetNextStepOfServedProcess(tr: Trace, sched: Schedule, served: Process, n: nat) returns (n': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served)
requires tr(n).pState.cs[served] != Idle && tr(n).pState.hasTicket[served] == tr(n).pState.serving
ensures n <= n' 
ensures sched(n') == served
ensures PostCondition(tr, sched, served, n, n')
{
    assert EventuallyTakeStep(sched, served, n);
    var u :| n <= u && sched(u) == served;
    assert sched(u) == served;
    n' := n;


    while sched(n') != served
        invariant n' <= u
        invariant PostCondition(tr, sched, served, n, n');
        decreases u - n'
    {   
        var k := n';  
             
        InvariantsInNextStateWhenServedProcessIsFrozen(tr, sched, served, k, k + 1);
        // InvariantsInPeriodWhenServedProcessIsFrozen(tr, sched, served, n, k, k + 1);
        assert PostCondition(tr, sched, served, n, k + 1);
        n' := k + 1;  
        
    }
    
}
*/

/*
lemma GetNextStepOfServedProcess(tr: Trace, sched: Schedule, served: Process, n: nat) returns (n': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served)
requires tr(n).pState.cs[served] != Idle && tr(n).pState.hasTicket[served] == tr(n).pState.serving
// requires tr(n).pState.hasTicket[served] == tr(n).pState.serving
ensures n <= n' 
ensures sched(n') == served
ensures tr(n').pState.serving == tr(n).pState.serving
ensures tr(n').pState.cs[served] == tr(n).pState.cs[served]
ensures tr(n').pState.hasTicket[served] == tr(n).pState.hasTicket[served]
ensures forall q :: (IsProcess(q) && tr(n).pState.cs[q] == Waiting) 
            ==> ( && tr(n').pState.cs[q] == Waiting 
                  && tr(n').pState.hasTicket[q] == tr(n).pState.hasTicket[q] )
{
    assert EventuallyTakeStep(sched, served, n);
    var u :| n <= u && sched(u) == served;
    n' := n;

    while sched(n') != served
        invariant n' <= u
        invariant tr(n').pState.serving == tr(n).pState.serving
        invariant tr(n').pState.cs[served] == tr(n).pState.cs[served]
        invariant tr(n').pState.hasTicket[served] == tr(n).pState.hasTicket[served]
        invariant forall q :: (IsProcess(q) && tr(n).pState.cs[q] == Waiting) 
                        ==> ( && tr(n').pState.cs[q] == Waiting 
                              && tr(n').pState.hasTicket[q] == tr(n).pState.hasTicket[q] )
        decreases u - n'
    {   
        
        var k := n';        

        assert IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(served);
        assert Valid(tr(n)) && Valid(tr(k)) && Valid(tr(k + 1));
        //
        assert n <= k;
        assert tr(k).pState.serving == tr(n).pState.serving;
        assert tr(k).pState.cs[served] == tr(n).pState.cs[served];
        assert tr(k).pState.hasTicket[served] == tr(n).pState.hasTicket[served];
        assert forall q :: (IsProcess(q) && tr(n).pState.cs[q] == Waiting) ==> tr(k).pState.cs[q] == Waiting && tr(k).pState.hasTicket[q] == tr(n).pState.hasTicket[q];
        //
        assert tr(k).pState.hasTicket[served] == tr(k).pState.serving;
        assert sched(k) != served;

        InvariantsInPeriodWhenServedProcessIsFrozen(tr, sched, served, n, k, k + 1);

        assert tr(k + 1).pState.serving == tr(n).pState.serving;
        assert tr(k + 1).pState.cs[served] == tr(n).pState.cs[served];
        assert tr(k + 1).pState.hasTicket[served] == tr(n).pState.hasTicket[served];
        assert forall q :: (IsProcess(q) && tr(n).pState.cs[q] == Waiting) 
                        ==> ( && tr(k + 1).pState.cs[q] == Waiting 
                              && tr(k + 1).pState.hasTicket[q] == tr(n).pState.hasTicket[q] );
        n' := n' + 1;    
    }
}
*/







lemma GetNextStepOfServedProcess(tr: Trace, sched: Schedule, served: Process, n: nat) returns (n': nat)
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

/*
lemma ServedProcessHasEnteredCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires sched(t) == p 
requires tr(t).pState.cs[p] == Waiting 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving 
ensures tr(t + 1).pState.cs[p] == Critical
ensures tr(t + 1).pState.hasTicket[p] == tr(t + 1).pState.serving 
ensures tr(t).pState.serving == tr(t + 1).pState.serving 
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> tr(t + 1).pState.cs[q] == Waiting && tr(t + 1).pState.hasTicket[q] == tr(t).pState.hasTicket[q]
{
    assert tr(t).pState.cs[p] == Waiting ==> !LeaveP(tr(t), p, tr(t + 1));
    assert tr(t).pState.cs[p] == Waiting ==> !RequestP(tr(t), p, tr(t + 1));
    assert tr(t).pState.cs[p] == Waiting && tr(t).pState.hasTicket[p] == tr(t).pState.serving 
                ==> !WaitP(tr(t), p, tr(t + 1));
}
*/

lemma ServedProcessHasEnteredCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat, t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires sched(t) == p 
requires tr(t).pState.cs[p] == Waiting 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires t' == t + 1
ensures tr(t').pState.cs[p] == Critical
ensures tr(t').pState.hasTicket[p] == tr(t').pState.serving 
ensures tr(t').pState.serving == tr(t).pState.serving 
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )                  
{
    assert tr(t).pState.cs[p] == Waiting ==> !LeaveP(tr(t), p, tr(t + 1));
    assert tr(t).pState.cs[p] == Waiting ==> !RequestP(tr(t), p, tr(t + 1));
    assert tr(t).pState.cs[p] == Waiting && tr(t).pState.hasTicket[p] == tr(t).pState.serving 
                ==> !WaitP(tr(t), p, tr(t + 1));
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
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> ( && tr(t').pState.cs[q] == Waiting 
                  && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q] )                  
{    
    var k := GetNextStepOfServedProcess(tr, sched, p, t);  
    t' := k + 1;  
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

lemma ServedProcessHasLeavedCriticalArea(tr: Trace, sched: Schedule, p: Process, 
            t: nat, t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] == Critical && tr(t).pState.hasTicket[p] == tr(t).pState.serving 
requires sched(t) == p
requires tr(t).pState.cs[p] == Critical
requires t' == t + 1
ensures LeaveP(tr(t), p, tr(t'))
ensures !RequestP(tr(t), p, tr(t'))
ensures !EnterP(tr(t), p, tr(t'))
ensures !WaitP(tr(t), p, tr(t'))
ensures tr(t').pState.serving == tr(t).pState.serving + 1
ensures forall q :: IsProcess(q) && tr(t).pState.cs[q] == Waiting ==> tr(t').pState.cs[q] == Waiting && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q]
ensures tr(t').pState.hasTicket[p] == 0 && tr(t').pState.cs[p] == Idle
{
    assert tr(t).pState.cs[p] == Critical;
}

lemma EventuallyLeavesTheCriticalAreaAfterFinishingAllTasks(tr: Trace, sched: Schedule, 
            p: Process, t: nat)  returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] == Critical && tr(t).pState.hasTicket[p] == tr(t).pState.serving 
ensures t <= t' 
ensures tr(t').pState.serving == tr(t).pState.serving + 1
ensures forall q :: IsProcess(q) && tr(t).pState.cs[q] == Waiting ==> tr(t').pState.cs[q] == Waiting && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q]
ensures tr(t').pState.hasTicket[p] == 0 && tr(t').pState.cs[p] == Idle
{    
    var k := GetNextStepOfServedProcess(tr, sched, p, t);        
    t' := k + 1;    
    ServedProcessHasLeavedCriticalArea(tr, sched, p, k, t');
}

lemma ServedProcessEventuallyLeavesCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] != Idle && tr(t).pState.hasTicket[p] == tr(t).pState.serving
ensures t <= t' && tr(t').pState.cs[p] != Critical 
ensures tr(t).pState.serving < tr(t').pState.serving 
ensures forall q :: (IsProcess(q) && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> tr(t').pState.cs[q] == Waiting && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q]
{        
    var k := ServedProcessEventuallyEntersCriticalArea(tr, sched, p, t);
    t' := EventuallyLeavesTheCriticalAreaAfterFinishingAllTasks(tr, sched, p, k); 
}


function CurrentlyServedProcess(s: PState): Process
requires ValidPState(s)
requires exists p | IsProcess(p) :: s.cs[p] == Waiting
{
    assert TicketIsInUse(s, s.serving);
    var q :| IsProcess(q) && s.cs[q] != Idle && s.hasTicket[q] == s.serving;
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
        var q := CurrentlyServedProcess(tr(n').pState);        
        if p == q {
            n' := ServedProcessEventuallyEntersCriticalArea(tr, sched, q, k);
            return;
        }
        else {
            n' := ServedProcessEventuallyLeavesCriticalArea(tr, sched, q, k);
        }        
    }
}

