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

datatype PState = PState( ticket: nat,
                          serving: nat,
                          cs: map<Process, CState>,
                          hasTicket: map<Process, nat>
)

datatype SState = SState(
    pState: PState,
    timer: map<Process, nat>
)

predicate IsProcess(p: Process)
{
    p in P
}

predicate InitPState(s: PState) 
ensures InitPState(s) ==> s.cs.Keys == P
ensures InitPState(s) ==> (forall p | IsProcess(p) :: s.cs[p] == Idle)
{
    && s.cs.Keys == s.hasTicket.Keys == P
    && s.ticket == s.serving == 1
    && (forall p :: IsProcess(p) ==> s.cs[p] == Idle)
    && (forall p :: IsProcess(p) ==> s.hasTicket[p] == 0)
}

predicate Init(s: SState)   
ensures Init(s) ==> s.pState.cs.Keys == P
ensures Init(s) ==> (forall p | IsProcess(p) :: s.pState.cs[p] == Idle)
{
    && pNull !in P
    && InitPState(s.pState)
}

predicate Next(s: SState, s': SState)
{
    && Valid(s)
    && ( || (SetTimer(s, s'))
         || (exists p | IsProcess(p) :: NextP(s, p, s')))
}

predicate SetTimer(s: SState, s': SState)
{
    && s'.pState == s.pState
}

predicate NextP(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    || RequestP(s, p, s')
    || LeaveP(s, p, s')
    || EnterP(s, p, s')
}

predicate RequestP(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    && s.pState.cs[p] == Idle
    && s'.pState.hasTicket == s.pState.hasTicket[p := s.pState.ticket]
    && s'.pState.ticket == s.pState.ticket + 1
    && s'.pState.serving == s.pState.serving
    && s'.pState.cs == s.pState.cs[p := Waiting]
}

predicate EnterP(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
    && s.pState.cs[p] == Waiting
    && s'.pState.ticket == s.pState.ticket
    && s'.pState.serving == s.pState.serving
    && s'.pState.hasTicket == s.pState.hasTicket
    && ( || ( && s.pState.hasTicket[p] == s.pState.serving
              && s'.pState.cs == s.pState.cs[p := Critical]
            )
         || ( && s.pState.hasTicket[p] < s.pState.serving
              && s'.pState.cs == s.pState.cs
            ))
}

predicate LeaveP(s: SState, p: Process, s': SState)
requires Valid(s)
requires IsProcess(p)
{
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
    && (forall p, q :: (IsProcess(p) && q in P && p != q && s.cs[p] != Idle && s.cs[q] != Idle) 
                        ==>  s.hasTicket[p] != s.hasTicket[q])                          
    && (forall p :: (IsProcess(p) && s.cs[p] == Critical) 
                        ==> s.hasTicket[p] == s.serving)
    && (forall i :: s.serving <= i < s.ticket ==> TicketIsInUse(s,i))    
    && (forall p :: (IsProcess(p) && s.cs[p] == Idle)
                        ==>  s.hasTicket[p] == 0)                         
    && (forall p, q :: (IsProcess(p) && q in P && p != q && (s.hasTicket[p] > 0 || s.hasTicket[q] > 0))
                        ==>  s.hasTicket[p] != s.hasTicket[q])   
    && (forall p :: (IsProcess(p) && s.cs[p] != Idle)
                        ==> s.hasTicket[p] > 0)
}

predicate Valid(s: SState)
{
    && pNull !in P
    && ValidPState(s.pState)
}

lemma MutualExclusion(s: SState, p:Process, q:Process)
requires Valid(s)
requires IsProcess(p) && q in P 
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
ensures exists q :: q in P && TicketIsInUseBy(s, i, q); 
{
    assert TicketIsInUse(s, i);
    var q :| q in P && TicketIsInUseBy(s, i, q); 
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

        forall i | s'.pState.serving  <= i < s.pState.ticket         
        ensures TicketIsInUse(s'.pState, i)
        {            
            ExistingOwnerOfTicket(s.pState, i);
            var q :| q in P && TicketIsInUseBy(s.pState, i, q); 
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
            var q :| q in P && TicketIsInUseBy(s.pState, i, q); 
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
            var q :| q in P && TicketIsInUseBy(s.pState, i, q); 
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
                                       || EnterP(s, p, s')
                                       || LeaveP(s, p, s'));
        
            if RequestP(s, p, s') {
                RequestPPreservesValid(s, p, s');            
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


type Schedule = (Process, nat) -> bool

// Warning: /!\ No terms found to trigger on.
predicate IsSchedule(sched: Schedule)
{
    && (forall p, t :: sched(p, t) ==> IsProcess(p))
    && (forall t: nat :: exists p: Process :: sched(p, t))
}


type Trace = nat -> SState

predicate IsTrace(tr: Trace, sched: Schedule)
requires IsSchedule(sched)
{
    && Init(tr(0))
    && forall i: nat ::  && Valid(tr(i))
                         && exists p :: IsProcess(p) && sched(p, i) && NextP(tr(i), p, tr(i+1))
}



predicate EventuallyTakeStep(sched: Schedule, p: Process, t: nat)
requires IsSchedule(sched)
requires IsProcess(p)
{
    exists t' | t' >= t :: sched(p, t') 
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


lemma AProcessWithoutAServingTicketCannotWorkInTheCriticalArea(tr: Trace, sched: Schedule, p: Process, n: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p) 
requires tr(n).pState.hasTicket[p] != tr(n).pState.serving
requires sched(p, n)
ensures !LeaveP(tr(n), p, tr(n + 1))
ensures !EnterP(tr(n), p, tr(n + 1))
{}

lemma AnIdleProcessInTheCriticalArea(tr: Trace, sched: Schedule, p: Process, n: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p) 
requires tr(n).pState.cs[p] == Idle
requires sched(p, n)
ensures !LeaveP(tr(n), p, tr(n + 1))
ensures !EnterP(tr(n), p, tr(n + 1))
{}

lemma OnlyRequestPIsAvailable(tr: Trace, sched: Schedule, p: Process, n: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p) 
requires tr(n).pState.cs[p] != Idle ==> tr(n).pState.hasTicket[p] != tr(n).pState.serving
requires sched(p, n)
ensures NextP(tr(n), p, tr(n + 1)) <==> RequestP(tr(n), p, tr(n + 1))
ensures !LeaveP(tr(n), p, tr(n + 1))
ensures !EnterP(tr(n), p, tr(n + 1))
{
    if tr(n).pState.cs[p] == Idle {
        AnIdleProcessInTheCriticalArea(tr, sched, p, n);
    }
    else {
        assert tr(n).pState.hasTicket[p] != tr(n).pState.serving;
        AProcessWithoutAServingTicketCannotWorkInTheCriticalArea(tr, sched, p, n);
    }
}


lemma NonServedProcessCanOnlyRequestTicket(tr: Trace, sched: Schedule, p: Process, t: nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p) 
requires !sched(p, t)
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving && tr(t).pState.hasTicket[p] > 0
ensures tr(t + 1).pState.serving == tr(t).pState.serving
ensures tr(t + 1).pState.cs[p] == tr(t).pState.cs[p]
ensures tr(t + 1).pState.hasTicket[p] == tr(t).pState.hasTicket[p]
ensures forall q :: (q in P && tr(t).pState.cs[q] == Waiting) ==> tr(t + 1).pState.cs[q] == Waiting && tr(t + 1).pState.hasTicket[q] == tr(t).pState.hasTicket[q]
{
    var q: Process :| sched(q, t);   
    assert Valid(tr(t));
    assert NextP(tr(t), q, tr(t + 1));
 
    assert tr(t).pState.cs[q] != Idle ==> tr(t).pState.hasTicket[q] != tr(t).pState.hasTicket[p];
    assert tr(t).pState.cs[q] != Idle ==> tr(t).pState.hasTicket[q] != tr(t).pState.serving;
    assert q in P && sched(q, t);
    OnlyRequestPIsAvailable(tr, sched, q, t);
    assert NextP(tr(t), q, tr(t + 1)) <==> RequestP(tr(t), q, tr(t + 1));  
    assert RequestP(tr(t), q, tr(t + 1));  
    
}


lemma NonServedProcessCanOnlyRequestTicketInc1(tr: Trace, sched: Schedule, p: Process, t: nat, t': nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p) 
requires !sched(p, t) 
requires tr(t).pState.hasTicket[p] == tr(t).pState.serving && tr(t).pState.hasTicket[p] > 0
requires t' == t + 1
ensures tr(t').pState.serving == tr(t).pState.serving
ensures tr(t').pState.cs[p] == tr(t).pState.cs[p]
ensures tr(t').pState.hasTicket[p] == tr(t).pState.hasTicket[p]
ensures forall q :: (q in P && tr(t).pState.cs[q] == Waiting) ==> tr(t').pState.cs[q] == Waiting && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q]
{
    NonServedProcessCanOnlyRequestTicket(tr, sched, p, t);
}


lemma GetNextStepOfServedProcess(tr: Trace, sched: Schedule, p: Process, n: nat) returns (n': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(n).pState.cs[p] != Idle && tr(n).pState.hasTicket[p] == tr(n).pState.serving
ensures n <= n' && sched(p, n')
ensures tr(n').pState.serving == tr(n).pState.serving
ensures tr(n').pState.cs[p] == tr(n).pState.cs[p]
ensures tr(n').pState.hasTicket[p] == tr(n).pState.hasTicket[p]
ensures forall q :: (q in P && tr(n).pState.cs[q] == Waiting) ==> tr(n').pState.cs[q] == Waiting && tr(n').pState.hasTicket[q] == tr(n).pState.hasTicket[q]
{
    assert EventuallyTakeStep(sched, p, n);
    var u :| n <= u && sched(p, u);
    n' := n;
    while !sched(p, n') 
        invariant n' <= u
        invariant tr(n').pState.serving == tr(n).pState.serving
        invariant tr(n').pState.cs[p] == tr(n).pState.cs[p]
        invariant tr(n').pState.hasTicket[p] == tr(n).pState.hasTicket[p]
        invariant forall q :: (q in P && tr(n).pState.cs[q] == Waiting) ==> tr(n').pState.cs[q] == Waiting && tr(n').pState.hasTicket[q] == tr(n).pState.hasTicket[q]
        decreases u - n'
    {   
        var k := n';
        NonServedProcessCanOnlyRequestTicketInc1(tr, sched, p, k, k + 1);       
        n' := n' + 1;    
    }
}




lemma ServedProcessMustEntersCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires sched(p, t) && tr(t).pState.cs[p] == Waiting && tr(t).pState.hasTicket[p] == tr(t).pState.serving 
ensures NextP(tr(t), p, tr(t + 1)) <==> EnterP(tr(t), p, tr(t + 1))
{
}


lemma ServedProcessEventuallyEntersCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] != Idle && tr(t).pState.hasTicket[p] == tr(t).pState.serving
ensures t <= t' && tr(t').pState.cs[p] == Critical 
ensures tr(t').pState.hasTicket[p] == tr(t').pState.serving 
ensures tr(t).pState.serving == tr(t').pState.serving 
ensures forall q :: (q in P && tr(t).pState.cs[q] == Waiting && q != p) 
            ==> tr(t').pState.cs[q] == Waiting && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q]
{        
    if tr(t).pState.cs[p] == Critical { 
        t' := t;        
    }
    else {
        var k := GetNextStepOfServedProcess(tr, sched, p, t);
        ServedProcessMustEntersCriticalArea(tr, sched, p, k);
        t' := k + 1;
    }
}



lemma EventuallyLeavesTheCriticalAreaAfterFinishingAllTasks(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] == Critical && tr(t).pState.hasTicket[p] == tr(t).pState.serving 
ensures t <= t' 
ensures tr(t').pState.serving == tr(t).pState.serving + 1
ensures forall q :: q in P && tr(t).pState.cs[q] == Waiting ==> tr(t').pState.cs[q] == Waiting && tr(t').pState.hasTicket[q] == tr(t).pState.hasTicket[q]
ensures tr(t').pState.hasTicket[p] == 0 && tr(t').pState.cs[p] == Idle
{
    assert Valid(tr(t));
    var k := GetNextStepOfServedProcess(tr, sched, p, t);    
    assert t <= k;
    assert tr(t).pState.cs[p] == tr(t).pState.cs[p] == Critical;
    
    assert !RequestP(tr(k), p, tr(k + 1));
    assert !EnterP(tr(k), p, tr(k + 1));    
    assert NextP(tr(k), p, tr(k + 1));
    assert LeaveP(tr(k), p, tr(k + 1));
        
    assert tr(k + 1).pState.serving == tr(t).pState.serving + 1;
    assert forall q :: q in P && tr(t).pState.cs[q] == Waiting ==> tr(k + 1).pState.cs[q] == Waiting && tr(k + 1).pState.hasTicket[q] == tr(t).pState.hasTicket[q];
    assert tr(k + 1).pState.hasTicket[p] == 0 && tr(k + 1).pState.cs[p] == Idle;

    t' := k + 1;    
}

lemma ServedProcessEventuallyLeavesCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && IsProcess(p)
requires tr(t).pState.cs[p] != Idle && tr(t).pState.hasTicket[p] == tr(t).pState.serving
ensures t <= t' && tr(t').pState.cs[p] != Critical 
ensures tr(t).pState.serving < tr(t').pState.serving 
ensures forall q :: (q in P && tr(t).pState.cs[q] == Waiting && q != p) 
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
    var q :| q in P && s.cs[q] != Idle && s.hasTicket[q] == s.serving;
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
