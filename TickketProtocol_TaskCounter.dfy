//============================================================
// Protocol Specification
//============================================================

//============================================================
// Process behaviors
//============================================================

type Process(==)
datatype CState = Idle | Waiting | Critical
const P : set<Process>;

datatype TSState = TSState( ticket: nat,
                            serving: nat,
                            cs: map<Process, CState>,
                            hasTicket: map<Process, nat>,
                            task_no: map<Process, nat>,
                            done: map<Process, nat>
)

predicate Init(s:TSState)
ensures Init(s) ==> s.cs.Keys == P
ensures Init(s) ==> (forall p | p in P :: s.cs[p] == Idle)
{
    && s.cs.Keys == s.hasTicket.Keys == s.task_no.Keys == s.done.Keys == P
    && s.ticket == s.serving == 1
    && (forall p :: p in P ==> s.cs[p] == Idle)
    && (forall p :: p in P ==> s.hasTicket[p] == 0)
    && (forall p :: p in P ==> s.task_no[p] == 0)
    && (forall p :: p in P ==> s.done[p] == 0)
}

predicate Next(s: TSState, s': TSState)
{
    && Valid(s)
    && exists p | p in P :: NextP(s, p, s')
}

predicate NextP(s: TSState, p: Process, s': TSState)
requires Valid(s)
requires p in P
{
    || RequestP(s, p, s')
    || LeaveP(s, p, s')
    || EnterP(s, p, s')
    || CreateNewTasksP(s, p, s')   
    || FinishOneTaskP(s, p, s')      
}

predicate RequestP(s: TSState, p: Process, s': TSState)
requires Valid(s)
requires p in P
{
    && s.cs[p] == Idle
    && s'.hasTicket== s.hasTicket[p := s.ticket]
    && s'.ticket == s.ticket + 1
    && s'.serving == s.serving
    && s'.cs == s.cs[p := Waiting]
    && s'.task_no == s.task_no
    && s'.done == s.done
}

predicate EnterP(s: TSState, p: Process, s': TSState)
requires Valid(s)
requires p in P
{
    && s.cs[p] == Waiting
    && s'.ticket == s.ticket
    && s'.serving == s.serving
    && s'.hasTicket == s.hasTicket
    && ( || ( && s.hasTicket[p] == s.serving
              && s'.cs == s.cs[p := Critical]
            )
         || ( && s.hasTicket[p] < s.serving
              && s'.cs == s.cs
            ))
       /* 
       (s'.cs ==  
        if s.hasTicket[p] == s.serving then
            s.cs[p := Critical]
        else
            s.cs)
       // Subtle difference: infinitely loop in Waiting since a process is not forced 
          to enter the critical area.
       ( || (  && s.hasTicket[p] == s.serving
               && s'.cs == s.cs[p := Critical]
            )
         || s'.cs == s.cs
       ) 
       */         
    && s'.task_no == s.task_no
    && s'.done == s.done            
}

predicate CreateNewTasksP(s: TSState, p: Process, s': TSState)
requires Valid(s)
requires p in P
{      
    var k :| k > 0;
    && s.cs[p] == Critical
    && s.hasTicket[p] == s.serving 
    && 0 == s.task_no[p] 
    && s'.ticket == s.ticket
    && s'.serving == s.serving 
    && s'.cs == s.cs
    && s'.hasTicket== s.hasTicket
    && s'.task_no == s.task_no[p := k]
    && s'.done == s.done      
}

predicate FinishOneTaskP(s: TSState, p: Process, s': TSState)
requires Valid(s)
requires p in P
{   
    && s.cs[p] == Critical
    && s.hasTicket[p] == s.serving 
    && 0 < s.task_no[p]
    && s.done[p] < s.task_no[p]    
    && s'.ticket == s.ticket
    && s'.serving == s.serving  
    && s'.cs == s.cs
    && s'.hasTicket== s.hasTicket
    && s'.task_no == s.task_no
    && s'.done == s.done[p := s.done[p] + 1]      
}

// The minor change here is that a thread needs to throw away
// its ticket before leaving the critical area.
predicate LeaveP(s: TSState, p: Process, s': TSState)
requires Valid(s)
requires p in P
{
    && s.cs[p] == Critical
    && s.task_no[p] == s.done[p]
    // && s.task_no[p] == 0
    && s.task_no[p] > 0
    && s.hasTicket[p] == s.serving 
    && s'.ticket == s.ticket
    && s'.serving == s.serving + 1    
    && s'.cs == s.cs[p := Idle]
    && s'.hasTicket== s.hasTicket[p := 0]
    && s'.task_no == s.task_no[p := 0]
    && s'.done == s.done[p := 0]    
}

//============================================================
// Safety Property - Mutual Exclusion
//============================================================

predicate TicketIsInUseBy(s: TSState, i: nat, p:Process)
requires p in P
requires s.cs.Keys == s.hasTicket.Keys == P
{
    s.cs[p] != Idle && s.hasTicket[p] == i
}

predicate TicketIsInUse(s: TSState, i: nat)
requires s.cs.Keys == s.hasTicket.Keys == P
{
    exists p :: p in P && s.cs[p] != Idle && s.hasTicket[p] == i
}

predicate Valid(s: TSState)
{
    && s.cs.Keys == s.hasTicket.Keys == s.task_no.Keys == s.done.Keys == P
    && 1 <= s.serving <= s.ticket
    && (forall p :: (p in P && s.cs[p] != Idle)
                        ==> s.serving <= s.hasTicket[p] < s.ticket)  
    && (forall p, q :: (p in P && q in P && p != q && s.cs[p] != Idle && s.cs[q] != Idle) 
                        ==>  s.hasTicket[p] != s.hasTicket[q])                          
    && (forall p :: (p in P && s.cs[p] == Critical) 
                        ==> s.hasTicket[p] == s.serving)
    && (forall i :: s.serving <= i < s.ticket ==> TicketIsInUse(s,i))    

    && (forall p :: p in P ==> s.task_no[p] >= 0) 
    && (forall p :: p in P ==> 0 <= s.done[p] <= s.task_no[p]) 
    // && (forall p :: (p in P && s.task_no[p] == 0) ==> s.done[p] == 0) 
    && (forall p :: (p in P && s.cs[p] != Critical) ==> 0 == s.done[p] == s.task_no[p]) 
    
    && (forall p :: (p in P && s.task_no[p] > 0)
                        ==>  s.cs[p] == Critical)
    
    && (forall p :: (p in P && s.cs[p] == Idle)
                        ==>  s.hasTicket[p] == 0)                         
    && (forall p, q :: (p in P && q in P && p != q && (s.hasTicket[p] > 0 || s.hasTicket[q] > 0))
                        ==>  s.hasTicket[p] != s.hasTicket[q])   
    && (forall p :: (p in P && s.cs[p] != Idle)
                        ==> s.hasTicket[p] > 0)
}

lemma MutualExclusion(s: TSState, p:Process, q:Process)
requires Valid(s)
requires p in P && q in P 
requires s.cs[p] == s.cs[q] == Critical 
ensures p == q
{
}

//============================================================
// Valid is an inductive invariant 
//============================================================


lemma InitPreservesValid(s:TSState)
ensures Init(s) ==> Valid(s)
{
}

lemma ExistingOwnerOfTicket(s: TSState, i: nat) 
requires Valid(s)
requires s.serving <= i < s.ticket
ensures exists q :: q in P && TicketIsInUseBy(s, i, q); 
{
    assert TicketIsInUse(s, i);
    var q :| q in P && TicketIsInUseBy(s, i, q); 
}


lemma RequestPPreservesValid(s:TSState, p: Process, s':TSState)
requires p in P
ensures Valid(s) && RequestP(s, p, s') ==> Valid(s')             
{
    if Valid(s) && RequestP(s, p, s') 
    {
        assert s'.ticket == s.ticket + 1;

        assert TicketIsInUseBy(s', s.ticket, p);
        assert TicketIsInUse(s', s.ticket);

        forall i | s'.serving  <= i < s.ticket         
        ensures TicketIsInUse(s', i)
        {            
            ExistingOwnerOfTicket(s, i);
            var q :| q in P && TicketIsInUseBy(s, i, q); 
            assert TicketIsInUseBy(s, i, q);
            assert TicketIsInUseBy(s', i, q);          
        }                 
    }
}

lemma EnterPPreservesValid(s:TSState, p: Process, s':TSState)
requires p in P
ensures Valid(s) && EnterP(s, p, s') ==> Valid(s')             
{
    if Valid(s) && EnterP(s, p, s') 
    {
        assert s.ticket == s'.ticket;

        forall i | s'.serving  <= i < s.ticket         
        ensures TicketIsInUse(s', i)
        {
            ExistingOwnerOfTicket(s, i);
            var q :| q in P && TicketIsInUseBy(s, i, q); 
            assert TicketIsInUseBy(s, i,  q);
            assert TicketIsInUseBy(s', i, q);            
        }             
    }
}


lemma LeavePPreservesValid(s:TSState, p: Process, s':TSState)
requires p in P
ensures Valid(s) && LeaveP(s, p, s') ==> Valid(s')             
{
    if Valid(s) && LeaveP(s, p, s') 
    {
        assert s.ticket == s'.ticket;

        forall i | s'.serving  <= i < s.ticket         
        ensures TicketIsInUse(s', i)
        {
            ExistingOwnerOfTicket(s, i);
            var q :| q in P && TicketIsInUseBy(s, i, q); 
            assert TicketIsInUseBy(s, i, q);
            assert TicketIsInUseBy(s', i, q);            
        }                
    }
}

lemma CreateNewTasksPPreservesValid(s:TSState, p: Process, s':TSState)
requires p in P
ensures Valid(s) && CreateNewTasksP(s, p, s') ==> Valid(s')   
{
    if Valid(s) && CreateNewTasksP(s, p, s') 
    {
        assert s.ticket == s'.ticket;
        assert s.serving == s'.serving;
        

        forall i | s'.serving  <= i < s.ticket         
        ensures TicketIsInUse(s', i)
        {
            ExistingOwnerOfTicket(s, i);
            var q :| q in P && TicketIsInUseBy(s, i, q); 
            assert TicketIsInUseBy(s, i, q);
            assert TicketIsInUseBy(s', i, q);            
        }        

        /*
        assert forall q :: (q in P && q != p) ==> (s'.task_no[q] == s.task_no[q]);
        assert forall q :: (q in P && q != p) ==> (s'.done[q] == s.done[q]);
        assert s'.task_no[p] > 0 && s'.done[p] == s.done[p];
        assert s'.task_no[p] > s'.done[p];
        assert forall q :: q in P ==> s'.done[q] <= s'.task_no[q];
        */
    }
}



lemma FinishOneTaskPPreservesValid(s:TSState, p: Process, s':TSState)
requires p in P
ensures Valid(s) && FinishOneTaskP(s, p, s') ==> Valid(s')             
{
    if Valid(s) && FinishOneTaskP(s, p, s') 
    {
        assert s.ticket == s'.ticket;

        forall i | s'.serving  <= i < s.ticket         
        ensures TicketIsInUse(s', i)
        {
            ExistingOwnerOfTicket(s, i);
            var q :| q in P && TicketIsInUseBy(s, i, q); 
            assert TicketIsInUseBy(s, i, q);
            assert TicketIsInUseBy(s', i, q);            
        }                
    }
}

lemma TransPreservesValid(s:TSState, s':TSState)
ensures Valid(s) && Next(s,s') ==> Valid(s')   
{
    if Valid(s) && Next(s,s') 
    {
        var p :| p in P && ( || RequestP(s, p, s') 
                             || EnterP(s, p, s')
                             || CreateNewTasksP(s, p, s') 
                             || FinishOneTaskP(s, p, s')
                             || LeaveP(s, p, s'));
        
        if RequestP(s, p, s') 
        {
            RequestPPreservesValid(s, p, s');            
            // assert Valid(s');
        }

        if EnterP(s, p, s') 
        {
            EnterPPreservesValid(s, p, s');            
            // assert Valid(s');
        }

        if CreateNewTasksP(s, p, s')
        {
            CreateNewTasksPPreservesValid(s, p, s');
            // assert Valid(s');
        }
                             
        if FinishOneTaskP(s, p, s')
        {
            FinishOneTaskPPreservesValid(s, p, s');
            // assert Valid(s');
        }

        if LeaveP(s, p, s') 
        {
            LeavePPreservesValid(s, p, s');            
            // assert Valid(s');
        }

        assert Valid(s');
    }
}

lemma ValidIsInductive(s:TSState, s':TSState)
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
    forall t :: sched(t) in P
}

type Trace = nat -> TSState

predicate IsTrace(tr: Trace, sched: Schedule)
requires IsSchedule(sched)
{
    && Init(tr(0))
    && forall i:nat ::  && Valid(tr(i))
                        && NextP(tr(i), sched(i), tr(i+1))
}

predicate EventuallyTakeStep(sched: Schedule, p: Process, t: nat)
requires IsSchedule(sched)
requires p in P
{
    exists t' | t' >= t :: sched(t') == p
}


predicate IsFairSchedule(sched: Schedule)
{
    && IsSchedule(sched)
    && forall p,n | p in P :: EventuallyTakeStep(sched, p, n)
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
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P && sched(n) == p
requires tr(n).hasTicket[p] != tr(n).serving
ensures !LeaveP(tr(n), sched(n), tr(n + 1))
ensures !EnterP(tr(n), sched(n), tr(n + 1))
ensures !CreateNewTasksP(tr(n), sched(n), tr(n + 1))
ensures !FinishOneTaskP(tr(n), sched(n), tr(n + 1))
{}

lemma AnIdleProcessInTheCriticalArea(tr: Trace, sched: Schedule, p: Process, n: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P && sched(n) == p
requires tr(n).cs[p] == Idle
ensures !LeaveP(tr(n), sched(n), tr(n + 1))
ensures !EnterP(tr(n), sched(n), tr(n + 1))
ensures !CreateNewTasksP(tr(n), sched(n), tr(n + 1))
ensures !FinishOneTaskP(tr(n), sched(n), tr(n + 1))
{}

lemma OnlyRequestPIsAvailable(tr: Trace, sched: Schedule, p: Process, n: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P && sched(n) == p
requires tr(n).cs[p] != Idle ==> tr(n).hasTicket[p] != tr(n).serving
ensures NextP(tr(n), sched(n), tr(n + 1)) <==> RequestP(tr(n), sched(n), tr(n + 1))
ensures !LeaveP(tr(n), sched(n), tr(n + 1))
ensures !EnterP(tr(n), sched(n), tr(n + 1))
ensures !CreateNewTasksP(tr(n), sched(n), tr(n + 1))
ensures !FinishOneTaskP(tr(n), sched(n), tr(n + 1))
{
    if tr(n).cs[p] == Idle {
        AnIdleProcessInTheCriticalArea(tr, sched, p, n);
    }
    else {
        assert tr(n).hasTicket[p] != tr(n).serving;
        AProcessWithoutAServingTicketCannotWorkInTheCriticalArea(tr, sched, p, n);
    }
}

lemma NonServedProcessCanOnlyRequestTicket(tr: Trace, sched: Schedule, p: Process, t: nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P 
requires sched(t) != p 
requires tr(t).hasTicket[p] == tr(t).serving && tr(t).hasTicket[p] > 0
ensures tr(t + 1).serving == tr(t).serving
ensures tr(t + 1).cs[p] == tr(t).cs[p]
ensures tr(t + 1).hasTicket[p] == tr(t).hasTicket[p]
ensures forall q :: (q in P && tr(t).cs[q] == Waiting) ==> tr(t + 1).cs[q] == Waiting && tr(t + 1).hasTicket[q] == tr(t).hasTicket[q]
ensures tr(t + 1).task_no[p] == tr(t).task_no[p] && tr(t + 1).done[p] == tr(t).done[p]
{
    var q := sched(t);   
    assert Valid(tr(t));
    assert NextP(tr(t), q, tr(t + 1));
 
    assert tr(t).cs[q] != Idle ==> tr(t).hasTicket[q] != tr(t).hasTicket[p];
    assert tr(t).cs[q] != Idle ==> tr(t).hasTicket[q] != tr(t).serving;
    assert q in P && sched(t) == q;        
    OnlyRequestPIsAvailable(tr, sched, q, t);
    assert NextP(tr(t), q, tr(t + 1)) <==> RequestP(tr(t), q, tr(t + 1));  
    assert RequestP(tr(t), q, tr(t + 1));  
    
}

lemma NonServedProcessCanOnlyRequestTicketInc1(tr: Trace, sched: Schedule, p: Process, t: nat, t': nat) 
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P 
requires sched(t) != p 
requires tr(t).hasTicket[p] == tr(t).serving && tr(t).hasTicket[p] > 0
requires t' == t + 1
ensures tr(t').serving == tr(t).serving
ensures tr(t').cs[p] == tr(t).cs[p]
ensures tr(t').hasTicket[p] == tr(t).hasTicket[p]
ensures forall q :: (q in P && tr(t).cs[q] == Waiting) ==> tr(t').cs[q] == Waiting && tr(t').hasTicket[q] == tr(t).hasTicket[q]
ensures tr(t').task_no[p] == tr(t).task_no[p] && tr(t').done[p] == tr(t).done[p]
{
    NonServedProcessCanOnlyRequestTicket(tr, sched, p, t);
}


lemma GetNextStepOfServedProcess(tr: Trace, sched: Schedule, p: Process, n: nat) returns (n': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P
requires tr(n).cs[p] != Idle && tr(n).hasTicket[p] == tr(n).serving
ensures n <= n' && sched(n') == p
ensures tr(n').serving == tr(n).serving
ensures tr(n').cs[p] == tr(n).cs[p]
ensures tr(n').hasTicket[p] == tr(n).hasTicket[p]
ensures forall q :: (q in P && tr(n).cs[q] == Waiting) ==> tr(n').cs[q] == Waiting && tr(n').hasTicket[q] == tr(n).hasTicket[q]
ensures tr(n').task_no[p] == tr(n).task_no[p] 
ensures tr(n').done[p] == tr(n).done[p]
{
    assert EventuallyTakeStep(sched, p, n);
    var u :| n <= u && sched(u) == p;
    n' := n;
    
    while sched(n') != p
        invariant n' <= u
        invariant tr(n').serving == tr(n).serving
        invariant tr(n').cs[p] == tr(n).cs[p]
        invariant tr(n').hasTicket[p] == tr(n).hasTicket[p]
        invariant forall q :: (q in P && tr(n).cs[q] == Waiting) ==> tr(n').cs[q] == Waiting && tr(n').hasTicket[q] == tr(n).hasTicket[q]
        invariant tr(n').task_no[p] == tr(n).task_no[p] 
        invariant tr(n').done[p] == tr(n).done[p]        
        decreases u - n'
    {   
        /*
        var k := n';
        NonServedProcessCanOnlyRequestTicket(tr, sched, p, k);       
        n' := n' + 1;
        */
        var k := n';
        NonServedProcessCanOnlyRequestTicketInc1(tr, sched, p, k, k + 1);       
        n' := n' + 1;    
    }
}


lemma ServedProcessMustEntersCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P
requires sched(t) == p && tr(t).cs[p] == Waiting && tr(t).hasTicket[p] == tr(t).serving 
ensures NextP(tr(t), p, tr(t + 1)) <==> EnterP(tr(t), p, tr(t + 1))
{
}

lemma ServedProcessEventuallyEntersCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P
requires tr(t).cs[p] != Idle && tr(t).hasTicket[p] == tr(t).serving
ensures t <= t' && tr(t').cs[p] == Critical 
ensures tr(t').hasTicket[p] == tr(t').serving 
ensures tr(t').task_no[p] == tr(t).task_no[p]
ensures tr(t).serving == tr(t').serving 
ensures forall q :: (q in P && tr(t).cs[q] == Waiting && q != p) 
            ==> tr(t').cs[q] == Waiting && tr(t').hasTicket[q] == tr(t).hasTicket[q]
{        
    if tr(t).cs[p] == Critical { 
        t' := t;        
    }
    else {
        var k := GetNextStepOfServedProcess(tr, sched, p, t);
        ServedProcessMustEntersCriticalArea(tr, sched, p, k);
        t' := k + 1;
    }
}

lemma ServedProcessMustCreateNewTasks(tr: Trace, sched: Schedule, p: Process, t: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P
requires sched(t) == p && tr(t).cs[p] == Critical && tr(t).hasTicket[p] == tr(t).serving 
requires tr(t).task_no[p] == 0
ensures NextP(tr(t), p, tr(t + 1)) <==> CreateNewTasksP(tr(t), p, tr(t + 1))
{
}

lemma AvailableStepForFreshCriticalProcess(tr: Trace, sched: Schedule, p: Process, t: nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P
requires sched(t) == p
requires tr(t).cs[p] == Critical 
requires tr(t).hasTicket[p] == tr(t).serving 
requires  tr(t).task_no[p] == tr(t).done[p] == 0
ensures !RequestP(tr(t), p, tr(t + 1))
ensures !EnterP(tr(t), p, tr(t + 1))
ensures !LeaveP(tr(t), p, tr(t + 1))
ensures !FinishOneTaskP(tr(t), p, tr(t + 1))
ensures CreateNewTasksP(tr(t), p, tr(t + 1))
{
}

lemma EventuallyCreateTasksAfterEnteringTheCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P
requires tr(t).cs[p] == Critical 
requires tr(t).hasTicket[p] == tr(t).serving 
requires  tr(t).task_no[p] == tr(t).done[p] == 0
ensures t <= t' 
ensures tr(t').serving == tr(t).serving
ensures tr(t').cs[p] == tr(t).cs[p]
ensures tr(t').hasTicket[p] == tr(t).hasTicket[p]
ensures forall q :: q in P && tr(t).cs[q] == Waiting ==> tr(t').cs[q] == Waiting && tr(t').hasTicket[q] == tr(t).hasTicket[q]
ensures tr(t').task_no[p] > 0 && tr(t').done[p] == 0
{
    var k := GetNextStepOfServedProcess(tr, sched, p, t);    
    AvailableStepForFreshCriticalProcess(tr, sched, p, k);
    t' := k + 1;    
}

lemma ServedProcessEventuallyCreatesNewTasks(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P
requires tr(t).cs[p] != Idle && tr(t).hasTicket[p] == tr(t).serving
ensures t <= t'
ensures tr(t').cs[p] == Critical && tr(t').hasTicket[p] == tr(t').serving
ensures tr(t').task_no[p] > 0 && tr(t').done[p] >= 0
ensures tr(t').task_no[p] >= tr(t').done[p] 
ensures tr(t).serving == tr(t').serving 
ensures forall q :: (q in P && tr(t).cs[q] == Waiting && q != p) 
            ==> tr(t').cs[q] == Waiting && tr(t').hasTicket[q] == tr(t).hasTicket[q]
{    
    if tr(t).task_no[p] > 0 { 
        t' := t;        
    }
    else {       
        var k0 := ServedProcessEventuallyEntersCriticalArea(tr, sched, p, t); 
        t' := EventuallyCreateTasksAfterEnteringTheCriticalArea(tr, sched, p, k0);
    }
    
}

lemma EventuallyFinishAllTasksAfterCreatingTasks(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P
requires tr(t).cs[p] == Critical && tr(t).hasTicket[p] == tr(t).serving
requires tr(t).task_no[p] > 0 && tr(t).done[p] >= 0
requires tr(t).task_no[p] >= tr(t).done[p]
ensures t <= t' 
ensures tr(t').serving == tr(t).serving
ensures tr(t').cs[p] == tr(t).cs[p] == Critical
ensures tr(t').hasTicket[p] == tr(t).hasTicket[p]
ensures forall q :: (q in P && tr(t).cs[q] == Waiting) ==> tr(t').cs[q] == Waiting && tr(t').hasTicket[q] == tr(t).hasTicket[q]
ensures tr(t').task_no[p] > 0 && tr(t').task_no[p] == tr(t').done[p] 
{
    if tr(t).done[p] == tr(t).task_no[p]
    {
        t' := t;
        return;
    }
    
    t' := t;
    while true
        invariant t <= t'
        invariant tr(t').serving == tr(t).serving
        invariant tr(t').cs[p] == tr(t).cs[p] == Critical
        invariant tr(t').hasTicket[p] == tr(t).hasTicket[p]
        invariant forall q :: q in P && tr(t).cs[q] == Waiting ==> tr(t').cs[q] == Waiting && tr(t').hasTicket[q] == tr(t).hasTicket[q]
        invariant tr(t').task_no[p] > 0 && tr(t').done[p] <= tr(t').task_no[p]
        decreases tr(t').task_no[p] - tr(t').done[p]
    {       
        if tr(t').done[p] == tr(t').task_no[p] 
        {
            return;
        }

        assert tr(t').done[p] < tr(t').task_no[p];
        var k := GetNextStepOfServedProcess(tr, sched, p, t');
        assert tr(k).done[p] < tr(k).task_no[p] && 0 < tr(k).task_no[p];        
        assert tr(k).cs[p] == Critical;

        assert !RequestP(tr(k), p, tr(k + 1));
        assert !EnterP(tr(k), p, tr(k + 1));    
        assert !LeaveP(tr(k), p, tr(k + 1));        
        assert !CreateNewTasksP(tr(k), p, tr(k + 1));
        assert NextP(tr(k), sched(k), tr(k + 1));
        assert FinishOneTaskP(tr(k), p, tr(k + 1));

        t' := k + 1;
    }
    
}

lemma ServedProcessEventuallyFinishAllTasks(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P
requires tr(t).cs[p] != Idle && tr(t).hasTicket[p] == tr(t).serving
ensures t <= t' && tr(t').cs[p] == Critical 
ensures tr(t').hasTicket[p] == tr(t').serving
ensures tr(t').task_no[p] > 0 && tr(t').task_no[p] == tr(t').done[p]
ensures tr(t).serving == tr(t').serving 
ensures forall q :: (q in P && tr(t).cs[q] == Waiting && q != p) 
            ==> tr(t').cs[q] == Waiting && tr(t').hasTicket[q] == tr(t).hasTicket[q]
{        
    var k0 := ServedProcessEventuallyCreatesNewTasks(tr, sched, p, t);             
    t':= EventuallyFinishAllTasksAfterCreatingTasks(tr, sched, p, k0);
}

lemma EventuallyLeavesTheCriticalAreaAfterFinishingAllTasks(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P
requires tr(t).cs[p] == Critical && tr(t).hasTicket[p] == tr(t).serving 
requires tr(t).task_no[p] == tr(t).done[p] && tr(t).task_no[p] > 0
ensures t <= t' 
ensures tr(t').serving == tr(t).serving + 1
ensures forall q :: q in P && tr(t).cs[q] == Waiting ==> tr(t').cs[q] == Waiting && tr(t').hasTicket[q] == tr(t).hasTicket[q]
ensures tr(t').task_no[p] == 0 && tr(t').done[p] == 0
ensures tr(t').hasTicket[p] == 0 && tr(t').cs[p] == Idle
{
    assert Valid(tr(t));
    assert tr(t).done[p] == tr(t).task_no[p] && tr(t).task_no[p] > 0;
    var k := GetNextStepOfServedProcess(tr, sched, p, t);    
    assert t <= k;
    assert tr(k).task_no[p] == tr(k).done[p] == tr(t).task_no[p];
    assert tr(k).task_no[p] > 0;
    assert tr(k).cs[p] == tr(t).cs[p] == Critical;
    
    assert !RequestP(tr(k), p, tr(k + 1));
    assert !EnterP(tr(k), p, tr(k + 1));    
    assert !FinishOneTaskP(tr(k), p, tr(k + 1));
    assert !CreateNewTasksP(tr(k), p, tr(k + 1));
    assert NextP(tr(k), sched(k), tr(k + 1));
    assert LeaveP(tr(k), p, tr(k + 1));
        
    assert tr(k + 1).serving == tr(t).serving + 1;
    assert forall q :: q in P && tr(t).cs[q] == Waiting ==> tr(k + 1).cs[q] == Waiting && tr(k + 1).hasTicket[q] == tr(t).hasTicket[q];
    assert tr(k + 1).task_no[p] == 0 && tr(k + 1).done[p] == 0;
    assert tr(k + 1).hasTicket[p] == 0 && tr(k + 1).cs[p] == Idle;

    t' := k + 1;    
}

lemma ServedProcessEventuallyLeavesCriticalArea(tr: Trace, sched: Schedule, p: Process, t: nat) returns (t': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P
requires tr(t).cs[p] != Idle && tr(t).hasTicket[p] == tr(t).serving
ensures t <= t' && tr(t').cs[p] != Critical 
ensures tr(t).serving < tr(t').serving 
ensures forall q :: (q in P && tr(t).cs[q] == Waiting && q != p) 
            ==> tr(t').cs[q] == Waiting && tr(t').hasTicket[q] == tr(t).hasTicket[q]
{        
    var k0 := ServedProcessEventuallyFinishAllTasks(tr, sched, p, t);             
    t' := EventuallyLeavesTheCriticalAreaAfterFinishingAllTasks(tr, sched, p, k0); 
}

function CurrentlyServedProcess(s: TSState): Process
requires Valid(s)
requires exists p | p in P :: s.cs[p] == Waiting
{
    assert TicketIsInUse(s, s.serving);
    var q :| q in P && s.cs[q] != Idle && s.hasTicket[q] == s.serving;
    q
}

lemma Liveness(tr: Trace, sched: Schedule, p: Process, n: nat) returns (n': nat)
requires IsFairSchedule(sched) && IsTrace(tr, sched) && p in P
requires tr(n).cs[p] == Waiting
ensures n <= n' && tr(n').cs[p] == Critical
{
    n' := n;
    while true
        invariant n <= n' && tr(n').cs[p] == Waiting
        decreases tr(n').hasTicket[p] - tr(n').serving
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