---- MODULE Spec -------------------------------------------------------

EXTENDS TLC

CONSTANTS Namespace, Commit, Device

Nothing == CHOOSE c : c \notin Commit

VARIABLES namespaces, commits, devices, running, pending, staged

------------------------------------------------------------------------

TypeOK ==
  /\ namespaces \subseteq Namespace
  /\ commits    \subseteq namespaces \X Commit
  /\ devices    \subseteq namespaces \X Device
  /\ running    \in [ devices -> commits ]
  /\ pending    \in [ devices -> commits \cup {Nothing} ]
  /\ staged     \in [ devices -> commits \cup {Nothing} ]

Init ==
  /\ namespaces = {}
  /\ commits    = {}
  /\ devices    = {}
  /\ running    = [ d \in {} |-> {} ]
  /\ pending    = [ d \in {} |-> {} ]
  /\ staged     = [ d \in {} |-> {} ]

------------------------------------------------------------------------

CreateAccount == \E ns \in Namespace :
  /\ ns \notin namespaces
  /\ namespaces' = namespaces \cup {ns}
  /\ UNCHANGED << commits, devices, running, pending, staged >>

Bitbake(ns) == \E c \in Commit :
  /\ ns \in namespaces
  /\ commits' = commits \cup {<< ns, c >>}
  /\ UNCHANGED << namespaces, devices, running, pending, staged >>

StartDevice(ns, c) == \E d \in Device :
  /\ ns          \in namespaces
  /\ << ns, c >> \in commits
  /\ << ns, d >> \notin devices
  /\ devices' = devices \cup {<< ns, d >>}
  /\ running' = running @@ << ns, d >> :> << ns, c >>
  /\ pending' = pending @@ << ns, d >> :> Nothing
  /\ staged'  = staged  @@ << ns, d >> :> Nothing
  /\ UNCHANGED << namespaces, commits >>

ScheduleUpdate(ns, c, d) ==
  /\ ns          \in namespaces
  /\ << ns, c >> \in commits
  /\ << ns, d >> \in devices
  /\ c /= running[<< ns, d >>]
  /\ pending[<< ns, d >>] = Nothing
  /\ pending' = [ pending EXCEPT ![<< ns, d >>] = << ns, c >> ]
  /\ UNCHANGED << namespaces, commits, devices, running, staged >>

PullUpdate(ns, d) ==
  /\ ns          \in namespaces
  /\ << ns, d >> \in devices
  /\ LET p == pending[<< ns, d >>] IN
     staged'  = IF p = Nothing
                THEN staged
                ELSE [ staged EXCEPT ![<< ns, d >>] = p ]
  /\ pending' = IF pending[<< ns, d >>] = Nothing
                THEN pending
                ELSE [ pending EXCEPT ![<< ns, d >>] = Nothing ]
  /\ UNCHANGED << namespaces, commits, devices, running >>

RebootDevice(ns, d) ==
  LET s == staged[<< ns, d >>] IN
  /\ ns          \in namespaces
  /\ << ns, d >> \in devices
  /\ running' = IF s = Nothing
                THEN running
                ELSE [ running EXCEPT ![<< ns, d >>] = s ]
  /\ staged'  = IF s = Nothing
                THEN staged
                ELSE [ staged EXCEPT ![<< ns, d >>] = Nothing ]
  /\ UNCHANGED << namespaces, commits, devices, pending >>

OstreeAdminStatus(ns, d) == \E c \in Commit, pc \in Commit \cup {Nothing} :
  /\ ns          \in namespaces
  /\ << ns, d >> \in devices
  /\ running[<< ns, d >>] = << ns, c >>
  /\ pending[<< ns, d >>] = pc
  /\ UNCHANGED << namespaces, commits, devices, pending, running, staged >>

------------------------------------------------------------------------

Next ==
  \/ CreateAccount
  \/ (\E ns \in Namespace                             : Bitbake(ns))
  \/ (\E ns \in Namespace, c \in Commit               : StartDevice(ns, c))
  \/ (\E ns \in Namespace, c \in Commit, d \in Device : ScheduleUpdate(ns, c, d))
  \/ (\E ns \in Namespace, d \in Device               : PullUpdate(ns, d))
  \/ (\E ns \in Namespace, d \in Device               : RebootDevice(ns, d))
  \/ (\E ns \in Namespace, d \in Device               : OstreeAdminStatus(ns, d))

------------------------------------------------------------------------

RunningOK ==
  \A << ns , d >> \in DOMAIN running : \E c \in Commit :
    running[<< ns, d >>] = << ns, c >>

PendingOK ==
  \A << ns , d >> \in DOMAIN pending : \E c \in Commit :
    \/ pending[<< ns, d >>] = << ns, c >>
    \/ pending[<< ns, d >>] = Nothing

StagedOK ==
  \A << ns , d >> \in DOMAIN staged : \E c \in Commit :
    \/ staged[<< ns, d >>] = << ns, c >>
    \/ staged[<< ns, d >>] = Nothing

Inv ==
  /\ TypeOK
  /\ RunningOK
  /\ PendingOK
  /\ StagedOK

vars == << namespaces, commits, devices, running, pending, staged >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

========================================================================