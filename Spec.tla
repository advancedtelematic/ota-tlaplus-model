---- MODULE Spec -------------------------------------------------------

EXTENDS TLC

CONSTANTS Namespace, Commit, Device, Nothing

ASSUME NothingNotInCommit == Nothing \notin Commit

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

Bitbake == \E ns \in Namespace, c \in Commit :
  /\ ns \in namespaces
  /\ commits' = commits \cup {<< ns, c >>}
  /\ UNCHANGED << namespaces, devices, running, pending, staged >>

StartDevice == \E ns \in Namespace, c \in Commit, d \in Device :
  /\ ns          \in namespaces
  /\ << ns, c >> \in commits
  /\ << ns, d >> \notin devices
  /\ devices' = devices \cup {<< ns, d >>}
  /\ running' = running @@ << ns, d >> :> << ns, c >>
  /\ pending' = pending @@ << ns, d >> :> Nothing
  /\ staged'  = staged  @@ << ns, d >> :> Nothing
  /\ UNCHANGED << namespaces, commits >>

ScheduleUpdate == \E ns \in Namespace, c \in Commit, d \in Device :
  /\ ns          \in namespaces
  /\ << ns, c >> \in commits
  /\ << ns, d >> \in devices
  /\ c /= running[<< ns, d >>]
  /\ pending[<< ns, d >>] = Nothing
  /\ pending'   = [ pending EXCEPT ![<< ns, d >>] = << ns, c >> ]
  /\ UNCHANGED << namespaces, commits, devices, running, staged >>

PullUpdate == \E ns \in Namespace, d \in Device :
  /\ ns          \in namespaces
  /\ << ns, d >> \in devices
  /\ staged'  = IF pending[<< ns, d >>] = Nothing
                THEN staged
                ELSE [ staged EXCEPT ![<< ns, d >>] = pending[<< ns, d >>] ]
  /\ pending' = IF pending[<< ns, d >>] = Nothing
                THEN pending
                ELSE [ pending EXCEPT ![<< ns, d >>] = Nothing ]
  /\ UNCHANGED << namespaces, commits, devices, running >>

RebootDevice == \E ns \in Namespace, d \in Device :
  /\ ns          \in namespaces
  /\ << ns, d >> \in devices
  /\ running' = IF staged[<< ns, d >>] = Nothing
                THEN running
                ELSE [ running EXCEPT ![<< ns, d >>] = staged[<< ns, d >>] ]
  /\ staged'  = IF staged[<< ns, d >>] = Nothing
                THEN staged
                ELSE [ staged EXCEPT ![<< ns, d >>] = Nothing ]
  /\ UNCHANGED << namespaces, commits, devices, pending >>

------------------------------------------------------------------------

Next ==
  \/ CreateAccount
  \/ Bitbake
  \/ StartDevice
  \/ ScheduleUpdate
  \/ PullUpdate
  \/ RebootDevice

------------------------------------------------------------------------

DeviceCommitSameNamespace ==
  \A << ns , d >> \in DOMAIN running :
    /\ << ns , running[<< ns , d >>][2] >> \in commits
    /\ << ns , d >> \in devices
    /\ running[<< ns, d >>][1] = ns

Inv ==
  /\ TypeOK
  /\ DeviceCommitSameNamespace

vars == << commits, devices, running, pending, staged >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

========================================================================