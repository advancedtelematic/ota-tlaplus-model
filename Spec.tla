---- MODULE Spec ----------------------------------------------------

CONSTANTS Namespace, Commit, Device

VARIABLES namespaces, commits, devices, running

------------------------------------------------------------------------

TypeOK == /\ namespaces \subseteq Namespace
          /\ commits    \in [ namespaces -> SUBSET Commit ]
          /\ devices    \in [ namespaces -> SUBSET Device ]
          /\ running    \in [ namespaces -> SUBSET (Device \X Commit) ]

Init == /\ namespaces = {}
        /\ commits    = [ ns \in namespaces |-> {} ]
        /\ devices    = [ ns \in namespaces |-> {} ]
        /\ running    = [ ns \in namespaces |-> {} ]

------------------------------------------------------------------------

Empty(r, x)  == [ y \in DOMAIN r \cup {x} |-> IF x = y THEN {} ELSE r[y] ]

Add(r, f, v) == [ x \in DOMAIN r |-> IF x = f THEN r[x] \cup v ELSE r[x] ]

DomainRel(r)   == { p[1] : p \in r }
CodomainRel(r) == { p[2] : p \in r }

TotalRelation(r, s) == DomainRel(r) = s

------------------------------------------------------------------------

CreateAccount(ns) == /\ namespaces' = namespaces \cup {ns}
                     /\ commits'    = Empty(commits, ns)
                     /\ devices'    = Empty(devices, ns)
                     /\ running'    = Empty(running, ns)

Bitbake(ns, c) == /\ commits' = Add(commits, ns, {c})
                  /\ UNCHANGED namespaces
                  /\ UNCHANGED devices
                  /\ UNCHANGED running

StartDevice(ns, c, d) == /\ ns \in namespaces
                         /\ c \in commits[ns]
                         /\ devices' = Add(devices, ns, {d})
                         /\ running' = Add(running, ns, {<<d, c>>})
                         /\ UNCHANGED namespaces
                         /\ UNCHANGED commits

Next == \E ns \in Namespace, c \in Commit, d \in Device : \/ CreateAccount(ns)
                                                          \/ Bitbake(ns, c)
                                                          \/ StartDevice(ns, c, d)

Inv == /\ TypeOK
       /\ \A ns \in namespaces : TotalRelation(running[ns], devices[ns])
       /\ \A ns \in namespaces : \A c \in CodomainRel(running[ns]) : c \in commits[ns]

========================================================================