---- MODULE Uptane -------------------------------------------------------------
EXTENDS TLC, Naturals, FiniteSets

VARIABLES root
--------------------------------------------------------------------------------
Versions == (1..8)

Thresholds == (1..8)

Keys == {"k1", "k2"}

Roles == [keys : SUBSET Keys, threshold : Thresholds]

(* Each key can sign once and be eiter valid or not *)
Signatures == [key : Keys , valid : BOOLEAN]

TypeOk ==
    /\ root \in [version        : Versions,
                 expired        : BOOLEAN,
                 root_role      : Roles,
                 targets_role   : Roles,
                 snapshot_role  : Roles,
                 timestamp_role : Roles,
                 signatures     : SUBSET Signatures]

RoleOk ==
    (* Thresholds greater than zero *)
    /\ root.root_role.threshold      > 0
    /\ root.targets_role.threshold   > 0
    /\ root.snapshot_role.threshold  > 0
    /\ root.timestamp_role.threshold > 0

    (* Roles can't have a number of keys lower than their threshold *)
    /\ Cardinality(root.root_role.keys)      >= root.root_role.threshold
    /\ Cardinality(root.targets_role.keys)   >= root.targets_role.threshold
    /\ Cardinality(root.snapshot_role.keys)  >= root.snapshot_role.threshold
    /\ Cardinality(root.timestamp_role.keys) >= root.timestamp_role.threshold

Inv ==
    /\ TypeOk
    /\ RoleOk

--------------------------------------------------------------------------------
UpdateRoot ==
    (* Root must always increment by one *)
    (* TODO cross signing of roots *)
    /\ root' = [root EXCEPT !.version = @ + 1]
    (* Here to halt execution *)
    /\ root.version < 8

(* Dummy state to halt execution *)
Done ==
    /\ UNCHANGED << root >>
--------------------------------------------------------------------------------
Init ==
    /\ TypeOk
    (* Root always starts at version 1. This is the only restriction. *)
    /\ root = [version |-> 1]
    (* Signatures on the Root must only come from authorized keys *)
    /\ \A signature \in root.signatures : signature.key \in root.role_role.keys

Next ==
    \/ UpdateRoot
    \/ Done
--------------------------------------------------------------------------------
vars == << root >>
Uptane == Init /\ [][Next]_vars
================================================================================
