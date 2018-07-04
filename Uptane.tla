---- MODULE Uptane -------------------------------------------------------------
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS Keys, Thresholds

VARIABLES root
--------------------------------------------------------------------------------
Roles == [ keys : SUBSET Keys, threshold : Thresholds]

Versions == (1..256)

TypeOk ==
    /\ root \in [version        : Versions,
                 expired        : BOOLEAN,
                 root_role      : Roles,
                 targets_role   : Roles,
                 snapshot_role  : Roles,
                 timestamp_role : Roles]

(* Roles can't have a number of keys lower than their threshold *)
RoleOk ==
    /\ root.root_role.threshold > 0
    /\ Cardinality(root.root_role.keys) <= root.root_role.threshold

Inv ==
    /\ TypeOk
    /\ RoleOk

--------------------------------------------------------------------------------
UpdateRoot ==
    /\ [root EXCEPT !.version = root.version + 1]
--------------------------------------------------------------------------------
Init ==
    (* Root always starts at version 1. It may be expired. *)
    /\ root = [version |-> 1]

Next ==
    \/ UpdateRoot
--------------------------------------------------------------------------------
vars == << root >>
Uptane == Init /\ [][Next]_vars
================================================================================
