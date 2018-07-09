---- MODULE Uptane -------------------------------------------------------------
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS Nothing, Hash

VARIABLES root, timestamp, snapshot
--------------------------------------------------------------------------------
Versions == (1..2)

Thresholds == (1..3)

Sizes == (1..2)

Keys == {"k1", "k2"}

Roles == [keys : SUBSET Keys, threshold : Thresholds]

(* Each key can sign once and be eiter valid or not *)
Signatures == [key : Keys , valid : BOOLEAN]
--------------------------------------------------------------------------------
TypeOk ==
    (* Root metadata *)
    /\ root \in [version        : Versions,
                 expired        : BOOLEAN,
                 root_role      : Roles,
                 targets_role   : Roles,
                 snapshot_role  : Roles,
                 timestamp_role : Roles,
                 signatures     : SUBSET Signatures]

    (* Timestamp metadata *)
    /\ timestamp \in [version          : Versions,
                      snapshot_hash    : Hash,
                      snapshot_size    : Sizes,
                      snapshot_version : Versions,
                      signatures       : SUBSET Signatures]

    (* Snapshot metadata *)
    /\ snapshot \in [version         : Versions,
                     targets_hash    : Hash,
                     targets_size    : Sizes,
                     targets_version : Versions,
                     signatures       : SUBSET Signatures]

RootOk ==
    /\ root.version > 0

    (* Thresholds are greater than zero *)
    /\ root.root_role.threshold      > 0
    /\ root.targets_role.threshold   > 0
    /\ root.snapshot_role.threshold  > 0
    /\ root.timestamp_role.threshold > 0

    (* Roles can't have a number of keys lower than their threshold *)
    /\ Cardinality(root.root_role.keys)      >= root.root_role.threshold
    /\ Cardinality(root.targets_role.keys)   >= root.targets_role.threshold
    /\ Cardinality(root.snapshot_role.keys)  >= root.snapshot_role.threshold
    /\ Cardinality(root.timestamp_role.keys) >= root.timestamp_role.threshold

TimestampOk ==
    /\ timestamp.version > 0
    /\ Cardinality(\A signature \in timestamp.signatures : signature \in root.timestamp_rool.keys /\ signature.valid) >= root.timestamp_role.threshold

SnapshotOk ==
    /\ snapshot.version > 0
    /\ Cardinality(\A signature \in snapshot.signatures : signature \in root.snapshot_rool.keys /\ signature.valid) >= root.snapshot_role.threshold

RolesOk ==
    /\ RootOk
    /\ TimestampOk
    /\ SnapshotOk

Inv ==
    /\ TypeOk
    /\ RolesOk
--------------------------------------------------------------------------------
UpdateRoot ==
    (* Root must always increment by one *)
    /\ root' = [root EXCEPT !.version = @ + 1]
    (* root' has a threshold of signatures from root' *)
    /\ Cardinality(\A signature \in root'.signatures : signature \in root'.root_rool.keys /\ signature.valid) >= root'.root_role.threshold
    (* root' has a threshold of signatures from root *)
    /\ Cardinality(\A signature \in root'.signatures : signature \in root.root_role.keys /\ signature.value) >= root.root_role.threshold
    (* Dummy condition to halt execution *)
    /\ root.version < 4
    /\ UNCHANGED << timestamp, snapshot >>

UpdateTimestamp ==
    (* Can't update timestamp if root is expired *)
    (* TODO this might not need to be true. We could update with expired root since that would tighten down the possible future states *)
    /\ ~ root.expired
    (* If we have no timestamp, accept whatever, otherwise restrictions apply *)
    /\ timestamp' = IF timestamp = Nothing
                    THEN timestamp
                    ELSE LET ts == CHOOSE t \in timestamp : t.version > timestamp.version IN
                         [timestamp EXCEPT !.version = ts]
    (* Dummy condition to halt execution *)
    /\ timestamp.version < 4
    /\ UNCHANGED << root, snapshot >>

UpdateSnapshot ==
    (* Can't update timestamp if root is expired *)
    (* TODO these might not need to be true. We could update with expired metadata since that would tighten down the possible future states *)
    /\ ~ root.expired
    /\ ~ timestamp.expired

    (* Dummy condition to halt execution *)
    /\ snapshot.version < 4
    /\ UNCHANGED << root, timestamp >>

DownloadTarget ==
    (* All metadata must be present *)
    /\ root # Nothing
    /\ timestamp # Nothing

    (* All metadata must not be expired *)
    /\ ~ root.expired
    /\ ~ timestamp.expired
    
    (* Downloading at target does not change the metadata *)
    /\ UNCHANGED << root, timestamp, snapshot >>

(* Dummy state to halt execution *)
Done ==
    /\ UNCHANGED << root, timestamp, snapshot >>
--------------------------------------------------------------------------------
Init ==
    /\ TypeOk
    /\ RolesOk

    (* Root always starts at version 1. This is the only restriction. *)
    /\ root = [version |-> 1]
    (* Signatures on the initial root must only come from authorized keys and be valid *)
    /\ \A signature \in root.signatures : signature.key \in root.role_role.keys /\ signature.valid
    (* Root signatures greater than or equal to threshold *)
    /\ Cardinality(root.signatures) >= root.root_role.thresohold
    
    /\ timestamp = Nothing
    /\ snapshot  = Nothing
    
Next ==
    \/ UpdateRoot
    \/ UpdateTimestamp
    \/ UpdateSnapshot
    \/ DownloadTarget
    \/ Done
--------------------------------------------------------------------------------
vars == << root, timestamp, snapshot >>
Uptane == Init /\ [][Next]_vars
================================================================================
