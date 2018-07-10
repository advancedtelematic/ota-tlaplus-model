---- MODULE Uptane -------------------------------------------------------------
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS Nothing, Hash

VARIABLES root, timestamp, snapshot, targets
--------------------------------------------------------------------------------
Versions == (1..16)

Thresholds == (1..3)

Sizes == (1..4)

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
     \cup {Nothing}

  (* Snapshot metadata *)
  /\ snapshot \in [version         : Versions,
                   size            : Sizes,
                   hash            : Hash,
                   targets_hash    : Hash,
                   targets_size    : Sizes,
                   targets_version : Versions,
                   signatures      : SUBSET Signatures]
     \cup {Nothing}

  (* Targets metadata *)
  /\ targets \in [version      : Versions,
                  size         : Sizes,
                  hash         : Hash,
                  targets_list : SUBSET Targets,
                  signatures   : SUBSET Signatures]
     \cup {Nothing}

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

  /\ Cardinality(root.signatures) > 0
  (* Signatures on the initial root must only come from authorized keys and be valid *)
  /\ LET valid_authorized_sigs ==
         {signature \in root.signatures :
          signature.key \in root.root_role.keys /\ signature.valid }
     IN Cardinality(valid_authorized_sigs) > root.root_role.threshold

TimestampOk ==
  \/ timestamp = Nothing
  \/
    /\ timestamp # Nothing
    /\ timestamp.version > 0
    /\ timestamp.snapshot_size > 0
    /\ timestamp.snapshot_version > 0

SnapshotOk ==
  \/ snapshot = Nothing
  \/
    /\ snapshot # Nothing
    /\ snapshot.version > 0
    /\ snapshot.size > 0
    /\ snapshot.targets_size > 0
    /\ snapshot.targets_version > 0

TargetsOk ==
  \/ targets = Nothing
  \/
    /\ targets # Nothing
    /\ targets.version > 0
    /\ targets.size > 0

RolesOk ==
  /\ RootOk
  /\ TimestampOk
  /\ SnapshotOk
  /\ TargetsOk

Inv ==
  /\ TypeOk
  /\ RolesOk
--------------------------------------------------------------------------------
UpdateRoot ==
  (* Root must always increment by one *)
  /\ root' = [root EXCEPT !.version = @ + 1]

  (* Cross signing of new root using old keys and new keys *)
  /\ LET valid_authorized_sigs ==
         {signature \in root'.signatures :
          signature.key \in root.root_role.keys /\ signature.valid }
     IN Cardinality(valid_authorized_sigs) > root.root_role.threshold
  /\ LET valid_authorized_sigs ==
         {signature \in root'.signatures :
          signature.key \in root'.root_role.keys /\ signature.valid }
     IN Cardinality(valid_authorized_sigs) > root'.root_role.threshold

  (* Dummy condition to halt execution *)
  /\ root.version < 16
  (* TODO rotate these *)
  /\ UNCHANGED << timestamp, snapshot, targets >>

UpdateTimestamp ==
  /\ timestamp # Nothing

  (* Can't update timestamp if root is expired *)
  (* TODO this might not need to be true. *)
  (* We could update with expired root since that would tighten down the possible future states *)
  /\ ~ root.expired

  /\ LET valid_authorized_sigs ==
         {signature \in timestamp.signatures :
          signature.key \in root.timestamp_role.keys /\ signature.valid }
     IN Cardinality(valid_authorized_sigs) > root.timestamp_role.threshold

  (* If we have no timestamp, accept whatever, otherwise restrictions apply *)
  /\ timestamp' =
     LET ts == CHOOSE t \in timestamp : t.version > timestamp.version
     IN [timestamp EXCEPT !.version = ts.version]
  (* Dummy condition to halt execution *)
  /\ timestamp.version < 16
  /\ UNCHANGED << root, snapshot, targets >>

UpdateSnapshot ==
  /\ timestamp # Nothing
  /\ snapshot  # Nothing

  (* Can't update timestamp if root is expired *)
  (* TODO these might not need to be true. *)
  (* We could update with expired metadata since that would tighten down the possible future states *)
  /\ ~ root.expired
  /\ ~ timestamp.expired

  /\ LET valid_authorized_sigs ==
         {signature \in snapshot.signatures :
          signature.key \in root.snapshot_role.keys /\ signature.valid }
     IN Cardinality(valid_authorized_sigs) > root.snapshot_role.threshold

  (* If we have no snapshot, accept whatever, otherwise restrictions apply *)
  /\ snapshot' =
     LET sn == CHOOSE s \in snapshot : s.version > snapshot.version
     IN [snapshot EXCEPT !.version = sn.version]

  /\ snapshot.hash = timestamp.snapshot_hash
  /\ snapshot.size <= timestamp.snapshot_size
  (* Dummy condition to halt execution *)
  /\ snapshot.version < 16
  /\ UNCHANGED << root, timestamp, targets >>

UpdateTargets ==
  /\ timestamp # Nothing
  /\ snapshot  # Nothing
  /\ targets   # Nothing

  (* Can't update timestamp if root is expired *)
  (* TODO these might not need to be true. *)
  (* We could update with expired metadata since that would tighten down the possible future states *)
  /\ ~ root.expired
  /\ ~ timestamp.expired
  /\ ~ snapshot.expired

  /\ Cardinality(\A signature \in targets.signatures :
                 signature.key \in root.targets_role.keys
                 /\ signature.valid) >= root.targets_role.threshold

  /\ targets' =
     LET ta == CHOOSE t \in targets : t.version > targets.version
     IN [targets EXCEPT !.version = ta.version]
  /\ targets.hash = snapshot.targets_hash
  /\ targets.size <= snapshot.targets_size

  (* Dummy condition to halt execution *)
  /\ targets.version < 16
  /\ UNCHANGED << root, timestamp, snapshot >>

DownloadTarget ==
  (* All metadata must be present *)
  /\ root      # Nothing
  /\ timestamp # Nothing
  /\ snapshot  # Nothing
  /\ targets   # Nothing

  (* All metadata must not be expired *)
  /\ ~ root.expired
  /\ ~ timestamp.expired
  /\ ~ snapshot.expired
  /\ ~ targets.expired

  (* Downloading at target does not change the metadata *)
  /\ UNCHANGED << root, timestamp, snapshot, targets >>

(* Dummy state to halt execution *)
Done ==
  /\ UNCHANGED << root, timestamp, snapshot, targets >>
--------------------------------------------------------------------------------
Init ==
  /\ timestamp = Nothing
  /\ snapshot  = Nothing
  /\ targets   = Nothing

  /\ TypeOk
  /\ RolesOk

  (* Root must start at version 1. *)
  /\ root.version = 1

Next ==
  \/ UpdateRoot
  \/ UpdateTimestamp
  \/ UpdateSnapshot
  \/ UpdateTargets
  \/ DownloadTarget
  \/ Done
--------------------------------------------------------------------------------
vars == << root, timestamp, snapshot, targets >>
Uptane == Init /\ [][Next]_vars
================================================================================
