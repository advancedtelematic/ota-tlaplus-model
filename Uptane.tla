---- MODULE Uptane -------------------------------------------------------------
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS Nothing

VARIABLES desired_target, acquired_target, root_metas, targets_meta
--------------------------------------------------------------------------------
Versions == (1..64)

Thresholds == (1..3)

Keys == {"k1", "k2"}

Targets == (1..8)
ChooseableTargets == Targets \union {Nothing}
--------------------------------------------------------------------------------
Last(s) ==
  LET len == Len(s)
  IN IF len = 1
     THEN Head(s)
     ELSE Head(SubSeq(s, len, len))
--------------------------------------------------------------------------------
Role ==
  [keys      : Keys,
   threshold : Thresholds]

TargetsMeta ==
  [version : Versions,
   targets : SUBSET Targets]

RootMeta ==
  [version      : Versions,
   targets_role : Role]
--------------------------------------------------------------------------------
TypeOk ==
  /\ desired_target  \in ChooseableTargets
  /\ acquired_target \in ChooseableTargets

  /\ \A i \in (1..Len(root_metas)) : Last(SubSeq(root_metas, 1, i)).version = i
  /\ targets_meta \in TargetsMeta \union {Nothing}
--------------------------------------------------------------------------------
SelectTarget ==
  /\ desired_target'  = CHOOSE t \in ChooseableTargets : TRUE
  /\ acquired_target' = Nothing
  /\ UNCHANGED << root_metas, targets_meta >>

DownloadTarget ==
  /\ desired_target   # Nothing
  /\ acquired_target' = desired_target
  /\ desired_target'  = Nothing
  /\ UNCHANGED << root_metas, targets_meta >>

UpdateRootMeta ==
  /\ LET new_root == CHOOSE r \in RootMeta : r.version = Last(root_metas).version + 1
     IN root_metas' = Append(root_metas, new_root)
  /\ UNCHANGED << desired_target, acquired_target, targets_meta >>

UpdateTargetsMeta ==
  /\ targets_meta' =
     IF targets_meta = Nothing
     THEN CHOOSE t \in TargetsMeta : t.version > 0
     ELSE CHOOSE t \in TargetsMeta : t.version > targets_meta.version
  /\ UNCHANGED << root_metas, desired_target, acquired_target >>
--------------------------------------------------------------------------------
TargetOk ==
  \/ acquired_target = Nothing
  \/ /\ acquired_target # Nothing
     (* A valid target must be present in the targets metadata. *)
     /\ acquired_target \in targets_meta.targets
--------------------------------------------------------------------------------
Inv ==
  /\ TypeOk
  /\ TargetOk

Init ==
  (* Root metadata must always start at 1 *)
  /\ root_metas = << CHOOSE r \in RootMeta : r.version = 1 >>

  /\ desired_target  = Nothing
  /\ acquired_target = Nothing
  /\ targets_meta    = Nothing

Next ==
  \/ UpdateRootMeta
  \/ UpdateTargetsMeta
  \/ SelectTarget
  \/ DownloadTarget
--------------------------------------------------------------------------------
vars == << desired_target, acquired_target, root_metas, targets_meta >>
Uptane == Init /\ [][Next]_vars
================================================================================
