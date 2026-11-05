module
prelude
public import PackedGraphCertificate
public import GraphGrowthInputs

@[expose] public section

/-!
# Packed certificates with semantic cache obligations

The packed record supplies exactly the same computational inputs as the
matrix checker. Validity may be established either by the original Boolean
metadata check or by restriction of an already verified global universe.
Consequently node certificates do not require one particular implementation
of the cache proof. Missing-row support and terminal distinctness remain
separate, explicit obligations at their respective uses.
-/

namespace Papers.RationalityTen.PackedGraphCertificate.RawData

open GraphGrowthInputs GraphGrowthConstraints FiniteChecks

def inputs (D : RawData) : Inputs D.n 1024 45 10 D.k where
  ridgeList := D.data.ridgeList
  compatible := D.data.literalCompatible
  kind := D.data.kind
  quota := D.data.quota
  candidates := D.data.candidateMasks
  incompatible := D.data.badMasks
  kinds := D.data.kindMasks
  vertexRows := D.data.vertexRows
  edges := D.data.edgeMasks
  missing := D.data.missingMasks
  edgeRows := D.data.edgeRows
  missingRows := D.data.missingRows
  requiredEdges := D.data.requiredEdges
  missingCount := D.data.missingCount
  minimumIncidence := D.data.minimumIncidence

theorem valid_of_metadata (D : RawData) (h : D.metadataCheck = true) :
    Valid D.inputs :=
  ofProblem_valid (D.problem h)

def nodeTestValid (D : RawData) (h : Valid D.inputs) (i : Nat) : Bool :=
  FastGeneralGraphReplay.nodeCheck (D.inputs.problem h) D.support
    D.maps D.bound D.base D.leaf D.nodes (Fin.ofNat D.t i)

def Supports (D : RawData) : Prop :=
  ∀ q : Fin 45, q ∈ D.support ∨ D.data.missingRows q = 0

theorem supports_of_metadata (D : RawData) (h : D.metadataCheck = true) :
    D.Supports := D.support_sound h

def leafTest (D : RawData) (i : Nat) : Bool :=
  decide ((D.leaf (Fin.ofNat D.l i)).Nodup)

theorem leaves_nodup_of_interval (D : RawData)
    (checked : Interval D.leafTest 0 D.l) (j : Fin D.l) : (D.leaf j).Nodup := by
  have h := checked j.val (Nat.zero_le _) j.isLt
  simpa only [leafTest, Fin.ofNat_val_eq_self, decide_eq_true_eq] using h

theorem node_checks_valid (D : RawData) (h : Valid D.inputs) (hs : D.Supports)
    (checked : Interval (D.nodeTestValid h) 0 D.t) (i : Fin D.t) :
    RawGraphConditionedGrowth.nodeCheck (D.inputs.problem h)
      D.maps D.leaf D.nodes i = true := by
  have hi := checked i.val (Nat.zero_le _) i.isLt
  have hnode : FastGeneralGraphReplay.nodeCheck (D.inputs.problem h) D.support
      D.maps D.bound D.base D.leaf D.nodes i = true := by
    simpa only [nodeTestValid, Fin.ofNat_val_eq_self] using hi
  exact FastGeneralGraphReplay.nodeCheck_sound (D.inputs.problem h) D.support hs
    D.maps D.bound D.base D.leaf D.nodes i hnode

#print axioms valid_of_metadata
#print axioms node_checks_valid

end Papers.RationalityTen.PackedGraphCertificate.RawData
