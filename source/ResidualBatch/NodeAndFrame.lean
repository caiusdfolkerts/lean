module
prelude
public import PackedGraphInputs
public import RawFrameSupportCore

/-! Common node and relabeling obligations with no global cell catalogue. -/
@[expose] public section
namespace Papers.RationalityTen.ResidualBatch
open FiniteChecks PackedGraphCertificate RawGraphSemanticCertificate

inductive FrameWitness where
  | identity
  | permutation (forward inverse : Nat)

def allFin {n : Nat} (test : Fin n → Bool) : Bool := (List.finRange n).all test

theorem allFin_at {n : Nat} (test : Fin n → Bool) (ok : allFin test = true)
    (i : Fin n) : test i = true :=
  List.all_eq_true.mp ok i (List.mem_finRange i)

def frameCheck (D : RawData) (f : Fin D.g) : FrameWitness → Bool
  | .identity => allFin fun c => decide (D.maps f c = c)
  | .permutation u v => frameHeadTest D.data.requiredEdges u v &&
      allFin (frameCellTest D.data.cells u (D.maps f) (D.inverseMaps f))

theorem supported_of_frameCheck (D : RawData) (f : Fin D.g) (w : FrameWitness)
    (ok : frameCheck D f w = true) : RawFrameSupport.Supported D f := by
  cases w with
  | identity =>
    exact RawFrameSupport.of_identity D f fun c => of_decide_eq_true (allFin_at _ ok c)
  | permutation u v =>
    obtain ⟨head, cells⟩ := Bool.and_eq_true_iff.mp ok
    exact Or.inr ⟨u, v, D.inverseMaps f,
      frameFacts_of_checks D.data.cells D.data.requiredEdges u v _ _ head (allFin_at _ cells)⟩

/-- Both problem constructors retain the same computational fields, including
`List.range k` as the selected kind keys. Their correctness fields are proofs. -/
theorem metadata_problem_eq (D : RawData) (h : D.metadataCheck = true) :
    D.inputs.problem (D.valid_of_metadata h) = D.problem h := rfl

/-- The same raw node predicate used by `GraphCaseCertificate.Core`, with the
semantic-cache problem reconstructed from independently checked metadata. -/
theorem rawNodesOfBatch {m : Nat} [NeZero m] (records : Fin m → RawData)
    (metadata : ∀ i, (records i).metadataCheck = true)
    (nodes : Interval (batchNodeTest records metadata) 0 m) (j : Fin m) :
    ∀ i, RawGraphConditionedGrowth.nodeCheck
      ((records j).inputs.problem ((records j).valid_of_metadata (metadata j)))
      (records j).maps (records j).leaf (records j).nodes i = true := by
  rw [metadata_problem_eq (records j) (metadata j)]
  exact batch_node_checks records metadata nodes j

end Papers.RationalityTen.ResidualBatch
