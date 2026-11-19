module
prelude
public import GraphCoreCertificate

@[expose] public section

/-!
# Direct coverage of certified graph leaves

An exhaustive propositional proof may establish that every complete boundary
is one of the already certified leaves. This interface retains the exact
incidence interpretation and every leaf disposition, while allowing that
coverage proof to replace a growth DAG and its intermediate search states.
-/

namespace Papers.RationalityTen.GraphCaseCertificate

open PackedGraphCertificate

/-- The observable action of a word of already certified relabelings. -/
def rawApplyWord {n g : Nat} (maps : Fin g → Fin n → Fin n) :
    List (Fin g) → List (Fin n) → List (Fin n)
  | [], B => B
  | f :: rest, B => rawApplyWord maps rest (B.map (maps f))

theorem same_map {n m : Nat} (f : Fin n → Fin m) (S T : List (Fin n))
    (h : GrowthDAG.Same (SparseGrowthDAG.family S) (SparseGrowthDAG.family T)) :
    GrowthDAG.Same (SparseGrowthDAG.family (S.map f))
      (SparseGrowthDAG.family (T.map f)) := by
  apply SparseGrowthDAG.sameCheck_sound
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    apply (SparseGrowthDAG.has_true _ _).mpr
    apply List.mem_map.mpr
    refine ⟨a, ?_, rfl⟩
    exact (SparseGrowthDAG.has_true T a).mp
      ((h a).symm.trans ((SparseGrowthDAG.has_true S a).mpr ha))
  · apply List.all_eq_true.mpr
    intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    apply (SparseGrowthDAG.has_true _ _).mpr
    apply List.mem_map.mpr
    refine ⟨a, ?_, rfl⟩
    exact (SparseGrowthDAG.has_true S a).mp
      ((h a).trans ((SparseGrowthDAG.has_true T a).mpr ha))

theorem rawApplyWord_same {n g : Nat} (maps : Fin g → Fin n → Fin n)
    (word : List (Fin g)) (S T : List (Fin n))
    (h : GrowthDAG.Same (SparseGrowthDAG.family S) (SparseGrowthDAG.family T)) :
    GrowthDAG.Same (SparseGrowthDAG.family (rawApplyWord maps word S))
      (SparseGrowthDAG.family (rawApplyWord maps word T)) := by
  induction word generalizing S T with
  | nil => exact h
  | cons f rest ih => exact ih _ _ (same_map (maps f) S T h)

/-- A finite table may give an orbit representative and the checked word
which carries it back to an original certified leaf. -/
theorem complete_of_orbits (D : RawData) (valid : GraphGrowthInputs.Valid D.inputs)
    {l : Nat} (orbits : Fin l → List (Fin D.n)) (leaves : Fin l → Fin D.l)
    (words : Fin l → List (Fin D.g))
    (hwords : ∀ i, SparseGrowthDAG.sameCheck (D.leaf (leaves i))
      (rawApplyWord D.maps (words i) (orbits i)) = true)
    (hcoverage : ∀ B, GraphGrowthConstraints.Target (D.inputs.problem valid) B →
      ∃ i, GrowthDAG.Same (SparseGrowthDAG.family (orbits i))
        (SparseGrowthDAG.family B))
    (B : List (Fin D.n)) (hB : GraphGrowthConstraints.Target (D.inputs.problem valid) B) :
    ∃ j word, GrowthDAG.Same (SparseGrowthDAG.family (D.leaf j))
      (SparseGrowthDAG.family (rawApplyWord D.maps word B)) := by
  obtain ⟨i, hi⟩ := hcoverage B hB
  refine ⟨leaves i, words i, ?_⟩
  have first := SparseGrowthDAG.sameCheck_sound _ _ (hwords i)
  have second := rawApplyWord_same D.maps (words i) (orbits i) B hi
  exact fun c => (first c).trans (second c)

structure DirectCore (D : RawData) : Prop where
  matrix : MatrixGraphProblem.Checked D.data
  valid : GraphGrowthInputs.Valid D.inputs
  literal : RawGraphSemanticCertificate.LiteralFacts D.data
  leaf_nodup : ∀ j, (D.leaf j).Nodup
  frames : ∀ f, RawFrameSupport.Supported D f
  leaves_checked : ∃ certificates : Fin D.l → RawLeafCertificate.Certificate,
    ∀ j, RawLeafCertificate.check D.data.quota
      ((D.leaf j).map D.data.cells) (certificates j) = true
  complete : ∀ B : List (Fin D.n),
    GraphGrowthConstraints.Target (D.inputs.problem valid) B →
      ∃ j word, GrowthDAG.Same (SparseGrowthDAG.family (D.leaf j))
        (SparseGrowthDAG.family (rawApplyWord D.maps word B))

end Papers.RationalityTen.GraphCaseCertificate
