module
public import Papers.RealIncidenceCores
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.Push

@[expose] public section

noncomputable section

open Matrix
open scoped BigOperators

namespace Papers.RationalityTen

open SmallTripleCores

/-- All active points are distinct projective points, represented by nonzero vectors. -/
def IndependentProjectivePoints (S : Finset (Fin 8)) (p : Fin 8 → PlaneVector) : Prop :=
  (∀ i ∈ S, p i ≠ 0) ∧
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → LinearIndependent ℝ ![p i,p j]

/-- The actual zero set of a homogeneous line among the active labels. -/
noncomputable def lineSupport (S : Finset (Fin 8)) (p : Fin 8 → PlaneVector)
    (l : PlaneVector) : Finset (Fin 8) :=
  S.filter fun i => dotProduct l (p i) = 0

/-- Rich lines are the supports of actual joins of two distinct active points. -/
noncomputable def richLines (S : Finset (Fin 8)) (p : Fin 8 → PlaneVector) : Family :=
  (((S ×ˢ S).filter fun ij => ij.1 ≠ ij.2).image
    (fun ij => lineSupport S p (crossProduct (p ij.1) (p ij.2)))).filter
      fun T => 3 ≤ T.card

theorem mem_richLines_iff {S : Finset (Fin 8)} {p : Fin 8 → PlaneVector}
    {T : Triple} :
    T ∈ richLines S p ↔ 3 ≤ T.card ∧
      ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
        lineSupport S p (crossProduct (p i) (p j)) = T := by
  classical
  simp only [richLines, Finset.mem_filter, Finset.mem_image,
    Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨⟨i,j,⟨⟨hi,hj⟩,hij⟩,hT⟩,hcard⟩
    exact ⟨hcard,i,hi,j,hj,hij,hT⟩
  · rintro ⟨hcard,i,hi,j,hj,hij,hT⟩
    exact ⟨⟨i,j,⟨⟨hi,hj⟩,hij⟩,hT⟩,hcard⟩

theorem richLine_subset {S : Finset (Fin 8)} {p : Fin 8 → PlaneVector}
    {T : Triple} (hT : T ∈ richLines S p) : T ⊆ S := by
  classical
  obtain ⟨_,i,hi,j,hj,hij,rfl⟩ := mem_richLines_iff.mp hT
  exact Finset.filter_subset _ _

theorem richLine_exists_covector {S : Finset (Fin 8)} {p : Fin 8 → PlaneVector}
    (hp : IndependentProjectivePoints S p) {T : Triple}
    (hT : T ∈ richLines S p) :
    ∃ l : PlaneVector, l ≠ 0 ∧ lineSupport S p l = T := by
  obtain ⟨_,i,hi,j,hj,hij,hT⟩ := mem_richLines_iff.mp hT
  exact ⟨crossProduct (p i) (p j),
    crossProduct_ne_zero_iff_linearIndependent.mpr (hp.2 i hi j hj hij),hT⟩

noncomputable def richLineCovector {S : Finset (Fin 8)} {p : Fin 8 → PlaneVector}
    (hp : IndependentProjectivePoints S p)
    (T : {T : Triple // T ∈ richLines S p}) : PlaneVector :=
  Classical.choose (richLine_exists_covector hp T.2)

theorem richLineCovector_ne_zero {S : Finset (Fin 8)} {p : Fin 8 → PlaneVector}
    (hp : IndependentProjectivePoints S p)
    (T : {T : Triple // T ∈ richLines S p}) :
    richLineCovector hp T ≠ 0 :=
  (Classical.choose_spec (richLine_exists_covector hp T.2)).1

theorem richLineCovector_support {S : Finset (Fin 8)} {p : Fin 8 → PlaneVector}
    (hp : IndependentProjectivePoints S p)
    (T : {T : Triple // T ∈ richLines S p}) :
    lineSupport S p (richLineCovector hp T) = T.1 :=
  (Classical.choose_spec (richLine_exists_covector hp T.2)).2

theorem lineSupport_smul {S : Finset (Fin 8)} {p : Fin 8 → PlaneVector}
    (l : PlaneVector) {c : ℝ} (hc : c ≠ 0) :
    lineSupport S p (c • l) = lineSupport S p l := by
  classical
  ext i
  simp [lineSupport, smul_dotProduct, hc]

theorem richLineCovector_pair_independent {S : Finset (Fin 8)}
    {p : Fin 8 → PlaneVector} (hp : IndependentProjectivePoints S p)
    (T U : {T : Triple // T ∈ richLines S p}) (hTU : T ≠ U) :
    LinearIndependent ℝ ![richLineCovector hp T,richLineCovector hp U] := by
  by_contra h
  rw [LinearIndependent.pair_iff' (richLineCovector_ne_zero hp T)] at h
  push_neg at h
  obtain ⟨c,hc⟩ := h
  have hc0 : c ≠ 0 := by
    intro h0
    exact richLineCovector_ne_zero hp U (by simpa [h0] using hc.symm)
  apply hTU
  apply Subtype.ext
  calc
    T.1 = lineSupport S p (richLineCovector hp T) :=
      (richLineCovector_support hp T).symm
    _ = lineSupport S p (c • richLineCovector hp T) :=
      (lineSupport_smul _ hc0).symm
    _ = lineSupport S p (richLineCovector hp U) := by rw [hc]
    _ = U.1 := richLineCovector_support hp U

/-- The finite rich-line family carries its original, actual real realization. -/
noncomputable def richLines_realization {S : Finset (Fin 8)}
    {p : Fin 8 → PlaneVector} (hp : IndependentProjectivePoints S p) :
    RealProjectiveIncidence (richLines S p) where
  point := p
  line := richLineCovector hp
  point_independent i j hi hj hij := by
    obtain ⟨T,hT,hiT⟩ := hi
    obtain ⟨U,hU,hjU⟩ := hj
    exact hp.2 i (richLine_subset hT hiT) j (richLine_subset hU hjU) hij
  line_independent := richLineCovector_pair_independent hp
  incident T i hi := by
    have hi' : i ∈ lineSupport S p (richLineCovector hp T) := by
      rw [richLineCovector_support hp T]
      exact hi
    exact (Finset.mem_filter.mp hi').2

/-- Every actual configuration of at most eight distinct projective points has
a point on at most two rich lines. This includes collinear configurations. -/
theorem exists_point_on_at_most_two_rich_lines
    {S : Finset (Fin 8)} {p : Fin 8 → PlaneVector}
    (hS : S.Nonempty) (hp : IndependentProjectivePoints S p) :
    ∃ v ∈ S, degree (richLines S p) v ≤ 2 := by
  classical
  by_contra h
  have hdeg : ∀ v ∈ S, 3 ≤ degree (richLines S p) v := by
    intro v hv
    have hn : ¬ degree (richLines S p) v ≤ 2 := by
      intro hle
      exact h ⟨v,hv,hle⟩
    omega
  obtain ⟨v,hv⟩ := hS
  have hpos : 0 < ((richLines S p).filter fun T => v ∈ T).card := by
    have := hdeg v hv
    change 3 ≤ ((richLines S p).filter fun T => v ∈ T).card at this
    omega
  obtain ⟨T,hT⟩ := Finset.card_pos.mp hpos
  have hne : (richLines S p).Nonempty :=
    ⟨T,(Finset.mem_filter.mp hT).1⟩
  apply real_incidence_core_impossible (richLines S p) (richLines_realization hp) hne
  · intro U hU
    exact (mem_richLines_iff.mp hU).1
  · intro i hi
    obtain ⟨U,hU,hiU⟩ := hi
    exact hdeg i (richLine_subset hU hiU)

theorem cross_dot_eq_det (a b c : PlaneVector) :
    dotProduct (crossProduct a b) c = Matrix.det ![a,b,c] := by
  rw [dotProduct_comm, triple_product_eq_det]
  exact triple_det_cycle c a b

theorem left_mem_joinSupport {S : Finset (Fin 8)} {p : Fin 8 → PlaneVector}
    {i j : Fin 8} (hi : i ∈ S) :
    i ∈ lineSupport S p (crossProduct (p i) (p j)) := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨hi,by rw [dotProduct_comm]; exact dot_self_cross _ _⟩

theorem right_mem_joinSupport {S : Finset (Fin 8)} {p : Fin 8 → PlaneVector}
    {i j : Fin 8} (hj : j ∈ S) :
    j ∈ lineSupport S p (crossProduct (p i) (p j)) := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨hj,by rw [dotProduct_comm]; exact dot_cross_self _ _⟩

/-- Every dependent triple of distinct active labels belongs to a rich line. -/
theorem dependent_triple_on_rich_line
    {S : Finset (Fin 8)} {p : Fin 8 → PlaneVector}
    {i j k : Fin 8} (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hdet : Matrix.det ![p i,p j,p k] = 0) :
    ∃ T ∈ richLines S p, i ∈ T ∧ j ∈ T ∧ k ∈ T := by
  classical
  let T := lineSupport S p (crossProduct (p i) (p j))
  have hiT : i ∈ T := left_mem_joinSupport hi
  have hjT : j ∈ T := right_mem_joinSupport hj
  have hkT : k ∈ T :=
    Finset.mem_filter.mpr ⟨hk,by simpa [cross_dot_eq_det] using hdet⟩
  have hsub : ({i,j,k} : Finset (Fin 8)) ⊆ T := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  have hcard : 3 ≤ T.card := by
    have h := Finset.card_le_card hsub
    simpa [hij,hik,hjk] using h
  exact ⟨T,(mem_richLines_iff.mpr ⟨hcard,i,hi,j,hj,hij,rfl⟩),hiT,hjT,hkT⟩

/-- A rich line still has an independent defining pair after one point is deleted. -/
theorem richLine_pair_after_deletion
    {S : Finset (Fin 8)} {p : Fin 8 → PlaneVector}
    (hp : IndependentProjectivePoints S p) {T : Triple}
    (hT : T ∈ richLines S p) (v : Fin 8) :
    ∃ i ∈ T.erase v, ∃ j ∈ T.erase v, i ≠ j ∧
      LinearIndependent ℝ ![p i,p j] := by
  classical
  have hcard : 1 < (T.erase v).card := by
    have hTcard := (mem_richLines_iff.mp hT).1
    by_cases hv : v ∈ T
    · rw [Finset.card_erase_of_mem hv]
      omega
    · rw [Finset.erase_eq_of_notMem hv]
      omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hcard
  exact ⟨i,hi,j,hj,hij,hp.2 i
    (richLine_subset hT (Finset.mem_of_mem_erase hi)) j
    (richLine_subset hT (Finset.mem_of_mem_erase hj)) hij⟩

end Papers.RationalityTen
