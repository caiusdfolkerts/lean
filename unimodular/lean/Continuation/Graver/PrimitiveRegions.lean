module

public import Unimodular
public import Unimodular.CycleTopology

/-!
# Regions of signed cone replacements

These statements concern the actual closed unions of a finite family of
full-dimensional polyhedral cones. A signed facet cycle with degree zero
has the same positive and negative region. The coefficient-restriction
lemmas isolate the algebraic step in the connected-interior argument of
Section 3.3 of the paper.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open scoped Topology BigOperators
open Set

namespace Unimodular.PrimitiveRegions

open CycleDegree

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (S : FullCones I V)

theorem cycle_add {c d : I → ℤ} (hc : S.IsCycle c) (hd : S.IsCycle d) :
    S.IsCycle (c + d) := by
  intro F
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hc F, hd F, add_zero]

theorem cycle_neg {c : I → ℤ} (hc : S.IsCycle c) :
    S.IsCycle (-c) := by
  intro F
  simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
    congrArg (fun z : ℤ => -z) (hc F)

theorem multiplicity_add (c d : I → ℤ) (x : V) :
    S.multiplicity (c + d) x = S.multiplicity c x + S.multiplicity d x := by
  unfold FullCones.multiplicity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x ∈ interior (S.cone i : Set V) <;> simp [hi]

theorem multiplicity_neg (c : I → ℤ) (x : V) :
    S.multiplicity (-c) x = -S.multiplicity c x := by
  unfold FullCones.multiplicity
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x ∈ interior (S.cone i : Set V) <;> simp [hi]

/-- The actual integer kernel of the facet equations and one degree row. -/
def zeroCycles (w : V) : AddSubgroup (I → ℤ) where
  carrier := {c | S.IsCycle c ∧ S.multiplicity c w = 0}
  zero_mem' := by
    constructor
    · intro F
      simp
    · simp [FullCones.multiplicity]
  add_mem' := by
    intro c d hc hd
    exact ⟨cycle_add S hc.1 hd.1, by rw [multiplicity_add S, hc.2, hd.2, add_zero]⟩
  neg_mem' := by
    intro c hc
    exact ⟨cycle_neg S hc.1, by rw [multiplicity_neg S, hc.2, neg_zero]⟩

@[simp] theorem mem_zeroCycles (w : V) (c : I → ℤ) :
    c ∈ zeroCycles S w ↔ S.IsCycle c ∧ S.multiplicity c w = 0 :=
  Iff.rfl

/-- An interior point of a positively weighted cone must also lie in a
negatively weighted cone when the signed covering multiplicity is zero. -/
theorem mem_selected_neg_of_multiplicity_zero (c : I → ℤ) {x : V}
    (hzero : S.multiplicity c x = 0)
    {i : I} (hi : 0 < c i) (hxi : x ∈ interior (S.cone i : Set V)) :
    x ∈ S.Selected (-c) := by
  by_contra hn
  have hnonneg : ∀ j : I,
      0 ≤ if x ∈ interior (S.cone j : Set V) then c j else 0 := by
    intro j
    split_ifs with hj
    · by_contra hneg
      apply hn
      refine ⟨j, ?_, interior_subset hj⟩
      exact neg_pos.mpr (lt_of_not_ge hneg)
    · exact le_rfl
  have hle := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  have hle' : c i ≤ S.multiplicity c x := by
    simpa only [if_pos hxi, FullCones.multiplicity] using hle
  rw [hzero] at hle'
  exact (not_le_of_gt hi) hle'

theorem selected_subset_neg (c : I → ℤ) (hc : S.IsCycle c)
    {w : V} (hw : S.Generic w) (hdegree : S.multiplicity c w = 0) :
    S.Selected c ⊆ S.Selected (-c) := by
  rintro x ⟨i, hi, hxi⟩
  have hgeneric :
      interior (S.cone i : Set V) ∩ {y | S.Generic y} ⊆ S.Selected (-c) := by
    rintro y ⟨hyi, hy⟩
    apply mem_selected_neg_of_multiplicity_zero S c
      ((S.multiplicity_eq c hc hy hw).trans hdegree) hi hyi
  have hinterior : interior (S.cone i : Set V) ⊆ S.Selected (-c) :=
    (S.generic_dense.open_subset_closure_inter isOpen_interior).trans
      ((closure_mono hgeneric).trans (S.selected_isClosed (-c)).closure_subset)
  exact closure_minimal hinterior (S.selected_isClosed (-c))
    (S.cone_subset_closure_interior i hxi)

/-- The positive and negative cone assemblies of a signed degree-zero cycle
cover exactly the same closed region. No feasibility or coefficient bound
is assumed. -/
theorem selected_eq_neg (c : I → ℤ) (hc : S.IsCycle c)
    {w : V} (hw : S.Generic w) (hdegree : S.multiplicity c w = 0) :
    S.Selected c = S.Selected (-c) := by
  apply Set.Subset.antisymm (selected_subset_neg S c hc hw hdegree)
  have hneg : S.multiplicity (-c) w = 0 := by
    rw [multiplicity_neg S, hdegree, neg_zero]
  simpa only [neg_neg] using selected_subset_neg S (-c) (cycle_neg S hc) hw hneg

/-- Keep precisely the coefficients indexed by a given subset. -/
def restrictCoeffs (c : I → ℤ) (s : Set I) : I → ℤ :=
  fun i => if i ∈ s then c i else 0

theorem restrictCoeffs_conformal (c : I → ℤ) (s : Set I) :
    Graver.ConformalLE (restrictCoeffs c s) c := by
  intro i
  by_cases hi : i ∈ s
  · simp only [restrictCoeffs, if_pos hi]
    exact ⟨le_rfl, le_rfl⟩
  · simp only [restrictCoeffs, if_neg hi, Int.toNat_zero, neg_zero]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- A nonempty coefficient restriction of a primitive kernel vector is
the whole vector whenever that restriction still satisfies the equations. -/
theorem primitive_restriction_eq {L : AddSubgroup (I → ℤ)} {c : I → ℤ}
    (hc : Graver.Primitive L c) (s : Set I)
    (hs : restrictCoeffs c s ∈ L)
    (hne : ∃ i ∈ s, c i ≠ 0) :
    restrictCoeffs c s = c := by
  apply hc.2.2 _ hs
  · obtain ⟨i, hi, hci⟩ := hne
    intro hzero
    have h := congrFun hzero i
    simp only [restrictCoeffs, if_pos hi, Pi.zero_apply] at h
    exact hci h
  · exact restrictCoeffs_conformal c s

end Unimodular.PrimitiveRegions

#print axioms Unimodular.PrimitiveRegions.selected_eq_neg
#print axioms Unimodular.PrimitiveRegions.primitive_restriction_eq
