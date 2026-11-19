module

public import Continuation.CycleBounds.NoncrossingWords
public import Mathlib.Data.List.Chain
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-! # The component count is bounded by the actual tangent dimension

The test-path lemma constructs independent tangent directions. It requires only
successive incidence evaluations, and consequently avoids assuming a formula
for graph rank or connected-component dimension.
-/

noncomputable section
open scoped BigOperators
namespace Unimodular.CycleBounds
attribute [local instance] Classical.propDecidable

variable {α W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Successive labels can be tested by an actual linear functional, with the
usual incidence values on a family of component directions. -/
def IncidenceTest (f : α → W) (a b : α) : Prop :=
  ∃ ℓ : W →ₗ[ℝ] ℝ, ∀ i,
    ℓ (f i) = (if i = a then 1 else 0) - (if i = b then 1 else 0)

/-- Along an incidence path, all component directions except one are independent.
This statement permits arbitrary repetitions in the path. -/
theorem independent_of_incidence_path (f : α → W) (a : α) (w : List α)
    (hpath : (a :: w).IsChain (IncidenceTest f)) :
    LinearIndependent ℝ (fun i : ((a :: w).toFinset.erase a) ↦ f i.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let T := (a :: w).toFinset.erase a
  let c : α → ℝ := fun x ↦ if hx : x ∈ T then g ⟨x, hx⟩ else 0
  have hsum (x : α) :
      (∑ j : T, g j * (if j.val = x then (1 : ℝ) else 0)) = c x := by
    by_cases hx : x ∈ T
    · rw [Finset.sum_eq_single ⟨x, hx⟩]
      · simp [c, hx]
      · intro j _ hj
        have hjx : j.val ≠ x := by
          intro heq
          exact hj (Subtype.ext heq)
        simp [hjx]
      · simp
    · have hzero : ∀ j : T, j.val ≠ x := by
        intro j heq
        exact hx (heq ▸ j.property)
      simp [hzero, c, hx]
  have hchain : (a :: w).IsChain (fun x y ↦ c x = c y) := by
    apply hpath.imp
    intro x y hxy
    obtain ⟨ℓ, hℓ⟩ := hxy
    have hh := congrArg ℓ hg
    simp only [map_sum, map_smul, map_zero, smul_eq_mul, hℓ, mul_sub,
      Finset.sum_sub_distrib] at hh
    rw [hsum, hsum] at hh
    exact sub_eq_zero.mp hh
  have hc : c i.val = c a := by
    have himem : i.val ∈ a :: w := List.mem_toFinset.mp (Finset.mem_of_mem_erase i.property)
    exact (hchain.induction (fun x ↦ c a = c x) (a :: w)
      (fun _ _ hxy hp ↦ hp.trans hxy) (fun _ ↦ rfl) i.val himem).symm
  have hiT : i.val ∈ T := i.property
  have haT : a ∉ T := by simp [T]
  simpa only [c, dif_pos hiT, dif_neg haT] using hc

/-- The actual linear-space dimension bounds the number of distinct path labels
minus one. -/
theorem card_sub_one_le_finrank_of_incidence_path [FiniteDimensional ℝ W]
    (f : α → W) (w : List α) (hpath : w.IsChain (IncidenceTest f)) (hne : w ≠ []) :
    w.toFinset.card - 1 ≤ Module.finrank ℝ W := by
  classical
  cases w with
  | nil => contradiction
  | cons a w =>
    have hli := independent_of_incidence_path f a w hpath
    have hd := hli.fintype_card_le_finrank
    have hd' : ((a :: w).toFinset.erase a).card ≤ Module.finrank ℝ W := by
      simpa only [Fintype.card_coe] using hd
    have ha : a ∈ (a :: w).toFinset := List.mem_toFinset.mpr List.mem_cons_self
    have hc := Finset.card_erase_add_one ha
    omega

/-- The potential-decrease bound takes values in the actual vector-space
 dimension, using an incidence path to justify every counted direction. -/
theorem cyclicCost_le_finrank_of_incidence_path [FiniteDimensional ℝ W]
    (f : α → W) (h : α → ℝ) (w : List α)
    (hnc : Noncrossing w) (hpath : w.IsChain (IncidenceTest f)) (hne : w ≠ []) :
    cyclicCost h w ≤ Module.finrank ℝ W :=
  (cyclicCost_le_card_sub_one h w hnc hne).trans
    (card_sub_one_le_finrank_of_incidence_path f w hpath hne)

#print axioms cyclicCost_le_finrank_of_incidence_path
end Unimodular.CycleBounds
