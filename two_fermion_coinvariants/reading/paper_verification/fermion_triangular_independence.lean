module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# The triangular test-map independence argument

The test maps kill the actual relation submodule. Their off-diagonal entries
vanish in the creator direction, while their diagonal images are linearly
independent polynomial boxes. Strong induction on the integer weight proves
independence of all proposed classes in the actual quotient.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators

variable {K W N J : Type*} [Ring K] [AddCommGroup W] [AddCommGroup N]
    [Module K W] [Module K N] [Fintype J]

/-- Triangular maps into any coefficient module separate the proposed quotient
classes once the images of each diagonal block are linearly independent. -/
theorem linearIndependent_quotient_of_triangular_test_maps
    (D : J → Type*) [∀ j, Fintype (D j)]
    (I : Submodule K W) (v : (j : J) → D j → W)
    (test : J → W →ₗ[K] N) (weight : J → ℕ)
    (hkill : ∀ j, I ≤ (test j).ker)
    (htri : ∀ j t, j ≠ t → weight j ≤ weight t → ∀ e, test j (v t e) = 0)
    (hdiag : ∀ j, LinearIndependent K (fun e ↦ test j (v j e))) :
    LinearIndependent K (fun p : Sigma D ↦ I.mkQ (v p.1 p.2)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hrel : (∑ p : Sigma D, c p • v p.1 p.2) ∈ I := by
    apply (Submodule.Quotient.mk_eq_zero I).mp
    change I.mkQ (∑ p : Sigma D, c p • v p.1 p.2) = 0
    simpa only [map_sum, map_smul] using hc
  have htest (j : J) : (∑ t : J, ∑ e : D t, c ⟨t, e⟩ • test j (v t e)) = 0 := by
    have h := hkill j hrel
    change test j (∑ p : Sigma D, c p • v p.1 p.2) = 0 at h
    simpa only [map_sum, map_smul, Fintype.sum_sigma] using h
  have hblock : ∀ m : ℕ, ∀ j : J, weight j = m → ∀ e : D j, c ⟨j, e⟩ = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hj
      have hsum : (∑ e : D j, c ⟨j, e⟩ • test j (v j e)) = 0 := by
        have hother (t : J) (ht : t ≠ j) :
            (∑ e : D t, c ⟨t, e⟩ • test j (v t e)) = 0 := by
          apply Finset.sum_eq_zero
          intro e _
          by_cases hlow : weight t < m
          · rw [ih (weight t) hlow t rfl e, zero_smul]
          · rw [htri j t (Ne.symm ht) (by rw [hj]; exact Nat.le_of_not_gt hlow) e,
              smul_zero]
        have hreduce :
            (∑ t : J, ∑ e : D t, c ⟨t, e⟩ • test j (v t e)) =
              ∑ e : D j, c ⟨j, e⟩ • test j (v j e) := by
          apply Finset.sum_eq_single j
          · intro t _ ht
            exact hother t ht
          · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
        rw [← hreduce]
        exact htest j
      exact Fintype.linearIndependent_iff.mp (hdiag j) (fun e ↦ c ⟨j, e⟩) hsum
  intro p
  exact hblock (weight p.1) p.1 rfl p.2

/-- The same argument for a specified quotient map, so its conclusion refers
exactly to the residue classes in that quotient. -/
theorem linearIndependent_map_of_triangular_test_maps
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (q : W →ₗ[K] Q) (D : J → Type*) [∀ j, Fintype (D j)]
    (v : (j : J) → D j → W) (test : J → W →ₗ[K] N) (weight : J → ℕ)
    (hkill : ∀ j, q.ker ≤ (test j).ker)
    (htri : ∀ j t, j ≠ t → weight j ≤ weight t → ∀ e, test j (v t e) = 0)
    (hdiag : ∀ j, LinearIndependent K (fun e ↦ test j (v j e))) :
    LinearIndependent K (fun p : Sigma D ↦ q (v p.1 p.2)) := by
  have h := linearIndependent_quotient_of_triangular_test_maps D q.ker v test weight
    hkill htri hdiag
  have hm := h.map' (q.ker.liftQ q le_rfl)
    (Submodule.ker_liftQ_eq_bot q.ker q le_rfl le_rfl)
  change LinearIndependent K (fun p : Sigma D ↦ q (v p.1 p.2)) at hm
  exact hm

end PaperVerification.Fermion
