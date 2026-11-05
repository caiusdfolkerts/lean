module

public import PaperVerification.FermionGaussPolynomial
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Completing a single mark in a largest exterior term

Only mixed annihilation equations are required after adding the missing colour.
The exact coefficient formula proves that no smaller-index creator contributes
to the completed largest word. This is the single-mark step of Section 4.3.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators
open Colex

section Coefficients

variable {R V J : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype J] [LinearOrder J]
variable (b : Module.Basis J R V)

/-- The actual coefficient transpose of creation is signed coordinate erasure. -/
theorem creation_coordinate (i : J) (T : Finset J) (w : ExteriorAlgebra R V) :
    b.ExteriorAlgebra.repr (creation (b i) w) T =
      if i ∈ T then TauCeti.ExteriorAlgebra.basisEraseSign i T •
        b.ExteriorAlgebra.repr w (T.erase i) else 0 := by
  have h : (b.ExteriorAlgebra.coord T).comp (creation (b i)) =
      if i ∈ T then TauCeti.ExteriorAlgebra.basisEraseSign i T •
        b.ExteriorAlgebra.coord (T.erase i) else 0 := by
    apply b.ExteriorAlgebra.ext
    intro U
    by_cases hiT : i ∈ T
    · rw [if_pos hiT]
      by_cases hiU : i ∈ U
      · have hU : U ≠ T.erase i := by
          intro hU
          rw [hU] at hiU
          exact Finset.notMem_erase i T hiU
        simp [LinearMap.comp_apply, creation_apply, TauCeti.ExteriorAlgebra.ι_mul_basis,
          hiU, Module.Basis.coord_apply, Finsupp.single_apply, hU, (Ne.symm hU)]
      · by_cases hUT : insert i U = T
        · have hU : U = T.erase i := by
            rw [← hUT, Finset.erase_insert hiU]
          simp [LinearMap.comp_apply, creation_apply, TauCeti.ExteriorAlgebra.ι_mul_basis,
            hiU, hUT, hU, hiT, Module.Basis.coord_apply, Finsupp.single_apply,
            Finset.insert_eq_of_mem hiT]
        · have hU : U ≠ T.erase i := by
            intro hU
            apply hUT
            rw [hU, Finset.insert_erase hiT]
          simp [LinearMap.comp_apply, creation_apply, TauCeti.ExteriorAlgebra.ι_mul_basis,
            hiU, Module.Basis.coord_apply, Finsupp.single_apply,
            hUT, (Ne.symm hUT), hU, (Ne.symm hU)]
    · rw [if_neg hiT]
      have hUT : insert i U ≠ T := by
        intro h
        exact hiT (h ▸ Finset.mem_insert_self i U)
      by_cases hiU : i ∈ U <;>
        simp [LinearMap.comp_apply, creation_apply, TauCeti.ExteriorAlgebra.ι_mul_basis,
          Module.Basis.coord_apply, Finsupp.single_apply, hiU, hUT, (Ne.symm hUT)]
  have hh := LinearMap.congr_fun h w
  by_cases hiT : i ∈ T
  · simpa only [if_pos hiT, LinearMap.comp_apply, LinearMap.smul_apply,
      Module.Basis.coord_apply] using hh
  · simpa only [if_neg hiT, LinearMap.comp_apply, LinearMap.zero_apply,
      Module.Basis.coord_apply] using hh

/-- A source obtained by replacing a smaller mark by a new larger one is
strictly above the selected colex maximum and hence has coefficient zero. -/
theorem replacement_coefficient_eq_zero
    (w : ExteriorAlgebra R V) (T : Finset J)
    (hmax : ∀ U : Finset J, b.ExteriorAlgebra.repr w U ≠ 0 → toColex U ≤ toColex T)
    (p j : J) (hp : p ∉ T) (hjp : j < p) :
    b.ExteriorAlgebra.repr w ((insert p T).erase j) = 0 := by
  by_contra h
  have hpU : p ∈ (insert p T).erase j :=
    Finset.mem_erase.mpr ⟨(ne_of_lt hjp).symm, Finset.mem_insert_self p T⟩
  obtain ⟨a, haT, haU, hpa⟩ := (Finset.Colex.toColex_le_toColex.mp (hmax _ h)) hpU hp
  have haj : a = j := by
    by_contra hne
    exact haU (Finset.mem_erase.mpr ⟨hne, Finset.mem_insert_of_mem haT⟩)
  exact (not_le_of_gt hjp) (haj ▸ hpa)

/-- Adding a missing mark at the top of the creator support has exactly the
claimed leading coefficient, with its genuine unit exterior sign. -/
theorem completion_coefficient
    (w : ExteriorAlgebra R V) (T : Finset J)
    (hmax : ∀ U : Finset J, b.ExteriorAlgebra.repr w U ≠ 0 → toColex U ≤ toColex T)
    (p : J) (hp : p ∉ T) (v : V)
    (hv : ∀ j : J, p < j → b.repr v j = 0) :
    b.ExteriorAlgebra.repr (creation v w) (insert p T) =
      b.repr v p • (TauCeti.ExteriorAlgebra.basisEraseSign p (insert p T) •
        b.ExteriorAlgebra.repr w T) := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply', Finsupp.smul_apply]
  rw [Finset.sum_eq_single p]
  · rw [creation_coordinate, if_pos (Finset.mem_insert_self p T), Finset.erase_insert hp]
  · intro j hj hjp
    rcases lt_or_gt_of_ne hjp with hlt | hgt
    · rw [creation_coordinate]
      split_ifs
      · rw [replacement_coefficient_eq_zero b w T hmax p j hp hlt, smul_zero, smul_zero]
      · exact smul_zero _
    · rw [hv j hgt, zero_smul]
  · simp

end Coefficients

section Mixed

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
variable (b : Module.Basis (Fin n ⊕ Fin n) R V)

/-- Completing the xi colour preserves every mixed equation. No ordinary
prefix moment is assumed, because none is required for the diagonal Gauss bound. -/
theorem xiCompletion_preserves_mixed
    (φ c : Fin n → R) (w : ExteriorAlgebra R V)
    (hw : ∀ p : Polynomial R, mixedCurrent b φ p w = 0)
    (hθ : ∀ p : Polynomial R, thetaCurrent b φ c p w = 0) :
    ∀ p : Polynomial R, mixedCurrent b φ p (xiCreator b φ c 1 w) = 0 := by
  intro p
  have h := congrArg (fun f : Module.End R (ExteriorAlgebra R V) ↦ f w)
    (mixedCurrent_xiCreator b φ c 1 p)
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, hw p,
    map_zero, mul_one, hθ p, sub_zero] using h

/-- The theta completion has the symmetric mixed-equation property. -/
theorem thetaCompletion_preserves_mixed
    (φ β a : Fin n → R) (w : ExteriorAlgebra R V)
    (hw : ∀ p : Polynomial R, mixedCurrent b φ p w = 0)
    (hξ : ∀ p : Polynomial R, xiCurrent b φ β a p w = 0) :
    ∀ p : Polynomial R, mixedCurrent b φ p (thetaCreator b φ β a 1 w) = 0 := by
  intro p
  have h := congrArg (fun f : Module.End R (ExteriorAlgebra R V) ↦ f w)
    (mixedCurrent_thetaCreator b φ β a 1 p)
  simpa only [Module.End.mul_apply, LinearMap.add_apply, hw p,
    map_zero, mul_one, hξ p, add_zero] using h

/-- At zero primitive weight the completed vector is zero, so the completed
leading coefficient vanishes as required by the endpoint single-mark relation. -/
theorem xiCompletion_eq_zero_at_middle
    (φ c : Fin n → R) (hfac : IsUnit (n.factorial : R))
    (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^n V)
    (hw : ∀ p : Polynomial R, mixedCurrent b φ p w = 0)
    (hθ : ∀ p : Polynomial R, thetaCurrent b φ c p w = 0) :
    xiCreator b φ c 1 w = 0 := by
  apply primitive_degree_bound b (by simpa only [Fintype.card_fin] using hfac)
    (n + 1) _ (creation_mem_succ _ hwdegree)
  · have h := xiCompletion_preserves_mixed b φ c w hw hθ 1
    simpa only [mixedCurrent, Polynomial.eval_one, one_smul, lowering, xiCreator, thetaCreator] using h
  · simp only [Fintype.card_fin]
    omega

theorem thetaCompletion_eq_zero_at_middle
    (φ β a : Fin n → R) (hfac : IsUnit (n.factorial : R))
    (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^n V)
    (hw : ∀ p : Polynomial R, mixedCurrent b φ p w = 0)
    (hξ : ∀ p : Polynomial R, xiCurrent b φ β a p w = 0) :
    thetaCreator b φ β a 1 w = 0 := by
  apply primitive_degree_bound b (by simpa only [Fintype.card_fin] using hfac)
    (n + 1) _ (creation_mem_succ _ hwdegree)
  · have h := thetaCompletion_preserves_mixed b φ β a w hw hξ 1
    simpa only [mixedCurrent, Polynomial.eval_one, one_smul, lowering, xiCreator, thetaCreator] using h
  · simp only [Fintype.card_fin]
    omega

end Mixed

section Remainder

variable {R : Type*} [CommRing R]

/-- Reversing the bounded single-mark identity gives the exact monic-division
remainder equation. This is valid with nilpotent or zero-divisor coefficients:
neither division by a node nor cancellation of the selected coefficient occurs. -/
theorem singleMark_remainder_of_bounded_identity
    (c : ℕ) (hc : 0 < c) (y a : R) (P Q : Polynomial R)
    (hQ : Q.natDegree ≤ c - 1)
    (hprod : (1 + Polynomial.C y * Polynomial.X) * Q = Polynomial.C a * P) :
    a * (Polynomial.reflect c P).eval (-y) = 0 := by
  have hdeg : (1 + Polynomial.C y * Polynomial.X : Polynomial R).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le y 1
  have hlin : Polynomial.reflect 1 (1 + Polynomial.C y * Polynomial.X) =
      Polynomial.X + Polynomial.C y := by
    rw [Polynomial.reflect_add, Polynomial.reflect_one,
      show Polynomial.C y * Polynomial.X = Polynomial.C y * Polynomial.X ^ 1 by rw [pow_one],
      Polynomial.reflect_C_mul_X_pow]
    simp only [pow_one, Polynomial.revAt_le le_rfl, Nat.sub_self, pow_zero, mul_one]
  have hmul : Polynomial.reflect c ((1 + Polynomial.C y * Polynomial.X) * Q) =
      (Polynomial.X + Polynomial.C y) * Polynomial.reflect (c - 1) Q := by
    have hc' : c = 1 + (c - 1) := by omega
    conv_lhs => rw [hc']
    rw [Polynomial.reflect_mul _ _ hdeg hQ, hlin]
  have h := congrArg (Polynomial.reflect c) hprod
  rw [hmul, Polynomial.reflect_C_mul] at h
  have he := congrArg (Polynomial.eval (-y)) h
  simpa only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, neg_add_cancel, zero_mul] using he.symm

/-- The paper's `t-y` convention is the same exact remainder statement. -/
theorem singleMark_remainder_of_bounded_identity_sub
    (c : ℕ) (hc : 0 < c) (y a : R) (P Q : Polynomial R)
    (hQ : Q.natDegree ≤ c - 1)
    (hprod : (1 - Polynomial.C y * Polynomial.X) * Q = Polynomial.C a * P) :
    a * (Polynomial.reflect c P).eval y = 0 := by
  have hprod' : (1 + Polynomial.C (-y) * Polynomial.X) * Q = Polynomial.C a * P := by
    simpa only [map_neg, neg_mul, ← sub_eq_add_neg] using hprod
  simpa only [neg_neg] using
    singleMark_remainder_of_bounded_identity c hc (-y) a P Q hQ hprod'

end Remainder

end PaperVerification.Fermion.Exterior
