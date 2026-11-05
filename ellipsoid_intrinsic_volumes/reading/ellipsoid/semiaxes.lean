module

public import Ellipsoid.Definitions
public import Ellipsoid.CoefficientDefinitions
public import tau_ceti.ring_theory.polynomial.roots
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

noncomputable section

open MeasureTheory Set Polynomial
open scoped BigOperators Pointwise

namespace EllipsoidVerification

def axisCoefficientPolynomial {n : ℕ} (a : Fin n → ℝ) : ℝ[X] :=
  ∏ i, (1 + C (a i ^ 2) * X)

def axisCoefficients {n : ℕ} (a : Fin n → ℝ) : Coefficients n :=
  fun j => (axisCoefficientPolynomial a).coeff j.val

def inverseSquareRoot {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ :=
  -(a i ^ 2)⁻¹

theorem axisCoefficientPolynomial_factorization {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    axisCoefficientPolynomial a = C (∏ i, a i ^ 2) *
      ∏ i, (X - C (inverseSquareRoot a i)) := by
  unfold axisCoefficientPolynomial
  rw [map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  unfold inverseSquareRoot
  have hai : a i ^ 2 ≠ 0 := pow_ne_zero _ (ha i).ne'
  rw [mul_sub, ← C_mul, mul_neg, mul_inv_cancel₀ hai]
  simp only [C_neg, map_one, sub_neg_eq_add]
  ring

theorem axisCoefficientPolynomial_roots {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    (axisCoefficientPolynomial a).roots = Finset.univ.val.map (inverseSquareRoot a) := by
  rw [axisCoefficientPolynomial_factorization a ha]
  exact roots_C_mul_prod_X_sub_C _ _
    (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (ha i).ne')

/-- Equality of finite value multisets gives an actual permutation matching
every occurrence, including repeated values. -/
theorem exists_perm_of_multiset_map_eq {n : ℕ} {f g : Fin n → ℝ}
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, f i = g (σ i) := by
  classical
  have hc (x : ℝ) : Fintype.card {i : Fin n // f i = x} =
      Fintype.card {i : Fin n // g i = x} := by
    have hh := congrArg (Multiset.count x) h
    simpa only [Multiset.count_map, ← Finset.filter_val, ← Finset.card_def,
      Fintype.card_subtype, eq_comm] using hh
  let σ : Equiv.Perm (Fin n) := Equiv.ofFiberEquiv fun x => Fintype.equivOfCardEq (hc x)
  exact ⟨σ, fun i => (Equiv.ofFiberEquiv_map _ i).symm⟩

theorem semiaxes_perm_of_axisPolynomial_eq {n : ℕ} {a b : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (h : axisCoefficientPolynomial a = axisCoefficientPolynomial b) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, a i = b (σ i) := by
  have hr := congrArg Polynomial.roots h
  rw [axisCoefficientPolynomial_roots a ha, axisCoefficientPolynomial_roots b hb] at hr
  obtain ⟨σ, hσ⟩ := exists_perm_of_multiset_map_eq hr
  refine ⟨σ, fun i => ?_⟩
  have hi := hσ i
  dsimp [inverseSquareRoot] at hi
  have hs : a i ^ 2 = b (σ i) ^ 2 := inv_injective (neg_injective hi)
  nlinarith [ha i, hb (σ i)]

def permuteAxes {n : ℕ} (σ : Equiv.Perm (Fin n)) : Space n ≃ₗᵢ[ℝ] Space n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ

theorem permuteAxes_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Space n) (i : Fin n) :
    permuteAxes σ x i = x (σ.symm i) := rfl

theorem permuteAxes_axisMap {n : ℕ} {a b : Fin n → ℝ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, a i = b (σ i)) (x : Space n) :
    permuteAxes σ (axisMap a x) = axisMap b (permuteAxes σ x) := by
  ext i
  simpa [permuteAxes_apply, axisMap] using
    congrArg (fun r : ℝ => r * x (σ.symm i)) (hσ (σ.symm i))

def FullEllipsoid.placement {n : ℕ} (E : FullEllipsoid n) : Space n ≃ᵢ Space n :=
  E.frame.toIsometryEquiv.trans (IsometryEquiv.vaddConst E.center)

@[simp] theorem FullEllipsoid.placement_apply {n : ℕ} (E : FullEllipsoid n) (x : Space n) :
    E.placement x = E.center + E.frame x := by
  simp [FullEllipsoid.placement, IsometryEquiv.vaddConst, add_comm]

/-- A permutation of positive semiaxes gives an isometry between the actual
ellipsoid bodies. No simple-spectrum hypothesis is used. -/
theorem FullEllipsoid.congruent_of_semiaxes_perm {n : ℕ} (E F : FullEllipsoid n)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, E.semiaxis i = F.semiaxis (σ i)) :
    E.congruent F := by
  let P := permuteAxes σ
  let T := E.placement.symm.trans (P.toIsometryEquiv.trans F.placement)
  refine ⟨T, ?_⟩
  apply Set.Subset.antisymm
  · rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨P x, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, P.norm_map] using hx
    · change F.center + F.frame (axisMap F.semiaxis (P x)) =
        T (E.center + E.frame (axisMap E.semiaxis x))
      rw [← F.placement_apply, ← E.placement_apply]
      simp only [T, IsometryEquiv.trans_apply, IsometryEquiv.symm_apply_apply,
        LinearIsometryEquiv.coe_toIsometryEquiv]
      exact congrArg F.placement (permuteAxes_axisMap σ hσ x).symm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨E.placement (axisMap E.semiaxis (P.symm x)), ?_, ?_⟩
    · refine ⟨P.symm x, ?_, by simp⟩
      simpa only [Metric.mem_closedBall, dist_zero_right, P.symm.norm_map] using hx
    · change T (E.placement (axisMap E.semiaxis (P.symm x))) =
        F.center + F.frame (axisMap F.semiaxis x)
      rw [← F.placement_apply]
      simp only [T, IsometryEquiv.trans_apply, IsometryEquiv.symm_apply_apply,
        LinearIsometryEquiv.coe_toIsometryEquiv]
      rw [permuteAxes_axisMap σ hσ, P.apply_symm_apply]

theorem FullEllipsoid.congruent_of_axisPolynomial_eq {n : ℕ} (E F : FullEllipsoid n)
    (h : axisCoefficientPolynomial E.semiaxis = axisCoefficientPolynomial F.semiaxis) :
    E.congruent F := by
  obtain ⟨σ, hσ⟩ := semiaxes_perm_of_axisPolynomial_eq E.semiaxis_pos F.semiaxis_pos h
  exact E.congruent_of_semiaxes_perm F σ hσ

end EllipsoidVerification
