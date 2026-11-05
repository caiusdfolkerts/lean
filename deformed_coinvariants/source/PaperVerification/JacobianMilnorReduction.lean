module

public import PaperVerification.JacobianGrading
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Reduction of the Brieskorn quotient modulo the potential

The polynomial coordinate Euler syzygy proves `J(F) = div(ker dF) + F P`.
Together with injectivity of multiplication by `F`, this is the algebraic
input to lifting a Milnor basis. No differential-form comparison is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [Field K] [Fintype ι]
local instance milnorReductionDecidableEq : DecidableEq ι := Classical.decEq ι
local notation "P" => MvPolynomial ι K

/-- The vector-space image of multiplication by the potential. -/
def potentialRange (F : P) : Submodule K P :=
  LinearMap.range (LinearMap.mulLeft K F)

/-- The relations for the divergence quotient modulo the potential. -/
def reductionSpace (F : P) : Submodule K P := divergenceSpace F ⊔ potentialRange F

theorem potential_mul_mem_reduction (F u : P) : F * u ∈ reductionSpace F :=
  (show potentialRange F ≤ reductionSpace F from le_sup_right) ⟨u, rfl⟩

@[simp] theorem coefficient_single (f : ι → P) (i : ι) (u : P) :
    KoszulSyzygies.coefficient f (Pi.single i u) = u * f i := by
  classical
  simp [KoszulSyzygies.coefficient_apply, Pi.single_apply]

@[simp] theorem divergence_single (i : ι) (u : P) :
    divergence (Pi.single i u) = pderiv i u := by
  classical
  simp [divergence_apply, Pi.single_apply, apply_ite]

theorem coefficient_eulerField_eq_euler_mul (F u : P) (w : ι → ℕ) :
    KoszulSyzygies.coefficient (gradient F) (eulerField w u) = weightedEuler w F * u := by
  simp only [KoszulSyzygies.coefficient_apply, gradient, eulerField,
    weightedEuler_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [nsmul_eq_mul]
  ring

/-- The tangent coordinate Euler relation used in the reduction argument. -/
def coordinateEulerSyzygy (F : P) (w : ι → ℕ) (h : ℕ) (i : ι) (u : P) : ι → P :=
  (pderiv i F) • eulerField w u - Pi.single i (h • (F * u))

theorem coordinateEulerSyzygy_mem_tangent (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (i : ι) (u : P) :
    coordinateEulerSyzygy F w h i u ∈ tangent F := by
  change KoszulSyzygies.coefficient (gradient F)
    ((pderiv i F) • eulerField w u - Pi.single i (h • (F * u))) = 0
  rw [map_sub, map_smul, coefficient_eulerField F w h hF, coefficient_single]
  simp only [gradient, smul_eq_mul, nsmul_eq_mul]
  ring

theorem divergence_coordinateEulerSyzygy (F : P) (w : ι → ℕ) (h d : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (i : ι) (u : P)
    (hu : u.IsWeightedHomogeneous w d) :
    divergence (coordinateEulerSyzygy F w h i u) =
      (((∑ j, w j : ℕ) + d : K) - (w i : K)) • (pderiv i F * u) -
        h • (F * pderiv i u) := by
  simp only [coordinateEulerSyzygy]
  rw [map_sub, divergence_mul (pderiv i F) (eulerField w u),
    coefficient_eulerField_eq_euler_mul (pderiv i F) u w,
    weightedEuler_gradient F w h hF i, divergence_eulerField_homogeneous w u d hu,
    divergence_single i (h • (F * u)), map_nsmul, pderiv_mul]
  simp only [nsmul_eq_mul]
  simp only [Algebra.smul_def, map_sub, map_add, map_natCast, Nat.cast_add]
  ring

theorem weight_lt_total [Nontrivial ι] (w : ι → ℕ) (hw : ∀ i, 0 < w i) (i : ι) :
    w i < ∑ j, w j := by
  classical
  obtain ⟨j, hji⟩ := exists_ne i
  have hle : w i + w j ≤ ∑ k, w k := by
    have hs : ∑ k ∈ ({i, j} : Finset ι), w k ≤ ∑ k, w k :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    simpa only [Finset.sum_pair hji.symm] using hs
  have hj := hw j
  omega

/-- Every homogeneous coefficient multiple of a partial derivative reduces
modulo divergences to a multiple of the potential. -/
theorem gradient_mul_mem_reduction_homogeneous [CharZero K] [Nontrivial ι]
    (F : P) (w : ι → ℕ) (h d : ℕ) (hw : ∀ i, 0 < w i)
    (hF : F.IsWeightedHomogeneous w h) (i : ι) (u : P)
    (hu : u.IsWeightedHomogeneous w d) : pderiv i F * u ∈ reductionSpace F := by
  let a : K := (((∑ j, w j : ℕ) + d : K) - (w i : K))
  have ha : a ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hz
    have hz' : (∑ j, w j) + d = w i := Nat.cast_injective (by simpa only [Nat.cast_add] using hz : (((∑ j, w j) + d : ℕ) : K) = (w i : K))
    have hi := weight_lt_total w hw i
    omega
  have hD : divergence (coordinateEulerSyzygy F w h i u) ∈ reductionSpace F := by
    apply (show divergenceSpace F ≤ reductionSpace F from le_sup_left)
    exact ⟨_, coordinateEulerSyzygy_mem_tangent F w h hF i u, rfl⟩
  have hFpart : h • (F * pderiv i u) ∈ reductionSpace F :=
    (reductionSpace F).nsmul_mem (potential_mul_mem_reduction F (pderiv i u)) h
  have hm := (reductionSpace F).add_mem hD hFpart
  rw [divergence_coordinateEulerSyzygy F w h d hF i u hu, sub_add_cancel] at hm
  have hs := (reductionSpace F).smul_mem a⁻¹ hm
  simpa only [a, smul_smul, inv_mul_cancel₀ ha, one_smul] using hs

/-- The same reduction holds for every polynomial multiplier. -/
theorem gradient_mul_mem_reduction [CharZero K] [Nontrivial ι]
    (F : P) (w : ι → ℕ) (h : ℕ) (hw : ∀ i, 0 < w i)
    (hF : F.IsWeightedHomogeneous w h) (i : ι) (u : P) :
    pderiv i F * u ∈ reductionSpace F := by
  induction u using MvPolynomial.induction_on' with
  | monomial a c =>
    exact gradient_mul_mem_reduction_homogeneous F w h (Finsupp.weight w a) hw hF i _
      (isWeightedHomogeneous_monomial w a c rfl)
  | add u v hu hv =>
    simpa only [mul_add] using (reductionSpace F).add_mem hu hv

/-- The exact reduction statement `V_F / F V_F = P / J(F)` at the level of
its defining polynomial subspaces. -/
theorem jacobian_eq_reductionSpace [CharZero K] {n : ℕ} (hn : 2 ≤ n)
    (F : MvPolynomial (Fin n) K) (w : Fin n → ℕ) (h : ℕ)
    (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn (gradient F))) :
    (Ideal.span (Set.range (gradient F))).restrictScalars K = reductionSpace F := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  apply le_antisymm
  · intro f hf
    change f ∈ Submodule.span (MvPolynomial (Fin n) K) (Set.range (gradient F)) at hf
    have aux : ∀ g : MvPolynomial (Fin n) K, g * f ∈ reductionSpace F := by
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        intro g
        simpa only [gradient, mul_comm] using gradient_mul_mem_reduction F w h hw hF i g
      | zero => intro g; simpa only [mul_zero] using (reductionSpace F).zero_mem
      | add x y hx hy ihx ihy =>
        intro g
        simpa only [mul_add] using (reductionSpace F).add_mem (ihx g) (ihy g)
      | smul a x hx ih =>
        intro g
        simpa only [smul_eq_mul, mul_assoc] using ih (g * a)
    simpa only [one_mul] using aux 1
  · apply sup_le
    · exact divergenceSpace_le_jacobian F hreg
    · have hE : EulerJacobian.EulerRelation (gradient F) F w (h : K) := by
        simpa only [EulerJacobian.EulerRelation, gradient, Nat.cast_smul_eq_nsmul]
          using hF.sum_weight_X_mul_pderiv
      have hFJ := EulerJacobian.perturbation_mem_ideal (gradient F) F w (h : K) hE
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hh))
      rintro _ ⟨u, rfl⟩
      exact (Ideal.span (Set.range (gradient F))).mul_mem_right u hFJ

end PaperVerification.JacobianDivergence
