module

public import PaperVerification.JacobianDefect
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The degree of the exceptional Jacobian defect

The quotient components are images of actual weighted homogeneous polynomials.
The hit subspace is proved homogeneous, and at resonance every Jacobian class
has a representative `F * p_d`. Thus the entire defect lies in degree `h + d`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.EulerResonance

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K

def quotientProjection (w : ι → ℕ) (d : ℕ) (U : Submodule K P)
    (hU : ∀ p ∈ U, weightedHomogeneousComponent w d p ∈ U) :
    (P ⧸ U) →ₗ[K] (P ⧸ U) :=
  U.mapQ U (weightedHomogeneousComponent w d) hU

@[simp] theorem quotientProjection_mk (w : ι → ℕ) (d : ℕ) (U : Submodule K P)
    (hU : ∀ p ∈ U, weightedHomogeneousComponent w d p ∈ U) (p : P) :
    quotientProjection w d U hU (U.mkQ p) = U.mkQ (weightedHomogeneousComponent w d p) :=
  rfl

theorem quotientProjection_of_mem (w : ι → ℕ) (d : ℕ) (U : Submodule K P)
    (hU : ∀ p ∈ U, weightedHomogeneousComponent w d p ∈ U)
    (x : P ⧸ U) (hx : x ∈ quotientComponent w d U) :
    quotientProjection w d U hU x = x := by
  obtain ⟨p, rfl⟩ := hx
  change U.mkQ (weightedHomogeneousComponent w d
    (weightedHomogeneousComponent w d p)) = U.mkQ (weightedHomogeneousComponent w d p)
  rw [homogeneous_projection_idempotent]

theorem quotientProjection_of_mem_ne (w : ι → ℕ) (d e : ℕ) (U : Submodule K P)
    (hU : ∀ p ∈ U, weightedHomogeneousComponent w d p ∈ U)
    (hde : d ≠ e) (x : P ⧸ U) (hx : x ∈ quotientComponent w e U) :
    quotientProjection w d U hU x = 0 := by
  obtain ⟨p, rfl⟩ := hx
  change U.mkQ (weightedHomogeneousComponent w d
    (weightedHomogeneousComponent w e p)) = 0
  rw [(weightedHomogeneousComponent_isWeightedHomogeneous e p).weightedHomogeneousComponent_ne d hde,
    map_zero]

theorem quotientComponent_disjoint (w : ι → ℕ) (d e : ℕ) (U : Submodule K P)
    (hU : ∀ p ∈ U, weightedHomogeneousComponent w d p ∈ U) (hde : d ≠ e) :
    Disjoint (quotientComponent w d U) (quotientComponent w e U) := by
  rw [disjoint_iff]
  apply eq_bot_iff.mpr
  intro x hx
  have hleft := quotientProjection_of_mem w d U hU x hx.1
  have hright := quotientProjection_of_mem_ne w d e U hU hde x hx.2
  exact hleft.symm.trans hright

theorem quotientComponent_finite (w : ι → ℕ) (d : ℕ) (U : Submodule K P)
    (hw : ∀ i, 0 < w i) : Module.Finite K (quotientComponent w d U) := by
  rw [quotientComponent_eq_map]
  letI : Module.Finite K (weightedHomogeneousSubmodule K w d) :=
    Module.Finite.of_fg (weightedHomogeneousSubmodule_fg K w
      (fun i => Nat.ne_of_gt (hw i)) d)
  infer_instance

end PaperVerification.EulerResonance

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K

theorem weightedEuler_operator (F g : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hF : F.IsWeightedHomogeneous w h) (i : ι) :
    weightedEuler w (EulerJacobian.operator (gradient F) F t i g) =
      EulerJacobian.operator (gradient F) F t i (weightedEuler w g) +
        h • EulerJacobian.operator (gradient F) F t i g -
        w i • EulerJacobian.operator (gradient F) F t i g := by
  have hder : weightedEuler w (pderiv i g) =
      pderiv i (weightedEuler w g) - w i • pderiv i g := by
    rw [pderiv_weightedEuler]
    abel
  simp only [EulerJacobian.operator, gradient, map_add, map_smul,
    weightedEuler_mul, weightedEuler_gradient F w h hF,
    weightedEuler_homogeneous w F h hF, hder]
  simp only [nsmul_eq_mul]
  simp only [Algebra.smul_def, map_natCast]
  ring

theorem weightedEuler_mem_hit (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hF : F.IsWeightedHomogeneous w h) (p : P)
    (hp : p ∈ EulerJacobian.hit (gradient F) F t) :
    weightedEuler w p ∈ EulerJacobian.hit (gradient F) F t := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, g, rfl⟩ := hp
    rw [weightedEuler_operator F g w h t hF i]
    exact (EulerJacobian.hit (gradient F) F t).sub_mem
      ((EulerJacobian.hit (gradient F) F t).add_mem
        (EulerJacobian.operator_mem_hit _ _ _ _ _)
        ((EulerJacobian.hit (gradient F) F t).nsmul_mem
          (EulerJacobian.operator_mem_hit _ _ _ _ _) h))
      ((EulerJacobian.hit (gradient F) F t).nsmul_mem
        (EulerJacobian.operator_mem_hit _ _ _ _ _) (w i))
  | zero => simpa only [map_zero] using (EulerJacobian.hit (gradient F) F t).zero_mem
  | add p q hp hq ihp ihq =>
    simpa only [map_add] using (EulerJacobian.hit (gradient F) F t).add_mem ihp ihq
  | smul c p hp ih =>
    simpa only [map_smul] using (EulerJacobian.hit (gradient F) F t).smul_mem c ih

theorem homogeneousComponent_mem_hit [CharZero K]
    (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hF : F.IsWeightedHomogeneous w h) (p : P)
    (hp : p ∈ EulerJacobian.hit (gradient F) F t) (d : ℕ) :
    weightedHomogeneousComponent w d p ∈ EulerJacobian.hit (gradient F) F t :=
  homogeneousComponent_mem_of_eulerStable w _
    (weightedEuler_mem_hit F w h t hF) p hp d

/-- Every potential class equals its actual resonant homogeneous component. -/
theorem potentialToHitQuotient_eq_component [CharZero K]
    (F : P) (w : ι → ℕ) (h d : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0) (p : P) :
    potentialToHitQuotient F t p =
      potentialToHitQuotient F t (weightedHomogeneousComponent w d p) := by
  obtain ⟨ht, hd, hother⟩ := normalized_resonance w h d t hh hres
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply LinearMap.mem_ker.mp
  rw [potentialToHitQuotient_kernel F w h t hh hF ht,
    EulerResonance.range_scalarEuler_eq_projection_kernel w _ _ d hd hother]
  apply (show LinearMap.ker (weightedHomogeneousComponent w d : P →ₗ[K] P) ≤
    LinearMap.ker (weightedHomogeneousComponent w d : P →ₗ[K] P) ⊔ divergenceSpace F
    from le_sup_left)
  rw [LinearMap.mem_ker, map_sub, EulerResonance.homogeneous_projection_idempotent, sub_self]

/-- Concentration refers to the polynomial target degree `h+d`, including the
shift by the degree of the potential. -/
theorem exceptional_defect_concentrated [CharZero K]
    (F : P) (w : ι → ℕ) (h d : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    defectImage F t ≤
      EulerResonance.quotientComponent w (h + d) (EulerJacobian.hit (gradient F) F t) := by
  rw [← potentialToHitQuotient_range F w h t hh hF]
  rintro _ ⟨p, rfl⟩
  rw [potentialToHitQuotient_eq_component F w h d t hh hF hres p,
    EulerResonance.quotientComponent_eq_map]
  refine ⟨F * weightedHomogeneousComponent w d p, ?_, rfl⟩
  exact hF.mul (weightedHomogeneousComponent_isWeightedHomogeneous d p)

theorem exceptional_defect_other_degree [CharZero K]
    (F : P) (w : ι → ℕ) (h d e : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0)
    (he : h + d ≠ e) :
    defectImage F t ⊓
      EulerResonance.quotientComponent w e (EulerJacobian.hit (gradient F) F t) = ⊥ := by
  apply eq_bot_iff.mpr
  exact (inf_le_inf_right _ (exceptional_defect_concentrated F w h d t hh hF hres)).trans
    (EulerResonance.quotientComponent_disjoint w (h + d) e _
      (fun p hp => homogeneousComponent_mem_hit F w h t hF p hp (h + d)) he).eq_bot.le

end PaperVerification.JacobianDivergence
