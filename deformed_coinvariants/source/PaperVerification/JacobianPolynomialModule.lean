module

public import PaperVerification.JacobianMilnorReduction
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The actual polynomial-module structure on the divergence quotient

All quotients below use the previously defined polynomial subspaces. The
parameter acts by multiplication by the given potential, rather than by an
unspecified endomorphism. The map to the Milnor quotient is the actual quotient
map, and its kernel is proved to be the parameter image.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial Polynomial

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K

abbrev BrieskornQuotient (F : P) := P ⧸ divergenceSpace F

def potentialAction (F : P) : BrieskornQuotient F →ₗ[K] BrieskornQuotient F :=
  (divergenceSpace F).mapQ (divergenceSpace F) (LinearMap.mulLeft K F)
    (fun u hu => potential_mul_mem F u hu)

@[simp] theorem potentialAction_mk (F u : P) :
    potentialAction F ((divergenceSpace F).mkQ u) =
      (divergenceSpace F).mkQ (F * u) := rfl

/-- `K[X]` acts on the divergence quotient with `X` acting as the potential. -/
abbrev BrieskornModule (F : P) := Module.AEval' (potentialAction F)

def classOf (F : P) : P →ₗ[K] BrieskornModule F :=
  (Module.AEval'.of (potentialAction F)).toLinearMap.comp (divergenceSpace F).mkQ

theorem classOf_surjective (F : P) : Function.Surjective (classOf F) :=
  (Module.AEval'.of (potentialAction F)).surjective.comp
    (divergenceSpace F).mkQ_surjective

@[simp] theorem X_smul_classOf (F u : P) :
    (Polynomial.X : K[X]) • classOf F u = classOf F (F * u) := by
  exact Module.AEval'.X_smul_of (potentialAction F) ((divergenceSpace F).mkQ u)

@[simp] theorem classOf_eq_zero (F u : P) :
    classOf F u = 0 ↔ u ∈ divergenceSpace F := by
  change Module.AEval'.of (potentialAction F) ((divergenceSpace F).mkQ u) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

def jacobianSubmodule (F : P) : Submodule K P :=
  (Ideal.span (Set.range (gradient F))).restrictScalars K

abbrev MilnorQuotient (F : P) := P ⧸ jacobianSubmodule F

variable {n : ℕ}
local notation "Pn" => MvPolynomial (Fin n) K

def milnorMap (F : Pn)
    (hreg : RingTheory.Sequence.IsWeaklyRegular Pn (List.ofFn (gradient F))) :
    BrieskornModule F →ₗ[K] MilnorQuotient F :=
  ((divergenceSpace F).factor (divergenceSpace_le_jacobian F hreg)).comp
    (Module.AEval'.of (potentialAction F)).symm.toLinearMap

@[simp] theorem milnorMap_classOf (F u : Pn)
    (hreg : RingTheory.Sequence.IsWeaklyRegular Pn (List.ofFn (gradient F))) :
    milnorMap F hreg (classOf F u) = (jacobianSubmodule F).mkQ u := rfl

theorem milnorMap_surjective (F : Pn)
    (hreg : RingTheory.Sequence.IsWeaklyRegular Pn (List.ofFn (gradient F))) :
    Function.Surjective (milnorMap F hreg) := by
  intro v
  obtain ⟨u, rfl⟩ := (jacobianSubmodule F).mkQ_surjective v
  exact ⟨classOf F u, rfl⟩

/-- Torsion-freeness is now a statement about the actual polynomial action. -/
theorem parameter_regular [CharZero K] [Nonempty (Fin n)]
    (F : Pn) (w : Fin n → ℕ) (h : ℕ)
    (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hreg : RingTheory.Sequence.IsWeaklyRegular Pn (List.ofFn (gradient F))) :
    IsSMulRegular (BrieskornModule F) (Polynomial.X : K[X]) := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro x hx
  obtain ⟨u, rfl⟩ := classOf_surjective F x
  rw [X_smul_classOf, classOf_eq_zero] at hx
  rw [classOf_eq_zero]
  exact potential_torsion_free F u w h hw hh hF hreg hx

/-- The kernel of the genuine Milnor quotient map is precisely `X V_F`. -/
theorem milnorMap_ker [CharZero K]
    (hn : 2 ≤ n) (F : Pn) (w : Fin n → ℕ) (h : ℕ)
    (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hreg : RingTheory.Sequence.IsWeaklyRegular Pn (List.ofFn (gradient F))) :
    LinearMap.ker (milnorMap F hreg) =
      LinearMap.range (Algebra.lsmul K K (BrieskornModule F) (Polynomial.X : K[X])) := by
  ext x
  obtain ⟨u, rfl⟩ := classOf_surjective F x
  constructor
  · intro hx
    have hu : u ∈ jacobianSubmodule F := by
      simpa only [LinearMap.mem_ker, milnorMap_classOf, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx
    rw [jacobianSubmodule, jacobian_eq_reductionSpace hn F w h hw hh hF hreg] at hu
    obtain ⟨r, hr, v, hv, hrv⟩ := Submodule.mem_sup.mp hu
    obtain ⟨b, rfl⟩ := hv
    refine ⟨classOf F b, ?_⟩
    change (Polynomial.X : K[X]) • classOf F b = classOf F u
    rw [X_smul_classOf, ← hrv, map_add, (classOf_eq_zero F r).mpr hr, zero_add]
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := classOf_surjective F x
    change (Polynomial.X : K[X]) • classOf F v = classOf F u at hx
    rw [← hx, X_smul_classOf, LinearMap.mem_ker, milnorMap_classOf,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change F * v ∈ (Ideal.span (Set.range (gradient F))).restrictScalars K
    rw [jacobian_eq_reductionSpace hn F w h hw hh hF hreg]
    exact potential_mul_mem_reduction F v

end PaperVerification.JacobianDivergence
