module

public import PaperVerification.FermionPairedMomentHighest
public import PaperVerification.FermionPairedCoupledIndependence

/-!
# The full coupled paired basis over a field

This source candidate joins the actual creator independence proof to filtered
spanning in the literal polynomial/exterior algebra.  The kernel of each
quotient map is identified with the span of all left/right ambient basis
multiples of the finite moment generators.  No flatness, initial-ideal, or
dimension hypothesis is supplied to the endpoint.

This module has not yet been compiler checked.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped BigOperators TensorProduct

section QuotientKernel

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The actual quotient linear map has the original two-sided ideal as its
coefficient submodule kernel. -/
theorem quotient_kernel_eq_twoSidedIdealSubmodule (H : TwoSidedIdeal A) :
    ((H.ringCon.mkₐ R).toLinearMap).ker = twoSidedIdealSubmodule H := by
  ext x
  change H.ringCon.mkₐ R x = H.ringCon.mkₐ R 0 ↔ H.ringCon x 0
  exact H.ringCon.eq

end QuotientKernel

variable {F : Type*} [Field F] {n : ℕ}

local instance FermionPairedCoupledBasis_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- Every proposed coupled class spans the full quotient together with the
other proposed classes.  This is reduction by the actual moment generators,
including both left and right products in the noncommutative algebra. -/
theorem pairedCoupledClasses_span (d : PairedData (K := F) (n := n)) :
    Submodule.span F (Set.range (pairedCoupledClasses d)) = ⊤ := by
  classical
  let b := superMonomialBasis (K := F) (n := n)
  let w := superMonomialWeight (coveringWeight d.r) (pairedOddWeight d)
  let v (z : PairedPowerIndex d.r d.u d.v d.s) : SuperRing F n :=
    b (z.2.val.val,z.1)
  let q := ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ F).toLinearMap
  let q₀ := ((pairedIdeal d.beta (fun i ↦ X i^d.r i)
    (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ F).toLinearMap
  let f := basisRelationMultiple b (pairedFiniteRelation d)
  let g := basisRelationMultiple b (pairedPowerFiniteRelation d)
  have hq : Function.Surjective q :=
    (pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ_surjective (α := F)
  have hq₀ : Function.Surjective q₀ :=
    (pairedIdeal d.beta (fun i ↦ X i^d.r i)
      (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ_surjective (α := F)
  have hker : q.ker = Submodule.span F (Set.range f) := by
    rw [show q.ker = twoSidedIdealSubmodule (pairedIdeal d.beta d.phi d.a d.b) from
      quotient_kernel_eq_twoSidedIdealSubmodule _]
    rw [← pairedFiniteRelation_ideal d,twoSidedIdealSubmodule_span b]
  have hker₀ : q₀.ker = Submodule.span F (Set.range g) := by
    rw [show q₀.ker = twoSidedIdealSubmodule (pairedIdeal d.beta
        (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)) from
      quotient_kernel_eq_twoSidedIdealSubmodule _]
    rw [← pairedPowerFiniteRelation_ideal d,twoSidedIdealSubmodule_span b]
  have hclass (z : PairedPowerIndex d.r d.u d.v d.s) :
      q (v z) = pairedCoupledClasses d z := by
    change q (superMonomialBasis (z.2.val.val,z.1)) = _
    rw [superMonomialBasis_apply]
    rfl
  have hclass₀ (z : PairedPowerIndex d.r d.u d.v d.s) :
      q₀ (v z) = pairedPowerClasses d.r d.u d.v d.beta d.s z := by
    change q₀ (superMonomialBasis (z.2.val.val,z.1)) = _
    rw [superMonomialBasis_apply]
    rfl
  have hpower : Submodule.span F (Set.range (fun z ↦ q₀ (v z))) = ⊤ := by
    have he : (fun z ↦ q₀ (v z)) =
        (pairedPowerBasis d.r d.u d.v d.beta d.s d.positive_s d.positive_r
          d.degree_split d.allowed_weights.2 d.allowed_weights.1 :
            PairedPowerIndex d.r d.u d.v d.s →
              PairedQuotient d.beta (fun i ↦ X i^d.r i)
                (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)) := by
      funext z
      rw [pairedPowerBasis_apply]
      exact hclass₀ z
    rw [he]
    exact Module.Basis.span_eq _
  have hleading : Submodule.span F (Set.range v) ⊔
      Submodule.span F (Set.range g) = ⊤ := by
    rw [← hker₀]
    exact (span_image_eq_top_iff q₀ hq₀ v).mp hpower
  have hactual : Submodule.span F (Set.range v) ⊔
      Submodule.span F (Set.range f) = ⊤ :=
    BasisFiltered.spanning_lifts b w f g (pairedRelationMultipleDegree d)
      (pairedRelationMultiple_hasTop d) v
      (fun z ↦ w (z.2.val.val,z.1))
      (fun z ↦ BasisFiltered.homogeneous_basis b w (z.2.val.val,z.1)) hleading
  have hspan : Submodule.span F (Set.range (fun z ↦ q (v z))) = ⊤ := by
    apply (span_image_eq_top_iff q hq v).mpr
    rw [hker]
    exact hactual
  have he : (fun z ↦ q (v z)) = pairedCoupledClasses d := funext hclass
  rwa [he] at hspan

/-- The full coupled field basis has precisely the claimed monomial residue
classes.  All positive cover degrees, all nonnegative degree splits, and all
coupled lower-weight perturbations allowed by `PairedData` are retained. -/
def pairedCoupledBasis (d : PairedData (K := F) (n := n)) :
    Module.Basis (PairedPowerIndex d.r d.u d.v d.s) F
      (PairedQuotient d.beta d.phi d.a d.b) :=
  Module.Basis.mk (pairedCoupledClasses_linearIndependent d)
    (pairedCoupledClasses_span d).ge

@[simp] theorem pairedCoupledBasis_apply (d : PairedData (K := F) (n := n))
    (z : PairedPowerIndex d.r d.u d.v d.s) :
    pairedCoupledBasis d z = pairedCoupledClasses d z :=
  Module.Basis.mk_apply _ _ _

end PaperVerification.Fermion
