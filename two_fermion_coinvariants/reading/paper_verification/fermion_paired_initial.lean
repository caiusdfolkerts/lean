module

public import PaperVerification.FermionFilteredInitial
public import PaperVerification.FermionHomogenizedFamily

/-!
# The actual paired initial relation equality

The filtration is the literal integer-weight filtration of polynomial/exterior
monomials.  Its initial relation submodule is proved equal to the homogeneous
power ideal by bounded reduction and the proved proposed basis.  It is not
identified through an assumed equality of dimensions.

Packaging the resulting successive
quotients as their total associated-graded algebra remains separate.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionPairedInitial_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem paired_initialSubmodule_eq_power (d : PairedData (K := R) (n := n)) :
    BasisFiltered.initialSubmodule (superMonomialBasis (K := R))
      (superMonomialWeight (coveringWeight d.r) (pairedOddWeight d))
      (twoSidedIdealSubmodule (pairedIdeal d.beta d.phi d.a d.b)) =
        twoSidedIdealSubmodule (pairedIdeal d.beta (fun i ↦ X i^d.r i)
          (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)) := by
  classical
  let b := superMonomialBasis (K := R) (n := n)
  let w := superMonomialWeight (coveringWeight d.r) (pairedOddWeight d)
  let v (z : PairedPowerIndex d.r d.u d.v d.s) : SuperRing R n := b (z.2.val.val,z.1)
  let q := ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R).toLinearMap
  let q₀ := ((pairedIdeal d.beta (fun i ↦ X i^d.r i)
    (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ R).toLinearMap
  let f := basisRelationMultiple b (pairedFiniteRelation d)
  let g := basisRelationMultiple b (pairedPowerFiniteRelation d)
  have hker : q.ker=Submodule.span R (Set.range f) :=
    paired_quotient_kernel_eq_relationSpan R d
  have hker₀ : q₀.ker=Submodule.span R (Set.range g) := by
    rw [show q₀.ker = twoSidedIdealSubmodule (pairedIdeal d.beta
        (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)) from
      quotient_kernel_eq_twoSidedIdealSubmodule _]
    rw [← pairedPowerFiniteRelation_ideal d,twoSidedIdealSubmodule_span b]
  have hclass (z : PairedPowerIndex d.r d.u d.v d.s) :
      q (v z) = pairedArbitraryRingBasis d z := by
    rw [pairedArbitraryRingBasis_apply]
    change q (superMonomialBasis (z.2.val.val,z.1)) = _
    rw [superMonomialBasis_apply]
    rfl
  have hclass₀ (z : PairedPowerIndex d.r d.u d.v d.s) :
      q₀ (v z) = pairedArbitraryRingBasis d.power z := by
    rw [pairedArbitraryRingBasis_apply]
    change q₀ (superMonomialBasis (z.2.val.val,z.1)) = _
    rw [superMonomialBasis_apply]
    rfl
  have hspan₀ : Submodule.span R (Set.range (fun z ↦ q₀ (v z))) = ⊤ := by
    rw [funext hclass₀]
    exact (pairedArbitraryRingBasis d.power).span_eq
  have hspan : Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g)=⊤ := by
    rw [← hker₀]
    exact (span_image_eq_top_iff q₀
      ((pairedIdeal d.beta (fun i ↦ X i^d.r i)
        (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ_surjective (α := R)) v).mp hspan₀
  have hli : LinearIndependent R (fun z ↦ q (v z)) := by
    rw [funext hclass]
    exact (pairedArbitraryRingBasis d).linearIndependent
  have he := BasisFiltered.initialSubmodule_eq_of_basis b w f g
    (pairedRelationMultipleDegree d) (pairedRelationMultiple_hasTop d)
    v (fun z ↦ w (z.2.val.val,z.1))
    (fun z ↦ BasisFiltered.homogeneous_basis b w (z.2.val.val,z.1))
    hspan q hker hli
  rw [← hker₀] at he
  simpa only [q,q₀,quotient_kernel_eq_twoSidedIdealSubmodule] using he

end PaperVerification.Fermion
