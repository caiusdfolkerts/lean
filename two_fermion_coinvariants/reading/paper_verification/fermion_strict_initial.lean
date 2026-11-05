module

public import PaperVerification.FermionFilteredInitial
public import PaperVerification.FermionStrictDescent
public import PaperVerification.FermionStrictHighestForms

/-!
# The actual strict initial ideal for zero exterior weight

Highest forms of all actual two-sided relation multiples and the proved
strict basis give equality of the full initial relation submodule with the
homogeneous strict power ideal. No equality of dimensions or assumed Rees
comparison is used to identify the actual kernels.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionStrictInitial_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem strictPower_kernel_eq_relationSpan (d : StrictData (K := R) (n := n)) :
    (((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ R).toLinearMap).ker=
      Submodule.span R (Set.range (basisRelationMultiple (superMonomialBasis (K := R))
        (strictPowerFiniteRelation d))) := strict_quotient_kernel_eq_relationSpan R d.power

theorem strict_initialSubmodule_eq_power (d : StrictData (K := R) (n := n)) :
    BasisFiltered.initialSubmodule (superMonomialBasis (K := R)) (strictSuperWeight d)
      (twoSidedIdealSubmodule (strictIdeal d.beta d.phi))=
        twoSidedIdealSubmodule (strictIdeal d.beta (fun i ↦ X i^d.r i)) := by
  classical
  let b := superMonomialBasis (K := R) (n := n)
  let w := strictSuperWeight d
  let v (z : StrictPowerIndex d.r) : SuperRing R n := b (z.2.val.val,z.1)
  let q := ((strictIdeal d.beta d.phi).ringCon.mkₐ R).toLinearMap
  let q₀ := ((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ R).toLinearMap
  let f := basisRelationMultiple b (strictFiniteRelation d)
  let g := basisRelationMultiple b (strictPowerFiniteRelation d)
  have hker : q.ker=Submodule.span R (Set.range f) := strict_quotient_kernel_eq_relationSpan R d
  have hker₀ : q₀.ker=Submodule.span R (Set.range g) := strictPower_kernel_eq_relationSpan d
  have hclass (z : StrictPowerIndex d.r) : q (v z)=strictArbitraryRingBasis d z := by
    rw [strictArbitraryRingBasis_apply]
    change q (superMonomialBasis (z.2.val.val,z.1))=_
    rw [superMonomialBasis_apply]
    rfl
  have hclass₀ (z : StrictPowerIndex d.r) : q₀ (v z)=strictArbitraryRingBasis d.power z := by
    rw [strictArbitraryRingBasis_apply]
    change q₀ (superMonomialBasis (z.2.val.val,z.1))=_
    rw [superMonomialBasis_apply]
    rfl
  have hspan₀ : Submodule.span R (Set.range (fun z ↦ q₀ (v z)))=⊤ := by
    rw [funext hclass₀]
    exact (strictArbitraryRingBasis d.power).span_eq
  have hspan : Submodule.span R (Set.range v)⊔Submodule.span R (Set.range g)=⊤ := by
    rw [←hker₀]
    exact (span_image_eq_top_iff q₀
      ((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ_surjective (α := R)) v).mp hspan₀
  have hli : LinearIndependent R (fun z ↦ q (v z)) := by
    rw [funext hclass]
    exact (strictArbitraryRingBasis d).linearIndependent
  have he := BasisFiltered.initialSubmodule_eq_of_basis b w f g
    (strictRelationMultipleDegree d) (strictRelationMultiple_hasTop d)
    v (fun z ↦ w (z.2.val.val,z.1))
    (fun z ↦ BasisFiltered.homogeneous_basis b w (z.2.val.val,z.1)) hspan q hker hli
  rw [←hker₀] at he
  simpa only [q,q₀,quotient_kernel_eq_twoSidedIdealSubmodule] using he

end PaperVerification.Fermion
