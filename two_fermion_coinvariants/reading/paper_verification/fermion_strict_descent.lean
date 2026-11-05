module

public import PaperVerification.FermionStrictBaseChange
public import PaperVerification.FermionStrictCoupledBasis
public import PaperVerification.FermionPairedDescent

/-!
# The full strict basis over the original arbitrary coefficient ring

The actual finite quotient has the proved field basis at every maximal
residue field. Reduced Jacobson descent gives a universal basis, and the
literal quotient base-change comparison transports its exact classes to
the original ring, including rings with nilpotents and the zero ring.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open Exterior
open scoped TensorProduct

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionStrictDescent_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem strictCoupledClasses_hasResidueBases (d : StrictData (K := R) (n := n)) :
    HasResidueBases (R := R) (strictCoupledClasses d) := by
  classical
  intro I hI
  letI : I.IsMaximal := hI
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  let e := strictQuotientBaseChangeEquiv R (R ⧸ I) d
  let b := strictCoupledBasis (d.map (algebraMap R (R ⧸ I)))
  refine ⟨b.map e.symm,?_⟩
  intro z
  apply e.injective
  rw [Module.Basis.map_apply,e.apply_symm_apply]
  change b z=e ((1 : R ⧸ I) ⊗ₜ[R] strictCoupledClasses d z)
  rw [strictQuotientBaseChangeEquiv_class,strictCoupledBasis_apply]

def strictReducedJacobsonBasis [IsReduced R] [IsJacobsonRing R]
    (d : StrictData (K := R) (n := n)) :
    Module.Basis (StrictPowerIndex d.r) R (StrictQuotient d.beta d.phi) := by
  letI := strictCoupled_quotient_finite d
  exact basisOfResidueBases (strictCoupledClasses d) (strictCoupledClasses_hasResidueBases d)

@[simp] theorem strictReducedJacobsonBasis_apply [IsReduced R] [IsJacobsonRing R]
    (d : StrictData (K := R) (n := n)) (z : StrictPowerIndex d.r) :
    strictReducedJacobsonBasis d z=strictCoupledClasses d z := by
  letI := strictCoupled_quotient_finite d
  unfold strictReducedJacobsonBasis
  exact basisOfResidueBases_apply _ _ _

namespace Universal

abbrev StrictRing (d : StrictData (K := R) (n := n)) := Ring d.pairedExtension

/-- The universal coefficient ring already contains all strict phi
coefficients and weights. The unused paired prefactor variables impose no
condition on this strict datum and are harmless polynomial parameters. -/
def strictData (d : StrictData (K := R) (n := n)) :
    StrictData (K := StrictRing d) (n := n) where
  positive_n := d.positive_n
  r := d.r
  positive_r := d.positive_r
  beta := (data d.pairedExtension).beta
  allowed_weights := (data d.pairedExtension).allowed_weights
  phi := (data d.pairedExtension).phi
  highest_phi := (data d.pairedExtension).highest_phi

theorem strictData_specialize (d : StrictData (K := R) (n := n)) :
    (strictData d).map (specialize d.pairedExtension)=d := by
  have hβ : (specialize d.pairedExtension) ∘ (strictData d).beta=d.beta := by
    funext i
    exact specialize_weight d.pairedExtension i
  have hφ : (fun i ↦ MvPolynomial.map (specialize d.pairedExtension)
      ((strictData d).phi i))=d.phi := by
    funext i
    exact data_specialize_phi d.pairedExtension i
  cases d
  simp only [StrictData.map,strictData,data,StrictData.pairedExtension] at hβ hφ ⊢
  congr 1 <;> first | assumption | rfl

end Universal

theorem exists_strictArbitraryRingBasis (d : StrictData (K := R) (n := n)) :
    ∃ b : Module.Basis (StrictPowerIndex d.r) R (StrictQuotient d.beta d.phi),
      ∀ z,b z=strictCoupledClasses d z := by
  classical
  let U := Universal.StrictRing d
  letI : Algebra U R := (Universal.specialize d.pairedExtension).toAlgebra
  let du := Universal.strictData d
  let ds := du.map (algebraMap U R)
  let bu := strictReducedJacobsonBasis du
  let e := strictQuotientBaseChangeEquiv U R du
  have h : ∃ b : Module.Basis (StrictPowerIndex ds.r) R (StrictQuotient ds.beta ds.phi),
      ∀ z,b z=strictCoupledClasses ds z := by
    refine ⟨(bu.baseChange R).map e,?_⟩
    intro z
    simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply]
    change strictQuotientBaseChangeEquiv U R du
      ((1 : R) ⊗ₜ[U] strictReducedJacobsonBasis du
        (show StrictPowerIndex du.r from z)) =
      strictCoupledClasses (du.map (algebraMap U R)) (show StrictPowerIndex du.r from z)
    rw [strictReducedJacobsonBasis_apply,strictQuotientBaseChangeEquiv_class]
  have hd : ds=d := Universal.strictData_specialize d
  exact hd ▸ h

/-- The unrestricted original-ring strict basis, before reindexing by the
paper's ordered pair of exterior supports. -/
def strictArbitraryRingBasis (d : StrictData (K := R) (n := n)) :
    Module.Basis (StrictPowerIndex d.r) R (StrictQuotient d.beta d.phi) :=
  Classical.choose (exists_strictArbitraryRingBasis d)

@[simp] theorem strictArbitraryRingBasis_apply (d : StrictData (K := R) (n := n))
    (z : StrictPowerIndex d.r) : strictArbitraryRingBasis d z=strictCoupledClasses d z :=
  Classical.choose_spec (exists_strictArbitraryRingBasis d) z

end PaperVerification.Fermion
