module

public import PaperVerification.FermionDescent
public import PaperVerification.FermionPairedFiniteRing
public import PaperVerification.FermionUniversalCoefficients

/-!
# Closed-point descent for the actual coupled paired classes

The residue-field bases are the proved field bases in the actual scalar
extensions of the original two-sided quotient.  The module is finite by
filtered reduction, and reduced Jacobson descent therefore applies without
an assumption on a presentation kernel.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open Exterior
open scoped TensorProduct

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionPairedDescent_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- Every literal residue-field fiber has the prescribed basis.  Both the
field theorem and the scalar-extension identification are constructed here. -/
theorem pairedCoupledClasses_hasResidueBases (d : PairedData (K := R) (n := n)) :
    HasResidueBases (R := R) (pairedCoupledClasses d) := by
  classical
  intro I hI
  letI : I.IsMaximal := hI
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  let e := pairedQuotientBaseChangeEquiv R (R ⧸ I) d
  let b := pairedCoupledBasis (d.map (algebraMap R (R ⧸ I)))
  refine ⟨b.map e.symm,?_⟩
  intro z
  apply e.injective
  rw [Module.Basis.map_apply,e.apply_symm_apply]
  change b z = e ((1 : R ⧸ I) ⊗ₜ[R] pairedCoupledClasses d z)
  rw [pairedQuotientBaseChangeEquiv_class,pairedCoupledBasis_apply]

/-- The full prescribed paired basis over every reduced Jacobson ring.  The
finiteness and every fiber basis are consequences of the actual data. -/
def pairedReducedJacobsonBasis [IsReduced R] [IsJacobsonRing R]
    (d : PairedData (K := R) (n := n)) :
    Module.Basis (PairedPowerIndex d.r d.u d.v d.s) R
      (PairedQuotient d.beta d.phi d.a d.b) := by
  letI := pairedCoupled_quotient_finite d
  exact basisOfResidueBases (pairedCoupledClasses d) (pairedCoupledClasses_hasResidueBases d)

@[simp] theorem pairedReducedJacobsonBasis_apply [IsReduced R] [IsJacobsonRing R]
    (d : PairedData (K := R) (n := n)) (z : PairedPowerIndex d.r d.u d.v d.s) :
    pairedReducedJacobsonBasis d z = pairedCoupledClasses d z := by
  letI := pairedCoupled_quotient_finite d
  unfold pairedReducedJacobsonBasis
  exact basisOfResidueBases_apply _ _ _

namespace Universal

/-- Specializing the actual universal data recovers the original data,
including every weight and every lower polynomial coefficient. -/
theorem data_specialize (d : PairedData (K := R) (n := n)) :
    (data d).map (specialize d) = d := by
  have hβ : (specialize d) ∘ (data d).beta = d.beta := by
    funext i
    exact specialize_weight d i
  have hφ : (fun i ↦ MvPolynomial.map (specialize d) ((data d).phi i)) = d.phi := by
    funext i
    exact data_specialize_phi d i
  have ha : (fun i ↦ MvPolynomial.map (specialize d) ((data d).a i)) = d.a := by
    funext i
    exact data_specialize_left d i
  have hb : (fun i ↦ MvPolynomial.map (specialize d) ((data d).b i)) = d.b := by
    funext i
    exact data_specialize_right d i
  cases d
  simp only [PairedData.map,data] at hβ hφ ha hb ⊢
  congr 1 <;> first | assumption | rfl

end Universal

/-- Every original base ring receives the actual universal basis.  The
specialization uses the literal tensor/exterior quotient comparison and its
proved formula on the proposed classes. -/
theorem exists_pairedArbitraryRingBasis (d : PairedData (K := R) (n := n)) :
    ∃ b : Module.Basis (PairedPowerIndex d.r d.u d.v d.s) R
        (PairedQuotient d.beta d.phi d.a d.b),
      ∀ z, b z = pairedCoupledClasses d z := by
  classical
  let U := Universal.Ring d
  letI : Algebra U R := (Universal.specialize d).toAlgebra
  let du := Universal.data d
  let ds := du.map (algebraMap U R)
  let bu := pairedReducedJacobsonBasis du
  let e := pairedQuotientBaseChangeEquiv U R du
  have h : ∃ b : Module.Basis (PairedPowerIndex ds.r ds.u ds.v ds.s) R
      (PairedQuotient ds.beta ds.phi ds.a ds.b),
      ∀ z, b z = pairedCoupledClasses ds z := by
    refine ⟨(bu.baseChange R).map e,?_⟩
    intro z
    simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply]
    change pairedQuotientBaseChangeEquiv U R du
      ((1 : R) ⊗ₜ[U] pairedReducedJacobsonBasis du
        (show PairedPowerIndex du.r du.u du.v du.s from z)) =
      pairedCoupledClasses (du.map (algebraMap U R))
        (show PairedPowerIndex du.r du.u du.v du.s from z)
    rw [pairedReducedJacobsonBasis_apply,pairedQuotientBaseChangeEquiv_class]
  have hd : ds=d := Universal.data_specialize d
  exact hd ▸ h

/-- The full coupled paired basis over the original arbitrary commutative
ring.  Its index is the valid-word rectangle index; the final paper-facing
index correspondence is handled separately. -/
def pairedArbitraryRingBasis (d : PairedData (K := R) (n := n)) :
    Module.Basis (PairedPowerIndex d.r d.u d.v d.s) R
      (PairedQuotient d.beta d.phi d.a d.b) :=
  Classical.choose (exists_pairedArbitraryRingBasis d)

@[simp] theorem pairedArbitraryRingBasis_apply (d : PairedData (K := R) (n := n))
    (z : PairedPowerIndex d.r d.u d.v d.s) :
    pairedArbitraryRingBasis d z = pairedCoupledClasses d z :=
  Classical.choose_spec (exists_pairedArbitraryRingBasis d) z

end PaperVerification.Fermion
