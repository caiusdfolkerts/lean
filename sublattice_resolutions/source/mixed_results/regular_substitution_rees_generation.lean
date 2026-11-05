module
public import mixed_results.regular_substitution_rees
public import mixed_results.part001
public import shared_results.part018_rees_standard_identification

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.RegularSubstitutionReesGeneration -/
section

/-! # Corollary 5.8: actual Rees homology after regular substitution -/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FlatReesBaseChange PolynomialRegularSubstitution
open scoped TensorProduct
universe u
variable {K : Type u} [Field K] {d : ℕ} {n : Fin d → ℕ}
  (E : Finset (FiniteTuple n))
local notation "I" => finiteSublatticeIdeal n (k := K) E

def finitePowerCoefficientEquiv : finiteReesImage E K ≃ₐ[K] coefficients I :=
  (finiteReesStandardEquiv E).trans ((polynomialEquiv I).restrictScalars K).symm

@[simp] theorem finitePowerCoefficientEquiv_val (x : finiteReesImage E K) :
    (finitePowerCoefficientEquiv E x).val=(finiteReesStandardEquiv E x).val.toFinsupp := rfl

theorem finitePowerCoefficientEquiv_basis_val (a : finiteReesExponentMonoid.{u} E) :
    (finitePowerCoefficientEquiv E (finiteReesImageBasis E K a)).val=
      AddMonoidAlgebra.single (a.val none) (monomial (finiteReesFineExponent a) 1) := by
  rw [finitePowerCoefficientEquiv_val,finiteReesStandardEquiv_basis,Polynomial.toFinsupp_monomial]

theorem finitePowerCoefficientEquiv_baseVariable (v : (FiniteVariable.{u} n)) :
    finitePowerCoefficientEquiv E (finiteReesBaseVariable E v)=
      algebraMap (MvPolynomial (FiniteVariable.{u} n) K) (coefficients I) (X v) := by
  apply Subtype.ext
  rw [finitePowerCoefficientEquiv_val,finiteReesStandardEquiv_baseVariable_val]
  rfl

def finitePowerCoefficientTensorEquiv : ReesKoszulTensorAlgebra E K ≃ₐ[K]
    (coefficients I ⊗[K] Simplicial.Ambient (FiniteVariable.{u} n) K) :=
  TensorKoszulCoefficientEquiv.algebra (finitePowerCoefficientEquiv E)

theorem finitePowerCoefficientTensorEquiv_d (hE : finiteLatticeClosed n E)
    (z : ReesKoszulTensorAlgebra E K) :
    finitePowerCoefficientTensorEquiv E ((reesKoszulTensorDGA (k := K) hE).d z)=
      (TensorExteriorKoszul.parityDifferential (K := K)
        (fun v : (FiniteVariable.{u} n) => algebraMap (MvPolynomial (FiniteVariable.{u} n) K) (coefficients I) (X v))).d
        (finitePowerCoefficientTensorEquiv E z) := by
  rw [reesKoszulTensorDGA_d]
  have he : (finitePowerCoefficientTensorEquiv E).toLinearMap.comp
      reesKoszulTensorDifferential=
    (TensorExteriorKoszul.differential (K := K) (M := coefficients I)
      (fun v : (FiniteVariable.{u} n) => algebraMap (MvPolynomial (FiniteVariable.{u} n) K) (coefficients I) (X v))).comp
      (finitePowerCoefficientTensorEquiv E).toLinearMap := by
    apply TensorProduct.ext'
    intro a z
    change finitePowerCoefficientTensorEquiv E
      (reesKoszulTensorDifferential (a ⊗ₜ[K] z))=_
    rw [reesKoszulTensorDifferential_tmul,map_sum]
    change _=TensorExteriorKoszul.differential (K := K) (M := coefficients I)
      (fun v : (FiniteVariable.{u} n) => algebraMap (MvPolynomial (FiniteVariable.{u} n) K) (coefficients I) (X v))
      (finitePowerCoefficientEquiv E a ⊗ₜ[K] z)
    rw [TensorExteriorKoszul.differential_tmul]
    apply Finset.sum_congr rfl
    intro v hv
    change finitePowerCoefficientEquiv E (finiteReesBaseVariable E v*a) ⊗ₜ[K]
      Simplicial.contraction v z=_
    rw [map_mul,finitePowerCoefficientEquiv_baseVariable]
    rfl
  exact LinearMap.congr_fun he z

theorem finitePowerCoefficientTensorEquiv_degree (m : ℕ)
    (z : ReesKoszulTensorAlgebra E K) (hz : z∈actualReesDegreePiece (E := E) m) :
    finitePowerCoefficientTensorEquiv E z∈LinearMap.range
      (KoszulCoefficientProjection.tensor («V» := (FiniteVariable.{u} n)) ((projection I m).restrictScalars K)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨a,F⟩,ha,rfl⟩ := hz
      change a.val none=m at ha
      refine ⟨finitePowerCoefficientTensorEquiv E (reesTensorBasis ⟨a,F⟩),?_⟩
      rw [reesTensorBasis,Module.Basis.tensorProduct_apply]
      change projection I m (finitePowerCoefficientEquiv E (finiteReesImageBasis E K a))
          ⊗ₜ[K] Simplicial.basis F=
        finitePowerCoefficientEquiv E (finiteReesImageBasis E K a) ⊗ₜ[K] Simplicial.basis F
      congr 1
      apply Subtype.ext
      change AddMonoidAlgebra.single m
        ((finitePowerCoefficientEquiv E (finiteReesImageBasis E K a)).val.coeff m)=_
      rw [finitePowerCoefficientEquiv_basis_val,ha,AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_same]
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ r ih

/-- The proved Theorem 1.2 applies to the coefficientwise Rees algebra
with its literal degree-one projection. -/
theorem finiteCoefficientRees_generated (hE : finiteLatticeClosed n E) :
    Algebra.adjoin K (coefficientReesClasses I 1)=⊤ := by
  let D := reesKoszulTensorDGA (k := K) hE
  let D' := TensorExteriorKoszul.parityDifferential (K := K)
    (fun v : (FiniteVariable.{u} n) => algebraMap (MvPolynomial (FiniteVariable.{u} n) K) (coefficients I) (X v))
  let e := ParityDifferential.homologyEquiv D D'
    (finitePowerCoefficientTensorEquiv E) (finitePowerCoefficientTensorEquiv_d E hE)
  apply adjoin_eq_top_of_algEquiv e (actualFirstReesClasses (k := K) hE)
    (coefficientReesClasses I 1) ?_ (reesKoszulHomology_generated_in_degree_one hE)
  rintro z ⟨x,⟨a,ha,rfl⟩,rfl⟩
  exact ⟨ParityDifferential.cyclesEquiv D D' (finitePowerCoefficientTensorEquiv E)
    (finitePowerCoefficientTensorEquiv_d E hE) a,
    finitePowerCoefficientTensorEquiv_degree E 1 a.val ha,rfl⟩

variable {Y : Type u} [Fintype Y] [LinearOrder Y]
  (f : (FiniteVariable.{u} n) → MvPolynomial Y K) (w : (FiniteVariable.{u} n) → ℕ)
  (hhom : ∀ v,(f v).IsHomogeneous (w v))
  (hreg : RegularFamilyKoszul.IsRegularFamily f) (hw : ∀ v,0<w v)

include hhom hreg hw in
/-- **Corollary 5.8, homology-algebra clause.** Every finite sublattice,
every positive homogeneous regular substitution and every field are
allowed. The ideal is generated by the literal products of the supplied
regular-sequence elements; the selected classes have actual Rees degree one. -/
theorem corollary58_generation (hE : finiteLatticeClosed n E) :
    Algebra.adjoin K
      (coefficientReesClasses (substitutedSublatticeIdeal f E) 1)=⊤ := by
  letI := substitutionAlgebra f
  letI : IsScalarTower K (MvPolynomial (FiniteVariable.{u} n) K) (MvPolynomial Y K) := IsScalarTower.of_algHom (MvPolynomial.aeval f)
  have h := (coefficientRees_generation_iff f w hhom hreg hw
    (fun v => MvPolynomial.aeval_X f v) I 1).mp
    (finiteCoefficientRees_generated E hE)
  have hI : substitutedSublatticeIdeal f E =
      Ideal.map (algebraMap (MvPolynomial (FiniteVariable.{u} n) K) (MvPolynomial Y K)) I :=
    substitutedSublatticeIdeal_eq_map f E
  exact (congrArg (fun L : Ideal (MvPolynomial Y K) =>
    Algebra.adjoin K (coefficientReesClasses L 1) = ⊤) hI).mpr h

end FourPapers.Sublattice

end
end
end

end
