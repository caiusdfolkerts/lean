module
public import mixed_results.regular_substitution_graph_contraction
public import mixed_results.koszul_family_elimination

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.RegularSubstitutionGraphCoordinates -/
section

/-! # The regular substitution graph complex in literal tensor coordinates -/

section
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.PolynomialRegularSubstitution
open Classical CommAlg MvPolynomial HomologicalPerturbation
open scoped TensorProduct
universe u
variable {K Y V : Type u} [Field K] [Fintype V] [LinearOrder V]
local notation "S" => MvPolynomial V K
local notation "R" => MvPolynomial Y K
variable (f : V → (MvPolynomial Y K)) (w : V → ℕ) (hhom : ∀ v, (f v).IsHomogeneous (w v))
  (hreg : RegularFamilyKoszul.IsRegularFamily f) (hw : ∀ v, 0 < w v)
variable [Algebra (MvPolynomial V K) (MvPolynomial Y K)] [IsScalarTower K (MvPolynomial V K) (MvPolynomial Y K)]
  (hvars : ∀ v, algebraMap (MvPolynomial V K) (MvPolynomial Y K) (X v)=f v)
variable (A : Type u) [CommRing A] [Algebra (MvPolynomial V K) A] [Algebra K A] [IsScalarTower K (MvPolynomial V K) A]
local notation "E" => Simplicial.Ambient V K

def graphCoordinates :
    (A ⊗[S] PolynomialModuleResolution.Bar («R» := K) (V := V) R) ≃ₗ[A]
      ((A ⊗[K] R) ⊗[K] E) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange K S A A (R ⊗[K] E)).trans
    (TensorProduct.AlgebraTensorModule.assoc K K A A R E).symm

@[simp] theorem graphCoordinates_tmul (a : A) (s : S) (r : R) (z : E) :
    graphCoordinates (K := K) (V := V) A (a ⊗ₜ[S] (s ⊗ₜ[K] (r ⊗ₜ[K] z)))=
      ((s • a) ⊗ₜ[K] r) ⊗ₜ[K] z := rfl

@[simp] theorem graphCoordinates_symm_tmul (a : A) (r : R) (z : E) :
    (graphCoordinates (K := K) (V := V) A).symm ((a ⊗ₜ[K] r) ⊗ₜ[K] z)=
      a ⊗ₜ[S] (1 ⊗ₜ[K] (r ⊗ₜ[K] z)) := rfl

def coefficientQuotient : (A ⊗[K] R) →ₐ[K] (A ⊗[S] R) :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] R).restrictScalars K)
    ((Algebra.TensorProduct.includeRight : R →ₐ[S] A ⊗[S] R).restrictScalars K)
    (fun _ _ => Commute.all _ _)

@[simp] theorem coefficientQuotient_tmul (a : A) (r : R) :
    coefficientQuotient (V := V) (Y := Y) A (a ⊗ₜ[K] r)=a ⊗ₜ[S] r := by
  rw [coefficientQuotient,Algebra.TensorProduct.lift_tmul]
  change (a ⊗ₜ[S] (1 : R))*((1 : A) ⊗ₜ[S] r)=_
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

def graphFamily (v : V) : A ⊗[K] R :=
  algebraMap S A (X v) ⊗ₜ[K] 1-(1 : A) ⊗ₜ[K] f v

def graphTensorContraction : LinearContraction
    («R» := K) (M := (A ⊗[K] R) ⊗[K] E) (H := A ⊗[S] R) :=
  ((graphBaseChangeContraction f w hhom hreg hw hvars A).changeSource
    (graphCoordinates (K := K) (V := V) A)).restrictScalars K

theorem graphTensorContraction_d_tmul (a : A) (r : R) (z : E) :
    (graphTensorContraction f w hhom hreg hw hvars A).d ((a ⊗ₜ[K] r) ⊗ₜ[K] z)=
      TensorExteriorKoszul.differential (K := K) (M := A ⊗[K] R)
        (graphFamily f A) ((a ⊗ₜ[K] r) ⊗ₜ[K] z) := by
  change graphCoordinates A
    (a ⊗ₜ[S] (graphContraction f w hhom hreg hw hvars).d
      (1 ⊗ₜ[K] (r ⊗ₜ[K] z)))=_
  rw [graphContraction_d,PolynomialModuleResolution.differential,LinearMap.sub_apply,
    PolynomialModuleResolution.externalDifferential_tmul,
    PolynomialModuleResolution.internalDifferential_tmul,
    TensorProduct.tmul_sub,TensorProduct.tmul_sum,TensorProduct.tmul_sum,
    map_sub,map_sum,map_sum,TensorExteriorKoszul.differential_tmul]
  have hs := Finset.sum_sub_distrib (s := Finset.univ)
    (fun v : V => graphCoordinates (K := K) (V := V) (Y := Y) A
      (a ⊗ₜ[S] (((X v : S) * 1) ⊗ₜ[K] (r ⊗ₜ[K] Simplicial.contraction v z))))
    (fun v : V => graphCoordinates (K := K) (V := V) (Y := Y) A
      (a ⊗ₜ[S] ((1 : S) ⊗ₜ[K] (((X v : S) • r) ⊗ₜ[K] Simplicial.contraction v z))))
  refine hs.symm.trans ?_
  apply Finset.sum_congr rfl
  intro v hv
  rw [graphCoordinates_tmul,graphCoordinates_tmul]
  change (((X v*1 : S) • a) ⊗ₜ[K] r) ⊗ₜ[K] Simplicial.contraction v z-
      ((1 : S) • a ⊗ₜ[K] (X v • r)) ⊗ₜ[K] Simplicial.contraction v z=
    (graphFamily f A v*(a ⊗ₜ[K] r)) ⊗ₜ[K] Simplicial.contraction v z
  simp only [mul_one,one_smul,graphFamily,sub_mul,Algebra.TensorProduct.tmul_mul_tmul,
    mul_one,one_mul,TensorProduct.sub_tmul]
  congr 2
  · exact congrArg (fun b : A => b ⊗ₜ[K] r) (Algebra.smul_def (X v : S) a)
  · exact congrArg (fun t : R => a ⊗ₜ[K] t)
      ((Algebra.smul_def (X v : S) r).trans (congrArg (fun t : R => t * r) (hvars v)))

theorem graphTensorContraction_d :
    (graphTensorContraction f w hhom hreg hw hvars A).d=
      TensorExteriorKoszul.differential (K := K) (M := A ⊗[K] R) (graphFamily f A) := by
  apply TensorProduct.ext'
  intro x z
  induction x using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul,map_zero]
  | add x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
  | tmul a r => exact graphTensorContraction_d_tmul f w hhom hreg hw hvars A a r z

theorem graphTensorContraction_projection :
    (graphTensorContraction f w hhom hreg hw hvars A).projection=
      (KoszulAugmentation.augmentation (V := V) (coefficientQuotient (V := V) (Y := Y) A)).toLinearMap := by
  apply TensorProduct.ext'
  intro x z
  induction x using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul,map_zero]
  | add x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
  | tmul a r =>
      have he : (graphTensorContraction f w hhom hreg hw hvars A).projection.comp
          (TensorProduct.mk K (A ⊗[K] R) E (a ⊗ₜ[K] r))=
        (KoszulAugmentation.augmentation (V := V) (coefficientQuotient (V := V) (Y := Y) A)).toLinearMap.comp
          (TensorProduct.mk K (A ⊗[K] R) E (a ⊗ₜ[K] r)) := by
        apply (Simplicial.basis (V := V) (k := K)).ext
        intro F
        change a ⊗ₜ[S] (graphContraction f w hhom hreg hw hvars).projection
          (1 ⊗ₜ[K] (r ⊗ₜ[K] Simplicial.basis F))=
            KoszulAugmentation.augmentation (coefficientQuotient (V := V) (Y := Y) A)
              ((a ⊗ₜ[K] r) ⊗ₜ[K] Simplicial.basis F)
        rw [graphContraction_projection_tmul,KoszulAugmentation.augmentation_tmul_basis,
          coefficientQuotient_tmul,map_one,one_mul]
        split_ifs <;> simp only [TensorProduct.tmul_zero]
      exact LinearMap.congr_fun he z


end FourPapers.PolynomialRegularSubstitution

end
end
end

end
