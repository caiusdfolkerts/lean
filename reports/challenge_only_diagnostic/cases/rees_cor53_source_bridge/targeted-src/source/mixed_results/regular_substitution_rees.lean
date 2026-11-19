module
public import mixed_results.regular_substitution_selected
public import mixed_results.flat_rees_base_change
public import shared_results.part018_tensor_koszul_coefficient_equiv

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.RegularSubstitutionRees -/
section

/-! # Regular substitution of the literal Rees homology algebra

The coefficient in auxiliary degree `m` remains the actual ideal power.
Flat base change identifies the full Rees algebra with the Rees algebra
of the extended ideal and respects this degree. The resulting generation
comparison concerns actual cycles in the original Koszul complexes.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.PolynomialRegularSubstitution
open Classical CommAlg MvPolynomial FlatReesBaseChange
open scoped TensorProduct
universe u
variable {K Y V : Type u} [Field K] [Fintype V] [LinearOrder V]
  [Fintype Y] [LinearOrder Y]
local notation "S" => MvPolynomial V K
local notation "R" => MvPolynomial Y K
variable (f : V → (MvPolynomial Y K)) (w : V → ℕ) (hhom : ∀ v,(f v).IsHomogeneous (w v))
  (hreg : RegularFamilyKoszul.IsRegularFamily f) (hw : ∀ v,0<w v)
variable [Algebra (MvPolynomial V K) (MvPolynomial Y K)] [IsScalarTower K (MvPolynomial V K) (MvPolynomial Y K)]
  (hvars : ∀ v, algebraMap (MvPolynomial V K) (MvPolynomial Y K) (X v)=f v)
variable (I : Ideal (MvPolynomial V K))
local notation "J" => I.map (algebraMap S R)

def coefficientReesBaseChangeEquiv :
    (coefficients I ⊗[S] R) ≃ₐ[K] coefficients J := by
  letI := substitution_free f w hhom hreg hw hvars
  exact ((Algebra.TensorProduct.comm S (coefficients I) R).restrictScalars K).trans
    ((FlatReesBaseChange.algebraEquiv I).restrictScalars K)

include hhom hreg hw hvars in
theorem coefficientReesBaseChangeEquiv_projection (m : ℕ)
    (z : coefficients I ⊗[S] R) :
    coefficientReesBaseChangeEquiv f w hhom hreg hw hvars I
      (baseCoefficientProjection (Y := Y) (coefficients I) (projection I m) z)=
      projection J m (coefficientReesBaseChangeEquiv f w hhom hreg hw hvars I z) := by
  letI := substitution_free f w hhom hreg hw hvars
  have hc : ∀ z : coefficients I ⊗[S] R,
      TensorProduct.comm S (coefficients I) R (((projection I m).rTensor R) z)=
        ((projection I m).lTensor R) (TensorProduct.comm S (coefficients I) R z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul a r => rfl
  change FlatReesBaseChange.linearEquiv I
    (TensorProduct.comm S (coefficients I) R (((projection I m).rTensor R) z))=_
  rw [hc]
  exact FlatReesBaseChange.linearEquiv_projection I m _

include hhom hreg hw hvars in
theorem coefficientReesBaseChangeEquiv_variable (y : Y) :
    coefficientReesBaseChangeEquiv f w hhom hreg hw hvars I
      ((1 : coefficients I) ⊗ₜ[S] (X y : R))=
      algebraMap R (coefficients J) (X y) := by
  letI := substitution_free f w hhom hreg hw hvars
  change FlatReesBaseChange.linearEquiv I ((X y : R) ⊗ₜ[S] (1 : coefficients I))=_
  rw [← single_zero_one I,linearEquiv_tmul_single]
  apply Subtype.ext
  change AddMonoidAlgebra.single 0
      (powerEquiv I 0 ((X y : R) ⊗ₜ[S] ⟨1,powerPiece_one I⟩)).val=
    algebraMap R (AddMonoidAlgebra R ℕ) (X y)
  rw [powerEquiv_tmul,map_one,mul_one]
  rfl

/-- The selected classes use the range of the literal coefficient
projection; in particular `m=1` means Rees degree one. -/
def coefficientReesClasses {Z : Type u} [Fintype Z] [LinearOrder Z]
    (L : Ideal (MvPolynomial Z K)) (m : ℕ) :
    Set ((TensorExteriorKoszul.parityDifferential (K := K)
      (fun z : Z => algebraMap (MvPolynomial Z K) (coefficients L) (X z))).Homology) :=
  (TensorExteriorKoszul.parityDifferential (K := K)
    (fun z : Z => algebraMap (MvPolynomial Z K) (coefficients L) (X z))).classesFrom
      (LinearMap.range (KoszulCoefficientProjection.tensor (V := Z)
        ((projection L m).restrictScalars K)))

attribute [local irreducible] coefficientReesBaseChangeEquiv
  TensorKoszulCoefficientEquiv.homologyEquiv TensorExteriorKoszul.parityDifferential
  ParityDifferential.homologyRing ParityDifferential.homologyAlgebra

include hhom hreg hw hvars in
/-- **Rees generation under regular substitution.** For every actual
ideal and every selected auxiliary degree, generation is preserved by
the substitution. Neither a Tor comparison nor generation is a premise. -/
theorem coefficientRees_generation_iff (m : ℕ) :
    Algebra.adjoin K (coefficientReesClasses I m)=⊤ ↔
      Algebra.adjoin K (coefficientReesClasses J m)=⊤ := by
  have hsub := selectedGeneration_iff (K := K) (V := V) (Y := Y)
    (A := coefficients I) f w hhom hreg hw hvars
    (projection I m) (projection_idempotent I m)
  let e := coefficientReesBaseChangeEquiv f w hhom hreg hw hvars I
  let x : Y → coefficients I ⊗[S] R := fun y => (1 : coefficients I) ⊗ₜ[S] (X y : R)
  let y : Y → coefficients J := fun y => algebraMap R (coefficients J) (X y)
  have hxy : ∀ y,e (x y)=algebraMap R (coefficients J) (X y) :=
    coefficientReesBaseChangeEquiv_variable f w hhom hreg hw hvars I
  have hclasses := TensorKoszulCoefficientEquiv.homologyEquiv_selectedClasses
    (K := K) (A := coefficients I ⊗[S] R) (B := coefficients J) (V := Y) e x y hxy
    (baseCoefficientProjection (Y := Y) (coefficients I) (projection I m))
    ((projection J m).restrictScalars K)
    (coefficientReesBaseChangeEquiv_projection f w hhom hreg hw hvars I m)
  have hbase := @adjoin_eq_top_iff_of_algEquiv K
    (TensorExteriorKoszul.parityDifferential (K := K) x).Homology
    (TensorExteriorKoszul.parityDifferential (K := K) y).Homology
    inferInstance
    (ParityDifferential.homologyRing (TensorExteriorKoszul.parityDifferential (K := K) x))
    (ParityDifferential.homologyRing (TensorExteriorKoszul.parityDifferential (K := K) y))
    (ParityDifferential.homologyAlgebra (TensorExteriorKoszul.parityDifferential (K := K) x))
    (ParityDifferential.homologyAlgebra (TensorExteriorKoszul.parityDifferential (K := K) y))
    (TensorKoszulCoefficientEquiv.homologyEquiv (K := K) (V := Y) e x y hxy)
    ((TensorExteriorKoszul.parityDifferential (K := K) x).classesFrom
      (LinearMap.range (KoszulCoefficientProjection.tensor (V := Y)
        (baseCoefficientProjection (Y := Y) (coefficients I) (projection I m)))))
    ((TensorExteriorKoszul.parityDifferential (K := K) y).classesFrom
      (LinearMap.range (KoszulCoefficientProjection.tensor (V := Y)
        ((projection J m).restrictScalars K)))) hclasses
  dsimp only [x, y] at hbase
  have hresult := hsub.trans hbase
  dsimp only [coefficientReesClasses]
  exact hresult

end FourPapers.PolynomialRegularSubstitution

end
end
end

end
