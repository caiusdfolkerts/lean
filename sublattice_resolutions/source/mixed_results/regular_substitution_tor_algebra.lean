module
public import mixed_results.regular_substitution_graph_coordinates
public import mixed_results.polynomial_coefficient_contraction
public import mixed_results.tensor_koszul_algebra_rename

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.RegularSubstitutionTorAlgebra -/
section

/-! # Multiplicative Tor comparison under a homogeneous regular substitution

The comparison is a zigzag of two literal Koszul algebra projections.
Both projections induce algebra equivalences by the explicitly constructed
contractions. This proves preservation of products, in addition to the
underlying Tor modules, for every source algebra.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.PolynomialRegularSubstitution
open Classical CommAlg MvPolynomial HomologicalPerturbation
open scoped TensorProduct
universe u
variable {K Y V : Type u} [Field K] [Fintype V] [LinearOrder V]
  [Fintype Y] [LinearOrder Y]
local instance : LinearOrder (V ⊕ Y) :=
  LinearOrder.lift' (fun z : V ⊕ Y => (toLex z : Lex (V ⊕ Y))) (fun _ _ h => h)
local instance : LinearOrder (Y ⊕ V) :=
  LinearOrder.lift' (fun z : Y ⊕ V => (toLex z : Lex (Y ⊕ V))) (fun _ _ h => h)
local notation "S" => MvPolynomial V K
local notation "R" => MvPolynomial Y K
variable (f : V → (MvPolynomial Y K)) (w : V → ℕ) (hhom : ∀ v, (f v).IsHomogeneous (w v))
  (hreg : RegularFamilyKoszul.IsRegularFamily f) (hw : ∀ v, 0 < w v)
variable [Algebra (MvPolynomial V K) (MvPolynomial Y K)] [IsScalarTower K (MvPolynomial V K) (MvPolynomial Y K)]
  (hvars : ∀ v, algebraMap (MvPolynomial V K) (MvPolynomial Y K) (X v)=f v)
variable (A : Type u) [CommRing A] [Algebra (MvPolynomial V K) A] [Algebra K A] [IsScalarTower K (MvPolynomial V K) A]

include hhom hw in
theorem substitution_constantCoeff_zero (v : V) : constantCoeff (f v)=0 := by
  rw [MvPolynomial.constantCoeff_eq]
  by_contra h
  have he := hhom v h
  have hp := hw v
  simp only [map_zero] at he
  omega

include hhom hw in
theorem evaluation_graphFamily (v : V) :
    PolynomialCoefficientContraction.evaluation (graphFamily f A v)=algebraMap S A (X v) := by
  rw [graphFamily,map_sub,PolynomialCoefficientContraction.evaluation_tmul,
    PolynomialCoefficientContraction.evaluation_tmul,map_one,
    substitution_constantCoeff_zero f w hhom hw,one_smul,zero_smul,sub_zero]

/-- Equality of coefficient families transports the full homology algebra,
including its quotient ring and scalar structures. -/
def koszulHomologyFamilyCongr {A₀ W₀ : Type u} [CommRing A₀] [Algebra K A₀]
    [Fintype W₀] [LinearOrder W₀] {x y : W₀ → A₀} (h : x = y) :
    (TensorExteriorKoszul.parityDifferential (K := K) x).Homology ≃ₐ[K]
      (TensorExteriorKoszul.parityDifferential (K := K) y).Homology := by
  subst y
  exact AlgEquiv.refl

/-- Deleting the graph variables gives the actual substituted coefficient
algebra, tensored over the source polynomial ring. -/
def graphElimination :
    (TensorExteriorKoszul.parityDifferential (K := K)
      (Sum.elim (graphFamily f A) (PolynomialCoefficientContraction.variables (K := K) (A := A) (Y := Y)))).Homology ≃ₐ[K]
    (TensorExteriorKoszul.parityDifferential (K := K)
      (fun y : Y => (1 : A) ⊗ₜ[S] (X y : R))).Homology := by
  let e := KoszulFamilyElimination.homologyEquiv
    (graphFamily f A) (PolynomialCoefficientContraction.variables (K := K) (A := A) (Y := Y))
    (coefficientQuotient (V := V) (Y := Y) A) (graphTensorContraction f w hhom hreg hw hvars A)
    (graphTensorContraction_d f w hhom hreg hw hvars A)
    (graphTensorContraction_projection f w hhom hreg hw hvars A)
  have he : (fun y : Y => coefficientQuotient (V := V) (Y := Y) A
      (PolynomialCoefficientContraction.variables (K := K) (A := A) y))=
      (fun y : Y => (1 : A) ⊗ₜ[S] (X y : R)) := by
    funext y
    exact coefficientQuotient_tmul (V := V) (Y := Y) A 1 (X y)
  exact e.trans (koszulHomologyFamilyCongr (K := K) he)

/-- Deleting the polynomial variables gives the original source Koszul
algebra; positive homogeneity is used exactly to make `f(0)=0`. -/
def variableElimination :
    (TensorExteriorKoszul.parityDifferential (K := K)
      (Sum.elim (PolynomialCoefficientContraction.variables (K := K) (A := A) (Y := Y)) (graphFamily f A))).Homology ≃ₐ[K]
    (TensorExteriorKoszul.parityDifferential (K := K)
      (fun v : V => algebraMap S A (X v))).Homology := by
  let e := KoszulFamilyElimination.homologyEquiv
    (PolynomialCoefficientContraction.variables (K := K) (A := A) (Y := Y)) (graphFamily f A)
    (PolynomialCoefficientContraction.evaluation (K := K) (A := A) (Y := Y))
    (PolynomialCoefficientContraction.contraction (K := K) (A := A) (Y := Y))
    PolynomialCoefficientContraction.contraction_d PolynomialCoefficientContraction.contraction_projection
  have he : (fun v : V => PolynomialCoefficientContraction.evaluation (graphFamily f A v))=
      (fun v : V => algebraMap S A (X v)) := funext (evaluation_graphFamily f w hhom hw A)
  exact e.trans (koszulHomologyFamilyCongr (K := K) he)

/-- **Multiplicative regular-substitution comparison.** Both sides are
the actual Koszul homology algebras, with their genuine cycle products.
The right coefficient algebra is literally `A ⊗[S] R`. -/
def torAlgebraEquiv :
    (TensorExteriorKoszul.parityDifferential (K := K)
      (fun v : V => algebraMap S A (X v))).Homology ≃ₐ[K]
    (TensorExteriorKoszul.parityDifferential (K := K)
      (fun y : Y => (1 : A) ⊗ₜ[S] (X y : R))).Homology :=
  (variableElimination f w hhom hw A).symm.trans
    ((TensorKoszulAlgebraRename.homologyEquiv (Equiv.sumComm V Y)
      (Sum.elim (graphFamily f A)
        (PolynomialCoefficientContraction.variables (K := K) (A := A) (Y := Y)))
      (Sum.elim (PolynomialCoefficientContraction.variables (K := K) (A := A) (Y := Y))
        (graphFamily f A))
      (by intro v; cases v <;> rfl)).symm.trans
        (graphElimination f w hhom hreg hw hvars A))

end FourPapers.PolynomialRegularSubstitution

end
end
end

end
