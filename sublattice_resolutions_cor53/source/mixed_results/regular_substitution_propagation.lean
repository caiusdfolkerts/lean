module
public import shared_results.part022
public import mixed_results.regular_substitution_rees_generation
public import mixed_results.tensor_koszul_coefficient_pieces

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.RegularSubstitutionPropagation -/
section

/-!
# Corollary 5.8: first-power propagation with the substituted target

The target identification is an actual algebra equivalence over the
original polynomial ring. Preservation of its coefficient degree one
derives preservation of the selected Koszul classes. Generation of the
target is proved by regular substitution and is not a theorem hypothesis.

The first-degree Betti premise is precisely that of Proposition 3.1 for
the original algebra and its literal associated graded algebra. Every
auxiliary, homological and integer internal degree remains in the result.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg MvPolynomial
open BigradedPolynomialAlgebra BigradedTensorKoszul FilteredTensorKoszul
open FilteredBigradedComparison IntegerFiltered
open IntegerFiltered.MultiplicativeFiltration
open FlatReesBaseChange PolynomialRegularSubstitution

universe u
variable {K A Y : Type u} [Field K] [CommRing A] [Algebra K A]
  [Fintype Y] [LinearOrder Y]
  [Algebra (MvPolynomial Y K) A] [IsScalarTower K (MvPolynomial Y K) A]
  (P : ℤ × ℕ → Submodule K A) [GradedAlgebra P]
  [hfinite : ∀ γ, Module.Finite K (P γ)]
  (hX : ∀ y, baseVariable (K := K) (A := A) (V := Y) y ∈ P (1,0))
  (F : MultiplicativeFiltration K A) (ν : Y → ℤ)
  (hF : ∀ j, DirectSum.SetLike.IsHomogeneous P (F.level j))
  (hwF : ∀ y, baseVariable (K := K) (A := A) (V := Y) y ∈ F.level (ν y))

local notation "R" => MvPolynomial Y K
local notation "B" => AssociatedPolynomialCarrier F ν
  (baseVariable (K := K) (A := A) (V := Y)) hwF
local notation "Q" => associatedGrading P F ν hwF hF
local notation "hY" => associatedVariableHomogeneous P hX F ν hF hwF
local notation "DA" => D (K := K) (A := A) (V := Y)
local notation "DB" => D (K := K) (A := B) (V := Y)

local instance substitutedTargetAssociatedGrading : GradedAlgebra Q :=
  F.associatedGradingAlgebra P hF

local instance substitutedTargetAssociatedFinite (γ : ℤ × ℕ) :
    Module.Finite K (Q γ) := F.associatedPiece_finite_of_finite (P γ)

variable {d : ℕ} {n : Fin d → ℕ}
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (f : FiniteVariable.{u} n → (MvPolynomial Y K)) (w : FiniteVariable.{u} n → ℕ)
  (hhom : ∀ v, (f v).IsHomogeneous (w v))
  (hreg : RegularFamilyKoszul.IsRegularFamily f) (hw : ∀ v, 0 < w v)

local notation "J" => substitutedSublatticeIdeal f E

include hE hhom hreg hw hfinite in
/-- **Corollary 5.8, propagation clause.** An actual homogeneous Rees
degeneration with the substituted target inherits the first-power
criterion. The algebra identification fixes every original polynomial
variable, and the degree condition concerns coefficient modules before
taking cycles or homology. -/
theorem corollary58_propagation
    (e : B ≃ₐ[R] coefficients J)
    (hdegree : ∀ b : B,
      e b ∈ LinearMap.range ((projection J 1).restrictScalars K) ↔
        b ∈ auxiliaryCoefficientPiece Q 1)
    (hβ : ∀ (p : ℕ) (q : ℤ),
      BigradedPolynomialAlgebra.bettiNumber P hX 1 p q =
        BigradedPolynomialAlgebra.bettiNumber Q hY 1 p q) :
    (∀ (m p : ℕ) (q : ℤ),
      BigradedPolynomialAlgebra.bettiNumber P hX m p q =
        BigradedPolynomialAlgebra.bettiNumber Q hY m p q) ∧
      Algebra.adjoin K (selectedHomologyClasses DA (auxiliaryPiece (V := Y) P 1)) = ⊤ := by
  let ee : B ≃ₐ[K] coefficients J := e.restrictScalars K
  let x : Y → B := baseVariable (K := K) (A := B) (V := Y)
  let y : Y → coefficients J := fun v => algebraMap R (coefficients J) (X v)
  have hevars : ∀ v, ee (x v) = y v := by
    intro v
    change e (algebraMap R B (X v)) = algebraMap R (coefficients J) (X v)
    exact e.commutes (X v)
  let eH := TensorKoszulCoefficientEquiv.homologyEquiv ee x y hevars
  have hclasses : eH '' selectedHomologyClasses DB (auxiliaryPiece (V := Y) Q 1) =
      coefficientReesClasses J 1 := by
    change TensorKoszulCoefficientEquiv.homologyEquiv ee x y hevars ''
      (TensorExteriorKoszul.parityDifferential (K := K) x).classesFrom
        (coordinatePiece (fun _ : Finset Y => auxiliaryCoefficientPiece Q 1)) =
      (TensorExteriorKoszul.parityDifferential (K := K) y).classesFrom
        (LinearMap.range (KoszulCoefficientProjection.tensor (V := Y)
          ((projection J 1).restrictScalars K)))
    exact TensorKoszulCoefficientEquiv.homologyEquiv_coordinateClasses
      ee (auxiliaryCoefficientPiece Q 1) ((projection J 1).restrictScalars K)
      hdegree x y hevars
  have hgen : Algebra.adjoin K
      (selectedHomologyClasses DB (auxiliaryPiece (V := Y) Q 1)) = ⊤ :=
    (adjoin_eq_top_iff_of_algEquiv eH _ _ hclasses).mpr
      (corollary58_generation E f w hhom hreg hw hE)
  exact proposition31 P hX F ν hF hwF hβ hgen

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary58_propagation

end
end
end


end
