module

public import ToricPower.DualDiagonalTopCoefficients
public import ToricPower.HomologyFunctorLinear

/-!
# The actual product-chart module of top dual-diagonal cohomology

The scalar top-class isomorphism is proved linear for the original
product-chart coordinate ring. The proof retains the actual ring scalar
maps on the original dual complex, their canonical induced homology
maps, and the genuine monomial comparison. No module action is
transported onto the target merely to force this conclusion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [Field k] (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s)) (frames : ∀ q, DiagonalCellFrames A S T q)
  (a : rayCharacterMonoid A S) (b : rayCharacterMonoid A T)

local notation "R" => DiagonalChartRing k A S T
local notation "K" => diagonalFramedDualComplex k A S T frames
local notation "restrict" => ModuleCat.restrictScalars (algebraMap k R)

/-- Actual homology scalar restriction commutes with the original
ring multiplication, through the proved monomial map of full weights. -/
theorem diagonalFramedDualTopScalarIso_monomial :
    (restrict).map (HomologicalComplex.homologyMap
      (AddMonoidAlgebra.single (a,b) (1:k) • 𝟙 K) n) ≫
        (diagonalFramedDualTopScalarIso k A S T frames).hom =
      (diagonalFramedDualTopScalarIso k A S T frames).hom ≫
        dualDiagonalBoundaryMonomialMap k A S T a b := by
  let f := AddMonoidAlgebra.single (a,b) (1:k) • 𝟙 K
  let e := diagonalFramedDualAllWeightIso k A S T frames
  have restriction : (restrict).map (HomologicalComplex.homologyMap f n) ≫
      (((K).sc n).mapHomologyIso restrict).inv =
    (((K).sc n).mapHomologyIso restrict).inv ≫
      HomologicalComplex.homologyMap
        (diagonalFramedDualMonomialMap k A S T a b frames) n :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℕ) n).map f) restrict
  have weights : HomologicalComplex.homologyMap
      (diagonalFramedDualMonomialMap k A S T a b frames) n ≫
        HomologicalComplex.homologyMap e.hom n =
      HomologicalComplex.homologyMap e.hom n ≫
        HomologicalComplex.homologyMap (dualDiagonalAllWeightMonomialMap k A S T a b) n := by
    rw [← HomologicalComplex.homologyMap_comp, diagonalFramedDualAllWeightIso_monomial,
      HomologicalComplex.homologyMap_comp]
  change (restrict).map (HomologicalComplex.homologyMap f n) ≫
    (((K).sc n).mapHomologyIso restrict).inv ≫ HomologicalComplex.homologyMap e.hom n ≫
      (dualDiagonalAllWeightTopIso k A S T).hom =
    (((K).sc n).mapHomologyIso restrict).inv ≫ HomologicalComplex.homologyMap e.hom n ≫
      (dualDiagonalAllWeightTopIso k A S T).hom ≫ dualDiagonalBoundaryMonomialMap k A S T a b
  rw [← Category.assoc, restriction, Category.assoc,
    ← Category.assoc (HomologicalComplex.homologyMap _ n), weights,
    Category.assoc, dualDiagonalAllWeightTopIso_monomial]

/-- Evaluation of the actual homology scalar map gives the literal
monomial action on the boundary coefficients. -/
theorem diagonalFramedDualTopScalarIso_monomial_apply (v : (K).homology n) :
    (diagonalFramedDualTopScalarIso k A S T frames).hom
      (AddMonoidAlgebra.single (a,b) (1:k) • v) =
    AddMonoidAlgebra.single (a,b) (1:k) •
      (diagonalFramedDualTopScalarIso k A S T frames).hom v := by
  have scalar : HomologicalComplex.homologyMap
      (AddMonoidAlgebra.single (a,b) (1:k) • 𝟙 K) n =
    AddMonoidAlgebra.single (a,b) (1:k) • 𝟙 ((K).homology n) := by
    change (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) n).map
      (AddMonoidAlgebra.single (a,b) (1:k) • 𝟙 K) = _
    rw [Functor.map_smul]
    exact congrArg (fun f => AddMonoidAlgebra.single (a,b) (1:k) • f)
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) n).map_id K)
  have equality := diagonalFramedDualTopScalarIso_monomial k A S T frames a b
  rw [scalar] at equality
  have value := ConcreteCategory.congr_hom equality v
  change (diagonalFramedDualTopScalarIso k A S T frames).hom
      (AddMonoidAlgebra.single (a,b) (1:k) • v) =
    Finsupp.mapDomain (dualDiagonalBoundaryTranslate A S T (a,b))
      ((diagonalFramedDualTopScalarIso k A S T frames).hom v) at value
  rw [dualDiagonalBoundary_single_smul, one_smul]
  exact value

/-- The canonical top class is linear for every actual chart-ring
coefficient, by its proved scalar and monomial compatibilities. -/
theorem diagonalFramedDualTopScalarIso_smul (r : R) (v : (K).homology n) :
    (diagonalFramedDualTopScalarIso k A S T frames).hom (r • v) =
      r • (diagonalFramedDualTopScalarIso k A S T frames).hom v := by
  have coefficient (t : k) (w : (K).homology n) :
      (diagonalFramedDualTopScalarIso k A S T frames).hom ((algebraMap k R t) • w) =
        t • (diagonalFramedDualTopScalarIso k A S T frames).hom w :=
    (diagonalFramedDualTopScalarIso k A S T frames).hom.hom.map_smul t w
  have monomial (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (t : k) :
      (diagonalFramedDualTopScalarIso k A S T frames).hom
        (AddMonoidAlgebra.single p t • v) =
      AddMonoidAlgebra.single p t •
        (diagonalFramedDualTopScalarIso k A S T frames).hom v := by
    have factor : AddMonoidAlgebra.single p t =
        (algebraMap k R t) * AddMonoidAlgebra.single p (1:k) := by
      change AddMonoidAlgebra.single p t =
        AddMonoidAlgebra.single 0 t * AddMonoidAlgebra.single p (1:k)
      rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    rw [factor, mul_smul, coefficient,
      diagonalFramedDualTopScalarIso_monomial_apply k A S T frames p.1 p.2]
    rw [← factor, dualDiagonalBoundary_single_smul,
      dualDiagonalBoundary_single_smul, one_smul]
  induction r using AddMonoidAlgebra.induction with
  | zero => rw [zero_smul, map_zero, zero_smul]
  | single_add p t r _ _ ih =>
      rw [add_smul, map_add, add_smul, monomial, ih]

/-- The top cohomology of the actual dual diagonal complex is the
explicit boundary-weight module over the actual product-chart ring. -/
def diagonalFramedDualTopModuleIso :
    (diagonalFramedDualComplex k A S T frames).homology n ≅
      dualDiagonalBoundaryModule A S T k :=
  (show (diagonalFramedDualComplex k A S T frames).homology n ≃ₗ[R]
      DualDiagonalBoundaryCoefficients A S T k from
    { toAddEquiv := (diagonalFramedDualTopScalarIso k A S T frames).toLinearEquiv.toAddEquiv
      map_smul' := diagonalFramedDualTopScalarIso_smul k A S T frames }).toModuleIso

end ToricPower.IntegralArrangement
