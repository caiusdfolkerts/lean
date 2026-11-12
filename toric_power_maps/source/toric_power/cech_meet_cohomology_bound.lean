module

public import ToricPower.CechMeetCoefficientComparison
public import ToricPower.CechComparisonFoundations
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# A uniform cohomological bound from a finite intersection-closed cover

The full Čech complex is compared by an actual homotopy equivalence to
finite projective coefficients. Its terms vanish above the number of
charts, so ordinary quasi-coherent sheaf cohomology vanishes there too.
This uses neither properness nor finite generation of the coefficient.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open BondalThomsen.FiniteAffineCechHigherComparison
open BondalThomsen.FiniteAffineCechAllDegreeComparison
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower.FiniteCech

variable {B : Type} [SemilatticeInf B] [Finite B]
  (k : Type) [Field k] (X : Scheme) [X.Over (Spec (.of k))]
  [IsNoetherian X] [X.IsSeparated]
  (opens : B ⥤ X.Opens)
  (meetEq : ∀ (q : ℕ) (t : Fin (q+1) → B),
    cechIntersection opens.obj q t = opens.obj (tupleMeet t))
  (cover : iSup opens.obj = ⊤) (affine : ∀ b, IsAffineOpen (opens.obj b))

include k opens meetEq cover affine in
/-- A genuine uniform bound for every actual quasi-coherent coefficient. -/
theorem meetCover_cohomology_subsingleton
    (M : X.Modules) [M.IsQuasicoherent] (degree : ℕ) (high : Nat.card B < degree) :
    Subsingleton (Cohomology M degree) := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  let F := meetChartSections k X opens M
  let forget := forget₂ (ModuleCat k) AddCommGrpCat
  let comparison := forget.mapHomotopyEquiv (finiteCoefficientComparison k F)
  have termZero : IsZero
      (((forget.mapHomologicalComplex (.up ℕ)).obj
        (coefficientComplex k F (finiteTupleResolution k).complex)).X degree) :=
    forget.map_isZero (finiteCoefficient_isZero_of_card_lt k F degree
      (by simpa only [Nat.card_eq_fintype_card] using high))
  have homologyZero := (HomologicalComplex.ExactAt.of_isZero termZero).isZero_homology
  let e : AddCommGrpCat.of (Cohomology M degree) ≅ _ :=
    cechSchemeCohomologyIso opens.obj cover affine M degree ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) degree).mapIso
        (meetCechComplexForgetIso k X opens meetEq M) ≪≫
      comparison.toHomologyIso degree
  exact AddCommGrpCat.subsingleton_of_isZero (e.isZero_iff.mpr homologyZero)

end ToricPower.FiniteCech

end
