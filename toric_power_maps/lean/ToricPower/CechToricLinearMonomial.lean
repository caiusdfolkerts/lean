module

public import ToricPower.CechToricLinearComplex
public import ToricPower.CechToricMonomialComplex

/-!
# Every actual monomial map on the complex-linear Čech complex

The coefficient isomorphism computes the complete cochain map induced by
an actual Cartier monomial morphism. Its action is translation of the
full character lattice, with the original complex coefficient unchanged.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TauCeti.Toric
open BondalThomsen.FiniteAffineCechHigherComparison

namespace ToricPower

/-- The actual complex-linear Čech functor on all module sheaves. -/
abbrev schemeLinearCechComplexFunctor (k : Type) [Field k] (X : Scheme)
    [X.Over (Spec (.of k))] {Index : Type} (opens : Index → X.Opens) :
    X.Modules ⥤ CochainComplex (ModuleCat k) ℕ :=
  FiniteCover.schemeBasePresheaf k X ⋙ cechComplexFunctor opens

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {Index : Type} (charts : Index → fan.cones)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  (b c : fan.Ray → ℤ) (character : N →+ ℤ)
  (nonnegative : ∀ ρ, 0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))

/-- The actual monomial map in the proved complex-linear Laurent coordinates. -/
def toricCechLaurentLinearMonomialMap :
    toricCechLaurentLinearComplex fan charts b ⟶ toricCechLaurentLinearComplex fan charts c :=
  letI := toricSchemeIntegral fan nonempty
  (toricCechLinearComplexIso fan charts b nonempty regular).inv ≫
    (schemeLinearCechComplexFunctor ℂ fan.algebraicRealization
      (toricCechChartOpen fan charts)).map
      (toricCartierMonomialMap fan nonempty regular b c character nonnegative) ≫
    (toricCechLinearComplexIso fan charts c nonempty regular).hom

/-- All tuple coordinates of the actual linear cochain map are the
specified full-character translation, with no change of scalar. -/
theorem toricCechLaurentLinearMonomialMap_coefficients (q : ℕ)
    (tuple : Fin (q+1) → Index)
    (p : (toricCechLaurentLinearComplex fan charts b).X q) :
    (((toricCechLaurentLinearMonomialMap fan charts nonempty regular b c character nonnegative).f
      q p) tuple).val =
      Finsupp.mapDomain (fun m : N →+ ℤ => character + m) (p tuple).val := by
  haveI := toricSchemeIntegral fan nonempty
  let z := (toricCechLinearDegreeIso fan charts b nonempty regular q).inv p
  let map := (toricCartierMonomialMap fan nonempty regular b c character nonnegative)
  have projection := ConcreteCategory.congr_hom
    (Limits.Pi.map_π (fun t : Fin (q+1) → Index =>
      ((FiniteCover.schemeBasePresheaf ℂ fan.algebraicRealization).map map).app
        (op (cechIntersection (toricCechChartOpen fan charts) q t))) tuple) z
  have source : toricCechCoefficientLinearEquiv fan charts nonempty regular b q tuple
      (Limits.Pi.π (toricCechActualLinearCoefficient fan charts nonempty regular b q) tuple z) =
        p tuple := by
    rw [← toricCechLinearDegreeIso_hom_apply]
    exact congrArg (fun a : toricCechLaurentLinearDegree fan charts b q => a tuple)
      (ConcreteCategory.congr_hom
        (toricCechLinearDegreeIso fan charts b nonempty regular q).inv_hom_id p)
  change ((toricCechLinearDegreeIso fan charts c nonempty regular q).hom
    (((schemeLinearCechComplexFunctor ℂ fan.algebraicRealization
      (toricCechChartOpen fan charts)).map map).f q z) tuple).val = _
  rw [toricCechLinearDegreeIso_hom_apply]
  change Limits.Pi.π (toricCechActualLinearCoefficient fan charts nonempty regular c q) tuple
    (((schemeLinearCechComplexFunctor ℂ fan.algebraicRealization
      (toricCechChartOpen fan charts)).map map).f q z) = _ at projection
  rw [projection, toricCechCoefficientLinearEquiv_apply]
  rw [toricCechCoefficientLinearEquiv_apply] at source
  have computed := toricCechCoefficientEquiv_monomial fan charts nonempty regular
    b c character nonnegative q tuple
    (Limits.Pi.π (toricCechActualLinearCoefficient fan charts nonempty regular b q) tuple z)
  exact computed.trans (congrArg
    (fun a : toricCechLaurentLinearCoefficient fan charts b q tuple =>
      Finsupp.mapDomain (fun m : N →+ ℤ => character + m) a.val) source)

/-- The complete linear complex comparison intertwines the actual
Cartier monomial map before derived localization. -/
@[reassoc]
theorem toricCechLinearComplexIso_monomial :
    letI := toricSchemeIntegral fan nonempty
    (toricCechLinearComplexIso fan charts b nonempty regular).hom ≫
        toricCechLaurentLinearMonomialMap fan charts nonempty regular b c character nonnegative =
      (schemeLinearCechComplexFunctor ℂ fan.algebraicRealization
          (toricCechChartOpen fan charts)).map
          (toricCartierMonomialMap fan nonempty regular b c character nonnegative) ≫
        (toricCechLinearComplexIso fan charts c nonempty regular).hom := by
  haveI := toricSchemeIntegral fan nonempty
  simp only [toricCechLaurentLinearMonomialMap, Iso.hom_inv_id_assoc]

end ToricPower
