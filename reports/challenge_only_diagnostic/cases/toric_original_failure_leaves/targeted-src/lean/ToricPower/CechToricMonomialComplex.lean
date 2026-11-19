module

public import ToricPower.CechToricMonomialSections
public import ToricPower.CechToricComplex

/-!
# Actual monomial morphisms of the full toric Čech complexes

The actual sheaf map induces an actual cochain map. After the proved
Laurent-coordinate chain isomorphisms, every tuple component translates
the full character by the monomial exponent and preserves its coefficient.
The final formula computes the transported chain map explicitly; it does
not merely give a name to an unspecified map between cohomology groups.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TauCeti.Toric
open BondalThomsen.FiniteAffineCechHigherComparison
open scoped Classical

namespace ToricPower

private theorem productConjugate_component
    {A I : Type*} [Category A] [HasProductsOfShape I A]
    {source target first second : I → A}
    (sourceIso : ∀ i, source i ≅ first i) (targetIso : ∀ i, target i ≅ second i)
    (mapping : ∀ i, source i ⟶ target i) (index : I) :
    ((Limits.Pi.mapIso sourceIso).inv ≫ Limits.Pi.map mapping ≫
        (Limits.Pi.mapIso targetIso).hom) ≫ Limits.Pi.π second index =
      Limits.Pi.π first index ≫ (sourceIso index).inv ≫ mapping index ≫
        (targetIso index).hom := by
  simp only [Category.assoc, Limits.Pi.mapIso_hom_π, Limits.Pi.map_π_assoc,
    Limits.Pi.mapIso_inv_π_assoc]

/-- The actual coefficient map commutes with transport along equality
of its open domain. -/
theorem toricSectionOpenEquiv_naturality (X : Scheme) {F G : X.Modules}
    (f : F ⟶ G) {U W : X.Opens} (same : U = W) (s : F.presheaf.obj (op U)) :
    toricSectionOpenEquiv X G same (Scheme.Modules.Hom.app f U s) =
      Scheme.Modules.Hom.app f W (toricSectionOpenEquiv X F same s) := by
  subst W
  rfl

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {Index : Type} (charts : Index → fan.cones)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  (b c : fan.Ray → ℤ) (character : N →+ ℤ)
  (nonnegative : ∀ ρ, 0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))

/-- Every actual tuple-intersection coefficient has the same explicit
full-character translation formula as an actual affine chart. -/
theorem toricCechCoefficientEquiv_monomial (degree : ℕ)
    (tuple : Fin (degree + 1) → Index)
    (s : toricCechActualCoefficient fan charts nonempty regular b degree tuple) :
    letI := toricSchemeIntegral fan nonempty
    (toricCechCoefficientEquiv fan charts nonempty regular c degree tuple
      (Scheme.Modules.Hom.app
        (toricCartierMonomialMap fan nonempty regular b c character nonnegative)
        (cechIntersection (toricCechChartOpen fan charts) degree tuple) s)).val =
      Finsupp.mapDomain (fun m : N →+ ℤ => character + m)
        (toricCechCoefficientEquiv fan charts nonempty regular b degree tuple s).val := by
  letI := toricSchemeIntegral fan nonempty
  change (toricDivisorLaurentCoefficientsEquiv fan nonempty regular c
      (toricCechCone fan charts degree tuple)
      (toricSectionOpenEquiv fan.algebraicRealization
        (invariantCartierDivisor fan nonempty regular c).sheaf
        (toricCechIntersection_eq_chart fan charts degree tuple)
        (Scheme.Modules.Hom.app
          (toricCartierMonomialMap fan nonempty regular b c character nonnegative)
          (cechIntersection (toricCechChartOpen fan charts) degree tuple) s))).val = _
  rw [toricSectionOpenEquiv_naturality]
  exact toricDivisorLaurentCoefficientsEquiv_monomial fan nonempty regular b c
    character nonnegative (toricCechCone fan charts degree tuple) _

/-- The genuine monomial chain map expressed in the independently proved
Laurent coordinates. Its explicit coefficient action is computed below. -/
def toricCechLaurentMonomialMap :
    toricCechLaurentComplex fan charts b ⟶ toricCechLaurentComplex fan charts c :=
  letI := toricSchemeIntegral fan nonempty
  (toricCechLaurentComplexIso fan charts b nonempty regular).inv ≫
    (schemeCechComplexFunctor (toricCechChartOpen fan charts)).map
      (toricCartierMonomialMap fan nonempty regular b c character nonnegative) ≫
    (toricCechLaurentComplexIso fan charts c nonempty regular).hom

/-- The Laurent coordinate comparison retains the actual monomial
cochain map, including every cohomological differential. -/
@[reassoc]
theorem toricCechLaurentComplexIso_monomial :
    letI := toricSchemeIntegral fan nonempty
    (toricCechLaurentComplexIso fan charts b nonempty regular).hom ≫
        toricCechLaurentMonomialMap fan charts nonempty regular b c character nonnegative =
      (schemeCechComplexFunctor (toricCechChartOpen fan charts)).map
          (toricCartierMonomialMap fan nonempty regular b c character nonnegative) ≫
        (toricCechLaurentComplexIso fan charts c nonempty regular).hom := by
  letI := toricSchemeIntegral fan nonempty
  simp only [toricCechLaurentMonomialMap, Iso.hom_inv_id_assoc]

/-- A projection of the chain map is the actual coefficient map between
the two explicit chart-coefficient equivalences. -/
theorem toricCechLaurentMonomialMap_f_π (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) :
    letI := toricSchemeIntegral fan nonempty
    (toricCechLaurentMonomialMap fan charts nonempty regular b c character nonnegative).f degree ≫
        Limits.Pi.π (toricCechLaurentCoefficient fan charts c degree) tuple =
      Limits.Pi.π (toricCechLaurentCoefficient fan charts b degree) tuple ≫
        (toricCechCoefficientEquiv fan charts nonempty regular b degree tuple).toAddCommGrpIso.inv ≫
        Scheme.Modules.Hom.app
          (toricCartierMonomialMap fan nonempty regular b c character nonnegative)
          (cechIntersection (toricCechChartOpen fan charts) degree tuple) ≫
        (toricCechCoefficientEquiv fan charts nonempty regular c degree tuple).toAddCommGrpIso.hom := by
  letI := toricSchemeIntegral fan nonempty
  change ((toricCechLaurentDegreeIso fan charts b nonempty regular degree).inv ≫
      ((schemeCechComplexFunctor (toricCechChartOpen fan charts)).map
        (toricCartierMonomialMap fan nonempty regular b c character nonnegative)).f degree ≫
      (toricCechLaurentDegreeIso fan charts c nonempty regular degree).hom) ≫ _ = _
  exact productConjugate_component
    (fun tuple => (toricCechCoefficientEquiv fan charts nonempty regular b degree tuple).toAddCommGrpIso)
    (fun tuple => (toricCechCoefficientEquiv fan charts nonempty regular c degree tuple).toAddCommGrpIso)
    (fun tuple => Scheme.Modules.Hom.app
      (toricCartierMonomialMap fan nonempty regular b c character nonnegative)
      (cechIntersection (toricCechChartOpen fan charts) degree tuple)) tuple

/-- Every component of the actual full Laurent chain map is exactly
translation by the monomial character, with unchanged complex coefficients. -/
theorem toricCechLaurentMonomialMap_coefficients (degree : ℕ)
    (tuple : Fin (degree + 1) → Index)
    (p : (toricCechLaurentComplex fan charts b).X degree) :
    (Limits.Pi.π (toricCechLaurentCoefficient fan charts c degree) tuple
      ((toricCechLaurentMonomialMap fan charts nonempty regular b c character nonnegative).f
        degree p)).val =
      Finsupp.mapDomain (fun m : N →+ ℤ => character + m)
        (Limits.Pi.π (toricCechLaurentCoefficient fan charts b degree) tuple p).val := by
  letI := toricSchemeIntegral fan nonempty
  have component := ConcreteCategory.congr_hom
    (toricCechLaurentMonomialMap_f_π fan charts nonempty regular b c character nonnegative
      degree tuple) p
  change Limits.Pi.π (toricCechLaurentCoefficient fan charts c degree) tuple
      ((toricCechLaurentMonomialMap fan charts nonempty regular b c character nonnegative).f
        degree p) =
    toricCechCoefficientEquiv fan charts nonempty regular c degree tuple
      (Scheme.Modules.Hom.app
        (toricCartierMonomialMap fan nonempty regular b c character nonnegative)
        (cechIntersection (toricCechChartOpen fan charts) degree tuple)
        ((toricCechCoefficientEquiv fan charts nonempty regular b degree tuple).symm
          (Limits.Pi.π (toricCechLaurentCoefficient fan charts b degree) tuple p))) at component
  rw [component, toricCechCoefficientEquiv_monomial, AddEquiv.apply_symm_apply]

end ToricPower
