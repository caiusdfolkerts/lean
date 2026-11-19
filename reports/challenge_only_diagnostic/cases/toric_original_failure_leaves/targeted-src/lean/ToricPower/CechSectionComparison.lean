module

public import ToricPower.CechComparison.HigherComparison

/-!
# Čech comparison from compatible maps on actual intersection sections

An isomorphism on each actual finite intersection, commuting with its
actual restriction maps, induces an isomorphism of the entire ordinary
Čech complexes. This construction retains every cosimplicial degree and
all alternating differentials.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open BondalThomsen.FiniteAffineCechHigherComparison
namespace ToricPower
universe u

private theorem productIso_component_postcompose
    {A I : Type*} [Category A] [HasProductsOfShape I A]
    {first second : I → A} (comparison : ∀ index, first index ≅ second index)
    (index : I) {Z : A} (mapping : second index ⟶ Z) :
    (Limits.Pi.mapIso comparison).hom ≫ Limits.Pi.π second index ≫ mapping =
      Limits.Pi.π first index ≫ (comparison index).hom ≫ mapping := by
  rw [← Category.assoc, Limits.Pi.mapIso_hom_π, Category.assoc]

variable {X : Scheme.{u}} {Index : Type u} (opens : Index → X.Opens)

/-- Actual sections in one component of a Čech cochain group. -/
abbrev cechSectionCoefficient (M : X.Modules) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) : AddCommGrpCat.{u} :=
  M.presheaf.obj (op (cechIntersection opens degree tuple))

/-- Actual restriction associated with any tuple selection. -/
def cechSectionRestriction (M : X.Modules) {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : Fin (next + 1) → Index) :
    cechSectionCoefficient opens M degree (tuple ∘ selection) ⟶
      cechSectionCoefficient opens M next tuple :=
  M.presheaf.map (Limits.Pi.lift (fun column : Fin (degree + 1) =>
    Limits.Pi.π (opens ∘ tuple) (selection column))).op

/-- A single actual coface of the ordinary scheme Čech complex. -/
def cechSectionCoface (M : X.Modules) (degree : ℕ) (deleted : Fin (degree + 2)) :
    (schemeCechComplex opens M).X degree ⟶ (schemeCechComplex opens M).X (degree + 1) :=
  Limits.Pi.lift (fun tuple =>
    Limits.Pi.π (cechSectionCoefficient opens M degree) (tuple ∘ deleted.succAbove) ≫
      cechSectionRestriction opens M deleted.succAbove tuple)

/-- The actual differential is the alternating sum of these actual cofaces. -/
theorem schemeCechComplex_d (M : X.Modules) (degree : ℕ) :
    (schemeCechComplex opens M).d degree (degree + 1) =
      ∑ deleted : Fin (degree + 2), (-1 : ℤ) ^ deleted.val •
        cechSectionCoface opens M degree deleted := by
  change (AlgebraicTopology.AlternatingCofaceMapComplex.obj _).d degree (degree + 1) = _
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  rfl

variable {M N : X.Modules}
  (comparison : ∀ degree tuple, cechSectionCoefficient opens M degree tuple ≅
    cechSectionCoefficient opens N degree tuple)

/-- Product of the actual intersection-section isomorphisms. -/
def cechSectionDegreeIso (degree : ℕ) :
    (schemeCechComplex opens M).X degree ≅ (schemeCechComplex opens N).X degree :=
  Limits.Pi.mapIso (comparison degree)

variable (compatible : ∀ {degree next : ℕ}
  (selection : Fin (degree + 1) → Fin (next + 1)) (tuple : Fin (next + 1) → Index),
  (comparison degree (tuple ∘ selection)).hom ≫ cechSectionRestriction opens N selection tuple =
    cechSectionRestriction opens M selection tuple ≫ (comparison next tuple).hom)

include compatible in
theorem cechSectionDegreeIso_coface (degree : ℕ) (deleted : Fin (degree + 2)) :
    (cechSectionDegreeIso opens comparison degree).hom ≫
      cechSectionCoface opens N degree deleted =
    cechSectionCoface opens M degree deleted ≫
      (cechSectionDegreeIso opens comparison (degree + 1)).hom := by
  apply Limits.Pi.hom_ext
  intro tuple
  simp only [cechSectionCoface, cechSectionDegreeIso, Category.assoc,
    Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc,
    Limits.Pi.mapIso_hom_π, Limits.Pi.mapIso_hom_π_assoc]
  exact (productIso_component_postcompose (comparison degree)
    (tuple ∘ deleted.succAbove) (cechSectionRestriction opens N deleted.succAbove tuple)).trans
      (congrArg (fun mapping =>
        Limits.Pi.π (cechSectionCoefficient opens M degree) (tuple ∘ deleted.succAbove) ≫ mapping)
        (compatible deleted.succAbove tuple))

/-- Compatible isomorphisms of actual intersection sections produce an
isomorphism of the complete ordinary Čech complexes. -/
def cechSectionComplexIso : schemeCechComplex opens M ≅ schemeCechComplex opens N :=
  HomologicalComplex.Hom.isoOfComponents (cechSectionDegreeIso opens comparison)
    (fun degree next related => by
      change degree + 1 = next at related
      subst next
      rw [schemeCechComplex_d, schemeCechComplex_d]
      simp only [comp_sum, sum_comp, comp_zsmul, zsmul_comp]
      apply Finset.sum_congr rfl
      intro deleted _
      exact congrArg (fun mapping => (-1 : ℤ) ^ deleted.val • mapping)
        (cechSectionDegreeIso_coface opens comparison compatible degree deleted))

end ToricPower
