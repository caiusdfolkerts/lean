module

public import ToricPower.CoherentFoundations
public import ToricPower.SchemeModulesBaseLinear
public import ToricPower.CellularDerivedHom
public import ToricPower.ExactDerivedConservative
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# The actual bounded-below derived Hom diagram

For a contravariant label diagram `P : Cᵒᵖ ⥤ A` in an abelian linear
category, this file constructs `E ↦ (c ↦ Hom(P(c), E))` as an actual
module-valued diagram. Its right-derived functor is taken only after
forming complexes in that functor category. Consequently all diagram
coherence is retained during localization.

For a scheme, enough injectives follows from Mathlib's proved
Grothendieck-abelian structure on its actual module-sheaf category. No
injective-resolution existence or derived comparison is postulated here.

The domain is explicitly the bounded-below derived category. The file
does not identify it with an unbounded quasicoherent derived category,
assert full faithfulness, or infer classical generation.

-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace ToricPower

universe u

local instance rhomSchemeStandardDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

local instance rhomCoherentStandardDerivedCategory (X : Scheme.{u})
    [IsLocallyNoetherian X] : HasDerivedCategory.{u + 1} (Coh X) :=
  HasDerivedCategory.standard _

local instance rhomDiagramStandardDerivedCategory
    (R : Type u) [CommRing R] (C : Type u) [Category.{u} C] :
    HasDerivedCategory.{u + 1} (C ⥤ ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- The ordinary coherent inclusion, with its source and target
universes explicit. -/
abbrev coherentModuleInclusion (X : Scheme.{u}) : Coh X ⥤ X.Modules :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι

instance (X : Scheme.{u}) [IsLocallyNoetherian X] :
    PreservesFiniteLimits (coherentModuleInclusion X) :=
  coherentInclusion_preservesFiniteLimits X

instance (X : Scheme.{u}) [IsLocallyNoetherian X] :
    PreservesFiniteColimits (coherentModuleInclusion X) :=
  coherentInclusion_preservesFiniteColimits X

/-- The literal coherent derived category maps to the bounded-below
derived category of all actual module sheaves by the proved exact
coherent inclusion. No equivalence or full faithfulness is assumed. -/
def coherentToModuleDerivedPlus (X : Scheme.{u}) [IsLocallyNoetherian X] :
    DbCoh X ⥤ DerivedCategory.Plus X.Modules :=
  (DerivedCategory.TStructure.t (C := X.Modules)).plus.lift
    ((coherentModuleInclusion X).mapBoundedDerivedCategory ⋙ DerivedCategory.Bounded.ι)
    (fun K => ((coherentModuleInclusion X).mapBoundedDerivedCategory.obj K).property.1)

instance (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (coherentToModuleDerivedPlus X).CommShift ℤ := by
  unfold coherentToModuleDerivedPlus
  infer_instance

instance (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (coherentToModuleDerivedPlus X).IsTriangulated := by
  unfold coherentToModuleDerivedPlus
  infer_instance

/-- The coherent derived inclusion detects zero objects.  The argument
uses exactness and faithfulness on sheaves, and does not require any
full-faithfulness assertion on derived morphisms. -/
theorem coherentToModuleDerivedPlus_isZero_iff (X : Scheme.{u})
    [IsLocallyNoetherian X] (K : DbCoh X) :
    IsZero ((coherentToModuleDerivedPlus X).obj K) ↔ IsZero K := by
  constructor
  · intro h
    have h' := (DerivedCategory.Plus.ι (C := X.Modules)).map_isZero h
    have hK : IsZero K.obj := exactDerived_reflects_isZero
      (coherentModuleInclusion X) K.obj h'
    apply (IsZero.iff_id_eq_zero _).mpr
    apply ObjectProperty.hom_ext
    exact (IsZero.iff_id_eq_zero K.obj).mp hK
  · exact (coherentToModuleDerivedPlus X).map_isZero

/-- The bounded-below derived Hom diagram of actual module sheaves over
the base ring. Enough injectives is a proved Mathlib instance. -/
def schemeLabelRHomPlus (R : Type u) [CommRing R]
    (X : Scheme.{u}) [X.Over (Spec (.of R))]
    {C : Type u} [Category.{u} C] (P : Cᵒᵖ ⥤ X.Modules) :
    DerivedCategory.Plus X.Modules ⥤
      DerivedCategory.Plus (C ⥤ ModuleCat.{u} R) :=
  Cellular.labelRHomPlus R P

/-- The same concrete functor with input in the literal bounded derived
category of coherent sheaves. Its target retains possibly unbounded-above
derived Hom and possibly infinite-dimensional coefficient modules. -/
def coherentLabelRHomPlus (R : Type u) [CommRing R]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [X.Over (Spec (.of R))]
    {C : Type u} [Category.{u} C] (P : Cᵒᵖ ⥤ X.Modules) :
    DbCoh X ⥤ DerivedCategory.Plus (C ⥤ ModuleCat.{u} R) :=
  coherentToModuleDerivedPlus X ⋙ schemeLabelRHomPlus R X P

instance (R : Type u) [CommRing R] (X : Scheme.{u})
    [IsLocallyNoetherian X] [X.Over (Spec (.of R))]
    {C : Type u} [Category.{u} C] (P : Cᵒᵖ ⥤ X.Modules) :
    (coherentLabelRHomPlus R X P).CommShift ℤ := by
  unfold coherentLabelRHomPlus schemeLabelRHomPlus
  infer_instance

instance (R : Type u) [CommRing R] (X : Scheme.{u})
    [IsLocallyNoetherian X] [X.Over (Spec (.of R))]
    {C : Type u} [Category.{u} C] (P : Cᵒᵖ ⥤ X.Modules) :
    (coherentLabelRHomPlus R X P).IsTriangulated := by
  unfold coherentLabelRHomPlus schemeLabelRHomPlus
  infer_instance

end ToricPower

end
