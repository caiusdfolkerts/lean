module

public import ToricPower.WeightedIncidencePushdown
public import ToricPower.ComplexDiagramTranspose

/-!
# Exact direct image of full weighted incidence complexes

The exact direct image of module diagrams acts on each degree. Evaluation
at a cell is literally the unrestricted direct sum of its lifted
complexes, and each incidence follows its uniquely lifted translation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (R : Type) [CommRing R]

local notation "C" => IncidenceObject A
local notation "W" => WeightedIncidenceObject A

/-- The actual direct image of a full complex-valued weighted diagram. -/
def weightedComplexPushdown (F : W ⥤ CochainComplex (ModuleCat.{0} R) ℕ) :
    C ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  (((weightedPushdown A R).mapHomologicalComplex (.up ℕ)).obj
    (complexDiagramTranspose F)).asFunctor

/-- Every fiber is the literal direct sum of all its actual complexes. -/
def weightedComplexPushdownCellIso
    (F : W ⥤ CochainComplex (ModuleCat.{0} R) ℕ) (c : C) :
    (weightedComplexPushdown A R F).obj c ≅
      ModuleDirectSum.complex R (fun m : Fin n → ℤ => F.obj (c,m)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun q r _ => by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl)

/-- On an actual single lift, incidence follows its translated lift. -/
theorem weightedComplexPushdown_map_single
    (F : W ⥤ CochainComplex (ModuleCat.{0} R) ℕ)
    {c d : C} (f : c ⟶ d) (q : ℕ) (m : Fin n → ℤ)
    (x : (F.obj (c,m)).X q) :
    ((weightedComplexPushdown A R F).map f).f q (DFinsupp.single m x) =
      DFinsupp.single (m+f.val) ((F.map (weightedIncidenceLift A f m)).f q x) := by
  exact ConcreteCategory.congr_hom
    (weightedPushdownMap_inclusion A R (F ⋙ HomologicalComplex.eval _ _ q) f m) x

end ToricPower.IntegralArrangement

end
