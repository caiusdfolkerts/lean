module

public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Coherent homology classes in actual filtered colimits

A proved natural identification of the homology of an exhausting system
with a constant module supplies the same identification on its actual
colimit. The inclusion and naturality formulas are proved once for
abstract complexes, so geometric specializations retain their actual
maps without normalizing the underlying cellular construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable (k : Type) [Ring k] (q : ℕ)

local instance : IsConnected ℕ := IsFiltered.isConnected ℕ

variable (F : ℕ ⥤ CochainComplex (ModuleCat.{0} k) ℕ) (M : ModuleCat.{0} k)
  (classes : F ⋙ HomologicalComplex.homologyFunctor _ _ q ≅ (Functor.const ℕ).obj M)

/-- The actual homology-colimit comparison followed by the supplied
coherent, already proved stagewise class identification. -/
def homologyColimitClassIso : (colimit F).homology q ≅ M :=
  preservesColimitIso (HomologicalComplex.homologyFunctor _ _ q) F ≪≫
    HasColimit.isoOfNatIso classes ≪≫
      (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone ℕ M)

@[reassoc]
theorem homologyColimitClassIso_inclusion (r : ℕ) :
    HomologicalComplex.homologyMap (colimit.ι F r) q ≫
        (homologyColimitClassIso k q F M classes).hom = (classes.app r).hom := by
  have leg : HomologicalComplex.homologyMap (colimit.ι F r) q ≫
      (preservesColimitIso (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) q) F).hom =
      colimit.ι (F ⋙ HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) q) r :=
    ι_preservesColimitIso_hom
      (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) q) F r
  have constantLeg : colimit.ι ((Functor.const ℕ).obj M) r ≫
      ((colimit.isColimit ((Functor.const ℕ).obj M)).coconePointUniqueUpToIso
        (isColimitConstCocone ℕ M)).hom = 𝟙 M :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit ((Functor.const ℕ).obj M)) (isColimitConstCocone ℕ M) r
  simp only [homologyColimitClassIso, Iso.trans_hom]
  rw [← Category.assoc, leg, HasColimit.ι_isoOfNatIso_hom_assoc, constantLeg]
  exact Category.comp_id (classes.hom.app r)

variable (G : ℕ ⥤ CochainComplex (ModuleCat.{0} k) ℕ)
  (targetClasses : G ⋙ HomologicalComplex.homologyFunctor _ _ q ≅ (Functor.const ℕ).obj M)
  (α : F ⟶ G)

/-- An actual map of exhausting complexes preserves the colimit class
as soon as its actual maps preserve every supplied finite-stage class. -/
theorem homologyColimitClassIso_natural
    (compatible : ∀ r, HomologicalComplex.homologyMap (α.app r) q ≫
      (targetClasses.app r).hom = (classes.app r).hom) :
    HomologicalComplex.homologyMap (colim.map α) q ≫
        (homologyColimitClassIso k q G M targetClasses).hom =
      (homologyColimitClassIso k q F M classes).hom := by
  apply (isColimitOfPreserves (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) q)
    (colimit.isColimit F)).hom_ext
  intro r
  change HomologicalComplex.homologyMap (colimit.ι F r) q ≫ _ =
    HomologicalComplex.homologyMap (colimit.ι F r) q ≫ _
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, colimit.ι_map,
    HomologicalComplex.homologyMap_comp, Category.assoc,
    homologyColimitClassIso_inclusion, homologyColimitClassIso_inclusion]
  exact compatible r

end ToricPower
