module

public import ToricPower.ArrangementCostalkRestriction
public import ToricPower.ArrangementCostalkFaces
public import ToricPower.CWRelativeCellularMap
public import ToricPower.CellularIncidenceNaturality
public import ToricPower.ConvexComplementTranslation

/-!
# Actual lattice translation of cellular costalks

The periodic characteristic maps make lattice translation cellular.
The selected monomial inequalities and the center translate together,
so this gives a chain map of the literal relative pairs. The comparison
with singular homology proves that it preserves the fixed ambient top
class; signs are not chosen separately for translated cells.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)
  (S : Set (Fin s ⊕ Fin n)) (a : Fin s ⊕ Fin n → ℤ)
  (x : Fin n → ℝ) (z : Fin n → ℤ)

local notation "shift" => augmentedLatticePairing matrix z
local notation "lift" => latticeLift z
local notation "sourceRegion" => costalkRegion (augmentedForms matrix) S a x
local notation "targetRegion" => costalkRegion (augmentedForms matrix) S (a + shift) (x + lift)

local instance costalkTranslationPeriodicCW : CWComplex (arrangementCarrier matrix) :=
  periodicArrangementCWComplex matrix

/-- The translated support is exactly the support at the translated
center and full shifted weight. -/
theorem periodicCostalkRegion_translation :
    translatedRegion sourceRegion lift = targetRegion := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (add_mem_costalkRegion_iff (augmentedForms matrix) S a shift lift
      (augmentedForms_latticeLift matrix z) x p).mpr hp
  · intro hy
    refine ⟨y - lift, ?_, sub_add_cancel y lift⟩
    apply (add_mem_costalkRegion_iff (augmentedForms matrix) S a shift lift
      (augmentedForms_latticeLift matrix z) x (y - lift)).mp
    simpa only [sub_add_cancel] using hy

/-- Translation preserves the actual complementary bases. -/
theorem periodicCostalkTranslation_base (p : arrangementCarrier matrix)
    (outside : p.val ∈ (sourceRegion)ᶜ) :
    (arrangementTranslation matrix z p).val ∈ (targetRegion)ᶜ := by
  intro inside
  exact outside ((add_mem_costalkRegion_iff (augmentedForms matrix) S a shift lift
    (augmentedForms_latticeLift matrix z) x p.val).mp inside)

variable {k : Type} [Ring k] (M : ModuleCat.{0} k)

/-- The genuine relative cellular chain map induced by the ambient
lattice translation and the original periodic characteristic maps. -/
def periodicCostalkTranslation :
    periodicCostalkCellComplex matrix S a x M ⟶
      periodicCostalkCellComplex matrix S (a + shift) (x + lift) M :=
  relativeCWChainMap
    (periodicCostalkComplementSubcomplex matrix S a x)
    (periodicCostalkComplementSubcomplex matrix S (a + shift) (x + lift))
    (arrangementTranslation matrix z) M (arrangementTranslation_cellular matrix z)
    (periodicCostalkTranslation_base matrix S a x z)

/-- The literal ambient translation of complementary topological pairs. -/
def periodicCostalkPairTranslation :
    TopPair.ofSubset ((sourceRegion)ᶜ : Set (TopCat.of (Fin n → ℝ))) ⟶
      TopPair.ofSubset ((targetRegion)ᶜ : Set (TopCat.of (Fin n → ℝ))) :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨fun p => p + lift, by fun_prop⟩)
    (fun p outside inside => outside
      ((add_mem_costalkRegion_iff (augmentedForms matrix) S a shift lift
        (augmentedForms_latticeLift matrix z) x p).mp inside))

/-- The cellular and singular translation maps are the same under the
actual comparison, in every degree. -/
theorem periodicCostalkCellularSingularIso_translation (q : ℕ) :
    HomologicalComplex.homologyMap (periodicCostalkTranslation matrix S a x z M) q ≫
        (periodicCostalkCellularSingularIso matrix S (a + shift) (x + lift) M q).hom =
      (periodicCostalkCellularSingularIso matrix S a x M q).hom ≫
        TopPair.singularHomologyMap (periodicCostalkPairTranslation matrix S a x z) M q := by
  let B := periodicCostalkComplementSubcomplex matrix S a x
  let D := periodicCostalkComplementSubcomplex matrix S (a + shift) (x + lift)
  let C₁ := relativeCWCarrier B
  let C₂ := relativeCWCarrier D
  let hf := relativeCWMap_cellular B D (arrangementTranslation matrix z)
    (arrangementTranslation_cellular matrix z) (periodicCostalkTranslation_base matrix S a x z)
  have comparison :
      TauCeti.complexBasePairMap C₁ C₂ hf ≫
          (periodicCostalkPairIso matrix S (a + shift) (x + lift)).hom =
        (periodicCostalkPairIso matrix S a x).hom ≫
          periodicCostalkPairTranslation matrix S a x z := by
    apply TopPair.hom_ext_of_fst
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp,
      TauCeti.complexBasePairMap_fst,
      periodicCostalkPairIso_hom_fst, periodicCostalkPairIso_hom_fst]
    dsimp only [relativeCWMap, periodicCostalkPairTranslation]
    erw [TopPair.ofSubsetMap_fst]
    ext p
    rfl
  change HomologicalComplex.homologyMap
      (TauCeti.cellularChainComplexMap C₁ C₂ hf M) q ≫
        (TauCeti.cellularSingularHomologyIso C₂ M q).hom ≫
          TopPair.singularHomologyMap
            (periodicCostalkPairIso matrix S (a + shift) (x + lift)).hom M q =
    (TauCeti.cellularSingularHomologyIso C₁ M q).hom ≫
      TopPair.singularHomologyMap (periodicCostalkPairIso matrix S a x).hom M q ≫
        TopPair.singularHomologyMap (periodicCostalkPairTranslation matrix S a x z) M q
  rw [← Category.assoc, cellularSingularHomologyIso_natural,
    Category.assoc, ← TopPair.singularHomologyMap_comp, comparison,
    TopPair.singularHomologyMap_comp]

/-- Lattice translation sends the chosen top class to the same chosen
top class in the translated region. -/
theorem periodicCostalkCellHomologyIso_translation
    (nonemptySource : (sourceRegion).Nonempty) (nonemptyTarget : (targetRegion).Nonempty) :
    HomologicalComplex.homologyMap (periodicCostalkTranslation matrix S a x z M) n ≫
        (periodicCostalkCellHomologyIso matrix S (a + shift) (x + lift) M
          nonemptyTarget).hom =
      (periodicCostalkCellHomologyIso matrix S a x M nonemptySource).hom := by
  simp only [periodicCostalkCellHomologyIso, Iso.trans_hom]
  rw [← Category.assoc, periodicCostalkCellularSingularIso_translation, Category.assoc]
  congr 1
  exact convexComplementTopClassIso_translation_to M sourceRegion targetRegion lift
    (costalkRegion_convex (augmentedForms matrix) S a x)
    (costalkRegion_convex (augmentedForms matrix) S (a + shift) (x + lift))
    nonemptySource nonemptyTarget
    (augmentedCostalkRegion_bounded matrix S a x)
    (augmentedCostalkRegion_bounded matrix S (a + shift) (x + lift))
    (periodicCostalkRegion_translation matrix S a x z)
    (periodicCostalkPairTranslation matrix S a x z)
    (TopPair.ofSubsetMap_fst _ _)

end ToricPower.IntegralArrangement
