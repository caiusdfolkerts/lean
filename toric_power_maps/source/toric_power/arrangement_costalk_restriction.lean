module

public import ToricPower.ArrangementCostalkCellular
public import ToricPower.CWRelativeSubcomplexMap

/-!
# Actual cellular support restriction for costalks

An inclusion of the literal open regions gives the identity map of the
ambient space, with increasing complementary base. The resulting maps
are actual cellular chain maps, preserve identities and composition, and
commute with the cellular–singular comparison and the fixed ambient
top class. There is no chosen map on homology substituted for a chain map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)
  {k : Type} [Ring k] (M : ModuleCat.{0} k)

local instance costalkRestrictionPeriodicCW : CWComplex (arrangementCarrier matrix) :=
  periodicArrangementCWComplex matrix

variable (S T U : Set (Fin s ⊕ Fin n))
  (a b c : Fin s ⊕ Fin n → ℤ) (x y z : Fin n → ℝ)

/-- The chosen relative carrier has the literal complementary pair. -/
def periodicCostalkPairIso :
    TauCeti.complexBasePair
        (relativeCWCarrier (periodicCostalkComplementSubcomplex matrix S a x)) ≅
      TopPair.ofSubset ((costalkRegion (augmentedForms matrix) S a x)ᶜ :
        Set (TopCat.of (Fin n → ℝ))) := by
  letI : RelCWComplex (univ : Set (Fin n → ℝ))
      (costalkRegion (augmentedForms matrix) S a x)ᶜ :=
    periodicCostalkRelativeCWComplex matrix S a x
  exact relativeUnivBasePairIso

@[simp]
theorem periodicCostalkPairIso_hom_fst :
    TopPair.Hom.fst (periodicCostalkPairIso matrix S a x).hom =
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := by
  letI : RelCWComplex (univ : Set (Fin n → ℝ))
      (costalkRegion (augmentedForms matrix) S a x)ᶜ :=
    periodicCostalkRelativeCWComplex matrix S a x
  exact relativeUnivBasePairIso_hom_fst

/-- The actual complementary subcomplex inclusion reverses the open
support inclusion. -/
theorem periodicCostalkComplement_le
    (h : costalkRegion (augmentedForms matrix) S a x ⊆
      costalkRegion (augmentedForms matrix) T b y) :
    periodicCostalkComplementSubcomplex matrix T b y ≤
      periodicCostalkComplementSubcomplex matrix S a x :=
  fun _ outside inside => outside (h inside)

/-- Support restriction is the actual chain map of the relative pairs.
Its direction is from the larger open support to the smaller support. -/
def periodicCostalkRestriction
    (h : costalkRegion (augmentedForms matrix) S a x ⊆
      costalkRegion (augmentedForms matrix) T b y) :
    periodicCostalkCellComplex matrix T b y M ⟶
      periodicCostalkCellComplex matrix S a x M :=
  relativeCellularMap M
    (periodicCostalkComplementSubcomplex matrix T b y)
    (periodicCostalkComplementSubcomplex matrix S a x)
    (periodicCostalkComplement_le matrix S T a b x y h)

@[simp]
theorem periodicCostalkRestriction_id :
    periodicCostalkRestriction matrix M S S a a x x subset_rfl =
      𝟙 (periodicCostalkCellComplex matrix S a x M) :=
  relativeCellularMap_id M (periodicCostalkComplementSubcomplex matrix S a x)

/-- Actual support restrictions compose before passing to homology. -/
theorem periodicCostalkRestriction_comp
    (hST : costalkRegion (augmentedForms matrix) S a x ⊆
      costalkRegion (augmentedForms matrix) T b y)
    (hTU : costalkRegion (augmentedForms matrix) T b y ⊆
      costalkRegion (augmentedForms matrix) U c z) :
    periodicCostalkRestriction matrix M S U a c x z (hST.trans hTU) =
      periodicCostalkRestriction matrix M T U b c y z hTU ≫
        periodicCostalkRestriction matrix M S T a b x y hST :=
  relativeCellularMap_comp M _ _ _
    (periodicCostalkComplement_le matrix T U b c y z hTU)
    (periodicCostalkComplement_le matrix S T a b x y hST)

/-- The cellular comparison commutes with the literal complementary
pair map induced by the same ambient identity. -/
theorem periodicCostalkCellularSingularIso_natural
    (h : costalkRegion (augmentedForms matrix) S a x ⊆
      costalkRegion (augmentedForms matrix) T b y) (q : ℕ) :
    HomologicalComplex.homologyMap
        (periodicCostalkRestriction matrix M S T a b x y h) q ≫
        (periodicCostalkCellularSingularIso matrix S a x M q).hom =
      (periodicCostalkCellularSingularIso matrix T b y M q).hom ≫
        TopPair.singularHomologyMap (complementRestriction h) M q := by
  let B := periodicCostalkComplementSubcomplex matrix T b y
  let D := periodicCostalkComplementSubcomplex matrix S a x
  let hBD : B ≤ D := periodicCostalkComplement_le matrix S T a b x y h
  let C₁ := relativeCWCarrier B
  let C₂ := relativeCWCarrier D
  let hf := relativeBaseInclusion_cellular B D hBD
  have comparison :
      TauCeti.complexBasePairMap C₁ C₂ hf ≫
          (periodicCostalkPairIso matrix S a x).hom =
        (periodicCostalkPairIso matrix T b y).hom ≫
            complementRestriction h := by
    apply TopPair.hom_ext_of_fst
    change TopPair.proj₁.map (TauCeti.complexBasePairMap C₁ C₂ hf ≫
        (periodicCostalkPairIso matrix S a x).hom) =
      TopPair.proj₁.map ((periodicCostalkPairIso matrix T b y).hom ≫
        complementRestriction h)
    rw [TopPair.proj₁.map_comp, TopPair.proj₁.map_comp]
    change TopPair.Hom.fst (TauCeti.complexBasePairMap C₁ C₂ hf) ≫
        TopPair.Hom.fst (periodicCostalkPairIso matrix S a x).hom =
      TopPair.Hom.fst (periodicCostalkPairIso matrix T b y).hom ≫
        TopPair.Hom.fst (complementRestriction h)
    rw [TauCeti.complexBasePairMap_fst,
      periodicCostalkPairIso_hom_fst, periodicCostalkPairIso_hom_fst]
    dsimp only [relativeBaseInclusion, complementRestriction]
    erw [TopPair.ofSubsetMap_fst]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  change HomologicalComplex.homologyMap
      (TauCeti.cellularChainComplexMap C₁ C₂ hf M) q ≫
        (TauCeti.cellularSingularHomologyIso C₂ M q).hom ≫
          TopPair.singularHomologyMap
            (periodicCostalkPairIso matrix S a x).hom M q =
    (TauCeti.cellularSingularHomologyIso C₁ M q).hom ≫
      TopPair.singularHomologyMap
        (periodicCostalkPairIso matrix T b y).hom M q ≫
        TopPair.singularHomologyMap (complementRestriction h) M q
  rw [← Category.assoc, cellularSingularHomologyIso_natural,
    Category.assoc, ← TopPair.singularHomologyMap_comp, comparison,
    TopPair.singularHomologyMap_comp]

/-- The chosen top-class identification is natural for the actual
cellular chain maps whenever both open regions are nonempty. -/
theorem periodicCostalkCellHomologyIso_natural
    (h : costalkRegion (augmentedForms matrix) S a x ⊆
      costalkRegion (augmentedForms matrix) T b y)
    (nonemptyS : (costalkRegion (augmentedForms matrix) S a x).Nonempty)
    (nonemptyT : (costalkRegion (augmentedForms matrix) T b y).Nonempty) :
    HomologicalComplex.homologyMap
        (periodicCostalkRestriction matrix M S T a b x y h) n ≫
        (periodicCostalkCellHomologyIso matrix S a x M nonemptyS).hom =
      (periodicCostalkCellHomologyIso matrix T b y M nonemptyT).hom := by
  simp only [periodicCostalkCellHomologyIso, Iso.trans_hom]
  rw [← Category.assoc, periodicCostalkCellularSingularIso_natural,
    Category.assoc]
  congr 1
  exact convexComplementTopClassIso_natural M h
    (costalkRegion_convex (augmentedForms matrix) S a x)
    (costalkRegion_convex (augmentedForms matrix) T b y)
    nonemptyS nonemptyT
    (augmentedCostalkRegion_bounded matrix S a x)
    (augmentedCostalkRegion_bounded matrix T b y)

end ToricPower.IntegralArrangement
