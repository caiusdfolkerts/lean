module

public import ToricPower.CellularHomologyNaturality
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Naturality of the actual cellular–singular comparison

The cellular comparison is built from skeletal pairs.  A cellular map
commutes with the inclusions of those actual pairs, and hence with their
relative singular homology.  The identities below establish naturality
first on cellular cycles and then on cellular homology.

This is needed to assemble weightwise diagonal augmentations into maps of
modules and sheaves.  Naturality is proved here, not supplied as an axiom.

Candidate until the complete cellular dependency closure compiles.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex

namespace ToricPower

universe w

section Relative

variable {X Y : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y] {D : Set X} {E : Set Y}
  (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : TauCeti.IsCellular C C' f)

/-- The naturality square of the inclusions from base pairs into skeletal
pairs commutes on the actual spaces. -/
theorem skeletonBaseToSkeletonPair_naturality (n : ℕ) :
    TauCeti.skeletonBasePairToSkeletonPair C n ≫ TauCeti.skeletonPairMap C C' hf n =
      TauCeti.skeletonBasePairMap C C' hf n ≫
        TauCeti.skeletonBasePairToSkeletonPair C' n := by
  exact (TauCeti.skeletonBasePairMap_comp_toSkeletonPair C C' hf n).symm

/-- The inclusion of a base pair into the whole complex is natural for
the actual restrictions of any cellular map. -/
theorem skeletonBaseToComplex_naturality (n : ℕ) :
    TauCeti.skeletonBasePairToComplex C n ≫ TauCeti.complexBasePairMap C C' hf =
      TauCeti.skeletonBasePairMap C C' hf n ≫
        TauCeti.skeletonBasePairToComplex C' n := by
  exact (TauCeti.skeletonBasePairMap_comp_toComplex C C' hf n).symm

variable {R : Type w} [Ring R] (M : ModuleCat.{w} R)

/-- The cycles identification is natural.  The proof uses uniqueness of
maps into the actual cycles kernel. -/
theorem cellularCyclesIso_inv_naturality (n : ℕ) :
    (TauCeti.cellularCyclesIso C M n).inv ≫
        HomologicalComplex.cyclesMap (TauCeti.cellularChainComplexMap C C' hf M) n =
      TopPair.singularHomologyMap (TauCeti.skeletonBasePairMap C C' hf n) M n ≫
        (TauCeti.cellularCyclesIso C' M n).inv := by
  exact cellularCyclesIso_inv_natural C C' hf M n

/-- The forward cycles identification is natural as well. -/
theorem cellularCyclesIso_hom_naturality (n : ℕ) :
    HomologicalComplex.cyclesMap (TauCeti.cellularChainComplexMap C C' hf M) n ≫
        (TauCeti.cellularCyclesIso C' M n).hom =
      (TauCeti.cellularCyclesIso C M n).hom ≫
        TopPair.singularHomologyMap (TauCeti.skeletonBasePairMap C C' hf n) M n := by
  exact cellularCyclesIso_natural C C' hf M n

/-- The actual cellular–singular homology isomorphism is natural for every
cellular map, with no dimension or cell-count restriction. -/
theorem cellularSingularHomologyIso_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (TauCeti.cellularChainComplexMap C C' hf M) n ≫
        (TauCeti.cellularSingularHomologyIso C' M n).hom =
      (TauCeti.cellularSingularHomologyIso C M n).hom ≫
        TopPair.singularHomologyMap (TauCeti.complexBasePairMap C C' hf) M n := by
  exact cellularSingularHomologyIso_natural C C' hf M n

end Relative

section Absolute

variable {X Y : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y]
  (C : Set X) [CWComplex C] (C' : Set Y) [CWComplex C']
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : TauCeti.IsCellular C C' f)
  {R : Type w} [Ring R] (M : ModuleCat.{w} R)

/-- The absolute comparison is the relative comparison followed by the
inverse of the actual quotient modulo the empty base. -/
def absoluteCellularSingularIso (n : ℕ) :
    (TauCeti.cellularChainComplex C M).homology n ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) n).obj M).obj
        (TopCat.of C) := by
  letI : IsEmpty (TauCeti.complexBasePair C).snd :=
    TauCeti.isEmpty_complexBasePair_snd C
  exact TauCeti.cellularSingularHomologyIso C M n ≪≫
    (asIso ((TauCeti.complexBasePair C).singularHomologyπ M n)).symm

/-- Passing from relative to absolute homology preserves the naturality
square because the quotient maps of the actual pairs are natural. -/
theorem absoluteCellularSingularIso_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (TauCeti.cellularChainComplexMap C C' hf M) n ≫
        (absoluteCellularSingularIso C' M n).hom =
      (absoluteCellularSingularIso C M n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) n).obj M).map f := by
  letI : IsEmpty (TauCeti.complexBasePair C).snd :=
    TauCeti.isEmpty_complexBasePair_snd C
  letI : IsEmpty (TauCeti.complexBasePair C').snd :=
    TauCeti.isEmpty_complexBasePair_snd C'
  have hπ := SSetPair.homologyπ_naturality
    (TopPair.toSSetPair.map (TauCeti.complexBasePairMap C C' hf)) M n
  rw [TopPair.toSSetPair_map_right, TauCeti.complexBasePairMap_fst] at hπ
  change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) n).obj M).map f ≫
      (TauCeti.complexBasePair C').singularHomologyπ M n =
    (TauCeti.complexBasePair C).singularHomologyπ M n ≫
      TopPair.singularHomologyMap (TauCeti.complexBasePairMap C C' hf) M n at hπ
  apply (cancel_mono ((TauCeti.complexBasePair C').singularHomologyπ M n)).mp
  dsimp only [absoluteCellularSingularIso, Iso.trans_hom, Iso.symm_hom,
    asIso_inv]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hπ]
  simp only [IsIso.inv_hom_id_assoc]
  exact cellularSingularHomologyIso_naturality C C' hf M n

end Absolute

end ToricPower
