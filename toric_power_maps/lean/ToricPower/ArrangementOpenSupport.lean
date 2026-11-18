module

public import ToricPower.ArrangementCostalkCellular
public import ToricPower.CWRelativeSubcomplexMap
public import ToricPower.LinearDualHomologyClass

/-!
# Actual relative cellular cochains of open arrangement supports

Every open union of cells supplies its literal closed complementary
subcomplex. Increasing the support induces the actual relative cellular
chain map in the opposite direction, and hence the actual cochain map.
For bounded convex supports the ambient orientation computes cohomology
and is natural for these maps. This is the finite-stage calculation for
compact support; no duality statement for an infinite direct sum occurs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local instance openSupportPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

/-- An actual open union of cells, with its inherited inclusion order. -/
def OpenCellSupport := {U : TopologicalSpace.Opens (Fin n → ℝ) //
  Cellwise (augmentedForms A) (U : Set (Fin n → ℝ))}

instance : PartialOrder (OpenCellSupport A) := inferInstanceAs
  (PartialOrder {U : TopologicalSpace.Opens (Fin n → ℝ) //
    Cellwise (augmentedForms A) (U : Set (Fin n → ℝ))})

/-- The base retains the original periodic characteristic maps. -/
def openSupportComplement (U : OpenCellSupport A) :
    CWComplex.Subcomplex (arrangementCarrier A) :=
  periodicCellwiseSubcomplex A (U.val : Set (Fin n → ℝ))ᶜ
    U.val.isOpen.isClosed_compl U.property.compl

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)

/-- Actual relative cellular chains, including the original differential. -/
def openSupportChainComplex (U : OpenCellSupport A) : ChainComplex (ModuleCat R) ℕ :=
  relativeCellularComplex M (openSupportComplement A U)

/-- Increasing the support gives the literal complementary base inclusion. -/
theorem openSupportComplement_antitone {U V : OpenCellSupport A} (h : U ≤ V) :
    openSupportComplement A V ≤ openSupportComplement A U :=
  fun _ outside inside => outside (h inside)

/-- The ambient identity gives actual support restriction on chains. -/
def openSupportChainRestriction {U V : OpenCellSupport A} (h : U ≤ V) :
    openSupportChainComplex A M V ⟶ openSupportChainComplex A M U :=
  relativeCellularMap M _ _ (openSupportComplement_antitone A h)

@[simp]
theorem openSupportChainRestriction_id (U : OpenCellSupport A) :
    openSupportChainRestriction A M (le_rfl : U ≤ U) = 𝟙 _ :=
  relativeCellularMap_id M _

@[reassoc]
theorem openSupportChainRestriction_comp {U V W : OpenCellSupport A}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    openSupportChainRestriction A M (hUV.trans hVW) =
      openSupportChainRestriction A M hVW ≫ openSupportChainRestriction A M hUV :=
  relativeCellularMap_comp M _ _ _
    (openSupportComplement_antitone A hVW) (openSupportComplement_antitone A hUV)

/-- Cellular chains form a contravariant functor on actual open supports. -/
def openSupportChainFunctor : (OpenCellSupport A)ᵒᵖ ⥤ ChainComplex (ModuleCat R) ℕ where
  obj U := openSupportChainComplex A M U.unop
  map f := openSupportChainRestriction A M f.unop.le
  map_id U := openSupportChainRestriction_id A M U.unop
  map_comp f g := openSupportChainRestriction_comp A M g.unop.le f.unop.le

/-- The literal complementary pair of the chosen relative structure. -/
def openSupportPairIso (U : OpenCellSupport A) :
    TauCeti.complexBasePair (relativeCWCarrier (openSupportComplement A U)) ≅
      TopPair.ofSubset ((U.val : Set (Fin n → ℝ))ᶜ :
        Set (TopCat.of (Fin n → ℝ))) := by
  letI : RelCWComplex (univ : Set (Fin n → ℝ)) (U.val : Set (Fin n → ℝ))ᶜ :=
    relativeToSubcomplex (openSupportComplement A U)
  exact relativeUnivBasePairIso

@[simp]
theorem openSupportPairIso_hom_fst (U : OpenCellSupport A) :
    TopPair.Hom.fst (openSupportPairIso A U).hom =
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := by
  letI : RelCWComplex (univ : Set (Fin n → ℝ)) (U.val : Set (Fin n → ℝ))ᶜ :=
    relativeToSubcomplex (openSupportComplement A U)
  exact relativeUnivBasePairIso_hom_fst

/-- Actual cellular--singular comparison for the literal support pair. -/
def openSupportCellularSingularIso (U : OpenCellSupport A) (q : ℕ) :
    (openSupportChainComplex A M U).homology q ≅
      (TopPair.ofSubset ((U.val : Set (Fin n → ℝ))ᶜ :
        Set (TopCat.of (Fin n → ℝ)))).singularHomology M q :=
  TauCeti.cellularSingularHomologyIso
      (relativeCWCarrier (openSupportComplement A U)) M q ≪≫
    topPairHomologyIso (openSupportPairIso A U) M q

/-- The actual support map commutes with the actual pair comparison. -/
theorem openSupportCellularSingularIso_natural
    {U V : OpenCellSupport A} (h : U ≤ V) (q : ℕ) :
    HomologicalComplex.homologyMap (openSupportChainRestriction A M h) q ≫
        (openSupportCellularSingularIso A M U q).hom =
      (openSupportCellularSingularIso A M V q).hom ≫
        TopPair.singularHomologyMap (complementRestriction h) M q := by
  let B := openSupportComplement A V
  let D := openSupportComplement A U
  let hBD : B ≤ D := openSupportComplement_antitone A h
  let C₁ := relativeCWCarrier B
  let C₂ := relativeCWCarrier D
  let hf := relativeBaseInclusion_cellular B D hBD
  have comparison :
      TauCeti.complexBasePairMap C₁ C₂ hf ≫ (openSupportPairIso A U).hom =
        (openSupportPairIso A V).hom ≫ complementRestriction h := by
    apply TopPair.hom_ext_of_fst
    change TopPair.proj₁.map (TauCeti.complexBasePairMap C₁ C₂ hf ≫
        (openSupportPairIso A U).hom) =
      TopPair.proj₁.map ((openSupportPairIso A V).hom ≫ complementRestriction h)
    rw [TopPair.proj₁.map_comp, TopPair.proj₁.map_comp]
    change TopPair.Hom.fst (TauCeti.complexBasePairMap C₁ C₂ hf) ≫
        TopPair.Hom.fst (openSupportPairIso A U).hom =
      TopPair.Hom.fst (openSupportPairIso A V).hom ≫
        TopPair.Hom.fst (complementRestriction h)
    rw [TauCeti.complexBasePairMap_fst, openSupportPairIso_hom_fst,
      openSupportPairIso_hom_fst]
    dsimp only [relativeBaseInclusion, complementRestriction]
    erw [TopPair.ofSubsetMap_fst]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  change HomologicalComplex.homologyMap
      (TauCeti.cellularChainComplexMap C₁ C₂ hf M) q ≫
        (TauCeti.cellularSingularHomologyIso C₂ M q).hom ≫
          TopPair.singularHomologyMap (openSupportPairIso A U).hom M q =
    (TauCeti.cellularSingularHomologyIso C₁ M q).hom ≫
      TopPair.singularHomologyMap (openSupportPairIso A V).hom M q ≫
        TopPair.singularHomologyMap (complementRestriction h) M q
  rw [← Category.assoc, cellularSingularHomologyIso_natural, Category.assoc,
    ← TopPair.singularHomologyMap_comp, comparison, TopPair.singularHomologyMap_comp]

/-- The fixed ambient orientation computes every nonempty bounded
convex open support. -/
def openSupportChainTopClassIso (U : OpenCellSupport A)
    (convex : Convex ℝ (U.val : Set (Fin n → ℝ)))
    (nonempty : (U.val : Set (Fin n → ℝ)).Nonempty)
    (bounded : Bornology.IsBounded (U.val : Set (Fin n → ℝ))) :
    (openSupportChainComplex A M U).homology n ≅ M :=
  openSupportCellularSingularIso A M U n ≪≫
    convexComplementTopClassIso M _ convex nonempty bounded

theorem openSupportChainComplex_isZero_homology (U : OpenCellSupport A)
    (convex : Convex ℝ (U.val : Set (Fin n → ℝ)))
    (nonempty : (U.val : Set (Fin n → ℝ)).Nonempty)
    (bounded : Bornology.IsBounded (U.val : Set (Fin n → ℝ)))
    (q : ℕ) (different : q ≠ n) :
    IsZero ((openSupportChainComplex A M U).homology q) :=
  (convexComplementHomology_isZero M _ convex nonempty bounded q different).of_iso
    (openSupportCellularSingularIso A M U q)

theorem openSupportChainTopClassIso_natural {U V : OpenCellSupport A} (h : U ≤ V)
    (convexU : Convex ℝ (U.val : Set (Fin n → ℝ)))
    (convexV : Convex ℝ (V.val : Set (Fin n → ℝ)))
    (nonemptyU : (U.val : Set (Fin n → ℝ)).Nonempty)
    (nonemptyV : (V.val : Set (Fin n → ℝ)).Nonempty)
    (boundedU : Bornology.IsBounded (U.val : Set (Fin n → ℝ)))
    (boundedV : Bornology.IsBounded (V.val : Set (Fin n → ℝ))) :
    HomologicalComplex.homologyMap (openSupportChainRestriction A M h) n ≫
        (openSupportChainTopClassIso A M U convexU nonemptyU boundedU).hom =
      (openSupportChainTopClassIso A M V convexV nonemptyV boundedV).hom := by
  simp only [openSupportChainTopClassIso, Iso.trans_hom]
  rw [← Category.assoc, openSupportCellularSingularIso_natural, Category.assoc]
  congr 1
  exact convexComplementTopClassIso_natural M h convexU convexV
    nonemptyU nonemptyV boundedU boundedV

section Field

variable (k : Type) [Field k]

/-- Scalar cochains of the actual relative chain complex. Finite windows
will be proved finite before this dual is identified with finite support. -/
def openSupportCochainComplex (U : OpenCellSupport A) : CochainComplex (ModuleCat k) ℕ :=
  scalarDualComplex k (openSupportChainComplex A (ModuleCat.of k k) U)

def openSupportCochainExtension {U V : OpenCellSupport A} (h : U ≤ V) :
    openSupportCochainComplex A k U ⟶ openSupportCochainComplex A k V :=
  scalarDualMap k (openSupportChainRestriction A (ModuleCat.of k k) h)

/-- The exact scalar-dual ambient top class. -/
def openSupportCochainTopClassIso (U : OpenCellSupport A)
    (convex : Convex ℝ (U.val : Set (Fin n → ℝ)))
    (nonempty : (U.val : Set (Fin n → ℝ)).Nonempty)
    (bounded : Bornology.IsBounded (U.val : Set (Fin n → ℝ))) :
    (openSupportCochainComplex A k U).homology n ≅ ModuleCat.of k k :=
  scalarDualHomologyClassIso k _ n
    (openSupportChainTopClassIso A (ModuleCat.of k k) U convex nonempty bounded)

theorem openSupportCochainComplex_isZero_homology (U : OpenCellSupport A)
    (convex : Convex ℝ (U.val : Set (Fin n → ℝ)))
    (nonempty : (U.val : Set (Fin n → ℝ)).Nonempty)
    (bounded : Bornology.IsBounded (U.val : Set (Fin n → ℝ)))
    (q : ℕ) (different : q ≠ n) :
    IsZero ((openSupportCochainComplex A k U).homology q) :=
  scalarDualComplex_isZero_homology k _ q
    (openSupportChainComplex_isZero_homology A (ModuleCat.of k k) U
      convex nonempty bounded q different)

theorem openSupportCochainTopClassIso_natural {U V : OpenCellSupport A} (h : U ≤ V)
    (convexU : Convex ℝ (U.val : Set (Fin n → ℝ)))
    (convexV : Convex ℝ (V.val : Set (Fin n → ℝ)))
    (nonemptyU : (U.val : Set (Fin n → ℝ)).Nonempty)
    (nonemptyV : (V.val : Set (Fin n → ℝ)).Nonempty)
    (boundedU : Bornology.IsBounded (U.val : Set (Fin n → ℝ)))
    (boundedV : Bornology.IsBounded (V.val : Set (Fin n → ℝ))) :
    HomologicalComplex.homologyMap (openSupportCochainExtension A k h) n ≫
        (openSupportCochainTopClassIso A k V convexV nonemptyV boundedV).hom =
      (openSupportCochainTopClassIso A k U convexU nonemptyU boundedU).hom :=
  scalarDualHomologyClassIso_natural k _ n _ _
    (openSupportChainTopClassIso_natural A (ModuleCat.of k k) h convexU convexV
      nonemptyU nonemptyV boundedU boundedV)

end Field
end ToricPower.IntegralArrangement
