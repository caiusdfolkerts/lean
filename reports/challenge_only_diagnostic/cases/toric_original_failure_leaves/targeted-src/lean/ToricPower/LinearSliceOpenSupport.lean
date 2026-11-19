module

public import ToricPower.LinearSliceCellularHomology
public import ToricPower.ArrangementOpenSupport

/-! # Natural intrinsic support maps on the actual closed linear slice

All chains use the original periodic characteristic disks. Increasing
the ambient open support gives the actual relative chain restriction;
scalar duality gives its actual cochain extension. The chosen intrinsic
orientation intertwines these maps, including in dimension zero.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set Opposite

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (zeroRows : Set (Fin s ⊕ Fin n))

local notation "E" => Fin n → ℝ
local notation "L" => arrangementZeroSlice (augmentedForms A) zeroRows

local instance sliceSupportAmbientCW : CWComplex (arrangementCarrier A) := periodicArrangementCWComplex A
local instance sliceSupportInheritedCW : CWComplex (L : Set E) :=
  inferInstanceAs (CWComplex (periodicLinearSliceSubcomplex A zeroRows : Set E))

def sliceSupportComplement (U : OpenCellSupport A) : CWComplex.Subcomplex (L : Set E) :=
  periodicSliceComplementWithin A zeroRows U.val U.val.isOpen U.property

theorem sliceSupportComplement_antitone {U V : OpenCellSupport A} (h : U ≤ V) :
    sliceSupportComplement A zeroRows V ≤ sliceSupportComplement A zeroRows U :=
  fun _ hx => ⟨hx.1,fun hu => hx.2 (h hu)⟩

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)

def sliceSupportChainComplex (U : OpenCellSupport A) : ChainComplex (ModuleCat R) ℕ :=
  relativeCellularComplex M (sliceSupportComplement A zeroRows U)

def sliceSupportChainRestriction {U V : OpenCellSupport A} (h : U ≤ V) :
    sliceSupportChainComplex A zeroRows M V ⟶ sliceSupportChainComplex A zeroRows M U :=
  relativeCellularMap M _ _ (sliceSupportComplement_antitone A zeroRows h)

@[simp]
theorem sliceSupportChainRestriction_id (U : OpenCellSupport A) :
    sliceSupportChainRestriction A zeroRows M (le_rfl : U ≤ U) = 𝟙 _ :=
  relativeCellularMap_id M _

@[reassoc]
theorem sliceSupportChainRestriction_comp {U V W : OpenCellSupport A}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    sliceSupportChainRestriction A zeroRows M (hUV.trans hVW) =
      sliceSupportChainRestriction A zeroRows M hVW ≫
        sliceSupportChainRestriction A zeroRows M hUV :=
  relativeCellularMap_comp M _ _ _
    (sliceSupportComplement_antitone A zeroRows hVW)
    (sliceSupportComplement_antitone A zeroRows hUV)

def sliceSupportChainFunctor : (OpenCellSupport A)ᵒᵖ ⥤ ChainComplex (ModuleCat R) ℕ where
  obj U := sliceSupportChainComplex A zeroRows M U.unop
  map f := sliceSupportChainRestriction A zeroRows M f.unop.le
  map_id U := sliceSupportChainRestriction_id A zeroRows M U.unop
  map_comp f g := sliceSupportChainRestriction_comp A zeroRows M g.unop.le f.unop.le

def sliceSupportPairIso (U : OpenCellSupport A) :
    TauCeti.complexBasePair (relativeCWCarrier (sliceSupportComplement A zeroRows U)) ≅
      TopPair.ofSubset ((Subtype.val ⁻¹' (U.val : Set E))ᶜ : Set (TopCat.of L)) := by
  letI := periodicLinearSliceRelativeCW A zeroRows U.val U.val.isOpen U.property
  exact relativeSubsetBasePairIso (L : Set E) U.val

@[simp]
theorem sliceSupportPairIso_hom_fst (U : OpenCellSupport A) :
    TopPair.Hom.fst (sliceSupportPairIso A zeroRows U).hom = 𝟙 (TopCat.of L) := by
  letI := periodicLinearSliceRelativeCW A zeroRows U.val U.val.isOpen U.property
  exact relativeSubsetBasePairIso_hom_fst (L : Set E) U.val

def sliceSupportCellularSingularIso (U : OpenCellSupport A) (q : ℕ) :
    (sliceSupportChainComplex A zeroRows M U).homology q ≅
      (TopPair.ofSubset ((Subtype.val ⁻¹' (U.val : Set E))ᶜ :
        Set (TopCat.of L))).singularHomology M q :=
  TauCeti.cellularSingularHomologyIso
      (relativeCWCarrier (sliceSupportComplement A zeroRows U)) M q ≪≫
    topPairHomologyIso (sliceSupportPairIso A zeroRows U) M q

theorem sliceSupportCellularSingularIso_natural {U V : OpenCellSupport A}
    (h : U ≤ V) (q : ℕ) :
    HomologicalComplex.homologyMap (sliceSupportChainRestriction A zeroRows M h) q ≫
        (sliceSupportCellularSingularIso A zeroRows M U q).hom =
      (sliceSupportCellularSingularIso A zeroRows M V q).hom ≫
        TopPair.singularHomologyMap
          (complementRestriction (Set.preimage_mono h)) M q := by
  let B := sliceSupportComplement A zeroRows V
  let D := sliceSupportComplement A zeroRows U
  let hBD : B ≤ D := sliceSupportComplement_antitone A zeroRows h
  let C₁ := relativeCWCarrier B
  let C₂ := relativeCWCarrier D
  let hf := relativeBaseInclusion_cellular B D hBD
  have comparison :
      TauCeti.complexBasePairMap C₁ C₂ hf ≫ (sliceSupportPairIso A zeroRows U).hom =
        (sliceSupportPairIso A zeroRows V).hom ≫
          complementRestriction (Set.preimage_mono h) := by
    apply TopPair.hom_ext_of_fst
    change TopPair.proj₁.map (TauCeti.complexBasePairMap C₁ C₂ hf ≫
        (sliceSupportPairIso A zeroRows U).hom) =
      TopPair.proj₁.map ((sliceSupportPairIso A zeroRows V).hom ≫
        complementRestriction (Set.preimage_mono h))
    rw [TopPair.proj₁.map_comp,TopPair.proj₁.map_comp]
    change TopPair.Hom.fst (TauCeti.complexBasePairMap C₁ C₂ hf) ≫
        TopPair.Hom.fst (sliceSupportPairIso A zeroRows U).hom =
      TopPair.Hom.fst (sliceSupportPairIso A zeroRows V).hom ≫
        TopPair.Hom.fst (complementRestriction (Set.preimage_mono h))
    rw [TauCeti.complexBasePairMap_fst,sliceSupportPairIso_hom_fst,
      sliceSupportPairIso_hom_fst]
    dsimp only [relativeBaseInclusion,complementRestriction]
    erw [TopPair.ofSubsetMap_fst]
    rfl
  change HomologicalComplex.homologyMap
      (TauCeti.cellularChainComplexMap C₁ C₂ hf M) q ≫
        (TauCeti.cellularSingularHomologyIso C₂ M q).hom ≫
          TopPair.singularHomologyMap (sliceSupportPairIso A zeroRows U).hom M q =
    (TauCeti.cellularSingularHomologyIso C₁ M q).hom ≫
      TopPair.singularHomologyMap (sliceSupportPairIso A zeroRows V).hom M q ≫
        TopPair.singularHomologyMap (complementRestriction (Set.preimage_mono h)) M q
  rw [← Category.assoc,cellularSingularHomologyIso_natural,Category.assoc,
    ← TopPair.singularHomologyMap_comp,comparison,TopPair.singularHomologyMap_comp]

def sliceSupportChainTopClassIso (U : OpenCellSupport A)
    (convexU : Convex ℝ (U.val : Set E))
    (nonemptyU : (Subtype.val ⁻¹' (U.val : Set E) : Set L).Nonempty)
    (boundedU : Bornology.IsBounded (U.val : Set E)) :
    (sliceSupportChainComplex A zeroRows M U).homology (Module.finrank ℝ L) ≅ M :=
  sliceSupportCellularSingularIso A zeroRows M U (Module.finrank ℝ L) ≪≫
    intrinsicConvexTopClassIso M _ (convexU.linear_preimage (L).subtype) nonemptyU
      (isometry_subtype_coe.antilipschitz.isBounded_preimage boundedU)

theorem sliceSupportChainComplex_isZero_homology (U : OpenCellSupport A)
    (convexU : Convex ℝ (U.val : Set E))
    (nonemptyU : (Subtype.val ⁻¹' (U.val : Set E) : Set L).Nonempty)
    (boundedU : Bornology.IsBounded (U.val : Set E))
    (q : ℕ) (different : q ≠ Module.finrank ℝ L) :
    IsZero ((sliceSupportChainComplex A zeroRows M U).homology q) :=
  (intrinsicConvexHomology_isZero M _ (convexU.linear_preimage (L).subtype) nonemptyU
    (isometry_subtype_coe.antilipschitz.isBounded_preimage boundedU) q different).of_iso
      (sliceSupportCellularSingularIso A zeroRows M U q)

theorem sliceSupportChainTopClassIso_natural {U V : OpenCellSupport A} (h : U ≤ V)
    (convexU : Convex ℝ (U.val : Set E)) (convexV : Convex ℝ (V.val : Set E))
    (nonemptyU : (Subtype.val ⁻¹' (U.val : Set E) : Set L).Nonempty)
    (nonemptyV : (Subtype.val ⁻¹' (V.val : Set E) : Set L).Nonempty)
    (boundedU : Bornology.IsBounded (U.val : Set E))
    (boundedV : Bornology.IsBounded (V.val : Set E)) :
    HomologicalComplex.homologyMap (sliceSupportChainRestriction A zeroRows M h)
        (Module.finrank ℝ L) ≫
      (sliceSupportChainTopClassIso A zeroRows M U convexU nonemptyU boundedU).hom =
        (sliceSupportChainTopClassIso A zeroRows M V convexV nonemptyV boundedV).hom := by
  simp only [sliceSupportChainTopClassIso,Iso.trans_hom]
  rw [← Category.assoc,sliceSupportCellularSingularIso_natural,Category.assoc]
  congr 1
  exact intrinsicConvexTopClassIso_natural M (Set.preimage_mono h)
    (convexU.linear_preimage (L).subtype) (convexV.linear_preimage (L).subtype)
    nonemptyU nonemptyV
    (isometry_subtype_coe.antilipschitz.isBounded_preimage boundedU)
    (isometry_subtype_coe.antilipschitz.isBounded_preimage boundedV)

section Field

variable (k : Type) [Field k]

def sliceSupportCochainComplex (U : OpenCellSupport A) : CochainComplex (ModuleCat k) ℕ :=
  scalarDualComplex k (sliceSupportChainComplex A zeroRows (ModuleCat.of k k) U)

def sliceSupportCochainExtension {U V : OpenCellSupport A} (h : U ≤ V) :
    sliceSupportCochainComplex A zeroRows k U ⟶ sliceSupportCochainComplex A zeroRows k V :=
  scalarDualMap k (sliceSupportChainRestriction A zeroRows (ModuleCat.of k k) h)

def sliceSupportCochainTopClassIso (U : OpenCellSupport A)
    (convexU : Convex ℝ (U.val : Set E))
    (nonemptyU : (Subtype.val ⁻¹' (U.val : Set E) : Set L).Nonempty)
    (boundedU : Bornology.IsBounded (U.val : Set E)) :
    (sliceSupportCochainComplex A zeroRows k U).homology (Module.finrank ℝ L) ≅
      ModuleCat.of k k :=
  scalarDualHomologyClassIso k _ (Module.finrank ℝ L)
    (sliceSupportChainTopClassIso A zeroRows (ModuleCat.of k k) U convexU nonemptyU boundedU)

theorem sliceSupportCochainComplex_isZero_homology (U : OpenCellSupport A)
    (convexU : Convex ℝ (U.val : Set E))
    (nonemptyU : (Subtype.val ⁻¹' (U.val : Set E) : Set L).Nonempty)
    (boundedU : Bornology.IsBounded (U.val : Set E))
    (q : ℕ) (different : q ≠ Module.finrank ℝ L) :
    IsZero ((sliceSupportCochainComplex A zeroRows k U).homology q) :=
  scalarDualComplex_isZero_homology k _ q
    (sliceSupportChainComplex_isZero_homology A zeroRows (ModuleCat.of k k) U
      convexU nonemptyU boundedU q different)

theorem sliceSupportCochainTopClassIso_natural {U V : OpenCellSupport A} (h : U ≤ V)
    (convexU : Convex ℝ (U.val : Set E)) (convexV : Convex ℝ (V.val : Set E))
    (nonemptyU : (Subtype.val ⁻¹' (U.val : Set E) : Set L).Nonempty)
    (nonemptyV : (Subtype.val ⁻¹' (V.val : Set E) : Set L).Nonempty)
    (boundedU : Bornology.IsBounded (U.val : Set E))
    (boundedV : Bornology.IsBounded (V.val : Set E)) :
    HomologicalComplex.homologyMap (sliceSupportCochainExtension A zeroRows k h)
        (Module.finrank ℝ L) ≫
      (sliceSupportCochainTopClassIso A zeroRows k V convexV nonemptyV boundedV).hom =
        (sliceSupportCochainTopClassIso A zeroRows k U convexU nonemptyU boundedU).hom :=
  scalarDualHomologyClassIso_natural k _ (Module.finrank ℝ L) _ _
    (sliceSupportChainTopClassIso_natural A zeroRows (ModuleCat.of k k) h
      convexU convexV nonemptyU nonemptyV boundedU boundedV)

end Field
end ToricPower.IntegralArrangement

end
