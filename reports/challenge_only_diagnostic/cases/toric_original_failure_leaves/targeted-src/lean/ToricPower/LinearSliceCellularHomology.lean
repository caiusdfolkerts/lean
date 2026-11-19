module

public import ToricPower.ArrangementLinearSliceCW
public import ToricPower.IntrinsicConvexTopClass

/-! # The actual intrinsic cellular top class of a closed linear slice

The relative cells and characteristic maps come from the original
periodic arrangement. The comparison removes only the redundant nested
subtypes in the topological pair. Thus the degree is the dimension of
the actual linear slice, and the scalar coefficients are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set Topology

namespace ToricPower

universe w

/-- The actual pair `(S, S ∩ Dᶜ)` is the intrinsic complement pair in
the subspace `S`. Both ambient maps are the identity on `S`. -/
def subsetComplementPairIso {X : Type w} [TopologicalSpace X]
    (S D : Set X) :
    TopPair.ofInclusion (X := TopCat.of X)
        (show S ∩ Dᶜ ⊆ S from inter_subset_left) ≅
      TopPair.ofSubset (X := TopCat.of S) (Subtype.val ⁻¹' D)ᶜ where
  hom := TopPair.ofHom (𝟙 (TopCat.of S))
    (TopCat.ofHom ⟨fun x => ⟨⟨x.val,x.property.1⟩,x.property.2⟩,by fun_prop⟩)
    (by ext x; rfl)
  inv := TopPair.ofHom (𝟙 (TopCat.of S))
    (TopCat.ofHom ⟨fun x => ⟨x.val.val,⟨x.val.property,x.property⟩⟩,by fun_prop⟩)
    (by ext x; rfl)
  hom_inv_id := by
    apply TopPair.hom_ext_of_fst
    ext x
    rfl
  inv_hom_id := by
    apply TopPair.hom_ext_of_fst
    ext x
    rfl

def relativeSubsetBasePairIso {X : Type w} [TopologicalSpace X] [T2Space X]
    (S D : Set X) [RelCWComplex S (S ∩ Dᶜ)] :
    TauCeti.complexBasePair S ≅
      TopPair.ofSubset (X := TopCat.of S) (Subtype.val ⁻¹' D)ᶜ :=
  eqToIso (TauCeti.complexBasePair_eq_ofInclusion S) ≪≫ subsetComplementPairIso S D

@[simp]
theorem relativeSubsetBasePairIso_hom_fst {X : Type w} [TopologicalSpace X] [T2Space X]
    (S D : Set X) [RelCWComplex S (S ∩ Dᶜ)] :
    TopPair.Hom.fst (relativeSubsetBasePairIso S D).hom = 𝟙 (TopCat.of S) := by
  change TopPair.proj₁.map ((eqToIso
    (TauCeti.complexBasePair_eq_ofInclusion S)).hom ≫
      (subsetComplementPairIso S D).hom) = _
  rw [Functor.map_comp,eqToIso.hom,eqToHom_map]
  simp only [eqToHom_refl,Category.id_comp]
  rfl

namespace IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (zeroRows : Set (Fin s ⊕ Fin n)) (region : Set (Fin n → ℝ))
  (openRegion : IsOpen region) (cellwise : Cellwise (augmentedForms A) region)
  {k : Type} [Ring k] (M : ModuleCat.{0} k)

local notation "E" => Fin n → ℝ
local notation "V" => arrangementZeroSlice (augmentedForms A) zeroRows

/-- The genuine relative cellular chains of the closed slice and its
closed complementary subcomplex, with the original boundary maps. -/
def periodicLinearSliceCellComplex : ChainComplex (ModuleCat.{0} k) ℕ := by
  letI := periodicLinearSliceRelativeCW A zeroRows region openRegion cellwise
  exact TauCeti.cellularChainComplex (V : Set E) M

def periodicLinearSliceCellularSingularIso (q : ℕ) :
    (periodicLinearSliceCellComplex A zeroRows region openRegion cellwise M).homology q ≅
      (TopPair.ofSubset ((Subtype.val ⁻¹' region)ᶜ :
        Set (TopCat.of V))).singularHomology M q := by
  letI := periodicLinearSliceRelativeCW A zeroRows region openRegion cellwise
  exact TauCeti.cellularSingularHomologyIso (V : Set E) M q ≪≫
    topPairHomologyIso (relativeSubsetBasePairIso (V : Set E) region) M q

/-- The canonical top class is intrinsic to the actual slice. A bounded
convex ambient window may intersect it in any nonempty dimension. -/
def periodicLinearSliceTopClassIso (convexRegion : Convex ℝ region)
    (nonemptyRegion : (Subtype.val ⁻¹' region : Set V).Nonempty)
    (boundedRegion : Bornology.IsBounded region) :
    (periodicLinearSliceCellComplex A zeroRows region openRegion cellwise M).homology
      (Module.finrank ℝ V) ≅ M :=
  periodicLinearSliceCellularSingularIso A zeroRows region openRegion cellwise M
      (Module.finrank ℝ V) ≪≫
    intrinsicConvexTopClassIso M (Subtype.val ⁻¹' region : Set V)
      (convexRegion.linear_preimage (V).subtype) nonemptyRegion
      (isometry_subtype_coe.antilipschitz.isBounded_preimage boundedRegion)

theorem periodicLinearSliceCellComplex_isZero_homology
    (convexRegion : Convex ℝ region)
    (nonemptyRegion : (Subtype.val ⁻¹' region : Set V).Nonempty)
    (boundedRegion : Bornology.IsBounded region)
    (q : ℕ) (different : q ≠ Module.finrank ℝ V) :
    IsZero ((periodicLinearSliceCellComplex A zeroRows region openRegion cellwise M).homology q) :=
  (intrinsicConvexHomology_isZero M (Subtype.val ⁻¹' region : Set V)
    (convexRegion.linear_preimage (V).subtype) nonemptyRegion
    (isometry_subtype_coe.antilipschitz.isBounded_preimage boundedRegion) q different).of_iso
      (periodicLinearSliceCellularSingularIso A zeroRows region openRegion cellwise M q)

end IntegralArrangement
end ToricPower

end
