module

public import Continuation.Geometry.OriginalLatticeCharts

@[expose] public section

/-!
# An original-lattice affine atlas on the unchanged toric scheme

The index set consists of the original lattice ray sets whose coordinate
images are cones of the given fan.  Every chart is the actual spectrum of
the original integral dual semigroup.  The chart maps into `F.fanScheme k`
are open immersions, cover that same scheme, and commute with every face
map.  Thus this construction changes the presentation of the atlas, not
the scheme carrying its geometric properties.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open TauCeti.Toric
open scoped Classical BigOperators

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)
    (k : Type u) [CommRing k]

include b in
@[simp] theorem affineFaceMap_self (s : Finset N) :
    affineFaceMap hi k (Finset.Subset.refl s) = 𝟙 (affineChart hi k s) := by
  apply (cancel_mono (affineChartIso b hi k s).hom).mp
  rw [affineChartIso_naturality, coneChartFaceMap_self, Category.comp_id,
    Category.id_comp]

include b in
theorem affineFaceMap_comp {r s t : Finset N} (hrs : r ⊆ s) (hst : s ⊆ t) :
    affineFaceMap hi k hrs ≫ affineFaceMap hi k hst =
      affineFaceMap hi k (hrs.trans hst) := by
  apply (cancel_mono (affineChartIso b hi k t).hom).mp
  rw [Category.assoc, affineChartIso_naturality,
    ← Category.assoc, affineChartIso_naturality,
    Category.assoc, coneChartFaceMap_comp, affineChartIso_naturality]

variable (F : SmoothCompleteFan n)

/-- All original finite ray sets corresponding to cones of the fan. -/
abbrev OriginalConeIndex :=
  {s : Finset N // s.image b.equivFun ∈ F.cones}

abbrev coordinateIndex (s : OriginalConeIndex b F) : F.ConeIndex :=
  ⟨s.val.image b.equivFun, s.property⟩

theorem coordinateIndex_surjective : Function.Surjective (coordinateIndex b F) := by
  intro s
  have hs : (s.val.image b.equivFun.symm).image b.equivFun = s.val := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      change b.equivFun (b.equivFun.symm z) ∈ s.val
      rw [b.equivFun.apply_symm_apply]
      exact hz
    · intro hv
      exact Finset.mem_image.mpr ⟨b.equivFun.symm v,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩, b.equivFun.apply_symm_apply v⟩
  refine ⟨⟨s.val.image b.equivFun.symm, hs.symm ▸ s.property⟩, ?_⟩
  exact Subtype.ext hs

theorem coordinateIndex_injective : Function.Injective (coordinateIndex b F) := by
  intro s t h
  apply Subtype.ext
  exact (Finset.image_injective b.equivFun.injective) (congrArg Subtype.val h)

/-- The actual face-index functor is the image under the integral basis. -/
def coordinateIndexFunctor : OriginalConeIndex b F ⥤ F.ConeIndex where
  obj := coordinateIndex b F
  map f := homOfLE (Finset.image_subset_image (leOfHom f))

/-- The diagram of spectra of the literal original-lattice dual cones. -/
def originalDiagram : OriginalConeIndex b F ⥤ Scheme.{u} where
  obj s := affineChart hi k s.val
  map f := affineFaceMap hi k (leOfHom f)
  map_id s := affineFaceMap_self b hi k s.val
  map_comp f g := affineFaceMap_comp b hi k (leOfHom f) (leOfHom g) |>.symm

/-- The entire affine diagram comparison, with its naturality proved on
actual character algebra maps in `OriginalLatticeCharts`. -/
def diagramComparison : originalDiagram b hi k F ≅
    coordinateIndexFunctor b F ⋙ F.coneDiagram k :=
  NatIso.ofComponents (fun s => affineChartIso b hi k s.val)
    (fun f => affineChartIso_naturality b hi k (leOfHom f))

/-- An original-lattice affine chart maps into the existing glued scheme. -/
def originalChartMap (s : OriginalConeIndex b F) :
    affineChart hi k s.val ⟶ F.fanScheme k :=
  (affineChartIso b hi k s.val).hom ≫ F.fanChartMap k (coordinateIndex b F s)

instance originalChartMap_isOpenImmersion (s : OriginalConeIndex b F) :
    IsOpenImmersion (originalChartMap b hi k F s) := by
  dsimp only [originalChartMap]
  infer_instance

@[reassoc] theorem originalChartMap_naturality {s t : OriginalConeIndex b F}
    (hst : s.val ⊆ t.val) :
    affineFaceMap hi k hst ≫ originalChartMap b hi k F t =
      originalChartMap b hi k F s := by
  change affineFaceMap hi k hst ≫ (affineChartIso b hi k t.val).hom ≫
      F.fanChartMap k (coordinateIndex b F t) =
    (affineChartIso b hi k s.val).hom ≫ F.fanChartMap k (coordinateIndex b F s)
  rw [← Category.assoc, affineChartIso_naturality, Category.assoc]
  exact congrArg (fun f => (affineChartIso b hi k s.val).hom ≫ f)
    (F.fanChartMap_naturality k (s := coordinateIndex b F s)
      (t := coordinateIndex b F t) (Finset.image_subset_image hst))

/-- Every point of the unchanged scheme is in an original-lattice chart. -/
theorem originalChartMap_jointly_surjective (x : F.fanScheme k) :
    ∃ (s : OriginalConeIndex b F) (y : affineChart hi k s.val),
      originalChartMap b hi k F s y = x := by
  obtain ⟨t, y, hy⟩ := F.fanChartMap_jointly_surjective k x
  obtain ⟨s, rfl⟩ := coordinateIndex_surjective b F t
  refine ⟨s, (affineChartIso b hi k s.val).inv y, ?_⟩
  change F.fanChartMap k (coordinateIndex b F s)
    ((affineChartIso b hi k s.val).hom ((affineChartIso b hi k s.val).inv y)) = x
  have he : (affineChartIso b hi k s.val).hom
      ((affineChartIso b hi k s.val).inv y) = y := by
    have h := congrArg (fun f : coneChart k (s.val.image b.equivFun) ⟶
        coneChart k (s.val.image b.equivFun) => f y)
        (affineChartIso b hi k s.val).inv_hom_id
    simpa using h
  rw [he]
  exact hy

/-- An actual open affine cover, rather than assumed chart data. -/
def originalOpenCover : (F.fanScheme k).OpenCover :=
  Scheme.Cover.mkOfCovers (OriginalConeIndex b F)
    (fun s => affineChart hi k s.val) (originalChartMap b hi k F)
    (originalChartMap_jointly_surjective b hi k F)
    (fun _ => inferInstance)

/-- The full original-lattice cocone on the same scheme. Its every
commutativity obligation is the proved face-map naturality. -/
def originalCocone : Cocone (originalDiagram b hi k F) where
  pt := F.fanScheme k
  ι := {
    app := originalChartMap b hi k F
    naturality := by
      intro s t f
      change affineFaceMap hi k (leOfHom f) ≫ originalChartMap b hi k F t =
        originalChartMap b hi k F s ≫ 𝟙 (F.fanScheme k)
      rw [Category.comp_id]
      exact originalChartMap_naturality b hi k F (leOfHom f)
  }

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.diagramComparison
#print axioms PaperVerification.OriginalLatticeCharts.originalOpenCover
