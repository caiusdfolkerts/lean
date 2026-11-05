module

public import Continuation.Geometry.OriginalLatticeAtlas

@[expose] public section

/-!
# The colimit of the actual original-lattice chart diagram

The integral basis gives an order isomorphism of the original and
coordinate cone indices.  Together with the proved natural isomorphism
of affine diagrams, this proves the colimit universal property on the
unchanged scheme.  No gluing compatibility is included as an assumption.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PaperVerification.ToricGeometry TauCeti.Toric
open scoped Classical

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)
    (k : Type u) [CommRing k] (F : SmoothCompleteFan n)

/-- The original and coordinate ray-set indices agree with their full
face-inclusion order, not merely as finite collections. -/
def coordinateIndexOrderIso : OriginalConeIndex b F ≃o F.ConeIndex where
  toEquiv := Equiv.ofBijective (coordinateIndex b F)
    ⟨coordinateIndex_injective b F, coordinateIndex_surjective b F⟩
  map_rel_iff' := by
    intro s t
    change s.val.image b.equivFun ⊆ t.val.image b.equivFun ↔ s.val ⊆ t.val
    constructor
    · intro h v hv
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp (h (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
      exact b.equivFun.injective he ▸ hw
    · exact Finset.image_subset_image

/-- The existing scheme is a genuine colimit of the original-lattice
semigroup charts with their literal character inclusion maps. -/
def originalCocone_isColimit : IsColimit (originalCocone b hi k F) := by
  let c := (colimit.cocone (F.coneDiagram k)).whisker (coordinateIndexFunctor b F)
  have hc : IsColimit c :=
    (colimit.isColimit (F.coneDiagram k)).whiskerEquivalence
      (coordinateIndexOrderIso b F).equivalence
  exact (IsColimit.precomposeHomEquiv (diagramComparison b hi k F) c).symm hc

instance hasColimit_originalDiagram : HasColimit (originalDiagram b hi k F) :=
  ⟨⟨originalCocone b hi k F, originalCocone_isColimit b hi k F⟩⟩

/-- Independently gluing the original character charts gives the same
actual scheme, by the proved colimit universal property. -/
def originalGluingIso : colimit (originalDiagram b hi k F) ≅ F.fanScheme k :=
  (colimit.isColimit (originalDiagram b hi k F)).coconePointUniqueUpToIso
    (originalCocone_isColimit b hi k F)

theorem originalGluingIso_chart (s : OriginalConeIndex b F) :
    colimit.ι (originalDiagram b hi k F) s ≫ (originalGluingIso b hi k F).hom =
      originalChartMap b hi k F s := by
  exact (colimit.isColimit (originalDiagram b hi k F)).fac
    (originalCocone b hi k F) s

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.originalCocone_isColimit
#print axioms PaperVerification.OriginalLatticeCharts.originalGluingIso
