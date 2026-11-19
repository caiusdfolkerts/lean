module

public import Continuation.Geometry.OriginalLatticeGluing
public import Continuation.Geometry.OriginalLatticeOverlaps

@[expose] public section

/-!
# The original gluing comparison over the original base field

The structural map is obtained from the actual k-algebra maps of every
original semigroup chart.  The proved gluing isomorphism commutes with
that map.  Thus the atlas comparison is an isomorphism over the given
base, with no separately supplied compatibility condition.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry TauCeti.Toric

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)
    (k : Type u) [CommRing k] (F : SmoothCompleteFan n)

instance affineFaceMap_isOver {s t : Finset N} (hst : s ⊆ t) :
    (affineFaceMap hi k hst).IsOver (Spec (CommRingCat.of k)) := by
  change (Spec.map (CommRingCat.ofHom
    (coordinateRingFaceMap hi k hst).toRingHom)).IsOver _
  infer_instance

/-- The original chart k-algebras give a genuine structural cocone. -/
def originalBaseCocone : Cocone (originalDiagram b hi k F) where
  pt := Spec (CommRingCat.of k)
  ι := {
    app s := affineChart hi k s.val ↘ Spec (CommRingCat.of k)
    naturality := by
      intro s t f
      change affineFaceMap hi k (leOfHom f) ≫
          (affineChart hi k t.val ↘ Spec (CommRingCat.of k)) =
        (affineChart hi k s.val ↘ Spec (CommRingCat.of k)) ≫ 𝟙 _
      rw [Category.comp_id]
      exact comp_over (affineFaceMap hi k (leOfHom f)) (Spec (CommRingCat.of k))
  }

/-- The structural map obtained by gluing the original k-algebra charts. -/
def originalSchemeStructureMap :
    colimit (originalDiagram b hi k F) ⟶ Spec (CommRingCat.of k) :=
  colimit.desc (originalDiagram b hi k F) (originalBaseCocone b hi k F)

/-- The comparison preserves the actual given scalar field. -/
theorem originalGluingIso_toSpec :
    (originalGluingIso b hi k F).hom ≫ F.fanSchemeStructureMap k =
      originalSchemeStructureMap b hi k F := by
  apply (colimit.isColimit (originalDiagram b hi k F)).hom_ext
  intro s
  change colimit.ι (originalDiagram b hi k F) s ≫
      ((originalGluingIso b hi k F).hom ≫ F.fanSchemeStructureMap k) =
    colimit.ι (originalDiagram b hi k F) s ≫ originalSchemeStructureMap b hi k F
  rw [← Category.assoc, originalGluingIso_chart]
  change originalChartMap b hi k F s ≫ F.fanSchemeStructureMap k =
    colimit.ι (originalDiagram b hi k F) s ≫
      colimit.desc (originalDiagram b hi k F) (originalBaseCocone b hi k F)
  rw [colimit.ι_desc]
  exact comp_over (originalChartMap b hi k F s) (Spec (CommRingCat.of k))

/-- An isomorphism in the actual category of schemes over k, not merely
an equality of cones or a homeomorphism of their underlying spaces. -/
def originalGluingOverIso :
    Over.mk (originalSchemeStructureMap b hi k F) ≅ F.fanSchemeOver k :=
  Over.isoMk (originalGluingIso b hi k F) (originalGluingIso_toSpec b hi k F)

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.originalGluingOverIso
