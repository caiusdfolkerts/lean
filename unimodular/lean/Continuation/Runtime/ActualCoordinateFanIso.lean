module

public import Continuation.Runtime.ActualCoordinateFan
public import Continuation.Divisor.ProjectiveFoundations

/-!
# Reconstructing the original scheme from its actual affine charts

The complete fan has already been constructed from the original cover.
Its cone charts now descend to the original scheme through the genuine
fan colimit. Their proved common-face overlaps make the descended map an
isomorphism. This isomorphism preserves both the original dense torus
and the structure morphism to the original ground field.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry

namespace PaperVerification.ToricSchemes.CoordinateChartCover

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
    [X.IsSeparated] [IsLocallyNoetherian X]
    {j : Spec (CommRingCat.of (AddMonoidAlgebra k (Lattice n))) ⟶ X}
    (C : CoordinateChartCover k n X j)
    (f : X ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap k (AddMonoidAlgebra k (Lattice n)))))

/-- The actual fan scheme is isomorphic to the original scheme. The
open-overlap equations and coverage are conclusions of the preceding
geometry, not extra hypotheses of this construction. -/
def schemeIso : (C.fan f hj).fanScheme k ≅ X :=
  (C.fan f hj).chartFamilyIso k C.rays
    (C.rays_mem_fan f hj) (C.fan_cones_covered f hj)
    C.coneMap C.coneMap_torus_agree C.coneMap_overlap C.coneMaps_cover

@[reassoc] theorem fanChartMap_schemeIso (i : C.Index) :
    (C.fan f hj).fanChartMap k ⟨C.rays i, C.rays_mem_fan f hj i⟩ ≫
      (C.schemeIso f hj).hom = C.coneMap i :=
  (C.fan f hj).familyChart_chartFamilyDesc k C.rays
    (C.rays_mem_fan f hj) (C.fan_cones_covered f hj)
    C.coneMap C.coneMap_torus_agree i

/-- The reconstructed scheme isomorphism fixes the specified original
torus map, including its original character coordinates. -/
@[reassoc] theorem schemeIso_torus :
    (C.fan f hj).splitTorusOpenMap k ≫ (C.schemeIso f hj).hom = j := by
  obtain ⟨i, hi⟩ := C.rayCones_cover f hj 0
  let F := C.fan f hj
  let e := C.schemeIso f hj
  let s : F.ConeIndex := ⟨C.rays i, C.rays_mem_fan f hj i⟩
  change ((zeroConeChartIso k n).inv ≫ F.torusOpenMap k) ≫ e.hom = j
  rw [← F.torusOpenMap_chart k s]
  calc
    ((zeroConeChartIso k n).inv ≫
        (coneChartFaceMap k (Finset.empty_subset s.val) ≫ F.fanChartMap k s)) ≫ e.hom =
      (zeroConeChartIso k n).inv ≫ coneChartFaceMap k (Finset.empty_subset s.val) ≫
        (F.fanChartMap k s ≫ e.hom) := by simp only [Category.assoc]
    _ = (zeroConeChartIso k n).inv ≫
        coneChartFaceMap k (Finset.empty_subset (C.rays i)) ≫ C.coneMap i := by
      rw [C.fanChartMap_schemeIso]
    _ = (zeroConeChartIso k n).inv ≫ (zeroConeChartIso k n).hom ≫ j := by
      rw [C.coneMap_torus]
    _ = j := by simp only [Iso.inv_hom_id_assoc]

/-- The reconstructed isomorphism also preserves the actual ground-field
map. Equality is checked on the dense original torus. -/
@[reassoc] theorem schemeIso_base :
    (C.schemeIso f hj).hom ≫ f = (C.fan f hj).fanSchemeStructureMap k := by
  let F := C.fan f hj
  letI : IsDominant (F.splitTorusOpenMap k) := ⟨F.splitTorusOpenMap_denseRange k⟩
  apply ext_of_isDominant (F.splitTorusOpenMap k)
  rw [← Category.assoc, C.schemeIso_torus]
  change j ≫ f = F.splitTorusOpenMap k ≫ (F.fanScheme k ↘ Spec (CommRingCat.of k))
  rw [comp_over]
  exact hj

include C hj in
/-- A complete scheme with a proved finite cover by actual smooth
character charts has the claimed fan presentation in its original
lattice, over its original field, and with its original torus. -/
theorem exists_fan_presentation :
    ∃ (F : SmoothCompleteFan n) (e : F.fanScheme k ≅ X),
      e.hom ≫ f = F.fanSchemeStructureMap k ∧ F.splitTorusOpenMap k ≫ e.hom = j :=
  ⟨C.fan f hj, C.schemeIso f hj, C.schemeIso_base f hj, C.schemeIso_torus f hj⟩

end PaperVerification.ToricSchemes.CoordinateChartCover

#print axioms PaperVerification.ToricSchemes.CoordinateChartCover.exists_fan_presentation
