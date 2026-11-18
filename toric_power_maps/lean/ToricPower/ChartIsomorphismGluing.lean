module

public import ToricPower.ChartOverHomRefinement

/-!
# Gluing compatible isomorphisms on actual scheme charts

Pairwise intersections are represented by the meet chart. Compatibility
is expressed using ordinary restriction and its genuine composition
isomorphisms. Transport to the image-open slice then supplies the
ordinary sheaf-gluing theorem, including all smaller opens.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules

namespace ToricPower

universe u v

variable {X : Scheme.{u}} {I : Type v} [SemilatticeInf I]
  (Y : I → Scheme.{u}) (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
  (face : ∀ small large, (small ≤ large) → (Y small ⟶ Y large))
  [faceOpen : ∀ small large (h : small ≤ large), IsOpenImmersion (face small large h)]
  (square : ∀ small large (h : small ≤ large), face small large h ≫ j large = j small)
  (intersection : ∀ first second, (j (first ⊓ second)).opensRange =
    (j first).opensRange ⊓ (j second).opensRange)
  (covers : IsOpenCover (fun i => (j i).opensRange))
  {M N : X.Modules} (e : ∀ i, M.restrict (j i) ≅ N.restrict (j i))
  (compatible : ∀ small large (h : small ≤ large),
    (chartRestrictionIso (face small large h) (j large) (j small) (square small large h) M).symm ≪≫
      (restrictFunctor (face small large h)).mapIso (e large) ≪≫
      chartRestrictionIso (face small large h) (j large) (j small) (square small large h) N = e small)

include intersection compatible in
/-- Actual chart compatibility is precisely enough for sheaf descent. -/
theorem chartOverIso_compatible :
    SheafModuleGluing.Compatible (fun i => (j i).opensRange)
      (fun i => (chartOverIso (j i) (e i)).hom) := by
  apply SheafModuleGluing.compatible_of_overlap_restrictions
  intro first second
  have left := chartOverIso_refinement (face (first ⊓ second) first inf_le_left)
    (j first) (j (first ⊓ second)) (square _ _ inf_le_left)
    (e first) (e (first ⊓ second)) (compatible _ _ inf_le_left)
  have right := chartOverIso_refinement (face (first ⊓ second) second inf_le_right)
    (j second) (j (first ⊓ second)) (square _ _ inf_le_right)
    (e second) (e (first ⊓ second)) (compatible _ _ inf_le_right)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  have inside : W.unop.left ≤ (j (first ⊓ second)).opensRange := by
    rw [intersection first second]
    exact W.unop.hom.le
  have onSections := congrArg
    (fun mapping : M.over (j (first ⊓ second)).opensRange ⟶
        N.over (j (first ⊓ second)).opensRange =>
      mapping.val.app (op (Over.mk (homOfLE inside))) value) (left.trans right.symm)
  exact (restrictOverHom_app X.ringCatSheaf
    (homOfLE (inf_le_left : (j first).opensRange ⊓ (j second).opensRange ≤
      (j first).opensRange)) (chartOverIso (j first) (e first)).hom W.unop value).trans
    (onSections.trans (restrictOverHom_app X.ringCatSheaf
      (homOfLE (inf_le_right : (j first).opensRange ⊓ (j second).opensRange ≤
        (j second).opensRange)) (chartOverIso (j second) (e second)).hom W.unop value).symm)

/-- The global isomorphism obtained from compatible actual chart maps. -/
def chartGluedIso : M ≅ N :=
  SheafModuleGluing.glueIso (fun i => (j i).opensRange) covers
    (fun i => chartOverIso (j i) (e i))
    (chartOverIso_compatible Y j face square intersection e compatible)

end ToricPower

end
