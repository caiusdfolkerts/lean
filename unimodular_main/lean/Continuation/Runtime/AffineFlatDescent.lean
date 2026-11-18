module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Affineness after a faithfully flat affine base change

For a quasi-compact, quasi-separated scheme, flat base change commutes with
global sections of the structure sheaf.  Consequently its canonical map to
the spectrum of global sections is cartesian under an affine flat base change.
If the base-changed scheme is affine, fpqc descent of isomorphisms makes the
original scheme affine as well.

This form is sufficient for descending affine character nonvanishing opens
after a field extension, including over finite ground fields.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty AlgebraicGeometry TopologicalSpace

namespace PaperVerification.ToricSchemes

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Affineness descends from a faithfully flat affine base change for a
quasi-compact, quasi-separated scheme.  All four schemes and the actual
pullback square are explicit. -/
theorem isAffine_of_affine_flat_baseChange
    {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X}
    {iX : X ⟶ S} {iY : Y ⟶ T}
    (H : IsPullback g iY iX f)
    [IsAffine S] [IsAffine T] [Flat f] [Surjective f]
    [CompactSpace X] [QuasiSeparatedSpace X] [IsAffine Y] : IsAffine X := by
  have hbase := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp)
    (isAffineOpen_top S) (isAffineOpen_top T) isCompact_univ isQuasiSeparated_univ
  have hpush : IsPushout iX.appTop f.appTop g.appTop iY.appTop := by
    have h := (isIso_pushoutSection_iff H
      (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
      (by simp) (by simp) (by simp)).mp hbase
    simpa [Scheme.Hom.appLE] using h
  let pX : Spec Γ(X, ⊤) ⟶ S := Spec.map iX.appTop ≫ S.isoSpec.inv
  let pY : Spec Γ(Y, ⊤) ⟶ T := Spec.map iY.appTop ≫ T.isoSpec.inv
  have hright : IsPullback pY (Spec.map g.appTop) f pX := by
    refine (hpush.op.map Scheme.Spec).of_iso
      (Iso.refl _) T.isoSpec.symm (Iso.refl _) S.isoSpec.symm ?_ ?_ ?_ ?_
    · simp [pY]
    · simp
    · simpa using Scheme.isoSpec_inv_naturality f
    · simp [pX]
  have hY : Y.toSpecΓ ≫ pY = iY := by
    dsimp only [pY]
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
    simp
  have hX : X.toSpecΓ ≫ pX = iX := by
    dsimp only [pX]
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
    simp
  have houter : IsPullback (Y.toSpecΓ ≫ pY) g f (X.toSpecΓ ≫ pX) := by
    rw [hY, hX]
    exact H.flip
  have hunit : IsPullback Y.toSpecΓ g (Spec.map g.appTop) X.toSpecΓ :=
    houter.of_right (Scheme.toSpecΓ_naturality g).symm hright
  letI : Flat (Spec.map g.appTop) :=
    MorphismProperty.of_isPullback hright inferInstance
  letI : Surjective (Spec.map g.appTop) :=
    MorphismProperty.of_isPullback hright inferInstance
  have hη : IsIso X.toSpecΓ :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := isomorphisms Scheme.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hunit ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  exact ⟨hη⟩

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isAffine_of_affine_flat_baseChange
