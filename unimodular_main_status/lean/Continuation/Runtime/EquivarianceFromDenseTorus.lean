module

public import Continuation.Runtime.IntrinsicCompleteFanPresentation

/-!
# Torus-preserving isomorphisms preserve the actual actions

The map from the product of the torus with the dense torus into the
product with the original scheme is dominant.  This is proved using the
actual product pullback and the open torus projection.  The product is
integral by the existing geometric-integrality theorem for the split
torus, so equality on this dense product determines maps to a separated
target.

Consequently the reconstructed isomorphism is an isomorphism of the
given torus actions, not only an isomorphism over the ground field.
This module is a source candidate pending its complete native check.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open PaperVerification.ToricGeometry

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [ModObj (splitTorusOver k (Fin n → ℤ)) Y]

/-- The literal product of the original dense torus immersion is
dominant.  Density is pulled back along the open product projection;
no density of rational points is used. -/
theorem torusProductInclusion_isDominant [Smooth X.hom]
    (T : SplitToricEmbedding k n X) :
    IsDominant ((splitTorusOver k (Fin n → ℤ) ◁ T.torus).left) := by
  let G := splitTorusOver k (Fin n → ℤ)
  letI : Smooth G.hom := T.torus_smooth
  letI : IsOpenImmersion ((Over.forget (Spec (CommRingCat.of k))).map T.torus) :=
    T.open_immersion
  have hp := (isPullback_whiskerLeft_snd G T.torus).map
    (Over.forget (Spec (CommRingCat.of k)))
  letI : IsOpenImmersion ((Over.forget (Spec (CommRingCat.of k))).map (G ◁ T.torus)) :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  have hrange := congrArg
    (fun U : (G ⊗ X).left.Opens => (U : Set (G ⊗ X).left))
    (opensRange_of_isPullback hp)
  change Set.range ((G ◁ T.torus).left) =
    (snd G X).left ⁻¹' Set.range T.torus.left at hrange
  have hopen : IsOpenMap (snd G X).left := by
    change IsOpenMap (Limits.pullback.snd G.hom X.hom)
    exact Scheme.Hom.isOpenMap _
  constructor
  change Dense (Set.range ((G ◁ T.torus).left))
  rw [hrange]
  exact (show Dense (Set.range T.torus.left) from T.dense).preimage hopen

/-- A morphism between the actual toric schemes which preserves their
specified dense torus maps commutes with the whole group-scheme action.
The source is integral and smooth, and the target is separated. -/
theorem isModHom_of_torus_eq [IsIntegral X.left] [Smooth X.hom]
    [Y.left.IsSeparated] (TX : SplitToricEmbedding k n X)
    (TY : SplitToricEmbedding k n Y) (f : X ⟶ Y)
    (hT : TX.torus ≫ f = TY.torus) :
    IsModHom (splitTorusOver k (Fin n → ℤ)) f := by
  let G := splitTorusOver k (Fin n → ℤ)
  letI : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsIntegral (G ⊗ X).left := torusProduct_integral k n X
  letI : IsDominant ((G ◁ TX.torus).left) := TX.torusProductInclusion_isDominant
  constructor
  apply Over.OverMorphism.ext
  apply ext_of_isDominant (G ◁ TX.torus).left
  have h :
      (G ◁ TX.torus) ≫ γ[G, X] ≫ f =
        (G ◁ TX.torus) ≫ (G ◁ f) ≫ γ[G, Y] := by
    calc
      _ = μ[G] ≫ TX.torus ≫ f := by
        rw [← Category.assoc, ← TX.equivariant, Category.assoc]
      _ = μ[G] ≫ TY.torus := by rw [hT]
      _ = (G ◁ TY.torus) ≫ γ[G, Y] := TY.equivariant
      _ = (G ◁ TX.torus) ≫ (G ◁ f) ≫ γ[G, Y] := by
        rw [← hT, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  exact congrArg (fun g : G ⊗ G ⟶ Y => g.left) h

section Complete

variable [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

/-- The original smooth complete toric scheme is isomorphic to its
constructed fan scheme over the original field, fixes its original
torus coordinates, and is equivariant in both directions. -/
theorem exists_equivariant_fan_of_complete :
    ∃ (F : SmoothCompleteFan n) (e : F.fanSchemeOver k ≅ X),
      (F.intrinsicToricEmbedding k).torus ≫ e.hom = T.torus ∧
        IsModHom (splitTorusOver k (Fin n → ℤ)) e.hom ∧
        IsModHom (splitTorusOver k (Fin n → ℤ)) e.inv := by
  obtain ⟨F, e, hT⟩ := T.exists_fan_of_complete
  letI : X.left.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from X.hom]
    infer_instance⟩
  letI : IsIntegral (F.fanSchemeOver k).left := IsIntegral.of_isIso e.inv.left
  letI : Smooth (F.fanSchemeOver k).hom := by
    rw [← e.hom.w]
    infer_instance
  letI : IsModHom (splitTorusOver k (Fin n → ℤ)) e.hom :=
    (F.intrinsicToricEmbedding k).isModHom_of_torus_eq T e.hom hT
  exact ⟨F, e, hT, inferInstance, inferInstance⟩

end Complete

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.torusProductInclusion_isDominant
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.isModHom_of_torus_eq
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.exists_equivariant_fan_of_complete
