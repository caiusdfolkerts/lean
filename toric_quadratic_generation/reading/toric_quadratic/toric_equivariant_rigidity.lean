module

public import PaperVerification.ToricTorusCoactionRational
public import PaperVerification.ToricActionProductProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

/-!
# Equivariance from an actual dense torus

A morphism over the ground field which agrees with the given torus
embeddings is equivariant. The equality is proved on the genuine scheme
product of two tori, then extended from that dense open subscheme to the
reduced action product. In particular no assertion about rational points
is substituted for equality of scheme morphisms.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj

variable {k : Type u} [Field k] {n : ℕ}
    {X Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [ModObj (splitTorusOver k (Fin n→ℤ)) Y]
    [IsIntegral X.left] [Smooth X.hom] [IsSeparated Y.hom]
    (T : SplitToricEmbedding k n X) (S : SplitToricEmbedding k n Y)

/-- The actual action square follows from the actual dense-torus square. -/
theorem isModHom_of_torus_compatibility (f : X ⟶ Y)
    (htorus : T.torus ≫ f = S.torus) :
    IsModHom (splitTorusOver k (Fin n→ℤ)) f := by
  let G := splitTorusOver k (Fin n→ℤ)
  letI : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsIntegral (G⊗G).left := T.doubleTorus_integral
  letI : IsIntegral (G⊗X).left := inferInstance
  letI : IsDominant T.doubleTorusMap := inferInstance
  constructor
  apply Over.OverMorphism.ext
  have hbase : (γ[G,X] ≫ f).left ≫ Y.hom =
      (G ◁ f ≫ γ[G,Y]).left ≫ Y.hom :=
    (γ[G,X] ≫ f).w.trans (G ◁ f ≫ γ[G,Y]).w.symm
  apply ext_of_isDominant_of_isSeparated Y.hom hbase T.doubleTorusMap
  have heq : (G ◁ T.torus) ≫ (γ[G,X] ≫ f) =
      (G ◁ T.torus) ≫ ((G ◁ f) ≫ γ[G,Y]) := by
    calc
      _ = μ[G] ≫ (T.torus ≫ f) := by
        rw [← Category.assoc,← T.equivariant,Category.assoc]
      _ = μ[G] ≫ S.torus := by rw [htorus]
      _ = (G ◁ S.torus) ≫ γ[G,Y] := S.equivariant
      _ = (G ◁ T.torus) ≫ ((G ◁ f) ≫ γ[G,Y]) := by
        rw [← htorus,MonoidalCategory.whiskerLeft_comp,Category.assoc]
  exact congrArg (fun g : G⊗G ⟶ Y => g.left) heq

/-- A torus-preserving isomorphism of the underlying schemes over the
field is an isomorphism respecting the genuine torus actions. -/
theorem iso_isModHom_of_torus_compatibility (e : X ≅ Y)
    (htorus : T.torus ≫ e.hom = S.torus) :
    IsModHom (splitTorusOver k (Fin n→ℤ)) e.hom :=
  T.isModHom_of_torus_compatibility S e.hom htorus

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.isModHom_of_torus_compatibility
