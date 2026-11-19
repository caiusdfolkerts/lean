module

public import Continuation.Runtime.IntrinsicReconstruction
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# A torus-preserving morphism respects the actual group action

Source candidate, not yet compiled. For a smooth integral toric source and a
separated target, a morphism over the field that agrees with the two specified
dense torus embeddings is equivariant for the existing group-scheme actions.
The two action maps are compared on the actual dense double torus. No new
action is defined and equivariance is not an input hypothesis.

The final wrapper strengthens the recovered ample/proper fan-reconstruction
statement with an actual equivariant isomorphism in the over category. It
retains exactly that reconstruction theorem's ample Cartier hypothesis and
does not assert reconstruction of arbitrary nonprojective complete varieties.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open PaperVerification.ToricGeometry

variable {k : Type u} [Field k] {n : ℕ}
    {X Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [ModObj (splitTorusOver k (Fin n → ℤ)) Y]
    [IsIntegral X.left] [Smooth X.hom] [IsSeparated Y.hom]

/-- Agreement on the specified dense torus forces equivariance for the actual
actions on all test schemes. The target need only be separated; no properness
or ampleness is required for this extension argument. -/
theorem isModHom_of_torusPreserving
    (T : SplitToricEmbedding k n X) (U : SplitToricEmbedding k n Y)
    (f : X ⟶ Y) (htorus : T.torus ≫ f = U.torus) :
    IsModHom (splitTorusOver k (Fin n → ℤ)) f := by
  let G := splitTorusOver k (Fin n → ℤ)
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsIntegral (G ⊗ X).left := torusProduct_integral k n X
  letI : IsIntegral (G ⊗ G).left := T.doubleTorus_integral
  letI : IsDominant T.doubleTorusMap := inferInstance
  have hdouble :
      (G ◁ T.torus) ≫ (γ[G, X] ≫ f) =
        (G ◁ T.torus) ≫ ((G ◁ f) ≫ γ[G, Y]) := by
    calc
      (G ◁ T.torus) ≫ (γ[G, X] ≫ f) = (μ[G] ≫ T.torus) ≫ f := by
        rw [← Category.assoc, ← T.equivariant]
      _ = μ[G] ≫ U.torus := by rw [Category.assoc, htorus]
      _ = (G ◁ U.torus) ≫ γ[G, Y] := U.equivariant
      _ = (G ◁ (T.torus ≫ f)) ≫ γ[G, Y] := by rw [htorus]
      _ = (G ◁ T.torus) ≫ ((G ◁ f) ≫ γ[G, Y]) := by
        rw [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  refine ⟨?_⟩
  change γ[G, X] ≫ f = (G ◁ f) ≫ γ[G, Y]
  apply Over.OverMorphism.ext
  apply ext_of_isDominant_of_isSeparated Y.hom
    ((γ[G, X] ≫ f).w.trans ((G ◁ f) ≫ γ[G, Y]).w.symm)
    T.doubleTorusMap
  exact congrArg (fun g => g.left) hdouble

/-- The underlying scheme isomorphism and its actual base triangle suffice;
its action compatibility is proved from its torus triangle. -/
theorem isModHom_overIso_of_torusPreserving
    (T : SplitToricEmbedding k n X) (U : SplitToricEmbedding k n Y)
    (e : X.left ≅ Y.left) (hbase : e.hom ≫ Y.hom = X.hom)
    (htorus : T.torus.left ≫ e.hom = U.torus.left) :
    IsModHom (splitTorusOver k (Fin n → ℤ)) (Over.isoMk e hbase).hom := by
  apply T.isModHom_of_torusPreserving U (Over.isoMk e hbase).hom
  apply Over.OverMorphism.ext
  exact htorus

end PaperVerification.ToricSchemes.SplitToricEmbedding

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]

/-- The recovered reconstruction from an actual ample Cartier divisor yields
an isomorphism over the field that respects the original torus actions. -/
theorem exists_equivariant_smooth_complete_fan (T : SplitToricEmbedding k n X)
    (D : CartierData X.left) (hD : D.IsAmple) :
    ∃ (P : LatticePolytope n) (F : SmoothCompleteFan n)
      (e : F.fanSchemeOver k ≅ X),
      P.Smooth ∧ F.realCones = P.normalFan ∧ F.IsPure ∧
      IsModHom (splitTorusOver k (Fin n → ℤ)) e.hom ∧
      (F.intrinsicToricEmbedding k).torus ≫ e.hom = T.torus := by
  obtain ⟨P, F, e, hP, hfan, hpure, hbase, htorus⟩ :=
    T.exists_smooth_complete_fan D hD
  let eOver : F.fanSchemeOver k ≅ X := Over.isoMk e hbase
  letI : IsIntegral (F.fanSchemeOver k).left := by
    change IsIntegral (F.fanScheme k)
    infer_instance
  letI : Smooth (F.fanSchemeOver k).hom := by
    change Smooth (F.fanSchemeStructureMap k)
    rw [← hbase]
    infer_instance
  have htorusOver : (F.intrinsicToricEmbedding k).torus ≫ eOver.hom = T.torus := by
    apply Over.OverMorphism.ext
    exact htorus
  have hequiv : IsModHom (splitTorusOver k (Fin n → ℤ)) eOver.hom :=
    (F.intrinsicToricEmbedding k).isModHom_of_torusPreserving T eOver.hom htorusOver
  exact ⟨P, F, eOver, hP, hfan, hpure, hequiv, htorusOver⟩

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.isModHom_of_torusPreserving
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.isModHom_overIso_of_torusPreserving
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.exists_equivariant_smooth_complete_fan

#check PaperVerification.ToricSchemes.SplitToricEmbedding.exists_equivariant_smooth_complete_fan
