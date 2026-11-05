module

public import PaperVerification.ToricFanAction
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

/-!
# Intrinsic split-torus embeddings and their actual action squares

An intrinsic torus embedding is an equivariant dense open immersion of
the genuine split group scheme into a scheme carrying a genuine action.
It includes no fan, invariant affine cover, semigroup presentation,
linearization, or character decomposition. Smoothness and properness are
the ordinary properties of the structure morphism and remain separate.
-/

noncomputable section

universe v u

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G X : C) [GrpObj G] [ModObj G X]

/-- The actual action graph isomorphism `(g,x) ↦ (g,g·x)`. -/
def ModObj.actionGraphIso : G ⊗ X ≅ G ⊗ X where
  hom := lift (fst G X) ((fst G X) • (snd G X))
  inv := lift (fst G X) ((fst G X)⁻¹ • (snd G X))
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp only [Category.assoc, lift_snd, ModObj.comp_smul, GrpObj.comp_inv,
        lift_fst, inv_smul_smul, Category.id_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp only [Category.assoc, lift_snd, ModObj.comp_smul, lift_fst,
        smul_inv_smul, Category.id_comp]

@[reassoc (attr := simp)] theorem ModObj.actionGraphIso_hom_fst :
    (ModObj.actionGraphIso G X).hom ≫ fst G X = fst G X := by
  simp [ModObj.actionGraphIso]

@[reassoc (attr := simp)] theorem ModObj.actionGraphIso_hom_snd :
    (ModObj.actionGraphIso G X).hom ≫ snd G X = γ[G,X] := by
  simp [ModObj.actionGraphIso, Hom.smul_def]

variable {G X} {Y : C} [ModObj G Y]

/-- The equivariance square for a group action is cartesian. This is an
identity of categorical pullbacks, valid on every test scheme. -/
theorem IsModHom.action_isPullback (f : Y ⟶ X) [IsModHom G f] :
    IsPullback (G ◁ f) γ[G,Y] γ[G,X] f := by
  refine IsPullback.mk' (IsModHom.smul_hom (A := G) (f := f)).symm ?_ ?_
  · intro Z a b hab haction
    apply CartesianMonoidalCategory.hom_ext
    · have h := congrArg (fun z => z ≫ fst G X) hab
      simpa only [Category.assoc, whiskerLeft_fst, Category.comp_id] using h
    · have hfst : a ≫ fst G Y = b ≫ fst G Y := by
        have h := congrArg (fun z => z ≫ fst G X) hab
        simpa only [Category.assoc, whiskerLeft_fst, Category.comp_id] using h
      have hsmul : (a ≫ fst G Y) • (a ≫ snd G Y) =
          (b ≫ fst G Y) • (b ≫ snd G Y) := by
        simpa only [Hom.smul_def, ← comp_lift_assoc, lift_fst_snd,
          Category.id_comp] using haction
      rw [hfst] at hsmul
      exact (MulAction.injective (b ≫ fst G Y)) hsmul
  · intro Z a b hab
    let g : Z ⟶ G := a ≫ fst G X
    let x : Z ⟶ X := a ≫ snd G X
    have hga : g • x = b ≫ f := by
      simpa only [g, x, Hom.smul_def, ← comp_lift_assoc, lift_fst_snd,
        Category.id_comp] using hab
    refine ⟨lift g (g⁻¹ • b), ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp [g]
      · simp only [Category.assoc, whiskerLeft_snd, lift_snd_assoc,
          IsModHom.map_smul]
        rw [← hga, inv_smul_smul]
    · change g • (g⁻¹ • b) = b
      exact smul_inv_smul g b

end CategoryTheory

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]

/-- Dense equivariant open torus, stated entirely using schemes and their
morphisms. All further classification conclusions must be derived. -/
structure SplitToricEmbedding where
  torus : splitTorusOver k (Fin n → ℤ) ⟶ X
  open_immersion : IsOpenImmersion torus.left
  dense : DenseRange torus.left
  equivariant : μ[splitTorusOver k (Fin n → ℤ)] ≫ torus =
    splitTorusOver k (Fin n → ℤ) ◁ torus ≫ γ[splitTorusOver k (Fin n → ℤ),X]

attribute [instance] SplitToricEmbedding.open_immersion

namespace SplitToricEmbedding

variable {k n X} (T : SplitToricEmbedding k n X)

def torusOpen : X.left.Opens := T.torus.left.opensRange

def boundary : Set X.left := (T.torusOpen : Set X.left)ᶜ

theorem boundary_isClosed : IsClosed T.boundary :=
  T.torusOpen.isOpen.isClosed_compl

theorem torusOpen_dense : Dense (T.torusOpen : Set X.left) := T.dense

attribute [local instance] ModObj.regular

instance torus_isModHom : IsModHom (splitTorusOver k (Fin n → ℤ)) T.torus where
  smul_hom := T.equivariant

/-- The action pulls the torus open back to its product with the torus.
The exact pullback statement precedes any assertion about boundaries. -/
theorem torus_action_isPullback :
    IsPullback (splitTorusOver k (Fin n → ℤ) ◁ T.torus)
      μ[splitTorusOver k (Fin n → ℤ)]
      γ[splitTorusOver k (Fin n → ℤ),X] T.torus :=
  IsModHom.action_isPullback T.torus

end SplitToricEmbedding

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

/-- The fan construction produces an intrinsic dense equivariant torus
embedding. This direction contains no classification assumption. -/
def intrinsicToricEmbedding :
    SplitToricEmbedding k n («Σ».fanSchemeOver k) where
  torus := («Σ».splitTorusOpenMap k).asOver (Spec (CommRingCat.of k))
  open_immersion := by
    change IsOpenImmersion («Σ».splitTorusOpenMap k)
    exact «Σ».splitTorusOpenMap_isOpenImmersion k
  dense := «Σ».splitTorusOpenMap_denseRange k
  equivariant := «Σ».fanScheme_action_extends_torus k

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms CategoryTheory.IsModHom.action_isPullback
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.intrinsicToricEmbedding
