module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import paper_verification.toric022
public import paper_verification.toric023

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricIntrinsicAction
section Source_ToricIntrinsicAction

-- original header: module

-- original header: public import PaperVerification.ToricFanAction
-- original header: public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
-- original header: public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.Proper

-- original header: @[expose] public section

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
end
end Source_ToricIntrinsicAction
-- END ORIGINAL PaperVerification.ToricIntrinsicAction


-- BEGIN ORIGINAL PaperVerification.ToricTorusGeometricIntegral
section Source_ToricTorusGeometricIntegral

-- original header: module

-- original header: public import PaperVerification.ToricTorusAction
-- original header: public import PaperVerification.ToricLaurentPicard
-- original header: public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
-- original header: public import Mathlib.AlgebraicGeometry.Geometrically.Integral

-- original header: @[expose] public section

/-!
# Geometric integrality of the actual split torus

The proof uses arbitrary field-valued base changes of schemes.  It makes
no appeal to the density of rational points.  The affine coordinate-ring
calculation is the literal scalar extension of the group algebra.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Limits
open PaperVerification.ToricCharacters
open scoped TensorProduct

variable (k : Type u) [Field k] (n : ℕ)

instance splitTorus_integral : IsIntegral (splitTorus k (Fin n→ℤ)) := by
  letI := torusCoordinateRing_isDomain k n
  change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing k n)))
  infer_instance

/-- The coordinate algebra of the actual base change of the torus. -/
def torusBaseChangeAlgEquiv (K : Type u) [Field K] [Algebra k K] :
    torusCoordinateRing k n ⊗[k] K ≃ₐ[k] torusCoordinateRing K n :=
  (Algebra.TensorProduct.comm k (torusCoordinateRing k n) K).trans
    ((AddMonoidAlgebra.scalarTensorEquiv k K (M := Fin n → ℤ)).restrictScalars k)

/-- Every field extension gives the actual torus over that field. -/
def torusBaseChangeIso (K : Type u) [Field K] [Algebra k K] :
    pullback (splitTorusOver k (Fin n → ℤ)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
        splitTorus K (Fin n → ℤ) :=
  pullbackSpecIso k (torusCoordinateRing k n) K ≪≫
    Scheme.Spec.mapIso (torusBaseChangeAlgEquiv k n K).toRingEquiv.toCommRingCatIso.symm.op

/-- Geometric integrality is derived from the actual affine base change,
including extensions that are not algebraically closed. -/
instance splitTorus_geometricallyIntegral :
    GeometricallyIntegral (splitTorusOver k (Fin n → ℤ)).hom := by
  constructor
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  letI := torusCoordinateRing_isDomain K n
  have hT : IsIntegral (splitTorus K (Fin n → ℤ)) := by
    change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing K n)))
    infer_instance
  let e := h.isoPullback ≪≫ torusBaseChangeIso k n K
  exact IsIntegral.of_isIso e.inv

/-- The torus projection is open and has geometrically irreducible
fibres. Consequently every irreducible subset has irreducible preimage. -/
theorem torusProjection_isIrreducible_preimage
    (X : Over (Spec (CommRingCat.of k))) {Z : Set X.left}
    (hZ : IsIrreducible Z) :
    IsIrreducible ((pullback.snd (splitTorusOver k (Fin n → ℤ)).hom X.hom) ⁻¹' Z) := by
  exact (pullback.snd (splitTorusOver k (Fin n → ℤ)).hom X.hom).isIrreducible_preimage
    (Scheme.Hom.isOpenMap _) hZ

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.splitTorus_geometricallyIntegral
end
end Source_ToricTorusGeometricIntegral
-- END ORIGINAL PaperVerification.ToricTorusGeometricIntegral


