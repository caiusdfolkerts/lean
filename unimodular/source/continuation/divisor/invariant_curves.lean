module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part12
public import Continuation.Divisor.WallCurves
public import Continuation.Divisor.FanDimension
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

public section

/-! Actual invariant integral curves are genuine orbit closures. Exact original source checksums and selections are recorded beside this file. -/

section Source_ToricIntrinsicAction



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
end
end
end Source_ToricIntrinsicAction

section Source_ToricEquivariantPullbacks



@[expose] public section

/-!
# Actual equivariant fibre products

The action on a fibre product is constructed by its categorical universal
property.  Both projections are genuine equivariant morphisms.  Forgetting
the base scheme preserves this pullback, so the construction supplies the
actual invariant affine restrictions used in the orbit classification.
-/

noncomputable section

universe v u

namespace PaperVerification.ToricSchemes

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

section Categorical

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (G : C) [MonObj G] {X Y Z : C}
    [ModObj G X] [ModObj G Y] [ModObj G Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsModHom G f] [IsModHom G g]
    [HasPullback f g]

def equivariantPullbackActionMap : G ⊗ pullback f g ⟶ pullback f g :=
  pullback.lift
    (G ◁ pullback.fst f g ≫ γ[G,X])
    (G ◁ pullback.snd f g ≫ γ[G,Y]) (by
      have hf := IsModHom.smul_hom (A := G) (f := f)
      have hg := IsModHom.smul_hom (A := G) (f := g)
      change γ[G,X] ≫ f = G ◁ f ≫ γ[G,Z] at hf
      change γ[G,Y] ≫ g = G ◁ g ≫ γ[G,Z] at hg
      rw [Category.assoc, hf, ← whiskerLeft_comp_assoc,
        pullback.condition, whiskerLeft_comp, Category.assoc, ← hg, Category.assoc])

@[reassoc (attr := simp)] theorem equivariantPullbackActionMap_fst :
    equivariantPullbackActionMap G f g ≫ pullback.fst f g =
      G ◁ pullback.fst f g ≫ γ[G,X] :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem equivariantPullbackActionMap_snd :
    equivariantPullbackActionMap G f g ≫ pullback.snd f g =
      G ◁ pullback.snd f g ≫ γ[G,Y] :=
  pullback.lift_snd _ _ _

/-- Actions on schemes, rather than only actions on geometric points,
are preserved by an equivariant fibre product. -/
def equivariantPullbackModObj : ModObj G (pullback f g) where
  smul := equivariantPullbackActionMap G f g
  one_smul := by
    change (η[G] ▷ pullback f g) ≫ equivariantPullbackActionMap G f g =
      (λ_ (pullback f g)).hom
    apply pullback.hom_ext
    · simp only [Category.assoc, equivariantPullbackActionMap_fst]
      rw [← whisker_exchange_assoc, ModObj.one_smul_self,
        leftUnitor_naturality]
    · simp only [Category.assoc, equivariantPullbackActionMap_snd]
      rw [← whisker_exchange_assoc, ModObj.one_smul_self,
        leftUnitor_naturality]
  mul_smul := by
    change (μ[G] ▷ pullback f g) ≫ equivariantPullbackActionMap G f g =
      (α_ G G (pullback f g)).hom ≫
        (G ◁ equivariantPullbackActionMap G f g) ≫ equivariantPullbackActionMap G f g
    apply pullback.hom_ext
    · simp only [Category.assoc, equivariantPullbackActionMap_fst]
      rw [← whiskerLeft_comp_assoc, equivariantPullbackActionMap_fst,
        whiskerLeft_comp, ← whisker_exchange_assoc,
        ModObj.mul_smul_self, associator_naturality_right_assoc]
      simp only [Category.assoc]
    · simp only [Category.assoc, equivariantPullbackActionMap_snd]
      rw [← whiskerLeft_comp_assoc, equivariantPullbackActionMap_snd,
        whiskerLeft_comp, ← whisker_exchange_assoc,
        ModObj.mul_smul_self, associator_naturality_right_assoc]
      simp only [Category.assoc]

theorem equivariantPullback_fst_isModHom :
    letI := equivariantPullbackModObj G f g
    IsModHom G (pullback.fst f g) := by
  letI := equivariantPullbackModObj G f g
  exact ⟨equivariantPullbackActionMap_fst G f g⟩

theorem equivariantPullback_snd_isModHom :
    letI := equivariantPullbackModObj G f g
    IsModHom G (pullback.snd f g) := by
  letI := equivariantPullbackModObj G f g
  exact ⟨equivariantPullbackActionMap_snd G f g⟩

end Categorical

open AlgebraicGeometry

variable {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The underlying square is the actual scheme-theoretic fibre product.
Connected-limit preservation is a theorem of the ordinary over category. -/
theorem overPullback_isPullback :
    IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left :=
  (Over.forget S).map_isPullback (IsPullback.of_hasPullback f g)

theorem overPullback_fst_isClosedImmersion [IsClosedImmersion g.left] :
    IsClosedImmersion (pullback.fst f g).left :=
  MorphismProperty.of_isPullback (overPullback_isPullback f g).flip inferInstance

theorem overPullback_snd_isOpenImmersion [IsOpenImmersion f.left] :
    IsOpenImmersion (pullback.snd f g).left :=
  MorphismProperty.of_isPullback (overPullback_isPullback f g) inferInstance

/-- An actual point in the inverse image of an open chart produces a
point of the equivariant pullback, including its residue-field data. -/
theorem overPullback_nonempty [IsOpenImmersion f.left]
    (y : Y.left) (hy : g.left y ∈ f.left.opensRange) :
    Nonempty (pullback f g).left := by
  have hy' : y ∈ Set.range (pullback.snd f.left g.left) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    exact hy
  obtain ⟨p, hp⟩ := hy'
  exact ⟨(overPullback_isPullback f g).isoPullback.inv p⟩

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.equivariantPullbackModObj
#print axioms PaperVerification.ToricSchemes.overPullback_isPullback
end
end
end Source_ToricEquivariantPullbacks

section Source_ToricAffineActionCoaction



@[expose] public section

/-!
# Comorphisms of actual affine torus actions

The coaction of an arbitrary affine torus scheme is extracted from its
actual action morphism by the fully faithful affine Spec functor and
the proved tensor-product/fiber-product isomorphism. Equivariance of
actual scheme maps implies the corresponding algebraic coaction equation.
-/

noncomputable section

universe u v

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory MonObj
open scoped TensorProduct

local instance (k : Type u) [CommRing k] :
    (algSpec (CommRingCat.of k)).Monoidal :=
  (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal

local instance (k : Type u) [CommRing k] :
    (algSpec (CommRingCat.of k)).LaxMonoidal :=
  (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toLaxMonoidal

local instance (k : Type u) [CommRing k] :
    (algSpec (CommRingCat.of k)).OplaxMonoidal :=
  (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toOplaxMonoidal

variable (k : Type (max u v)) [CommRing k] (M : Type v) [AddCommGroup M]

local notation "F" => (algSpec (CommRingCat.of k) :
  (CommAlgCat k)ᵒᵖ ⥤ Over (Spec (CommRingCat.of k)))
local notation "T" => op (CommAlgCat.of k (AddMonoidAlgebra k M))
local notation "G" => splitTorusOver k M

/-- The actual semigroup action, on the literally bundled affine Spec object. -/
instance semigroupChart_algSpec_torusAction (S : AddSubmonoid M) :
    ModObj G ((F).obj (op (CommAlgCat.of k (AddMonoidAlgebra k S)))) := by
  change ModObj G (semigroupChartOver k S)
  exact semigroupChart_torusAction k S

def affineTorusActionArrow (B : CommAlgCat.{max u v} k)
    [ModObj G ((F).obj (op B))] : T⊗op B⟶op B :=
  (algSpec.fullyFaithful (R:=CommRingCat.of k)).preimage
    (Functor.OplaxMonoidal.δ F T (op B)≫γ[G,(F).obj (op B)])

@[simp] theorem affineTorusActionArrow_spec (B : CommAlgCat.{max u v} k)
    [ModObj G ((F).obj (op B))] :
    (F).map (affineTorusActionArrow k M B)=
      Functor.OplaxMonoidal.δ F T (op B)≫γ[G,(F).obj (op B)] :=
  (algSpec.fullyFaithful (R:=CommRingCat.of k)).map_preimage _

/-- The literal algebra comorphism of the given action. -/
def affineTorusActionCoaction (B : CommAlgCat.{max u v} k)
    [ModObj G ((F).obj (op B))] :
    B→ₐ[k]AddMonoidAlgebra k M⊗[k]B :=
  (affineTorusActionArrow k M B).unop.hom

theorem affineTorusActionArrow_natural {B C : CommAlgCat.{max u v} k}
    [ModObj G ((F).obj (op B))] [ModObj G ((F).obj (op C))]
    (f : op B⟶op C) [IsModHom G ((F).map f)] :
    affineTorusActionArrow k M B≫f=
      (T◁f)≫affineTorusActionArrow k M C := by
  let a : (F).obj T ⊗ (F).obj (op B) ⟶ (F).obj (op B) := γ[G,(F).obj (op B)]
  let b : (F).obj T ⊗ (F).obj (op C) ⟶ (F).obj (op C) := γ[G,(F).obj (op C)]
  have ha : (F).map (affineTorusActionArrow k M B) =
      Functor.OplaxMonoidal.δ F T (op B) ≫ a := affineTorusActionArrow_spec k M B
  have hb : (F).map (affineTorusActionArrow k M C) =
      Functor.OplaxMonoidal.δ F T (op C) ≫ b := affineTorusActionArrow_spec k M C
  have heq : a ≫ (F).map f = ((F).obj T ◁ (F).map f) ≫ b :=
    IsModHom.smul_hom (A := G) (f := (F).map f)
  apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  calc
    (F).map (affineTorusActionArrow k M B ≫ f) =
        (F).map (affineTorusActionArrow k M B) ≫ (F).map f := (F).map_comp _ _
    _ = (Functor.OplaxMonoidal.δ F T (op B) ≫ a) ≫ (F).map f :=
      congrArg (fun g : (F).obj (T ⊗ op B) ⟶ (F).obj (op B) => g ≫ (F).map f) ha
    _ = Functor.OplaxMonoidal.δ F T (op B) ≫ (a ≫ (F).map f) := Category.assoc _ _ _
    _ = Functor.OplaxMonoidal.δ F T (op B) ≫ (((F).obj T ◁ (F).map f) ≫ b) :=
      congrArg (fun g : (F).obj T ⊗ (F).obj (op B) ⟶ (F).obj (op C) =>
        Functor.OplaxMonoidal.δ F T (op B) ≫ g) heq
    _ = (Functor.OplaxMonoidal.δ F T (op B) ≫ ((F).obj T ◁ (F).map f)) ≫ b :=
      (Category.assoc _ _ _).symm
    _ = ((F).map (T ◁ f) ≫ Functor.OplaxMonoidal.δ F T (op C)) ≫ b :=
      congrArg (fun g : (F).obj (T ⊗ op B) ⟶ (F).obj T ⊗ (F).obj (op C) => g ≫ b)
        (Functor.OplaxMonoidal.δ_natural_right F T f)
    _ = (F).map (T ◁ f) ≫ (Functor.OplaxMonoidal.δ F T (op C) ≫ b) :=
      Category.assoc _ _ _
    _ = (F).map (T ◁ f) ≫ (F).map (affineTorusActionArrow k M C) :=
      congrArg (fun g : (F).obj (T ⊗ op C) ⟶ (F).obj (op C) => (F).map (T ◁ f) ≫ g) hb.symm
    _ = (F).map ((T ◁ f) ≫ affineTorusActionArrow k M C) := ((F).map_comp _ _).symm

/-- Naturality is obtained from actual equivariance, for arbitrary
affine actions on the source and target. -/
theorem affineTorusActionCoaction_natural {B C : CommAlgCat.{max u v} k}
    [ModObj G ((F).obj (op B))] [ModObj G ((F).obj (op C))]
    (q : C→ₐ[k]B) [IsModHom G ((F).map (CommAlgCat.ofHom q).op)] :
    (Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M)) q).comp
        (affineTorusActionCoaction k M C)=
      (affineTorusActionCoaction k M B).comp q := by
  have h := congrArg (fun f : T⊗op B⟶op C=>f.unop.hom)
    (affineTorusActionArrow_natural k M (CommAlgCat.ofHom q).op)
  exact h.symm

theorem affineTorusActionCoaction_semigroup (S : AddSubmonoid M) :
    affineTorusActionCoaction k M (CommAlgCat.of k (AddMonoidAlgebra k S))=
      semigroupChartCoaction k S := by
  have h : affineTorusActionArrow k M (CommAlgCat.of k (AddMonoidAlgebra k S))=
      (CommAlgCat.ofHom (semigroupChartCoaction k S)).op := by
    apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
    rw [affineTorusActionArrow_spec]
    apply Over.OverMorphism.ext
    change (pullbackSpecIso (CommRingCat.of k)
        (CommRingCat.of (AddMonoidAlgebra k M))
        (CommRingCat.of (AddMonoidAlgebra k S))).inv≫
      (γ[G,semigroupChartOver k S]).left=
        Spec.map (CommRingCat.ofHom (semigroupChartCoaction k S).toRingHom)
    rw [semigroupChart_action_spec]
    exact (pullbackSpecIso (CommRingCat.of k)
      (CommRingCat.of (AddMonoidAlgebra k M))
      (CommRingCat.of (AddMonoidAlgebra k S))).inv_hom_id_assoc
        (Spec.map (CommRingCat.ofHom (semigroupChartCoaction k S).toRingHom))
  exact congrArg (fun f=>f.unop.hom) h

/-- Vanishing in an actual equivariant affine quotient is preserved by
the true semigroup coaction after applying that quotient in the second
factor. No character-stability hypothesis appears. -/
theorem semigroupCoaction_quotient_zero (S : AddSubmonoid M)
    (B : CommAlgCat.{max u v} k) [ModObj G ((F).obj (op B))]
    (q : AddMonoidAlgebra k S→ₐ[k]B)
    [IsModHom G ((F).map (CommAlgCat.ofHom q).op)]
    {f : AddMonoidAlgebra k S} (hf : q f=0) :
    Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M)) q
      (semigroupChartCoaction k S f)=0 := by
  have h := congrArg
    (fun φ : AddMonoidAlgebra k S →ₐ[k] AddMonoidAlgebra k M ⊗[k] B => φ f)
    (affineTorusActionCoaction_natural k M
      (B := B) (C := CommAlgCat.of k (AddMonoidAlgebra k S)) q)
  rw [affineTorusActionCoaction_semigroup] at h
  simpa only [AlgHom.comp_apply,hf,map_zero] using h

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.semigroupCoaction_quotient_zero
end
end
end Source_ToricAffineActionCoaction

section Source_ToricMonomialPrimeFaces



@[expose] public section

/-!
# Prime character ideals and their actual additive faces

The component property of an equivariant quotient kernel is derived
from the actual affine action. Primality then makes its surviving
characters an additive face, and the ideal is exactly the kernel of the
literal semigroup-face quotient.
-/

noncomputable section

universe u v

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricSchemes
open scoped TensorProduct Classical

variable (k : Type (max u v)) [Field k] {M : Type v} [AddCommGroup M]
    (S : AddSubmonoid M)

theorem semigroupCoefficient_quotient
    (B : Type (max u v)) [CommRing B] [Algebra k B]
    (q : AddMonoidAlgebra k S→ₐ[k]B) (s : S) (f : AddMonoidAlgebra k S) :
    characterCoefficient k (s:M)
      (Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M)) q
        (semigroupChartCoaction k S f))=q (single s (f.coeff s)) := by
  have h : (characterCoefficient k (s:M)).comp
        (((Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M)) q).toLinearMap).comp
          (semigroupChartCoaction k S).toLinearMap)=
      q.toLinearMap.comp ((AddMonoidAlgebra.lsingle (R:=k) s).comp
        ((AddMonoidAlgebra.basis S k).coord s)) := by
    apply (AddMonoidAlgebra.basis S k).ext
    intro t
    by_cases ht : t=s
    · subst t
      simp [AddMonoidAlgebra.basis,semigroupChartCoaction_single,characterCoefficient_tmul]
    · have hv : (t:M)≠(s:M) := fun h=>ht (Subtype.ext h)
      simp [AddMonoidAlgebra.basis,semigroupChartCoaction_single,characterCoefficient_tmul,ht,hv,Ne.symm ht,Ne.symm hv]
  exact congrArg (fun φ=>φ f) h

/-- An actual equivariant affine quotient kernel contains every literal
character component of each of its elements. -/
theorem equivariant_kernel_component
    (B : CommAlgCat.{max u v} k)
    [ModObj (splitTorusOver k M) ((algSpec (CommRingCat.of k)).obj (op B))]
    (q : AddMonoidAlgebra k S→ₐ[k]B)
    [IsModHom (splitTorusOver k M)
      ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom q).op)]
    {f : AddMonoidAlgebra k S} (hf : f∈RingHom.ker q.toRingHom) (s : S) :
    single s (f.coeff s)∈RingHom.ker q.toRingHom := by
  have h := semigroupCoaction_quotient_zero k M S B q (RingHom.mem_ker.mp hf)
  have hc := congrArg (characterCoefficient k (s:M)) h
  rw [semigroupCoefficient_quotient,map_zero] at hc
  exact RingHom.mem_ker.mpr hc

variable {S}

/-- The component property is an intermediate theorem, rather than a
replacement for equivariance in the geometric endpoint. -/
def IsMonomialIdeal (P : Ideal (AddMonoidAlgebra k S)) : Prop :=
  ∀ f∈P,∀ s : S,single s (f.coeff s)∈P

theorem single_one_mem_of_component
    (P : Ideal (AddMonoidAlgebra k S)) (hP : IsMonomialIdeal k P)
    {f : AddMonoidAlgebra k S} (hf : f∈P) {s : S} (hs : f.coeff s≠0) :
    single s (1:k)∈P := by
  have h := (P.restrictScalars k).smul_mem (f.coeff s)⁻¹ (hP f hf s)
  change (f.coeff s)⁻¹ • single s (f.coeff s) ∈ P at h
  simpa only [smul_single,smul_eq_mul,inv_mul_cancel₀ hs] using h

def survivingCharacterFace (P : Ideal (AddMonoidAlgebra k S)) [P.IsPrime] :
    AddSubmonoid S where
  carrier := {s | single s (1:k)∉P}
  zero_mem' := by
    change single (0 : S) (1 : k) ∉ P
    simpa only [← AddMonoidAlgebra.one_def] using Ideal.one_notMem P
  add_mem' := by
    intro s t hs ht
    change single s (1 : k) ∉ P at hs
    change single t (1 : k) ∉ P at ht
    change single (s + t) (1 : k) ∉ P
    have h := (inferInstance : P.IsPrime).mul_notMem hs ht
    simpa only [single_mul_single,one_mul] using h

theorem survivingCharacterFace_isAdditiveFace
    (P : Ideal (AddMonoidAlgebra k S)) [P.IsPrime] :
    IsAdditiveFace (survivingCharacterFace k P) := by
  intro s t h
  constructor
  · intro hs
    apply h
    have hm := P.mul_mem_right (single t (1:k)) hs
    simpa only [single_mul_single,one_mul] using hm
  · intro ht
    apply h
    have hm := P.mul_mem_left (single s (1:k)) ht
    simpa only [single_mul_single,one_mul] using hm

theorem additiveFaceRetraction_coeff
    (F : AddSubmonoid S) (hF : IsAdditiveFace F)
    (f : AddMonoidAlgebra k S) (s : F) :
    (additiveFaceRetraction k F hF f).coeff s=f.coeff s.val := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,coeff_add,hf,hg,Finsupp.add_apply]
  | single t c =>
    by_cases ht : t∈F
    · rw [additiveFaceRetraction_single_of_mem k F hF t ht]
      by_cases hts : t=s.val
      · subst t
        simp
      · have hn : (⟨t,ht⟩:F)≠s := fun h=>hts (congrArg Subtype.val h)
        simp [hts,hn,Ne.symm hts,Ne.symm hn]
    · rw [additiveFaceRetraction_single_of_not_mem k F hF t ht]
      have hts : t≠s.val := fun h=>ht (h.symm ▸ s.property)
      simp [hts,Ne.symm hts]

/-- The quotient ideal is the actual kernel of the canonical face
retraction, with equality of all polynomials, not only characters. -/
theorem monomialPrime_eq_face_kernel
    (P : Ideal (AddMonoidAlgebra k S)) [P.IsPrime] (hP : IsMonomialIdeal k P) :
    P=RingHom.ker (additiveFaceRetraction k (survivingCharacterFace k P)
      (survivingCharacterFace_isAdditiveFace k P)).toRingHom := by
  let F := survivingCharacterFace k P
  let hF := survivingCharacterFace_isAdditiveFace k P
  ext f
  rw [RingHom.mem_ker]
  constructor
  · intro hf
    change additiveFaceRetraction k F hF f = 0
    ext s
    rw [additiveFaceRetraction_coeff]
    change f.coeff s.val=0
    by_contra hs
    exact s.property (single_one_mem_of_component k P hP hf hs)
  · intro hf
    change additiveFaceRetraction k F hF f = 0 at hf
    have hsum : f=∑ s∈f.coeff.support,single s (f.coeff s) :=
      (AddMonoidAlgebra.sum_coeff_single f).symm
    rw [hsum]
    apply P.sum_mem
    intro s hs
    by_cases hsF : s∈F
    · have hz := congrArg (fun g : AddMonoidAlgebra k F=>g.coeff ⟨s,hsF⟩) hf
      rw [additiveFaceRetraction_coeff] at hz
      have hc : f.coeff s=0 := by simpa using hz
      simp only [hc,single_zero,P.zero_mem]
    · have hm : single s (1:k)∈P := by
        change ¬¬single s (1:k)∈P at hsF
        exact not_not.mp hsF
      have h := (P.restrictScalars k).smul_mem (f.coeff s) hm
      change f.coeff s • single s (1 : k) ∈ P at h
      simpa only [smul_single,smul_eq_mul,mul_one] using h

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.equivariant_kernel_component
#print axioms PaperVerification.ToricCharacters.monomialPrime_eq_face_kernel
end
end
end Source_ToricMonomialPrimeFaces

section Source_ToricSmoothMonoidFaces



@[expose] public section

/-!
# Additive faces of an actual smooth full cone

A full smooth dual cone is the nonnegative integer span of an integral
basis. Every additive face is obtained by forcing a subset of those
coordinates to zero. This is proved by basis expansion and the actual
additive-face property.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open scoped BigOperators Classical

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℤ E]
    (b : Module.Basis ι ℤ E)

abbrev fullCoordinateMonoid := coordinateConeMonoid b Finset.univ

def fullConeBasisVector (i : ι) : fullCoordinateMonoid b :=
  ⟨b i,by
    intro j hj
    rw [b.repr_self_apply]
    split_ifs <;> norm_num⟩

@[simp] theorem fullConeBasisVector_repr (i j : ι) :
    b.repr (fullConeBasisVector b i).val j=if i=j then 1 else 0 :=
  b.repr_self_apply (i := i) j

theorem fullCoordinate_nonneg (x : fullCoordinateMonoid b) (i : ι) :
    0≤b.repr x.val i := x.property i (Finset.mem_univ i)

theorem fullCoordinate_basis_sum (x : fullCoordinateMonoid b) :
    (∑ i,(b.repr x.val i).toNat • fullConeBasisVector b i)=x := by
  apply Subtype.ext
  change (fullCoordinateMonoid b).subtype
    (∑ i,(b.repr x.val i).toNat • fullConeBasisVector b i) = x.val
  rw [map_sum]
  simp only [map_nsmul]
  change (∑ i,(b.repr x.val i).toNat • b i)=x.val
  calc
    _=(∑ i,b.repr x.val i • b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← natCast_zsmul,Int.toNat_of_nonneg (fullCoordinate_nonneg b x i)]
    _=x.val :=
      (Finset.sum_congr rfl (fun i _ =>
        (int_smul_eq_zsmul (inferInstance : Module ℤ E)
          (b.repr x.val i) (b i)).symm)).trans (b.sum_repr x.val)

def fullConeSubtractBasis (x : fullCoordinateMonoid b) (i : ι)
    (hi : 0<b.repr x.val i) : fullCoordinateMonoid b :=
  ⟨x.val-b i,by
    intro j hj
    rw [map_sub,Finsupp.sub_apply,b.repr_self_apply]
    by_cases h : i=j
    · subst j
      simp only [if_pos rfl]
      omega
    · simp only [if_neg h,sub_zero]
      exact fullCoordinate_nonneg b x j⟩

theorem fullConeSubtractBasis_add (x : fullCoordinateMonoid b) (i : ι)
    (hi : 0<b.repr x.val i) :
    fullConeBasisVector b i+fullConeSubtractBasis b x i hi=x := by
  apply Subtype.ext
  change b i+(x.val-b i)=x.val
  abel

theorem additiveFace_basis_mem_of_coordinate_pos
    (F : AddSubmonoid (fullCoordinateMonoid b)) (hF : IsAdditiveFace F)
    {x : fullCoordinateMonoid b} (hx : x∈F) (i : ι)
    (hi : 0<b.repr x.val i) : fullConeBasisVector b i∈F := by
  have hsum : fullConeBasisVector b i+fullConeSubtractBasis b x i hi∈F := by
    rwa [fullConeSubtractBasis_add]
  exact (hF _ _ hsum).1

/-- Exactly the coordinates omitted by an additive face. -/
def forbiddenFaceCoordinates (F : AddSubmonoid (fullCoordinateMonoid b)) : Finset ι :=
  Finset.univ.filter (fun i=>fullConeBasisVector b i∉F)

theorem additiveFace_mem_iff_zero_coordinates
    (F : AddSubmonoid (fullCoordinateMonoid b)) (hF : IsAdditiveFace F)
    (x : fullCoordinateMonoid b) :
    x∈F ↔ ∀ i∈forbiddenFaceCoordinates b F,b.repr x.val i=0 := by
  constructor
  · intro hx i hi
    have hnot := (Finset.mem_filter.mp hi).2
    have hn := fullCoordinate_nonneg b x i
    by_contra hz
    have hp : 0<b.repr x.val i := lt_of_le_of_ne hn (Ne.symm hz)
    exact hnot (additiveFace_basis_mem_of_coordinate_pos b F hF hx i hp)
  · intro hx
    rw [← fullCoordinate_basis_sum b x]
    apply F.sum_mem
    intro i hi
    by_cases hmem : fullConeBasisVector b i∈F
    · exact F.nsmul_mem hmem _
    · have hz := hx i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hmem⟩)
      simp only [hz,Int.toNat_zero,zero_nsmul,F.zero_mem]

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open scoped BigOperators Classical

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))

def fullDualConeBasisVector (i : Fin n) :
    dualConeMonoid (Finset.univ.image b) :=
  ⟨integralDualBasis b i,by
    intro u hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hu
    rw [integerPairing_basis_eq_dualCoordinate,(integralDualBasis b).repr_self_apply]
    split_ifs <;> norm_num⟩

def fullDualForbiddenCoordinates
    (F : AddSubmonoid (dualConeMonoid (Finset.univ.image b))) : Finset (Fin n) :=
  Finset.univ.filter (fun i=>fullDualConeBasisVector b i∉F)

/-- Every actual additive face of a smooth full dual cone is the face
annihilating an actual subset of the original primitive cone rays. -/
theorem fullDual_additiveFace_eq_orbitFace
    (F : AddSubmonoid (dualConeMonoid (Finset.univ.image b)))
    (hF : IsAdditiveFace F) :
    F=orbitCharacterFace (Finset.univ.image b)
      ((fullDualForbiddenCoordinates b F).image b) := by
  have he : dualConeMonoid (Finset.univ.image b)=
      fullCoordinateMonoid (integralDualBasis b) := dualConeMonoid_basis_eq b Finset.univ
  let e : dualConeMonoid (Finset.univ.image b)≃+
      fullCoordinateMonoid (integralDualBasis b) :=
    { toFun x := ⟨x.val,he ▸ x.property⟩
      invFun x := ⟨x.val,he.symm ▸ x.property⟩
      left_inv x := Subtype.ext rfl
      right_inv x := Subtype.ext rfl
      map_add' x y := Subtype.ext rfl }
  let F' := F.map e.toAddMonoidHom
  have hF' : IsAdditiveFace F' := by
    intro x y h
    obtain ⟨z,hz,hzxy⟩ := h
    have heq : z=e.symm x+e.symm y := by
      apply e.injective
      simpa using hzxy
    have hm := hF _ _ (heq ▸ hz)
    exact ⟨⟨e.symm x,hm.1,e.apply_symm_apply x⟩,
      ⟨e.symm y,hm.2,e.apply_symm_apply y⟩⟩
  have hmem (x : dualConeMonoid (Finset.univ.image b)) : e x∈F'↔x∈F := by
    constructor
    · rintro ⟨y,hy,he⟩
      exact e.injective he ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  have haxis (i : Fin n) : e (fullDualConeBasisVector b i)=
      fullConeBasisVector (integralDualBasis b) i := by
    apply Subtype.ext
    rfl
  have hind : forbiddenFaceCoordinates (integralDualBasis b) F'=
      fullDualForbiddenCoordinates b F := by
    ext i
    simp only [forbiddenFaceCoordinates,fullDualForbiddenCoordinates,Finset.mem_filter,
      Finset.mem_univ,true_and,← haxis,hmem]
  ext x
  rw [← hmem x,additiveFace_mem_iff_zero_coordinates _ F' hF',hind]
  change (∀ i∈fullDualForbiddenCoordinates b F,
    (integralDualBasis b).repr x.val i=0) ↔
      ∀ u∈(fullDualForbiddenCoordinates b F).image b,integerPairing u x.val=0
  constructor
  · intro hx u hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    rw [integerPairing_basis_eq_dualCoordinate]
    exact hx i hi
  · intro hx i hi
    rw [← integerPairing_basis_eq_dualCoordinate]
    exact hx (b i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.fullDual_additiveFace_eq_orbitFace
end
end
end Source_ToricSmoothMonoidFaces

section Source_ToricInvariantChartPrimes



@[expose] public section

/-!
# Actual invariant prime closed subschemes of smooth affine charts

An arbitrary integral affine quotient with its genuine equivariant
torus action has a monomial prime kernel. The actual smooth basis then
identifies this kernel with the literal coordinate-face orbit quotient.
The final statement is equality of actual scheme ideal sheaves.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open AddMonoidAlgebra AlgebraicGeometry CategoryTheory Opposite MonoidalCategory MonObj
open scoped Classical

variable (k : Type u) [Field k] {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))

local notation "s" => Finset.univ.image b
local notation "S" => dualConeMonoid s
local notation "R" => monoidChartAlgebra k S
local notation "F" => (algSpec (CommRingCat.of k) :
  (CommAlgCat k)ᵒᵖ ⥤ Over (Spec (CommRingCat.of k)))
local notation "G" => splitTorusOver k (Lattice n)

local instance fullChart_algSpec_torusAction :
    ModObj G ((F).obj (op (CommAlgCat.of k R))) := by
  change ModObj G (monoidChartSchemeOver k S)
  exact monoidChartScheme_torusAction k S

theorem invariant_fullCone_ringKernel
    (B : CommAlgCat.{u} k) [IsDomain B]
    [ModObj G ((F).obj (op B))]
    (q : R→ₐ[k]B) [IsModHom G ((F).map (CommAlgCat.ofHom q).op)] :
    ∃ I : Finset (Fin n),
      RingHom.ker q.toRingHom=
        RingHom.ker (orbitQuotientAlgebraMap k b I s
          (Finset.image_subset_image (Finset.subset_univ I))).toRingHom := by
  let e := monoidChartAlgebraEquiv k S
  let q' := q.comp e.toAlgHom
  let f₀ : (F).obj (op B) ⟶ monoidChartSchemeOver k S :=
    (F).map (CommAlgCat.ofHom q).op
  letI : IsModHom G f₀ :=
    inferInstanceAs (IsModHom G ((F).map (CommAlgCat.ofHom q).op))
  have hspec : (F).map (CommAlgCat.ofHom q').op=
      f₀≫(monoidChartSchemeOverIso k S).hom := by
    change (F).map (CommAlgCat.ofHom q').op =
      (F).map (CommAlgCat.ofHom q).op ≫
        (F).map (CommAlgCat.ofHom e.toAlgHom).op
    exact (F).map_comp (CommAlgCat.ofHom q).op (CommAlgCat.ofHom e.toAlgHom).op
  letI : IsModHom G ((F).map (CommAlgCat.ofHom q').op) :=
    hspec.symm ▸ (inferInstance : IsModHom G (f₀≫(monoidChartSchemeOverIso k S).hom))
  let P := RingHom.ker q'.toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime q'.toRingHom
  have hP : IsMonomialIdeal k P := fun f hf m=>equivariant_kernel_component k S B q' hf m
  let J := survivingCharacterFace k P
  let I := fullDualForbiddenCoordinates b J
  have hJ : J=orbitCharacterFace s (I.image b) :=
    fullDual_additiveFace_eq_orbitFace b J (survivingCharacterFace_isAdditiveFace k P)
  have hker := monomialPrime_eq_face_kernel k P hP
  change P=RingHom.ker (additiveFaceRetraction k J
    (survivingCharacterFace_isAdditiveFace k P)).toRingHom at hker
  have hfaceKernel (J₁ J₂ : AddSubmonoid S)
      (h₁ : IsAdditiveFace J₁) (h₂ : IsAdditiveFace J₂) (h : J₁ = J₂) :
      RingHom.ker (additiveFaceRetraction k J₁ h₁).toRingHom =
        RingHom.ker (additiveFaceRetraction k J₂ h₂).toRingHom := by
    cases h
    rfl
  have hker := hker.trans (hfaceKernel J (orbitCharacterFace s (I.image b))
    (survivingCharacterFace_isAdditiveFace k P)
    (orbitCharacterFace_isAdditiveFace s (I.image b)
      (Finset.image_subset_image (Finset.subset_univ I))) hJ)
  refine ⟨I,?_⟩
  ext f
  rw [RingHom.mem_ker,RingHom.mem_ker]
  change q f = 0 ↔ orbitQuotientAlgebraMap k b I s
    (Finset.image_subset_image (Finset.subset_univ I)) f = 0
  have hz : q f=0 ↔
      additiveFaceRetraction k (orbitCharacterFace s (I.image b))
        (orbitCharacterFace_isAdditiveFace s (I.image b)
          (Finset.image_subset_image (Finset.subset_univ I))) (e.symm f)=0 := by
    have he := Iff.of_eq
      (congrArg (fun K : Ideal (AddMonoidAlgebra k S)=>e.symm f∈K) hker)
    change q (e (e.symm f)) = 0 ↔
      additiveFaceRetraction k (orbitCharacterFace s (I.image b))
        (orbitCharacterFace_isAdditiveFace s (I.image b)
          (Finset.image_subset_image (Finset.subset_univ I))) (e.symm f) = 0 at he
    simpa only [AlgEquiv.apply_symm_apply] using he
  rw [hz]
  let e₁ := AddMonoidAlgebra.domCongr k k (orbitQuotientSemigroupEquiv b I s)
  let e₂ := monoidChartAlgebraEquiv k (dualConeMonoid (orbitQuotientCone b I s))
  let z : AddMonoidAlgebra k (orbitCharacterFace s (I.image b)) :=
    additiveFaceRetraction k (orbitCharacterFace s (I.image b))
      (orbitCharacterFace_isAdditiveFace s (I.image b)
        (Finset.image_subset_image (Finset.subset_univ I))) (e.symm f)
  change z = 0 ↔ e₂ (e₁ z) = 0
  constructor
  · intro h
    rw [h,map_zero,map_zero]
  · intro h
    apply e₁.injective
    apply e₂.injective
    simpa only [map_zero] using h

end PaperVerification.ToricGeometry

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory MonObj
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open scoped Classical

/-- Equal affine coordinate kernels give equal actual scheme ideal
sheaves through the proved ΓSpec natural isomorphisms. -/
theorem specMap_kernel_eq_of_ringKernel_eq
    {A B C : CommRingCat.{u}} (f : A⟶B) (g : A⟶C)
    (h : RingHom.ker f.hom=RingHom.ker g.hom) :
    (Spec.map f).ker=(Spec.map g).ker := by
  rw [Scheme.ker_of_isAffine,Scheme.ker_of_isAffine]
  congr 1
  ext a
  have hf : (Spec.map f).appTop a=0 ↔ f ((Scheme.ΓSpecIso A).hom a)=0 := by
    have he := congrArg (fun φ=>φ a) (Scheme.ΓSpecIso_naturality f)
    constructor
    · intro hz
      simpa only [ConcreteCategory.comp_apply,hz,map_zero] using he.symm
    · intro hz
      apply (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv.injective
      change (Scheme.ΓSpecIso B).hom ((Spec.map f).appTop a) =
        (Scheme.ΓSpecIso B).hom 0
      simpa only [ConcreteCategory.comp_apply,hz,map_zero] using he
  have hg : (Spec.map g).appTop a=0 ↔ g ((Scheme.ΓSpecIso A).hom a)=0 := by
    have he := congrArg (fun φ=>φ a) (Scheme.ΓSpecIso_naturality g)
    constructor
    · intro hz
      simpa only [ConcreteCategory.comp_apply,hz,map_zero] using he.symm
    · intro hz
      apply (Scheme.ΓSpecIso C).commRingCatIsoToRingEquiv.injective
      change (Scheme.ΓSpecIso C).hom ((Spec.map g).appTop a) =
        (Scheme.ΓSpecIso C).hom 0
      simpa only [ConcreteCategory.comp_apply,hz,map_zero] using he
  rw [RingHom.mem_ker,RingHom.mem_ker,hf,hg]
  simpa only [RingHom.mem_ker] using
    Iff.of_eq (congrArg (fun I : Ideal A=>(Scheme.ΓSpecIso A).hom a∈I) h)

variable (k : Type u) [Field k] {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))

local notation "s" => Finset.univ.image b
local notation "S" => dualConeMonoid s
local notation "R" => monoidChartAlgebra k S
local notation "F" => (algSpec (CommRingCat.of k) :
  (CommAlgCat k)ᵒᵖ ⥤ Over (Spec (CommRingCat.of k)))
local notation "G" => splitTorusOver k (Lattice n)

local instance fullChart_algSpec_torusAction :
    ModObj G ((F).obj (op (CommAlgCat.of k R))) := by
  change ModObj G (monoidChartSchemeOver k S)
  exact monoidChartScheme_torusAction k S

theorem invariant_fullCone_Spec_kernel
    (B : CommAlgCat.{u} k) [IsDomain B]
    [ModObj G ((F).obj (op B))]
    (q : R→ₐ[k]B) [IsModHom G ((F).map (CommAlgCat.ofHom q).op)] :
    ∃ I : Finset (Fin n),
      (Spec.map (CommRingCat.ofHom q.toRingHom)).ker=
        (orbitQuotientChartMap k b I s
          (Finset.image_subset_image (Finset.subset_univ I))).ker := by
  obtain ⟨I,hI⟩ := invariant_fullCone_ringKernel k b B q
  exact ⟨I,specMap_kernel_eq_of_ringKernel_eq _ _ hI⟩

/-- Every actual invariant integral closed subscheme of a full smooth
chart is exactly one of its coordinate-face orbit closures. The source
is any integral scheme with an actual group-scheme action; affineness,
the coordinate quotient, and character stability are all derived. -/
theorem invariant_integral_closed_fullChart_kernel
    (Y : Over (Spec (CommRingCat.of k))) [IsIntegral Y.left]
    [ModObj G Y]
    (f : Y⟶monoidChartSchemeOver k S)
    [IsClosedImmersion f.left] [IsModHom G f] :
    ∃ I : Finset (Fin n),f.left.ker=
      (orbitQuotientChartMap k b I s
        (Finset.image_subset_image (Finset.subset_univ I))).ker := by
  letI : IsAffine (monoidChartSchemeOver k S).left := by
    change IsAffine (Spec (CommRingCat.of R))
    infer_instance
  letI : Y.left.Over (Spec (CommRingCat.of k)) := OverClass.fromOver Y
  letI : IsAffine Y.left := (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).1
  let ρ : CommRingCat.of k ⟶ Γ(Y.left,⊤) :=
    (Spec.fullyFaithful.preimage (Y.left.isoSpec.inv ≫ Y.hom)).unop
  letI : Algebra k Γ(Y.left,⊤) := ρ.hom.toAlgebra
  let B : CommAlgCat.{u} k := CommAlgCat.of k Γ(Y.left,⊤)
  have hρ : Spec.map ρ = Y.left.isoSpec.inv ≫ Y.hom :=
    Spec.fullyFaithful.map_preimage (Y.left.isoSpec.inv ≫ Y.hom)
  let e : Y≅(F).obj (op B) := Over.isoMk Y.left.isoSpec (by
    change Y.left.isoSpec.hom ≫ Spec.map ρ = Y.hom
    rw [hρ,Iso.hom_inv_id_assoc])
  letI : IsMonHom (Iso.refl G).hom := by
    change IsMonHom (𝟙 G)
    infer_instance
  letI : ModObj G ((F).obj (op B)) := ModObj.ofIso (Iso.refl G) e
  letI : IsModHom G e.hom := by
    refine ⟨?_⟩
    change γ[G,Y]≫e.hom=
      (G◁e.hom)≫((𝟙 G⊗ₘe.inv)≫γ[G,Y]≫e.hom)
    simp only [id_tensorHom,← Category.assoc,← whiskerLeft_comp,Iso.hom_inv_id,
      whiskerLeft_id,Category.id_comp]
  let f₀ : Y ⟶ (F).obj (op (CommAlgCat.of k R)) := f
  letI : IsModHom G f₀ := inferInstanceAs (IsModHom G f)
  let q : R→ₐ[k]B :=
    ((algSpec.fullyFaithful («R» := CommRingCat.of k)).preimage
      (X := op B) (Y := op (CommAlgCat.of k R)) (e.inv≫f₀)).unop.hom
  have hq : (F).map (CommAlgCat.ofHom q).op=e.inv≫f₀ :=
    (algSpec.fullyFaithful («R» := CommRingCat.of k)).map_preimage (e.inv≫f₀)
  letI : IsModHom G ((F).map (CommAlgCat.ofHom q).op) := by
    rw [hq]
    infer_instance
  obtain ⟨I,hI⟩ := invariant_fullCone_Spec_kernel k b B q
  refine ⟨I,?_⟩
  have hleft := congrArg (fun g=>g.left) hq
  change Spec.map (CommRingCat.ofHom q.toRingHom)=e.inv.left≫f.left at hleft
  let e₀ := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  have hcomp : (e.inv.left ≫ f.left).ker = f.left.ker :=
    Scheme.Hom.ker_comp_of_isIso e₀.inv f.left
  have hker : (Spec.map (CommRingCat.ofHom q.toRingHom)).ker =
      (e.inv.left ≫ f.left).ker :=
    congrArg (fun g : ((F).obj (op B)).left ⟶ (monoidChartSchemeOver k S).left => g.ker) hleft
  exact hcomp.symm.trans (hker.symm.trans hI)

/-- The ideal equality yields an actual local scheme isomorphism over
the original chart, using the universal property of closed immersions. -/
theorem invariant_integral_closed_fullChart_exists_faceIso
    (Y : Over (Spec (CommRingCat.of k))) [IsIntegral Y.left]
    [ModObj G Y]
    (f : Y⟶monoidChartSchemeOver k S)
    [IsClosedImmersion f.left] [IsModHom G f] :
    ∃ I : Finset (Fin n),
      ∃ e : Y.left≅coneChart k (orbitQuotientCone b I s),
        e.hom≫orbitQuotientChartMap k b I s
          (Finset.image_subset_image (Finset.subset_univ I))=f.left := by
  obtain ⟨I,hI⟩ := invariant_integral_closed_fullChart_kernel k b Y f
  let g : coneChart k (orbitQuotientCone b I s) ⟶
      (monoidChartSchemeOver k S).left := orbitQuotientChartMap k b I s
    (Finset.image_subset_image (Finset.subset_univ I))
  letI : IsClosedImmersion g := inferInstanceAs
    (IsClosedImmersion (orbitQuotientChartMap k b I s
      (Finset.image_subset_image (Finset.subset_univ I))))
  letI := IsClosedImmersion.isIso_lift g f.left hI.symm
  exact ⟨I,asIso (IsClosedImmersion.lift g f.left hI.symm.le),
    IsClosedImmersion.lift_fac _ _ _⟩

theorem invariant_integral_closed_fullChart_kernel_of_basis
    (s₀ : Finset (Lattice n)) (hs : s₀=Finset.univ.image b)
    (Y : Over (Spec (CommRingCat.of k))) [IsIntegral Y.left]
    [ModObj G Y]
    (f : Y⟶monoidChartSchemeOver k (dualConeMonoid s₀))
    [IsClosedImmersion f.left] [IsModHom G f] :
    ∃ I : Finset (Fin n),f.left.ker=
      (orbitQuotientChartMap k b I s₀
        (by rw [hs]; exact Finset.image_subset_image (Finset.subset_univ I))).ker := by
  subst s₀
  exact invariant_integral_closed_fullChart_kernel k b Y f

theorem invariant_integral_closed_fullChart_faceIso_of_basis
    (s₀ : Finset (Lattice n)) (hs : s₀=Finset.univ.image b)
    (Y : Over (Spec (CommRingCat.of k))) [IsIntegral Y.left]
    [ModObj G Y]
    (f : Y⟶monoidChartSchemeOver k (dualConeMonoid s₀))
    [IsClosedImmersion f.left] [IsModHom G f] :
    ∃ I : Finset (Fin n),∃ e : Y.left≅coneChart k (orbitQuotientCone b I s₀),
      e.hom≫orbitQuotientChartMap k b I s₀
        (by rw [hs]; exact Finset.image_subset_image (Finset.subset_univ I))=f.left := by
  subst s₀
  exact invariant_integral_closed_fullChart_exists_faceIso k b Y f

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.invariant_integral_closed_fullChart_kernel
end
end
end Source_ToricInvariantChartPrimes

section Source_ToricFanCharacterTranslations



@[expose] public section

/-!
# Character translations of actual fan Cartier sheaves

Changing ray coefficients by the pairing with one integral character
translates every genuine local Cartier point by that character. The
resulting actual sheaf isomorphism is multiplication by the rational
character. Thus the customary lattice translations are proved principal
translations of the actual invertible sheaves.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]
    (hpure : «Σ».IsPure)

theorem cartierLatticePoint_characterTranslation
    (a b : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ v ∈ «Σ».rays,b v=a v-integerPairing v m) (s : «Σ».fullCones) :
    «Σ».cartierLatticePoint b s=«Σ».cartierLatticePoint a s+m := by
  symm
  apply «Σ».eq_cartierLatticePoint_of_pairings
  intro v hv
  rw [integerPairing_add,«Σ».cartierLatticePoint_pairing a s v hv,
    h v («Σ».ray_mem_of_mem_cone («Σ».fullCones_mem s) hv)]
  omega

/-- The character translate is a principal change of the actual
fractional presentation, with an actual isomorphism of its sheaf. -/
theorem fanCartierData_characterTranslation
    (a b : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ v ∈ «Σ».rays,b v=a v-integerPairing v m) :
    («Σ».fanCartierData k hpure a).LinearlyEquivalent
      («Σ».fanCartierData k hpure b) := by
  let C := «Σ».fanCartierCocycle k hpure a
  let E := «Σ».fanCartierCocycle k hpure b
  let q := «Σ».rationalCharacter k m
  have he (i : C.index) : (C.scale q).generator i=E.generator i := by
    change «Σ».rationalCharacter k m *
        «Σ».rationalCharacter k («Σ».cartierLatticePoint a i.down) =
      «Σ».rationalCharacter k («Σ».cartierLatticePoint b i.down)
    rw [«Σ».cartierLatticePoint_characterTranslation a b m h,
      «Σ».rationalCharacter_add k]
    exact mul_comm _ _
  have hCE : (C.scale q).toCartierData.Equivalent E.toCartierData := by
    apply (C.scale q).equivalent_of_generatorRatios E
    · intro i j x hi hj
      rw [he i]
      exact E.transition i j x hi hj
    · intro i j x hi hj
      rw [he j]
      exact E.transition i j x hi hj
  exact ⟨C.scaleSheafIso q ≪≫ hCE.choose⟩

/-- The corresponding polytope is the literal integral translation of
the original halfspace intersection, even without positivity. -/
theorem fanPolytope_characterTranslation
    (a b : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ v ∈ «Σ».rays,b v=a v-integerPairing v m) :
    «Σ».fanPolytope (fun v => (b v : ℝ)) =
      (fun x : Ambient n => x+embed n m) '' «Σ».fanPolytope (fun v => (a v : ℝ)) := by
  ext x
  constructor
  · intro hx
    refine ⟨x-embed n m,?_,sub_add_cancel _ _⟩
    intro v hv
    have hvx := hx v hv
    change -(b v : ℝ) ≤ _ at hvx
    rw [h v hv,Int.cast_sub] at hvx
    rw [map_sub,normalRay_pairing_lattice]
    change -((a v : ℝ)-(integerPairing v m : ℝ)) ≤ _ at hvx
    change -(a v : ℝ) ≤ _
    change -(a v : ℝ) ≤ _-(integerPairing v m : ℝ)
    linarith
  · rintro ⟨y,hy,rfl⟩ v hv
    have hvy := hy v hv
    change -(b v : ℝ) ≤ _
    rw [h v hv,Int.cast_sub,map_add,normalRay_pairing_lattice]
    change -((a v : ℝ)-(integerPairing v m : ℝ)) ≤ _+(integerPairing v m : ℝ)
    linarith

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierData_characterTranslation
end
end
end Source_ToricFanCharacterTranslations

section Source_ToricProjectiveLineTwists



@[expose] public section

/-!
# The usual O(d) characterization of degree on the actual projective line

The divisor `d·∞` is defined by its two actual boundary coefficients. Its
Cartier sheaf is the usual twist O(d). Every fan Cartier presentation is
isomorphic to exactly the twist indexed by the sum of its coefficients.
Together with the arbitrary-Cartier classification, this identifies the
previous curve-degree relation with the intrinsic O(d) characterization
for every actual Cartier sheaf, including negative degrees.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable (k : Type u) [Field k]

def projectiveLineTwistCoefficients (d : ℤ) (v : Lattice 1) : ℤ :=
  if v=projectiveLineRay true then d else 0

def projectiveLineTwist (d : ℤ) : CartierData (projectiveLineScheme k) :=
  projectiveLineCartierData k (projectiveLineTwistCoefficients d)

@[simp] theorem projectiveLineTwistCoefficients_positive (d : ℤ) :
    projectiveLineTwistCoefficients d (projectiveLineRay false)=0 := by
  simp only [projectiveLineTwistCoefficients,projectiveLineRay_ne,if_false]

@[simp] theorem projectiveLineTwistCoefficients_negative (d : ℤ) :
    projectiveLineTwistCoefficients d (projectiveLineRay true)=d := by
  simp only [projectiveLineTwistCoefficients,if_true]

/-- Multiplication by the explicit integral character moves all the
degree to the point at infinity. This is an actual sheaf isomorphism. -/
theorem projectiveLineCartier_linearlyEquivalent_twist (a : Lattice 1 → ℤ) :
    (projectiveLineCartierData k a).LinearlyEquivalent
      (projectiveLineTwist k (a (projectiveLineRay false)+a (projectiveLineRay true))) := by
  apply projectiveLineFan.fanCartierData_characterTranslation k projectiveLineFan_isPure
    a (projectiveLineTwistCoefficients
      (a (projectiveLineRay false)+a (projectiveLineRay true)))
    (fun _ => a (projectiveLineRay false))
  intro v hv
  rw [projectiveLineFan_rays,Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl|rfl
  · simp only [projectiveLineTwistCoefficients_positive,integerPairing,Fin.sum_univ_one,
      projectiveLineRay,Bool.false_eq_true,if_false,one_mul,sub_self]
  · simp only [projectiveLineTwistCoefficients_negative,integerPairing,Fin.sum_univ_one,
      projectiveLineRay,if_true,neg_one_mul,sub_neg_eq_add]
    exact add_comm _ _

/-- This is the usual degree definition by the unique projective-line
twist, now justified for the actual sheaf and both integral signs. -/
theorem projectiveLineHasDegree_iff_twist (M : (projectiveLineScheme k).Modules) (d : ℤ) :
    ProjectiveLineHasDegree k M d ↔ Nonempty (M ≅ (projectiveLineTwist k d).sheaf) := by
  constructor
  · rintro ⟨a,⟨F⟩,ha⟩
    have h := projectiveLineCartier_linearlyEquivalent_twist k a
    rw [ha] at h
    exact ⟨F ≪≫ h.some⟩
  · rintro ⟨F⟩
    refine ⟨projectiveLineTwistCoefficients d,⟨F⟩,?_⟩
    simp only [projectiveLineTwistCoefficients_positive,
      projectiveLineTwistCoefficients_negative,zero_add]

theorem projectiveLineTwists_iso_iff (d e : ℤ) :
    Nonempty ((projectiveLineTwist k d).sheaf ≅ (projectiveLineTwist k e).sheaf) ↔ d=e := by
  constructor
  · rintro ⟨F⟩
    have hd := (projectiveLineHasDegree_iff_twist k (projectiveLineTwist k d).sheaf d).mpr
      ⟨Iso.refl _⟩
    have he := (projectiveLineHasDegree_iff_twist k (projectiveLineTwist k d).sheaf e).mpr ⟨F⟩
    exact projectiveLineHasDegree_unique k hd he
  · rintro rfl
    exact ⟨Iso.refl _⟩

/-- Every actual invertible fractional sheaf is a unique O(d). This is
the full projective-line Picard classification used by the degree bridge. -/
theorem projectiveLineCartier_existsUnique_twist (D : CartierData (projectiveLineScheme k)) :
    ∃! d : ℤ,Nonempty (D.sheaf ≅ (projectiveLineTwist k d).sheaf) := by
  simpa only [projectiveLineHasDegree_iff_twist] using
    projectiveLineCartier_existsUnique_degree k D

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLineHasDegree_iff_twist
#print axioms PaperVerification.ToricGeometry.projectiveLineCartier_existsUnique_twist
end
end
end Source_ToricProjectiveLineTwists

section Source_ToricCartierRationalSections



@[expose] public section

/-! # Actual section membership under dominant pullback -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

namespace RationalCartierCocycle

variable (C : RationalCartierCocycle X)

theorem mem_sectionValueRange_iff_stalkwise (U : X.Opens) [Nonempty U]
    (r : X.functionField) :
    r∈C.toCartierData.sectionValueRange U ↔
      ∀ i (x : X), x∈U → x∈C.openSet i →
        r/(C.generator i : X.functionField)∈regularAtSubring X x := by
  constructor
  · rintro ⟨s,rfl⟩ i x hx hi
    change rationalValue X U s.val / (C.generator i : X.functionField) ∈
      regularAtSubring X x
    exact (congrArg (fun v : X.functionField =>
      v / (C.generator i : X.functionField) ∈ regularAtSubring X x)
        (rationalValueAt_eq X U ⟨x,hx⟩
          (show Γ(rationalFunctions X,U) from s.val))).mp
            (s.property i ⟨x,hx⟩ hi)
  · intro h
    let s := (rationalValue X U).symm r
    have hs : C.IsSection U s := by
      intro i x hi
      simpa only [rationalValueAt_eq,s,AddEquiv.apply_symm_apply] using
        h i x.val x.property hi
    exact ⟨⟨s,hs⟩,(rationalValue X U).apply_symm_apply r⟩

/-- Pullback of an actual section is a section of the genuinely
constructed Cartier pullback; the proof uses actual stalk maps. -/
theorem dominantPullback_mem_sectionValueRange
    (f : Y ⟶ X) [IsDominant f] (U : X.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] (r : X.functionField)
    (hr : r∈C.toCartierData.sectionValueRange U) :
    dominantFunctionFieldMap f r∈
      (C.dominantPullback f).toCartierData.sectionValueRange (f ⁻¹ᵁ U) := by
  apply ((C.dominantPullback f).mem_sectionValueRange_iff_stalkwise
    (f ⁻¹ᵁ U) _).mpr
  intro i y hy hi
  have h := (C.mem_sectionValueRange_iff_stalkwise U r).mp hr i (f y) hy hi
  change dominantFunctionFieldMap f r /
    dominantFunctionFieldMap f (C.generator i : X.functionField) ∈ regularAtSubring Y y
  simpa only [map_div₀] using
    dominantFunctionFieldMap_mem_regularAt f y
      (r/(C.generator i : X.functionField)) h

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X)

theorem mem_sectionValueRange_iff_localStalks (U : X.Opens) [Nonempty U]
    (r : X.functionField) :
    r∈D.sectionValueRange U ↔
      ∀ i (x : X), x∈U → x∈D.localCocycle.openSet i →
        r/(D.localCocycle.generator i : X.functionField)∈regularAtSubring X x := by
  rw [D.equivalent_sectionValueRange D.localCocycle.toCartierData
    D.equivalent_localCocycle U]
  exact D.localCocycle.mem_sectionValueRange_iff_stalkwise U r

theorem dominantPullback_mem_sectionValueRange
    (f : Y ⟶ X) [IsDominant f] (U : X.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] (r : X.functionField)
    (hr : r∈D.sectionValueRange U) :
    dominantFunctionFieldMap f r∈
      (D.dominantPullback f).sectionValueRange (f ⁻¹ᵁ U) := by
  apply D.localCocycle.dominantPullback_mem_sectionValueRange f U r
  rwa [← D.equivalent_sectionValueRange D.localCocycle.toCartierData
    D.equivalent_localCocycle U]

/-- Local affine neighborhoods suffice for the true global-section
condition. Affineness is not an assumption on the covering cocycle. -/
theorem mem_globalSectionValueRange_of_affine_ratios
    (r : X.functionField)
    (h : ∀ i (U : X.Opens) [Nonempty U], IsAffineOpen U →
      U≤D.localCocycle.openSet i →
        r/(D.localCocycle.generator i : X.functionField)∈
          (X.germToFunctionField U).hom.range) :
    r∈D.sectionValueRange ⊤ := by
  apply (D.mem_sectionValueRange_iff_localStalks ⊤ r).mpr
  intro i x hx hi
  obtain ⟨U,hU,hxU,hUi⟩ := exists_isAffineOpen_mem_and_subset hi
  letI : Nonempty U := ⟨⟨x,hxU⟩⟩
  obtain ⟨a,ha⟩ := h i U hU hUi
  rw [← ha]
  exact regular_germ_mem_regularAt X U a x hxU

end CartierData

end PaperVerification.ToricSchemes
end
end
end Source_ToricCartierRationalSections

section Source_ToricCartierSchemeIso



@[expose] public section

/-!
# Actual Cartier sections under a scheme isomorphism

The maps below use the genuine generic-stalk homomorphism. The section
condition is transported in both directions through the genuine maps of
local rings. This gives base-linear equivalences of actual global-section
spaces. Compatibility with addition and multiplication is proved from the
actual rational values, so no section-space identification is assumed.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

@[simp] theorem dominantFunctionFieldMap_id :
    dominantFunctionFieldMap (𝟙 X)=RingHom.id X.functionField := by
  ext r
  have h := congrArg (fun φ : X.functionField →+* X.functionField => φ r)
    (dominantFunctionFieldMap_comp (𝟙 X) (𝟙 X))
  simp only [Category.id_comp,RingHom.comp_apply] at h
  exact (dominantFunctionFieldMap_injective (𝟙 X)) h.symm

@[simp] theorem dominantFunctionFieldMap_iso_hom_inv (e : Y ≅ X)
    (r : X.functionField) :
    dominantFunctionFieldMap e.inv (dominantFunctionFieldMap e.hom r)=r := by
  have h := congrArg (fun φ : X.functionField →+* X.functionField => φ r)
    (dominantFunctionFieldMap_comp e.inv e.hom)
  simpa only [e.inv_hom_id,dominantFunctionFieldMap_id,RingHom.id_apply,
    RingHom.comp_apply] using h.symm

@[simp] theorem dominantFunctionFieldMap_iso_inv_hom (e : Y ≅ X)
    (r : Y.functionField) :
    dominantFunctionFieldMap e.hom (dominantFunctionFieldMap e.inv r)=r :=
  dominantFunctionFieldMap_iso_hom_inv e.symm r

/-- Regularity is transported by the actual local-ring isomorphism. -/
theorem regularAt_schemeIso_iff (e : Y ≅ X) (y : Y) (r : X.functionField) :
    dominantFunctionFieldMap e.hom r ∈ regularAtSubring Y y ↔
      r ∈ regularAtSubring X (e.hom y) := by
  constructor
  · intro h
    have he : e.inv (e.hom y)=y := by
      change (e.hom≫e.inv) y=y
      rw [e.hom_inv_id]
      rfl
    have h' := dominantFunctionFieldMap_mem_regularAt e.inv (e.hom y)
      (dominantFunctionFieldMap e.hom r) (by simpa only [he] using h)
    simpa only [dominantFunctionFieldMap_iso_hom_inv] using h'
  · exact dominantFunctionFieldMap_mem_regularAt e.hom y r

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X) (f : Y ⟶ X) [IsDominant f]

theorem toCartierData_dominantPullback_equivalent :
    (C.toCartierData.dominantPullback f).Equivalent
      (C.dominantPullback f).toCartierData :=
  C.toCartierData.localCocycle.dominantPullback_equivalent_of_equivalent f C
    (C.toCartierData.equivalent_symm C.toCartierData.localCocycle.toCartierData
      C.toCartierData.equivalent_localCocycle)

theorem dominantPullback_mul_equivalent :
    ((C.mul D).dominantPullback f).toCartierData.Equivalent
      ((C.dominantPullback f).mul (D.dominantPullback f)).toCartierData := by
  apply RationalCartierCocycle.equivalent_of_generatorRatios
  · intro i j y hi hj
    have h := ((C.dominantPullback f).mul (D.dominantPullback f)).transition
      i j y hi hj
    change ((dominantFunctionFieldMap f) (C.generator i.1 : X.functionField) *
      (dominantFunctionFieldMap f) (D.generator i.2 : X.functionField)) /
      ((dominantFunctionFieldMap f) (C.generator j.1 : X.functionField) *
      (dominantFunctionFieldMap f) (D.generator j.2 : X.functionField)) ∈
        regularAtSubring Y y at h
    change (dominantFunctionFieldMap f)
      ((C.generator i.1 : X.functionField) * (D.generator i.2 : X.functionField)) /
      ((dominantFunctionFieldMap f) (C.generator j.1 : X.functionField) *
      (dominantFunctionFieldMap f) (D.generator j.2 : X.functionField)) ∈
        regularAtSubring Y y
    simpa only [map_mul] using h
  · intro i j y hi hj
    have h := ((C.dominantPullback f).mul (D.dominantPullback f)).transition
      i j y hi hj
    change ((dominantFunctionFieldMap f) (C.generator i.1 : X.functionField) *
      (dominantFunctionFieldMap f) (D.generator i.2 : X.functionField)) /
      ((dominantFunctionFieldMap f) (C.generator j.1 : X.functionField) *
      (dominantFunctionFieldMap f) (D.generator j.2 : X.functionField)) ∈
        regularAtSubring Y y at h
    change ((dominantFunctionFieldMap f) (C.generator i.1 : X.functionField) *
      (dominantFunctionFieldMap f) (D.generator i.2 : X.functionField)) /
      (dominantFunctionFieldMap f)
      ((C.generator j.1 : X.functionField) * (D.generator j.2 : X.functionField)) ∈
        regularAtSubring Y y
    simpa only [map_mul] using h

end RationalCartierCocycle

namespace CartierData

variable (D E : CartierData X)

theorem dominantPullback_add_equivalent (f : Y ⟶ X) [IsDominant f] :
    ((D.add E).dominantPullback f).Equivalent
      ((D.dominantPullback f).add (E.dominantPullback f)) := by
  let C := D.localCocycle
  let F := E.localCocycle
  have h₁ := (C.mul F).toCartierData_dominantPullback_equivalent f
  have h₂ := C.dominantPullback_mul_equivalent F f
  have h₃ := (C.dominantPullback f).toCartierData_add_equivalent
    (F.dominantPullback f)
  exact ((D.add E).dominantPullback f).equivalent_trans
    ((C.mul F).dominantPullback f).toCartierData _ h₁
    (((C.mul F).dominantPullback f).toCartierData.equivalent_trans
      ((C.dominantPullback f).mul (F.dominantPullback f)).toCartierData _ h₂
      (((D.dominantPullback f).add (E.dominantPullback f)).equivalent_symm _ h₃))

/-- Every global section is detected in both directions, not merely
injected into the pullback section space. -/
theorem globalSectionRange_schemeIso_iff (e : Y ≅ X) (r : X.functionField) :
    dominantFunctionFieldMap e.hom r ∈ (D.dominantPullback e.hom).sectionValueRange ⊤ ↔
      r ∈ D.sectionValueRange ⊤ := by
  constructor
  · intro h
    apply (D.mem_sectionValueRange_iff_localStalks ⊤ r).mpr
    intro i x hx hi
    have hex : e.hom (e.inv x)=x := by
      change (e.inv≫e.hom) x=x
      rw [e.inv_hom_id]
      rfl
    have h' := ((D.localCocycle.dominantPullback e.hom).mem_sectionValueRange_iff_stalkwise
      ⊤ _).mp h i (e.inv x) trivial
        (by
          change e.hom (e.inv x) ∈ D.localCocycle.openSet i
          rw [hex]
          exact hi)
    change dominantFunctionFieldMap e.hom r /
      dominantFunctionFieldMap e.hom (D.localCocycle.generator i : X.functionField) ∈
        regularAtSubring Y (e.inv x) at h'
    rw [← map_div₀,regularAt_schemeIso_iff,hex] at h'
    exact h'
  · intro h
    apply ((D.localCocycle.dominantPullback e.hom).mem_sectionValueRange_iff_stalkwise
      ⊤ _).mpr
    intro i y _ hi
    change e.hom y ∈ D.localCocycle.openSet i at hi
    have h' := (D.mem_sectionValueRange_iff_localStalks ⊤ r).mp h
      i (e.hom y) trivial hi
    change dominantFunctionFieldMap e.hom r /
      dominantFunctionFieldMap e.hom (D.localCocycle.generator i : X.functionField) ∈
        regularAtSubring Y y
    rw [← map_div₀,regularAt_schemeIso_iff]
    exact h'

end CartierData

open scoped BaseSections

variable (k : Type u) [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (e : Y ≅ X) [e.hom.IsOver (Spec (CommRingCat.of k))]

def schemeIsoFunctionFieldAlgEquiv : X.functionField ≃ₐ[k] Y.functionField where
  __ := openImmersionFunctionFieldEquiv e.hom
  commutes' := (BaseSections.dominantFunctionFieldAlgHom k e.hom).commutes

@[simp] theorem schemeIsoFunctionFieldAlgEquiv_apply (r : X.functionField) :
    schemeIsoFunctionFieldAlgEquiv k e r=dominantFunctionFieldMap e.hom r := rfl

namespace CartierData

variable (D E : CartierData X)

theorem globalSectionValue_map_schemeIso :
    ((D.globalSectionValue k).range).map
      (schemeIsoFunctionFieldAlgEquiv k e).toLinearEquiv.toLinearMap =
        ((D.dominantPullback e.hom).globalSectionValue k).range := by
  ext r
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (D.globalSectionRange_schemeIso_iff e z).mpr hz
  · intro hr
    obtain ⟨z,rfl⟩ := (schemeIsoFunctionFieldAlgEquiv k e).surjective r
    exact ⟨z,(D.globalSectionRange_schemeIso_iff e z).mp hr,rfl⟩

/-- The actual global-section equivalence over the original base field. -/
def schemeIsoGlobalSections :
    Γ(D.sheaf,⊤) ≃ₗ[k] Γ((D.dominantPullback e.hom).sheaf,⊤) :=
  (LinearEquiv.ofInjective (D.globalSectionValue k) (D.globalSectionValue_injective k)).trans
    (((schemeIsoFunctionFieldAlgEquiv k e).toLinearEquiv.ofSubmodules
      (D.globalSectionValue k).range ((D.dominantPullback e.hom).globalSectionValue k).range
      (D.globalSectionValue_map_schemeIso k e)).trans
        (LinearEquiv.ofInjective ((D.dominantPullback e.hom).globalSectionValue k)
          ((D.dominantPullback e.hom).globalSectionValue_injective k)).symm)

theorem schemeIsoGlobalSections_value (s : Γ(D.sheaf,⊤)) :
    (D.dominantPullback e.hom).globalSectionValue k (D.schemeIsoGlobalSections k e s) =
      dominantFunctionFieldMap e.hom (D.globalSectionValue k s) := by
  change (D.dominantPullback e.hom).globalSectionValue k
    ((LinearEquiv.ofInjective ((D.dominantPullback e.hom).globalSectionValue k)
      ((D.dominantPullback e.hom).globalSectionValue_injective k)).symm _) = _
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective ((D.dominantPullback e.hom).globalSectionValue k)
      ((D.dominantPullback e.hom).globalSectionValue_injective k)).apply_symm_apply _)

def schemeIsoSumGlobalSections :
    Γ((D.add E).sheaf,⊤) ≃ₗ[k]
      Γ(((D.dominantPullback e.hom).add (E.dominantPullback e.hom)).sheaf,⊤) :=
  ((D.add E).schemeIsoGlobalSections k e).trans
    (((D.add E).dominantPullback e.hom).equivalentGlobalSections k _
      (D.dominantPullback_add_equivalent E e.hom))

theorem schemeIsoSumGlobalSections_value (s : Γ((D.add E).sheaf,⊤)) :
    ((D.dominantPullback e.hom).add (E.dominantPullback e.hom)).globalSectionValue k
        (D.schemeIsoSumGlobalSections k e E s) =
      dominantFunctionFieldMap e.hom ((D.add E).globalSectionValue k s) := by
  rw [schemeIsoSumGlobalSections,LinearEquiv.trans_apply,
    equivalentGlobalSections_value,schemeIsoGlobalSections_value]

theorem sectionMultiplicationOver_schemeIso :
    (D.schemeIsoSumGlobalSections k e E).toLinearMap.comp
      (D.sectionMultiplicationOver k E) =
    ((D.dominantPullback e.hom).sectionMultiplicationOver k (E.dominantPullback e.hom)).comp
      (TensorProduct.map (D.schemeIsoGlobalSections k e).toLinearMap
        (E.schemeIsoGlobalSections k e).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  apply ((D.dominantPullback e.hom).add (E.dominantPullback e.hom)).globalSectionValue_injective k
  change ((D.dominantPullback e.hom).add (E.dominantPullback e.hom)).globalSectionValue k
    (D.schemeIsoSumGlobalSections k e E (D.sectionMultiplicationOver k E (s⊗ₜ[k]t))) =
    ((D.dominantPullback e.hom).add (E.dominantPullback e.hom)).globalSectionValue k
      ((D.dominantPullback e.hom).sectionMultiplicationOver k (E.dominantPullback e.hom)
        (D.schemeIsoGlobalSections k e s⊗ₜ[k]E.schemeIsoGlobalSections k e t))
  rw [schemeIsoSumGlobalSections_value,sectionMultiplicationOver_value_tmul,
    sectionMultiplicationOver_value_tmul,map_mul,schemeIsoGlobalSections_value,
    schemeIsoGlobalSections_value]

/-- Actual section multiplication is surjective before transport exactly
when it is surjective after transport through a genuine k-scheme isomorphism. -/
theorem sectionMultiplicationOver_surjective_iff_schemeIso :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      Function.Surjective ((D.dominantPullback e.hom).sectionMultiplicationOver k
        (E.dominantPullback e.hom)) := by
  let es := TensorProduct.congr (D.schemeIsoGlobalSections k e) (E.schemeIsoGlobalSections k e)
  let et := D.schemeIsoSumGlobalSections k e E
  have he (z) : et (D.sectionMultiplicationOver k E z)=
      (D.dominantPullback e.hom).sectionMultiplicationOver k (E.dominantPullback e.hom) (es z) :=
    congrArg (fun φ=>φ z) (D.sectionMultiplicationOver_schemeIso k e E)
  constructor
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨es z,(he z).symm.trans (by rw [hz,ht])⟩
  · intro h t
    obtain ⟨y,hy⟩ := h (et t)
    obtain ⟨z,hz⟩ := es.surjective y
    exact ⟨z,et.injective (by rw [he,hz,hy])⟩

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.schemeIsoGlobalSections
#print axioms PaperVerification.ToricSchemes.CartierData.sectionMultiplicationOver_surjective_iff_schemeIso
end
end
end Source_ToricCartierSchemeIso

section Source_ToricProjectiveLineDegreeInvariant



@[expose] public section

/-!
# Degree is independent of a projective-line coordinate

The actual global sections of O(d) have dimension max(d+1,0), proved by
the actual character-coordinate equivalence and a finite interval count.
The dimension determines all nonnegative degrees. For negative degrees,
tensoring with the opposite twist reduces to degree zero. Consequently
every actual k-scheme automorphism preserves the degree of every Cartier
sheaf. No invariance of principal-divisor degrees is assumed.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical BaseSections

theorem projectiveLineTwist_exponents (d : ℤ) (m : Lattice 1) :
    m ∈ projectiveLineFan.fanIntegralExponents (projectiveLineTwistCoefficients d) ↔
      0 ≤ m 0 ∧ m 0 ≤ d := by
  change (∀ v ∈ projectiveLineFan.rays,
    -(projectiveLineTwistCoefficients d v : ℝ) ≤
      (dotProductEquiv ℝ (Fin 1) (embed 1 v)) (embed 1 m)) ↔ _
  rw [projectiveLineFan_rays]
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,
    forall_eq,projectiveLineTwistCoefficients_positive,
    projectiveLineTwistCoefficients_negative]
  rw [SmoothCompleteFan.normalRay_pairing_lattice,
    SmoothCompleteFan.normalRay_pairing_lattice]
  simp only [Fin.sum_univ_one,projectiveLineRay,Bool.false_eq_true,if_false,
    if_true,one_mul,neg_one_mul,Int.cast_neg,neg_zero,neg_le_neg_iff]
  exact_mod_cast (Iff.rfl : (0 ≤ m 0 ∧ m 0 ≤ d) ↔ (0 ≤ m 0 ∧ m 0 ≤ d))

/-- The actual allowed character set is a finite integer interval, with
the empty interval retained for every degree below zero. -/
def projectiveLineTwistExponentEquiv (d : ℤ) :
    projectiveLineFan.fanIntegralExponents (projectiveLineTwistCoefficients d) ≃
      Fin (d+1).toNat where
  toFun m := ⟨(m.val 0).toNat,by
    have hm := (projectiveLineTwist_exponents d m.val).mp m.property
    omega⟩
  invFun i := ⟨fun _ => (i.val : ℤ),by
    apply (projectiveLineTwist_exponents d _).mpr
    have hi := i.isLt
    constructor <;> omega⟩
  left_inv m := by
    apply Subtype.ext
    funext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    have hm := (projectiveLineTwist_exponents d m.val).mp m.property
    simp only [hi]
    exact Int.toNat_of_nonneg hm.1
  right_inv i := by
    apply Fin.ext
    simp only [Int.toNat_natCast]

variable (k : Type u) [Field k]

def projectiveLineTwistSectionCoordinates (d : ℤ) :
    Γ((projectiveLineTwist k d).sheaf,⊤) ≃ₗ[k] (Fin (d+1).toNat →₀ k) :=
  (projectiveLineFan.fanCartierSectionCoordinates k projectiveLineFan_isPure
    (projectiveLineTwistCoefficients d)).trans
      ((AddMonoidAlgebra.supportedEquivFinsupp (R:=k) (S:=k) _).trans
        (Finsupp.domLCongr (projectiveLineTwistExponentEquiv d)))

theorem projectiveLineTwist_finrank (d : ℤ) :
    Module.finrank k Γ((projectiveLineTwist k d).sheaf,⊤)=(d+1).toNat := by
  rw [(projectiveLineTwistSectionCoordinates k d).finrank_eq,
    Module.finrank_finsupp_self,Fintype.card_fin]

theorem projectiveLineHasDegree_finrank
    {M : (projectiveLineScheme k).Modules} {d : ℤ} (h : ProjectiveLineHasDegree k M d) :
    Module.finrank k Γ(M,⊤)=(d+1).toNat := by
  obtain ⟨F⟩ := (projectiveLineHasDegree_iff_twist k M d).mp h
  exact (BaseSections.globalSectionsIso k F).finrank_eq.trans
    (projectiveLineTwist_finrank k d)

theorem projectiveLineHasDegree_add
    (D E : CartierData (projectiveLineScheme k)) {d e : ℤ}
    (hD : ProjectiveLineHasDegree k D.sheaf d)
    (hE : ProjectiveLineHasDegree k E.sheaf e) :
    ProjectiveLineHasDegree k (D.add E).sheaf (d+e) := by
  obtain ⟨F⟩ := (projectiveLineHasDegree_iff_twist k D.sheaf d).mp hD
  obtain ⟨G⟩ := (projectiveLineHasDegree_iff_twist k E.sheaf e).mp hE
  let a := projectiveLineTwistCoefficients d
  let b := projectiveLineTwistCoefficients e
  let J : (D.add E).sheaf ≅ (projectiveLineCartierData k (a+b)).sheaf :=
    D.addSheafIso (projectiveLineTwist k d) E (projectiveLineTwist k e) F G ≪≫
      (projectiveLineFan.fanCartierData_add_equivalent k projectiveLineFan_isPure a b).choose
  refine ⟨a+b,⟨J⟩,?_⟩
  simp only [a,b,Pi.add_apply,projectiveLineTwistCoefficients_positive,
    projectiveLineTwistCoefficients_negative,zero_add]

variable (e : projectiveLineScheme k ≅ projectiveLineScheme k)
    [e.hom.IsOver (Spec (CommRingCat.of k))]

/-- Preservation in nonnegative degree follows from the dimension of the
actual global-section vector space under the actual scheme isomorphism. -/
theorem projectiveLineHasDegree_pullback_of_nonneg
    (D : CartierData (projectiveLineScheme k)) {d : ℤ}
    (hd : 0≤d) (hD : ProjectiveLineHasDegree k D.sheaf d) :
    ProjectiveLineHasDegree k (D.dominantPullback e.hom).sheaf d := by
  obtain ⟨r,hr,_⟩ := projectiveLineCartier_existsUnique_degree k (D.dominantPullback e.hom)
  have hdim : (d+1).toNat=(r+1).toNat :=
    (projectiveLineHasDegree_finrank k hD).symm.trans
      ((D.schemeIsoGlobalSections k e).finrank_eq.trans
        (projectiveLineHasDegree_finrank k hr))
  have hrd : r=d := by omega
  simpa only [hrd] using hr

/-- Every integral degree, including negative degree, is preserved by an
arbitrary actual k-scheme automorphism of the projective line. -/
theorem projectiveLineHasDegree_pullback
    (D : CartierData (projectiveLineScheme k)) {d : ℤ}
    (hD : ProjectiveLineHasDegree k D.sheaf d) :
    ProjectiveLineHasDegree k (D.dominantPullback e.hom).sheaf d := by
  by_cases hd : 0≤d
  · exact projectiveLineHasDegree_pullback_of_nonneg k e D hd hD
  · obtain ⟨r,hr,_⟩ := projectiveLineCartier_existsUnique_degree k (D.dominantPullback e.hom)
    let E := projectiveLineTwist k (-d)
    have hE : ProjectiveLineHasDegree k E.sheaf (-d) :=
      (projectiveLineHasDegree_iff_twist k E.sheaf (-d)).mpr ⟨Iso.refl _⟩
    have hDE : ProjectiveLineHasDegree k (D.add E).sheaf 0 := by
      simpa only [add_neg_cancel] using projectiveLineHasDegree_add k D E hD hE
    have hE' : ProjectiveLineHasDegree k (E.dominantPullback e.hom).sheaf (-d) :=
      projectiveLineHasDegree_pullback_of_nonneg k e E (by omega) hE
    have hDE' : ProjectiveLineHasDegree k ((D.add E).dominantPullback e.hom).sheaf 0 :=
      projectiveLineHasDegree_pullback_of_nonneg k e (D.add E) (by omega) hDE
    have hsum : ProjectiveLineHasDegree k
        ((D.dominantPullback e.hom).add (E.dominantPullback e.hom)).sheaf 0 :=
      (projectiveLineHasDegree_iso k
        (D.dominantPullback_add_equivalent E e.hom).choose 0).mp hDE'
    have hnum := projectiveLineHasDegree_unique k
      (projectiveLineHasDegree_add k (D.dominantPullback e.hom)
        (E.dominantPullback e.hom) hr hE') hsum
    have hrd : r=d := by omega
    simpa only [hrd] using hr

/-- The same invariance for Mathlib's actual module-sheaf pullback,
without referring to a fractional embedding in its conclusion. -/
theorem projectiveLineHasDegree_pullbackSheaf
    (D : CartierData (projectiveLineScheme k)) {d : ℤ}
    (hD : ProjectiveLineHasDegree k D.sheaf d) :
    ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.hom).obj D.sheaf) d :=
  (projectiveLineHasDegree_iso k (D.dominantPullbackSheafIso e.hom) d).mpr
    (projectiveLineHasDegree_pullback k e D hD)

/-- The embedding in rational functions is unnecessary: a degree
certificate itself gives an actual twist presentation of the module sheaf. -/
theorem projectiveLineHasDegree_pullbackModule
    {M : (projectiveLineScheme k).Modules} {d : ℤ}
    (hM : ProjectiveLineHasDegree k M d) :
    ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.hom).obj M) d := by
  obtain ⟨F⟩ := (projectiveLineHasDegree_iff_twist k M d).mp hM
  apply (projectiveLineHasDegree_iso k
    ((Scheme.Modules.pullback e.hom).mapIso F) d).mpr
  apply projectiveLineHasDegree_pullbackSheaf k e (projectiveLineTwist k d)
  exact (projectiveLineHasDegree_iff_twist k _ d).mpr ⟨Iso.refl _⟩

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLineTwist_finrank
#print axioms PaperVerification.ToricGeometry.projectiveLineHasDegree_pullbackSheaf
end
end
end Source_ToricProjectiveLineDegreeInvariant

section Source_ToricRationalCurveDegree



@[expose] public section

/-!
# Intrinsic degree on a curve isomorphic to the projective line

Degree uses an actual isomorphism over the original field and the actual
pullback of the line bundle. The preceding automorphism theorem proves
that it is independent of this isomorphism. The wall-curve degree used in
the polytope comparison is then a special case of this intrinsic relation.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical

variable (k : Type u) [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]

/-- The usual degree of a line bundle on an actual rational smooth
projective curve, with a genuine k-scheme isomorphism as its witness. -/
def RationalCurveHasDegree (M : C.Modules) (d : ℤ) : Prop :=
  ∃ e : C ≅ projectiveLineScheme k,
    e.hom.IsOver (Spec (CommRingCat.of k)) ∧
    ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.inv).obj M) d

theorem projectiveLineDegree_coordinate_independent
    (M : C.Modules) (e f : C ≅ projectiveLineScheme k)
    [e.hom.IsOver (Spec (CommRingCat.of k))]
    [f.hom.IsOver (Spec (CommRingCat.of k))] {d : ℤ}
    (h : ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.inv).obj M) d) :
    ProjectiveLineHasDegree k ((Scheme.Modules.pullback f.inv).obj M) d := by
  let g : projectiveLineScheme k ≅ projectiveLineScheme k := f.symm.trans e
  letI : Scheme.Hom.IsOver g.hom (Spec (CommRingCat.of k)) := by
    change Scheme.Hom.IsOver (f.inv ≫ e.hom) (Spec (CommRingCat.of k))
    infer_instance
  have hg : g.hom≫e.inv=f.inv := by
    change (f.inv≫e.hom)≫e.inv=f.inv
    simp only [Category.assoc,e.hom_inv_id,Category.comp_id]
  let J : (Scheme.Modules.pullback g.hom).obj
      ((Scheme.Modules.pullback e.inv).obj M) ≅
        (Scheme.Modules.pullback f.inv).obj M :=
    (Scheme.Modules.pullbackComp g.hom e.inv).app M ≪≫
      (Scheme.Modules.pullbackCongr hg).app M
  exact (projectiveLineHasDegree_iso k J d).mp
    (projectiveLineHasDegree_pullbackModule k g h)

/-- Any actual k-isomorphism with the projective line computes the same
integer, so the existential choice in the definition carries no ambiguity. -/
theorem rationalCurveHasDegree_iff
    (M : C.Modules) (e : C ≅ projectiveLineScheme k)
    [e.hom.IsOver (Spec (CommRingCat.of k))] (d : ℤ) :
    RationalCurveHasDegree k M d ↔
      ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.inv).obj M) d := by
  constructor
  · rintro ⟨f,hf,hd⟩
    letI := hf
    exact projectiveLineDegree_coordinate_independent k M f e hd
  · intro hd
    exact ⟨e,inferInstance,hd⟩

theorem rationalCurveHasDegree_unique {M : C.Modules} {d e : ℤ}
    (hd : RationalCurveHasDegree k M d) (he : RationalCurveHasDegree k M e) : d=e := by
  obtain ⟨f,hf,hfd⟩ := hd
  letI := hf
  exact projectiveLineHasDegree_unique k hfd
    ((rationalCurveHasDegree_iff k M f e).mp he)

theorem rationalCurveHasDegree_iso {M N : C.Modules} (F : M ≅ N) (d : ℤ) :
    RationalCurveHasDegree k M d ↔ RationalCurveHasDegree k N d := by
  constructor
  · rintro ⟨e,he,hd⟩
    exact ⟨e,he,(projectiveLineHasDegree_iso k
      ((Scheme.Modules.pullback e.inv).mapIso F) d).mp hd⟩
  · rintro ⟨e,he,hd⟩
    exact ⟨e,he,(projectiveLineHasDegree_iso k
      ((Scheme.Modules.pullback e.inv).mapIso F) d).mpr hd⟩

namespace SmoothCompleteFan

variable {d : ℕ} (Γ : SmoothCompleteFan d) (hd : d=1)

instance oneDimensionalFanSchemeIso_isOver :
    (oneDimensionalFanSchemeIso Γ hd k).hom.IsOver (Spec (CommRingCat.of k)) := by
  subst d
  have hΓ := Γ.rankOne_eq_projectiveLine
  subst Γ
  change Scheme.Hom.IsOver (𝟙 (projectiveLineScheme k)) (Spec (CommRingCat.of k))
  infer_instance

theorem oneDimensionalHasDegree_iff_rationalCurve (M : (Γ.fanScheme k).Modules) (r : ℤ) :
    Γ.OneDimensionalHasDegree hd k M r ↔ RationalCurveHasDegree k M r :=
  (rationalCurveHasDegree_iff k M (oneDimensionalFanSchemeIso Γ hd k) r).symm

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem wallCurve_hasDegree (hpure : «Σ».IsPure)
    (s : «Σ».fullCones) (j : Fin n) (D : CartierData («Σ».fanScheme k))
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hw : («Σ».fullConeBasis s).repr w j = -1) :
    RationalCurveHasDegree k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).obj D.sheaf)
      («Σ».integerWallSlack («Σ».cartierCoefficients k hpure D) s w) :=
  ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iff_rationalCurve k
    («Σ».wallIndices_codimension s j) _ _).mp
      («Σ».wallCurve_cartier_hasDegree s j k hpure D t w ht hw)

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.rationalCurveHasDegree_unique
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_hasDegree
end
end
end Source_ToricRationalCurveDegree

section Source_ToricInvariantCurveBounds



@[expose] public section

/-!
# Actual invariant integral curves and their degree bounds

An invariant curve is an actual integral scheme of ordinary Krull
dimension one, with a closed immersion and a genuine group-scheme action
making that immersion equivariant. The curve itself is not defined by a
fan wall. Bounds on these actual curves imply the wall bounds used in the
polytope proof, and transport through actual equivariant scheme isomorphisms.

The degree relation is the coordinate-independent O(d) degree on rational
smooth projective curves. The classification and degree-existence theorem
for all invariant curves is a separate obligation in the intrinsic dictionary.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry
open scoped Classical

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]

/-- A genuine invariant integral curve, including its scheme structure
and its action on arbitrary test schemes. -/
structure InvariantIntegralCurve where
  curve : Over (Spec (CommRingCat.of k))
  integral : IsIntegral curve.left
  action : ModObj (splitTorusOver k (Fin n→ℤ)) curve
  inclusion : curve ⟶ X
  closed : IsClosedImmersion inclusion.left
  dimension : topologicalKrullDim curve.left=1
  equivariant : letI := action
    IsModHom (splitTorusOver k (Fin n→ℤ)) inclusion

attribute [instance] InvariantIntegralCurve.integral InvariantIntegralCurve.action
  InvariantIntegralCurve.closed InvariantIntegralCurve.equivariant

variable [IsIntegral X.left]

/-- Degree bounds on the actual restricted line bundles. No wall, edge,
coefficient function, or polytope appears in this condition. -/
def InvariantCurveDegreesAtLeast (D : CartierData X.left) (bound : ℕ) : Prop :=
  ∀ C : InvariantIntegralCurve k n X, ∀ d : ℤ,
    RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj D.sheaf) d → (bound : ℤ)≤d

theorem invariantCurveDegreesAtLeast_sheafIso
    (D E : CartierData X.left) (F : D.sheaf ≅ E.sheaf) (bound : ℕ) :
    InvariantCurveDegreesAtLeast k n X D bound ↔
      InvariantCurveDegreesAtLeast k n X E bound := by
  constructor
  · intro h C d hd
    apply h C d
    exact (rationalCurveHasDegree_iso k
      ((Scheme.Modules.pullback C.inclusion.left).mapIso F) d).mpr hd
  · intro h C d hd
    apply h C d
    exact (rationalCurveHasDegree_iso k
      ((Scheme.Modules.pullback C.inclusion.left).mapIso F) d).mp hd

namespace InvariantIntegralCurve

variable {k n X} {Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) Y]
    (e : X ≅ Y) [IsModHom (splitTorusOver k (Fin n→ℤ)) e.hom]

/-- Composition with an actual equivariant isomorphism transports the
whole curve, rather than only its set of points. -/
def mapIso (C : InvariantIntegralCurve k n X) : InvariantIntegralCurve k n Y where
  curve := C.curve
  integral := C.integral
  action := C.action
  inclusion := C.inclusion≫e.hom
  closed := by
    change IsClosedImmersion (C.inclusion.left≫e.hom.left)
    infer_instance
  dimension := C.dimension
  equivariant := by
    letI := C.action
    infer_instance

variable [IsIntegral Y.left]

def restrictionPullbackIso (C : InvariantIntegralCurve k n X) (D : CartierData Y.left) :
    (Scheme.Modules.pullback C.inclusion.left).obj (D.dominantPullback e.hom.left).sheaf ≅
      (Scheme.Modules.pullback (C.mapIso e).inclusion.left).obj D.sheaf :=
  (Scheme.Modules.pullback C.inclusion.left).mapIso
      (D.dominantPullbackSheafIso e.hom.left).symm ≪≫
    (Scheme.Modules.pullbackComp C.inclusion.left e.hom.left).app D.sheaf

end InvariantIntegralCurve

variable {k n X} {Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) Y] [IsIntegral Y.left]

/-- The actual geometric degree hypothesis pulls back along a genuine
equivariant k-scheme isomorphism. -/
theorem invariantCurveDegreesAtLeast_pullbackIso (e : X ≅ Y)
    [IsModHom (splitTorusOver k (Fin n→ℤ)) e.hom]
    (D : CartierData Y.left) (bound : ℕ)
    (hD : InvariantCurveDegreesAtLeast k n Y D bound) :
    InvariantCurveDegreesAtLeast k n X (D.dominantPullback e.hom.left) bound := by
  intro C d hd
  apply hD (C.mapIso e) d
  exact (rationalCurveHasDegree_iso k (C.restrictionPullbackIso e D) d).mp hd

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

local instance : IsIntegral («Σ».fanSchemeOver k).left := by
  change IsIntegral («Σ».fanScheme k)
  infer_instance

/-- A fan wall supplies a genuine instance of the intrinsic curve type. -/
def wallInvariantCurve (s : «Σ».fullCones) (j : Fin n) :
    InvariantIntegralCurve k n («Σ».fanSchemeOver k) where
  curve := («Σ».wallCurveFan s j).fanSchemeOver k
  integral := by
    change IsIntegral («Σ».wallCurve s j k)
    exact «Σ».wallCurve_isIntegral s j k
  action := «Σ».orbitClosureSourceAction k («Σ».fullConeBasis s)
    («Σ».wallIndices s j) («Σ».wallCone_mem s j)
  inclusion := («Σ».wallCurveInclusion s j k).asOver (Spec (CommRingCat.of k))
  closed := by
    change IsClosedImmersion («Σ».wallCurveInclusion s j k)
    exact «Σ».wallCurveInclusion_isClosedImmersion s j k
  dimension := «Σ».wallCurve_dimension s j k
  equivariant := «Σ».wallCurve_equivariant s j k

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end
end Source_ToricInvariantCurveBounds

section Source_ToricMonomialImageComparison

@[expose] public section
noncomputable section
universe u
namespace PaperVerification.ToricSchemes
open AlgebraicGeometry CategoryTheory
theorem closedImmersion_ker_eq_of_dense_composite
    {T X Y Z : Scheme.{u}} (j : T⟶X) (q : T⟶Y)
    (f : X⟶Z) (g : Y⟶Z)
    [IsSchemeTheoreticallyDominant j] [IsSchemeTheoreticallyDominant q]
    (h : j≫f=q≫g) : f.ker=g.ker := by
  have H := congrArg Scheme.Hom.ker h
  simpa only [Scheme.Hom.ker_comp,Scheme.Hom.ker_eq_bot,
    Scheme.IdealSheafData.map_bot] using H

def closedImageIsoOfDenseComposite
    {T X Y Z : Scheme.{u}} (j : T⟶X) (q : T⟶Y)
    (f : X⟶Z) (g : Y⟶Z)
    [IsSchemeTheoreticallyDominant j] [IsSchemeTheoreticallyDominant q]
    [IsClosedImmersion f] [IsClosedImmersion g]
    (h : j≫f=q≫g) : X≅Y := by
  let H := (closedImmersion_ker_eq_of_dense_composite j q f g h).symm
  letI := IsClosedImmersion.isIso_lift g f H
  exact asIso (IsClosedImmersion.lift g f H.le)

@[reassoc (attr := simp)] theorem closedImageIsoOfDenseComposite_embedding
    {T X Y Z : Scheme.{u}} (j : T⟶X) (q : T⟶Y)
    (f : X⟶Z) (g : Y⟶Z)
    [IsSchemeTheoreticallyDominant j] [IsSchemeTheoreticallyDominant q]
    [IsClosedImmersion f] [IsClosedImmersion g] (h : j≫f=q≫g) :
    (closedImageIsoOfDenseComposite j q f g h).hom≫g=f := by
  exact IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)] theorem closedImageIsoOfDenseComposite_torus
    {T X Y Z : Scheme.{u}} (j : T⟶X) (q : T⟶Y)
    (f : X⟶Z) (g : Y⟶Z)
    [IsSchemeTheoreticallyDominant j] [IsSchemeTheoreticallyDominant q]
    [IsClosedImmersion f] [IsClosedImmersion g] (h : j≫f=q≫g) :
    j≫(closedImageIsoOfDenseComposite j q f g h).hom=q := by
  apply (cancel_mono g).mp
  rw [Category.assoc,closedImageIsoOfDenseComposite_embedding]
  exact h

end PaperVerification.ToricSchemes
end
end
end Source_ToricMonomialImageComparison

section Source_ToricInvariantOrbitClosure



@[expose] public section

/-!
# Actual invariant integral curves are orbit closures

An invariant integral closed subscheme meets a full affine chart.  Its
actual equivariant pullback has a prime monomial kernel, which is the
coordinate-face kernel.  This gives a common dense open subscheme with
the quotient-star orbit closure.  Equality of the two actual closed
immersion kernels then identifies the whole schemes.  Ordinary Krull
dimension, rather than a prescribed fan rank, forces the quotient fan
of a curve to have rank one.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

/-- The orbit-closure classification is derived from the actual action
on an arbitrary integral closed subscheme.  In particular the curve
need not be presented by an orbit or a fan wall. -/
theorem invariantIntegralCurve_isOrbitClosure_fullCone (hpure : «Σ».IsPure)
    (C : InvariantIntegralCurve k n («Σ».fanSchemeOver k)) :
    ∃ (s : «Σ».fullCones) (I : Finset (Fin n))
      (hF : I.image («Σ».fullConeBasis s) ∈ «Σ».cones),
      ∃ e : C.curve ≅ («Σ».completeQuotientStarFan («Σ».fullConeBasis s) I hF).fanSchemeOver k,
        e.hom.left ≫ «Σ».orbitClosureMap k («Σ».fullConeBasis s) I hF = C.inclusion.left := by
  let G := splitTorusOver k (Lattice n)
  obtain ⟨s, hs⟩ := «Σ».fullChartOpen_cover k hpure
    (C.inclusion.left (genericPoint C.curve.left))
  let j : (coneChart k s.val).asOver (Spec (CommRingCat.of k)) ⟶ «Σ».fanSchemeOver k :=
    («Σ».fanChartMap k («Σ».fullConeIndex s)).asOver (Spec (CommRingCat.of k))
  letI : IsOpenImmersion j.left := by
    change IsOpenImmersion («Σ».fanChartMap k («Σ».fullConeIndex s))
    infer_instance
  letI : IsModHom G j := «Σ».fanChartMap_isModHom k («Σ».fullConeIndex s)
  let Y := pullback j C.inclusion
  let p : Y ⟶ (coneChart k s.val).asOver (Spec (CommRingCat.of k)) :=
    pullback.fst j C.inclusion
  let q : Y ⟶ C.curve := pullback.snd j C.inclusion
  letI : ModObj G Y := equivariantPullbackModObj G j C.inclusion
  letI : IsModHom G p := equivariantPullback_fst_isModHom G j C.inclusion
  letI : IsModHom G q := equivariantPullback_snd_isModHom G j C.inclusion
  letI : IsClosedImmersion p.left := overPullback_fst_isClosedImmersion j C.inclusion
  letI : IsOpenImmersion q.left := overPullback_snd_isOpenImmersion j C.inclusion
  letI : Nonempty Y.left := overPullback_nonempty j C.inclusion
    (genericPoint C.curve.left) hs
  letI : IsIntegral Y.left := isIntegral_of_isOpenImmersion q.left
  let b := «Σ».fullConeBasis s
  let p₀ : Y ⟶ monoidChartSchemeOver k (dualConeMonoid s.val) := p
  letI : IsClosedImmersion p₀.left := inferInstanceAs (IsClosedImmersion p.left)
  letI : IsModHom G p₀ := inferInstanceAs (IsModHom G p)
  obtain ⟨I, E, hE⟩ := invariant_integral_closed_fullChart_faceIso_of_basis
    k b s.val («Σ».fullConeBasis_ray_set s) Y p₀
  have hIs : I.image b ⊆ s.val := by
    rw [«Σ».fullConeBasis_ray_set s]
    exact Finset.image_subset_image (Finset.subset_univ I)
  have hF : I.image b ∈ «Σ».cones :=
    «Σ».downward s.val («Σ».fullCones_mem s) _ hIs
  let Γ := «Σ».completeQuotientStarFan b I hF
  let t : «Σ».OrbitConeIndex b I := ⟨s.val, «Σ».fullCones_mem s, hIs⟩
  let t₀ : Γ.ConeIndex := «Σ».orbitConeQuotientIndex b I hF t
  let U := coneChart k (orbitQuotientCone b I s.val)
  let a : U ⟶ C.curve.left := E.inv ≫ q.left
  let z : U ⟶ Γ.fanScheme k := Γ.fanChartMap k t₀
  let i : Γ.fanScheme k ⟶ «Σ».fanScheme k := «Σ».orbitClosureMap k b I hF
  let c : C.curve.left ⟶ «Σ».fanScheme k := C.inclusion.left
  let j₀ : coneChart k s.val ⟶ «Σ».fanScheme k := j.left
  let p₁ : Y.left ⟶ coneChart k s.val := p.left
  let f : U ⟶ coneChart k s.val := orbitQuotientChartMap k b I s.val hIs
  letI : IsClosedImmersion c := C.closed
  letI : IsIntegral U := Γ.coneChart_isIntegral k t₀
  letI : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion (E.inv ≫ q.left))
  letI : IsOpenImmersion z := inferInstanceAs (IsOpenImmersion (Γ.fanChartMap k t₀))
  letI : IsSchemeTheoreticallyDominant a := IsSchemeTheoreticallyDominant.of_isDominant a
  letI : IsSchemeTheoreticallyDominant z := IsSchemeTheoreticallyDominant.of_isDominant z
  letI : IsClosedImmersion i := inferInstanceAs
    (IsClosedImmersion («Σ».orbitClosureMap k b I hF))
  have hpq : p₁ ≫ j₀ = q.left ≫ c :=
    (overPullback_isPullback j C.inclusion).w
  have hE' : E.hom ≫ f = p₁ := hE
  have hinv : E.inv ≫ p₁ = f := by
    calc
      E.inv ≫ p₁ = E.inv ≫ (E.hom ≫ f) :=
        congrArg (fun q : Y.left ⟶ coneChart k s.val => E.inv ≫ q) hE'.symm
      _ = f := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hcommon : a ≫ c = z ≫ i := by
    calc
      a ≫ c = E.inv ≫ (q.left ≫ c) := Category.assoc E.inv q.left c
      _ = E.inv ≫ (p₁ ≫ j₀) :=
        congrArg (fun q : Y.left ⟶ «Σ».fanScheme k => E.inv ≫ q) hpq.symm
      _ = (E.inv ≫ p₁) ≫ j₀ := (Category.assoc E.inv p₁ j₀).symm
      _ = f ≫ j₀ := congrArg (fun q : U ⟶ coneChart k s.val => q ≫ j₀) hinv
      _ = z ≫ i := («Σ».orbitClosureMap_chart k b I hF t).symm
  let F := closedImageIsoOfDenseComposite a z c i hcommon
  have hFmap : F.hom ≫ i = c :=
    closedImageIsoOfDenseComposite_embedding a z c i hcommon
  have hiBase : i ≫ («Σ».fanSchemeOver k).hom = (Γ.fanSchemeOver k).hom :=
    comp_over («Σ».orbitClosureMap k b I hF) (Spec (CommRingCat.of k))
  have hbase : F.hom ≫ (Γ.fanSchemeOver k).hom = C.curve.hom := by
    calc
      F.hom ≫ (Γ.fanSchemeOver k).hom = F.hom ≫ (i ≫ («Σ».fanSchemeOver k).hom) :=
        congrArg (fun q : Γ.fanScheme k ⟶ Spec (CommRingCat.of k) => F.hom ≫ q) hiBase.symm
      _ = (F.hom ≫ i) ≫ («Σ».fanSchemeOver k).hom :=
        (Category.assoc F.hom i («Σ».fanSchemeOver k).hom).symm
      _ = c ≫ («Σ».fanSchemeOver k).hom :=
        congrArg (fun q : C.curve.left ⟶ «Σ».fanScheme k => q ≫ («Σ».fanSchemeOver k).hom) hFmap
      _ = C.curve.hom := C.inclusion.w
  exact ⟨s, I, hF, Over.isoMk F hbase, hFmap⟩

theorem invariantIntegralCurve_isOrbitClosure (hpure : «Σ».IsPure)
    (C : InvariantIntegralCurve k n («Σ».fanSchemeOver k)) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
      (hF : I.image b ∈ «Σ».cones),
      ∃ e : C.curve ≅ («Σ».completeQuotientStarFan b I hF).fanSchemeOver k,
        e.hom.left ≫ «Σ».orbitClosureMap k b I hF = C.inclusion.left := by
  obtain ⟨s, I, hF, e, he⟩ := «Σ».invariantIntegralCurve_isOrbitClosure_fullCone k hpure C
  exact ⟨«Σ».fullConeBasis s, I, hF, e, he⟩

/-- Every genuine invariant integral curve is the projective line over
the original field.  The rank-one conclusion follows from the curve's
ordinary Krull dimension. -/
theorem invariantIntegralCurve_exists_projectiveLineIso (hpure : «Σ».IsPure)
    (C : InvariantIntegralCurve k n («Σ».fanSchemeOver k)) :
    ∃ e : C.curve.left ≅ projectiveLineScheme k,
      e.hom.IsOver (Spec (CommRingCat.of k)) := by
  obtain ⟨b, I, hF, e, he⟩ := «Σ».invariantIntegralCurve_isOrbitClosure k hpure C
  let Γ := «Σ».completeQuotientStarFan b I hF
  have hpureΓ : Γ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  have hdim : n-I.card = 1 := by
    have h := IsHomeomorph.topologicalKrullDim_eq _
      ((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom.homeomorph.isHomeomorph
    change topologicalKrullDim C.curve.left = topologicalKrullDim (Γ.fanScheme k) at h
    rw [C.dimension, Γ.fanScheme_topologicalKrullDim k hpureΓ] at h
    exact_mod_cast h.symm
  let e₀ := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  let e₁ := oneDimensionalFanSchemeIso Γ hdim k
  refine ⟨e₀ ≪≫ e₁, ?_⟩
  change (e.hom.left ≫ e₁.hom).IsOver (Spec (CommRingCat.of k))
  letI : e₁.hom.IsOver (Spec (CommRingCat.of k)) := inferInstanceAs
    ((oneDimensionalFanSchemeIso Γ hdim k).hom.IsOver (Spec (CommRingCat.of k)))
  refine ⟨?_⟩
  change (e.hom.left ≫ e₁.hom) ≫ (projectiveLineScheme k ↘ Spec (CommRingCat.of k)) =
    C.curve.hom
  exact (Category.assoc e.hom.left e₁.hom _).trans
    ((congrArg (fun q : Γ.fanScheme k ⟶ Spec (CommRingCat.of k) => e.hom.left ≫ q)
      (comp_over e₁.hom (Spec (CommRingCat.of k)))).trans e.hom.w)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.invariantIntegralCurve_isOrbitClosure
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.invariantIntegralCurve_exists_projectiveLineIso
end
end
end Source_ToricInvariantOrbitClosure

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.invariantIntegralCurve_isOrbitClosure_fullCone
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.invariantIntegralCurve_exists_projectiveLineIso
