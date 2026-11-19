module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import geometry_verified.stage000
import all geometry_verified.stage000
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Category.TopCat.Opens
public import geometry_verified.stage001
import all geometry_verified.stage001
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.FinCases
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import paper_verification.literal004
import all paper_verification.literal004
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import tau_ceti.algebra.homology.short_complex.short_exact
import all tau_ceti.algebra.homology.short_complex.short_exact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Data.Fintype.Lattice
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Skyscraper

set_option Elab.async false

section GeometryLiteralSource006
/- Original source: TauCeti.CategoryTheory.Sites.SheafCohomology.Over -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Cohomology on a localized site

Cohomology at an object agrees with cohomology of the restricted sheaf on the localized site
when restriction and its left adjoint are exact. On a preorder site, this left adjoint is
extension by zero to the ambient site. For the site of open subsets of a space, the comparison
identifies cohomology on an open subset with cohomology of the restricted sheaf.

The comparison uses the action of the left adjoint on free abelian representable sheaves and
Mathlib's `CategoryTheory.Adjunction.extEquiv` for exact adjunctions.

## Main declarations

* `CategoryTheory.GrothendieckTopology.sheafPullbackFreeYonedaIso`: extension on the source
  objects defining cohomology on an object of the site.
* `CategoryTheory.GrothendieckTopology.cohomologyPresheafEvaluationIsoFunctorOverH`: the comparison,
  natural in the coefficient sheaf.
* `CategoryTheory.Sheaf.cohomologyPresheafObjIsoOverH`: `Hⁿ(U, F) ≅ Hⁿ(F.over U)`.

This comparison transports acyclicity of the restricted sheaf to vanishing of cohomology on
the corresponding object, for instance from affine acyclicity to local vanishing hypotheses.
-/

public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

open TauCeti.CategoryTheory

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify (J.over U) AddCommGrpCat.{v}]
  [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]

private def extendedSectionsCorepresentation (V : Over U) :
    ((sheafSections J AddCommGrpCat.{v}).obj (op V.left) ⋙ forget AddCommGrpCat).CorepresentableBy
      (((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).obj
        ((freeYonedaSheafFunctor (J.over U)).obj V)) where
  homEquiv :=
    ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).homEquiv _ _ |>.trans
      (freeYonedaSheafSectionsEquiv (J.over U) V _).toEquiv
  homEquiv_comp g f := by
    let adj := (Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J
    exact (congrArg (freeYonedaSheafSectionsEquiv (J.over U) V _)
      (adj.homEquiv_naturality_right f g)).trans
      (freeYonedaSheafSectionsEquiv_naturality_right (J.over U) _
        ((J.overPullback AddCommGrpCat.{v} U).map g))

/-- Extension to the ambient site sends the free abelian sheaf on `V : Over U` to the free
abelian sheaf on `V.left`. -/
def sheafPullbackFreeYonedaIso (V : Over U) :
    ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).obj
      ((freeYonedaSheafFunctor (J.over U)).obj V) ≅ (freeYonedaSheafFunctor J).obj V.left :=
  (extendedSectionsCorepresentation J U V).uniqueUpToIso (freeYonedaSheafCorepresentableBy J V.left)

end

local instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint] :
    ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).isLeftAdjoint

local instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C) :
    (J.overPullback AddCommGrpCat.{v} U).Additive where
  map_add := rfl

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify (J.over U) AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  [HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{v})]
  [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]
  [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U)]
  [PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J)]

local instance : ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).Additive :=
  ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).left_adjoint_additive

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Under an exact restriction adjunction, cohomology at `U` agrees with cohomology at the
terminal object of the localized site, naturally in the coefficient sheaf. -/
private def cohomologyPresheafEvaluationIsoOver (n : ℕ) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U) ≅
    J.overPullback AddCommGrpCat.{v} U ⋙
      _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor (J.over U) n ⋙
        (evaluation (Over U)ᵒᵖ AddCommGrpCat.{w}).obj (op (Over.mk (𝟙 U))) := by
  change (Abelian.extFunctor n).obj (op ((freeYonedaSheafFunctor J).obj U)) ≅
    J.overPullback AddCommGrpCat.{v} U ⋙ (Abelian.extFunctor n).obj
      (op ((freeYonedaSheafFunctor (J.over U)).obj (Over.mk (𝟙 U))))
  exact (Abelian.extFunctor n).mapIso (sheafPullbackFreeYonedaIso J U (Over.mk (𝟙 U))).op ≪≫
    NatIso.ofComponents
      (fun F ↦ AddEquiv.toAddCommGrpIso
        (((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).extEquiv
          (X := (freeYonedaSheafFunctor (J.over U)).obj (Over.mk (𝟙 U)))
          (Y := F) (n := n)))
      (by
        intro F G f
        ext x
        let adj := (Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J
        exact adj.extEquiv_naturality_right₀ x f)

/-- Under an exact restriction adjunction, cohomology at `U` agrees with the cohomology of the
restricted sheaf, naturally in the coefficient sheaf. -/
def cohomologyPresheafEvaluationIsoFunctorOverH (n : ℕ) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U) ≅
    J.overPullback AddCommGrpCat.{v} U ⋙ _root_.CategoryTheory.Sheaf.functorH (J.over U) n :=
  cohomologyPresheafEvaluationIsoOver J U n ≪≫
    Functor.isoWhiskerLeft (J.overPullback AddCommGrpCat.{v} U)
      (_root_.CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH (J.over U) n
        (Over.mkIdTerminal (X := U)))

end

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- Under an exact restriction adjunction, cohomology at an object is the cohomology of the
restricted sheaf on the localized site. -/
noncomputable def cohomologyPresheafObjIsoOverH (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{v})]
    [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]
    [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U)]
    [PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J)] :
    H' F n U ≅ AddCommGrpCat.of (H (F.over U) n) :=
  (J.cohomologyPresheafEvaluationIsoFunctorOverH U n).app F

end CategoryTheory.Sheaf
end
end GeometryLiteralSource006

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Sites.SheafCohomology.Over"

section GeometryLiteralSource007
/- Original source: TauCeti.Topology.Sheaves.Over -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Open embeddings and over categories of open subsets

Let `f : X ⟶ Y` be an open embedding of topological spaces, with open image `U = range f`.
Mathlib's `TopologicalSpace.Opens.overEquivalence` identifies `Over U` with the open subsets of the
subspace `U`. This file gives the corresponding equivalence `Over U ≌ Opens X` for the open
embedding itself: an open subset `W ⊆ U` goes to `f⁻¹(W)`, and an open subset `V ⊆ X` goes back to
`f(V)`. The equivalence is a dense subsite in both directions, so it induces an equivalence of
sheaf categories under which a sheaf `F` on `Y`, restricted to `U`, becomes the sheaf
`V ↦ F(f(V))` on `X`.

Working with `f` rather than with the subspace `U` keeps that sheaf literally equal to the
pushforward along `f(-)`, which is how Mathlib defines the restriction of a sheaf of modules along
an open immersion of schemes.

The construction of the dense-subsite instances is adapted from
`Mathlib.Topology.Sheaves.Over`, by Joël Riou.

## Main declarations

* `Topology.IsOpenEmbedding.overEquivalence`: the equivalence `Over (range f) ≌ Opens X`.
* The instances saying that its functor and inverse are dense subsites for the Grothendieck
  topologies of open covers.
-/

public section

universe u

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenEmbedding f)

/-- An open embedding `f : X ⟶ Y` identifies the open subsets of `Y` contained in the range of
`f` with the open subsets of `X`, by taking preimages and images under `f`. -/
def _root_.Topology.IsOpenEmbedding.overEquivalence :
    Over (⟨Set.range f, hf.isOpen_range⟩ : Opens Y) ≌ Opens X where
  functor.obj W := (Opens.map f).obj W.left
  functor.map g := (Opens.map f).map g.left
  inverse.obj V := Over.mk (Y := hf.functor.obj V) (homOfLE (Set.image_subset_range f V))
  inverse.map g := Over.homMk (hf.functor.map g)
  unitIso := NatIso.ofComponents (fun W ↦ Over.isoMk (eqToIso (by
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := W.hom.le hy
      exact ⟨x, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx)))
  counitIso := NatIso.ofComponents (fun V ↦ eqToIso (by
    ext x
    exact hf.injective.mem_set_image))

@[simp]
lemma _root_.Topology.IsOpenEmbedding.overEquivalence_functor_obj
    (W : Over (⟨Set.range f, hf.isOpen_range⟩ : Opens Y)) :
    hf.overEquivalence.functor.obj W = (Opens.map f).obj W.left := by
  rw [Topology.IsOpenEmbedding.overEquivalence]

end TauCeti

namespace Topology.IsOpenEmbedding

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenEmbedding f)

/-- The inverse of `overEquivalence`, followed by the forgetful functor from the over category,
is the image functor on open subsets. -/
def overEquivalenceInverseCompForgetIso :
    hf.overEquivalence.inverse ⋙ Over.forget _ ≅ hf.functor := by
  rw [Topology.IsOpenEmbedding.overEquivalence]
  exact NatIso.ofComponents (fun _ ↦ Iso.refl _)

instance isDenseSubsite_overEquivalence_functor :
    CategoryTheory.Functor.IsDenseSubsite ((Opens.grothendieckTopology Y).over _)
      (Opens.grothendieckTopology X) hf.overEquivalence.functor where
  functorPushforward_mem_iff {V S} := by
    simp only [Opens.mem_grothendieckTopology, Sieve.mem_functorPushforward_functor]
    constructor
    · intro H y hyV
      obtain ⟨x, rfl⟩ := V.hom.le hyV
      obtain ⟨W, g, hW, hxW⟩ := H x hyV
      exact ⟨_, ((hf.overEquivalence.symm.toAdjunction.homEquiv _ _).symm g).left,
        ⟨_, _, 𝟙 _, hW, rfl⟩, x, hxW, rfl⟩
    · intro H x hxV
      obtain ⟨W, g, ⟨W', hW'V, hWW', hSW'V, rfl⟩, hxW⟩ := H (f x) hxV
      exact ⟨_, hf.overEquivalence.functor.map hW'V,
        S.downward_closed hSW'V (hf.overEquivalence.unitInv.app W'), hWW'.le hxW⟩

instance isDenseSubsite_overEquivalence_symm_inverse :
    CategoryTheory.Functor.IsDenseSubsite ((Opens.grothendieckTopology Y).over _)
      (Opens.grothendieckTopology X) hf.overEquivalence.symm.inverse :=
  inferInstanceAs (CategoryTheory.Functor.IsDenseSubsite
    ((Opens.grothendieckTopology Y).over _) (Opens.grothendieckTopology X)
      hf.overEquivalence.functor)

instance isDenseSubsite_overEquivalence_inverse :
    CategoryTheory.Functor.IsDenseSubsite (Opens.grothendieckTopology X)
      ((Opens.grothendieckTopology Y).over _) hf.overEquivalence.inverse :=
  inferInstanceAs (CategoryTheory.Functor.IsDenseSubsite (Opens.grothendieckTopology X)
    ((Opens.grothendieckTopology Y).over _) hf.overEquivalence.symm.functor)

instance isContinuous_functor : hf.functor.IsContinuous
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  CategoryTheory.Functor.isContinuous_comp'
    hf.overEquivalenceInverseCompForgetIso (Opens.grothendieckTopology X)
      ((Opens.grothendieckTopology Y).over _) (Opens.grothendieckTopology Y)

/-- Restriction to the range of an open embedding, followed by transport along
`overEquivalence`, is naturally isomorphic to pushforward along the image functor on opens. -/
def overPullbackSheafCongrIso (A : Type*) [Category A] :
    (Opens.grothendieckTopology Y).overPullback A
        (⟨Set.range f, hf.isOpen_range⟩ : Opens Y) ⋙
      (hf.overEquivalence.sheafCongr
        ((Opens.grothendieckTopology Y).over _)
        (Opens.grothendieckTopology X) A).functor ≅
    hf.functor.sheafPushforwardContinuous A
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  CategoryTheory.Functor.sheafPushforwardContinuousComp'
    hf.overEquivalenceInverseCompForgetIso A (Opens.grothendieckTopology X)
      ((Opens.grothendieckTopology Y).over _) (Opens.grothendieckTopology Y)

end Topology.IsOpenEmbedding
end
end GeometryLiteralSource007

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Topology.Sheaves.Over"

section GeometryLiteralSource008
/- Original source: TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Cohomology on the image of an open immersion

Let `f : Y ⟶ X` be an open immersion of schemes and `M` a sheaf of modules on `X`. This file
identifies the cohomology `Hⁿ(f(Y), M)` of the open subset `f(Y)` of `X` with the cohomology
`Hⁿ(Y, M|_Y)` of the restriction of `M` along `f`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.cohomologyOnOpensRangeNatIso`: the comparison
  `Hⁿ(f(Y), M) ≅ Hⁿ(Y, M|_Y)`, natural in `M`, and `cohomologyOnOpensRangeIso` its component at
  a single sheaf of modules.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- Transporting the underlying sheaf of a sheaf of modules restricted to `f.opensRange` along
the open-embedding equivalence agrees with restriction of modules along `f`. -/
def overPullbackSheafCongrIsoRestrict
    [f.isOpenEmbedding.overEquivalence.inverse.IsDenseSubsite
      (Opens.grothendieckTopology Y)
      ((Opens.grothendieckTopology X).over f.opensRange)] :
    SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (Opens.grothendieckTopology X).overPullback AddCommGrpCat.{u} f.opensRange ⋙
          (f.isOpenEmbedding.overEquivalence.sheafCongr
            ((Opens.grothendieckTopology X).over f.opensRange)
            (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).functor ≅
      Scheme.Modules.restrictFunctor f ⋙ SheafOfModules.toSheaf Y.ringCatSheaf := by
  exact Functor.isoWhiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf)
    (Topology.IsOpenEmbedding.overPullbackSheafCongrIso
      f.isOpenEmbedding AddCommGrpCat.{u})

/-- The cohomology of a sheaf of modules on the image of an open immersion `f : Y ⟶ X` is the
cohomology of its restriction along `f`, naturally in the sheaf of modules. -/
def cohomologyOnOpensRangeNatIso (n : ℕ) :
    SheafOfModules.toSheaf X.ringCatSheaf ⋙
        CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
          (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op f.opensRange) ≅
      Scheme.Modules.restrictFunctor f ⋙ cohomologyFunctor Y n :=
  let J := Opens.grothendieckTopology X
  let e := f.isOpenEmbedding.overEquivalence
  haveI : (J.overPullback AddCommGrpCat.{u} f.opensRange).IsLeftAdjoint :=
    ((Over.forget f.opensRange).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (J.over f.opensRange) J).isLeftAdjoint
  haveI : e.inverse.IsDenseSubsite (Opens.grothendieckTopology Y) (J.over f.opensRange) :=
    Topology.IsOpenEmbedding.isDenseSubsite_overEquivalence_inverse f.isOpenEmbedding
  -- Cohomology on `f(Y)` is cohomology on the over category of `f(Y)`, which is equivalent to the
  -- site of open subsets of `Y`; the transported sheaf is the underlying sheaf of `M|_Y`.
  Functor.isoWhiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf)
      (J.cohomologyPresheafEvaluationIsoFunctorOverH f.opensRange n) ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.toSheaf X.ringCatSheaf ⋙ J.overPullback AddCommGrpCat.{u} f.opensRange)
      ((CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH (J.over f.opensRange) n
        (isTerminalTop.isTerminalObj e.inverse)).symm ≪≫
      (CategoryTheory.cohomologyPresheafEvaluationIsoSheafCongr (J.over f.opensRange)
        (Opens.grothendieckTopology Y) e n ⊤).symm) ≪≫
    Functor.isoWhiskerRight (overPullbackSheafCongrIsoRestrict f)
      (CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Y) n ⋙
        (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) ≪≫
    Functor.isoWhiskerLeft
      (Scheme.Modules.restrictFunctor f ⋙ SheafOfModules.toSheaf Y.ringCatSheaf)
      (CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH
        (Opens.grothendieckTopology Y) n isTerminalTop)

variable (M : X.Modules)

/-- The cohomology of a sheaf of modules `M` on the image of an open immersion `f : Y ⟶ X` is the
cohomology of the restriction of `M` along `f`. -/
def cohomologyOnOpensRangeIso (n : ℕ) :
    cohomologyOn M n f.opensRange ≅ AddCommGrpCat.of (Cohomology (M.restrict f) n) :=
  (cohomologyOnOpensRangeNatIso f n).app M

end AlgebraicGeometry.Scheme.Modules

end
end
end GeometryLiteralSource008

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion"

section GeometryLiteralSource009
/- Original source: TauCeti.Data.Fin.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Basic results about finite ordinal types

This file collects elementary facts about finite ordinal types, including the classification of
permutations of `Fin 2`, sums of reversed indices, indicator sums indexed by `Fin n`, the final
value of a partial product, sums of families vanishing beyond an index, and the cyclic index
arithmetic of `Fin 3`.

`Fintype.sum_ite_eq` evaluates a sum whose indicator compares two elements of the index type.
When the comparison is instead between a natural number and the `Fin.val` of the index — as it is
whenever a family is indexed by `ℕ` and summed over `Fin n` — the index may fall outside the
range, so the value is a `dite` rather than a plain application.

## Main results

* `Equiv.Perm.eq_one_or_swap_fin_two` and `Equiv.Perm.univ_fin_two`: every permutation of
  `Fin 2` is the identity or the transposition, and these form the set of all permutations.
* `TauCeti.forall_cons_swap_eq_zero_iff`: vanishing of the final coordinates after swapping
  coordinate zero with coordinate `d` in a vector built with `Fin.cons`.
* `Fin.sum_univ_eq_sum_castLE_add`: a sum over `Fin n` of a family vanishing beyond `i`
  splits as its sum over the first `i` indices plus its value at `i`.
* `Fin.rev_finRotate_rev` and `Fin.rev_finRotate_symm`: reversal carries forward rotation to
  backward rotation and conversely.
* `Fin.finRotate_rev_finRotate_rev`: negation modulo `n`, written as `i ↦ finRotate n i.rev`, is
  an involution.
* `Fin.coe_finRotate_pow`: a power of the rotation `finRotate n` adds its exponent modulo `n`;
  `Fin.coe_finRotate_of_add_one_lt` is the step away from the last index, where no wrapping occurs.
* `Finset.sum_range_const_sub_succ`: the sum of a reversed initial segment of natural numbers.
* `Finset.card_filter_castSucc_lt_succ`: counting the elements of a set of indices below `i.succ`
  rather than `i.castSucc` adds `1` exactly when `i` belongs to it.
* `Fin.sum_rev_castLE`: the sum of the values of a reversed embedded finite ordinal.
* `Fin.castSucc_add_one_of_ne_last`, `Fin.castSucc_sub_one_of_ne_zero`: how `Fin.castSucc`
  interacts with the cyclic successor and predecessor.
* `Fin.castSucc_last_add_one`: adding one to the penultimate index gives the last index.
* `Fin.zero_sub_one_eq_last`: subtracting one from `0` gives the last index.
* `Fin.eq_castSucc_last_or_eq_last`: an index `≥ n` of `Fin (n + 2)` is the penultimate or the
  last one.
* `Fin.exists_succ_succ_eq`: the indices `> 1` of `Fin (n + 2)` are the double successors.
* `Fin.last_ne_zero`, `Fin.castSucc_last_ne_zero`, `Fin.castSucc_last_ne_one`, `Fin.last_ne_one`:
  the last and penultimate indices differ from `0` and `1` in the nondegenerate cases.
* `Fin.sum_univ_eq_zero_add_last_add_sum_erase`: a sum over `Fin (n + 1)` with its first and last
  summands split off.
* `Fin.natCast_ne_zero`: the cast of a natural number `0 < a < n` to `Fin n` (under
  `open Fin.NatCast`) is nonzero.
* `Fin.val_one_of_two_le`: the element `1` of `Fin m` has value `1` once `2 ≤ m`.
* `Fin.insertNth_insertNth`: two insertions into a tuple commute, up to reindexing by `succAbove`
  and `predAbove`; the dual of Mathlib's `Fin.removeNth_removeNth_eq_swap`.
* `Fin.insertNth_append_castAdd` and `Fin.insertNth_append_natAdd`: insertion into either block
  of an appended tuple, used to compute faces of cross products of cubes.
* `Fin.predAbove_succ_succAbove`: `Fin.predAbove p` inverts `p.succ.succAbove`, the
  counterpart of Mathlib's `Fin.predAbove_succAbove` for `p.castSucc.succAbove`.
* `Fin.val_succAbove`: the value of `p.succAbove i`, read off the comparison of `i` with `p`.
* `Fin.castSucc_le_succAbove`: `p.succAbove i` lies weakly above `i.castSucc`.
* `Fin.val_predAbove`: the value of `p.predAbove i`, read off the comparison of `i` with `p`.
* `Fin.natAdd_succAbove_castAdd` and `Fin.natAdd_succAbove_natAdd`: skipping a point of the
  second block of `Fin (n + (m + 1))`, on either block.
* `Fin.finRotate_succ_eq_succ_succAbove` and `Fin.finRotate_succ_succAbove_of_ne`: the cyclic
  successor of `Fin (n + 1)` against the embeddings `Fin.succ` and `i.succ.succAbove` of `Fin n`,
  as used when a new entry is inserted into a cyclic sequence.
* `Fin.finRotate_castSucc`: the cyclic successor of a non-last index `i.castSucc` is `i.succ`.
* `Fin.ite_even_comp_finRotate_symm`: rotating a tuple of even length alternating between two
  entries swaps the two entries.
* `Fin.succAbove_adjacent_cases`: the positions `p` of `Fin (n + 1)` cyclically adjacent to
  `p.succAbove i`.
* `Fin.swap_castSucc_succ_succAbove`: the transposition of `k.castSucc` and `k.succ` exchanges the
  embeddings of `Fin n` skipping either of them.
* `Fin.card_filter_prod_succAbove`: a count of pairs in `Fin (n + 1)` split at a point in each
  coordinate.
* `Fin.val_orderSucc_of_lt` and `Fin.orderSucc_eq_self_of_not_lt`: the order successor of `Fin n`
  read off the value, below and at the top element.  Mathlib's `Fin.orderSucc_castSucc` and
  `Fin.orderSucc_last` state the same thing in the `castSucc`/`last` normal form; these are the
  versions keyed on the inequality `i + 1 < n`.
* `Fin.insertNth_castAdd_comp_castAdd`, `Fin.insertNth_castAdd_apply_natAdd`,
  `Fin.insertNth_natAdd_apply_castAdd` and `Fin.insertNth_natAdd_comp_natAdd`: the entries of a
  tuple indexed by `Fin ((k + 1) + (l + 1))` after inserting an entry into one of the two blocks.
* `Fin.Ioo_eq_empty_of_le_two` and `Fin.eq_empty_of_subset_Ioo_of_le_two`: open intervals in
  `Fin n`, and hence finsets inside them, are empty when `n ≤ 2`.
* `Fin.partialProd_last`: the final partial product is the product of all the entries.
* `Fin.partialSum_last`: the final partial sum is the sum of all the entries.
* `Fin.prod_contractNth_castSucc` and `Fin.sum_contractNth_castSucc`: multiplying (adding) two
  adjacent entries of a tuple does not change the product (sum) of all its entries.
* `TauCeti.add_one_ne_self`: adding one in `Fin n` is nontrivial when `2 ≤ n`.
* `TauCeti.add_one_add_one_ne_self`: adding one twice in `Fin n` is nontrivial when `3 ≤ n`;
  `TauCeti.sub_one_ne_self` and `TauCeti.add_one_ne_sub_one` are the companions for subtraction.
* `TauCeti.apply_eq_apply_zero_of_add_one`: a function on `Fin (n + 1)` unchanged by adding one
  is constant.
* `TauCeti.eq_add_one_or_eq_add_two_fin_three`: a distinct index of `Fin 3` is one of the two
  shifts of the other.
* `TauCeti.add_one_add_one_fin_three`, `TauCeti.add_one_add_two_fin_three`,
  `TauCeti.add_two_add_one_fin_three` and `TauCeti.add_two_add_two_fin_three`: the shifts by `1`
  and `2` compose cyclically in `Fin 3`.
* `TauCeti.sum_fin_three_rotate`: a sum over `Fin 3` read off starting from an arbitrary index.
* `TauCeti.neg_one_pow_val_add_one`: for `n` even, adding one in `Fin n` flips the sign `(-1) ^ ·`
  read off the value.
* `TauCeti.sum_ite_val_add`: a sum against the indicator of `b = k + j` picks out the summand at
  `b - j`, or vanishes when there is no such index.
* `TauCeti.exists_foldl_eq_of_parent`: a decreasing parent table gives paths from its root.
* `TauCeti.not_mem_Ioo_castSucc_succ`: a monotone `Fin` family has no value strictly between
  consecutive entries.
* `TauCeti.exists_mem_Icc_castSucc_succ`: consecutive closed intervals cover the interval
  between the first and last values of any `Fin` family with at least two entries.
-/

public section

open scoped BigOperators

namespace Finset

/-- The sum of the first `k` entries of the reversed range `N - 1, ..., 0`. -/
theorem sum_range_const_sub_succ (N k : ℕ) (hk : k ≤ N) :
    Finset.sum (Finset.range k) (fun x => N - (x + 1)) =
      k.choose 2 + k * (N - k) := by
  calc
    Finset.sum (Finset.range k) (fun x => N - (x + 1)) =
        Finset.sum (Finset.range k) (fun x => (N - k) + (k - 1 - x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxk := Finset.mem_range.mp hx
      omega
    _ = k * (N - k) + Finset.sum (Finset.range k) (fun x => k - 1 - x) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = k * (N - k) + Finset.sum (Finset.range k) (fun x => x) := by
      rw [Finset.sum_range_reflect (fun x => x) k]
    _ = k.choose 2 + k * (N - k) := by
      rw [Finset.sum_range_id, Nat.choose_two_right]
      omega

/-- Counting the elements of `S` below `i.succ` adds `1` to those below `i.castSucc` when
`i ∈ S`. -/
theorem card_filter_castSucc_lt_succ {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    #{s ∈ S | s.castSucc < i.succ} =
      #{s ∈ S | s.castSucc < i.castSucc} + if i ∈ S then 1 else 0 := by
  have h : ({s ∈ S | s.castSucc < i.succ} : Finset (Fin n)) =
      {s ∈ S | s.castSucc < i.castSucc} ∪ {s ∈ S | s = i} := by
    ext s
    simp only [mem_filter, mem_union, Fin.castSucc_lt_succ_iff, Fin.castSucc_lt_castSucc_iff,
      le_iff_lt_or_eq]
    tauto
  rw [h, card_union_of_disjoint (disjoint_filter.mpr fun s _ h h' ↦ by simp [h'] at h)]
  split_ifs with hi <;> simp [filter_eq', hi]

end Finset

namespace Fin

/-- The sum of the values in the first `k` positions of the reversed finite ordinal `Fin N`. -/
theorem sum_rev_castLE (N k : ℕ) (hk : k ≤ N) :
    (∑ i : Fin k, (Fin.rev (Fin.castLE hk i) : ℕ)) =
      k.choose 2 + k * (N - k) := by
  rw [Finset.sum_fin_eq_sum_range]
  simp only [Fin.rev, Fin.castLE]
  calc
    Finset.sum (Finset.range k)
        (fun x => if h : x < k then N - (x + 1) else 0) =
        Finset.sum (Finset.range k) (fun x => N - (x + 1)) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]
    _ = _ := Finset.sum_range_const_sub_succ N k hk

/-- The final partial product is the product of all the entries. -/
@[to_additive /-- The final partial sum is the sum of all the entries. -/]
theorem partialProd_last {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) :
    Fin.partialProd f (Fin.last n) = ∏ i, f i := by
  rw [Fin.partialProd, Fin.val_last]
  rw [(List.take_eq_self_iff _).mpr (by simp), Fin.prod_ofFn]

/-- The last entry times the preceding partial product is the product of all entries. -/
theorem last_mul_partialProd {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin (n + 1) → M) :
    f (Fin.last n) * Fin.partialProd (Fin.init f) (Fin.last n) = ∏ i, f i := by
  rw [mul_comm, Fin.partialProd_last, Fin.init_def, ← Fin.prod_univ_castSucc f]

/-- Multiplying two adjacent entries of a tuple does not change the product of all its
entries. -/
@[to_additive (attr := simp)
  /-- Adding two adjacent entries of a tuple does not change the sum of all its entries. -/]
theorem prod_contractNth_castSucc {M : Type*} [CommMonoid M] {n : ℕ} (j : Fin (n + 1))
    (g : Fin (n + 2) → M) : ∏ k, Fin.contractNth j.castSucc (· * ·) g k = ∏ k, g k := by
  have hlast : j.castSucc.succ.succAbove (Fin.last (n + 1)) = Fin.last (n + 2) :=
    Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
  rw [← partialProd_last, ← partialProd_last, Fin.partialProd_contractNth, Function.comp_apply,
    hlast]

/-- A product over `Fin n` of a family equal to `1` beyond `i` is its product over the first
`i` indices times its value at `i`. -/
@[to_additive /-- A sum over `Fin n` of a family vanishing beyond `i` is its sum over the
first `i` indices plus its value at `i`. -/]
theorem prod_univ_eq_prod_castLE_mul {M : Type*} [CommMonoid M] {n : ℕ} (i : Fin n)
    (f : Fin n → M) (hf : ∀ j, i < j → f j = 1) :
    ∏ j, f j = (∏ j : Fin i, f (castLE i.is_lt.le j)) * f i := by
  have hIio : Finset.univ.map (castLEEmb i.is_lt.le) = Finset.Iio i := by
    simp [← Finset.coe_inj, Set.Iio_def]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.Iic i))
      fun j _ hj => hf j (by simpa using hj),
    ← Finset.Iio_insert, Finset.prod_insert Finset.notMem_Iio_self, mul_comm, ← hIio,
    Finset.prod_map]
  simp only [castLEEmb_apply]

/-- Conjugating forward rotation of a finite ordinal by reversal gives backward rotation. -/
@[simp]
theorem rev_finRotate_rev {n : ℕ} (i : Fin n) :
    haveI := i.neZero
    Fin.rev (Fin.rev i + 1) = (finRotate n).symm i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [finRotate_symm_apply, ← Fin.last_sub, ← Fin.last_sub]
    have hlast : Fin.last n = (-1 : Fin (n + 1)) := by
      apply Fin.ext
      simp
    simp [sub_eq_add_neg, hlast, add_comm, add_left_comm]

/-- Reversal carries backward rotation of a finite ordinal to forward rotation. -/
@[simp]
theorem rev_finRotate_symm {n : ℕ} (i : Fin n) :
    haveI := i.neZero
    Fin.rev (i - 1) = finRotate n (Fin.rev i) := by
  apply Fin.rev_injective
  simp only [Fin.rev_rev]
  simpa only [finRotate_apply, finRotate_symm_apply] using (rev_finRotate_rev i).symm

/-- The map `i ↦ finRotate n i.rev`, which is negation modulo `n`, is an involution. -/
theorem finRotate_rev_finRotate_rev {n : ℕ} (i : Fin n) :
    finRotate n (finRotate n i.rev).rev = i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have := i.isLt
    ext
    simp only [coe_finRotate, Fin.ext_iff, Fin.val_last, Fin.val_rev]
    split_ifs <;> omega

/-- The value of a power of the cyclic permutation `finRotate n`: it adds `k` modulo `n`. -/
theorem coe_finRotate_pow {n : ℕ} (k : ℕ) (c : Fin n) :
    ((finRotate n ^ k) c : ℕ) = (c + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt c.isLt]
  | succ k ih =>
    have : NeZero n := ⟨Nat.pos_iff_ne_zero.mp c.pos⟩
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
      ← Nat.add_mod, ← add_assoc]

/-- Away from the last index, the cyclic permutation `finRotate n` adds one without wrapping
around. -/
theorem coe_finRotate_of_add_one_lt {n : ℕ} {i : Fin n} (h : (i : ℕ) + 1 < n) :
    (finRotate n i : ℕ) = i + 1 := by
  have := coe_finRotate_pow 1 i
  rwa [pow_one, Nat.mod_eq_of_lt h] at this

/-- Collapsing the hole opened immediately after `p` back onto `p` inverts the embedding
`p.succ.succAbove`. -/
@[simp]
theorem predAbove_succ_succAbove {n : ℕ} (p i : Fin n) : p.predAbove (p.succ.succAbove i) = i := by
  rcases le_or_gt i p with h | h
  · rw [succAbove_succ_of_le _ _ h, predAbove_castSucc_of_le _ _ h]
  · rw [succAbove_succ_of_lt _ _ h, predAbove_succ_of_le _ _ h.le]

/-- The value of `p.succAbove i`: the value of `i` below `p`, and one more from `p` on. -/
theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (p.succAbove i : ℕ) = if (i : ℕ) < p then (i : ℕ) else (i : ℕ) + 1 := by
  unfold succAbove
  split_ifs <;> simp_all [lt_def]

/-- `p.succAbove i` lies weakly above `i.castSucc`. -/
theorem castSucc_le_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    i.castSucc ≤ p.succAbove i := by
  rw [succAbove]
  split_ifs
  · exact le_rfl
  · exact castSucc_le_succ i

/-- The value of `p.predAbove i`: the value of `i` up to `p`, and one less above `p`. -/
theorem val_predAbove {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    (p.predAbove i : ℕ) = if (p : ℕ) < i then (i : ℕ) - 1 else (i : ℕ) := by
  rcases lt_or_ge p.castSucc i with h | h
  · rw [predAbove_of_castSucc_lt _ _ h]
    rw [lt_def, val_castSucc] at h
    simp [h]
  · rw [predAbove_of_le_castSucc _ _ h]
    rw [le_def, val_castSucc] at h
    simp [h]

/-- Skipping a point of the second block of `Fin (n + (m + 1))` fixes the first block. -/
@[simp]
theorem natAdd_succAbove_castAdd {n m : ℕ} (j : Fin (m + 1)) (k : Fin n) :
    (natAdd n j).succAbove (castAdd m k) = castAdd (m + 1) k := by
  ext
  simp only [val_succAbove, val_castAdd, val_natAdd]
  have := k.isLt
  split_ifs <;> omega

/-- Skipping a point of the second block of `Fin (n + (m + 1))` is skipping it in that block. -/
@[simp]
theorem natAdd_succAbove_natAdd {n m : ℕ} (j : Fin (m + 1)) (i : Fin m) :
    (natAdd n j).succAbove (natAdd n i) = natAdd n (j.succAbove i) := by
  ext
  simp only [val_succAbove, val_natAdd]
  split_ifs <;> omega

/-- The cyclic successor of `i.succ` in `Fin (n + 1)` is the cyclic successor of `i` in `Fin n`,
read through the embedding `i.succ.succAbove` that skips `i.succ`. -/
theorem finRotate_succ_eq_succ_succAbove {n : ℕ} (i : Fin n) :
    finRotate (n + 1) i.succ = i.succ.succAbove (finRotate n i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  have := i.isLt
  ext
  simp only [succAbove]
  split_ifs <;> simp only [lt_def, val_castSucc, val_succ, coe_finRotate, Fin.ext_iff,
    val_last] at * <;> split_ifs at * <;> omega

/-- Away from `i`, the embedding `i.succ.succAbove : Fin n → Fin (n + 1)`, which skips `i.succ`,
commutes with the cyclic successors. -/
theorem finRotate_succ_succAbove_of_ne {n : ℕ} {i k : Fin n} (hk : k ≠ i) :
    finRotate (n + 1) (i.succ.succAbove k) = i.succ.succAbove (finRotate n k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  rw [Ne, Fin.ext_iff] at hk
  have := k.isLt
  have := i.isLt
  ext
  simp only [succAbove]
  split_ifs <;> simp only [lt_def, val_castSucc, val_succ, coe_finRotate, Fin.ext_iff,
    val_last] at * <;> split_ifs at * <;> omega

/-- The cyclic successor of a non-last index `i.castSucc` of `Fin (n + 1)` is `i.succ`. -/
theorem finRotate_castSucc {n : ℕ} (i : Fin n) : finRotate (n + 1) i.castSucc = i.succ :=
  finRotate_of_lt i.isLt

/-- Rotating a tuple of even length alternating between two entries swaps the two entries. -/
theorem ite_even_comp_finRotate_symm {α : Type*} {n : ℕ} (hn : Even n) (x y : α) :
    (fun k : Fin n ↦ if Even (k : ℕ) then x else y) ∘ (finRotate n).symm =
      fun k : Fin n ↦ if Even (k : ℕ) then y else x := by
  funext k
  cases n with
  | zero => exact k.elim0
  | succ n =>
    cases k using Fin.cases with
    | zero =>
      have h : (finRotate (n + 1)).symm 0 = last n := (Equiv.symm_apply_eq _).2 finRotate_last.symm
      simp [h, Nat.even_add_one.1 hn]
    | succ k =>
      have h : (finRotate (n + 1)).symm k.succ = k.castSucc :=
        (Equiv.symm_apply_eq _).2 (finRotate_castSucc k).symm
      by_cases hk : Even (k : ℕ) <;> simp [h, hk, Nat.even_add_one]

/-- A position `p` of `Fin (n + 1)` cyclically adjacent to `p.succAbove i` is `i.castSucc` or
`i.succ`, or wraps around: `p` is last and `p.succAbove i` is `0`, or `p` is `0` and
`p.succAbove i` is last. -/
theorem succAbove_adjacent_cases {n : ℕ} {p : Fin (n + 1)} {i : Fin n}
    (h : finRotate (n + 1) p = p.succAbove i ∨ finRotate (n + 1) (p.succAbove i) = p) :
    p = i.castSucc ∨ p = i.succ ∨ (p = last n ∧ i.castSucc = 0) ∨ (p = 0 ∧ i.succ = last n) := by
  have hv := val_succAbove p i
  have := i.isLt
  simp only [Fin.ext_iff, coe_finRotate, val_last, val_zero, val_castSucc, val_succ] at h hv ⊢
  split_ifs at h hv <;> omega

/-- The transposition of `k.castSucc` and `k.succ` carries the embedding `k.castSucc.succAbove`,
which skips `k.castSucc`, to the embedding `k.succ.succAbove`, which skips `k.succ`. -/
theorem swap_castSucc_succ_succAbove {n : ℕ} (k i : Fin n) :
    Equiv.swap k.castSucc k.succ (k.castSucc.succAbove i) = k.succ.succAbove i := by
  rcases eq_or_ne i k with rfl | hik
  · simp
  have h : k.castSucc.succAbove i = k.succ.succAbove i := by
    ext
    simp only [val_succAbove, val_castSucc, val_succ]
    rw [Ne, Fin.ext_iff] at hik
    split_ifs <;> omega
  rw [h, Equiv.swap_apply_of_ne_of_ne]
  · rw [← succAbove_succ_self]
    exact fun h' ↦ hik (succAbove_right_injective h')
  · rw [← h, ← succAbove_castSucc_self]
    exact fun h' ↦ hik (succAbove_right_injective h')

/-- A count of pairs in `Fin (n + 1)`, split at `a` in the first coordinate and at `b` in the
second: the pair `(a, b)`, the pairs with exactly one coordinate at its split point, and the pairs
embedded by `a.succAbove` and `b.succAbove`. -/
theorem card_filter_prod_succAbove {n : ℕ} (P : Fin (n + 1) × Fin (n + 1) → Prop)
    [DecidablePred P] (a b : Fin (n + 1)) :
    (Finset.univ.filter P).card =
      (if P (a, b) then 1 else 0) +
        (Finset.univ.filter fun j : Fin n => P (a, b.succAbove j)).card +
        (Finset.univ.filter fun i : Fin n => P (a.succAbove i, b)).card +
        (Finset.univ.filter fun p : Fin n × Fin n =>
          P (a.succAbove p.1, b.succAbove p.2)).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [sum_univ_succAbove _ a]
  simp_rw [sum_univ_succAbove _ b]
  rw [Finset.sum_add_distrib, ← add_assoc]

/-- Adding one commutes with `Fin.castSucc` away from the last index. -/
theorem castSucc_add_one_of_ne_last {n : ℕ} {i : Fin (n + 1)} (hi : i ≠ last n) :
    castSucc (i + 1) = castSucc i + 1 := by
  simp [Fin.ext_iff, val_add_one, hi]

/-- Adding one to the penultimate index gives the last index. -/
theorem castSucc_last_add_one (n : ℕ) : castSucc (last n) + 1 = last (n + 1) :=
  coeSucc_eq_succ.trans (succ_last _)

/-- Subtracting one commutes with `Fin.castSucc` away from `0`. -/
theorem castSucc_sub_one_of_ne_zero {n : ℕ} {i : Fin (n + 1)} (hi : i ≠ 0) :
    castSucc (i - 1) = castSucc i - 1 := by
  simp [Fin.ext_iff, coe_sub_one, hi]

/-- Subtracting one from `0` gives the last index. -/
theorem zero_sub_one_eq_last {n : ℕ} : (0 : Fin (n + 1)) - 1 = last n :=
  (eq_sub_of_add_eq (last_add_one n)).symm

/-- The last index of `Fin (n + 1)` is not `0` when `n ≠ 0`. -/
theorem last_ne_zero {n : ℕ} (hn : n ≠ 0) : last n ≠ (0 : Fin (n + 1)) :=
  mt last_eq_zero_iff.1 hn

/-- The penultimate index of `Fin (n + 2)` is not `0` when `n ≠ 0`. -/
theorem castSucc_last_ne_zero {n : ℕ} (hn : n ≠ 0) : castSucc (last n) ≠ (0 : Fin (n + 2)) :=
  castSucc_ne_zero_iff.2 (last_ne_zero hn)

/-- The penultimate index of `Fin (n + 2)` is not `1` when `n ≠ 1`. -/
theorem castSucc_last_ne_one {n : ℕ} (hn : n ≠ 1) : castSucc (last n) ≠ (1 : Fin (n + 2)) :=
  ne_of_val_ne (by simp only [val_castSucc, val_last, val_one]; omega)

/-- The last index of `Fin (n + 2)` is not `1` when `n ≠ 0`. -/
theorem last_ne_one {n : ℕ} (hn : n ≠ 0) : last (n + 1) ≠ (1 : Fin (n + 2)) :=
  ne_of_val_ne (by simp only [val_last, val_one]; omega)

/-- An index of `Fin (n + 2)` that is at least `n` is the penultimate or the last one. -/
theorem eq_castSucc_last_or_eq_last {n : ℕ} {i : Fin (n + 2)} (hi : n ≤ i.val) :
    i = castSucc (last n) ∨ i = last (n + 1) := by
  have := i.isLt
  simp only [Fin.ext_iff, val_castSucc, val_last]
  omega

/-- The indices of `Fin (n + 2)` greater than `1` are the double successors of indices of
`Fin n`. -/
theorem exists_succ_succ_eq {n : ℕ} {j : Fin (n + 2)} :
    (∃ k : Fin n, k.succ.succ = j) ↔ 1 < j := by
  refine ⟨by rintro ⟨k, rfl⟩; simp [Fin.lt_def], fun hj => ?_⟩
  cases j using Fin.cases with
  | zero => exact absurd hj (by simp)
  | succ j =>
    cases j using Fin.cases with
    | zero => exact absurd hj (by simp)
    | succ k => exact ⟨k, rfl⟩

/-- A sum over `Fin (n + 1)` with the first and the last summands split off. -/
theorem sum_univ_eq_zero_add_last_add_sum_erase {n : ℕ} {M : Type*} [AddCommMonoid M]
    (hn : n ≠ 0)
    (f : Fin (n + 1) → M) :
    ∑ i, f i = f 0 + f (last n) + ∑ i ∈ (Finset.univ.erase 0).erase (last n), f i := by
  rw [add_assoc, Finset.add_sum_erase _ _
    (Finset.mem_erase.2 ⟨mt last_eq_zero_iff.1 hn, Finset.mem_univ _⟩),
    Finset.add_sum_erase _ _ (Finset.mem_univ 0)]

open Fin.NatCast in
/-- The cast of a natural number `0 < a < n` to `Fin n` is nonzero. -/
theorem natCast_ne_zero {n a : ℕ} [NeZero n] (ha : a ≠ 0) (han : a < n) : (a : Fin n) ≠ 0 :=
  natCast_eq_zero.not.2 (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero ha) han)

/-- The element `1` of `Fin m` has value `1` once `2 ≤ m`. Unlike `Fin.val_one`, this applies
when `m` is not syntactically of the form `n + 2`. -/
theorem val_one_of_two_le {m : ℕ} [NeZero m] (hm : 2 ≤ m) : ((1 : Fin m) : ℕ) = 1 := by
  rw [val_one', Nat.mod_eq_of_lt hm]

/-- Below the top element of `Fin n`, the order successor increments the value. -/
theorem val_orderSucc_of_lt {n : ℕ} {i : Fin n} (h : (i : ℕ) + 1 < n) :
    ((Order.succ i : Fin n) : ℕ) = (i : ℕ) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j : Fin m, i = j.castSucc := ⟨⟨(i : ℕ), by omega⟩, by ext; simp⟩
  simp

/-- At the top element of `Fin n` the order successor is that element itself. -/
theorem orderSucc_eq_self_of_not_lt {n : ℕ} {i : Fin n} (h : ¬(i : ℕ) + 1 < n) :
    (Order.succ i : Fin n) = i :=
  IsMax.succ_eq fun b _ => Fin.le_def.2 (by have := b.isLt; have := i.isLt; omega)

/-- Two insertions into a tuple commute, up to reindexing: inserting `a` at `i` after inserting
`b` at `j` is inserting `b` at `i.succAbove j` after inserting `a` at `j.predAbove i`.  This is the
dual of `Fin.removeNth_removeNth_eq_swap`. -/
theorem insertNth_insertNth {n : ℕ} {β : Sort*} (i : Fin (n + 2)) (j : Fin (n + 1)) (a b : β)
    (x : Fin n → β) :
    @insertNth _ (fun _ ↦ β) i a (@insertNth _ (fun _ ↦ β) j b x) =
      @insertNth _ (fun _ ↦ β) (i.succAbove j) b
        (@insertNth _ (fun _ ↦ β) (j.predAbove i) a x) := by
  rw [eq_insertNth_iff]
  refine ⟨by simp, ?_⟩
  funext k
  rcases eq_self_or_eq_succAbove (j.predAbove i) k with rfl | ⟨k, rfl⟩
  · simp only [removeNth, succAbove_succAbove_predAbove, insertNth_apply_same]
  · simp only [removeNth, succAbove_succAbove_succAbove_predAbove, insertNth_apply_succAbove]

/-- Inserting in the first block of an appended tuple is insertion in its first factor. -/
theorem insertNth_append_castAdd {n m : ℕ} {β : Sort*} (i : Fin (n + 1)) (a : β)
    (x : Fin n → β) (y : Fin m → β) :
    (Fin.cast (by omega : (n + 1) + m = (n + m) + 1) (i.castAdd m)).insertNth a
        (append x y) =
      append (i.insertNth a x) y ∘ Fin.cast (by omega) := by
  symm
  rw [eq_insertNth_iff]
  refine ⟨by simp, ?_⟩
  funext k
  induction k using Fin.addCases with
  | left k =>
      have hk : Fin.cast (by omega : (n + m) + 1 = (n + 1) + m)
          ((Fin.cast (by omega) (i.castAdd m)).succAbove (k.castAdd m)) =
          (i.succAbove k).castAdd m := by
        apply Fin.ext
        simp only [val_cast, val_succAbove, val_castAdd]
      simp [removeNth, Function.comp_apply, hk]
  | right k =>
      have hk : Fin.cast (by omega : (n + m) + 1 = (n + 1) + m)
          ((Fin.cast (by omega) (i.castAdd m)).succAbove (k.natAdd n)) =
          k.natAdd (n + 1) := by
        apply Fin.ext
        simp only [val_cast, val_succAbove, val_castAdd, val_natAdd]
        have := i.isLt
        split_ifs <;> omega
      simp [removeNth, Function.comp_apply, hk]

/-- Inserting in the second block of an appended tuple is insertion in its second factor. -/
theorem insertNth_append_natAdd {n m : ℕ} {β : Sort*} (i : Fin (m + 1)) (a : β)
    (x : Fin n → β) (y : Fin m → β) :
    (i.natAdd n).insertNth a (append x y) = append x (i.insertNth a y) := by
  symm
  rw [eq_insertNth_iff]
  refine ⟨by simp, ?_⟩
  funext k
  induction k using Fin.addCases with
  | left k => simp [removeNth, natAdd_succAbove_castAdd]
  | right k => simp [removeNth, natAdd_succAbove_natAdd]

/-! ### Inserting an entry into a tuple indexed by a sum of two blocks -/

/-- Inserting `x` at a slot `i` of the first block of `Fin ((k + 1) + (l + 1))` and restricting to
that block is inserting `x` at `i` into the restriction of `y` to its first `k` entries. -/
theorem insertNth_castAdd_comp_castAdd {α : Type*} {k l : ℕ} (i : Fin (k + 1)) (x : α)
    (y : Fin (k + 1 + l) → α) :
    (fun a : Fin (k + 1) => Fin.insertNth (α := fun _ => α)
      (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)) x y (Fin.castAdd (l + 1) a)) =
      Fin.insertNth (α := fun _ => α) i x
        (fun b : Fin k => y (Fin.cast (show k + (l + 1) = k + 1 + l by omega)
          (Fin.castAdd (l + 1) b))) := by
  rw [Fin.eq_insertNth_iff]
  refine ⟨Fin.insertNth_apply_same _ _ _, funext fun b => ?_⟩
  have : (Fin.castAdd (l + 1) (i.succAbove b) : Fin (k + 1 + l + 1)) =
      (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)).succAbove
        (Fin.cast (show k + (l + 1) = k + 1 + l by omega) (Fin.castAdd (l + 1) b)) := by
    ext
    simp only [Fin.val_castAdd, Fin.val_succAbove, Fin.val_cast]
  simp only [Fin.removeNth, this, Fin.insertNth_apply_succAbove]

/-- Inserting `x` at a slot of the first block of `Fin ((k + 1) + (l + 1))` leaves the entries of
the second block as the corresponding entries of `y`, shifted down by one. -/
@[simp]
theorem insertNth_castAdd_apply_natAdd {α : Type*} {k l : ℕ} (i : Fin (k + 1)) (x : α)
    (y : Fin (k + 1 + l) → α) (b : Fin (l + 1)) :
    Fin.insertNth (α := fun _ => α) (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)) x y
      (Fin.natAdd (k + 1) b) =
      y (Fin.cast (show k + (l + 1) = k + 1 + l by omega) (Fin.natAdd k b)) := by
  have : (Fin.natAdd (k + 1) b : Fin (k + 1 + l + 1)) =
      (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)).succAbove
        (Fin.cast (show k + (l + 1) = k + 1 + l by omega) (Fin.natAdd k b)) := by
    ext
    simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_succAbove, Fin.val_cast]
    split_ifs <;> omega
  rw [this, Fin.insertNth_apply_succAbove]

/-- Inserting `x` at a slot of the second block of `Fin (k + (l + 1))` leaves the entries of the
first block as the corresponding entries of `y`. -/
@[simp]
theorem insertNth_natAdd_apply_castAdd {α : Type*} {k l : ℕ} (i : Fin (l + 1)) (x : α)
    (y : Fin (k + l) → α) (a : Fin k) :
    Fin.insertNth (α := fun _ => α) (Fin.natAdd k i : Fin (k + l + 1)) x y
      (Fin.castAdd (l + 1) a) = y (Fin.castAdd l a) := by
  have : (Fin.castAdd (l + 1) a : Fin (k + l + 1)) =
      (Fin.natAdd k i : Fin (k + l + 1)).succAbove (Fin.castAdd l a) := by
    ext
    simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_succAbove]
    split_ifs <;> omega
  rw [this, Fin.insertNth_apply_succAbove]

/-- Inserting `x` at a slot `i` of the second block of `Fin (k + (l + 1))` and restricting to that
block is inserting `x` at `i` into the restriction of `y` to its last `l` entries. -/
theorem insertNth_natAdd_comp_natAdd {α : Type*} {k l : ℕ} (i : Fin (l + 1)) (x : α)
    (y : Fin (k + l) → α) :
    (fun b : Fin (l + 1) => Fin.insertNth (α := fun _ => α)
      (Fin.natAdd k i : Fin (k + l + 1)) x y (Fin.natAdd k b)) =
      Fin.insertNth (α := fun _ => α) i x (fun c : Fin l => y (Fin.natAdd k c)) := by
  rw [Fin.eq_insertNth_iff]
  refine ⟨Fin.insertNth_apply_same _ _ _, funext fun c => ?_⟩
  have : (Fin.natAdd k (i.succAbove c) : Fin (k + l + 1)) =
      (Fin.natAdd k i : Fin (k + l + 1)).succAbove (Fin.natAdd k c) := by
    ext
    simp only [Fin.val_natAdd, Fin.val_succAbove]
    split_ifs <;> omega
  simp only [Fin.removeNth, this, Fin.insertNth_apply_succAbove]

/-- An open interval in `Fin n` with `n ≤ 2` is empty. -/
theorem Ioo_eq_empty_of_le_two {n : ℕ} (hn : n ≤ 2) (a b : Fin n) : Finset.Ioo a b = ∅ :=
  Finset.card_eq_zero.1 (by rw [Fin.card_Ioo]; omega)

/-- A finset inside an open interval in `Fin n` with `n ≤ 2` is empty. -/
theorem eq_empty_of_subset_Ioo_of_le_two {n : ℕ} (hn : n ≤ 2) {a b : Fin n}
    {s : Finset (Fin n)} (hs : s ⊆ Finset.Ioo a b) : s = ∅ :=
  Finset.subset_empty.1 (hs.trans (Ioo_eq_empty_of_le_two hn a b).subset)

end Fin

namespace TauCeti

/-- After swapping coordinates zero and `d`, the entries of `Fin.cons a y` at indices at least
`d` vanish exactly when `a` and the entries of `y` at indices at least `d` vanish. -/
theorem forall_cons_swap_eq_zero_iff {α : Type*} [Zero α] {n d : ℕ}
    (hd : d ≤ n) (a : α) (y : Fin n → α) :
    (∀ i : Fin (n + 1), d ≤ i.val →
      (Fin.cons a y : Fin (n + 1) → α) (Equiv.swap 0 ⟨d, by omega⟩ i) = 0) ↔
      a = 0 ∧ ∀ j : Fin n, d ≤ j.val → y j = 0 := by
  constructor
  · intro h
    refine ⟨?_, fun j hj ↦ ?_⟩
    · simpa using h ⟨d, by omega⟩ (by simp)
    · have h0 : j.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero j
      have hd' : j.succ ≠ (⟨d, by omega⟩ : Fin (n + 1)) := by
        intro heq
        have := congrArg Fin.val heq
        simp only [Fin.val_succ] at this
        omega
      simpa [Equiv.swap_apply_of_ne_of_ne h0 hd'] using h j.succ (by simp; omega)
  · rintro ⟨ha, hy⟩ i hi
    by_cases hid : i = ⟨d, by omega⟩
    · rw [hid, Equiv.swap_apply_right, Fin.cons_zero]
      exact ha
    have hi0 : i ≠ 0 := by
      intro h0
      subst i
      have : d = 0 := by simpa using hi
      apply hid
      ext
      simp [this]
    rw [Equiv.swap_apply_of_ne_of_ne hi0 hid]
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (i := i) hi0
    have hne : j.val + 1 ≠ d := fun h ↦ hid (Fin.ext h)
    exact hy j (by simp only [Fin.val_succ] at hi; omega)

/-- A decreasing parent table gives a word carrying its root to every vertex. -/
theorem exists_foldl_eq_of_parent {n : ℕ} {J : Type*}
    (step : Fin (n + 1) → J → Fin (n + 1))
    (parent : Fin n → Fin (n + 1)) (edge : Fin n → J)
    (hparent : ∀ a, (parent a : ℕ) < (a.succ : ℕ))
    (hstep : ∀ a, step (parent a) (edge a) = a.succ) (a : Fin (n + 1)) :
    ∃ l : List J, l.foldl step 0 = a := by
  have aux : ∀ m, ∀ hm : m < n + 1,
      ∃ l : List J, l.foldl step 0 = (⟨m, hm⟩ : Fin (n + 1)) := by
    intro m hm
    induction m using Nat.strong_induction_on with
    | _ m ih =>
        by_cases hzero : m = 0
        · subst m
          exact ⟨[], rfl⟩
        · let c : Fin n := ⟨m - 1, by omega⟩
          have hsucc : c.succ = (⟨m, hm⟩ : Fin (n + 1)) := by
            apply Fin.ext
            simp [c]
            omega
          obtain ⟨l, hl⟩ := ih (parent c)
            (by
              have hlt := hparent c
              have hval : (c.succ : ℕ) = m := congrArg Fin.val hsucc
              rwa [hval] at hlt)
            (parent c).isLt
          refine ⟨l ++ [edge c], ?_⟩
          rw [List.foldl_append, hl]
          simpa only [List.foldl_cons, List.foldl_nil, hstep] using hsucc
  exact aux a a.isLt

open Set

/-- No value of a monotone `Fin` family lies strictly between consecutive entries. -/
theorem not_mem_Ioo_castSucc_succ {β : Type*} [Preorder β] {n : ℕ} (a : Fin (n + 1) → β)
    (ha : Monotone a) (i : Fin n) (k : Fin (n + 1)) :
    a k ∉ Set.Ioo (a i.castSucc) (a i.succ) := by
  intro hk
  by_cases hki : k ≤ i.castSucc
  · exact (not_lt_of_ge (ha hki)) hk.1
  · have hik : i.succ ≤ k := by
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] at hki ⊢
      omega
    exact (not_lt_of_ge (ha hik)) hk.2

/-- A point between the first and last values of a `Fin` family with at least two entries lies
between consecutive values. The family need not be monotone. -/
theorem exists_mem_Icc_castSucc_succ {β : Type*} [LinearOrder β] {n : ℕ}
    (a : Fin (n + 1) → β) (hn : n ≠ 0)
    {x : β} (hx : x ∈ Set.Icc (a 0) (a (Fin.last n))) :
    ∃ i : Fin n, x ∈ Set.Icc (a i.castSucc) (a i.succ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h : ∃ i : Fin (n + 1), x ≤ a i.succ := ⟨Fin.last n, hx.2⟩
  -- Formal source: Mathlib's Fin.find least-index API.
  refine ⟨Fin.find _ h, ?_, Fin.find_spec h⟩
  cases hi : Fin.find _ h using Fin.cases with
  | zero => exact hx.1
  | succ i =>
    exact (not_le.mp (Fin.find_min h (j := i.castSucc)
      (by rw [hi]; exact i.castSucc_lt_succ))).le

/-- **Adding one in `Fin n` never returns to the same element** when `2 ≤ n`. -/
theorem add_one_ne_self {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) : i + 1 ≠ i := by
  intro h
  have hone : (1 : Fin n) = 0 := by
    apply add_left_cancel (a := i)
    simpa using h
  have hval := congrArg Fin.val hone
  simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at hval

/-- **Adding one twice in `Fin n` never returns to the same element** when `3 ≤ n`. -/
theorem add_one_add_one_ne_self {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : Fin n) :
    i + 1 + 1 ≠ i := by
  intro h
  have htwo : (1 + 1 : Fin n) = 0 := by
    apply add_left_cancel (a := i)
    simpa [add_assoc] using h
  have hval := congrArg Fin.val htwo
  simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < n)] at hval

/-- Subtracting one in `Fin n` never returns to the same element when `2 ≤ n`. -/
theorem sub_one_ne_self {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) : i - 1 ≠ i := fun h ↦
  add_one_ne_self hn (i - 1) (by rw [sub_add_cancel, h])

/-- In `Fin n` with `3 ≤ n`, the successor and the predecessor of an element are distinct. -/
theorem add_one_ne_sub_one {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : Fin n) : i + 1 ≠ i - 1 :=
  mt eq_sub_iff_add_eq.1 (add_one_add_one_ne_self hn i)

/-- **A function on `Fin (n + 1)` unchanged by adding one is constant.** -/
theorem apply_eq_apply_zero_of_add_one {β : Type*} {n : ℕ} {f : Fin (n + 1) → β}
    (h : ∀ i, f (i + 1) = f i) (i : Fin (n + 1)) : f i = f 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => rw [← Fin.coeSucc_eq_succ, h, ih]

/-- **Adding one in `Fin n` flips the sign `(-1) ^ ·` read off the value** when `n` is even.  The
wraparound at the last index respects the sign exactly because `n` is even. -/
theorem neg_one_pow_val_add_one {M : Type*} [Monoid M] [HasDistribNeg M] {n : ℕ} [NeZero n]
    (hn : Even n) (i : Fin n) : (-1 : M) ^ ((i + 1 : Fin n) : ℕ) = -(-1 : M) ^ (i : ℕ) := by
  have hval : ((i + 1 : Fin n) : ℕ) = (i.val + 1) % n := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [hval]
  rcases Nat.lt_or_ge (i.val + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_succ, mul_neg_one]
  · have hi : i.val + 1 = n := by have := i.isLt; omega
    have hn' : Even (i.val + 1) := by rw [hi]; exact hn
    have hodd : Odd i.val := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hn')
    rw [hi, Nat.mod_self, pow_zero, hodd.neg_one_pow, neg_neg]

end TauCeti

namespace Equiv.Perm

/-- A permutation of `Fin 2` is either the identity or the transposition. -/
theorem eq_one_or_swap_fin_two (e : Equiv.Perm (Fin 2)) :
    e = 1 ∨ e = Equiv.swap 0 1 := by
  by_cases h0 : e 0 = 0
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · apply Fin.eq_one_of_ne_zero
      intro h1
      exact Fin.zero_ne_one (e.injective (h1.trans h0.symm)).symm
  · right
    have h0' : e 0 = 1 := Fin.eq_one_of_ne_zero _ h0
    apply Equiv.ext
    intro i
    fin_cases i
    · simpa using h0'
    · have h1 : e 1 = 0 := by
        by_contra h
        have h1' : e 1 = 1 := Fin.eq_one_of_ne_zero _ h
        exact Fin.zero_ne_one (e.injective (h1'.trans h0'.symm)).symm
      simpa using h1

/-- The permutations of `Fin 2`, as a finite set, are the identity and the transposition. -/
theorem univ_fin_two [Fintype (Equiv.Perm (Fin 2))] :
    (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
    {1, Equiv.swap 0 1} := by
  classical
  ext e
  simpa using e.eq_one_or_swap_fin_two

end Equiv.Perm

namespace TauCeti

/-- **A shifted indicator picks out one summand.** Summing `f` over `Fin n` against the indicator
of `b = k + j` gives `f` at the index `b - j` when that is a valid index and `j ≤ b`, and `0`
otherwise. -/
theorem sum_ite_val_add {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) (b j : ℕ) :
    ∑ k : Fin n, (if b = (k : ℕ) + j then f k else 0)
      = if h : b - j < n ∧ j ≤ b then f ⟨b - j, h.1⟩ else 0 := by
  by_cases h : b - j < n ∧ j ≤ b
  · have hb : ∀ k : Fin n, (b = (k : ℕ) + j) = (k = (⟨b - j, h.1⟩ : Fin n)) := by
      intro k
      have := h.2
      simp only [Fin.ext_iff, eq_iff_iff]
      omega
    simp only [hb, dite_eq_left h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · rw [dite_eq_right h, Finset.sum_eq_zero]
    intro k _
    have := k.isLt
    exact ite_eq_right (by omega)

/-! ### Cyclic index arithmetic in `Fin 3` -/

/-- **A distinct index of `Fin 3` is one of the two shifts of the other.** -/
theorem eq_add_one_or_eq_add_two_fin_three {i j : Fin 3} (h : i ≠ j) : i = j + 1 ∨ i = j + 2 := by
  revert h; revert i j; decide

/-- **Shifting an index of `Fin 3` by one twice is shifting it by two.** -/
theorem add_one_add_one_fin_three (j : Fin 3) : j + 1 + 1 = j + 2 := by revert j; decide

/-- **Shifting an index of `Fin 3` by one and then by two returns to it.** -/
theorem add_one_add_two_fin_three (j : Fin 3) : j + 1 + 2 = j := by revert j; decide

/-- **Shifting an index of `Fin 3` by two and then by one returns to it.** -/
theorem add_two_add_one_fin_three (j : Fin 3) : j + 2 + 1 = j := by revert j; decide

/-- **Shifting an index of `Fin 3` by two twice is shifting it by one.** -/
theorem add_two_add_two_fin_three (j : Fin 3) : j + 2 + 2 = j + 1 := by revert j; decide

/-- **A sum over `Fin 3` read off starting from an arbitrary index.** -/
theorem sum_fin_three_rotate {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) (j : Fin 3) :
    ∑ m, f m = f j + f (j + 1) + f (j + 2) := by
  have h : ∑ m : Fin 3, f (j + m) = ∑ m : Fin 3, f m :=
    Fintype.sum_equiv (Equiv.addLeft j) _ _ fun _ => rfl
  rw [← h, Fin.sum_univ_three, add_zero]

end TauCeti
end
end GeometryLiteralSource009

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Data.Fin.Basic"

section GeometryLiteralSource010
/- Original source: TauCeti.AlgebraicTopology.CechNerve -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Homotopies between maps of Čech nerves, and maps into a Čech nerve

Let `F G : f ⟶ g` be two morphisms of arrows with the same component `F.right = G.right` on the
targets. The induced maps of Čech nerves `Arrow.mapCechNerve F` and `Arrow.mapCechNerve G` are
simplicially homotopic. In degree `n` the `i`-th component of the homotopy
`f.cechNerve _⦋n⦌ ⟶ g.cechNerve _⦋n + 1⦌` repeats the `i`-th factor of the wide pullback and
applies `F.left` to the factors in positions `≤ i` and `G.left` to the others.

Applied to the Čech nerve of a family of objects over a terminal object, this says that the map
induced on Čech nerves by a refinement of covers does not depend on the chosen refinement map, up
to homotopy. This is the input for `TauCeti.CategoryTheory.cechComplexMapHomotopy`, which shows
that the maps induced on Čech complexes by two refinement maps are homotopic.

The simplices of `cechNerveTerminalFrom U`, the Čech nerve of `U ⟶ ⊤_ C` with `⦋n⦌ ↦ Uⁿ⁺¹`, are
determined by their vertices, and every family of vertices is the family of vertices of a simplex
(`CategoryTheory.cechNerveTerminalFrom.hom_ext` and `CategoryTheory.cechNerveTerminalFrom.lift`).

For an object `T`, the morphisms from `T` into the Čech nerve of `f` form an augmented simplicial
set over the morphisms `T ⟶ f.right` which lift along `f.hom`. It has an extra degeneracy, which
inserts a chosen lift of the base as a new first factor; this is Mathlib's extra degeneracy of the
Čech nerve of a split epimorphism, `Arrow.AugmentedCechNerve.extraDegeneracy`, with the section
chosen separately over each morphism. For the map from the disjoint union of a family of open sets
and `T` a topological simplex, it shows that the rows of the Čech--singular double complex resolve
the singular chains subordinate to the family.

## Main definitions

* `CategoryTheory.Arrow.mapCechNerveHomotopy`: the simplicial homotopy between
  `Arrow.mapCechNerve F` and `Arrow.mapCechNerve G` for `F.right = G.right`.
* `CategoryTheory.Arrow.augmentedCechNerveMapsFrom`: the morphisms from `T` into the Čech nerve,
  augmented over the morphisms which lift along `f.hom`.
* `CategoryTheory.Arrow.AugmentedCechNerveMapsFrom.extraDegeneracy`: its extra degeneracy.
* `CategoryTheory.cechNerveTerminalFrom.lift`: the simplex of `cechNerveTerminalFrom U` with given
  vertices.

## References

* R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer, 1977,
  Exercise III.4.4, for the independence of the map induced on Čech cohomology by a refinement
  from the refinement map.
-/

public section

open CategoryTheory Limits Opposite

open scoped Simplicial

universe v u

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] {f g : Arrow C}
  [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) ↦ f.left) fun _ ↦ f.hom]
  [∀ n : ℕ, HasWidePullback g.right (fun _ : Fin (n + 1) ↦ g.left) fun _ ↦ g.hom]

/-- The `i`-th component `f.cechNerve _⦋n⦌ ⟶ g.cechNerve _⦋n + 1⦌` of the homotopy between
`mapCechNerve F` and `mapCechNerve G`: its `j`-th factor is the `i.predAbove j`-th factor of the
source followed by `F.left` if `j ≤ i` and by `G.left` otherwise. -/
private noncomputable def mapCechNerveHomotopyApp (F G : f ⟶ g) (h : F.right = G.right) {n : ℕ}
    (i : Fin (n + 1)) : f.cechNerve _⦋n⦌ ⟶ g.cechNerve _⦋n + 1⦌ :=
  WidePullback.lift (WidePullback.base _ ≫ F.right)
    (fun j ↦ WidePullback.π _ (i.predAbove j) ≫ if j ≤ i.castSucc then F.left else G.left)
    (fun j ↦ by split_ifs <;> simp [h])

variable (F G : f ⟶ g) (h : F.right = G.right)

@[reassoc (attr := simp)]
private theorem mapCechNerveHomotopyApp_π {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    mapCechNerveHomotopyApp F G h i ≫ WidePullback.π _ j =
      WidePullback.π _ (i.predAbove j) ≫ if j ≤ i.castSucc then F.left else G.left :=
  WidePullback.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
private theorem mapCechNerveHomotopyApp_base {n : ℕ} (i : Fin (n + 1)) :
    mapCechNerveHomotopyApp F G h i ≫ WidePullback.base _ = WidePullback.base _ ≫ F.right :=
  WidePullback.lift_base _ _ _ _

omit [∀ n : ℕ, HasWidePullback g.right (fun _ : Fin (n + 1) ↦ g.left) fun _ ↦ g.hom] in
/-- Two composites `π a ≫ (if p then F.left else G.left)` out of a wide pullback agree when the
factors `a`, `b` and the conditions `p`, `q` do. -/
private theorem π_comp_ite_congr {n : ℕ} {a b : Fin (n + 1)} {p q : Prop} [Decidable p]
    [Decidable q] (hab : a = b) (hpq : p ↔ q) :
    (WidePullback.π (fun _ : Fin (n + 1) ↦ f.hom) a ≫ if p then F.left else G.left) =
      WidePullback.π (fun _ : Fin (n + 1) ↦ f.hom) b ≫ if q then F.left else G.left := by
  subst hab
  simp only [hpq]

/- The five proofs below are the literal tactic expansion of the original local
`cech_nerve_homotopy_ext` macro. Their statements and mathematical steps are unchanged. -/

/-- **Morphisms of arrows with the same target component induce homotopic maps of Čech
nerves.** If `F.right = G.right`, then `Arrow.mapCechNerve F` and `Arrow.mapCechNerve G` are
simplicially homotopic. -/
noncomputable def mapCechNerveHomotopy :
    SimplicialObject.Homotopy (mapCechNerve F) (mapCechNerve G) where
  h i := mapCechNerveHomotopyApp F G h i
  h_zero_comp_δ_zero n := by
    apply WidePullback.hom_ext
    · intro j
      simp [SimplicialObject.δ, SimplexCategory.δ]
    · simp [SimplicialObject.δ, h]
  h_last_comp_δ_last n := by
    apply WidePullback.hom_ext
    · intro j
      simp [SimplicialObject.δ, SimplexCategory.δ, Fin.le_last]
    · simp [SimplicialObject.δ]
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply WidePullback.hom_ext
    · intro k
      simp only [SimplicialObject.δ, SimplicialObject.σ, SimplexCategory.δ, SimplexCategory.σ,
        SimplexCategory.mkHom, cechNerve_map, Quiver.Hom.unop_op, SimplexCategory.Hom.toOrderHom_mk,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, Fin.predAboveOrderHom_coe,
        Category.assoc, WidePullback.lift_π, WidePullback.lift_π_assoc, mapCechNerveHomotopyApp_π]
      refine π_comp_ite_congr _ _ ?_ ?_ <;>
        simp only [Fin.ext_iff, Fin.le_def, Fin.lt_def, Fin.val_succAbove, Fin.val_predAbove,
          Fin.val_castSucc, Fin.val_succ] at * <;>
        split_ifs at * <;> omega
    · simp [SimplicialObject.δ, SimplicialObject.σ]
  h_succ_comp_δ_castSucc_succ j := by
    apply WidePullback.hom_ext
    · intro k
      simp only [SimplicialObject.δ, SimplicialObject.σ, SimplexCategory.δ, SimplexCategory.σ,
        SimplexCategory.mkHom, cechNerve_map, Quiver.Hom.unop_op, SimplexCategory.Hom.toOrderHom_mk,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, Fin.predAboveOrderHom_coe,
        Category.assoc, WidePullback.lift_π, WidePullback.lift_π_assoc, mapCechNerveHomotopyApp_π]
      refine π_comp_ite_congr _ _ ?_ ?_ <;>
        simp only [Fin.ext_iff, Fin.le_def, Fin.lt_def, Fin.val_succAbove, Fin.val_predAbove,
          Fin.val_castSucc, Fin.val_succ] at * <;>
        split_ifs at * <;> omega
    · simp [SimplicialObject.δ, SimplicialObject.σ]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply WidePullback.hom_ext
    · intro k
      simp only [SimplicialObject.δ, SimplicialObject.σ, SimplexCategory.δ, SimplexCategory.σ,
        SimplexCategory.mkHom, cechNerve_map, Quiver.Hom.unop_op, SimplexCategory.Hom.toOrderHom_mk,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, Fin.predAboveOrderHom_coe,
        Category.assoc, WidePullback.lift_π, WidePullback.lift_π_assoc, mapCechNerveHomotopyApp_π]
      refine π_comp_ite_congr _ _ ?_ ?_ <;>
        simp only [Fin.ext_iff, Fin.le_def, Fin.lt_def, Fin.val_succAbove, Fin.val_predAbove,
          Fin.val_castSucc, Fin.val_succ] at * <;>
        split_ifs at * <;> omega
    · simp [SimplicialObject.δ, SimplicialObject.σ]
  h_comp_σ_castSucc_of_le i j hij := by
    apply WidePullback.hom_ext
    · intro k
      simp only [SimplicialObject.δ, SimplicialObject.σ, SimplexCategory.δ, SimplexCategory.σ,
        SimplexCategory.mkHom, cechNerve_map, Quiver.Hom.unop_op, SimplexCategory.Hom.toOrderHom_mk,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, Fin.predAboveOrderHom_coe,
        Category.assoc, WidePullback.lift_π, WidePullback.lift_π_assoc, mapCechNerveHomotopyApp_π]
      refine π_comp_ite_congr _ _ ?_ ?_ <;>
        simp only [Fin.ext_iff, Fin.le_def, Fin.lt_def, Fin.val_succAbove, Fin.val_predAbove,
          Fin.val_castSucc, Fin.val_succ] at * <;>
        split_ifs at * <;> omega
    · simp [SimplicialObject.δ, SimplicialObject.σ]
  h_comp_σ_succ_of_lt i j hji := by
    apply WidePullback.hom_ext
    · intro k
      simp only [SimplicialObject.δ, SimplicialObject.σ, SimplexCategory.δ, SimplexCategory.σ,
        SimplexCategory.mkHom, cechNerve_map, Quiver.Hom.unop_op, SimplexCategory.Hom.toOrderHom_mk,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, Fin.predAboveOrderHom_coe,
        Category.assoc, WidePullback.lift_π, WidePullback.lift_π_assoc, mapCechNerveHomotopyApp_π]
      refine π_comp_ite_congr _ _ ?_ ?_ <;>
        simp only [Fin.ext_iff, Fin.le_def, Fin.lt_def, Fin.val_succAbove, Fin.val_predAbove,
          Fin.val_castSucc, Fin.val_succ] at * <;>
        split_ifs at * <;> omega
    · simp [SimplicialObject.δ, SimplicialObject.σ]

/-- The `j`-th factor of the `i`-th component of `mapCechNerveHomotopy F G h` is the
`i.predAbove j`-th factor of the source followed by `F.left` if `j ≤ i` and by `G.left`
otherwise. -/
@[reassoc (attr := simp)]
theorem mapCechNerveHomotopy_h_π {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (mapCechNerveHomotopy F G h).h i ≫ WidePullback.π _ j =
      WidePullback.π _ (i.predAbove j) ≫ if j ≤ i.castSucc then F.left else G.left :=
  mapCechNerveHomotopyApp_π F G h i j

/-- Every component of `mapCechNerveHomotopy F G h` lies over `F.right = G.right`. -/
@[reassoc (attr := simp)]
theorem mapCechNerveHomotopy_h_base {n : ℕ} (i : Fin (n + 1)) :
    (mapCechNerveHomotopy F G h).h i ≫ WidePullback.base _ = WidePullback.base _ ≫ F.right :=
  mapCechNerveHomotopyApp_base F G h i

end CategoryTheory.Arrow

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] (f : Arrow C)
  [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) ↦ f.left) fun _ ↦ f.hom]

/-- The morphisms from `T` into the Čech nerve of `f`, augmented over the morphisms
`T ⟶ f.right` which lift along `f.hom`. The augmentation composes with the projection
`WidePullback.base`. -/
@[expose] noncomputable def augmentedCechNerveMapsFrom (T : C) :
    SimplicialObject.Augmented (Type v) where
  left := f.cechNerve ⋙ coyoneda.obj (op T)
  right := {g : T ⟶ f.right // ∃ l : T ⟶ f.left, l ≫ f.hom = g}
  hom :=
    { app n := ↾fun σ ↦ ⟨σ ≫ WidePullback.base _, σ ≫ WidePullback.π _ 0, by simp⟩
      naturality n m θ := by
        ext σ
        simp }

/-- The simplicial operators act on maps into the Čech nerve by postcomposition. -/
@[simp]
theorem augmentedCechNerveMapsFrom_left_map (T : C) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (σ : T ⟶ f.cechNerve.obj n) :
    (f.augmentedCechNerveMapsFrom T).left.map θ σ = σ ≫ f.cechNerve.map θ :=
  (rfl)

/-- The augmentation sends a map into the Čech nerve to its composite with the base.

The source and target of `ConcreteCategory.hom` are given explicitly, as `left.obj n` and
`right`, so that the left-hand side is in simp normal form: elaborated directly they would be
`(𝟭 _).obj left` and `(const.obj right).obj n`, which simp rewrites first. -/
@[simp]
theorem augmentedCechNerveMapsFrom_hom_app_coe (T : C) (n : SimplexCategoryᵒᵖ)
    (σ : T ⟶ f.cechNerve.obj n) :
    Subtype.val (ConcreteCategory.hom (X := (f.augmentedCechNerveMapsFrom T).left.obj n)
      (Y := (f.augmentedCechNerveMapsFrom T).right) ((f.augmentedCechNerveMapsFrom T).hom.app n)
      σ) = σ ≫ WidePullback.base _ :=
  (rfl)

namespace AugmentedCechNerveMapsFrom

variable {f} {T : C}

omit [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) ↦ f.left) fun _ ↦ f.hom] in
/-- A chosen lift along `f.hom` of a morphism which admits one. -/
private noncomputable def lift (g : {g : T ⟶ f.right // ∃ l : T ⟶ f.left, l ≫ f.hom = g}) :
    T ⟶ f.left :=
  g.2.choose

omit [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) ↦ f.left) fun _ ↦ f.hom] in
@[reassoc (attr := simp)]
private theorem lift_comp (g : {g : T ⟶ f.right // ∃ l : T ⟶ f.left, l ≫ f.hom = g}) :
    lift g ≫ f.hom = g.1 :=
  g.2.choose_spec

/-- The section of the augmentation in degree `0`: a liftable morphism goes to its chosen lift. -/
private noncomputable def sectionFun (g : {g : T ⟶ f.right // ∃ l : T ⟶ f.left, l ≫ f.hom = g}) :
    T ⟶ f.cechNerve _⦋0⦌ :=
  WidePullback.lift g.1 (fun _ ↦ lift g) (by simp)

/-- The extra degeneracy on maps into the Čech nerve: it inserts the chosen lift of the base
as the new `0`-th factor. -/
private noncomputable def sFun {n : ℕ} (σ : T ⟶ f.cechNerve _⦋n⦌) : T ⟶ f.cechNerve _⦋n + 1⦌ :=
  WidePullback.lift (σ ≫ WidePullback.base _)
    (Fin.cases (lift ⟨σ ≫ WidePullback.base _, σ ≫ WidePullback.π _ 0, by simp⟩)
      fun i ↦ σ ≫ WidePullback.π _ i)
    fun i ↦ by cases i using Fin.cases <;> simp

@[reassoc (attr := simp)]
private theorem sectionFun_π (g : {g : T ⟶ f.right // ∃ l : T ⟶ f.left, l ≫ f.hom = g})
    (i : Fin 1) :
    sectionFun g ≫ WidePullback.π _ i = lift g :=
  WidePullback.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
private theorem sectionFun_base (g : {g : T ⟶ f.right // ∃ l : T ⟶ f.left, l ≫ f.hom = g}) :
    sectionFun g ≫ WidePullback.base _ = g.1 :=
  WidePullback.lift_base _ _ _ _

@[reassoc (attr := simp)]
private theorem sFun_π_zero {n : ℕ} (σ : T ⟶ f.cechNerve _⦋n⦌) :
    sFun σ ≫ WidePullback.π _ 0 =
      lift ⟨σ ≫ WidePullback.base _, σ ≫ WidePullback.π _ 0, by simp⟩ :=
  WidePullback.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
private theorem sFun_π_succ {n : ℕ} (σ : T ⟶ f.cechNerve _⦋n⦌) (i : Fin (n + 1)) :
    sFun σ ≫ WidePullback.π _ i.succ = σ ≫ WidePullback.π _ i :=
  WidePullback.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
private theorem sFun_base {n : ℕ} (σ : T ⟶ f.cechNerve _⦋n⦌) :
    sFun σ ≫ WidePullback.base _ = σ ≫ WidePullback.base _ :=
  WidePullback.lift_base _ _ _ _

private theorem sFun_zero_comp_δ_one (σ : T ⟶ f.cechNerve _⦋0⦌) :
    sFun σ ≫ f.cechNerve.δ 1 =
      sectionFun ⟨σ ≫ WidePullback.base _, σ ≫ WidePullback.π _ 0, by simp⟩ := by
  apply WidePullback.hom_ext
  · intro j
    fin_cases j
    simp [SimplicialObject.δ, SimplexCategory.δ]
  · simp [SimplicialObject.δ]

private theorem sFun_comp_δ_zero {n : ℕ} (σ : T ⟶ f.cechNerve _⦋n⦌) :
    sFun σ ≫ f.cechNerve.δ 0 = σ := by
  apply WidePullback.hom_ext
  · intro j
    simp [SimplicialObject.δ, SimplexCategory.δ]
  · simp [SimplicialObject.δ]

private theorem sFun_comp_δ_succ {n : ℕ} (i : Fin (n + 2)) (σ : T ⟶ f.cechNerve _⦋n + 1⦌) :
    sFun σ ≫ f.cechNerve.δ i.succ = sFun (σ ≫ f.cechNerve.δ i) := by
  apply WidePullback.hom_ext
  · intro j
    induction j using Fin.cases <;> simp [SimplicialObject.δ, SimplexCategory.δ]
  · simp [SimplicialObject.δ]

private theorem sFun_comp_σ_succ {n : ℕ} (i : Fin (n + 1)) (σ : T ⟶ f.cechNerve _⦋n⦌) :
    sFun σ ≫ f.cechNerve.σ i.succ = sFun (σ ≫ f.cechNerve.σ i) := by
  apply WidePullback.hom_ext
  · intro j
    induction j using Fin.cases <;> simp [SimplicialObject.σ, SimplexCategory.σ]
  · simp [SimplicialObject.σ]

end AugmentedCechNerveMapsFrom

open AugmentedCechNerveMapsFrom in
/-- **Maps into a Čech nerve over liftable maps have an extra degeneracy.** -/
noncomputable def AugmentedCechNerveMapsFrom.extraDegeneracy (T : C) :
    SimplicialObject.Augmented.ExtraDegeneracy (f.augmentedCechNerveMapsFrom T) where
  s' := ↾sectionFun
  s _ := ↾sFun
  -- The simplices of `f.augmentedCechNerveMapsFrom T` are morphisms into the Čech nerve and its
  -- simplicial operators act by postcomposition, so each identity is the corresponding identity
  -- for morphisms into the Čech nerve.
  s'_comp_ε := by
    ext g
    exact Subtype.ext (sectionFun_base g)
  s₀_comp_δ₁ := by
    ext σ
    exact sFun_zero_comp_δ_one σ
  s_comp_δ₀ n := by
    ext σ
    exact sFun_comp_δ_zero σ
  s_comp_δ n i := by
    ext σ
    exact sFun_comp_δ_succ i σ
  s_comp_σ n i := by
    ext σ
    exact sFun_comp_σ_succ i σ

end CategoryTheory.Arrow

namespace CategoryTheory.cechNerveTerminalFrom

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] (U : C)

/-- The `i`-th vertex of a simplex of `cechNerveTerminalFrom U` is its `i`-th factor. -/
@[simp]
theorem map_const_π {m : ℕ} (i : Fin (⦋m⦌.len + 1)) :
    (cechNerveTerminalFrom U).map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op ≫
      Pi.π (fun _ : Fin (⦋0⦌.len + 1) ↦ U) 0 = Pi.π (fun _ : Fin (⦋m⦌.len + 1) ↦ U) i := by
  simp [cechNerveTerminalFrom]

/-- Two morphisms into `(cechNerveTerminalFrom U) _⦋m⦌` agree if they have the same vertices. -/
theorem hom_ext {Z : C} {m : ℕ} {a b : Z ⟶ (cechNerveTerminalFrom U) _⦋m⦌}
    (h : ∀ i, a ≫ (cechNerveTerminalFrom U).map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op =
      b ≫ (cechNerveTerminalFrom U).map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op) : a = b :=
  Pi.hom_ext _ _ fun i ↦ by
    -- The source of `Pi.π` is `(cechNerveTerminalFrom U) _⦋0⦌` only up to unfolding, which
    -- blocks rewriting with associativity, so the composites are reassociated as terms.
    have e := map_const_π U i
    exact (congrArg (a ≫ ·) e.symm).trans <| (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (h i)).trans <| (Category.assoc _ _ _).trans (congrArg (b ≫ ·) e)

/-- The morphism into `(cechNerveTerminalFrom U) _⦋m⦌` with prescribed vertices `a i`. -/
noncomputable def lift {Z : C} {m : ℕ} (a : Fin (m + 1) → (Z ⟶ (cechNerveTerminalFrom U) _⦋0⦌)) :
    Z ⟶ (cechNerveTerminalFrom U) _⦋m⦌ :=
  Pi.lift fun i ↦ a i ≫ Pi.π (fun _ : Fin 1 ↦ U) 0

/-- The `i`-th vertex of `lift U a` is `a i`. -/
@[reassoc (attr := simp)]
theorem lift_map_const {Z : C} {m : ℕ} (a : Fin (m + 1) → (Z ⟶ (cechNerveTerminalFrom U) _⦋0⦌))
    (i : Fin (m + 1)) :
    lift U a ≫ (cechNerveTerminalFrom U).map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op = a i :=
  Pi.hom_ext _ _ fun k ↦ by
    simp [lift, cechNerveTerminalFrom, Fin.fin_one_eq_zero k]

end CategoryTheory.cechNerveTerminalFrom
end
end GeometryLiteralSource010

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.AlgebraicTopology.CechNerve"

section GeometryLiteralSource011
/- Original source: TauCeti.CategoryTheory.Limits.FormalCoproducts.Cech -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Naturality of the Čech object of a formal coproduct

Mathlib identifies the Čech object `U.cech` of a formal coproduct `U` with the Čech nerve of the
morphism from `U` to a terminal object (`CategoryTheory.Limits.FormalCoproduct.cechIsoCechNerve`).
This file records that the identification is natural in `U`: the map of Čech objects induced by a
morphism `φ : X ⟶ Y` corresponds to the map of Čech nerves induced by the morphism of arrows with
components `φ` and the identity of the terminal object. It also records how the map
`FormalCoproduct.powerMap φ α` induced on powers interacts with the projections.

## Main results

* `CategoryTheory.Limits.FormalCoproduct.powerMap_π`: `powerMap φ α` followed by the `a`-th
  projection is the `a`-th projection followed by `φ`.
* `CategoryTheory.Limits.FormalCoproduct.cechFunctor_map_comp_cechIsoCechNerve_hom`: the
  naturality of `cechIsoCechNerve`.
-/

public section

universe w v u

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- The map `powerMap φ α` induced by `φ : X ⟶ Y` on powers commutes with the projections: followed
by the `a`-th projection of `Y.power α` it is the `a`-th projection of `X.power α` followed by
`φ`. -/
@[reassoc (attr := simp)]
theorem powerMap_π {X Y : FormalCoproduct.{w} C} (φ : X ⟶ Y) (α : Type)
    [HasProductsOfShape α C] (a : α) :
    powerMap φ α ≫ Y.powerπ a = X.powerπ a ≫ φ :=
  hom_ext rfl fun x ↦ by
    simp only [category_comp_φ, powerMap_φ, powerπ_φ]
    exact (Pi.map_π (fun b ↦ φ.φ (x b)) a =≫ _).trans (Category.comp_id _)

variable [HasFiniteProducts C] {T : C} (hT : IsTerminal T)

/-- **Naturality of `cechIsoCechNerve`.** Under the identification of the Čech object of a formal
coproduct with the Čech nerve of its morphism to the terminal object, the map induced by
`φ : X ⟶ Y` on Čech objects is the map `Arrow.mapCechNerve` induced by the morphism of arrows
with components `φ` and `𝟙 T`. -/
theorem cechFunctor_map_comp_cechIsoCechNerve_hom {X Y : FormalCoproduct.{w} C} (φ : X ⟶ Y) :
    cechFunctor.map φ ≫ (Y.cechIsoCechNerve hT).hom = (X.cechIsoCechNerve hT).hom ≫
      Arrow.mapCechNerve (Arrow.homMk (f := Arrow.mk ((isTerminalIncl _ hT).from X))
        (g := Arrow.mk ((isTerminalIncl _ hT).from Y)) φ (𝟙 _)
          ((isTerminalIncl _ hT).hom_ext _ _)) := by
  refine NatTrans.ext (funext fun n ↦ WidePullback.hom_ext _ _ _ (fun j ↦ ?_) ?_)
  · -- both sides are the `j`-th projection of `X.cech` followed by `φ`
    simp [cechFunctor]
  · exact (isTerminalIncl _ hT).hom_ext _ _

end CategoryTheory.Limits.FormalCoproduct
end
end GeometryLiteralSource011

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Limits.FormalCoproducts.Cech"

section GeometryLiteralSource012
/- Original source: TauCeti.CategoryTheory.Sites.IsSheafFor -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Compatible families over a terminal object and a meet-semilattice, and local sheaf conditions

For a family of maps `π i : X i ⟶ B` to a terminal object `B`, every pair of maps into two members
of the family agrees after composing with `π`. So a family of elements `x i ∈ P(X i)` of a presheaf
of types `P` is compatible exactly when, for every pair `k : Fin 2 → I`, the restrictions of
`x (k 0)` and `x (k 1)` to the product of `X (k 0)` and `X (k 1)` agree. This is the form the
compatibility condition takes in degree `1` of the Čech complex.

In a meet-semilattice, such as the opens of a topological space, there is at most one morphism
between two objects, and two members `X i`, `X j` of a family have the greatest lower bound
`X i ⊓ X j`. So a family of elements is compatible exactly when the restrictions of `x i` and
`x j` to `X i ⊓ X j` agree.

The sheaf condition for a presieve on `X` reads a presheaf only at objects mapping to `X`. So a
natural transformation `P ⟶ P'` that is bijective at those objects carries the sheaf condition
from `P'` back to `P`, even if `P` and `P'` differ elsewhere. This is how a sheaf condition on an
open subspace is compared with one on the ambient space.

## Main results

* `CategoryTheory.Presieve.Arrows.compatible_iff_of_isTerminal`: the characterisation above.
* `CategoryTheory.Presieve.Arrows.compatible_homOfLE_iff`: compatibility in a meet-semilattice is
  agreement on pairwise meets.
* `CategoryTheory.Presieve.isSheafFor_of_bijective_app`: the sheaf condition for a presieve on `X`
  passes back along a natural transformation that is bijective at the objects over `X`.
-/

public section

universe w v u t

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presieve.Arrows

variable {C : Type u} [Category.{v} C] [HasProductsOfShape (Fin 2) C] {P : Cᵒᵖ ⥤ Type w}
  {I : Type t} {X : I → C} {B : C}

/-- A family of elements indexed by maps `π i : X i ⟶ B` to a terminal object is compatible
exactly when its restrictions agree on the product `∏ᶜ fun j ↦ X (k j)` of every pair of members
`k : Fin 2 → I`. Unlike `Presieve.Arrows.pullbackCompatible_iff`, it needs only products of two
objects, and the products are indexed as in the Čech complex `CategoryTheory.cechComplexFunctor`. -/
theorem compatible_iff_of_isTerminal (hB : IsTerminal B) (π : ∀ i, X i ⟶ B)
    (x : ∀ i, P.obj (op (X i))) :
    Compatible P π x ↔ ∀ k : Fin 2 → I, P.map (Pi.π (fun j ↦ X (k j)) 1).op (x (k 1)) =
      P.map (Pi.π (fun j ↦ X (k j)) 0).op (x (k 0)) := by
  refine ⟨fun h k ↦ h (k 1) (k 0) _ _ _ (hB.hom_ext _ _), fun h i j Z gi gj _ ↦ ?_⟩
  -- restrict the condition for the pair `(j, i)` along the map into the product given by `gj`, `gi`
  have := congrArg (P.map (Pi.lift (Fin.cons gj fun _ ↦ gi)).op) (h (Fin.cons j fun _ ↦ i))
  simp only [← Functor.map_comp_apply, ← op_comp, Pi.lift_comp_π] at this
  exact this

section SemilatticeInf

variable {X : Type u} [SemilatticeInf X] {P : Xᵒᵖ ⥤ Type w} {I : Type t} {Y : I → X} {B : X}

/-- **Compatibility in a meet-semilattice is agreement on pairwise meets.** For members `Y i ≤ B`
of a meet-semilattice, such as opens of a topological space, a family of elements
`x i ∈ P(Y i)` of a presheaf of types is compatible exactly when, for all `i` and `j`, the
restrictions of `x i` and `x j` to `Y i ⊓ Y j` agree. -/
theorem compatible_homOfLE_iff (hY : ∀ i, Y i ≤ B) (x : ∀ i, P.obj (op (Y i))) :
    Compatible P (fun i ↦ homOfLE (hY i)) x ↔ ∀ i j,
      P.map (homOfLE inf_le_left : Y i ⊓ Y j ⟶ Y i).op (x i) =
        P.map (homOfLE inf_le_right : Y i ⊓ Y j ⟶ Y j).op (x j) := by
  refine ⟨fun h i j ↦ h i j _ _ _ (Subsingleton.elim _ _), fun h i j Z gi gj _ ↦ ?_⟩
  -- both maps out of `Z` factor through `Y i ⊓ Y j`, and morphisms in a preorder are unique
  have hZ : Z ≤ Y i ⊓ Y j := le_inf gi.le gj.le
  rw [show gi = homOfLE hZ ≫ homOfLE inf_le_left from Subsingleton.elim _ _,
    show gj = homOfLE hZ ≫ homOfLE inf_le_right from Subsingleton.elim _ _, op_comp, op_comp,
    Functor.map_comp_apply, Functor.map_comp_apply, h i j]

end SemilatticeInf

end CategoryTheory.Presieve.Arrows

namespace CategoryTheory.Presieve

variable {C : Type u} [Category.{v} C] {P P' : Cᵒᵖ ⥤ Type w}

/-- **The sheaf condition for a presieve on `X` only involves the objects over `X`.** If a natural
transformation `α : P ⟶ P'` is bijective at every object admitting a morphism to `X`, then `P`
satisfies the sheaf condition for a presieve `R` on `X` whenever `P'` does. Unlike
`CategoryTheory.Presieve.isSheafFor_of_nat_equiv`, nothing is assumed away from `X`. -/
theorem isSheafFor_of_bijective_app (α : P ⟶ P') {X : C} {R : Presieve X}
    (hα : ∀ ⦃Y : C⦄, (Y ⟶ X) → Function.Bijective (α.app (op Y))) (h : IsSheafFor P' R) :
    IsSheafFor P R := by
  intro x hx
  obtain ⟨t', ht', hu⟩ := h (x.map α) (hx.map α)
  obtain ⟨t, rfl⟩ := (hα (𝟙 X)).2 t'
  refine ⟨t, fun Y f hf ↦ (hα f).1 ?_, fun t₁ ht₁ ↦ (hα (𝟙 X)).1 (hu _ (ht₁.map α))⟩
  rw [NatTrans.naturality_apply]
  exact ht' f hf

end CategoryTheory.Presieve
end
end GeometryLiteralSource012

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Sites.IsSheafFor"

section GeometryLiteralSource013
/- Original source: TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The augmented Čech complex of a presheaf

Let `C` be a category with finite products and a terminal object `T`, let `U : ι → C` be a family
of objects and let `P : Cᵒᵖ ⥤ A` be a presheaf with values in a preadditive category with
products. Mathlib's `CategoryTheory.cechComplexFunctor U` sends `P` to its Čech complex
`Č(U, P)`, whose degree `n` term is the product, over `a : Fin (n + 1) → ι`, of
`P(U (a 0) × ⋯ × U (a n))`. This file constructs the augmentation `P(T) ⟶ Č⁰(U, P)`, as a map of
cochain complexes from `P(T)` placed in degree `0`, and characterises when it is a
quasi-isomorphism, that is, when the augmented Čech complex
`0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is exact. The augmentation is Mathlib's
`AlgebraicTopology.AlternatingFaceMapComplex.ε` for the augmented Čech object
`FormalCoproduct.cech.augmentOfIsTerminal` evaluated at `P`, transported from `Aᵒᵖ` to `A`.

For an open cover `U` of a topological space `X` and a presheaf of abelian groups `F` on `X`, this
is Wedhorn's notion of an `F`-acyclic cover: the augmentation identifies `F(X)` with the degree `0`
cohomology of `Č(U, F)`, and `Č(U, F)` has no cohomology in positive degrees. A cover of an open
subset `W` fits this setting in the category `Over W`, which has finite products and the terminal
object `Over.mk (𝟙 W)` (`CategoryTheory.Over.mkIdTerminal`).

A morphism of families `U ⟶ V`, that is a morphism of formal coproducts, induces a map of Čech
complexes `Č(V, P) ⟶ Č(U, P)` compatible with the augmentations, and any two morphisms `U ⟶ V`
induce homotopic maps. For open covers this says that the map on Čech cohomology induced by a
refinement does not depend on the refinement map; in particular, acyclicity of a cover only depends
on the cover up to refinement in both directions, so that members contained in other members may
be added or removed.

## Main definitions

* `TauCeti.CategoryTheory.cechAugmentation U hT P`: the augmentation of the Čech complex of `P`
  for `U`; its degree `0` component restricts a section over `T` along each map to `T`
  (`TauCeti.CategoryTheory.cechAugmentation_f_zero_comp_π`).
* `TauCeti.CategoryTheory.cechComplexMap P φ`: the map of Čech complexes `Č(V, P) ⟶ Č(U, P)`
  induced by a morphism of families `φ : U ⟶ V`.

## Main results

* `TauCeti.CategoryTheory.quasiIsoAt_cechAugmentation_zero_iff`: the augmentation induces an
  isomorphism in degree `0` exactly when `P` satisfies the sheaf condition for the family of
  maps `U i ⟶ T`, in Mathlib's form for presheaves with values in `A`: every
  `P ⋙ coyoneda.obj E` is a sheaf for `Presieve.ofArrows U`.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff`: the augmentation is a
  quasi-isomorphism exactly when `P` satisfies that sheaf condition and the Čech complex is
  exact in every positive degree.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_hom`: if some `U i₀` receives a map from
  `T`, for instance if `U i₀ = T`, then the augmentation is a quasi-isomorphism. This comes from
  Mathlib's extra degeneracy `CategoryTheory.Limits.FormalCoproduct.extraDegeneracyCech` of the
  Čech object, which makes `ε` a homotopy equivalence
  (`SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv`).
* `TauCeti.CategoryTheory.cechComplexMapHomotopy`: any two morphisms of families `U ⟶ V`
  induce homotopic maps of Čech complexes.
* `TauCeti.CategoryTheory.cechComplexHomotopyEquiv`: families with morphisms `U ⟶ V` and
  `V ⟶ U` have homotopy equivalent Čech complexes.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_congr`: for such families, the augmented Čech
  complex of `P` for `U` is exact if and only if the one for `V` is.
* `TauCeti.CategoryTheory.isIso_cechComplexMap`: a morphism of families that is the identity on
  indices induces an isomorphism of Čech complexes when `P` inverts the induced maps of products.
* `TauCeti.CategoryTheory.cechAugmentation_naturality`: the augmentation is natural in `P`.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff_of_iso`: acyclicity of a family is
  invariant under isomorphisms of presheaves.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Appendix A: Definition A.1 and
  the acyclicity of a cover having `X` as a member, stated after Remark A.2.
* R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer, 1977,
  Exercise III.4.4, for the independence of the map induced by a refinement from the refinement
  map.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology Simplicial

universe w v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  {ι : Type w} (U : ι → C) {T : C} (hT : IsTerminal T) (P : Cᵒᵖ ⥤ A)

variable [Preadditive A] [HasProducts.{w} A]

/-! ### The Čech complex in degrees `0` and `1`

Mathlib's `cechComplexFunctor` is a composite of several functors, so its terms agree only up to
unfolding with the products that define them. The identity isomorphisms `cechXIso₀` and
`cechXIso₁` record these identifications once, so that every later statement composes maps
between syntactically equal objects. A `0`-cochain is determined by its restrictions `restrict`
to the members `U i`, and it is killed by the differential `Č⁰(U, P) ⟶ Č¹(U, P)` exactly when
these restrictions agree on the products of pairs of members (`comp_d_eq_zero_iff`). -/

private def cechXIso₀ : ((cechComplexFunctor U).obj P).X 0 ≅
    ∏ᶜ fun a : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))) := Iso.refl _

private def cechXIso₁ : ((cechComplexFunctor U).obj P).X 1 ≅
    ∏ᶜ fun k : Fin 2 → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (k j))) := Iso.refl _

private def cechδ (m : Fin 2) : ((cechComplexFunctor U).obj P).X 0 ⟶
    ((cechComplexFunctor U).obj P).X 1 :=
  ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P).δ m

private lemma cechComplexFunctor_obj_d_zero_one :
    ((cechComplexFunctor U).obj P).d 0 1 = cechδ U P 0 - cechδ U P 1 :=
  (CochainComplex.of_d _ (AlternatingCofaceMapComplex.objD _) 0).trans <| by
    simp [sub_eq_add_neg]
    -- `cechδ m` unfolds to the coface map `δ m`
    rfl

private lemma cechδ_comp_π (m : Fin 2) (k : Fin 2 → ι) :
    cechδ U P m ≫ (cechXIso₁ U P).hom ≫ Pi.π _ k =
      (cechXIso₀ U P).hom ≫ Pi.π _ (fun x ↦ k (m.succAbove x)) ≫
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (m.succAbove x)).op :=
  -- `cechXIso₀` and `cechXIso₁` are identities, and `cechδ m` unfolds to a `Pi.lift`
  (_ ≫= Category.id_comp _).trans <| (Pi.lift_comp_π _ _).trans (Category.id_comp _).symm

private def restrict (a : Fin 1 → ι) :
    ((cechComplexFunctor U).obj P).X 0 ⟶ P.obj (op (U (a default))) :=
  (cechXIso₀ U P).hom ≫ Pi.π _ a ≫ P.map (productUniqueIso _).inv.op

private lemma restrict_eq_restrict_const (a : Fin 1 → ι) :
    restrict U P a = restrict U P (fun _ ↦ a default) :=
  eq_const_of_unique a ▸ rfl

@[reassoc]
private lemma cechXIso₀_hom_comp_π (a : Fin 1 → ι) : (cechXIso₀ U P).hom ≫ Pi.π _ a =
    restrict U P a ≫ P.map (productUniqueIso fun j ↦ U (a j)).hom.op :=
  -- `restrict a` is the left-hand side followed by `P.map (productUniqueIso _).inv.op`
  (P.mapIso (productUniqueIso _).op).comp_inv_eq.1 (Category.assoc _ _ _)

private lemma cechComplexFunctor_obj_X_zero_hom_ext {W : A}
    {y y' : W ⟶ ((cechComplexFunctor U).obj P).X 0}
    (h : ∀ i, y ≫ restrict U P (fun _ ↦ i) = y' ≫ restrict U P (fun _ ↦ i)) : y = y' :=
  (cancel_mono (cechXIso₀ U P).hom).1 <| Pi.hom_ext _ _ fun a ↦ by
    grind [cechXIso₀_hom_comp_π, restrict_eq_restrict_const]

private lemma comp_d_eq_zero_iff {W : A} (y : W ⟶ ((cechComplexFunctor U).obj P).X 0) :
    y ≫ ((cechComplexFunctor U).obj P).d 0 1 = 0 ↔ ∀ k : Fin 2 → ι,
      y ≫ restrict U P (fun _ ↦ k 1) ≫ P.map (Pi.π (fun j ↦ U (k j)) 1).op =
        y ≫ restrict U P (fun _ ↦ k 0) ≫ P.map (Pi.π (fun j ↦ U (k j)) 0).op := by
  have key (m : Fin 2) (k : Fin 2 → ι) : cechδ U P m ≫ (cechXIso₁ U P).hom ≫ Pi.π _ k =
      restrict U P (fun _ ↦ k (m.succAbove default)) ≫
        P.map (Pi.π (fun j ↦ U (k j)) (m.succAbove default)).op := by
    rw [cechδ_comp_π, cechXIso₀_hom_comp_π_assoc, ← P.map_comp, ← op_comp, productUniqueIso_hom,
      Pi.lift_comp_π, restrict_eq_restrict_const]
  rw [← cancel_mono (cechXIso₁ U P).hom, zero_comp, Pi.hom_ext_iff]
  simp [cechComplexFunctor_obj_d_zero_one, key, sub_eq_zero, Fin.one_succAbove_zero]

private def lift₀ {W : A} (x : ∀ i, W ⟶ P.obj (op (U i))) :
    W ⟶ ((cechComplexFunctor U).obj P).X 0 :=
  (Pi.lift fun a ↦ x (a default) ≫ P.map (productUniqueIso _).hom.op) ≫ (cechXIso₀ U P).inv

@[reassoc]
private lemma lift₀_comp_restrict {W : A} (x : ∀ i, W ⟶ P.obj (op (U i))) (a : Fin 1 → ι) :
    lift₀ U P x ≫ restrict U P a = x (a default) := by
  simp [restrict, lift₀, ← P.map_comp, ← op_comp]

/-! ### The augmented Čech object with values in `Aᵒᵖ`

Applying `P` to Mathlib's augmented Čech object `FormalCoproduct.cech.augmentOfIsTerminal`
gives an augmented simplicial object in `Aᵒᵖ`, whose alternating face map complex is, after
passing back to `A`, the Čech complex of `P`. Its augmentation `AlternatingFaceMapComplex.ε`,
passed back to `A` in the same way (`singleIso`), is the augmentation of the Čech complex. -/

private abbrev cechSimplicial : SimplicialObject Aᵒᵖ :=
  ((SimplicialObject.whiskering _ _).obj ((FormalCoproduct.evalOp C A).obj P).rightOp).obj
    (FormalCoproduct.mk _ U).cech

private abbrev augmentedCech : SimplicialObject.Augmented Aᵒᵖ :=
  ((SimplicialObject.Augmented.whiskering _ _).obj ((FormalCoproduct.evalOp C A).obj P).rightOp).obj
    ((FormalCoproduct.mk _ U).cech.augmentOfIsTerminal (FormalCoproduct.isTerminalIncl _ hT))

private lemma unop_d_eq_cechComplexFunctor_obj_d (n : ℕ) :
    (AlternatingFaceMapComplex.obj (cechSimplicial U P)).unop.d n (n + 1) =
      ((cechComplexFunctor U).obj P).d n (n + 1) := by
  rw [HomologicalComplex.unop_d, AlternatingFaceMapComplex.obj_d_eq]
  -- the unopposite of each face map of `cechSimplicial` is a coface map of the Čech object
  exact Eq.symm <| (CochainComplex.of_d _ _ n).trans (AlternatingCofaceMapComplex.d_eq_unop_d _ n)

private def unopAlternatingFaceMapComplexIso :
    ((AlternatingFaceMapComplex.obj (cechSimplicial U P)).unop : CochainComplex A ℕ) ≅
      (cechComplexFunctor U).obj P :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) fun i _ h ↦
    h ▸ (Category.id_comp _).trans
      ((unop_d_eq_cechComplexFunctor_obj_d U P i).symm.trans (Category.comp_id _).symm)

/-! ### The differential -/

/-- The differential of the Čech complex is the alternating sum of the restrictions along the
coface maps: the factor of `((cechComplexFunctor U).obj P).d n (n + 1)` indexed by
`k : Fin (n + 2) → ι` is the alternating sum over `m` of the factor indexed by `k ∘ m.succAbove`,
restricted along the projection `U (k 0) × ⋯ × U (k (n + 1)) ⟶ ∏ⱼ U (k (m.succAbove j))`. -/
@[reassoc]
theorem cechComplexFunctor_obj_d_comp_π (n : ℕ) (k : Fin (n + 2) → ι) :
    ((cechComplexFunctor U).obj P).d n (n + 1) ≫ Pi.π _ k =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) • (Pi.π _ (k ∘ m.succAbove) ≫
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (m.succAbove x)).op) := by
  have h : ((cechComplexFunctor U).obj P).d n (n + 1) = AlternatingCofaceMapComplex.objD
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P) n :=
    (CochainComplex.of_d _ (AlternatingCofaceMapComplex.objD _) n).trans rfl
  rw [h, AlternatingCofaceMapComplex.objD]
  refine (Preadditive.sum_comp _ _ _).trans (Finset.sum_congr rfl fun m _ ↦ ?_)
  -- the coface map `δ m` unfolds to a `Pi.lift`
  exact (Preadditive.zsmul_comp _ _ _).trans <| congrArg _ <| Pi.lift_comp_π _ _

/-! ### Maps of presheaves -/

/-- A morphism of presheaves `α : P ⟶ Q` acts on the Čech complexes factorwise: the factor of
`((cechComplexFunctor U).map α).f n` indexed by `a` is the component of `α` at
`U (a 0) × ⋯ × U (a n)`. -/
@[reassoc]
theorem cechComplexFunctor_map_f_π {Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) (a : Fin (n + 1) → ι) :
    ((cechComplexFunctor U).map α).f n ≫ Pi.π _ a =
      Pi.π _ a ≫ α.app (op (∏ᶜ fun j ↦ U (a j))) :=
  Pi.map_π (fun _ ↦ α.app _) a

/-! ### Maps of families

A morphism `φ` from the family `U` to a family `V : κ → C`, as a morphism of formal coproducts,
consists of a map `φ.f : ι → κ` of indices and morphisms `φ.φ i : U i ⟶ V (φ.f i)`; for open covers
it is a refinement map. It induces a map of Čech complexes `Č(V, P) ⟶ Č(U, P)`
(`cechComplexMap`). Any two morphisms `U ⟶ V` induce homotopic maps (`cechComplexMapHomotopy`),
because they induce simplicially homotopic maps of Čech nerves
(`CategoryTheory.Arrow.mapCechNerveHomotopy`). -/

section Map

variable {U} {κ : Type w} {V : κ → C}

/-- The map of Čech complexes `Č(V, P) ⟶ Č(U, P)` induced by a morphism `φ` from the family `U`
to the family `V`. In degree `n` it sends the factor `P(V (b 0) × ⋯ × V (b n))` indexed by
`b = φ.f ∘ a` to the factor `P(U (a 0) × ⋯ × U (a n))` by restriction along the product of the
`φ.φ (a j)` (`cechComplexMap_f_π`). -/
noncomputable def cechComplexMap (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (cechComplexFunctor V).obj P ⟶ (cechComplexFunctor U).obj P :=
  (alternatingCofaceMapComplex A).map (Functor.whiskerRight
    (NatTrans.rightOp (FormalCoproduct.cechFunctor.map φ)) ((FormalCoproduct.evalOp C A).obj P))

/-- The factor of `(cechComplexMap P φ).f n` indexed by `a` is the factor of `Č(V, P)` indexed by
`φ.f ∘ a`, restricted along the product of the morphisms `φ.φ (a j)`. -/
theorem cechComplexMap_f_π (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (n : ℕ)
    (a : Fin (n + 1) → ι) :
    (cechComplexMap P φ).f n ≫ Pi.π _ a =
      Pi.π _ (φ.f ∘ a) ≫ P.map (Limits.Pi.map fun j ↦ φ.φ (a j)).op :=
  Pi.lift_comp_π _ _

/-- The identity morphism of a family induces the identity of its Čech complex. -/
@[simp]
theorem cechComplexMap_id : cechComplexMap P (𝟙 (FormalCoproduct.mk _ U)) = 𝟙 _ := by
  simp only [cechComplexMap, CategoryTheory.Functor.map_id, NatTrans.rightOp_id,
    Functor.whiskerRight_id']
  exact (alternatingCofaceMapComplex A).map_id _

/-- `cechComplexMap` is contravariantly functorial in the morphism of families. -/
@[simp]
theorem cechComplexMap_comp {ι' : Type w} {W : ι' → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ W) :
    cechComplexMap P (φ ≫ ψ) = cechComplexMap P ψ ≫ cechComplexMap P φ := by
  simp only [cechComplexMap, CategoryTheory.Functor.map_comp, NatTrans.rightOp_comp,
    Functor.whiskerRight_comp]
  exact (alternatingCofaceMapComplex A).map_comp _ _

/-- A morphism of families which is the identity on indices, given by morphisms
`φ i : U i ⟶ W i`, induces an isomorphism of Čech complexes `Č(W, P) ⟶ Č(U, P)` as soon as `P`
turns each induced morphism `U (a 0) × ⋯ × U (a n) ⟶ W (a 0) × ⋯ × W (a n)` into an
isomorphism. -/
theorem isIso_cechComplexMap {W : ι → C} (φ : ∀ i, U i ⟶ W i)
    (h : ∀ (n : ℕ) (a : Fin (n + 1) → ι), IsIso (P.map (Limits.Pi.map fun j ↦ φ (a j)).op)) :
    IsIso (cechComplexMap P (⟨id, φ⟩ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ W)) := by
  have (n : ℕ) : IsIso ((cechComplexMap P
      (⟨id, φ⟩ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ W)).f n) := by
    have hπ (a : Fin (n + 1) → ι) : (cechComplexMap P
        (⟨id, φ⟩ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ W)).f n ≫ Pi.π _ a =
          Pi.π _ a ≫ P.map (Limits.Pi.map fun j ↦ φ (a j)).op :=
      cechComplexMap_f_π P _ n a
    -- in degree `n` the map is the product of the maps `P.map (Pi.map fun j ↦ φ (a j)).op`
    have e : (cechComplexMap P
        (⟨id, φ⟩ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ W)).f n =
          Limits.Pi.map (fun a : Fin (n + 1) → ι ↦ P.map (Limits.Pi.map fun j ↦ φ (a j)).op) :=
      Pi.hom_ext _ _ fun a ↦ (hπ a).trans
        (Pi.map_π (fun a : Fin (n + 1) → ι ↦ P.map (Limits.Pi.map fun j ↦ φ (a j)).op) a).symm
    have := h n
    rw [e]
    exact Pi.map_isIso _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The morphism of arrows to the terminal object of `FormalCoproduct C` induced by a morphism of
formal coproducts. -/
private abbrev cechArrowHom {X Y : FormalCoproduct.{w} C} (φ : X ⟶ Y) :
    Arrow.mk ((FormalCoproduct.isTerminalIncl _ terminalIsTerminal).from X) ⟶
      Arrow.mk ((FormalCoproduct.isTerminalIncl _ terminalIsTerminal).from Y) :=
  Arrow.homMk φ (𝟙 _) ((FormalCoproduct.isTerminalIncl _ terminalIsTerminal).hom_ext _ _)

/-- Under the identification of the Čech object of a formal coproduct with the Čech nerve of its
map to the terminal object, the map induced by `φ` is `Arrow.mapCechNerve`. -/
private lemma cechFunctor_map_eq {X Y : FormalCoproduct.{w} C} (φ : X ⟶ Y) :
    (FormalCoproduct.cechFunctor.map φ : X.cech ⟶ Y.cech) =
      (X.cechIsoCechNerve terminalIsTerminal).hom ≫ Arrow.mapCechNerve (cechArrowHom φ) ≫
        (Y.cechIsoCechNerve terminalIsTerminal).inv :=
  ((Iso.eq_comp_inv _).2 (FormalCoproduct.cechFunctor_map_comp_cechIsoCechNerve_hom _ φ)).trans
    (Category.assoc _ _ _)

/-- `cechComplexMap` read through `unopAlternatingFaceMapComplexIso`, as the map of alternating
face map complexes of simplicial objects in `Aᵒᵖ`. -/
private lemma cechComplexMap_eq (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechComplexMap P φ = (unopAlternatingFaceMapComplexIso V P).inv ≫
      (HomologicalComplex.unopFunctor _ _).map ((alternatingFaceMapComplex Aᵒᵖ).map
        (((SimplicialObject.whiskering _ _).obj ((FormalCoproduct.evalOp C A).obj P).rightOp).map
          (FormalCoproduct.cechFunctor.map φ))).op ≫
        (unopAlternatingFaceMapComplexIso U P).hom := by
  ext n : 1
  -- the components of `unopAlternatingFaceMapComplexIso` are identities
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **Any two morphisms of families induce homotopic maps of Čech complexes.** For morphisms
`φ ψ` from the family `U` to the family `V`, for instance two refinement maps between open covers,
the maps `Č(V, P) ⟶ Č(U, P)` they induce are homotopic. -/
noncomputable def cechComplexMapHomotopy (φ ψ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    Homotopy (cechComplexMap P φ) (cechComplexMap P ψ) :=
  -- the simplicial homotopy between the maps of Čech nerves, carried to the Čech objects and
  -- then to simplicial objects in `Aᵒᵖ` by `P`
  let H := (((Arrow.mapCechNerveHomotopy (cechArrowHom φ) (cechArrowHom ψ) rfl).postcomp
    ((FormalCoproduct.mk _ V).cechIsoCechNerve terminalIsTerminal).inv).precomp
      ((FormalCoproduct.mk _ U).cechIsoCechNerve terminalIsTerminal).hom).whiskerRight
        ((FormalCoproduct.evalOp C A).obj P).rightOp
  (Homotopy.ofEq (by
    rw [cechComplexMap_eq, cechFunctor_map_eq]
    exact (Category.assoc _ _ _).symm)).trans <|
      ((H.toChainHomotopy.unop.compLeft (unopAlternatingFaceMapComplexIso V P).inv).compRight
        (unopAlternatingFaceMapComplexIso U P).hom).trans <|
          Homotopy.ofEq (by
            rw [cechComplexMap_eq, cechFunctor_map_eq]
            exact Category.assoc _ _ _)

/-- **Families that map to each other have homotopy equivalent Čech complexes.** Given morphisms
of families `φ : U ⟶ V` and `ψ : V ⟶ U`, for instance two open covers each refining the other, the
induced maps `Č(V, P) ⟶ Č(U, P)` and `Č(U, P) ⟶ Č(V, P)` are mutually inverse homotopy
equivalences. -/
noncomputable def cechComplexHomotopyEquiv (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U) :
    HomotopyEquiv ((cechComplexFunctor V).obj P) ((cechComplexFunctor U).obj P) where
  hom := cechComplexMap P φ
  inv := cechComplexMap P ψ
  homotopyHomInvId := (Homotopy.ofEq (cechComplexMap_comp P ψ φ).symm).trans <|
    (cechComplexMapHomotopy P (ψ ≫ φ) (𝟙 _)).trans (Homotopy.ofEq (cechComplexMap_id P))
  homotopyInvHomId := (Homotopy.ofEq (cechComplexMap_comp P φ ψ).symm).trans <|
    (cechComplexMapHomotopy P (φ ≫ ψ) (𝟙 _)).trans (Homotopy.ofEq (cechComplexMap_id P))

/-- The forward map of `cechComplexHomotopyEquiv P φ ψ` is the map induced by `φ`. -/
@[simp]
theorem cechComplexHomotopyEquiv_hom (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U) :
    (cechComplexHomotopyEquiv P φ ψ).hom = cechComplexMap P φ := (rfl)

/-- The backward map of `cechComplexHomotopyEquiv P φ ψ` is the map induced by `ψ`. -/
@[simp]
theorem cechComplexHomotopyEquiv_inv (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U) :
    (cechComplexHomotopyEquiv P φ ψ).inv = cechComplexMap P ψ := (rfl)

end Map

variable [HasZeroObject A]

private def singleIso : (CochainComplex.single₀ A).obj (P.obj (op T)) ≅
    (((ChainComplex.single₀ Aᵒᵖ).obj (augmentedCech U hT P).right).unop : CochainComplex A ℕ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun
      | 0 => HomologicalComplex.singleObjXSelf _ 0 _ ≪≫
          (((FormalCoproduct.evalOpCompInlIsoId C A).app P).app (op T)).symm ≪≫
            (HomologicalComplex.singleObjXSelf _ 0 _).unop
      | n + 1 => (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)).iso
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)).unop)
    (fun _ _ _ ↦ by
      simp only [HomologicalComplex.single_obj_d, HomologicalComplex.unop_d, unop_zero, zero_comp]
      exact comp_zero)

/-- The augmentation of the Čech complex of `P` for the family `U`, as a map of cochain complexes
from `P(T)` placed in degree `0`. It is Mathlib's augmentation `AlternatingFaceMapComplex.ε` of the
augmented Čech object evaluated at `P`, passed from `Aᵒᵖ` back to `A`. Its degree `0` component
`P(T) ⟶ Č⁰(U, P)` restricts a section over `T` along the maps to `T`
(`cechAugmentation_f_zero_comp_π`). As for `CategoryTheory.InjectiveResolution.ι`, exactness of the
augmented Čech complex `0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is expressed as
`QuasiIso (cechAugmentation U hT P)`; `quasiIso_cechAugmentation_iff` unpacks it into the sheaf
condition for the family `U i ⟶ T` and exactness of the Čech complex in positive degrees. -/
def cechAugmentation : (CochainComplex.single₀ A).obj (P.obj (op T)) ⟶
    (cechComplexFunctor U).obj P :=
  (singleIso U hT P).hom ≫ (HomologicalComplex.unopFunctor _ _).map
    (AlternatingFaceMapComplex.ε.app (augmentedCech U hT P)).op ≫
      (unopAlternatingFaceMapComplexIso U P).hom

/-- The degree `0` component of the augmentation, followed by the projection of `Č⁰(U, P)` onto its
factor indexed by `a : Fin 1 → ι`, is `P` applied to the map from `∏ᶜ fun j ↦ U (a j)` to the
terminal object: the augmentation restricts a section over `T` to each member of the family, seen as
a one-fold product. -/
@[reassoc]
theorem cechAugmentation_f_zero_comp_π (a : Fin 1 → ι) : (cechAugmentation U hT P).f 0 ≫ Pi.π _ a =
    P.map (hT.from (∏ᶜ fun j ↦ U (a j))).op := by
  -- in degree `0`, `cechAugmentation` is `ε` between the identifications made by `singleIso` and
  -- `unopAlternatingFaceMapComplexIso`, and `ε` is `P` applied to the map to the terminal object
  have h : (cechAugmentation U hT P).f 0 = ((HomologicalComplex.singleObjXSelf _ 0 _).hom ≫
      (Pi.lift fun _ ↦ 𝟙 _) ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
        (augmentedCech U hT P).right).hom.unop) ≫
      ((AlternatingFaceMapComplex.ε.app (augmentedCech U hT P)).f 0).unop ≫ 𝟙 _ := rfl
  -- the augmentation of `augmentedCech` is `evalOp P` applied to the map to `incl T`
  have hM : ((augmentedCech U hT P).hom.app (op ⦋0⦌)).unop = 𝟙 _ ≫
      ((FormalCoproduct.evalOp C A).obj P).map ((FormalCoproduct.isTerminalIncl _ hT).from _).op :=
    rfl
  rw [h]
  simp only [CochainComplex.single₀_obj_zero, Functor.rightOp_obj, FormalCoproduct.cech_obj,
    Functor.comp_obj, SimplicialObject.Augmented.point_obj, ChainComplex.single₀_obj_zero,
    SimplicialObject.Augmented.drop_obj, alternatingFaceMapComplex_obj_X,
    CochainComplex.single₀ObjXSelf, Iso.refl_hom, ChainComplex.single₀ObjXSelf, unop_id,
    Category.id_comp, AlternatingFaceMapComplex.ε_app_f_zero, Functor.id_obj, Category.comp_id]
  rw [hM]
  simp only [SimplicialObject.Augmented.drop_obj, FormalCoproduct.evalOp_obj_map,
    Quiver.Hom.unop_op]
  exact ((Category.comp_id _ =≫ _) =≫ _).trans <| ((_ ≫= Category.id_comp _) =≫ _).trans <|
    (Category.assoc _ _ _).trans <| (_ ≫= Pi.lift_comp_π _ _).trans <|
      (Pi.lift_comp_π_assoc _ _ _).trans <| (Category.id_comp _).trans <|
        P.congr_map (congrArg Quiver.Hom.op (hT.hom_ext _ _))

section Map

variable {U} {κ : Type w} {V : κ → C}

/-- The augmentations of the Čech complexes are compatible with the maps induced by morphisms of
families: restricting a section over `T` to the members of `V` and then to the members of `U`
restricts it to the members of `U`. -/
@[reassoc (attr := simp)]
theorem cechAugmentation_comp_cechComplexMap
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechAugmentation V hT P ≫ cechComplexMap P φ = cechAugmentation U hT P := by
  refine HomologicalComplex.from_single_hom_ext (Pi.hom_ext _ _ fun (a : Fin 1 → ι) ↦ ?_)
  -- both sides restrict along a map to the terminal object `T`
  exact (Category.assoc _ _ _).trans <| (_ ≫= cechComplexMap_f_π P φ 0 a).trans <|
    (Category.assoc _ _ _).symm.trans <| (cechAugmentation_f_zero_comp_π V hT P _ =≫ _).trans <|
      (P.map_comp _ _).symm.trans <|
      (P.congr_map (congrArg Quiver.Hom.op (hT.hom_ext _ _))).trans
        (cechAugmentation_f_zero_comp_π U hT P a).symm

end Map

/-- The augmentation is natural in the presheaf: for `α : P ⟶ Q`, restricting a section of `P`
over `T` to the members of the family and then applying `α` is applying `α` over `T` and then
restricting. -/
@[reassoc]
theorem cechAugmentation_naturality {Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) :
    cechAugmentation U hT P ≫ (cechComplexFunctor U).map α =
      (CochainComplex.single₀ A).map (α.app (op T)) ≫ cechAugmentation U hT Q := by
  refine HomologicalComplex.from_single_hom_ext (Pi.hom_ext _ _ fun (a : Fin 1 → ι) ↦ ?_)
  -- restrict to `a`, then use naturality of `α` along the map to `T`
  exact (Category.assoc _ _ _).trans <| (_ ≫= cechComplexFunctor_map_f_π U P α 0 a).trans <|
    (Category.assoc _ _ _).symm.trans <| (cechAugmentation_f_zero_comp_π U hT P a =≫ _).trans <|
      (α.naturality _).trans <|
      (_ ≫= cechAugmentation_f_zero_comp_π U hT Q a).symm.trans <| (Category.assoc _ _ _).symm.trans
        ((by simp : _ = ((CochainComplex.single₀ A).map (α.app (op T)) ≫
          cechAugmentation U hT Q).f 0) =≫ _)

/-! ### The augmentation in degree `0`

The degree `0` component `augmentation₀ : P(T) ⟶ Č⁰(U, P)` of the augmentation restricts along
the maps to `T`. Since any family of sections over the `U i` defines a `0`-cochain (`lift₀`),
which is killed by the Čech differential exactly when the family is compatible,
`comp_d_eq_zero_iff` shows that `augmentation₀` is a kernel of the Čech differential exactly when
`P` satisfies the sheaf condition for the family `U i ⟶ T`
(`isLimit_kernelFork_iff_isSheafFor`). -/

private def augmentation₀ : P.obj (op T) ⟶ ((cechComplexFunctor U).obj P).X 0 :=
  (HomologicalComplex.singleObjXSelf _ 0 _).inv ≫ (cechAugmentation U hT P).f 0

@[reassoc]
private lemma augmentation₀_comp_restrict (a : Fin 1 → ι) :
    augmentation₀ U hT P ≫ restrict U P a = P.map (hT.from (U (a default))).op :=
  -- `singleObjXSelf _ 0 _` and `cechXIso₀` are identities
  (Category.assoc _ _ _).trans <| (Category.id_comp _).trans <| (_ ≫= Category.id_comp _).trans <|
    (Category.assoc _ _ _).symm.trans <| (cechAugmentation_f_zero_comp_π U hT P a =≫ _).trans <|
      (P.map_comp _ _).symm.trans <| P.congr_map (congrArg Quiver.Hom.op (hT.hom_ext _ _))

private lemma augmentation₀_comp_d :
    augmentation₀ U hT P ≫ ((cechComplexFunctor U).obj P).d 0 1 = 0 :=
  (Category.assoc _ _ _).trans <| (_ ≫= (cechAugmentation U hT P).comm 0 1).trans <| by
    simp only [HomologicalComplex.single_obj_d, zero_comp]
    exact comp_zero

private lemma comp_augmentation₀_eq_iff {W : A} (t : W ⟶ P.obj (op T))
    (y : W ⟶ ((cechComplexFunctor U).obj P).X 0) : t ≫ augmentation₀ U hT P = y ↔
      ∀ i, t ≫ P.map (hT.from (U i)).op = y ≫ restrict U P fun _ ↦ i :=
  ⟨fun h i ↦ by simp [← h, augmentation₀_comp_restrict], fun h ↦
    cechComplexFunctor_obj_X_zero_hom_ext U P fun i ↦ by simp [augmentation₀_comp_restrict, h]⟩

private lemma isLimit_kernelFork_iff_isSheafFor :
    Nonempty (IsLimit (KernelFork.ofι (augmentation₀ U hT P) (augmentation₀_comp_d U hT P))) ↔
      ∀ E : Aᵒᵖ, (Presieve.ofArrows U fun i ↦ hT.from (U i)).IsSheafFor (P ⋙ coyoneda.obj E) := by
  simp only [op_surjective.forall, Presieve.isSheafFor_arrows_iff,
    Presieve.Arrows.compatible_iff_of_isTerminal hT, Functor.comp_map, Functor.flip_obj_map,
    yoneda_map_app, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
  refine ⟨fun ⟨hl⟩ W x hx ↦ ?_, fun h ↦ ⟨Fork.IsLimit.ofExistsUnique fun s ↦ ?_⟩⟩
  · simpa [comp_augmentation₀_eq_iff, lift₀_comp_restrict] using
      Fork.IsLimit.existsUnique hl (lift₀ U P x) <| by
        simpa [comp_d_eq_zero_iff, lift₀_comp_restrict_assoc] using hx
  · simpa [comp_augmentation₀_eq_iff] using h s.pt (fun i ↦ s.ι ≫ restrict U P fun _ ↦ i) <| by
      simpa using (comp_d_eq_zero_iff U P _).1 (KernelFork.condition s)

variable [CategoryWithHomology A]

private lemma quasiIsoAt_cechAugmentation_zero_iff_isLimit :
    QuasiIsoAt (cechAugmentation U hT P) 0 ↔
      Nonempty (IsLimit (KernelFork.ofι (augmentation₀ U hT P) (augmentation₀_comp_d U hT P))) := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  refine (ShortComplex.quasiIso_iff_isIso_liftCycles _ rfl rfl rfl).trans <|
    ((ShortComplex.cyclesIsKernel _).nonempty_isLimit_iff_isIso_lift
      (t := KernelFork.ofι _ _)).symm.trans ?_
  exact (IsLimit.equivIsoLimit (Fork.ext _ (Iso.hom_inv_id_assoc _ _))).nonempty_congr

/-- The augmentation identifies `P(T)` with the degree `0` cohomology of the Čech complex (that is,
`0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P)` is exact) if and only if `P` satisfies the sheaf condition for the
family of maps `U i ⟶ T`: for every `E`, the presheaf of types `P ⋙ coyoneda.obj E` is a sheaf for
`Presieve.ofArrows U`. The condition holds when `P` is a sheaf (`Presheaf.IsSheaf J P`) for a
topology `J` in which `Sieve.ofArrows U _` covers `T` (use `Presieve.isSheafFor_iff_generate`), and
`Presheaf.isLimit_iff_isSheafFor_presieve` expresses it as a limit condition. -/
@[stacks 03AN "The equivalence for a single covering, which is the content of the proof there."]
theorem quasiIsoAt_cechAugmentation_zero_iff : QuasiIsoAt (cechAugmentation U hT P) 0 ↔
    ∀ E : Aᵒᵖ, (Presieve.ofArrows U fun i ↦ hT.from (U i)).IsSheafFor (P ⋙ coyoneda.obj E) :=
  (quasiIsoAt_cechAugmentation_zero_iff_isLimit U hT P).trans
    (isLimit_kernelFork_iff_isSheafFor U hT P)

/-- The augmentation is a quasi-isomorphism, that is, the augmented Čech complex
`0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is exact, if and only if `P` satisfies the sheaf condition
for the family of maps `U i ⟶ T` and the Čech complex is exact in every positive degree, that is,
the Čech cohomology of `P` for `U` vanishes in every positive degree. This unpacks acyclicity in the
sense of [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition A.1, so that it can be proved or used
degree by degree; the degree `0` part alone is `quasiIsoAt_cechAugmentation_zero_iff`. -/
theorem quasiIso_cechAugmentation_iff : QuasiIso (cechAugmentation U hT P) ↔
    (∀ E : Aᵒᵖ, (Presieve.ofArrows U fun i ↦ hT.from (U i)).IsSheafFor (P ⋙ coyoneda.obj E)) ∧
      ∀ n, ((cechComplexFunctor U).obj P).ExactAt (n + 1) := by
  rw [quasiIso_iff, ← Nat.and_forall_add_one, quasiIsoAt_cechAugmentation_zero_iff]
  simp [quasiIsoAt_iff_exactAt, CochainComplex.exactAt_succ_single_obj]

/-- If some member `U i₀` of the family receives a map `f : T ⟶ U i₀` from the terminal object,
equivalently if `U i₀ ⟶ T` is a split epimorphism, then the augmentation of the Čech complex of
every presheaf `P` for `U` is a quasi-isomorphism: the augmented Čech complex
`0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is exact. For an open cover of `W`, viewed in `Over W`, such
a map exists exactly when `W` is itself a member of the cover. -/
@[stacks 0G6S "exactness of the extended Čech complex"]
theorem quasiIso_cechAugmentation_of_hom {i₀ : ι} (f : T ⟶ U i₀) :
    QuasiIso (cechAugmentation U hT P) := by
  -- `f` gives an extra degeneracy of the augmented Čech object, so that its augmentation `ε` is a
  -- homotopy equivalence
  have : QuasiIso (AlternatingFaceMapComplex.ε.app (augmentedCech U hT P)) :=
    (((FormalCoproduct.mk _ U).extraDegeneracyCech hT f).map
      ((FormalCoproduct.evalOp C A).obj P).rightOp).homotopyEquiv.quasiIso_hom
  have hε : QuasiIso ((HomologicalComplex.unopFunctor _ _).map
    (AlternatingFaceMapComplex.ε.app (augmentedCech U hT P)).op) := inferInstance
  -- the isomorphisms on either side are quasi-isomorphisms, as homotopy equivalences
  exact quasiIso_comp _ _ (hφ := (HomotopyEquiv.ofIso (singleIso U hT P)).quasiIso_hom)
    (hφ' := quasiIso_comp _ _ (hφ := hε)
      (hφ' := (HomotopyEquiv.ofIso (unopAlternatingFaceMapComplexIso U P)).quasiIso_hom))

section Map

variable {U} {κ : Type w} {V : κ → C}

/-- **Acyclicity of the Čech complex depends only on the family up to maps both ways.** If there
are morphisms of families `U ⟶ V` and `V ⟶ U`, for instance if `U` and `V` are open covers each
refining the other, then the augmented Čech complex of `P` for `U` is exact if and only if the one
for `V` is. -/
theorem quasiIso_cechAugmentation_congr (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U) :
    QuasiIso (cechAugmentation U hT P) ↔ QuasiIso (cechAugmentation V hT P) := by
  have : QuasiIso (cechComplexMap P φ) := (cechComplexHomotopyEquiv P φ ψ).quasiIso_hom
  rw [← cechAugmentation_comp_cechComplexMap hT P φ]
  exact quasiIso_iff_comp_right _ _

end Map

/-- **Acyclicity of a family is invariant under isomorphisms of presheaves.** If `P ≅ Q`, then the
augmented Čech complex of `P` for `U` is exact if and only if the one for `Q` is. -/
theorem quasiIso_cechAugmentation_iff_of_iso {Q : Cᵒᵖ ⥤ A} (e : P ≅ Q) :
    QuasiIso (cechAugmentation U hT P) ↔ QuasiIso (cechAugmentation U hT Q) := by
  rw [← quasiIso_iff_comp_right _ ((cechComplexFunctor U).map e.hom), cechAugmentation_naturality]
  exact quasiIso_iff_comp_left _ _

end TauCeti.CategoryTheory
end
end
end GeometryLiteralSource013

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic"

section GeometryLiteralSource014
/- Original source: TauCeti.CategoryTheory.Limits.Shapes.BinaryProducts -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Binary products with a terminal object

Mathlib's `CategoryTheory.Limits.prod.leftUnitor` and `CategoryTheory.Limits.prod.rightUnitor`
identify `⊤_ C ⨯ X` and `X ⨯ ⊤_ C` with `X` for the chosen terminal object `⊤_ C`. This file gives
the same identifications, natural in `X`, for an arbitrary terminal object `T`.

## Main definitions

* `CategoryTheory.Limits.IsTerminal.prodRightUnitor`: the projections `X ⨯ T ⟶ X`, as a natural
  isomorphism `(- ⨯ T) ≅ 𝟭 C`.
* `CategoryTheory.Limits.IsTerminal.prodLeftUnitor`: the projections `T ⨯ X ⟶ X`, as a natural
  isomorphism `(T ⨯ -) ≅ 𝟭 C`.
-/

public section

noncomputable section

universe v u

namespace CategoryTheory.Limits.IsTerminal

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {T : C} (hT : IsTerminal T)

/-- For a terminal object `T`, the projections `X ⨯ T ⟶ X` onto the first factor form a natural
isomorphism `(- ⨯ T) ≅ 𝟭 C`. -/
def prodRightUnitor : prod.functor.flip.obj T ≅ 𝟭 C :=
  NatIso.ofComponents (fun X ↦
    ({ hom := prod.fst
       inv := prod.lift (𝟙 X) (hT.from X)
       hom_inv_id := prod.hom_ext (by simp) (hT.hom_ext _ _) } : X ⨯ T ≅ X))
    fun f ↦ prod.map_fst f (𝟙 T)

/-- The component of `prodRightUnitor` at `X` is the first projection `X ⨯ T ⟶ X`. -/
@[simp]
lemma prodRightUnitor_hom_app (X : C) : hT.prodRightUnitor.hom.app X = (prod.fst : X ⨯ T ⟶ X) := by
  rfl

/-- The inverse component of `prodRightUnitor` at `X` is `prod.lift (𝟙 X) (hT.from X)`. -/
@[simp]
lemma prodRightUnitor_inv_app (X : C) :
    hT.prodRightUnitor.inv.app X = (prod.lift (𝟙 X) (hT.from X) : X ⟶ X ⨯ T) := by
  rfl

/-- For a terminal object `T`, the projections `T ⨯ X ⟶ X` onto the second factor form a natural
isomorphism `(T ⨯ -) ≅ 𝟭 C`. -/
def prodLeftUnitor : prod.functor.obj T ≅ 𝟭 C :=
  NatIso.ofComponents (fun X ↦
    ({ hom := prod.snd
       inv := prod.lift (hT.from X) (𝟙 X)
       hom_inv_id := prod.hom_ext (hT.hom_ext _ _) (by simp) } : T ⨯ X ≅ X))
    fun f ↦ prod.map_snd (𝟙 T) f

/-- The component of `prodLeftUnitor` at `X` is the second projection `T ⨯ X ⟶ X`. -/
@[simp]
lemma prodLeftUnitor_hom_app (X : C) : hT.prodLeftUnitor.hom.app X = (prod.snd : T ⨯ X ⟶ X) := by
  rfl

/-- The inverse component of `prodLeftUnitor` at `X` is `prod.lift (hT.from X) (𝟙 X)`. -/
@[simp]
lemma prodLeftUnitor_inv_app (X : C) :
    hT.prodLeftUnitor.inv.app X = (prod.lift (hT.from X) (𝟙 X) : X ⟶ T ⨯ X) := by
  rfl

end CategoryTheory.Limits.IsTerminal
end
end
end GeometryLiteralSource014

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Limits.Shapes.BinaryProducts"

section GeometryLiteralSource015
/- Original source: TauCeti.Algebra.Homology.Functor.Resolution -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Cycles and augmented resolutions of diagrams of complexes

For a diagram `K : D ⥤ HomologicalComplex A c`, the cycles in degree `i` form a diagram in `A`.
Their inclusions and the differentials corestricted to cycles are natural transformations,
forming the short complex `Zⁱ(K) ⟶ Kⁱ ⟶ Zʲ(K)`. At any object where `K` is exact in degree `j`,
this sequence is short exact if `c.Rel i j`.

An augmentation `ε : P ⋙ CochainComplex.single₀ A ⟶ K` gives the short complex
`P ⟶ K⁰ ⟶ Z¹(K)`. It is short exact at any object where `ε` is a quasi-isomorphism in degrees
zero and one. These sequences split an augmented resolution into short exact sequences, allowing
objectwise dimension shifting without imposing exactness at every object of the diagram.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Functor

section Cycles

variable {D A : Type*} [Category* D] [Category* A] [HasZeroMorphisms A]
  [CategoryWithHomology A] {ι : Type*} {c : ComplexShape ι}
  (K : D ⥤ HomologicalComplex A c)

/-- The natural inclusion of the diagram of degree-`i` cycles into the degree-`i` terms. -/
def iCycles (i : ι) : K ⋙ HomologicalComplex.cyclesFunctor A c i ⟶
    K ⋙ HomologicalComplex.eval A c i where
  app Y := (K.obj Y).iCycles i
  naturality _ _ f := HomologicalComplex.cyclesMap_i (K.map f) i

@[simp]
lemma iCycles_app (i : ι) (Y : D) : (K.iCycles i).app Y = (K.obj Y).iCycles i := (rfl)

/-- The differential from degree `i` corestricted to the diagram of degree-`j` cycles. -/
def toCycles (i j : ι) : K ⋙ HomologicalComplex.eval A c i ⟶
    K ⋙ HomologicalComplex.cyclesFunctor A c j where
  app Y := (K.obj Y).toCycles i j
  naturality _ _ f := ((K.obj _).toCycles_cyclesMap (K.map f) i j).symm

@[simp]
lemma toCycles_app (i j : ι) (Y : D) :
    (K.toCycles i j).app Y = (K.obj Y).toCycles i j := (rfl)

/-- The short complex `Zⁱ(K) ⟶ Kⁱ ⟶ Zʲ(K)` of diagrams of cycles and terms. -/
def cyclesShortComplex (i j : ι) : ShortComplex (D ⥤ A) :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i j) <|
    NatTrans.ext <| funext fun Y ↦ (K.obj Y).iCycles_toCycles i j

@[simp]
lemma cyclesShortComplex_X₁ (i j : ι) :
    (K.cyclesShortComplex i j).X₁ = K ⋙ HomologicalComplex.cyclesFunctor A c i := (rfl)

@[simp]
lemma cyclesShortComplex_X₂ (i j : ι) :
    (K.cyclesShortComplex i j).X₂ = K ⋙ HomologicalComplex.eval A c i := (rfl)

@[simp]
lemma cyclesShortComplex_X₃ (i j : ι) :
    (K.cyclesShortComplex i j).X₃ = K ⋙ HomologicalComplex.cyclesFunctor A c j := (rfl)

@[simp]
lemma cyclesShortComplex_f (i j : ι) :
    (K.cyclesShortComplex i j).f = eqToHom (K.cyclesShortComplex_X₁ i j) ≫
      K.iCycles i ≫ eqToHom (K.cyclesShortComplex_X₂ i j).symm := by
  unfold cyclesShortComplex
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp]
lemma cyclesShortComplex_g (i j : ι) :
    (K.cyclesShortComplex i j).g = eqToHom (K.cyclesShortComplex_X₂ i j) ≫
      K.toCycles i j ≫ eqToHom (K.cyclesShortComplex_X₃ i j).symm := by
  unfold cyclesShortComplex
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp]
lemma map_cyclesShortComplex (i j : ι) (Y : D) :
    (K.cyclesShortComplex i j).map ((evaluation D A).obj Y) =
      ShortComplex.mk ((K.obj Y).iCycles i) ((K.obj Y).toCycles i j)
        ((K.obj Y).iCycles_toCycles i j) := (rfl)

end Cycles

variable {D A : Type*} [Category* D] [Category* A] [Preadditive A]
  [CategoryWithHomology A] {ι : Type*} {c : ComplexShape ι}
  (K : D ⥤ HomologicalComplex A c)

/-- The cycle sequence is short exact at an object where the complex is exact in the next degree.
No exactness is required at the other objects of the diagram. -/
lemma shortExact_map_cyclesShortComplex (i j : ι) (hij : c.Rel i j) {Y : D}
    (hY : (K.obj Y).ExactAt j) :
    ((K.cyclesShortComplex i j).map ((evaluation D A).obj Y)).ShortExact := by
  rw [K.map_cyclesShortComplex]
  have : Epi ((K.obj Y).toCycles i j) :=
    HomologicalComplex.epi_toCycles_of_exactAt hY (c.prev_eq' hij)
  exact
    { exact := by
        simpa only [HomologicalComplex.cyclesShortComplex_def] using
          (K.obj Y).cyclesShortComplex_exact i j (c.next_eq' hij)
      mono_f := inferInstanceAs (Mono ((K.obj Y).iCycles i))
      epi_g := inferInstanceAs (Epi ((K.obj Y).toCycles i j)) }

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

section Augmentation

variable {D A : Type*} [Category* D] [Category* A] [HasZeroMorphisms A]
  [HasZeroObject A] {P : D ⥤ A} {K : D ⥤ CochainComplex A ℕ}
  (ε : P ⋙ CochainComplex.single₀ A ⟶ K)

/-- The degree-zero component of an augmentation, as a morphism of diagrams in `A`. -/
def augmentationι : P ⟶ K ⋙ HomologicalComplex.eval A _ 0 :=
  (Functor.rightUnitor P).inv ≫
    Functor.whiskerLeft P (HomologicalComplex.singleCompEvalIsoSelf A (ComplexShape.up ℕ) 0).inv ≫
      (Functor.associator P (CochainComplex.single₀ A) _).inv ≫
        Functor.whiskerRight ε (HomologicalComplex.eval A _ 0)

@[simp]
lemma augmentationι_app (Y : D) :
    ε.augmentationι.app Y =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj Y)).inv ≫ (ε.app Y).f 0 := by
  simp [augmentationι]

variable [CategoryWithHomology A]

/-- The short complex `P ⟶ K⁰ ⟶ Z¹(K)` cut out by an augmented diagram of cochain complexes. -/
def augmentationShortComplex : ShortComplex (D ⥤ A) :=
  ShortComplex.mk ε.augmentationι (K.toCycles 0 1) <|
    NatTrans.ext <| funext fun Y ↦ by
      rw [NatTrans.comp_app, zero_app, augmentationι_app, Functor.toCycles_app]
      exact (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (HomologicalComplex.single_f_toCycles (ε.app Y) 1)).trans comp_zero

@[simp]
lemma augmentationShortComplex_X₁ : ε.augmentationShortComplex.X₁ = P := (rfl)

@[simp]
lemma augmentationShortComplex_X₂ :
    ε.augmentationShortComplex.X₂ = K ⋙ HomologicalComplex.eval A _ 0 := (rfl)

@[simp]
lemma augmentationShortComplex_X₃ :
    ε.augmentationShortComplex.X₃ = K ⋙ HomologicalComplex.cyclesFunctor A _ 1 := (rfl)

@[simp]
lemma augmentationShortComplex_f :
    ε.augmentationShortComplex.f = eqToHom ε.augmentationShortComplex_X₁ ≫
      ε.augmentationι ≫ eqToHom ε.augmentationShortComplex_X₂.symm := by
  unfold augmentationShortComplex
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp]
lemma augmentationShortComplex_g :
    ε.augmentationShortComplex.g = eqToHom ε.augmentationShortComplex_X₂ ≫
      K.toCycles 0 1 ≫ eqToHom ε.augmentationShortComplex_X₃.symm := by
  unfold augmentationShortComplex
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp]
lemma map_augmentationShortComplex (Y : D) :
    ε.augmentationShortComplex.map ((evaluation D A).obj Y) =
      ShortComplex.mk
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj Y)).inv ≫ (ε.app Y).f 0)
        ((K.obj Y).toCycles 0 1)
        ((Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (HomologicalComplex.single_f_toCycles (ε.app Y) 1)).trans
            comp_zero) := by
  dsimp only [augmentationShortComplex, ShortComplex.map]
  simp only [evaluation_obj_map, augmentationι_app, Functor.toCycles_app]
  rfl

end Augmentation

variable {D A : Type*} [Category* D] [Category* A] [Preadditive A]
  [HasZeroObject A] [CategoryWithHomology A] {P : D ⥤ A} {K : D ⥤ CochainComplex A ℕ}
  (ε : P ⋙ CochainComplex.single₀ A ⟶ K)

/-- The augmented sequence is short exact at any object where the augmentation is a
quasi-isomorphism in degrees zero and one. No condition on its higher cohomology is needed. -/
lemma shortExact_map_augmentationShortComplex {Y : D}
    (h₀ : QuasiIsoAt (ε.app Y) 0) (h₁ : QuasiIsoAt (ε.app Y) 1) :
    (ε.augmentationShortComplex.map ((evaluation D A).obj Y)).ShortExact := by
  rw [ε.map_augmentationShortComplex]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj Y)
  let ψ := (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℕ) 0 0 1).map
    (ε.app Y)
  -- In degree zero, the augmentation identifies its source with the kernel of the differential.
  have hψ := (ShortComplex.quasiIso_iff_isIso_liftCycles ψ
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) _ _ _ _)
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) _ _ _ _)
    ((K.obj Y).shape 0 0 (by simp))).1
      ((CochainComplex.quasiIsoAt₀_iff (ε.app Y)).1 h₀)
  let S := (K.obj Y).sc' 0 0 1
  let l := S.liftCycles ((ε.app Y).f 0) (HomologicalComplex.single_f_d (ε.app Y) 1)
  have : IsIso (S.liftCycles ((ε.app Y).f 0)
      (HomologicalComplex.single_f_d (ε.app Y) 1)) := hψ
  have hk : IsLimit (KernelFork.ofι ((ε.app Y).f 0)
      (HomologicalComplex.single_f_d (ε.app Y) 1)) :=
    IsLimit.ofIsoLimit S.cyclesIsKernel
      (Fork.ext (asIso l).symm (by
        apply (cancel_epi l).1
        simp only [Iso.symm_hom, ← Category.assoc, asIso_inv, IsIso.hom_inv_id,
          Category.id_comp]
        erw [KernelFork.ι_ofι, KernelFork.ι_ofι]
        exact (S.liftCycles_i _ _).symm))
  have hmono : Mono ((ε.app Y).f 0) := mono_of_isLimit_fork hk
  have hexact : (ShortComplex.mk ((ε.app Y).f 0) ((K.obj Y).d 0 1)
      (HomologicalComplex.single_f_d (ε.app Y) 1)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ hk
  -- Exactness in degree one makes the differential onto the next cycles an epimorphism.
  have h₁' : (K.obj Y).ExactAt 1 := (quasiIsoAt_iff_exactAt (ε.app Y) 1
    (CochainComplex.exactAt_succ_single_obj _ 0)).1 h₁
  have : Epi ((K.obj Y).toCycles 0 1) :=
    HomologicalComplex.epi_toCycles_of_exactAt h₁' (by simp)
  let φ : ShortComplex.mk
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj Y)).inv ≫ (ε.app Y).f 0)
      ((K.obj Y).toCycles 0 1) ((Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (HomologicalComplex.single_f_toCycles (ε.app Y) 1)).trans comp_zero) ⟶
      ShortComplex.mk ((ε.app Y).f 0) ((K.obj Y).d 0 1)
        (HomologicalComplex.single_f_d (ε.app Y) 1) :=
    { τ₁ := e.inv
      τ₂ := 𝟙 _
      τ₃ := (K.obj Y).iCycles 1
      comm₁₂ := (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (HomologicalComplex.toCycles_i _ _ _).symm }
  -- The degree-zero term of a single complex is identified with `P(Y)` by `e`.
  exact
    { exact := (@ShortComplex.exact_iff_of_epi_of_isIso_of_mono _ _ _ _ _ φ
        (inferInstanceAs (Epi e.inv)) (inferInstanceAs (IsIso (𝟙 _)))
        (inferInstanceAs (Mono ((K.obj Y).iCycles 1)))).2 hexact
      mono_f := @mono_comp _ _ _ _ _ e.inv inferInstance ((ε.app Y).f 0) hmono
      epi_g := inferInstanceAs (Epi ((K.obj Y).toCycles 0 1)) }

end CategoryTheory.NatTrans
end
end
end GeometryLiteralSource015

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Algebra.Homology.Functor.Resolution"

section GeometryLiteralSource016
/- Original source: TauCeti.Algebra.Homology.HomologySequenceLemmas -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Lemmas on the homology sequence of a short exact sequence of complexes

Let `φ : S₁ ⟶ S₂` be a morphism between two short exact sequences of homological complexes in an
abelian category. Mathlib's `HomologicalComplex.HomologySequence.quasiIso_τ₃` shows that `φ.τ₃`
is a quasi-isomorphism when `φ.τ₁` and `φ.τ₂` are. This file proves the corresponding statement
for the middle map: `φ.τ₂` is a quasi-isomorphism when `φ.τ₁` and `φ.τ₃` are. This lets one
transfer a quasi-isomorphism to the middle terms of short exact sequences after comparing their
outer terms, as for the short exact sequences associated with maps of mapping cones. It also proves
the degreewise statements for the left map `φ.τ₁`, which are the dimension-shifting steps that
compare the homology of a kernel with that of a cokernel one degree lower. For a single short
exact sequence, it characterizes when either of its maps is a quasi-isomorphism by acyclicity of
the opposite outer term.

It also proves that the connecting maps of a `3 × 3` diagram of complexes with short exact rows
and columns anticommute: the two composites of connecting maps from the homology of one corner to
that of the opposite corner differ by a sign. Both composites factor through the connecting maps of
two auxiliary short exact sequences, `ker (X₂₂ ⟶ X₃₃) ⟶ X₂₂ ⟶ X₃₃` and
`X₁₁ ⟶ X₁₂ ⊞ X₂₁ ⟶ ker (X₂₂ ⟶ X₃₃)`, and the sign is that of the first map `(f, -f)` of the
second one. This is the sign rule behind the compatibility of products with connecting maps in each
variable, such as for the cup product in Tate cohomology.

## Main results

* `HomologicalComplex.HomologySequence.mono_homologyMap_τ₂`,
  `HomologicalComplex.HomologySequence.epi_homologyMap_τ₂`,
  `HomologicalComplex.HomologySequence.isIso_homologyMap_τ₂`: sufficient conditions for `φ.τ₂`
  to induce a mono, epi or iso in a given degree.
* `HomologicalComplex.HomologySequence.quasiIso_τ₂`: if `φ.τ₁` and `φ.τ₃` are
  quasi-isomorphisms, so is `φ.τ₂`.
* `HomologicalComplex.HomologySequence.mono_homologyMap_τ₁`,
  `HomologicalComplex.HomologySequence.epi_homologyMap_τ₁`,
  `HomologicalComplex.HomologySequence.isIso_homologyMap_τ₁`: sufficient conditions for `φ.τ₁`
  to induce a mono, epi or iso in a given degree.
* `HomologicalComplex.HomologySequence.quasiIso_τ₁`: if `φ.τ₂` and `φ.τ₃` are
  quasi-isomorphisms, so is `φ.τ₁`.
* `CategoryTheory.ShortComplex.ShortExact.quasiIso_f_iff`,
  `CategoryTheory.ShortComplex.ShortExact.quasiIso_g_iff`: in a short exact sequence of
  complexes, the first map is a quasi-isomorphism if and only if the third term is acyclic, and
  the second map is one if and only if the first term is acyclic.
* `HomologicalComplex.HomologySequence.δ_comp_δ_eq_neg`: the connecting maps of a `3 × 3` diagram
  with short exact rows and columns anticommute.
-/

public section

open CategoryTheory ComposableArrows Abelian

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

namespace HomologicalComplex

namespace HomologySequence

include hS₁ hS₂

/-- The map `φ.τ₂` is injective on homology in degree `j` if `φ.τ₁` and `φ.τ₃` are injective in
degree `j` and `φ.τ₃` is surjective in the degrees preceding `j`. -/
lemma mono_homologyMap_τ₂ (j : ι)
    (h₁ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i))
    (h₂ : Mono (homologyMap φ.τ₁ j))
    (h₃ : Mono (homologyMap φ.τ₃ j)) :
    Mono (homologyMap φ.τ₂ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    -- The exact sequence `H_i(X₃) ⟶ H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃)`.
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δ₀
    · exact h₁ i hij
    · exact h₂
    · exact h₃
  · have := hS₂.mono_f
    have := mono_homologyMap_of_mono_of_not_rel S₂.f j (by simpa using hj)
    exact mono_of_mono_of_mono_of_mono (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₁ j) this h₂ h₃

/-- The map `φ.τ₂` is surjective on homology in degree `j` if `φ.τ₁` and `φ.τ₃` are surjective in
degree `j` and `φ.τ₁` is injective in the degrees following `j`. -/
lemma epi_homologyMap_τ₂ (j : ι)
    (h₁ : Epi (homologyMap φ.τ₁ j))
    (h₂ : Epi (homologyMap φ.τ₃ j))
    (h₃ : ∀ k, c.Rel j k → Mono (homologyMap φ.τ₁ k)) :
    Epi (homologyMap φ.τ₂ j) := by
  by_cases hj : ∃ k, c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    -- The exact sequence `H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃) ⟶ H_k(X₁)`.
    apply epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ j k hjk))
    · exact (composableArrows₅_exact hS₁ j k hjk).δlast.δlast
    · exact (composableArrows₅_exact hS₂ j k hjk).δlast.δlast
    · exact h₁
    · exact h₂
    · exact h₃ k hjk
  · have := hS₁.epi_g
    have := epi_homologyMap_of_epi_of_not_rel S₁.g j (by simpa using hj)
    exact epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₂ j) this h₁ h₂

/-- The map `φ.τ₂` is an isomorphism on homology in degree `j` if `φ.τ₁` and `φ.τ₃` are
isomorphisms in degree `j`, `φ.τ₃` is surjective in the degrees preceding `j`, and `φ.τ₁` is
injective in the degrees following `j`. -/
lemma isIso_homologyMap_τ₂ (j : ι)
    (h₁ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i))
    (h₂ : IsIso (homologyMap φ.τ₁ j))
    (h₃ : IsIso (homologyMap φ.τ₃ j))
    (h₄ : ∀ k, c.Rel j k → Mono (homologyMap φ.τ₁ k)) :
    IsIso (homologyMap φ.τ₂ j) := by
  have := mono_homologyMap_τ₂ φ hS₁ hS₂ j h₁ inferInstance inferInstance
  have := epi_homologyMap_τ₂ φ hS₁ hS₂ j inferInstance inferInstance h₄
  exact isIso_of_mono_of_epi _

/-- **Two out of three for the middle map.** In a morphism of short exact sequences of complexes,
if the outer maps `φ.τ₁` and `φ.τ₃` are quasi-isomorphisms, so is the middle map `φ.τ₂`. -/
lemma quasiIso_τ₂ (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_homologyMap_τ₂ φ hS₁ hS₂
  all_goals infer_instance

/-- The map `φ.τ₁` is injective on homology in degree `j` if `φ.τ₂` is injective in degree `j`,
and in the degrees preceding `j` the map `φ.τ₂` is surjective and `φ.τ₃` is injective. -/
lemma mono_homologyMap_τ₁ (j : ι)
    (h₁ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₂ i))
    (h₂ : ∀ i, c.Rel i j → Mono (homologyMap φ.τ₃ i))
    (h₃ : Mono (homologyMap φ.τ₂ j)) :
    Mono (homologyMap φ.τ₁ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    -- The exact sequence `H_i(X₂) ⟶ H_i(X₃) ⟶ H_j(X₁) ⟶ H_j(X₂)`.
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δlast
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δlast
    · exact h₁ i hij
    · exact h₂ i hij
    · exact h₃
  · -- With no preceding degree, `H_j(X₁) ⟶ H_j(X₂)` is injective.
    have := hS₁.mono_f
    have := mono_homologyMap_of_mono_of_not_rel S₁.f j (by simpa using hj)
    have h := (homologyFunctor C c j).congr_map φ.comm₁₂
    simp only [homologyFunctor_map, homologyMap_comp] at h
    exact mono_of_mono_fac h

/-- The map `φ.τ₁` is surjective on homology in degree `j` if `φ.τ₂` is surjective and `φ.τ₃` is
injective in degree `j`, and `φ.τ₃` is surjective in the degrees preceding `j`. -/
lemma epi_homologyMap_τ₁ (j : ι)
    (h₁ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i))
    (h₂ : Epi (homologyMap φ.τ₂ j))
    (h₃ : Mono (homologyMap φ.τ₃ j)) :
    Epi (homologyMap φ.τ₁ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    -- The exact sequence `H_i(X₃) ⟶ H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃)`.
    apply epi_of_epi_of_epi_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δ₀
    · exact h₁ i hij
    · exact h₂
    · exact h₃
  · have := hS₂.mono_f
    have := mono_homologyMap_of_mono_of_not_rel S₂.f j (by simpa using hj)
    exact epi_of_mono_of_epi_of_mono (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₁ j) (composableArrows₂_exact hS₂ j) this h₂ h₃

/-- The map `φ.τ₁` is an isomorphism on homology in degree `j` if `φ.τ₂` is an isomorphism and
`φ.τ₃` is injective in degree `j`, and in the degrees preceding `j` the map `φ.τ₂` is surjective
and `φ.τ₃` is an isomorphism. -/
lemma isIso_homologyMap_τ₁ (j : ι)
    (h₁ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₂ i))
    (h₂ : ∀ i, c.Rel i j → IsIso (homologyMap φ.τ₃ i))
    (h₃ : IsIso (homologyMap φ.τ₂ j))
    (h₄ : Mono (homologyMap φ.τ₃ j)) :
    IsIso (homologyMap φ.τ₁ j) := by
  have := mono_homologyMap_τ₁ φ hS₁ hS₂ j h₁ (fun i hij ↦ have := h₂ i hij; inferInstance)
    inferInstance
  have := epi_homologyMap_τ₁ φ hS₁ hS₂ j (fun i hij ↦ have := h₂ i hij; inferInstance)
    inferInstance h₄
  exact isIso_of_mono_of_epi _

/-- **Two out of three for the left map.** In a morphism of short exact sequences of complexes, if
`φ.τ₂` and `φ.τ₃` are quasi-isomorphisms, so is the left map `φ.τ₁`. -/
lemma quasiIso_τ₁ (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₁ := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_homologyMap_τ₁ φ hS₁ hS₂
  all_goals infer_instance

end HomologySequence

end HomologicalComplex

/-! ### Short exact sequences with an acyclic outer term -/

namespace CategoryTheory.ShortComplex.ShortExact

open HomologicalComplex

variable {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)
include hS

/-- In a short exact sequence of complexes, the first map is a quasi-isomorphism if and only if
the third term is acyclic. -/
lemma quasiIso_f_iff : _root_.QuasiIso S.f ↔ S.X₃.Acyclic := by
  refine ⟨hS.acyclic_X₃, fun h ↦ (_root_.quasiIso_iff _).2 fun j ↦ ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Epi (HomologicalComplex.homologyMap S.f j) :=
    (hS.homology_exact₂ j).epi_f ((h j).isZero_homology.eq_of_tgt _ _)
  have : Mono (HomologicalComplex.homologyMap S.f j) := by
    by_cases! hj : ∃ i, c.Rel i j
    · obtain ⟨i, hij⟩ := hj
      exact (hS.homology_exact₁ i j hij).mono_g ((h i).isZero_homology.eq_of_src _ _)
    · have := hS.mono_f
      exact mono_homologyMap_of_mono_of_not_rel S.f j hj
  exact isIso_of_mono_of_epi _

/-- In a short exact sequence of complexes, the second map is a quasi-isomorphism if and only if
the first term is acyclic. -/
lemma quasiIso_g_iff : _root_.QuasiIso S.g ↔ S.X₁.Acyclic := by
  refine ⟨hS.acyclic_X₁, fun h ↦ (_root_.quasiIso_iff _).2 fun i ↦ ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (HomologicalComplex.homologyMap S.g i) :=
    (hS.homology_exact₂ i).mono_g ((h i).isZero_homology.eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap S.g i) := by
    by_cases! hi : ∃ j, c.Rel i j
    · obtain ⟨j, hij⟩ := hi
      exact (hS.homology_exact₃ i j hij).epi_f ((h j).isZero_homology.eq_of_tgt _ _)
    · have := hS.epi_g
      exact epi_homologyMap_of_epi_of_not_rel S.g i hi
  exact isIso_of_mono_of_epi _

end CategoryTheory.ShortComplex.ShortExact


/-! ### Anticommutativity of the connecting maps of a `3 × 3` diagram -/

open Limits

namespace ThreeByThree

section

variable {A : Type*} [Category* A] [HasZeroMorphisms A] [HasKernels A]
  (D : ShortComplex (ShortComplex A))

/-- The kernel of the diagonal `X₂₂ ⟶ X₃₃` of a `3 × 3` diagram. -/
private noncomputable abbrev K : A := kernel (D.X₂.g ≫ D.g.τ₃)

/-- The inclusion of the kernel of the diagonal. -/
private noncomputable abbrev incl : K D ⟶ D.X₂.X₂ := kernel.ι (D.X₂.g ≫ D.g.τ₃)

end

section

variable {A : Type*} [Category* A] [Preadditive A] [Balanced A] [HasKernels A]
  (D : ShortComplex (ShortComplex A))

/-- The map from the kernel of the diagonal to `X₃₁`. -/
private noncomputable def toX₃₁ (h₃ : D.X₃.ShortExact) : K D ⟶ D.X₃.X₁ :=
  have := h₃.mono_f
  h₃.exact.lift (incl D ≫ D.g.τ₂) (by rw [Category.assoc, D.g.comm₂₃, kernel.condition])

private lemma toX₃₁_f (h₃ : D.X₃.ShortExact) : toX₃₁ D h₃ ≫ D.X₃.f = incl D ≫ D.g.τ₂ :=
  have := h₃.mono_f
  h₃.exact.lift_f _ _

/-- The map from the kernel of the diagonal to `X₁₃`. -/
private noncomputable def toX₁₃ (h₃' : (D.map ShortComplex.π₃).ShortExact) : K D ⟶ D.X₁.X₃ :=
  have := h₃'.mono_f
  h₃'.exact.lift (incl D ≫ D.X₂.g)
    ((Category.assoc _ _ _).trans (kernel.condition (D.X₂.g ≫ D.g.τ₃)))

private lemma toX₁₃_f (h₃' : (D.map ShortComplex.π₃).ShortExact) :
    toX₁₃ D h₃' ≫ D.f.τ₃ = incl D ≫ D.X₂.g :=
  have := h₃'.mono_f
  h₃'.exact.lift_f _ _

end

variable {A : Type*} [Category* A] [Abelian A] (D : ShortComplex (ShortComplex A))

/-- The morphism from the kernel sequence of the diagonal to the third row. -/
private noncomputable def diagSequenceToRow₃ (h₃ : D.X₃.ShortExact) :
    ShortComplex.kernelSequence (D.X₂.g ≫ D.g.τ₃) ⟶ D.X₃ where
  τ₁ := toX₃₁ D h₃
  τ₂ := D.g.τ₂
  τ₃ := 𝟙 _
  comm₁₂ := toX₃₁_f D h₃
  comm₂₃ := D.g.comm₂₃.trans (Category.comp_id _).symm

/-- The morphism from the kernel sequence of the diagonal to the third column. -/
private noncomputable def diagSequenceToCol₃ (h₃' : (D.map ShortComplex.π₃).ShortExact) :
    ShortComplex.kernelSequence (D.X₂.g ≫ D.g.τ₃) ⟶ D.map ShortComplex.π₃ where
  τ₁ := toX₁₃ D h₃'
  τ₂ := D.X₂.g
  τ₃ := 𝟙 _
  comm₁₂ := toX₁₃_f D h₃'
  comm₂₃ := (Category.comp_id _).symm

section

variable {A : Type*} [Category* A] [HasZeroMorphisms A] [HasBinaryBiproducts A] [HasKernels A]
  (D : ShortComplex (ShortComplex A))

/-- The map `X₁₂ ⊞ X₂₁ ⟶ ker (X₂₂ ⟶ X₃₃)` induced by the sum of the two maps to `X₂₂`. -/
private noncomputable def toK : D.X₁.X₂ ⊞ D.X₂.X₁ ⟶ K D :=
  kernel.lift _ (biprod.desc D.f.τ₂ D.X₂.f) (by
    ext
    · rw [biprod.inl_desc_assoc, ← Category.assoc, D.f.comm₂₃, Category.assoc,
        ← ShortComplex.comp_τ₃, D.zero, ShortComplex.zero_τ₃, comp_zero, comp_zero]
    · rw [biprod.inr_desc_assoc, ← Category.assoc, D.X₂.zero, zero_comp, comp_zero])

private lemma toK_incl : toK D ≫ incl D = biprod.desc D.f.τ₂ D.X₂.f := kernel.lift_ι _ _ _

end

/-- The short complex `X₁₁ ⟶ X₁₂ ⊞ X₂₁ ⟶ ker (X₂₂ ⟶ X₃₃)`, whose first map is `(f, -f)`. -/
private noncomputable abbrev crossSequence : ShortComplex A :=
  ShortComplex.mk (biprod.lift D.X₁.f (-D.f.τ₁)) (toK D) (by
    rw [← cancel_mono (incl D), Category.assoc, toK_incl, biprod.lift_desc, zero_comp,
      Preadditive.neg_comp, D.f.comm₁₂, add_neg_cancel])

variable {D}

private lemma crossSequence_shortExact (h₁ : D.X₁.ShortExact) (h₂ : D.X₂.ShortExact)
    (h₃ : D.X₃.ShortExact) (h₁' : (D.map ShortComplex.π₁).ShortExact)
    (h₂' : (D.map ShortComplex.π₂).ShortExact)
    (h₃' : (D.map ShortComplex.π₃).ShortExact) :
    (crossSequence D).ShortExact := by
  have := h₁.mono_f
  have := h₂.mono_f
  have : Epi D.g.τ₁ := h₁'.epi_g
  have : Mono D.f.τ₂ := h₂'.mono_f
  have : Mono D.f.τ₃ := h₃'.mono_f
  have : Mono (crossSequence D).f := mono_of_mono_fac (biprod.lift_fst D.X₁.f (-D.f.τ₁))
  have : Epi (crossSequence D).g := by
    rw [epi_iff_surjective_up_to_refinements]
    intro B y
    -- The image of `y` in `X₃₂` comes from `X₃₁`; lift it to `X₂₁` up to refinement.
    obtain ⟨B', π, _, a, ha⟩ := surjective_up_to_refinements_of_epi D.g.τ₁ (y ≫ toX₃₁ D h₃)
    -- The difference of `y` and the image of `a` in `X₂₂` comes from `X₁₂`.
    have hb : (π ≫ y ≫ incl D - a ≫ D.X₂.f) ≫ D.g.τ₂ = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, Category.assoc, ← toX₃₁_f D h₃, ← Category.assoc y,
        ← Category.assoc π, ha, Category.assoc, Category.assoc, D.g.comm₁₂, sub_self]
    have := h₂'.mono_f
    let b : B' ⟶ D.X₁.X₂ := h₂'.exact.lift _ hb
    have hb' : b ≫ D.f.τ₂ = π ≫ y ≫ incl D - a ≫ D.X₂.f := h₂'.exact.lift_f _ hb
    refine ⟨B', π, inferInstance, biprod.lift b a, ?_⟩
    rw [← cancel_mono (incl D), Category.assoc, Category.assoc, toK_incl, biprod.lift_desc, hb',
      sub_add_cancel]
  refine { exact := ?_ }
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro B x hx
  have hx' : x ≫ biprod.fst ≫ D.f.τ₂ + x ≫ biprod.snd ≫ D.X₂.f = 0 := by
    have e := hx =≫ incl D
    rwa [Category.assoc, toK_incl, zero_comp, biprod.desc_eq, Preadditive.comp_add] at e
  -- The first component of `x` comes from `X₁₁`.
  have hb : (x ≫ biprod.fst) ≫ D.X₁.g = 0 := by
    rw [← cancel_mono D.f.τ₃, Category.assoc, Category.assoc, ← D.f.comm₂₃, zero_comp,
      ← Category.assoc biprod.fst, ← Category.assoc x, eq_neg_of_add_eq_zero_left hx',
      Preadditive.neg_comp, Category.assoc, Category.assoc, D.X₂.zero, comp_zero, comp_zero,
      neg_zero]
  refine ⟨B, 𝟙 B, inferInstance, h₁.exact.lift _ hb, ?_⟩
  ext
  · rw [Category.id_comp, Category.assoc, biprod.lift_fst, h₁.exact.lift_f]
  · rw [Category.id_comp, Category.assoc, biprod.lift_snd, ← cancel_mono D.X₂.f]
    simp only [Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp, D.f.comm₁₂]
    rw [← Category.assoc (h₁.exact.lift _ hb), h₁.exact.lift_f, Category.assoc]
    exact eq_neg_of_add_eq_zero_right hx'

/-- The morphism from the cross sequence to the first row: the identity on `X₁₁` and the first
projection on `X₁₂ ⊞ X₂₁`. -/
private noncomputable def crossSequenceToRow₁ (h₃' : (D.map ShortComplex.π₃).ShortExact) :
    crossSequence D ⟶ D.X₁ where
  τ₁ := 𝟙 _
  τ₂ := biprod.fst
  τ₃ := toX₁₃ D h₃'
  comm₁₂ := by rw [Category.id_comp]; exact (biprod.lift_fst D.X₁.f (-D.f.τ₁)).symm
  comm₂₃ := by
    have : Mono D.f.τ₃ := h₃'.mono_f
    rw [← cancel_mono D.f.τ₃]
    simp only [Category.assoc, toX₁₃_f]
    ext
    · simp [← D.f.comm₂₃, ← Category.assoc, toK_incl]
    · simp [← Category.assoc, toK_incl]

/-- The morphism from the cross sequence to the first column: minus the identity on `X₁₁` and the
second projection on `X₁₂ ⊞ X₂₁`. -/
private noncomputable def crossSequenceToCol₁ (h₃ : D.X₃.ShortExact) :
    crossSequence D ⟶ D.map ShortComplex.π₁ where
  τ₁ := -𝟙 _
  τ₂ := biprod.snd
  τ₃ := toX₃₁ D h₃
  comm₁₂ := by
    dsimp only [ShortComplex.map, ShortComplex.π₁]
    rw [Preadditive.neg_comp, Category.id_comp, biprod.lift_snd]
  comm₂₃ := by
    dsimp only [ShortComplex.map, ShortComplex.π₁]
    have := h₃.mono_f
    rw [← cancel_mono D.X₃.f]
    simp only [Category.assoc, toX₃₁_f]
    ext
    · simp [← Category.assoc, toK_incl, ← ShortComplex.comp_τ₂, D.zero]
    · simp [← Category.assoc, toK_incl, D.g.comm₁₂]

end ThreeByThree

namespace HomologicalComplex.HomologySequence

open ThreeByThree in
/-- **The connecting maps of a `3 × 3` diagram anticommute.** Let `D` be a `3 × 3` diagram of
homological complexes in an abelian category, presented as a short complex `D.X₁ ⟶ D.X₂ ⟶ D.X₃`
of short complexes, all of whose rows `D.Xᵢ` and columns `D.map π_j` are short exact. Then the two
composites of connecting maps from the homology of the corner `X₃₃` to that of the corner `X₁₁`,
through the third row and the first column, and through the third column and the first row,
differ by a sign. -/
lemma δ_comp_δ_eq_neg (D : ShortComplex (ShortComplex (HomologicalComplex C c)))
    (h₁ : D.X₁.ShortExact) (h₂ : D.X₂.ShortExact) (h₃ : D.X₃.ShortExact)
    (h₁' : (D.map ShortComplex.π₁).ShortExact) (h₂' : (D.map ShortComplex.π₂).ShortExact)
    (h₃' : (D.map ShortComplex.π₃).ShortExact) (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    h₃.δ i j hij ≫ h₁'.δ j k hjk = -(h₃'.δ i j hij ≫ h₁.δ j k hjk) := by
  have : Epi (D.X₂.g ≫ D.g.τ₃) := by
    have := h₂.epi_g
    have : Epi D.g.τ₃ := h₃'.epi_g
    exact epi_comp _ _
  have hE := TauCeti.kernelSequence_shortExact (D.X₂.g ≫ D.g.τ₃)
  have hT := crossSequence_shortExact (A := HomologicalComplex C c) h₁ h₂ h₃ h₁' h₂' h₃'
  -- Give the auxiliary and column connecting maps the diagram's objects as endpoints, so rewriting
  -- does not need to unfold the chosen kernels and the column projection functors.
  let δE : D.X₃.X₃.homology i ⟶ (K D).homology j := hE.δ i j hij
  let δT : (K D).homology j ⟶ D.X₁.X₁.homology k := hT.δ j k hjk
  let δC₁ : D.X₃.X₁.homology j ⟶ D.X₁.X₁.homology k := h₁'.δ j k hjk
  let δC₃ : D.X₃.X₃.homology i ⟶ D.X₁.X₃.homology j := h₃'.δ i j hij
  -- The connecting maps of the third row and column factor through the one of the kernel sequence
  -- of the diagonal `X₂₂ ⟶ X₃₃`, and the connecting maps of the first row and column factor,
  -- with opposite signs, through the one of the cross sequence `X₁₁ ⟶ X₁₂ ⊞ X₂₁ ⟶ ker`.
  have eR₃ : δE ≫ homologyMap (toX₃₁ D h₃) j = homologyMap (𝟙 _) i ≫ h₃.δ i j hij :=
    δ_naturality (diagSequenceToRow₃ D h₃) hE h₃ i j hij
  have eC₃ : δE ≫ homologyMap (toX₁₃ D h₃') j = homologyMap (𝟙 _) i ≫ δC₃ :=
    δ_naturality (diagSequenceToCol₃ D h₃') hE h₃' i j hij
  have eR₁ : δT ≫ homologyMap (𝟙 _) k = homologyMap (toX₁₃ D h₃') j ≫ h₁.δ j k hjk :=
    δ_naturality (crossSequenceToRow₁ h₃') hT h₁ j k hjk
  have eC₁ : δT ≫ homologyMap (-𝟙 _) k = homologyMap (toX₃₁ D h₃) j ≫ δC₁ :=
    δ_naturality (crossSequenceToCol₁ h₃) hT h₁' j k hjk
  rw [homologyMap_id, Category.id_comp] at eR₃ eC₃
  rw [homologyMap_id, Category.comp_id] at eR₁
  rw [homologyMap_neg, homologyMap_id, Preadditive.comp_neg, Category.comp_id] at eC₁
  suffices h₃.δ i j hij ≫ δC₁ = -(δC₃ ≫ h₁.δ j k hjk) from this
  rw [← eR₃, ← eC₃, Category.assoc, Category.assoc, ← eC₁, ← eR₁,
    Preadditive.comp_neg]

end HomologicalComplex.HomologySequence
end
end GeometryLiteralSource016

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Algebra.Homology.HomologySequenceLemmas"

section GeometryLiteralSource017
/- Original source: TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Exact -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Short exact coefficient sequences and Čech acyclicity

The Čech complex preserves short exact sequences of presheaves when the coefficient category
has products and its products of the required sizes are exact. The exactness requirement is
automatic for finite families in an abelian category, and for arbitrary families of abelian
groups. Exactness is tested in the presheaf values before sheafification, only at the
objects specified below. For finite families, the exact-product hypothesis is supplied by
locally enabling `Abelian.hasFiniteBiproducts`.

Only the values at finite products of members matter: a sequence of presheaves that is short
exact after evaluation at each such product has a short exact sequence of Čech complexes
(`shortExact_map_cechComplexFunctor`). For an open cover, this asks for exactness only on the
finite intersections of members.

For a coefficient sequence that is short exact at the terminal object and at the finite
products of members, acyclicity of its middle and right terms implies acyclicity of its left term.
This is the coefficient-sequence descent used when iterating
Mayer-Vietoris sequences for Laurent covers: the middle term is the pair of restrictions and
the right term is the restriction to the intersection.

The comparison uses `HomologicalComplex.HomologySequence.quasiIso_τ₁` for the morphism of
short exact sequences induced by the augmentations.

Shifting dimension along such sequences gives Čech acyclicity from a resolution. If
`0 ⟶ P ⟶ K⁰ ⟶ K¹ ⟶ ⋯` is a sequence of presheaves which is exact at the terminal object and at the
finite products of members, and every `Kᵏ` is acyclic, then `P` is acyclic
(`quasiIso_cechAugmentation_of_resolution`). The resolution splits into sequences of presheaves
of cycles, short exact at those objects, and in each of them the augmented Čech complexes of the
left and right terms agree up to a shift of one degree, by the degreewise lemmas
`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₁` and
`HomologicalComplex.HomologySequence.mono_homologyMap_τ₁`.

## Main results

* `TauCeti.CategoryTheory.preservesLimitsOfShape_cechComplexFunctor`: the Čech complex functor
  preserves every limit that exists in the coefficient category.
* `TauCeti.CategoryTheory.shortExact_map_cechComplexFunctor`: a sequence of presheaves short exact
  at the finite products of members has a short exact sequence of Čech complexes.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_shortExact`: for a coefficient sequence
  short exact at the terminal object and at finite products of members, acyclicity of the middle
  and right terms implies acyclicity of the left term.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_X₃_of_shortExact`: for such a coefficient
  sequence, acyclicity of the left and middle terms implies acyclicity of the right term.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_resolution`: a presheaf with a resolution by
  acyclic presheaves, exact at the terminal object and at the finite products of members, is
  acyclic.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Appendix A and Lemma 8.34(i).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' u u'

namespace TauCeti.CategoryTheory

section Preservation

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C)

/-- Evaluation of the Čech complex in degree `n` is the product of the evaluations at
`U (a 0) × ⋯ × U (a n)`. -/
private def cechEvalIso (n : ℕ) :
    cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) n ≅
      (Functor.whiskeringLeft (Discrete (Fin (n + 1) → ι)) Cᵒᵖ A).obj
        (Discrete.functor (fun a ↦ op (∏ᶜ fun j ↦ U (a j)))) ⋙ lim :=
  NatIso.ofComponents (fun P ↦
    let e : ((cechComplexFunctor U).obj P).X n ≅
        ∏ᶜ (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) := Iso.refl _
    e ≪≫ HasLimit.isoOfNatIso
      (F := Discrete.functor (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))))
      (G := Discrete.functor (fun a : Fin (n + 1) → ι ↦ op (∏ᶜ fun j ↦ U (a j))) ⋙ P)
      (Discrete.compNatIsoDiscrete _ P).symm) (fun α ↦ by
    apply limit.hom_ext
    intro a
    -- The Čech term and the product use definitionally equal diagrams with different
    -- chosen-limit instances; `erw` also normalizes those instances.
    erw [Iso.trans_hom, Iso.trans_hom, Iso.refl_hom, Iso.refl_hom,
      Category.id_comp, Category.id_comp]
    dsimp only [Functor.comp_map, HomologicalComplex.eval_map,
      Functor.whiskeringLeft_obj_obj, Functor.whiskeringLeft_obj_map]
    erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, Category.assoc, limMap_π,
      HasLimit.isoOfNatIso_hom_π_assoc]
    simp only [Discrete.compNatIsoDiscrete, Iso.symm_hom, Discrete.natIso_inv_app,
      Iso.refl_inv]
    erw [Category.comp_id, Category.id_comp]
    convert cechComplexFunctor_map_f_π U _ α n a.as using 1
    rfl)

/-- The Čech complex functor preserves every limit that exists in the coefficient category: in
each degree it is a product of evaluations, and limits commute with products and evaluations. -/
instance preservesLimitsOfShape_cechComplexFunctor (J : Type*) [Category J]
    [HasLimitsOfShape J A] : PreservesLimitsOfShape J (cechComplexFunctor (A := A) U) := by
  apply HomologicalComplex.preservesLimitsOfShape_of_eval
  intro n
  exact preservesLimitsOfShape_of_natIso (cechEvalIso U n).symm

/-- The Čech complex functor preserves finite limits. -/
instance preservesFiniteLimits_cechComplexFunctor [HasFiniteLimits A] :
    PreservesFiniteLimits (cechComplexFunctor (A := A) U) where
  preservesFiniteLimits _ _ _ := inferInstance

section FiniteColimits

variable [HasFiniteColimits A]
  [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) A]

/-- With exact products, the Čech complex functor preserves finite colimits. -/
instance preservesFiniteColimits_cechComplexFunctor : PreservesFiniteColimits (cechComplexFunctor
    (A := A) U) where
  preservesFiniteColimits J _ _ := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    exact preservesColimitsOfShape_of_natIso (cechEvalIso U n).symm

end FiniteColimits

end Preservation

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C)
  [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) A]

/-- **The Čech complexes of a coefficient sequence that is short exact on the members.** If a
sequence of presheaves becomes short exact after evaluation at every finite product
`U (a 0) × ⋯ × U (a n)` of members of the family `U`, then its sequence of Čech complexes for `U`
is short exact. No exactness is required at other objects: for an open cover, only the
intersections of members matter. -/
theorem shortExact_map_cechComplexFunctor (S : ShortComplex (Cᵒᵖ ⥤ A))
    (hS : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      (S.map ((evaluation Cᵒᵖ A).obj (op (∏ᶜ fun j ↦ U (a j))))).ShortExact) :
    (S.map (cechComplexFunctor U)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  -- in degree `n`, the sequence of Čech complexes is the product of the evaluations of `S`
  have h := (ShortComplex.shortExact_of_forall_evaluation (S.map ((Functor.whiskeringLeft
    (Discrete (Fin (n + 1) → ι)) Cᵒᵖ A).obj (Discrete.functor fun a ↦ op (∏ᶜ fun j ↦ U (a j)))))
      fun a ↦ hS n a.as).map_of_exact lim
  exact ShortComplex.shortExact_of_iso (S.mapNatIso (cechEvalIso U n).symm) h

variable {T : C} (hT : IsTerminal T)

/-- The augmentation is a morphism from the coefficient sequence, concentrated in degree zero,
to its sequence of Čech complexes. -/
private def cechAugmentationShortComplexHom (S : ShortComplex (Cᵒᵖ ⥤ A)) :
    S.map ((evaluation Cᵒᵖ A).obj (op T) ⋙
      HomologicalComplex.single A (ComplexShape.up ℕ) 0) ⟶
        S.map (cechComplexFunctor U) where
  τ₁ := cechAugmentation U hT S.X₁
  τ₂ := cechAugmentation U hT S.X₂
  τ₃ := cechAugmentation U hT S.X₃
  comm₁₂ := cechAugmentation_naturality U hT S.X₁ S.f
  comm₂₃ := cechAugmentation_naturality U hT S.X₂ S.g

/-- **Čech acyclicity descends to the kernel of a locally short exact coefficient sequence.**
If a sequence of presheaves is short exact at the terminal object and at every finite product of
members of `U`, and `U` is acyclic for the middle and right presheaves, then `U` is acyclic for the
left presheaf as well. Exactness at other objects is not required. -/
theorem quasiIso_cechAugmentation_of_shortExact (S : ShortComplex (Cᵒᵖ ⥤ A))
    (hST : (S.map ((evaluation Cᵒᵖ A).obj (op T))).ShortExact)
    (hSU : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      (S.map ((evaluation Cᵒᵖ A).obj (op (∏ᶜ fun j ↦ U (a j))))).ShortExact)
    (h₂ : QuasiIso (cechAugmentation U hT S.X₂))
    (h₃ : QuasiIso (cechAugmentation U hT S.X₃)) :
    QuasiIso (cechAugmentation U hT S.X₁) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₁ (cechAugmentationShortComplexHom U hT S)
    (hST.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℕ) 0))
    (shortExact_map_cechComplexFunctor U S hSU) h₂ h₃

/-- **Čech acyclicity passes to the cokernel of a locally short exact coefficient sequence.**
If a sequence of presheaves is short exact at the terminal object and at every finite product of
members of `U`, and `U` is acyclic for the left and middle presheaves, then `U` is acyclic for the
right presheaf as well. Exactness at other objects is not required. -/
theorem quasiIso_cechAugmentation_X₃_of_shortExact (S : ShortComplex (Cᵒᵖ ⥤ A))
    (hST : (S.map ((evaluation Cᵒᵖ A).obj (op T))).ShortExact)
    (hSU : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      (S.map ((evaluation Cᵒᵖ A).obj (op (∏ᶜ fun j ↦ U (a j))))).ShortExact)
    (h₁ : QuasiIso (cechAugmentation U hT S.X₁))
    (h₂ : QuasiIso (cechAugmentation U hT S.X₂)) :
    QuasiIso (cechAugmentation U hT S.X₃) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (cechAugmentationShortComplexHom U hT S)
    (hST.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℕ) 0))
    (shortExact_map_cechComplexFunctor U S hSU) h₁ h₂

/-! ### Acyclic resolutions

For a sequence of presheaves `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` that is short exact at `T` and at the finite
products of members, with `X₂` acyclic, the augmented Čech complexes of `X₁` and `X₃` agree up to a
shift by one degree. Along the short exact sequences of cycles of a resolution by acyclic
presheaves, this shows that the resolved presheaf is acyclic. -/

section Resolution

variable {S : ShortComplex (Cᵒᵖ ⥤ A)}
  (hST : (S.map ((evaluation Cᵒᵖ A).obj (op T))).ShortExact)
  (hSU : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
    (S.map ((evaluation Cᵒᵖ A).obj (op (∏ᶜ fun j ↦ U (a j))))).ShortExact)

include hST hSU in
/-- The source and the target of the augmentation of `S` are short exact sequences of complexes. -/
private lemma shortExact_map_single_and_cechComplexFunctor :
    (S.map ((evaluation Cᵒᵖ A).obj (op T) ⋙
      HomologicalComplex.single A (ComplexShape.up ℕ) 0)).ShortExact ∧
      (S.map (cechComplexFunctor U)).ShortExact :=
  ⟨hST.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℕ) 0),
    shortExact_map_cechComplexFunctor U S hSU⟩

include hST hSU in
/-- In degree `0`, the augmentation of `X₁` is injective on cohomology if that of `X₂` is an
isomorphism. -/
private lemma mono_homologyMap_cechAugmentation_X₁_zero
    (h₂ : QuasiIsoAt (cechAugmentation U hT S.X₂) 0) :
    Mono (HomologicalComplex.homologyMap (cechAugmentation U hT S.X₁) 0) := by
  let φ := cechAugmentationShortComplexHom U hT S
  have : QuasiIsoAt φ.τ₂ 0 := h₂
  have := (quasiIsoAt_iff_isIso_homologyMap φ.τ₂ 0).1 this
  obtain ⟨hS₁, hS₂⟩ := shortExact_map_single_and_cechComplexFunctor U hST hSU
  exact HomologicalComplex.HomologySequence.mono_homologyMap_τ₁ φ hS₁ hS₂ 0
    (fun _ hi ↦ absurd hi (by simp)) (fun _ hi ↦ absurd hi (by simp)) inferInstance

include hST hSU in
/-- In degree `0`, the augmentation of `X₁` is a quasi-isomorphism if that of `X₂` is, and that of
`X₃` is injective on cohomology. -/
private lemma quasiIsoAt_cechAugmentation_X₁_zero
    (h₂ : QuasiIsoAt (cechAugmentation U hT S.X₂) 0)
    (h₃ : Mono (HomologicalComplex.homologyMap (cechAugmentation U hT S.X₃) 0)) :
    QuasiIsoAt (cechAugmentation U hT S.X₁) 0 := by
  let φ := cechAugmentationShortComplexHom U hT S
  have : QuasiIsoAt φ.τ₂ 0 := h₂
  have := (quasiIsoAt_iff_isIso_homologyMap φ.τ₂ 0).1 this
  obtain ⟨hS₁, hS₂⟩ := shortExact_map_single_and_cechComplexFunctor U hST hSU
  exact (quasiIsoAt_iff_isIso_homologyMap _ 0).2 <|
    HomologicalComplex.HomologySequence.isIso_homologyMap_τ₁ φ hS₁ hS₂ 0
      (fun _ hi ↦ absurd hi (by simp)) (fun _ hi ↦ absurd hi (by simp)) inferInstance h₃

include hST hSU in
/-- **Dimension shifting.** If the augmentation of `X₂` is a quasi-isomorphism, then the
augmentation of `X₁` is a quasi-isomorphism in degree `n + 1` as soon as that of `X₃` is one in
degree `n`. -/
private lemma quasiIsoAt_cechAugmentation_X₁_succ (h₂ : QuasiIso (cechAugmentation U hT S.X₂))
    {n : ℕ} (h₃ : QuasiIsoAt (cechAugmentation U hT S.X₃) n) :
    QuasiIsoAt (cechAugmentation U hT S.X₁) (n + 1) := by
  let φ := cechAugmentationShortComplexHom U hT S
  have : QuasiIso φ.τ₂ := h₂
  have (i : ℕ) : IsIso (HomologicalComplex.homologyMap φ.τ₂ i) :=
    (quasiIsoAt_iff_isIso_homologyMap φ.τ₂ i).1 inferInstance
  have : QuasiIsoAt φ.τ₃ n := h₃
  have := (quasiIsoAt_iff_isIso_homologyMap φ.τ₃ n).1 this
  obtain ⟨hS₁, hS₂⟩ := shortExact_map_single_and_cechComplexFunctor U hST hSU
  refine (quasiIsoAt_iff_isIso_homologyMap _ (n + 1)).2 <|
    HomologicalComplex.HomologySequence.isIso_homologyMap_τ₁ φ hS₁ hS₂ (n + 1)
      (fun _ _ ↦ inferInstance) (fun i hi ↦ ?_) inferInstance ?_
  · obtain rfl : i = n := by simpa using hi
    infer_instance
  · -- the cohomology of a complex concentrated in degree `0` vanishes in degree `n + 1`
    exact mono_of_source_iso_zero _
      (CochainComplex.exactAt_succ_single_obj (S.X₃.obj (op T)) n).isZero_homology.isoZero

/-- **Čech acyclicity from an acyclic resolution.** Let `ε : P ⋙ single₀ ⟶ K` be a morphism from
a presheaf `P`, placed in degree `0`, to a presheaf of cochain complexes `K`, which is a
quasi-isomorphism at `T` and at every finite product of members of the family `U`: for an open
cover, the sequence `0 ⟶ P ⟶ K⁰ ⟶ K¹ ⟶ ⋯` is exact on the whole space and on every finite
intersection of members. If every presheaf `Kᵏ` is acyclic for `U`, then so is `P`. -/
theorem quasiIso_cechAugmentation_of_resolution {P : Cᵒᵖ ⥤ A} {K : Cᵒᵖ ⥤ CochainComplex A ℕ}
    (ε : P ⋙ CochainComplex.single₀ A ⟶ K) (hεT : QuasiIso (ε.app (op T)))
    (hεU : ∀ (n : ℕ) (a : Fin (n + 1) → ι), QuasiIso (ε.app (op (∏ᶜ fun j ↦ U (a j)))))
    (hK : ∀ k, QuasiIso (cechAugmentation U hT (K ⋙ HomologicalComplex.eval A _ k))) :
    QuasiIso (cechAugmentation U hT P) := by
  -- the sequences of cycles are short exact at `T` and at the finite products of members
  have hexact {Y : Cᵒᵖ} (hY : QuasiIso (ε.app Y)) (k : ℕ) : (K.obj Y).ExactAt (k + 1) :=
    (quasiIsoAt_iff_exactAt (ε.app Y) (k + 1) (CochainComplex.exactAt_succ_single_obj _ k)).1
      (hY.quasiIsoAt (k + 1))
  have hcT (k : ℕ) :=
    K.shortExact_map_cyclesShortComplex k (k + 1) (by simp) (hexact hεT k)
  have hcU (k n : ℕ) (a : Fin (n + 1) → ι) :=
    K.shortExact_map_cyclesShortComplex k (k + 1) (by simp) (hexact (hεU n a) k)
  have haT :=
    ε.shortExact_map_augmentationShortComplex (hεT.quasiIsoAt 0) (hεT.quasiIsoAt 1)
  have haU (n : ℕ) (a : Fin (n + 1) → ι) :=
    ε.shortExact_map_augmentationShortComplex ((hεU n a).quasiIsoAt 0) ((hεU n a).quasiIsoAt 1)
  have hKC (k : ℕ) :
      QuasiIso (cechAugmentation U hT (K.cyclesShortComplex k (k + 1)).X₂) := by
    rw [Functor.cyclesShortComplex_X₂]
    exact hK k
  have hKA : QuasiIso (cechAugmentation U hT ε.augmentationShortComplex.X₂) := by
    rw [NatTrans.augmentationShortComplex_X₂]
    exact hK 0
  -- dimension shifting: in each degree, `P` and every presheaf of cycles are acyclic
  have key (n : ℕ) : QuasiIsoAt (cechAugmentation U hT P) n ∧ ∀ k,
      QuasiIsoAt (cechAugmentation U hT (K ⋙ HomologicalComplex.cyclesFunctor A _ (k + 1))) n := by
    induction n with
    | zero =>
      have hmono (k : ℕ) : Mono (HomologicalComplex.homologyMap
          (cechAugmentation U hT (K ⋙ HomologicalComplex.cyclesFunctor A _ (k + 1))) 0) := by
        have h := mono_homologyMap_cechAugmentation_X₁_zero U hT (hcT (k + 1))
          (hcU (k + 1)) ((hKC (k + 1)).quasiIsoAt 0)
        rw [Functor.cyclesShortComplex_X₁] at h
        exact h
      constructor
      · have h := quasiIsoAt_cechAugmentation_X₁_zero U hT haT haU (hKA.quasiIsoAt 0)
          (by rw [NatTrans.augmentationShortComplex_X₃]; exact hmono 0)
        rw [NatTrans.augmentationShortComplex_X₁] at h
        exact h
      · intro k
        have h := quasiIsoAt_cechAugmentation_X₁_zero U hT (hcT (k + 1)) (hcU (k + 1))
          ((hKC (k + 1)).quasiIsoAt 0)
          (by rw [Functor.cyclesShortComplex_X₃]; exact hmono (k + 1))
        rw [Functor.cyclesShortComplex_X₁] at h
        exact h
    | succ n ih =>
      constructor
      · have h := quasiIsoAt_cechAugmentation_X₁_succ U hT haT haU hKA
          (by rw [NatTrans.augmentationShortComplex_X₃]; exact ih.2 0)
        rw [NatTrans.augmentationShortComplex_X₁] at h
        exact h
      · intro k
        have h := quasiIsoAt_cechAugmentation_X₁_succ U hT (hcT (k + 1)) (hcU (k + 1)) (hKC (k + 1))
          (by rw [Functor.cyclesShortComplex_X₃]; exact ih.2 (k + 1))
        rw [Functor.cyclesShortComplex_X₁] at h
        exact h
  rw [quasiIso_iff]
  exact fun n ↦ (key n).1

end Resolution

end TauCeti.CategoryTheory
end
end
end GeometryLiteralSource017

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Exact"

section GeometryLiteralSource018
/- Original source: TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.MayerVietoris -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Čech complexes of two-member covers

Let `C` be a thin category with finite products and a terminal object `T`, for instance the poset
of open subsets of a topological space, and let `P : Cᵒᵖ ⥤ A` be a presheaf with values in an
abelian category. For a family of two objects `U 0` and `U 1`, the cohomology of the Čech complex
of `P` vanishes in every degree `≥ 2`, and the augmented Čech complex is exact precisely when the
Mayer-Vietoris sequence `0 ⟶ P(T) ⟶ P(U 0) ⊞ P(U 1) ⟶ P(U 0 × U 1) ⟶ 0` is short exact. The
Čech complex itself still has terms in every degree; only its exactness reduces to that of this
sequence. This is the form in which exactness in every degree of the augmented Čech complex of a
cover by two opens follows from statements in degrees `0` and `1`: the sheaf condition for the
cover, and the fact that every section over the intersection is a difference of restrictions.

More generally, let `W` be a family each of whose members maps to `V 0` or to `V 1`, for instance
an open cover refining a cover by two opens. If the restrictions of `W` to `V 0`, `V 1` and
`V 0 × V 1` are acyclic, then `W` is acyclic exactly when the two-member family `V` is
(`quasiIso_cechAugmentation_iff_of_fin_two`). This is the inductive step in the acyclicity of
Laurent covers in rigid and adic geometry, where a Laurent cover generated by several elements
refines the cover generated by one of them. The family `W` need not refine `V` if instead the
restriction of `V` to every nonempty finite intersection of members of `W` is acyclic
(`quasiIso_cechAugmentation_iff_of_fin_two_of_quasiIso_prod`); this is the step that passes
acyclicity from Laurent covers to the covers they refine.

The proof restricts `P` to the members. For an object `Y`, the presheaf `P(Y × -)` has an exact
augmented Čech complex for any family with a member receiving a map from `Y`
(`quasiIso_cechAugmentation_prod_of_hom`): in a thin category the family `U` may be replaced by
`Y × U`, which refines and is refined by the single object `Y`. Restriction along the projections
then gives a short exact sequence of Čech complexes
`0 ⟶ Č(W, P) ⟶ Č(W, P(V 0 × -)) ⊞ Č(W, P(V 1 × -)) ⟶ Č(W, P(V 0 × V 1 × -)) ⟶ 0`,
split in each degree because each product of members of `W` lies in `V 0` or in `V 1`. When the
restrictions of `W` are acyclic, its long exact cohomology sequence identifies the cohomology of
`Č(W, P)` with that of the Mayer-Vietoris sequence of `V`. Without refinement, the same sequence is
the sequence of Čech complexes of the short complex of presheaves
`P ⟶ P(V 0 × -) ⊞ P(V 1 × -) ⟶ P(V 0 × V 1 × -)`; it is short exact once this short complex is short
exact at each product of members of `W` (`shortExact_map_cechComplexFunctor`), that is, once `V`
restricted to each such product is acyclic.

## Main results

* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_prod_of_hom`: for `Y ⟶ U i₀`, the augmented
  Čech complex of `P(Y × -)` for the family `U` is exact.
* `TauCeti.CategoryTheory.exactAt_add_two_cechComplexFunctor_obj`: the Čech complex of any
  presheaf for a two-member family is exact in every degree `≥ 2`.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_fin_two_iff`: the augmented Čech complex of `P`
  for a two-member family is exact if and only if `P` satisfies the sheaf condition for the family
  and `P(U 0) ⊞ P(U 1) ⟶ P(U 0 × U 1)` is an epimorphism.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff_of_fin_two`: a family refining a
  two-member family `V`, whose restrictions to `V 0`, `V 1` and `V 0 × V 1` are acyclic, is
  acyclic if and only if `V` is.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff_of_fin_two_of_quasiIso_prod`: the same
  for a family `W` that need not refine `V`, provided that `V` restricted to each finite product of
  members of `W` is acyclic.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Appendix A, Definition A.1,
  where a cover is called `F`-acyclic when its augmented Čech complex is exact, and Lemma 8.34(i),
  whose proof is an induction on the number of generators of a Laurent cover.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]

variable [HasFiniteProducts C]

/-! ### Restriction to an object -/

section Restriction

variable [Quiver.IsThin C] [Preadditive A] [HasProducts.{w} A]

/-- The projection from the family `Y × W` to the family `W`. -/
private abbrev prodFamilyHom (Y : C) {κ : Type w} (W : κ → C) :
    FormalCoproduct.mk _ (fun i ↦ Y ⨯ W i) ⟶ FormalCoproduct.mk _ W :=
  ⟨id, fun i ↦ (prod.snd : Y ⨯ W i ⟶ W i)⟩

/-- For the presheaf `P(Y × -)`, replacing a family `W` by `Y × W` does not change the Čech
complex: each factor `P(Y × W (a 0) × ⋯ × W (a n))` is restricted along a morphism between
isomorphic objects of the thin category `C`. -/
private lemma isIso_cechComplexMap_prod (P : Cᵒᵖ ⥤ A) (Y : C) {κ : Type w} (W : κ → C) :
    IsIso (cechComplexMap ((prod.functor.obj Y).op ⋙ P) (prodFamilyHom Y W)) :=
  isIso_cechComplexMap _ _ fun _ a ↦
    (P.mapIso (iso_of_both_ways
      (prod.map (𝟙 Y) (Limits.Pi.map fun j ↦ (prod.snd : Y ⨯ W (a j) ⟶ W (a j))))
      (prod.lift prod.fst (Pi.lift fun j ↦ prod.lift prod.fst (prod.snd ≫ Pi.π _ j)))).op).isIso_hom

variable [HasZeroObject A] [CategoryWithHomology A] {ι : Type w} (U : ι → C) {T : C}
  (hT : IsTerminal T) (P : Cᵒᵖ ⥤ A)

/-- **The Čech complex of a restricted presheaf.** If some member `U i₀` of the family receives a
morphism from `Y`, then the augmented Čech complex of the presheaf `P(Y × -)` for `U` is exact.
For `Y = T` this is `quasiIso_cechAugmentation_of_hom`; for an open cover of `T` and an open
`Y` contained in a member, it says that the cover restricted to `Y` is acyclic for `P`. -/
theorem quasiIso_cechAugmentation_prod_of_hom (Y : C) {i₀ : ι} (g : Y ⟶ U i₀) :
    QuasiIso (cechAugmentation U hT ((prod.functor.obj Y).op ⋙ P)) := by
  -- replacing a family `W` by `Y × W` does not change the augmented Čech complex of `P(Y × -)`
  have key {κ : Type w} (W : κ → C) :
      QuasiIso (cechAugmentation (fun i ↦ Y ⨯ W i) hT ((prod.functor.obj Y).op ⋙ P)) ↔
        QuasiIso (cechAugmentation W hT ((prod.functor.obj Y).op ⋙ P)) := by
    have := isIso_cechComplexMap_prod P Y W
    rw [← cechAugmentation_comp_cechComplexMap hT _ (prodFamilyHom Y W)]
    exact quasiIso_iff_comp_right _ _
  -- the families `Y × U` and `Y × T` map to each other, and replacing `Y × T` by `T` gives a
  -- family with `T` as a member
  rw [← key, quasiIso_cechAugmentation_congr hT _ (V := fun _ : PUnit.{w + 1} ↦ Y ⨯ T)
    ⟨fun _ ↦ PUnit.unit, fun _ ↦ prod.map (𝟙 Y) (hT.from _)⟩
    ⟨fun _ ↦ i₀, fun _ ↦ prod.lift prod.fst (prod.fst ≫ g)⟩, key]
  exact quasiIso_cechAugmentation_of_hom _ hT _ (i₀ := PUnit.unit) (𝟙 T)

end Restriction

/-! ### Families refining a two-member family

Throughout, `V 0` and `V 1` are two objects and `W` is a family each of whose members maps to
`V 0` or to `V 1`, through `g k : W k ⟶ V (c k)`; the main case is `W = V`. -/

section TwoMembers

variable (V : Fin 2 → C) {κ : Type w} (W : κ → C) (c : κ → Fin 2) (g : ∀ k, W k ⟶ V (c k))
  {T : C} (hT : IsTerminal T) (P : Cᵒᵖ ⥤ A)

section FactorwiseMaps

/-! In degree `n`, the terms of Čech complexes for `W` are products indexed by
`a : Fin (n + 1) → κ`; `cechXMap` builds morphisms between them factorwise. -/

variable [Preadditive A] [HasProducts.{w} A]

/-- The morphism of degree `n` terms of Čech complexes acting on the factor indexed by `a` by
`φ a`. -/
private def cechXMap {F G : Cᵒᵖ ⥤ A} (n : ℕ)
    (φ : ∀ a : Fin (n + 1) → κ,
      F.obj (op (∏ᶜ fun j ↦ W (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ W (a j)))) :
    ((cechComplexFunctor W).obj F).X n ⟶ ((cechComplexFunctor W).obj G).X n :=
  Limits.Pi.map φ

private lemma cechXMap_π {F G : Cᵒᵖ ⥤ A} (n : ℕ)
    (φ : ∀ a : Fin (n + 1) → κ,
      F.obj (op (∏ᶜ fun j ↦ W (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ W (a j))))
    (a : Fin (n + 1) → κ) :
    cechXMap W n φ ≫ Pi.π _ a = Pi.π _ a ≫ φ a :=
  Pi.map_π φ a

private lemma cechXMap_ext {F G : Cᵒᵖ ⥤ A} {n : ℕ}
    {φ ψ : ∀ a : Fin (n + 1) → κ,
      F.obj (op (∏ᶜ fun j ↦ W (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ W (a j)))}
    (h : ∀ a, φ a = ψ a) : cechXMap W n φ = cechXMap W n ψ :=
  congrArg _ (funext h)

private lemma map_f_eq_cechXMap {F G : Cᵒᵖ ⥤ A} (α : F ⟶ G) (n : ℕ) :
    ((cechComplexFunctor W).map α).f n = cechXMap W n fun a ↦ α.app (op (∏ᶜ fun j ↦ W (a j))) :=
  Pi.hom_ext _ _ fun a ↦ (cechComplexFunctor_map_f_π W F α n a).trans
    (cechXMap_π W n (fun b ↦ α.app (op (∏ᶜ fun j ↦ W (b j)))) a).symm

private lemma cechXMap_comp {F G H : Cᵒᵖ ⥤ A} (n : ℕ)
    (φ : ∀ a : Fin (n + 1) → κ,
      F.obj (op (∏ᶜ fun j ↦ W (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ W (a j))))
    (ψ : ∀ a : Fin (n + 1) → κ,
      G.obj (op (∏ᶜ fun j ↦ W (a j))) ⟶ H.obj (op (∏ᶜ fun j ↦ W (a j)))) :
    cechXMap W n φ ≫ cechXMap W n ψ = cechXMap W n fun a ↦ φ a ≫ ψ a :=
  Limits.Pi.map_comp_map φ ψ

private lemma cechXMap_add {F G : Cᵒᵖ ⥤ A} (n : ℕ)
    (φ ψ : ∀ a : Fin (n + 1) → κ,
      F.obj (op (∏ᶜ fun j ↦ W (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ W (a j)))) :
    cechXMap W n φ + cechXMap W n ψ = cechXMap W n fun a ↦ φ a + ψ a :=
  Pi.hom_ext _ _ fun a ↦ (Preadditive.add_comp _ _ _ _ _ _).trans <|
    (congrArg₂ (· + ·) (cechXMap_π W n φ a) (cechXMap_π W n ψ a)).trans <|
      (Preadditive.comp_add _ _ _ _ _ _).symm.trans (cechXMap_π W n (fun b ↦ φ b + ψ b) a).symm

private lemma cechXMap_neg {F G : Cᵒᵖ ⥤ A} (n : ℕ)
    (φ : ∀ a : Fin (n + 1) → κ,
      F.obj (op (∏ᶜ fun j ↦ W (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ W (a j)))) :
    -cechXMap W n φ = cechXMap W n fun a ↦ -φ a :=
  Pi.hom_ext _ _ fun a ↦ (Preadditive.neg_comp _ _).trans <|
    (congrArg Neg.neg (cechXMap_π W n φ a)).trans <|
      (Preadditive.comp_neg _ _).symm.trans (cechXMap_π W n (fun b ↦ -φ b) a).symm

private lemma cechXMap_id (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    cechXMap W n (fun a ↦ 𝟙 (F.obj (op (∏ᶜ fun j ↦ W (a j))))) = 𝟙 _ :=
  Limits.Pi.map_id

private lemma cechXMap_zero (F G : Cᵒᵖ ⥤ A) (n : ℕ) :
    cechXMap W n (fun a ↦ (0 : F.obj (op (∏ᶜ fun j ↦ W (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ W (a j))))) =
      0 :=
  Pi.hom_ext _ _ fun a ↦ (cechXMap_π W n (fun b ↦ (0 : F.obj (op (∏ᶜ fun j ↦ W (b j))) ⟶
    G.obj (op (∏ᶜ fun j ↦ W (b j))))) a).trans <| comp_zero.trans zero_comp.symm

end FactorwiseMaps

/-- The presheaf `P(Y × -)`. -/
private abbrev restr (Y : C) : Cᵒᵖ ⥤ A :=
  (prod.functor.obj Y).op ⋙ P

/-- Restriction `P ⟶ P(Y × -)` along the projections `Y × V ⟶ V`. -/
private def toRestr (Y : C) : P ⟶ restr P Y where
  app V := P.map (prod.snd : Y ⨯ V.unop ⟶ V.unop).op
  -- the projections `Y × V ⟶ V` are natural in `V`
  naturality _ _ _ := by
    dsimp [prod.functor]
    simp only [← P.map_comp]
    exact P.congr_map (Quiver.Hom.unop_inj (by simp))

/-- Restriction `P(Y × -) ⟶ P(Y' × -)` along a morphism `Y' ⟶ Y`. -/
private abbrev restrMap {Y Y' : C} (h : Y' ⟶ Y) : restr P Y ⟶ restr P Y' :=
  Functor.whiskerRight (NatTrans.op (prod.functor.map h)) P

private lemma toRestr_comp_restrMap {Y Y' : C} (h : Y' ⟶ Y) :
    toRestr P Y ≫ restrMap P h = toRestr P Y' := by
  ext V
  simp [toRestr, prod.functor, ← P.map_comp, ← op_comp]

/-- The two restrictions `P ⟶ P(V 0 × V 1 × -)`, through `V 0` and through `V 1`, agree. -/
private lemma toRestr_comp_restrMap_app (X : C) :
    (toRestr P (V 0)).app (op X) ≫ (restrMap P (prod.fst : V 0 ⨯ V 1 ⟶ V 0)).app (op X) =
      (toRestr P (V 1)).app (op X) ≫ (restrMap P (prod.snd : V 0 ⨯ V 1 ⟶ V 1)).app (op X) :=
  (NatTrans.comp_app _ _ _).symm.trans <| (NatTrans.congr_app ((toRestr_comp_restrMap P _).trans
    (toRestr_comp_restrMap P _).symm) (op X)).trans (NatTrans.comp_app _ _ _)

variable [Quiver.IsThin C]

/-- Over an object `X` with a morphism to `Y`, restriction along `Y × X ⟶ X` is invertible. -/
private lemma isIso_toRestr_app {Y X : C} (f : X ⟶ Y) : IsIso ((toRestr P Y).app (op X)) :=
  (P.mapIso (iso_of_both_ways (prod.snd : Y ⨯ X ⟶ X) (prod.lift f (𝟙 X))).op).isIso_hom

/-- Over an object `X` with `Y × X` mapping to `Y'`, restriction along `Y' × X ⟶ Y × X` is
invertible. -/
private lemma isIso_restrMap_app {Y Y' X : C} (h : Y' ⟶ Y) (f : Y ⨯ X ⟶ Y') :
    IsIso ((restrMap P h).app (op X)) :=
  (P.mapIso (iso_of_both_ways (prod.map h (𝟙 X)) (prod.lift f prod.snd)).op).isIso_hom

variable [Abelian A] [HasProducts.{w} A]

/-- The difference of restrictions
`Č(W, P(V 0 × -)) ⊞ Č(W, P(V 1 × -)) ⟶ Č(W, P(V 0 × V 1 × -))`. -/
private abbrev mvDiff :
    (cechComplexFunctor W).obj (restr P (V 0)) ⊞ (cechComplexFunctor W).obj (restr P (V 1)) ⟶
      (cechComplexFunctor W).obj (restr P (V 0 ⨯ V 1)) :=
  biprod.desc ((cechComplexFunctor W).map (restrMap P (prod.fst : V 0 ⨯ V 1 ⟶ V 0)))
    (-(cechComplexFunctor W).map (restrMap P (prod.snd : V 0 ⨯ V 1 ⟶ V 1)))

/-- The short complex of Čech complexes
`Č(W, P) ⟶ Č(W, P(V 0 × -)) ⊞ Č(W, P(V 1 × -)) ⟶ Č(W, P(V 0 × V 1 × -))`, given by restriction
and by the difference of restrictions. -/
private abbrev mvShortComplex : ShortComplex (CochainComplex A ℕ) :=
  ShortComplex.mk
    (biprod.lift ((cechComplexFunctor W).map (toRestr P (V 0)))
      ((cechComplexFunctor W).map (toRestr P (V 1))))
    (mvDiff V W P)
    (by
      rw [biprod.lift_desc, Preadditive.comp_neg, ← Functor.map_comp, ← Functor.map_comp,
        toRestr_comp_restrMap, toRestr_comp_restrMap, add_neg_cancel])

/-! The splitting in degree `n` acts factorwise. A factor of the degree `n` term is indexed by
`a : Fin (n + 1) → κ`, and the product `X` of the members `W (a j)` maps to `V (c (a 0))`. If
`c (a 0) = 0`, then `P(X) ⟶ P(V 0 × X)` and `P(V 1 × X) ⟶ P(V 0 × V 1 × X)` are isomorphisms;
if `c (a 0) = 1`, then so are `P(X) ⟶ P(V 1 × X)` and `P(V 0 × X) ⟶ P(V 0 × V 1 × X)`. -/

/-- The product of the members indexed by `a` maps to `V i` when `c (a 0) = i`. -/
private def toMember {n : ℕ} {a : Fin (n + 1) → κ} {i : Fin 2} (h : c (a 0) = i) :
    (∏ᶜ fun j ↦ W (a j)) ⟶ V i :=
  Pi.π _ 0 ≫ g (a 0) ≫ eqToHom (congrArg V h)

/-- The factors of the retraction of `Č(W, P) ⟶ Č(W, P(V 0 × -)) ⊞ Č(W, P(V 1 × -))` in degree
`n` coming from the first summand. -/
private def retr₀ {n : ℕ} (a : Fin (n + 1) → κ) :
    (restr P (V 0)).obj (op (∏ᶜ fun j ↦ W (a j))) ⟶ P.obj (op (∏ᶜ fun j ↦ W (a j))) :=
  if h : c (a 0) = 0 then
    haveI := isIso_toRestr_app P (toMember V W c g h)
    inv ((toRestr P (V 0)).app (op (∏ᶜ fun j ↦ W (a j))))
  else 0

/-- The factors of the retraction coming from the second summand. -/
private def retr₁ {n : ℕ} (a : Fin (n + 1) → κ) :
    (restr P (V 1)).obj (op (∏ᶜ fun j ↦ W (a j))) ⟶ P.obj (op (∏ᶜ fun j ↦ W (a j))) :=
  if h : c (a 0) = 0 then 0
  else
    haveI := isIso_toRestr_app P (toMember V W c g (Fin.eq_one_of_ne_zero _ h))
    inv ((toRestr P (V 1)).app (op (∏ᶜ fun j ↦ W (a j))))

/-- The factors of the section of the difference map in degree `n`, into the first summand. -/
private def sect₀ {n : ℕ} (a : Fin (n + 1) → κ) :
    (restr P (V 0 ⨯ V 1)).obj (op (∏ᶜ fun j ↦ W (a j))) ⟶
      (restr P (V 0)).obj (op (∏ᶜ fun j ↦ W (a j))) :=
  if h : c (a 0) = 0 then 0
  else
    haveI := isIso_restrMap_app P (prod.fst : V 0 ⨯ V 1 ⟶ V 0)
      (prod.lift prod.fst (prod.snd ≫ toMember V W c g (Fin.eq_one_of_ne_zero _ h)))
    inv ((restrMap P (prod.fst : V 0 ⨯ V 1 ⟶ V 0)).app (op (∏ᶜ fun j ↦ W (a j))))

/-- The factors of the section of the difference map in degree `n`, into the second summand. -/
private def sect₁ {n : ℕ} (a : Fin (n + 1) → κ) :
    (restr P (V 0 ⨯ V 1)).obj (op (∏ᶜ fun j ↦ W (a j))) ⟶
      (restr P (V 1)).obj (op (∏ᶜ fun j ↦ W (a j))) :=
  if h : c (a 0) = 0 then
    haveI := isIso_restrMap_app P (prod.snd : V 0 ⨯ V 1 ⟶ V 1)
      (prod.lift (prod.snd ≫ toMember V W c g h) prod.fst)
    (-inv ((restrMap P (prod.snd : V 0 ⨯ V 1 ⟶ V 1)).app (op (∏ᶜ fun j ↦ W (a j)))))
  else 0

/-- The retraction of `Č(W, P) ⟶ Č(W, P(V 0 × -)) ⊞ Č(W, P(V 1 × -))` in degree `n`. -/
private def mvRetr (n : ℕ) :
    ((cechComplexFunctor W).obj (restr P (V 0)) ⊞ (cechComplexFunctor W).obj (restr P (V 1))).X n ⟶
      ((cechComplexFunctor W).obj P).X n :=
  (biprod.fst : _ ⟶ (cechComplexFunctor W).obj (restr P (V 0))).f n ≫
      cechXMap W n (retr₀ V W c g P) +
    (biprod.snd : _ ⟶ (cechComplexFunctor W).obj (restr P (V 1))).f n ≫
      cechXMap W n (retr₁ V W c g P)

/-- The section of the difference map in degree `n`. -/
private def mvSect (n : ℕ) :
    ((cechComplexFunctor W).obj (restr P (V 0 ⨯ V 1))).X n ⟶
      ((cechComplexFunctor W).obj (restr P (V 0)) ⊞
        (cechComplexFunctor W).obj (restr P (V 1))).X n :=
  cechXMap W n (sect₀ V W c g P) ≫
      (biprod.inl : (cechComplexFunctor W).obj (restr P (V 0)) ⟶ _).f n +
    cechXMap W n (sect₁ V W c g P) ≫
      (biprod.inr : (cechComplexFunctor W).obj (restr P (V 1)) ⟶ _).f n

private lemma mvRetr_id (n : ℕ) :
    mvRetr V W c g P n ≫ (biprod.lift ((cechComplexFunctor W).map (toRestr P (V 0)))
        ((cechComplexFunctor W).map (toRestr P (V 1)))).f n +
      (mvDiff V W P).f n ≫ mvSect V W c g P n = 𝟙 _ := by
  -- compare the four components of both sides with respect to the biproduct decomposition
  apply HomologicalComplex.biprodX_ext_from <;> apply HomologicalComplex.biprodX_ext_to <;>
    simp only [mvRetr, mvSect, Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
      HomologicalComplex.biprod_inl_fst_f_assoc, HomologicalComplex.biprod_inl_snd_f_assoc,
      HomologicalComplex.biprod_inr_fst_f_assoc, HomologicalComplex.biprod_inr_snd_f_assoc,
      HomologicalComplex.biprod_inl_fst_f, HomologicalComplex.biprod_inl_snd_f,
      HomologicalComplex.biprod_inr_fst_f, HomologicalComplex.biprod_inr_snd_f,
      HomologicalComplex.biprod_lift_fst_f, HomologicalComplex.biprod_lift_snd_f,
      HomologicalComplex.biprod_inl_desc_f_assoc, HomologicalComplex.biprod_inr_desc_f_assoc,
      HomologicalComplex.neg_f_apply, Preadditive.neg_comp, zero_comp,
      comp_zero, Category.comp_id, add_zero, zero_add, map_f_eq_cechXMap,
      cechXMap_comp, cechXMap_neg, cechXMap_add]
  · refine (cechXMap_ext W fun a ↦ ?_).trans (cechXMap_id W _ n)
    by_cases h : c (a 0) = 0 <;> simp [retr₀, sect₀, h]
  · refine (cechXMap_ext W fun a ↦ ?_).trans (cechXMap_zero W _ _ n)
    by_cases h : c (a 0) = 0
    · have := isIso_toRestr_app P (toMember V W c g h)
      have := isIso_restrMap_app P (prod.snd : V 0 ⨯ V 1 ⟶ V 1)
        (prod.lift (prod.snd ≫ toMember V W c g h) prod.fst)
      simp only [retr₀, sect₁, h, ↓reduceDIte, Preadditive.comp_neg]
      -- solve the square `toRestr_comp_restrMap_app` for the two inverses
      rw [add_neg_eq_zero, IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
      exact (toRestr_comp_restrMap_app V P _).symm
    · simp [retr₀, sect₁, h]
  · refine (cechXMap_ext W fun a ↦ ?_).trans (cechXMap_zero W _ _ n)
    by_cases h : c (a 0) = 0
    · simp [retr₁, sect₀, h]
    · have := isIso_toRestr_app P (toMember V W c g (Fin.eq_one_of_ne_zero _ h))
      have := isIso_restrMap_app P (prod.fst : V 0 ⨯ V 1 ⟶ V 0)
        (prod.lift prod.fst (prod.snd ≫ toMember V W c g (Fin.eq_one_of_ne_zero _ h)))
      simp only [retr₁, sect₀, h, ↓reduceDIte]
      rw [add_neg_eq_zero, IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
      exact toRestr_comp_restrMap_app V P _
  · refine (cechXMap_ext W fun a ↦ ?_).trans (cechXMap_id W _ n)
    by_cases h : c (a 0) = 0 <;> simp [retr₁, sect₁, h]

/-- The short complex `mvShortComplex` is split in each degree. -/
private def mvSplitting (n : ℕ) :
    ((mvShortComplex V W P).map (HomologicalComplex.eval A (ComplexShape.up ℕ) n)).Splitting where
  r := mvRetr V W c g P n
  s := mvSect V W c g P n
  f_r := by
    simp only [mvShortComplex, mvRetr, ShortComplex.map_f, ShortComplex.map_X₁, ShortComplex.map_X₂,
      HomologicalComplex.eval_obj, HomologicalComplex.eval_map, Preadditive.comp_add,
      HomologicalComplex.biprod_lift_fst_f_assoc, HomologicalComplex.biprod_lift_snd_f_assoc,
      map_f_eq_cechXMap, cechXMap_comp, cechXMap_add, ← cechXMap_id]
    exact cechXMap_ext W fun a ↦ by by_cases h : c (a 0) = 0 <;> simp [retr₀, retr₁, h]
  s_g := by
    simp only [mvShortComplex, mvSect, ShortComplex.map_g, ShortComplex.map_X₂, ShortComplex.map_X₃,
      HomologicalComplex.eval_obj, HomologicalComplex.eval_map, Preadditive.add_comp,
      Category.assoc, HomologicalComplex.biprod_inl_desc_f, HomologicalComplex.biprod_inr_desc_f,
      HomologicalComplex.neg_f_apply, map_f_eq_cechXMap, cechXMap_neg, cechXMap_comp, cechXMap_add,
      ← cechXMap_id]
    exact cechXMap_ext W fun a ↦ by by_cases h : c (a 0) = 0 <;> simp [sect₀, sect₁, h]
  -- the maps of `(mvShortComplex V W P).map (eval _ _ n)` are the degree `n` components
  id := mvRetr_id V W c g P n

include g in
private lemma mvShortComplex_shortExact : (mvShortComplex V W P).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    (mvSplitting V W c g P n).shortExact

/-! The cohomology of the middle and last terms of `mvShortComplex` is computed from acyclicity of
`W` for the restricted presheaves `P(Y × -)`, `Y = V 0, V 1, V 0 × V 1`. When `W = V`, these hold
by `quasiIso_cechAugmentation_prod_of_hom`. -/

omit [Quiver.IsThin C] in
/-- The Čech complex of `P(Y × -)` for `W` is exact in positive degrees when the augmented one is
exact. -/
private lemma exactAt_restr {Y : C} (hY : QuasiIso (cechAugmentation W hT (restr P Y))) (n : ℕ) :
    ((cechComplexFunctor W).obj (restr P Y)).ExactAt (n + 1) :=
  ((quasiIso_cechAugmentation_iff W hT (restr P Y)).1 hY).2 n

/-- The value of `P(Y × -)` at `X` is the value of `P` at `Y × X`. -/
private def restrObjIso (Y X : C) : (restr P Y).obj (op X) ≅ P.obj (op (Y ⨯ X)) :=
  Iso.refl _

/-- The map from `P(Y)` to the degree `0` cohomology of `Č(W, P(Y × -))`: restriction
`P(Y) ⟶ P(Y × T)` followed by the augmentation. It is an isomorphism when the augmented Čech
complex of `P(Y × -)` for `W` is exact (`isIso_homologyZeroRestr`). -/
private def homologyZeroRestr (Y : C) :
    P.obj (op Y) ⟶ ((cechComplexFunctor W).obj (restr P Y)).homology 0 :=
  P.map (prod.fst : Y ⨯ T ⟶ Y).op ≫ (restrObjIso P Y T).inv ≫
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
      ((restr P Y).obj (op T))).inv ≫
      HomologicalComplex.homologyMap (cechAugmentation W hT (restr P Y)) 0

private lemma isIso_homologyZeroRestr {Y : C} (hY : QuasiIso (cechAugmentation W hT (restr P Y))) :
    IsIso (homologyZeroRestr W hT P Y) := by
  have : IsIso (HomologicalComplex.homologyMap (cechAugmentation W hT (restr P Y)) 0) :=
    (quasiIsoAt_iff_isIso_homologyMap _ 0).1 ((quasiIso_iff _).1 hY 0)
  have : IsIso (P.map (prod.fst : Y ⨯ T ⟶ Y).op) := (P.mapIso (iso_of_both_ways
    (prod.fst : Y ⨯ T ⟶ Y) (prod.lift (𝟙 Y) (hT.from Y))).op).isIso_hom
  unfold homologyZeroRestr
  infer_instance

omit [Quiver.IsThin C] in
/-- Restriction from `Y` to `Y'` is compatible with the identifications `homologyZeroRestr`. -/
private lemma homologyZeroRestr_comp_homologyMap {Y Y' : C} (h : Y' ⟶ Y) :
    homologyZeroRestr W hT P Y ≫
        HomologicalComplex.homologyMap ((cechComplexFunctor W).map (restrMap P h)) 0 =
      P.map h.op ≫ homologyZeroRestr W hT P Y' := by
  simp only [homologyZeroRestr, Category.assoc]
  rw [← HomologicalComplex.homologyMap_comp, cechAugmentation_naturality,
    HomologicalComplex.homologyMap_comp,
    HomologicalComplex.singleObjHomologySelfIso_inv_naturality_assoc]
  simp [restrObjIso, prod.functor, ← P.map_comp_assoc, ← op_comp]

/-- The map from `P(V 0) ⊞ P(V 1)` to the degree `0` cohomology of the middle term of
`mvShortComplex` given by the maps `homologyZeroRestr`. It is an isomorphism when the augmented Čech
complexes of `P(V 0 × -)` and `P(V 1 × -)` for `W` are exact (`isIso_homologyZeroBiprod`). -/
private abbrev homologyZeroBiprod :
    P.obj (op (V 0)) ⊞ P.obj (op (V 1)) ⟶
      ((cechComplexFunctor W).obj (restr P (V 0)) ⊞
        (cechComplexFunctor W).obj (restr P (V 1))).homology 0 :=
  biprod.desc (homologyZeroRestr W hT P (V 0) ≫ HomologicalComplex.homologyMap biprod.inl 0)
    (homologyZeroRestr W hT P (V 1) ≫ HomologicalComplex.homologyMap biprod.inr 0)

omit [Quiver.IsThin C] in
/-- `homologyZeroBiprod` is the biproduct of the maps `homologyZeroRestr`, followed by the
comparison of degree `0` cohomology with biproducts. -/
private lemma homologyZeroBiprod_eq :
    homologyZeroBiprod V W hT P = biprod.map (homologyZeroRestr W hT P (V 0))
      (homologyZeroRestr W hT P (V 1)) ≫ biprod.desc (HomologicalComplex.homologyMap biprod.inl 0)
        (HomologicalComplex.homologyMap biprod.inr 0) := by
  ext <;> simp

private lemma isIso_homologyZeroBiprod
    (h₀ : QuasiIso (cechAugmentation W hT (restr P (V 0))))
    (h₁ : QuasiIso (cechAugmentation W hT (restr P (V 1)))) :
    IsIso (homologyZeroBiprod V W hT P) := by
  have := isIso_homologyZeroRestr W hT P h₀
  have := isIso_homologyZeroRestr W hT P h₁
  -- degree `0` cohomology commutes with the biproduct, being an additive functor
  have : IsIso (biprod.desc (HomologicalComplex.homologyMap
      (biprod.inl : (cechComplexFunctor W).obj (restr P (V 0)) ⟶ _) 0)
      (HomologicalComplex.homologyMap
        (biprod.inr : (cechComplexFunctor W).obj (restr P (V 1)) ⟶ _) 0)) := by
    have := preservesBinaryBiproducts_of_preservesBiproducts
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) 0)
    -- `homologyFunctor A _ 0` sends a complex to its degree `0` homology and a map to its
    -- `homologyMap` by definition (`HomologicalComplex.homologyFunctor_obj`,
    -- `HomologicalComplex.homologyFunctor_map`); in that form the comparison map is the inverse of
    -- `Functor.mapBiprod` (`Functor.mapBiprod_inv`).
    change IsIso (biprod.desc
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) 0).map biprod.inl)
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) 0).map biprod.inr))
    rw [← Functor.mapBiprod_inv]
    infer_instance
  rw [homologyZeroBiprod_eq]
  have : IsIso (biprod.map (homologyZeroRestr W hT P (V 0)) (homologyZeroRestr W hT P (V 1))) :=
    (biprod.mapIso (asIso (homologyZeroRestr W hT P (V 0)))
      (asIso (homologyZeroRestr W hT P (V 1)))).isIso_hom
  infer_instance

/-- The Mayer-Vietoris short complex `P(T) ⟶ P(V 0) ⊞ P(V 1) ⟶ P(V 0 × V 1)`, given by
restriction and by the difference of restrictions. -/
private def mvSC : ShortComplex A :=
  ShortComplex.mk (biprod.lift (P.map (hT.from (V 0)).op) (P.map (hT.from (V 1)).op))
    (biprod.desc (P.map (prod.fst : V 0 ⨯ V 1 ⟶ V 0).op)
      (-P.map (prod.snd : V 0 ⨯ V 1 ⟶ V 1).op)) (by
    -- the two restrictions `P(T) ⟶ P(V 0 × V 1)` agree, as `T` is terminal
    rw [biprod.lift_desc, Preadditive.comp_neg, ← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp,
      hT.hom_ext (prod.fst ≫ hT.from (V 0)) (prod.snd ≫ hT.from (V 1)), add_neg_cancel])

omit [Quiver.IsThin C] in
/-- In degree `0` cohomology, the difference map of `mvShortComplex` is the Mayer-Vietoris map
`P(V 0) ⊞ P(V 1) ⟶ P(V 0 × V 1)`. -/
private lemma homologyZeroBiprod_comp_homologyMap_mvDiff :
    homologyZeroBiprod V W hT P ≫ HomologicalComplex.homologyMap (mvDiff V W P) 0 =
      biprod.desc (P.map (prod.fst : V 0 ⨯ V 1 ⟶ V 0).op)
        (-P.map (prod.snd : V 0 ⨯ V 1 ⟶ V 1).op) ≫ homologyZeroRestr W hT P (V 0 ⨯ V 1) := by
  ext
  · rw [biprod.inl_desc_assoc, biprod.inl_desc_assoc, Category.assoc,
      ← HomologicalComplex.homologyMap_comp]
    exact (_ ≫= congrArg (HomologicalComplex.homologyMap · 0) (biprod.inl_desc _ _)).trans
      (homologyZeroRestr_comp_homologyMap W hT P _)
  · rw [biprod.inr_desc_assoc, biprod.inr_desc_assoc, Category.assoc,
      ← HomologicalComplex.homologyMap_comp, Preadditive.neg_comp,
      ← homologyZeroRestr_comp_homologyMap, ← Preadditive.comp_neg,
      ← HomologicalComplex.homologyMap_neg]
    exact _ ≫= congrArg (HomologicalComplex.homologyMap · 0) (biprod.inr_desc _ _)

/-- The map from `P(T)` to the degree `0` cohomology of `Č(W, P)` induced by the augmentation. -/
private def homologyZeroAug :
    P.obj (op T) ⟶ ((cechComplexFunctor W).obj P).homology 0 :=
  (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (P.obj (op T))).inv ≫
    HomologicalComplex.homologyMap (cechAugmentation W hT P) 0

omit [Quiver.IsThin C] in
/-- In degree `0` cohomology, restriction from `Č(W, P)` to the middle term of `mvShortComplex`
is restriction `P(T) ⟶ P(V 0) ⊞ P(V 1)`. -/
private lemma homologyZeroAug_comp_homologyMap_f :
    homologyZeroAug W hT P ≫ HomologicalComplex.homologyMap (mvShortComplex V W P).f 0 =
      (mvSC V hT P).f ≫ homologyZeroBiprod V W hT P := by
  have key (i : Fin 2) : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
      (P.obj (op T))).inv ≫ HomologicalComplex.homologyMap (cechAugmentation W hT P ≫
        (cechComplexFunctor W).map (toRestr P (V i))) 0 =
      P.map (hT.from (V i)).op ≫ homologyZeroRestr W hT P (V i) := by
    rw [cechAugmentation_naturality, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.singleObjHomologySelfIso_inv_naturality_assoc]
    simp only [homologyZeroRestr, restrObjIso, Iso.refl_inv, toRestr, ← P.map_comp_assoc,
      ← op_comp]
    -- the two restrictions `P(T) ⟶ P(V i × T)` agree, as `T` is terminal
    rw [hT.hom_ext (prod.fst ≫ hT.from (V i) : V i ⨯ T ⟶ T) prod.snd]
    exact (_ ≫= Category.id_comp _).symm
  have e : HomologicalComplex.homologyMap (mvShortComplex V W P).f 0 =
      HomologicalComplex.homologyMap ((cechComplexFunctor W).map (toRestr P (V 0))) 0 ≫
          HomologicalComplex.homologyMap biprod.inl 0 +
        HomologicalComplex.homologyMap ((cechComplexFunctor W).map (toRestr P (V 1))) 0 ≫
          HomologicalComplex.homologyMap biprod.inr 0 := by
    simp only [mvShortComplex, biprod.lift_eq, HomologicalComplex.homologyMap_add,
      HomologicalComplex.homologyMap_comp]
  rw [e, Preadditive.comp_add]
  dsimp only [mvSC]
  rw [biprod.lift_desc]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [homologyZeroAug, Category.assoc, ← Category.assoc (HomologicalComplex.homologyMap _ _),
      ← HomologicalComplex.homologyMap_comp, ← Category.assoc, key 0, Category.assoc]
  · rw [homologyZeroAug, Category.assoc, ← Category.assoc (HomologicalComplex.homologyMap _ _),
      ← HomologicalComplex.homologyMap_comp, ← Category.assoc, key 1, Category.assoc]

/-- The augmentation identifies `P(T)` with the degree `0` cohomology of `Č(W, P)` exactly when
`0 ⟶ P(T) ⟶ P(V 0) ⊞ P(V 1) ⟶ P(V 0 × V 1)` is exact. -/
private lemma quasiIsoAt_cechAugmentation_zero_iff_mvSC (hS : (mvShortComplex V W P).ShortExact)
    (h₀ : QuasiIso (cechAugmentation W hT (restr P (V 0))))
    (h₁ : QuasiIso (cechAugmentation W hT (restr P (V 1))))
    (h₀₁ : QuasiIso (cechAugmentation W hT (restr P (V 0 ⨯ V 1)))) :
    QuasiIsoAt (cechAugmentation W hT P) 0 ↔ (mvSC V hT P).Exact ∧ Mono (mvSC V hT P).f := by
  have : Mono (mvShortComplex V W P).f := hS.mono_f
  have : Mono (HomologicalComplex.homologyMap (mvShortComplex V W P).f 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel _ 0 (by simp)
  -- the Mayer-Vietoris short complex maps to the exact sequence
  -- `0 ⟶ H⁰(Č(W, P)) ⟶ H⁰(Č(W, P(V 0 × -))) ⊞ H⁰(Č(W, P(V 1 × -))) ⟶ H⁰(Č(W, P(V 0 × V 1 × -)))`
  let L := ShortComplex.mk (HomologicalComplex.homologyMap (mvShortComplex V W P).f 0)
    (HomologicalComplex.homologyMap (mvShortComplex V W P).g 0)
    (by rw [← HomologicalComplex.homologyMap_comp, (mvShortComplex V W P).zero,
      HomologicalComplex.homologyMap_zero])
  have hL : L.Exact := hS.homology_exact₂ 0
  let ψ : mvSC V hT P ⟶ L :=
    { τ₁ := homologyZeroAug W hT P
      τ₂ := homologyZeroBiprod V W hT P
      τ₃ := homologyZeroRestr W hT P (V 0 ⨯ V 1)
      comm₁₂ := homologyZeroAug_comp_homologyMap_f V W hT P
      comm₂₃ := homologyZeroBiprod_comp_homologyMap_mvDiff V W hT P }
  have : IsIso ψ.τ₂ := isIso_homologyZeroBiprod V W hT P h₀ h₁
  have : IsIso ψ.τ₃ := isIso_homologyZeroRestr W hT P h₀₁
  have hτ₁ : QuasiIsoAt (cechAugmentation W hT P) 0 ↔ IsIso ψ.τ₁ := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (isIso_comp_left_iff (HomologicalComplex.singleObjHomologySelfIso _ 0 _).inv _).symm
  rw [hτ₁]
  refine ⟨fun _ ↦ ?_, fun ⟨hM, _⟩ ↦ ?_⟩
  · have := ShortComplex.isIso_of_isIso ψ
    exact (ShortComplex.exact_and_mono_f_iff_of_iso (asIso ψ)).2 ⟨hL, inferInstance⟩
  · have : Mono ψ.τ₁ := mono_of_mono_fac ψ.comm₁₂
    have : Epi ψ.τ₁ := ShortComplex.epi_of_mono_of_epi_of_mono ψ hM inferInstance
      inferInstance inferInstance
    exact isIso_of_mono_of_epi _

/-! A family `W` need not refine `V` for `mvShortComplex` to be short exact. It is the sequence of
Čech complexes for `W` of the short complex of presheaves `mvPresheafSC`, whose evaluation at an
object `X` is the Mayer-Vietoris sequence of `V` for `P(X × -)`; it is therefore short exact as
soon as these Mayer-Vietoris sequences are, for every product `X` of members of `W`. -/

/-- The short complex of presheaves `P ⟶ P(V 0 × -) ⊞ P(V 1 × -) ⟶ P(V 0 × V 1 × -)`, given by
restriction and by the difference of restrictions. -/
private abbrev mvPresheafSC : ShortComplex (Cᵒᵖ ⥤ A) :=
  ShortComplex.mk (biprod.lift (toRestr P (V 0)) (toRestr P (V 1)))
    (biprod.desc (restrMap P (prod.fst : V 0 ⨯ V 1 ⟶ V 0))
      (-restrMap P (prod.snd : V 0 ⨯ V 1 ⟶ V 1)))
    (by
      rw [biprod.lift_desc, Preadditive.comp_neg, toRestr_comp_restrMap, toRestr_comp_restrMap,
        add_neg_cancel])

/-- The Čech complexes of `mvPresheafSC` for `W` form `mvShortComplex`. -/
private def mvShortComplexIso :
    (mvPresheafSC V P).map (cechComplexFunctor W) ≅ mvShortComplex V W P :=
  haveI : PreservesBinaryBiproducts (cechComplexFunctor (A := A) W) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  ShortComplex.isoMk (Iso.refl _) ((cechComplexFunctor W).mapBiprod _ _) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.id_comp]; exact (biprod.map_lift_mapBiprod _ _ _ _ _).symm)
    (by
      have := Functor.additive_of_preservesBinaryBiproducts (cechComplexFunctor (A := A) W)
      simp only [mvDiff, ← Functor.map_neg, biprod.mapBiprod_hom_desc]
      simp)

/-- Evaluation of a presheaf `F` at `Y` is `F.obj Y`. -/
private def evalObjIso (F : Cᵒᵖ ⥤ A) (Y : Cᵒᵖ) : ((evaluation Cᵒᵖ A).obj Y).obj F ≅ F.obj Y :=
  Iso.refl _

/-- Evaluated at an object `X`, the short complex `mvPresheafSC` is the Mayer-Vietoris sequence of
`V` for the presheaf `P(X × -)`, up to the isomorphisms `X × Y ≅ Y × X` and `X × T ≅ X`. -/
private def mvPresheafSCEvalIso (X : C) :
    (mvPresheafSC V P).map ((evaluation Cᵒᵖ A).obj (op X)) ≅ mvSC V hT (restr P X) :=
  haveI : PreservesBinaryBiproducts ((evaluation Cᵒᵖ A).obj (op X)) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  ShortComplex.isoMk
    (P.mapIso (iso_of_both_ways (prod.fst : X ⨯ T ⟶ X) (prod.lift (𝟙 X) (hT.from X))).op ≪≫
      (restrObjIso P X T).symm)
    (((evaluation Cᵒᵖ A).obj (op X)).mapBiprod _ _ ≪≫
      biprod.mapIso (evalObjIso _ _ ≪≫ restrObjIso P (V 0) X ≪≫
          P.mapIso (prod.braiding X (V 0)).op ≪≫ (restrObjIso P X (V 0)).symm)
        (evalObjIso _ _ ≪≫ restrObjIso P (V 1) X ≪≫ P.mapIso (prod.braiding X (V 1)).op ≪≫
          (restrObjIso P X (V 1)).symm))
    (restrObjIso P (V 0 ⨯ V 1) X ≪≫ P.mapIso (prod.braiding X (V 0 ⨯ V 1)).op ≪≫
      (restrObjIso P X (V 0 ⨯ V 1)).symm)
    -- In each component, both sides are composites of restrictions of `P` between objects of the
    -- thin category `C`. The objects of `P(X × -)` agree with those of `P` only after unfolding
    -- `prod.functor`, so the restrictions are combined with `erw`.
    (by
      apply biprod.hom_ext <;>
        simp only [Category.assoc, Iso.trans_hom, biprod.mapIso_hom, Functor.mapIso_hom,
          Iso.op_hom, Iso.symm_hom, Functor.mapBiprod_hom, biprod.lift_fst, biprod.lift_snd,
          biprod.map_fst, biprod.map_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc, mvSC,
          ShortComplex.map_f, ← Functor.map_comp_assoc] <;>
        simp only [restrObjIso, evalObjIso, Iso.refl_inv, Iso.refl_hom, evaluation_obj_map,
          toRestr] <;>
        (repeat erw [Category.id_comp]) <;> (repeat erw [Category.comp_id]) <;>
        (repeat erw [← P.map_comp]) <;>
        exact P.congr_map (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))
    (by
      dsimp only [mvSC]
      rw [← cancel_epi (((evaluation Cᵒᵖ A).obj (op X)).mapBiprod _ _).inv]
      apply biprod.hom_ext' <;>
        simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc] <;>
        simp only [biprod.mapIso_hom, biprod.inl_map_assoc, biprod.inr_map_assoc, biprod.inl_desc,
          biprod.inr_desc, Functor.mapBiprod_inv, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
          ShortComplex.map_g, ← Functor.map_comp_assoc, Iso.trans_hom, Functor.mapIso_hom,
          Iso.op_hom, Iso.symm_hom, Category.assoc, Preadditive.comp_neg] <;>
        simp only [restrObjIso, evalObjIso, Iso.refl_inv, Iso.refl_hom, evaluation_obj_map,
          NatTrans.app_neg, Preadditive.neg_comp, neg_inj] <;>
        (repeat erw [Category.id_comp]) <;> (repeat erw [Category.comp_id]) <;>
        (repeat erw [← P.map_comp]) <;>
        exact P.congr_map (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))

/-- The difference map of `mvShortComplex` is an epimorphism in degree `0` cohomology exactly
when the Mayer-Vietoris map `P(V 0) ⊞ P(V 1) ⟶ P(V 0 × V 1)` is an epimorphism. -/
private lemma epi_homologyMap_mvDiff_iff
    (h₀ : QuasiIso (cechAugmentation W hT (restr P (V 0))))
    (h₁ : QuasiIso (cechAugmentation W hT (restr P (V 1))))
    (h₀₁ : QuasiIso (cechAugmentation W hT (restr P (V 0 ⨯ V 1)))) :
    Epi (HomologicalComplex.homologyMap (mvDiff V W P) 0) ↔ Epi (mvSC V hT P).g := by
  have := isIso_homologyZeroBiprod V W hT P h₀ h₁
  have := isIso_homologyZeroRestr W hT P h₀₁
  rw [← epi_comp_iff_of_epi (homologyZeroBiprod V W hT P),
    homologyZeroBiprod_comp_homologyMap_mvDiff, epi_comp_iff_of_isIso]
  rfl

/-- The augmented Čech complex of `P` for `W` is exact if and only if the Mayer-Vietoris sequence
`0 ⟶ P(T) ⟶ P(V 0) ⊞ P(V 1) ⟶ P(V 0 × V 1) ⟶ 0` is short exact, provided that `mvShortComplex` is
short exact and that the augmented Čech complexes of `P(V 0 × -)`, `P(V 1 × -)` and
`P(V 0 × V 1 × -)` for `W` are exact. -/
private lemma quasiIso_cechAugmentation_iff_mvSC (hS : (mvShortComplex V W P).ShortExact)
    (h₀ : QuasiIso (cechAugmentation W hT (restr P (V 0))))
    (h₁ : QuasiIso (cechAugmentation W hT (restr P (V 1))))
    (h₀₁ : QuasiIso (cechAugmentation W hT (restr P (V 0 ⨯ V 1)))) :
    QuasiIso (cechAugmentation W hT P) ↔
      ((mvSC V hT P).Exact ∧ Mono (mvSC V hT P).f) ∧ Epi (mvSC V hT P).g := by
  have hX₂ (n : ℕ) : (mvShortComplex V W P).X₂.ExactAt (n + 1) :=
    (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact.exactAt_X₂ (n + 1)
      (exactAt_restr W hT P h₀ n) (exactAt_restr W hT P h₁ n)
  have hX₃ (n : ℕ) : (mvShortComplex V W P).X₃.ExactAt (n + 1) := exactAt_restr W hT P h₀₁ n
  rw [quasiIso_cechAugmentation_iff, ← quasiIsoAt_cechAugmentation_zero_iff,
    ← quasiIsoAt_cechAugmentation_zero_iff_mvSC V W hT P hS h₀ h₁ h₀₁,
    ← epi_homologyMap_mvDiff_iff V W hT P h₀ h₁ h₀₁]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun h n ↦ ?_⟩
  · -- the connecting map `H⁰(Č(W, P(V 0 × V 1 × -))) ⟶ H¹(Č(W, P))` vanishes
    exact (hS.homology_exact₃ 0 1 (by simp)).epi_f ((h 0).isZero_homology.eq_of_tgt _ _)
  · cases n with
    | zero =>
      exact hS.exactAt_X₁ 1
        (mono_of_source_iso_zero _ (hX₂ 0).isZero_homology.isoZero)
        fun i hi ↦ by
          obtain rfl : i = 0 := by simp only [ComplexShape.up_Rel] at hi; omega
          exact h
    | succ n =>
      exact hS.exactAt_X₁ (n + 2)
        (mono_of_source_iso_zero _ (hX₂ (n + 1)).isZero_homology.isoZero)
        fun i hi ↦ by
          obtain rfl : i = n + 1 := by simp only [ComplexShape.up_Rel] at hi; omega
          exact epi_of_target_iso_zero _ (hX₃ n).isZero_homology.isoZero

end TwoMembers

/-! ### Two-member covers -/

section Main

variable [Quiver.IsThin C] [Abelian A] {T : C} (hT : IsTerminal T) (P : Cᵒᵖ ⥤ A)

section

variable [HasProducts.{0} A] (U : Fin 2 → C)

/-- The family `U` restricted to an object mapping to one of its members is acyclic. -/
private lemma quasiIso_restr {Y : C} {i₀ : Fin 2} (f : Y ⟶ U i₀) :
    QuasiIso (cechAugmentation U hT (restr P Y)) :=
  quasiIso_cechAugmentation_prod_of_hom U hT P Y f

/-- **The Čech complex of a two-member family is exact in degrees `≥ 2`.** In a thin category
with finite products, the Čech complex of any presheaf with values in an abelian category, for a
family of two objects, is exact in every degree `≥ 2`. -/
theorem exactAt_add_two_cechComplexFunctor_obj (n : ℕ) :
    ((cechComplexFunctor U).obj P).ExactAt (n + 2) := by
  have hS := mvShortComplex_shortExact U U id (fun i ↦ 𝟙 (U i)) P
  have hX₂ := (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact.exactAt_X₂ (n + 2)
    (exactAt_restr U terminalIsTerminal P (quasiIso_restr terminalIsTerminal P U (𝟙 (U 0)))
      (n + 1))
    (exactAt_restr U terminalIsTerminal P (quasiIso_restr terminalIsTerminal P U (𝟙 (U 1)))
      (n + 1))
  have hX₃ := exactAt_restr U terminalIsTerminal P
    (quasiIso_restr terminalIsTerminal P U (prod.fst : U 0 ⨯ U 1 ⟶ U 0)) n
  exact hS.exactAt_X₁ (n + 2) (mono_of_source_iso_zero _ hX₂.isZero_homology.isoZero)
    fun i hi ↦ by
      obtain rfl : i = n + 1 := by simp only [ComplexShape.up_Rel] at hi; omega
      exact epi_of_target_iso_zero _ hX₃.isZero_homology.isoZero

/-- The augmented Čech complex of `P` for a two-member family `U` is exact exactly when the
Mayer-Vietoris sequence of `U` is short exact. -/
private lemma quasiIso_cechAugmentation_fin_two_iff_mvSC :
    QuasiIso (cechAugmentation U hT P) ↔
      ((mvSC U hT P).Exact ∧ Mono (mvSC U hT P).f) ∧ Epi (mvSC U hT P).g :=
  quasiIso_cechAugmentation_iff_mvSC U U hT P
    (mvShortComplex_shortExact U U id (fun i ↦ 𝟙 (U i)) P)
    (quasiIso_restr hT P U (𝟙 (U 0))) (quasiIso_restr hT P U (𝟙 (U 1)))
    (quasiIso_restr hT P U (prod.fst : U 0 ⨯ U 1 ⟶ U 0))

/-- **Exactness of the Čech complex of a two-member cover.** In a thin category with finite
products and a terminal object `T`, let `P` be a presheaf with values in an abelian category and
let `U 0`, `U 1` be two objects. The augmented Čech complex `0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯`
is exact if and only if `P` satisfies the sheaf condition for the family `U i ⟶ T` and the
difference of restrictions `P(U 0) ⊞ P(U 1) ⟶ P(U 0 × U 1)` is an epimorphism, that is, if and
only if the Mayer-Vietoris sequence `0 ⟶ P(T) ⟶ P(U 0) ⊞ P(U 1) ⟶ P(U 0 × U 1) ⟶ 0` is short
exact. -/
theorem quasiIso_cechAugmentation_fin_two_iff :
    QuasiIso (cechAugmentation U hT P) ↔
      (∀ E : Aᵒᵖ, (Presieve.ofArrows U fun i ↦ hT.from (U i)).IsSheafFor (P ⋙ coyoneda.obj E)) ∧
        Epi (biprod.desc (P.map (prod.fst : U 0 ⨯ U 1 ⟶ U 0).op)
          (-P.map (prod.snd : U 0 ⨯ U 1 ⟶ U 1).op)) := by
  rw [← quasiIsoAt_cechAugmentation_zero_iff,
    quasiIsoAt_cechAugmentation_zero_iff_mvSC U U hT P
      (mvShortComplex_shortExact U U id (fun i ↦ 𝟙 (U i)) P)
      (quasiIso_restr hT P U (𝟙 (U 0))) (quasiIso_restr hT P U (𝟙 (U 1)))
      (quasiIso_restr hT P U (prod.fst : U 0 ⨯ U 1 ⟶ U 0)),
    quasiIso_cechAugmentation_fin_two_iff_mvSC]
  rfl

end

/-- **Acyclicity of a family refining a two-member family.** In a thin category with finite
products and a terminal object `T`, let `P` be a presheaf with values in an abelian category, let
`V 0`, `V 1` be two objects and let `W` be a family each of whose members maps to `V 0` or to
`V 1`. Suppose that the augmented Čech complexes of the restricted presheaves `P(V 0 × -)`,
`P(V 1 × -)` and `P(V 0 × V 1 × -)` for `W` are exact; for open covers, this says that the
restrictions of `W` to `V 0`, `V 1` and `V 0 ∩ V 1` are acyclic. Then the augmented Čech complex of
`P` for `W` is exact if and only if the one for the two-member family `V` is. -/
theorem quasiIso_cechAugmentation_iff_of_fin_two [HasProducts.{w} A] [HasProducts.{0} A]
    (V : Fin 2 → C) {κ : Type w} {W : κ → C} (hW : ∀ k, ∃ i, Nonempty (W k ⟶ V i))
    (h₀ : QuasiIso (cechAugmentation W hT ((prod.functor.obj (V 0)).op ⋙ P)))
    (h₁ : QuasiIso (cechAugmentation W hT ((prod.functor.obj (V 1)).op ⋙ P)))
    (h₀₁ : QuasiIso (cechAugmentation W hT ((prod.functor.obj (V 0 ⨯ V 1)).op ⋙ P))) :
    QuasiIso (cechAugmentation W hT P) ↔ QuasiIso (cechAugmentation V hT P) := by
  rw [quasiIso_cechAugmentation_fin_two_iff_mvSC hT P V]
  exact quasiIso_cechAugmentation_iff_mvSC V W hT P (mvShortComplex_shortExact V W
    (fun k ↦ (hW k).choose) (fun k ↦ (hW k).choose_spec.some) P) h₀ h₁ h₀₁

/-- **Acyclicity relative to a two-member family acyclic on intersections.** In a thin category
with finite products and a terminal object `T`, let `P` be a presheaf with values in an abelian
category with exact products, let `V 0`, `V 1` be two objects and let `W` be a family. Suppose
that the augmented Čech complexes of the restricted presheaves `P(V 0 × -)`, `P(V 1 × -)` and
`P(V 0 × V 1 × -)` for `W` are exact, and that the augmented Čech complex of `P(X × -)` for `V` is
exact for every product `X = W a₀ × ⋯ × W aₙ` of one or more members of `W`; for open covers,
this says that the restrictions of `W` to `V 0`, `V 1` and `V 0 ∩ V 1` are acyclic, and that the
restriction of `V` to every nonempty finite intersection of members of `W` is acyclic. Then the
augmented Čech complex of `P` for `W` is exact if and only if the one for `V` is.

Unlike `quasiIso_cechAugmentation_iff_of_fin_two`, the family `W` need not refine `V`. -/
theorem quasiIso_cechAugmentation_iff_of_fin_two_of_quasiIso_prod [HasProducts.{w} A]
    [HasProducts.{0} A] (V : Fin 2 → C) {κ : Type w} (W : κ → C)
    [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → κ)) A]
    (hV : ∀ (n : ℕ) (a : Fin (n + 1) → κ),
      QuasiIso (cechAugmentation V hT ((prod.functor.obj (∏ᶜ fun j ↦ W (a j))).op ⋙ P)))
    (h₀ : QuasiIso (cechAugmentation W hT ((prod.functor.obj (V 0)).op ⋙ P)))
    (h₁ : QuasiIso (cechAugmentation W hT ((prod.functor.obj (V 1)).op ⋙ P)))
    (h₀₁ : QuasiIso (cechAugmentation W hT ((prod.functor.obj (V 0 ⨯ V 1)).op ⋙ P))) :
    QuasiIso (cechAugmentation W hT P) ↔ QuasiIso (cechAugmentation V hT P) := by
  rw [quasiIso_cechAugmentation_fin_two_iff_mvSC hT P V]
  refine quasiIso_cechAugmentation_iff_mvSC V W hT P ?_ h₀ h₁ h₀₁
  -- `mvShortComplex` is the sequence of Čech complexes of `mvPresheafSC`, which is short exact
  -- at each product of members of `W` by the Mayer-Vietoris criterion for `V`
  refine ShortComplex.shortExact_of_iso (mvShortComplexIso V W P)
    (shortExact_map_cechComplexFunctor W _ fun n a ↦ ?_)
  obtain ⟨⟨hex, hmono⟩, hepi⟩ :=
    (quasiIso_cechAugmentation_fin_two_iff_mvSC hT (restr P _) V).1 (hV n a)
  exact ShortComplex.shortExact_of_iso (mvPresheafSCEvalIso V hT P _).symm
    (ShortComplex.ShortExact.mk' hex hmono hepi)

end Main

end TauCeti.CategoryTheory
end
end
end GeometryLiteralSource018

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.MayerVietoris"

section GeometryLiteralSource019
/- Original source: TauCeti.Algebra.Category.Grp.EpiMono -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Epimorphisms of differences of restrictions for presheaves of abelian groups

Let `P` be a presheaf of abelian groups on a meet-semilattice `X` with a greatest element, and let
`U` and `V` be elements of `X`. The difference of restrictions `P(U) ⊞ P(V) ⟶ P(U ⨯ V)` (the
second map of the Mayer-Vietoris sequence) is an epimorphism of abelian groups exactly when every
element of `P(U ⊓ V)` is the difference of the restrictions of an element of `P(U)` and an
element of `P(V)`. The categorical product `U ⨯ V` is the meet `U ⊓ V`
(`CategoryTheory.Limits.CompleteLattice.prod_eq_inf`), and epimorphisms in `AddCommGrpCat` are
the surjections (`AddCommGrpCat.epi_iff_surjective`).

## Main results

* `CategoryTheory.Functor.epi_biprod_desc_map_prod_fst_neg_map_prod_snd_iff_surjective`: the
  difference of restrictions `P(U) ⊞ P(V) ⟶ P(U ⨯ V)` is an epimorphism if and only if the
  difference of restrictions `P(U) × P(V) → P(U ⊓ V)` is surjective.
-/

public section

open CategoryTheory Limits Opposite

universe w u

namespace CategoryTheory.Functor

variable {X : Type u} [SemilatticeInf X] [OrderTop X]

/-- **Surjectivity of a difference of restrictions.** For a presheaf `P` of abelian groups on a
meet-semilattice with a greatest element, the map `P(U) ⊞ P(V) ⟶ P(U ⨯ V)` sending `(s, t)` to the
difference of the restrictions of `s` and `t` is an epimorphism exactly when the difference of
restrictions `P(U) × P(V) → P(U ⊓ V)` is surjective. -/
theorem epi_biprod_desc_map_prod_fst_neg_map_prod_snd_iff_surjective
    (P : Xᵒᵖ ⥤ AddCommGrpCat.{w}) (U V : X) :
    Epi (biprod.desc (P.map (prod.fst : U ⨯ V ⟶ U).op) (-P.map (prod.snd : U ⨯ V ⟶ V).op)) ↔
      Function.Surjective fun x : P.obj (op U) × P.obj (op V) ↦
        P.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op x.1 -
          P.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op x.2 := by
  -- the product `U ⨯ V` is the meet `U ⊓ V`, so restriction between them is invertible
  let e := iso_of_both_ways (homOfLE (CompleteLattice.prod_eq_inf U V).ge)
    (homOfLE (CompleteLattice.prod_eq_inf U V).le)
  have he : biprod.desc (P.map (prod.fst : U ⨯ V ⟶ U).op)
      (-P.map (prod.snd : U ⨯ V ⟶ V).op) ≫ P.map e.hom.op =
        biprod.desc (P.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op)
          (-P.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op) := by
    -- morphisms of `X` are unique, so `e` followed by a projection is the inequality of the meet
    have h₀ : e.hom ≫ prod.fst = homOfLE inf_le_left := Subsingleton.elim _ _
    have h₁ : e.hom ≫ prod.snd = homOfLE inf_le_right := Subsingleton.elim _ _
    apply biprod.hom_ext' <;> simp [← P.map_comp, ← op_comp, h₀, h₁]
  rw [← epi_comp_iff_of_isIso _ (P.map e.hom.op), he,
    ← epi_comp_iff_of_epi (AddCommGrpCat.biprodIsoProd _ _).inv, AddCommGrpCat.epi_iff_surjective]
  refine Iff.of_eq (congrArg _ (funext fun x ↦ ?_))
  simp [AddCommGrpCat.biprodIsoProd_inv_comp_desc_apply, sub_eq_add_neg]

end CategoryTheory.Functor
end
end GeometryLiteralSource019

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Algebra.Category.Grp.EpiMono"

section GeometryLiteralSource020
/- Original source: TauCeti.Algebra.Category.Grp.IsSheafFor -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The sheaf condition for one presieve, for presheaves of abelian groups

For a presheaf `P` with values in an arbitrary category, the sheaf condition for a presieve `R` is
expressed through the presheaves of types `P ⋙ coyoneda.obj E` (as in `Presheaf.IsSheaf`, or in
`Presheaf.isLimit_iff_isSheafFor_presieve`). For a presheaf of abelian groups this is the same as
the sheaf condition for `R` on the underlying presheaf of sets: a compatible family of
homomorphisms out of `E` glues pointwise, and the glued map is additive because restriction to the
members of `R` is jointly injective. Mathlib's `Presheaf.isSheaf_iff_isSheaf_forget` is the
analogous statement for all covering sieves of a Grothendieck topology at once.

## Main results

* `CategoryTheory.Presieve.isSheafFor_comp_forget_addCommGrpCat_iff`: a presheaf of abelian
  groups satisfies the sheaf condition for a presieve `R` against every abelian group exactly when
  its underlying presheaf of sets satisfies the sheaf condition for `R`.
-/

public section

open Opposite

universe w v u

namespace CategoryTheory.Presieve

variable {C : Type u} [Category.{v} C] {X : C}

/-- **The sheaf condition for a presheaf of abelian groups is checked on underlying sets.** A
presheaf `P` of abelian groups satisfies the sheaf condition for a presieve `R` on the underlying
presheaf of sets exactly when, for every abelian group `E`, the presheaf of homomorphisms
`P ⋙ coyoneda.obj E` satisfies it. -/
theorem isSheafFor_comp_forget_addCommGrpCat_iff (R : Presieve X) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    R.IsSheafFor (P ⋙ forget AddCommGrpCat) ↔
      ∀ E : AddCommGrpCat.{w}ᵒᵖ, R.IsSheafFor (P ⋙ coyoneda.obj E) := by
  refine ⟨fun h E x hx ↦ ?_, fun h ↦ (Presieve.isSheafFor_iff_of_iso
    (Functor.isoWhiskerLeft P AddCommGrpCat.coyonedaObjIsoForget)).1 (h _)⟩
  -- restriction to the members of `R` is jointly injective on underlying sets
  have hsep {s t : P.obj (op X)} (hst : ∀ ⦃Y : C⦄ ⦃g : Y ⟶ X⦄ (hg : R g),
      P.map g.op s = P.map g.op t) : s = t :=
    h.isSeparatedFor.ext hst
  -- glue the values of the family at each `e : E`
  let y (e : E.unop) : Presieve.FamilyOfElements (P ⋙ forget _) R := fun _ g hg ↦ (x g hg).hom e
  have hy (e : E.unop) : (y e).Compatible := fun _ _ _ g₁ g₂ f₁ f₂ hf₁ hf₂ hw ↦
    ConcreteCategory.congr_hom (hx g₁ g₂ hf₁ hf₂ hw) e
  let t (e : E.unop) : P.obj (op X) := h.amalgamate (y e) (hy e)
  have ht (e : E.unop) ⦃Y : C⦄ ⦃g : Y ⟶ X⦄ (hg : R g) : P.map g.op (t e) = (x g hg).hom e :=
    h.valid_glue (hy e) g hg
  let φ : E.unop →+ P.obj (op X) :=
    { toFun := t
      map_zero' := hsep fun _ g hg ↦ by simp [ht _ hg]
      map_add' e e' := hsep fun _ g hg ↦ by simp [ht _ hg] }
  refine ⟨AddCommGrpCat.ofHom φ, fun _ g hg ↦ ConcreteCategory.ext_apply (ht · hg),
    fun ψ hψ ↦ ConcreteCategory.ext_apply fun e ↦ hsep fun _ g hg ↦ ?_⟩
  -- `ψ` and the glued map have the same restrictions at each `e`
  exact (ConcreteCategory.congr_hom (hψ g hg) e).trans (ht e hg).symm

end CategoryTheory.Presieve
end
end GeometryLiteralSource020

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Algebra.Category.Grp.IsSheafFor"

section GeometryLiteralSource021
/- Original source: TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.AddCommGrp -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Čech complexes of two-member covers for presheaves of abelian groups

Let `X` be a meet-semilattice with a greatest element `⊤`, for instance the opens of a topological
space contained in a fixed open, and let `P` be a presheaf of abelian groups on `X`. For two
elements `U 0` and `U 1`, `quasiIso_cechAugmentation_fin_two_iff` says that the augmented Čech
complex `0 ⟶ P(⊤) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is exact exactly when the Mayer-Vietoris sequence
`0 ⟶ P(⊤) ⟶ P(U 0) ⊞ P(U 1) ⟶ P(U 0 ⨯ U 1) ⟶ 0` is short exact. This file restates that criterion
elementwise, in the form in which it is checked in practice: the underlying presheaf of sets
satisfies the sheaf condition for the family `U i ≤ ⊤`, and every element of `P(U 0 ⊓ U 1)` is a
difference of restrictions of elements of `P(U 0)` and `P(U 1)`. The categorical product
`U 0 ⨯ U 1` is the meet `U 0 ⊓ U 1` (`CategoryTheory.Limits.CompleteLattice.prod_eq_inf`).

## Main results

* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_fin_two_iff_isSheafFor_and_surjective`: the
  augmented Čech complex of a presheaf of abelian groups on a meet-semilattice with top, for a
  two-member family, is exact if and only if the underlying presheaf of sets satisfies the sheaf
  condition for the family and the difference of restrictions `P(U 0) × P(U 1) → P(U 0 ⊓ U 1)` is
  surjective.
-/

public section

open CategoryTheory Limits Opposite

universe w u

namespace TauCeti.CategoryTheory

variable {X : Type u} [SemilatticeInf X] [OrderTop X] (P : Xᵒᵖ ⥤ AddCommGrpCat.{w})
  (U : Fin 2 → X)

/-- **The Čech complex of a two-member cover, elementwise.** Let `P` be a presheaf of abelian groups
on a meet-semilattice `X` with a greatest element `⊤`, and let `U 0`, `U 1` be two elements of
`X`. The augmented Čech complex `0 ⟶ P(⊤) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is exact if and only if the
underlying presheaf of sets of `P` satisfies the sheaf condition for the family `U i ≤ ⊤`, and
every element of `P(U 0 ⊓ U 1)` is the difference of the restrictions of an element of `P(U 0)`
and an element of `P(U 1)`. -/
theorem quasiIso_cechAugmentation_fin_two_iff_isSheafFor_and_surjective :
    QuasiIso (cechAugmentation U isTerminalTop P) ↔
      (Presieve.ofArrows U fun _ ↦ homOfLE le_top).IsSheafFor (P ⋙ forget AddCommGrpCat) ∧
        Function.Surjective fun x : P.obj (op (U 0)) × P.obj (op (U 1)) ↦
          P.map (homOfLE inf_le_left : U 0 ⊓ U 1 ⟶ U 0).op x.1 -
            P.map (homOfLE inf_le_right : U 0 ⊓ U 1 ⟶ U 1).op x.2 := by
  -- the maps to the terminal object `⊤` are the inequalities `U i ≤ ⊤`
  have hπ : (fun i ↦ isTerminalTop.from (U i)) = fun _ ↦ homOfLE le_top :=
    funext fun _ ↦ Subsingleton.elim _ _
  rw [quasiIso_cechAugmentation_fin_two_iff,
    P.epi_biprod_desc_map_prod_fst_neg_map_prod_snd_iff_surjective,
    Presieve.isSheafFor_comp_forget_addCommGrpCat_iff, hπ]

end TauCeti.CategoryTheory
end
end GeometryLiteralSource021

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.AddCommGrp"

section GeometryLiteralSource022
/- Original source: TauCeti.Algebra.Homology.ShortComplex.FunctorEquivalence -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Evaluating the short complex of diagrams associated to a diagram of short complexes

Mathlib's `CategoryTheory.ShortComplex.functorEquivalence` identifies the category of short
complexes in `J ⥤ C` with the functor category `J ⥤ ShortComplex C`. This file packages the
component at `j : J` of its counit on `F : J ⥤ ShortComplex C` as the isomorphism
`ShortComplex.diagramEvaluationIso F j` from
`((functorEquivalence J C).inverse.obj F).map ((evaluation J C).obj j)` to `F.obj j`, together
with its `@[simp]` component lemmas (`τ₁`, `τ₂`, `τ₃`) and naturality in `j`.
-/

public section

namespace CategoryTheory.ShortComplex

variable {C J : Type*} [Category* C] [Limits.HasZeroMorphisms C] [Category* J]

/-- Evaluating the short complex of diagrams attached to `F : J ⥤ ShortComplex C` at `j` gives
back `F.obj j`. This is the component at `j` of the counit of `ShortComplex.functorEquivalence`,
stated with the evaluated short complex as its source so that later composites are well typed. -/
def diagramEvaluationIso (F : J ⥤ ShortComplex C) (j : J) :
    ((functorEquivalence J C).inverse.obj F).map ((evaluation J C).obj j) ≅ F.obj j :=
  ((functorEquivalence J C).counitIso.app F).app j

/-- The first component of the forward morphism of `ShortComplex.diagramEvaluationIso` is the
identity. -/
@[simp]
theorem diagramEvaluationIso_hom_τ₁ (F : J ⥤ ShortComplex C) (j : J) :
    (diagramEvaluationIso F j).hom.τ₁ = 𝟙 (F.obj j).X₁ := by rfl

/-- The second component of the forward morphism of `ShortComplex.diagramEvaluationIso` is the
identity. -/
@[simp]
theorem diagramEvaluationIso_hom_τ₂ (F : J ⥤ ShortComplex C) (j : J) :
    (diagramEvaluationIso F j).hom.τ₂ = 𝟙 (F.obj j).X₂ := by rfl

/-- The third component of the forward morphism of `ShortComplex.diagramEvaluationIso` is the
identity. -/
@[simp]
theorem diagramEvaluationIso_hom_τ₃ (F : J ⥤ ShortComplex C) (j : J) :
    (diagramEvaluationIso F j).hom.τ₃ = 𝟙 (F.obj j).X₃ := by rfl

/-- The first component of the inverse morphism of `ShortComplex.diagramEvaluationIso` is the
identity. -/
@[simp]
theorem diagramEvaluationIso_inv_τ₁ (F : J ⥤ ShortComplex C) (j : J) :
    (diagramEvaluationIso F j).inv.τ₁ = 𝟙 (F.obj j).X₁ := by rfl

/-- The second component of the inverse morphism of `ShortComplex.diagramEvaluationIso` is the
identity. -/
@[simp]
theorem diagramEvaluationIso_inv_τ₂ (F : J ⥤ ShortComplex C) (j : J) :
    (diagramEvaluationIso F j).inv.τ₂ = 𝟙 (F.obj j).X₂ := by rfl

/-- The third component of the inverse morphism of `ShortComplex.diagramEvaluationIso` is the
identity. -/
@[simp]
theorem diagramEvaluationIso_inv_τ₃ (F : J ⥤ ShortComplex C) (j : J) :
    (diagramEvaluationIso F j).inv.τ₃ = 𝟙 (F.obj j).X₃ := by rfl

/-- Naturality of the forward morphism of `ShortComplex.diagramEvaluationIso`. -/
@[reassoc]
theorem diagramEvaluationIso_hom_naturality (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    ((functorEquivalence J C).inverse.obj F).mapNatTrans ((evaluation J C).map f) ≫
        (diagramEvaluationIso F Y).hom =
      (diagramEvaluationIso F X).hom ≫ F.map f :=
  ((functorEquivalence J C).counitIso.app F).hom.naturality f

/-- Naturality of the inverse morphism of `ShortComplex.diagramEvaluationIso`. -/
@[reassoc]
theorem diagramEvaluationIso_inv_naturality (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    F.map f ≫ (diagramEvaluationIso F Y).inv =
      (diagramEvaluationIso F X).inv ≫
        ((functorEquivalence J C).inverse.obj F).mapNatTrans ((evaluation J C).map f) := by
  rw [Iso.comp_inv_eq, Category.assoc, diagramEvaluationIso_hom_naturality, Iso.inv_hom_id_assoc]

end CategoryTheory.ShortComplex
end
end GeometryLiteralSource022

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Algebra.Homology.ShortComplex.FunctorEquivalence"

section GeometryLiteralSource023
/- Original source: TauCeti.Algebra.Homology.ShortComplex.PreservesHomology -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Homology classes and diagrams under functors preserving homology

For a functor `F` preserving the left homology of a short complex `S`, Mathlib identifies the
cycles and the homology of `S.map F` with the images under `F` of those of `S`, by
`ShortComplex.mapCyclesIso` and `ShortComplex.mapHomologyIso`, and records how the first of them
interacts with the inclusion of the cycles (`ShortComplex.mapCyclesIso_hom_iCycles`). This file
records the companion statement for the class map: under the two identifications, the class map
`homologyπ` of `S.map F` is the image under `F` of the class map of `S`
(`ShortComplex.homologyπ_comp_mapHomologyIso_hom`).

It also provides the natural isomorphism `ShortComplex.homologyDiagramIso` identifying the
pointwise homology diagram `F ⋙ ShortComplex.homologyFunctor C` of a diagram
`F : J ⥤ ShortComplex C` with the homology of the associated short complex of diagrams
`(functorEquivalence J C).inverse.obj F` when that short complex has homology
(`((functorEquivalence J C).inverse.obj F).HasHomology`) and evaluation at each object preserves
its left and right homology.
-/

public section

namespace CategoryTheory.ShortComplex

section Map

variable {C D : Type*} [Category C] [Category D] [Limits.HasZeroMorphisms C]
  [Limits.HasZeroMorphisms D] (S : ShortComplex C) (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- The inverse cycles identification carries the inclusion of cycles in the mapped complex to
the image of the original inclusion. -/
@[reassoc (attr := simp)]
theorem mapCyclesIso_inv_comp_iCycles [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
  rw [Iso.inv_comp_eq, mapCyclesIso_hom_iCycles]

/-- **The class map commutes with a functor preserving homology.** Under the identifications
`mapCyclesIso` and `mapHomologyIso`, the class map of `S.map F` is the image under `F` of the
class map of `S`. -/
@[reassoc (attr := simp)]
theorem homologyπ_comp_mapHomologyIso_hom [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  -- Both identifications are computed from the left homology data `h` of `S`. The objects of
  -- `h.map F` are those of `h` under `F` only after unfolding, so rewriting with
  -- `LeftHomologyData.mapHomologyIso_eq` produces goals that are not type-correct at reducible
  -- transparency; the squares are therefore pasted as terms.
  let h := S.leftHomologyData
  exact (congrArg ((S.map F).homologyπ ≫ ·)
      (congrArg Iso.hom (LeftHomologyData.mapHomologyIso_eq h F))).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ F.map h.homologyIso.inv) (h.map F).homologyπ_comp_homologyIso_hom).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((h.map F).cyclesIso.hom ≫ ·) ((F.map_comp _ _).symm.trans
      ((congrArg F.map h.π_comp_homologyIso_inv).trans (F.map_comp _ _)))).trans <|
    (Category.assoc _ _ _).symm.trans <|
    congrArg (· ≫ F.map S.homologyπ)
      (congrArg Iso.hom (LeftHomologyData.mapCyclesIso_eq h F)).symm

end Map

section Diagram

variable {C J : Type*} [Category* C] [Limits.HasZeroMorphisms C] [Category* J]

/-- Evaluating the homology of the short complex of diagrams attached to `F : J ⥤ ShortComplex C`
along a morphism `f : X ⟶ Y` commutes with `ShortComplex.mapHomologyIso`. -/
@[reassoc]
theorem mapHomologyIso_evaluation_naturality (F : J ⥤ ShortComplex C)
    [((functorEquivalence J C).inverse.obj F).HasHomology]
    {X Y : J} (f : X ⟶ Y)
    [((evaluation J C).obj X).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [((evaluation J C).obj X).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [((evaluation J C).obj Y).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [((evaluation J C).obj Y).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)] :
    homologyMap
        (((functorEquivalence J C).inverse.obj F).mapNatTrans ((evaluation J C).map f)) ≫
      (((functorEquivalence J C).inverse.obj F).mapHomologyIso
        ((evaluation J C).obj Y)).hom =
    (((functorEquivalence J C).inverse.obj F).mapHomologyIso
        ((evaluation J C).obj X)).hom ≫
      ((functorEquivalence J C).inverse.obj F).homology.map f := by
  -- Since `((evaluation J C).map f).app G = G.map f`, the right-hand factor is the component of
  -- `NatTrans.app_homology ((evaluation J C).map f)` on `(functorEquivalence J C).inverse.obj F`.
  rw [← Iso.inv_comp_eq]
  exact (NatTrans.app_homology ((evaluation J C).map f)
    ((functorEquivalence J C).inverse.obj F)).symm

variable [CategoryWithHomology C]

/-- The pointwise homology diagram of `F : J ⥤ ShortComplex C` is naturally isomorphic to the
homology of the associated short complex of diagrams `(functorEquivalence J C).inverse.obj F` when
`((functorEquivalence J C).inverse.obj F).HasHomology` holds and evaluation at each object
preserves its left and right homology. -/
noncomputable def homologyDiagramIso (F : J ⥤ ShortComplex C)
    [((functorEquivalence J C).inverse.obj F).HasHomology]
    [∀ j : J, ((evaluation J C).obj j).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [∀ j : J, ((evaluation J C).obj j).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)] :
    F ⋙ homologyFunctor C ≅ ((functorEquivalence J C).inverse.obj F).homology :=
  NatIso.ofComponents
    (fun j ↦ homologyMapIso (diagramEvaluationIso F j).symm ≪≫
      ((functorEquivalence J C).inverse.obj F).mapHomologyIso ((evaluation J C).obj j))
    (fun {X Y} f ↦ by
      dsimp [homologyFunctor, homologyMapIso]
      rw [Category.assoc, ← mapHomologyIso_evaluation_naturality F f, ← Category.assoc,
        ← Category.assoc, ← homologyMap_comp, ← homologyMap_comp,
        diagramEvaluationIso_inv_naturality])

/-- The forward component of `ShortComplex.homologyDiagramIso` at `j`. -/
@[simp]
theorem homologyDiagramIso_hom_app (F : J ⥤ ShortComplex C)
    [((functorEquivalence J C).inverse.obj F).HasHomology]
    [∀ j : J, ((evaluation J C).obj j).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [∀ j : J, ((evaluation J C).obj j).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)] (j : J) :
    (homologyDiagramIso F).hom.app j =
      homologyMap (diagramEvaluationIso F j).inv ≫
        (((functorEquivalence J C).inverse.obj F).mapHomologyIso
          ((evaluation J C).obj j)).hom := by rfl

/-- The inverse component of `ShortComplex.homologyDiagramIso` at `j`. -/
@[simp]
theorem homologyDiagramIso_inv_app (F : J ⥤ ShortComplex C)
    [((functorEquivalence J C).inverse.obj F).HasHomology]
    [∀ j : J, ((evaluation J C).obj j).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [∀ j : J, ((evaluation J C).obj j).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)] (j : J) :
    (homologyDiagramIso F).inv.app j =
      (((functorEquivalence J C).inverse.obj F).mapHomologyIso
          ((evaluation J C).obj j)).inv ≫
        homologyMap (diagramEvaluationIso F j).hom := by rfl

end Diagram

end CategoryTheory.ShortComplex
end
end GeometryLiteralSource023

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Algebra.Homology.ShortComplex.PreservesHomology"

section GeometryLiteralSource024
/- Original source: TauCeti.Algebra.Homology.ShortComplex.Limit -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Homology and exact limits

This file proves that homology of short complexes, and hence homology of homological complexes,
commutes with limits of every shape whose limits are exact. Consequently a limit of
quasi-isomorphisms is a quasi-isomorphism when limits of that shape are exact.

## Main results

* `TauCeti.shortComplexHomologyFunctor_preservesLimitsOfShape`: homology of short complexes
  preserves limits of any exact shape.
* `TauCeti.homologicalComplexShortComplexFunctor_preservesLimitsOfShape`: the short complex
  associated to a homological complex preserves all existing limits.
* `TauCeti.homologicalComplexHomologyFunctor_preservesLimitsOfShape`: homology of homological
  complexes preserves limits of any exact shape.
* `TauCeti.quasiIso_limMap`: a limit of quasi-isomorphisms of homological complexes is a
  quasi-isomorphism when limits of that shape are exact.
* `TauCeti.quasiIso_pi_map`: a product of quasi-isomorphisms of homological complexes is a
  quasi-isomorphism when products of that shape are exact.

## Implementation notes

A diagram `F : J ⥤ ShortComplex C` corresponds under `ShortComplex.functorEquivalence` to a short
complex `S` of diagrams. The limiting cone used here is the image of `S` under
`lim : (J ⥤ C) ⥤ C`, with legs assembled from the counit of that equivalence. Working with the
counit rather than with the definitional identification of this cone with `ShortComplex.limitCone`
keeps every intermediate statement well typed for `rw` and `simp`: in a general category, unlike in
a concrete one, neither the unit laws nor associativity hold definitionally, so the composites
appearing here cannot be manipulated by `rfl` alone.

Exactness of `J`-shaped limits makes `lim` preserve homology, identifying the homology of this cone
with the chosen limit of the pointwise homology diagram.

## Sources

This file is the exact-limit dual of `TauCeti/Algebra/Homology/ShortComplex/Colimit`, and follows
that file's exact-colimit construction step for step. The formal inputs are Joël Riou's short
complex API in Mathlib — `ShortComplex.functorEquivalence` in
`Mathlib/Algebra/Homology/ShortComplex/FunctorEquivalence`, `ShortComplex.isLimitOfIsLimitπ` in
`Mathlib/Algebra/Homology/ShortComplex/Limits`, `ShortComplex.mapHomologyIso` and
`NatTrans.app_homology` in `Mathlib/Algebra/Homology/ShortComplex/PreservesHomology` and
`Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex` — together with the exactness class
`HasExactLimitsOfShape` of Dagur Asgeirsson, Isaac Hernando, Coleton Kotch and Adam Topaz in
`Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic`.
-/

public section

namespace TauCeti

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w w'

variable {C : Type u} [Category.{v} C]

section

variable {J : Type w} [Category.{w'} J] [HasLimitsOfShape J C]

section HasZeroMorphisms

variable [HasZeroMorphisms C]

private theorem lim_π_comp_mapNatTrans_evaluation
    (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (lim.π X) ≫
        ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans
          ((evaluation J C).map f) =
      ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (lim.π Y) := by
  ext <;>
    simp only [ShortComplex.comp_τ₁, ShortComplex.comp_τ₂, ShortComplex.comp_τ₃,
      ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₂, ShortComplex.mapNatTrans_τ₃,
      evaluation_map_app, lim.π_app] <;>
    exact limit.w _ f

/-- The cone on `F : J ⥤ ShortComplex C` obtained by applying `lim` to the associated short
complex of diagrams. -/
private noncomputable def shortComplexLimCone (F : J ⥤ ShortComplex C) : Cone F where
  pt := ((ShortComplex.functorEquivalence J C).inverse.obj F).map lim
  π :=
    { app := fun j ↦
        ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (lim.π j) ≫
          (ShortComplex.diagramEvaluationIso F j).hom
      naturality := fun _ _ f ↦ by
        dsimp
        rw [Category.id_comp, Category.assoc,
          ← ShortComplex.diagramEvaluationIso_hom_naturality,
          ← Category.assoc, lim_π_comp_mapNatTrans_evaluation] }

/-- The cone `shortComplexLimCone F` is limiting: each of its three components is the chosen limit
cone of the corresponding diagram in `C`, up to the identities contributed by the counit of
`ShortComplex.functorEquivalence`. -/
private noncomputable def isLimitShortComplexLimCone (F : J ⥤ ShortComplex C) :
    IsLimit (shortComplexLimCone F) :=
  ShortComplex.isLimitOfIsLimitπ _
    (IsLimit.ofIsoLimit (limit.isLimit (F ⋙ ShortComplex.π₁))
      (Cone.ext (Iso.refl _) fun _ ↦ by
        dsimp [shortComplexLimCone, ShortComplex.π₁]
        rw [ShortComplex.diagramEvaluationIso_hom_τ₁]
        exact (Category.comp_id _).symm.trans (Category.id_comp _).symm))
    (IsLimit.ofIsoLimit (limit.isLimit (F ⋙ ShortComplex.π₂))
      (Cone.ext (Iso.refl _) fun _ ↦ by
        dsimp [shortComplexLimCone, ShortComplex.π₂]
        rw [ShortComplex.diagramEvaluationIso_hom_τ₂]
        exact (Category.comp_id _).symm.trans (Category.id_comp _).symm))
    (IsLimit.ofIsoLimit (limit.isLimit (F ⋙ ShortComplex.π₃))
      (Cone.ext (Iso.refl _) fun _ ↦ by
        dsimp [shortComplexLimCone, ShortComplex.π₃]
        rw [ShortComplex.diagramEvaluationIso_hom_τ₃]
        exact (Category.comp_id _).symm.trans (Category.id_comp _).symm))

end HasZeroMorphisms

variable [Abelian C] [HasExactLimitsOfShape J C]

private theorem shortComplex_mapHomologyIso_limit (F : J ⥤ ShortComplex C) (j : J) :
    (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso lim).inv ≫
        ShortComplex.homologyMap
          (((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (lim.π j)) =
      limit.π ((ShortComplex.functorEquivalence J C).inverse.obj F).homology j ≫
        (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso
          ((evaluation J C).obj j)).inv := by
  -- Since `(lim.π j).app G = limit.π G j`, the projection on the right is the component of
  -- `NatTrans.app_homology (lim.π j)` on `(ShortComplex.functorEquivalence J C).inverse.obj F`.
  rw [Iso.eq_comp_inv, Category.assoc]
  exact (NatTrans.app_homology (lim.π j)
    ((ShortComplex.functorEquivalence J C).inverse.obj F)).symm

private theorem shortComplexHomologyLimit_compatibility
    (F : J ⥤ ShortComplex C) (j : J) :
    limit.π ((ShortComplex.functorEquivalence J C).inverse.obj F).homology j ≫
        ((((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso
             ((evaluation J C).obj j)).inv ≫
          ShortComplex.homologyMap (ShortComplex.diagramEvaluationIso F j).hom) =
      (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso lim).inv ≫
        ShortComplex.homologyMap
          (((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (lim.π j) ≫
            (ShortComplex.diagramEvaluationIso F j).hom) := by
  rw [ShortComplex.homologyMap_comp, ← Category.assoc, ← Category.assoc,
    shortComplex_mapHomologyIso_limit]

/-- Homology of the limit cone `shortComplexLimCone F` is the chosen limit of the pointwise
homology diagram of `F`. -/
private noncomputable def shortComplexHomologyLimitConeIso (F : J ⥤ ShortComplex C) :
    (Cone.postcompose (ShortComplex.homologyDiagramIso F).inv).obj
        (limit.cone ((ShortComplex.functorEquivalence J C).inverse.obj F).homology) ≅
      (ShortComplex.homologyFunctor C).mapCone (shortComplexLimCone F) :=
  Cone.ext (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso lim).symm
    (fun j ↦ by
      dsimp [shortComplexLimCone, ShortComplex.homologyFunctor]
      rw [ShortComplex.homologyDiagramIso_inv_app, shortComplexHomologyLimit_compatibility])

/-- Homology of short complexes preserves limits of any exact shape. -/
instance shortComplexHomologyFunctor_preservesLimitsOfShape :
    PreservesLimitsOfShape J (ShortComplex.homologyFunctor C) where
  preservesLimit {F} :=
    preservesLimit_of_preserves_limit_cone
      (isLimitShortComplexLimCone F)
      ((IsLimit.equivOfNatIsoOfIso
        (ShortComplex.homologyDiagramIso F).symm
        (limit.cone ((ShortComplex.functorEquivalence J C).inverse.obj F).homology)
        ((ShortComplex.homologyFunctor C).mapCone (shortComplexLimCone F))
        (shortComplexHomologyLimitConeIso F)) (limit.isLimit _))

variable {I D : Type*} [Category D] [HasZeroMorphisms D] [HasLimitsOfShape J D]
  (c : ComplexShape I) (q : I)

/-- Sending a homological complex to its short complex at one degree preserves all existing
limits. -/
instance homologicalComplexShortComplexFunctor_preservesLimitsOfShape :
    PreservesLimitsOfShape J
      (HomologicalComplex.shortComplexFunctor D c q) where
  preservesLimit {F} := by
    apply preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    apply ShortComplex.isLimitOfIsLimitπ
    · exact isLimitOfPreserves (HomologicalComplex.eval D c (c.prev q))
        (limit.isLimit F)
    · exact isLimitOfPreserves (HomologicalComplex.eval D c q)
        (limit.isLimit F)
    · exact isLimitOfPreserves (HomologicalComplex.eval D c (c.next q))
        (limit.isLimit F)

/-- Homology in any degree of a homological complex preserves limits of any exact shape. -/
instance homologicalComplexHomologyFunctor_preservesLimitsOfShape :
    PreservesLimitsOfShape J
      (HomologicalComplex.homologyFunctor C c q) := by
  exact preservesLimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso C c q).symm

variable {c}

/-- **Limits of quasi-isomorphisms.** If limits of shape `J` are exact, a morphism of `J`-shaped
diagrams of homological complexes which is a quasi-isomorphism at every index induces a
quasi-isomorphism on limits: homology commutes with these limits. -/
theorem quasiIso_limMap {F G : J ⥤ HomologicalComplex C c} (φ : F ⟶ G)
    (hφ : ∀ j, QuasiIso (φ.app j)) : QuasiIso (limMap φ) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor C c q
  have (j : J) : IsIso ((Functor.whiskerRight φ H).app j) :=
    (quasiIsoAt_iff_isIso_homologyMap (φ.app j) q).mp ((hφ j).quasiIsoAt q)
  have : IsIso (Functor.whiskerRight φ H) := NatIso.isIso_of_isIso_app _
  have : IsIso (H.map (limMap φ) ≫ limit.post G H) := by
    rw [limit.map_post]
    infer_instance
  exact IsIso.of_isIso_comp_right (H.map (limMap φ)) (limit.post G H)

end

/-- **Products of quasi-isomorphisms.** If products indexed by `β` are exact, the product of a
family of quasi-isomorphisms of homological complexes is a quasi-isomorphism. -/
theorem quasiIso_pi_map [Abelian C] {I : Type*} {c : ComplexShape I}
    {β : Type w} [HasLimitsOfShape (Discrete β) C]
    [HasExactLimitsOfShape (Discrete β) C] {K L : β → HomologicalComplex C c}
    (φ : ∀ b, K b ⟶ L b) (hφ : ∀ b, QuasiIso (φ b)) : QuasiIso (Limits.Pi.map φ) :=
  quasiIso_limMap (F := Discrete.functor K) (G := Discrete.functor L)
    (Discrete.natTrans fun b ↦ φ b.as) fun b ↦ hφ b.as

end TauCeti
end
end GeometryLiteralSource024

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Algebra.Homology.ShortComplex.Limit"

section GeometryLiteralSource025
/- Original source: TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Comparison -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Comparing the Čech acyclicity of two families

Let `C` be a category with finite products and a terminal object `T`, and let `P` be a presheaf
on `C` with values in an abelian category with exact products. For two families `U` and `V` of
objects, suppose that the restriction of `V` to every finite product of members of `U` is acyclic
for `P`, and that the restriction of `U` to every finite product of members of `V` is acyclic.
Then `U` is acyclic for `P` exactly when `V` is
(`quasiIso_cechAugmentation_iff_of_quasiIso_prod`). Here a family `U` is acyclic for `P` when the
augmented Čech complex `0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is exact, and its restriction to an
object `X` is the family `U` with the presheaf `P(X × -)`.

For open covers of a space this is the classical comparison of the Čech cohomology of two covers
each of which is acyclic on the finite intersections of members of the other. Its main use is for
a cover `U` with a refinement `V`: then the restriction of `U` to every finite intersection of
members of `V` has a member containing everything, so it is acyclic, and acyclicity passes from
`V` to `U` as soon as `V` is acyclic on the finite intersections of members of `U`
(`quasiIso_cechAugmentation_of_quasiIso_prod_of_hom`). This is how acyclicity passes from
standard covers, which refine every finite cover of an affinoid by rational subsets, to all such
covers in the proof of Tate's acyclicity theorem.

The proof resolves `P` by the presheaves `Y ↦ Čᵏ(V, P(Y × -))`. This resolution is exact at `T`
and at the finite products of members of `U`, by the hypotheses on `V`. Each term is a product of
restrictions of `P` to finite products of members of `V`, hence acyclic for `U`
(`quasiIso_cechAugmentation_pi`), so `quasiIso_cechAugmentation_of_resolution` applies. This
replaces the usual double complex argument by dimension shifting along the resolution.

## Main results

* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_limit`: a limit of acyclic presheaves is
  acyclic, when limits of that shape are exact.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_pi`: a product of acyclic presheaves is
  acyclic, when products of that shape are exact.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff_of_quasiIso_prod`: two families each
  acyclic on the finite products of members of the other are acyclic together.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_quasiIso_prod_of_hom`: in a thin category,
  a family is acyclic if some acyclic refinement of it is acyclic on the finite products of its
  members.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Appendix A, for acyclic covers,
  and the proof of Theorem 8.28, which passes from standard covers to arbitrary rational covers.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Springer, 1984, §8.1.4, for the
  comparison of the Čech cohomology of a covering and a refinement, as used in rigid geometry.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C) {T : C} (hT : IsTerminal T)

/-! ### Limits of acyclic presheaves -/

/-- The augmentation of the Čech complex for `U`, as a natural transformation in the presheaf. -/
private def cechAugmentationNatTrans :
    (evaluation Cᵒᵖ A).obj (op T) ⋙ CochainComplex.single₀ A ⟶ cechComplexFunctor (A := A) U where
  app Q := cechAugmentation U hT Q
  naturality _ _ α := (cechAugmentation_naturality U hT _ α).symm

/-- **Limits of acyclic presheaves are acyclic.** If limits of shape `J` are exact in `A`, a limit
of a `J`-shaped diagram of presheaves whose augmented Čech complexes for `U` are exact has an exact
augmented Čech complex for `U`. -/
theorem quasiIso_cechAugmentation_limit {J : Type*} [Category J] [HasLimitsOfShape J A]
    [HasExactLimitsOfShape J A] (F : J ⥤ Cᵒᵖ ⥤ A)
    (hF : ∀ j, QuasiIso (cechAugmentation U hT (F.obj j))) :
    QuasiIso (cechAugmentation U hT (limit F)) := by
  -- both the Čech complex and the complex concentrated in degree `0` preserve the limit
  have h : cechAugmentation U hT (limit F) ≫ limit.post F (cechComplexFunctor U) =
      limit.post F ((evaluation Cᵒᵖ A).obj (op T) ⋙ CochainComplex.single₀ A) ≫
        limMap (Functor.whiskerLeft F (cechAugmentationNatTrans U hT)) := by
    refine limit.hom_ext fun j ↦ ?_
    rw [Category.assoc, Category.assoc, limit.post_π, limMap_π, limit.post_π_assoc,
      Functor.whiskerLeft_app]
    exact cechAugmentation_naturality U hT _ (limit.π F j)
  rw [← quasiIso_iff_comp_right _ (limit.post F (cechComplexFunctor U)), h,
    quasiIso_iff_comp_left]
  exact quasiIso_limMap _ hF

/-- **Products of acyclic presheaves are acyclic.** If products indexed by `J` are exact in `A`,
a product of presheaves whose augmented Čech complexes for `U` are exact has an exact augmented
Čech complex for `U`. -/
theorem quasiIso_cechAugmentation_pi {J : Type w} [HasExactLimitsOfShape (Discrete J) A]
    (G : J → Cᵒᵖ ⥤ A) (hG : ∀ j, QuasiIso (cechAugmentation U hT (G j))) :
    QuasiIso (cechAugmentation U hT (∏ᶜ G)) :=
  quasiIso_cechAugmentation_limit U hT (Discrete.functor G) fun j ↦ hG j.as

/-! ### Comparing two families

The proof that acyclicity passes from `V` to `U` resolves `P` by the Čech complexes of the
restricted presheaves `P(Y × -)` for `V`: in degree `k` this is the presheaf
`Y ↦ ∏_b P(Y × V (b 0) × ⋯ × V (b k))`, which is acyclic for `U` by the hypothesis on `U`, and the
resolution is exact at `T` and on the finite products of members of `U` by the hypotheses on `V`.
`quasiIso_cechAugmentation_of_resolution` then applies. -/

section Comparison

variable (P : Cᵒᵖ ⥤ A)

/-- The presheaves `P(Y × -)`, as a presheaf in `Y`. -/
private abbrev restrictionFunctor : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A :=
  prod.functor.op ⋙ Functor.opHom C C ⋙ (Functor.whiskeringRight Cᵒᵖ Cᵒᵖ A).obj P

/-- The isomorphism `P(Y × T) ≅ P(Y)` of presheaves in `Y`. -/
private def restrictionFunctorTerminalIso :
    restrictionFunctor P ⋙ (evaluation Cᵒᵖ A).obj (op T) ≅ P :=
  -- evaluating `P(Y × -)` at `T` is `P(- × T)` by unfolding the composite
  (Functor.isoWhiskerRight (NatIso.op hT.prodRightUnitor).symm P ≪≫
    Functor.isoWhiskerRight (Functor.opId C) P ≪≫ Functor.leftUnitor P :
      (prod.functor.flip.obj T).op ⋙ P ≅ P)

/-- The isomorphism `P(T × X) ≅ P(X)` of presheaves in `X`. -/
private def terminalRestrictionIso : (prod.functor.obj T).op ⋙ P ≅ P :=
  Functor.isoWhiskerRight (NatIso.op hT.prodLeftUnitor).symm P ≪≫
    Functor.isoWhiskerRight (Functor.opId C) P ≪≫ Functor.leftUnitor P

/-- The isomorphism `P(Y × X) ≅ P(X × Y)` of presheaves in `Y` induced by the braiding. -/
private def restrictionBraidingIso (X : C) :
    (prod.functor.flip.obj X).op ⋙ P ≅ (prod.functor.obj X).op ⋙ P :=
  Functor.isoWhiskerRight (NatIso.op (NatIso.ofComponents (fun Y ↦ prod.braiding X Y)
    fun f ↦ braid_natural (𝟙 X) f)) P

variable {κ : Type w} (V : κ → C)

/-- In degree `k`, the Čech complex of `P(Y × -)` for `V` is the product, over
`b : Fin (k + 1) → κ`, of the presheaves `P(Y × V (b 0) × ⋯ × V (b k))` in `Y`. -/
private def cechTermIso (k : ℕ) :
    (restrictionFunctor P ⋙ cechComplexFunctor V) ⋙ HomologicalComplex.eval A _ k ≅
      ∏ᶜ fun b : Fin (k + 1) → κ ↦ (prod.functor.flip.obj (∏ᶜ fun j ↦ V (b j))).op ⋙ P :=
  NatIso.ofComponents (fun Y ↦ (piObjIso (fun b : Fin (k + 1) → κ ↦
    (prod.functor.flip.obj (∏ᶜ fun j ↦ V (b j))).op ⋙ P) Y).symm) fun {Y Y'} f ↦ by
    refine (Iso.comp_inv_eq _).2 ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine (Iso.eq_inv_comp _).2 ?_
    refine Pi.hom_ext _ _ fun b ↦ ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans (congrArg _ (cechComplexFunctor_map_f_π V _ _ k b)) ?_
    -- the factors of the Čech term are the values of the product, up to unfolding
    let G := fun b : Fin (k + 1) → κ ↦ (prod.functor.flip.obj (∏ᶜ fun j ↦ V (b j))).op ⋙ P
    have key (b : Fin (k + 1) → κ) :
        (piObjIso G Y).hom ≫ Pi.π (fun s ↦ (G s).obj Y) b ≫ (G b).map f =
          (∏ᶜ G).map f ≫ (piObjIso G Y').hom ≫ Pi.π (fun s ↦ (G s).obj Y') b := by
      rw [piObjIso_hom_comp_π_assoc, piObjIso_hom_comp_π, NatTrans.naturality]
    exact key b

variable [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) A]
  [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → κ)) A]

/-- If `V` is acyclic for `P`, the restriction of `V` to every finite product of members of `U`
is acyclic, and the restriction of `U` to every finite product of members of `V` is acyclic, then
`U` is acyclic for `P`. -/
private lemma quasiIso_cechAugmentation_of_quasiIso_prod
    (hV : QuasiIso (cechAugmentation V hT P))
    (hVU : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      QuasiIso (cechAugmentation V hT ((prod.functor.obj (∏ᶜ fun j ↦ U (a j))).op ⋙ P)))
    (hUV : ∀ (n : ℕ) (b : Fin (n + 1) → κ),
      QuasiIso (cechAugmentation U hT ((prod.functor.obj (∏ᶜ fun j ↦ V (b j))).op ⋙ P))) :
    QuasiIso (cechAugmentation U hT P) := by
  rw [← quasiIso_cechAugmentation_iff_of_iso U hT _ (restrictionFunctorTerminalIso hT P)]
  -- resolve `P(- × T) ≅ P` by the Čech complexes of the presheaves `P(Y × -)` for `V`
  refine quasiIso_cechAugmentation_of_resolution U hT
    (P := restrictionFunctor P ⋙ (evaluation Cᵒᵖ A).obj (op T))
    (Functor.whiskerLeft (restrictionFunctor P) (cechAugmentationNatTrans V hT)) ?_ hVU
    fun k ↦ ?_
  · exact (quasiIso_cechAugmentation_iff_of_iso V hT _ (terminalRestrictionIso hT P)).2 hV
  · rw [quasiIso_cechAugmentation_iff_of_iso U hT _ (cechTermIso P V k)]
    exact quasiIso_cechAugmentation_pi U hT _ fun b ↦
      (quasiIso_cechAugmentation_iff_of_iso U hT _ (restrictionBraidingIso P _)).2 (hUV k b)

/-- **Comparison of the Čech acyclicity of two families.** In a category with finite products and
a terminal object `T`, let `P` be a presheaf with values in an abelian category with exact
products, and let `U` and `V` be two families. Suppose that `V` is acyclic for `P(X × -)` for
every product `X` of finitely many members of `U`, and that `U` is acyclic for `P(X × -)` for
every product `X` of finitely many members of `V`; for open covers, the restriction of each cover
to every finite intersection of members of the other is acyclic. Then `U` is acyclic for `P` if
and only if `V` is. -/
theorem quasiIso_cechAugmentation_iff_of_quasiIso_prod
    (hVU : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      QuasiIso (cechAugmentation V hT ((prod.functor.obj (∏ᶜ fun j ↦ U (a j))).op ⋙ P)))
    (hUV : ∀ (n : ℕ) (b : Fin (n + 1) → κ),
      QuasiIso (cechAugmentation U hT ((prod.functor.obj (∏ᶜ fun j ↦ V (b j))).op ⋙ P))) :
    QuasiIso (cechAugmentation U hT P) ↔ QuasiIso (cechAugmentation V hT P) :=
  ⟨fun hU ↦ quasiIso_cechAugmentation_of_quasiIso_prod V hT P U hU hUV hVU,
    fun hV ↦ quasiIso_cechAugmentation_of_quasiIso_prod U hT P V hV hVU hUV⟩

/-- **Acyclicity from an acyclic refinement.** In a thin category with finite products and a
terminal object `T`, let `P` be a presheaf with values in an abelian category with exact
products, and let `V` be a family each of whose members maps to a member of the family `U`; for
open covers, `V` refines `U`. If `V` is acyclic for `P`, and the restriction of `V` to every
finite product of members of `U` is acyclic, then `U` is acyclic for `P`. -/
theorem quasiIso_cechAugmentation_of_quasiIso_prod_of_hom [Quiver.IsThin C]
    (hV : QuasiIso (cechAugmentation V hT P))
    (hVU : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      QuasiIso (cechAugmentation V hT ((prod.functor.obj (∏ᶜ fun j ↦ U (a j))).op ⋙ P)))
    (hrefine : ∀ j, ∃ i, Nonempty (V j ⟶ U i)) :
    QuasiIso (cechAugmentation U hT P) := by
  refine (quasiIso_cechAugmentation_iff_of_quasiIso_prod U hT P V hVU fun n b ↦ ?_).2 hV
  -- `V (b 0) × ⋯ × V (b n)` lies in `V (b 0)`, which lies in a member of `U`
  obtain ⟨i, ⟨g⟩⟩ := hrefine (b 0)
  exact quasiIso_cechAugmentation_prod_of_hom U hT P _ (Pi.π _ 0 ≫ g)

end Comparison

end TauCeti.CategoryTheory
end
end
end GeometryLiteralSource025

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Comparison"

section GeometryLiteralSource026
/- Original source: TauCeti.Topology.Sheaves.Cech -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Čech complexes of flasque sheaves, and degree zero Čech cohomology

Let `F` be a flasque sheaf of abelian groups on a topological space `X`. This file proves that
for every finite open cover `U` of `X` the augmented Čech complex
`0 ⟶ F(X) ⟶ Č⁰(U, F) ⟶ Č¹(U, F) ⟶ ⋯` is exact: flasque sheaves have no higher Čech cohomology
for finite covers. Together with the acyclicity of flasque sheaves for derived-functor cohomology
(`TauCeti.Topology.subsingleton_H'_succ_of_isFlasque`), this is the input to the comparison of
Čech and derived-functor cohomology for covers whose finite intersections are acyclic.

The proof is by induction on the number of members of the cover, applied more generally to the
restricted presheaves `V ↦ F(Y ∩ V)` for opens `Y` contained in the union of the members. For a
cover by two opens `V 0`, `V 1`, exactness reduces to the Mayer–Vietoris sequence
`0 ⟶ F(Y) ⟶ F(Y ∩ V 0) ⊕ F(Y ∩ V 1) ⟶ F(Y ∩ V 0 ∩ V 1) ⟶ 0`, which is exact on the left by the
sheaf condition and on the right because `F` is flasque. A cover by the opens `U a` and `U i`,
`i ∈ s`, refines the two-member cover by `U a` and `⋃_{i ∈ s} U i`, so it is acyclic once its
restrictions to these two opens and to their intersection are
(`TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff_of_fin_two`). The restrictions to `U a`
and to `U a ∩ ⋃_{i ∈ s} U i` have a member containing everything; the restriction to
`⋃_{i ∈ s} U i` is compared with the smaller cover by the `U i`, `i ∈ s`, which is acyclic by
induction (`TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff_of_quasiIso_prod`).

For an arbitrary sheaf of abelian groups and any open cover of `X`, the sheaf condition alone
identifies the degree `0` Čech cohomology with the global sections, and hence with the degree `0`
sheaf cohomology `H⁰(X, F)`.

## Main results

* `TopCat.Sheaf.isSheafFor_ofArrows_prod`: for any sheaf `F`, a family of opens `V i` and an
  open `Y` contained in their union, the presheaf `V ↦ F(Y ∩ V)` satisfies the sheaf condition
  for the family `V i`.
* `TopCat.Sheaf.quasiIso_cechAugmentation_prod_of_isFlasque`: for a flasque sheaf `F`, a
  finite family of opens `U i` and an open `Y` contained in their union, the augmented Čech
  complex of `V ↦ F(Y ∩ V)` for `U` is exact.
* `TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque`: a flasque sheaf has an exact
  augmented Čech complex for every finite open cover.
* `TauCeti.Topology.quasiIsoAt_cechAugmentation_zero_of_iSup_eq_top`: for any sheaf and any
  open cover of `X`, the augmentation of the Čech complex is a quasi-isomorphism in degree `0`.
* `TauCeti.Topology.homologyZeroCechIso`: the degree `0` Čech cohomology of a sheaf for an open
  cover of `X` is isomorphic to its degree `0` sheaf cohomology, naturally in the sheaf
  (`TauCeti.Topology.homologyMap_comp_homologyZeroCechIso_hom`).

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.4.3.
* The Stacks Project, Lemma 20.11.4 (tag 01EW).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TauCeti.CategoryTheory

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : X.Sheaf AddCommGrpCat.{u})

/-- **Gluing over an open contained in a union.** For a sheaf `F`, a family of opens `V i` and an
open `Y` contained in their union, the underlying presheaf of sets of `V ↦ F(Y ∩ V)` satisfies the
sheaf condition for the family `V i ≤ ⊤`: sections over the opens `Y ∩ V i` that agree on the
pairwise intersections glue uniquely to a section over `Y`. -/
theorem isSheafFor_ofArrows_prod (Y : Opens X) {ι : Type*} (V : ι → Opens X)
    (hY : Y ≤ ⨆ i, V i) :
    (Presieve.ofArrows V fun _ ↦ homOfLE le_top).IsSheafFor
      (((prod.functor.obj Y).op ⋙ F.presheaf) ⋙ CategoryTheory.forget AddCommGrpCat) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  rw [Presieve.Arrows.compatible_homOfLE_iff] at hx
  refine F.existsUnique_gluing' (fun i ↦ Y ⨯ V i) (Y ⨯ ⊤)
    (fun i ↦ (prod.functor.obj Y).map (homOfLE le_top)) ?_ x fun i j ↦ ?_
  · simp only [CompleteLattice.prod_eq_inf, inf_top_eq, ← inf_iSup_eq]
    exact le_inf le_rfl hY
  · -- the two restrictions agree on `Y ∩ V i ∩ V j`, which contains `(Y ∩ V i) ∩ (Y ∩ V j)`
    have h : (Y ⨯ V i) ⊓ (Y ⨯ V j) ≤ (Y ⨯ (V i ⊓ V j)) := by
      simp only [CompleteLattice.prod_eq_inf]
      exact le_inf (inf_le_left.trans inf_le_left) (inf_le_inf inf_le_right inf_le_right)
    rw [show (Y ⨯ V i).infLELeft (Y ⨯ V j) =
        homOfLE h ≫ (prod.functor.obj Y).map (homOfLE inf_le_left) from Subsingleton.elim _ _,
      show (Y ⨯ V i).infLERight (Y ⨯ V j) =
        homOfLE h ≫ (prod.functor.obj Y).map (homOfLE inf_le_right) from Subsingleton.elim _ _,
      op_comp, op_comp, F.presheaf.map_comp, F.presheaf.map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
    exact congrArg _ (hx i j)

variable [F.presheaf.IsFlasque]

/-- **Two-member covers.** For a flasque sheaf `F`, opens `V 0`, `V 1` and an open `Y` contained
in their union, the augmented Čech complex of `V ↦ F(Y ∩ V)` for the family `V 0`, `V 1` is
exact: sections over `Y ∩ V 0` and `Y ∩ V 1` agreeing on `Y ∩ V 0 ∩ V 1` glue uniquely, and
every section over `Y ∩ V 0 ∩ V 1` extends to `Y ∩ V 0` because `F` is flasque. -/
private lemma quasiIso_cechAugmentation_fin_two (Y : Opens X) (V : Fin 2 → Opens X)
    (hY : Y ≤ V 0 ⊔ V 1) :
    QuasiIso (cechAugmentation V isTerminalTop ((prod.functor.obj Y).op ⋙ F.presheaf)) := by
  rw [quasiIso_cechAugmentation_fin_two_iff_isSheafFor_and_surjective]
  refine ⟨F.isSheafFor_ofArrows_prod Y V (hY.trans (sup_le (le_iSup V 0) (le_iSup V 1))),
    fun z ↦ ?_⟩
  -- a section over `Y ∩ V 0 ∩ V 1` extends to `Y ∩ V 0`, as `F` is flasque
  obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective _).1 (TopCat.Presheaf.IsFlasque.epi
    (F := F.presheaf) ((prod.functor.obj Y).map (homOfLE inf_le_left : V 0 ⊓ V 1 ⟶ V 0)).op) z
  exact ⟨(y, 0), by simpa using hy⟩

/-- For a flasque sheaf `F`, a nonempty finite set `s` of indices of opens `U i` and an open `Y`
contained in the union of the `U i` with `i ∈ s`, the augmented Čech complex of `V ↦ F(Y ∩ V)` for
the subfamily indexed by `s` is exact. -/
private lemma quasiIso_cechAugmentation_prod_finset {ι : Type u} (U : ι → Opens X)
    {s : Finset ι} (hs : s.Nonempty) (Y : Opens X) (hY : Y ≤ s.sup U) :
    QuasiIso (cechAugmentation (fun i : s ↦ U i) isTerminalTop
      ((prod.functor.obj Y).op ⋙ F.presheaf)) := by
  induction hs using Finset.Nonempty.cons_induction generalizing Y with
  | singleton a =>
    exact quasiIso_cechAugmentation_prod_of_hom _ isTerminalTop _ Y
      (i₀ := ⟨a, Finset.mem_singleton_self a⟩) (homOfLE (by simpa using hY))
  | cons a s ha hs ih =>
    -- the cover refines the two-member cover by `U a` and `⋃_{i ∈ s} U i`
    let W : Finset.cons a s ha → Opens X := fun i ↦ U i
    let V : Fin 2 → Opens X := ![U a, s.sup U]
    let Q := (prod.functor.obj Y).op ⋙ F.presheaf
    have ha' : a ∈ Finset.cons a s ha := Finset.mem_cons_self a s
    have hW (k : Finset.cons a s ha) : ∃ i, Nonempty (W k ⟶ V i) := by
      obtain ⟨k, hk⟩ := k
      rcases Finset.mem_cons.1 hk with rfl | hk
      · exact ⟨0, ⟨𝟙 _⟩⟩
      · exact ⟨1, ⟨homOfLE (Finset.le_sup (f := U) hk)⟩⟩
    refine (quasiIso_cechAugmentation_iff_of_fin_two isTerminalTop Q V hW
      (quasiIso_cechAugmentation_prod_of_hom W isTerminalTop Q (V 0) (i₀ := ⟨a, ha'⟩) (𝟙 _)) ?_
      (quasiIso_cechAugmentation_prod_of_hom W isTerminalTop Q (V 0 ⨯ V 1) (i₀ := ⟨a, ha'⟩)
        prod.fst)).2
      (quasiIso_cechAugmentation_fin_two F Y V (by simpa [V, Finset.sup_cons] using hY))
    -- the restriction to `⋃_{i ∈ s} U i` is compared with the cover by the `U i`, `i ∈ s`
    let W' : s → Opens X := fun i ↦ U i
    -- restricting to `V 1` and then to `Y` is restricting to `Y ∩ V 1`
    let e := Functor.isoWhiskerRight (NatIso.op (prod.functorLeftComp Y (V 1))) F.presheaf
    refine (quasiIso_cechAugmentation_iff_of_quasiIso_prod W isTerminalTop
      ((prod.functor.obj (V 1)).op ⋙ Q) W' (fun n b ↦ ?_) (fun n b ↦ ?_)).2 ?_
    · exact (quasiIso_cechAugmentation_iff_of_iso _ _ _ (Functor.isoWhiskerLeft _ e ≪≫
        Functor.isoWhiskerRight (NatIso.op (prod.functorLeftComp _ _)) F.presheaf)).2
        (ih _ (leOfHom (prod.fst ≫ prod.snd)))
    · exact quasiIso_cechAugmentation_prod_of_hom W isTerminalTop _ _
        (i₀ := ⟨b 0, Finset.mem_cons_of_mem (b 0).2⟩) (Pi.π _ 0)
    · exact (quasiIso_cechAugmentation_iff_of_iso _ _ _ e).2 (ih _ (leOfHom prod.snd))

/-- **Flasque sheaves are acyclic for finite covers, restricted to an open.** Let `F` be a flasque
sheaf of abelian groups on `X`, let `U i` be a finite family of opens, and let `Y` be an open
contained in their union. Then the augmented Čech complex of the presheaf `V ↦ F(Y ∩ V)` for the
family `U` is exact; that is, the cover of `Y` by the opens `Y ∩ U i` is acyclic for `F`. -/
theorem quasiIso_cechAugmentation_prod_of_isFlasque {ι : Type u} [Finite ι] (U : ι → Opens X)
    (Y : Opens X) (hY : Y ≤ ⨆ i, U i) :
    QuasiIso (cechAugmentation U isTerminalTop ((prod.functor.obj Y).op ⋙ F.presheaf)) := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    -- an empty family only covers the empty open, over which every section group is zero
    have hzero (V : Opens X) : IsZero (((prod.functor.obj Y).op ⋙ F.presheaf).obj (op V)) :=
      (isZero_zero _).of_iso ((isZero_zero _).isoIsTerminal (F.isTerminalOfEqEmpty
        (eq_bot_iff.2 ((leOfHom prod.fst).trans (hY.trans (by rw [iSup_of_empty])))))).symm
    have hL : IsZero ((cechComplexFunctor U).obj ((prod.functor.obj Y).op ⋙ F.presheaf)) :=
      Functor.map_isZero _ (Functor.isZero _ fun V ↦ hzero V.unop)
    have := (Functor.map_isZero (CochainComplex.single₀ _) (hzero ⊤)).isIso hL
      (cechAugmentation U isTerminalTop ((prod.functor.obj Y).op ⋙ F.presheaf))
    infer_instance
  | inr _ =>
    have := Fintype.ofFinite ι
    exact (quasiIso_cechAugmentation_congr isTerminalTop _
      ⟨fun i ↦ ⟨i, Finset.mem_univ i⟩, fun _ ↦ 𝟙 _⟩ ⟨Subtype.val, fun _ ↦ 𝟙 _⟩).2
      (quasiIso_cechAugmentation_prod_finset F U Finset.univ_nonempty Y
        (by rwa [Finset.sup_univ_eq_iSup]))

/-- **Flasque sheaves are acyclic for finite covers.** For a flasque sheaf `F` of abelian groups
on `X` and a finite family of opens `U i` covering `X`, the augmented Čech complex
`0 ⟶ F(X) ⟶ Č⁰(U, F) ⟶ Č¹(U, F) ⟶ ⋯` is exact: `F` has no Čech cohomology for `U` in positive
degrees, and its degree `0` Čech cohomology is `F(X)`. -/
theorem quasiIso_cechAugmentation_of_isFlasque {ι : Type u} [Finite ι] (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) : QuasiIso (cechAugmentation U isTerminalTop F.presheaf) :=
  (quasiIso_cechAugmentation_iff_of_iso _ _ _
    (Functor.isoWhiskerRight (NatIso.op isTerminalTop.prodLeftUnitor) F.presheaf)).2
    (quasiIso_cechAugmentation_prod_of_isFlasque F U ⊤ hU.ge)

end TopCat.Sheaf

namespace TauCeti.Topology

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)

include hU

/-- A sheaf on `X` satisfies the sheaf condition for a family of opens covering `X`, in the form
used by the augmentation of the Čech complex. -/
theorem isSheafFor_ofArrows_of_iSup_eq_top
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (E : AddCommGrpCat.{u}ᵒᵖ) :
    (Presieve.ofArrows U fun i ↦ isTerminalTop.from (U i)).IsSheafFor
      (F.obj ⋙ coyoneda.obj E) := by
  rw [Presieve.isSheafFor_iff_generate]
  refine F.property E.unop _ fun x _ ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show x ∈ ⨆ i, U i by rw [hU]; trivial)
  exact ⟨U i, isTerminalTop.from _, Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i), hi⟩

/-- For a sheaf on `X` and a family of opens covering `X`, the augmentation of the Čech complex
is a quasi-isomorphism in degree `0`: the degree `0` Čech cohomology is the group of global
sections. -/
theorem quasiIsoAt_cechAugmentation_zero_of_iSup_eq_top
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    QuasiIsoAt (cechAugmentation U isTerminalTop F.obj) 0 :=
  (quasiIsoAt_cechAugmentation_zero_iff U isTerminalTop F.obj).2
    (isSheafFor_ofArrows_of_iSup_eq_top U hU F)

/-- The degree `0` Čech cohomology of a sheaf for a cover of `X` is the group of global sections,
which is also the degree `0` sheaf cohomology. -/
def homologyZeroCechIso (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((cechComplexFunctor U).obj F.obj).homology 0 ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{u} F 0) :=
  have := quasiIsoAt_cechAugmentation_zero_of_iSup_eq_top U hU F
  (asIso (HomologicalComplex.homologyMap (cechAugmentation U isTerminalTop F.obj) 0)).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 _ ≪≫
      ((_root_.CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).symm.toAddCommGrpIso)

/-- The identification of degree `0` Čech cohomology with degree `0` sheaf cohomology is natural
in the sheaf. -/
@[reassoc (attr := simp)]
theorem homologyMap_comp_homologyZeroCechIso_hom
    {P Q : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (g : P ⟶ Q) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map g.hom) 0 ≫
        (homologyZeroCechIso U hU Q).hom =
      (homologyZeroCechIso U hU P).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map g 0) := by
  have := quasiIsoAt_cechAugmentation_zero_of_iSup_eq_top U hU P
  have := quasiIsoAt_cechAugmentation_zero_of_iSup_eq_top U hU Q
  rw [← cancel_epi (HomologicalComplex.homologyMap (cechAugmentation U isTerminalTop P.obj) 0)]
  simp only [homologyZeroCechIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    ← HomologicalComplex.homologyMap_comp_assoc, cechAugmentation_naturality]
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc, IsIso.hom_inv_id_assoc,
    HomologicalComplex.singleObjHomologySelfIso_hom_naturality_assoc]
  congr 1
  ext x
  exact (_root_.CategoryTheory.Sheaf.H.equiv₀_symm_naturality isTerminalTop g x).symm

end TauCeti.Topology
end
end
end GeometryLiteralSource026

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Topology.Sheaves.Cech"

section GeometryLiteralSource027
/- Original source: TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Consequences of the long exact cohomology sequence of abelian sheaves

Mathlib's `CategoryTheory.Sheaf.H.longSequence` is the long exact cohomology sequence

`⋯ ⟶ Hⁿ⁰(F₁) ⟶ Hⁿ⁰(F₂) ⟶ Hⁿ⁰(F₃) ⟶ Hⁿ¹(F₁) ⟶ Hⁿ¹(F₂) ⟶ Hⁿ¹(F₃) ⟶ ⋯`

of a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of abelian sheaves on a site `(C, J)`, as a
`ComposableArrows` in `AddCommGrpCat`. This file repackages the exactness of the three
consecutive pairs as `Function.Exact` statements about the underlying additive maps, which is the
form in which the sequence is used, and records the injectivity and vanishing consequences that
follow from it.

## Main declarations

* `CategoryTheory.Sheaf.H.map_injective`, the injectivity of `H⁰(F₁) →+ H⁰(F₂)`, which is where
  the sequence starts;
* `CategoryTheory.Sheaf.H.exact_map_map`, `H.exact_map_δ` and `H.exact_δ_map`, the exactness of
  the sequence at `Hⁿ(F₂)`, at `Hⁿ⁰(F₃)` and at `Hⁿ¹(F₁)`;
* `CategoryTheory.Sheaf.H.map_g_surjective`, `H.subsingleton_X₂`, `H.subsingleton_X₃` and
  `H.subsingleton_X₁`, the vanishing consequences that the sequence is normally used for;
* `CategoryTheory.Sheaf.H.δ_surjective` and `H.δ_bijective`, the connecting map is onto, or an
  isomorphism, when the middle sheaf has no cohomology in the relevant degrees;
* `CategoryTheory.Sheaf.H'.postcomp_g_surjective`, `H'.subsingleton_X₃` and
  `H'.g_hom_app_surjective`, the corresponding statements for the cohomology `Hⁿ(V, -)` over an
  object `V` of the site, read off from the long exact `Ext` sequence out of the free abelian sheaf
  on `V`; the last is the degree zero case of the first, and says that
  sections over `V` of `F₂` map onto those of `F₃` when `H¹(V, F₁) = 0`, so that the sequence
  `0 ⟶ F₁(V) ⟶ F₂(V) ⟶ F₃(V) ⟶ 0` of sections is then short exact
  (`H'.shortExact_map_sheafSections`);
* `CategoryTheory.Sheaf.H'.subsingleton_X₁` and `H'.subsingleton_X₁_one`, the dimension-shifting
  steps `Hⁿ(V, F₃) = 0 ⇒ Hⁿ⁺¹(V, F₁) = 0` and `F₂(V) ↠ F₃(V) ⇒ H¹(V, F₁) = 0` when `F₂` has no
  cohomology on `V` in the next degree, both instances of
  `H'.subsingleton_X₁_of_postcomp_g_surjective`.

The underlying exactness statements are Mathlib's `CategoryTheory.Sheaf.H.longSequence_exact₁'`,
`longSequence_exact₂'` and `longSequence_exact₃'`. Sheaf cohomology on the small Zariski site of a
scheme is the cohomology of a sheaf of modules; the module-level form of the sequence is in
`TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence`.
-/

public section

open CategoryTheory Abelian

universe w v u

namespace CategoryTheory

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

namespace H

/-- A monomorphism of abelian sheaves is injective on cohomology in degree zero. -/
theorem map_injective {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) [Mono f] :
    Function.Injective (map f 0) := by
  intro x y hxy
  apply (Ext.addEquiv₀ (C := Sheaf J AddCommGrpCat.{v})).injective
  rw [← cancel_mono f, ← addEquiv₀_map, ← addEquiv₀_map, hxy]

include hS

/-- The long exact cohomology sequence is exact at `Hⁿ(F₂)`. -/
theorem exact_map_map (n : ℕ) : Function.Exact (map S.f n) (map S.g n) := by
  have := longSequence_exact₂' hS n
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

/-- The long exact cohomology sequence is exact at `Hⁿ⁰(F₃)`. -/
theorem exact_map_δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (map S.g n₀) (δ hS n₀ n₁ h) := by
  have := longSequence_exact₃' hS n₀ n₁ h
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

/-- The long exact cohomology sequence is exact at `Hⁿ¹(F₁)`. -/
theorem exact_δ_map (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (δ hS n₀ n₁ h) (map S.f n₁) := by
  have := longSequence_exact₁' hS n₀ n₁ h
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

/-- If `Hⁿ¹(F₁)` vanishes, then `Hⁿ⁰(F₂) →+ Hⁿ⁰(F₃)` is surjective. -/
theorem map_g_surjective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (_ : Subsingleton (H S.X₁ n₁)) :
    Function.Surjective (map S.g n₀) := fun x ↦
  (exact_map_δ hS n₀ n₁ h x).1 (Subsingleton.elim _ _)

/-- If `Hⁿ(F₁)` and `Hⁿ(F₃)` vanish, then so does `Hⁿ(F₂)`. -/
theorem subsingleton_X₂ (n : ℕ) (h₁ : Subsingleton (H S.X₁ n))
    (h₃ : Subsingleton (H S.X₃ n)) : Subsingleton (H S.X₂ n) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x₁, hx₁⟩ := (exact_map_map hS n x).1 (Subsingleton.elim _ _)
  obtain ⟨y₁, hy₁⟩ := (exact_map_map hS n y).1 (Subsingleton.elim _ _)
  rw [← hx₁, ← hy₁, Subsingleton.elim x₁ y₁]

/-- If `Hⁿ⁰(F₂)` and `Hⁿ¹(F₁)` vanish, then so does `Hⁿ⁰(F₃)`. -/
theorem subsingleton_X₃ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (_ : Subsingleton (H S.X₂ n₀))
    (h₁ : Subsingleton (H S.X₁ n₁)) : Subsingleton (H S.X₃ n₀) :=
  (map_g_surjective hS n₀ n₁ h h₁).subsingleton

/-- If `Hⁿ⁰(F₃)` and `Hⁿ¹(F₂)` vanish, then so does `Hⁿ¹(F₁)`. -/
theorem subsingleton_X₁ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (h₃ : Subsingleton (H S.X₃ n₀))
    (h₂ : Subsingleton (H S.X₂ n₁)) : Subsingleton (H S.X₁ n₁) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x₃, hx₃⟩ := (exact_δ_map hS n₀ n₁ h x).1 (Subsingleton.elim _ _)
  obtain ⟨y₃, hy₃⟩ := (exact_δ_map hS n₀ n₁ h y).1 (Subsingleton.elim _ _)
  rw [← hx₃, ← hy₃, Subsingleton.elim x₃ y₃]

/-- If `Hⁿ¹(F₂)` vanishes, then the connecting map `Hⁿ⁰(F₃) →+ Hⁿ¹(F₁)` is surjective. -/
theorem δ_surjective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (_ : Subsingleton (H S.X₂ n₁)) :
    Function.Surjective (δ hS n₀ n₁ h) := fun x ↦
  (exact_δ_map hS n₀ n₁ h x).1 (Subsingleton.elim _ _)

/-- If `Hⁿ⁰(F₂)` and `Hⁿ¹(F₂)` vanish, then the connecting map `Hⁿ⁰(F₃) →+ Hⁿ¹(F₁)` is
bijective. -/
theorem δ_bijective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (_ : Subsingleton (H S.X₂ n₀))
    (h₁ : Subsingleton (H S.X₂ n₁)) : Function.Bijective (δ hS n₀ n₁ h) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, δ_surjective hS n₀ n₁ h h₁⟩
  obtain ⟨y, rfl⟩ := (exact_map_δ hS n₀ n₁ h x).1 hx
  rw [Subsingleton.elim y 0, map_zero]

end H

namespace H'

open Opposite TauCeti.CategoryTheory

include hS

/-- If `Hⁿ⁺¹(V, F₁)` vanishes, then `Hⁿ(V, F₂) ⟶ Hⁿ(V, F₃)` is surjective. Here `Hⁿ(V, -)` is
`Ext` out of the free abelian sheaf on `V` (`TauCeti.CategoryTheory.sheafH'_eq`), and the map is
postcomposition with `F₂ ⟶ F₃`. -/
theorem postcomp_g_surjective (V : C) (n : ℕ) (h : Subsingleton (S.X₁.H' (n + 1) V)) :
    Function.Surjective
      ((Ext.mk₀ S.g).postcomp ((freeYonedaSheafFunctor J).obj V) (add_zero n)) := by
  have : Subsingleton (Ext ((freeYonedaSheafFunctor J).obj V) S.X₁ (n + 1)) := by
    simpa only [sheafH'_eq] using h
  exact fun x₃ ↦ Ext.covariant_sequence_exact₃ _ hS x₃ rfl (Subsingleton.elim _ _)

/-- If `Hⁿ(V, F₂)` and `Hⁿ⁺¹(V, F₁)` vanish, then so does `Hⁿ(V, F₃)`. -/
theorem subsingleton_X₃ (V : C) (n : ℕ) (h₂ : Subsingleton (S.X₂.H' n V))
    (h₁ : Subsingleton (S.X₁.H' (n + 1) V)) : Subsingleton (S.X₃.H' n V) := by
  have : Subsingleton (Ext ((freeYonedaSheafFunctor J).obj V) S.X₂ n) := by
    simpa only [sheafH'_eq] using h₂
  simpa only [sheafH'_eq] using (postcomp_g_surjective hS V n h₁).subsingleton

/-- If `H¹(V, F₁)` vanishes, then every section of `F₃` over `V` lifts to a section of `F₂`. -/
theorem g_hom_app_surjective (V : C) (h : Subsingleton (S.X₁.H' 1 V)) :
    Function.Surjective (S.g.hom.app (op V)) := by
  intro s
  obtain ⟨x, hx⟩ := postcomp_g_surjective hS V 0 h
    (Ext.mk₀ ((freeYonedaSheafSectionsEquiv J V S.X₃).symm s))
  refine ⟨freeYonedaSheafSectionsEquiv J V S.X₂ (Ext.addEquiv₀ x), ?_⟩
  rw [← freeYonedaSheafSectionsEquiv_naturality_right]
  have hx' : Ext.addEquiv₀ x ≫ S.g = (freeYonedaSheafSectionsEquiv J V S.X₃).symm s :=
    (TauCeti.ext_addEquiv₀_comp_mk₀ x S.g).symm.trans <| (congrArg Ext.addEquiv₀ hx).trans <|
      Ext.addEquiv₀.apply_symm_apply _
  rw [hx', AddEquiv.apply_symm_apply]

/-- If `Hⁿ(V, F₂) ⟶ Hⁿ(V, F₃)` is surjective and `Hⁿ⁺¹(V, F₂)` vanishes, then so does
`Hⁿ⁺¹(V, F₁)`. -/
theorem subsingleton_X₁_of_postcomp_g_surjective (V : C) (n : ℕ)
    (hg : Function.Surjective
      ((Ext.mk₀ S.g).postcomp ((freeYonedaSheafFunctor J).obj V) (add_zero n)))
    (h₂ : Subsingleton (S.X₂.H' (n + 1) V)) : Subsingleton (S.X₁.H' (n + 1) V) := by
  rw [sheafH'_eq] at h₂ ⊢
  refine subsingleton_of_forall_eq 0 fun x₁ ↦ ?_
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x₁ (Subsingleton.elim _ _) rfl
  obtain ⟨x₂, rfl⟩ := hg x₃
  rw [AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply, Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass, Ext.comp_zero]

/-- If `Hⁿ(V, F₃)` and `Hⁿ⁺¹(V, F₂)` vanish, then so does `Hⁿ⁺¹(V, F₁)`. -/
theorem subsingleton_X₁ (V : C) (n : ℕ) (h₃ : Subsingleton (S.X₃.H' n V))
    (h₂ : Subsingleton (S.X₂.H' (n + 1) V)) : Subsingleton (S.X₁.H' (n + 1) V) := by
  rw [sheafH'_eq] at h₃
  exact subsingleton_X₁_of_postcomp_g_surjective hS V n
    (fun _ ↦ ⟨0, Subsingleton.elim _ _⟩) h₂

/-- If `H¹(V, F₂)` vanishes and every section of `F₃` over `V` lifts to a section of `F₂`, then
`H¹(V, F₁)` vanishes. This is the converse of `g_hom_app_surjective`. -/
theorem subsingleton_X₁_one (V : C) (hg : Function.Surjective (S.g.hom.app (op V)))
    (h₂ : Subsingleton (S.X₂.H' 1 V)) : Subsingleton (S.X₁.H' 1 V) := by
  refine subsingleton_X₁_of_postcomp_g_surjective hS V 0 (fun x₃ ↦ ?_) h₂
  obtain ⟨t, ht⟩ := hg (freeYonedaSheafSectionsEquiv J V S.X₃ (Ext.addEquiv₀ x₃))
  refine ⟨Ext.mk₀ ((freeYonedaSheafSectionsEquiv J V S.X₂).symm t), ?_⟩
  rw [AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply, Ext.mk₀_comp_mk₀,
    ← Ext.mk₀_addEquiv₀_apply x₃]
  congr 1
  apply (freeYonedaSheafSectionsEquiv J V S.X₃).injective
  rw [freeYonedaSheafSectionsEquiv_naturality_right, AddEquiv.apply_symm_apply, ht]

/-- If `H¹(V, F₁)` vanishes, then the sequence of sections `0 ⟶ F₁(V) ⟶ F₂(V) ⟶ F₃(V) ⟶ 0` is
short exact. -/
theorem shortExact_map_sheafSections (V : C) (h : Subsingleton (S.X₁.H' 1 V)) :
    (S.map (sheafToPresheaf J AddCommGrpCat.{v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V))).ShortExact := by
  have := hS.mono_f
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
  · exact Functor.map_mono (sheafToPresheaf J AddCommGrpCat.{v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V)) S.f
  · exact (AddCommGrpCat.epi_iff_surjective _).2 (g_hom_app_surjective hS V h)

end H'

end Sheaf

end CategoryTheory
end
end GeometryLiteralSource027

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence"

section GeometryLiteralSource028
/- Original source: TauCeti.Topology.Sheaves.Flasque.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Flasque sheaves are acyclic

A sheaf of abelian groups on a topological space is flasque when all of its restriction maps are
surjective. This file proves that a flasque sheaf has no higher cohomology.

## Main declarations

* `TauCeti.Topology.isFlasque_of_injective`: an injective object in the category of abelian
  sheaves is flasque;
* `TauCeti.Topology.subsingleton_H'_succ_of_isFlasque`: a flasque sheaf has vanishing
  cohomology in every positive degree over every open subset;
* `TauCeti.Topology.subsingleton_H_succ_of_isFlasque`: the same statement for the cohomology
  of the whole space;
* `TauCeti.Topology.isFlasque_skyscraperSheaf`: skyscraper sheaves are flasque, and hence acyclic;
* `TopCat.Sheaf.IsFlasque.epi_cokernel_π_app` and `TopCat.Sheaf.IsFlasque.exact_cokernel_π_app`:
  if `0 ⟶ A ⟶ B ⟶ C` is exact with `A` and `B` flasque, then taking sections over an open `U`
  gives an exact sequence `B(U) ⟶ C(U) ⟶ (coker (B ⟶ C))(U) ⟶ 0`.

The proof is the classical dimension shift. Embedding a flasque sheaf `F` in an injective sheaf
`I` gives a short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0`, and the covariant long exact sequence of
`Ext` presents `Hⁿ⁺¹(U, F)` as a quotient of `Hⁿ(U, Q)`. In degree zero, the sections of `Q` over
`U` lift to sections of `I` because `F` is flasque, so the quotient vanishes; in higher degrees
`Q` is again flasque, because `I` is, and induction applies. That `I` is flasque is the point at
which `TauCeti/CategoryTheory/Sites/SheafCohomology/FreeYoneda.lean` enters: an inclusion of open
subsets induces a monomorphism of the free abelian sheaves they generate, and `Hom(-, I)` turns it
into the restriction map of `I`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer B, "coherent sheaves and
cohomology `Hⁱ(X, ℱ)`: acyclicity of affines, …, vanishing above dimension": it is the first
acyclicity theorem of the lane, and the acyclic skyscraper sheaves are the coefficients in which
the Riemann-Roch induction over the points of a divisor reads the additivity of
`TauCeti/AlgebraicGeometry/Cohomology/EulerCharacteristic.lean`.

No formalization is vendored: flasqueness, the surjectivity of sections out of a flasque
subsheaf, the stability of flasqueness under quotients and the flasqueness of skyscraper sheaves
are Mathlib's `Mathlib/Topology/Sheaves/Flasque.lean`, and the long exact sequence is Mathlib's
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₁`.

## References

* R. Hartshorne, *Algebraic Geometry*, III.2.4–2.5.
* The Stacks Project, tag 09SY, Lemma 20.12.3, *Flasque sheaves*.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.CategoryTheory (freeYonedaSheafFunctor freeYonedaSheafSectionsEquiv sheafH'_eq
  freeYonedaSheafSectionsEquiv_naturality_left freeYonedaSheafSectionsEquiv_naturality_right)

universe u

namespace TauCeti

namespace Topology

variable {X : TopCat.{u}}

noncomputable section

/-- An injective object in the category of sheaves of abelian groups is flasque. -/
instance isFlasque_of_injective
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective F] :
    TopCat.Presheaf.IsFlasque F.obj where
  -- Given `s : I(V)` and `V ≤ U`, represent `s` by `ℤ_V ⟶ I`, extend it along the
  -- monomorphism `ℤ_V ⟶ ℤ_U` using injectivity, and translate the extension back to a section.
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    refine ⟨freeYonedaSheafSectionsEquiv _ U.unop F
      (Injective.factorThru ((freeYonedaSheafSectionsEquiv _ V.unop F).symm s)
        ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).map i.unop)), ?_⟩
    have h := freeYonedaSheafSectionsEquiv_naturality_left
      (Opens.grothendieckTopology X) i.unop F
      (Injective.factorThru ((freeYonedaSheafSectionsEquiv _ V.unop F).symm s)
        ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).map i.unop))
    rw [Injective.comp_factorThru, AddEquiv.apply_symm_apply] at h
    exact h.symm

/-- The dimension-shifting induction: a flasque sheaf has no cohomology in positive degrees over
any open subset. -/
private lemma subsingleton_H'_succ_of_isFlasque_aux (n : ℕ) :
    ∀ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
      TopCat.Presheaf.IsFlasque F.obj → ∀ U : Opens X,
      Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) := by
  -- the injective sheaf `I` in `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` has no higher cohomology
  have hI (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (m : ℕ) (U : Opens X) :
      Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} (Injective.under F) (m + 1) U) := by
    rw [sheafH'_eq]
    exact Abelian.Ext.subsingleton_of_injective _ _ m
  induction n with
  | zero =>
    intro F hF U
    have hS := injectiveCokernelSequence_shortExact F
    have : TopCat.Presheaf.IsFlasque (injectiveCokernelSequence F).X₁.obj := hF
    have : TopCat.Presheaf.IsFlasque (injectiveCokernelSequence F).X₂.obj :=
      isFlasque_of_injective _
    -- sections of `Q` lift to `I`, because `F` is flasque
    have hepi : Epi ((injectiveCokernelSequence F).g.hom.app (op U)) :=
      TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
    exact Sheaf.H'.subsingleton_X₁_one hS U ((AddCommGrpCat.epi_iff_surjective _).1 hepi)
      (hI F 0 U)
  | succ n ih =>
    intro F hF U
    have hS := injectiveCokernelSequence_shortExact F
    have : TopCat.Presheaf.IsFlasque (injectiveCokernelSequence F).X₁.obj := hF
    have : TopCat.Presheaf.IsFlasque (injectiveCokernelSequence F).X₂.obj :=
      isFlasque_of_injective _
    -- `Q` is flasque, as a quotient of flasque sheaves
    exact Sheaf.H'.subsingleton_X₁ hS U (n + 1)
      (ih _ (TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS) U) (hI F (n + 1) U)

/-- A flasque sheaf of abelian groups has vanishing cohomology in every positive degree over
every open subset. -/
instance subsingleton_H'_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) (U : Opens X) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) :=
  subsingleton_H'_succ_of_isFlasque_aux n F inferInstance U

/-- A flasque sheaf of abelian groups has vanishing cohomology in every positive degree. -/
instance subsingleton_H_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F (n + 1)) := by
  have := subsingleton_H'_succ_of_isFlasque F n (⊤ : Opens X)
  exact Function.Injective.subsingleton
    (f := ConcreteCategory.hom
      (F.cohomologyPresheafObjIsoH (n + 1) isTerminalTop).inv)
    ((ConcreteCategory.bijective_of_isIso _).injective)

/-- A skyscraper sheaf of abelian groups is flasque. -/
instance isFlasque_skyscraperSheaf (p₀ : X) (A : AddCommGrpCat.{u})
    [(U : Opens X) → Decidable (p₀ ∈ U)] :
    TopCat.Presheaf.IsFlasque (skyscraperSheaf p₀ A).obj :=
  isFlasque_skyscraperSheaf_of_hasZeroObject p₀ A

end

end Topology

end TauCeti

namespace TopCat.Presheaf.IsFlasque

/-- A zero presheaf is flasque: each of its restriction maps lands in a zero object. -/
theorem of_isZero {C : Type*} [Category* C] [HasZeroObject C] {X : TopCat.{u}}
    {F : Presheaf C X} (h : IsZero F) : IsFlasque F :=
  ⟨fun _ ↦ (h.obj _).epi _⟩

end TopCat.Presheaf.IsFlasque

namespace TopCat.Sheaf.IsFlasque

variable {X : TopCat.{u}}
  {E : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}

/-- If `0 ⟶ A ⟶ B ⟶ C` is an exact sequence of sheaves of abelian groups with `A` and `B` flasque,
then every section of the cokernel of `B ⟶ C` lifts to a section of `C`. -/
theorem epi_cokernel_π_app (hE : E.Exact) [Mono E.f] [Presheaf.IsFlasque E.X₁.obj]
    [Presheaf.IsFlasque E.X₂.obj] (U : Opens X) : Epi ((cokernel.π E.g).hom.app (op U)) :=
  have := of_shortExact_of_isFlasque₁₂ hE.shortExact_factorThruImage
  epi_of_shortExact (ShortComplex.shortExact_image_ι_cokernel_π E.g)

/-- If `0 ⟶ A ⟶ B ⟶ C` is an exact sequence of sheaves of abelian groups with `A` flasque, then a
section of `C` maps to zero in the cokernel of `B ⟶ C` exactly when it comes from a section of
`B`. -/
theorem exact_cokernel_π_app (hE : E.Exact) [Mono E.f] [Presheaf.IsFlasque E.X₁.obj]
    (U : Opens X) :
    (ShortComplex.mk (E.g.hom.app (op U)) ((cokernel.π E.g).hom.app (op U)) (by
      simp [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom])).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro c hc
  -- `c` is a section of the image sheaf, since sections preserve kernels
  have h₂ := (ShortComplex.shortExact_image_ι_cokernel_π E.g).exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)) inferInstance inferInstance
  obtain ⟨i, rfl⟩ := (ShortComplex.ab_exact_iff _).1 h₂ c hc
  -- and sections of the image lift to `B`, because the kernel `A` is flasque
  obtain ⟨b, rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).1
    (epi_of_shortExact hE.shortExact_factorThruImage (U := U)) i
  exact ⟨b, by simp [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom]⟩

end TopCat.Sheaf.IsFlasque
end
end GeometryLiteralSource028

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Topology.Sheaves.Flasque.Basic"

