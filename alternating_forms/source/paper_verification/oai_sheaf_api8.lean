module

public import Mathlib.Topology.Sheaves.Abelian
import all Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Skyscraper
import all Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import all Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import all Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Tactic.Common
import all Mathlib.Tactic.Common
public import Mathlib.Topology.Sheaves.Functors
import all Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import all Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Zero
import all Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import all Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.LocallyInjective
import all Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import all Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Topology.Sheaves.LocallySurjective
import all Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import all Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.Stalks
import all Mathlib.Topology.Sheaves.Stalks
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let opts ← getOptions
  if env.header.trustLevel != 0 then
    throwError "Header-cache environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "Header-cache environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "Header-cache environment unexpectedly uses server mode"
  logInfo "HEADER_CACHE_CHECKING_OPTIONS_VERIFIED"

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.SheafCohomology.Vanishing -/

/-! # Vanishing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat

open _root_.TopCat

/-!
# Native site sheaves for the ProjectiveCohomology vanishing development

These abbreviations use the same category of site sheaves as ProjectiveCohomology's cohomology.
They avoid the extra category wrapper on `TopCat.Sheaf` in the current library.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe w v u

abbrev Sheaf (C : Type u) [Category.{v} C] (X : _root_.TopCat.{w}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) C

namespace Sheaf
open _root_.TopCat.Sheaf

variable (C : Type u) [Category.{v} C] {X Y : _root_.TopCat.{w}}

abbrev forget (X : _root_.TopCat.{w}) :=
  sheafToPresheaf (Opens.grothendieckTopology X) C

abbrev pushforward (f : X ⟶ Y) : Projective.TopCat.Sheaf C X ⥤ Projective.TopCat.Sheaf C Y :=
  (Opens.map f).sheafPushforwardContinuous C _ _

noncomputable def isTerminalOfEmpty (F : Projective.TopCat.Sheaf C X) : IsTerminal (F.obj.obj (.op ⊥)) :=
  F.isTerminalOfBotCover ⊥ (fun _ h => h.elim)

variable (A : Type*) [Category.{w} A] {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
variable [HasColimits A] [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

noncomputable abbrev pullback (f : X ⟶ Y) : Projective.TopCat.Sheaf A Y ⥤ Projective.TopCat.Sheaf A X :=
  (Opens.map f).sheafPullback A _ _

noncomputable def pullbackIso (f : X ⟶ Y) :
    Projective.TopCat.Sheaf.pullback A f ≅ Projective.TopCat.Sheaf.forget A Y ⋙ _root_.TopCat.Presheaf.pullback A f ⋙
      presheafToSheaf _ _ :=
  Functor.sheafPullbackConstruction.sheafPullbackIso _ _ _ _

noncomputable abbrev pullbackPushforwardAdjunction (f : X ⟶ Y) :
    Projective.TopCat.Sheaf.pullback A f ⊣ pushforward A f :=
  (Opens.map f).sheafAdjunctionContinuous A _ _

instance (f : X ⟶ Y) : (Projective.TopCat.Sheaf.pullback A f).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction A f).isLeftAdjoint

instance (f : X ⟶ Y) : (pushforward A f).IsRightAdjoint :=
  (pullbackPushforwardAdjunction A f).isRightAdjoint

end Sheaf

end OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.SheafCohomology.Vanishing"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.SheafCohomology.ClosedImmersion -/

/-! # Closed Immersion -/

namespace OAI.AlgebraicGeometry.SheafCohomology.ClosedImmersion

noncomputable section

open _root_.TopCat

open _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open _root_.CategoryTheory.Limits _root_.Opposite

set_option backward.isDefEq.respectTransparency false

namespace ProjectiveVanishing

open OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat

/-!
# Closed immersions

This module packages the `TopCat` API for the closed inclusion `closedIncl: TopCat.of s ⟶ X`
and the stalk comparisons needed in the closed-immersion step of Grothendieck vanishing.

Main results:
- `closedIncl_isClosedEmbedding` and `closedIncl_isInducing` record the basic topology of
 the closed inclusion.
- `closedIncl_map_eq_bot_of_le_compl` shows that opens contained in the complement pull back
 to `⊥` on the closed subspace.
- `pushforward_closedIncl_stalk_eq_zero` identifies stalks of a closed-immersion
 pushforward away from the closed subset with zero.
- `closedIncl_pushforward_preservesEpis/Monos` and
 `closedIncl_pushforward_shortExact` package exactness of pushforward along the
 closed inclusion for `AddCommGrpCat`-valued sheaves.
- `stalkFunctor_map_iso_toSheafify` identifies the stalk of sheafification with an isomorphism.
- `closedIncl_counit_isIso` identifies the pushforward-pullback counit for
 presheaves on the closed subspace carrying a sheaf condition.
- `stalkPullbackHom_naturality` is the stalk-level naturality needed to compare the unit with
 the counit isomorphism.
- `closedIncl_unit_stalk_isIso` shows that the adjunction unit is an isomorphism on stalks at
 points of the closed subset.
- `epi_unit_of_closedImmersion` upgrades the adjunction unit to an epi of sheaves.
- `closedImmersionSES` and `closedImmersionSES_shortExact` package the short exact sequence
 `0 → ker(η) → F → i_*(i^*F) → 0` associated to a closed immersion.
-/

open Limits

universe u

instance sheafAbelianAddCommGrp (X : TopCat.{u}) :
    Abelian (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

namespace TopCat

/-- Closed inclusion `s ↪ X` as a morphism in `TopCat`. -/
def closedIncl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) : TopCat.of s ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, hs.isClosedEmbedding_subtypeVal.continuous⟩

lemma set_range_closedIncl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    Set.range (ProjectiveVanishing.TopCat.closedIncl hs : s → X) = s := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

lemma closedIncl_isClosedEmbedding {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    Topology.IsClosedEmbedding (ProjectiveVanishing.TopCat.closedIncl hs) :=
  hs.isClosedEmbedding_subtypeVal

lemma closedIncl_isInducing {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    Topology.IsInducing (ProjectiveVanishing.TopCat.closedIncl hs) :=
  (closedIncl_isClosedEmbedding hs).isInducing

theorem closedIncl_map_eq_bot_of_le_compl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {U : Opens X} (hU : U ≤ ⟨sᶜ, hs.isOpen_compl⟩) :
    (Opens.map (ProjectiveVanishing.TopCat.closedIncl hs)).obj U = ⊥ := by
  apply Opens.ext
  change (ProjectiveVanishing.TopCat.closedIncl hs : s → X) ⁻¹' (U : Set X) = (⊥ : Opens (TopCat.of s))
  have hdisj : Disjoint (U : Set X) (Set.range (ProjectiveVanishing.TopCat.closedIncl hs : s → X)) := by
    rw [set_range_closedIncl hs]
    exact Set.disjoint_left.mpr fun x hxU hxS ↦ hU hxU hxS
  simpa using (Set.preimage_eq_empty hdisj)

instance closedIncl_stalkPushforward_isIso {X : TopCat.{u}} {s : Set X} {hs : IsClosed s}
    {C : Type*} [Category.{u} C] [HasColimits C]
    {F : (TopCat.of s).Presheaf C} {x : TopCat.of s} :
    IsIso (Presheaf.stalkPushforward C (ProjectiveVanishing.TopCat.closedIncl hs) F x) :=
  Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    C (closedIncl_isInducing hs) F x

lemma opensMap_range_isBasis_of_isInducing {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsInducing f) :
    Opens.IsBasis (Set.range (Opens.map f).obj) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  refine ⟨U, ?_, hx, le_rfl⟩
  refine ⟨hf.functorObj U, ?_⟩
  simpa using hf.map_functorObj U

lemma opensMap_isCoverDense_of_isInducing {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsInducing f) :
    (Opens.map f).IsCoverDense (Opens.grothendieckTopology X) := by
  rw [TopCat.Opens.coverDense_iff_isBasis]
  exact opensMap_range_isBasis_of_isInducing hf

instance opensMap_isLocallyFull {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (Opens.map f).IsLocallyFull (Opens.grothendieckTopology X) where
  functorPushforward_imageSieve_mem := by
    intro U V i
    rw [Opens.grothendieckTopology]
    intro x hx
    refine ⟨(Opens.map f).obj (U ⊓ V), (Opens.map f).map (Opens.infLELeft U V), ?_, ?_⟩
    · refine ⟨U ⊓ V, Opens.infLELeft U V, 𝟙 _, ?_, by simp⟩
      refine ⟨Opens.infLERight U V, ?_⟩
      exact Subsingleton.elim _ _
    · exact ⟨hx, i.le hx⟩

theorem locallyInjective_stalkFunctor_map_injective
    {C : Type*} [Category.{u} C] [HasColimits C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesFilteredColimits (forget C)]
    {X : TopCat.{u}} {F G : X.Presheaf C} (T : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) T] :
    ∀ x : X, Function.Injective ((TopCat.Presheaf.stalkFunctor C x).map T) := by
  intro x s t hst
  obtain ⟨U, hxU, sU, rfl⟩ := F.exists_germ_eq s
  obtain ⟨V, hxV, sV, hsV⟩ := F.exists_germ_eq t
  rw [← hsV] at hst ⊢
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iWU, iWV, hEq⟩ := G.germ_eq x hxU hxV _ _ hst
  have hnat (Y : Opens X) (iWY : W ⟶ Y) (sY : CC (F.obj (op Y))) :
      T.app (op W) (F.map iWY.op sY) = G.map iWY.op (T.app (op Y) sY) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, T.naturality]
  have hEq' : T.app (op W) (F.map iWU.op sU) =
      T.app (op W) (F.map iWV.op sV) := by rw [hnat _ iWU, hnat _ iWV]; exact hEq
  have hloc := CategoryTheory.Presheaf.equalizerSieve_mem
    (J := Opens.grothendieckTopology X) (φ := T)
    (x := F.map iWU.op sU) (y := F.map iWV.op sV) hEq'
  rw [Opens.grothendieckTopology] at hloc
  rcases hloc x hxW with ⟨Z, iZW, hEqZ, hxZ⟩
  apply F.germ_ext Z hxZ (iZW ≫ iWU) (iZW ≫ iWV)
  simpa using hEqZ

theorem stalkFunctor_map_iso_toSheafify
    {C : Type*} [Category.{u} C] [HasColimits C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} [HasWeakSheafify (Opens.grothendieckTopology X) C]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective C]
    (P : X.Presheaf C) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor C x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · exact locallyInjective_stalkFunctor_map_injective
      (T := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) x
  · have hls : TopCat.Presheaf.IsLocallySurjective
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) := by
        dsimp [TopCat.Presheaf.IsLocallySurjective]; infer_instance
    exact
      ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
        (T := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)).mp hls) x

theorem closedIncl_counit_isIso
    {C : Type*} [Category.{u} C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (forget C)]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (F : Vanishing.Projective.TopCat.Sheaf C (TopCat.of s)) :
    IsIso ((Vanishing.Projective.TopCat.Sheaf.pullbackPushforwardAdjunction C (ProjectiveVanishing.TopCat.closedIncl hs)).counit.app
      F) := by
  let : (Opens.map (ProjectiveVanishing.TopCat.closedIncl hs)).IsCoverDense
      (Opens.grothendieckTopology (TopCat.of s)) :=
    opensMap_isCoverDense_of_isInducing (closedIncl_isInducing hs)
  let : (Opens.map (ProjectiveVanishing.TopCat.closedIncl hs)).IsLocallyFull
      (Opens.grothendieckTopology (TopCat.of s)) :=
    opensMap_isLocallyFull (ProjectiveVanishing.TopCat.closedIncl hs)
  let : (Opens.map (ProjectiveVanishing.TopCat.closedIncl hs)).IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of s)) :=
    CategoryTheory.Functor.IsCoverDense.isContinuous
      (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology (TopCat.of s))
      (G := Opens.map (ProjectiveVanishing.TopCat.closedIncl hs))
      (coverPreserving_opens_map (ProjectiveVanishing.TopCat.closedIncl hs))
  have : (Vanishing.Projective.TopCat.Sheaf.pushforward C (ProjectiveVanishing.TopCat.closedIncl hs)).Full := by
    simpa [Vanishing.Projective.TopCat.Sheaf.pushforward] using
      (CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous
        (J := Opens.grothendieckTopology X)
        (K := Opens.grothendieckTopology (TopCat.of s))
        (G := Opens.map (ProjectiveVanishing.TopCat.closedIncl hs)) :
          ((Opens.map (ProjectiveVanishing.TopCat.closedIncl hs)).sheafPushforwardContinuous
            C (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology (TopCat.of s))).Full)
  have : (Vanishing.Projective.TopCat.Sheaf.pushforward C (ProjectiveVanishing.TopCat.closedIncl hs)).Faithful := by
    simpa [Vanishing.Projective.TopCat.Sheaf.pushforward] using
      (CategoryTheory.Functor.IsCoverDense.faithful_sheafPushforwardContinuous
        (J := Opens.grothendieckTopology X)
        (K := Opens.grothendieckTopology (TopCat.of s))
        (G := Opens.map (ProjectiveVanishing.TopCat.closedIncl hs)) :
          ((Opens.map (ProjectiveVanishing.TopCat.closedIncl hs)).sheafPushforwardContinuous
            C (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology (TopCat.of s))).Faithful)
  infer_instance

end TopCat

/-- Stalks of a pushforward along a closed inclusion vanish outside the closed set:
 if `x ∉ s`, every element of `stalk(i_*(G), x)` is zero. -/
theorem pushforward_closedIncl_stalk_eq_zero
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of s)} (hG : G.IsSheaf)
    {x : X} (hx : x ∉ s)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (ProjectiveVanishing.TopCat.closedIncl hs)).obj G)) :
    a = 0 := by
  let Gsh : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s) := ⟨G, hG⟩
  let F' := (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (ProjectiveVanishing.TopCat.closedIncl hs)).obj G
  obtain ⟨U, hxU, sU, rfl⟩ := F'.exists_germ_eq a
  let W : Opens X := U ⊓ ⟨sᶜ, hs.isOpen_compl⟩
  have hW_map : (Opens.map (ProjectiveVanishing.TopCat.closedIncl hs)).obj W = ⊥ := by
    exact ProjectiveVanishing.TopCat.closedIncl_map_eq_bot_of_le_compl (hs := hs) (U := W) inf_le_right
  have : Subsingleton (F'.obj (op W)) := AddCommGrpCat.subsingleton_of_isZero (by
    change IsZero (G.obj (op ((Opens.map (ProjectiveVanishing.TopCat.closedIncl hs)).obj W)))
    rw [hW_map]
    exact (Vanishing.Projective.TopCat.Sheaf.isTerminalOfEmpty _ Gsh).isZero)
  rw [← TopCat.Presheaf.germ_res_apply F'
    (homOfLE (show W ≤ U from inf_le_left)) x ⟨hxU, hx⟩ sU]
  simp [Subsingleton.eq_zero (ConcreteCategory.hom (F'.map (homOfLE (show W ≤ U from
    inf_le_left)).op) sU)]

/-- Pushforward along a closed immersion preserves epis: if `f: F ⟶ G` is epi in
 presheaves on the closed subspace, then `i_*(f)` is epi in sheaves on the ambient
 space whenever `f` is locally surjective.
 Proof: stalkwise surjectivity (identity on the closed set, zero outside). -/
theorem epi_pushforward_map_closedIncl_of_locallySurjective
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {F G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of s)}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : F ⟶ G)
    (hf_loc : TopCat.Presheaf.IsLocallySurjective f) :
    Epi ((Vanishing.Projective.TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (ProjectiveVanishing.TopCat.closedIncl hs)).map (show
        (⟨F, hF⟩ : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) ⟶
          (⟨G, hG⟩ : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) from
            ObjectProperty.homMk f)) := by
  let fsh : (⟨F, hF⟩ : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) ⟶
      (⟨G, hG⟩ : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) := ObjectProperty.homMk f
  let : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    balanced_of_strongEpiCategory
  change Epi ((Vanishing.Projective.TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (ProjectiveVanishing.TopCat.closedIncl hs)).map fsh)
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
    ((Vanishing.Projective.TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (ProjectiveVanishing.TopCat.closedIncl hs)).map fsh)]
  change TopCat.Presheaf.IsLocallySurjective
    ((Vanishing.Projective.TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (ProjectiveVanishing.TopCat.closedIncl hs)).map fsh).hom
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x; by_cases hx : (x : X) ∈ s
  · let z : TopCat.of s := ⟨x, hx⟩
    have : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr
        (((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
            (T := f)).mp hf_loc) z)
    have hnat : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((ProjectiveVanishing.TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (ProjectiveVanishing.TopCat.closedIncl hs)).map f) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (ProjectiveVanishing.TopCat.closedIncl hs) G z =
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (ProjectiveVanishing.TopCat.closedIncl hs) F z ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f := by
      apply TopCat.Presheaf.stalk_hom_ext; intro U hU
      rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
        TopCat.Presheaf.stalkPushforward_germ,
        TopCat.Presheaf.stalkPushforward_germ_assoc,
        TopCat.Presheaf.stalkFunctor_map_germ]
      rfl
    apply (AddCommGrpCat.epi_iff_surjective _).mp
    change Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((ProjectiveVanishing.TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (ProjectiveVanishing.TopCat.closedIncl hs)).map f))
    rw [← epi_comp_iff_of_isIso _ (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (ProjectiveVanishing.TopCat.closedIncl hs) G z), hnat]
    exact epi_comp _ _
  · intro b
    rw [pushforward_closedIncl_stalk_eq_zero (hs := hs) (G := G) hG hx b]
    exact ⟨0, AddMonoidHom.map_zero _⟩

instance closedIncl_pushforward_preservesEpis
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    (Vanishing.Projective.TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (ProjectiveVanishing.TopCat.closedIncl hs)).PreservesEpimorphisms where
  preserves {F G} f hf := by
    let : Epi f := hf
    let : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
      balanced_of_strongEpiCategory
    have hf_loc : TopCat.Presheaf.IsLocallySurjective f.hom := by
      exact
        (show Sheaf.IsLocallySurjective f from
          (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} f).mpr inferInstance)
    exact epi_pushforward_map_closedIncl_of_locallySurjective
      (hs := hs) (F := F.obj) (G := G.obj) F.property G.property f.hom hf_loc

instance closedIncl_pushforward_preservesMonos
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    (Vanishing.Projective.TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (ProjectiveVanishing.TopCat.closedIncl hs)).PreservesMonomorphisms := inferInstance

/-- Pushforward along a closed immersion preserves short exact sequences. -/
theorem closedIncl_pushforward_shortExact
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s))}
    (hSE : S.ShortExact) :
    (S.map (Vanishing.Projective.TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (ProjectiveVanishing.TopCat.closedIncl hs))).ShortExact := by
  let F := Vanishing.Projective.TopCat.Sheaf.pushforward AddCommGrpCat.{u} (ProjectiveVanishing.TopCat.closedIncl hs)
  have := hSE.mono_f
  have := hSE.epi_g
  have : Mono (F.map S.f) := inferInstance
  have : Epi (F.map S.g) := inferInstance
  exact ShortComplex.ShortExact.mk'
    (hSE.exact.map_of_mono_of_preservesKernel _ hSE.mono_f inferInstance) ‹_› ‹_›

namespace TopCat

-- Stalk pullback hom naturality
lemma stalkPullbackHom_naturality
    {C : Type*} [Category C] [HasColimits C]
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F G : Y.Presheaf C} (α : F ⟶ G) (x : ↑X) :
    (Presheaf.stalkFunctor C (ConcreteCategory.hom f x)).map α ≫
      Presheaf.stalkPullbackHom C f G x =
    Presheaf.stalkPullbackHom C f F x ≫
      (Presheaf.stalkFunctor C x).map
        ((Presheaf.pullback C f).map α) := by
  apply Presheaf.stalk_hom_ext; intro U hU
  simp only [Presheaf.stalkFunctor_map_germ_assoc, Presheaf.germ_stalkPullbackHom,
    Presheaf.germ_stalkPullbackHom_assoc, Presheaf.stalkFunctor_map_germ]
  have key : α.app (Opposite.op U) ≫
      ((Presheaf.pullbackPushforwardAdjunction C f).unit.app G).app (Opposite.op U) =
    ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F).app (Opposite.op U) ≫
      ((Presheaf.pullback C f).map α).app
        (Opposite.op ((TopologicalSpace.Opens.map f).obj U)) := by
    have h := congr_arg (fun β ↦ NatTrans.app β (Opposite.op U))
      ((Presheaf.pullbackPushforwardAdjunction C f).unit.naturality α)
    exact h
  rw [← CategoryTheory.Category.assoc, key, CategoryTheory.Category.assoc]

-- Unit stalk is iso for closed immersions.
-- Proof chain: triangle identity → pullback.map(η) iso → pullbackIso naturality
-- → toSheafify naturality → stalkPullbackHom_naturality → η stalk iso
theorem closedIncl_unit_stalk_isIso
    {C : Type*} [Category.{u} C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (forget C)]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (F : Vanishing.Projective.TopCat.Sheaf C X) (x : TopCat.of s) :
    IsIso ((Presheaf.stalkFunctor C ((ProjectiveVanishing.TopCat.closedIncl hs) x)).map
      ((Vanishing.Projective.TopCat.Sheaf.pullbackPushforwardAdjunction C (ProjectiveVanishing.TopCat.closedIncl hs)).unit.app
        F).hom) := by
  -- Use the triangle identity + counit iso
  let i := ProjectiveVanishing.TopCat.closedIncl hs
  let adj := Vanishing.Projective.TopCat.Sheaf.pullbackPushforwardAdjunction C i
  let pb := Vanishing.Projective.TopCat.Sheaf.pullback C i
  let η := adj.unit.app F
  have : IsIso (adj.counit.app (pb.obj F)) :=
    closedIncl_counit_isIso (C := C) (hs := hs) (pb.obj F)
  have : IsIso (𝟙 (pb.obj F)) := inferInstance
  have : IsIso (pb.map η) := IsIso.of_isIso_fac_right (adj.left_triangle_components F)
  -- Step 2: val stalk of pb.map(η) is iso
  have : IsIso (pb.map η).hom :=
    inferInstanceAs (IsIso (sheafToPresheaf _ _ |>.map (pb.map η)))
  let Tz := Presheaf.stalkFunctor C x
  let K := Opens.grothendieckTopology (TopCat.of s)
  let pull := Presheaf.pullback C i
  -- Step 3: pullbackIso naturality
  let pi := Vanishing.Projective.TopCat.Sheaf.pullbackIso C i
  let piF := pi.hom.app F
  let piT := pi.hom.app ((pb ⋙ Vanishing.Projective.TopCat.Sheaf.pushforward C i).obj F)
  have : IsIso piF.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map piF))
  have : IsIso piT.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map piT))
  have hnat : (pb.map η).hom ≫ piT.hom = piF.hom ≫ sheafifyMap K (pull.map η.hom) :=
    congr_arg InducedCategory.Hom.hom (pi.hom.naturality η)
  have hnat_stalk := by simpa only [Functor.map_comp] using congr_arg Tz.map hnat
  -- Step 4: presheafToSheaf.map(pull.map(η.hom)).hom stalk is iso
  have : IsIso (Tz.map (sheafifyMap K (pull.map η.hom))) :=
    IsIso.of_isIso_fac_left hnat_stalk.symm
  -- Step 5: toSheafify naturality → pull.map(η.hom) stalk is iso
  let P₁ := pull.obj F.obj
  let P₂ := pull.obj ((pb ⋙ Vanishing.Projective.TopCat.Sheaf.pushforward C i).obj F).obj
  have hts : Tz.map (pull.map η.hom) ≫ Tz.map (CategoryTheory.toSheafify K P₂) =
      Tz.map (CategoryTheory.toSheafify K P₁) ≫ Tz.map (sheafifyMap K (pull.map η.hom)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congr_arg Tz.map (CategoryTheory.toSheafify_naturality K (pull.map η.hom))
  have (P : (TopCat.of s).Presheaf C) : IsIso (Tz.map (toSheafify K P)) := stalkFunctor_map_iso_toSheafify P x
  have : IsIso (Tz.map (pull.map η.hom)) :=
    IsIso.of_isIso_fac_right hts
  -- Step 6: stalkPull_nat → η.hom stalk is iso
  have (G : Vanishing.Projective.TopCat.Sheaf C X) : IsIso (Presheaf.stalkPullbackHom C i G.obj x) :=
    (Presheaf.stalkPullbackIso C i G.obj x).isIso_hom
  exact IsIso.of_isIso_fac_right (stalkPullbackHom_naturality i η.hom x)

end TopCat

-- The adjunction unit `F → i_*(i^*F)` is epi for closed immersions.
theorem epi_unit_of_closedImmersion
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) :
    Epi ((Vanishing.Projective.TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (ProjectiveVanishing.TopCat.closedIncl hZ)).unit.app F) := by
  let closedIncl := ProjectiveVanishing.TopCat.closedIncl hZ
  let adj := Vanishing.Projective.TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} closedIncl
  let : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    balanced_of_strongEpiCategory
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} (adj.unit.app F),
    show Sheaf.IsLocallySurjective (adj.unit.app F) =
      TopCat.Presheaf.IsLocallySurjective (adj.unit.app F).hom from rfl,
    TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x
  by_cases hxZ : (x : X) ∈ Z
  · have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((ProjectiveVanishing.TopCat.closedIncl hZ) ⟨x, hxZ⟩)).map (adj.unit.app F).hom) := by
      simpa using
        (ProjectiveVanishing.TopCat.closedIncl_unit_stalk_isIso (C := AddCommGrpCat.{u})
          (hs := hZ) F ⟨x, hxZ⟩)
    exact (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((ProjectiveVanishing.TopCat.closedIncl hZ) ⟨x, hxZ⟩)).map
        ((Vanishing.Projective.TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (ProjectiveVanishing.TopCat.closedIncl hZ)).unit.app F).hom)).2
  · exact fun b ↦ ⟨0, by
      rw [pushforward_closedIncl_stalk_eq_zero
        (hs := hZ)
        (G := ((Vanishing.Projective.TopCat.Sheaf.pullback AddCommGrpCat.{u} closedIncl).obj F).obj)
        (((Vanishing.Projective.TopCat.Sheaf.pullback AddCommGrpCat.{u} closedIncl).obj F).property)
        hxZ b]
      exact map_zero _⟩

/-- The short exact sequence `0 → ker(η) → F → i_*(i^*F) → 0` from a closed immersion,
 where `η` is the pullback-pushforward adjunction unit and `i: Z ↪ X` is the
 inclusion of a closed subset. -/
noncomputable def closedImmersionSES
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let closedIncl := ProjectiveVanishing.TopCat.closedIncl hZ
  let η := (Vanishing.Projective.TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} closedIncl).unit.app F
  ShortComplex.mk (kernel.ι η) η (kernel.condition η)

theorem closedImmersionSES_shortExact
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) :
    (closedImmersionSES (Z := Z) (hZ := hZ) F).ShortExact := by
  unfold closedImmersionSES
  have := epi_unit_of_closedImmersion (Z := Z) (hZ := hZ) F
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance
end ProjectiveVanishing

end

end OAI.AlgebraicGeometry.SheafCohomology.ClosedImmersion
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.SheafCohomology.ClosedImmersion"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.SheafCohomology.API -/

/-! # API -/

namespace OAI.AlgebraicGeometry.SheafCohomology.API

open _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open _root_.CategoryTheory.Limits _root_.Opposite

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace ProjectiveVanishing

open OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat

/-!
# Sheaf Cohomology API

Centralizes results about sheaf cohomology `Sheaf.H`, keeping the underlying `Ext`
calculations internal so downstream files never need to unfold `Sheaf.H` directly.

## Main results

* `subsingleton_sheafH_of_shortExact_middle`: middle-term cohomology vanishing
* `sheafH_subsingleton_of_isEmpty`: empty-space vanishing
* `sheaf_isZero_of_zero_stalks`: zero stalks imply zero sheaf
* `sheafH_subsingleton_of_isZero`: bundled zero-sheaf vanishing
* `stalk_zero_of_ses_g_iso`: stalk vanishing from SES with iso on `g`
* `stalk_zero_of_shortExact_kernel`: stalk vanishing from SES kernel
* `stalk_zero_of_g_is_cokernel_of_stalk_epi`: sheaf-level stalk
 vanishing from a cokernel and stalk-epi hypothesis
* `cokernel_stalk_zero_of_stalk_surj`: actual-cokernel specialization of the same stalk
 vanishing under stalk-surjectivity
* `sheafH_succ_map`: successor connecting morphism
* `sheafH_succ_map_exists_preimage_of_subsingleton_middle`: successor-map
 preimage wrapper
* `sheafH0EquivSections`: sheaf-level wrapper for `H^0(F) ≃+ F(⊤)`
* `sheafH0EquivSections_natural`: sheaf-level naturality of the above
* `sheafH1_cokernel_iso_of_subsingleton_middle`: sheaf-level form of the
 `H¹` cokernel identification
* `sheafH1_cokernel_iso_of_subsingleton_middle_natural`: sheaf-level
 naturality for the same `H¹` cokernel identification
* `sheafH_succ_iso_of_subsingleton_middle`: sheaf-level form of the
 higher-degree connecting isomorphism
* `sheafH_succ_iso_of_subsingleton_middle_natural`: sheaf-level
 naturality for the same connecting isomorphism
* `sheafH0_surj_of_epi_app_top`: sheaf-level surjectivity on top sections
 gives H^0 surjectivity
* `sheafH_subsingleton_H1_via_surj`: sheaf-level H^1 vanishing via
 H^0-surjectivity
* `sheafH_subsingleton_H1_via_epi_app_top`: sheaf-level H^1 vanishing via
 surjective top sections
* `sheafH_subsingleton_of_injective`: positive-degree cohomology of an injective sheaf
 is subsingleton
* `sheafH_subsingleton_H1_of_injective_of_epi_app_top`: sheaf-level
 injective-middle-term `H¹` vanishing
* `sheafH_dimension_shift_of_both`: sheaf-level forward dimension shift
 for short exact sequences
* `sheafH_dimension_shift_of_mono`: forward dimension shift for a monomorphism
* `sheafH_dimension_shift_of_injective`: forward dimension shift with injective middle term
* `sheafH_dimension_shift_X₃_of_locallySurjective`: reverse dimension shift for locally
 surjective morphisms
-/

universe w' w v u

open Abelian Limits

instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift ℤ)
    intro A B f g h
    simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq',
      ULift.forall]
    intro x
    specialize h (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y ↦ y • x) fun y z ↦ by simp only [add_smul])) 1
    aesop

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

instance {C : Type*} [Category C] {D : Type*} [Category D] [Preadditive D] :
    (Functor.const Cᵒᵖ : D ⥤ Cᵒᵖ ⥤ D).Additive where

instance {C : Type*} [Category C] [Preadditive C] {X : TopCat.{u}} :
    Preadditive (TopCat.Presheaf C X) := by
  delta TopCat.Presheaf
  infer_instance

instance {X : TopCat.{u}} :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive :=
  inferInstanceAs ((Functor.const (Opens X)ᵒᵖ ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive)

noncomputable instance sheafHasExt (X : TopCat.{u}) :
    HasExt.{u} (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) :=
  hasExt_of_enoughInjectives _

/-- Stalks preserve monomorphisms in the native site-sheaf category. -/
instance nativeSheafStalk_preservesMonos (X : TopCat.{u}) (x : X) :
    (Vanishing.Projective.TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      _root_.TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).PreservesMonomorphisms where
  preserves {F G} f hf := by
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    apply _root_.TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective (f := f.hom)
    intro U
    apply (AddCommGrpCat.mono_iff_injective _).mp
    have hmono : Mono f.hom :=
      (Sheaf.Hom.mono_iff_presheaf_mono
        (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) f).mp hf
    exact (NatTrans.mono_iff_mono_app f.hom).mp hmono (op U)

/-! ## Internal Ext helpers -/

section ExtDimShift
variable {C' : Type*} [Category C'] [Abelian C'] [HasExt C']

/-- Dimension shift for Ext via LES: given `0 → X₁ → X₂ → X₃ → 0` short exact,
 `Ext^n(Z, X₃) = 0` and `Ext^{n+1}(Z, X₂) = 0` imply `Ext^{n+1}(Z, X₁) = 0`. -/
theorem ext_dimension_shift (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₃ : Subsingleton (Ext Z S.X₃ n))
    (h₂ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Subsingleton (Ext Z S.X₁ (n + 1)) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hS a (@Subsingleton.elim _ h₂ _ _) rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hS b (@Subsingleton.elim _ h₂ _ _) rfl
  rw [← hc, ← hd, @Subsingleton.elim _ h₃ c d]

/-- Reverse dimension shift: `Ext^n(Z, X₂) = 0` and `Ext^{n+1}(Z, X₁) = 0` imply
 `Ext^n(Z, X₃) = 0`. Uses exactness at X₃ in the covariant LES. -/
theorem ext_dimension_shift_X₃ (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂ : Subsingleton (Ext Z S.X₂ n))
    (h₁ : Subsingleton (Ext Z S.X₁ (n + 1))) :
    Subsingleton (Ext Z S.X₃ n) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₃ _ hS a rfl (@Subsingleton.elim _ h₁ _ _)
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₃ _ hS b rfl (@Subsingleton.elim _ h₁ _ _)
  rw [← hc, ← hd, @Subsingleton.elim _ h₂ c d]

/-- If the middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the
 connecting morphism `Ext^n(Z, X₃) → Ext^(n+1)(Z, X₁)` is bijective. -/
theorem extClass_postcomp_bijective_of_subsingleton_middle
    (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Ext Z S.X₂ n))
    (h₂succ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Function.Bijective (hS.extClass.postcomp Z (rfl : n + 1 = n + 1)) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hzero : (x - y).comp hS.extClass rfl = 0 := by
      change (hS.extClass.postcomp Z (rfl : n + 1 = n + 1)) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ Z hS (x - y) rfl hzero
    have hz0 : z = 0 := Subsingleton.elim _ _
    apply sub_eq_zero.mp
    rw [← hz, hz0, Ext.zero_comp]
  · intro x
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Z hS x
      (@Subsingleton.elim _ h₂succ _ _) rfl
    exact ⟨y, hy⟩

/-- The connecting morphism in the covariant long exact sequence as an additive equivalence,
 assuming the middle cohomology groups in degrees `n` and `n + 1` vanish. -/
noncomputable def extClass_postcompAddEquiv_of_subsingleton_middle
    (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Ext Z S.X₂ n))
    (h₂succ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Ext Z S.X₃ n ≃+ Ext Z S.X₁ (n + 1) :=
  AddEquiv.ofBijective (hS.extClass.postcomp Z (rfl : n + 1 = n + 1))
    (extClass_postcomp_bijective_of_subsingleton_middle Z hS n h₂n h₂succ)

/-- Naturality of the extension class: given a morphism `φ: S₁ ⟶ S₂` of short exact sequences,
 the connecting homomorphism commutes with the induced maps on Ext groups.
 Proved via the triangulated category axiom TR3 (`complete_distinguished_triangle_morphism₁`),
 fullness/faithfulness of `singleFunctor`, and mono cancellation. -/
lemma extClass_naturality {S₁ S₂ : ShortComplex C'} (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    (Ext.mk₀ φ.τ₃).comp hS₂.extClass (zero_add 1) =
    hS₁.extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1) := by
  let := HasDerivedCategory.standard C'
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShortComplex.ShortExact.extClass_hom]
  rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  have comm₂ : hS₁.singleTriangle.mor₂ ≫ (DerivedCategory.singleFunctor C' 0).map φ.τ₃ =
      (DerivedCategory.singleFunctor C' 0).map φ.τ₂ ≫ hS₂.singleTriangle.mor₂ := by
    show (DerivedCategory.singleFunctor C' 0).map S₁.g ≫
      (DerivedCategory.singleFunctor C' 0).map φ.τ₃ =
      (DerivedCategory.singleFunctor C' 0).map φ.τ₂ ≫
      (DerivedCategory.singleFunctor C' 0).map S₂.g
    simp [← Functor.map_comp, φ.comm₂₃]
  obtain ⟨a', ha₁, ha₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    hS₁.singleTriangle hS₂.singleTriangle
    hS₁.singleTriangle_distinguished hS₂.singleTriangle_distinguished
    ((DerivedCategory.singleFunctor C' 0).map φ.τ₂)
    ((DerivedCategory.singleFunctor C' 0).map φ.τ₃) comm₂
  simp only [ShortComplex.ShortExact.singleTriangle_mor₃] at ha₃
  rw [← ha₃]
  suffices a' = (DerivedCategory.singleFunctor C' 0).map φ.τ₁ by rw [this]; simp
  obtain ⟨a'', rfl⟩ := (DerivedCategory.singleFunctor C' 0).map_surjective a'
  congr 1
  have h : S₁.f ≫ φ.τ₂ = a'' ≫ S₂.f := by
    have := ha₁
    simp only [ShortComplex.ShortExact.singleTriangle_mor₁] at this
    rwa [← Functor.map_comp, ← Functor.map_comp,
      (DerivedCategory.singleFunctor C' 0).map_injective.eq_iff] at this
  have : Mono S₂.f := hS₂.mono_f
  exact (cancel_mono S₂.f).mp (by rw [← φ.comm₁₂.symm, h])

/-- Internal helper: if `Y` is zero in an abelian category, `Ext X Y n` is subsingleton
 for all `X`, `n`.
 Proof: `𝟙 Y = 0` because `Y` is zero, so `x = x ∘ mk₀(𝟙 Y) = x ∘ mk₀(0) = x ∘ 0 = 0`. -/
theorem ext_subsingleton_of_isZero_tgt {X Y : C'} (hY : IsZero Y) (n : ℕ) :
    Subsingleton (Ext X Y n) :=
  ⟨fun a b ↦ by
    have eq : ∀ x : Ext X Y n, x = 0 := fun x ↦ by
      have h := Ext.comp_mk₀_id x
      rw [show (𝟙 Y : Y ⟶ Y) = 0 from hY.eq_of_src _ _, Ext.mk₀_zero] at h
      exact h.symm.trans (Ext.comp_zero x Y 0 n (add_zero n))
    exact (eq a).trans (eq b).symm⟩

end ExtDimShift

/-! ## Stalks and zero sheaves -/

/-- Naturality of the connecting map on sheaf cohomology for a morphism of short exact
 sequences, with the associativity rewrites needed for nested `comp` expressions. -/
theorem sheafH_comp_extClass_naturality {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ)
    (y : Sheaf.H S₁.X₃ n) :
    (y.comp hS₁.extClass rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) =
      (y.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hS₂.extClass rfl := by
  have hcomp :
      y.comp (hS₁.extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1)) rfl =
        y.comp ((Ext.mk₀ φ.τ₃).comp hS₂.extClass (zero_add 1)) rfl := by
    exact congrArg (fun t ↦ y.comp t rfl) (extClass_naturality hS₁ hS₂ φ).symm
  simpa [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero] using hcomp

/-- Successor connecting morphism attached to a short exact sequence of sheaves. -/
noncomputable def sheafH_succ_map {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H S.X₃ n) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ (n + 1)) := by
  exact AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun y ↦ y.comp hS.extClass rfl)
      (by
        intro a b
        change (a + b).comp hS.extClass rfl = a.comp hS.extClass rfl + b.comp hS.extClass rfl
        rw [Ext.add_comp])

theorem sheafH_succ_map_apply {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (n : ℕ)
    (y : Sheaf.H S.X₃ n) :
    ConcreteCategory.hom (sheafH_succ_map hS n) y = y.comp hS.extClass rfl := rfl

/-- If the middle term has subsingleton cohomology in degree `n + 1`, every
`H^(n+1)(S.X₁)` class comes from some `H^n(S.X₃)` class via the successor map. -/
theorem sheafH_succ_map_exists_preimage_of_subsingleton_middle {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (n : ℕ)
    (h₂H : Subsingleton (Sheaf.H S.X₂ (n + 1)))
    (x : Sheaf.H S.X₁ (n + 1)) :
    ∃ y : Sheaf.H S.X₃ n, ConcreteCategory.hom (sheafH_succ_map hS n) y = x := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x (@Subsingleton.elim _ h₂H _ _) rfl
  refine ⟨y, ?_⟩
  rw [sheafH_succ_map_apply]
  exact hy

theorem sheaf_isZero_of_zero_stalks (X : TopCat.{u})
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    (hstalk : ∀ (x : X)
      (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F), a = 0) :
    IsZero ((⟨F, hF⟩ : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)) := by
  let Fsh : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  have hZ : IsZero F := Functor.isZero F (fun ⟨U⟩ ↦
    @AddCommGrpCat.isZero_of_subsingleton _
      ⟨fun s t ↦ by
        apply hF.section_ext
        intro x hx
        obtain ⟨W, hxW, iU, iV, hEq⟩ := F.germ_eq x hx hx s t
          ((hstalk x _).trans (hstalk x _).symm)
        rw [Subsingleton.elim iU iV] at hEq
        have hWU : W ≤ U := leOfHom iV
        rw [Subsingleton.elim iV (homOfLE hWU)] at hEq
        exact ⟨W, hWU, hxW, hEq⟩⟩)
  have hFsh : IsZero Fsh := by
    exact IsZero.mk
      (fun G ↦ ⟨{ default := 0, uniq := fun f ↦ Sheaf.hom_ext (NatTrans.ext (funext
        fun U ↦ (hZ.obj U).eq_zero_of_src (f.hom.app U))) }⟩)
      (fun G ↦ ⟨{ default := 0, uniq := fun f ↦ Sheaf.hom_ext (NatTrans.ext (funext
        fun U ↦ (hZ.obj U).eq_zero_of_tgt (f.hom.app U))) }⟩)
  simpa [Fsh] using hFsh

/-- If a bundled sheaf is zero, then its cohomology is subsingleton in every degree. -/
theorem sheafH_subsingleton_of_isZero {X : TopCat.{u}}
    {F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X} (hzero : IsZero F) (n : ℕ) :
    Subsingleton (Sheaf.H F n) :=
  ext_subsingleton_of_isZero_tgt hzero n

/-- In a short exact sequence `X₁ → X₂ → X₃`, if the stalk map of `g` at `x` is an
isomorphism, then the stalk of `X₁` at `x` vanishes. -/
theorem stalk_zero_of_ses_g_iso
    {X : TopCat.{u}}
    (S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)) (hS : S.ShortExact)
    (x : X)
    (hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.hom))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₁.obj) :
    a = 0 := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hf_mono : Mono S.f.hom := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) S.f).1 hS.mono_f
  have : Mono S.f := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) S.f).2 hf_mono
  have hTf_mono : Mono (T.map S.f.hom) := by
    exact Functor.map_mono (Vanishing.Projective.TopCat.Sheaf.forget _ _ ⋙ T) S.f
  have hf0 : T.map S.f.hom = 0 := by
    have : T.map S.f.hom ≫ T.map S.g.hom = 0 := by
      have hzero : S.f.hom ≫ S.g.hom = 0 := congrArg InducedCategory.Hom.hom S.zero
      rw [← T.map_comp, hzero, Functor.map_zero]
    rw [show T.map S.f.hom = (T.map S.f.hom ≫ T.map S.g.hom) ≫ inv (T.map S.g.hom) by simp,
      this, zero_comp]
  exact (AddCommGrpCat.mono_iff_injective _).mp hTf_mono
    (show ConcreteCategory.hom (T.map S.f.hom) a = ConcreteCategory.hom (T.map S.f.hom) 0 by
      simp [hf0])

/-- In a short exact sequence `X₁ → X₂ → X₃`, if all stalks of `X₂` at `x` vanish, then
 all stalks of `X₁` at `x` vanish (by mono-injectivity of `f`). -/
theorem stalk_zero_of_shortExact_kernel
    {X : TopCat.{u}}
    (S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)) (hS : S.ShortExact)
    (x : X)
    (hX₂ : ∀ (b : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₂.obj), b = 0)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₁.obj) :
    a = 0 := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hf_mono : Mono S.f.hom := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) S.f).1 hS.mono_f
  have : Mono S.f := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) S.f).2 hf_mono
  have hTf_mono : Mono (T.map S.f.hom) := by
    exact Functor.map_mono (Vanishing.Projective.TopCat.Sheaf.forget _ _ ⋙ T) S.f
  exact (AddCommGrpCat.mono_iff_injective _).mp hTf_mono
    ((hX₂ _).trans (map_zero _).symm)

/-- If `g` is a cokernel of `f` and the stalk map of `f` at `x` is epi, then the stalk
of `S.X₃` at `x` vanishes. -/
theorem stalk_zero_of_g_is_cokernel_of_stalk_epi
    {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hg : IsColimit (CokernelCofork.ofπ S.g S.zero))
    (x : X)
    (hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.hom))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₃.obj) :
    a = 0 := by
  let T : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    Vanishing.Projective.TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : ∀ U : Opens X, Decidable (x ∈ U) := fun _ ↦ Classical.dec _
  have : T.IsLeftAdjoint :=
    (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) (X := X) (p₀ := x)).isLeftAdjoint
  have : Epi (T.map S.f) := by
    simpa [T] using hepi
  have hzero_map : T.map S.f ≫ T.map S.g = 0 := by
    rw [← T.map_comp, S.zero, Functor.map_zero]
  have hcolim : IsColimit (CokernelCofork.ofπ (T.map S.g) hzero_map) := by
    exact CokernelCofork.mapIsColimit _ hg T
  have hzero : IsZero (T.obj S.X₃) := CokernelCofork.IsColimit.isZero_of_epi hcolim
  have := AddCommGrpCat.subsingleton_of_isZero hzero
  change T.obj S.X₃ at a
  change (a : T.obj S.X₃) = 0
  exact Subsingleton.elim _ _

/-- Actual-cokernel specialization of
`stalk_zero_of_g_is_cokernel_of_stalk_epi`: if the stalk map of `f` at `x`
is surjective, then the stalk of `cokernel f` at `x` vanishes. -/
theorem cokernel_stalk_zero_of_stalk_surj
    {X : TopCat.{u}}
    {F G : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (x : X)
    (hf : Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom)))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (Limits.cokernel f).obj) :
    a = 0 := by
  let S := ShortComplex.mk f (Limits.cokernel.π f) (Limits.cokernel.condition f)
  have hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) := by
    simpa using (AddCommGrpCat.epi_iff_surjective _).mpr hf
  simpa [S] using stalk_zero_of_g_is_cokernel_of_stalk_epi
    (S := S)
    (by simpa [S] using (cokernelIsCokernel f))
    x hepi a

/-! ## H⁰ ≅ Sections -/

/-- If `F` is a sheaf, then `H F 0` is equivalent to sections on `⊤`. -/
noncomputable def sheafH0EquivSections {X : TopCat.{u}}
    (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) :
    Sheaf.H F 0 ≃+ F.obj.obj (op ⊤) :=
  Ext.addEquiv₀.trans
    (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat
        Limits.isTerminalTop).homAddEquiv _ F).trans
      ((@AddCommGrpCat.homAddEquiv (AddCommGrpCat.of (ULift ℤ)) (F.obj.obj (op ⊤))).trans
        (AddEquiv.mk' (uliftZMultiplesHom (F.obj.obj (op ⊤))) (by
          intro x y
          ext
          simp_all only [uliftZMultiplesHom_apply_apply, smul_add, AddMonoidHom.add_apply])).symm))

/-- Naturality of `sheafH0EquivSections`: composing `x` with `mk₀ f` at
 degree 0 corresponds to applying `f.app(⊤)` on sections. -/
lemma sheafH0EquivSections_natural {X : TopCat.{u}}
    {F G : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (x : Sheaf.H F 0) :
    sheafH0EquivSections G (x.comp (Ext.mk₀ f) (add_zero 0)) =
    ConcreteCategory.hom (f.hom.app (op ⊤)) (sheafH0EquivSections F x) := by
  conv_lhs => rw [show x = Ext.mk₀ (Ext.addEquiv₀ x) from
    (Ext.mk₀_addEquiv₀_apply x).symm, Ext.mk₀_comp_mk₀]
  unfold sheafH0EquivSections
  simp only [AddEquiv.trans_apply]
  have key :
      Ext.addEquiv₀ (Ext.mk₀ (Ext.addEquiv₀ x ≫ f)) = Ext.addEquiv₀ x ≫ f :=
    by
      change Ext.addEquiv₀ (Ext.addEquiv₀.symm (Ext.addEquiv₀ x ≫ f)) = Ext.addEquiv₀ x ≫ f
      simpa using Ext.addEquiv₀.apply_symm_apply (Ext.addEquiv₀ x ≫ f)
  erw [Adjunction.homAddEquiv_apply, Adjunction.homAddEquiv_apply, key,
    Adjunction.homEquiv_naturality_right, Adjunction.homAddEquiv_apply]
  rfl

/-- `H¹(S.X₁)` as the cokernel of top sections for a short exact sequence of sheaves,
 assuming `H¹(S.X₂)` is subsingleton. -/
noncomputable def sheafH1_cokernel_iso_of_subsingleton_middle {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (h₂H : Subsingleton (Sheaf.H S.X₂ 1)) :
  cokernel (S.g.hom.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H S.X₁ 1) := by
  let δ : S.X₃.obj.obj (op ⊤) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ 1) :=
    AddCommGrpCat.ofHom ((sheafH0EquivSections S.X₃).symm.toAddMonoidHom) ≫
      sheafH_succ_map hS 0
  have hδ : S.g.hom.app (op ⊤) ≫ δ = 0 := by
    ext s
    let y : Sheaf.H S.X₂ 0 := (sheafH0EquivSections S.X₂).symm s
    change ConcreteCategory.hom (sheafH_succ_map hS 0)
      ((sheafH0EquivSections S.X₃).symm
        (ConcreteCategory.hom (S.g.hom.app (op ⊤)) s)) = 0
    rw [← show y.comp (Ext.mk₀ S.g) (add_zero 0) =
        (sheafH0EquivSections S.X₃).symm
          (ConcreteCategory.hom (S.g.hom.app (op ⊤)) s) from
          (sheafH0EquivSections S.X₃).injective (by
            simpa [y] using sheafH0EquivSections_natural (f := S.g) (x := y)),
      sheafH_succ_map_apply,
      Ext.comp_assoc_of_second_deg_zero _ (Ext.mk₀ S.g) hS.extClass rfl,
      hS.comp_extClass, Ext.comp_zero _ _ 1 1 rfl]
  let πH : cokernel (S.g.hom.app (op ⊤)) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ 1) :=
    cokernel.desc _ δ hδ
  have hπH_epi : Epi πH := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro x
    obtain ⟨y, hy⟩ := sheafH_succ_map_exists_preimage_of_subsingleton_middle hS 0 h₂H x
    refine ⟨ConcreteCategory.hom (cokernel.π (S.g.hom.app (op ⊤)))
      (sheafH0EquivSections S.X₃ y), ?_⟩
    simpa [πH, δ] using hy
  have hπH_mono : Mono πH := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    apply sub_eq_zero.mp
    obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective
      (cokernel.π (S.g.hom.app (op ⊤)))).mp inferInstance (a - b)
    rw [← hs]
    have hzero :
        ((((sheafH0EquivSections S.X₃).symm s).comp hS.extClass rfl) :
            Sheaf.H S.X₁ 1) = 0 := by
      change ConcreteCategory.hom (sheafH_succ_map hS 0)
        ((sheafH0EquivSections S.X₃).symm s) = 0
      simpa [πH, δ, ← hs] using (by
        rw [map_sub, hab, sub_self] : ConcreteCategory.hom πH (a - b) = 0)
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ hS
      ((sheafH0EquivSections S.X₃).symm s) rfl hzero
    have hy_sec : ConcreteCategory.hom (S.g.hom.app (op ⊤))
        (sheafH0EquivSections S.X₂ y) = s := by
      rw [← sheafH0EquivSections_natural (f := S.g) (x := y), hy]
      exact (sheafH0EquivSections S.X₃).apply_symm_apply s
    simpa using
      congrArg (ConcreteCategory.hom (cokernel.π (S.g.hom.app (op ⊤)))) hy_sec.symm
  have : IsIso πH := isIso_of_mono_of_epi πH
  exact asIso πH

@[simp] theorem sheafH1_cokernel_iso_of_subsingleton_middle_hom_π {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (h₂H : Subsingleton (Sheaf.H S.X₂ 1))
    (s : S.X₃.obj.obj (op ⊤)) :
    ConcreteCategory.hom
        ((sheafH1_cokernel_iso_of_subsingleton_middle hS h₂H).hom)
        (ConcreteCategory.hom (cokernel.π (S.g.hom.app (op ⊤))) s) =
      ((sheafH0EquivSections S.X₃).symm s).comp hS.extClass rfl := by
  simpa [sheafH1_cokernel_iso_of_subsingleton_middle] using
    sheafH_succ_map_apply hS 0 ((sheafH0EquivSections S.X₃).symm s)

/-- If a sheaf morphism is surjective on top sections, then every degree-zero cohomology
 class of the target lifts along it. -/
theorem sheafH0_surj_of_epi_app_top {X : TopCat.{u}}
    {F G : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : Epi (f.hom.app (op ⊤))) :
    ∀ y : Sheaf.H G 0, ∃ z : Sheaf.H F 0, z.comp (Ext.mk₀ f) (add_zero 0) = y := by
  intro y
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hf
    (sheafH0EquivSections G y)
  refine ⟨(sheafH0EquivSections F).symm s, ?_⟩
  apply (sheafH0EquivSections G).injective
  rw [sheafH0EquivSections_natural (f := f), AddEquiv.apply_symm_apply, hs]

/-- Internal helper for `H^1` vanishing via degree-zero surjectivity. -/
theorem subsingleton_H1_via_surj {C' : Type*} [Category C'] [Abelian C'] [HasExt C']
    (Z : C') {S : ShortComplex C'} (hSE : S.ShortExact)
    (hJ : Subsingleton (Ext Z S.X₂ 1))
    (h_surj : ∀ y : Ext Z S.X₃ 0,
      ∃ z : Ext Z S.X₂ 0, z.comp (Ext.mk₀ S.g) (add_zero 0) = y) :
    Subsingleton (Ext Z S.X₁ 1) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hSE a (@Subsingleton.elim _ hJ _ _) rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hSE b (@Subsingleton.elim _ hJ _ _) rfl
  obtain ⟨c', hc'⟩ := h_surj c; obtain ⟨d', hd'⟩ := h_surj d
  simp only [← hc, ← hd, ← hc', ← hd', Ext.comp_assoc_of_second_deg_zero _ (Ext.mk₀ S.g)
    hSE.extClass rfl, hSE.comp_extClass, Ext.comp_zero _ _ 1 1 rfl]

/-- `H¹` vanishing via degree-zero surjectivity. -/
theorem sheafH_subsingleton_H1_via_surj {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (h₂H : Subsingleton (Sheaf.H S.X₂ 1))
    (h_surj : ∀ y : Sheaf.H S.X₃ 0,
      ∃ z : Sheaf.H S.X₂ 0, z.comp (Ext.mk₀ S.g) (add_zero 0) = y) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  subsingleton_H1_via_surj _ hS h₂H h_surj

/-- `H¹` vanishing criterion from surjective top sections. -/
theorem sheafH_subsingleton_H1_via_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (h₂H : Subsingleton (Sheaf.H S.X₂ 1))
    (hg : Epi (S.g.hom.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  sheafH_subsingleton_H1_via_surj hS h₂H (sheafH0_surj_of_epi_app_top S.g hg)

/-- Positive-degree cohomology of an injective sheaf is subsingleton. -/
theorem sheafH_subsingleton_of_injective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (I : Sheaf J AddCommGrpCat.{w}) [Injective I] (n : ℕ) :
    Subsingleton (Sheaf.H I (n + 1)) := by
  simpa [Sheaf.H] using
    (Ext.subsingleton_of_injective
      ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))) I n)

/-- `H¹` vanishing criterion with injective middle term. -/
theorem sheafH_subsingleton_H1_of_injective_of_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    [Injective S.X₂]
    (hg : Epi (S.g.hom.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  sheafH_subsingleton_H1_via_epi_app_top hS (Ext.subsingleton_of_injective _ _ 0) hg

/-- Forward dimension shift for a short exact sequence of sheaves. -/
theorem sheafH_dimension_shift_of_both {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (n : ℕ)
    (h₃H : Subsingleton (Sheaf.H S.X₃ n))
    (h₂H : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n h₃H h₂H

/-- Forward dimension shift for a monomorphism of sheaves:
 if `f: F ⟶ G` is mono, the cokernel sheaf has subsingleton `H^n`, and
 `G` has subsingleton `H^(n+1)`, then `F` has subsingleton `H^(n+1)`. -/
theorem sheafH_dimension_shift_of_mono {X : TopCat.{u}}
    {F G : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) [Mono f] (n : ℕ)
    (h₃ : Subsingleton (Sheaf.H (cokernel f) n))
    (h₂ : Subsingleton (Sheaf.H G (n + 1))) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
    inferInstance inferInstance
  simpa [S] using
    sheafH_dimension_shift_of_both hS n (by simpa [S] using h₃) (by simpa [S] using h₂)

/-- Forward dimension shifting with injective middle term:
 if `0 → S.X₁ → S.X₂ → S.X₃ → 0` is short exact, `S.X₂` is injective,
 and `H^n(S.X₃)=0`, then `H^(n+1)(S.X₁)=0`. -/
theorem sheafH_dimension_shift_of_injective {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    [Injective S.X₂]
    (n : ℕ)
    (h₃H : Subsingleton (Sheaf.H S.X₃ n)) :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n h₃H (Ext.subsingleton_of_injective _ _ n)

/-- Reverse dimension shift for a locally surjective morphism:
 if `f: F ⟶ G` is locally surjective, `H^n(F)` is subsingleton, and
 `H^(n+1)(kernel f)` is subsingleton, then `H^n(G)` is subsingleton. -/
theorem sheafH_dimension_shift_X₃_of_locallySurjective {X : TopCat.{u}}
    {F G : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (hf : TopCat.Presheaf.IsLocallySurjective f.hom) (n : ℕ)
    (h₂ : Subsingleton (Sheaf.H F n))
    (h₁ : Subsingleton (Sheaf.H (kernel f) (n + 1))) :
    Subsingleton (Sheaf.H G n) := by
  let : Balanced (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) := balanced_of_strongEpiCategory
  have : Epi f := by
    rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} f]
    exact hf
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f)) inferInstance inferInstance
  simpa [S] using
    ext_dimension_shift_X₃ _ hS n (by simpa [S] using h₂) (by simpa [S] using h₁)

/-- If `X` is empty, then the cohomology of every sheaf on `X` is subsingleton. -/
theorem sheafH_subsingleton_of_isEmpty {X : TopCat.{u}} [IsEmpty X]
    (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Subsingleton (Sheaf.H F n) :=
  sheafH_subsingleton_of_isZero
    (sheaf_isZero_of_zero_stalks X F.property (fun x _ ↦ (IsEmpty.false x).elim)) n

/-! ## Sheaf Cohomology Functor -/

/-- The sheaf cohomology functor `H^n: Sheaf(X, Ab) ⥤ Ab`, defined as the covariant
 Ext functor `Ext^n(ℤ_X, −)` where `ℤ_X` is the constant sheaf of integers. -/
noncomputable def sheafCohomologyFunctor (X : TopCat.{u}) (n : ℕ) :
    Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  extFunctorObj ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))) n

@[simp]
theorem sheafCohomologyFunctor_map_apply (X : TopCat.{u}) (n : ℕ)
    {F G : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (x : Sheaf.H F n) :
    ConcreteCategory.hom ((sheafCohomologyFunctor X n).map f) x =
    x.comp (Ext.mk₀ f) (add_zero n) := rfl

-- If both ends of a short exact sequence have vanishing H^n, so does the middle.
/-- Middle-term cohomology vanishing: if `f: F ⟶ G` is mono and the cohomology of `F`
and `cokernel f` are subsingleton in degree `n`, then so is the cohomology of `G`. -/
theorem subsingleton_sheafH_of_shortExact_middle {X : TopCat.{u}}
    {F G : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) [Mono f] (n : ℕ)
    (h₁ : Subsingleton (Sheaf.H F n))
    (h₃ : Subsingleton (Sheaf.H (cokernel f) n)) :
    Subsingleton (Sheaf.H G n) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
    inferInstance inferInstance
  have h₁' : Subsingleton (Sheaf.H S.X₁ n) := by
    simpa [S] using h₁
  have h₃' : Subsingleton (Sheaf.H S.X₃ n) := by
    simpa [S] using h₃
  constructor
  intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₂ _ hS a
    (@Subsingleton.elim _ ((add_zero n) ▸ h₃') _ _)
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₂ _ hS b
    (@Subsingleton.elim _ ((add_zero n) ▸ h₃') _ _)
  rw [← hc, ← hd, @Subsingleton.elim _ h₁' c d]

/-- Naturality of `sheafH1_cokernel_iso_of_subsingleton_middle` for a morphism between
 two short exact sequences of sheaves. -/
theorem sheafH1_cokernel_iso_of_subsingleton_middle_natural {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (h₁₂H : Subsingleton (Sheaf.H S₁.X₂ 1))
    (h₂₂H : Subsingleton (Sheaf.H S₂.X₂ 1)) :
    cokernel.map (S₁.g.hom.app (op ⊤)) (S₂.g.hom.app (op ⊤))
        (φ.τ₂.hom.app (op ⊤)) (φ.τ₃.hom.app (op ⊤))
        (by
          simpa using congrArg
            (fun α : S₁.X₂ ⟶ S₂.X₃ ↦ α.hom.app (op ⊤)) φ.comm₂₃.symm) ≫
      (sheafH1_cokernel_iso_of_subsingleton_middle hS₂ h₂₂H).hom =
    (sheafH1_cokernel_iso_of_subsingleton_middle hS₁ h₁₂H).hom ≫
      (sheafCohomologyFunctor X 1).map φ.τ₁ := by
  apply (cancel_epi (cokernel.π (S₁.g.hom.app (op ⊤)))).mp
  rw [cokernel.π_desc_assoc, Category.assoc]
  ext s
  have hs :
      (((sheafH0EquivSections S₁.X₃).symm s).comp
          (Ext.mk₀ φ.τ₃) (add_zero 0)) =
        (sheafH0EquivSections S₂.X₃).symm
          (ConcreteCategory.hom (φ.τ₃.hom.app (op ⊤)) s) := by
    apply (sheafH0EquivSections S₂.X₃).injective
    simpa using
      (sheafH0EquivSections_natural (f := φ.τ₃)
        (x := (sheafH0EquivSections S₁.X₃).symm s))
  change ConcreteCategory.hom
      (cokernel.π (S₂.g.hom.app (op ⊤)) ≫
        (sheafH1_cokernel_iso_of_subsingleton_middle hS₂ h₂₂H).hom)
      (ConcreteCategory.hom (φ.τ₃.hom.app (op ⊤)) s) =
    ConcreteCategory.hom
      ((sheafH1_cokernel_iso_of_subsingleton_middle hS₁ h₁₂H).hom ≫
        (sheafCohomologyFunctor X 1).map φ.τ₁)
      (ConcreteCategory.hom (cokernel.π (S₁.g.hom.app (op ⊤))) s)
  simp only [ConcreteCategory.comp_apply]
  rw [sheafH1_cokernel_iso_of_subsingleton_middle_hom_π,
    sheafH1_cokernel_iso_of_subsingleton_middle_hom_π]
  change (((sheafH0EquivSections S₂.X₃).symm
        (ConcreteCategory.hom (φ.τ₃.hom.app (op ⊤)) s)).comp hS₂.extClass rfl) =
      ((((sheafH0EquivSections S₁.X₃).symm s).comp hS₁.extClass rfl).comp
        (Ext.mk₀ φ.τ₁) (add_zero 1))
  rw [← hs]
  simpa using
    (sheafH_comp_extClass_naturality hS₁ hS₂ φ 0
      ((sheafH0EquivSections S₁.X₃).symm s)).symm

/-- The degree-`0` sheaf cohomology functor is naturally isomorphic to taking sections on `⊤`. -/
noncomputable def sheafH0NatIsoSections {X : TopCat.{u}} :
    sheafCohomologyFunctor X 0 ≅
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents (fun F ↦ (sheafH0EquivSections F).toAddCommGrpIso)
    fun {F G} f ↦ by
    ext x
    exact sheafH0EquivSections_natural (f := f) (x := x)

/-- Higher-degree connecting additive equivalence for a short exact sequence of sheaves:
if the middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the
connecting morphism induces an additive equivalence `H^n(S.X₃) ≃+ H^(n+1)(S.X₁)`. -/
noncomputable def sheafH_extClassAddEquiv_of_subsingleton_middle {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    Sheaf.H S.X₃ n ≃+ Sheaf.H S.X₁ (n + 1) :=
  extClass_postcompAddEquiv_of_subsingleton_middle _ hS n h₂n h₂succ

@[simp] theorem sheafH_extClassAddEquiv_of_subsingleton_middle_apply
    {X : TopCat.{u}} {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1)))
    (y : Sheaf.H S.X₃ n) :
    sheafH_extClassAddEquiv_of_subsingleton_middle hS n h₂n h₂succ y =
      y.comp hS.extClass rfl := rfl

/-- Higher-degree connecting isomorphism for a short exact sequence of sheaves: if the
middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the connecting
morphism induces an isomorphism `H^n(S.X₃) ≅ H^(n+1)(S.X₁)`. -/
noncomputable def sheafH_succ_iso_of_subsingleton_middle {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    AddCommGrpCat.of (Sheaf.H S.X₃ n) ≅ AddCommGrpCat.of (Sheaf.H S.X₁ (n + 1)) :=
  (sheafH_extClassAddEquiv_of_subsingleton_middle hS n h₂n h₂succ).toAddCommGrpIso

theorem sheafH_succ_iso_of_subsingleton_middle_hom_apply {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1)))
    (y : Sheaf.H S.X₃ n) :
    ConcreteCategory.hom
        ((sheafH_succ_iso_of_subsingleton_middle hS n h₂n h₂succ).hom) y =
      y.comp hS.extClass rfl :=
  sheafH_extClassAddEquiv_of_subsingleton_middle_apply hS n h₂n h₂succ y

/-- Naturality of `sheafH_succ_iso_of_subsingleton_middle` for a morphism between two
short exact sequences of sheaves. -/
theorem sheafH_succ_iso_of_subsingleton_middle_natural {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ)
    (h₁₂n : Subsingleton (Sheaf.H S₁.X₂ n))
    (h₁₂succ : Subsingleton (Sheaf.H S₁.X₂ (n + 1)))
    (h₂₂n : Subsingleton (Sheaf.H S₂.X₂ n))
    (h₂₂succ : Subsingleton (Sheaf.H S₂.X₂ (n + 1))) :
    (sheafH_succ_iso_of_subsingleton_middle hS₁ n h₁₂n h₁₂succ).hom ≫
        (sheafCohomologyFunctor X (n + 1)).map φ.τ₁ =
      (sheafCohomologyFunctor X n).map φ.τ₃ ≫
        (sheafH_succ_iso_of_subsingleton_middle hS₂ n h₂₂n h₂₂succ).hom := by
  ext y
  have hcomp :
      y.comp (hS₁.extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1)) rfl =
        y.comp ((Ext.mk₀ φ.τ₃).comp hS₂.extClass (zero_add 1)) rfl := by
    exact congrArg (fun t ↦ y.comp t rfl) (extClass_naturality hS₁ hS₂ φ).symm
  rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp]
  change
      (ConcreteCategory.hom ((sheafCohomologyFunctor X (n + 1)).map φ.τ₁)
        (ConcreteCategory.hom ((sheafH_succ_iso_of_subsingleton_middle
          hS₁ n h₁₂n h₁₂succ).hom) y)) =
      (ConcreteCategory.hom ((sheafH_succ_iso_of_subsingleton_middle
        hS₂ n h₂₂n h₂₂succ).hom)
        (ConcreteCategory.hom ((sheafCohomologyFunctor X n).map φ.τ₃) y))
  rw [sheafH_succ_iso_of_subsingleton_middle_hom_apply,
    sheafCohomologyFunctor_map_apply, sheafCohomologyFunctor_map_apply,
    sheafH_succ_iso_of_subsingleton_middle_hom_apply]
  simpa [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero] using hcomp
end ProjectiveVanishing

end OAI.AlgebraicGeometry.SheafCohomology.API
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.SheafCohomology.API"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`OAI.AlgebraicGeometry.SheafCohomology.API.ProjectiveVanishing.sheafH_subsingleton_of_injective, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "1883acd676e78a165f3366ef3418864f"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:1883acd676e78a165f3366ef3418864f"
