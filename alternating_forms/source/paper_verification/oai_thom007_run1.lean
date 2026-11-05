module

public import paper_verification.oai_thom006_run2
import all paper_verification.oai_thom006_run2
public import Mathlib.Topology.Sheaves.Flasque
import all Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Functors
import all Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import all Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import all Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Diffeomorph
import all Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
import all Mathlib.Topology.OpenPartialHomeomorph.Basic
public import paper_verification.oai_thom000_run1
import all paper_verification.oai_thom000_run1
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite
import all Mathlib.Topology.Algebra.Monoid.FunOnFinite
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import all Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import all Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import all Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import all Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import all Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
import all Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import all Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import all Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import all Mathlib.Analysis.Calculus.ContDiff.Operations
public import paper_verification.oai_thom004_run1
import all paper_verification.oai_thom004_run1
public import Mathlib.Analysis.Convex.Contractible
import all Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex
import all Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Geometry.Manifold.ChartedSpace
import all Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Topology.Sheaves.Presheaf
import all Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.Functor
public import paper_verification.oai_thom005_run1
import all paper_verification.oai_thom005_run1
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import all Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Topology.LocallyConstant.Algebra
import all Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Sheaves.LocalPredicate
import all Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.Forget
import all Mathlib.Topology.Sheaves.Forget
public import Mathlib.Algebra.Category.ModuleCat.Limits
import all Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Analysis.Complex.Basic
import all Mathlib.Analysis.Complex.Basic
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport -/

/-! # Sheaf Closed Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport

noncomputable section

/-!
# Sections of a module sheaf with closed support

For an open subset `O`, the closed support is its complement. The sheaf of
sections supported there is the actual kernel of restriction to `O` and
pushforward to the ambient space. Its sections have exactly the expected
vanishing condition, and it is flasque whenever the original sheaf is flasque.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cohomology

variable {R : Type} [Ring R] {X : TopCat.{0}}

/-- Intersection with the open complement of the prescribed closed support. -/
def supportOpenIntersection (O : Opens X) : Opens X ⥤ Opens X where
  obj U := U ⊓ O
  map i := homOfLE (inf_le_inf_right O (leOfHom i))

/-- The actual restriction-pushforward presheaf has sections `F(U ∩ O)`. -/
def openRestrictionPushforwardPresheafIso (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    ((TopCat.Sheaf.pushforward (ModuleCat.{0} R) O.inclusion').obj
      ((O.sheafRestrict (C := ModuleCat.{0} R)).obj F)).obj ≅
        (supportOpenIntersection O).op ⋙ F.obj :=
  NatIso.ofComponents
    (fun U => F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf O U.unop))))
    (by
      intro U V i
      dsimp [supportOpenIntersection]
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1)

/-- The restriction-pushforward sheaf, written with literal intersection opens. -/
def openRestrictionPushforwardSheaf (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) : TopCat.Sheaf (ModuleCat.{0} R) X :=
  ⟨(supportOpenIntersection O).op ⋙ F.obj,
    TopCat.Presheaf.isSheaf_of_iso (openRestrictionPushforwardPresheafIso O F)
      (((TopCat.Sheaf.pushforward (ModuleCat.{0} R) O.inclusion').obj
        ((O.sheafRestrict (C := ModuleCat.{0} R)).obj F)).property)⟩

/-- The intersection description is canonically the usual `j_* (F|O)`. -/
def openRestrictionPushforwardSheafIso (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (TopCat.Sheaf.pushforward (ModuleCat.{0} R) O.inclusion').obj
      ((O.sheafRestrict (C := ModuleCat.{0} R)).obj F) ≅
        openRestrictionPushforwardSheaf O F :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X)
    (ModuleCat.{0} R)).preimageIso (openRestrictionPushforwardPresheafIso O F)

/-- Restriction followed by pushforward acts on actual sheaf morphisms. -/
def openRestrictionPushforwardFunctor (O : Opens X) :
    TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) X where
  obj F := openRestrictionPushforwardSheaf O F
  map f := ⟨Functor.whiskerLeft (supportOpenIntersection O).op f.hom⟩

instance openRestrictionPushforwardFunctor_additive (O : Opens X) :
    (openRestrictionPushforwardFunctor (R := R) O).Additive where
  map_add := rfl

/-- Restriction from `F(U)` to `F(U ∩ O)`. -/
def sheafRestrictionToOpen (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    F ⟶ openRestrictionPushforwardSheaf O F :=
  ⟨{ app U := F.obj.map (homOfLE (inf_le_left : U.unop ⊓ O ≤ U.unop)).op
     naturality U V i := by
       dsimp [openRestrictionPushforwardSheaf, supportOpenIntersection]
       rw [← F.obj.map_comp, ← F.obj.map_comp]
       congr 1 }⟩

/-- The restriction maps form a natural transformation on sheaves. -/
def sheafRestrictionToOpenNatTrans (O : Opens X) :
    𝟭 (TopCat.Sheaf (ModuleCat.{0} R) X) ⟶ openRestrictionPushforwardFunctor O where
  app F := sheafRestrictionToOpen O F
  naturality F G f := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact (f.hom.naturality (homOfLE (inf_le_left : U.unop ⊓ O ≤ U.unop)).op).symm

/-- The sheaf of sections supported in the closed set `X \ O`. -/
def closedSupportSheaf (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) : TopCat.Sheaf (ModuleCat.{0} R) X :=
  kernel (sheafRestrictionToOpen O F)

/-- Include the supported sheaf into the original sheaf. -/
def closedSupportSheafInclusion (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) : closedSupportSheaf O F ⟶ F :=
  kernel.ι (sheafRestrictionToOpen O F)

/-- Evaluation of a module sheaf on a specified open subset. -/
def moduleSheafSections (U : Opens X) :
    TopCat.Sheaf (ModuleCat.{0} R) X ⥤ ModuleCat.{0} R :=
  sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R) ⋙
    (evaluation (Opens X)ᵒᵖ (ModuleCat.{0} R)).obj (op U)

instance moduleSheafSections_additive (U : Opens X) :
    (moduleSheafSections (R := R) U).Additive where
  map_add := rfl

instance moduleSheafSections_preservesFiniteLimits (U : Opens X) :
    PreservesFiniteLimits (moduleSheafSections (R := R) U) := by
  have : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)) :=
    CategoryTheory.Sheaf.instPreservesFiniteLimitsFunctorOppositeSheafToPresheafOfHasFiniteLimits
  exact comp_preservesFiniteLimits _ _

/-- The inclusion's image is exactly the sections vanishing on `U ∩ O`. -/
theorem closedSupportSheafInclusion_range (O U : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    LinearMap.range (((closedSupportSheafInclusion O F).hom.app (op U)).hom) =
      LinearMap.ker ((F.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op).hom) := by
  have h := (ShortComplex.kernelSequence_exact (sheafRestrictionToOpen O F)).map_of_mono_of_preservesKernel
    (moduleSheafSections U) inferInstance inferInstance
  exact h.moduleCat_range_eq_ker

/-- A supported section vanishes on the open complement by construction. -/
theorem closedSupportSheafInclusion_vanishes (O U : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X)
    (s : (closedSupportSheaf O F).obj.obj (op U)) :
    F.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op
      ((closedSupportSheafInclusion O F).hom.app (op U) s) = 0 := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op U)) (kernel.condition (sheafRestrictionToOpen O F))) s
  exact h

/-- Inclusion of supported sections is injective on every open set. -/
theorem closedSupportSheafInclusion_injective (O U : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    Function.Injective ((closedSupportSheafInclusion O F).hom.app (op U)) := by
  change Function.Injective
    ((moduleSheafSections U).map (kernel.ι (sheafRestrictionToOpen O F)))
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

end Cohomology

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.ChartOpenDiffeomorph -/

/-! # Chart Open Diffeomorph -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ChartOpenDiffeomorph

noncomputable section

/-!
# Smooth coordinates on arbitrary open chart subdomains

An open subset contained in a chart source is diffeomorphic to its actual
open image under that chart. Neither the subset nor its image is required
to be nonempty, and the chart anchor need not belong to the subset.

Nested open submanifolds also flatten to their actual ambient open image,
through the pointwise identity on the underlying ambient points.
-/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

section ChartTopology

variable (H : Type*) [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The actual chart image of an arbitrary open subset of the chart source. -/
def chartOpenImage (x : M) (W : Opens M) (hW : (W : Set M) ⊆ (chartAt H x).source) :
    Opens H :=
  ⟨chartAt H x '' (W : Set M), (chartAt H x).isOpen_image_of_subset_source W.isOpen hW⟩

/-- Every point of the open chart image lies in the actual chart target. -/
theorem chartOpenImage_subset_target (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt H x).source) :
    (chartOpenImage H x W hW : Set H) ⊆ (chartAt H x).target := by
  rintro y ⟨z, hz, rfl⟩
  exact (chartAt H x).map_source (hW hz)

/-- Restriction of the given chart is a homeomorphism onto its open image. -/
def chartOpenHomeomorph (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt H x).source) :
    W ≃ₜ chartOpenImage H x W hW :=
  (chartAt H x).homeomorphOfImageSubsetSource hW rfl

@[simp]
theorem chartOpenHomeomorph_apply (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt H x).source) (y : W) :
    (chartOpenHomeomorph H x W hW y : H) = chartAt H x (y : M) := rfl

@[simp]
theorem chartOpenHomeomorph_symm_apply (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt H x).source) (y : chartOpenImage H x W hW) :
    ((chartOpenHomeomorph H x W hW).symm y : M) = (chartAt H x).symm (y : H) := rfl

end ChartTopology

section NestedTopology

variable {M : Type*} [TopologicalSpace M]

/-- The ambient open subset obtained by forgetting one layer of an open subtype. -/
def nestedOpenImage (U : Opens M) (W : Opens U) : Opens M :=
  ⟨Subtype.val '' (W : Set U), U.isOpenEmbedding'.isOpenMap _ W.isOpen⟩

/-- The flattened open subset is contained in the original ambient open subset. -/
theorem nestedOpenImage_subset (U : Opens M) (W : Opens U) :
    (nestedOpenImage U W : Set M) ⊆ (U : Set M) := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem nestedOpenImage_inner_mem (U : Opens M) (W : Opens U)
    (y : nestedOpenImage U W) :
    (⟨(y : M), nestedOpenImage_subset U W y.property⟩ : U) ∈ W := by
  rcases y.property with ⟨z, hz, heq⟩
  have h : (⟨(y : M), nestedOpenImage_subset U W y.property⟩ : U) = z :=
    Subtype.ext heq.symm
  exact h.symm ▸ hz

/-- Flattening two open-subtype layers preserves precisely the ambient point. -/
def nestedOpenEquiv (U : Opens M) (W : Opens U) : W ≃ nestedOpenImage U W where
  toFun y := ⟨((y : U) : M), ⟨(y : U), y.property, rfl⟩⟩
  invFun y := ⟨⟨(y : M), nestedOpenImage_subset U W y.property⟩,
    nestedOpenImage_inner_mem U W y⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl

@[simp]
theorem nestedOpenEquiv_apply (U : Opens M) (W : Opens U) (y : W) :
    (nestedOpenEquiv U W y : M) = ((y : U) : M) := rfl

@[simp]
theorem nestedOpenEquiv_symm_apply (U : Opens M) (W : Opens U)
    (y : nestedOpenImage U W) :
    (((nestedOpenEquiv U W).symm y : U) : M) = (y : M) := rfl

end NestedTopology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- Nested open submanifolds flatten smoothly while preserving the given model.
No nonemptiness or manifold-compatibility premise is needed for these inclusions. -/
def nestedOpenDiffeomorph (U : Opens M) (W : Opens U) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) W (nestedOpenImage U W) ∞ where
  toEquiv := nestedOpenEquiv U W
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (nestedOpenImage U W) _).mp
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun y : W => ((y : U) : M))
    exact (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U)).comp
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := W))
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff W _).mp
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val : nestedOpenImage U W → M)
    exact contMDiff_subtype_val

@[simp]
theorem nestedOpenDiffeomorph_apply (U : Opens M) (W : Opens U) (y : W) :
    (nestedOpenDiffeomorph E U W y : M) = ((y : U) : M) := rfl

@[simp]
theorem nestedOpenDiffeomorph_symm_apply (U : Opens M) (W : Opens U)
    (y : nestedOpenImage U W) :
    (((nestedOpenDiffeomorph E U W).symm y : U) : M) = (y : M) := rfl

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual chart identifies each open subset of its source smoothly with
its open model image. This includes empty subsets and subsets missing the anchor. -/
def chartOpenDiffeomorph (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt E x).source) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) W (chartOpenImage E x W hW) ∞ where
  toEquiv := (chartOpenHomeomorph E x W hW).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (chartOpenImage E x W hW) _).mp
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun y : W => chartAt E x (y : M))
    exact (contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := x)).comp_contMDiff
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := W)) (fun y => hW y.property)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff W _).mp
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun y : chartOpenImage E x W hW => (chartAt E x).symm (y : E))
    exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x)).comp_contMDiff
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := chartOpenImage E x W hW))
      (fun y => chartOpenImage_subset_target E x W hW y.property)

@[simp]
theorem chartOpenDiffeomorph_apply (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt E x).source) (y : W) :
    (chartOpenDiffeomorph E x W hW y : E) = chartAt E x (y : M) := rfl

@[simp]
theorem chartOpenDiffeomorph_symm_apply (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt E x).source) (y : chartOpenImage E x W hW) :
    ((chartOpenDiffeomorph E x W hW).symm y : M) = (chartAt E x).symm (y : E) := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.ChartOpenDiffeomorph
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.ChartOpenDiffeomorph"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.Smooth -/

/-! # Smooth -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Smooth

noncomputable section

/-!
# Smooth singular simplices in a real normed space

A smooth simplex is a continuous simplex that extends smoothly to an open
neighborhood of the standard simplex in its ambient coordinate space. This is
the usual extendibility condition at the boundary; no differentiability of a
function on a bare subtype is substituted for it.

The extension condition is preserved by every simplicial operator, since the
standard simplex maps extend to continuous linear maps of coordinate spaces.
Consequently these simplices form an actual subcomplex of the continuous
singular simplicial set. No quasi-isomorphism assertion is made here.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial ContDiff OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth extension to an open neighborhood of the closed standard simplex. -/
def IsSmoothSimplex {n : ℕ} (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)) : Prop :=
  ∃ (F : (Fin (n + 1) → ℝ) → E) (U : Set (Fin (n + 1) → ℝ)),
    IsOpen U ∧ Set.range (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) => (x : Fin (n + 1) → ℝ)) ⊆ U ∧
      ContDiffOn ℝ ∞ F U ∧ ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)), F x = σ x

/-- The ambient continuous linear extension of a simplex operator. -/
def simplexLinearMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    (Fin (m + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) where
  toLinearMap := FunOnFinite.linearMap ℝ ℝ f
  cont := FunOnFinite.continuous_linearMap ℝ ℝ f

theorem simplexLinearMap_weights {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1)) (x : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    simplexLinearMap f x = (Convexity.StdSimplex.map f x : Fin (n + 1) → ℝ) := by
  simp [simplexLinearMap, FunOnFinite.linearMap, Convexity.StdSimplex.map]
  rfl

theorem IsSmoothSimplex.precomp {m n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)} (hσ : IsSmoothSimplex σ)
    (f : Fin (m + 1) → Fin (n + 1)) :
    IsSmoothSimplex (σ.comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩) := by
  rcases hσ with ⟨F, U, hU, hsub, hF, heq⟩
  refine ⟨F ∘ simplexLinearMap f, (simplexLinearMap f) ⁻¹' U,
    hU.preimage (simplexLinearMap f).continuous, ?_,
    hF.comp_continuousLinearMap (simplexLinearMap f), ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hsub ⟨Convexity.StdSimplex.map f x, (simplexLinearMap_weights f x).symm⟩
  · intro x
    change F (simplexLinearMap f x) = σ (Convexity.StdSimplex.map f x)
    rw [simplexLinearMap_weights]
    exact heq (Convexity.StdSimplex.map f x)

/-- Constant simplices have globally smooth extensions. -/
theorem isSmoothSimplex_const (n : ℕ) (x : E) :
    IsSmoothSimplex (ContinuousMap.const (Convexity.StdSimplex ℝ (Fin (n + 1))) x) := by
  exact ⟨fun _ => x, Set.univ, isOpen_univ, Set.subset_univ _,
    contDiffOn_const, fun _ => rfl⟩

/-- Smooth simplices form a simplicial subcomplex of genuine singular simplices. -/
def smoothSingularSubcomplex (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (TopCat.toSSet.obj (TopCat.of E)).Subcomplex where
  obj n := {σ | IsSmoothSimplex ((TopCat.of E).toSSetObjEquiv n σ)}
  map {m n} f σ hσ := by
    change IsSmoothSimplex ((TopCat.of E).toSSetObjEquiv n
      ((TopCat.toSSet.obj (TopCat.of E)).map f σ))
    have h := IsSmoothSimplex.precomp
      (σ := (TopCat.of E).toSSetObjEquiv m σ) hσ f.unop
    convert h using 1
    ext x
    rfl

/-- The actual simplicial inclusion of smooth into continuous singular simplices. -/
abbrev smoothSingularInclusion (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (smoothSingularSubcomplex E).toSSet ⟶ TopCat.toSSet.obj (TopCat.of E) :=
  (smoothSingularSubcomplex E).ι

variable {R : Type} [Ring R]

/-- Smooth singular chains with coefficients in a module. -/
abbrev smoothSingularChains (M : ModuleCat.{0} R)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  (smoothSingularSubcomplex E).toSSet.chainComplex M

/-- The genuine comparison map on chains induced by inclusion of smooth simplices. -/
def smoothSingularChainInclusion (M : ModuleCat.{0} R)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    smoothSingularChains M E ⟶ (TopCat.toSSet.obj (TopCat.of E)).chainComplex M :=
  SSet.chainComplexMap (smoothSingularInclusion E) M

/-- Smooth singular cochains, using products over the actual smooth simplices. -/
abbrev smoothSingularCochains (M : ModuleCat.{0} R)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  Singular.Basic.simplicialCochains (smoothSingularSubcomplex E).toSSet M

/-- Restrict an ordinary singular cochain to its smooth simplices. -/
def smoothSingularCochainRestriction (M : ModuleCat.{0} R)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Singular.Basic.singularCochains M (TopCat.of E) ⟶ smoothSingularCochains M E :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    (SSet.chainComplexMap (smoothSingularInclusion E) (op M)).op

end

end OAI.AlgebraicTopology.Cohomology.Singular.Smooth
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.Smooth"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth -/

/-! # Manifold Smooth -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth

noncomputable section

/-!
# Genuine smooth singular simplices in charted manifolds

The target now has its actual manifold smooth structure. A simplex is smooth
when it extends to an open neighborhood of the closed standard simplex as a
`ContMDiffOn` map. This uses the usual model without boundary and does not put a
spurious linear structure on the manifold. The construction is meaningful for
a charted space, and has its usual interpretation for a smooth atlas.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff _root_.Manifold

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

/-- A manifold-valued simplex with an actual smooth neighborhood extension. -/
def IsManifoldSmoothSimplex {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)) : Prop :=
  ∃ (F : (Fin (n + 1) → ℝ) → M) (U : Set (Fin (n + 1) → ℝ)),
    IsOpen U ∧ Set.range (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      (x : Fin (n + 1) → ℝ)) ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, E) ∞ F U ∧
        ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)), F x = σ x

theorem IsManifoldSmoothSimplex.precomp {m n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)}
    (hσ : IsManifoldSmoothSimplex E σ) (f : Fin (m + 1) → Fin (n + 1)) :
    IsManifoldSmoothSimplex E
      (σ.comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩) := by
  rcases hσ with ⟨F, U, hU, hsub, hF, heq⟩
  refine ⟨F ∘ Smooth.simplexLinearMap f, (Smooth.simplexLinearMap f) ⁻¹' U,
    hU.preimage (Smooth.simplexLinearMap f).continuous, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hsub ⟨Convexity.StdSimplex.map f x, (Smooth.simplexLinearMap_weights f x).symm⟩
  · exact hF.comp (Smooth.simplexLinearMap f).contDiff.contMDiff.contMDiffOn
      (Set.mapsTo_preimage _ _)
  · intro x
    change F (Smooth.simplexLinearMap f x) = σ (Convexity.StdSimplex.map f x)
    rw [Smooth.simplexLinearMap_weights]
    exact heq (Convexity.StdSimplex.map f x)

/-- Constant simplices have constant smooth manifold-valued extensions. -/
theorem isManifoldSmoothSimplex_const (n : ℕ) (x : M) :
    IsManifoldSmoothSimplex E (ContinuousMap.const (Convexity.StdSimplex ℝ (Fin (n + 1))) x) := by
  exact ⟨fun _ => x, Set.univ, isOpen_univ, Set.subset_univ _,
    contMDiffOn_const, fun _ => rfl⟩

/-- The genuine simplicial subcomplex of manifold-smooth singular simplices. -/
def manifoldSmoothSingularSubcomplex (M : Type) [TopologicalSpace M] [ChartedSpace E M] :
    (TopCat.toSSet.obj (TopCat.of M)).Subcomplex where
  obj n := {σ | IsManifoldSmoothSimplex E ((TopCat.of M).toSSetObjEquiv n σ)}
  map {m n} f σ hσ := by
    change IsManifoldSmoothSimplex E ((TopCat.of M).toSSetObjEquiv n
      ((TopCat.toSSet.obj (TopCat.of M)).map f σ))
    have h := IsManifoldSmoothSimplex.precomp E
      (σ := (TopCat.of M).toSSetObjEquiv m σ) hσ f.unop
    convert h using 1
    ext x
    rfl

/-- The actual inclusion forgetting only the smoothness property. -/
abbrev manifoldSmoothInclusion (M : Type) [TopologicalSpace M] [ChartedSpace E M] :
    (manifoldSmoothSingularSubcomplex E M).toSSet ⟶ TopCat.toSSet.obj (TopCat.of M) :=
  (manifoldSmoothSingularSubcomplex E M).ι

variable {R : Type} [Ring R]

/-- Smooth singular cochains of the genuine smooth simplicial set. -/
abbrev manifoldSmoothCochains (A : ModuleCat.{0} R)
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  Basic.simplicialCochains (manifoldSmoothSingularSubcomplex E M).toSSet A

/-- Restrict a continuous singular cochain to manifold-smooth simplices. -/
def manifoldSmoothCochainRestriction (A : ModuleCat.{0} R)
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] :
    Basic.singularCochains A (TopCat.of M) ⟶ manifoldSmoothCochains E A M :=
  Functor.simplicialPullback A (manifoldSmoothInclusion E M)

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor -/

/-! # Manifold Smooth Functor -/

namespace OAI.AlgebraicTopology.Cohomology.Singular

noncomputable section

/-!
# Smooth singular functoriality for manifolds

Smooth singular simplices use actual open-neighborhood extensions into a
charted space. A smooth map of charted spaces postcomposes these extensions,
giving genuine simplicial maps and contravariant maps on smooth cochains.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff _root_.Manifold

variable {E F G : Type}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {M N P : Type}
variable [TopologicalSpace M] [ChartedSpace E M]
variable [TopologicalSpace N] [ChartedSpace F N]
variable [TopologicalSpace P] [ChartedSpace G P]

/-- Smooth postcomposition preserves the actual neighborhood-extension condition. -/
theorem ManifoldSmooth.IsManifoldSmoothSimplex.postcomp {n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)} (hσ : ManifoldSmooth.IsManifoldSmoothSimplex E σ)
    {f : M → N} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ManifoldSmooth.IsManifoldSmoothSimplex F ((⟨f, hf.continuous⟩ : C(M, N)).comp σ) := by
  rcases hσ with ⟨σ', U, hU, hsub, hσ', heq⟩
  refine ⟨f ∘ σ', U, hU, hsub, hf.comp_contMDiffOn hσ', ?_⟩
  intro x
  exact congrArg f (heq x)

variable (E F) in
/-- The genuine simplicial map on smooth singular simplices induced by a smooth map. -/
def ManifoldSmoothFunctor.manifoldSmoothSingularMap (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet ⟶
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex F N).toSSet where
  app n := ↾fun σ => ⟨(TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).app n σ.val, by
    change ManifoldSmooth.IsManifoldSmoothSimplex F ((TopCat.of N).toSSetObjEquiv n
      ((TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).app n σ.val))
    exact ManifoldSmooth.IsManifoldSmoothSimplex.postcomp σ.property hf⟩
  naturality n m θ := by
    ext σ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).naturality θ) σ.val

@[simp]
theorem ManifoldSmoothFunctor.manifoldSmoothSingularMap_app_val (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : SimplexCategoryᵒᵖ)
    (σ : (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).obj n) :
    ((ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf).app n σ).val =
      (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).app n σ.val := rfl

/-- The image simplex is given by ordinary pointwise postcomposition. -/
@[simp]
theorem ManifoldSmoothFunctor.manifoldSmoothSingularMap_apply (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : SimplexCategoryᵒᵖ)
    (σ : (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).obj n)
    (x : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    (TopCat.of N).toSSetObjEquiv n ((ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf).app n σ).val x =
      f ((TopCat.of M).toSSetObjEquiv n σ.val x) := rfl

/-- Inclusion into continuous singular simplices is natural for smooth maps. -/
@[reassoc]
theorem ManifoldSmoothFunctor.manifoldSmoothSingularMap_inclusion (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf ≫ ManifoldSmooth.manifoldSmoothInclusion F N =
      ManifoldSmooth.manifoldSmoothInclusion E M ≫
        TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩) := rfl

@[simp]
theorem ManifoldSmoothFunctor.manifoldSmoothSingularMap_id :
    ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (id : M → M) contMDiff_id =
      𝟙 (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet := by
  ext n σ
  apply Subtype.ext
  rfl

@[simp]
theorem ManifoldSmoothFunctor.manifoldSmoothSingularMap_comp (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (g : N → P)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g) :
    ManifoldSmoothFunctor.manifoldSmoothSingularMap E G (g ∘ f) (hg.comp hf) =
      ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf ≫ ManifoldSmoothFunctor.manifoldSmoothSingularMap F G g hg := by
  ext n σ
  apply Subtype.ext
  rfl

variable {R : Type} [Ring R]

variable (E F) in
/-- Pullback of genuine smooth singular cochains along a smooth map of manifolds. -/
def ManifoldSmoothFunctor.manifoldSmoothPullback (A : ModuleCat.{0} R) (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ManifoldSmooth.manifoldSmoothCochains F A N ⟶ ManifoldSmooth.manifoldSmoothCochains E A M :=
  Functor.simplicialPullback A (ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf)

@[simp]
theorem ManifoldSmoothFunctor.manifoldSmoothPullback_id (A : ModuleCat.{0} R) :
    ManifoldSmoothFunctor.manifoldSmoothPullback E E A (id : M → M) contMDiff_id =
      𝟙 (ManifoldSmooth.manifoldSmoothCochains E A M) := by
  simp [ManifoldSmoothFunctor.manifoldSmoothPullback]

@[simp]
theorem ManifoldSmoothFunctor.manifoldSmoothPullback_comp (A : ModuleCat.{0} R) (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (g : N → P)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g) :
    ManifoldSmoothFunctor.manifoldSmoothPullback E G A (g ∘ f) (hg.comp hf) =
      ManifoldSmoothFunctor.manifoldSmoothPullback F G A g hg ≫ ManifoldSmoothFunctor.manifoldSmoothPullback E F A f hf := by
  exact (congrArg (fun k => Functor.simplicialPullback A k)
    (ManifoldSmoothFunctor.manifoldSmoothSingularMap_comp f hf g hg)).trans (Functor.simplicialPullback_comp A _ _)

/-- Ordinary-to-smooth cochain restriction commutes with smooth pullback. -/
@[reassoc]
theorem ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality (A : ModuleCat.{0} R)
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    Functor.singularPullback A (TopCat.ofHom ⟨f, hf.continuous⟩) ≫
        ManifoldSmooth.manifoldSmoothCochainRestriction E A M =
      ManifoldSmooth.manifoldSmoothCochainRestriction F A N ≫ ManifoldSmoothFunctor.manifoldSmoothPullback E F A f hf := by
  change Functor.simplicialPullback A (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) ≫
      Functor.simplicialPullback A (ManifoldSmooth.manifoldSmoothInclusion E M) =
    Functor.simplicialPullback A (ManifoldSmooth.manifoldSmoothInclusion F N) ≫
      Functor.simplicialPullback A (ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf)
  rw [← Functor.simplicialPullback_comp, ← Functor.simplicialPullback_comp,
    ManifoldSmoothFunctor.manifoldSmoothSingularMap_inclusion]

end

end OAI.AlgebraicTopology.Cohomology.Singular
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.SmoothOpen -/

/-! # Smooth Open -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmoothOpen

noncomputable section

/-!
# Smooth singular simplices in subsets and open domains

The simplicial set is constructed by inverse image of the genuine smooth
singular subcomplex under the continuous inclusion of a subset. For an open
subset the extension can be chosen with its values in that open subset; the
equivalence is proved rather than imposed as a hypothesis.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ordinary continuous inclusion of a subset into the ambient normed space. -/
def normedSubsetInclusion (U : Set E) : TopCat.of U ⟶ TopCat.of E :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- A simplex in a subset is smooth when its ambient simplex has a genuine
smooth neighborhood extension. -/
def IsSmoothSimplexIn (U : Set E) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) : Prop :=
  Smooth.IsSmoothSimplex ((normedSubsetInclusion U).hom.comp σ)

/-- In an open target the smooth extension itself may be chosen to remain in
the target, by shrinking its open domain. -/
theorem isSmoothSimplexIn_iff_extension {U : Set E} (hU : IsOpen U) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) :
    IsSmoothSimplexIn U σ ↔
      ∃ (F : (Fin (n + 1) → ℝ) → E) (V : Set (Fin (n + 1) → ℝ)),
        IsOpen V ∧ Set.range (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
          (x : Fin (n + 1) → ℝ)) ⊆ V ∧
          ContDiffOn ℝ ∞ F V ∧ Set.MapsTo F V U ∧
            ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)), F x = (σ x).val := by
  constructor
  · rintro ⟨F, V, hV, hsub, hF, heq⟩
    refine ⟨F, V ∩ F ⁻¹' U, hF.continuousOn.isOpen_inter_preimage hV hU,
      ?_, hF.mono Set.inter_subset_left, Set.inter_subset_right, heq⟩
    rintro _ ⟨x, rfl⟩
    refine ⟨hsub ⟨x, rfl⟩, ?_⟩
    change F x ∈ U
    have hxeq := heq x
    change F x = (σ x).val at hxeq
    rw [hxeq]
    exact (σ x).property
  · rintro ⟨F, V, hV, hsub, hF, _, heq⟩
    exact ⟨F, V, hV, hsub, hF, heq⟩

/-- Actual smooth singular simplices in a subset, as a simplicial subcomplex
of the continuous singular simplices of that subset. -/
def subsetSmoothSingularSubcomplex (U : Set E) :
    (TopCat.toSSet.obj (TopCat.of U)).Subcomplex :=
  (Smooth.smoothSingularSubcomplex E).preimage
    (TopCat.toSSet.map (normedSubsetInclusion U))

/-- Inclusion from subset-valued smooth simplices into ambient smooth simplices. -/
def subsetSmoothToAmbient (U : Set E) :
    (subsetSmoothSingularSubcomplex U).toSSet ⟶
      (Smooth.smoothSingularSubcomplex E).toSSet :=
  (Smooth.smoothSingularSubcomplex E).fromPreimage
    (TopCat.toSSet.map (normedSubsetInclusion U))

@[reassoc]
theorem subsetSmoothToAmbient_inclusion (U : Set E) :
    subsetSmoothToAmbient U ≫ Smooth.smoothSingularInclusion E =
      (subsetSmoothSingularSubcomplex U).ι ≫
        TopCat.toSSet.map (normedSubsetInclusion U) := rfl

/-- Ordinary continuous inclusion associated with a containment of subsets. -/
def normedSubsetMap {U V : Set E} (h : U ⊆ V) : TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x => ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩

/-- Inclusion of targets restricts to their genuine smooth singular simplices. -/
def subsetSmoothMap {U V : Set E} (h : U ⊆ V) :
    (subsetSmoothSingularSubcomplex U).toSSet ⟶
      (subsetSmoothSingularSubcomplex V).toSSet where
  app n := ↾fun σ => ⟨(TopCat.toSSet.map (normedSubsetMap h)).app n σ.val, by
    exact σ.property⟩
  naturality n m f := by
    ext σ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((TopCat.toSSet.map (normedSubsetMap h)).naturality f) σ.val

@[reassoc]
theorem subsetSmoothMap_inclusion {U V : Set E} (h : U ⊆ V) :
    subsetSmoothMap h ≫ (subsetSmoothSingularSubcomplex V).ι =
      (subsetSmoothSingularSubcomplex U).ι ≫
        TopCat.toSSet.map (normedSubsetMap h) := rfl

@[simp]
theorem subsetSmoothMap_refl (U : Set E) :
    subsetSmoothMap (Set.Subset.refl U) =
      𝟙 (subsetSmoothSingularSubcomplex U).toSSet := by
  ext n σ
  apply Subtype.ext
  rfl

@[simp]
theorem subsetSmoothMap_comp {U V W : Set E} (h : U ⊆ V) (k : V ⊆ W) :
    subsetSmoothMap (h.trans k) = subsetSmoothMap h ≫ subsetSmoothMap k := by
  ext n σ
  apply Subtype.ext
  rfl

variable {R : Type} [Ring R]

/-- Actual smooth singular cochains in a subset of the normed space. -/
abbrev subsetSmoothCochains (M : ModuleCat.{0} R) (U : Set E) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  Basic.simplicialCochains (subsetSmoothSingularSubcomplex U).toSSet M

/-- Restriction of continuous singular cochains to the smooth simplices. -/
def subsetSmoothCochainRestriction (M : ModuleCat.{0} R) (U : Set E) :
    Basic.singularCochains M (TopCat.of U) ⟶ subsetSmoothCochains M U :=
  Functor.simplicialPullback M (subsetSmoothSingularSubcomplex U).ι

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmoothOpen
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.SmoothOpen"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothModels -/

/-! # Manifold Smooth Models -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothModels

noncomputable section

/-!
# Compatibility of manifold smooth simplices with the normed-space models

For the standard chart on a real normed space, manifold smoothness is ordinary
smoothness. For an open subset with its inherited charts, the same definition
agrees with the previously constructed subset-valued smooth singular complex.
The open-target argument constructs a genuine target-valued neighborhood
extension; it does not assume that an ambient extension stays in the open set.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff _root_.Manifold

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The standard manifold structure on a normed space gives the old smooth
neighborhood-extension condition. -/
theorem isManifoldSmoothSimplex_self_iff {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)) :
    ManifoldSmooth.IsManifoldSmoothSimplex E σ ↔ Smooth.IsSmoothSimplex σ := by
  simp only [ManifoldSmooth.IsManifoldSmoothSimplex, Smooth.IsSmoothSimplex, contMDiffOn_iff_contDiffOn]

/-- The two genuine smooth singular subcomplexes of a normed space agree. -/
theorem manifoldSmoothSingularSubcomplex_self :
    ManifoldSmooth.manifoldSmoothSingularSubcomplex E E = Smooth.smoothSingularSubcomplex E := by
  ext n σ
  exact isManifoldSmoothSimplex_self_iff E _

/-- On an open subset with its inherited charts, manifold-smooth simplices are
exactly the subset-valued smooth simplices previously defined in the ambient space. -/
theorem isManifoldSmoothSimplex_open_iff (U : TopologicalSpace.Opens E) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) :
    ManifoldSmooth.IsManifoldSmoothSimplex E σ ↔ SmoothOpen.IsSmoothSimplexIn (U : Set E) σ := by
  classical
  constructor
  · rintro ⟨F, V, hV, hsub, hF, heq⟩
    refine ⟨Subtype.val ∘ F, V, hV, hsub, ?_, ?_⟩
    · apply contMDiffOn_iff_contDiffOn.mp
      intro x hx
      exact (ContMDiffWithinAt.subtypeVal_comp_iff U F V x).mpr (hF x hx)
    · intro x
      exact congrArg Subtype.val (heq x)
  · intro hσ
    obtain ⟨F, V, hV, hsub, hF, hmap, heq⟩ :=
      (SmoothOpen.isSmoothSimplexIn_iff_extension U.isOpen σ).mp hσ
    let d : U := σ (Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n + 1)))
    let G : (Fin (n + 1) → ℝ) → U :=
      fun x => if hx : x ∈ V then ⟨F x, hmap hx⟩ else d
    have hG : ∀ x ∈ V, (G x).val = F x := by
      intro x hx
      simp only [G, dite_eq_left hx]
    have hGval : ContDiffOn ℝ ∞ (Subtype.val ∘ G) V := hF.congr hG
    refine ⟨G, V, hV, hsub, ?_, ?_⟩
    · intro x hx
      exact (ContMDiffWithinAt.subtypeVal_comp_iff U G V x).mp
        (hGval.contMDiffOn x hx)
    · intro x
      apply Subtype.ext
      exact (hG x (hsub ⟨x, rfl⟩)).trans (heq x)

/-- The open-subset manifold model is the old subset smooth singular subcomplex. -/
theorem manifoldSmoothSingularSubcomplex_open (U : TopologicalSpace.Opens E) :
    ManifoldSmooth.manifoldSmoothSingularSubcomplex E U = SmoothOpen.subsetSmoothSingularSubcomplex (U : Set E) := by
  ext n σ
  change ManifoldSmooth.IsManifoldSmoothSimplex E ((TopCat.of U).toSSetObjEquiv n σ) ↔
    SmoothOpen.IsSmoothSimplexIn (U : Set E) ((TopCat.of U).toSSetObjEquiv n σ)
  exact isManifoldSmoothSimplex_open_iff E U _

/-- The canonical simplicial identification for the standard normed-space model. -/
def manifoldSmoothSelfIso :
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E E).toSSet ≅ (Smooth.smoothSingularSubcomplex E).toSSet :=
  SSet.Subcomplex.eqToIso (manifoldSmoothSingularSubcomplex_self E)

/-- The canonical simplicial identification for an open subset with inherited charts. -/
def manifoldSmoothOpenIso (U : TopologicalSpace.Opens E) :
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet ≅
      (SmoothOpen.subsetSmoothSingularSubcomplex (U : Set E)).toSSet :=
  SSet.Subcomplex.eqToIso (manifoldSmoothSingularSubcomplex_open E U)

@[reassoc (attr := simp)]
theorem manifoldSmoothSelfIso_inv_inclusion :
    (manifoldSmoothSelfIso E).inv ≫ ManifoldSmooth.manifoldSmoothInclusion E E =
      Smooth.smoothSingularInclusion E :=
  SSet.Subcomplex.homOfLE_ι (manifoldSmoothSingularSubcomplex_self E).symm.le

@[reassoc (attr := simp)]
theorem manifoldSmoothOpenIso_inv_inclusion (U : TopologicalSpace.Opens E) :
    (manifoldSmoothOpenIso E U).inv ≫ ManifoldSmooth.manifoldSmoothInclusion E U =
      (SmoothOpen.subsetSmoothSingularSubcomplex (U : Set E)).ι :=
  SSet.Subcomplex.homOfLE_ι (manifoldSmoothSingularSubcomplex_open E U).symm.le

variable {R : Type} [Ring R]

/-- The manifold-smooth cochains on a normed space are the existing smooth
singular cochains, with their actual differentials. -/
def manifoldSmoothSelfCochainsIso (A : ModuleCat.{0} R) :
    ManifoldSmooth.manifoldSmoothCochains E A E ≅ Smooth.smoothSingularCochains A E :=
  (Functor.simplicialCochainsFunctor A).mapIso (manifoldSmoothSelfIso E).symm.op

/-- The manifold-smooth cochains on an open subset are the existing subset-smooth
cochains, with their actual differentials. -/
def manifoldSmoothOpenCochainsIso (U : TopologicalSpace.Opens E) (A : ModuleCat.{0} R) :
    ManifoldSmooth.manifoldSmoothCochains E A U ≅ SmoothOpen.subsetSmoothCochains A (U : Set E) :=
  (Functor.simplicialCochainsFunctor A).mapIso (manifoldSmoothOpenIso E U).symm.op

@[reassoc (attr := simp)]
theorem manifoldSmoothSelfCochainRestriction_iso_hom (A : ModuleCat.{0} R) :
    ManifoldSmooth.manifoldSmoothCochainRestriction E A E ≫ (manifoldSmoothSelfCochainsIso E A).hom =
      Smooth.smoothSingularCochainRestriction A E := by
  change Functor.simplicialPullback A (ManifoldSmooth.manifoldSmoothInclusion E E) ≫
      Functor.simplicialPullback A (manifoldSmoothSelfIso E).inv =
    Functor.simplicialPullback A (Smooth.smoothSingularInclusion E)
  rw [← Functor.simplicialPullback_comp, manifoldSmoothSelfIso_inv_inclusion]

@[reassoc (attr := simp)]
theorem manifoldSmoothOpenCochainRestriction_iso_hom (U : TopologicalSpace.Opens E)
    (A : ModuleCat.{0} R) :
    ManifoldSmooth.manifoldSmoothCochainRestriction E A U ≫ (manifoldSmoothOpenCochainsIso E U A).hom =
      SmoothOpen.subsetSmoothCochainRestriction A (U : Set E) := by
  change Functor.simplicialPullback A (ManifoldSmooth.manifoldSmoothInclusion E U) ≫
      Functor.simplicialPullback A (manifoldSmoothOpenIso E U).inv =
    Functor.simplicialPullback A (SmoothOpen.subsetSmoothSingularSubcomplex (U : Set E)).ι
  rw [← Functor.simplicialPullback_comp, manifoldSmoothOpenIso_inv_inclusion]

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothModels
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothModels"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.SmoothFunctor -/

/-! # Smooth Functor -/

namespace OAI.AlgebraicTopology.Cohomology.Singular

noncomputable section

/-!
# Functoriality of smooth singular simplices

A globally smooth map between real normed spaces postcomposes every smooth
singular simplex. The resulting simplicial map commutes with the actual
inclusion into the ordinary continuous singular simplicial set.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff

variable {E F G : Type}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Postcomposition by a globally smooth map preserves smooth simplex extensions. -/
theorem Smooth.IsSmoothSimplex.postcomp {n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)} (hσ : Smooth.IsSmoothSimplex σ)
    {f : E → F} (hf : ContDiff ℝ ∞ f) :
    Smooth.IsSmoothSimplex ((⟨f, hf.continuous⟩ : C(E, F)).comp σ) := by
  rcases hσ with ⟨σ', U, hU, hsub, hσ', heq⟩
  refine ⟨f ∘ σ', U, hU, hsub, hf.comp_contDiffOn hσ', ?_⟩
  intro x
  exact congrArg f (heq x)

/-- The simplicial map on smooth singular simplices induced by a smooth map. -/
def SmoothFunctor.smoothSingularMap (f : E → F) (hf : ContDiff ℝ ∞ f) :
    (Smooth.smoothSingularSubcomplex E).toSSet ⟶ (Smooth.smoothSingularSubcomplex F).toSSet where
  app n := ↾fun σ => ⟨(TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).app n σ.val, by
    change Smooth.IsSmoothSimplex ((TopCat.of F).toSSetObjEquiv n
      ((TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).app n σ.val))
    exact Smooth.IsSmoothSimplex.postcomp σ.property hf⟩
  naturality n m θ := by
    ext σ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).naturality θ) σ.val

/-- The smooth simplicial map is ordinary postcomposition on underlying simplices. -/
@[simp]
theorem SmoothFunctor.smoothSingularMap_app_val (f : E → F) (hf : ContDiff ℝ ∞ f)
    (n : SimplexCategoryᵒᵖ) (σ : (Smooth.smoothSingularSubcomplex E).obj n) :
    ((SmoothFunctor.smoothSingularMap f hf).app n σ).val =
      (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)).app n σ.val := rfl

/-- Evaluating the image simplex is pointwise postcomposition by the smooth map. -/
@[simp]
theorem SmoothFunctor.smoothSingularMap_apply (f : E → F) (hf : ContDiff ℝ ∞ f)
    (n : SimplexCategoryᵒᵖ) (σ : (Smooth.smoothSingularSubcomplex E).obj n)
    (x : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    (TopCat.of F).toSSetObjEquiv n ((SmoothFunctor.smoothSingularMap f hf).app n σ).val x =
      f ((TopCat.of E).toSSetObjEquiv n σ.val x) := rfl

/-- Inclusion of smooth simplices is natural with respect to smooth maps. -/
@[reassoc]
theorem SmoothFunctor.smoothSingularMap_inclusion (f : E → F) (hf : ContDiff ℝ ∞ f) :
    SmoothFunctor.smoothSingularMap f hf ≫ Smooth.smoothSingularInclusion F =
      Smooth.smoothSingularInclusion E ≫
        TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩) := rfl

@[simp]
theorem SmoothFunctor.smoothSingularMap_id :
    SmoothFunctor.smoothSingularMap (id : E → E) contDiff_id =
      𝟙 (Smooth.smoothSingularSubcomplex E).toSSet := by
  ext n σ
  apply Subtype.ext
  rfl

@[simp]
theorem SmoothFunctor.smoothSingularMap_comp (f : E → F) (hf : ContDiff ℝ ∞ f)
    (g : F → G) (hg : ContDiff ℝ ∞ g) :
    SmoothFunctor.smoothSingularMap (g ∘ f) (hg.comp hf) =
      SmoothFunctor.smoothSingularMap f hf ≫ SmoothFunctor.smoothSingularMap g hg := by
  ext n σ
  apply Subtype.ext
  rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.SmoothFunctor"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.SmoothHomotopy -/

/-! # Smooth Homotopy -/

namespace OAI.AlgebraicTopology.Cohomology.Singular

noncomputable section

/-!
# Linear contraction of smooth singular simplices

The interval parameter on an n-simplex is the sum of its barycentric coordinates
whose vertices map to 1. It extends to a continuous linear map on the ambient
coordinate space, so a straight-line contraction preserves the required smooth
extension to an open neighborhood of the closed simplex.
-/

open _root_.CategoryTheory Opposite MonoidalCategory
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine interval parameter associated to a map of simplex vertices. -/
def SmoothHomotopy.simplexTimeMap {n : ℕ} (τ : Fin (n + 1) → Fin 2) :
    (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (1 : Fin 2)).comp (Smooth.simplexLinearMap τ)

@[simp]
theorem SmoothHomotopy.simplexTimeMap_apply {n : ℕ} (τ : Fin (n + 1) → Fin 2)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    SmoothHomotopy.simplexTimeMap τ x = (Convexity.StdSimplex.map τ x) 1 :=
  congrArg (fun y : Fin 2 → ℝ => y 1) (Smooth.simplexLinearMap_weights τ x)

theorem SmoothHomotopy.simplexTimeMap_precomp {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1))
    (τ : Fin (n + 1) → Fin 2) (x : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    SmoothHomotopy.simplexTimeMap (τ ∘ θ) x = SmoothHomotopy.simplexTimeMap τ (Convexity.StdSimplex.map θ x) := by
  simp only [SmoothHomotopy.simplexTimeMap_apply, Convexity.StdSimplex.map_comp]

@[simp]
theorem SmoothHomotopy.simplexTimeMap_const_zero {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    SmoothHomotopy.simplexTimeMap (fun _ : Fin (n + 1) => (0 : Fin 2)) x = 0 := by
  rw [SmoothHomotopy.simplexTimeMap_apply, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.weights_map_sum]
  simp

@[simp]
theorem SmoothHomotopy.simplexTimeMap_const_one {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    SmoothHomotopy.simplexTimeMap (fun _ : Fin (n + 1) => (1 : Fin 2)) x = 1 := by
  rw [SmoothHomotopy.simplexTimeMap_apply, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.weights_map_sum]
  simp [Convexity.StdSimplex.total_of_fintype]

/-- The simplex obtained by contracting a simplex linearly toward `c`, with
its interval coordinate prescribed by the vertex map `τ`. -/
def SmoothHomotopy.linearContractionSimplex {n : ℕ} (c : E)
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)) (τ : Fin (n + 1) → Fin 2) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), E) where
  toFun x := (1 - SmoothHomotopy.simplexTimeMap τ x) • σ x + SmoothHomotopy.simplexTimeMap τ x • c
  continuous_toFun := by
    have hc : Continuous (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        (x : Fin (n + 1) → ℝ)) :=
      (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous
    exact ((continuous_const.sub ((SmoothHomotopy.simplexTimeMap τ).continuous.comp hc)).smul
      σ.continuous).add (((SmoothHomotopy.simplexTimeMap τ).continuous.comp hc).smul continuous_const)

/-- The contraction extends smoothly on the same open neighborhood as `σ`. -/
theorem Smooth.IsSmoothSimplex.linearContraction {n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)} (hσ : Smooth.IsSmoothSimplex σ)
    (c : E) (τ : Fin (n + 1) → Fin 2) :
    Smooth.IsSmoothSimplex (SmoothHomotopy.linearContractionSimplex c σ τ) := by
  rcases hσ with ⟨F, U, hU, hsub, hF, heq⟩
  refine ⟨fun x => (1 - SmoothHomotopy.simplexTimeMap τ x) • F x + SmoothHomotopy.simplexTimeMap τ x • c,
    U, hU, hsub, ?_, ?_⟩
  · exact ((contDiffOn_const.sub (SmoothHomotopy.simplexTimeMap τ).contDiff.contDiffOn).smul hF).add
      ((SmoothHomotopy.simplexTimeMap τ).contDiff.contDiffOn.smul_const c)
  · intro x
    change (1 - SmoothHomotopy.simplexTimeMap τ x) • F x + SmoothHomotopy.simplexTimeMap τ x • c =
      (1 - SmoothHomotopy.simplexTimeMap τ x) • σ x + SmoothHomotopy.simplexTimeMap τ x • c
    rw [heq x]

/-- Simplicial naturality of the explicit contraction formula. -/
theorem SmoothHomotopy.linearContractionSimplex_precomp {m n : ℕ} (c : E)
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E))
    (θ : Fin (m + 1) → Fin (n + 1)) (τ : Fin (n + 1) → Fin 2) :
    SmoothHomotopy.linearContractionSimplex c (σ.comp ⟨Convexity.StdSimplex.map θ, Convexity.StdSimplex.continuous_map ℝ θ⟩)
        (τ ∘ θ) =
      (SmoothHomotopy.linearContractionSimplex c σ τ).comp
        ⟨Convexity.StdSimplex.map θ, Convexity.StdSimplex.continuous_map ℝ θ⟩ := by
  ext x
  change (1 - SmoothHomotopy.simplexTimeMap (τ ∘ θ) x) • σ (Convexity.StdSimplex.map θ x) +
      SmoothHomotopy.simplexTimeMap (τ ∘ θ) x • c =
    (1 - SmoothHomotopy.simplexTimeMap τ (Convexity.StdSimplex.map θ x)) • σ (Convexity.StdSimplex.map θ x) +
      SmoothHomotopy.simplexTimeMap τ (Convexity.StdSimplex.map θ x) • c
  rw [SmoothHomotopy.simplexTimeMap_precomp]

@[simp]
theorem SmoothHomotopy.linearContractionSimplex_zero {n : ℕ} (c : E)
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)) :
    SmoothHomotopy.linearContractionSimplex c σ (fun _ => 0) = σ := by
  ext x
  change (1 - SmoothHomotopy.simplexTimeMap (fun _ => 0) x) • σ x +
    SmoothHomotopy.simplexTimeMap (fun _ => 0) x • c = σ x
  rw [SmoothHomotopy.simplexTimeMap_const_zero]
  simp

@[simp]
theorem SmoothHomotopy.linearContractionSimplex_one {n : ℕ} (c : E)
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)) :
    SmoothHomotopy.linearContractionSimplex c σ (fun _ => 1) = ContinuousMap.const _ c := by
  ext x
  change (1 - SmoothHomotopy.simplexTimeMap (fun _ => 1) x) • σ x +
    SmoothHomotopy.simplexTimeMap (fun _ => 1) x • c = c
  rw [SmoothHomotopy.simplexTimeMap_const_one]
  simp

/-- The linear contraction as an actual morphism from the simplicial cylinder
of smooth singular simplices to smooth singular simplices. -/
def SmoothHomotopy.smoothContractionMap (c : E) :
    (Smooth.smoothSingularSubcomplex E).toSSet ⊗ Δ[1] ⟶
      (Smooth.smoothSingularSubcomplex E).toSSet where
  app n := ↾fun p => ⟨((TopCat.of E).toSSetObjEquiv n).symm
      (SmoothHomotopy.linearContractionSimplex c ((TopCat.of E).toSSetObjEquiv n p.1.val)
        (SSet.stdSimplex.asOrderHom p.2)), by
    change Smooth.IsSmoothSimplex _
    simp only [Equiv.apply_symm_apply]
    exact Smooth.IsSmoothSimplex.linearContraction p.1.property c _⟩
  naturality n m θ := by
    apply ConcreteCategory.ext_apply
    intro p
    apply Subtype.ext
    apply ((TopCat.of E).toSSetObjEquiv m).injective
    change SmoothHomotopy.linearContractionSimplex c
        (((TopCat.of E).toSSetObjEquiv n p.1.val).comp
          ⟨Convexity.StdSimplex.map θ.unop, Convexity.StdSimplex.continuous_map ℝ θ.unop⟩)
        ((SSet.stdSimplex.asOrderHom p.2) ∘ θ.unop) =
      (SmoothHomotopy.linearContractionSimplex c ((TopCat.of E).toSSetObjEquiv n p.1.val)
        (SSet.stdSimplex.asOrderHom p.2)).comp
          ⟨Convexity.StdSimplex.map θ.unop, Convexity.StdSimplex.continuous_map ℝ θ.unop⟩
    exact SmoothHomotopy.linearContractionSimplex_precomp c _ _ _

/-- The identity on smooth singular simplices is genuinely simplicially
homotopic to the map induced by the constant smooth map with value `c`. -/
def SmoothHomotopy.smoothLinearContraction (c : E) :
    SSet.Homotopy (𝟙 (Smooth.smoothSingularSubcomplex E).toSSet)
      (SmoothFunctor.smoothSingularMap (fun _ : E => c) contDiff_const) where
  h := SmoothHomotopy.smoothContractionMap c
  h₀ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.ext_apply
    intro p
    apply Subtype.ext
    apply ((TopCat.of E).toSSetObjEquiv n).injective
    change SmoothHomotopy.linearContractionSimplex c ((TopCat.of E).toSSetObjEquiv n p.val)
      (fun _ => 0) = _
    exact SmoothHomotopy.linearContractionSimplex_zero c _
  h₁ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.ext_apply
    intro p
    apply Subtype.ext
    apply ((TopCat.of E).toSSetObjEquiv n).injective
    change SmoothHomotopy.linearContractionSimplex c ((TopCat.of E).toSSetObjEquiv n p.val)
      (fun _ => 1) = _
    exact SmoothHomotopy.linearContractionSimplex_one c _
  rel := by ext _ ⟨⟨_, ⟨⟩⟩, _⟩

end

end OAI.AlgebraicTopology.Cohomology.Singular
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.SmoothHomotopy"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.Contractible -/

/-! # Contractible -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Contractible

noncomputable section

/-!
# Positive-degree singular cohomology of contractible spaces

These are statements about the genuine singular cochain complex. The proof
uses mathlib's computation for totally disconnected spaces, followed by the
proved invariance under continuous homotopy equivalences. Contractibility is
mathlib's actual homotopy equivalence to a one-point space.

For positive-degree cocycles this gives an actual lower-degree singular
cochain whose coboundary is the original cocycle. Convex and star-convex
specializations use the existing continuous straight-line contractions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable {R : Type} [Ring R]

/-- Positive-degree singular cohomology vanishes for totally disconnected
spaces, by the corresponding general homology computation in the opposite
category of modules. -/
theorem isZero_singularCohomology_of_totallyDisconnected (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [TotallyDisconnectedSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (Basic.singularCohomology M X n) := by
  have h := AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} R)ᵒᵖ n (op M) X hn
  exact h.unop.of_iso (Basic.singularCohomologyOppositeIso M X n)

/-- An actual homotopy equivalence to the one-point space implies vanishing
of positive-degree singular cohomology. -/
theorem isZero_singularCohomology_of_homotopyEquiv_unit (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (e : ContinuousMap.HomotopyEquiv X Unit)
    (n : ℕ) (hn : n ≠ 0) : IsZero (Basic.singularCohomology M X n) :=
  (isZero_singularCohomology_of_totallyDisconnected M (TopCat.of Unit) n hn).of_iso
    (Homotopy.singularCohomologyIsoOfHomotopyEquiv M (Y := TopCat.of Unit) e n).symm

/-- Positive-degree singular cohomology vanishes on every contractible space. -/
theorem isZero_singularCohomology_of_contractible (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (Basic.singularCohomology M X n) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  exact isZero_singularCohomology_of_homotopyEquiv_unit M X e n hn

/-- Elementwise version of contractible-space vanishing. -/
theorem singularCohomology_eq_zero_of_contractible (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0)
    (c : Basic.singularCohomology M X n) : c = 0 := by
  let := ModuleCat.subsingleton_of_isZero
    (isZero_singularCohomology_of_contractible M X n hn)
  exact Subsingleton.elim c 0

/-- The genuine singular cochain complex of a contractible space is exact
in every positive degree. -/
theorem singularCochains_exactAt_of_contractible (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    (Basic.singularCochains M X).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact isZero_singularCohomology_of_contractible M X n hn

/-- Every positive-degree singular cocycle on a contractible space admits a
singular cochain primitive. -/
theorem exists_singularPrimitive_of_contractible (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ)
    (c : Representatives.singularCocycles M X (n + 1)) :
    ∃ b : (Basic.singularCochains M X).X n,
      ((Basic.singularCochains M X).d n (n + 1)) b = c.1 := by
  have h : Representatives.singularClass M X (n + 1) c = Representatives.singularClass M X (n + 1) 0 := by
    rw [map_zero]
    exact singularCohomology_eq_zero_of_contractible M X (n + 1) (Nat.succ_ne_zero n) _
  simpa using (Representatives.singularClass_eq_iff_exists_succ M X n c 0).mp h

section RealTopologicalVectorSpace

variable {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- Positive-degree singular cohomology vanishes on nonempty star-convex sets. -/
theorem isZero_singularCohomology_of_starConvex (M : ModuleCat.{0} R)
    {s : Set E} {x : E} (hs : StarConvex ℝ x s) (hne : s.Nonempty)
    (n : ℕ) (hn : n ≠ 0) : IsZero (Basic.singularCohomology M (TopCat.of s) n) := by
  let : ContractibleSpace s := hs.contractibleSpace hne
  exact isZero_singularCohomology_of_contractible M (TopCat.of s) n hn

/-- Positive-degree singular cohomology vanishes on nonempty convex sets. -/
theorem isZero_singularCohomology_of_convex (M : ModuleCat.{0} R)
    {s : Set E} (hs : Convex ℝ s) (hne : s.Nonempty)
    (n : ℕ) (hn : n ≠ 0) : IsZero (Basic.singularCohomology M (TopCat.of s) n) := by
  let : ContractibleSpace s := hs.contractibleSpace hne
  exact isZero_singularCohomology_of_contractible M (TopCat.of s) n hn

/-- Singular cocycles of positive degree on a nonempty convex set have
singular cochain primitives. -/
theorem exists_singularPrimitive_of_convex (M : ModuleCat.{0} R)
    {s : Set E} (hs : Convex ℝ s) (hne : s.Nonempty) (n : ℕ)
    (c : Representatives.singularCocycles M (TopCat.of s) (n + 1)) :
    ∃ b : (Basic.singularCochains M (TopCat.of s)).X n,
      ((Basic.singularCochains M (TopCat.of s)).d n (n + 1)) b = c.1 := by
  let : ContractibleSpace s := hs.contractibleSpace hne
  exact exists_singularPrimitive_of_contractible M (TopCat.of s) n c

end RealTopologicalVectorSpace

/-- In particular, every positive-radius open ball in a real normed vector
space has vanishing singular cohomology in positive degrees. -/
theorem isZero_singularCohomology_ball (M : ModuleCat.{0} R)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (r : ℝ) (hr : 0 < r) (n : ℕ) (hn : n ≠ 0) :
    IsZero (Basic.singularCohomology M (TopCat.of (Metric.ball x r)) n) :=
  isZero_singularCohomology_of_convex M (convex_ball x r)
    ⟨x, Metric.mem_ball_self hr⟩ n hn

end

end OAI.AlgebraicTopology.Cohomology.Singular.Contractible
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.Contractible"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.SmoothComparison -/

/-! # Smooth Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmoothComparison

noncomputable section

/-!
# Smooth-versus-continuous singular comparison on a normed space

For a real normed vector space, the actual inclusion of smooth singular
simplices into continuous singular simplices is a chain homotopy equivalence.
Its inverse up to homotopy is the constant simplicial map at a chosen point.
The two composites are contracted using genuine simplicial homotopies.

This proves a local comparison theorem on normed model spaces; it does not
assert a global smoothing theorem on arbitrary manifolds.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The constant smooth zero-simplex at a selected point. -/
def smoothPointSimplex (c : E) : (Smooth.smoothSingularSubcomplex E).toSSet _⦋0⦌ :=
  ⟨((TopCat.of E).toSSetObjEquiv _).symm (ContinuousMap.const _ c), by
    change Smooth.IsSmoothSimplex _
    simp only [Equiv.apply_symm_apply]
    exact Smooth.isSmoothSimplex_const 0 c⟩

/-- A simplicial inverse to the smooth inclusion, up to homotopy. It sends
all simplices to the constant smooth simplex at `c`. -/
def smoothComparisonRetraction (c : E) :
    TopCat.toSSet.obj (TopCat.of E) ⟶ (Smooth.smoothSingularSubcomplex E).toSSet :=
  SSet.const (smoothPointSimplex c)

theorem smoothInclusion_retraction (c : E) :
    Smooth.smoothSingularInclusion E ≫ smoothComparisonRetraction c =
      SmoothFunctor.smoothSingularMap (fun _ : E => c) contDiff_const := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.ext_apply
  intro σ
  apply Subtype.ext
  apply ((TopCat.of E).toSSetObjEquiv n).injective
  ext x
  rfl

theorem smoothRetraction_inclusion (c : E) :
    smoothComparisonRetraction c ≫ Smooth.smoothSingularInclusion E =
      TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const E c)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.ext_apply
  intro σ
  apply ((TopCat.of E).toSSetObjEquiv n).injective
  ext x
  rfl

/-- The ordinary continuous linear contraction of a normed vector space. -/
def continuousLinearContraction (c : E) :
    TopCat.Homotopy (𝟙 (TopCat.of E))
      (TopCat.ofHom (ContinuousMap.const E c)) where
  toFun p := (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • c
  continuous_toFun := by fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

/-- The smooth composite is simplicially homotopic to the identity. -/
def smoothComparisonHomotopy (c : E) :
    SSet.Homotopy (𝟙 (Smooth.smoothSingularSubcomplex E).toSSet)
      (Smooth.smoothSingularInclusion E ≫ smoothComparisonRetraction c) := by
  rw [smoothInclusion_retraction]
  exact SmoothHomotopy.smoothLinearContraction c

/-- The continuous composite is simplicially homotopic to the identity. -/
def continuousComparisonHomotopy (c : E) :
    SSet.Homotopy (𝟙 (TopCat.toSSet.obj (TopCat.of E)))
      (smoothComparisonRetraction c ≫ Smooth.smoothSingularInclusion E) := by
  rw [smoothRetraction_inclusion]
  have h := (continuousLinearContraction c).toSSet
  rw [TopCat.toSSet.map_id] at h
  exact h

variable {R : Type} [Ring R]

/-- The genuine smooth-to-continuous chain inclusion is a chain homotopy
equivalence on every real normed vector space. -/
def smoothChainComparisonHomotopyEquiv (M : ModuleCat.{0} R) (c : E) :
    _root_.HomotopyEquiv (Smooth.smoothSingularChains M E)
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex M) where
  hom := Smooth.smoothSingularChainInclusion M E
  inv := SSet.chainComplexMap (smoothComparisonRetraction c) M
  homotopyHomInvId := by
    have H := ((smoothComparisonHomotopy c).chainComplexMap M).symm
    dsimp only [SSet.chainComplexMap] at H
    rw [((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj M).map_id,
      ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj M).map_comp] at H
    exact H
  homotopyInvHomId := by
    have H := ((continuousComparisonHomotopy c).chainComplexMap M).symm
    dsimp only [SSet.chainComplexMap] at H
    rw [((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj M).map_id,
      ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj M).map_comp] at H
    exact H

/-- The existing restriction is the simplicial pullback along the actual inclusion. -/
theorem smoothRestriction_eq_simplicialPullback (M : ModuleCat.{0} R) :
    Smooth.smoothSingularCochainRestriction M E =
      Functor.simplicialPullback M (Smooth.smoothSingularInclusion E) := rfl

/-- Restriction to the smooth singular simplices is a cochain homotopy
equivalence on every real normed vector space. -/
def smoothCochainComparisonHomotopyEquiv (M : ModuleCat.{0} R) (c : E) :
    _root_.HomotopyEquiv (Basic.singularCochains M (TopCat.of E))
      (Smooth.smoothSingularCochains M E) where
  hom := Smooth.smoothSingularCochainRestriction M E
  inv := Functor.simplicialPullback M (smoothComparisonRetraction c)
  homotopyHomInvId := by
    simpa only [Functor.simplicialPullback_comp, Functor.simplicialPullback_id,
      smoothRestriction_eq_simplicialPullback] using
      (Singular.Homotopy.simplicialPullbackHomotopy M (continuousComparisonHomotopy c)).symm
  homotopyInvHomId := by
    simpa only [Functor.simplicialPullback_comp, Functor.simplicialPullback_id,
      smoothRestriction_eq_simplicialPullback] using
      (Singular.Homotopy.simplicialPullbackHomotopy M (smoothComparisonHomotopy c)).symm

/-- Actual cohomology comparison induced by restriction to smooth simplices. -/
def smoothCohomologyComparisonIso (M : ModuleCat.{0} R) (c : E) (n : ℕ) :
    Basic.singularCohomology M (TopCat.of E) n ≅ (Smooth.smoothSingularCochains M E).homology n :=
  (smoothCochainComparisonHomotopyEquiv M c).toHomologyIso n

/-- The forward comparison map is precisely the map on cohomology induced by
the already defined smooth-simplex restriction, not an arbitrarily chosen iso. -/
@[simp]
theorem smoothCohomologyComparisonIso_hom (M : ModuleCat.{0} R) (c : E) (n : ℕ) :
    (smoothCohomologyComparisonIso M c n).hom =
      HomologicalComplex.homologyMap (Smooth.smoothSingularCochainRestriction M E) n := rfl

/-- The actual restriction map induces isomorphisms in every cohomological degree. -/
theorem isIso_smoothCohomologyRestriction (M : ModuleCat.{0} R) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Smooth.smoothSingularCochainRestriction M E) n) := by
  change IsIso (smoothCohomologyComparisonIso M (0 : E) n).hom
  infer_instance

/-- Positive-degree smooth singular cohomology vanishes on real normed spaces. -/
theorem isZero_smoothSingularCohomology (M : ModuleCat.{0} R) (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero ((Smooth.smoothSingularCochains M E).homology n) :=
  (Contractible.isZero_singularCohomology_of_contractible M (TopCat.of E) n hn).of_iso
    (smoothCohomologyComparisonIso M (0 : E) n).symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmoothComparison
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.SmoothComparison"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.SmoothConvexComparison -/

/-! # Smooth Convex Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular

noncomputable section

/-!
# Smooth singular comparison on nonempty convex domains

The affine contraction stays inside a convex domain and has the previously
proved ambient smooth extension. Consequently the actual restriction from
continuous to smooth singular cochains is a cochain homotopy equivalence.
-/

open _root_.CategoryTheory Opposite MonoidalCategory
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : Set E}

/-- The affine interval coordinate lies in the closed unit interval. -/
theorem SmoothConvexComparison.simplexTimeMap_mem_Icc {n : ℕ} (τ : Fin (n + 1) → Fin 2)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) : SmoothHomotopy.simplexTimeMap τ x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [SmoothHomotopy.simplexTimeMap_apply]
  exact ⟨Convexity.StdSimplex.weights_nonneg (w := Convexity.StdSimplex.map τ x) 1,
    Convexity.StdSimplex.weights_apply_le_one (Convexity.StdSimplex.map τ x) 1⟩

/-- The subset-valued affine contraction of a simplex in a convex set. -/
def SmoothConvexComparison.convexContractionSimplex (hU : Convex ℝ U) (c : U) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) (τ : Fin (n + 1) → Fin 2) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), U) where
  toFun x := ⟨SmoothHomotopy.linearContractionSimplex (c : E) ((SmoothOpen.normedSubsetInclusion U).hom.comp σ) τ x,
    hU (σ x).property c.property (sub_nonneg.mpr (SmoothConvexComparison.simplexTimeMap_mem_Icc τ x).2)
      (SmoothConvexComparison.simplexTimeMap_mem_Icc τ x).1 (sub_add_cancel 1 _)⟩
  continuous_toFun :=
    (SmoothHomotopy.linearContractionSimplex (c : E) ((SmoothOpen.normedSubsetInclusion U).hom.comp σ) τ).continuous.subtype_mk _

/-- The subset contraction has exactly the known ambient smooth formula. -/
theorem SmoothConvexComparison.convexContractionSimplex_ambient (hU : Convex ℝ U) (c : U) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) (τ : Fin (n + 1) → Fin 2) :
    (SmoothOpen.normedSubsetInclusion U).hom.comp (SmoothConvexComparison.convexContractionSimplex hU c σ τ) =
      SmoothHomotopy.linearContractionSimplex (c : E) ((SmoothOpen.normedSubsetInclusion U).hom.comp σ) τ := rfl

/-- Affine contraction preserves the actual ambient smooth extension condition. -/
theorem SmoothOpen.IsSmoothSimplexIn.convexContraction (hU : Convex ℝ U) (c : U) {n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)} (hσ : SmoothOpen.IsSmoothSimplexIn U σ)
    (τ : Fin (n + 1) → Fin 2) :
    SmoothOpen.IsSmoothSimplexIn U (SmoothConvexComparison.convexContractionSimplex hU c σ τ) :=
  hσ.linearContraction (c : E) τ

theorem SmoothConvexComparison.convexContractionSimplex_precomp (hU : Convex ℝ U) (c : U) {m n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U))
    (θ : Fin (m + 1) → Fin (n + 1)) (τ : Fin (n + 1) → Fin 2) :
    SmoothConvexComparison.convexContractionSimplex hU c
        (σ.comp ⟨Convexity.StdSimplex.map θ, Convexity.StdSimplex.continuous_map ℝ θ⟩) (τ ∘ θ) =
      (SmoothConvexComparison.convexContractionSimplex hU c σ τ).comp
        ⟨Convexity.StdSimplex.map θ, Convexity.StdSimplex.continuous_map ℝ θ⟩ := by
  ext x
  exact congrArg (fun f : C(Convexity.StdSimplex ℝ (Fin (m + 1)), E) => f x)
    (SmoothHomotopy.linearContractionSimplex_precomp (c : E) ((SmoothOpen.normedSubsetInclusion U).hom.comp σ) θ τ)

@[simp]
theorem SmoothConvexComparison.convexContractionSimplex_zero (hU : Convex ℝ U) (c : U) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) :
    SmoothConvexComparison.convexContractionSimplex hU c σ (fun _ => 0) = σ := by
  ext x
  change SmoothHomotopy.linearContractionSimplex (c : E) ((SmoothOpen.normedSubsetInclusion U).hom.comp σ)
    (fun _ => 0) x = (σ x).val
  rw [SmoothHomotopy.linearContractionSimplex_zero]
  rfl

@[simp]
theorem SmoothConvexComparison.convexContractionSimplex_one (hU : Convex ℝ U) (c : U) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) :
    SmoothConvexComparison.convexContractionSimplex hU c σ (fun _ => 1) = ContinuousMap.const _ c := by
  ext x
  change SmoothHomotopy.linearContractionSimplex (c : E) ((SmoothOpen.normedSubsetInclusion U).hom.comp σ)
    (fun _ => 1) x = c.val
  rw [SmoothHomotopy.linearContractionSimplex_one]
  rfl

/-- The constant smooth zero-simplex in an arbitrary subset. -/
def SmoothConvexComparison.subsetSmoothPointSimplex (c : U) :
    (SmoothOpen.subsetSmoothSingularSubcomplex U).toSSet _⦋0⦌ :=
  ⟨((TopCat.of U).toSSetObjEquiv _).symm (ContinuousMap.const _ c), by
    change Smooth.IsSmoothSimplex (ContinuousMap.const _ (c : E))
    exact Smooth.isSmoothSimplex_const 0 (c : E)⟩

/-- Constant simplicial inverse, up to homotopy, for a convex-domain inclusion. -/
def SmoothConvexComparison.subsetSmoothComparisonRetraction (c : U) :
    TopCat.toSSet.obj (TopCat.of U) ⟶ (SmoothOpen.subsetSmoothSingularSubcomplex U).toSSet :=
  SSet.const (SmoothConvexComparison.subsetSmoothPointSimplex c)

/-- The affine contraction as a morphism from the smooth simplicial cylinder. -/
def SmoothConvexComparison.convexSmoothContractionMap (hU : Convex ℝ U) (c : U) :
    (SmoothOpen.subsetSmoothSingularSubcomplex U).toSSet ⊗ Δ[1] ⟶
      (SmoothOpen.subsetSmoothSingularSubcomplex U).toSSet where
  app n := ↾fun p => ⟨((TopCat.of U).toSSetObjEquiv n).symm
      (SmoothConvexComparison.convexContractionSimplex hU c ((TopCat.of U).toSSetObjEquiv n p.1.val)
        (SSet.stdSimplex.asOrderHom p.2)), by
    change SmoothOpen.IsSmoothSimplexIn U
      (SmoothConvexComparison.convexContractionSimplex hU c ((TopCat.of U).toSSetObjEquiv n p.1.val)
        (SSet.stdSimplex.asOrderHom p.2))
    exact SmoothOpen.IsSmoothSimplexIn.convexContraction hU c
      (σ := (TopCat.of U).toSSetObjEquiv n p.1.val) p.1.property _⟩
  naturality n m θ := by
    apply ConcreteCategory.ext_apply
    intro p
    apply Subtype.ext
    apply ((TopCat.of U).toSSetObjEquiv m).injective
    change SmoothConvexComparison.convexContractionSimplex hU c
        (((TopCat.of U).toSSetObjEquiv n p.1.val).comp
          ⟨Convexity.StdSimplex.map θ.unop, Convexity.StdSimplex.continuous_map ℝ θ.unop⟩)
        ((SSet.stdSimplex.asOrderHom p.2) ∘ θ.unop) =
      (SmoothConvexComparison.convexContractionSimplex hU c ((TopCat.of U).toSSetObjEquiv n p.1.val)
        (SSet.stdSimplex.asOrderHom p.2)).comp
          ⟨Convexity.StdSimplex.map θ.unop, Convexity.StdSimplex.continuous_map ℝ θ.unop⟩
    exact SmoothConvexComparison.convexContractionSimplex_precomp hU c _ _ _

/-- The smooth-side composite is simplicially homotopic to identity. -/
def SmoothConvexComparison.convexSmoothComparisonHomotopy (hU : Convex ℝ U) (c : U) :
    SSet.Homotopy (𝟙 (SmoothOpen.subsetSmoothSingularSubcomplex U).toSSet)
      ((SmoothOpen.subsetSmoothSingularSubcomplex U).ι ≫ SmoothConvexComparison.subsetSmoothComparisonRetraction c) where
  h := SmoothConvexComparison.convexSmoothContractionMap hU c
  h₀ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.ext_apply
    intro p
    apply Subtype.ext
    apply ((TopCat.of U).toSSetObjEquiv n).injective
    change SmoothConvexComparison.convexContractionSimplex hU c ((TopCat.of U).toSSetObjEquiv n p.val)
      (fun _ => 0) = _
    exact SmoothConvexComparison.convexContractionSimplex_zero hU c _
  h₁ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.ext_apply
    intro p
    apply Subtype.ext
    apply ((TopCat.of U).toSSetObjEquiv n).injective
    change SmoothConvexComparison.convexContractionSimplex hU c ((TopCat.of U).toSSetObjEquiv n p.val)
      (fun _ => 1) = ContinuousMap.const _ c
    exact SmoothConvexComparison.convexContractionSimplex_one hU c _
  rel := by ext _ ⟨⟨_, ⟨⟩⟩, _⟩

/-- Ordinary continuous affine contraction inside the convex domain. -/
def SmoothConvexComparison.convexContinuousContraction (hU : Convex ℝ U) (c : U) :
    TopCat.Homotopy (𝟙 (TopCat.of U))
      (TopCat.ofHom (ContinuousMap.const U c)) where
  toFun p := ⟨(1 - (p.1 : ℝ)) • (p.2 : E) + (p.1 : ℝ) • (c : E),
    hU p.2.property c.property (sub_nonneg.mpr p.1.property.2)
      p.1.property.1 (sub_add_cancel 1 _)⟩
  continuous_toFun := by fun_prop
  map_zero_left x := by apply Subtype.ext; simp
  map_one_left x := by apply Subtype.ext; simp

theorem SmoothConvexComparison.subsetSmoothRetraction_inclusion (c : U) :
    SmoothConvexComparison.subsetSmoothComparisonRetraction c ≫ (SmoothOpen.subsetSmoothSingularSubcomplex U).ι =
      TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const U c)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.ext_apply
  intro σ
  apply ((TopCat.of U).toSSetObjEquiv n).injective
  ext x
  rfl

/-- The continuous-side composite is simplicially homotopic to identity. -/
def SmoothConvexComparison.convexContinuousComparisonHomotopy (hU : Convex ℝ U) (c : U) :
    SSet.Homotopy (𝟙 (TopCat.toSSet.obj (TopCat.of U)))
      (SmoothConvexComparison.subsetSmoothComparisonRetraction c ≫ (SmoothOpen.subsetSmoothSingularSubcomplex U).ι) := by
  rw [SmoothConvexComparison.subsetSmoothRetraction_inclusion]
  have h := (SmoothConvexComparison.convexContinuousContraction hU c).toSSet
  rw [TopCat.toSSet.map_id] at h
  exact h

variable {R : Type} [Ring R]

/-- The actual smooth-simplex restriction on a convex domain is a cochain
homotopy equivalence. -/
def SmoothConvexComparison.convexSmoothCochainComparisonHomotopyEquiv (M : ModuleCat.{0} R)
    (hU : Convex ℝ U) (c : U) :
    _root_.HomotopyEquiv (Basic.singularCochains M (TopCat.of U)) (SmoothOpen.subsetSmoothCochains M U) where
  hom := SmoothOpen.subsetSmoothCochainRestriction M U
  inv := Functor.simplicialPullback M (SmoothConvexComparison.subsetSmoothComparisonRetraction c)
  homotopyHomInvId := by
    simpa only [Functor.simplicialPullback_comp, Functor.simplicialPullback_id,
      SmoothOpen.subsetSmoothCochainRestriction] using
      (Singular.Homotopy.simplicialPullbackHomotopy M (SmoothConvexComparison.convexContinuousComparisonHomotopy hU c)).symm
  homotopyInvHomId := by
    simpa only [Functor.simplicialPullback_comp, Functor.simplicialPullback_id,
      SmoothOpen.subsetSmoothCochainRestriction] using
      (Singular.Homotopy.simplicialPullbackHomotopy M (SmoothConvexComparison.convexSmoothComparisonHomotopy hU c)).symm

/-- Genuine smooth-versus-continuous cohomology comparison on a convex domain. -/
def SmoothConvexComparison.convexSmoothCohomologyComparisonIso (M : ModuleCat.{0} R)
    (hU : Convex ℝ U) (c : U) (n : ℕ) :
    Basic.singularCohomology M (TopCat.of U) n ≅ (SmoothOpen.subsetSmoothCochains M U).homology n :=
  (SmoothConvexComparison.convexSmoothCochainComparisonHomotopyEquiv M hU c).toHomologyIso n

@[simp]
theorem SmoothConvexComparison.convexSmoothCohomologyComparisonIso_hom (M : ModuleCat.{0} R)
    (hU : Convex ℝ U) (c : U) (n : ℕ) :
    (SmoothConvexComparison.convexSmoothCohomologyComparisonIso M hU c n).hom =
      HomologicalComplex.homologyMap (SmoothOpen.subsetSmoothCochainRestriction M U) n := rfl

/-- Restriction induces an isomorphism in every degree on a nonempty convex
domain, including every nonempty convex open domain. -/
theorem SmoothConvexComparison.isIso_convexSmoothCohomologyRestriction (M : ModuleCat.{0} R)
    (hU : Convex ℝ U) (hne : U.Nonempty) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (SmoothOpen.subsetSmoothCochainRestriction M U) n) := by
  let c : U := ⟨hne.choose, hne.choose_spec⟩
  change IsIso (SmoothConvexComparison.convexSmoothCohomologyComparisonIso M hU c n).hom
  infer_instance

end

end OAI.AlgebraicTopology.Cohomology.Singular
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.SmoothConvexComparison"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.ChartBalls -/

/-! # Chart Balls -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ChartBalls

noncomputable section

/-!
# Chart balls and local singular cohomology

For a space charted on a real normed vector space, balls contained in a
chart target pull back to a neighborhood basis. Each such domain is
explicitly homeomorphic to the model ball. Positive-radius chart balls are
therefore contractible and have vanishing positive-degree singular
cohomology. Only the actual charted-space topology is used here; these
results in particular apply to smooth manifolds without boundary.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Filter
open scoped _root_.Topology

variable (E : Type) [NormedAddCommGroup E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]

/-- The part of a chart source whose chart coordinates lie in a ball
centered at the coordinates of the chosen point. -/
def chartBallDomain (x : X) (r : ℝ) : Set X :=
  (chartAt E x).source ∩ (chartAt E x) ⁻¹' Metric.ball (chartAt E x x) r

@[simp]
theorem mem_chartBallDomain (x y : X) (r : ℝ) :
    y ∈ chartBallDomain E x r ↔
      y ∈ (chartAt E x).source ∧ chartAt E x y ∈ Metric.ball (chartAt E x x) r :=
  Iff.rfl

theorem isOpen_chartBallDomain (x : X) (r : ℝ) :
    IsOpen (chartBallDomain E x r) :=
  (chartAt E x).isOpen_inter_preimage Metric.isOpen_ball

/-- A chart ball as an actual open subspace of the original topological
space. This carries the canonical open-submanifold chart structure. -/
def chartBallOpen (x : X) (r : ℝ) : TopologicalSpace.Opens X :=
  ⟨chartBallDomain E x r, isOpen_chartBallDomain E x r⟩

@[simp]
theorem coe_chartBallOpen (x : X) (r : ℝ) :
    (chartBallOpen E x r : Set X) = chartBallDomain E x r :=
  rfl

@[simp]
theorem mem_chartBallOpen (x y : X) (r : ℝ) :
    y ∈ chartBallOpen E x r ↔
      y ∈ (chartAt E x).source ∧ chartAt E x y ∈ Metric.ball (chartAt E x x) r :=
  Iff.rfl

theorem mem_chartBallDomain_self (x : X) {r : ℝ} (hr : 0 < r) :
    x ∈ chartBallDomain E x r :=
  ⟨mem_chart_source E x, Metric.mem_ball_self hr⟩

theorem chartBallDomain_mem_nhds (x : X) {r : ℝ} (hr : 0 < r) :
    chartBallDomain E x r ∈ 𝓝 x :=
  (isOpen_chartBallDomain E x r).mem_nhds (mem_chartBallDomain_self E x hr)

theorem chartBallDomain_mono (x : X) {r s : ℝ} (hrs : r ≤ s) :
    chartBallDomain E x r ⊆ chartBallDomain E x s := by
  intro y hy
  exact ⟨hy.1, Metric.ball_subset_ball hrs hy.2⟩

/-- The chart maps an admissible chart-ball domain onto the entire model
ball, not merely into it. -/
theorem chart_image_chartBallDomain (x : X) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    chartAt E x '' chartBallDomain E x r = Metric.ball (chartAt E x x) r := by
  change chartAt E x '' ((chartAt E x).source ∩
    (chartAt E x) ⁻¹' Metric.ball (chartAt E x x) r) = _
  rw [← (chartAt E x).symm_image_eq_source_inter_preimage htarget]
  exact (chartAt E x).image_symm_image_of_subset_target htarget

/-- Restricting the actual chart gives a homeomorphism from an admissible
open chart-ball domain to the corresponding ball in the model space. -/
def chartBallHomeomorph (x : X) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    chartBallOpen E x r ≃ₜ Metric.ball (chartAt E x x) r :=
  (chartAt E x).homeomorphOfImageSubsetSource Set.inter_subset_left
    (chart_image_chartBallDomain E x r htarget)

@[simp]
theorem chartBallHomeomorph_coe_apply (x : X) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target)
    (y : chartBallOpen E x r) :
    (chartBallHomeomorph E x r htarget y : E) = chartAt E x y :=
  rfl

@[simp]
theorem chartBallHomeomorph_symm_coe_apply (x : X) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target)
    (y : Metric.ball (chartAt E x x) r) :
    ((chartBallHomeomorph E x r htarget).symm y : X) = (chartAt E x).symm y :=
  rfl

/-- Admissible positive-radius chart balls form a basis of the actual
neighborhood filter at the chart center. -/
theorem nhds_basis_chartBall (x : X) :
    (𝓝 x).HasBasis
      (fun r : ℝ => 0 < r ∧ Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target)
      (fun r => chartBallDomain E x r) := by
  rw [← (chartAt E x).symm_map_nhds_eq (mem_chart_source E x)]
  have hb := (Metric.nhds_basis_ball (x := chartAt E x x)).restrict_subset
    (chart_target_mem_nhds E x)
  refine (hb.map (chartAt E x).symm).congr (fun _ => Iff.rfl) ?_
  intro r hr
  exact (chartAt E x).symm_image_eq_source_inter_preimage hr.2

/-- Every neighborhood contains an admissible positive-radius chart ball. -/
theorem exists_chartBall_subset_of_mem_nhds (x : X) {s : Set X} (hs : s ∈ 𝓝 x) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target ∧
      chartBallDomain E x r ⊆ s := by
  obtain ⟨r, ⟨hr, ht⟩, hsub⟩ := (nhds_basis_chartBall E x).mem_iff.mp hs
  exact ⟨r, hr, ht, hsub⟩

variable [NormedSpace ℝ E]

/-- Each admissible positive-radius chart ball is contractible by transport
of the straight-line contraction of its convex model ball. -/
theorem contractibleSpace_chartBall (x : X) (r : ℝ) (hr : 0 < r)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    ContractibleSpace (chartBallOpen E x r) := by
  let : ContractibleSpace (Metric.ball (chartAt E x x) r) :=
    (convex_ball (chartAt E x x) r).contractibleSpace
      ⟨chartAt E x x, Metric.mem_ball_self hr⟩
  exact (chartBallHomeomorph E x r htarget).contractibleSpace

include E in
/-- The chart-ball basis supplies a contractible open neighborhood inside
every prescribed neighborhood. -/
theorem exists_contractible_open_subset_of_mem_nhds (x : X)
    {s : Set X} (hs : s ∈ 𝓝 x) :
    ∃ U : TopologicalSpace.Opens X,
      x ∈ U ∧ (U : Set X) ⊆ s ∧ ContractibleSpace U := by
  obtain ⟨r, hr, ht, hsub⟩ := exists_chartBall_subset_of_mem_nhds E x hs
  exact ⟨chartBallOpen E x r, mem_chartBallDomain_self E x hr, hsub,
    contractibleSpace_chartBall E x r hr ht⟩

variable {R : Type} [Ring R]

/-- Positive-degree singular cohomology vanishes on admissible chart balls. -/
theorem isZero_singularCohomology_chartBall (M : ModuleCat.{0} R)
    (x : X) (r : ℝ) (hr : 0 < r)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target)
    (n : ℕ) (hn : n ≠ 0) :
    IsZero (Basic.singularCohomology M (TopCat.of (chartBallOpen E x r)) n) := by
  let := contractibleSpace_chartBall E x r hr htarget
  exact Contractible.isZero_singularCohomology_of_contractible M (TopCat.of (chartBallOpen E x r)) n hn

end

end OAI.AlgebraicTopology.Cohomology.Singular.ChartBalls
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.ChartBalls"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.ChartSmoothComparison -/

/-! # Chart Smooth Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ChartSmoothComparison

noncomputable section

/-!
# Smooth singular comparison in chart neighborhoods

Actual smooth diffeomorphisms induce compatible isomorphisms of continuous and
smooth singular cochains. These preserve the genuine smooth-simplex restriction
map, allowing the proved convex-domain comparison to be transported to chart
neighborhoods. No global smoothing theorem or de Rham comparison is assumed.
-/

open _root_.CategoryTheory Opposite
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {E F : Type}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {M N : Type}
variable [TopologicalSpace M] [ChartedSpace E M]
variable [TopologicalSpace N] [ChartedSpace F N]

/-- A smooth diffeomorphism gives an isomorphism of the actual smooth singular
simplicial sets. -/
def manifoldSmoothSingularDiffeomorphIso
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) :
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet ≅
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex F N).toSSet where
  hom := ManifoldSmoothFunctor.manifoldSmoothSingularMap E F e e.contMDiff
  inv := ManifoldSmoothFunctor.manifoldSmoothSingularMap F E e.symm e.symm.contMDiff
  hom_inv_id := by
    ext n σ
    apply Subtype.ext
    apply ((TopCat.of M).toSSetObjEquiv n).injective
    ext x
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext n σ
    apply Subtype.ext
    apply ((TopCat.of N).toSSetObjEquiv n).injective
    ext x
    exact e.apply_symm_apply _

variable {R : Type} [Ring R]

/-- Contravariant transport of genuine smooth cochains by a diffeomorphism. -/
def manifoldSmoothCochainsDiffeomorphIso (A : ModuleCat.{0} R)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) :
    ManifoldSmooth.manifoldSmoothCochains F A N ≅ ManifoldSmooth.manifoldSmoothCochains E A M :=
  (Functor.simplicialCochainsFunctor A).mapIso (manifoldSmoothSingularDiffeomorphIso e).op

/-- Contravariant transport of continuous singular cochains by the underlying
homeomorphism of an actual diffeomorphism. -/
def continuousCochainsDiffeomorphIso (A : ModuleCat.{0} R)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) :
    Basic.singularCochains A (TopCat.of N) ≅ Basic.singularCochains A (TopCat.of M) :=
  (Functor.singularCochainsFunctor A).mapIso (TopCat.isoOfHomeo e.toHomeomorph).op

/-- The continuous-to-smooth restriction maps form an isomorphic arrow under
an actual diffeomorphism. -/
def manifoldSmoothRestrictionDiffeomorphArrowIso (A : ModuleCat.{0} R)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) :
    Arrow.mk (ManifoldSmooth.manifoldSmoothCochainRestriction F A N) ≅
      Arrow.mk (ManifoldSmooth.manifoldSmoothCochainRestriction E A M) :=
  Arrow.isoMk (continuousCochainsDiffeomorphIso A e)
    (manifoldSmoothCochainsDiffeomorphIso A e)
    (ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality A e e.contMDiff)

/-- The genuine smooth-cochain comparison is invariant under diffeomorphism. -/
theorem quasiIso_manifoldSmoothRestriction_diffeomorph_iff (A : ModuleCat.{0} R)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction F A N) ↔
      QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E A M) :=
  quasiIso_iff_of_arrow_mk_iso _ _
    (manifoldSmoothRestrictionDiffeomorphArrowIso A e)

/-- On an actual nonempty convex open subset of a normed space, the manifold
smooth cochains agree with the previously verified convex-domain model. -/
theorem quasiIso_convexManifoldSmoothRestriction (A : ModuleCat.{0} R)
    (U : TopologicalSpace.Opens F) (hU : Convex ℝ (U : Set F))
    (hne : (U : Set F).Nonempty) :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction F A U) := by
  have : QuasiIso (SmoothOpen.subsetSmoothCochainRestriction A (U : Set F)) := by
    refine ⟨fun n => ?_⟩
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).2
      (SmoothConvexComparison.isIso_convexSmoothCohomologyRestriction A hU hne n)
  have : QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction F A U ≫
      (ManifoldSmoothModels.manifoldSmoothOpenCochainsIso F U A).hom) := by
    rw [ManifoldSmoothModels.manifoldSmoothOpenCochainRestriction_iso_hom]
    infer_instance
  exact quasiIso_of_comp_right (ManifoldSmooth.manifoldSmoothCochainRestriction F A U)
    (ManifoldSmoothModels.manifoldSmoothOpenCochainsIso F U A).hom

/-- Transport the actual convex comparison through a verified smooth
diffeomorphism to a convex open subset of a normed model space. -/
theorem quasiIso_manifoldSmoothRestriction_of_convexDiffeomorph (A : ModuleCat.{0} R)
    (U : TopologicalSpace.Opens F) (hU : Convex ℝ (U : Set F))
    (hne : (U : Set F).Nonempty)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M U ∞) :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E A M) :=
  (quasiIso_manifoldSmoothRestriction_diffeomorph_iff A e).mp
    (quasiIso_convexManifoldSmoothRestriction A U hU hne)

/-- The actual cohomology comparison on a manifold diffeomorphic to a convex
open domain. Its forward map is the smooth-simplex restriction. -/
def convexDiffeomorphSmoothCohomologyIso (A : ModuleCat.{0} R)
    (U : TopologicalSpace.Opens F) (hU : Convex ℝ (U : Set F))
    (hne : (U : Set F).Nonempty)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M U ∞) (n : ℕ) :
    Basic.singularCohomology A (TopCat.of M) n ≅ (ManifoldSmooth.manifoldSmoothCochains E A M).homology n := by
  letI := quasiIso_manifoldSmoothRestriction_of_convexDiffeomorph A U hU hne e
  exact isoOfQuasiIsoAt (ManifoldSmooth.manifoldSmoothCochainRestriction E A M) n

@[simp]
theorem convexDiffeomorphSmoothCohomologyIso_hom (A : ModuleCat.{0} R)
    (U : TopologicalSpace.Opens F) (hU : Convex ℝ (U : Set F))
    (hne : (U : Set F).Nonempty)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M U ∞) (n : ℕ) :
    (convexDiffeomorphSmoothCohomologyIso A U hU hne e n).hom =
      HomologicalComplex.homologyMap (ManifoldSmooth.manifoldSmoothCochainRestriction E A M) n := rfl

variable (E) in
/-- The target model ball as an open submanifold of the normed model space. -/
def chartBallModelOpen (x : M) (r : ℝ) : TopologicalSpace.Opens E :=
  ⟨Metric.ball (chartAt E x x) r, Metric.isOpen_ball⟩

variable [IsManifold 𝓘(ℝ, E) ∞ M]

variable (E) in
/-- The actual chart homeomorphism on an admissible chart ball has smooth
forward and inverse maps in the inherited open-submanifold structures. -/
def chartBallDiffeomorph (x : M) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E)
      (ChartBalls.chartBallOpen E x r) (chartBallModelOpen E x r) ∞ where
  toEquiv := (ChartBalls.chartBallHomeomorph E x r htarget).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (chartBallModelOpen E x r) _).mp
    intro y
    change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun z : ChartBalls.chartBallOpen E x r => chartAt E x (z : M)) y
    apply contMDiffAt_subtype_iff.mpr
    exact contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) x) y.property.1
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (ChartBalls.chartBallOpen E x r) _).mp
    intro y
    change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun z : chartBallModelOpen E x r => (chartAt E x).symm (z : E)) y
    apply contMDiffAt_subtype_iff.mpr
    exact contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) x)
      (htarget y.property)

@[simp]
theorem chartBallDiffeomorph_apply (x : M) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target)
    (y : ChartBalls.chartBallOpen E x r) :
    (chartBallDiffeomorph E x r htarget y : E) = chartAt E x y := rfl

@[simp]
theorem chartBallDiffeomorph_symm_apply (x : M) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target)
    (y : chartBallModelOpen E x r) :
    ((chartBallDiffeomorph E x r htarget).symm y : M) = (chartAt E x).symm y := rfl

variable (E) in
/-- The actual continuous-to-smooth cochain restriction on an admissible
positive-radius chart ball is a quasi-isomorphism. -/
theorem quasiIso_chartBallSmoothRestriction (A : ModuleCat.{0} R)
    (x : M) (r : ℝ) (hr : 0 < r)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E A (ChartBalls.chartBallOpen E x r)) :=
  quasiIso_manifoldSmoothRestriction_of_convexDiffeomorph A
    (chartBallModelOpen E x r) (convex_ball (chartAt E x x) r)
    ⟨chartAt E x x, Metric.mem_ball_self hr⟩ (chartBallDiffeomorph E x r htarget)

variable (E) in
/-- The cohomology isomorphism on a genuine chart-ball domain, induced by
restriction of ordinary singular cochains to manifold-smooth simplices. -/
def chartBallSmoothCohomologyIso (A : ModuleCat.{0} R)
    (x : M) (r : ℝ) (hr : 0 < r)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) (n : ℕ) :
    Basic.singularCohomology A (TopCat.of (ChartBalls.chartBallOpen E x r)) n ≅
      (ManifoldSmooth.manifoldSmoothCochains E A (ChartBalls.chartBallOpen E x r)).homology n := by
  letI := quasiIso_chartBallSmoothRestriction E A x r hr htarget
  exact isoOfQuasiIsoAt (ManifoldSmooth.manifoldSmoothCochainRestriction E A (ChartBalls.chartBallOpen E x r)) n

@[simp]
theorem chartBallSmoothCohomologyIso_hom (A : ModuleCat.{0} R)
    (x : M) (r : ℝ) (hr : 0 < r)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) (n : ℕ) :
    (chartBallSmoothCohomologyIso E A x r hr htarget n).hom =
      HomologicalComplex.homologyMap
        (ManifoldSmooth.manifoldSmoothCochainRestriction E A (ChartBalls.chartBallOpen E x r)) n := rfl

variable (E) in
/-- Every neighborhood contains an actual open neighborhood on which smooth
singular restriction is a quasi-isomorphism. -/
theorem exists_open_smoothComparison_subset (A : ModuleCat.{0} R)
    (x : M) {s : Set M} (hs : s ∈ 𝓝 x) :
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧ (U : Set M) ⊆ s ∧
      QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E A U) := by
  obtain ⟨r, hr, ht, hsub⟩ := ChartBalls.exists_chartBall_subset_of_mem_nhds E x hs
  exact ⟨ChartBalls.chartBallOpen E x r, ChartBalls.mem_chartBallDomain_self E x hr, hsub,
    quasiIso_chartBallSmoothRestriction E A x r hr ht⟩

end

end OAI.AlgebraicTopology.Cohomology.Singular.ChartSmoothComparison
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.ChartSmoothComparison"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf -/

/-! # Manifold Smooth Presheaf -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf

noncomputable section

/-!
# Smooth singular cochains on open subsets of a manifold

Each open subset carries its actual induced charted-space structure. Inclusions
of open subsets are smooth, and therefore induce maps of the genuine smooth
singular simplicial sets. Pulling back cochains gives the presheaf constructed
here. No sheaf condition is asserted for ordinary smooth singular cochains.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

/-- Smooth singular simplicial sets of open subsets, covariant for inclusions. -/
def manifoldOpenSmoothSingularFunctor : Opens M ⥤ SSet.{0} where
  obj U := (ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
  map i := ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (Opens.inclusion i.le) (contMDiff_inclusion i.le)
  map_id U := by
    ext n σ
    apply Subtype.ext
    rfl
  map_comp i j := by
    ext n σ
    apply Subtype.ext
    rfl

/-- Forgetting smoothness is natural over all open subsets. -/
def manifoldOpenSmoothInclusion :
    manifoldOpenSmoothSingularFunctor E M ⟶ (Opens.toTopCat (TopCat.of M)) ⋙ TopCat.toSSet where
  app U := ManifoldSmooth.manifoldSmoothInclusion E U
  naturality _ _ i :=
    ManifoldSmoothFunctor.manifoldSmoothSingularMap_inclusion (Opens.inclusion i.le) (contMDiff_inclusion i.le)

variable {R : Type} [Ring R]

/-- The actual presheaf of smooth singular cochain complexes on a charted manifold. -/
def manifoldSmoothCochainPresheaf (A : ModuleCat.{0} R) :
    (TopCat.of M).Presheaf (CochainComplex (ModuleCat.{0} R) ℕ) :=
  (manifoldOpenSmoothSingularFunctor E M).op ⋙ Singular.Functor.simplicialCochainsFunctor A

/-- Cochain restriction along an inclusion of open subsets. -/
def manifoldSmoothOpenRestriction (A : ModuleCat.{0} R) {U V : Opens M} (i : U ⟶ V) :
    ManifoldSmooth.manifoldSmoothCochains E A V ⟶ ManifoldSmooth.manifoldSmoothCochains E A U :=
  Singular.Functor.simplicialPullback A ((manifoldOpenSmoothSingularFunctor E M).map i)

@[simp]
theorem manifoldSmoothCochainPresheaf_obj (A : ModuleCat.{0} R) (U : Opens M) :
    (manifoldSmoothCochainPresheaf E M A).obj (op U) = ManifoldSmooth.manifoldSmoothCochains E A U := rfl

/-- The presheaf restriction is exactly pullback along the actual smooth inclusion. -/
@[simp]
theorem manifoldSmoothCochainPresheaf_map (A : ModuleCat.{0} R)
    {U V : Opens M} (i : U ⟶ V) :
    (manifoldSmoothCochainPresheaf E M A).map i.op =
      manifoldSmoothOpenRestriction E M A i := rfl

@[simp]
theorem manifoldSmoothOpenRestriction_id (A : ModuleCat.{0} R) (U : Opens M) :
    manifoldSmoothOpenRestriction E M A (𝟙 U) = 𝟙 (ManifoldSmooth.manifoldSmoothCochains E A U) :=
  (manifoldSmoothCochainPresheaf E M A).map_id (op U)

@[simp]
theorem manifoldSmoothOpenRestriction_comp (A : ModuleCat.{0} R)
    {U V W : Opens M} (i : U ⟶ V) (j : V ⟶ W) :
    manifoldSmoothOpenRestriction E M A (i ≫ j) =
      manifoldSmoothOpenRestriction E M A j ≫ manifoldSmoothOpenRestriction E M A i :=
  (manifoldSmoothCochainPresheaf E M A).map_comp j.op i.op

/-- Restriction commutes with every cochain differential. -/
theorem manifoldSmoothOpenRestriction_comm (A : ModuleCat.{0} R)
    {U V : Opens M} (i : U ⟶ V) (n m : ℕ) :
    (manifoldSmoothOpenRestriction E M A i).f n ≫ (ManifoldSmooth.manifoldSmoothCochains E A U).d n m =
      (ManifoldSmooth.manifoldSmoothCochains E A V).d n m ≫ (manifoldSmoothOpenRestriction E M A i).f m :=
  (manifoldSmoothOpenRestriction E M A i).comm n m

/-- The module-valued smooth singular cochain presheaf in a fixed degree. -/
def manifoldSmoothCochainDegreePresheaf (A : ModuleCat.{0} R) (n : ℕ) :
    (TopCat.of M).Presheaf (ModuleCat.{0} R) :=
  manifoldSmoothCochainPresheaf E M A ⋙
    HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n

/-- The presheaf of smooth singular cohomology groups. -/
def manifoldSmoothCohomologyPresheaf (A : ModuleCat.{0} R) (n : ℕ) :
    (TopCat.of M).Presheaf (ModuleCat.{0} R) :=
  manifoldSmoothCochainPresheaf E M A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n

@[simp]
theorem manifoldSmoothCochainDegreePresheaf_obj (A : ModuleCat.{0} R)
    (U : Opens M) (n : ℕ) :
    (manifoldSmoothCochainDegreePresheaf E M A n).obj (op U) =
      (ManifoldSmooth.manifoldSmoothCochains E A U).X n := rfl

@[simp]
theorem manifoldSmoothCohomologyPresheaf_obj (A : ModuleCat.{0} R)
    (U : Opens M) (n : ℕ) :
    (manifoldSmoothCohomologyPresheaf E M A n).obj (op U) =
      (ManifoldSmooth.manifoldSmoothCochains E A U).homology n := rfl

/-- The cochain complex of module-valued presheaves obtained degree by degree. -/
def manifoldSmoothPresheafComplex (A : ModuleCat.{0} R) :
    CochainComplex ((Opens M)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ where
  X := manifoldSmoothCochainDegreePresheaf E M A
  d i j :=
    { app := fun U => ((manifoldSmoothCochainPresheaf E M A).obj U).d i j
      naturality := fun U V f => ((manifoldSmoothCochainPresheaf E M A).map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext U
    exact ((manifoldSmoothCochainPresheaf E M A).obj U).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext U
    exact ((manifoldSmoothCochainPresheaf E M A).obj U).d_comp_d i j k

@[simp]
theorem manifoldSmoothPresheafComplex_d_app (A : ModuleCat.{0} R)
    (U : Opens M) (i j : ℕ) :
    ((manifoldSmoothPresheafComplex E M A).d i j).app (op U) =
      (ManifoldSmooth.manifoldSmoothCochains E A U).d i j := rfl

/-- Restriction from continuous to smooth singular cochains on all open subsets. -/
def manifoldSmoothRestrictionNatTrans (A : ModuleCat.{0} R) :
    (Opens.toTopCat (TopCat.of M)).op ⋙ Singular.Functor.singularCochainsFunctor A ⟶
      manifoldSmoothCochainPresheaf E M A where
  app U := ManifoldSmooth.manifoldSmoothCochainRestriction E A U.unop
  naturality _ _ f := by
    exact ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality A
      (Opens.inclusion f.unop.le)
      (contMDiff_inclusion (I := 𝓘(ℝ, E)) f.unop.le)

@[simp]
theorem manifoldSmoothRestrictionNatTrans_app (A : ModuleCat.{0} R) (U : Opens M) :
    (manifoldSmoothRestrictionNatTrans E M A).app (op U) =
      ManifoldSmooth.manifoldSmoothCochainRestriction E A U := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.StalkLocalIso -/

/-! # Stalk Local Iso -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.StalkLocalIso

noncomputable section

/-!
# Isomorphisms on a neighborhood basis induce stalk isomorphisms

These statements concern the actual filtered-colimit stalk of a module
presheaf. They require componentwise injectivity or surjectivity only on an
arbitrarily small open neighborhood of the point. No sheaf condition is needed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

universe u

variable {R : Type} [Ring R] {X : TopCat.{u}}
variable {F G : X.Presheaf (ModuleCat.{u,0} R)}

attribute [local instance] StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Injectivity on an arbitrarily small neighborhood gives injectivity on the
stalk. The proof first shrinks until the image of a section vanishes. -/
theorem stalkMap_injective_of_locally_injective (τ : F ⟶ G) (x : X)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (V : Opens X) (_hxV : x ∈ V) (_i : V ⟶ U),
        Function.Injective (τ.app (op V))) :
    Function.Injective ((stalkFunctor (ModuleCat.{u,0} R) x).map τ) := by
  apply (injective_iff_map_eq_zero _).2
  intro z hz
  obtain ⟨U, hxU, s, rfl⟩ := F.exists_germ_eq z
  rw [stalkFunctor_map_germ_apply] at hz
  obtain ⟨V, hxV, i, hi⟩ :=
    (StalkExactnessAt.germ_eq_zero_iff_locally_zero G x U hxU (τ.app (op U) s)).mp hz
  obtain ⟨W, hxW, j, hinj⟩ := hlocal V hxV
  have hV : τ.app (op V) (F.map i.op s) = 0 :=
    (ConcreteCategory.congr_hom (τ.naturality i.op) s).trans hi
  have hW : τ.app (op W) (F.map j.op (F.map i.op s)) = 0 := by
    rw [← ConcreteCategory.comp_apply, τ.naturality, ConcreteCategory.comp_apply,
      hV, map_zero]
  have hs : F.map j.op (F.map i.op s) = 0 := hinj (by simpa only [map_zero] using hW)
  calc
    F.germ U x hxU s = F.germ V x hxV (F.map i.op s) :=
      (F.germ_res_apply i x hxV s).symm
    _ = F.germ W x hxW (F.map j.op (F.map i.op s)) :=
      (F.germ_res_apply j x hxW _).symm
    _ = 0 := by rw [hs, map_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Surjectivity on an arbitrarily small neighborhood gives surjectivity on
the stalk, by lifting a restricted representative of each germ. -/
theorem stalkMap_surjective_of_locally_surjective (τ : F ⟶ G) (x : X)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (V : Opens X) (_hxV : x ∈ V) (_i : V ⟶ U),
        Function.Surjective (τ.app (op V))) :
    Function.Surjective ((stalkFunctor (ModuleCat.{u,0} R) x).map τ) := by
  intro z
  obtain ⟨U, hxU, s, rfl⟩ := G.exists_germ_eq z
  obtain ⟨V, hxV, i, hsurj⟩ := hlocal U hxU
  obtain ⟨t, ht⟩ := hsurj (G.map i.op s)
  refine ⟨F.germ V x hxV t, ?_⟩
  rw [stalkFunctor_map_germ_apply, ht]
  exact G.germ_res_apply i x hxV s

/-- A natural transformation which is an isomorphism on arbitrarily small
neighborhoods of a point induces an isomorphism on the actual stalk there. -/
theorem stalkMap_isIso_of_locally_isIso (τ : F ⟶ G) (x : X)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (V : Opens X) (_hxV : x ∈ V) (_i : V ⟶ U), IsIso (τ.app (op V))) :
    IsIso ((stalkFunctor (ModuleCat.{u,0} R) x).map τ) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply stalkMap_injective_of_locally_injective τ x
    intro U hxU
    obtain ⟨V, hxV, i, h⟩ := hlocal U hxU
    let := h
    exact ⟨V, hxV, i, (ConcreteCategory.bijective_of_isIso (τ.app (op V))).1⟩
  · apply stalkMap_surjective_of_locally_surjective τ x
    intro U hxU
    obtain ⟨V, hxV, i, h⟩ := hlocal U hxU
    let := h
    exact ⟨V, hxV, i, (ConcreteCategory.bijective_of_isIso (τ.app (op V))).2⟩

end

end OAI.AlgebraicTopology.Cohomology.Singular.StalkLocalIso
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.StalkLocalIso"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.SmoothStalkComparison -/

/-! # Smooth Stalk Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmoothStalkComparison

noncomputable section

/-!
# The actual continuous-to-smooth comparison on stalk complexes

The cochain map is formed from restriction of ordinary singular cochains to
the genuine manifold-smooth singular simplices on every open set. Its map on
stalks is the degreewise map of the actual filtered-colimit stalk functor.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]
variable {R : Type} [Ring R]

/-- The actual restriction to smooth simplices as a map of complexes of
module-valued presheaves. -/
def manifoldSmoothPresheafRestriction (A : ModuleCat.{0} R) :
    DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M) ⟶
      ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A where
  f n :=
    { app := fun U => (ManifoldSmooth.manifoldSmoothCochainRestriction E A U.unop).f n
      naturality := fun U V i => congrArg (fun f => f.f n)
        ((ManifoldSmoothPresheaf.manifoldSmoothRestrictionNatTrans E M A).naturality i) }
  comm' i j _ := by
    apply NatTrans.ext
    funext U
    exact (ManifoldSmooth.manifoldSmoothCochainRestriction E A U.unop).comm i j

@[simp]
theorem manifoldSmoothPresheafRestriction_f_app (A : ModuleCat.{0} R)
    (U : Opens M) (n : ℕ) :
    ((manifoldSmoothPresheafRestriction E M A).f n).app (op U) =
      (ManifoldSmooth.manifoldSmoothCochainRestriction E A U).f n := rfl

/-- The induced comparison between the ordinary and smooth singular stalk
complexes, obtained by applying the actual stalk functor in every degree. -/
def manifoldSmoothStalkRestriction (A : ModuleCat.{0} R) (x : M) :
    (((stalkFunctor (X := TopCat.of M) (ModuleCat.{0} R) x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M))) ⟶
    (((stalkFunctor (X := TopCat.of M) (ModuleCat.{0} R) x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A)) :=
  ((stalkFunctor (X := TopCat.of M) (ModuleCat.{0} R) x).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (manifoldSmoothPresheafRestriction E M A)

/-- If ordinary-to-smooth restriction is a quasi-isomorphism on an open set,
the corresponding component of the cohomology presheaf map is an isomorphism.
This uses the canonical evaluation--cohomology comparison. -/
theorem isIso_manifoldSmoothPresheafRestriction_homology_app
    (A : ModuleCat.{0} R) (U : Opens M)
    [QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E A U)] (n : ℕ) :
    IsIso ((HomologicalComplex.homologyMap
      (manifoldSmoothPresheafRestriction E M A) n).app (op U)) := by
  let f := manifoldSmoothPresheafRestriction E M A
  have : IsIso (HomologicalComplex.homologyMap
      (((Stalk.presheafSectionFunctor (X := TopCat.of M) U).mapHomologicalComplex
        (ComplexShape.up ℕ)).map f) n) := by
    change IsIso (HomologicalComplex.homologyMap
      (ManifoldSmooth.manifoldSmoothCochainRestriction E A U) n)
    infer_instance
  have : IsIso ((Stalk.openCohomologyIso
      (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M)) U n).hom ≫
      (HomologicalComplex.homologyMap f n).app (op U)) := by
    rw [← Stalk.openCohomologyIso_naturality f U n]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (Stalk.openCohomologyIso (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M)) U n).hom
    ((HomologicalComplex.homologyMap f n).app (op U))

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- On a smooth manifold, restriction to genuine smooth singular simplices
induces an isomorphism on the stalk of every cohomology presheaf. -/
theorem isIso_manifoldSmoothPresheafRestriction_homology_stalk
    (A : ModuleCat.{0} R) (x : M) (n : ℕ) :
    IsIso ((stalkFunctor (X := TopCat.of M) (ModuleCat.{0} R) x).map
      (HomologicalComplex.homologyMap (manifoldSmoothPresheafRestriction E M A) n)) := by
  apply StalkLocalIso.stalkMap_isIso_of_locally_isIso
  intro U hxU
  obtain ⟨V, hxV, hVU, hV⟩ :=
    ChartSmoothComparison.exists_open_smoothComparison_subset E A x (U.isOpen.mem_nhds hxU)
  let := hV
  exact ⟨V, hxV, homOfLE hVU,
    isIso_manifoldSmoothPresheafRestriction_homology_app E M A V n⟩

/-- The actual map between stalk complexes is a quasi-isomorphism. Its proof
uses genuine chart-ball comparison and exactness of filtered colimits. -/
theorem quasiIso_manifoldSmoothStalkRestriction
    (A : ModuleCat.{0} R) (x : M) :
    QuasiIso (manifoldSmoothStalkRestriction E M A x) := by
  constructor
  intro n
  apply (quasiIsoAt_iff_isIso_homologyMap _ n).2
  have := isIso_manifoldSmoothPresheafRestriction_homology_stalk E M A x n
  have : IsIso (HomologicalComplex.homologyMap
      (manifoldSmoothStalkRestriction E M A x) n ≫
      (Stalk.stalkCohomologyIso (X := TopCat.of M)
        (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A) x n).hom) := by
    change IsIso (HomologicalComplex.homologyMap
      (((stalkFunctor (X := TopCat.of M) (ModuleCat.{0} R) x).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (manifoldSmoothPresheafRestriction E M A)) n ≫ _)
    rw [Stalk.stalkCohomologyIso_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (HomologicalComplex.homologyMap (manifoldSmoothStalkRestriction E M A x) n)
    (Stalk.stalkCohomologyIso (X := TopCat.of M)
      (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A) x n).hom

/-- The canonical cohomology comparison between the ordinary and smooth
singular stalk complexes. -/
def manifoldSmoothStalkCohomologyIso (A : ModuleCat.{0} R) (x : M) (n : ℕ) :
    (Stalk.stalkCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of M)) x).homology n ≅
      (Stalk.stalkCochainComplex (X := TopCat.of M)
        (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A) x).homology n := by
  letI := quasiIso_manifoldSmoothStalkRestriction E M A x
  exact isoOfQuasiIsoAt (manifoldSmoothStalkRestriction E M A x) n

@[simp]
theorem manifoldSmoothStalkCohomologyIso_hom (A : ModuleCat.{0} R) (x : M) (n : ℕ) :
    (manifoldSmoothStalkCohomologyIso E M A x n).hom =
      HomologicalComplex.homologyMap (manifoldSmoothStalkRestriction E M A x) n := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmoothStalkComparison
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.SmoothStalkComparison"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.OpenCochainPresheafComparison -/

/-! # Open Cochain Presheaf Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.OpenCochainPresheafComparison

noncomputable section

/-!
# Cochains on an open subspace and restriction of ambient cochain presheaves

An open subset of an open subspace is identified with its actual ambient
image. The resulting homeomorphisms and diffeomorphisms give natural
isomorphisms of genuine ordinary and smooth singular cochain presheaves,
including their differentials and the ordinary-to-smooth restriction map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Type} [TopologicalSpace X]

/-- Send an open subset of an open subspace to its actual ambient open image. -/
def nestedOpenImageFunctor (W : Opens X) : Opens W ⥤ Opens X where
  obj := ChartOpenDiffeomorph.nestedOpenImage W
  map i := homOfLE (Set.image_mono i.le)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
theorem nestedOpenImageFunctor_obj (W : Opens X) (V : Opens W) :
    (nestedOpenImageFunctor W).obj V = ChartOpenDiffeomorph.nestedOpenImage W V := rfl

/-- The topological identification of nested and flattened open subspaces. -/
def nestedOpenHomeomorph (W : Opens X) (V : Opens W) : V ≃ₜ ChartOpenDiffeomorph.nestedOpenImage W V where
  toEquiv := ChartOpenDiffeomorph.nestedOpenEquiv W V
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Flattening nested opens commutes with their actual continuous inclusions. -/
theorem nestedOpenHomeomorph_naturality (W : Opens X) {U V : Opens W} (i : U ⟶ V) :
    (Opens.toTopCat (TopCat.of W)).map i ≫
        (TopCat.isoOfHomeo (nestedOpenHomeomorph W V)).hom =
      (TopCat.isoOfHomeo (nestedOpenHomeomorph W U)).hom ≫
        (Opens.toTopCat (TopCat.of X)).map ((nestedOpenImageFunctor W).map i) := rfl

variable {R : Type} [Ring R]

/-- Ordinary cochains on an open subspace agree naturally with the ambient
ordinary cochain presheaf restricted to its nested open images. -/
def singularOpenCochainPresheafIso (A : ModuleCat.{0} R) (W : Opens X) :
    (nestedOpenImageFunctor W).op ⋙ DeRham.Comparison.SingularPresheaf.singularCochainPresheaf A (TopCat.of X) ≅
      DeRham.Comparison.SingularPresheaf.singularCochainPresheaf A (TopCat.of W) :=
  NatIso.ofComponents
    (fun V => (Singular.Functor.singularCochainsFunctor A).mapIso
      (TopCat.isoOfHomeo (nestedOpenHomeomorph W V.unop)).op)
    (fun {U V} i => by
      change Singular.Functor.singularPullback A
          ((Opens.toTopCat (TopCat.of X)).map ((nestedOpenImageFunctor W).map i.unop)) ≫
          Singular.Functor.singularPullback A (TopCat.isoOfHomeo (nestedOpenHomeomorph W V.unop)).hom =
        Singular.Functor.singularPullback A (TopCat.isoOfHomeo (nestedOpenHomeomorph W U.unop)).hom ≫
          Singular.Functor.singularPullback A ((Opens.toTopCat (TopCat.of W)).map i.unop)
      rw [← Singular.Functor.singularPullback_comp, ← Singular.Functor.singularPullback_comp,
        nestedOpenHomeomorph_naturality])

@[simp]
theorem singularOpenCochainPresheafIso_hom_app (A : ModuleCat.{0} R)
    (W : Opens X) (V : Opens W) :
    (singularOpenCochainPresheafIso A W).hom.app (op V) =
      Singular.Functor.singularPullback A (TopCat.isoOfHomeo (nestedOpenHomeomorph W V)).hom := rfl

/-- Degreewise precomposition by the actual nested-open image functor. -/
def nestedOpenPresheafComplexFunctor (W : Opens X) :
    CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ ⥤
      CochainComplex ((Opens W)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ :=
  ((Functor.whiskeringLeft _ _ (ModuleCat.{0} R)).obj
    (nestedOpenImageFunctor W).op).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The same ordinary comparison as an isomorphism of actual complexes of
module-valued presheaves, preserving every differential. -/
def singularOpenPresheafComplexIso (A : ModuleCat.{0} R) (W : Opens X) :
    (nestedOpenPresheafComplexFunctor W).obj
        (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of X)) ≅
      DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of W) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => Functor.isoWhiskerRight (singularOpenCochainPresheafIso A W)
      (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n))
    (fun i j _ => by
      apply NatTrans.ext
      funext V
      exact ((singularOpenCochainPresheafIso A W).hom.app V).comm i j)

@[simp]
theorem singularOpenPresheafComplexIso_hom_f_app (A : ModuleCat.{0} R)
    (W : Opens X) (V : Opens W) (n : ℕ) :
    ((singularOpenPresheafComplexIso A W).hom.f n).app (op V) =
      ((singularOpenCochainPresheafIso A W).hom.app (op V)).f n := rfl

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

/-- Genuine smooth cochains on an open submanifold agree naturally with
the ambient smooth cochain presheaf on its actual nested-open images. -/
def manifoldSmoothOpenCochainPresheafIso (A : ModuleCat.{0} R) (W : Opens M) :
    (nestedOpenImageFunctor W).op ⋙ ManifoldSmoothPresheaf.manifoldSmoothCochainPresheaf E M A ≅
      ManifoldSmoothPresheaf.manifoldSmoothCochainPresheaf E W A :=
  NatIso.ofComponents
    (fun V => ChartSmoothComparison.manifoldSmoothCochainsDiffeomorphIso A (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W V.unop))
    (fun {U V} i => by
      change Singular.Functor.simplicialPullback A
          ((ManifoldSmoothPresheaf.manifoldOpenSmoothSingularFunctor E M).map
            ((nestedOpenImageFunctor W).map i.unop)) ≫
          Singular.Functor.simplicialPullback A
            (ChartSmoothComparison.manifoldSmoothSingularDiffeomorphIso (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W V.unop)).hom =
        Singular.Functor.simplicialPullback A
            (ChartSmoothComparison.manifoldSmoothSingularDiffeomorphIso (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W U.unop)).hom ≫
          Singular.Functor.simplicialPullback A ((ManifoldSmoothPresheaf.manifoldOpenSmoothSingularFunctor E W).map i.unop)
      rw [← Singular.Functor.simplicialPullback_comp, ← Singular.Functor.simplicialPullback_comp]
      congr 1)

@[simp]
theorem manifoldSmoothOpenCochainPresheafIso_hom_app (A : ModuleCat.{0} R)
    (W : Opens M) (V : Opens W) :
    (manifoldSmoothOpenCochainPresheafIso E M A W).hom.app (op V) =
      ManifoldSmoothFunctor.manifoldSmoothPullback E E A (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W V)
        (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W V).contMDiff := rfl

/-- The ordinary and smooth natural identifications intertwine the actual
restriction from continuous simplices to smooth simplices. -/
theorem openCochainPresheafIso_restriction (A : ModuleCat.{0} R) (W : Opens M) :
    Functor.whiskerLeft (nestedOpenImageFunctor W).op
        (ManifoldSmoothPresheaf.manifoldSmoothRestrictionNatTrans E M A) ≫
        (manifoldSmoothOpenCochainPresheafIso E M A W).hom =
      (singularOpenCochainPresheafIso A W).hom ≫
        ManifoldSmoothPresheaf.manifoldSmoothRestrictionNatTrans E W A := by
  apply NatTrans.ext
  funext V
  exact (ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality A
    (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W V.unop) (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W V.unop).contMDiff).symm

/-- The native smooth comparison as an actual isomorphism of complexes of
module-valued presheaves on the open subspace. -/
def manifoldSmoothOpenPresheafComplexIso (A : ModuleCat.{0} R) (W : Opens M) :
    (nestedOpenPresheafComplexFunctor W).obj (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A) ≅
      ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E W A :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => Functor.isoWhiskerRight (manifoldSmoothOpenCochainPresheafIso E M A W)
      (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n))
    (fun i j _ => by
      apply NatTrans.ext
      funext V
      exact ((manifoldSmoothOpenCochainPresheafIso E M A W).hom.app V).comm i j)

@[simp]
theorem manifoldSmoothOpenPresheafComplexIso_hom_f_app (A : ModuleCat.{0} R)
    (W : Opens M) (V : Opens W) (n : ℕ) :
    ((manifoldSmoothOpenPresheafComplexIso E M A W).hom.f n).app (op V) =
      ((manifoldSmoothOpenCochainPresheafIso E M A W).hom.app (op V)).f n := rfl

/-- The isomorphisms of presheaf complexes preserve the actual ordinary-to-smooth
restriction morphism in every degree, as a commuting square of complexes. -/
theorem openPresheafComplexIso_restriction (A : ModuleCat.{0} R) (W : Opens M) :
    (nestedOpenPresheafComplexFunctor W).map (SmoothStalkComparison.manifoldSmoothPresheafRestriction E M A) ≫
        (manifoldSmoothOpenPresheafComplexIso E M A W).hom =
      (singularOpenPresheafComplexIso A W).hom ≫
        SmoothStalkComparison.manifoldSmoothPresheafRestriction E W A := by
  ext n : 1
  apply NatTrans.ext
  funext V
  exact congrArg (fun f => f.f n)
    (NatTrans.congr_app (openCochainPresheafIso_restriction E M A W) V)

end

end OAI.AlgebraicTopology.Cohomology.Singular.OpenCochainPresheafComparison
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.OpenCochainPresheafComparison"

@[expose] public section ComponentSource_18
/- Original module: OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf -/

/-! # Locally Constant Sheaf -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf

noncomputable section

/-!
# The actual sheaf of locally constant complex-valued functions

The sections on an open set U are literally `LocallyConstant U ℂ`.
Restriction is precomposition with the open inclusion. The sheaf property
is proved from locality of local constancy, independently of differential
forms and their kernels.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u

/-- Locally constant complex functions with their usual restriction maps. -/
def locallyConstantPresheaf (X : TopCat.{u}) : X.Presheaf (ModuleCat.{u} ℂ) where
  obj U := ModuleCat.of ℂ (LocallyConstant U.unop ℂ)
  map i := ModuleCat.ofHom {
    toFun := fun f => ⟨fun x => f (i.unop x),
      f.isLocallyConstant.comp_continuous
        (Opens.isOpenEmbedding_of_le i.unop.le).continuous⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl
  map_comp i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl

@[simp]
theorem locallyConstantPresheaf_obj (X : TopCat.{u}) (U : Opens X) :
    (locallyConstantPresheaf X).obj (op U) = ModuleCat.of ℂ (LocallyConstant U ℂ) := rfl

@[simp]
theorem locallyConstantPresheaf_map_apply {X : TopCat.{u}} {U V : Opens X}
    (h : V ≤ U) (f : LocallyConstant U ℂ) (x : V) :
    LocallyConstant.toFun ((locallyConstantPresheaf X).map (homOfLE h).op f) x =
      f ⟨x, h x.property⟩ := rfl

/-- Local constancy is a genuinely local predicate on scalar functions. -/
def locallyConstantPredicate (X : TopCat.{u}) :
    TopCat.LocalPredicate (fun _ : X => ℂ) where
  pred f := IsLocallyConstant f
  res i f hf := hf.comp_continuous (Opens.isOpenEmbedding_of_le i.le).continuous
  locality f h := by
    intro t
    apply isOpen_iff_forall_mem_open.2
    intro x hx
    obtain ⟨V, hxV, i, hV⟩ := h x
    refine ⟨i '' ((fun y : V => f (i y)) ⁻¹' t), ?_, ?_, ?_⟩
    · rintro y ⟨z, hz, rfl⟩
      exact hz
    · exact (Opens.isOpenEmbedding_of_le i.le).isOpenMap _ (hV t)
    · exact ⟨⟨x, hxV⟩, hx, by ext; rfl⟩

/-- Unbundling local constancy changes only the packaging of the actual functions. -/
def locallyConstantSectionEquiv {X : TopCat.{u}} (U : Opens X) :
    LocallyConstant U ℂ ≃ {f : U → ℂ // IsLocallyConstant f} where
  toFun f := ⟨f, f.isLocallyConstant⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

/-- The underlying presheaf is the presheaf cut out by the local predicate. -/
def locallyConstantUnderlyingIso (X : TopCat.{u}) :
    locallyConstantPresheaf X ⋙ forget (ModuleCat.{u} ℂ) ≅
      TopCat.subpresheafToTypes (locallyConstantPredicate X).toPrelocalPredicate :=
  NatIso.ofComponents
    (fun U => (locallyConstantSectionEquiv U.unop).toIso)
    (by intro U V i; ext f; rfl)

/-- Compatible locally constant sections glue uniquely. -/
theorem locallyConstantPresheaf_isSheaf (X : TopCat.{u}) :
    (locallyConstantPresheaf X).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget (ModuleCat.{u} ℂ)) (locallyConstantPresheaf X)).2
  exact TopCat.Presheaf.isSheaf_of_iso (locallyConstantUnderlyingIso X).symm
    (TopCat.subpresheafToTypes.isSheaf (locallyConstantPredicate X))

/-- The genuine complex-module-valued sheaf of locally constant functions. -/
def locallyConstantSheaf (X : TopCat.{u}) : X.Sheaf (ModuleCat.{u} ℂ) where
  obj := locallyConstantPresheaf X
  property := locallyConstantPresheaf_isSheaf X

@[simp]
theorem locallyConstantSheaf_presheaf (X : TopCat.{u}) :
    (locallyConstantSheaf X).presheaf = locallyConstantPresheaf X := rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf"


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
    (`OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf_presheaf, "theorem")
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
    ("nonce", toJson "a2ffacebd2a01f606ce759aab9485153"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:a2ffacebd2a01f606ce759aab9485153"
