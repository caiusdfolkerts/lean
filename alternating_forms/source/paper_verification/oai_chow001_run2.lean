module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import all Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import all Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Basic.Complex.Basic
import all Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.FiniteType
import all Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import all Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import all Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import all Mathlib.AlgebraicGeometry.Morphisms.Separated
public import paper_verification.oai_chow000_run4
import all paper_verification.oai_chow000_run4
public import Mathlib.Algebra.Polynomial.Eval.Algebra
import all Mathlib.Algebra.Polynomial.Eval.Algebra
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import all Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Topology.Sets.OpenCover
import all Mathlib.Topology.Sets.OpenCover
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import all Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
import all Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Topology.NoetherianSpace
import all Mathlib.Topology.NoetherianSpace
public import Mathlib.Data.Finsupp.Defs
import all Mathlib.Data.Finsupp.Defs
public import Mathlib.RingTheory.Ideal.GoingUp
import all Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.GoingDown
import all Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.KrullDimension.Basic
import all Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.NoetherNormalization
import all Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.KrullDimension.Polynomial
import all Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
import all Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import all Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Jacobson.Ring
import all Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import all Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
public import Mathlib.RingTheory.KrullDimension.Regular
import all Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.IntegralClosure.GoingDown
import all Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.AlgebraicGeometry.Properties
import all Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import all Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.AlgebraicGeometry.FunctionField
import all Mathlib.AlgebraicGeometry.FunctionField
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace -/

/-! # Projective Space -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace

noncomputable section

/-!
# Standard complex projective space

The scheme is literally the projective spectrum of the polynomial ring with
its standard grading. Its structure map uses the proved identification of the
degree-zero ring with the complex numbers.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The base scheme for complex algebraic geometry. -/
abbrev complexBase : Scheme := Spec (.of ℂ)

/-- The standard homogeneous coordinate ring in `n + 1` variables. -/
abbrev homogeneousCoordinateRing (n : ℕ) := MvPolynomial (Fin (n + 1)) ℂ

/-- The usual grading by total degree. -/
abbrev projectiveGrading (n : ℕ) : ℕ → Submodule ℂ (homogeneousCoordinateRing n) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ

instance projectiveGradedAlgebra (n : ℕ) : GradedAlgebra (projectiveGrading n) :=
  MvPolynomial.gradedAlgebra

/-- Complex projective `n`-space as the genuine scheme `Proj ℂ[X₀,...,Xₙ]`. -/
abbrev projectiveSpace (n : ℕ) : Scheme := AlgebraicGeometry.Proj (projectiveGrading n)

/-- The degree-zero ring of the homogeneous coordinate ring consists exactly
of the constant complex polynomials. -/
def degreeZeroConstants (n : ℕ) : ℂ ≃+* projectiveGrading n 0 where
  toFun z := ⟨MvPolynomial.C z, MvPolynomial.isHomogeneous_C (Fin (n + 1)) z⟩
  invFun p := p.val.coeff 0
  left_inv z := MvPolynomial.coeff_zero_C z
  right_inv p := by
    apply Subtype.ext
    have hp : MvPolynomial.IsHomogeneous p.val 0 := p.property
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).mpr hp)).symm
  map_mul' z w := by
    apply Subtype.ext
    exact map_mul MvPolynomial.C z w
  map_add' z w := by
    apply Subtype.ext
    exact map_add MvPolynomial.C z w

@[simp]
theorem degreeZeroConstants_coe (n : ℕ) (z : ℂ) :
    (degreeZeroConstants n z : homogeneousCoordinateRing n) = MvPolynomial.C z := rfl

@[simp]
theorem degreeZeroConstants_symm_apply (n : ℕ) (p : projectiveGrading n 0) :
    (degreeZeroConstants n).symm p = p.val.coeff 0 := rfl

/-- The standard structure morphism `ℙⁿ_ℂ → Spec ℂ`. -/
def projectiveSpaceToBase (n : ℕ) : projectiveSpace n ⟶ complexBase :=
  Proj.toSpecZero (projectiveGrading n) ≫
    Spec.map (CommRingCat.ofHom (degreeZeroConstants n).toRingHom)

/-- On every standard homogeneous chart, the structure morphism is induced
by constants followed by the canonical map to the degree-zero localization. -/
theorem projectiveSpaceToBase_chart (n : ℕ) (m : ℕ)
    (f : homogeneousCoordinateRing n) (hf : f ∈ projectiveGrading n m) (hm : 0 < m) :
    Proj.awayι (projectiveGrading n) f hf hm ≫ projectiveSpaceToBase n =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (projectiveGrading n) (Submonoid.powers f)).comp
          (degreeZeroConstants n).toRingHom)) := by
  rw [projectiveSpaceToBase, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpaceFiniteType -/

/-! # Projective Space Finite Type -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpaceFiniteType

noncomputable section

/-! Finite generation of the homogeneous coordinate ring over its degree-zero ring. -/

/-- The polynomial coordinate ring is finitely generated as an algebra over
its actual degree-zero coefficient ring. -/
instance homogeneousCoordinateRing_finiteType_over_zero (n : ℕ) :
    Algebra.FiniteType (ProjectiveSpace.projectiveGrading n 0) (ProjectiveSpace.homogeneousCoordinateRing n) := by
  let : IsScalarTower ℂ (ProjectiveSpace.projectiveGrading n 0) (ProjectiveSpace.homogeneousCoordinateRing n) :=
    IsScalarTower.of_algebraMap_eq
      (R := ℂ) (S := ProjectiveSpace.projectiveGrading n 0) (A := ProjectiveSpace.homogeneousCoordinateRing n)
      (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    ℂ (ProjectiveSpace.projectiveGrading n 0) (ProjectiveSpace.homogeneousCoordinateRing n)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpaceFiniteType
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpaceFiniteType"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective -/

/-! # Smooth Projective -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective

noncomputable section

/-!
# Actual smooth projective presentations over the complex numbers

A projective presentation is a closed immersion into the `Proj` scheme of a
standard graded complex polynomial ring, commuting with the structure maps to
`Spec ℂ`. Smoothness is mathlib's smoothness of the structure morphism.

These are raw presentations: connectedness and irreducibility are not imposed.
There is no cohomology, cycle map, analytic topology, or unproved comparison
property in either structure.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- A genuine projective presentation of an actual complex scheme morphism. -/
structure ProjectivePresentation (X : Scheme) (f : X ⟶ ProjectiveSpace.complexBase) where
  /-- Dimension of the ambient standard projective space. -/
  ambientDimension : ℕ
  /-- The actual scheme morphism giving the projective embedding. -/
  embedding : X ⟶ ProjectiveSpace.projectiveSpace ambientDimension
  /-- Closed immersion has its existing scheme-theoretic meaning in mathlib. -/
  closedImmersion : IsClosedImmersion embedding
  /-- The embedding is a morphism over `Spec ℂ`. -/
  over_base : embedding ≫ ProjectiveSpace.projectiveSpaceToBase ambientDimension = f

namespace ProjectivePresentation

variable {X : Scheme} {f : X ⟶ ProjectiveSpace.complexBase}

instance (P : ProjectivePresentation X f) : IsClosedImmersion P.embedding :=
  P.closedImmersion

/-- The displayed structure map is the composite through the projective space. -/
theorem structureMap_eq (P : ProjectivePresentation X f) :
    f = P.embedding ≫ ProjectiveSpace.projectiveSpaceToBase P.ambientDimension :=
  P.over_base.symm

/-- Forgetting a projective presentation gives a morphism in the category over `Spec ℂ`. -/
def toOverHom (P : ProjectivePresentation X f) :
    Over.mk f ⟶ Over.mk (ProjectiveSpace.projectiveSpaceToBase P.ambientDimension) :=
  Over.homMk P.embedding P.over_base

@[simp]
theorem toOverHom_left (P : ProjectivePresentation X f) :
    P.toOverHom.left = P.embedding := rfl

/-- Packaging does not add any hypothesis beyond an actual closed projective embedding. -/
theorem nonempty_iff :
    Nonempty (ProjectivePresentation X f) ↔
      ∃ (n : ℕ) (i : X ⟶ ProjectiveSpace.projectiveSpace n),
        IsClosedImmersion i ∧ i ≫ ProjectiveSpace.projectiveSpaceToBase n = f := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.ambientDimension, P.embedding, P.closedImmersion, P.over_base⟩
  · rintro ⟨n, i, hi, hf⟩
    exact ⟨⟨n, i, hi, hf⟩⟩

/-- The underlying point map of the projective embedding is a closed embedding. -/
theorem isClosedEmbedding (P : ProjectivePresentation X f) :
    Topology.IsClosedEmbedding P.embedding :=
  P.embedding.isClosedEmbedding

/-- In particular, the embedding is injective on underlying scheme points. -/
theorem embedding_injective (P : ProjectivePresentation X f) :
    Function.Injective P.embedding :=
  P.isClosedEmbedding.injective

end ProjectivePresentation

/-- A smooth projective complex scheme with a chosen projective presentation.

The carrier is an actual scheme; the projectivity and smoothness fields use
only genuine algebraic-geometric definitions. No assertion about the analytic
space or Hodge theory is built into the data. -/
structure SmoothProjectivePresentation where
  carrier : Scheme
  structureMap : carrier ⟶ ProjectiveSpace.complexBase
  projective : ProjectivePresentation carrier structureMap
  smooth : Smooth structureMap

namespace SmoothProjectivePresentation

variable (P : SmoothProjectivePresentation)

/-- The ambient dimension of the chosen projective embedding. -/
abbrev ambientDimension : ℕ := P.projective.ambientDimension

/-- The chosen projective embedding. -/
abbrev embedding : P.carrier ⟶ ProjectiveSpace.projectiveSpace P.ambientDimension :=
  P.projective.embedding

instance : Smooth P.structureMap := P.smooth

instance : IsClosedImmersion P.embedding := P.projective.closedImmersion

/-- The carrier together with its specified complex structure map. -/
def toOver : Over ProjectiveSpace.complexBase := Over.mk P.structureMap

@[simp]
theorem toOver_left : P.toOver.left = P.carrier := rfl

@[simp]
theorem toOver_hom : P.toOver.hom = P.structureMap := rfl

@[reassoc]
theorem embedding_over :
    P.embedding ≫ ProjectiveSpace.projectiveSpaceToBase P.ambientDimension = P.structureMap :=
  P.projective.over_base

/-- Local finite presentation follows from genuine smoothness; it is not assumed. -/
instance : LocallyOfFinitePresentation P.structureMap := inferInstance

/-- Flatness follows from genuine smoothness; it is not assumed. -/
instance : Flat P.structureMap := inferInstance

/-- The actual structure morphism has standard smooth affine neighborhoods. -/
theorem exists_standardSmooth_neighborhood (x : P.carrier) :
    ∃ (U : ProjectiveSpace.complexBase.Opens) (_ : IsAffineOpen U)
      (V : P.carrier.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
      (e : V ≤ P.structureMap ⁻¹ᵁ U),
      (P.structureMap.appLE U V e).hom.IsStandardSmooth :=
  Smooth.exists_isStandardSmooth P.structureMap x

end SmoothProjectivePresentation

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective -/

/-! # Closed Projective -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme

/-!
# Algebraic consequences of a closed immersion into a projective spectrum

These lemmas concern actual schemes, morphisms, and the `Proj` construction in
mathlib. They supply properness, finite type, and Noetherian consequences used
by a projective presentation. Compactness here refers to the scheme's Zariski
topology; no assertion about an analytification is made in this module.
-/

set_option autoImplicit false
set_option warningAsError true

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

section General

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Proper morphisms are quasi-compact and locally of finite type, the two
conditions defining a morphism of finite type. -/
theorem ClosedProjective.finiteType_of_isProper [IsProper f] :
    LocallyOfFiniteType f ∧ QuasiCompact f :=
  ⟨inferInstance, inferInstance⟩

/-- A proper scheme over a Noetherian affine scheme is Noetherian. -/
theorem ClosedProjective.isNoetherian_of_isProper_toSpec {R : Type u} [CommRing R]
    [IsNoetherianRing R] (g : X ⟶ Spec (.of R)) [IsProper g] :
    AlgebraicGeometry.IsNoetherian X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  let : CompactSpace X := (quasiCompact_iff_compactSpace g).mp inferInstance
  exact ⟨⟩

end General

section ProjectiveSpectrum

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A]
variable {X : Scheme.{u}} (i : X ⟶ Proj 𝒜) [IsClosedImmersion i]

/-- A closed subscheme of a finite-type projective spectrum is proper over its
actual degree-zero ring. -/
theorem ClosedProjective.closedImmersion_proj_isProper :
    IsProper (i ≫ Proj.toSpecZero 𝒜) := by
  infer_instance

/-- The morphism in `closedImmersion_proj_isProper` is of finite type. -/
theorem ClosedProjective.closedImmersion_proj_finiteType :
    LocallyOfFiniteType (i ≫ Proj.toSpecZero 𝒜) ∧
      QuasiCompact (i ≫ Proj.toSpecZero 𝒜) :=
  ClosedProjective.finiteType_of_isProper _

include 𝒜 i in
/-- Algebraic (Zariski) compactness of a closed subscheme of `Proj`. -/
theorem ClosedProjective.closedImmersion_proj_compactSpace : CompactSpace X :=
  (quasiCompact_iff_compactSpace (i ≫ Proj.toSpecZero 𝒜)).mp inferInstance

include 𝒜 i in
/-- A closed subscheme of a finite-type `Proj` is Noetherian when the
actual degree-zero coefficient ring is Noetherian. -/
theorem ClosedProjective.closedImmersion_proj_isNoetherian [IsNoetherianRing (𝒜 0)] :
    AlgebraicGeometry.IsNoetherian X :=
  ClosedProjective.isNoetherian_of_isProper_toSpec (i ≫ Proj.toSpecZero 𝒜)

/-- Properness survives an arbitrary scheme-theoretic base change. -/
theorem ClosedProjective.closedImmersion_proj_baseChange_isProper {T : Scheme.{u}}
    (g : T ⟶ Spec (.of (𝒜 0))) :
    IsProper (Limits.pullback.snd (i ≫ Proj.toSpecZero 𝒜) g) := by
  infer_instance

/-- Finite type survives the same scheme-theoretic base change. -/
theorem ClosedProjective.closedImmersion_proj_baseChange_finiteType {T : Scheme.{u}}
    (g : T ⟶ Spec (.of (𝒜 0))) :
    LocallyOfFiniteType (Limits.pullback.snd (i ≫ Proj.toSpecZero 𝒜) g) ∧
      QuasiCompact (Limits.pullback.snd (i ≫ Proj.toSpecZero 𝒜) g) :=
  ClosedProjective.finiteType_of_isProper _

/-- An actual surjective identification of base rings yields a proper
morphism to the target affine scheme, without adding properness as a premise. -/
theorem ClosedProjective.closedImmersion_proj_changeBase_isProper {R : Type u} [CommRing R]
    (φ : R →+* (𝒜 0)) (hφ : Function.Surjective φ) :
    IsProper (i ≫ Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom φ)) := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ
  infer_instance

end ProjectiveSpectrum

/-- The standard complex projective-space structure morphism is proper.
The degree-zero ring is related to the complex base by the proved constants
isomorphism, rather than an assumed comparison. -/
instance ClosedProjective.projectiveSpaceToBase_isProper (n : ℕ) :
    IsProper (ProjectiveSpace.projectiveSpaceToBase n) := by
  unfold ProjectiveSpace.projectiveSpaceToBase
  let : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (ProjectiveSpace.degreeZeroConstants n).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (ProjectiveSpace.degreeZeroConstants n).toRingHom)
      (ProjectiveSpace.degreeZeroConstants n).surjective
  infer_instance

/-- Finite type of the actual complex projective-space structure morphism. -/
theorem ClosedProjective.projectiveSpaceToBase_finiteType (n : ℕ) :
    LocallyOfFiniteType (ProjectiveSpace.projectiveSpaceToBase n) ∧
      QuasiCompact (ProjectiveSpace.projectiveSpaceToBase n) :=
  ClosedProjective.finiteType_of_isProper _

/-- Standard complex projective space is a Noetherian scheme. -/
instance ClosedProjective.projectiveSpace_isNoetherian (n : ℕ) :
    AlgebraicGeometry.IsNoetherian (ProjectiveSpace.projectiveSpace n) :=
  ClosedProjective.isNoetherian_of_isProper_toSpec (ProjectiveSpace.projectiveSpaceToBase n)

/-- A genuine closed projective embedding supplies properness over the complex
base; this property need not be added as a field of a presentation. -/
theorem ClosedProjective.closedImmersion_projectiveSpace_isProper {X : Scheme} (n : ℕ)
    (i : X ⟶ ProjectiveSpace.projectiveSpace n) [IsClosedImmersion i] :
    IsProper (i ≫ ProjectiveSpace.projectiveSpaceToBase n) := by
  infer_instance

section

variable {X : Scheme} {f : X ⟶ ProjectiveSpace.complexBase} (P : SmoothProjective.ProjectivePresentation X f)

include P

/-- Properness is a consequence of the actual chosen projective embedding. -/
theorem SmoothProjective.ProjectivePresentation.isProper : IsProper f := by
  rw [P.structureMap_eq]
  exact ClosedProjective.closedImmersion_projectiveSpace_isProper P.ambientDimension P.embedding

/-- Both conditions of finite type follow from the chosen projective embedding. -/
theorem SmoothProjective.ProjectivePresentation.finiteType : LocallyOfFiniteType f ∧ QuasiCompact f := by
  let : IsProper f := P.isProper
  exact ClosedProjective.finiteType_of_isProper f

/-- The carrier of an actual complex projective presentation is Noetherian. -/
theorem SmoothProjective.ProjectivePresentation.isNoetherian : AlgebraicGeometry.IsNoetherian X := by
  let : IsProper f := P.isProper
  exact ClosedProjective.isNoetherian_of_isProper_toSpec f

/-- Finite presentation locally on source and target follows because the base
is the spectrum of the Noetherian field of complex numbers. -/
theorem SmoothProjective.ProjectivePresentation.locallyOfFinitePresentation : LocallyOfFinitePresentation f := by
  let : IsProper f := P.isProper
  infer_instance

/-- The actual projective presentation remains proper after any base change. -/
theorem SmoothProjective.ProjectivePresentation.baseChange_isProper {T : Scheme} (g : T ⟶ ProjectiveSpace.complexBase) :
    IsProper (Limits.pullback.snd f g) := by
  let : IsProper f := P.isProper
  infer_instance

end

variable (P : SmoothProjective.SmoothProjectivePresentation)

/-- The properness instance is proved from projectivity, not stored in the
smooth-projective data. -/
instance SmoothProjective.SmoothProjectivePresentation.isProper : IsProper P.structureMap := P.projective.isProper

/-- The scheme underlying a smooth projective presentation is Noetherian. -/
instance SmoothProjective.SmoothProjectivePresentation.isNoetherian : AlgebraicGeometry.IsNoetherian P.carrier :=
  P.projective.isNoetherian

/-- The structure morphism of a smooth projective presentation is of finite type. -/
theorem SmoothProjective.SmoothProjectivePresentation.finiteType : LocallyOfFiniteType P.structureMap ∧ QuasiCompact P.structureMap :=
  ClosedProjective.finiteType_of_isProper _

end OAI.AlgebraicGeometry.Foundations.Scheme
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenAmbient -/

/-! # Open Ambient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenAmbient.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: the scheme-theoretic graph factorization

These are the actual graph, fiber product, and projection of a complex
scheme morphism. The source structure morphism is written `f.left ≫ Y.structureMap`,
which equals `X.structureMap` by the defining equation of a morphism over ℂ.

This file constructs the geometry preceding the refined Gysin map. It does
not assert that a closed immersion alone supplies such a map on Chow groups.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}

/-- The fiber product containing the graph, with the source base map
written as the composite supplied by the morphism over the base. -/
def graphAmbient (f : X.toOver ⟶ Y.toOver) : Scheme :=
  pullback (f.left ≫ Y.structureMap) Y.structureMap

/-- The first projection of the graph's ambient product. -/
def graphFirstProjection (f : X.toOver ⟶ Y.toOver) : graphAmbient f ⟶ X.carrier :=
  pullback.fst (f.left ≫ Y.structureMap) Y.structureMap

/-- The projection along which flat pullback is used in the graph construction. -/
def graphSecondProjection (f : X.toOver ⟶ Y.toOver) : graphAmbient f ⟶ Y.carrier :=
  pullback.snd (f.left ≫ Y.structureMap) Y.structureMap

/-- The actual scheme-theoretic graph morphism. -/
def graph (f : X.toOver ⟶ Y.toOver) : X.carrier ⟶ graphAmbient f :=
  pullback.lift (𝟙 X.carrier) f.left (Category.id_comp (f.left ≫ Y.structureMap))

@[simp]
theorem graph_firstProjection (f : X.toOver ⟶ Y.toOver) :
    graph f ≫ graphFirstProjection f = 𝟙 X.carrier :=
  pullback.lift_fst _ _ _

@[simp]
theorem graph_secondProjection (f : X.toOver ⟶ Y.toOver) :
    graph f ≫ graphSecondProjection f = f.left :=
  pullback.lift_snd _ _ _

/-- The graph is a closed immersion because the target is separated over ℂ. -/
instance graph_isClosedImmersion (f : X.toOver ⟶ Y.toOver) :
    IsClosedImmersion (graph f) := by
  have hsep : IsSeparated Y.structureMap :=
    @IsProper.toIsSeparated _ _ _ Y.projective.isProper
  exact @IsSeparated.instIsClosedImmersionLiftSchemeId X.carrier Y.carrier Foundations.Scheme.ProjectiveSpace.complexBase
    f.left Y.structureMap hsep

/-- The first projection is the base change of the smooth target structure map. -/
instance graphFirstProjection_smooth (f : X.toOver ⟶ Y.toOver) :
    Smooth (graphFirstProjection f) := by
  exact AlgebraicGeometry.instSmoothFstScheme (f.left ≫ Y.structureMap) Y.structureMap

/-- The second projection is the base change of the smooth source structure map. -/
instance graphSecondProjection_smooth (f : X.toOver ⟶ Y.toOver) :
    Smooth (graphSecondProjection f) := by
  have hbase : f.left ≫ Y.structureMap = X.structureMap := f.w
  have : Smooth (f.left ≫ Y.structureMap) := hbase.symm ▸ X.smooth
  exact AlgebraicGeometry.instSmoothSndScheme (f.left ≫ Y.structureMap) Y.structureMap

instance graphSecondProjection_flat (f : X.toOver ⟶ Y.toOver) :
    Flat (graphSecondProjection f) := by infer_instance

end

/-! Actual open maps of source and target induce the corresponding open map of graph ambient products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y X' Y' : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (g : X'.toOver ⟶ Y'.toOver)
    (a : X'.toOver ⟶ X.toOver) (b : Y'.toOver ⟶ Y.toOver)

def graphOpenAmbientMap : graphAmbient g ⟶ graphAmbient f :=
  pullback.map (g.left ≫ Y'.structureMap) Y'.structureMap (f.left ≫ Y.structureMap) Y.structureMap
    a.left b.left (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    ((Category.comp_id _).trans (g.w.trans
      ((congrArg (fun k => a.left ≫ k) f.w).trans a.w).symm))
    ((Category.comp_id _).trans b.w.symm)

theorem graphOpenAmbientMap_first :
    graphOpenAmbientMap f g a b ≫ graphFirstProjection f = graphFirstProjection g ≫ a.left :=
  pullback.lift_fst ..

theorem graphOpenAmbientMap_second :
    graphOpenAmbientMap f g a b ≫ graphSecondProjection f = graphSecondProjection g ≫ b.left :=
  pullback.lift_snd ..

instance graphOpenAmbientMap_open [IsOpenImmersion a.left] [IsOpenImmersion b.left] :
    IsOpenImmersion (graphOpenAmbientMap f g a b) := by
  exact @Scheme.pullback_map_isOpenImmersion X'.carrier Y'.carrier Foundations.Scheme.ProjectiveSpace.complexBase X.carrier Y.carrier Foundations.Scheme.ProjectiveSpace.complexBase
    (g.left ≫ Y'.structureMap) Y'.structureMap (f.left ≫ Y.structureMap) Y.structureMap
    a.left b.left (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    ((Category.comp_id _).trans (g.w.trans
      ((congrArg (fun k => a.left ≫ k) f.w).trans a.w).symm))
    ((Category.comp_id _).trans b.w.symm)
    (inferInstanceAs (IsOpenImmersion a.left)) (inferInstanceAs (IsOpenImmersion b.left)) inferInstance

theorem graphOpenAmbientMap_graph (h : a ≫ f = g ≫ b) :
    graph g ≫ graphOpenAmbientMap f g a b = a.left ≫ graph f := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => graph g ≫ k) (graphOpenAmbientMap_first f g a b)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ a.left) (graph_firstProjection g)).trans
            ((Category.id_comp _).trans
              ((Category.comp_id _).symm.trans
                ((congrArg (fun k => a.left ≫ k) (graph_firstProjection f)).symm.trans
                  (Category.assoc _ _ _).symm))))))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => graph g ≫ k) (graphOpenAmbientMap_second f g a b)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ b.left) (graph_secondProjection g)).trans
            ((congrArg (fun k => k.left) h).symm.trans
              ((congrArg (fun k => a.left ≫ k) (graph_secondProjection f)).symm.trans
                (Category.assoc _ _ _).symm)))))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenAmbient.BundleCycles
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenAmbient"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Parameter -/

/-! # Parameter -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Parameter.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the global deformation parameter and the graph deformation

The local elements t agree under coefficient restriction, so they give a
global morphism from the glued deformation to the affine integer line. The
graph deformation uses the actual kernel ideal sheaf of the closed graph.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- The parameter line, with integers lifted only to match the scheme universe. -/
def deformationParameterLine : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The integer polynomial variable evaluates to the actual deformation parameter. -/
def deformationParameterRingMap (I : Ideal R) :
    Polynomial (ULift.{u} ℤ) →+* Iff.BundleCycles.deformationAlgebra I :=
  Polynomial.eval₂RingHom
    ((Int.castRingHom (Iff.BundleCycles.deformationAlgebra I)).comp ULift.ringEquiv.toRingHom)
    (Iff.BundleCycles.deformationParameter I)

@[simp]
theorem deformationParameterRingMap_X (I : Ideal R) :
    deformationParameterRingMap I Polynomial.X = Iff.BundleCycles.deformationParameter I :=
  Polynomial.eval₂_X _ _

theorem deformationParameterRingMap_natural (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hf : I ≤ J.comap f) :
    (Maps.BundleCycles.deformationMap I J f hf).comp (deformationParameterRingMap I) =
      deformationParameterRingMap J := by
  apply Polynomial.ringHom_ext
  · intro z
    simp only [RingHom.comp_apply, deformationParameterRingMap,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    change Maps.BundleCycles.deformationMap I J f hf (z.down : Iff.BundleCycles.deformationAlgebra I) =
      (z.down : Iff.BundleCycles.deformationAlgebra J)
    exact map_intCast _ _
  · change Maps.BundleCycles.deformationMap I J f hf (deformationParameterRingMap I Polynomial.X) =
      deformationParameterRingMap J Polynomial.X
    rw [deformationParameterRingMap_X, deformationParameterRingMap_X,
      Maps.BundleCycles.deformationMap_parameter]

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Compatible parameter morphisms on all affine deformation charts. -/
def deformationParameterCocone : Cocone (Global.Deformation.BundleCycles.deformationGlueData I).functor where
  pt := deformationParameterLine
  ι.app U := Spec.map (CommRingCat.ofHom (deformationParameterRingMap (I.ideal U)))
  ι.naturality {U V} f := by
    have h : CommRingCat.ofHom (deformationParameterRingMap (I.ideal V)) ≫
        (Global.Deformation.BundleCycles.deformationDiagram I).map f.op =
          CommRingCat.ofHom (deformationParameterRingMap (I.ideal U)) := by
      apply CommRingCat.hom_ext
      exact deformationParameterRingMap_natural (I.ideal V) (I.ideal U)
        (X.presheaf.map ((toOpensFunctor X).op.map f.op)).hom
        (I.ideal_le_comap_ideal (toOpens_mono f.le))
    exact (Spec.map_comp (CommRingCat.ofHom (deformationParameterRingMap (I.ideal V)))
      ((Global.Deformation.BundleCycles.deformationDiagram I).map f.op)).symm.trans (congrArg Spec.map h)

/-- The actual global parameter morphism of the deformation scheme. -/
def globalDeformationParameter : Global.Deformation.BundleCycles.globalDeformation I ⟶ deformationParameterLine :=
  colimit.desc _ (deformationParameterCocone I)

/-- The global parameter restricts to t on each affine deformation chart. -/
theorem globalDeformationParameter_on_chart (U : X.AffineZariskiSite) :
    (Global.Deformation.BundleCycles.globalDeformationCover I).f U ≫ globalDeformationParameter I =
      Spec.map (CommRingCat.ofHom (deformationParameterRingMap (I.ideal U))) :=
  colimit.ι_desc (deformationParameterCocone I) U

variable {P Q : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}

/-- The actual ideal sheaf defining the scheme-theoretic graph. -/
def graphIdeal (f : P.toOver ⟶ Q.toOver) : (Graph.OpenAmbient.BundleCycles.graphAmbient f).IdealSheafData := (Graph.OpenAmbient.BundleCycles.graph f).ker

/-- Deformation of the ambient product along the actual graph ideal. -/
def graphDeformation (f : P.toOver ⟶ Q.toOver) : Scheme := Global.Deformation.BundleCycles.globalDeformation (graphIdeal f)

/-- Projection of the graph deformation to the original ambient product. -/
def graphDeformationProjection (f : P.toOver ⟶ Q.toOver) :
    graphDeformation f ⟶ Graph.OpenAmbient.BundleCycles.graphAmbient f := Global.Deformation.BundleCycles.globalDeformationProjection (graphIdeal f)

/-- The graph deformation's global parameter. -/
def graphDeformationParameter (f : P.toOver ⟶ Q.toOver) :
    graphDeformation f ⟶ deformationParameterLine := globalDeformationParameter (graphIdeal f)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Parameter.BundleCycles
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Parameter"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientFiber -/

/-! # Quotient Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientFiber.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the universal property of the parameter-zero fiber

Quotienting by the image of an ideal gives the ring pushout. Applied to the
parameter ideal, this identifies the affine special fiber as a scheme
pullback, including its scheme structure.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- Extension of an ideal and quotient form a pushout of commutative rings. -/
theorem quotient_isPushout {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Ideal R) :
    IsPushout f (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.Quotient.mk (J.map f.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap (J.map f.hom) f.hom
        (fun _ hx => Ideal.mem_map_of_mem _ hx))) := by
  apply IsPushout.mk'
  · apply CommRingCat.hom_ext
    ext x : 1
    rfl
  · intro T a b hab _
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom hab
  · intro T a b hab
    have hker : J.map f.hom ≤ RingHom.ker a.hom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      change a (f x) = 0
      have h := ConcreteCategory.congr_hom hab x
      change a (f x) = b (Ideal.Quotient.mk J x) at h
      exact h.trans ((congrArg b (Ideal.Quotient.eq_zero_iff_mem.mpr hx)).trans
        b.hom.map_zero)
    refine ⟨CommRingCat.ofHom (Ideal.Quotient.lift _ a.hom hker), ?_, ?_⟩
    · apply CommRingCat.hom_ext
      ext x : 1
      rfl
    · apply CommRingCat.hom_ext
      apply Ideal.Quotient.ringHom_ext
      ext x : 1
      exact ConcreteCategory.congr_hom hab x

/-- The quotient pushout with a specified, equal image ideal. -/
theorem quotient_isPushout_of_map_eq {R S : CommRingCat.{u}} (f : R ⟶ S)
    (J : Ideal R) (K : Ideal S) (hJK : J.map f.hom = K) :
    IsPushout f (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.Quotient.mk K))
      (CommRingCat.ofHom (Ideal.quotientMap K f.hom
        (Ideal.map_le_iff_le_comap.mp hJK.le))) := by
  subst K
  exact quotient_isPushout f J

/-- The ideal defining zero in the actual parameter line. -/
def parameterZeroIdeal : Ideal (Polynomial (ULift.{u} ℤ)) := Ideal.span {Polynomial.X}

/-- The zero subscheme of the parameter line. -/
def parameterZeroBase : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal))

def parameterZeroInclusion : parameterZeroBase ⟶ Deformation.Parameter.BundleCycles.deformationParameterLine :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk parameterZeroIdeal))

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The parameter's zero ideal extends to precisely the deformation's special ideal. -/
theorem parameterZeroIdeal_map :
    parameterZeroIdeal.map (Deformation.Parameter.BundleCycles.deformationParameterRingMap I) = Deformation.Iff.BundleCycles.deformationSpecialIdeal I := by
  unfold parameterZeroIdeal Deformation.Iff.BundleCycles.deformationSpecialIdeal
  rw [Ideal.map_span, Set.image_singleton, Deformation.Parameter.BundleCycles.deformationParameterRingMap_X]

/-- The structural ring map of the special fiber over the zero subscheme. -/
def specialFiberToZeroRingMap :
    Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal →+* SpecialFiber.BundleCycles.DeformationSpecialRing I :=
  Ideal.quotientMap (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (Deformation.Parameter.BundleCycles.deformationParameterRingMap I)
    (Ideal.map_le_iff_le_comap.mp (parameterZeroIdeal_map I).le)

/-- The affine special fiber has the full universal property of the zero fiber. -/
theorem affineSpecialFiber_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I))))
      (Spec.map (CommRingCat.ofHom
        (R := Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal)
        (S := SpecialFiber.BundleCycles.DeformationSpecialRing I) (specialFiberToZeroRingMap I)))
      (Spec.map (CommRingCat.ofHom (Deformation.Parameter.BundleCycles.deformationParameterRingMap I)))
      parameterZeroInclusion := by
  apply AlgebraicGeometry.isPullback_SpecMap_of_isPushout
  exact quotient_isPushout_of_map_eq
    (R := CommRingCat.of (Polynomial (ULift.{u} ℤ)))
    (S := CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I))
    (CommRingCat.ofHom (Deformation.Parameter.BundleCycles.deformationParameterRingMap I))
    parameterZeroIdeal (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (parameterZeroIdeal_map I)

variable {S : Type u} [CommRing S]

/-- The parameter-zero structure map commutes with coefficient homomorphisms. -/
theorem specialFiberToZeroRingMap_natural (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) :
    (Deformation.Maps.BundleCycles.deformationSpecialMap I J f hf).comp (specialFiberToZeroRingMap I) =
      specialFiberToZeroRingMap J := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  change Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J)
      (Deformation.Maps.BundleCycles.deformationMap I J f hf (Deformation.Parameter.BundleCycles.deformationParameterRingMap I p)) =
    Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J) (Deformation.Parameter.BundleCycles.deformationParameterRingMap J p)
  exact congrArg (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J))
    (RingHom.congr_fun (Deformation.Parameter.BundleCycles.deformationParameterRingMap_natural I J f hf) p)

variable {X : Scheme.{u}} (K : X.IdealSheafData)

/-- The compatible structural maps of all zero-fiber charts. -/
def specialFiberZeroCocone : Cocone (Global.SpecialFiber.BundleCycles.specialFiberGlueData K).functor where
  pt := parameterZeroBase
  ι.app U := Spec.map (CommRingCat.ofHom
    (R := Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal)
    (S := SpecialFiber.BundleCycles.DeformationSpecialRing (K.ideal U)) (specialFiberToZeroRingMap (K.ideal U)))
  ι.naturality {U V} f := by
    have h : CommRingCat.ofHom
        (R := Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal)
        (S := SpecialFiber.BundleCycles.DeformationSpecialRing (K.ideal V)) (specialFiberToZeroRingMap (K.ideal V)) ≫
        (Global.SpecialFiber.BundleCycles.specialFiberDiagram K).map f.op =
      CommRingCat.ofHom
        (R := Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal)
        (S := SpecialFiber.BundleCycles.DeformationSpecialRing (K.ideal U)) (specialFiberToZeroRingMap (K.ideal U)) := by
      apply CommRingCat.hom_ext
      exact specialFiberToZeroRingMap_natural (K.ideal V) (K.ideal U)
        (X.presheaf.map ((toOpensFunctor X).op.map f.op)).hom
        (K.ideal_le_comap_ideal (toOpens_mono f.le))
    exact (Spec.map_comp (CommRingCat.ofHom
      (R := Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal)
      (S := SpecialFiber.BundleCycles.DeformationSpecialRing (K.ideal V)) (specialFiberToZeroRingMap (K.ideal V)))
      ((Global.SpecialFiber.BundleCycles.specialFiberDiagram K).map f.op)).symm.trans (congrArg Spec.map h)

/-- The global special fiber's structure morphism to parameter zero. -/
def globalSpecialFiberToZero : Global.SpecialFiber.BundleCycles.globalSpecialFiber K ⟶ parameterZeroBase :=
  colimit.desc _ (specialFiberZeroCocone K)

theorem globalSpecialFiberToZero_on_chart (U : X.AffineZariskiSite) :
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberCover K).f U ≫ globalSpecialFiberToZero K =
      Spec.map (CommRingCat.ofHom
        (R := Polynomial (ULift.{u} ℤ) ⧸ parameterZeroIdeal)
        (S := SpecialFiber.BundleCycles.DeformationSpecialRing (K.ideal U)) (specialFiberToZeroRingMap (K.ideal U))) :=
  colimit.ι_desc (specialFiberZeroCocone K) U

/-- Pullback squares descend from explicit pullback charts of an open cover. -/
theorem isPullback_of_cover_squares {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (k : B ⟶ D) (l : C ⟶ D)
    (V : B.OpenCover) (Z : V.I₀ → Scheme.{u})
    (a : ∀ i, Z i ⟶ A) (b : ∀ i, Z i ⟶ V.X i)
    (h : ∀ i, IsPullback (b i) (a i) (V.f i) f)
    (hs : ∀ i, IsPullback (b i) (a i ≫ g) (V.f i ≫ k) l) :
    IsPullback f g k l := by
  apply Scheme.isPullback_of_openCover f g k l V
  intro i
  let hi := (h i).flip
  apply (hs i).of_iso hi.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change b i ≫ 𝟙 (V.X i) = hi.isoPullback.hom ≫ pullback.snd f (V.f i)
    exact (Category.comp_id _).trans hi.isoPullback_hom_snd.symm
  · change (a i ≫ g) ≫ 𝟙 C = hi.isoPullback.hom ≫ (pullback.fst f (V.f i) ≫ g)
    exact (Category.comp_id _).trans
      ((congrArg (fun k => k ≫ g) hi.isoPullback_hom_fst.symm).trans (Category.assoc ..))
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The globally glued cone is exactly the scheme-theoretic fiber at parameter zero. -/
theorem globalSpecialFiber_isPullback :
    IsPullback (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap K) (globalSpecialFiberToZero K)
      (Deformation.Parameter.BundleCycles.globalDeformationParameter K) parameterZeroInclusion := by
  apply isPullback_of_cover_squares (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap K) (globalSpecialFiberToZero K)
    (Deformation.Parameter.BundleCycles.globalDeformationParameter K) parameterZeroInclusion (Global.Deformation.BundleCycles.globalDeformationCover K)
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberCover K).X (Global.SpecialFiber.BundleCycles.globalSpecialFiberCover K).f
    (fun U => Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (K.ideal U)))))
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_chart_isPullback K)
  intro U
  have h := affineSpecialFiber_isPullback (K.ideal U)
  rw [← globalSpecialFiberToZero_on_chart K U, ← Deformation.Parameter.BundleCycles.globalDeformationParameter_on_chart K U] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientFiber.BundleCycles
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientFiber"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties -/

/-! # Deformation Properties -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties.BundleCycles

noncomputable section

/-!
# LineBundleCycles: geometric properties of the global deformation

The affine chart pullback squares prove that the global structural map is
affine. Noetherianity then follows from the actual Noetherian extended-Rees
algebras and compactness over a Noetherian base.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- Evaluation at t = 1 on the actual extended-Rees subalgebra. -/
def deformationAtOne {R : Type u} [CommRing R] (J : Ideal R) :
    Deformation.Iff.BundleCycles.deformationAlgebra J →+* R :=
  (LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ)).comp (Deformation.Iff.BundleCycles.deformationAlgebra J).val.toRingHom

theorem deformationAtOne_algebraMap {R : Type u} [CommRing R] (J : Ideal R) :
    (deformationAtOne J).comp (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra J)) = RingHom.id R := by
  apply RingHom.ext
  intro r
  exact LaurentPolynomial.eval₂_C _ _ r

/-- A target-local morphism property can be checked on specified pullback charts. -/
theorem morphismProperty_of_cover_pullbacks (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {A B : Scheme.{u}} (f : A ⟶ B)
    (C : B.OpenCover) (Z : C.I₀ → Scheme.{u}) (a : ∀ i, Z i ⟶ A)
    (b : ∀ i, Z i ⟶ C.X i)
    (h : ∀ i, IsPullback (b i) (a i) (C.f i) f)
    (hb : ∀ i, P (b i)) : P f := by
  apply IsZariskiLocalAtTarget.of_openCover (P := P) C
  intro i
  let hi := (h i).flip
  have hc : P (hi.isoPullback.inv ≫ b i) :=
    (P.cancel_left_of_respectsIso _ _).mpr (hb i)
  exact (congrArg (fun k => P k) hi.isoPullback_inv_snd).mp hc

variable {X : Scheme.{u}} (I : X.IdealSheafData)

instance affineBaseRing_noetherian [IsLocallyNoetherian X] (U : X.AffineZariskiSite) :
    IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U

instance globalDeformationCover_isAffine (U : X.AffineZariskiSite) :
    IsAffine ((Deformation.BundleCycles.globalDeformationCover I).X U) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))))

instance globalDeformationCover_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion ((Deformation.BundleCycles.globalDeformationCover I).f U) :=
  (Deformation.BundleCycles.globalDeformationCover I).map_prop U

/-- The inverse image of a base affine open is exactly its deformation chart. -/
theorem globalDeformationProjection_preimage (U : X.AffineZariskiSite) :
    Deformation.BundleCycles.globalDeformationProjection I ⁻¹ᵁ U.1 = ((Deformation.BundleCycles.globalDeformationCover I).f U).opensRange := by
  have h := (Deformation.BundleCycles.deformationGlueData I).toBase_preimage_eq_opensRange_ι U
  change Deformation.BundleCycles.globalDeformationProjection I ⁻¹ᵁ U.1.ι.opensRange =
    ((Deformation.BundleCycles.globalDeformationCover I).f U).opensRange at h
  rw [Scheme.Opens.opensRange_ι] at h
  exact h

/-- The actual global deformation is affine over its original base. -/
instance globalDeformationProjection_isAffineHom :
    IsAffineHom (Deformation.BundleCycles.globalDeformationProjection I) := by
  constructor
  intro U hU
  let V : X.AffineZariskiSite := ⟨U, hU⟩
  have he : Deformation.BundleCycles.globalDeformationProjection I ⁻¹ᵁ U =
      ((Deformation.BundleCycles.globalDeformationCover I).f V).opensRange :=
    globalDeformationProjection_preimage I V
  exact he.symm ▸ isAffineOpen_opensRange ((Deformation.BundleCycles.globalDeformationCover I).f V)

/-- Noetherianity of the coefficient rings gives local Noetherianity of the gluing. -/
instance globalDeformation_isLocallyNoetherian [IsLocallyNoetherian X] :
    IsLocallyNoetherian (Deformation.BundleCycles.globalDeformation I) := by
  have : ∀ U, IsAffine ((Deformation.BundleCycles.globalDeformationCover I).X U) :=
    fun U => globalDeformationCover_isAffine I U
  apply (isLocallyNoetherian_iff_of_affine_openCover (Deformation.BundleCycles.globalDeformationCover I)).mpr
  intro U
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact isNoetherianRing_of_ringEquiv (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U))
    (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))).symm.commRingCatIsoToRingEquiv

/-- Over a Noetherian scheme the global deformation is itself Noetherian. -/
instance globalDeformation_isNoetherian [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian (Deformation.BundleCycles.globalDeformation I) := by
  have : CompactSpace (Deformation.BundleCycles.globalDeformation I) :=
    QuasiCompact.compactSpace_of_compactSpace (Deformation.BundleCycles.globalDeformationProjection I)
  exact ⟨⟩

/-- Evaluation at one supplies an actual section of each affine deformation chart. -/
def deformationChartSection (U : X.AffineZariskiSite) :
    U.1.toScheme ⟶ (Deformation.BundleCycles.globalDeformationCover I).X U :=
  U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (deformationAtOne (I.ideal U)))

theorem deformationChartSection_toBase (U : X.AffineZariskiSite) :
    deformationChartSection I U ≫ (Deformation.BundleCycles.deformationGlueData I).natTrans.app U = 𝟙 U.1.toScheme := by
  let a : Γ(X, U.1) ⟶ CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) :=
    CommRingCat.ofHom (algebraMap Γ(X, U.1) (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))
  let b : CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) ⟶ Γ(X, U.1) :=
    CommRingCat.ofHom (deformationAtOne (I.ideal U))
  have hab : a ≫ b = 𝟙 Γ(X, U.1) :=
    CommRingCat.hom_ext (deformationAtOne_algebraMap (I.ideal U))
  have hs : Spec.map b ≫ Spec.map a = 𝟙 (Spec Γ(X, U.1)) :=
    (Spec.map_comp a b).symm.trans ((congrArg Spec.map hab).trans (Spec.map_id _))
  change (U.2.isoSpec.hom ≫ Spec.map b) ≫ (Spec.map a ≫ U.2.isoSpec.inv) = _
  rw [Category.assoc, ← Category.assoc (Spec.map b), hs, Category.id_comp, U.2.isoSpec.hom_inv_id]

/-- Every base point has a point above it in the deformation, namely at t = 1. -/
theorem globalDeformationProjection_surjective : Function.Surjective (Deformation.BundleCycles.globalDeformationProjection I) := by
  intro x
  let U : X.AffineZariskiSite := (directedCover X).idx x
  obtain ⟨y, hy⟩ := (directedCover X).covers x
  let z := deformationChartSection I U y
  refine ⟨(Deformation.BundleCycles.globalDeformationCover I).f U z, ?_⟩
  have hbase := congrArg (fun k => k z) ((Deformation.BundleCycles.deformationGlueData I).ι_toBase U)
  have hsection := congrArg (fun k => k y) (deformationChartSection_toBase I U)
  change (Deformation.BundleCycles.deformationGlueData I).natTrans.app U z = y at hsection
  change Deformation.BundleCycles.globalDeformationProjection I ((Deformation.BundleCycles.globalDeformationCover I).f U z) =
    U.1.ι ((Deformation.BundleCycles.deformationGlueData I).natTrans.app U z) at hbase
  exact hbase.trans ((congrArg U.1.ι hsection).trans hy)

/-- Empty affine base opens may be discarded without losing any deformation point. -/
def nonemptyDeformationCover : (Deformation.BundleCycles.globalDeformation I).OpenCover :=
  Scheme.Cover.mkOfCovers {U : X.AffineZariskiSite // Nonempty U.1}
    (fun U => (Deformation.BundleCycles.globalDeformationCover I).X U.1)
    (fun U => (Deformation.BundleCycles.globalDeformationCover I).f U.1)
    (by
      intro x
      obtain ⟨U, y, rfl⟩ := (Deformation.BundleCycles.globalDeformationCover I).exists_eq x
      exact ⟨⟨U, ⟨(Deformation.BundleCycles.deformationGlueData I).natTrans.app U y⟩⟩, y, rfl⟩)
    (fun U => globalDeformationCover_isOpenImmersion I U.1)

instance nonemptyDeformationCover_isIntegral [IsIntegral X]
    (U : (nonemptyDeformationCover I).I₀) :
    IsIntegral ((nonemptyDeformationCover I).X U) := by
  have : Nonempty U.1.1 := U.2
  have : IsDomain Γ(X, U.1.1) := inferInstance
  exact inferInstanceAs (IsIntegral (Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U.1)))))

instance globalDeformation_isReduced [IsIntegral X] : IsReduced (Deformation.BundleCycles.globalDeformation I) := by
  have : ∀ U, IsReduced ((nonemptyDeformationCover I).X U) := fun U => by
    have := nonemptyDeformationCover_isIntegral I U
    infer_instance
  exact IsReduced.of_openCover (Deformation.BundleCycles.globalDeformation I) (nonemptyDeformationCover I)

/-- Any two retained deformation charts intersect above their nonempty base intersection. -/
theorem nonemptyDeformationCover_pairwise_inter [IsIntegral X] :
    Pairwise (fun U V : (nonemptyDeformationCover I).I₀ =>
      ¬ Disjoint ((nonemptyDeformationCover I).f U).opensRange
        ((nonemptyDeformationCover I).f V).opensRange) := by
  intro U V _
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.1.1.isOpen V.1.1.isOpen
    (Set.nonempty_coe_sort.mp U.2) (Set.nonempty_coe_sort.mp V.2)
  obtain ⟨y, hy⟩ := globalDeformationProjection_surjective I x
  have hU : y ∈ ((nonemptyDeformationCover I).f U).opensRange := by
    change y ∈ ((Deformation.BundleCycles.globalDeformationCover I).f U.1).opensRange
    rw [← globalDeformationProjection_preimage I U.1]
    change Deformation.BundleCycles.globalDeformationProjection I y ∈ U.1.1
    exact hy.symm ▸ hxU
  have hV : y ∈ ((nonemptyDeformationCover I).f V).opensRange := by
    change y ∈ ((Deformation.BundleCycles.globalDeformationCover I).f V.1).opensRange
    rw [← globalDeformationProjection_preimage I V.1]
    change Deformation.BundleCycles.globalDeformationProjection I y ∈ V.1.1
    exact hy.symm ▸ hxV
  intro hd
  exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr hd) hU hV

/-- Integrality of the base implies integrality of its actual global deformation. -/
instance globalDeformation_isIntegral [IsIntegral X] : IsIntegral (Deformation.BundleCycles.globalDeformation I) := by
  have hpre : ∀ U : (nonemptyDeformationCover I).I₀,
      IsPreirreducible (((nonemptyDeformationCover I).f U).opensRange : Set (Deformation.BundleCycles.globalDeformation I)) := by
    intro U
    have := nonemptyDeformationCover_isIntegral I U
    have h := (IrreducibleSpace.isIrreducible_univ ((nonemptyDeformationCover I).X U)).2.image
      ((nonemptyDeformationCover I).f U) ((nonemptyDeformationCover I).f U).continuous.continuousOn
    simp only [Set.image_univ] at h
    exact h
  have : PreirreducibleSpace (Deformation.BundleCycles.globalDeformation I) := ⟨IsPreirreducible.of_subset_iUnion
    (nonemptyDeformationCover_pairwise_inter I) hpre isOpen_univ
    (by
      change Set.univ ⊆ ⋃ U, Set.range ((nonemptyDeformationCover I).f U)
      rw [(nonemptyDeformationCover I).iUnion_range])⟩
  have : Nonempty (Deformation.BundleCycles.globalDeformation I) := by
    obtain ⟨y, _⟩ := globalDeformationProjection_surjective I (Classical.choice (inferInstance : Nonempty X))
    exact ⟨y⟩
  have : IrreducibleSpace (Deformation.BundleCycles.globalDeformation I) :=
    { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties.BundleCycles
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SupportDeformation -/

/-! # Support Deformation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SupportDeformation.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the global deformation of a closed support

The affine extended-Rees algebras over the actual support quotients glue
to a scheme. The coefficient quotient maps give a closed immersion into
the ambient deformation, with the expected affine restrictions.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I P : X.IdealSheafData)

def supportDeformationGlueData : (directedCover X).RelativeGluingData :=
  relativeGluingData (Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered I P)

instance supportDeformationGlueData_isLocallyDirected :
    ((supportDeformationGlueData I P).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The global deformation of the closed support with its restricted center. -/
def globalSupportDeformation : Scheme := (supportDeformationGlueData I P).glued

def globalSupportDeformationCover : (globalSupportDeformation I P).OpenCover :=
  (supportDeformationGlueData I P).cover

def globalSupportDeformationProjection : globalSupportDeformation I P ⟶ X :=
  (supportDeformationGlueData I P).toBase

/-- The actual global map induced by quotienting the ambient coefficients. -/
def globalSupportDeformationMap : globalSupportDeformation I P ⟶ Deformation.BundleCycles.globalDeformation I :=
  Relative.AffineMap.BundleCycles.relativeAffineMap (Deformation.BundleCycles.deformationDiagramMap_coequifibered I)
    (Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered I P) (Support.DeformationDiagram.BundleCycles.deformationToSupportDiagram I P)

theorem globalSupportDeformationMap_on_chart (U : X.AffineZariskiSite) :
    (globalSupportDeformationCover I P).f U ≫ globalSupportDeformationMap I P =
      Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion (I.ideal U) (P.ideal U) ≫ (Deformation.BundleCycles.globalDeformationCover I).f U :=
  Relative.AffineMap.BundleCycles.relativeAffineMap_on_chart (Deformation.BundleCycles.deformationDiagramMap_coequifibered I)
    (Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered I P) (Support.DeformationDiagram.BundleCycles.deformationToSupportDiagram I P) U

theorem globalSupportDeformationMap_toBase :
    globalSupportDeformationMap I P ≫ Deformation.BundleCycles.globalDeformationProjection I =
      globalSupportDeformationProjection I P :=
  Relative.AffineMap.BundleCycles.relativeAffineMap_toBase (Deformation.BundleCycles.deformationDiagramMap_coequifibered I)
    (Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered I P) (Support.DeformationDiagram.BundleCycles.deformationToSupportDiagram I P) rfl

theorem globalSupportDeformationMap_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion (I.ideal U) (P.ideal U))
      ((globalSupportDeformationCover I P).f U) ((Deformation.BundleCycles.globalDeformationCover I).f U)
      (globalSupportDeformationMap I P) :=
  Relative.AffineMap.BundleCycles.relativeAffineMap_chart_isPullback (Deformation.BundleCycles.deformationDiagramMap_coequifibered I)
    (Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered I P) (Support.DeformationDiagram.BundleCycles.deformationToSupportDiagram I P) rfl U

/-- Deformation of a closed support remains a closed subscheme of the ambient deformation. -/
instance globalSupportDeformationMap_isClosedImmersion :
    IsClosedImmersion (globalSupportDeformationMap I P) :=
  Relative.AffineMap.BundleCycles.relativeAffineMap_isClosedImmersion (Deformation.BundleCycles.deformationDiagramMap_coequifibered I)
    (Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered I P) (Support.DeformationDiagram.BundleCycles.deformationToSupportDiagram I P) rfl
    (Support.DeformationDiagram.BundleCycles.deformationToSupportDiagram_surjective I P)

instance globalSupportDeformationCover_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion ((globalSupportDeformationCover I P).f U) :=
  (globalSupportDeformationCover I P).map_prop U

theorem globalSupportDeformationProjection_preimage (U : X.AffineZariskiSite) :
    globalSupportDeformationProjection I P ⁻¹ᵁ U.1 =
      ((globalSupportDeformationCover I P).f U).opensRange := by
  have h := (supportDeformationGlueData I P).toBase_preimage_eq_opensRange_ι U
  change globalSupportDeformationProjection I P ⁻¹ᵁ U.1.ι.opensRange =
    ((globalSupportDeformationCover I P).f U).opensRange at h
  rw [Scheme.Opens.opensRange_ι] at h
  exact h

/-- The support deformation is Noetherian when the ambient base is Noetherian. -/
instance globalSupportDeformation_isNoetherian [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian (globalSupportDeformation I P) := by
  have : IsLocallyNoetherian (globalSupportDeformation I P) :=
    LocallyOfFiniteType.isLocallyNoetherian (globalSupportDeformationMap I P)
  have : CompactSpace (globalSupportDeformation I P) :=
    QuasiCompact.compactSpace_of_compactSpace (globalSupportDeformationMap I P)
  exact ⟨⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SupportDeformation.BundleCycles
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SupportDeformation"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Projection -/

/-! # Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Projection.BundleCycles

noncomputable section

/-!
# LineBundleCycles: projection of the support deformation to the actual closed scheme

The quotient coefficient spectra are the standard affine charts of the
closed subscheme. Their constant maps glue to a projection from its
deformation, and evaluation at one proves this projection surjective.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I P : X.IdealSheafData)

/-- The standard affine coefficient chart in the actual closed support scheme. -/
def supportCoefficientChart (U : X.AffineZariskiSite) :
    Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) ⟶ P.subscheme := P.subschemeCover.f U

instance supportCoefficientChart_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion (supportCoefficientChart P U) := P.subschemeCover.openCover.map_prop U

theorem supportCoefficientChart_range (U : X.AffineZariskiSite) :
    (supportCoefficientChart P U).opensRange = P.subschemeι ⁻¹ᵁ U.1 :=
  P.opensRange_subschemeCover_map U

/-- The constants map from a support deformation chart to its coefficient spectrum. -/
def supportDeformationChartProjection (U : X.AffineZariskiSite) :
    (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U ⟶ Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) :=
  Spec.map (CommRingCat.ofHom (algebraMap ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))
    (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))))

/-- The chart projection regarded as a map to the whole closed support. -/
def supportDeformationChartToSupport (U : X.AffineZariskiSite) :
    (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U ⟶ P.subscheme :=
  supportDeformationChartProjection I P U ≫ supportCoefficientChart P U

theorem supportDeformationChartToSupport_toBase (U : X.AffineZariskiSite) :
    supportDeformationChartToSupport I P U ≫ P.subschemeι =
      (Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).natTrans.app U ≫ U.1.ι := by
  let a : Γ(X, U.1) ⟶ (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (P.ideal U))
  let b : (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U) ⟶
      (DeformationDiagram.BundleCycles.supportDeformationDiagram I P).obj (.op U) :=
    CommRingCat.ofHom (algebraMap ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))
      (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)))
  have hab : a ≫ b = (DeformationDiagram.BundleCycles.supportDeformationDiagramMap I P).app (.op U) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (DeformationDiagram.BundleCycles.supportDeformationDiagramMap_apply I P U r).symm
  have hP : supportCoefficientChart P U ≫ P.subschemeι =
      (Spec.map a ≫ U.2.isoSpec.inv) ≫ U.1.ι := P.subschemeCover_map_subschemeι U
  have hspec : Spec.map b ≫ Spec.map a =
      Spec.map ((DeformationDiagram.BundleCycles.supportDeformationDiagramMap I P).app (.op U)) :=
    (Spec.map_comp a b).symm.trans (congrArg Spec.map hab)
  change (Spec.map b ≫ supportCoefficientChart P U) ≫ P.subschemeι =
    (Spec.map ((DeformationDiagram.BundleCycles.supportDeformationDiagramMap I P).app (.op U)) ≫ U.2.isoSpec.inv) ≫ U.1.ι
  rw [Category.assoc, hP, ← Category.assoc, ← Category.assoc, hspec]
  rfl

/-- The chart maps to the support agree on every affine transition. -/
def supportProjectionCocone : Cocone (Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).functor where
  pt := P.subscheme
  ι.app U := supportDeformationChartToSupport I P U
  ι.naturality {U V} f := by
    apply (cancel_mono P.subschemeι).mp
    have h : (Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).functor.map f ≫
        ((Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).natTrans.app V ≫ V.1.ι) =
      (Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).natTrans.app U ≫ U.1.ι :=
      (((Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).natTrans ≫
        (directedCover X).functorOfLocallyDirectedHomBase).naturality f).trans (Category.comp_id _)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).functor.map f ≫ k)
        (supportDeformationChartToSupport_toBase I P V)).trans
      (h.trans ((supportDeformationChartToSupport_toBase I P U).symm.trans
        (congrArg (fun k => k ≫ P.subschemeι)
          (Category.comp_id (supportDeformationChartToSupport I P U)).symm))))

/-- The actual structural projection to the closed support scheme. -/
def globalSupportDeformationToSupport : Global.SupportDeformation.BundleCycles.globalSupportDeformation I P ⟶ P.subscheme :=
  colimit.desc _ (supportProjectionCocone I P)

theorem globalSupportDeformationToSupport_on_chart (U : X.AffineZariskiSite) :
    (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U ≫ globalSupportDeformationToSupport I P =
      supportDeformationChartToSupport I P U :=
  colimit.ι_desc (supportProjectionCocone I P) U

theorem globalSupportDeformationToSupport_toBase :
    globalSupportDeformationToSupport I P ≫ P.subschemeι = Global.SupportDeformation.BundleCycles.globalSupportDeformationProjection I P := by
  apply (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).hom_ext
  intro U
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ P.subschemeι) (globalSupportDeformationToSupport_on_chart I P U)).trans
    ((supportDeformationChartToSupport_toBase I P U).trans
      ((Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).ι_toBase U).symm))

/-- Evaluation at t = 1 on a support chart. -/
def supportDeformationChartSection (U : X.AffineZariskiSite) :
    Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) ⟶ (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U :=
  Spec.map (CommRingCat.ofHom (Global.DeformationProperties.BundleCycles.deformationAtOne (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)))

theorem supportDeformationChartSection_projection (U : X.AffineZariskiSite) :
    supportDeformationChartSection I P U ≫ supportDeformationChartProjection I P U = 𝟙 _ := by
  let a : (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U) ⟶
      (DeformationDiagram.BundleCycles.supportDeformationDiagram I P).obj (.op U) :=
    CommRingCat.ofHom (algebraMap ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))
      (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)))
  let b : (DeformationDiagram.BundleCycles.supportDeformationDiagram I P).obj (.op U) ⟶
      (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U) :=
    CommRingCat.ofHom (Global.DeformationProperties.BundleCycles.deformationAtOne (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
  have hab : a ≫ b = 𝟙 _ := CommRingCat.hom_ext (Global.DeformationProperties.BundleCycles.deformationAtOne_algebraMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
  exact (Spec.map_comp a b).symm.trans ((congrArg Spec.map hab).trans (Spec.map_id _))

/-- Every point of the actual support has a point above it at t = 1. -/
theorem globalSupportDeformationToSupport_surjective :
    Function.Surjective (globalSupportDeformationToSupport I P) := by
  intro x
  obtain ⟨U, y, hy⟩ := P.subschemeCover.openCover.exists_eq x
  let z := supportDeformationChartSection I P U y
  refine ⟨(Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U z, ?_⟩
  have h := congrArg (fun k => k z) (globalSupportDeformationToSupport_on_chart I P U)
  have hs := congrArg (fun k => k y) (supportDeformationChartSection_projection I P U)
  change supportDeformationChartProjection I P U z = y at hs
  change globalSupportDeformationToSupport I P ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U z) =
    supportCoefficientChart P U (supportDeformationChartProjection I P U z) at h
  exact h.trans ((congrArg (supportCoefficientChart P U) hs).trans hy)

/-- The support's standard affine opens pull back to the expected deformation charts. -/
theorem globalSupportDeformationToSupport_preimage (U : X.AffineZariskiSite) :
    globalSupportDeformationToSupport I P ⁻¹ᵁ (supportCoefficientChart P U).opensRange =
      ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U).opensRange := by
  rw [supportCoefficientChart_range, ← Scheme.Hom.comp_preimage,
    globalSupportDeformationToSupport_toBase, Global.SupportDeformation.BundleCycles.globalSupportDeformationProjection_preimage]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Projection.BundleCycles
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Projection"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Integrality -/

/-! # Integrality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Integrality.BundleCycles

noncomputable section

/-!
# LineBundleCycles: integrality of the deformation of an integral closed support

The coefficient spectra are genuine open subschemes of the integral support.
Their nonempty deformation charts are integral and meet above intersections
of the support charts. This proves integrality without assuming that the
ambient scheme or the closed support is smooth.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I P : X.IdealSheafData)

/-- Discard coefficient charts that do not meet the closed support. -/
def nonemptySupportDeformationCover : (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).OpenCover :=
  Scheme.Cover.mkOfCovers
    {U : X.AffineZariskiSite // Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))}
    (fun U => (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U.1)
    (fun U => (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U.1)
    (by
      intro x
      obtain ⟨U, y, rfl⟩ := (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).exists_eq x
      exact ⟨⟨U, ⟨Projection.BundleCycles.supportDeformationChartProjection I P U y⟩⟩, y, rfl⟩)
    (fun U => Global.SupportDeformation.BundleCycles.globalSupportDeformationCover_isOpenImmersion I P U.1)

variable [IsIntegral P.subscheme]

/-- A nonempty coefficient chart of the integral support has an actual domain as its ring. -/
instance supportCoefficientRing_isDomain (U : X.AffineZariskiSite)
    [Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))] :
    IsDomain ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) :=
  (affine_isIntegral_iff _).mp (isIntegral_of_isOpenImmersion (Projection.BundleCycles.supportCoefficientChart P U))

instance nonemptySupportDeformationCover_isIntegral
    (U : (nonemptySupportDeformationCover I P).I₀) :
    IsIntegral ((nonemptySupportDeformationCover I P).X U) := by
  have : Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U.1))) := U.2
  have : IsDomain ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U.1)) := supportCoefficientRing_isDomain P U.1
  exact inferInstanceAs (IsIntegral (Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U.1)))))

instance globalSupportDeformation_isReduced : IsReduced (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) := by
  have : ∀ U, IsReduced ((nonemptySupportDeformationCover I P).X U) := fun U => by
    have := nonemptySupportDeformationCover_isIntegral I P U
    infer_instance
  exact IsReduced.of_openCover (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) (nonemptySupportDeformationCover I P)

/-- Retained deformation charts intersect because their support charts intersect. -/
theorem nonemptySupportDeformationCover_pairwise_inter :
    Pairwise (fun U V : (nonemptySupportDeformationCover I P).I₀ =>
      ¬ Disjoint ((nonemptySupportDeformationCover I P).f U).opensRange
        ((nonemptySupportDeformationCover I P).f V).opensRange) := by
  intro U V _
  have hU : ((Projection.BundleCycles.supportCoefficientChart P U.1).opensRange : Set P.subscheme).Nonempty :=
    ⟨Projection.BundleCycles.supportCoefficientChart P U.1 (Classical.choice U.2), Classical.choice U.2, rfl⟩
  have hV : ((Projection.BundleCycles.supportCoefficientChart P V.1).opensRange : Set P.subscheme).Nonempty :=
    ⟨Projection.BundleCycles.supportCoefficientChart P V.1 (Classical.choice V.2), Classical.choice V.2, rfl⟩
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter
    (Projection.BundleCycles.supportCoefficientChart P U.1).opensRange.isOpen (Projection.BundleCycles.supportCoefficientChart P V.1).opensRange.isOpen hU hV
  obtain ⟨y, hy⟩ := Projection.BundleCycles.globalSupportDeformationToSupport_surjective I P x
  have hyU : y ∈ ((nonemptySupportDeformationCover I P).f U).opensRange := by
    change y ∈ ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U.1).opensRange
    rw [← Projection.BundleCycles.globalSupportDeformationToSupport_preimage I P U.1]
    change Projection.BundleCycles.globalSupportDeformationToSupport I P y ∈ (Projection.BundleCycles.supportCoefficientChart P U.1).opensRange
    exact hy.symm ▸ hxU
  have hyV : y ∈ ((nonemptySupportDeformationCover I P).f V).opensRange := by
    change y ∈ ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f V.1).opensRange
    rw [← Projection.BundleCycles.globalSupportDeformationToSupport_preimage I P V.1]
    change Projection.BundleCycles.globalSupportDeformationToSupport I P y ∈ (Projection.BundleCycles.supportCoefficientChart P V.1).opensRange
    exact hy.symm ▸ hxV
  intro hd
  exact Set.disjoint_left.mp (Opens.coe_disjoint.mpr hd) hyU hyV

/-- The global deformation of an actual integral support is integral. -/
instance globalSupportDeformation_isIntegral : IsIntegral (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) := by
  have hpre : ∀ U : (nonemptySupportDeformationCover I P).I₀,
      IsPreirreducible (((nonemptySupportDeformationCover I P).f U).opensRange :
        Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)) := by
    intro U
    have := nonemptySupportDeformationCover_isIntegral I P U
    have h := (IrreducibleSpace.isIrreducible_univ ((nonemptySupportDeformationCover I P).X U)).2.image
      ((nonemptySupportDeformationCover I P).f U)
      ((nonemptySupportDeformationCover I P).f U).continuous.continuousOn
    simp only [Set.image_univ] at h
    exact h
  have : PreirreducibleSpace (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) := ⟨IsPreirreducible.of_subset_iUnion
    (nonemptySupportDeformationCover_pairwise_inter I P) hpre isOpen_univ (by
      change Set.univ ⊆ ⋃ U, Set.range ((nonemptySupportDeformationCover I P).f U)
      rw [(nonemptySupportDeformationCover I P).iUnion_range])⟩
  have : Nonempty (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) := by
    obtain ⟨y, _⟩ := Projection.BundleCycles.globalSupportDeformationToSupport_surjective I P
      (Classical.choice (inferInstance : Nonempty P.subscheme))
    exact ⟨y⟩
  have : IrreducibleSpace (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) :=
    { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Integrality.BundleCycles
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Integrality"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Dimension -/

/-! # Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Dimension.BundleCycles

noncomputable section

/-!
# LineBundleCycles: dimension of the global deformation and support deformations

Actual open immersion charts and the proved constants maps identify the
global structure morphisms with the affine coefficient-field actions.
The one-parameter transcendence calculation therefore gives the exact
global dimension increase, including for singular integral supports.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- An actual deformation chart determines the global dimension increase. -/
theorem deformation_dimension_of_chart (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R] (I : Ideal R)
    {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (a : Spec (CommRingCat.of R) ⟶ A) [IsOpenImmersion a]
    (b : Spec (CommRingCat.of (Iff.BundleCycles.deformationAlgebra I)) ⟶ B) [IsOpenImmersion b]
    (g : B ⟶ A)
    (h : b ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R (Iff.BundleCycles.deformationAlgebra I))) ≫ a)
    (f : A ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (g ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  let α : CommRingCat.of k ⟶ CommRingCat.of R := Spec.preimage (a ≫ f)
  let : Algebra k R := α.hom.toAlgebra
  have hα : Spec.map α = a ≫ f := Spec.map_preimage _
  have hfα : LocallyOfFiniteType (Spec.map α) :=
    (congrArg (fun q => LocallyOfFiniteType q) hα).mpr inferInstance
  have : Algebra.FiniteType k R :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hfα
  let := Transcendence.BundleCycles.deformationScalarAlgebra I k
  let c : CommRingCat.of R ⟶ CommRingCat.of (Iff.BundleCycles.deformationAlgebra I) :=
    CommRingCat.ofHom (algebraMap R (Iff.BundleCycles.deformationAlgebra I))
  have hαc : α ≫ c = CommRingCat.ofHom (algebraMap k (Iff.BundleCycles.deformationAlgebra I)) := rfl
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap k (Iff.BundleCycles.deformationAlgebra I))) =
      Spec.map c ≫ (a ≫ f) :=
    (congrArg Spec.map hαc.symm).trans
      ((Spec.map_comp α c).trans (congrArg (fun q => Spec.map c ≫ q) hα))
  have hb : b ≫ (g ≫ f) = Spec.map (CommRingCat.ofHom (algebraMap k (Iff.BundleCycles.deformationAlgebra I))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ f) h).trans ((Category.assoc _ _ _).trans hspec.symm))
  have haDim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = (Algebra.trdeg k R).toNat :=
    (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion a f).symm.trans
      ((congrArg (fun q => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension q) hα.symm).trans
        (Affine.DimensionBridge.BundleCycles.schemeTranscendenceDimension_spec_algebra k R))
  exact (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion b (g ≫ f)).symm.trans
    ((congrArg (fun q => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension q) hb).trans
    ((Affine.DimensionBridge.BundleCycles.schemeTranscendenceDimension_spec_algebra k (Iff.BundleCycles.deformationAlgebra I)).trans
    ((Transcendence.BundleCycles.deformationAlgebra_trdeg_toNat I k).trans (congrArg (fun n => n + 1) haDim.symm))))

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual global deformation of an integral scheme has one additional dimension. -/
theorem globalDeformation_dimension (I : X.IdealSheafData) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  let x : X := Classical.choice inferInstance
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let V : X.AffineZariskiSite := ⟨U, hU⟩
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsDomain Γ(X, U) := inferInstance
  have : IsOpenImmersion ((Global.Deformation.BundleCycles.globalDeformationCover I).f V) :=
    Global.DeformationProperties.BundleCycles.globalDeformationCover_isOpenImmersion I V
  have hbase : (Global.Deformation.BundleCycles.globalDeformationCover I).f V ≫ Global.Deformation.BundleCycles.globalDeformationProjection I =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Iff.BundleCycles.deformationAlgebra (I.ideal V))))) ≫ hU.fromSpec := by
    have h0 : (Global.Deformation.BundleCycles.globalDeformationCover I).f V ≫ Global.Deformation.BundleCycles.globalDeformationProjection I =
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Iff.BundleCycles.deformationAlgebra (I.ideal V)))) ≫
          hU.isoSpec.inv) ≫ U.ι := (Global.Deformation.BundleCycles.deformationGlueData I).ι_toBase V
    exact h0.trans ((Category.assoc _ _ _).trans
      (congrArg (fun q => Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (Iff.BundleCycles.deformationAlgebra (I.ideal V)))) ≫ q) hU.isoSpec_inv_ι))
  exact @deformation_dimension_of_chart k _ Γ(X, U) _ _ (I.ideal V)
    X (Global.Deformation.BundleCycles.globalDeformation I) _ _ hU.fromSpec inferInstance
    ((Global.Deformation.BundleCycles.globalDeformationCover I).f V) (Global.DeformationProperties.BundleCycles.globalDeformationCover_isOpenImmersion I V)
    (Global.Deformation.BundleCycles.globalDeformationProjection I) hbase f inferInstance

/-- The global deformation of a singular integral closed support has exactly one additional dimension. -/
theorem globalSupportDeformation_dimension (I P : X.IdealSheafData) [IsIntegral P.subscheme]
    (f : P.subscheme ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ f) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  let x : P.subscheme := Classical.choice inferInstance
  obtain ⟨U, y, _⟩ := P.subschemeCover.openCover.exists_eq x
  have : Nonempty (Spec ((Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))) := ⟨y⟩
  have : IsDomain ((Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) := Support.Integrality.BundleCycles.supportCoefficientRing_isDomain P U
  have : IsOpenImmersion (Support.Projection.BundleCycles.supportCoefficientChart P U) :=
    Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion P U
  have : IsOpenImmersion ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U) :=
    Global.SupportDeformation.BundleCycles.globalSupportDeformationCover_isOpenImmersion I P U
  exact @deformation_dimension_of_chart k _ ((Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) _ _
    (Support.CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) P.subscheme (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) _ _
    (Support.Projection.BundleCycles.supportCoefficientChart P U) (Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion P U)
    ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U) (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover_isOpenImmersion I P U)
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P)
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport_on_chart I P U) f inferInstance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Dimension.BundleCycles
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Dimension"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationFiniteType -/

/-! # Deformation Finite Type -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationFiniteType.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite type of the actual global deformation projections

The extended-Rees constants maps have finite type over Noetherian
coefficient rings. Source-locality transfers this property from the
constructed charts to the global projections.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The spectrum of the actual constants map has finite type. -/
theorem deformationConstants_locallyOfFiniteType {R : Type u} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I)))) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr
      (Deformation.FiniteType.BundleCycles.deformationAlgebra_finiteType I (IsNoetherian.noetherian I)))

/-- The global deformation projection is locally of finite type over a locally Noetherian base. -/
instance globalDeformationProjection_locallyOfFiniteType (I : X.IdealSheafData) :
    LocallyOfFiniteType (Deformation.BundleCycles.globalDeformationProjection I) := by
  let : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (Deformation.BundleCycles.globalDeformationCover I)
  intro U
  have : IsNoetherianRing Γ(X, U.1) := DeformationProperties.BundleCycles.affineBaseRing_noetherian U
  have hc := deformationConstants_locallyOfFiniteType (I.ideal U)
  have ht : LocallyOfFiniteType
      ((Deformation.BundleCycles.deformationGlueData I).natTrans.app U ≫ U.1.ι) := by
    change LocallyOfFiniteType ((Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U.1) (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))) ≫ U.2.isoSpec.inv) ≫ U.1.ι)
    infer_instance
  exact (congrArg (fun f => LocallyOfFiniteType f) ((Deformation.BundleCycles.deformationGlueData I).ι_toBase U)).mpr ht

/-- The projection to the actual closed support is locally of finite type. -/
instance globalSupportDeformationToSupport_locallyOfFiniteType (I P : X.IdealSheafData) :
    LocallyOfFiniteType (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P) := by
  let : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (SupportDeformation.BundleCycles.globalSupportDeformationCover I P)
  intro U
  have : IsNoetherianRing Γ(X, U.1) := DeformationProperties.BundleCycles.affineBaseRing_noetherian U
  have : IsNoetherianRing ((Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) :=
    inferInstanceAs (IsNoetherianRing (Γ(X, U.1) ⧸ P.ideal U))
  have hc : LocallyOfFiniteType (Support.Projection.BundleCycles.supportDeformationChartProjection I P U) :=
    deformationConstants_locallyOfFiniteType (Support.CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)
  have ho : IsOpenImmersion (Support.Projection.BundleCycles.supportCoefficientChart P U) :=
    Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion P U
  have ht : LocallyOfFiniteType (Support.Projection.BundleCycles.supportDeformationChartToSupport I P U) :=
    @locallyOfFiniteType_comp _ _ _ (Support.Projection.BundleCycles.supportDeformationChartProjection I P U)
      (Support.Projection.BundleCycles.supportCoefficientChart P U) hc
      (@locallyOfFiniteType_of_isOpenImmersion _ _ (Support.Projection.BundleCycles.supportCoefficientChart P U) ho)
  exact (congrArg (fun f => LocallyOfFiniteType f)
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport_on_chart I P U)).mpr ht

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationFiniteType.BundleCycles
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationFiniteType"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Ord -/

/-! # Ord -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Ord.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finiteness of principal divisors

On an integral Noetherian scheme, the order function of a rational function
has finite support. A nonzero rational function is a unit on a nonempty open;
only finitely many codimension-one points lie outside that open.
-/

open _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

universe u

theorem finite_codimension_one_complement
    (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (U : X.Opens) [Nonempty U] :
    {x : X | coheight x = 1 ∧ x ∉ U}.Finite := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  let := hSf.to_subtype
  let C : S → IrreducibleCloseds X := fun s => ⟨s.1, hSi s.1 s.2, hSc s.1 s.2⟩
  let g : S → X := fun s => irreducibleSetEquivPoints (C s)
  apply (Set.finite_range g).subset
  intro x hx
  have hxc : x ∈ (U : Set X)ᶜ := hx.2
  rw [hSU] at hxc
  obtain ⟨s, hs, hxs⟩ := Set.mem_sUnion.mp hxc
  let s' : S := ⟨s, hs⟩
  let A : IrreducibleCloseds X := irreducibleSetEquivPoints.symm x
  let T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hAC : A ≤ C s' := by
    change closure ({x} : Set X) ⊆ s
    exact (hSc s hs).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxs)
  have hCT : C s' < T := by
    refine lt_of_le_of_ne (show C s' ≤ T from Set.subset_univ _) ?_
    intro heq
    obtain ⟨y⟩ := ‹Nonempty U›
    have hy : y.1 ∈ s := by
      change y.1 ∈ (C s' : Set X)
      rw [heq]
      trivial
    have hyc : y.1 ∈ (U : Set X)ᶜ := by
      rw [hSU]
      exact Set.mem_sUnion.mpr ⟨s, hs, hy⟩
    exact hyc y.2
  have hC1 : 1 ≤ coheight (C s') := by
    calc
      1 ≤ coheight T + 1 := le_add_self
      _ ≤ coheight (C s') := coheight_add_one_le hCT
  have hA1 : coheight A = 1 := by
    simpa only [A, coheight_orderIso] using hx.1
  have hEq : A = C s' := by
    apply le_antisymm hAC
    by_contra hCA
    have hlt : A < C s' := lt_of_le_not_ge hAC hCA
    have h2 : (2 : ℕ∞) ≤ coheight A := by
      calc
        2 = 1 + 1 := rfl
        _ ≤ coheight (C s') + 1 := add_le_add hC1 le_rfl
        _ ≤ coheight A := coheight_add_one_le hlt
    rw [hA1] at h2
    exact (by decide : ¬ (2 : ℕ∞) ≤ 1) h2
  refine ⟨s', ?_⟩
  change irreducibleSetEquivPoints (C s') = x
  rw [← hEq]
  exact irreducibleSetEquivPoints.apply_symm_apply x

/-- The actual local-length orders form a finite principal divisor. -/
theorem finite_support_ord (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (f : X.functionField) :
    (Function.support (X.ord f)).Finite := by
  classical
  by_cases hf : f = 0
  · subst f
    simp only [Scheme.ord_zero, Function.support_zero, Set.finite_empty]
  obtain ⟨U, _, a, hU, hfa, ha⟩ := exists_isUnit_germ_eq X f hf
  let := hU
  apply (finite_codimension_one_complement X U).subset
  intro x hx
  have hxne : X.ord f x ≠ 0 := hx
  constructor
  · by_contra hc
    exact hxne (Scheme.ord_eq_zero_of_coheight_neq_one hc f)
  · intro hxU
    apply hxne
    rw [← hfa]
    exact Scheme.ord_of_isUnit ha hxU

/-- The integral principal-divisor cycle, with no fallback on infinite support. -/
def principalDivisor (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (f : X.functionField) : X →₀ ℤ :=
  Finsupp.ofSupportFinite (X.ord f) (finite_support_ord X f)

@[simp]
theorem principalDivisor_apply (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (f : X.functionField) (x : X) :
    principalDivisor X f x = X.ord f x := rfl

theorem principalDivisor_mul (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (f g : X.functionField)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    principalDivisor X (f * g) = principalDivisor X f + principalDivisor X g := by
  ext x
  exact Scheme.ord_mul hf hg

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Ord.BundleCycles
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Ord"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor -/

/-! # Regular Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor.BundleCycles

noncomputable section

/-!
# LineBundleCycles: effective divisors of nonzero regular functions

On an integral Noetherian scheme, the principal divisor of a nonzero
global section has nonnegative coefficients. At a codimension-one point
its coefficient is the finite length of the local quotient by that section.
These are the multiplicities needed in specialization along t = 0.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

universe u
variable (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

instance integralTopNonempty : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩

/-- Regard a global regular function as an element of the actual function field. -/
def globalFunctionFieldElement (a : Γ(X, ⊤)) : X.functionField :=
  X.germToFunctionField ⊤ a

omit [AlgebraicGeometry.IsNoetherian X] in
theorem globalFunctionFieldElement_ne_zero (a : Γ(X, ⊤)) (ha : a ≠ 0) :
    globalFunctionFieldElement X a ≠ 0 :=
  (map_ne_zero_iff _ (X.germToFunctionField_injective ⊤)).mpr ha

/-- The actual finite principal divisor of a global regular function. -/
def regularFunctionDivisor (a : Γ(X, ⊤)) : X →₀ ℤ :=
  Ord.BundleCycles.principalDivisor X (globalFunctionFieldElement X a)

/-- At codimension one, a nonzero regular function has its local quotient
length as multiplicity. Finiteness of the length is proved from Noetherianity
and the local dimension bound. -/
theorem regularFunctionDivisor_coeff_length (a : Γ(X, ⊤)) (ha : a ≠ 0)
    (x : X) (hx : coheight x = 1) :
    regularFunctionDivisor X a x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ ⊤ x (by trivial) a})).toNat : ℤ) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hg : X.presheaf.germ ⊤ x (by trivial) a ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral X x (by trivial))).mpr ha
  change X.ord (X.germToFunctionField ⊤ a) x = _
  apply (Scheme.ord_eq_iff hx (globalFunctionFieldElement_ne_zero X a ha)).mpr
  change Ring.ordFrac (X.presheaf.stalk x) (X.germToFunctionField ⊤ a) = _
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (x := x) (by trivial) a,
    Ring.ordFrac_eq_ord (X.presheaf.stalk x) hg]
  apply Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_iff_ne_zero.mpr hg)
  exact (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hg))).symm

theorem regularFunctionDivisor_nonnegative (a : Γ(X, ⊤)) (ha : a ≠ 0) (x : X) :
    0 ≤ regularFunctionDivisor X a x := by
  by_cases hx : coheight x = 1
  · rw [regularFunctionDivisor_coeff_length X a ha x hx]
    exact Int.natCast_nonneg _
  · change 0 ≤ X.ord (globalFunctionFieldElement X a) x
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- The divisor has no coefficient where the section is a local unit. -/
theorem regularFunctionDivisor_eq_zero_of_isUnit_germ (a : Γ(X, ⊤)) (x : X)
    (ha : IsUnit (X.presheaf.germ ⊤ x (by trivial) a)) : regularFunctionDivisor X a x = 0 := by
  by_cases hx : coheight x = 1
  · have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    change X.ord (X.germToFunctionField ⊤ a) x = 0
    have hfield : X.germToFunctionField ⊤ a ≠ 0 := by
      rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (x := x) (by trivial) a]
      exact (ha.map (algebraMap _ X.functionField)).ne_zero
    apply (Scheme.ord_eq_iff hx hfield).mpr
    change Ring.ordFrac (X.presheaf.stalk x) (X.germToFunctionField ⊤ a) = 1
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (x := x) (by trivial) a]
    exact Ring.ordFrac_of_isUnit ha
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

theorem regularFunctionDivisor_support_subset (a : Γ(X, ⊤)) :
    ((regularFunctionDivisor X a).support : Set X) ⊆ (X.basicOpen a : Set X)ᶜ := by
  classical
  intro x hx hxa
  apply (Finsupp.mem_support_iff.mp hx)
  apply regularFunctionDivisor_eq_zero_of_isUnit_germ
  exact (Scheme.mem_basicOpen X a x (by trivial)).mp hxa

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor.BundleCycles
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Specialization -/

/-! # Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Specialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the finite specialization cycle of an integral affine support

The regular parameter t has a finite effective divisor on the integral
deformation. Its support lies on t = 0. The proved special-fiber isomorphism
therefore transports this actual divisor, without discarding coefficients,
to a finite cycle on the normal cone. Descent modulo rational equivalence
and refined Gysin are further steps.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

universe u
variable {R : Type u} [CommRing R]

/-- The regular section on Spec R[t,I/t] represented by the parameter t. -/
def affineDeformationParameterSection (I : Ideal R) : Γ(Deformation.ClosedSupport.BundleCycles.affineDeformation I, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I))).inv (Deformation.Iff.BundleCycles.deformationParameter I)

/-- The actual quotient map onto the normal cone, via the special-fiber comparison. -/
def normalConeFiberRingMap (I : Ideal R) : Deformation.Iff.BundleCycles.deformationAlgebra I →+* Normal.Cone.BundleCycles.NormalConeRing I :=
  (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).symm.toRingHom.comp (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I))

theorem normalConeFiberRingMap_surjective (I : Ideal R) :
    Function.Surjective (normalConeFiberRingMap I) :=
  (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).symm.surjective.comp Ideal.Quotient.mk_surjective

theorem normalConeFiberRingMap_ker (I : Ideal R) :
    RingHom.ker (normalConeFiberRingMap I) = Deformation.Iff.BundleCycles.deformationSpecialIdeal I := by
  ext p
  change (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).symm (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) p) = 0 ↔ _
  rw [map_eq_zero_iff _ (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).symm.injective,
    Ideal.Quotient.eq_zero_iff_mem]

/-- Closed inclusion of the actual affine normal cone into the deformation. -/
def normalConeFiberInclusion (I : Ideal R) : Normal.Cone.BundleCycles.affineNormalCone I ⟶ Deformation.ClosedSupport.BundleCycles.affineDeformation I :=
  Spec.map (CommRingCat.ofHom (normalConeFiberRingMap I))

instance normalConeFiberInclusion_isClosedImmersion (I : Ideal R) :
    IsClosedImmersion (normalConeFiberInclusion I) :=
  IsClosedImmersion.spec_of_surjective _ (normalConeFiberRingMap_surjective I)

/-- The cone is exactly the vanishing locus of t in the deformation. -/
theorem normalConeFiberInclusion_range (I : Ideal R) :
    Set.range (normalConeFiberInclusion I) =
      (Deformation.ClosedSupport.BundleCycles.affineDeformation I |>.basicOpen (affineDeformationParameterSection I) : Set (Deformation.ClosedSupport.BundleCycles.affineDeformation I))ᶜ := by
  let A : CommRingCat := .of (Deformation.Iff.BundleCycles.deformationAlgebra I)
  let B : CommRingCat := .of (Normal.Cone.BundleCycles.NormalConeRing I)
  let g : A ⟶ B := CommRingCat.ofHom (normalConeFiberRingMap I)
  have hk : RingHom.ker g.hom = Deformation.Iff.BundleCycles.deformationSpecialIdeal I := normalConeFiberRingMap_ker I
  change Set.range (PrimeSpectrum.comap g.hom) = _
  rw [range_comap_of_surjective _ _ (normalConeFiberRingMap_surjective I), hk]
  change PrimeSpectrum.zeroLocus (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) =
    ((Spec A).basicOpen ((Scheme.ΓSpecIso A).inv (Deformation.Iff.BundleCycles.deformationParameter I)) : Set (Spec A))ᶜ
  rw [basicOpen_eq_of_affine]
  ext x
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  change Ideal.span {Deformation.Iff.BundleCycles.deformationParameter I} ≤ x.asIdeal ↔ ¬Deformation.Iff.BundleCycles.deformationParameter I ∉ x.asIdeal
  exact (Ideal.span_singleton_le_iff_mem (I := x.asIdeal)).trans not_not.symm

variable [IsDomain R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
theorem affineDeformationParameterSection_ne_zero (I : Ideal R) :
    affineDeformationParameterSection I ≠ 0 := by
  intro h
  have ht : Deformation.Iff.BundleCycles.deformationParameter I ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (Deformation.Iff.BundleCycles.deformationParameter_regular I)
  apply ht
  have he := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I))).hom h
  have hzero : (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I))).hom 0 = 0 :=
    map_zero (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I))).hom.hom
  simp only [affineDeformationParameterSection, Iso.inv_hom_id_apply] at he
  exact he.trans hzero

/-- The finite effective divisor of the actual parameter on the integral deformation. -/
def affineDeformationParameterDivisor (I : Ideal R) : Deformation.ClosedSupport.BundleCycles.affineDeformation I →₀ ℤ :=
  RegularDivisor.BundleCycles.regularFunctionDivisor (Deformation.ClosedSupport.BundleCycles.affineDeformation I) (affineDeformationParameterSection I)

theorem affineDeformationParameterDivisor_nonnegative (I : Ideal R) (x : Deformation.ClosedSupport.BundleCycles.affineDeformation I) :
    0 ≤ affineDeformationParameterDivisor I x :=
  RegularDivisor.BundleCycles.regularFunctionDivisor_nonnegative _ _ (affineDeformationParameterSection_ne_zero I) x

/-- All divisor coefficients occur on the actual closed normal-cone fiber. -/
theorem affineDeformationParameterDivisor_support (I : Ideal R) :
    ((affineDeformationParameterDivisor I).support : Set (Deformation.ClosedSupport.BundleCycles.affineDeformation I)) ⊆
      Set.range (normalConeFiberInclusion I) := by
  rw [normalConeFiberInclusion_range]
  exact RegularDivisor.BundleCycles.regularFunctionDivisor_support_subset _ _

/-- The point embedding induced by the normal-cone closed immersion. -/
def normalConeFiberPointEmbedding (I : Ideal R) : Normal.Cone.BundleCycles.affineNormalCone I ↪ Deformation.ClosedSupport.BundleCycles.affineDeformation I :=
  ⟨normalConeFiberInclusion I, (normalConeFiberInclusion I).isClosedEmbedding.injective⟩

/-- The finite specialization cycle on the normal cone of an integral affine scheme. -/
def affineSpecializationCycle (I : Ideal R) : Normal.Cone.BundleCycles.affineNormalCone I →₀ ℤ :=
  Finsupp.comapDomain (normalConeFiberPointEmbedding I) (affineDeformationParameterDivisor I)
    (normalConeFiberPointEmbedding I).injective.injOn

@[simp]
theorem affineSpecializationCycle_apply (I : Ideal R) (x : Normal.Cone.BundleCycles.affineNormalCone I) :
    affineSpecializationCycle I x = affineDeformationParameterDivisor I (normalConeFiberInclusion I x) := rfl

/-- Re-embedding the cone cycle recovers the whole parameter divisor, coefficient by coefficient. -/
theorem affineSpecializationCycle_push (I : Ideal R) :
    Finsupp.embDomain (normalConeFiberPointEmbedding I) (affineSpecializationCycle I) =
      affineDeformationParameterDivisor I :=
  Finsupp.embDomain_comapDomain (affineDeformationParameterDivisor_support I)

theorem affineSpecializationCycle_nonnegative (I : Ideal R) (x : Normal.Cone.BundleCycles.affineNormalCone I) :
    0 ≤ affineSpecializationCycle I x := affineDeformationParameterDivisor_nonnegative I _

/-- Every codimension-one specialization coefficient is the actual finite
local length of the quotient by t on the deformation. -/
theorem affineSpecializationCycle_coeff_length (I : Ideal R) (x : Normal.Cone.BundleCycles.affineNormalCone I)
    (hx : coheight (normalConeFiberInclusion I x) = 1) :
    affineSpecializationCycle I x =
      ((Module.length ((Deformation.ClosedSupport.BundleCycles.affineDeformation I).presheaf.stalk (normalConeFiberInclusion I x))
        (((Deformation.ClosedSupport.BundleCycles.affineDeformation I).presheaf.stalk (normalConeFiberInclusion I x)) ⧸
          Ideal.span (Set.singleton ((Deformation.ClosedSupport.BundleCycles.affineDeformation I).presheaf.germ ⊤ (normalConeFiberInclusion I x)
            (by trivial) (affineDeformationParameterSection I))))).toNat : ℤ) :=
  RegularDivisor.BundleCycles.regularFunctionDivisor_coeff_length _ _ (affineDeformationParameterSection_ne_zero I) _ hx

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Specialization.BundleCycles
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Specialization"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralDimension -/

/-! # Integral Dimension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralDimension.Construction

/-!
# ChernClass: dimension comparisons for integral algebra extensions

These order-theoretic facts support the comparison between divisor points
and the function-field dimension grading of the geometric cycle-class map.
-/

open _root_.Order

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]

/-- Incomparability makes contraction strictly monotone on chains of prime ideals. -/
theorem integral_comap_strictMono : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro p q hpq
  exact Ideal.IsIntegral.under_lt_under hpq

/-- Integral extensions preserve the lengths of chains above a prime, by going up. -/
theorem integral_comap_coheight (p : PrimeSpectrum S) :
    coheight p = coheight (PrimeSpectrum.comap (algebraMap R S) p) := by
  apply coheight_eq_of_strictMono _ integral_comap_strictMono
  intro q r hqr
  obtain ⟨r', hle, hprime, hcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime r.asIdeal q.asIdeal hqr.le
  refine ⟨⟨r', hprime⟩, ?_, PrimeSpectrum.ext hcomap⟩
  apply lt_of_le_of_ne hle
  intro heq
  have he : PrimeSpectrum.comap (algebraMap R S) q = r := by
    apply PrimeSpectrum.ext
    change q.asIdeal.comap (algebraMap R S) = r.asIdeal
    rw [heq]
    exact hcomap
  exact hqr.ne he

/-- When going down is available, contraction also preserves prime height. -/
theorem integral_comap_height [Algebra.HasGoingDown R S] (p : PrimeSpectrum S) :
    height p = height (PrimeSpectrum.comap (algebraMap R S) p) := by
  apply height_eq_of_strictMono _ integral_comap_strictMono
  intro q r hrq
  let : q.asIdeal.LiesOver (q.asIdeal.under R) := ⟨rfl⟩
  obtain ⟨r', hlt, hprime, hover⟩ := Ideal.exists_ideal_lt_liesOver_of_lt
    (R := R) (S := S) (p := r.asIdeal) (q := q.asIdeal.under R) q.asIdeal hrq
  exact ⟨⟨r', hprime⟩, hlt, PrimeSpectrum.ext hover.over.symm⟩

/-- An injective integral extension preserves Krull dimension. -/
theorem integral_ringKrullDim_eq (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R := by
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) := by
    intro p
    obtain ⟨q, _, hprime, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal S)
      (by simpa only [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
        using (bot_le : (⊥ : Ideal R) ≤ p.asIdeal))
    exact ⟨⟨q, hprime⟩, PrimeSpectrum.ext hcomap⟩
  unfold ringKrullDim
  rw [krullDim_eq_iSup_coheight, krullDim_eq_iSup_coheight]
  simp_rw [integral_comap_coheight (R := R) (S := S)]
  exact hsurj.iSup_comp (fun p : PrimeSpectrum R => (coheight p : WithBot ℕ∞))

end OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralDimension.Construction
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralDimension"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.DivisorClass.Chern.FiniteTypeDimension -/

/-! # Finite Type Dimension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.FiniteTypeDimension.Construction

noncomputable section

/-!
# ChernClass: finite-type integral algebras have their function-field dimension

Noether normalization identifies both Krull dimension and transcendence degree
with the number of polynomial parameters, using the actual integral embedding.
-/

variable (K A : Type) [Field K] [CommRing A] [IsDomain A]
variable [Algebra K A] [Algebra.FiniteType K A]

/-- Krull dimension agrees with the finite transcendence degree of a finite-type domain. -/
theorem finiteType_ringKrullDim_eq_trdeg :
    ringKrullDim A = ((Algebra.trdeg K A).toNat : WithBot ℕ∞) := by
  obtain ⟨n, f, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let P := MvPolynomial (Fin n) K
  let : Algebra P A := f.toRingHom.toAlgebra
  let : Algebra.IsIntegral P A := ⟨hint⟩
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  let : IsScalarTower K P A := IsScalarTower.of_algebraMap_eq' (by
    ext k
    exact (f.commutes k).symm)
  have hd : ringKrullDim A = (n : WithBot ℕ∞) := by
    rw [IntegralDimension.Construction.integral_ringKrullDim_eq (R := P) (S := A) hinj]
    change ringKrullDim (MvPolynomial (Fin n) K) = _
    simp
  have ht : (n : Cardinal) = Algebra.trdeg K A := by
    have h := trdeg_add_eq K P (A := A)
    rw [trdeg_eq_zero (R := P) (A := A), add_zero] at h
    change Algebra.trdeg K (MvPolynomial (Fin n) K) = _ at h
    simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast] using h
  rw [hd, ← ht, Cardinal.toNat_natCast]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.FiniteTypeDimension.Construction
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.DivisorClass.Chern.FiniteTypeDimension"

@[expose] public section ComponentSource_18
/- Original module: OAI.AlgebraicGeometry.DivisorClass.Chern.PolynomialDimension -/

/-! # Polynomial Dimension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PolynomialDimension.Construction

noncomputable section

/-!
# ChernClass: dimension drop at height-one primes of polynomial rings

Maximal polynomial ideals have the full ambient height. A height-one prime
is generated by a prime element, and the regular-element dimension theorem
then gives the exact one-dimensional drop.
-/

variable (K : Type) [Field K]

/-- Every maximal ideal of an `n`-variable polynomial algebra over a field has height `n`. -/
theorem mvPolynomial_maximal_height (n : ℕ) (p : Ideal (MvPolynomial (Fin n) K)) [p.IsMaximal] :
    p.height = n := by
  induction n with
  | zero =>
    let e := (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toRingEquiv
    let q : Ideal K := p.map e
    have : q.IsMaximal := by dsimp [q]; infer_instance
    have hq := Ideal.height_le_ringKrullDim_of_ne_top (show q ≠ ⊤ from
      (show q.IsMaximal from inferInstance).ne_top)
    rw [ringKrullDim_eq_zero_of_field] at hq
    have hq0 : q.height = 0 := by
      apply le_antisymm _ bot_le
      exact_mod_cast hq
    exact (e.height_map p).symm.trans hq0
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv K n).toRingEquiv
    let q : Ideal (Polynomial (MvPolynomial (Fin n) K)) := p.map e
    have : q.IsMaximal := by dsimp [q]; infer_instance
    let r : Ideal (MvPolynomial (Fin n) K) := q.comap Polynomial.C
    have : r.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing q
    have : q.LiesOver r := ⟨rfl⟩
    calc
      p.height = q.height := (e.height_map p).symm
      _ = r.height + 1 := Polynomial.height_eq_height_add_one r q
      _ = (n + 1 : ℕ) := by rw [ih r]; simp only [Nat.cast_add, Nat.cast_one]

/-- Quotient by a height-one polynomial prime lowers Krull dimension by exactly one. -/
theorem mvPolynomial_height_one_quotient_dimension (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime] (hp : p.height = 1) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ p) + 1 =
      ringKrullDim (MvPolynomial (Fin n) K) := by
  obtain ⟨f, hfp, hf⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot
    (show p.IsPrime from inferInstance) (Ideal.ne_bot_of_height_eq_one hp)
  have hspan : p = Ideal.span {f} := Ideal.eq_span_singleton_of_height_eq_one hp hfp hf
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p Ideal.IsPrime.ne_top'
  let : m.IsMaximal := hm
  have hmax : (m.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin n) K) := by
    rw [mvPolynomial_maximal_height, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  have hdim := Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf.ne_zero) hmax (hpm hfp)
  rwa [← hspan] at hdim

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PolynomialDimension.Construction
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.DivisorClass.Chern.PolynomialDimension"

@[expose] public section ComponentSource_19
/- Original module: OAI.AlgebraicGeometry.DivisorClass.Chern.HeightOneDimension -/

/-! # Height One Dimension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HeightOneDimension.Construction

noncomputable section

/-!
# ChernClass: height-one primes have transcendence codimension one

Noether normalization and going down reduce the statement to polynomial rings.
The quotient integral embedding preserves its actual Krull dimension, giving
the exact one-dimensional drop and then the transcendence-degree formula.
-/

variable (K A : Type) [Field K] [CommRing A] [IsDomain A]
variable [Algebra K A] [Algebra.FiniteType K A]

include K in
/-- A height-one prime in a finite-type domain lowers Krull dimension by exactly one. -/
theorem finiteType_height_one_quotient_dimension (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    ringKrullDim (A ⧸ p) + 1 = ringKrullDim A := by
  obtain ⟨n, f, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let P := MvPolynomial (Fin n) K
  let : Algebra P A := f.toRingHom.toAlgebra
  let : Algebra.IsIntegral P A := ⟨hint⟩
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  let q : Ideal P := p.comap (algebraMap P A)
  have hq : q.height = 1 := by
    have h := IntegralDimension.Construction.integral_comap_height (R := P) (S := A) ⟨p, inferInstance⟩
    have h' : p.height = q.height := by
      rw [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at h
      exact h
    exact h'.symm.trans hp
  have hquot : ringKrullDim (A ⧸ p) = ringKrullDim (P ⧸ q) :=
    IntegralDimension.Construction.integral_ringKrullDim_eq (R := P ⧸ q) (S := A ⧸ p) Ideal.algebraMap_quotient_injective
  calc
    ringKrullDim (A ⧸ p) + 1 = ringKrullDim (P ⧸ q) + 1 := congrArg (fun d => d + 1) hquot
    _ = ringKrullDim P := PolynomialDimension.Construction.mvPolynomial_height_one_quotient_dimension K n q hq
    _ = ringKrullDim A := (IntegralDimension.Construction.integral_ringKrullDim_eq (R := P) (S := A) hinj).symm

/-- The same height-one statement in the actual transcendence-degree grading. -/
theorem finiteType_height_one_trdeg (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    (Algebra.trdeg K (A ⧸ p)).toNat + 1 = (Algebra.trdeg K A).toNat := by
  have h := finiteType_height_one_quotient_dimension K A p hp
  rw [FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K (A ⧸ p), FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K A] at h
  exact_mod_cast h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HeightOneDimension.Construction
end ComponentSource_19

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.DivisorClass.Chern.HeightOneDimension"

@[expose] public section ComponentSource_20
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.CycleSupports -/

/-! # Cycle Supports -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.CycleSupports

noncomputable section

/-!
# Generic points and codimension-indexed algebraic cycle supports

This file identifies codimension-indexed scheme points with irreducible closed
supports. Codimension is the coheight in the specialization order, equivalently
in the inclusion order on irreducible closed sets. No cycle class map is assumed.
-/

open _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

universe u

/-- A generic point of an irreducible codimension-`p` algebraic cycle support. -/
def CyclePoint (X : Scheme.{u}) (p : ℕ) : Type u :=
  {x : X // Order.coheight x = p}

/-- An irreducible closed algebraic support of codimension `p`. -/
def IrreducibleCycleSupport (X : Scheme.{u}) (p : ℕ) : Type u :=
  {Z : IrreducibleCloseds X // Order.coheight Z = p}

/-- Scheme sobriety identifies irreducible closed sets with their generic points,
and its order isomorphism preserves codimension. -/
def irreducibleCycleSupportEquivCyclePoint (X : Scheme.{u}) (p : ℕ) :
    IrreducibleCycleSupport X p ≃ CyclePoint X p where
  toFun Z := ⟨irreducibleSetEquivPoints Z.1, by
    rw [Order.coheight_orderIso]
    exact Z.2⟩
  invFun x := ⟨irreducibleSetEquivPoints.symm x.1, by
    rw [Order.coheight_orderIso]
    exact x.2⟩
  left_inv Z := by
    apply Subtype.ext
    exact irreducibleSetEquivPoints.symm_apply_apply Z.1
  right_inv x := by
    apply Subtype.ext
    exact irreducibleSetEquivPoints.apply_symm_apply x.1

/-- The irreducible support corresponding to a cycle point is its closure. -/
theorem cyclePoint_support_coe (X : Scheme.{u}) (p : ℕ) (x : CyclePoint X p) :
    (((irreducibleCycleSupportEquivCyclePoint X p).symm x).1 : Set X) =
      closure ({x.1} : Set X) := rfl

/-- The point indexing a support is indeed its generic point. -/
theorem cycleSupport_isGenericPoint (X : Scheme.{u}) (p : ℕ)
    (Z : IrreducibleCycleSupport X p) :
    IsGenericPoint ((irreducibleCycleSupportEquivCyclePoint X p Z).1)
      (Z.1 : Set X) :=
  Z.1.2.isGenericPoint_genericPoint Z.1.3

/-- Codimension can equivalently be read off from the dimension of the local ring. -/
theorem cyclePoint_stalk_dimension (X : Scheme.{u}) (p : ℕ) (x : CyclePoint X p) :
    ringKrullDim (X.presheaf.stalk x.1) = (p : WithBot ℕ∞) := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, x.2]
  rfl

/-- On an affine scheme, the indexing codimension is the height of its prime ideal. -/
theorem cyclePoint_affine_prime_height (R : CommRingCat.{u}) (p : ℕ)
    (x : CyclePoint (Spec R) p) : x.1.asIdeal.height = p := by
  rw [AlgebraicGeometry.idealHeight_eq_coheight]
  exact x.2

end

end OAI.AlgebraicGeometry.Foundations.Scheme.CycleSupports
end ComponentSource_20

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.CycleSupports"

@[expose] public section ComponentSource_21
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecializationGrading -/

/-! # Specialization Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecializationGrading.BundleCycles

noncomputable section

/-!
# LineBundleCycles: dimension grading of affine specialization

A nonzero specialization multiplicity comes from a codimension-one point
on the integral deformation. The height-one dimension theorem and the
proved one-parameter transcendence formula show that its quotient has
exactly the original support's transcendence dimension.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

/-- A surjection identifies the quotient by the inverse-image ideal with the target quotient in transcendence degree. -/
theorem quotient_trdeg_of_surjective {k A B : Type} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (hf : Function.Surjective f) (q : Ideal B) :
    Algebra.trdeg k (A ⧸ q.comap f.toRingHom) = Algebra.trdeg k (B ⧸ q) := by
  let g := Ideal.quotientMapₐ q f le_rfl
  exact (trdeg_le_of_injective g Ideal.quotientMap_injective).antisymm
    (trdeg_le_of_surjective g (Ideal.quotientMap_surjective (H := le_rfl) hf))

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R)

/-- Every nonzero specialization coefficient is a codimension-one divisor coefficient. -/
theorem affineSpecializationCycle_coheight (x : Normal.Cone.BundleCycles.affineNormalCone I)
    (hx : Specialization.BundleCycles.affineSpecializationCycle I x ≠ 0) : coheight (Specialization.BundleCycles.normalConeFiberInclusion I x) = 1 := by
  by_contra h
  apply hx
  change (Deformation.ClosedSupport.BundleCycles.affineDeformation I).ord
    (RegularDivisor.BundleCycles.globalFunctionFieldElement (Deformation.ClosedSupport.BundleCycles.affineDeformation I) (Specialization.BundleCycles.affineDeformationParameterSection I))
      (Specialization.BundleCycles.normalConeFiberInclusion I x) = 0
  exact Scheme.ord_eq_zero_of_coheight_neq_one h _

/-- The ambient prime of a point on the affine normal-cone fiber. -/
def affineSpecializationAmbientPrime (x : Normal.Cone.BundleCycles.affineNormalCone I) : PrimeSpectrum (Deformation.Iff.BundleCycles.deformationAlgebra I) :=
  Specialization.BundleCycles.normalConeFiberInclusion I x

variable (k : Type) [Field k] [Algebra k R] [Algebra.FiniteType k R]

/-- A height-one prime of the deformation has the original coefficient ring's dimension. -/
theorem deformationHeightOne_trdeg (q : PrimeSpectrum (Deformation.Iff.BundleCycles.deformationAlgebra I)) (hq : q.asIdeal.height = 1) :
    letI := Deformation.Transcendence.BundleCycles.deformationScalarAlgebra I k
    (Algebra.trdeg k (Deformation.Iff.BundleCycles.deformationAlgebra I ⧸ q.asIdeal)).toNat = (Algebra.trdeg k R).toNat := by
  let := Deformation.Transcendence.BundleCycles.deformationScalarAlgebra I k
  have : Algebra.FiniteType k (Deformation.Iff.BundleCycles.deformationAlgebra I) :=
    Deformation.Transcendence.BundleCycles.deformationAlgebra_finiteType_base I k (IsNoetherian.noetherian I)
  have h := DivisorClass.Chern.HeightOneDimension.Construction.finiteType_height_one_trdeg k (Deformation.Iff.BundleCycles.deformationAlgebra I) q.asIdeal hq
  rw [Deformation.Transcendence.BundleCycles.deformationAlgebra_trdeg_toNat I k] at h
  omega

/-- The actual nonzero specialization coefficients preserve transcendence dimension. -/
theorem affineSpecializationCycle_dimension (x : Normal.Cone.BundleCycles.affineNormalCone I)
    (hx : Specialization.BundleCycles.affineSpecializationCycle I x ≠ 0) :
    letI := Deformation.Transcendence.BundleCycles.deformationScalarAlgebra I k
    (Algebra.trdeg k (Deformation.Iff.BundleCycles.deformationAlgebra I ⧸ (affineSpecializationAmbientPrime I x).asIdeal)).toNat =
      (Algebra.trdeg k R).toNat := by
  apply deformationHeightOne_trdeg I k
  exact (idealHeight_eq_coheight (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I))
    (affineSpecializationAmbientPrime I x)).trans (affineSpecializationCycle_coheight I x hx)

/-- The field action on the normal cone is induced by its actual closed-fiber quotient map. -/
abbrev normalConeScalarAlgebra : Algebra k (Normal.Cone.BundleCycles.NormalConeRing I) :=
  @RingHom.toAlgebra k (Normal.Cone.BundleCycles.NormalConeRing I) (by infer_instance) (by infer_instance)
    ((Specialization.BundleCycles.normalConeFiberRingMap I).comp
      ((algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I)).comp (algebraMap k R)))

/-- The actual fiber quotient as a homomorphism over the original coefficient field. -/
def normalConeFiberAlgHom :
    letI := Deformation.Transcendence.BundleCycles.deformationScalarAlgebra I k
    letI := normalConeScalarAlgebra I k
    Deformation.Iff.BundleCycles.deformationAlgebra I →ₐ[k] Normal.Cone.BundleCycles.NormalConeRing I := by
  let := Deformation.Transcendence.BundleCycles.deformationScalarAlgebra I k
  let := normalConeScalarAlgebra I k
  exact { Specialization.BundleCycles.normalConeFiberRingMap I with commutes' := fun _ => rfl }

/-- The quotient ring of the normal-cone support itself has the original support's dimension. -/
theorem affineSpecializationCycle_cone_dimension (x : Normal.Cone.BundleCycles.affineNormalCone I)
    (hx : Specialization.BundleCycles.affineSpecializationCycle I x ≠ 0) :
    letI := normalConeScalarAlgebra I k
    (Algebra.trdeg k (Normal.Cone.BundleCycles.NormalConeRing I ⧸ x.asIdeal)).toNat = (Algebra.trdeg k R).toNat := by
  let := Deformation.Transcendence.BundleCycles.deformationScalarAlgebra I k
  let := normalConeScalarAlgebra I k
  have hq := quotient_trdeg_of_surjective (normalConeFiberAlgHom I k)
    (Specialization.BundleCycles.normalConeFiberRingMap_surjective I) x.asIdeal
  exact (congrArg Cardinal.toNat hq).symm.trans (affineSpecializationCycle_dimension I k x hx)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecializationGrading.BundleCycles
end ComponentSource_21

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecializationGrading"

@[expose] public section ComponentSource_22
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.GenericPoint -/

/-! # Generic Point -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.GenericPoint

noncomputable section

/-!
# Integral closed subschemes representing cycle supports

An irreducible closed subset of a scheme carries its reduced induced scheme
structure. This file constructs that actual scheme from mathlib's vanishing
ideal sheaf, proves it is integral, and identifies its generic point with the
point indexing the algebraic cycle support.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

/-- The radical ideal sheaf defining the reduced structure on a closed support. -/
def reducedSupportIdeal (Z : IrreducibleCloseds X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨Z, Z.isClosed⟩

/-- The actual reduced induced closed subscheme on an irreducible support. -/
def reducedSupportScheme (Z : IrreducibleCloseds X) : Scheme.{u} :=
  (reducedSupportIdeal Z).subscheme

/-- The closed immersion of the reduced induced support into its ambient scheme. -/
def reducedSupportι (Z : IrreducibleCloseds X) : reducedSupportScheme Z ⟶ X :=
  (reducedSupportIdeal Z).subschemeι

instance reducedSupportι_isClosedImmersion (Z : IrreducibleCloseds X) :
    IsClosedImmersion (reducedSupportι Z) := by
  exact inferInstanceAs (IsClosedImmersion (reducedSupportIdeal Z).subschemeι)

@[simp]
theorem range_reducedSupportι (Z : IrreducibleCloseds X) :
    Set.range (reducedSupportι Z) = (Z : Set X) := by
  change Set.range (reducedSupportIdeal Z).subschemeι = (Z : Set X)
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp [reducedSupportIdeal]

instance reducedSupportScheme_isReduced (Z : IrreducibleCloseds X) :
    AlgebraicGeometry.IsReduced (reducedSupportScheme Z) := by
  let I := reducedSupportIdeal Z
  change AlgebraicGeometry.IsReduced I.subscheme
  apply (AlgebraicGeometry.IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover).2
  intro U
  change X.affineOpens at U
  change AlgebraicGeometry.IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
  apply (AlgebraicGeometry.affine_isReduced_iff _).2
  apply (Ideal.isRadical_iff_quotient_reduced _).1
  change (PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))).IsRadical
  exact PrimeSpectrum.isRadical_vanishingIdeal _

instance reducedSupportScheme_irreducible (Z : IrreducibleCloseds X) :
    IrreducibleSpace (reducedSupportScheme Z) := by
  exact Subtype.irreducibleSpace Z.isIrreducible

instance reducedSupportScheme_isIntegral (Z : IrreducibleCloseds X) :
    IsIntegral (reducedSupportScheme Z) :=
  AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

/-- The generic point of the reduced support has the stated irreducible closure
in the ambient scheme. -/
theorem reducedSupport_genericPoint (Z : IrreducibleCloseds X) :
    IsGenericPoint ((reducedSupportι Z) (genericPoint (reducedSupportScheme Z)))
      (Z : Set X) := by
  have h := (genericPoint_spec (reducedSupportScheme Z)).image
    (reducedSupportι Z).continuous
  simpa only [Set.image_univ, range_reducedSupportι, Z.isClosed.closure_eq] using h

/-- The scheme-theoretic generic point agrees with the existing sober-space
correspondence used to index cycles. -/
theorem reducedSupport_genericPoint_eq (Z : IrreducibleCloseds X) :
    (reducedSupportι Z) (genericPoint (reducedSupportScheme Z)) =
      irreducibleSetEquivPoints Z := by
  exact (reducedSupport_genericPoint Z).eq
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)

/-- For a codimension-indexed support, its actual integral closed subscheme has
exactly the prescribed codimension at its generic point. -/
theorem reducedSupport_genericPoint_codimension (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p) :
    Order.coheight ((reducedSupportι Z.1)
      (genericPoint (reducedSupportScheme Z.1))) = p := by
  rw [reducedSupport_genericPoint_eq]
  exact (Foundations.Scheme.CycleSupports.irreducibleCycleSupportEquivCyclePoint X p Z).2

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.GenericPoint
end ComponentSource_22

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.GenericPoint"

@[expose] public section ComponentSource_23
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SupportFiniteType -/

/-! # Support Finite Type -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Finite presentation and projectivity of integral cycle supports

The structure morphism on a cycle support is the composite of its actual
closed immersion with the ambient structure morphism. Finite type and, over
a locally Noetherian base, local finite presentation follow from this map.
The support also inherits a genuine projective presentation. No smoothness
of the possibly singular support is assumed.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X S : Scheme.{u}}

/-- A cycle support has the structure morphism induced by its closed immersion. -/
def CycleClass.Geometric.SupportFiniteType.supportStructureMap (Z : IrreducibleCloseds X) (f : X ⟶ S) :
    CycleClass.Geometric.GenericPoint.reducedSupportScheme Z ⟶ S :=
  CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ f

instance CycleClass.Geometric.SupportFiniteType.reducedSupportι_locallyOfFiniteType (Z : IrreducibleCloseds X) :
    LocallyOfFiniteType (CycleClass.Geometric.GenericPoint.reducedSupportι Z) := by
  infer_instance

instance CycleClass.Geometric.SupportFiniteType.reducedSupportι_quasiCompact (Z : IrreducibleCloseds X) :
    QuasiCompact (CycleClass.Geometric.GenericPoint.reducedSupportι Z) := by
  infer_instance

instance CycleClass.Geometric.SupportFiniteType.reducedSupportι_locallyOfFinitePresentation (Z : IrreducibleCloseds X)
    [IsLocallyNoetherian X] : LocallyOfFinitePresentation (CycleClass.Geometric.GenericPoint.reducedSupportι Z) := by
  infer_instance

instance CycleClass.Geometric.SupportFiniteType.reducedSupportScheme_isLocallyNoetherian (Z : IrreducibleCloseds X)
    [IsLocallyNoetherian X] : IsLocallyNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) :=
  LocallyOfFiniteType.isLocallyNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportι Z)

/-- Compactness here is compactness of the underlying Zariski space. -/
instance CycleClass.Geometric.SupportFiniteType.reducedSupportScheme_compactSpace (Z : IrreducibleCloseds X)
    [CompactSpace X] : CompactSpace (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) :=
  QuasiCompact.compactSpace_of_compactSpace (CycleClass.Geometric.GenericPoint.reducedSupportι Z)

instance CycleClass.Geometric.SupportFiniteType.reducedSupportScheme_isNoetherian (Z : IrreducibleCloseds X)
    [IsNoetherian X] : IsNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) where

instance CycleClass.Geometric.SupportFiniteType.supportStructureMap_locallyOfFiniteType (Z : IrreducibleCloseds X)
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) := by
  unfold CycleClass.Geometric.SupportFiniteType.supportStructureMap
  infer_instance

instance CycleClass.Geometric.SupportFiniteType.supportStructureMap_quasiCompact (Z : IrreducibleCloseds X)
    (f : X ⟶ S) [QuasiCompact f] : QuasiCompact (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) := by
  unfold CycleClass.Geometric.SupportFiniteType.supportStructureMap
  infer_instance

/-- Over a locally Noetherian base, finite type supplies local finite
presentation for the support, with no regularity assumption on it. -/
instance CycleClass.Geometric.SupportFiniteType.supportStructureMap_locallyOfFinitePresentation (Z : IrreducibleCloseds X)
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) := by
  infer_instance

/-- Both conditions in the usual definition of finite type hold for the
support whenever they hold for its ambient scheme morphism. -/
theorem CycleClass.Geometric.SupportFiniteType.supportStructureMap_finiteType (Z : IrreducibleCloseds X)
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    LocallyOfFiniteType (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) ∧
      QuasiCompact (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) :=
  ⟨inferInstance, inferInstance⟩

section

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}

/-- A closed integral support inherits the actual ambient projective embedding. -/
def Foundations.Scheme.SmoothProjective.ProjectivePresentation.reducedSupport (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) (Z : IrreducibleCloseds X) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) where
  ambientDimension := P.ambientDimension
  embedding := CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ P.embedding
  closedImmersion := by infer_instance
  over_base := by
    dsimp only [CycleClass.Geometric.SupportFiniteType.supportStructureMap]
    rw [Category.assoc, P.over_base]

/-- Noetherianity of each support follows from the genuine projective embedding. -/
theorem Foundations.Scheme.SmoothProjective.ProjectivePresentation.reducedSupport_isNoetherian (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (Z : IrreducibleCloseds X) : IsNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) :=
  (P.reducedSupport Z).isNoetherian

/-- Each support is locally of finite presentation over the complex base. -/
theorem Foundations.Scheme.SmoothProjective.ProjectivePresentation.reducedSupport_locallyOfFinitePresentation (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (Z : IrreducibleCloseds X) : LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) :=
  (P.reducedSupport Z).locallyOfFinitePresentation

/-- Each support is proper over the complex base. -/
theorem Foundations.Scheme.SmoothProjective.ProjectivePresentation.reducedSupport_isProper (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (Z : IrreducibleCloseds X) : IsProper (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) :=
  (P.reducedSupport Z).isProper

/-- The three standard conditions for a finitely presented morphism all hold
for this projective support: local finite presentation, quasi-compactness, and
quasi-separatedness. -/
theorem Foundations.Scheme.SmoothProjective.ProjectivePresentation.reducedSupport_finitePresentation (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (Z : IrreducibleCloseds X) :
    LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) ∧
      QuasiCompact (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) ∧
        QuasiSeparated (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) := by
  let : IsProper (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) := P.reducedSupport_isProper Z
  exact ⟨P.reducedSupport_locallyOfFinitePresentation Z, inferInstance, inferInstance⟩

end

/-- An actual codimension-indexed support in a smooth projective presentation
has a locally finitely presented structure map over `Spec ℂ`. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupport_locallyOfFinitePresentation (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (p : ℕ) (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) :
    LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap) :=
  P.projective.reducedSupport_locallyOfFinitePresentation Z.1

/-- The integral closed scheme underlying an actual cycle support is Noetherian. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupport_isNoetherian (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (p : ℕ) (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) :
    IsNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1) :=
  P.projective.reducedSupport_isNoetherian Z.1

end

end OAI.AlgebraicGeometry
end ComponentSource_23

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SupportFiniteType"

@[expose] public section ComponentSource_24
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.ClosedImmersionDimension -/

/-! # Closed Immersion Dimension -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ClosedImmersionDimension

noncomputable section

/-!
# Dimension monotonicity for closed immersions

The algebraic comparison uses a surjection between affine coordinate rings.
It does not assert a map between the two function fields: a closed immersion
does not in general induce such a map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

/-- Quotienting an integral algebra cannot increase the transcendence degree
of its fraction field. -/
theorem fractionRing_trdeg_le_of_surjective_algHom
    (k : Type u) {A B : Type v} [Field k] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (hf : Function.Surjective f) :
    Algebra.trdeg k (FractionRing B) ≤ Algebra.trdeg k (FractionRing A) := by
  rw [← TranscendenceDegreeTransfer.trdeg_eq_fractionRing k B, ← TranscendenceDegreeTransfer.trdeg_eq_fractionRing k A]
  exact trdeg_le_of_surjective f hf

/-- The same comparison for any actual fraction fields, with their compatible
base-field scalar structures. -/
theorem fractionField_trdeg_le_of_surjective_algHom
    (k : Type u) {A B KA KB : Type v} [Field k] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Field KA] [Field KB]
    [Algebra k A] [Algebra k B] [Algebra k KA] [Algebra k KB]
    [Algebra A KA] [Algebra B KB] [IsScalarTower k A KA] [IsScalarTower k B KB]
    [IsFractionRing A KA] [IsFractionRing B KB]
    (f : A →ₐ[k] B) (hf : Function.Surjective f) :
    Algebra.trdeg k KB ≤ Algebra.trdeg k KA := by
  rw [← TranscendenceDegreeTransfer.trdeg_eq_of_isFractionRing k B KB, ← TranscendenceDegreeTransfer.trdeg_eq_of_isFractionRing k A KA]
  exact trdeg_le_of_surjective f hf

/-- The fraction-ring inequality with explicit cardinal lifts when the two
coordinate rings live in different universes. -/
theorem lift_fractionRing_trdeg_le_of_surjective_algHom
    (k : Type u) {A : Type v} {B : Type w} [Field k] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (hf : Function.Surjective f) :
    Cardinal.lift.{v} (Algebra.trdeg k (FractionRing B)) ≤
      Cardinal.lift.{w} (Algebra.trdeg k (FractionRing A)) := by
  rw [← TranscendenceDegreeTransfer.trdeg_eq_fractionRing k B, ← TranscendenceDegreeTransfer.trdeg_eq_fractionRing k A]
  exact lift_trdeg_le_of_surjective f hf

/-- Restriction along a scheme morphism commutes with the actual base-section
map on an open set and its inverse image. -/
theorem sectionBaseMap_app {Z X S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S)
    (U : X.Opens) :
    Betti.AffineDimension.Realization.sectionBaseMap f U ≫ i.app U =
      Betti.AffineDimension.Realization.sectionBaseMap (i ≫ f) (i ⁻¹ᵁ U) := by
  dsimp only [Betti.AffineDimension.Realization.sectionBaseMap]
  rw [i.app_eq_appLE]
  exact Scheme.Hom.appLE_comp_appLE i f ⊤ U (i ⁻¹ᵁ U) le_top le_rfl

/-- Pullback on sections respects the scalar map induced by the structure
morphism to the spectrum of the scalar ring. -/
theorem specSectionScalarMap_app {k : Type u} [CommRing k]
    {Z X : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ Spec (.of k)) (U : X.Opens) :
    (i.app U).hom.comp (SpecScalarTransport.specSectionScalarMap f U) =
      SpecScalarTransport.specSectionScalarMap (i ≫ f) (i ⁻¹ᵁ U) := by
  ext r
  exact congrArg
    (fun q : Γ(Spec (.of k), ⊤) ⟶ Γ(Z, i ⁻¹ᵁ U) =>
      q ((Scheme.ΓSpecIso (.of k)).inv r))
    (sectionBaseMap_app i f U)

/-- The existing section pullback as an algebra homomorphism for the actual
base-ring scalar structures. -/
def sectionPullbackAlgHom {k : Type u} [CommRing k]
    {Z X : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ Spec (.of k)) (U : X.Opens) :
    letI := SpecScalarTransport.specSectionScalarAlgebra f U
    letI := SpecScalarTransport.specSectionScalarAlgebra (i ≫ f) (i ⁻¹ᵁ U)
    Γ(X, U) →ₐ[k] Γ(Z, i ⁻¹ᵁ U) := by
  letI := SpecScalarTransport.specSectionScalarAlgebra f U
  letI := SpecScalarTransport.specSectionScalarAlgebra (i ≫ f) (i ⁻¹ᵁ U)
  exact
    { (i.app U).hom with
      commutes' := fun r => congrArg (fun h : k →+* Γ(Z, i ⁻¹ᵁ U) => h r)
        (specSectionScalarMap_app i f U) }

/-- On an affine open of the target, a closed immersion gives a surjective
algebra homomorphism of the actual section rings. -/
theorem sectionPullbackAlgHom_surjective {k : Type u} [CommRing k]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of k)) (U : X.Opens) (hU : IsAffineOpen U) :
    letI := SpecScalarTransport.specSectionScalarAlgebra f U
    letI := SpecScalarTransport.specSectionScalarAlgebra (i ≫ f) (i ⁻¹ᵁ U)
    Function.Surjective (sectionPullbackAlgHom i f U) :=
  i.app_surjective U hU

/-- A nonempty common affine chart compares the actual function fields of
an integral closed subscheme and its integral ambient scheme. -/
theorem closedImmersion_functionField_trdeg_le_of_affineOpen
    {k : Type u} [Field k] {Z X : Scheme.{u}} [IsIntegral Z] [IsIntegral X]
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k))
    (U : X.Opens) [hV : Nonempty (i ⁻¹ᵁ U)] (hU : IsAffineOpen U) :
    let := FunctionFieldScalar.functionFieldScalarAlgebra f
    let := FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
    Algebra.trdeg k Z.functionField ≤ Algebra.trdeg k X.functionField := by
  let z := Classical.choice hV
  let : Nonempty U := ⟨⟨i z.val, z.property⟩⟩
  let := SpecScalarTransport.specSectionScalarAlgebra f U
  let := SpecScalarTransport.specSectionScalarAlgebra (i ≫ f) (i ⁻¹ᵁ U)
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  let := FunctionFieldScalar.functionFieldScalar_isScalarTower f U
  let := FunctionFieldScalar.functionFieldScalar_isScalarTower (i ≫ f) (i ⁻¹ᵁ U)
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let := functionField_isFractionRing_of_isAffineOpen Z (i ⁻¹ᵁ U) (hU.preimage i)
  exact fractionField_trdeg_le_of_surjective_algHom k
    (KA := X.functionField) (KB := Z.functionField)
    (sectionPullbackAlgHom i f U) (sectionPullbackAlgHom_surjective i f U hU)

/-- A closed immersion between integral schemes cannot increase the
transcendence degree of the actual function field over the given scalar field.
The proof uses an affine chart around the image of the source generic point. -/
theorem closedImmersion_functionField_trdeg_le
    {k : Type u} [Field k] {Z X : Scheme.{u}} [IsIntegral Z] [IsIntegral X]
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k)) :
    let := FunctionFieldScalar.functionFieldScalarAlgebra f
    let := FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
    Algebra.trdeg k Z.functionField ≤ Algebra.trdeg k X.functionField := by
  let z := genericPoint Z
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx (i z))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  let : Nonempty (i ⁻¹ᵁ U) := ⟨⟨z, X.affineCover.covers (i z)⟩⟩
  exact closedImmersion_functionField_trdeg_le_of_affineOpen i f U hU

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ClosedImmersionDimension
end ComponentSource_24

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.ClosedImmersionDimension"

@[expose] public section ComponentSource_25
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineQuotient -/

/-! # Support Affine Quotient -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineQuotient

noncomputable section

/-!
# Affine coordinate rings of actual reduced irreducible supports

An ambient affine open meets a reduced irreducible support in the spectrum of
the quotient by its vanishing ideal. The actual support function field is the
fraction field of this quotient. All maps below come from the closed immersion
and from the structure sheaf, rather than from extra algebraic data.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

/-- The open part of a support lying over an ambient affine open. -/
abbrev supportAffineOpen (Z : IrreducibleCloseds X) (U : X.affineOpens) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).Opens :=
  CycleClass.Geometric.GenericPoint.reducedSupportι Z ⁻¹ᵁ U

/-- The actual quotient coordinate ring of the support on an ambient affine open. -/
abbrev supportAffineQuotient (Z : IrreducibleCloseds X) (U : X.affineOpens) :=
  Γ(X, U) ⧸ (CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U

/-- A closed immersion has affine inverse image of an affine open. -/
theorem supportAffineOpen_isAffine (Z : IrreducibleCloseds X) (U : X.affineOpens) :
    IsAffineOpen (supportAffineOpen Z U) :=
  U.2.preimage (CycleClass.Geometric.GenericPoint.reducedSupportι Z)

/-- The sheaf-theoretic sections are exactly the quotient by the support ideal. -/
def supportAffineSectionsEquiv (Z : IrreducibleCloseds X) (U : X.affineOpens) :
    Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, supportAffineOpen Z U) ≃+* supportAffineQuotient Z U :=
  ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).subschemeObjIso U).commRingCatIsoToRingEquiv

/-- Pullback of an ambient regular function is its quotient class. -/
theorem supportAffineSectionsEquiv_app (Z : IrreducibleCloseds X) (U : X.affineOpens)
    (a : Γ(X, U)) :
    supportAffineSectionsEquiv Z U ((CycleClass.Geometric.GenericPoint.reducedSupportι Z).app U a) =
      Ideal.Quotient.mk ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U) a := by
  change ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).subschemeObjIso U).hom
    ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).subschemeι.app U a) = _
  rw [(CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).subschemeι_app U]
  simp

/-- A nonempty open of the integral support has an integral coordinate ring. -/
instance supportAffineQuotient_isDomain (Z : IrreducibleCloseds X) (U : X.affineOpens)
    [Nonempty (supportAffineOpen Z U)] : IsDomain (supportAffineQuotient Z U) :=
  (supportAffineSectionsEquiv Z U).symm.injective.isDomain
    (supportAffineSectionsEquiv Z U).symm

/-- In particular the affine vanishing ideal is prime whenever the open meets
the support. -/
theorem supportAffineIdeal_isPrime (Z : IrreducibleCloseds X) (U : X.affineOpens)
    [Nonempty (supportAffineOpen Z U)] : ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

/-- The quotient maps to the actual function field by its section isomorphism
and the germ at the generic point. -/
abbrev supportAffineQuotientFunctionFieldAlgebra
    (Z : IrreducibleCloseds X) (U : X.affineOpens) [Nonempty (supportAffineOpen Z U)] :
    Algebra (supportAffineQuotient Z U) (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField :=
  ((algebraMap Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, supportAffineOpen Z U)
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField).comp
      (supportAffineSectionsEquiv Z U).symm.toRingHom).toAlgebra

/-- The actual function field of the support is the fraction field of its
affine quotient coordinate ring. -/
theorem supportAffineQuotient_isFractionRing
    (Z : IrreducibleCloseds X) (U : X.affineOpens) [Nonempty (supportAffineOpen Z U)] :
    letI := supportAffineQuotientFunctionFieldAlgebra Z U
    IsFractionRing (supportAffineQuotient Z U) (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField := by
  let := supportAffineQuotientFunctionFieldAlgebra Z U
  let := functionField_isFractionRing_of_isAffineOpen (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)
    (supportAffineOpen Z U) (supportAffineOpen_isAffine Z U)
  exact IsFractionRing.of_ringEquiv_left (supportAffineSectionsEquiv Z U).symm
    (fun _ => rfl)

variable {K : Type u} [CommRing K]

/-- The base algebra on the quotient is induced by the ambient structure map. -/
abbrev supportAffineQuotientScalarAlgebra (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) (U : X.affineOpens) : Algebra K (supportAffineQuotient Z U) :=
  letI := SpecScalarTransport.specSectionScalarAlgebra f U
  inferInstance

/-- The affine quotient identification respects the actual base scalar map. -/
def supportAffineSectionsAlgEquiv (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) (U : X.affineOpens) :
    letI := SpecScalarTransport.specSectionScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) (supportAffineOpen Z U)
    letI := supportAffineQuotientScalarAlgebra Z f U
    Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, supportAffineOpen Z U) ≃ₐ[K] supportAffineQuotient Z U := by
  letI := SpecScalarTransport.specSectionScalarAlgebra f U
  letI := SpecScalarTransport.specSectionScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) (supportAffineOpen Z U)
  letI := supportAffineQuotientScalarAlgebra Z f U
  refine { supportAffineSectionsEquiv Z U with commutes' := ?_ }
  intro r
  calc
    supportAffineSectionsEquiv Z U
        (algebraMap K Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, supportAffineOpen Z U) r) =
      supportAffineSectionsEquiv Z U ((CycleClass.Geometric.GenericPoint.reducedSupportι Z).app U
        (algebraMap K Γ(X, U) r)) := by
          exact congrArg (supportAffineSectionsEquiv Z U)
            ((ClosedImmersionDimension.sectionPullbackAlgHom (CycleClass.Geometric.GenericPoint.reducedSupportι Z) f U).commutes r).symm
    _ = Ideal.Quotient.mk ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U)
        (algebraMap K Γ(X, U) r) := supportAffineSectionsEquiv_app Z U _
    _ = algebraMap K (supportAffineQuotient Z U) r := rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineQuotient
end ComponentSource_25

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineQuotient"

@[expose] public section ComponentSource_26
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension -/

/-! # Support Dimension -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension

noncomputable section

/-!
# Dimension of genuine irreducible closed supports

The dimension is the transcendence degree of the function field of the actual
reduced induced support scheme. On every nonempty ambient affine chart it is
the transcendence degree of the genuine quotient coordinate ring, or of its
fraction field. This file makes no identification with order-theoretic coheight.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The transcendence dimension of an irreducible support with its actual
reduced scheme structure and induced structural morphism. -/
def supportTranscendenceDimension (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) : ℕ :=
  TranscendenceDimension.schemeTranscendenceDimension (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)

/-- This dimension is computed in the true function field of the support. -/
theorem supportTranscendenceDimension_def (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
    supportTranscendenceDimension Z f =
      (Algebra.trdeg K (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField).toNat := rfl

/-- Local finite type guarantees that the natural number retains the full
cardinal-valued transcendence degree of the support. -/
theorem supportTranscendenceDimension_cast (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
    (supportTranscendenceDimension Z f : Cardinal) =
      Algebra.trdeg K (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField :=
  TranscendenceDimension.schemeTranscendenceDimension_cast (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)

/-- The support dimension can be computed on any nonempty affine chart of the
ambient scheme by its actual quotient coordinate ring. -/
theorem supportTranscendenceDimension_eq_affineQuotient
    (Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) (U : X.affineOpens)
    [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    letI := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
    supportTranscendenceDimension Z f =
      (Algebra.trdeg K (SupportAffineQuotient.supportAffineQuotient Z U)).toNat := by
  let := SpecScalarTransport.specSectionScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) (SupportAffineQuotient.supportAffineOpen Z U)
  let := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
  exact (TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
    (SupportAffineQuotient.supportAffineOpen Z U) (SupportAffineQuotient.supportAffineOpen_isAffine Z U)).trans
      (congrArg Cardinal.toNat (SupportAffineQuotient.supportAffineSectionsAlgEquiv Z f U).trdeg_eq)

/-- The same affine formula expressed in the fraction field of the quotient. -/
theorem supportTranscendenceDimension_eq_affineFractionRing
    (Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) (U : X.affineOpens)
    [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    letI := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
    supportTranscendenceDimension Z f =
      (Algebra.trdeg K (FractionRing (SupportAffineQuotient.supportAffineQuotient Z U))).toNat := by
  let := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
  exact (supportTranscendenceDimension_eq_affineQuotient Z f U).trans
    (congrArg Cardinal.toNat (TranscendenceDegreeTransfer.trdeg_eq_fractionRing K (SupportAffineQuotient.supportAffineQuotient Z U)))

/-- The quotient-to-function-field map respects the canonical base scalars. -/
theorem supportAffineQuotientFunctionField_isScalarTower
    (Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) (U : X.affineOpens)
    [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    letI := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
    letI := SupportAffineQuotient.supportAffineQuotientFunctionFieldAlgebra Z U
    letI := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
    IsScalarTower K (SupportAffineQuotient.supportAffineQuotient Z U) (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField := by
  let := SpecScalarTransport.specSectionScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) (SupportAffineQuotient.supportAffineOpen Z U)
  let := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
  let := SupportAffineQuotient.supportAffineQuotientFunctionFieldAlgebra Z U
  let := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
  let := FunctionFieldScalar.functionFieldScalar_isScalarTower (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) (SupportAffineQuotient.supportAffineOpen Z U)
  apply IsScalarTower.of_algebraMap_eq'
  ext r
  change algebraMap K (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField r =
    algebraMap Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, SupportAffineQuotient.supportAffineOpen Z U)
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField
        ((SupportAffineQuotient.supportAffineSectionsEquiv Z U).symm (algebraMap K (SupportAffineQuotient.supportAffineQuotient Z U) r))
  rw [IsScalarTower.algebraMap_apply K
    Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, SupportAffineQuotient.supportAffineOpen Z U) (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField]
  exact congrArg
    (algebraMap Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, SupportAffineQuotient.supportAffineOpen Z U)
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField)
    ((SupportAffineQuotient.supportAffineSectionsAlgEquiv Z f U).symm.commutes r).symm

/-- The quotient fraction field is canonically isomorphic over the actual base
field to the function field of the reduced support. -/
def supportFunctionFieldEquivAffineFractionRing
    (Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) (U : X.affineOpens)
    [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    letI := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
    letI := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField ≃ₐ[K] FractionRing (SupportAffineQuotient.supportAffineQuotient Z U) := by
  letI := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
  letI := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
  letI := SupportAffineQuotient.supportAffineQuotientFunctionFieldAlgebra Z U
  letI := supportAffineQuotientFunctionField_isScalarTower Z f U
  letI := SupportAffineQuotient.supportAffineQuotient_isFractionRing Z U
  exact ((FractionRing.algEquiv (SupportAffineQuotient.supportAffineQuotient Z U)
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField).symm).restrictScalars K

/-- A genuine irreducible closed support has dimension at most that of its
integral ambient scheme. Local finite type makes the natural-number comparison
faithful to the proved function-field transcendence-degree comparison. -/
theorem supportTranscendenceDimension_le [IsIntegral X]
    (Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    supportTranscendenceDimension Z f ≤ TranscendenceDimension.schemeTranscendenceDimension f := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
  apply (Nat.cast_le (α := Cardinal)).mp
  rw [supportTranscendenceDimension_cast Z f, TranscendenceDimension.schemeTranscendenceDimension_cast f]
  exact ClosedImmersionDimension.closedImmersion_functionField_trdeg_le (CycleClass.Geometric.GenericPoint.reducedSupportι Z) f

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension
end ComponentSource_26

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension"

@[expose] public section ComponentSource_27
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineInclusion -/

/-! # Support Affine Inclusion -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineInclusion

noncomputable section

/-!
# Strict inclusion of irreducible supports on a common affine open

A nonempty open part of an irreducible closed set is dense in that closed set.
Consequently a proper closed subset cannot become the entire support after
restriction to an open meeting it. On an affine open, the actual vanishing
ideals of the two reduced supports are therefore strictly nested in the
opposite direction. The quotient rings are those of `SupportAffineQuotient`.

These statements require no finite-type or dimension hypothesis.
-/

open _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

section Topology

variable {T : Type u} [TopologicalSpace T]

/-- Every nonempty open part of an irreducible closed set has that entire
closed set as its ambient closure. -/
theorem irreducibleCloseds_closure_inter_open (W : IrreducibleCloseds T)
    (U : Opens T) (hWU : ((W : Set T) ∩ (U : Set T)).Nonempty) :
    closure ((W : Set T) ∩ (U : Set T)) = (W : Set T) := by
  apply Set.Subset.antisymm
  · exact closure_minimal Set.inter_subset_left W.isClosed
  · exact subset_closure_inter_of_isPreirreducible_of_isOpen
      W.isIrreducible.2 U.isOpen hWU

/-- Proper inclusion of irreducible closed supports persists on every open
set meeting the smaller support. -/
theorem irreducibleCloseds_inter_open_ssubset (Z W : IrreducibleCloseds T)
    (hZW : Z < W) (U : Opens T)
    (hZU : ((Z : Set T) ∩ (U : Set T)).Nonempty) :
    (Z : Set T) ∩ (U : Set T) ⊂ (W : Set T) ∩ (U : Set T) := by
  have hWU : ((W : Set T) ∩ (U : Set T)).Nonempty := by
    obtain ⟨x, hxZ, hxU⟩ := hZU
    exact ⟨x, hZW.le hxZ, hxU⟩
  rw [Set.ssubset_def]
  refine ⟨Set.inter_subset_inter_left _ hZW.le, ?_⟩
  intro h
  apply (not_le_of_gt hZW)
  have hsub : closure ((W : Set T) ∩ (U : Set T)) ⊆ (Z : Set T) :=
    closure_minimal (h.trans Set.inter_subset_left) Z.isClosed
  rwa [irreducibleCloseds_closure_inter_open W U hWU] at hsub

end Topology

variable {X : Scheme.{u}}

/-- The support's inverse-image open is nonempty precisely when the ambient
open meets the support. -/
theorem supportAffineOpen_nonempty_iff (Z : IrreducibleCloseds X)
    (U : X.affineOpens) :
    Nonempty (SupportAffineQuotient.supportAffineOpen Z U) ↔
      ((Z : Set X) ∩ (U.1 : Set X)).Nonempty := by
  constructor
  · rintro ⟨⟨x, hx⟩⟩
    refine ⟨CycleClass.Geometric.GenericPoint.reducedSupportι Z x, ?_, hx⟩
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι Z]
    exact ⟨x, rfl⟩
  · rintro ⟨x, hxZ, hxU⟩
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι Z] at hxZ
    obtain ⟨y, rfl⟩ := hxZ
    exact ⟨⟨y, hxU⟩⟩

/-- An affine open meeting the smaller support also meets every containing
support. -/
theorem supportAffineOpen_nonempty_of_le (Z W : IrreducibleCloseds X)
    (hZW : Z ≤ W) (U : X.affineOpens) [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    Nonempty (SupportAffineQuotient.supportAffineOpen W U) := by
  apply (supportAffineOpen_nonempty_iff W U).mpr
  obtain ⟨x, hxZ, hxU⟩ := (supportAffineOpen_nonempty_iff Z U).mp inferInstance
  exact ⟨x, hZW hxZ, hxU⟩

/-- Every irreducible support meets an actual affine open of the ambient scheme. -/
theorem exists_supportAffineOpen_nonempty (Z : IrreducibleCloseds X) :
    ∃ U : X.affineOpens, Nonempty (SupportAffineQuotient.supportAffineOpen Z U) := by
  obtain ⟨x, hxZ⟩ := Z.isIrreducible.nonempty
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  exact ⟨⟨U, hU⟩, (supportAffineOpen_nonempty_iff Z ⟨U, hU⟩).mpr ⟨x, hxZ, hxU⟩⟩

/-- Nested irreducible supports admit a common ambient affine open meeting both. -/
theorem exists_common_supportAffineOpen (Z W : IrreducibleCloseds X)
    (hZW : Z ≤ W) :
    ∃ U : X.affineOpens,
      Nonempty (SupportAffineQuotient.supportAffineOpen Z U) ∧ Nonempty (SupportAffineQuotient.supportAffineOpen W U) := by
  obtain ⟨U, hU⟩ := exists_supportAffineOpen_nonempty Z
  let : Nonempty (SupportAffineQuotient.supportAffineOpen Z U) := hU
  exact ⟨U, hU, supportAffineOpen_nonempty_of_le Z W hZW U⟩

/-- An ambient affine open meeting a support contains its generic point. -/
theorem support_genericPoint_mem_affineOpen (Z : IrreducibleCloseds X)
    (U : X.affineOpens) [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    irreducibleSetEquivPoints Z ∈ U.1 := by
  apply (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem_open_set_iff
    U.1.isOpen |>.mpr
  exact (supportAffineOpen_nonempty_iff Z U).mp inferInstance

/-- Inverse images in the actual affine spectrum preserve the strict support
inclusion whenever that affine open meets the smaller support. -/
theorem supportAffine_preimage_ssubset (Z W : IrreducibleCloseds X)
    (hZW : Z < W) (U : X.affineOpens) [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    U.2.fromSpec ⁻¹' (Z : Set X) ⊂ U.2.fromSpec ⁻¹' (W : Set X) := by
  have h := irreducibleCloseds_inter_open_ssubset Z W hZW U.1
    ((supportAffineOpen_nonempty_iff Z U).mp inferInstance)
  rw [Set.ssubset_def] at h ⊢
  refine ⟨Set.preimage_mono hZW.le, ?_⟩
  intro hpre
  apply h.2
  intro x hx
  have hxRange : x ∈ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    exact hx.2
  obtain ⟨y, rfl⟩ := hxRange
  exact ⟨hpre hx.1, hx.2⟩

/-- Actual affine support ideals reverse inclusion. -/
theorem supportAffineIdeal_le (Z W : IrreducibleCloseds X)
    (hZW : Z ≤ W) (U : X.affineOpens) :
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W).ideal U ≤ (CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U := by
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (W : Set X)) ≤
    PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))
  exact PrimeSpectrum.vanishingIdeal_anti_mono (Set.preimage_mono hZW)

/-- The vanishing ideals of proper nested supports are strictly nested in the
opposite direction on a common affine open meeting the smaller support. -/
theorem supportAffineIdeal_lt (Z W : IrreducibleCloseds X)
    (hZW : Z < W) (U : X.affineOpens) [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W).ideal U < (CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U := by
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (W : Set X)) <
    PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))
  exact (PrimeSpectrum.vanishingIdeal_strict_anti_mono_iff
    (Z.isClosed.preimage U.2.fromSpec.continuous)
    (W.isClosed.preimage U.2.fromSpec.continuous)).mp
      (supportAffine_preimage_ssubset Z W hZW U)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineInclusion
end ComponentSource_27

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineInclusion"

@[expose] public section ComponentSource_28
/- Original module: OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension -/

/-! # Support Codimension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension

noncomputable section

/-!
# ChernClass: codimension-one scheme points give dimension-graded divisor supports

The affine ideal of the closure of a point is its actual prime ideal on an
affine chart. Its height is the point's specialization coheight. The proved
finite-type height-one formula identifies the support dimension exactly.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Construction

variable {X : Scheme}

/-- The reduced affine ideal of a point's closure is precisely the point's affine prime. -/
theorem pointClosure_affineIdeal (x : X) (U : X.affineOpens) (hx : x ∈ U.1) :
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (irreducibleSetEquivPoints.symm x)).ideal U =
      (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' closure {x}) = _
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous]
  have hp : U.2.fromSpec ⁻¹' {x} = {U.2.primeIdealOf ⟨x, hx⟩} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy
      apply U.2.fromSpec.isOpenEmbedding.injective
      rw [U.2.fromSpec_primeIdealOf, hy]
    · intro hy
      rw [hy, U.2.fromSpec_primeIdealOf]
  rw [hp, PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]

/-- The affine prime height is the scheme point's actual specialization coheight. -/
theorem pointClosure_affineIdeal_height (x : X) (U : X.affineOpens) (hx : x ∈ U.1) :
    ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal (irreducibleSetEquivPoints.symm x)).ideal U).height = Order.coheight x := by
  rw [pointClosure_affineIdeal x U hx]
  calc
    (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.height =
        Order.coheight (show Spec Γ(X, U) from U.2.primeIdealOf ⟨x, hx⟩) :=
      idealHeight_eq_coheight Γ(X, U) _
    _ = Order.coheight x := by
      rw [← coheight_eq_of_isOpenImmersion U.2.fromSpec, U.2.fromSpec_primeIdealOf]

/-- A codimension-one point has support dimension exactly one less than the ambient integral scheme. -/
theorem pointClosure_dimension_add_one [IsIntegral X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (x : X) (hx : Order.coheight x = 1) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + 1 =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let V : X.affineOpens := ⟨U, hU⟩
  let Z : IrreducibleCloseds X := irreducibleSetEquivPoints.symm x
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Nonempty (Foundations.Scheme.SupportAffineQuotient.supportAffineOpen Z V) := (Foundations.Scheme.SupportAffineInclusion.supportAffineOpen_nonempty_iff Z V).mpr
    ⟨x, subset_closure (Set.mem_singleton x), hxU⟩
  let : Algebra ℂ Γ(X, U) := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let : Algebra.FiniteType ℂ Γ(X, U) := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let : ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal V).IsPrime := Foundations.Scheme.SupportAffineQuotient.supportAffineIdeal_isPrime Z V
  have hp : ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal V).height = 1 :=
    (pointClosure_affineIdeal_height x V hxU).trans hx
  rw [Foundations.Scheme.SupportDimension.supportTranscendenceDimension_eq_affineQuotient Z f V,
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections f U hU]
  exact HeightOneDimension.Construction.finiteType_height_one_trdeg ℂ Γ(X, U) ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal V) hp

end Construction

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension
end ComponentSource_28

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension"

@[expose] public section ComponentSource_29
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension -/

/-! # Support Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension.BundleCycles

noncomputable section

/-!
# LineBundleCycles: point-support dimension under closed immersion

On a common affine chart, a closed immersion induces a surjection of
coordinate rings. Quotienting by the actual point primes therefore gives
isomorphic algebras and preserves the transcendence dimension of the
reduced point closures.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {k : Type} [Field k] {X Y : Scheme}

/-- The point closure has the dimension of its actual affine prime quotient. -/
theorem pointClosure_dimension_eq_affine (f : X ⟶ Spec (CommRingCat.of k))
    (x : X) (U : X.affineOpens) (hx : x ∈ U.1) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U.1
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f =
      (Algebra.trdeg k (Γ(X, U.1) ⧸ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal)).toNat := by
  let Z := irreducibleSetEquivPoints.symm x
  have : Nonempty (Foundations.Scheme.SupportAffineQuotient.supportAffineOpen Z U) :=
    (Foundations.Scheme.SupportAffineInclusion.supportAffineOpen_nonempty_iff Z U).mpr ⟨x, subset_closure (Set.mem_singleton x), hx⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U.1
  have h := Foundations.Scheme.SupportDimension.supportTranscendenceDimension_eq_affineQuotient Z f U
  exact h.trans (congrArg (fun J : Ideal Γ(X, U.1) => (Algebra.trdeg k (Γ(X, U.1) ⧸ J)).toNat)
    (DivisorClass.Chern.SupportCodimension.Construction.pointClosure_affineIdeal x U hx))

/-- A closed immersion preserves the dimension of every reduced point closure. -/
theorem pointClosure_dimension_closedImmersion (i : X ⟶ Y) [IsClosedImmersion i]
    (f : Y ⟶ Spec (CommRingCat.of k)) (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (i x)) f =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (i x))
  let V := i ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage i
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (i ≫ f) V
  let p := hU.primeIdealOf ⟨i x, hxU⟩
  let q := hV.primeIdealOf ⟨x, hxU⟩
  let a := Foundations.Scheme.ClosedImmersionDimension.sectionPullbackAlgHom i f U
  have hprime : q.asIdeal.comap a.toRingHom = p.asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hxU
    have he := congrArg PrimeSpectrum.asIdeal h
    change q.asIdeal.comap (i.appLE U V le_rfl).hom = p.asIdeal at he
    exact (congrArg (fun b : Γ(Y, U) ⟶ Γ(X, V) => q.asIdeal.comap b.hom)
      i.app_eq_appLE).trans he
  have hq := Affine.SpecializationGrading.BundleCycles.quotient_trdeg_of_surjective (k := k) (A := Γ(Y, U)) (B := Γ(X, V))
    a (Foundations.Scheme.ClosedImmersionDimension.sectionPullbackAlgHom_surjective i f U hU) q.asIdeal
  have hpDim : (Algebra.trdeg k (Γ(Y, U) ⧸ p.asIdeal)).toNat =
      (Algebra.trdeg k (Γ(X, V) ⧸ q.asIdeal)).toNat :=
    (congrArg (fun J : Ideal Γ(Y, U) => (Algebra.trdeg k (Γ(Y, U) ⧸ J)).toNat) hprime.symm).trans
      (congrArg Cardinal.toNat hq)
  exact (pointClosure_dimension_eq_affine f (i x) ⟨U, hU⟩ hxU).trans
    (hpDim.trans (pointClosure_dimension_eq_affine (i ≫ f) x ⟨V, hV⟩ hxU).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension.BundleCycles
end ComponentSource_29

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension"


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
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion, "theorem")
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
    ("nonce", toJson "5ed4a7b6e1eb1dc8e6713a96557d5928"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:5ed4a7b6e1eb1dc8e6713a96557d5928"
