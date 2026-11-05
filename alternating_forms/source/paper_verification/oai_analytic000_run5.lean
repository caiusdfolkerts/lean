module

public import paper_verification.oai_chow001_run2
import all paper_verification.oai_chow001_run2
public import Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Group.Affine
import all Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.Analysis.Complex.Basic
import all Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff
import all Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Algebra.Category.CommAlgCat.Basic
import all Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Topology.Category.TopCat.Basic
import all Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import Mathlib.RingTheory.Localization.Away.Basic
import all Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Basic.Complex.Basic
import all Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.GroupWithZero
import all Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.MvPolynomial
import all Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.RingTheory.Nullstellensatz
import all Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Topology.ContinuousOn
import all Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Homeomorph.Lemmas
import all Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import all Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import all Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Pullbacks
import all Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.ResidueField
import all Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.LocallyClosed
import all Mathlib.Topology.LocallyClosed
public import Mathlib.RingTheory.FiniteType
import all Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.Compactness.LocallyCompact
import all Mathlib.Topology.Compactness.LocallyCompact
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.OpenImmersionPoints -/

/-! # Open Immersion Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.OpenImmersionPoints

noncomputable section

/-!
# Relative points of an open subscheme

The universal property of an actual open immersion lifts exactly those scheme
maps whose underlying image is contained in its open image. The lift respects
the base automatically. For complex-valued points, the image condition reduces
to membership of their unique underlying scheme point.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Lift a relative test point through an open immersion when its image lies
inside the open subscheme. Base compatibility follows from the lift equation. -/
def openImmersion_relativeLift {S : Scheme.{u}} {T U X : Over S}
    (i : U ⟶ X) [IsOpenImmersion i.left] (p : T ⟶ X)
    (hp : Set.range p.left ⊆ Set.range i.left) : T ⟶ U :=
  Over.homMk (IsOpenImmersion.lift i.left p.left hp) (by
    rw [← Over.w i, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w p])

@[reassoc (attr := simp)]
theorem openImmersion_relativeLift_fac {S : Scheme.{u}} {T U X : Over S}
    (i : U ⟶ X) [IsOpenImmersion i.left] (p : T ⟶ X)
    (hp : Set.range p.left ⊆ Set.range i.left) :
    openImmersion_relativeLift i p hp ≫ i = p := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac i.left p.left hp

/-- This relative lift is unique, by monomorphy of the open immersion. -/
theorem openImmersion_relativeLift_unique {S : Scheme.{u}} {T U X : Over S}
    (i : U ⟶ X) [IsOpenImmersion i.left] (p : T ⟶ X)
    (hp : Set.range p.left ⊆ Set.range i.left) (q : T ⟶ U) (hq : q ≫ i = p) :
    q = openImmersion_relativeLift i p hp := by
  let : Mono i := Over.mono_of_mono_left i
  apply (cancel_mono i).mp
  exact hq.trans (openImmersion_relativeLift_fac i p hp).symm

/-- Relative points of an open subscheme are exactly relative points whose
scheme-theoretic image lies inside that open subscheme. -/
def openImmersion_relativePointEquiv {S : Scheme.{u}} {T U X : Over S}
    (i : U ⟶ X) [IsOpenImmersion i.left] :
    (T ⟶ U) ≃ {p : T ⟶ X // Set.range p.left ⊆ Set.range i.left} where
  toFun q := ⟨q ≫ i, by
    rintro z ⟨t, rfl⟩
    exact ⟨q.left t, (Scheme.Hom.comp_apply q.left i.left t).symm⟩⟩
  invFun p := openImmersion_relativeLift i p.val p.property
  left_inv q := (openImmersion_relativeLift_unique i (q ≫ i) _ q rfl).symm
  right_inv p := Subtype.ext (openImmersion_relativeLift_fac i p.val p.property)

@[simp]
theorem openImmersion_relativePointEquiv_apply_val {S : Scheme.{u}} {T U X : Over S}
    (i : U ⟶ X) [IsOpenImmersion i.left] (q : T ⟶ U) :
    (openImmersion_relativePointEquiv i q).val = q ≫ i := rfl

/-- A complex point has singleton scheme-theoretic image, so containment in an
open image is equivalent to membership of its unique point. -/
theorem complexPoint_range_subset_iff {U X : Over ProjectiveSpace.complexBase} (i : U ⟶ X)
    (p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) :
    Set.range p.left ⊆ Set.range i.left ↔ p.left (default : ProjectiveSpace.complexBase) ∈ Set.range i.left := by
  let : Unique (Over.mk (𝟙 ProjectiveSpace.complexBase)).left := inferInstanceAs (Unique ProjectiveSpace.complexBase)
  rw [Set.range_unique, Set.singleton_subset_iff]

/-- An open immersion induces a bijection onto the complex points whose
underlying point lies in the open image. -/
def openImmersion_complexPointEquiv {U X : Over ProjectiveSpace.complexBase}
    (i : U ⟶ X) [IsOpenImmersion i.left] :
    (Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ U) ≃
      {p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X // p.left (default : ProjectiveSpace.complexBase) ∈ Set.range i.left} :=
  (openImmersion_relativePointEquiv i).trans
    (Equiv.subtypeEquivRight (complexPoint_range_subset_iff i))

@[simp]
theorem openImmersion_complexPointEquiv_apply_val {U X : Over ProjectiveSpace.complexBase}
    (i : U ⟶ X) [IsOpenImmersion i.left] (q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ U) :
    (openImmersion_complexPointEquiv i q).val = q ≫ i := rfl

/-- The point map of an open immersion is injective. -/
theorem openImmersion_complexPointMap_injective {U X : Over ProjectiveSpace.complexBase}
    (i : U ⟶ X) [IsOpenImmersion i.left] :
    Function.Injective (fun q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ U => q ≫ i) := by
  intro q r h
  apply (openImmersion_complexPointEquiv i).injective
  exact Subtype.ext h

/-- Exact set-theoretic image of the complex-point map. -/
theorem range_openImmersion_complexPointMap {U X : Over ProjectiveSpace.complexBase}
    (i : U ⟶ X) [IsOpenImmersion i.left] :
    Set.range (fun q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ U => q ≫ i) =
      {p | p.left (default : ProjectiveSpace.complexBase) ∈ Set.range i.left} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact (openImmersion_complexPointEquiv i q).property
  · intro hp
    refine ⟨(openImmersion_complexPointEquiv i).symm ⟨p, hp⟩, ?_⟩
    exact congrArg Subtype.val ((openImmersion_complexPointEquiv i).apply_symm_apply ⟨p, hp⟩)

/-- Every complex point in the open image has a unique relative lift. -/
theorem openImmersion_complexPoint_existsUnique {U X : Over ProjectiveSpace.complexBase}
    (i : U ⟶ X) [IsOpenImmersion i.left]
    (p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) (hp : p.left (default : ProjectiveSpace.complexBase) ∈ Set.range i.left) :
    ∃! q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ U, q ≫ i = p := by
  let q := (openImmersion_complexPointEquiv i).symm ⟨p, hp⟩
  have hq : q ≫ i = p :=
    congrArg Subtype.val ((openImmersion_complexPointEquiv i).apply_symm_apply ⟨p, hp⟩)
  refine ⟨q, hq, ?_⟩
  intro r hr
  exact openImmersion_complexPointMap_injective i (hr.trans hq.symm)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.OpenImmersionPoints
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.OpenImmersionPoints"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints -/

/-! # Affine Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints

/-!
# Affine complex points and scheme morphisms

The carrier of affine complex points is the standard algebraic one: complex-algebra
homomorphisms to `ℂ`. Fully faithfulness of mathlib's relative `Spec` functor identifies
these points with scheme morphisms over `Spec ℂ`. No topology is installed here.
-/

open _root_.CategoryTheory Opposite _root_.AlgebraicGeometry

universe u

/-- The complex points of an affine complex algebra are its complex-algebra characters. -/
abbrev affineComplexPoints (A : Type u) [CommRing A] [Algebra ℂ A] := A →ₐ[ℂ] ℂ

/-- The affine scheme of an algebra, equipped with its actual structure morphism. -/
noncomputable abbrev affineSchemeOver (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Over (Spec (CommRingCat.of R)) :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))

/-- Packaging an algebra homomorphism as an arrow in the opposite algebra category. -/
def algHomOppositeEquiv (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    (A →ₐ[R] B) ≃ (op (CommAlgCat.of R B) ⟶ op (CommAlgCat.of R A)) where
  toFun f := (CommAlgCat.ofHom f).op
  invFun f := f.unop.hom
  left_inv _ := rfl
  right_inv _ := rfl

/-- The fully faithful relative spectrum functor, written on ordinary algebra homomorphisms. -/
noncomputable def affineAlgHomOverSpecEquiv (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] :
    (A →ₐ[R] B) ≃ (affineSchemeOver R B ⟶ affineSchemeOver R A) :=
  (algHomOppositeEquiv R A B).trans (algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv

/-- The scheme morphism underlying the equivalence is precisely `Spec.map`. -/
@[simp] theorem affineAlgHomOverSpecEquiv_left (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) :
    (affineAlgHomOverSpecEquiv R A B f).left =
      Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

/-- Complex-algebra characters are exactly morphisms from the complex point over `Spec ℂ`. -/
noncomputable def affineComplexPointsEquiv (A : Type) [CommRing A] [Algebra ℂ A] :
    affineComplexPoints A ≃ (affineSchemeOver ℂ ℂ ⟶ affineSchemeOver ℂ A) :=
  affineAlgHomOverSpecEquiv ℂ A ℂ

/-- This correspondence sends a complex character to its usual spectrum morphism. -/
@[simp] theorem affineComplexPointsEquiv_left (A : Type) [CommRing A] [Algebra ℂ A]
    (x : affineComplexPoints A) :
    (affineComplexPointsEquiv A x).left =
      Spec.map (CommRingCat.ofHom x.toRingHom) := rfl

/-- The base object used for points has identity structure morphism. -/
@[simp] theorem affineComplexBase_hom :
    (affineSchemeOver ℂ ℂ).hom = 𝟙 (Spec (CommRingCat.of ℂ)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = _
  simp

/-- The base algebra, as a relative affine scheme, is the identity object.
The construction is polymorphic so that no concrete scalar implementation is unfolded. -/
noncomputable def affineBaseIso (R : Type u) [CommRing R] :
    affineSchemeOver R R ≅ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of R))) (by
    change 𝟙 (Spec (CommRingCat.of R)) ≫ 𝟙 (Spec (CommRingCat.of R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R R))
    simp)

/-- The spectrum of `ℂ` as a relative affine scheme is the identity object over the base. -/
noncomputable def affineComplexBaseIso :
    affineSchemeOver ℂ ℂ ≅ Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) :=
  affineBaseIso ℂ

/-- The standard relative-points formulation, with the literal identity object as source. -/
noncomputable def affineComplexPointsOverEquiv (A : Type) [CommRing A] [Algebra ℂ A] :
    affineComplexPoints A ≃
      (Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ affineSchemeOver ℂ A) :=
  (affineComplexPointsEquiv A).trans
    { toFun := fun f => affineComplexBaseIso.inv ≫ f
      invFun := fun f => affineComplexBaseIso.hom ≫ f
      left_inv := fun f => by simp
      right_inv := fun f => by simp }

/-- The relative-points equivalence has the usual underlying spectrum map. -/
@[simp] theorem affineComplexPointsOverEquiv_left (A : Type) [CommRing A] [Algebra ℂ A]
    (x : affineComplexPoints A) :
    (affineComplexPointsOverEquiv A x).left =
      Spec.map (CommRingCat.ofHom x.toRingHom) := by
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom x.toRingHom) = _
  simp

end OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.Affine -/

/-! # Affine -/

namespace OAI.AlgebraicGeometry

/-!
# Ordinary topology on affine complex points

For a complex algebra `A`, a complex point is an algebra homomorphism `A →ₐ[ℂ] ℂ`.
We give these points the topology induced by evaluation into the product `A → ℂ`,
where each factor has the usual topology on the complex numbers. Thus this is
the topology generated by evaluations of regular functions, not a scheme's
Zariski topology. The connection with finite-dimensional affine coordinates is
proved separately in `PolynomialEvaluation`.
-/

universe u v

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- Evaluation of a regular function at an affine complex point. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval (a : A) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) : ℂ := x a

/-- The ordinary topology generated by all complex-valued regular functions. -/
noncomputable instance Foundations.Scheme.AffineComplexPoints.affineComplexPoints.instTopologicalSpace : TopologicalSpace (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :=
  TopologicalSpace.induced
    (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => (x : A → ℂ)) inferInstance

/-- The topology on affine points is induced by their evaluations. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coe :
    Topology.IsInducing (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => (x : A → ℂ)) :=
  ⟨rfl⟩

/-- Distinct algebra characters are separated by evaluation. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isEmbedding_coe :
    Topology.IsEmbedding (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => (x : A → ℂ)) :=
  ⟨Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coe, DFunLike.coe_injective⟩

/-- Evaluation of every regular function is continuous. -/
@[continuity, fun_prop]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval (a : A) : Continuous (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval a) :=
  (continuous_apply a).comp continuous_induced_dom

/-- Continuity into affine points is exactly continuity of all evaluations. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff {X : Type v} [TopologicalSpace X]
    (f : X → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Continuous f ↔ ∀ a : A, Continuous (fun x => f x a) := by
  exact continuous_induced_rng.trans continuous_pi_iff

/-- Equivalently, the point topology is the infimum of the evaluation topologies. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.topology_eq_iInf :
    (inferInstance : TopologicalSpace (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)) =
      ⨅ a : A, TopologicalSpace.induced (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval a) inferInstance := by
  change TopologicalSpace.induced
      (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => (x : A → ℂ))
      (⨅ a : A, TopologicalSpace.induced (fun f : A → ℂ => f a) inferInstance) = _
  rw [induced_iInf]
  apply iInf_congr
  intro a
  rw [induced_compose]
  rfl

/-- Open sets of affine points are intersections with open sets of the product. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_iff (s : Set (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)) :
    IsOpen s ↔ ∃ t : Set (A → ℂ), IsOpen t ∧
      (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => (x : A → ℂ)) ⁻¹' t = s :=
  Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coe.isOpen_iff

/-- The ordinary topology on affine complex points is Hausdorff. -/
instance Foundations.Scheme.AffineComplexPoints.affineComplexPoints.instT2Space : T2Space (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :=
  Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isEmbedding_coe.t2Space

end OAI.AlgebraicGeometry
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.Affine"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointMaps -/

/-! # Affine Point Maps -/

namespace OAI.AlgebraicGeometry

/-!+# Continuous maps of affine complex points

The evaluation topology on `affineComplexPoints A = (A →ₐ[ℂ] ℂ)` makes
precomposition by an actual complex algebra homomorphism continuous. These maps
form a contravariant functor from complex commutative algebras to topological
spaces. No continuity assumption on the algebra homomorphism is needed.
-/

universe u v w

section

variable {A : Type u} {B : Type v} {D : Type w}
variable [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B]
variable [CommRing D] [Algebra ℂ D]

/-- The continuous map of complex points induced contravariantly by an algebra map. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (f : A →ₐ[ℂ] B) : C(Foundations.Scheme.AffineComplexPoints.affineComplexPoints B, Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) where
  toFun x := x.comp f
  continuous_toFun := by
    apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).mpr
    intro a
    exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval (f a)

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap_apply (f : A →ₐ[ℂ] B) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (a : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x a = x (f a) := rfl

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap_id :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (AlgHom.id ℂ A) = ContinuousMap.id (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) := by
  ext x a
  rfl

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap_comp (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] D) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (g.comp f) = (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f).comp (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap g) := by
  ext x a
  rfl

/-- Isomorphic complex algebras have homeomorphic spaces of complex points. -/
noncomputable def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comapHomeomorph (e : A ≃ₐ[ℂ] B) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints B ≃ₜ Foundations.Scheme.AffineComplexPoints.affineComplexPoints A where
  toFun := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap e.toAlgHom
  invFun := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap e.symm.toAlgHom
  left_inv x := by
    ext b
    change x (e (e.symm b)) = x b
    exact congrArg x (e.apply_symm_apply b)
  right_inv x := by
    ext a
    change x (e.symm (e a)) = x a
    exact congrArg x (e.symm_apply_apply a)
  continuous_toFun := (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap e.toAlgHom).continuous
  continuous_invFun := (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap e.symm.toAlgHom).continuous

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comapHomeomorph_apply (e : A ≃ₐ[ℂ] B) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (a : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comapHomeomorph e x a = x (e a) := rfl

end

open _root_.CategoryTheory Opposite

/-- Under the standard affine-scheme correspondence, precomposition is composition
with the induced morphism of affine schemes over `Spec ℂ`. -/
@[simp]
theorem ComplexPoints.Analytic.AffinePointMaps.affineComplexPointsEquiv_comap {A B : Type}
    [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPointsEquiv A (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) =
      Foundations.Scheme.AffineComplexPoints.affineComplexPointsEquiv B x ≫ Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B f := by
  apply Over.OverMorphism.ext
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsEquiv_left, Over.comp_left, Foundations.Scheme.AffineComplexPoints.affineComplexPointsEquiv_left,
    Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv_left]
  exact AlgebraicGeometry.Spec.map_comp (CommRingCat.ofHom f.toRingHom)
    (CommRingCat.ofHom x.toRingHom)

/-- Complex points, with their evaluation topology, form a contravariant functor. -/
noncomputable def ComplexPoints.Analytic.AffinePointMaps.affineComplexPointsFunctor : (CommAlgCat.{u} ℂ)ᵒᵖ ⥤ TopCat.{u} where
  obj A := TopCat.of (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A.unop)
  map f := TopCat.ofHom (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f.unop.hom)
  map_id A := by
    ext x a
    rfl
  map_comp f g := by
    ext x a
    rfl

end OAI.AlgebraicGeometry
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointMaps"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs -/

/-! # Scheme Point Homeomorphs -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-!
# Complex points of schemes and their affine-test topology

The carrier is the actual type of morphisms over `Spec ℂ` from the complex
point. Its topology is final with respect to all maps from ordinary affine
complex point spaces induced by actual morphisms of schemes over `Spec ℂ`.
This definition uses no chosen atlas or additional geometric data.

This file proves the universal continuity criterion, functoriality, and exact
recovery of the ordinary evaluation topology for affine schemes. Recovery
along arbitrary open immersions is a separate gluing theorem.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Genuine complex-valued points of a scheme over the complex base. -/
abbrev schemeComplexPoints (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) := (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X)

/-- The standard affine-character correspondence with the native scheme-point carrier. -/
abbrev affineSchemePointEquiv (A : Type) [CommRing A] [Algebra ℂ A] :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints A ≃ schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A) :=
  Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A

/-- The native affine-point correspondence commutes with the genuine scheme maps. -/
@[simp]
theorem affineSchemePointEquiv_comap {A B : Type}
    [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    affineSchemePointEquiv A (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) =
      affineSchemePointEquiv B x ≫ Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B f := by
  change Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫
      Foundations.Scheme.AffineComplexPoints.affineComplexPointsEquiv A (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) =
    (Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫ Foundations.Scheme.AffineComplexPoints.affineComplexPointsEquiv B x) ≫ _
  rw [AffinePointMaps.affineComplexPointsEquiv_comap, Category.assoc]

namespace schemeComplexPoints

variable {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- Postcomposition is the actual covariant map on complex-valued points. -/
def map (f : X ⟶ Y) (x : schemeComplexPoints X) : schemeComplexPoints Y := x ≫ f

@[simp]
theorem map_id (x : schemeComplexPoints X) : schemeComplexPoints.map (𝟙 X) x = x := Category.comp_id x

@[simp]
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : schemeComplexPoints X) :
    schemeComplexPoints.map (f ≫ g) x = schemeComplexPoints.map g (schemeComplexPoints.map f x) := (Category.assoc x f g).symm

/-- A genuine affine scheme map induces this map from ordinary affine complex points. -/
def affinePointMap (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) : schemeComplexPoints X :=
  affineSchemePointEquiv A x ≫ f

@[simp]
theorem affinePointMap_comp (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (g : X ⟶ Y) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    affinePointMap A (f ≫ g) x = schemeComplexPoints.map g (affinePointMap A f x) :=
  (Category.assoc _ _ _).symm

/-- Algebra-map precomposition agrees with composition of the corresponding affine tests. -/
theorem affinePointMap_comap (A B : CommAlgCat ℂ) (f : A →ₐ[ℂ] B)
    (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    affinePointMap B (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B f ≫ g) x =
      affinePointMap A g (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) := by
  change affineSchemePointEquiv B x ≫ (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B f ≫ g) =
    affineSchemePointEquiv A (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) ≫ g
  rw [affineSchemePointEquiv_comap, Category.assoc]

/-- The topology final with respect to all actual affine complex-point test maps. -/
@[instance_reducible]
def analyticTopology (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : TopologicalSpace (schemeComplexPoints X) :=
  ⨆ (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X),
    TopologicalSpace.coinduced (affinePointMap A f) inferInstance

instance instTopologicalSpace (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    TopologicalSpace (schemeComplexPoints X) := analyticTopology X

/-- Each affine test map is continuous by construction of the final topology. -/
theorem continuous_affinePointMap (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) :
    Continuous (affinePointMap A f) := by
  apply continuous_iff_coinduced_le.mpr
  exact le_iSup_of_le A (le_iSup_of_le f le_rfl)

/-- A map from scheme points is continuous exactly when every affine test is continuous. -/
theorem continuous_iff_affineTests {T : Type*} [TopologicalSpace T]
    (F : schemeComplexPoints X → T) :
    Continuous F ↔ ∀ (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X),
      Continuous (fun x => F (affinePointMap A f x)) := by
  change @Continuous _ _ (analyticTopology X) _ F ↔ _
  simp only [continuous_iSup_dom, continuous_coinduced_dom,
    Function.comp_def]

/-- Openness in the final topology can be tested on every actual affine scheme map. -/
theorem isOpen_iff_affineTests (S : Set (schemeComplexPoints X)) :
    IsOpen S ↔ ∀ (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X),
      IsOpen (affinePointMap A f ⁻¹' S) := by
  change @IsOpen _ (analyticTopology X) S ↔ _
  simp only [isOpen_iSup_iff, isOpen_coinduced]

/-- Every morphism of complex schemes gives a continuous map on these complex points. -/
theorem continuous_map (f : X ⟶ Y) : Continuous (schemeComplexPoints.map f) := by
  apply (continuous_iff_affineTests _).mpr
  intro A g
  change Continuous (fun x => (affineSchemePointEquiv A x ≫ g) ≫ f)
  have h : Continuous (fun x => affineSchemePointEquiv A x ≫ (g ≫ f)) :=
    continuous_affinePointMap A (g ≫ f)
  simpa only [Category.assoc] using h

/-- The bundled continuous map on complex points induced by a scheme morphism. -/
def mapContinuous (f : X ⟶ Y) : C(schemeComplexPoints X, schemeComplexPoints Y) :=
  ⟨schemeComplexPoints.map f, continuous_map f⟩

end schemeComplexPoints

/-- On an actual affine scheme, the final topology is exactly the ordinary
evaluation topology on complex algebra characters. -/
def affineSchemePointHomeomorph (A : Type) [CommRing A] [Algebra ℂ A] :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints A ≃ₜ schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A) where
  toEquiv := affineSchemePointEquiv A
  continuous_toFun := by
    have h : Continuous (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A =>
        affineSchemePointEquiv A x ≫ 𝟙 (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)) :=
      schemeComplexPoints.continuous_affinePointMap (CommAlgCat.of ℂ A)
        (𝟙 (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A))
    exact h.congr fun x => Category.comp_id _
  continuous_invFun := by
    apply (schemeComplexPoints.continuous_iff_affineTests _).mpr
    intro B f
    obtain ⟨g, rfl⟩ := (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B).surjective f
    change Continuous (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B => (affineSchemePointEquiv A).symm
      (affineSchemePointEquiv B x ≫ Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B g))
    simp only [← affineSchemePointEquiv_comap, Equiv.symm_apply_apply]
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap g).continuous

/-- Complex points with the affine-test topology form a covariant topological functor. -/
def schemeComplexPointsFunctor : Over Foundations.Scheme.ProjectiveSpace.complexBase ⥤ TopCat where
  obj X := TopCat.of (schemeComplexPoints X)
  map f := TopCat.ofHom (schemeComplexPoints.mapContinuous f)
  map_id X := by
    apply TopCat.ext
    intro x
    exact schemeComplexPoints.map_id x
  map_comp f g := by
    apply TopCat.ext
    intro x
    exact schemeComplexPoints.map_comp f g x

end AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

namespace AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints

/-!
# Homeomorphisms of genuine complex scheme points

An isomorphism of schemes over the complex base induces a homeomorphism of
their actual complex-valued point spaces with the affine-test topology.
-/

open _root_.CategoryTheory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- An actual scheme isomorphism gives a homeomorphism of complex-point spaces. -/
def isoHomeomorph (e : X ≅ Y) : schemeComplexPoints X ≃ₜ schemeComplexPoints Y where
  toFun := schemeComplexPoints.map e.hom
  invFun := schemeComplexPoints.map e.inv
  left_inv x := by
    change (x ≫ e.hom) ≫ e.inv = x
    simp only [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv y := by
    change (y ≫ e.inv) ≫ e.hom = y
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  continuous_toFun := continuous_map e.hom
  continuous_invFun := continuous_map e.inv

@[simp]
theorem isoHomeomorph_apply (e : X ≅ Y) (x : schemeComplexPoints X) :
    isoHomeomorph e x = x ≫ e.hom := rfl

@[simp]
theorem isoHomeomorph_symm_apply (e : X ≅ Y) (y : schemeComplexPoints Y) :
    (isoHomeomorph e).symm y = y ≫ e.inv := rfl

end AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints

end

end OAI
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints -/

/-! # Localization Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic

noncomputable section

/-!
# Field-valued points of a principal localization

Restriction along `A → A[g⁻¹]` identifies field-valued characters of the
localization with characters of `A` at which `g` does not vanish. The inverse
is the universal-property extension, with an explicit fractional evaluation
formula and compatibility with algebra morphisms.
-/

universe u v w

variable {K : Type u} {S : Type v}
variable [Field K] [CommRing S] [Algebra K S]

/-- Extend a field-valued point to a principal localization when the inverted
element does not vanish at that point. -/
def localizePoint (x : S →ₐ[K] K) (g : S) (hg : x g ≠ 0) :
    Localization.Away g →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (S := Localization.Away g) (f := x) g
    (isUnit_iff_ne_zero.mpr hg)

@[simp]
theorem localizePoint_algebraMap (x : S →ₐ[K] K) (g : S) (hg : x g ≠ 0)
    (a : S) : localizePoint x g hg (algebraMap S (Localization.Away g) a) = x a := by
  simp [localizePoint]

/-- The localized character restricts to the original character. -/
@[simp]
theorem localizePoint_comp (x : S →ₐ[K] K) (g : S) (hg : x g ≠ 0) :
    (localizePoint x g hg).comp (Algebra.algHom K S (Localization.Away g)) = x := by
  ext a
  exact localizePoint_algebraMap x g hg a

/-- A character extension to this localization is unique. -/
theorem localizePoint_unique (x : S →ₐ[K] K) (g : S) (hg : x g ≠ 0)
    (y : Localization.Away g →ₐ[K] K)
    (hy : y.comp (Algebra.algHom K S (Localization.Away g)) = x) :
    y = localizePoint x g hg := by
  apply IsLocalization.algHom_ext (Submonoid.powers g)
  exact hy.trans (localizePoint_comp x g hg).symm

/-- Restricting a character from a principal localization gives a character
at which the inverted element is nonzero. -/
def localizationPointRestrict (g : S) (y : Localization.Away g →ₐ[K] K) :
    {x : S →ₐ[K] K // x g ≠ 0} :=
  ⟨y.comp (Algebra.algHom K S (Localization.Away g)), by
    exact isUnit_iff_ne_zero.mp
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map y)⟩

/-- Field-valued points of `A[g⁻¹]` are exactly points of `A` where `g ≠ 0`. -/
def localizationPointEquiv (g : S) :
    (Localization.Away g →ₐ[K] K) ≃ {x : S →ₐ[K] K // x g ≠ 0} where
  toFun := localizationPointRestrict g
  invFun x := localizePoint x.val g x.property
  left_inv y := by
    symm
    apply localizePoint_unique
    rfl
  right_inv x := by
    apply Subtype.ext
    exact localizePoint_comp x.val g x.property

@[simp]
theorem localizationPointEquiv_apply_val (g : S)
    (y : Localization.Away g →ₐ[K] K) :
    (localizationPointEquiv g y).val =
      y.comp (Algebra.algHom K S (Localization.Away g)) := rfl

@[simp]
theorem localizationPointEquiv_symm_apply (g : S)
    (x : {x : S →ₐ[K] K // x g ≠ 0}) :
    (localizationPointEquiv g).symm x = localizePoint x.val g x.property := rfl

/-- Evaluating an extended character is a quotient of two evaluations on the
original algebra. The numerator and exponent depend only on the localized element. -/
theorem localizePoint_eq_div_sec (x : S →ₐ[K] K) (g : S) (hg : x g ≠ 0)
    (z : Localization.Away g) :
    localizePoint x g hg z =
      x (IsLocalization.Away.sec g z).1 / (x g) ^ (IsLocalization.Away.sec g z).2 := by
  apply (eq_div_iff (pow_ne_zero _ hg)).mpr
  have h := congrArg (localizePoint x g hg)
    (IsLocalization.Away.sec_spec (S := Localization.Away g) g z)
  simpa only [map_mul, localizePoint_algebraMap, map_pow] using h

/-- The inverse point equivalence has an explicit fractional evaluation formula. -/
theorem localizationPointEquiv_symm_apply_eval (g : S)
    (x : {x : S →ₐ[K] K // x g ≠ 0}) (z : Localization.Away g) :
    (localizationPointEquiv g).symm x z =
      x.val (IsLocalization.Away.sec g z).1 /
        (x.val g) ^ (IsLocalization.Away.sec g z).2 :=
  localizePoint_eq_div_sec x.val g x.property z

variable {T : Type w} [CommRing T] [Algebra K T]

/-- The induced algebra map on principal localizations agrees with the
original algebra map on numerators. -/
@[simp]
theorem awayMap_algebraMap (f : S →ₐ[K] T) (g a : S) :
    Localization.awayMapₐ f g (algebraMap S (Localization.Away g) a) =
      algebraMap T (Localization.Away (f g)) (f a) := by
  simp [Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

/-- Extending a point to a principal localization commutes with pullback
along an algebra morphism. -/
theorem localizePoint_natural (f : S →ₐ[K] T) (g : S)
    (y : T →ₐ[K] K) (hy : y (f g) ≠ 0) :
    (localizePoint y (f g) hy).comp (Localization.awayMapₐ f g) =
      localizePoint (y.comp f) g hy := by
  apply localizePoint_unique
  ext a
  change localizePoint y (f g) hy
    (Localization.awayMapₐ f g (algebraMap S (Localization.Away g) a)) = y (f a)
  rw [awayMap_algebraMap, localizePoint_algebraMap]

/-- Restriction of localized points commutes with algebra morphisms. -/
theorem localizationPointEquiv_natural (f : S →ₐ[K] T) (g : S)
    (y : Localization.Away (f g) →ₐ[K] K) :
    (localizationPointEquiv g (y.comp (Localization.awayMapₐ f g))).val =
      ((localizationPointEquiv (f g) y).val).comp f := by
  ext a
  change y (Localization.awayMapₐ f g (algebraMap S (Localization.Away g) a)) =
    y (algebraMap T (Localization.Away (f g)) (f a))
  rw [awayMap_algebraMap]

/-- The complex specialization used for ordinary affine complex-point charts. -/
abbrev localizationComplexPointsEquiv {A : Type v} [CommRing A] [Algebra ℂ A]
    (g : A) :
    (Localization.Away g →ₐ[ℂ] ℂ) ≃ {x : A →ₐ[ℂ] ℂ // x g ≠ 0} :=
  localizationPointEquiv g

end

end OAI.AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalizationPointEvaluation -/

/-! # Localization Point Evaluation -/

namespace OAI.AlgebraicGeometry

/-!
# Continuity of fractions on principal affine open sets

The ambient topology is the ordinary evaluation topology on complex algebra
characters. Denominators are nonzero because the domain is the principal open
set on which the element being inverted does not vanish.
-/

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Fractions with a power denominator are continuous on the corresponding
principal open set of affine complex points. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_principalFraction (a g : A) (n : ℕ) :
    Continuous (fun x : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A // x g ≠ 0} =>
      x.1 a / (x.1 g) ^ n) := by
  exact ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a).comp continuous_subtype_val).div
    (((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval g).comp continuous_subtype_val).pow n)
    (fun x => pow_ne_zero n x.2)

/-- Every evaluation of the universal-property extension to a principal
localization varies continuously with the original complex point. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizePoint_eval (g : A) (z : Localization.Away g) :
    Continuous (fun x : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A // x g ≠ 0} =>
      Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x.1 g x.2 z) := by
  simpa only [Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_eq_div_sec] using
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_principalFraction (IsLocalization.Away.sec g z).1 g
      (IsLocalization.Away.sec g z).2

/-- Extension of complex characters to a principal localization is continuous
for the ordinary evaluation topologies. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizePoint (g : A) :
    Continuous (fun x : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A // x g ≠ 0} =>
      Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x.1 g x.2) := by
  apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).mpr
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizePoint_eval g

/-- The inverse algebraic localization-point equivalence is continuous. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizationPointEquiv_symm (g : A) :
    Continuous (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizationPointEquiv (K := ℂ) g).symm := by
  change Continuous (fun x : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A // x g ≠ 0} =>
    Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x.1 g x.2)
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizePoint g

end OAI.AlgebraicGeometry
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalizationPointEvaluation"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialZeroLocus -/

/-! # Polynomial Zero Locus -/

namespace OAI.AlgebraicGeometry

/-!
# Euclidean closedness of complex polynomial zero loci

The topology on `ι → ℂ` is its usual product topology. In particular, when `ι` is
finite this is the ordinary Euclidean topology on complex affine space, not the
Zariski topology. The ideal zero locus below is mathlib's `MvPolynomial.zeroLocus`.
-/

variable {ι : Type*}

/-- Every level set of a complex multivariable polynomial is Euclidean closed. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_levelSet (p : MvPolynomial ι ℂ) (z : ℂ) :
    IsClosed {x : ι → ℂ | MvPolynomial.eval x p = z} :=
  isClosed_eq p.continuous_eval continuous_const

/-- The zero set of a complex multivariable polynomial is Euclidean closed. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_zeroSet (p : MvPolynomial ι ℂ) :
    IsClosed {x : ι → ℂ | MvPolynomial.eval x p = 0} :=
  ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_levelSet p 0

/-- Arbitrary simultaneous polynomial equations define a Euclidean closed set. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_commonZeroSet (S : Set (MvPolynomial ι ℂ)) :
    IsClosed {x : ι → ℂ | ∀ p ∈ S, MvPolynomial.eval x p = 0} := by
  have hset : {x : ι → ℂ | ∀ p ∈ S, MvPolynomial.eval x p = 0} =
      ⋂ p ∈ S, {x : ι → ℂ | MvPolynomial.eval x p = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  exact isClosed_biInter fun p _ => ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_zeroSet p

/-- Mathlib's affine algebraic zero locus is also closed for the Euclidean topology. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_zeroLocus (I : Ideal (MvPolynomial ι ℂ)) :
    IsClosed (MvPolynomial.zeroLocus ℂ I) := by
  simpa only [MvPolynomial.zeroLocus, MvPolynomial.aeval_eq_eval, SetLike.mem_coe] using
    ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_commonZeroSet (I : Set (MvPolynomial ι ℂ))

/-- Replacing equations by their generated ideal gives the same Euclidean zero set. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.mvPolynomial_zeroLocus_span_eq (S : Set (MvPolynomial ι ℂ)) :
    MvPolynomial.zeroLocus ℂ (Ideal.span S) =
      {x : ι → ℂ | ∀ p ∈ S, MvPolynomial.eval x p = 0} := by
  simpa only [MvPolynomial.aeval_eq_eval] using MvPolynomial.zeroLocus_span (K := ℂ) S

/-- A polynomial's nonvanishing locus is open in ordinary complex affine space. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.isOpen_mvPolynomial_nonzeroSet (p : MvPolynomial ι ℂ) :
    IsOpen {x : ι → ℂ | MvPolynomial.eval x p ≠ 0} :=
  (ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_zeroSet p).isOpen_compl

/-- Continuous coordinate maps pull polynomial equations back to closed sets. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_commonZeroSet_preimage {X : Type*} [TopologicalSpace X]
    (f : X → ι → ℂ) (hf : Continuous f) (S : Set (MvPolynomial ι ℂ)) :
    IsClosed {x : X | ∀ p ∈ S, MvPolynomial.eval (f x) p = 0} :=
  (ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_commonZeroSet S).preimage hf

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The zero set of a regular function on affine complex points is closed. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_zeroSet (a : A) :
    IsClosed {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | x a = 0} :=
  isClosed_eq (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a) continuous_const

/-- Arbitrary regular-function equations define a closed set of affine complex points. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_commonZeroSet (S : Set A) :
    IsClosed {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | ∀ a ∈ S, x a = 0} := by
  have hset : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | ∀ a ∈ S, x a = 0} =
      ⋂ a ∈ S, {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | x a = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  exact isClosed_biInter fun a _ => Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_zeroSet a

/-- The points whose characters kill a fixed ideal form a closed set. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_zeroLocus (I : Ideal A) :
    IsClosed {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | I ≤ RingHom.ker x.toRingHom} := by
  have hset : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | I ≤ RingHom.ker x.toRingHom} =
      {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | ∀ a ∈ (I : Set A), x a = 0} := by
    ext x
    constructor
    · intro hx a ha
      exact hx ha
    · intro hx a ha
      exact hx a ha
  rw [hset]
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_commonZeroSet (I : Set A)

/-- Principal nonvanishing loci are open for the ordinary affine-point topology. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_nonzeroSet (a : A) :
    IsOpen {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | x a ≠ 0} :=
  (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_zeroSet a).isOpen_compl

end OAI.AlgebraicGeometry
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialZeroLocus"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.PrincipalOpen -/

/-! # Principal Open -/

namespace OAI.AlgebraicGeometry

/-!
# Principal open subsets of ordinary affine complex points

Nonvanishing loci of regular functions are open for the evaluation topology.
Their intersections and inverse images have the expected algebraic formulas.
Functions generating the unit ideal give an open cover, on which continuity
can be checked locally. These are genuine subsets of the complex-character
space, with its ordinary topology.
-/

universe u v w

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- The principal open subset of complex characters where a regular function is nonzero. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (a : A) : Set (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) := {x | x a ≠ 0}

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.mem_principalOpen (a : A) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    x ∈ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a ↔ x a ≠ 0 := Iff.rfl

theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_principalOpen (a : A) : IsOpen (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a) :=
  Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_nonzeroSet a

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_zero : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (0 : A) = ∅ := by
  ext x
  simp [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen]

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_one : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (1 : A) = Set.univ := by
  ext x
  simp [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen]

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_mul (a b : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (a * b) = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a ∩ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen b := by
  ext x
  simp [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen]

theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_pow (a : A) {n : ℕ} (hn : n ≠ 0) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (a ^ n) = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a := by
  ext x
  simp [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen, hn]

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_neg (a : A) : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (-a) = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a := by
  ext x
  simp [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen]

theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_add_subset (a b : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (a + b) ⊆ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a ∪ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen b := by
  intro x hx
  by_contra h
  have hz : x a = 0 ∧ x b = 0 := by
    simpa only [Set.mem_union, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.mem_principalOpen, not_or, not_not] using h
  exact hx (by simp [hz.1, hz.2])

/-- Pullback of a principal open is the principal open of the pulled-back function. -/
@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap_preimage_principalOpen {B : Type v} [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (a : A) :
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f) ⁻¹' Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (f a) := rfl

/-- Functions generating the unit ideal cannot all vanish at a complex point. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.exists_mem_principalOpen_of_span_eq_top {ι : Type v}
    (g : ι → A) (hg : Ideal.span (Set.range g) = ⊤) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ i, x ∈ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (g i) := by
  by_contra h
  have hz : ∀ i, x (g i) = 0 := by
    simpa only [not_exists, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.mem_principalOpen, not_not] using h
  have hle : Ideal.span (Set.range g) ≤ RingHom.ker x.toRingHom := by
    apply Ideal.span_le.mpr
    rintro a ⟨i, rfl⟩
    exact hz i
  have hone : (1 : A) ∈ RingHom.ker x.toRingHom := hle (by simp [hg])
  simp at hone

theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.iUnion_principalOpen_eq_univ {ι : Type v}
    (g : ι → A) (hg : Ideal.span (Set.range g) = ⊤) :
    (⋃ i, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (g i)) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.exists_mem_principalOpen_of_span_eq_top g hg x

/-- Continuity can be checked on a principal open cover from a unit-ideal generating family. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff_principalOpen_cover {ι : Type v} {X : Type w} [TopologicalSpace X]
    (g : ι → A) (hg : Ideal.span (Set.range g) = ⊤) (F : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A → X) :
    Continuous F ↔ ∀ i, Continuous (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (g i) => F x.1) := by
  constructor
  · intro h i
    exact h.comp continuous_subtype_val
  · intro h
    apply continuous_of_cover_nhds (s := fun i => Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (g i))
    · intro x
      obtain ⟨i, hi⟩ := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.exists_mem_principalOpen_of_span_eq_top g hg x
      exact ⟨i, (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_principalOpen (g i)).mem_nhds hi⟩
    · intro i
      exact continuousOn_iff_continuous_domRestrict.mpr (h i)

end OAI.AlgebraicGeometry
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.PrincipalOpen"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalizationPointTopology -/

/-! # Localization Point Topology -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Localization charts and gluing for ordinary affine complex points

Restriction from a principal localization is a homeomorphism onto the
ordinary open set where the inverted regular function is nonzero. These
charts identify localization at a product with the intersection of the two
corresponding chart images. A unit-ideal family of such charts detects
continuity, giving the topological gluing property for this affine atlas.
-/

universe u v w

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- The actual map of complex points induced by the localization algebra map. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction (g : A) :
    C(Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g), Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :=
  Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (Algebra.algHom ℂ A (Localization.Away g))

@[simp] theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction_apply (g : A)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)) (a : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g x a = x (algebraMap A (Localization.Away g) a) := rfl

/-- A principal localization is the ordinary open chart on which its denominator
is nonzero, with the genuine complex-point topology on both sides. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph (g : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g) ≃ₜ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen g where
  toEquiv := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizationPointEquiv (K := ℂ) g
  continuous_toFun := by
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g).continuous.subtype_mk _
  continuous_invFun := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizationPointEquiv_symm g

@[simp] theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph_val (g : A)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)) :
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g x).val = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g x := rfl

/-- The image of a localization chart is exactly its principal open set. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.range_localizationRestriction (g : A) :
    Set.range (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g) = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen g := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g y).property
  · intro hx
    refine ⟨(Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g).apply_symm_apply ⟨x, hx⟩)

/-- The algebraic localization map induces an open embedding of ordinary point spaces. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction (g : A) :
    Topology.IsOpenEmbedding (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g) := by
  change Topology.IsOpenEmbedding
    ((Subtype.val : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen g → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) ∘ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g)
  exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_principalOpen g).isOpenEmbedding_subtypeVal.comp
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g).isOpenEmbedding

/-- Localization at a product has precisely the overlap of the individual chart images. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localization_chart_overlap (g h : A) :
    Set.range (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction (g * h)) =
      Set.range (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g) ∩ Set.range (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction h) := by
  simp only [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.range_localizationRestriction, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_mul]

/-- A family generating the unit ideal is an open atlas of localization charts. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.iUnion_range_localizationRestriction {ι : Type v}
    (g : ι → A) (hg : Ideal.span (Set.range g) = ⊤) :
    (⋃ i, Set.range (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction (g i))) = Set.univ := by
  simp only [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.range_localizationRestriction]
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.iUnion_principalOpen_eq_univ g hg

/-- Continuity can be checked on the actual principal-localization point spaces.
This is the gluing property of the ordinary affine localization atlas. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff_localizationCover {ι : Type v} {X : Type w} [TopologicalSpace X]
    (g : ι → A) (hg : Ideal.span (Set.range g) = ⊤)
    (F : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A → X) :
    Continuous F ↔ ∀ i, Continuous (F ∘ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction (g i)) := by
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff_principalOpen_cover g hg F]
  apply forall_congr'
  intro i
  change Continuous (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (g i) => F x.val) ↔
    Continuous ((fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (g i) => F x.val) ∘ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph (g i))
  exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph (g i)).comp_continuous_iff'.symm

end

end OAI.AlgebraicGeometry
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalizationPointTopology"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointSpectrum -/

/-! # Affine Point Spectrum -/

namespace OAI.AlgebraicGeometry

/-!
# Affine complex characters and their underlying spectrum points

An ordinary complex point of an affine algebra determines its prime kernel.
This map is continuous to the Zariski spectrum, and inverse images of scheme
basic opens are precisely the ordinary principal open subsets. The topology on
the source remains the evaluation topology on complex characters.
-/

universe u v

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- The underlying prime-spectrum point of a complex algebra character. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) : PrimeSpectrum A :=
  ⟨RingHom.ker x.toRingHom, RingHom.ker_isPrime x.toRingHom⟩

/-- A complex-algebra character is surjective, so its prime kernel is maximal. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_isMaximal (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum x).asIdeal.IsMaximal := by
  change (RingHom.ker x.toRingHom).IsMaximal
  apply RingHom.ker_isMaximal_of_surjective x.toRingHom
  intro z
  refine ⟨algebraMap ℂ A z, ?_⟩
  simp

/-- The prime kernel is the usual spectrum image of the unique point of `Spec ℂ`. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_eq_comap_bot (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum x = PrimeSpectrum.comap x.toRingHom
      (⟨⊥, by infer_instance⟩ : PrimeSpectrum ℂ) := rfl

/-- Scheme basic opens pull back to nonvanishing loci in the ordinary point topology. -/
@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_preimage_basicOpen (a : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) =
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a := by
  ext x
  change (a ∉ RingHom.ker x.toRingHom) ↔ x.toRingHom a ≠ 0
  exact not_congr (RingHom.mem_ker (f := x.toRingHom) (r := a))

/-- Scheme closed loci pull back to the same equations on complex characters. -/
@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_preimage_zeroLocus (S : Set A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum ⁻¹' PrimeSpectrum.zeroLocus S =
      {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | ∀ a ∈ S, x a = 0} := by
  ext x
  change (S ⊆ (RingHom.ker x.toRingHom : Set A)) ↔ ∀ a ∈ S, x a = 0
  constructor
  · intro hx a ha
    exact hx ha
  · intro hx a ha
    exact hx a ha

/-- The map from ordinary affine complex points to the Zariski spectrum is continuous. -/
@[continuity, fun_prop]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_toPrimeSpectrum :
    Continuous (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (A := A)) := by
  rw [continuous_iff_isClosed]
  intro S hS
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus S).mp hS
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_preimage_zeroLocus]
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_commonZeroSet I

/-- Underlying spectrum points commute with pullback of complex characters. -/
@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_comap {B : Type v} [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) = PrimeSpectrum.comap f.toRingHom (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum x) := by
  ext a
  rfl

end OAI.AlgebraicGeometry
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointSpectrum"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointUnderlying -/

/-! # Scheme Point Underlying -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Underlying points of complex-valued scheme points

This is the genuine map obtained by evaluating a morphism from `Spec ℂ` at its
unique point. It is continuous from the ordinary affine-test topology on complex
points to the Zariski topology of the scheme. Its affine formula is the prime
kernel of the corresponding complex algebra character.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The unique point of the complex base scheme, represented by its zero prime. -/
def SchemePointHomeomorphs.schemeComplexPoints.basePoint : Foundations.Scheme.ProjectiveSpace.complexBase := (⊥ : PrimeSpectrum ℂ)

/-- The underlying scheme point of a morphism from the complex point. -/
def SchemePointHomeomorphs.schemeComplexPoints.underlying (x : SchemePointHomeomorphs.schemeComplexPoints X) : X.left := x.left SchemePointHomeomorphs.schemeComplexPoints.basePoint

/-- Taking the underlying point commutes with a morphism of complex schemes. -/
@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.underlying_map (f : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    SchemePointHomeomorphs.schemeComplexPoints.underlying (SchemePointHomeomorphs.schemeComplexPoints.map f x) = f.left (SchemePointHomeomorphs.schemeComplexPoints.underlying x) := rfl

/-- On an affine test, the underlying point is the image of the character's prime kernel. -/
@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.underlying_affinePointMap (A : CommAlgCat ℂ)
    (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    SchemePointHomeomorphs.schemeComplexPoints.underlying (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f x) = f.left (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (A := A) x) := by
  change ((Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A x).left ≫ f.left) SchemePointHomeomorphs.schemeComplexPoints.basePoint = _
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
  change f.left (PrimeSpectrum.comap x.toRingHom (⊥ : PrimeSpectrum ℂ)) = _
  rfl

/-- The actual underlying-point map is continuous for the affine-test topology. -/
@[continuity, fun_prop]
theorem SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying : Continuous (SchemePointHomeomorphs.schemeComplexPoints.underlying (X := X)) := by
  apply (SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_affineTests _).mpr
  intro A f
  simp only [SchemePointHomeomorphs.schemeComplexPoints.underlying_affinePointMap]
  exact f.left.continuous.comp Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_toPrimeSpectrum

/-- Scheme open sets give open sets of ordinary complex-valued points. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isOpen_preimage_underlying (U : Set X.left) (hU : IsOpen U) :
    IsOpen (SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' U) :=
  hU.preimage SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointUnderlying"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenLifts -/

/-! # Affine Open Lifts -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Local affine factorizations through open immersions

A map from an affine complex scheme whose selected point lies in an open
subscheme factors through that open subscheme on a principal neighborhood of
the selected point. The factorization is constructed in the category over
`Spec ℂ`, using the actual spectrum localization map and open-immersion lift.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- A selected prime has a principal neighborhood on which the affine map
lifts through the given open immersion, compatibly with the complex base. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.exists_localizationLift_of_prime_mem
    {U X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : U ⟶ X) [IsOpenImmersion i.left]
    (A : CommAlgCat ℂ) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (p : PrimeSpectrum A)
    (hp : g.left p ∈ Set.range i.left) :
    ∃ a : A, a ∉ p.asIdeal ∧
      ∃ l : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Localization.Away a) ⟶ U,
        l ≫ i =
          Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
            (Algebra.algHom ℂ A (Localization.Away a)) ≫ g := by
  have hopen : IsOpen (g.left ⁻¹' Set.range i.left) :=
    (IsOpenImmersion.isOpen_range i.left).preimage g.left.continuous
  obtain ⟨V, ⟨a, rfl⟩, ha, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open
      hp hopen
  let j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Localization.Away a) ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A :=
    Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
      (Algebra.algHom ℂ A (Localization.Away a))
  have hfactor : Set.range (j ≫ g).left ⊆ Set.range i.left := by
    rintro y ⟨q, rfl⟩
    change g.left (PrimeSpectrum.comap (algebraMap A (Localization.Away a)) q) ∈
      Set.range i.left
    apply hsub
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away a) a).le
      (Set.mem_range_self q)
  refine ⟨a, ha, Foundations.Scheme.OpenImmersionPoints.openImmersion_relativeLift i (j ≫ g) hfactor, ?_⟩
  exact Foundations.Scheme.OpenImmersionPoints.openImmersion_relativeLift_fac i (j ≫ g) hfactor

/-- A complex point mapping into an open subscheme has an ordinary principal
neighborhood whose entire affine localization map lifts to that open subscheme. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.exists_localizationLift
    {U X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : U ⟶ X) [IsOpenImmersion i.left]
    (A : CommAlgCat ℂ) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
    (hx : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A g x ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.map i)) :
    ∃ a : A, x a ≠ 0 ∧
      ∃ l : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Localization.Away a) ⟶ U,
        l ≫ i =
          Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
            (Algebra.algHom ℂ A (Localization.Away a)) ≫ g := by
  have hp : g.left (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (A := A) x) ∈ Set.range i.left := by
    obtain ⟨y, hy⟩ := hx
    refine ⟨SchemePointHomeomorphs.schemeComplexPoints.underlying y, ?_⟩
    simpa only [SchemePointHomeomorphs.schemeComplexPoints.underlying_map, SchemePointHomeomorphs.schemeComplexPoints.underlying_affinePointMap] using congrArg SchemePointHomeomorphs.schemeComplexPoints.underlying hy
  obtain ⟨a, ha, l, hl⟩ :=
    SchemePointHomeomorphs.schemeComplexPoints.exists_localizationLift_of_prime_mem i A g (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (A := A) x) hp
  refine ⟨a, ?_, l, hl⟩
  exact ha

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenLifts"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion -/

/-! # Open Immersion -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion.SchemeComplexPoints

noncomputable section

/-!
# Open immersions on ordinary complex points

The carrier is the native type of relative scheme morphisms from `Spec ℂ`.
The point topology is the final topology of actual affine tests. Principal
localization neighborhoods provide the local lifts used below.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {U X : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- Local algebraic lifts through principal localizations imply openness of the
induced map on native complex points. -/
private theorem isOpenMap_of_localizationLifts
    (i : U ⟶ X) [IsOpenImmersion i.left]
    (hloc : ∀ (A : CommAlgCat ℂ) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
      (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A), SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A g x ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.map i) →
      ∃ a : A, x a ≠ 0 ∧ ∃ l : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Localization.Away a) ⟶ U,
        l ≫ i = Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
          (Algebra.algHom ℂ A (Localization.Away a)) ≫ g) :
    IsOpenMap (SchemePointHomeomorphs.schemeComplexPoints.map i) := by
  intro S hS
  apply (SchemePointHomeomorphs.schemeComplexPoints.isOpen_iff_affineTests _).mpr
  intro A g
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨y, hy, heq⟩ := hx
  obtain ⟨a, ha, l, hl⟩ := hloc A g x ⟨y, heq⟩
  let F : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a → SchemePointHomeomorphs.schemeComplexPoints U :=
    fun z => SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (Localization.Away a)) l
      ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph a).symm z)
  have hF : Continuous F :=
    (SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap (CommAlgCat.of ℂ (Localization.Away a)) l).comp
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph a).symm.continuous
  have hcomm (z : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a) :
      SchemePointHomeomorphs.schemeComplexPoints.map i (F z) = SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A g z.val := by
    dsimp only [F]
    rw [← SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp, hl, SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap]
    have hz : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction a
        ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph a).symm z) = z.val := by
      rw [← Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph_val,
        Homeomorph.apply_symm_apply]
    exact congrArg (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A g) hz
  let x' : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a := ⟨x, ha⟩
  have hx' : F x' ∈ S := by
    have hxy : F x' = y :=
      Foundations.Scheme.OpenImmersionPoints.openImmersion_complexPointMap_injective i ((hcomm x').trans heq.symm)
    rw [hxy]
    exact hy
  have hopen : IsOpen ((Subtype.val : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a →
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) '' (F ⁻¹' S)) :=
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_principalOpen a).isOpenEmbedding_subtypeVal.isOpenMap _
      (hS.preimage hF)
  have hmem : x ∈ ((Subtype.val : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a →
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) '' (F ⁻¹' S)) := ⟨x', hx', rfl⟩
  apply Filter.mem_of_superset (hopen.mem_nhds hmem)
  rintro z ⟨w, hw, rfl⟩
  exact ⟨F w, hw, hcomm w⟩

/-- An actual open immersion of complex schemes induces an open map on their
native complex-valued points with the ordinary affine-test topology. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenMap_map_of_isOpenImmersion (i : U ⟶ X) [IsOpenImmersion i.left] :
    IsOpenMap (SchemePointHomeomorphs.schemeComplexPoints.map i) :=
  isOpenMap_of_localizationLifts i (SchemePointHomeomorphs.schemeComplexPoints.exists_localizationLift i)

/-- An actual open immersion induces an open embedding of ordinary complex
point spaces. Its local inverses come from genuine principal localizations. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (i : U ⟶ X) [IsOpenImmersion i.left] :
    Topology.IsOpenEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map i) :=
  .of_continuous_injective_isOpenMap (SchemePointHomeomorphs.schemeComplexPoints.continuous_map i)
    (Foundations.Scheme.OpenImmersionPoints.openImmersion_complexPointMap_injective i) (SchemePointHomeomorphs.schemeComplexPoints.isOpenMap_map_of_isOpenImmersion i)

/-- The image consists exactly of points whose underlying scheme point lies
in the open subscheme. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion (i : U ⟶ X) [IsOpenImmersion i.left] :
    Set.range (SchemePointHomeomorphs.schemeComplexPoints.map i) = SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range i.left := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨SchemePointHomeomorphs.schemeComplexPoints.underlying q, rfl⟩
  · intro hp
    have hsub : Set.range p.left ⊆ Set.range i.left := by
      rintro z ⟨t, rfl⟩
      have ht : t = SchemePointHomeomorphs.schemeComplexPoints.basePoint := by
        exact @Subsingleton.elim (PrimeSpectrum ℂ) inferInstance t SchemePointHomeomorphs.schemeComplexPoints.basePoint
      rw [ht]
      exact hp
    exact ⟨Foundations.Scheme.OpenImmersionPoints.openImmersion_relativeLift i p hsub, Foundations.Scheme.OpenImmersionPoints.openImmersion_relativeLift_fac i p hsub⟩

/-- Native points of an open subscheme are homeomorphic to the corresponding
ordinary open subset of the target point space. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.openImmersionPointHomeomorph (i : U ⟶ X) [IsOpenImmersion i.left] :
    SchemePointHomeomorphs.schemeComplexPoints U ≃ₜ (SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range i.left) :=
  (SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion i).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion i))

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.openImmersionPointHomeomorph_val (i : U ⟶ X) [IsOpenImmersion i.left]
    (p : SchemePointHomeomorphs.schemeComplexPoints U) :
    (SchemePointHomeomorphs.schemeComplexPoints.openImmersionPointHomeomorph i p).val = SchemePointHomeomorphs.schemeComplexPoints.map i p :=
  rfl

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion.SchemeComplexPoints
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints -/

/-! # Affine Scheme Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints

noncomputable section

/-!
# Complex points of an affine scheme and its global sections

The algebra on global sections and the isomorphism with their spectrum are the
canonical mathlib constructions over the given complex structure morphism.
-/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The global-section algebra induced by the specified complex structure map. -/
instance affineOverGammaAlgebra (X : Over ProjectiveSpace.complexBase) [IsAffine X.left] :
    Algebra ℂ Γ(X.left, ⊤) :=
  (Spec.preimage (X.left.isoSpec.inv ≫ X.hom)).hom.toAlgebra

/-- An affine complex scheme is isomorphic over `Spec ℂ` to the spectrum of its
actual global-section algebra. -/
def affineOverIso (X : Over ProjectiveSpace.complexBase) [IsAffine X.left] :
    X ≅ AffineComplexPoints.affineSchemeOver ℂ Γ(X.left, ⊤) :=
  Over.isoMk X.left.isoSpec (by
    change X.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.left, ⊤))) = X.hom
    change X.left.isoSpec.hom ≫ Spec.map (Spec.preimage (X.left.isoSpec.inv ≫ X.hom)) = X.hom
    simp)

@[simp]
theorem affineOverIso_hom_left (X : Over ProjectiveSpace.complexBase) [IsAffine X.left] :
    (affineOverIso X).hom.left = X.left.isoSpec.hom := rfl

@[simp]
theorem affineOverIso_inv_left (X : Over ProjectiveSpace.complexBase) [IsAffine X.left] :
    (affineOverIso X).inv.left = X.left.isoSpec.inv := rfl

/-- Native relative complex points of an affine scheme are exactly the
complex-algebra characters of its global sections. -/
def affineNativePointEquiv (X : Over ProjectiveSpace.complexBase) [IsAffine X.left] :
    (Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) ≃ AffineComplexPoints.affineComplexPoints Γ(X.left, ⊤) where
  toFun p := (AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤)).symm
    (p ≫ (affineOverIso X).hom)
  invFun x := AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤) x ≫ (affineOverIso X).inv
  left_inv p := by simp
  right_inv x := by simp

@[simp]
theorem affineNativePointEquiv_symm_left (X : Over ProjectiveSpace.complexBase) [IsAffine X.left]
    (x : AffineComplexPoints.affineComplexPoints Γ(X.left, ⊤)) :
    ((affineNativePointEquiv X).symm x).left =
      Spec.map (CommRingCat.ofHom x.toRingHom) ≫ X.left.isoSpec.inv := by
  change (AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤) x).left ≫ X.left.isoSpec.inv = _
  rw [AffineComplexPoints.affineComplexPointsOverEquiv_left]

/-- The character corresponding to a native point has the usual spectrum map. -/
theorem affineNativePointEquiv_spec (X : Over ProjectiveSpace.complexBase) [IsAffine X.left]
    (p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) :
    Spec.map (CommRingCat.ofHom (affineNativePointEquiv X p).toRingHom) =
      p.left ≫ X.left.isoSpec.hom := by
  change Spec.map (CommRingCat.ofHom
    ((AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤)).symm
      (p ≫ (affineOverIso X).hom)).toRingHom) = _
  rw [← AffineComplexPoints.affineComplexPointsOverEquiv_left, Equiv.apply_symm_apply]
  rfl

/-- Pullback on global sections, bundled as a complex-algebra homomorphism. -/
def affineAppTopAlgHom {X Y : Over ProjectiveSpace.complexBase} [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) : Γ(Y.left, ⊤) →ₐ[ℂ] Γ(X.left, ⊤) :=
  (AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(Y.left, ⊤) Γ(X.left, ⊤)).symm
    ((affineOverIso X).inv ≫ f ≫ (affineOverIso Y).hom)

/-- The coordinate homomorphism gives precisely the conjugated scheme morphism. -/
theorem affineAppTopAlgHom_over {X Y : Over ProjectiveSpace.complexBase}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(Y.left, ⊤) Γ(X.left, ⊤) (affineAppTopAlgHom f) =
      (affineOverIso X).inv ≫ f ≫ (affineOverIso Y).hom :=
  (AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(Y.left, ⊤) Γ(X.left, ⊤)).apply_symm_apply _

/-- This algebra homomorphism really is the existing pullback on global sections. -/
theorem affineAppTopAlgHom_toRingHom {X Y : Over ProjectiveSpace.complexBase}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    (affineAppTopAlgHom f).toRingHom = f.left.appTop.hom := by
  have h := congrArg Over.Hom.left (affineAppTopAlgHom_over f)
  have hs : Spec.map (CommRingCat.ofHom (affineAppTopAlgHom f).toRingHom) =
      Spec.map f.left.appTop := by
    calc
      _ = X.left.isoSpec.inv ≫ f.left ≫ Y.left.isoSpec.hom := by
        simpa only [AffineComplexPoints.affineAlgHomOverSpecEquiv_left, Over.comp_left,
          affineOverIso_inv_left, affineOverIso_hom_left] using h
      _ = _ := by
        rw [← Scheme.isoSpec_hom_naturality f.left]
        simp
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hs)

@[simp]
theorem affineAppTopAlgHom_apply {X Y : Over ProjectiveSpace.complexBase}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) (a : Γ(Y.left, ⊤)) :
    affineAppTopAlgHom f a = f.left.appTop a :=
  congrArg (fun h : Γ(Y.left, ⊤) →+* Γ(X.left, ⊤) => h a)
    (affineAppTopAlgHom_toRingHom f)

/-- Evaluating the character of a scheme point is pullback of the section,
followed by the canonical identification of sections of `Spec ℂ` with `ℂ`. -/
theorem affineNativePointEquiv_toRingHom (X : Over ProjectiveSpace.complexBase) [IsAffine X.left]
    (p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) :
    (affineNativePointEquiv X p).toRingHom =
      (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom := by
  have hcat : (CommRingCat.ofHom (affineNativePointEquiv X p).toRingHom :
      Γ(X.left, ⊤) ⟶ CommRingCat.of ℂ) =
      p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := by
    apply (cancel_epi (Scheme.ΓSpecIso Γ(X.left, ⊤)).hom).mp
    rw [← Scheme.ΓSpecIso_naturality, affineNativePointEquiv_spec]
    simp only [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom,
      Scheme.toSpecΓ_appTop, Category.assoc]
  exact congrArg CommRingCat.Hom.hom hcat

theorem affineNativePointEquiv_eval (X : Over ProjectiveSpace.complexBase) [IsAffine X.left]
    (p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) (a : Γ(X.left, ⊤)) :
    affineNativePointEquiv X p a =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.left.appTop a) :=
  congrArg (fun h : Γ(X.left, ⊤) →+* ℂ => h a) (affineNativePointEquiv_toRingHom X p)

/-- The native-point/global-section correspondence is natural in affine
complex schemes. -/
theorem affineNativePointEquiv_natural {X Y : Over ProjectiveSpace.complexBase}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    (p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) :
    affineNativePointEquiv Y (p ≫ f) =
      (affineNativePointEquiv X p).comp (affineAppTopAlgHom f) := by
  ext a
  simp only [AlgHom.comp_apply, affineNativePointEquiv_eval,
    affineAppTopAlgHom_apply, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

end

end OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineSchemePointTopology -/

/-! # Affine Scheme Point Topology -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineSchemePointTopology

noncomputable section

/-!
# Ordinary point topology on arbitrary affine complex schemes

The canonical relative spectrum isomorphism identifies every affine scheme
over `Spec ℂ` with the spectrum of its actual global-section algebra. Combining
that isomorphism with the proved affine point topology gives a homeomorphism,
not just a set-theoretic equivalence. Its compatibility with arbitrary affine
scheme morphisms is proved below.
-/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The native points of any affine complex scheme have the ordinary topology
of complex-algebra characters of its actual global sections. -/
def affineNativePointHomeomorph (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] :
    SchemePointHomeomorphs.schemeComplexPoints X ≃ₜ Foundations.Scheme.AffineComplexPoints.affineComplexPoints Γ(X.left, ⊤) where
  toEquiv := Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X
  continuous_toFun := by
    change Continuous (fun p : SchemePointHomeomorphs.schemeComplexPoints X =>
      (SchemePointHomeomorphs.affineSchemePointEquiv Γ(X.left, ⊤)).symm (p ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom))
    exact (SchemePointHomeomorphs.affineSchemePointHomeomorph Γ(X.left, ⊤)).symm.continuous.comp
      (SchemePointHomeomorphs.schemeComplexPoints.continuous_map (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom)
  continuous_invFun := by
    change Continuous (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints Γ(X.left, ⊤) =>
      SchemePointHomeomorphs.affineSchemePointEquiv Γ(X.left, ⊤) x ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv)
    exact (SchemePointHomeomorphs.schemeComplexPoints.continuous_map (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv).comp
      (SchemePointHomeomorphs.affineSchemePointHomeomorph Γ(X.left, ⊤)).continuous

@[simp]
theorem affineNativePointHomeomorph_apply (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    (p : SchemePointHomeomorphs.schemeComplexPoints X) :
    affineNativePointHomeomorph X p = Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p := rfl

@[simp]
theorem affineNativePointHomeomorph_symm_apply (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints Γ(X.left, ⊤)) :
    (affineNativePointHomeomorph X).symm x =
      SchemePointHomeomorphs.affineSchemePointEquiv Γ(X.left, ⊤) x ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv := rfl

/-- Applying the affine point correspondence recovers composition with the
canonical spectrum isomorphism. -/
@[simp]
theorem affineSchemePointEquiv_affineNativePointHomeomorph
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] (p : SchemePointHomeomorphs.schemeComplexPoints X) :
    SchemePointHomeomorphs.affineSchemePointEquiv Γ(X.left, ⊤) (affineNativePointHomeomorph X p) =
      p ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom :=
  (SchemePointHomeomorphs.affineSchemePointEquiv Γ(X.left, ⊤)).apply_symm_apply _

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left] [IsAffine Y.left]

/-- The algebra homomorphism corresponding to an affine scheme morphism in
the canonical global-section presentations. -/
abbrev affineCoordinateHom (f : X ⟶ Y) : Γ(Y.left, ⊤) →ₐ[ℂ] Γ(X.left, ⊤) :=
  Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom f

@[simp]
theorem affineAlgHomOverSpecEquiv_affineCoordinateHom (f : X ⟶ Y) :
    Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(Y.left, ⊤) Γ(X.left, ⊤) (affineCoordinateHom f) =
      (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv ≫ f ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso Y).hom :=
  Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom_over f

/-- The coordinate homomorphism is the existing pullback on global sections. -/
theorem affineCoordinateHom_toRingHom (f : X ⟶ Y) :
    (affineCoordinateHom f).toRingHom = f.left.appTop.hom :=
  Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom_toRingHom f

/-- Under the canonical affine homeomorphisms, every actual affine scheme map
acts by precomposition with its corresponding complex-algebra homomorphism. -/
theorem affineNativePointHomeomorph_map (f : X ⟶ Y) (p : SchemePointHomeomorphs.schemeComplexPoints X) :
    affineNativePointHomeomorph Y (SchemePointHomeomorphs.schemeComplexPoints.map f p) =
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (affineCoordinateHom f) (affineNativePointHomeomorph X p) :=
  Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_natural f p

/-- The same naturality formula as an equality of point maps. -/
theorem schemePointMap_eq_affineCoordinates (f : X ⟶ Y) :
    SchemePointHomeomorphs.schemeComplexPoints.map f =
      (affineNativePointHomeomorph Y).symm ∘
        Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (affineCoordinateHom f) ∘
          affineNativePointHomeomorph X := by
  funext p
  apply (affineNativePointHomeomorph Y).injective
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply,
    affineNativePointHomeomorph_map]

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineSchemePointTopology
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineSchemePointTopology"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.AffineClosedImmersion -/

/-! # Affine Closed Immersion -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.AffineClosedImmersion

noncomputable section

/-!
# Affine equations of a closed immersion

A closed immersion into an affine scheme has affine source. Its coordinate ring
is the quotient of the target coordinate ring by the actual kernel ideal.
The resulting spectrum isomorphism is compatible with the original immersion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v

variable {X Y : Scheme.{u}} [IsAffine Y] (i : X ⟶ Y) [IsClosedImmersion i]

include i in
/-- A closed subscheme of an affine scheme is affine. -/
theorem affineClosedImmersion_source_isAffine : IsAffine X :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine i).1

/-- The coordinate map of a closed immersion into an affine scheme is surjective. -/
theorem affineClosedImmersion_appTop_surjective : Function.Surjective i.appTop :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine i).2

/-- The actual ideal of equations in the target's coordinate ring. -/
abbrev affineClosedImmersionIdeal : Ideal Γ(Y, ⊤) := RingHom.ker i.appTop.hom

/-- The source coordinate ring is the quotient by the actual ideal of equations. -/
def affineClosedImmersionCoordinateEquiv :
    (Γ(Y, ⊤) ⧸ affineClosedImmersionIdeal i) ≃+* Γ(X, ⊤) :=
  RingHom.quotientKerEquivOfSurjective (affineClosedImmersion_appTop_surjective i)

@[simp]
theorem affineClosedImmersionCoordinateEquiv_mk (a : Γ(Y, ⊤)) :
    affineClosedImmersionCoordinateEquiv i
      (Ideal.Quotient.mk (affineClosedImmersionIdeal i) a) = i.appTop a :=
  RingHom.quotientKerEquivOfSurjective_apply_mk _ a

/-- The affine closed subscheme is the actual spectrum of its quotient ring. -/
def affineClosedImmersionIsoQuotient :
    X ≅ Spec (.of (Γ(Y, ⊤) ⧸ affineClosedImmersionIdeal i)) := by
  letI : IsAffine X := affineClosedImmersion_source_isAffine i
  exact X.isoSpec ≪≫ Scheme.Spec.mapIso
    (affineClosedImmersionCoordinateEquiv i).toCommRingCatIso.op

/-- The quotient ring map agrees with the original map on global sections. -/
theorem affineClosedImmersion_quotient_comp :
    CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionIdeal i)) ≫
      (affineClosedImmersionCoordinateEquiv i).toCommRingCatIso.hom = i.appTop := by
  ext a
  exact affineClosedImmersionCoordinateEquiv_mk i a

/-- The spectrum isomorphism carries the original immersion to the quotient map. -/
theorem affineClosedImmersionIsoQuotient_over :
    (affineClosedImmersionIsoQuotient i).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionIdeal i))) ≫
      Y.isoSpec.inv = i := by
  let _ : IsAffine X := affineClosedImmersion_source_isAffine i
  simp only [affineClosedImmersionIsoQuotient, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
  rw [← Category.assoc (Spec.map _) (Spec.map _) Y.isoSpec.inv,
    ← Spec.map_comp, affineClosedImmersion_quotient_comp]
  rw [Scheme.isoSpec_inv_naturality]
  simp

/-- A ring map whose spectrum morphism is a closed immersion is surjective. -/
theorem ringMap_surjective_of_spec_closedImmersion {R S : CommRingCat.{u}}
    (f : R ⟶ S) [IsClosedImmersion (Spec.map f)] : Function.Surjective f := by
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map f)).2
  have hcomp : (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop ≫
      (Scheme.ΓSpecIso S).hom = f := by simp
  rw [← hcomp]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom).2.comp hs).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2

/-- For algebra maps, the coordinate quotient identification respects the base
algebra structure, in particular for complex algebras. -/
def algebraQuotientEquivOfSpecClosedImmersion {K : Type v} [CommRing K]
    {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))] :
    (A ⧸ RingHom.ker f) ≃ₐ[K] B :=
  Ideal.quotientKerAlgEquivOfSurjective
    (ringMap_surjective_of_spec_closedImmersion (CommRingCat.ofHom f.toRingHom))

@[simp]
theorem algebraQuotientEquivOfSpecClosedImmersion_mk {K : Type v} [CommRing K]
    {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))] (a : A) :
    algebraQuotientEquivOfSpecClosedImmersion f (Ideal.Quotient.mk (RingHom.ker f) a) =
      f a := rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme.AffineClosedImmersion
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.AffineClosedImmersion"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.QuotientComplexPoints -/

/-! # Quotient Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.QuotientComplexPoints

/-!
# Points of an affine quotient

Complex points of `A ⧸ I` are exactly complex-algebra characters of `A` vanishing
on `I`. This is the actual algebraic universal property of the quotient, with
compatibility with the scheme morphism induced by the quotient map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- The zero locus of an ideal among actual complex-algebra characters. -/
def affineIdealZeroLocus (I : Ideal A) : Set (AffineComplexPoints.affineComplexPoints A) :=
  {x | ∀ a : A, a ∈ I → x a = 0}

/-- Vanishing on an ideal is equivalently containment of that ideal in the character's kernel. -/
theorem mem_affineIdealZeroLocus_iff_le_ker (I : Ideal A) (x : AffineComplexPoints.affineComplexPoints A) :
    x ∈ affineIdealZeroLocus I ↔ I ≤ RingHom.ker x.toRingHom := Iff.rfl

/-- Complex points of a quotient are exactly characters vanishing on the defining ideal. -/
def quotientComplexPointsEquiv (I : Ideal A) :
    AffineComplexPoints.affineComplexPoints (A ⧸ I) ≃ affineIdealZeroLocus I where
  toFun x := ⟨x.comp (Ideal.Quotient.mkₐ ℂ I), by
    intro a ha
    change x (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]⟩
  invFun x := Ideal.Quotient.liftₐ I x.val x.property
  left_inv x := by
    apply Ideal.Quotient.algHom_ext ℂ
    exact Ideal.Quotient.liftₐ_comp I _ _
  right_inv x := by
    apply Subtype.ext
    exact Ideal.Quotient.liftₐ_comp I _ _

/-- Restricting a quotient point is precomposition by the canonical algebra quotient map. -/
@[simp] theorem quotientComplexPointsEquiv_val (I : Ideal A)
    (x : AffineComplexPoints.affineComplexPoints (A ⧸ I)) :
    (quotientComplexPointsEquiv I x).val = x.comp (Ideal.Quotient.mkₐ ℂ I) := rfl

/-- The inverse is the standard quotient algebra lift. -/
@[simp] theorem quotientComplexPointsEquiv_symm (I : Ideal A)
    (x : affineIdealZeroLocus I) :
    (quotientComplexPointsEquiv I).symm x =
      Ideal.Quotient.liftₐ I x.val x.property := rfl

/-- Quotient points are determined by the resulting characters on the original algebra. -/
theorem quotientComplexPoints_restrict_injective (I : Ideal A) :
    Function.Injective (fun x : AffineComplexPoints.affineComplexPoints (A ⧸ I) =>
      x.comp (Ideal.Quotient.mkₐ ℂ I)) := by
  intro x y h
  apply (quotientComplexPointsEquiv I).injective
  exact Subtype.ext h

/-- The image of restriction is exactly the ideal's zero locus. -/
theorem range_quotientComplexPoints_restrict (I : Ideal A) :
    Set.range (fun x : AffineComplexPoints.affineComplexPoints (A ⧸ I) =>
      x.comp (Ideal.Quotient.mkₐ ℂ I)) = affineIdealZeroLocus I := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (quotientComplexPointsEquiv I y).property
  · intro hx
    refine ⟨(quotientComplexPointsEquiv I).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((quotientComplexPointsEquiv I).apply_symm_apply ⟨x, hx⟩)

/-- On the scheme side, restriction is composition with `Spec` of the quotient map. -/
theorem quotientComplexPointsEquiv_specMap {A : Type} [CommRing A] [Algebra ℂ A]
    (I : Ideal A) (x : AffineComplexPoints.affineComplexPoints (A ⧸ I)) :
    Spec.map (CommRingCat.ofHom (quotientComplexPointsEquiv I x).val.toRingHom) =
      Spec.map (CommRingCat.ofHom x.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rw [← Spec.map_comp]
  rfl

end OAI.AlgebraicGeometry.Foundations.Scheme.QuotientComplexPoints
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.QuotientComplexPoints"

@[expose] public section ComponentSource_18
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.QuotientPointTopology -/

/-! # Quotient Point Topology -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.QuotientPointTopology

/-!
# Quotient algebras and closed spaces of complex points

The algebraic correspondence between characters of `A ⧸ I` and characters of A
vanishing on I is a homeomorphism for their ordinary evaluation topologies.
Consequently the point map of the quotient is a closed topological embedding.
-/

universe u

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- An ideal's zero locus is closed in the ordinary topology on affine points. -/
theorem isClosed_affineIdealZeroLocus (I : Ideal A) :
    IsClosed (Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus I) :=
  Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_commonZeroSet (I : Set A)

/-- The ordinary complex points of a quotient are its closed ideal zero locus. -/
def quotientComplexPointsHomeomorph (I : Ideal A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⧸ I) ≃ₜ Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus I where
  toEquiv := Foundations.Scheme.QuotientComplexPoints.quotientComplexPointsEquiv I
  continuous_toFun :=
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (Ideal.Quotient.mkₐ ℂ I)).continuous.subtype_mk _
  continuous_invFun := by
    apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).mpr
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    change Continuous (fun x : Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus I => x.val a)
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a).comp continuous_subtype_val

/-- The homeomorphism uses the original algebraic quotient-point correspondence. -/
@[simp]
theorem quotientComplexPointsHomeomorph_toEquiv (I : Ideal A) :
    (quotientComplexPointsHomeomorph I).toEquiv = Foundations.Scheme.QuotientComplexPoints.quotientComplexPointsEquiv I := rfl

/-- Its forward map is restriction along the quotient algebra homomorphism. -/
@[simp]
theorem quotientComplexPointsHomeomorph_val (I : Ideal A)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⧸ I)) :
    (quotientComplexPointsHomeomorph I x).val =
      x.comp (Ideal.Quotient.mkₐ ℂ I) := rfl

/-- Its inverse evaluates a quotient class using any representative. -/
@[simp]
theorem quotientComplexPointsHomeomorph_symm_apply_mk (I : Ideal A)
    (x : Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus I) (a : A) :
    (quotientComplexPointsHomeomorph I).symm x (Ideal.Quotient.mk I a) = x.val a := rfl

/-- The ordinary point map of an algebra quotient is a closed topological embedding. -/
theorem isClosedEmbedding_quotientComplexPoints_restrict (I : Ideal A) :
    Topology.IsClosedEmbedding (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⧸ I) =>
      x.comp (Ideal.Quotient.mkₐ ℂ I)) :=
  (isClosed_affineIdealZeroLocus I).isClosedEmbedding_subtypeVal.comp
    (quotientComplexPointsHomeomorph I).isClosedEmbedding

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.QuotientPointTopology
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.QuotientPointTopology"

@[expose] public section ComponentSource_19
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.ClosedImmersionPointTopology -/

/-! # Closed Immersion Point Topology -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Ordinary topology of affine closed immersions

A surjective complex algebra map induces a closed embedding of its actual
complex-point spaces. The image is exactly the common zero locus of its kernel.
Mathlib's characterization of affine scheme closed immersions then applies
this result to the actual spectrum map, rather than an assumed presentation.
-/

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

/-- A surjective algebra map identifies target points with the zero locus of its kernel. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph (f : A →ₐ[ℂ] B) (hf : Function.Surjective f) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints B ≃ₜ Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus (RingHom.ker f) :=
  (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comapHomeomorph (Ideal.quotientKerAlgEquivOfSurjective hf)).trans
    (ComplexPoints.Analytic.QuotientPointTopology.quotientComplexPointsHomeomorph (RingHom.ker f))

/-- The homeomorphism is the actual precomposition map on algebra characters. -/
@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph_val (f : A →ₐ[ℂ] B) (hf : Function.Surjective f)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf x).val = x.comp f := by
  ext a
  rfl

/-- The image of a surjective algebra map on complex points is its kernel zero locus. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.range_comap_of_surjective (f : A →ₐ[ℂ] B) (hf : Function.Surjective f) :
    Set.range (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f) = Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus (RingHom.ker f) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change y.comp f ∈ Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus (RingHom.ker f)
    rw [← Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph_val f hf y]
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf y).property
  · intro hx
    refine ⟨(Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf).symm ⟨x, hx⟩, ?_⟩
    change ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf).symm ⟨x, hx⟩).comp f = x
    rw [← Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph_val f hf]
    exact congrArg Subtype.val ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf).apply_symm_apply ⟨x, hx⟩)

/-- A surjective algebra map induces a closed embedding for ordinary complex-point topologies. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_surjective (f : A →ₐ[ℂ] B)
    (hf : Function.Surjective f) : Topology.IsClosedEmbedding (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f) := by
  have heq : (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B => (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf x).val) =
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f := by
    funext x
    exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph_val f hf x
  rw [← heq]
  exact (ComplexPoints.Analytic.QuotientPointTopology.isClosed_affineIdealZeroLocus (RingHom.ker f)).isClosedEmbedding_subtypeVal.comp
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf).isClosedEmbedding

/-- A genuine affine spectrum closed immersion induces an ordinary closed point embedding. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_spec_closedImmersion
    {A B : Type u} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B)
    [AlgebraicGeometry.IsClosedImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom))] :
    Topology.IsClosedEmbedding (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f) :=
  Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_surjective f
    (Foundations.Scheme.AffineClosedImmersion.ringMap_surjective_of_spec_closedImmersion (CommRingCat.ofHom f.toRingHom))

end

end OAI.AlgebraicGeometry
end ComponentSource_19

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.ClosedImmersionPointTopology"

@[expose] public section ComponentSource_20
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointClosedMap -/

/-! # Scheme Point Closed Map -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

section

/-!
# Actual pullbacks and images of complex scheme points

The ordinary scheme pullback is equipped with its complex structure map. Its
universal property gives the precise point-set identity needed to test images
under a morphism against affine test spaces.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y Z T : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The ordinary scheme fiber product, regarded as a scheme over the same complex base. -/
def SchemePointHomeomorphs.schemeComplexPoints.pullbackOver (f : X ⟶ Z) (g : Y ⟶ Z) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (pullback.snd f.left g.left ≫ Y.hom)

/-- The left projection of the actual fiber product over the complex base. -/
def SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft (f : X ⟶ Z) (g : Y ⟶ Z) : SchemePointHomeomorphs.schemeComplexPoints.pullbackOver f g ⟶ X :=
  Over.homMk (pullback.fst f.left g.left) (by
    change pullback.fst f.left g.left ≫ X.hom = pullback.snd f.left g.left ≫ Y.hom
    calc
      _ = (pullback.fst f.left g.left ≫ f.left) ≫ Z.hom := by
        rw [Category.assoc, Over.w f]
      _ = (pullback.snd f.left g.left ≫ g.left) ≫ Z.hom := by
        rw [pullback.condition]
      _ = _ := by rw [Category.assoc, Over.w g])

/-- The right projection of the actual fiber product over the complex base. -/
def SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight (f : X ⟶ Z) (g : Y ⟶ Z) : SchemePointHomeomorphs.schemeComplexPoints.pullbackOver f g ⟶ Y :=
  Over.homMk (pullback.snd f.left g.left) (by rfl)

/-- The two projections satisfy the actual scheme pullback relation. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.pullback_condition (f : X ⟶ Z) (g : Y ⟶ Z) :
    SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g ≫ f = SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g ≫ g := by
  apply Over.OverMorphism.ext
  exact pullback.condition

/-- Compatible morphisms over the complex base lift to the actual fiber product. -/
def SchemePointHomeomorphs.schemeComplexPoints.pullbackLift (f : X ⟶ Z) (g : Y ⟶ Z) (x : T ⟶ X) (y : T ⟶ Y)
    (h : x ≫ f = y ≫ g) : T ⟶ SchemePointHomeomorphs.schemeComplexPoints.pullbackOver f g :=
  Over.homMk
    (pullback.lift x.left y.left (congrArg (fun q : T ⟶ Z => q.left) h)) (by
      change (pullback.lift x.left y.left _) ≫
        (pullback.snd f.left g.left ≫ Y.hom) = T.hom
      rw [← Category.assoc, pullback.lift_snd, Over.w y])

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.pullbackLift_toLeft (f : X ⟶ Z) (g : Y ⟶ Z) (x : T ⟶ X) (y : T ⟶ Y)
    (h : x ≫ f = y ≫ g) :
    SchemePointHomeomorphs.schemeComplexPoints.pullbackLift f g x y h ≫ SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g = x := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.pullbackLift_toRight (f : X ⟶ Z) (g : Y ⟶ Z) (x : T ⟶ X) (y : T ⟶ Y)
    (h : x ≫ f = y ≫ g) :
    SchemePointHomeomorphs.schemeComplexPoints.pullbackLift f g x y h ≫ SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g = y := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

/-- Pulling an image back along a test map is the image from the actual fiber product. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.preimage_image_eq_pullback_image (f : X ⟶ Z) (g : Y ⟶ Z)
    (s : Set (SchemePointHomeomorphs.schemeComplexPoints X)) :
    SchemePointHomeomorphs.schemeComplexPoints.map g ⁻¹' (SchemePointHomeomorphs.schemeComplexPoints.map f '' s) =
      SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g) '' (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g) ⁻¹' s) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨SchemePointHomeomorphs.schemeComplexPoints.pullbackLift f g x y hxy, ?_, ?_⟩
    · change (SchemePointHomeomorphs.schemeComplexPoints.pullbackLift f g x y hxy ≫ SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g) ∈ s
      exact (SchemePointHomeomorphs.schemeComplexPoints.pullbackLift_toLeft f g x y hxy).symm ▸ hx
    · exact SchemePointHomeomorphs.schemeComplexPoints.pullbackLift_toRight f g x y hxy
  · rintro ⟨p, hp, rfl⟩
    refine ⟨SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g) p, hp, ?_⟩
    change (p ≫ SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g) ≫ f = (p ≫ SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g) ≫ g
    simpa only [Category.assoc] using
      congrArg (fun q => p ≫ q) (SchemePointHomeomorphs.schemeComplexPoints.pullback_condition f g)

end

/-!
# Closed maps tested on actual affine pullbacks

This module establishes the topological descent step for closed immersions.
Its local premise is an ordinary closed-map assertion on each actual affine
pullback; the closed-immersion module proves that premise from the algebraic
closed-immersion property.
-/

open _root_.CategoryTheory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- Closedness in the affine-test topology is checked on the actual affine test maps. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isClosed_iff_affineTests (s : Set (SchemePointHomeomorphs.schemeComplexPoints X)) :
    IsClosed s ↔ ∀ (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X),
      IsClosed (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f ⁻¹' s) := by
  constructor
  · intro hs A f
    exact hs.preimage (SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap A f)
  · intro hs
    rw [← isOpen_compl_iff]
    apply (SchemePointHomeomorphs.schemeComplexPoints.isOpen_iff_affineTests _).mpr
    intro A f
    exact (hs A f).isOpen_compl

/-- Closedness of all affine pullback point maps implies closedness of the global point map. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isClosedMap_map_of_affine_pullbacks (f : X ⟶ Y)
    (h : ∀ (A : CommAlgCat ℂ) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y),
      IsClosedMap (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g))) :
    IsClosedMap (SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  intro s hs
  apply (SchemePointHomeomorphs.schemeComplexPoints.isClosed_iff_affineTests _).mpr
  intro A g
  have hclosed : IsClosed
      (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g) '' (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g) ⁻¹' s)) :=
    h A g _ (hs.preimage (SchemePointHomeomorphs.schemeComplexPoints.continuous_map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g)))
  change IsClosed ((SchemePointHomeomorphs.affineSchemePointEquiv A) ⁻¹' (SchemePointHomeomorphs.schemeComplexPoints.map g ⁻¹' (SchemePointHomeomorphs.schemeComplexPoints.map f '' s)))
  rw [SchemePointHomeomorphs.schemeComplexPoints.preimage_image_eq_pullback_image f g s]
  exact hclosed.preimage (SchemePointHomeomorphs.affineSchemePointHomeomorph A).continuous

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
end ComponentSource_20

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointClosedMap"

@[expose] public section ComponentSource_21
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeClosed -/

/-! # Scheme Closed -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Closed immersions on genuine complex scheme points

Every closed immersion of schemes over the complex base induces a closed
topological embedding for the affine-test topology. The proof first treats
affine schemes using their actual global-section algebras, then tests an
arbitrary closed image on affine spaces. Actual scheme pullbacks identify each
test preimage with the image under an affine closed immersion.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- An affine closed immersion is a closed embedding on its genuine complex-valued points. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isAffine
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) [IsClosedImmersion f.left] :
    Topology.IsClosedEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  have hsurj : Function.Surjective (AffineSchemePointTopology.affineCoordinateHom f) := by
    change Function.Surjective (AffineSchemePointTopology.affineCoordinateHom f).toRingHom
    rw [AffineSchemePointTopology.affineCoordinateHom_toRingHom]
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).2
  rw [AffineSchemePointTopology.schemePointMap_eq_affineCoordinates f]
  exact (AffineSchemePointTopology.affineNativePointHomeomorph Y).symm.isClosedEmbedding.comp
    ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_surjective
      (AffineSchemePointTopology.affineCoordinateHom f) hsurj).comp (AffineSchemePointTopology.affineNativePointHomeomorph X).isClosedEmbedding)

/-- A closed immersion gives an injective map on genuine complex-valued points. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.map_injective_of_isClosedImmersion (f : X ⟶ Y) [IsClosedImmersion f.left] :
    Function.Injective (SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  intro x y h
  apply Over.OverMorphism.ext
  apply (cancel_mono f.left).mp
  exact congrArg Over.Hom.left h

/-- Closed immersions send all closed sets of complex-valued points to closed sets. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isClosedMap_map_of_isClosedImmersion (f : X ⟶ Y) [IsClosedImmersion f.left] :
    IsClosedMap (SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  apply SchemePointHomeomorphs.schemeComplexPoints.isClosedMap_map_of_affine_pullbacks f
  intro A g
  have : IsClosedImmersion (SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g).left := by
    change IsClosedImmersion (pullback.snd f.left g.left)
    infer_instance
  have : IsAffine (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left := by
    change IsAffine (Spec (CommRingCat.of A))
    infer_instance
  have : IsAffine (SchemePointHomeomorphs.schemeComplexPoints.pullbackOver f g).left :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g).left).1
  exact (SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isAffine (SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g)).isClosedMap

/-- A closed immersion is a closed point embedding for the affine-test topology. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
    (f : X ⟶ Y) [IsClosedImmersion f.left] :
    Topology.IsClosedEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map f) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (SchemePointHomeomorphs.schemeComplexPoints.continuous_map f) (SchemePointHomeomorphs.schemeComplexPoints.map_injective_of_isClosedImmersion f)
    (SchemePointHomeomorphs.schemeComplexPoints.isClosedMap_map_of_isClosedImmersion f)

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
end ComponentSource_21

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeClosed"

@[expose] public section ComponentSource_22
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.ImmersionComplexPoints -/

/-! # Immersion Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ImmersionComplexPoints

noncomputable section

/-!
# Field-valued points in the image of an immersion

A morphism surjective on stalks induces isomorphisms on residue fields. Hence
a field-valued point whose underlying point lies in its image lifts through
the morphism: transport the residue-field character through that isomorphism.
This also proves the exact image formula for ordinary relative complex points
of closed immersions, immersions, and preimmersions, without any finite-type
or algebraic-closedness assumption in the field-valued lifting theorem.

Only algebraic point sets occur here; no analytic topology is imported.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

section ResidueFields

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f]

/-- Surjectivity on stalks descends to surjectivity on the actual residue fields. -/
theorem residueFieldMap_surjective_of_surjectiveOnStalks (x : X) :
    Function.Surjective (f.residueFieldMap x) := by
  have h : Function.Surjective (f.stalkMap x ≫ X.residue x) :=
    (X.residue_surjective x).comp (f.stalkMap_surjective x)
  rw [← Scheme.residue_residueFieldMap f x] at h
  rw [ConcreteCategory.coe_comp] at h
  exact Function.Surjective.of_comp h

/-- The induced residue-field map is an actual isomorphism: injectivity comes
from its field domain and surjectivity from the stalk map. -/
def residueFieldIsoOfSurjectiveOnStalks (x : X) :
    Y.residueField (f x) ≅ X.residueField x :=
  (RingEquiv.ofBijective (f.residueFieldMap x).hom
    ⟨(f.residueFieldMap x).hom.injective,
      residueFieldMap_surjective_of_surjectiveOnStalks f x⟩).toCommRingCatIso

@[simp]
theorem residueFieldIsoOfSurjectiveOnStalks_hom (x : X) :
    (residueFieldIsoOfSurjectiveOnStalks f x).hom = f.residueFieldMap x := rfl

end ResidueFields

section FieldPoints

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- Every field-valued point with underlying point in the image lifts through
a morphism surjective on stalks. The residue-field character is transported
through the inverse of the actual residue-field map. -/
theorem surjectiveOnStalks_exists_fieldPoint_lift (f : X ⟶ Y)
    [SurjectiveOnStalks f] (p : Spec (.of K) ⟶ Y) (z : Spec (.of K))
    (hp : p z ∈ Set.range f) :
    ∃ q : Spec (.of K) ⟶ X, q ≫ f = p := by
  obtain ⟨⟨y, χ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective p
  change (Spec.map χ ≫ Y.fromSpecResidueField y) z ∈ Set.range f at hp
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at hp
  obtain ⟨x, hx⟩ := hp
  subst y
  let : IsIso (f.residueFieldMap x) :=
    (residueFieldIsoOfSurjectiveOnStalks f x).isIso_hom
  refine ⟨Spec.map (inv (f.residueFieldMap x) ≫ χ) ≫ X.fromSpecResidueField x, ?_⟩
  change _ = Spec.map χ ≫ Y.fromSpecResidueField (f x)
  rw [Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField x,
    ← Category.assoc, ← Spec.map_comp]
  simp

/-- The field-valued lift respects a prescribed base morphism automatically. -/
theorem surjectiveOnStalks_relativeFieldPoint_existsLift
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [SurjectiveOnStalks f.left]
    {b : Spec (.of K) ⟶ S} (p : Over.mk b ⟶ Y) (z : Spec (.of K))
    (hp : p.left z ∈ Set.range f.left) :
    ∃ q : Over.mk b ⟶ X, q ≫ f = p := by
  obtain ⟨q, hq⟩ := surjectiveOnStalks_exists_fieldPoint_lift f.left p.left z hp
  refine ⟨Over.homMk q ?_, ?_⟩
  · rw [← f.w, ← Category.assoc, hq]
    exact p.w
  · apply Over.OverMorphism.ext
    exact hq

/-- Exact image of the relative field-point map for a morphism surjective
on stalks. -/
theorem range_surjectiveOnStalks_relativeFieldPointMap
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [SurjectiveOnStalks f.left]
    (b : Spec (.of K) ⟶ S) (z : Spec (.of K)) :
    Set.range (fun q : Over.mk b ⟶ X => q ≫ f) =
      {p : Over.mk b ⟶ Y | p.left z ∈ Set.range f.left} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.left z, (Scheme.Hom.comp_apply q.left f.left z).symm⟩
  · exact fun hp => surjectiveOnStalks_relativeFieldPoint_existsLift f p z hp

/-- For a preimmersion the relative field-valued lift is unique. -/
theorem preimmersion_relativeFieldPoint_existsUnique
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [IsPreimmersion f.left]
    {b : Spec (.of K) ⟶ S} (p : Over.mk b ⟶ Y) (z : Spec (.of K))
    (hp : p.left z ∈ Set.range f.left) :
    ∃! q : Over.mk b ⟶ X, q ≫ f = p := by
  let : Mono f := Over.mono_of_mono_left f
  obtain ⟨q, hq⟩ := surjectiveOnStalks_relativeFieldPoint_existsLift f p z hp
  refine ⟨q, hq, ?_⟩
  intro r hr
  exact (cancel_mono f).mp (hr.trans hq.symm)

end FieldPoints

variable {X Y : Over ProjectiveSpace.complexBase}

/-- The precise image of the ordinary relative complex-point map, stated
without importing or changing its analytic topology. -/
theorem range_surjectiveOnStalks_complexPointMap (f : X ⟶ Y)
    [SurjectiveOnStalks f.left] :
    Set.range (fun q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X => q ≫ f) =
      {p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Y |
        p.left (⊥ : PrimeSpectrum ℂ) ∈ Set.range f.left} :=
  range_surjectiveOnStalks_relativeFieldPointMap f (𝟙 ProjectiveSpace.complexBase)
    (⊥ : PrimeSpectrum ℂ)

/-- Closed immersions have exactly the complex points prescribed by their
underlying scheme image. -/
theorem range_closedImmersion_complexPointMap (f : X ⟶ Y)
    [IsClosedImmersion f.left] :
    Set.range (fun q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X => q ≫ f) =
      {p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Y |
        p.left (⊥ : PrimeSpectrum ℂ) ∈ Set.range f.left} :=
  range_surjectiveOnStalks_complexPointMap f

/-- The same image characterization holds for every scheme immersion. -/
theorem range_immersion_complexPointMap (f : X ⟶ Y) [IsImmersion f.left] :
    Set.range (fun q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X => q ≫ f) =
      {p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Y |
        p.left (⊥ : PrimeSpectrum ℂ) ∈ Set.range f.left} :=
  range_surjectiveOnStalks_complexPointMap f

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ImmersionComplexPoints
end ComponentSource_22

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.ImmersionComplexPoints"

@[expose] public section ComponentSource_23
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeImmersionPointTopology -/

/-! # Scheme Immersion Point Topology -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Immersions on ordinary complex-valued scheme points

The factorization used here is mathlib's actual coborder factorization of a
scheme immersion into a closed immersion followed by an open immersion.
The ordinary point topology is the established affine-test topology.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The genuine open intermediate scheme in the coborder factorization,
with its inherited complex structure morphism. -/
def SchemePointHomeomorphs.schemeComplexPoints.immersionOpenTarget (φ : X ⟶ Y) [IsImmersion φ.left] : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (φ.left.coborderRange.ι ≫ Y.hom)

/-- The closed part of the actual immersion factorization, over `Spec ℂ`. -/
def SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor (φ : X ⟶ Y) [IsImmersion φ.left] :
    X ⟶ SchemePointHomeomorphs.schemeComplexPoints.immersionOpenTarget φ :=
  Over.homMk φ.left.liftCoborder (by
    change φ.left.liftCoborder ≫ (φ.left.coborderRange.ι ≫ Y.hom) = X.hom
    rw [← Category.assoc, Scheme.Hom.liftCoborder_ι]
    exact φ.w)

/-- The open part of the actual immersion factorization, over `Spec ℂ`. -/
def SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor (φ : X ⟶ Y) [IsImmersion φ.left] :
    SchemePointHomeomorphs.schemeComplexPoints.immersionOpenTarget φ ⟶ Y :=
  Over.homMk φ.left.coborderRange.ι rfl

instance SchemePointHomeomorphs.schemeComplexPoints.isClosedImmersion_immersionClosedFactor (φ : X ⟶ Y) [IsImmersion φ.left] :
    IsClosedImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ).left :=
  inferInstanceAs (IsClosedImmersion φ.left.liftCoborder)

instance SchemePointHomeomorphs.schemeComplexPoints.isOpenImmersion_immersionOpenFactor (φ : X ⟶ Y) [IsImmersion φ.left] :
    IsOpenImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ).left :=
  inferInstanceAs (IsOpenImmersion φ.left.coborderRange.ι)

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor_comp_openFactor (φ : X ⟶ Y) [IsImmersion φ.left] :
    SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ ≫ SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ = φ := by
  apply Over.OverMorphism.ext
  exact φ.left.liftCoborder_ι

/-- On native complex points, the actual immersion is the composition of
the induced closed and open point maps. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.map_immersion_factorization (φ : X ⟶ Y) [IsImmersion φ.left] :
    SchemePointHomeomorphs.schemeComplexPoints.map φ = SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ) ∘ SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ) := by
  funext p
  change p ≫ φ = (p ≫ SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ) ≫ SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ
  rw [Category.assoc, SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor_comp_openFactor]

/-- An actual scheme immersion induces an embedding of ordinary complex
point spaces. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (φ : X ⟶ Y) [IsImmersion φ.left] :
    Topology.IsEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map φ) := by
  rw [SchemePointHomeomorphs.schemeComplexPoints.map_immersion_factorization]
  exact (SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ)).isEmbedding.comp
    (SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ)).isEmbedding

/-- The ordinary complex-point image of an actual immersion is locally
closed, by its genuine closed-then-open factorization. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isLocallyClosed_range_map_of_isImmersion (φ : X ⟶ Y) [IsImmersion φ.left] :
    IsLocallyClosed (Set.range (SchemePointHomeomorphs.schemeComplexPoints.map φ)) := by
  rw [SchemePointHomeomorphs.schemeComplexPoints.map_immersion_factorization, Set.range_comp]
  have hc := SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ)
  have ho := SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ)
  exact hc.isClosed_range.isLocallyClosed.image ho.isEmbedding.isInducing
    ho.isOpen_range.isLocallyClosed

/-- The two standard requirements for a locally closed embedding hold for
the induced ordinary complex-point map. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isLocallyClosedEmbedding_map_of_isImmersion (φ : X ⟶ Y) [IsImmersion φ.left] :
    Topology.IsEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map φ) ∧ IsLocallyClosed (Set.range (SchemePointHomeomorphs.schemeComplexPoints.map φ)) :=
  ⟨SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion φ, SchemePointHomeomorphs.schemeComplexPoints.isLocallyClosed_range_map_of_isImmersion φ⟩

/-- Surjectivity on the actual scheme stalks gives exactly the complex
points lying over the underlying image, by the proved residue-field lift. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.range_map_of_surjectiveOnStalks (φ : X ⟶ Y) [SurjectiveOnStalks φ.left] :
    Set.range (SchemePointHomeomorphs.schemeComplexPoints.map φ) = SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range φ.left :=
  Foundations.Scheme.ImmersionComplexPoints.range_surjectiveOnStalks_complexPointMap φ

/-- The native point image of an actual immersion is precisely the inverse
image of its underlying scheme image. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion (φ : X ⟶ Y) [IsImmersion φ.left] :
    Set.range (SchemePointHomeomorphs.schemeComplexPoints.map φ) = SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range φ.left :=
  SchemePointHomeomorphs.schemeComplexPoints.range_map_of_surjectiveOnStalks φ

/-- Native points of the immersed scheme are homeomorphic to the genuine
locally closed subset specified by its underlying image. -/
def SchemePointHomeomorphs.schemeComplexPoints.immersionPointHomeomorph (φ : X ⟶ Y) [IsImmersion φ.left] :
    SchemePointHomeomorphs.schemeComplexPoints X ≃ₜ (SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range φ.left) :=
  (SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion φ).toHomeomorph.trans
    (Homeomorph.setCongr (SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion φ))

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.immersionPointHomeomorph_val (φ : X ⟶ Y) [IsImmersion φ.left]
    (p : SchemePointHomeomorphs.schemeComplexPoints X) :
    (SchemePointHomeomorphs.schemeComplexPoints.immersionPointHomeomorph φ p).val = SchemePointHomeomorphs.schemeComplexPoints.map φ p := rfl

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
end ComponentSource_23

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeImmersionPointTopology"

@[expose] public section ComponentSource_24
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.GeneratingCoordinates -/

/-! # Generating Coordinates -/

namespace OAI.AlgebraicGeometry

/-!
# Independence of the generating coordinates

If a family generates a complex algebra, evaluation on that family induces the
ordinary topology on its complex points. The proof expresses each algebra
element as a multivariate polynomial in the generators. Consequently a finite
generating family realizes this topology inside ordinary finite-dimensional
complex affine space, and the topology is independent of the chosen family.
-/

universe u v w z

variable {A : Type u} [CommRing A] [Algebra ℂ A]
variable {ι : Type v} {κ : Type w}

/-- Coordinates of an affine complex point on a family of algebra elements. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates (g : ι → A) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) : ι → ℂ :=
  fun i => x (g i)

/-- Evaluating any family of regular functions is continuous. -/
@[continuity, fun_prop]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_coordinates (g : ι → A) : Continuous (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) :=
  continuous_pi fun i => Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval (g i)

/-- A generating family gives a surjective polynomial presentation. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.aeval_surjective_of_adjoin_eq_top (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    Function.Surjective (MvPolynomial.aeval g : MvPolynomial ι ℂ →ₐ[ℂ] A) := by
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
  exact hg

/-- A regular-function evaluation is polynomial evaluation in the coordinates. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval_aeval (g : ι → A) (p : MvPolynomial ι ℂ) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval (MvPolynomial.aeval g p) =
      fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => MvPolynomial.eval (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g x) p := by
  funext x
  exact MvPolynomial.comp_aeval_apply g x p

/-- Generating coordinates induce exactly the ordinary topology on complex points. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coordinates (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    Topology.IsInducing (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) := by
  constructor
  apply le_antisymm (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_coordinates g).le_induced
  change TopologicalSpace.induced (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) inferInstance ≤
    TopologicalSpace.induced
      (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => (x : A → ℂ)) inferInstance
  apply Continuous.le_induced
  let : TopologicalSpace (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :=
    TopologicalSpace.induced (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) inferInstance
  apply continuous_pi
  intro a
  obtain ⟨p, rfl⟩ := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.aeval_surjective_of_adjoin_eq_top g hg a
  change @Continuous (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) ℂ
    (TopologicalSpace.induced (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) inferInstance) _
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval (MvPolynomial.aeval g p))
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval_aeval]
  exact (MvPolynomial.continuous_eval p).comp
    (continuous_induced_dom (f := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g))

/-- A point is determined by its values on any algebra generating family. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates_injective (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    Function.Injective (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) := by
  intro x y h
  apply AlgHom.ext_of_adjoin_eq_top hg
  rintro a ⟨i, rfl⟩
  exact congrFun h i

/-- Generating coordinates embed the complex-point space topologically. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isEmbedding_coordinates (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    Topology.IsEmbedding (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) :=
  ⟨Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coordinates g hg, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates_injective g hg⟩

/-- Continuity can be tested on the values of algebra generators alone. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff_coordinates (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤)
    {X : Type z} [TopologicalSpace X] (f : X → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Continuous f ↔ ∀ i : ι, Continuous (fun x => f x (g i)) :=
  (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coordinates g hg).continuous_iff.trans continuous_pi_iff

/-- Two algebra generating families define exactly the same topology. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.induced_coordinates_eq (g : ι → A) (h : κ → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤)
    (hh : Algebra.adjoin ℂ (Set.range h) = ⊤) :
    TopologicalSpace.induced (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) inferInstance =
      TopologicalSpace.induced (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates h) inferInstance :=
  (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coordinates g hg).eq_induced.symm.trans
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coordinates h hh).eq_induced

end OAI.AlgebraicGeometry
end ComponentSource_24

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.GeneratingCoordinates"

@[expose] public section ComponentSource_25
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation -/

/-! # Polynomial Evaluation -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation

noncomputable section

/-!
# Polynomial coordinates on affine complex points

The complex points of a polynomial algebra, with the topology induced by all
regular functions, are homeomorphic to the ordinary product of complex
coordinate spaces. This identifies the affine-point topology with the standard
Euclidean topology when the variable type is finite. No Zariski topology is used.
-/

universe u v

/-- A character of a polynomial algebra is uniquely determined by its coordinates. -/
def polynomialPointEquiv (ι : Type u) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ) ≃ (ι → ℂ) where
  toFun x i := x (MvPolynomial.X i)
  invFun z := MvPolynomial.aeval z
  left_inv x := (MvPolynomial.aeval_unique x).symm
  right_inv z := by
    funext i
    exact MvPolynomial.aeval_X z i

@[simp] theorem polynomialPointEquiv_apply {ι : Type u}
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ)) (i : ι) :
    polynomialPointEquiv ι x i = x (MvPolynomial.X i) := rfl

@[simp] theorem polynomialPointEquiv_symm_apply {ι : Type u}
    (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    (polynomialPointEquiv ι).symm z p = MvPolynomial.eval z p := rfl

/-- Evaluation in coordinates agrees with the given algebra character. -/
@[simp] theorem polynomialPointEquiv_eval {ι : Type u}
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ)) (p : MvPolynomial ι ℂ) :
    MvPolynomial.eval (polynomialPointEquiv ι x) p = x p :=
  (AlgHom.congr_fun (MvPolynomial.aeval_unique x) p).symm

/-- The topology defined by all polynomial evaluations is exactly the coordinate topology. -/
def polynomialPointHomeomorph (ι : Type u) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ) ≃ₜ (ι → ℂ) where
  toEquiv := polynomialPointEquiv ι
  continuous_toFun := continuous_pi fun i =>
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval (MvPolynomial.X i)
  continuous_invFun := by
    apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).2
    intro p
    exact MvPolynomial.continuous_eval p

@[simp] theorem polynomialPointHomeomorph_apply {ι : Type u}
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ)) (i : ι) :
    polynomialPointHomeomorph ι x i = x (MvPolynomial.X i) := rfl

@[simp] theorem polynomialPointHomeomorph_symm_apply {ι : Type u}
    (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    (polynomialPointHomeomorph ι).symm z p = MvPolynomial.eval z p := rfl

/-- A family of polynomial coordinate functions defines a continuous map. -/
theorem continuous_polynomial_map {ι : Type u} {κ : Type v}
    (P : κ → MvPolynomial ι ℂ) :
    Continuous (fun z : ι → ℂ => fun j => MvPolynomial.eval z (P j)) :=
  continuous_pi fun j => MvPolynomial.continuous_eval (P j)

/-- Restricting a regular function to any affine coordinate subspace is continuous. -/
theorem continuous_polynomial_restriction {ι : Type u}
    (s : Set (ι → ℂ)) (p : MvPolynomial ι ℂ) :
    Continuous (fun z : s => MvPolynomial.eval (z : ι → ℂ) p) :=
  (MvPolynomial.continuous_eval p).comp continuous_subtype_val

/-- Algebraic substitution becomes the usual polynomial map in complex coordinates. -/
theorem polynomialPointEquiv_comp_aeval {ι : Type u} {κ : Type v}
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ))
    (P : κ → MvPolynomial ι ℂ) (j : κ) :
    polynomialPointEquiv κ (x.comp (MvPolynomial.aeval P)) j =
      MvPolynomial.eval (polynomialPointEquiv ι x) (P j) := by
  simp only [polynomialPointEquiv_apply, AlgHom.comp_apply, MvPolynomial.aeval_X,
    polynomialPointEquiv_eval]

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation
end ComponentSource_25

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation"

@[expose] public section ComponentSource_26
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeAffineTopology -/

/-! # Finite Type Affine Topology -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeAffineTopology

/-!
# Ordinary topology of finite-type affine complex points

A finite polynomial presentation embeds the actual complex-character space as
a closed subspace of a finite-dimensional complex coordinate space. This gives
local compactness. Finite generating coordinates also give second countability.
No smoothness assumption is needed for either property.
-/

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- A surjective polynomial presentation gives a closed embedding by its actual
coordinate functions. -/
theorem isClosedEmbedding_polynomialPresentation {ι : Type*}
    (f : MvPolynomial ι ℂ →ₐ[ℂ] A) (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding
      (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => fun i : ι => x (f (MvPolynomial.X i))) := by
  exact (PolynomialEvaluation.polynomialPointHomeomorph ι).isClosedEmbedding.comp
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_surjective f hf)

/-- A finite-type complex affine point space is a closed subspace of some
finite-dimensional complex coordinate space. -/
theorem finiteTypeAffinePoints_exists_closedEmbedding [Algebra.FiniteType ℂ A] :
    ∃ (n : ℕ) (f : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A → Fin n → ℂ), Topology.IsClosedEmbedding f := by
  obtain ⟨n, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := ℂ) (S := A)).mp inferInstance
  exact ⟨n, (fun x i => x (f (MvPolynomial.X i))),
    isClosedEmbedding_polynomialPresentation f hf⟩

/-- The ordinary point topology of a finite-type complex algebra is second
countable: finite algebra generators embed it in a finite complex product. -/
instance finiteTypeAffinePoints_secondCountable [Algebra.FiniteType ℂ A] :
    SecondCountableTopology (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℂ) (A := A)
  have hg : Algebra.adjoin ℂ (Set.range (fun i : s => (i : A))) = ⊤ := by
    have hr : Set.range (fun i : s => (i : A)) = (s : Set A) := by
      ext a
      constructor
      · rintro ⟨i, rfl⟩
        exact i.property
      · intro ha
        exact ⟨⟨a, ha⟩, rfl⟩
    rw [hr]
    exact hs
  exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coordinates (fun i : s => (i : A)) hg).secondCountableTopology

/-- Finite-type affine complex point spaces are locally compact in the ordinary
evaluation topology, including at singular points. -/
instance finiteTypeAffinePoints_locallyCompact [Algebra.FiniteType ℂ A] :
    LocallyCompactSpace (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) := by
  obtain ⟨n, f, hf⟩ := finiteTypeAffinePoints_exists_closedEmbedding (A := A)
  exact hf.locallyCompactSpace

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeAffineTopology
end ComponentSource_26

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeAffineTopology"


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
    (`OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeAffineTopology.finiteTypeAffinePoints_exists_closedEmbedding, "theorem")
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
    ("nonce", toJson "2957c5b1f3dc3dc08d131a37652263b0"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:2957c5b1f3dc3dc08d131a37652263b0"
