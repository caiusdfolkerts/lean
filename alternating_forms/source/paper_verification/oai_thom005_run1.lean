module

public import paper_verification.oai_thom004_run1
import all paper_verification.oai_thom004_run1
public import paper_verification.oai_thom003_run1
import all paper_verification.oai_thom003_run1
public import paper_verification.oai_thom001_run1
import all paper_verification.oai_thom001_run1
public import Mathlib.Algebra.Category.ModuleCat.Descent
import all Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import all Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import all Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import all Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Localization
import all Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.FractionRing
import all Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import all Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import paper_verification.oai_thom000_run1
import all paper_verification.oai_thom000_run1
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.LinearAlgebra.Dual.Defs
import all Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Algebra.Category.ModuleCat.Basic
import all Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.Sheaves.Abelian
import all Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import all Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.LinearAlgebra.Matrix.ToLin
import all Mathlib.LinearAlgebra.Matrix.ToLin
public import paper_verification.oai_thom002_run2
import all paper_verification.oai_thom002_run2
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
import all Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.LinearAlgebra.Complex.Orientation
import all Mathlib.LinearAlgebra.Complex.Orientation
public import Mathlib.RingTheory.Complex
import all Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
import all Mathlib.RingTheory.Norm.Transitivity
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainD -/

/-! # Relative Chain D -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Geometric.RelativeChainD

/-!
# Genuine relative cochains as functionals on relative chains

Relative cochains are the actual kernel of restriction to the subspace.
Relative scalar chains are the actual cokernel of the subspace inclusion.
The absolute evaluation equivalence identifies the former with functionals
vanishing on the kernel of the latter's quotient projection.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Cycles

variable {R : Type} [CommRing R]

/-- Absolute evaluation intertwines restriction of cochains and inclusion of chains. -/
theorem singularDegreewiseChainDualEquiv_restriction (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X n) :
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M (TopCat.of A) n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n c) =
      (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n c).comp
        ((RelativeScalarChains.Cycles.scalarSubspaceChainInclusion R X A).f n).hom :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.degreewiseChainDualEquiv_pullback M (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X A)) n c

/-- A relative cochain restricts to zero on the subspace in each degree. -/
theorem relativeCochainInclusion_restriction_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c) = 0 :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_restriction M X A) n) c

/-- The actual absolute-chain functional associated to a relative cochain. -/
def relativeCochainAbsoluteDual (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n →ₗ[R]
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n →ₗ[R] M) :=
  (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).toLinearMap.comp
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n).hom

@[simp]
theorem relativeCochainAbsoluteDual_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    relativeCochainAbsoluteDual M X A n c =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c) :=
  rfl

/-- Relative evaluation vanishes on every chain coming from the subspace. -/
theorem relativeCochainAbsoluteDual_comp_subspace (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    (relativeCochainAbsoluteDual M X A n c).comp
        ((RelativeScalarChains.Cycles.scalarSubspaceChainInclusion R X A).f n).hom = 0 := by
  have h := singularDegreewiseChainDualEquiv_restriction M X A n
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c)
  rw [relativeCochainInclusion_restriction_apply, map_zero] at h
  exact h.symm

/-- Relative evaluation annihilates the exact kernel of the relative chain projection. -/
theorem relativeCochainAbsoluteDual_ker (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    LinearMap.ker ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom ≤
      LinearMap.ker (relativeCochainAbsoluteDual M X A n c) := by
  rw [RelativeScalarChains.Cycles.relativeScalarChainProjection_ker]
  rintro z ⟨a, rfl⟩
  exact LinearMap.congr_fun (relativeCochainAbsoluteDual_comp_subspace M X A n c) a

/-- A relative cochain is determined by its values on absolute chains. -/
theorem relativeCochainAbsoluteDual_injective (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Function.Injective (relativeCochainAbsoluteDual M X A n) := by
  intro c d h
  apply (ModuleCat.mono_iff_injective ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n)).mp
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainSequence_degreewiseShortExact M X A n).mono_f
  exact (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).injective h

/-- Every absolute functional vanishing on the relative projection kernel is represented
by an actual relative cochain. -/
theorem exists_relativeCochain_of_vanishes (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (φ : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n →ₗ[R] M)
    (hφ : LinearMap.ker ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom ≤
      LinearMap.ker φ) :
    ∃ c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n,
      relativeCochainAbsoluteDual M X A n c = φ := by
  let a := (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).symm φ
  have ha : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n a = 0 := by
    apply (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M (TopCat.of A) n).injective
    rw [map_zero, singularDegreewiseChainDualEquiv_restriction]
    change ((AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n)
      ((AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).symm φ)).comp _ = 0
    rw [LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro z
    have hz : (RelativeScalarChains.Cycles.scalarSubspaceChainInclusion R X A).f n z ∈
        LinearMap.ker ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom := by
      rw [RelativeScalarChains.Cycles.relativeScalarChainProjection_ker]
      exact ⟨z, rfl⟩
    exact hφ hz
  have ha' : a ∈ LinearMap.range ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n).hom := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_range]
    exact ha
  obtain ⟨c, hc⟩ := ha'
  refine ⟨c, ?_⟩
  rw [relativeCochainAbsoluteDual_apply, hc]
  exact (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).apply_symm_apply φ

/-- The actual relative cochain kernel is the annihilator of the actual
relative chain projection kernel. -/
def relativeCochainAnnihilatorEquiv (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n ≃ₗ[R]
      LinearQuotientDual.Cycles.kernelAnnihilator ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom M :=
  LinearEquiv.ofBijective
    ((relativeCochainAbsoluteDual M X A n).codRestrict _
      (fun c => relativeCochainAbsoluteDual_ker M X A n c))
    ⟨by
      intro c d h
      apply relativeCochainAbsoluteDual_injective M X A n
      exact congrArg Subtype.val h,
      by
      intro φ
      obtain ⟨c, hc⟩ := exists_relativeCochain_of_vanishes M X A n φ.val φ.property
      exact ⟨c, Subtype.ext hc⟩⟩

@[simp]
theorem relativeCochainAnnihilatorEquiv_val (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    (relativeCochainAnnihilatorEquiv M X A n c).val = relativeCochainAbsoluteDual M X A n c :=
  rfl

/-- Relative singular cochains are exactly coefficient-valued linear functionals
on the actual relative scalar chains. -/
def relativeDegreewiseChainDualEquiv (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n ≃ₗ[R]
      ((RelativeScalarChains.Cycles.relativeScalarChains R X A).X n →ₗ[R] M) :=
  (relativeCochainAnnihilatorEquiv M X A n).trans
    (LinearQuotientDual.Cycles.quotientDualEquiv (M := M) ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom
      (RelativeScalarChains.Cycles.relativeScalarChainProjection_surjective R X A n)).symm

/-- Evaluation on a projected chain is the ordinary absolute evaluation. -/
@[simp]
theorem relativeDegreewiseChainDualEquiv_projection (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n) :
    relativeDegreewiseChainDualEquiv M X A n c
        ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n z) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c) z := by
  change (LinearQuotientDual.Cycles.quotientDualEquiv (M := M) ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom
    (RelativeScalarChains.Cycles.relativeScalarChainProjection_surjective R X A n)).symm
      (relativeCochainAnnihilatorEquiv M X A n c)
        (((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n).hom z) = _
  rw [LinearQuotientDual.Cycles.quotientDualEquiv_symm_apply]
  rfl

/-- The inverse duality has the same explicit evaluation formula. -/
theorem relativeDegreewiseChainDualEquiv_symm_projection (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (φ : (RelativeScalarChains.Cycles.relativeScalarChains R X A).X n →ₗ[R] M)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n) :
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n
          ((relativeDegreewiseChainDualEquiv M X A n).symm φ)) z =
      φ ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n z) := by
  have h := relativeDegreewiseChainDualEquiv_projection M X A n
    ((relativeDegreewiseChainDualEquiv M X A n).symm φ) z
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- On a projected genuine singular simplex, the relative functional evaluates
the relative cochain's absolute image on that same simplex. -/
@[simp]
theorem relativeDegreewiseChainDualEquiv_simplex (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    relativeDegreewiseChainDualEquiv M X A n c
        ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (TopCat.toSSet.obj X) s)) =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M s
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c) := by
  rw [relativeDegreewiseChainDualEquiv_projection]
  exact AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex (TopCat.toSSet.obj X) M _ s

/-- The relative cochain differential is dual to the actual relative chain
differential, for all indices. -/
theorem relativeDegreewiseChainDualEquiv_d (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (i j : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X i) :
    relativeDegreewiseChainDualEquiv M X A j ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).d i j c) =
      (relativeDegreewiseChainDualEquiv M X A i c).comp
        ((RelativeScalarChains.Cycles.relativeScalarChains R X A).d j i).hom := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := RelativeScalarChains.Cycles.relativeScalarChainProjection_surjective R X A j z
  simp only [LinearMap.comp_apply]
  rw [relativeDegreewiseChainDualEquiv_projection]
  have hp := ConcreteCategory.congr_hom ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).comm j i) z
  change (RelativeScalarChains.Cycles.relativeScalarChains R X A).d j i ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f j z) =
    (RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f i ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d j i z) at hp
  rw [hp, relativeDegreewiseChainDualEquiv_projection]
  have hi := ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).comm i j) c
  change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d i j ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f i c) =
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f j ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).d i j c) at hi
  rw [← hi]
  exact LinearMap.congr_fun (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_d (TopCat.toSSet.obj X) M i j
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f i c)) z

/-- The actual relative cochain complex is the actual linear Hom complex of
the relative scalar chains. -/
def relativeCochainDualIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A ≅ DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex (RelativeScalarChains.Cycles.relativeScalarChains R X A) M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (relativeDegreewiseChainDualEquiv M X A n).toModuleIso)
    (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change (relativeDegreewiseChainDualEquiv M X A i c).comp
        ((RelativeScalarChains.Cycles.relativeScalarChains R X A).d j i).hom =
          relativeDegreewiseChainDualEquiv M X A j ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).d i j c)
      exact (relativeDegreewiseChainDualEquiv_d M X A i j c).symm)

@[simp]
theorem relativeCochainDualIso_hom_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    (relativeCochainDualIso M X A).hom.f n c = relativeDegreewiseChainDualEquiv M X A n c :=
  rfl

@[simp]
theorem relativeCochainDualIso_inv_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (φ : (RelativeScalarChains.Cycles.relativeScalarChains R X A).X n →ₗ[R] M) :
    (relativeCochainDualIso M X A).inv.f n φ = (relativeDegreewiseChainDualEquiv M X A n).symm φ :=
  rfl

/-- Scalar-valued relative cochains are the genuine linear dual cochain complex. -/
abbrev relativeScalarCochainDualIso (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A ≅
      DualComplexUniversalCoefficient.Cycles.dualCochainComplex (RelativeScalarChains.Cycles.relativeScalarChains R X A) :=
  relativeCochainDualIso (ModuleCat.of R R) X A

end Cycles

end AlgebraicGeometry.CycleClass.Geometric.RelativeChainD

namespace AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles
open _root_.CategoryTheory
section

/-!
# Canonical universal-coefficient duality for relative singular cohomology

The cohomology of the actual relative cochain kernel is identified with the
dual of the homology of the actual relative scalar-chain cokernel. The map is
ordinary evaluation on representatives, descended through both boundaries.
-/

section Evaluation

variable {R : Type} [CommRing R]

/-- Canonical evaluation of actual relative cohomology on actual relative homology. -/
def relativeHomologyEvaluation (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n →ₗ[R]
      (RelativeScalarChains.Cycles.relativeScalarHomology R X A n →ₗ[R] M) :=
  (DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation (RelativeScalarChains.Cycles.relativeScalarChains R X A) M n).comp
    (HomologicalComplex.homologyMap (relativeCochainDualIso M X A).hom n).hom

/-- On genuine cocycle and cycle representatives the descended evaluation is
the actual relative-chain functional. -/
@[simp]
theorem relativeHomologyEvaluation_class_class (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeScalarChains.Cycles.relativeScalarChains R X A) n) :
    relativeHomologyEvaluation M X A n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n c)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains R X A) n z) =
        relativeDegreewiseChainDualEquiv M X A n c.val z.val := by
  change DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation (RelativeScalarChains.Cycles.relativeScalarChains R X A) M n
    ((HomologicalComplex.homologyMap (relativeCochainDualIso M X A).hom n)
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n c))
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains R X A) n z) = _
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation_class_class]
  rfl

/-- A projected relative cycle evaluates by the original absolute singular-chain
functional, even when its absolute representative is not an absolute cycle. -/
theorem relativeHomologyEvaluation_class_projection (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n)
    (hz : (RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n z ∈
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeScalarChains.Cycles.relativeScalarChains R X A) n) :
    relativeHomologyEvaluation M X A n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n c)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains R X A) n
        ⟨(RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n z, hz⟩) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c.val) z := by
  rw [relativeHomologyEvaluation_class_class]
  exact relativeDegreewiseChainDualEquiv_projection M X A n c.val z

end Evaluation

variable (F : Type) [Field F]

/-- The universal-coefficient isomorphism for the genuine singular cohomology
and homology of any topological pair over a field, including degree zero. -/
def relativeUniversalCoefficientEquiv (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) X A n ≃ₗ[F]
      Module.Dual F (RelativeScalarChains.Cycles.relativeScalarHomology F X A n) :=
  (((HomologicalComplex.homologyFunctor (ModuleCat.{0} F) (ComplexShape.up ℕ) n).mapIso
    (relativeScalarCochainDualIso F X A)).toLinearEquiv).trans
      (DualComplexUniversalCoefficient.Cycles.dualComplexUniversalCoefficientEquiv (RelativeScalarChains.Cycles.relativeScalarChains F X A) n)

/-- The equivalence's forward map is precisely the canonical relative evaluation. -/
@[simp]
theorem relativeUniversalCoefficientEquiv_apply (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) X A n) :
    relativeUniversalCoefficientEquiv F X A n c =
      relativeHomologyEvaluation (ModuleCat.of F F) X A n c := rfl

/-- Universal-coefficient duality sends relative cocycle classes to their actual
evaluation on relative cycle classes. -/
@[simp]
theorem relativeUniversalCoefficientEquiv_class_class
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of F F) X A) n)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeScalarChains.Cycles.relativeScalarChains F X A) n) :
    relativeUniversalCoefficientEquiv F X A n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of F F) X A) n c)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains F X A) n z) =
        relativeDegreewiseChainDualEquiv (ModuleCat.of F F) X A n c.val z.val :=
  relativeHomologyEvaluation_class_class (ModuleCat.of F F) X A n c z

/-- On a projected relative cycle the universal-coefficient equivalence computes
the same ordinary singular-chain evaluation as the cochain's absolute image. -/
theorem relativeUniversalCoefficientEquiv_class_projection
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of F F) X A) n)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := F) X).X n)
    (hz : (RelativeScalarChains.Cycles.relativeScalarChainProjection F X A).f n z ∈
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeScalarChains.Cycles.relativeScalarChains F X A) n) :
    relativeUniversalCoefficientEquiv F X A n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of F F) X A) n c)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains F X A) n
        ⟨(RelativeScalarChains.Cycles.relativeScalarChainProjection F X A).f n z, hz⟩) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of F F) X n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of F F) X A).f n c.val) z :=
  relativeHomologyEvaluation_class_projection (ModuleCat.of F F) X A n c z hz

end

/-!
# Relative cohomology detects actual relative homology

The genuine field universal-coefficient equivalence identifies every linear
functional on relative scalar homology with an actual relative cohomology
class. Algebraic dual separation therefore detects classes in the original
relative homology group, without a finite-dimensionality or duality premise.
-/

variable (F : Type) [Field F] (X : TopCat.{0}) (A : Set X) (n : ℕ)

/-- Every nonzero actual relative homology class has a relative cohomology
test whose genuine evaluation on it is one. -/
theorem exists_relativeCohomology_evaluation_eq_one
    {z : RelativeScalarChains.Cycles.relativeScalarHomology F X A n} (hz : z ≠ 0) :
    ∃ c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) X A n,
      relativeUniversalCoefficientEquiv F X A n c z = 1 := by
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_eq_one F hz
  refine ⟨(relativeUniversalCoefficientEquiv F X A n).symm L, ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  exact hL

/-- Vanishing of all actual relative cohomology evaluations is equivalent
to vanishing of the original relative homology class. -/
theorem relativeScalarHomology_eq_zero_iff_evaluation
    (z : RelativeScalarChains.Cycles.relativeScalarHomology F X A n) :
    z = 0 ↔ ∀ c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) X A n,
      relativeUniversalCoefficientEquiv F X A n c z = 0 := by
  constructor
  · rintro rfl c
    exact map_zero (relativeUniversalCoefficientEquiv F X A n c)
  · intro h
    by_contra hz
    obtain ⟨c, hc⟩ := exists_relativeCohomology_evaluation_eq_one F X A n hz
    exact one_ne_zero (hc.symm.trans (h c))

/-- The full family of genuine relative cohomology evaluations separates
relative homology classes, in every degree and over every field. -/
theorem relativeScalarHomology_eq_iff_evaluation
    (z w : RelativeScalarChains.Cycles.relativeScalarHomology F X A n) :
    z = w ↔ ∀ c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) X A n,
      relativeUniversalCoefficientEquiv F X A n c z =
        relativeUniversalCoefficientEquiv F X A n c w := by
  constructor
  · rintro rfl c
    rfl
  · intro h
    apply sub_eq_zero.mp
    apply (relativeScalarHomology_eq_zero_iff_evaluation F X A n (z - w)).mpr
    intro c
    rw [map_sub, h c, sub_self]

end AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles

end

end OAI
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainD"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension -/

/-! # Rational Scalar Extension -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles

noncomputable section

/-!
# Rational scalar extension and homology

Rationalization is the actual extension-of-scalars functor from integral modules
to rational modules. Its exactness follows from the localization description of
the rational numbers, and gives the native homology comparison for chain
complexes. The unit-module comparison is the tensor-product right unitor, with
its value on elementary tensors recorded explicitly.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

/-- Rationalization of integral modules by the canonical inclusion into `ℚ`. -/
def rationalizeModules : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ :=
  ModuleCat.extendScalars (Int.castRingHom ℚ)

/-- Flatness comes from the actual fraction-ring localization of `ℤ`. -/
theorem rationalModule_flat : Module.Flat ℤ ℚ :=
  IsLocalization.flat ℚ (nonZeroDivisors ℤ)

/-- The canonical integer-to-rational ring homomorphism is flat. -/
theorem rationalCast_flat : (Int.castRingHom ℚ).Flat := by
  change (algebraMap ℤ ℚ).Flat
  exact RingHom.flat_algebraMap_iff.mpr rationalModule_flat

instance rationalizeModules_isLeftAdjoint : rationalizeModules.IsLeftAdjoint := by
  unfold rationalizeModules
  infer_instance

instance rationalizeModules_preservesColimits : PreservesColimits rationalizeModules := by
  infer_instance

instance rationalizeModules_preservesFiniteLimits :
    PreservesFiniteLimits rationalizeModules :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat rationalCast_flat

instance rationalizeModules_preservesZeroMorphisms :
    rationalizeModules.PreservesZeroMorphisms := by
  infer_instance

instance rationalizeModules_additive : rationalizeModules.Additive :=
  Functor.additive_of_preserves_binary_products rationalizeModules

instance rationalizeModules_preservesHomology : rationalizeModules.PreservesHomology := by
  infer_instance

/-- The degreewise rationalization functor also preserves small colimits. -/
instance rationalizeModules_chain_preservesColimits :
    PreservesColimits (rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)) where
  preservesColimitsOfShape := by
    intros
    infer_instance

/-- Exact rationalization commutes with the native homology of chain complexes. -/
def rationalizeHomologyIso (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    ((rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).homology n ≅
      rationalizeModules.obj (C.homology n) :=
  (C.sc n).mapHomologyIso rationalizeModules

/-- The homology comparison respects all actual integral chain maps. -/
@[reassoc]
theorem rationalizeHomologyIso_hom_naturality
    {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : C ⟶ D) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)).map f) n ≫
        (rationalizeHomologyIso D n).hom =
      (rationalizeHomologyIso C n).hom ≫
        rationalizeModules.map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f) rationalizeModules

/-- Rationalizing the integral unit module gives the rational unit module. -/
def rationalizeUnitIso :
    rationalizeModules.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℚ ℚ :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toModuleIso

/-- Elementary tensors are sent to the product of their rational coefficients. -/
@[simp]
theorem rationalizeUnitIso_hom_tmul (q : ℚ) (z : ℤ) :
    rationalizeUnitIso.hom (q ⊗ₜ[ℤ, Int.castRingHom ℚ] z) = q * (z : ℚ) := by
  change z • q = q * (z : ℚ)
  simp [zsmul_eq_mul, mul_comm]

/-- In particular, the scalar extension of an integer has its usual rational value. -/
@[simp]
theorem rationalizeUnitIso_hom_one_tmul (z : ℤ) :
    rationalizeUnitIso.hom ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z) = (z : ℚ) := by
  simpa only [one_mul] using rationalizeUnitIso_hom_tmul (1 : ℚ) z

/-- The inverse inserts an elementary tensor with integral unit. -/
@[simp]
theorem rationalizeUnitIso_inv_apply (q : ℚ) :
    rationalizeUnitIso.inv q = q ⊗ₜ[ℤ, Int.castRingHom ℚ] (1 : ℤ) :=
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains -/

/-! # Rational Singular Chains -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles

noncomputable section

/-!
# Change of coefficients for genuine singular chains

An additive functor preserving coproducts commutes with the actual simplicial
chain construction. The degreewise isomorphism sends the image of each simplex
summand to the corresponding simplex summand with its coefficient transported
by the specified coefficient isomorphism.
-/

open Simplicial _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe w u₁ u₂ v₁ v₂

section CoefficientFunctor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasCoproducts.{w} C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasCoproducts.{w} D]
variable (F : C ⥤ D) [PreservesColimitsOfSize.{w, w} F]
variable (R : C) (S : D) (e : F.obj R ≅ S)

/-- The actual degreewise coproduct comparison for simplicial chains. -/
def coefficientFunctorChainDegreeIso (K : SSet.{w}) (n : ℕ) :
    F.obj ((K.chainComplex R).X n) ≅ (K.chainComplex S).X n :=
  (asIso (sigmaComparison F (fun _ : K _⦋n⦌ => R))).symm ≪≫
    Sigma.mapIso (fun _ => e)

/-- On each simplex summand, the coproduct comparison applies precisely the
chosen coefficient isomorphism. -/
@[reassoc (attr := simp)]
theorem coefficientFunctorChainDegreeIso_ι (K : SSet.{w}) (n : ℕ) (x : K _⦋n⦌) :
    F.map (K.ιChainComplex (R := R) x) ≫
        (coefficientFunctorChainDegreeIso F R S e K n).hom =
      e.hom ≫ K.ιChainComplex (R := S) x := by
  change F.map (Sigma.ι (fun _ : K _⦋n⦌ => R) x) ≫
    inv (sigmaComparison F (fun _ : K _⦋n⦌ => R)) ≫
    (Sigma.mapIso (fun _ : K _⦋n⦌ => e)).hom =
      e.hom ≫ Sigma.ι (fun _ : K _⦋n⦌ => S) x
  rw [map_ι_comp_inv_sigmaComparison_assoc, Sigma.ι_mapIso_hom]

omit [Preadditive D] [HasCoproducts D] in
/-- The images of the actual simplex summands are jointly epimorphic. -/
theorem coefficientFunctorChain_hom_ext (K : SSet.{w}) (n : ℕ) {T : D}
    {f g : F.obj ((K.chainComplex R).X n) ⟶ T}
    (h : ∀ x : K _⦋n⦌,
      F.map (K.ιChainComplex (R := R) x) ≫ f =
        F.map (K.ιChainComplex (R := R) x) ≫ g) : f = g := by
  apply (isColimitCofanMkObjOfIsColimit F (fun _ : K _⦋n⦌ => R)
    (fun x => K.ιChainComplex (R := R) x) (K.isColimitChainComplexXCofan R n)).hom_ext
  intro x
  exact h x.as

variable [F.Additive]

/-- Coproduct comparison commutes with the alternating face differential. -/
theorem coefficientFunctorChainDegreeIso_comm (K : SSet.{w}) (n : ℕ) :
    (coefficientFunctorChainDegreeIso F R S e K (n + 1)).hom ≫
        (K.chainComplex S).d (n + 1) n =
      F.map ((K.chainComplex R).d (n + 1) n) ≫
        (coefficientFunctorChainDegreeIso F R S e K n).hom := by
  apply coefficientFunctorChain_hom_ext F R K (n + 1)
  intro x
  rw [← Category.assoc, coefficientFunctorChainDegreeIso_ι, Category.assoc,
    SSet.ιChainComplex_d, ← F.map_comp_assoc, SSet.ιChainComplex_d]
  simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.sum_comp,
    Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    coefficientFunctorChainDegreeIso_ι]

/-- An additive coproduct-preserving coefficient functor commutes with the
actual simplicial chain complex, including its boundary maps. -/
def coefficientFunctorChainsIso (K : SSet.{w}) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (K.chainComplex R) ≅
      K.chainComplex S :=
  HomologicalComplex.Hom.isoOfComponents
    (coefficientFunctorChainDegreeIso F R S e K) (by
      rintro i j (rfl : j + 1 = i)
      exact coefficientFunctorChainDegreeIso_comm F R S e K j)

/-- The chain comparison preserves every simplex summand. -/
@[reassoc (attr := simp)]
theorem coefficientFunctorChainsIso_ι (K : SSet.{w}) (n : ℕ) (x : K _⦋n⦌) :
    F.map (K.ιChainComplex (R := R) x) ≫
        (coefficientFunctorChainsIso F R S e K).hom.f n =
      e.hom ≫ K.ιChainComplex (R := S) x :=
  coefficientFunctorChainDegreeIso_ι F R S e K n x

/-- The actual chain comparison is natural under every simplicial map. -/
@[reassoc]
theorem coefficientFunctorChainsIso_hom_naturality {K L : SSet.{w}} (f : K ⟶ L) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (SSet.chainComplexMap f R) ≫
        (coefficientFunctorChainsIso F R S e L).hom =
      (coefficientFunctorChainsIso F R S e K).hom ≫ SSet.chainComplexMap f S := by
  ext n
  apply coefficientFunctorChain_hom_ext F R K n
  intro x
  change F.map (K.ιChainComplex (R := R) x) ≫
      (F.map ((SSet.chainComplexMap f R).f n) ≫
        (coefficientFunctorChainDegreeIso F R S e L n).hom) =
    F.map (K.ιChainComplex (R := R) x) ≫
      ((coefficientFunctorChainDegreeIso F R S e K n).hom ≫
        (SSet.chainComplexMap f S).f n)
  rw [← F.map_comp_assoc, SSet.ι_chainComplexMap_f,
    coefficientFunctorChainDegreeIso_ι, coefficientFunctorChainDegreeIso_ι_assoc,
    SSet.ι_chainComplexMap_f]

end CoefficientFunctor

/-- Rationalizing genuine integral singular chains gives the genuine singular
chain complex with rational coefficients. -/
def rationalSingularChainsIso (X : TopCat.{0}) :
    (RationalScalarExtension.Cycles.rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (LocalHomology.Cycles.integralSingularChains X) ≅
      (RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).obj X :=
  coefficientFunctorChainsIso RationalScalarExtension.Cycles.rationalizeModules (ModuleCat.of ℤ ℤ) (ModuleCat.of ℚ ℚ)
    RationalScalarExtension.Cycles.rationalizeUnitIso (TopCat.toSSet.obj X)

/-- Rational coefficient comparison is natural for every continuous map. -/
@[reassoc]
theorem rationalSingularChainsIso_hom_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (RationalScalarExtension.Cycles.rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (LocalHomology.Cycles.integralSingularChainFunctor.map f) ≫ (rationalSingularChainsIso Y).hom =
      (rationalSingularChainsIso X).hom ≫ (RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f :=
  coefficientFunctorChainsIso_hom_naturality RationalScalarExtension.Cycles.rationalizeModules
    (ModuleCat.of ℤ ℤ) (ModuleCat.of ℚ ℚ) RationalScalarExtension.Cycles.rationalizeUnitIso (TopCat.toSSet.map f)

/-- The rational chain comparison transports the coefficient of each singular
simplex by the canonical rationalized-unit isomorphism. -/
@[reassoc (attr := simp)]
theorem rationalSingularChainsIso_ι (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    RationalScalarExtension.Cycles.rationalizeModules.map
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ) ≫
        (rationalSingularChainsIso X).hom.f n =
      RationalScalarExtension.Cycles.rationalizeUnitIso.hom ≫
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ :=
  coefficientFunctorChainsIso_ι RationalScalarExtension.Cycles.rationalizeModules
    (ModuleCat.of ℤ ℤ) (ModuleCat.of ℚ ℚ) RationalScalarExtension.Cycles.rationalizeUnitIso (TopCat.toSSet.obj X) n σ

/-- On an elementary tensor supported at a singular simplex, the coefficient
is the usual product of the rational scalar and the integral coefficient. -/
@[simp]
theorem rationalSingularChainsIso_hom_tmul_simplex (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (q : ℚ) (z : ℤ) :
    (rationalSingularChainsIso X).hom.f n
        (q ⊗ₜ[ℤ, Int.castRingHom ℚ]
          (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ z) =
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ (q * (z : ℚ)) := by
  have h := ConcreteCategory.congr_hom (rationalSingularChainsIso_ι X n σ)
    (q ⊗ₜ[ℤ, Int.castRingHom ℚ] z)
  change (rationalSingularChainsIso X).hom.f n
      (RationalScalarExtension.Cycles.rationalizeModules.map
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ)
        (q ⊗ₜ[ℤ, Int.castRingHom ℚ] z)) =
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ
      (RationalScalarExtension.Cycles.rationalizeUnitIso.hom (q ⊗ₜ[ℤ, Int.castRingHom ℚ] z)) at h
  rw [RationalScalarExtension.Cycles.rationalizeUnitIso_hom_tmul] at h
  exact h

/-- A unit-coefficient integral singular simplex becomes the same simplex
with unit rational coefficient. -/
@[simp]
theorem rationalSingularChainsIso_hom_one_tmul_simplex (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (rationalSingularChainsIso X).hom.f n
        ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
          (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ 1) =
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ 1 := by
  simpa using rationalSingularChainsIso_hom_tmul_simplex X n σ 1 1

/-- The rational comparison assembled as a natural isomorphism of the actual
singular chain functors. -/
def rationalSingularChainsNatIso :
    LocalHomology.Cycles.integralSingularChainFunctor ⋙
        RationalScalarExtension.Cycles.rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ) ≅
      RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ :=
  NatIso.ofComponents rationalSingularChainsIso
    (fun f => rationalSingularChainsIso_hom_naturality f)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalVanishing -/

/-! # Complex Local Vanishing -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalVanishing.Cycles

noncomputable section

/-!
# Concentration of complex normal local homology

The canonical zeroth-homology augmentations identify the inclusion map of a
path-connected subspace in a path-connected ambient space. The actual relative
long exact sequence then gives the low-degree vanishing needed for the pair
`(ℂ^p, ℂ^p \ {0})`. Together with the sphere calculation this proves that the
local integral singular homology is zero exactly outside degree `2p`.

The top group was already computed as `ℤ`. Neither this concentration result
nor that rank calculation asserts compatibility of generators with orientation
or chart changes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
/-- The actual map induced on H0 by a subspace inclusion agrees with the
canonical augmentation identifications when both spaces are path connected. -/
theorem subspaceHomologyInclusion_zero_eq (X : TopCat.{0}) (A : Set X)
    [PathConnectedSpace X] [PathConnectedSpace A] :
    RelativeHomologyExact.Cycles.subspaceHomologyInclusion X A 0 =
      (ContractibleModel.Cycles.integralSingularH0Iso (TopCat.of A)).hom ≫ (ContractibleModel.Cycles.integralSingularH0Iso X).inv := by
  apply (cancel_mono (ContractibleModel.Cycles.integralSingularH0Iso X).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact HomologyZeroNaturality.Cycles.integralSingularH0_augmentation_naturality (LocalHomology.Cycles.subspaceInclusion X A)

/-- In particular this genuine H0 inclusion is an isomorphism. -/
instance subspaceHomologyInclusion_zero_isIso (X : TopCat.{0}) (A : Set X)
    [PathConnectedSpace X] [PathConnectedSpace A] :
    IsIso (RelativeHomologyExact.Cycles.subspaceHomologyInclusion X A 0) := by
  rw [subspaceHomologyInclusion_zero_eq]
  infer_instance

/-- The actual degree-zero relative group vanishes for a path-connected
subspace of a path-connected ambient space. -/
theorem relativeH0_isZero_of_pathConnected (X : TopCat.{0}) (A : Set X)
    [PathConnectedSpace X] [PathConnectedSpace A] :
    IsZero (LocalHomology.Cycles.relativeSingularHomology X A 0) := by
  apply IsZero.of_epi_eq_zero (RelativeHomologyExact.Cycles.relativeHomologyProjection X A 0)
  exact zero_of_epi_comp (RelativeHomologyExact.Cycles.subspaceHomologyInclusion X A 0)
    (RelativeHomologyExact.Cycles.subspaceHomologyInclusion_projection X A 0)

/-- If the ambient H1 vanishes as well, the actual relative H1 vanishes.
The connecting map is mono and its target's inclusion map is an isomorphism. -/
theorem relativeH1_isZero_of_pathConnected (X : TopCat.{0}) (A : Set X)
    [PathConnectedSpace X] [PathConnectedSpace A]
    (hambient : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology X 1)) :
    IsZero (LocalHomology.Cycles.relativeSingularHomology X A 1) := by
  let : Mono (RelativeHomologyExact.Cycles.relativeHomologyBoundary X A 0) :=
    (LocalHomology.Cycles.relativeChainSequence_shortExact X A).mono_δ 1 0 rfl hambient
  apply IsZero.of_mono_eq_zero (RelativeHomologyExact.Cycles.relativeHomologyBoundary X A 0)
  exact zero_of_comp_mono (RelativeHomologyExact.Cycles.subspaceHomologyInclusion X A 0)
    (RelativeHomologyExact.Cycles.relativeHomologyBoundary_inclusion X A 0)

/-- Punctured positive-dimensional complex coordinate space is genuinely
path connected. The real coordinate model has dimension at least two. -/
instance positiveComplexPunctured_pathConnectedSpace (p : ℕ) :
    PathConnectedSpace (NormalSphere.Cycles.PuncturedNormal (Fin (p + 1) → ℂ)) := by
  have hdim : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * (p + 1)))) := by
    simp only [finrank_euclideanSpace_fin]
    omega
  let : PathConnectedSpace (NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * (p + 1))))) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank
        (Module.one_lt_rank_of_one_lt_finrank hdim) 0)
  exact (RealComplexNormalModel.Cycles.complexRealPuncturedHomeomorph (p + 1)).symm.surjective.pathConnectedSpace
    (RealComplexNormalModel.Cycles.complexRealPuncturedHomeomorph (p + 1)).symm.continuous

/-- Local H0 vanishes in positive complex dimension. -/
theorem positiveComplexLocalH0_isZero (p : ℕ) :
    IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (p + 1) → ℂ)) 0 0) :=
  relativeH0_isZero_of_pathConnected (TopCat.of (Fin (p + 1) → ℂ)) {0}ᶜ

/-- Local H1 vanishes in positive complex dimension. -/
theorem positiveComplexLocalH1_isZero (p : ℕ) :
    IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (p + 1) → ℂ)) 0 1) :=
  relativeH1_isZero_of_pathConnected (TopCat.of (Fin (p + 1) → ℂ)) {0}ᶜ
    (ContractibleModel.Cycles.isZero_complexNormalModelHomology (p + 1) 1 (by decide))

/-- The zero-dimensional model has no local homology in positive degree.
Here the punctured subspace is empty, so the actual relative chain complex
is identified with the absolute one. -/
theorem complexZeroLocalHomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin 0 → ℂ)) 0 n) := by
  have hempty : ({0}ᶜ : Set (Fin 0 → ℂ)) = ∅ := by
    ext x
    simp [Subsingleton.elim x 0]
  unfold LocalHomology.Cycles.localSingularHomology
  rw [hempty]
  exact (ContractibleModel.Cycles.isZero_complexNormalModelHomology 0 n hn).of_iso
    (Point.Cycles.relativeEmptyHomologyIso (TopCat.of (Fin 0 → ℂ)) n)

/-- Actual complex normal local homology vanishes outside the real dimension,
in every degree and including the zero-dimensional case. -/
theorem complexNormalLocalHomology_isZero (p n : ℕ) (hnotTop : n ≠ 2 * p) :
    IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 n) := by
  cases p with
  | zero => exact complexZeroLocalHomology_isZero n (by simpa using hnotTop)
  | succ p =>
      cases n with
      | zero => exact positiveComplexLocalH0_isZero p
      | succ n =>
          cases n with
          | zero => exact positiveComplexLocalH1_isZero p
          | succ n =>
              exact ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalHomology_isZero p (n + 1)
                (Nat.succ_ne_zero n) (by simpa only [Nat.mul_succ] using hnotTop)

/-- The top group is nonzero because its already-proved value is `ℤ`. -/
theorem complexNormalTopLocalHomology_not_isZero (p : ℕ) :
    ¬ IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (2 * p)) := by
  intro h
  have hZ := h.of_iso (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).symm
  let : Subsingleton ℤ := ModuleCat.isZero_iff_subsingleton.mp hZ
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

/-- The precise concentration statement: the genuine local group vanishes
if and only if its degree is different from `2p`. -/
theorem complexNormalLocalHomology_isZero_iff (p n : ℕ) :
    IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 n) ↔ n ≠ 2 * p := by
  constructor
  · intro h hn
    subst n
    exact complexNormalTopLocalHomology_not_isZero p h
  · exact complexNormalLocalHomology_isZero p n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalVanishing.Cycles
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalVanishing"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology -/

/-! # Rational Relative Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles

noncomputable section

/-!
# Rational coefficients on actual relative singular homology

Rationalizing the actual integral relative singular-chain quotient gives the
actual rational relative singular-chain quotient. The comparison is induced
by the natural coefficient comparison on absolute singular chains and by
preservation of cokernels. Exactness of rationalization then identifies its
homology with the rationalization of integral relative homology.

The known integral calculation of the complex normal local groups therefore
gives the rational calculation, in all degrees including complex dimension
zero.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Degreewise extension of integral chain complexes to rational coefficients. -/
abbrev rationalizeChains :
    ChainComplex (ModuleCat.{0} ℤ) ℕ ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  RationalScalarExtension.Cycles.rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)

/-- Rationalization commutes with the actual relative singular-chain quotient. -/
def rationalRelativeChainsIso (X : TopCat.{0}) (A : Set X) :
    rationalizeChains.obj (LocalHomology.Cycles.relativeSingularChains X A) ≅ RelativeScalarChains.Cycles.relativeScalarChains ℚ X A :=
  PreservesCokernel.iso rationalizeChains (LocalHomology.Cycles.subspaceChainInclusion X A) ≪≫
    cokernel.mapIso
      (rationalizeChains.map (LocalHomology.Cycles.subspaceChainInclusion X A))
      (RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X A)
      (RationalSingularChains.Cycles.rationalSingularChainsIso (TopCat.of A)) (RationalSingularChains.Cycles.rationalSingularChainsIso X)
      (RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality (LocalHomology.Cycles.subspaceInclusion X A))

/-- The comparison commutes with the actual absolute-to-relative quotient maps. -/
@[reassoc]
theorem rationalRelativeChainsIso_projection (X : TopCat.{0}) (A : Set X) :
    rationalizeChains.map (LocalHomology.Cycles.relativeChainProjection X A) ≫
        (rationalRelativeChainsIso X A).hom =
      (RationalSingularChains.Cycles.rationalSingularChainsIso X).hom ≫ RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A := by
  dsimp only [rationalRelativeChainsIso, Iso.trans_hom, cokernel.mapIso_hom]
  rw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]

/-- The relative rationalization comparison is natural for actual maps of pairs. -/
@[reassoc]
theorem rationalRelativeChainsIso_hom_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    rationalizeChains.map (LocalHomology.Cycles.relativeSingularChainsMap f h) ≫
        (rationalRelativeChainsIso Y B).hom =
      (rationalRelativeChainsIso X A).hom ≫ RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h := by
  apply (cancel_epi (rationalizeChains.map (LocalHomology.Cycles.relativeChainProjection X A))).mp
  calc
    _ = rationalizeChains.map
        (LocalHomology.Cycles.relativeChainProjection X A ≫ LocalHomology.Cycles.relativeSingularChainsMap f h) ≫
          (rationalRelativeChainsIso Y B).hom := by
      rw [rationalizeChains.map_comp, Category.assoc]
    _ = rationalizeChains.map (LocalHomology.Cycles.integralSingularChainFunctor.map f) ≫
        rationalizeChains.map (LocalHomology.Cycles.relativeChainProjection Y B) ≫
          (rationalRelativeChainsIso Y B).hom := by
      rw [LocalHomology.Cycles.relativeChainProjection_naturality, rationalizeChains.map_comp, Category.assoc]
    _ = rationalizeChains.map (LocalHomology.Cycles.integralSingularChainFunctor.map f) ≫
        (RationalSingularChains.Cycles.rationalSingularChainsIso Y).hom ≫ RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B := by
      rw [rationalRelativeChainsIso_projection]
    _ = (RationalSingularChains.Cycles.rationalSingularChainsIso X).hom ≫
        (RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f ≫ RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B := by
      rw [← Category.assoc, RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality, Category.assoc]
    _ = (RationalSingularChains.Cycles.rationalSingularChainsIso X).hom ≫ RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A ≫
        RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h := by
      rw [RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality]
    _ = _ := by
      rw [← Category.assoc, ← rationalRelativeChainsIso_projection, Category.assoc]

/-- The inverse comparison is also natural for actual maps of pairs. -/
@[reassoc]
theorem rationalRelativeChainsIso_inv_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h ≫ (rationalRelativeChainsIso Y B).inv =
      (rationalRelativeChainsIso X A).inv ≫
        rationalizeChains.map (LocalHomology.Cycles.relativeSingularChainsMap f h) := by
  calc
    _ = (rationalRelativeChainsIso X A).inv ≫
        ((rationalRelativeChainsIso X A).hom ≫ RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h) ≫
          (rationalRelativeChainsIso Y B).inv := by simp
    _ = (rationalRelativeChainsIso X A).inv ≫
        (rationalizeChains.map (LocalHomology.Cycles.relativeSingularChainsMap f h) ≫
          (rationalRelativeChainsIso Y B).hom) ≫
          (rationalRelativeChainsIso Y B).inv := by
      rw [← rationalRelativeChainsIso_hom_naturality]
    _ = _ := by simp

/-- Rational relative homology is the scalar extension of the actual integral relative group. -/
def rationalRelativeHomologyIso (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A n ≅
      RationalScalarExtension.Cycles.rationalizeModules.obj (LocalHomology.Cycles.relativeSingularHomology X A n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapIso
      (rationalRelativeChainsIso X A).symm ≪≫
    RationalScalarExtension.Cycles.rationalizeHomologyIso (LocalHomology.Cycles.relativeSingularChains X A) n

/-- The homology-level scalar-extension identification respects every actual map of pairs. -/
@[reassoc]
theorem rationalRelativeHomologyIso_hom_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (n : ℕ) :
    HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h) n ≫
        (rationalRelativeHomologyIso Y B n).hom =
      (rationalRelativeHomologyIso X A n).hom ≫
        RationalScalarExtension.Cycles.rationalizeModules.map (LocalHomology.Cycles.relativeSingularHomologyMap f h n) := by
  have hnat := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (rationalRelativeChainsIso_inv_naturality f h)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hnat
  change HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h) n ≫
      (HomologicalComplex.homologyMap (rationalRelativeChainsIso Y B).inv n ≫
        (RationalScalarExtension.Cycles.rationalizeHomologyIso (LocalHomology.Cycles.relativeSingularChains Y B) n).hom) =
    (HomologicalComplex.homologyMap (rationalRelativeChainsIso X A).inv n ≫
        (RationalScalarExtension.Cycles.rationalizeHomologyIso (LocalHomology.Cycles.relativeSingularChains X A) n).hom) ≫
      RationalScalarExtension.Cycles.rationalizeModules.map (LocalHomology.Cycles.relativeSingularHomologyMap f h n)
  rw [← Category.assoc, hnat, Category.assoc, RationalScalarExtension.Cycles.rationalizeHomologyIso_hom_naturality,
    ← Category.assoc]

/-- Vanishing of integral relative homology implies vanishing with rational coefficients. -/
theorem rationalRelativeHomology_isZero (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (h : IsZero (LocalHomology.Cycles.relativeSingularHomology X A n)) :
    IsZero (RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A n) :=
  (RationalScalarExtension.Cycles.rationalizeModules.map_isZero h).of_iso (rationalRelativeHomologyIso X A n)

/-- The actual top rational local homology of a complex coordinate normal space is `ℚ`. -/
def complexNormalRationalTopLocalHomologyIso (p : ℕ) :
    RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin p → ℂ)) 0 (2 * p) ≅ ModuleCat.of ℚ ℚ :=
  rationalRelativeHomologyIso (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) (2 * p) ≪≫
    RationalScalarExtension.Cycles.rationalizeModules.mapIso (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p) ≪≫ RationalScalarExtension.Cycles.rationalizeUnitIso

/-- Every rational local homology group outside real degree `2*p` vanishes. -/
theorem complexNormalRationalLocalHomology_isZero (p n : ℕ) (hn : n ≠ 2 * p) :
    IsZero (RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin p → ℂ)) 0 n) :=
  rationalRelativeHomology_isZero (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) n
    (ComplexLocalVanishing.Cycles.complexNormalLocalHomology_isZero p n hn)

/-- The top rational local group is nonzero. -/
theorem complexNormalRationalTopLocalHomology_not_isZero (p : ℕ) :
    ¬ IsZero (RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin p → ℂ)) 0 (2 * p)) := by
  intro h
  have hQ := h.of_iso (complexNormalRationalTopLocalHomologyIso p).symm
  let : Subsingleton ℚ := ModuleCat.isZero_iff_subsingleton.mp hQ
  exact zero_ne_one (Subsingleton.elim (0 : ℚ) 1)

/-- Rational normal local homology is concentrated exactly in its real top degree. -/
theorem complexNormalRationalLocalHomology_isZero_iff (p n : ℕ) :
    IsZero (RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin p → ℂ)) 0 n) ↔ n ≠ 2 * p := by
  constructor
  · intro h hn
    subst n
    exact complexNormalRationalTopLocalHomology_not_isZero p h
  · exact complexNormalRationalLocalHomology_isZero p n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.DualNormalization -/

/-! # Dual Normalization -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.DualNormalization.Cycles

noncomputable section

/-!
# Dual normalization of a module identified with its coefficient field

An actual linear equivalence `e: V ≃ₗ[F] F` identifies the dual of `V` with `F`
by evaluating a functional on `e.symm 1`. This is the composite of mathlib's
dual-map equivalence and its equivalence between linear maps out of the scalar
ring and their values at `1`. The inverse sends a scalar to that scalar times
`e.toLinearMap`, so no choice of basis or generator is introduced.
-/

universe uF uV

variable {F : Type uF} [Field F]
variable {V : Type uV} [AddCommGroup V] [Module F V]

/-- Normalize a dual functional by its value on the vector corresponding to `1`. -/
def dualNormalizationEquiv (e : V ≃ₗ[F] F) : Module.Dual F V ≃ₗ[F] F :=
  e.symm.dualMap.trans (LinearMap.ringLmapEquivSelf F F F)

@[simp]
theorem dualNormalizationEquiv_apply (e : V ≃ₗ[F] F) (φ : Module.Dual F V) :
    dualNormalizationEquiv e φ = φ (e.symm 1) :=
  rfl

@[simp]
theorem dualNormalizationEquiv_symm_apply (e : V ≃ₗ[F] F) (a : F) :
    (dualNormalizationEquiv e).symm a = a • e.toLinearMap := by
  ext v
  change e v * a = a * e v
  exact mul_comm _ _

@[simp]
theorem dualNormalizationEquiv_symm_one (e : V ≃ₗ[F] F) :
    (dualNormalizationEquiv e).symm 1 = e.toLinearMap := by
  rw [dualNormalizationEquiv_symm_apply, one_smul]

@[simp]
theorem dualNormalizationEquiv_toLinearMap (e : V ≃ₗ[F] F) :
    dualNormalizationEquiv e e.toLinearMap = 1 := by
  simp

/-- Evaluation of the functional of any prescribed normalization. -/
theorem dualNormalizationEquiv_symm_apply_apply (e : V ≃ₗ[F] F) (a : F) (v : V) :
    (dualNormalizationEquiv e).symm a v = a * e v := by
  rw [dualNormalizationEquiv_symm_apply]
  rfl

/-- Every functional is its normalization times the original coordinate map. -/
theorem dual_eq_normalization_smul (e : V ≃ₗ[F] F) (φ : Module.Dual F V) :
    φ = dualNormalizationEquiv e φ • e.toLinearMap := by
  rw [← dualNormalizationEquiv_symm_apply]
  exact ((dualNormalizationEquiv e).symm_apply_apply φ).symm

theorem dual_apply_eq_normalization_mul (e : V ≃ₗ[F] F)
    (φ : Module.Dual F V) (v : V) :
    φ v = dualNormalizationEquiv e φ * e v :=
  congrArg (fun ψ : Module.Dual F V => ψ v) (dual_eq_normalization_smul e φ)

/-- The coefficient of a functional is determined by evaluation on `e.symm 1`. -/
theorem dual_eq_smul_iff (e : V ≃ₗ[F] F) (φ : Module.Dual F V) (a : F) :
    φ = a • e.toLinearMap ↔ φ (e.symm 1) = a := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    calc
      φ = dualNormalizationEquiv e φ • e.toLinearMap := dual_eq_normalization_smul e φ
      _ = a • e.toLinearMap := by rw [dualNormalizationEquiv_apply, h]

/-- The original coordinate map is the unique functional normalized to `1`. -/
theorem dual_normalization_eq_one_iff (e : V ≃ₗ[F] F) (φ : Module.Dual F V) :
    φ (e.symm 1) = 1 ↔ φ = e.toLinearMap := by
  simpa only [one_smul] using (dual_eq_smul_iff e φ 1).symm

theorem dual_existsUnique_smul (e : V ≃ₗ[F] F) (φ : Module.Dual F V) :
    ∃! a : F, φ = a • e.toLinearMap := by
  refine ⟨dualNormalizationEquiv e φ, dual_eq_normalization_smul e φ, ?_⟩
  intro a ha
  exact ((dual_eq_smul_iff e φ a).mp ha).symm

/-- Evaluation on the normalized vector detects equality of dual functionals. -/
theorem dual_eq_of_normalization_eq (e : V ≃ₗ[F] F) {φ ψ : Module.Dual F V}
    (h : φ (e.symm 1) = ψ (e.symm 1)) : φ = ψ :=
  (dualNormalizationEquiv e).injective h

/-- The dual of an actual zero module is zero. -/
theorem dual_isZero_of_isZero
    (hV : CategoryTheory.Limits.IsZero (ModuleCat.of F V)) :
    CategoryTheory.Limits.IsZero (ModuleCat.of F (Module.Dual F V)) := by
  let : Subsingleton V := ModuleCat.subsingleton_of_isZero hV
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.DualNormalization.Cycles
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.DualNormalization"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity -/

/-! # Rational Local Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity.Cycles

noncomputable section

/-!
# Rational local cohomology of complex normal coordinates

The cochain complex is the actual kernel of singular-cochain restriction to
the punctured space. Its cohomology is identified, through the proved relative
evaluation isomorphism, with the dual of the actual rational relative homology.
Exact rationalization of the integral local calculation then gives `ℚ` in
degree `2p` and zero in every other degree.

The distinguished class is dual to the specified integral-to-rational local
homology normalization. Its evaluation is proved to be one. Compatibility
with geometric orientations and nonlinear changes of normal charts is a
separate obligation, and no global Thom or algebraic-cycle class is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- The genuine relative rational cohomology of the punctured complex model. -/
abbrev complexNormalRationalLocalCohomology (p n : ℕ) : ModuleCat.{0} ℚ :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin p → ℂ))
    ({0}ᶜ : Set (Fin p → ℂ)) n

/-- The established rational top local homology normalization, as a linear equivalence. -/
def complexNormalRationalTopHomologyEquiv (p : ℕ) :
    RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin p → ℂ)) 0 (2 * p) ≃ₗ[ℚ] ℚ :=
  (RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso p).toLinearEquiv

/-- The rational homology generator specified by the integral local calculation
and its exact coefficient change. -/
def complexNormalRationalTopHomologyGenerator (p : ℕ) :
    RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin p → ℂ)) 0 (2 * p) :=
  (complexNormalRationalTopHomologyEquiv p).symm 1

@[simp]
theorem complexNormalRationalTopHomologyGenerator_normalization (p : ℕ) :
    complexNormalRationalTopHomologyEquiv p (complexNormalRationalTopHomologyGenerator p) = 1 :=
  (complexNormalRationalTopHomologyEquiv p).apply_symm_apply 1

/-- Top relative rational cohomology is `ℚ`, by actual evaluation on the
specified rational local homology generator. -/
def complexNormalRationalTopCohomologyEquiv (p : ℕ) :
    complexNormalRationalLocalCohomology p (2 * p) ≃ₗ[ℚ] ℚ :=
  (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
    ({0}ᶜ : Set (Fin p → ℂ)) (2 * p)).trans
      (DualNormalization.Cycles.dualNormalizationEquiv (complexNormalRationalTopHomologyEquiv p))

/-- The normalization map is explicitly evaluation on the actual generator. -/
theorem complexNormalRationalTopCohomologyEquiv_apply (p : ℕ)
    (a : complexNormalRationalLocalCohomology p (2 * p)) :
    complexNormalRationalTopCohomologyEquiv p a =
      RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
        ({0}ᶜ : Set (Fin p → ℂ)) (2 * p) a
          (complexNormalRationalTopHomologyGenerator p) := rfl

/-- The same genuine top cohomology computation in the category of rational modules. -/
def complexNormalRationalTopCohomologyIso (p : ℕ) :
    complexNormalRationalLocalCohomology p (2 * p) ≅ ModuleCat.of ℚ ℚ :=
  (complexNormalRationalTopCohomologyEquiv p).toModuleIso

/-- All other relative cohomology degrees vanish, including the low degrees. -/
theorem complexNormalRationalLocalCohomology_isZero (p n : ℕ) (hn : n ≠ 2 * p) :
    IsZero (complexNormalRationalLocalCohomology p n) := by
  have hH := RationalRelativeHomology.Cycles.complexNormalRationalLocalHomology_isZero p n hn
  have hdual := DualNormalization.Cycles.dual_isZero_of_isZero hH
  exact hdual.of_iso
    (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
      ({0}ᶜ : Set (Fin p → ℂ)) n).toModuleIso

/-- The distinguished local rational class is the inverse image of one under
the genuine evaluation normalization. -/
def complexNormalRationalDualClass (p : ℕ) :
    complexNormalRationalLocalCohomology p (2 * p) :=
  (complexNormalRationalTopCohomologyEquiv p).symm 1

@[simp]
theorem complexNormalRationalDualClass_normalization (p : ℕ) :
    complexNormalRationalTopCohomologyEquiv p (complexNormalRationalDualClass p) = 1 :=
  (complexNormalRationalTopCohomologyEquiv p).apply_symm_apply 1

/-- The class evaluates to one on the specified rational local homology generator. -/
theorem complexNormalRationalDualClass_evaluation (p : ℕ) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
      ({0}ᶜ : Set (Fin p → ℂ)) (2 * p) (complexNormalRationalDualClass p)
        (complexNormalRationalTopHomologyGenerator p) = 1 :=
  complexNormalRationalDualClass_normalization p

/-- Its full evaluation functional is the actual normalized local homology coordinate. -/
theorem complexNormalRationalDualClass_functional (p : ℕ) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
      ({0}ᶜ : Set (Fin p → ℂ)) (2 * p) (complexNormalRationalDualClass p) =
        (complexNormalRationalTopHomologyEquiv p).toLinearMap := by
  apply (DualNormalization.Cycles.dualNormalizationEquiv (complexNormalRationalTopHomologyEquiv p)).injective
  rw [DualNormalization.Cycles.dualNormalizationEquiv_toLinearMap]
  exact complexNormalRationalDualClass_normalization p

/-- Evaluation one uniquely characterizes the normalized local rational class. -/
theorem complexNormalRationalDualClass_unique (p : ℕ)
    (a : complexNormalRationalLocalCohomology p (2 * p))
    (ha : RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
      ({0}ᶜ : Set (Fin p → ℂ)) (2 * p) a
        (complexNormalRationalTopHomologyGenerator p) = 1) :
    a = complexNormalRationalDualClass p := by
  apply (complexNormalRationalTopCohomologyEquiv p).injective
  exact ha.trans (complexNormalRationalDualClass_normalization p).symm

theorem complexNormalRationalDualClass_ne_zero (p : ℕ) :
    complexNormalRationalDualClass p ≠ 0 := by
  intro h
  have hn := complexNormalRationalDualClass_normalization p
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- Every top-degree local rational class is a unique rational multiple of
the normalized dual class. -/
theorem complexNormalRationalDualClass_generates (p : ℕ)
    (a : complexNormalRationalLocalCohomology p (2 * p)) :
    ∃! q : ℚ, q • complexNormalRationalDualClass p = a := by
  have hnorm (q : ℚ) :
      complexNormalRationalTopCohomologyEquiv p (q • complexNormalRationalDualClass p) = q := by
    rw [map_smul, complexNormalRationalDualClass_normalization]
    exact mul_one q
  refine ⟨complexNormalRationalTopCohomologyEquiv p a, ?_, ?_⟩
  · apply (complexNormalRationalTopCohomologyEquiv p).injective
    exact hnorm _
  · intro q hq
    calc
      q = complexNormalRationalTopCohomologyEquiv p
          (q • complexNormalRationalDualClass p) := (hnorm q).symm
      _ = complexNormalRationalTopCohomologyEquiv p a :=
        congrArg (complexNormalRationalTopCohomologyEquiv p) hq

/-- The top relative cohomology group is nonzero. -/
theorem complexNormalRationalTopCohomology_not_isZero (p : ℕ) :
    ¬ IsZero (complexNormalRationalLocalCohomology p (2 * p)) := by
  intro h
  let : Subsingleton (complexNormalRationalLocalCohomology p (2 * p)) :=
    ModuleCat.subsingleton_of_isZero h
  exact complexNormalRationalDualClass_ne_zero p (Subsingleton.elim _ _)

/-- Precise rational local purity in every degree, with no omitted zero-dimensional case. -/
theorem complexNormalRationalLocalCohomology_isZero_iff (p n : ℕ) :
    IsZero (complexNormalRationalLocalCohomology p n) ↔ n ≠ 2 * p := by
  constructor
  · intro h hn
    subst n
    exact complexNormalRationalTopCohomology_not_isZero p h
  · exact complexNormalRationalLocalCohomology_isZero p n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity.Cycles
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity -/

/-! # Finite Complex Local Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles

noncomputable section

/-!
# Local rational purity for finite-dimensional complex vector spaces

The actual punctured-space relative cochain complexes are transported along
continuous complex-linear equivalences. A genuine coordinate equivalence with
the standard finite complex vector space then gives local purity and a
normalized rational class. Coordinate independence is proved separately.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality.Cohomology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A continuous complex-linear equivalence as an actual topological isomorphism. -/
def complexLinearTopIso (e : E ≃L[ℂ] F) : TopCat.of E ≅ TopCat.of F :=
  TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of F) e.toHomeomorph

theorem complexLinearEquiv_mapsTo_puncture (e : E ≃L[ℂ] F) :
    Set.MapsTo e ({0}ᶜ : Set E) ({0}ᶜ : Set F) := by
  intro x hx
  change x ≠ 0 at hx
  change e x ≠ 0
  exact fun he => hx (e.injective (he.trans e.map_zero.symm))

/-- Actual cochain pullback gives a contravariant isomorphism of punctured
relative cochains under a complex-linear homeomorphism. -/
def complexLinearLocalCochainIso (e : E ≃L[ℂ] F) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of E) ({0}ᶜ : Set E) where
  hom := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
    (complexLinearTopIso e).hom (complexLinearEquiv_mapsTo_puncture e)
  inv := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
    (complexLinearTopIso e).inv (complexLinearEquiv_mapsTo_puncture e.symm)
  hom_inv_id := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id (ModuleCat.of ℚ ℚ)
    (complexLinearTopIso e).inv (complexLinearTopIso e).hom
    (complexLinearEquiv_mapsTo_puncture e.symm) (complexLinearEquiv_mapsTo_puncture e)
    (complexLinearTopIso e).inv_hom_id
  inv_hom_id := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id (ModuleCat.of ℚ ℚ)
    (complexLinearTopIso e).hom (complexLinearTopIso e).inv
    (complexLinearEquiv_mapsTo_puncture e) (complexLinearEquiv_mapsTo_puncture e.symm)
    (complexLinearTopIso e).hom_inv_id

/-- The induced isomorphism is on the genuine rational relative cohomology. -/
def complexLinearLocalCohomologyIso (e : E ≃L[ℂ] F) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of E) ({0}ᶜ : Set E) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
    (complexLinearLocalCochainIso e)

@[simp]
theorem complexLinearLocalCohomologyIso_hom (e : E ≃L[ℂ] F) (n : ℕ) :
    (complexLinearLocalCohomologyIso e n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (complexLinearTopIso e).hom (complexLinearEquiv_mapsTo_puncture e) n :=
  rfl

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- An actual continuous linear coordinate system in the full complex dimension. -/
def finiteComplexCoordinates : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm

/-- Rational local cohomology at zero, with the actual punctured complement. -/
abbrev finiteComplexLocalCohomology (n : ℕ) : ModuleCat ℚ :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of E) ({0}ᶜ : Set E) n

/-- Actual coordinates identify local cohomology with the standard normal model. -/
def finiteComplexLocalCohomologyIso (n : ℕ) :
    finiteComplexLocalCohomology E n ≅
      RationalLocalPurity.Cycles.complexNormalRationalLocalCohomology (Module.finrank ℂ E) n :=
  (complexLinearLocalCohomologyIso (finiteComplexCoordinates E) n).symm

/-- Top local rational cohomology is one-dimensional with its specified
normalization transported by an actual complex coordinate map. -/
def finiteComplexTopCohomologyIso :
    finiteComplexLocalCohomology E (2 * Module.finrank ℂ E) ≅ ModuleCat.of ℚ ℚ :=
  finiteComplexLocalCohomologyIso E (2 * Module.finrank ℂ E) ≪≫
    RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso (Module.finrank ℂ E)

/-- Local rational cohomology vanishes in every other degree, including the
zero-dimensional case with its genuine punctured pair. -/
theorem finiteComplexLocalCohomology_isZero (n : ℕ) (hn : n ≠ 2 * Module.finrank ℂ E) :
    IsZero (finiteComplexLocalCohomology E n) :=
  (RationalLocalPurity.Cycles.complexNormalRationalLocalCohomology_isZero (Module.finrank ℂ E) n hn).of_iso
    (finiteComplexLocalCohomologyIso E n)

/-- The normalized local rational class. -/
def finiteComplexLocalClass : finiteComplexLocalCohomology E (2 * Module.finrank ℂ E) :=
  (finiteComplexTopCohomologyIso E).inv 1

@[simp]
theorem finiteComplexLocalClass_normalization :
    (finiteComplexTopCohomologyIso E).hom (finiteComplexLocalClass E) = 1 := by
  exact (finiteComplexTopCohomologyIso E).toLinearEquiv.apply_symm_apply 1

theorem finiteComplexLocalClass_ne_zero : finiteComplexLocalClass E ≠ 0 := by
  intro h
  have heq := finiteComplexLocalClass_normalization E
  rw [h, map_zero] at heq
  exact zero_ne_one heq

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity -/

/-! # Immersion Local Purity -/

namespace OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

noncomputable section

/-!
# Local relative cohomology of genuine embedded normal pairs

The coordinate maps in this file are actual homeomorphisms of pairs. Their
pullbacks identify the kernel-defined relative singular cochain complexes.
Normal neighborhoods are constructed from genuine manifold immersions and
topological embeddings; their removed subspaces are the complements of the
full embedded image.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] (A : ModuleCat.{0} R)

/-- A genuine homeomorphism of pairs induces an isomorphism of the actual
relative singular cochain kernels, by pullback in both directions. -/
def relativePairHomeomorphCochainIso {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (S : Set X) (T : Set Y) (h : ∀ x, x ∈ S ↔ e x ∈ T) :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains A Y T ≅ Cohomology.Singular.RelativeSequence.relativeSingularCochains A X S := by
  let f : X ⟶ Y := (TopCat.isoOfHomeo e).hom
  let g : Y ⟶ X := (TopCat.isoOfHomeo e).inv
  have hf : Set.MapsTo f S T := fun x hx => (h x).mp hx
  have hg : Set.MapsTo g T S := by
    intro y hy
    apply (h (e.symm y)).mpr
    simpa only [e.apply_symm_apply] using hy
  exact {
    hom := Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap A f hf
    inv := Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap A g hg
    hom_inv_id := Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id A g f hg hf
      (TopCat.isoOfHomeo e).inv_hom_id
    inv_hom_id := Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id A f g hf hg
      (TopCat.isoOfHomeo e).hom_inv_id }

@[simp]
theorem relativePairHomeomorphCochainIso_hom {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (S : Set X) (T : Set Y) (h : ∀ x, x ∈ S ↔ e x ∈ T) :
    (relativePairHomeomorphCochainIso A e S T h).hom =
      Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap A (TopCat.isoOfHomeo e).hom
        (fun x hx => (h x).mp hx) := rfl

/-- The corresponding genuine relative-cohomology isomorphism. -/
def relativePairHomeomorphCohomologyIso {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (S : Set X) (T : Set Y) (h : ∀ x, x ∈ S ↔ e x ∈ T) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology A Y T n ≅ Cohomology.Singular.RelativeSequence.relativeSingularCohomology A X S n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapIso
    (relativePairHomeomorphCochainIso A e S T h)

@[simp]
theorem relativePairHomeomorphCohomologyIso_hom {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (S : Set X) (T : Set Y) (h : ∀ x, x ∈ S ↔ e x ∈ T) (n : ℕ) :
    (relativePairHomeomorphCohomologyIso A e S T h n).hom =
      Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap A (TopCat.isoOfHomeo e).hom
        (fun x hx => (h x).mp hx) n := rfl

end

namespace Analytic.ImmersionNormalPair

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {M N E F : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

/-- The removed subset is exactly the complement of the full embedded image
inside the genuine coordinate neighborhood. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeComplement : Set P.neighborhood :=
  {y | y.val ∉ Set.range f}

variable {R : Type} [Ring R] (A : ModuleCat.{0} R)

/-- Actual relative singular cohomology with support in the embedded image,
computed in this actual ambient coordinate neighborhood. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomology (n : ℕ) : ModuleCat.{0} R :=
  Cohomology.Singular.RelativeSequence.relativeSingularCohomology A (TopCat.of P.neighborhood) P.relativeComplement n

/-- The actual normal coordinate, as a continuous map into the full normal
vector space. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCoordinate : TopCat.of P.neighborhood ⟶ TopCat.of F :=
  TopCat.ofHom ⟨fun y => (P.homeomorph y).2.val,
    continuous_subtype_val.comp (continuous_snd.comp P.homeomorph.continuous)⟩

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCoordinate_apply (y : P.neighborhood) :
    P.normalCoordinate y = (P.ambientChart y.val).2 := rfl

/-- The coordinate map factors through the product of balls by its actual
normal projection and the actual open-ball inclusion. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCoordinate_eq :
    P.normalCoordinate = (TopCat.isoOfHomeo P.homeomorph).hom ≫
      AlgebraicGeometry.CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection (Metric.ball (0 : E) P.radius)
        (Metric.ball (0 : F) P.radius) ≫
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of F) (Metric.ball (0 : F) P.radius) := rfl

/-- The normal coordinate sends the actual removed subspace into the
punctured normal vector space. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCoordinate_mapsTo :
    Set.MapsTo P.normalCoordinate P.relativeComplement ({0}ᶜ : Set F) :=
  fun y hy => (P.mem_complement_iff y).mp hy

/-- Pullback of relative cochains along the actual normal coordinate. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCochainPullback :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains A (TopCat.of F) ({0}ᶜ : Set F) ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCochains A (TopCat.of P.neighborhood) P.relativeComplement :=
  Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap A P.normalCoordinate P.normalCoordinate_mapsTo

/-- The canonical relative-cohomology pullback whose invertibility expresses
local purity in this coordinate neighborhood. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology A (TopCat.of F) ({0}ᶜ : Set F) n ⟶
      P.relativeCohomology A n :=
  Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap A P.normalCoordinate P.normalCoordinate_mapsTo n

/-- The exact pair condition for the normal-coordinate homeomorphism. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.homeomorph_mem_relativeComplement (y : P.neighborhood) :
    y ∈ P.relativeComplement ↔
      P.homeomorph y ∈ AlgebraicGeometry.CycleClass.Geometric.NormalProductPair.Cycles.normalProductComplement
        (Metric.ball (0 : E) P.radius) (Metric.ball (0 : F) P.radius)
        ⟨0, Metric.mem_ball_self P.radius_pos⟩ := by
  change y.val ∉ Set.range f ↔
    (P.homeomorph y).2 ≠ ⟨0, Metric.mem_ball_self P.radius_pos⟩
  rw [P.mem_complement_iff y]
  constructor
  · intro hy hzero
    exact hy (congrArg Subtype.val hzero)
  · intro hy hzero
    exact hy (Subtype.ext hzero)

/-- Normal coordinates identify the actual relative cochain complexes. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.ballPairCochainIso :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains A
        (TopCat.of (Metric.ball (0 : E) P.radius × Metric.ball (0 : F) P.radius))
        (AlgebraicGeometry.CycleClass.Geometric.NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) P.radius)
          (Metric.ball (0 : F) P.radius) ⟨0, Metric.mem_ball_self P.radius_pos⟩) ≅
      Cohomology.Singular.RelativeSequence.relativeSingularCochains A (TopCat.of P.neighborhood) P.relativeComplement :=
  relativePairHomeomorphCochainIso A P.homeomorph _ _
    P.homeomorph_mem_relativeComplement

/-- The corresponding relative-cohomology comparison is the actual
pullback along the normal-coordinate homeomorphism. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.ballPairCohomologyIso (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology A
        (TopCat.of (Metric.ball (0 : E) P.radius × Metric.ball (0 : F) P.radius))
        (AlgebraicGeometry.CycleClass.Geometric.NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) P.radius)
          (Metric.ball (0 : F) P.radius) ⟨0, Metric.mem_ball_self P.radius_pos⟩) n ≅
      P.relativeCohomology A n :=
  relativePairHomeomorphCohomologyIso A P.homeomorph _ _
    P.homeomorph_mem_relativeComplement n

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.ballPairCohomologyIso_hom (n : ℕ) :
    (P.ballPairCohomologyIso A n).hom =
      Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap A (TopCat.isoOfHomeo P.homeomorph).hom
        (fun y hy => (P.homeomorph_mem_relativeComplement y).mp hy) n := rfl

/-- Shrinking an actual normal neighborhood while retaining its chart does
not change the underlying normal-coordinate map. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCoordinate_comp_neighborhoodInclusion (Q : AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of N)) hQP ≫ P.normalCoordinate = Q.normalCoordinate := by
  ext y
  change (P.ambientChart y.val).2 = (Q.ambientChart y.val).2
  rw [hchart]

/-- The normal-coordinate pullback commutes with the actual relative
cohomology restriction to a smaller neighborhood with the same chart. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap_restrict (Q : AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart)
    (n : ℕ) :
    P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n ≫
        AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f) n =
      Q.normalCohomologyMap (ModuleCat.of ℚ ℚ) n := by
  change Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) P.normalCoordinate
      P.normalCoordinate_mapsTo n ≫
    Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of N)) hQP) (fun _ hx => hx) n = _
  rw [Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  unfold AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap
  congr 1
  exact P.normalCoordinate_comp_neighborhoodInclusion Q hQP hchart

variable [NormedSpace ℝ E]

/-- Actual normal projection identifies relative rational cohomology of the
embedded-support neighborhood with punctured-normal cohomology. Its two steps
are normal-ball excision and the actual pair-coordinate homeomorphism. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyIso (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) n ≅
      P.relativeCohomology (ModuleCat.of ℚ ℚ) n :=
  AlgebraicGeometry.CycleClass.Geometric.NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyIso E F P.radius P.radius P.radius_pos P.radius_pos n ≪≫
    P.ballPairCohomologyIso (ModuleCat.of ℚ ℚ) n

/-- The comparison is precisely pullback along the actual normal coordinate. -/
@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyIso_hom (n : ℕ) :
    (P.relativeCohomologyIso n).hom = P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n := by
  change (AlgebraicGeometry.CycleClass.Geometric.NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyIso E F P.radius P.radius
      P.radius_pos P.radius_pos n).hom ≫
    (P.ballPairCohomologyIso (ModuleCat.of ℚ ℚ) n).hom = _
  rw [AlgebraicGeometry.CycleClass.Geometric.NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyIso_hom, AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.ballPairCohomologyIso_hom]
  unfold AlgebraicGeometry.CycleClass.Geometric.NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyMap AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap
  rw [Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap_isIso (n : ℕ) :
    IsIso (P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n) := by
  rw [← P.relativeCohomologyIso_hom n]
  infer_instance

variable [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- The actual top rational cohomology of the local support pair is one
dimensional, normalized by the established complex normal-space calculation. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalTopCohomologyIso :
    P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * Module.finrank ℂ F) ≅ ModuleCat.of ℚ ℚ :=
  (P.relativeCohomologyIso (2 * Module.finrank ℂ F)).symm ≪≫
    AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexTopCohomologyIso F

/-- The chart-normalized local class is the inverse image of one under the
proved top cohomology isomorphism. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass : P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * Module.finrank ℂ F) :=
  P.rationalTopCohomologyIso.inv 1

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_normalization : P.rationalTopCohomologyIso.hom P.rationalClass = 1 :=
  P.rationalTopCohomologyIso.toLinearEquiv.apply_symm_apply 1

/-- This class is literally the pullback of the normalized complex normal
class along the actual second coordinate. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_eq_pullback :
    P.rationalClass = P.normalCohomologyMap (ModuleCat.of ℚ ℚ)
      (2 * Module.finrank ℂ F) (AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass F) := by
  rw [← P.relativeCohomologyIso_hom]
  rfl

theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_ne_zero : P.rationalClass ≠ 0 := by
  intro h
  have hn := P.rationalClass_normalization
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- Normalization one uniquely specifies the local class in this chart. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_unique
    (a : P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * Module.finrank ℂ F))
    (ha : P.rationalTopCohomologyIso.hom a = 1) : a = P.rationalClass := by
  apply P.rationalTopCohomologyIso.toLinearEquiv.injective
  exact ha.trans P.rationalClass_normalization.symm

/-- Every top local class is a unique rational multiple of the normalized class. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_generates
    (a : P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * Module.finrank ℂ F)) :
    ∃! q : ℚ, q • P.rationalClass = a := by
  let e := P.rationalTopCohomologyIso.toLinearEquiv
  have hnorm (q : ℚ) : e (q • P.rationalClass) = q := by
    rw [map_smul]
    change q • P.rationalTopCohomologyIso.hom P.rationalClass = q
    rw [P.rationalClass_normalization]
    exact mul_one q
  refine ⟨e a, ?_, ?_⟩
  · apply e.injective
    exact hnorm _
  · intro q hq
    exact (hnorm q).symm.trans (congrArg e hq)

/-- All non-normal degrees vanish, for the actual embedded-support pair. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomology_isZero (n : ℕ) (hn : n ≠ 2 * Module.finrank ℂ F) :
    IsZero (P.relativeCohomology (ModuleCat.of ℚ ℚ) n) :=
  (AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology_isZero F n hn).of_iso (P.relativeCohomologyIso n).symm

/-- In particular local support cohomology vanishes below real codimension. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomology_isZero_of_lt (n : ℕ) (hn : n < 2 * Module.finrank ℂ F) :
    IsZero (P.relativeCohomology (ModuleCat.of ℚ ℚ) n) :=
  P.relativeCohomology_isZero n (Nat.ne_of_lt hn)

theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomology_isZero_iff (n : ℕ) :
    IsZero (P.relativeCohomology (ModuleCat.of ℚ ℚ) n) ↔ n ≠ 2 * Module.finrank ℂ F := by
  refine ⟨?_, P.relativeCohomology_isZero n⟩
  intro hz hn
  subst n
  let : Subsingleton (P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * Module.finrank ℂ F)) :=
    ModuleCat.subsingleton_of_isZero hz
  exact P.rationalClass_ne_zero (Subsingleton.elim _ _)

/-- The normalized class restricts to the normalized class on every smaller
normal neighborhood with the same actual chart. This is local compatibility;
no compatibility between different normal charts is assumed. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_restrict (Q : AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart) :
    AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f)
        (2 * Module.finrank ℂ F) P.rationalClass = Q.rationalClass := by
  rw [P.rationalClass_eq_pullback, Q.rationalClass_eq_pullback]
  exact ConcreteCategory.congr_hom
    (P.normalCohomologyMap_restrict Q hQP hchart (2 * Module.finrank ℂ F))
      (AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass F)

end Analytic.ImmersionNormalPair

end

end OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt -/

/-! # Stalk Exactness At -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt

noncomputable section

/-!
# Local primitives imply exactness of actual stalk complexes

The stalks here are mathlib's colimits over open neighborhoods. A closed germ
first has a representative whose differential becomes zero on a smaller
neighborhood. An actual local primitive of that representative then supplies
a primitive germ. The local primitive premise is explicit and is not asserted
for any particular geometric complex by this file.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

universe u

variable {R : Type} [Ring R] {X : TopCat.{u}}

/-- Module filtered colimits have the usual underlying filtered colimit of groups,
including when the carrier universe is larger than the scalar universe. -/
local instance stalkModulesForget₂PreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (ModuleCat.{u,0} R) AddCommGrpCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone
          (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ (ModuleCat.{u,0} R) AddCommGrpCat.{u})) }

/-- The underlying-set functor preserves the filtered colimits defining stalks. -/
local instance stalkModulesForgetPreservesFilteredColimits :
    PreservesFilteredColimits (forget (ModuleCat.{u,0} R)) :=
  Limits.comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{u,0} R) AddCommGrpCat.{u}) (forget AddCommGrpCat.{u})

/-- A section has zero germ exactly when it vanishes on a smaller neighborhood. -/
theorem germ_eq_zero_iff_locally_zero (F : X.Presheaf (ModuleCat.{u,0} R))
    (x : X) (U : Opens X) (hxU : x ∈ U) (s : F.obj (op U)) :
    F.germ U x hxU s = 0 ↔
      ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U), F.map i.op s = 0 := by
  constructor
  · intro hs
    have hzero : F.germ U x hxU s = F.germ U x hxU 0 := by
      simpa only [map_zero] using hs
    obtain ⟨V, hxV, i, j, hij⟩ := F.germ_eq x hxU hxU s 0 hzero
    exact ⟨V, hxV, i, by simpa only [map_zero] using hij⟩
  · rintro ⟨V, hxV, i, hs⟩
    rw [← F.germ_res_apply i x hxV s, hs, map_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An explicit local primitive condition for a short complex of module
presheaves implies exactness after taking the actual stalk at `x`. -/
theorem stalk_exact_of_locally_exact
    (S : ShortComplex (X.Presheaf (ModuleCat.{u,0} R))) (x : X)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U) (s : S.X₂.obj (op U)),
      S.g.app (op U) s = 0 →
        ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U) (t : S.X₁.obj (op V)),
          S.f.app (op V) t = S.X₂.map i.op s) :
    (S.map (stalkFunctor (ModuleCat.{u,0} R) x)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  change (stalkFunctor (ModuleCat.{u,0} R) x).map S.g z = 0 at hz
  obtain ⟨U, hxU, s, rfl⟩ := S.X₂.exists_germ_eq z
  rw [stalkFunctor_map_germ_apply] at hz
  obtain ⟨V, hxV, i, hi⟩ :=
    (germ_eq_zero_iff_locally_zero S.X₃ x U hxU (S.g.app (op U) s)).mp hz
  have hclosed : S.g.app (op V) (S.X₂.map i.op s) = 0 := by
    have hnat := ConcreteCategory.congr_hom (S.g.naturality i.op) s
    exact hnat.trans hi
  obtain ⟨W, hxW, j, t, ht⟩ := hlocal V hxV (S.X₂.map i.op s) hclosed
  refine ⟨S.X₁.germ W x hxW t, ?_⟩
  change (stalkFunctor (ModuleCat.{u,0} R) x).map S.f (S.X₁.germ W x hxW t) =
    S.X₂.germ U x hxU s
  calc
    _ = S.X₂.germ W x hxW (S.f.app (op W) t) :=
      stalkFunctor_map_germ_apply W x hxW S.f t
    _ = S.X₂.germ W x hxW (S.X₂.map j.op (S.X₂.map i.op s)) :=
      congrArg (S.X₂.germ W x hxW) ht
    _ = S.X₂.germ V x (j.le hxW) (S.X₂.map i.op s) :=
      S.X₂.germ_res_apply j x hxW _
    _ = S.X₂.germ U x hxU s := S.X₂.germ_res_apply i x (j.le hxW) s

/-- A cochain complex of module presheaves has exact stalks in degree `n+1`
whenever each closed degree-`n+1` section has an actual local degree-`n` primitive. -/
theorem stalkComplex_exactAt_succ_of_local_primitives
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ) (x : X) (n : ℕ)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U) (s : (K.X (n + 1)).obj (op U)),
      (K.d (n + 1) (n + 2)).app (op U) s = 0 →
        ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U) (t : (K.X n).obj (op V)),
          (K.d n (n + 1)).app (op V) t = (K.X (n + 1)).map i.op s) :
    (((stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      K).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
    ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl))
    ((ComplexShape.up ℕ).next_eq'
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl))).2
  exact stalk_exact_of_locally_exact (K.sc' n (n + 1) (n + 2)) x hlocal

end

end OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.StalkRestrictionIso -/

/-! # Stalk Restriction Iso -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.StalkRestrictionIso

noncomputable section

/-!
# A germ isomorphism from invertible restrictions on a neighborhood basis

For the actual filtered-colimit stalk of a module presheaf, the germ map from
a fixed neighborhood is an isomorphism whenever restriction from that
neighborhood is invertible on arbitrarily small neighborhoods of the point.
No sheaf condition or additional description of the stalk is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

universe u

variable {R : Type} [Ring R] {X : TopCat.{u}}

attribute [local instance] StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

/-- If restrictions from a fixed neighborhood are injective on arbitrarily
small neighborhoods of a point, its actual germ map is injective. -/
theorem germ_injective_of_cofinal_restrictions
    (F : X.Presheaf (ModuleCat.{u,0} R)) (x : X) (V : Opens X) (hxV : x ∈ V)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (W : Opens X) (_hxW : x ∈ W) (hWV : W ≤ V) (_hWU : W ≤ U),
        Function.Injective (F.map (homOfLE hWV).op)) :
    Function.Injective (F.germ V x hxV) := by
  apply (injective_iff_map_eq_zero _).2
  intro s hs
  obtain ⟨U, hxU, i, hi⟩ := (StalkExactnessAt.germ_eq_zero_iff_locally_zero F x V hxV s).mp hs
  obtain ⟨W, _hxW, hWV, hWU, hinj⟩ := hlocal U hxU
  apply hinj
  rw [map_zero]
  calc
    F.map (homOfLE hWV).op s =
        F.map (homOfLE hWU).op (F.map i.op s) := by
      have hcomp : i.op ≫ (homOfLE hWU).op = (homOfLE hWV).op :=
        Subsingleton.elim _ _
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, hcomp]
    _ = 0 := by rw [hi, map_zero]

/-- If restrictions from a fixed neighborhood are surjective on arbitrarily
small neighborhoods of a point, every actual germ has a representative on it. -/
theorem germ_surjective_of_cofinal_restrictions
    (F : X.Presheaf (ModuleCat.{u,0} R)) (x : X) (V : Opens X) (hxV : x ∈ V)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (W : Opens X) (_hxW : x ∈ W) (hWV : W ≤ V) (_hWU : W ≤ U),
        Function.Surjective (F.map (homOfLE hWV).op)) :
    Function.Surjective (F.germ V x hxV) := by
  intro z
  obtain ⟨U, hxU, s, rfl⟩ := F.exists_germ_eq z
  obtain ⟨W, hxW, hWV, hWU, hsurj⟩ := hlocal U hxU
  obtain ⟨t, ht⟩ := hsurj (F.map (homOfLE hWU).op s)
  refine ⟨t, ?_⟩
  calc
    F.germ V x hxV t = F.germ W x hxW (F.map (homOfLE hWV).op t) :=
      (F.germ_res_apply (homOfLE hWV) x hxW t).symm
    _ = F.germ W x hxW (F.map (homOfLE hWU).op s) :=
      congrArg (F.germ W x hxW) ht
    _ = F.germ U x hxU s := F.germ_res_apply (homOfLE hWU) x hxW s

/-- The actual germ map is an isomorphism if restriction from its fixed
neighborhood is an isomorphism on arbitrarily small neighborhoods of the point. -/
theorem germ_isIso_of_cofinal_restrictions
    (F : X.Presheaf (ModuleCat.{u,0} R)) (x : X) (V : Opens X) (hxV : x ∈ V)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (W : Opens X) (_hxW : x ∈ W) (hWV : W ≤ V) (_hWU : W ≤ U),
        IsIso (F.map (homOfLE hWV).op)) :
    IsIso (F.germ V x hxV) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply germ_injective_of_cofinal_restrictions F x V hxV
    intro U hxU
    obtain ⟨W, hxW, hWV, hWU, h⟩ := hlocal U hxU
    let := h
    exact ⟨W, hxW, hWV, hWU,
      (ConcreteCategory.bijective_of_isIso (F.map (homOfLE hWV).op)).1⟩
  · apply germ_surjective_of_cofinal_restrictions F x V hxV
    intro U hxU
    obtain ⟨W, hxW, hWV, hWU, h⟩ := hlocal U hxU
    let := h
    exact ⟨W, hxW, hWV, hWU,
      (ConcreteCategory.bijective_of_isIso (F.map (homOfLE hWV).op)).2⟩

end

end OAI.AlgebraicTopology.Cohomology.Singular.StalkRestrictionIso
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.StalkRestrictionIso"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalChartPurity -/

/-! # Normal Chart Purity -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Local purity at the actual relative-cohomology stalk

A fixed genuine normal neighborhood computes the stalk of relative
cohomology. Its smaller concentric normal neighborhoods form a cofinal
system, and all the actual restriction maps in that system are invertible.
This proves the stalk comparison without assuming that arbitrary
intersections of normal neighborhoods have product shape.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf OAI.AlgebraicTopology.Cohomology.Singular.StalkRestrictionIso OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {M N E F : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

/-- The genuine normal neighborhood as an object of the open-set category. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.openNeighborhood : Opens (TopCat.of N) :=
  ⟨P.neighborhood, P.isOpen_neighborhood⟩

/-- Actual restriction between normal neighborhoods agrees with the map
of the genuine relative-cohomology presheaf. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyPresheaf_restrict (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ n).map
        (homOfLE (show Q.openNeighborhood ≤ P.openNeighborhood from hQP)).op =
      CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f) n := rfl

/-- The genuine germ map from the cohomology of one normal neighborhood. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyGerm (n : ℕ) :
    P.relativeCohomology (ModuleCat.of ℚ ℚ) n ⟶
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ n).stalk (f x) :=
  (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ n).germ
    P.openNeighborhood (f x) P.point_mem_neighborhood

/-- Actual germs commute with the actual restriction of normal neighborhoods. -/
@[reassoc]
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyGerm_restrict (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (n : ℕ) :
    CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f) n ≫
        Q.relativeCohomologyGerm n = P.relativeCohomologyGerm n :=
  (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ n).germ_res
    (homOfLE (show Q.openNeighborhood ≤ P.openNeighborhood from hQP))
    (f x) Q.point_mem_neighborhood

variable [NormedSpace ℝ E]

/-- Restricting to a smaller neighborhood in the same actual normal chart
is an isomorphism in every degree. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalNeighborhoodRestriction_isIso (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart)
    (n : ℕ) :
    IsIso (CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f) n) := by
  have := P.normalCohomologyMap_isIso n
  have := Q.normalCohomologyMap_isIso n
  have : IsIso (P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n ≫
      CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f) n) := by
    rw [P.normalCohomologyMap_restrict Q hQP hchart n]
    infer_instance
  exact IsIso.of_isIso_comp_left (P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n) _

/-- A normal neighborhood computes the actual relative-cohomology stalk.
The proof uses cofinal smaller neighborhoods and actual germ representatives. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyGerm_isIso (n : ℕ) : IsIso (P.relativeCohomologyGerm n) := by
  apply AlgebraicTopology.Cohomology.Singular.StalkRestrictionIso.germ_isIso_of_cofinal_restrictions
  intro U hxU
  obtain ⟨r, hr, hle, hsub⟩ := P.exists_restrictRadius_subset (U : Set N)
    (U.isOpen.mem_nhds hxU)
  let Q := P.restrictRadius r hr hle
  have hQP : Q.neighborhood ⊆ P.neighborhood := P.restrictRadius_neighborhood_subset r hr hle
  refine ⟨Q.openNeighborhood, Q.point_mem_neighborhood, hQP, hsub, ?_⟩
  rw [P.relativeCohomologyPresheaf_restrict Q hQP n]
  exact P.normalNeighborhoodRestriction_isIso Q hQP rfl n

/-- The isomorphism is the actual germ map, not a chosen identification. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyGermIso (n : ℕ) :
    P.relativeCohomology (ModuleCat.of ℚ ℚ) n ≅
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ n).stalk (f x) := by
  have := P.relativeCohomologyGerm_isIso n
  exact asIso (P.relativeCohomologyGerm n)

@[simp]
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyGermIso_hom (n : ℕ) :
    (P.relativeCohomologyGermIso n).hom = P.relativeCohomologyGerm n := rfl

/-- The actual normal coordinate followed by the actual germ gives the
normal-model comparison with the relative-cohomology stalk. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalStalkCohomologyIso (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) n ≅
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ n).stalk (f x) :=
  P.relativeCohomologyIso n ≪≫ P.relativeCohomologyGermIso n

@[simp]
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalStalkCohomologyIso_hom (n : ℕ) :
    (P.normalStalkCohomologyIso n).hom =
      P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n ≫ P.relativeCohomologyGerm n := by
  simp only [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalStalkCohomologyIso, Iso.trans_hom, ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyIso_hom,
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyGermIso_hom]

/-- Shrinking the normal neighborhood while retaining the chart gives
exactly the same map into the stalk. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalStalkCohomologyIso_hom_eq (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart)
    (n : ℕ) :
    (P.normalStalkCohomologyIso n).hom = (Q.normalStalkCohomologyIso n).hom := by
  rw [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalStalkCohomologyIso_hom, ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalStalkCohomologyIso_hom,
    ← P.relativeCohomologyGerm_restrict Q hQP n, ← Category.assoc,
    P.normalCohomologyMap_restrict Q hQP hchart n]

variable [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- The stalk in the top normal degree is the actual one-dimensional
rational module, with normalization from the complex normal coordinates. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalStalkTopCohomologyIso :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ (2 * Module.finrank ℂ F)).stalk (f x) ≅ ModuleCat.of ℚ ℚ :=
  (P.normalStalkCohomologyIso (2 * Module.finrank ℂ F)).symm ≪≫
    CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexTopCohomologyIso F

include P in
/-- Genuine relative-cohomology stalks vanish outside the top normal degree. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyStalk_isZero (n : ℕ) (hn : n ≠ 2 * Module.finrank ℂ F) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ n).stalk (f x)) :=
  (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology_isZero F n hn).of_iso (P.normalStalkCohomologyIso n).symm

include P in
/-- In particular, every degree below the real normal dimension vanishes. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyStalk_isZero_of_lt (n : ℕ)
    (hn : n < 2 * Module.finrank ℂ F) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ n).stalk (f x)) :=
  P.relativeCohomologyStalk_isZero n (Nat.ne_of_lt hn)

end

end OAI.AlgebraicGeometry
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalChartPurity"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearLocalCohomology -/

/-! # Complex Linear Local Cohomology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearLocalCohomology.Cycles

noncomputable section

/-!
# Complex linear invariance of actual local cohomology

The proved path of invertible complex matrices acts on the entire vector
space and preserves its punctured complement at every time. It therefore
gives a homotopy of the actual pair `(ℂ^p, ℂ^p \ {0})`. The induced pullback
on genuine relative singular cohomology is the identity in every degree.
The construction includes `p = 0` and uses no orientation or purity theorem.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy.Cohomology
open scoped _root_.Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual ambient homotopy induced by the path of invertible matrices. -/
def complexMatrixAmbientHomotopy (A : Matrix ι ι ℂ) (hA : IsUnit A) :
    TopCat.Homotopy (𝟙 (TopCat.of (ι → ℂ)))
      (TopCat.ofHom (ComplexLinearPuncturedHomotopy.Cycles.complexMatrixMap A)) where
  toFun q := ComplexLinearHomotopy.Cycles.complexMatrixPath A hA q.1 *ᵥ q.2
  continuous_toFun :=
    ((ComplexLinearHomotopy.Cycles.complexMatrixPath A hA).continuous.comp continuous_fst).matrix_mulVec continuous_snd
  map_zero_left x := by simp
  map_one_left x := by simp [ComplexLinearPuncturedHomotopy.Cycles.complexMatrixMap]

/-- No nonzero vector reaches the puncture during the ambient homotopy. -/
theorem complexMatrixAmbientHomotopy_preservesPuncture
    (A : Matrix ι ι ℂ) (hA : IsUnit A) (t : unitInterval) :
    Set.MapsTo (fun x => complexMatrixAmbientHomotopy A hA (t, x))
      ({0}ᶜ : Set (ι → ℂ)) ({0}ᶜ : Set (ι → ℂ)) :=
  fun _ hx => PuncturedLinearHomotopy.Cycles.complexMatrix_mulVec_ne_zero _ (ComplexLinearHomotopy.Cycles.complexMatrixPath_isUnit A hA t) hx

/-- An invertible complex matrix induces the identity on actual local
cohomology, with any coefficient module and in every degree. -/
theorem complexMatrixLocalCohomologyMap_eq_id
    {R : Type} [Ring R] (M : ModuleCat.{0} R)
    (A : Matrix ι ι ℂ) (hA : IsUnit A) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (TopCat.ofHom (ComplexLinearPuncturedHomotopy.Cycles.complexMatrixMap A))
      (ComplexLinearPuncturedHomotopy.Cycles.complexMatrixMap_preservesPuncture A hA) n =
      𝟙 (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (ι → ℂ)) ({0}ᶜ : Set (ι → ℂ)) n) := by
  have h := RelativeCochainHomotopy.Cohomology.relativeSingularCohomologyMap_eq_of_homotopy M
    (A := ({0}ᶜ : Set (ι → ℂ))) (B := ({0}ᶜ : Set (ι → ℂ)))
    (fun _ hx => hx) (ComplexLinearPuncturedHomotopy.Cycles.complexMatrixMap_preservesPuncture A hA)
    (complexMatrixAmbientHomotopy A hA)
    (complexMatrixAmbientHomotopy_preservesPuncture A hA) n
  simpa only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id] using h.symm

theorem complexLinearMatrix_isUnit {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ)) :
    IsUnit (LinearMap.toMatrix' L.toLinearEquiv.toLinearMap) :=
  LinearMap.isUnit_toMatrix'_iff.mpr ((Module.End.isUnit_iff _).mpr L.bijective)

/-- The ambient homotopy ends at the given continuous complex-linear map
itself, using its actual matrix in the standard coordinates. -/
def complexLinearAmbientHomotopy {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ)) :
    TopCat.Homotopy (𝟙 (TopCat.of (Fin p → ℂ)))
      (TopCat.isoOfHomeo (X := TopCat.of (Fin p → ℂ))
        (Y := TopCat.of (Fin p → ℂ)) L.toHomeomorph).hom :=
  (complexMatrixAmbientHomotopy (LinearMap.toMatrix' L.toLinearEquiv.toLinearMap)
    (complexLinearMatrix_isUnit L)).cast rfl (by
      apply ContinuousMap.ext
      intro x
      exact LinearMap.toMatrix'_mulVec L.toLinearEquiv.toLinearMap x)

theorem complexLinearAmbientHomotopy_preservesPuncture {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ)) (t : unitInterval) :
    Set.MapsTo (fun x => complexLinearAmbientHomotopy L (t, x))
      ({0}ᶜ : Set (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) :=
  complexMatrixAmbientHomotopy_preservesPuncture
    (LinearMap.toMatrix' L.toLinearEquiv.toLinearMap) (complexLinearMatrix_isUnit L) t

/-- The identity theorem for the pullback induced by the actual continuous
complex-linear equivalence, with arbitrary coefficients. -/
theorem complexLinearLocalCohomologyMap_eq_id_withCoefficients
    {R : Type} [Ring R] (M : ModuleCat.{0} R) {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hL : Set.MapsTo L
      ({0}ᶜ : Set (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ))) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M
      (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
      (A := ({0}ᶜ : Set (Fin p → ℂ))) (B := ({0}ᶜ : Set (Fin p → ℂ)))
      (TopCat.isoOfHomeo (X := TopCat.of (Fin p → ℂ))
        (Y := TopCat.of (Fin p → ℂ)) L.toHomeomorph).hom hL n =
      𝟙 (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (Fin p → ℂ))
        ({0}ᶜ : Set (Fin p → ℂ)) n) := by
  have h := RelativeCochainHomotopy.Cohomology.relativeSingularCohomologyMap_eq_of_homotopy M
    (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
    (f := 𝟙 (TopCat.of (Fin p → ℂ)))
    (g := (TopCat.isoOfHomeo (X := TopCat.of (Fin p → ℂ))
      (Y := TopCat.of (Fin p → ℂ)) L.toHomeomorph).hom)
    (A := ({0}ᶜ : Set (Fin p → ℂ))) (B := ({0}ᶜ : Set (Fin p → ℂ)))
    (fun _ hx => hx) hL (complexLinearAmbientHomotopy L)
    (complexLinearAmbientHomotopy_preservesPuncture L) n
  simpa only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id] using h.symm

/-- In every degree, including in complex dimension zero, the actual rational
local cohomology pullback of an invertible complex-linear map is the identity. -/
theorem complexLinearLocalCohomologyMap_eq_id {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hL : Set.MapsTo L
      ({0}ᶜ : Set (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ))) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
      (A := ({0}ᶜ : Set (Fin p → ℂ))) (B := ({0}ᶜ : Set (Fin p → ℂ)))
      (TopCat.isoOfHomeo (X := TopCat.of (Fin p → ℂ))
        (Y := TopCat.of (Fin p → ℂ)) L.toHomeomorph).hom hL n =
      𝟙 (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin p → ℂ))
        ({0}ᶜ : Set (Fin p → ℂ)) n) :=
  complexLinearLocalCohomologyMap_eq_id_withCoefficients (ModuleCat.of ℚ ℚ) L hL n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearLocalCohomology.Cycles
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearLocalCohomology"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality -/

/-! # Complex Local Purity Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality

noncomputable section

/-!
# Coordinate independence of the normalized complex local class

Actual complex-linear coordinates induce the same pullback on local
cohomology because their transition automorphism is homotopic to the
identity as a map of the punctured pair. Consequently the normalized
finite-dimensional complex local class is independent of coordinates and
is natural under complex-linear equivalences. The final formula records
the required transport of cohomological degree explicitly.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

variable {E F G : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Actual local cohomology pullback is contravariant under composition
of continuous complex-linear equivalences. -/
theorem complexLinearLocalCohomologyIso_trans_hom
    (e : E ≃L[ℂ] F) (f : F ≃L[ℂ] G) (n : ℕ) :
    (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso (e.trans f) n).hom =
      (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso f n).hom ≫
        (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso e n).hom := by
  exact RelativeCochainFunctoriality.Cohomology.relativeSingularCohomologyMap_of_comp (ModuleCat.of ℚ ℚ)
    (FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom (FiniteComplexLocalPurity.Cycles.complexLinearTopIso f).hom
    (FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture e) (FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture f) n

/-- Two actual complex-linear coordinate systems have identical induced
pullback maps on local cohomology in every degree. -/
theorem complexLinearLocalCohomologyIso_hom_eq_of_coordinates {p : ℕ}
    (e f : E ≃L[ℂ] (Fin p → ℂ)) (n : ℕ) :
    (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso e n).hom =
      (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso f n).hom := by
  have hcoord : e.trans (e.symm.trans f) = f := by
    apply ContinuousLinearEquiv.ext
    funext x
    exact congrArg f (e.symm_apply_apply x)
  have hid : (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso (e.symm.trans f) n).hom = 𝟙 _ :=
    ComplexLinearLocalCohomology.Cycles.complexLinearLocalCohomologyMap_eq_id (e.symm.trans f)
      (FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture (e.symm.trans f)) n
  have h := complexLinearLocalCohomologyIso_trans_hom e (e.symm.trans f) n
  rw [hcoord, hid, Category.id_comp] at h
  exact h.symm

/-- The normalized local class transported by an actual coordinate map. -/
def complexCoordinateLocalClass {p : ℕ} (e : E ≃L[ℂ] (Fin p → ℂ)) :
    FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology E (2 * p) :=
  (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso e (2 * p)).hom
    ((RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso p).inv 1)

/-- The transported normalized class does not depend on its coordinates. -/
theorem complexCoordinateLocalClass_eq {p : ℕ}
    (e f : E ≃L[ℂ] (Fin p → ℂ)) :
    complexCoordinateLocalClass e = complexCoordinateLocalClass f := by
  exact ConcreteCategory.congr_hom
    (complexLinearLocalCohomologyIso_hom_eq_of_coordinates e f (2 * p))
      ((RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso p).inv 1)

/-- Pullback preserves the coordinate-normalized class for any actual
complex-linear equivalence and any coordinates in the same dimension. -/
theorem complexCoordinateLocalClass_naturality {p : ℕ}
    (e : E ≃L[ℂ] F) (cE : E ≃L[ℂ] (Fin p → ℂ)) (cF : F ≃L[ℂ] (Fin p → ℂ)) :
    (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso e (2 * p)).hom (complexCoordinateLocalClass cF) =
      complexCoordinateLocalClass cE := by
  have h := ConcreteCategory.congr_hom
    (complexLinearLocalCohomologyIso_trans_hom e cF (2 * p))
      ((RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso p).inv 1)
  exact h.symm.trans (complexCoordinateLocalClass_eq (e.trans cF) cE)

/-- Reindexing the coordinate dimension transports the actual class by
the corresponding equality of local cohomology objects. -/
theorem complexCoordinateLocalClass_cast {p q : ℕ} (h : p = q)
    (e : E ≃L[ℂ] (Fin p → ℂ)) :
    (eqToHom (congrArg (fun n => FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology E (2 * n)) h))
        (complexCoordinateLocalClass e) =
      complexCoordinateLocalClass
        (cast (congrArg (fun n => E ≃L[ℂ] (Fin n → ℂ)) h) e) := by
  subst q
  rfl

variable (E) [FiniteDimensional ℂ E]

/-- The previously constructed local class is exactly the coordinate
normalization for its chosen actual coordinates. -/
theorem finiteComplexLocalClass_eq_coordinate :
    FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass E = complexCoordinateLocalClass (FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates E) :=
  rfl

/-- Any actual complex coordinates in the full dimension give the
canonical local class. -/
theorem finiteComplexLocalClass_eq_of_coordinates
    (e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ)) :
    FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass E = complexCoordinateLocalClass e := by
  exact (finiteComplexLocalClass_eq_coordinate E).trans
    (complexCoordinateLocalClass_eq (FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates E) e)

variable {E} [FiniteDimensional ℂ F]

/-- The normalized local class is natural under actual complex-linear
equivalences, with the equality of complex dimensions transported explicitly. -/
theorem finiteComplexLocalClass_naturality (e : E ≃L[ℂ] F) :
    (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso e (2 * Module.finrank ℂ F)).hom
        (FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass F) =
      (eqToHom (congrArg (fun n => FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology E (2 * n))
        e.toLinearEquiv.finrank_eq)) (FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass E) := by
  rw [finiteComplexLocalClass_eq_coordinate F, finiteComplexLocalClass_eq_coordinate E,
    complexCoordinateLocalClass_cast e.toLinearEquiv.finrank_eq (FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates E)]
  exact complexCoordinateLocalClass_naturality e
    (cast (congrArg (fun n => E ≃L[ℂ] (Fin n → ℂ)) e.toLinearEquiv.finrank_eq)
      (FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates E)) (FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates F)

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin -/

/-! # Immersion Normal Fin -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin

noncomputable section

/-!
# The actual normal class in the explicit degree `2p`

For the normal space `Fin p → ℂ`, this file transports the existing normalized
class along the proved dimension equality. Coordinate independence then
identifies it with the standard normal generator, including when `p = 0`.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

/-- Identity coordinates give precisely the standard normalized rational
normal class. -/
theorem complexCoordinateLocalClass_refl (p : ℕ) :
    ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass (ContinuousLinearEquiv.refl ℂ (Fin p → ℂ)) =
      RationalLocalPurity.Cycles.complexNormalRationalDualClass p := by
  unfold ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass
  rw [FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso_hom]
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (Fin p → ℂ)))
    (fun _ hx => hx) (2 * p) ((RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso p).inv 1) = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id]
  rfl

/-- Explicit degree transport identifies the existing finite-dimensional
normal class with the standard class in degree `2p`. -/
theorem finiteComplexLocalClass_fin (p : ℕ) :
    (eqToHom (congrArg (fun n => FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology (Fin p → ℂ) (2 * n))
      (Module.finrank_fin_fun ℂ : Module.finrank ℂ (Fin p → ℂ) = p)))
        (FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass (Fin p → ℂ)) = RationalLocalPurity.Cycles.complexNormalRationalDualClass p := by
  rw [ComplexLocalPurityNaturality.Cycles.finiteComplexLocalClass_eq_coordinate]
  exact (ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass_cast (Module.finrank_fin_fun ℂ)
    (FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates (Fin p → ℂ))).trans
      ((ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass_eq _ (ContinuousLinearEquiv.refl ℂ (Fin p → ℂ))).trans
        (complexCoordinateLocalClass_refl p))

end Cycles

namespace Analytic.ImmersionNormalPair

open OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin.Cycles

variable {M N E : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : M → N} {x : M} {p : ℕ} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)

/-- The existing normal-pair class, transported only along the proved
identity `finrank ℂ (Fin p → ℂ) = p`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin : P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * p) :=
  (eqToHom (congrArg (fun n => P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * n))
    (Module.finrank_fin_fun ℂ : Module.finrank ℂ (Fin p → ℂ) = p))) P.rationalClass

omit [NormedSpace ℝ E] in
theorem normalCohomologyMap_degree_transport {a b : ℕ} (h : a = b)
    (c : FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology (Fin p → ℂ) (2 * a)) :
    (eqToHom (congrArg (fun n => P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * n)) h))
        (P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * a) c) =
      P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * b)
        ((eqToHom (congrArg (fun n => FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology (Fin p → ℂ) (2 * n)) h)) c) := by
  subst b
  rfl

/-- The explicit-degree class is the actual normal-coordinate pullback
of the established standard rational normal class. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_eq_normalPullback :
    P.rationalClassFin = P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p)
      (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) := by
  unfold ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin
  rw [P.rationalClass_eq_pullback,
    (normalCohomologyMap_degree_transport P) (Module.finrank_fin_fun ℂ),
    Cycles.finiteComplexLocalClass_fin]

/-- The explicit-degree class respects actual shrinking in one normal
coordinate chart. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_restrict (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart) :
    RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f) (2 * p)
      P.rationalClassFin = Q.rationalClassFin := by
  rw [P.rationalClassFin_eq_normalPullback, Q.rationalClassFin_eq_normalPullback]
  exact ConcreteCategory.congr_hom (P.normalCohomologyMap_restrict Q hQP hchart (2 * p))
    (RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

end Analytic.ImmersionNormalPair

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.DerivativePuncturedHomotopy -/

/-! # Derivative Punctured Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.DerivativePuncturedHomotopy.Cycles

noncomputable section

/-!
# A differentiable germ and its invertible derivative on a punctured ball

An invertible derivative controls the error relative to the derivative's own
norm. On a sufficiently small punctured ball, the straight line between the
translated map and its derivative consequently avoids zero. This constructs
the local topological homotopy needed for comparing nonlinear coordinate
changes with their linear derivatives. No local orientation class or excision
theorem is assumed.
-/

open Filter Set
open scoped _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative error is eventually at most half the derivative norm. -/
theorem eventually_derivative_remainder_small {f : E → F} (L : E ≃L[ℝ] F)
    (hf : HasFDerivAt f (L : E →L[ℝ] F) 0) :
    ∀ᶠ x in 𝓝 (0 : E), ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖ := by
  have h := (hf.isEquivalent_sub L.toHomeomorph.isInducing).isLittleO
  simpa only [Pi.sub_apply, sub_zero, ContinuousLinearEquiv.coe_coe] using
    h.bound (by norm_num : (0 : ℝ) < 1 / 2)

/-- A perturbation by at most half the norm stays away from zero throughout
the straight-line interpolation. -/
theorem straightLine_ne_zero_of_half_norm {u v : F} (hu : u ≠ 0)
    (herror : ‖v - u‖ ≤ (1 / 2 : ℝ) * ‖u‖) (t : unitInterval) :
    u + (t : ℝ) • (v - u) ≠ 0 := by
  intro hzero
  have hnorm : ‖u‖ = ‖(t : ℝ) • (v - u)‖ := by
    calc
      ‖u‖ = ‖-((t : ℝ) • (v - u))‖ := congrArg norm (eq_neg_of_add_eq_zero_left hzero)
      _ = ‖(t : ℝ) • (v - u)‖ := norm_neg _
  have hbound : ‖(t : ℝ) • (v - u)‖ ≤ (1 / 2 : ℝ) * ‖u‖ := by
    calc
      ‖(t : ℝ) • (v - u)‖ = (t : ℝ) * ‖v - u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
      _ ≤ ‖v - u‖ := mul_le_of_le_one_left (norm_nonneg _) t.property.2
      _ ≤ (1 / 2 : ℝ) * ‖u‖ := herror
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  linarith

/-- The actual punctured ball in a normed model space. -/
abbrev PuncturedBall (E : Type*) [NormedAddCommGroup E] (r : ℝ) :=
  {x : E // x ≠ 0 ∧ ‖x‖ < r}

/-- Restriction of an invertible linear derivative to a punctured ball. -/
def puncturedBallLinearMap (L : E ≃L[ℝ] F) (r : ℝ) :
    C(PuncturedBall E r, NormalSphere.Cycles.PuncturedNormal F) where
  toFun x := ⟨L x.1, by
    change L x.1 ≠ 0
    intro hx
    exact x.property.1 (L.injective (by simpa only [map_zero] using hx))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact L.continuous.comp continuous_subtype_val

/-- Restriction of the translated nonlinear map; the quantitative error
estimate proves its values avoid zero. -/
def puncturedBallTranslatedMap {f : E → F} (L : E ≃L[ℝ] F) (r : ℝ)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) :
    C(PuncturedBall E r, NormalSphere.Cycles.PuncturedNormal F) where
  toFun x := ⟨f x.1 - f 0, by
    change f x.1 - f 0 ≠ 0
    have hL : L x.1 ≠ 0 := by
      intro hx
      exact x.property.1 (L.injective (by simpa only [map_zero] using hx))
    simpa using straightLine_ne_zero_of_half_norm hL (he x.1 x.property.2)
      (1 : unitInterval)⟩
  continuous_toFun := by
    have hfc : Continuous (fun x : PuncturedBall E r => f x.1) := by
      apply hc.comp_continuous continuous_subtype_val
      intro x
      simpa only [Metric.mem_ball, dist_zero_right] using x.property.2
    exact (hfc.sub continuous_const).subtype_mk _

/-- The actual zero-avoiding homotopy between the derivative and the
translated nonlinear map on the chosen punctured ball. -/
def derivativePuncturedBallHomotopy {f : E → F} (L : E ≃L[ℝ] F) (r : ℝ)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) :
    ContinuousMap.Homotopy (puncturedBallLinearMap L r)
      (puncturedBallTranslatedMap L r hc he) where
  toFun z := ⟨L z.2.1 + (z.1 : ℝ) • (f z.2.1 - f 0 - L z.2.1), by
    change L z.2.1 + (z.1 : ℝ) • ((f z.2.1 - f 0) - L z.2.1) ≠ 0
    apply straightLine_ne_zero_of_half_norm
    · intro hx
      exact z.2.property.1 (L.injective (by simpa only [map_zero] using hx))
    · exact he z.2.1 z.2.property.2⟩
  continuous_toFun := by
    have hfc : Continuous (fun x : PuncturedBall E r => f x.1) := by
      apply hc.comp_continuous continuous_subtype_val
      intro x
      simpa only [Metric.mem_ball, dist_zero_right] using x.property.2
    exact ((L.continuous.comp (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (((hfc.comp continuous_snd).sub continuous_const).sub
          (L.continuous.comp (continuous_subtype_val.comp continuous_snd))))).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    simp [puncturedBallLinearMap]
  map_one_left x := by
    apply Subtype.ext
    simp [puncturedBallTranslatedMap]

/-- Differentiability with an invertible derivative supplies a positive
radius on which the nonlinear germ has the explicit punctured homotopy. -/
theorem exists_derivativePuncturedBallHomotopy {f : E → F}
    (L : E ≃L[ℝ] F) (hf : HasFDerivAt f (L : E →L[ℝ] F) 0)
    {U : Set E} (hU : U ∈ 𝓝 (0 : E)) (hc : ContinuousOn f U) :
    ∃ r : ℝ, 0 < r ∧ ∃ (hc' : ContinuousOn f (Metric.ball 0 r))
      (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖),
      Nonempty (ContinuousMap.Homotopy (puncturedBallLinearMap L r)
        (puncturedBallTranslatedMap L r hc' he)) := by
  have hmem : U ∩ {x | ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖} ∈
      𝓝 (0 : E) := inter_mem hU (eventually_derivative_remainder_small L hf)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  have hc' : ContinuousOn f (Metric.ball 0 r) := hc.mono fun x hx => (hball hx).1
  have he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖ := by
    intro x hx
    exact (hball (by simpa only [Metric.mem_ball, dist_zero_right] using hx)).2
  exact ⟨r, hr, hc', he, ⟨derivativePuncturedBallHomotopy L r hc' he⟩⟩

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.DerivativePuncturedHomotopy.Cycles
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.DerivativePuncturedHomotopy"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.LocalDerivativeHomology -/

/-! # Local Derivative Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocalDerivativeHomology.Cycles

noncomputable section

/-!
# Local homology of a differentiable coordinate change

The actual homotopy from a map to its derivative is a homotopy of punctured
pairs on a small ball. Relative homotopy invariance and proved local excision
therefore identify its induced local homology map with that of its derivative.
For a complex-linear invertible derivative this map preserves the entire
orientation-degree local homology group. No orientation generator is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped _root_.Topology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A real invertible linear map as an actual continuous map of spaces. -/
def linearNormalMap (L : E ≃L[ℝ] F) : TopCat.of E ⟶ TopCat.of F :=
  TopCat.ofHom ⟨L, L.continuous⟩

theorem linearNormalMap_preservesPuncture (L : E ≃L[ℝ] F) :
    Set.MapsTo (linearNormalMap L) ({0}ᶜ : Set E) ({0}ᶜ : Set F) := by
  intro x hx
  change L x ≠ 0
  intro he
  exact hx (L.injective (by simpa only [map_zero] using he))

/-- The actual local homology map of an invertible real linear map. -/
def linearLocalHomologyMap (L : E ≃L[ℝ] F) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of E) 0 n ⟶
      LocalHomology.Cycles.localSingularHomology (TopCat.of F) 0 n :=
  LocalHomology.Cycles.relativeSingularHomologyMap (linearNormalMap L)
    (linearNormalMap_preservesPuncture L) n

/-- The distinguished point of a positive-radius coordinate ball. -/
abbrev ballZero (E : Type) [NormedAddCommGroup E] (r : ℝ) (hr : 0 < r) :
    Metric.ball (0 : E) r := ⟨0, by simpa using hr⟩

def linearBallMap (L : E ≃L[ℝ] F) (r : ℝ) :
    TopCat.of (Metric.ball (0 : E) r) ⟶ TopCat.of F :=
  TopCat.ofHom ⟨fun x => L x.1, L.continuous.comp continuous_subtype_val⟩

def translatedBallMap (f : E → F) (r : ℝ)
    (hc : ContinuousOn f (Metric.ball 0 r)) :
    TopCat.of (Metric.ball (0 : E) r) ⟶ TopCat.of F :=
  TopCat.ofHom ⟨fun x => f x.1 - f 0,
    (hc.domRestrict).sub continuous_const⟩

/-- The straight line on the full coordinate ball, including its center. -/
def derivativeBallHomotopy (f : E → F) (L : E ≃L[ℝ] F) (r : ℝ)
    (hc : ContinuousOn f (Metric.ball 0 r)) :
    TopCat.Homotopy (linearBallMap L r) (translatedBallMap f r hc) where
  toFun z := L z.2.1 + (z.1 : ℝ) • (f z.2.1 - f 0 - L z.2.1)
  continuous_toFun :=
    (L.continuous.comp (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (((hc.domRestrict.comp continuous_snd).sub continuous_const).sub
          (L.continuous.comp (continuous_subtype_val.comp continuous_snd))))
  map_zero_left x := by simp [linearBallMap]
  map_one_left x := by
    change L x.1 + (1 : ℝ) • (f x.1 - f 0 - L x.1) = f x.1 - f 0
    simp

theorem derivativeBallHomotopy_preservesPuncture (f : E → F)
    (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) :
    ∀ t : unitInterval, Set.MapsTo
      (fun x => derivativeBallHomotopy f L r hc (t, x))
      ({ballZero E r hr}ᶜ : Set (Metric.ball (0 : E) r)) ({0}ᶜ : Set F) := by
  intro t x hx
  change x ≠ ballZero E r hr at hx
  change L x.1 + (t : ℝ) • ((f x.1 - f 0) - L x.1) ≠ 0
  apply DerivativePuncturedHomotopy.Cycles.straightLine_ne_zero_of_half_norm
  · intro hL
    apply hx
    apply Subtype.ext
    change x.1 = 0
    exact L.injective (by simpa only [map_zero] using hL)
  · apply he
    simpa only [Metric.mem_ball, dist_zero_right] using x.property

theorem linearBallMap_preservesPuncture (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    Set.MapsTo (linearBallMap L r)
      ({ballZero E r hr}ᶜ : Set (Metric.ball (0 : E) r)) ({0}ᶜ : Set F) := by
  intro x hx
  change x ≠ ballZero E r hr at hx
  change L x.1 ≠ 0
  intro hL
  exact hx (Subtype.ext (L.injective (by simpa only [map_zero] using hL)))

theorem translatedBallMap_preservesPuncture (f : E → F)
    (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) :
    Set.MapsTo (translatedBallMap f r hc)
      ({ballZero E r hr}ᶜ : Set (Metric.ball (0 : E) r)) ({0}ᶜ : Set F) :=
  RelativeHomotopy.Cycles.homotopy_end_mapsTo (derivativeBallHomotopy f L r hc)
    (derivativeBallHomotopy_preservesPuncture f L r hr hc he)

def translatedBallLocalHomologyMap (f : E → F)
    (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Metric.ball (0 : E) r)) (ballZero E r hr) n ⟶
      LocalHomology.Cycles.localSingularHomology (TopCat.of F) 0 n :=
  LocalHomology.Cycles.relativeSingularHomologyMap (translatedBallMap f r hc)
    (translatedBallMap_preservesPuncture f L r hr hc he) n

/-- The nonlinear map and derivative induce equal relative homology maps
on the ball because the explicit homotopy preserves the punctured pair. -/
theorem translatedBallLocalHomologyMap_eq_linear (f : E → F)
    (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) (n : ℕ) :
    translatedBallLocalHomologyMap f L r hr hc he n =
      LocalHomology.Cycles.relativeSingularHomologyMap (linearBallMap L r)
        (linearBallMap_preservesPuncture L r hr) n :=
  (RelativeHomotopy.Cycles.relativeSingularHomologyMap_eq_of_homotopy
    (linearBallMap_preservesPuncture L r hr)
    (translatedBallMap_preservesPuncture f L r hr hc he)
    (derivativeBallHomotopy f L r hc)
    (derivativeBallHomotopy_preservesPuncture f L r hr hc he) n).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual linear map of punctured pairs factors through neighborhood
inclusion, before passing to homology. -/
theorem linearBallRelativeMap_factor (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    LocalExcision.Cycles.localExcisionChainMap (TopCat.of E) (Metric.ball 0 r) 0
        (by simpa using hr) ≫
      LocalHomology.Cycles.relativeSingularChainsMap (linearNormalMap L) (linearNormalMap_preservesPuncture L) =
    LocalHomology.Cycles.relativeSingularChainsMap (linearBallMap L r) (linearBallMap_preservesPuncture L r hr) := by
  unfold LocalExcision.Cycles.localExcisionChainMap
  rw [LocalHomology.Cycles.relativeSingularChainsMap_comp]
  rfl

/-- Excision identifies the local action of a differentiable germ with the
local action of its derivative. -/
theorem translatedBallLocalHomologyMap_eq_excision_comp (f : E → F)
    (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) (n : ℕ) :
    translatedBallLocalHomologyMap f L r hr hc he n =
      (LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of E) (Metric.ball 0 r) 0
        (by simpa using hr) Metric.isOpen_ball n).hom ≫ linearLocalHomologyMap L n := by
  rw [translatedBallLocalHomologyMap_eq_linear, LocalExcision.Cycles.localExcisionHomologyIso_hom]
  change HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, linearBallRelativeMap_factor]

/-- Complex-linear invertible derivatives preserve every local homology
class above degree one, without choosing a generator. -/
theorem complexLinearLocalHomologyMap_eq_id {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ)) (n : ℕ) (hn : 1 < n) :
    linearLocalHomologyMap (L.restrictScalars ℝ) n = 𝟙 _ := by
  let A := LinearMap.toMatrix' L.toLinearEquiv.toLinearMap
  have hA : IsUnit A :=
    LinearMap.isUnit_toMatrix'_iff.mpr ((Module.End.isUnit_iff _).mpr L.bijective)
  have hm : linearNormalMap (L.restrictScalars ℝ) = TopCat.ofHom (ComplexLinearPuncturedHomotopy.Cycles.complexMatrixMap A) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact (LinearMap.toMatrix'_mulVec L.toLinearEquiv.toLinearMap x).symm
  simpa only [linearLocalHomologyMap, hm, ComplexLinearPuncturedHomotopy.Cycles.complexMatrixLocalHomologyMap] using
    ComplexLinearPuncturedHomotopy.Cycles.complexMatrixLocalHomologyMap_eq_id A hA n hn

set_option backward.isDefEq.respectTransparency false in
/-- A nonlinear map with invertible complex derivative preserves the actual
orientation-degree local homology, on a sufficiently small ball. -/
theorem exists_complexDerivative_localHomology_eq_excision {p : ℕ} (hp : 0 < p)
    (f : (Fin p → ℂ) → (Fin p → ℂ))
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hf : HasFDerivAt f ((L.restrictScalars ℝ) : _ →L[ℝ] _) 0)
    {U : Set (Fin p → ℂ)} (hU : U ∈ 𝓝 (0 : Fin p → ℂ)) (hc : ContinuousOn f U) :
    ∃ (r : ℝ) (hr : 0 < r) (hc' : ContinuousOn f (Metric.ball 0 r))
      (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖),
      Metric.ball (0 : Fin p → ℂ) r ⊆ U ∧
      translatedBallLocalHomologyMap f (L.restrictScalars ℝ) r hr hc' he (2 * p) =
        (LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of (Fin p → ℂ)) (Metric.ball 0 r) 0
          (by simpa using hr) Metric.isOpen_ball (2 * p)).hom := by
  have hmem : U ∩ {x | ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖} ∈
      𝓝 (0 : Fin p → ℂ) :=
    Filter.inter_mem hU (DerivativePuncturedHomotopy.Cycles.eventually_derivative_remainder_small (L.restrictScalars ℝ) hf)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  have hsub : Metric.ball (0 : Fin p → ℂ) r ⊆ U := fun _ hx => (hball hx).1
  have hc' : ContinuousOn f (Metric.ball 0 r) := hc.mono hsub
  have he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖ := by
    intro x hx
    exact (hball (by simpa only [Metric.mem_ball, dist_zero_right] using hx)).2
  refine ⟨r, hr, hc', he, hsub, ?_⟩
  rw [translatedBallLocalHomologyMap_eq_excision_comp,
    complexLinearLocalHomologyMap_eq_id L (2 * p) (by omega), Category.comp_id]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocalDerivativeHomology.Cycles
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.LocalDerivativeHomology"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOrientation -/

/-! # Complex Orientation -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOrientation

noncomputable section

/-!+# Complex orientations of finite-dimensional tangent model spaces

The real determinant of a complex-linear automorphism is the squared complex
norm of its complex determinant and is therefore positive. The real bases
`(v₁, I v₁, …, vₙ, I vₙ)` consequently give one orientation independent of
the chosen complex basis. These are linear-algebraic prerequisites for cycle
orientations; this file does not construct fundamental or cycle classes.
-/

open _root_.Module

variable {V W : Type*}
variable [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
variable [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]

/-- The determinant after restricting a complex-linear map to real scalars. -/
theorem complexLinearMap_realDet (f : V →ₗ[ℂ] V) :
    LinearMap.det (f.restrictScalars ℝ) = Complex.normSq (LinearMap.det f) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- Every complex-linear automorphism has positive real determinant. -/
theorem complexLinearEquiv_realDet_pos (e : V ≃ₗ[ℂ] V) :
    0 < LinearMap.det ((e.restrictScalars ℝ).toLinearMap) := by
  change 0 < LinearMap.det (e.toLinearMap.restrictScalars ℝ)
  rw [complexLinearMap_realDet, Complex.normSq_pos]
  exact e.isUnit_det'.ne_zero

variable {ι : Type*}

/-- The real basis obtained from a complex basis by replacing each vector with
itself and its multiple by `I`, in that order. -/
def complexRealBasis (b : Basis ι ℂ V) : Basis (ι × Fin 2) ℝ V :=
  Complex.basisOneI.smulTower' b

@[simp]
theorem complexRealBasis_apply (b : Basis ι ℂ V) (i : ι) (j : Fin 2) :
    complexRealBasis b (i, j) = Complex.basisOneI j • b i := by
  exact Complex.basisOneI.smulTower'_apply b (i, j)

@[simp]
theorem complexRealBasis_map (b : Basis ι ℂ V) (e : V ≃ₗ[ℂ] W) :
    complexRealBasis (b.map e) = (complexRealBasis b).map (e.restrictScalars ℝ) := by
  ext ij
  simp [complexRealBasis, Basis.smulTower'_apply]

variable [Fintype ι] [DecidableEq ι]

/-- The complex orientation as presented by a complex basis. -/
def complexOrientationOfBasis (b : Basis ι ℂ V) : Orientation ℝ V (ι × Fin 2) :=
  (complexRealBasis b).orientation

theorem complexOrientationOfBasis_map (b : Basis ι ℂ V) (e : V ≃ₗ[ℂ] W) :
    complexOrientationOfBasis (b.map e) =
      Orientation.map (ι × Fin 2) (e.restrictScalars ℝ) (complexOrientationOfBasis b) := by
  rw [complexOrientationOfBasis, complexRealBasis_map, Basis.orientation_map]
  rfl

/-- A complex-linear automorphism preserves the orientation of any real basis. -/
theorem complexLinearEquiv_preserves_realBasis_orientation
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Basis κ ℝ V) (e : V ≃ₗ[ℂ] V) :
    Orientation.map κ (e.restrictScalars ℝ) b.orientation = b.orientation := by
  rw [← Basis.orientation_map]
  exact (b.orientation_comp_linearEquiv_eq_iff_det_pos (e.restrictScalars ℝ)).2
    (complexLinearEquiv_realDet_pos e)

/-- The orientation from the paired real basis is independent of the complex basis. -/
theorem complexOrientationOfBasis_eq (b c : Basis ι ℂ V) :
    complexOrientationOfBasis b = complexOrientationOfBasis c := by
  let e := b.equiv c (Equiv.refl ι)
  have he : b.map e = c := by
    simp [e]
  calc
    complexOrientationOfBasis b =
        Orientation.map (ι × Fin 2) (e.restrictScalars ℝ) (complexOrientationOfBasis b) :=
      (complexLinearEquiv_preserves_realBasis_orientation (complexRealBasis b) e).symm
    _ = complexOrientationOfBasis (b.map e) := (complexOrientationOfBasis_map b e).symm
    _ = complexOrientationOfBasis c := congrArg complexOrientationOfBasis he

/-- Complex-linear coordinate transitions preserve the orientations defined by
any complex bases on the source and target. -/
theorem complexOrientationOfBasis_equiv (b : Basis ι ℂ V) (c : Basis ι ℂ W)
    (e : V ≃ₗ[ℂ] W) :
    Orientation.map (ι × Fin 2) (e.restrictScalars ℝ) (complexOrientationOfBasis b) =
      complexOrientationOfBasis c := by
  rw [← complexOrientationOfBasis_map]
  exact complexOrientationOfBasis_eq (b.map e) c

/-- The standard complex orientation on the real tangent model space `ℂⁿ`. -/
def standardComplexOrientation (n : ℕ) :
    Orientation ℝ (Fin n → ℂ) (Fin n × Fin 2) :=
  complexOrientationOfBasis (Pi.basisFun ℂ (Fin n))

/-- Every complex-linear change of standard complex coordinates preserves
the standard real orientation. -/
theorem standardComplexOrientation_preserved (n : ℕ)
    (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    Orientation.map (Fin n × Fin 2) (e.restrictScalars ℝ)
      (standardComplexOrientation n) = standardComplexOrientation n := by
  exact complexOrientationOfBasis_equiv (Pi.basisFun ℂ (Fin n))
    (Pi.basisFun ℂ (Fin n)) e

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOrientation
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOrientation"


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
    (`OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOrientation.standardComplexOrientation_preserved, "theorem")
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
    ("nonce", toJson "83da9da6138027d07d17812571013a62"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:83da9da6138027d07d17812571013a62"
