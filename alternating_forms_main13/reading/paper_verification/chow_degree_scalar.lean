module

public import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow
public import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.DimensionBridge
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Lean.Elab.Tactic.Omega

/-!
# The actual Chow group of the complex point

The unique support has transcendence dimension zero.  There is no integral
support of dimension one, so the principal-divisor relation submodule is
zero. Evaluation at the unique point therefore identifies its genuine
zero-dimensional Chow group with `ℚ`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ChowDegree

open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.AlgebraicGeometry
open Foundations.Scheme.SupportDimension
open Foundations.Scheme.TranscendenceDimension
open Divisors.LineBundles.Graded.GlobalSpecialization.BundleCycles
open Divisors.LineBundles.DimensionChow.BundleCycles

abbrev complexBase := Foundations.Scheme.ProjectiveSpace.complexBase

theorem complexBase_dimension : schemeTranscendenceDimension (𝟙 complexBase) = 0 := by
  have h := Divisors.LineBundles.Affine.DimensionBridge.BundleCycles.schemeTranscendenceDimension_spec_algebra ℂ ℂ
  simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Functor.map_id,
    AlgebraicGeometry.Spec.map_id, trdeg_eq_zero, Cardinal.zero_toNat] using h

theorem complexBase_support_dimension (W : IrreducibleCloseds complexBase) :
    supportTranscendenceDimension W (𝟙 complexBase) = 0 := by
  have h := supportTranscendenceDimension_le W (𝟙 complexBase)
  rw [complexBase_dimension] at h
  exact Nat.eq_zero_of_le_zero h

/-- The actual zero-dimensional point index, with its grading proved. -/
def complexBasePoint : SchemeDimensionCyclePoint (𝟙 complexBase) 0 :=
  ⟨Classical.choice inferInstance,
    complexBase_support_dimension (irreducibleSetEquivPoints.symm _)⟩

theorem complexBase_relations_zero :
    dimensionRationalEquivalenceQ (𝟙 complexBase) 0 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [dimensionRationalEquivalenceQ, Submodule.span_le]
  rintro z ⟨W,hW,g,hg,hz⟩
  rw [complexBase_support_dimension] at hW
  omega

instance complexBasePoint_subsingleton :
    Subsingleton (SchemeDimensionCyclePoint (𝟙 complexBase) 0) := by
  unfold SchemeDimensionCyclePoint
  infer_instance

/-- The scalar degree reads the coefficient at the unique actual point
after quotienting by the proved zero relation submodule. -/
def complexBaseChowEquiv : DimensionChowQ (𝟙 complexBase) 0 ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEqBot (dimensionRationalEquivalenceQ (𝟙 complexBase) 0)
    complexBase_relations_zero).trans
      (Finsupp.uniqueLinearEquiv ℚ ℚ complexBasePoint)

@[simp]
theorem complexBaseChowEquiv_pointClass (q : ℚ) :
    complexBaseChowEquiv (dimensionCycleToChowQ (𝟙 complexBase) 0
      (Finsupp.single complexBasePoint q)) = q := by
  change (Finsupp.single complexBasePoint q) complexBasePoint = q
  exact Finsupp.single_eq_same

end PaperVerification.ChowDegree
