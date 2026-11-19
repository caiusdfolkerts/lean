module

public import OAI.AlgebraicGeometry.Divisors.LineBundles.ChowLocalization
public import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowOver
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Total genuine rational Chow groups and finite closed filtrations

`TotalChowQ` is the direct sum of the actual dimension-graded principal-divisor
quotients.  Its elements retain all dimensions; this is a convenient underlying
vector space for a rank bound and does not redefine intersection or Chern classes.

Localization is proved by summing the genuine closed/open localization maps.
In particular the finite-dimensionality argument never assumes a cycle class
isomorphism, a projective bundle formula, or Poincaré duality.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TotalChow

open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.AlgebraicGeometry
open Divisors.LineBundles
open DimensionChow.BundleCycles
open scoped DirectSum

abbrev complexBase := Foundations.Scheme.ProjectiveSpace.complexBase

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]

/-- Every open of a genuine Noetherian scheme is itself Noetherian. -/
instance opens_isNoetherian (U : X.Opens) : AlgebraicGeometry.IsNoetherian U := by
  letI : NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  exact ⟨⟩


/-- The full direct sum of the actual Chow groups in every dimension. -/
abbrev TotalChowQ (f : X ⟶ complexBase) :=
  ⨁ d : ℕ, DimensionChowQ f d

/-- Every actual scheme point contributes its irreducible closed support
in its proved transcendence dimension. -/
def pointDimension (f : X ⟶ complexBase) (x : X) : ℕ :=
  Foundations.Scheme.SupportDimension.supportTranscendenceDimension
    (irreducibleSetEquivPoints.symm x) f

def pointClass (f : X ⟶ complexBase) (x : X) : TotalChowQ f :=
  DirectSum.of (fun d => DimensionChowQ f d) (pointDimension f x)
    (dimensionCycleToChowQ f (pointDimension f x) (Finsupp.single ⟨x,rfl⟩ 1))

/-- Sending an ordinary finite rational cycle to the direct sum of its
actual dimension-graded classes. -/
def totalCycleToChow (f : X ⟶ complexBase) : (X →₀ ℚ) →ₗ[ℚ] TotalChowQ f :=
  Finsupp.linearCombination ℚ (pointClass f)

theorem totalCycleToChow_single (f : X ⟶ complexBase) (x : X) (q : ℚ) :
    totalCycleToChow f (Finsupp.single x q) =
      DirectSum.of (fun d => DimensionChowQ f d) (pointDimension f x)
        (dimensionCycleToChowQ f (pointDimension f x) (Finsupp.single ⟨x,rfl⟩ q)) := by
  classical
  rw [totalCycleToChow, Finsupp.linearCombination_single]
  simp only [pointClass, ← DirectSum.of_smul, ← map_smul,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The direct sum consists precisely of genuine finite cycle classes. -/
theorem totalCycleToChow_surjective (f : X ⟶ complexBase) :
    Function.Surjective (totalCycleToChow f) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro a ha
  clear ha
  induction a using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | of d a =>
    obtain ⟨z,rfl⟩ := dimensionCycleToChowQ_surjective f d a
    induction z using Finsupp.induction_linear with
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => simp only [map_add]; exact Submodule.add_mem _ ha hb
    | single x q =>
      rcases x with ⟨x,hx⟩
      change pointDimension f x = d at hx
      subst d
      exact ⟨Finsupp.single x q,totalCycleToChow_single f x q⟩

/-- A finite point set bounds the rank of its actual total cycle quotient. -/
theorem finite_of_finite_points (f : X ⟶ complexBase) [Finite X] :
    Module.Finite ℚ (TotalChowQ f) :=
  Module.Finite.of_surjective (totalCycleToChow f) (totalCycleToChow_surjective f)

theorem finrank_le_card_points (f : X ⟶ complexBase) [Finite X] :
    Module.finrank ℚ (TotalChowQ f) ≤ Nat.card X := by
  classical
  letI := Fintype.ofFinite X
  have h := LinearMap.finrank_le_finrank_of_surjective (totalCycleToChow_surjective f)
  simpa only [Module.finrank_finsupp_self, Nat.card_eq_fintype_card] using h

theorem finite_complexBase : Module.Finite ℚ (TotalChowQ (𝟙 complexBase)) :=
  finite_of_finite_points _

theorem finrank_complexBase_le_one :
    Module.finrank ℚ (TotalChowQ (𝟙 complexBase)) ≤ 1 := by
  simpa only [Nat.card_unique] using finrank_le_card_points (𝟙 complexBase)

/-- Actual isomorphisms over the coefficient field act on every Chow group. -/
def totalChowEquiv {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y]
    (e : X ≅ Y) (f : X ⟶ complexBase) (g : Y ⟶ complexBase)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (h : e.hom ≫ g = f) :
    TotalChowQ f ≃ₗ[ℚ] TotalChowQ g :=
  DirectSum.congrLinearEquiv
    (fun d => Closed.ChowOver.BundleCycles.schemeIsoChowEquiv e f g h d)

section Localization

variable {U Z : Scheme.{0}} [AlgebraicGeometry.IsNoetherian U]
  [AlgebraicGeometry.IsNoetherian Z]
  (i : U ⟶ X) [IsOpenImmersion i] (j : Z ⟶ X) [IsClosedImmersion j]
  (f : X ⟶ complexBase) [LocallyOfFiniteType f]

def totalOpenRestriction : TotalChowQ f →ₗ[ℚ] TotalChowQ (i ≫ f) :=
  DirectSum.lmap (fun d => Open.ChowRestriction.BundleCycles.openChowRestriction i f d)

def totalClosedPushforward : TotalChowQ (j ≫ f) →ₗ[ℚ] TotalChowQ f :=
  DirectSum.lmap (fun d => Closed.ChowPushforward.BundleCycles.closedChowPushforward j f d)

theorem totalOpenRestriction_surjective : Function.Surjective (totalOpenRestriction i f) :=
  (DirectSum.lmap_surjective _).mpr
    (fun d => Open.ChowRestriction.BundleCycles.openChowRestriction_surjective i f d)

/-- Summing the actual localization sequences remains exact, with no
finiteness of the set of dimensions assumed. -/
theorem totalChowLocalization_exact (hc : Set.range j = (Set.range i)ᶜ) :
    LinearMap.range (totalClosedPushforward j f) =
      LinearMap.ker (totalOpenRestriction i f) := by
  simp only [totalClosedPushforward, totalOpenRestriction, DirectSum.range_lmap,
    DirectSum.ker_lmap, ChowLocalization.BundleCycles.chowLocalization_exact i j hc f]

theorem finite_of_closed_open (hc : Set.range j = (Set.range i)ᶜ)
    [Module.Finite ℚ (TotalChowQ (j ≫ f))]
    [Module.Finite ℚ (TotalChowQ (i ≫ f))] : Module.Finite ℚ (TotalChowQ f) :=
  Module.Finite.of_exact
    (LinearMap.exact_iff.mpr (totalChowLocalization_exact i j f hc).symm)
    (totalOpenRestriction_surjective i f)

/-- The full actual Chow rank grows by at most the rank of the newly
adjoined affine stratum. This is the inductive finite-paving bound. -/
theorem finrank_le_closed_add_open (hc : Set.range j = (Set.range i)ᶜ)
    [Module.Finite ℚ (TotalChowQ (j ≫ f))]
    [Module.Finite ℚ (TotalChowQ (i ≫ f))] :
    Module.finrank ℚ (TotalChowQ f) ≤
      Module.finrank ℚ (TotalChowQ (j ≫ f)) + Module.finrank ℚ (TotalChowQ (i ≫ f)) := by
  letI := finite_of_closed_open i j f hc
  rw [← (totalOpenRestriction i f).finrank_range_add_finrank_ker,
    ← totalChowLocalization_exact i j f hc,
    LinearMap.range_eq_top.mpr (totalOpenRestriction_surjective i f),
    finrank_top]
  exact (Nat.add_le_add_left (totalClosedPushforward j f).finrank_range_le _).trans_eq
    (Nat.add_comm _ _)

end Localization
end PaperVerification.TotalChow
