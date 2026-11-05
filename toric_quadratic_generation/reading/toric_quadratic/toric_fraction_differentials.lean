module

public import PaperVerification.ToricLogarithmicVolume
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-!
# Differential forms in the actual character fraction field

All maps in this file come from the universal Kähler derivation and its
localization theorem.  In particular, the map from a chart's top exterior
power is the exterior extension of the actual differential map; its
principal image is a conclusion, not part of the definition.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra KaehlerDifferential
open scoped BigOperators Classical

section ExteriorExtension

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] {n : ℕ}

/-- Extension of scalars for actual exterior forms, constructed from the
universal alternating map.  The source and target exterior powers retain
their respective coefficient rings. -/
def exteriorScalarExtensionMap (f : M →ₗ[R] N) :
    (⋀[R]^n M) →ₗ[R] (⋀[S]^n N) := by
  let a : N [⋀^Fin n]→ₗ[R] (⋀[S]^n N) :=
    { (exteriorPower.ιMulti S n (M := N)).toMultilinearMap.restrictScalars R with
      map_eq_zero_of_eq' := fun v i j hij hne =>
        (exteriorPower.ιMulti S n).map_eq_zero_of_eq v hij hne }
  exact exteriorPower.alternatingMapLinearEquiv (a.compLinearMap f)

@[simp] theorem exteriorScalarExtensionMap_wedge (f : M →ₗ[R] N) (v : Fin n → M) :
    exteriorScalarExtensionMap (S := S) f (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun i => f (v i)) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem topExterior_eq_smul_basis (b : Module.Basis (Fin n) R M)
    (x : ⋀[R]^n M) :
    x = basisTopExteriorEquiv b x • exteriorPower.ιMulti R n b :=
  ((basisTopExteriorEquiv b).symm_apply_apply x).symm

end ExteriorExtension

variable (k : Type*) [CommRing k] {E : Type*} [AddCommGroup E] [Module ℤ E]
    (K : Type*) [Field K] [Algebra k K] [Algebra (AddMonoidAlgebra k E) K]
    [IsScalarTower k (AddMonoidAlgebra k E) K]
    [IsFractionRing (AddMonoidAlgebra k E) K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordinary Kähler differential basis after localization to the
actual fraction field of the character ring. -/
def fractionLogDifferentialBasis (b : Module.Basis ι ℤ E) :
    Module.Basis ι K Ω[K⁄k] :=
  (logDifferentialBasis k b).ofIsLocalizedModule K
    (nonZeroDivisors (AddMonoidAlgebra k E))
    (KaehlerDifferential.map k k (AddMonoidAlgebra k E) K)

def fractionLogDifferential (m : E) : Ω[K⁄k] :=
  algebraMap (AddMonoidAlgebra k E) K (single (-m) 1) •
    D k K (algebraMap (AddMonoidAlgebra k E) K (single m 1))

@[simp] theorem map_logDifferential (m : E) :
    KaehlerDifferential.map k k (AddMonoidAlgebra k E) K (logDifferential k m) =
      fractionLogDifferential k K m := by
  rw [logDifferential, map_smul, KaehlerDifferential.map_D]
  exact (IsScalarTower.algebraMap_smul K _ _).symm

@[simp] theorem fractionLogDifferentialBasis_apply (b : Module.Basis ι ℤ E) (i : ι) :
    fractionLogDifferentialBasis k K b i = fractionLogDifferential k K (b i) := by
  rw [fractionLogDifferentialBasis, Module.Basis.ofIsLocalizedModule_apply,
    logDifferentialBasis_eq, map_logDifferential]

theorem fractionLogDifferentialBasis_repr (b : Module.Basis ι ℤ E) (m : E) (i : ι) :
    (fractionLogDifferentialBasis k K b).repr (fractionLogDifferential k K m) i =
      (b.repr m i : K) := by
  rw [← map_logDifferential, fractionLogDifferentialBasis,
    Module.Basis.ofIsLocalizedModule_repr_apply, logDifferentialBasis_repr, map_intCast]

theorem fraction_character_differential (m : E) :
    D k K (algebraMap (AddMonoidAlgebra k E) K (single m 1)) =
      algebraMap (AddMonoidAlgebra k E) K (single m 1) •
        fractionLogDifferential k K m := by
  rw [fractionLogDifferential, smul_smul, ← map_mul]
  simp only [single_mul_single, add_neg_cancel, mul_one,
    ← AddMonoidAlgebra.one_def, map_one, one_smul]

section Top

variable {n : ℕ}

def fractionLogVolume (b : Module.Basis (Fin n) ℤ E) : ⋀[K]^n Ω[K⁄k] :=
  exteriorPower.ιMulti K n (fractionLogDifferentialBasis k K b)

def fractionRegularCoordinateVolume (b : Module.Basis (Fin n) ℤ E) : ⋀[K]^n Ω[K⁄k] :=
  exteriorPower.ιMulti K n
    (fun i => D k K (algebraMap (AddMonoidAlgebra k E) K (single (b i) 1)))

theorem fractionLogDifferentialBasis_det (b c : Module.Basis (Fin n) ℤ E) :
    (fractionLogDifferentialBasis k K b).det (fractionLogDifferentialBasis k K c) =
      (b.det c : K) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  have hmatrix :
      (fractionLogDifferentialBasis k K b).toMatrix (fractionLogDifferentialBasis k K c) =
        (Int.castRingHom K).mapMatrix (b.toMatrix c) := by
    ext i j
    change (fractionLogDifferentialBasis k K b).repr
      (fractionLogDifferentialBasis k K c j) i = (b.repr (c j) i : K)
    rw [fractionLogDifferentialBasis_apply, fractionLogDifferentialBasis_repr]
  rw [hmatrix, ← RingHom.map_det]
  rfl

theorem fractionLogVolume_change_basis (b c : Module.Basis (Fin n) ℤ E) :
    fractionLogVolume k K c = (b.det c : K) • fractionLogVolume k K b := by
  have h := congrArg (fun f => f (fractionLogDifferentialBasis k K c))
    (alternating_eq_basis_determinant (fractionLogDifferentialBasis k K b)
      (exteriorPower.ιMulti K n))
  change fractionLogVolume k K c =
    (fractionLogDifferentialBasis k K b).det (fractionLogDifferentialBasis k K c) •
      fractionLogVolume k K b at h
  rw [fractionLogDifferentialBasis_det] at h
  exact h

theorem fractionRegularCoordinateVolume_eq_character
    (b : Module.Basis (Fin n) ℤ E) :
    fractionRegularCoordinateVolume k K b =
      algebraMap (AddMonoidAlgebra k E) K (single (∑ i, b i) 1) •
        fractionLogVolume k K b := by
  unfold fractionRegularCoordinateVolume
  simp_rw [fraction_character_differential]
  rw [AlternatingMap.map_smul_univ, ← map_prod]
  simp only [AddMonoidAlgebra.prod_single, Finset.prod_const_one]
  congr 1
  exact congrArg (exteriorPower.ιMulti K n)
    (funext (fun i => (fractionLogDifferentialBasis_apply k K b i).symm))

variable (b : Module.Basis (Fin n) ℤ E)

local notation "S" => monoidChartAlgebra k (coordinateConeMonoid b Finset.univ)

-- The chart acts through its canonical inclusion into the character algebra
-- and the already supplied character-algebra map to K.  In particular, the
-- algebra and inherited subalgebra actions are the same actual action.

/-- Coefficients of genuine regular top differential forms in a chosen
generic logarithmic volume. This is defined from the differential map,
without a monomial or divisor formula. -/
def chartTopDifferentialCoefficient (b₀ : Module.Basis (Fin n) ℤ E) :
    (⋀[S]^n Ω[S⁄k]) →ₗ[S] K := by
  let d : Ω[S⁄k] →ₗ[S] Ω[K⁄k] := KaehlerDifferential.map k k S K
  let e : (⋀[S]^n Ω[S⁄k]) →ₗ[S] (⋀[K]^n Ω[K⁄k]) :=
    exteriorScalarExtensionMap (R := S) («S» := K)
      (M := KaehlerDifferential k S) (N := KaehlerDifferential k K) (n := n) d
  exact ((basisTopExteriorEquiv (fractionLogDifferentialBasis k K b₀)).toLinearMap.restrictScalars S).comp e

theorem chartTopDifferentialCoefficient_basis (b₀ : Module.Basis (Fin n) ℤ E) :
    chartTopDifferentialCoefficient k K b b₀
        (exteriorPower.ιMulti S n (fullChartDifferentialBasis k b)) =
      algebraMap (AddMonoidAlgebra k E) K (single (∑ i, b i) 1) * (b₀.det b : K) := by
  have hw := exteriorScalarExtensionMap_wedge (R := S) («S» := K)
    (M := KaehlerDifferential k S) (N := KaehlerDifferential k K) (n := n)
    (show Ω[S⁄k] →ₗ[S] Ω[K⁄k] from KaehlerDifferential.map k k S K)
    (fullChartDifferentialBasis k b)
  refine (congrArg (basisTopExteriorEquiv (fractionLogDifferentialBasis k K b₀)) hw).trans ?_
  have hdiff (i : Fin n) :
      KaehlerDifferential.map k k S K (fullChartDifferentialBasis k b i) =
        D k K (algebraMap (AddMonoidAlgebra k E) K (single (b i) 1)) := by
    rw [fullChartDifferentialBasis_apply, KaehlerDifferential.map_D,
      IsScalarTower.algebraMap_eq S (AddMonoidAlgebra k E) K]
    rfl
  refine (congrArg
    (fun v : Fin n→Ω[K⁄k] =>
      basisTopExteriorEquiv (fractionLogDifferentialBasis k K b₀)
        (exteriorPower.ιMulti K n v))
    (funext hdiff)).trans ?_
  change basisTopExteriorEquiv (fractionLogDifferentialBasis k K b₀)
    (fractionRegularCoordinateVolume k K b) = _
  rw [fractionRegularCoordinateVolume_eq_character, map_smul,
    fractionLogVolume_change_basis k K b₀ b, map_smul]
  change _ * ((b₀.det b : K) *
    basisTopExteriorEquiv (fractionLogDifferentialBasis k K b₀)
      (exteriorPower.ιMulti K n (fractionLogDifferentialBasis k K b₀))) = _
  rw [basisTopExteriorEquiv_basis, mul_one]

/-- The principal chart formula is derived for the image of the actual
top Kähler module. The determinant is a unit because both lattices bases
are integral bases; this statement keeps the exact transition scalar. -/
theorem mem_range_chartTopDifferentialCoefficient_iff
    (b₀ : Module.Basis (Fin n) ℤ E) (z : K) :
    z ∈ LinearMap.range (chartTopDifferentialCoefficient k K b b₀) ↔
      ∃ r : S, algebraMap S K r *
        (algebraMap (AddMonoidAlgebra k E) K (single (∑ i, b i) 1) * (b₀.det b : K)) = z := by
  constructor
  · rintro ⟨ω, rfl⟩
    refine ⟨basisTopExteriorEquiv (fullChartDifferentialBasis k b) ω, ?_⟩
    conv_rhs => rw [topExterior_eq_smul_basis (fullChartDifferentialBasis k b) ω]
    rw [map_smul, chartTopDifferentialCoefficient_basis]
    exact (Algebra.smul_def _ _).symm
  · rintro ⟨r, hr⟩
    refine ⟨r • exteriorPower.ιMulti S n (fullChartDifferentialBasis k b), ?_⟩
    rw [map_smul, chartTopDifferentialCoefficient_basis]
    exact (Algebra.smul_def _ _).trans hr

end Top

end PaperVerification.ToricCharacters
