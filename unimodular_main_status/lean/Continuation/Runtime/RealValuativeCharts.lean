module

public import Continuation.Runtime.RealValuedCharacters
public import Continuation.Runtime.RealConeCharacters

/-!
# Actual valuative maps into character charts

The Hahn-valued torus point extends to an affine character chart exactly
when every character in its literal exponent monoid has nonnegative
weight. For a smooth chart this is exactly membership in its real cone.
Every factorization below is an equality of actual algebra homomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PaperVerification.ToricCharacters

variable (k : Type*) [Field k] {M : Type*} [AddCommGroup M]
    (w : M →+ ℝ) (S : AddSubmonoid M)

/-- The actual map from the chart coordinate ring to the Hahn valuation
ring, when all of its regular characters have nonnegative weight. -/
def realChartCharacterEvaluation (hS : ∀ m ∈ S, 0 ≤ w m) :
    monoidChartAlgebra k S →ₐ[k] RealCharacterValuationRing k :=
  (realMonoidCharacterEvaluation k w S hS).comp
    (monoidChartAlgebraEquiv k S).symm.toAlgHom

theorem realChartCharacterEvaluation_generic (hS : ∀ m ∈ S, 0 ≤ w m) :
    (IsScalarTower.toAlgHom k (RealCharacterValuationRing k) (HahnSeries ℝ k)).comp
        (realChartCharacterEvaluation k w S hS) =
      (realCharacterEvaluation k w).comp (monoidChartAlgebra k S).val := by
  apply AlgHom.ext
  intro f
  obtain ⟨g, rfl⟩ := (monoidChartAlgebraEquiv k S).surjective f
  change (realMonoidCharacterEvaluation k w S hS
      ((monoidChartAlgebraEquiv k S).symm ((monoidChartAlgebraEquiv k S) g)) :
        HahnSeries ℝ k) = _
  rw [AlgEquiv.symm_apply_apply]
  have h := congrArg (fun φ => φ g) (realMonoidCharacterEvaluation_generic k w S hS)
  exact h

/-- Any actual extension of the original torus values forces all
regular characters to have nonnegative real weight. -/
theorem nonnegative_of_realChart_factorization
    (φ : monoidChartAlgebra k S →ₐ[k] RealCharacterValuationRing k)
    (hφ : (IsScalarTower.toAlgHom k (RealCharacterValuationRing k) (HahnSeries ℝ k)).comp φ =
      (realCharacterEvaluation k w).comp (monoidChartAlgebra k S).val) :
    ∀ m ∈ S, 0 ≤ w m := by
  intro m hm
  apply (realCharacterEvaluation_mem_iff k w m).mp
  have h := congrArg (fun ψ => ψ (chartCharacter k S m hm)) hφ
  change (φ (chartCharacter k S m hm) : HahnSeries ℝ k) =
    realCharacterEvaluation k w (AddMonoidAlgebra.single m 1) at h
  rw [← h]
  exact (φ (chartCharacter k S m hm)).property

/-- The converse only needs the literal ring map. This form applies
directly to the comorphism of a scheme-theoretic valuative lift. -/
theorem nonnegative_of_realChart_ringFactorization
    (φ : monoidChartAlgebra k S →+* RealCharacterValuationRing k)
    (hφ : (algebraMap (RealCharacterValuationRing k) (HahnSeries ℝ k)).comp φ =
      (realCharacterEvaluation k w).toRingHom.comp
        (monoidChartAlgebra k S).val.toRingHom) :
    ∀ m ∈ S, 0 ≤ w m := by
  intro m hm
  apply (realCharacterEvaluation_mem_iff k w m).mp
  have h := congrArg (fun ψ => ψ (chartCharacter k S m hm)) hφ
  change (φ (chartCharacter k S m hm) : HahnSeries ℝ k) =
    realCharacterEvaluation k w (AddMonoidAlgebra.single m 1) at h
  rw [← h]
  exact (φ (chartCharacter k S m hm)).property

/-- Literal affine-chart extension is equivalent to the full family of
weight inequalities; neither direction assumes injectivity of the
Hahn-valued torus point. -/
theorem realChart_factorization_iff :
    (∃ φ : monoidChartAlgebra k S →ₐ[k] RealCharacterValuationRing k,
      (IsScalarTower.toAlgHom k (RealCharacterValuationRing k) (HahnSeries ℝ k)).comp φ =
        (realCharacterEvaluation k w).comp (monoidChartAlgebra k S).val) ↔
      ∀ m ∈ S, 0 ≤ w m := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact nonnegative_of_realChart_factorization k w S φ hφ
  · intro hS
    exact ⟨realChartCharacterEvaluation k w S hS,
      realChartCharacterEvaluation_generic k w S hS⟩

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters

variable (k : Type*) [Field k] {n : ℕ}

/-- Extension to a coordinate chart detects exactly its entire real
cone, with the original lattice pairing and all free directions intact. -/
theorem realChart_factorization_iff_mem_cone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) (x : Ambient n) :
    (∃ φ : monoidChartAlgebra k (coordinateConeMonoid b I) →ₐ[k]
        RealCharacterValuationRing k,
      (IsScalarTower.toAlgHom k (RealCharacterValuationRing k) (HahnSeries ℝ k)).comp φ =
        (realCharacterEvaluation k (latticeRealWeight x)).comp
          (monoidChartAlgebra k (coordinateConeMonoid b I)).val) ↔
      x ∈ latticeRayCone (I.image (integralDualBasis b)) := by
  rw [realChart_factorization_iff, mem_dualBasisCone_iff_nonnegative_characters]

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricCharacters.realChart_factorization_iff
#print axioms PaperVerification.ToricGeometry.realChart_factorization_iff_mem_cone
