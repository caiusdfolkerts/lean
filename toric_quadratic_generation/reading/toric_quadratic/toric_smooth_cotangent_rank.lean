module

public import PaperVerification.ToricMonoidCotangent
public import PaperVerification.ToricFractionDifferentials
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.LinearAlgebra.Dimension.Localization

@[expose] public section

/-!
# Smooth cotangent fibres have the actual generic differential rank

Smoothness makes the Kähler module finite projective, hence finite flat.
The existing rank-at-prime theorem then identifies its fibre dimension
with its fraction-field rank. This argument requires no additional
regular-local-ring or normality hypothesis.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open KaehlerDifferential
open scoped TensorProduct Classical

section GenericRank

variable (k R K : Type*) [Field k] [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
    [IsFractionRing R K] {n : ℕ}
    (bK : Module.Basis (Fin n) K Ω[K⁄k])

include bK in
theorem kaehler_finrank_eq_generic_basis : Module.finrank R Ω[R⁄k] = n := by
  calc
    Module.finrank R Ω[R⁄k] = Module.finrank R Ω[K⁄k] :=
      (IsLocalizedModule.finrank_eq (nonZeroDivisors R)
        (KaehlerDifferential.map k k R K) le_rfl).symm
    _ = Module.finrank K Ω[K⁄k] :=
      (IsFractionRing.finrank_right_eq R K Ω[K⁄k]).symm
    _ = n := by simpa using Module.finrank_eq_card_basis bK

variable [Algebra.Smooth k R] [Algebra R k] [IsScalarTower k R k]

include bK in
/-- The point is specified by the actual algebra structure R→k. -/
theorem smooth_rational_cotangent_finrank :
    Module.finrank k (k ⊗[R] Ω[R⁄k]) = n := by
  let p₀ : PrimeSpectrum k := ⟨⊥,inferInstance⟩
  let p : PrimeSpectrum R := p₀.comap (algebraMap R k)
  have hb := Module.rankAtStalk_baseChange (R := R) (M := Ω[R⁄k]) p₀
  rw [Module.rankAtStalk_eq_finrank_of_free] at hb
  calc
    Module.finrank k (k ⊗[R] Ω[R⁄k]) = Module.rankAtStalk Ω[R⁄k] p := hb
    _ = Module.finrank R Ω[R⁄k] := by
      rw [Module.rankAtStalk_eq]
      exact p.asIdeal.finrank_fiber_eq_finrank
    _ = n := kaehler_finrank_eq_generic_basis k R K bK

end GenericRank

section Pointed

variable (k : Type*) [Field k] (S : Type*) [AddCommMonoid S]
    (hzero : ∀ a b : S,a+b=0 → a=0 ∧ b=0)
    [IsDomain (AddMonoidAlgebra k S)] [Algebra.Smooth k (AddMonoidAlgebra k S)]
    (K : Type*) [Field K] [Algebra k K] [Algebra (AddMonoidAlgebra k S) K]
    [IsScalarTower k (AddMonoidAlgebra k S) K]
    [IsFractionRing (AddMonoidAlgebra k S) K]
    {n : ℕ} (bK : Module.Basis (Fin n) K Ω[K⁄k])

include bK in
theorem pointedCotangentFiber_finrank :
    Module.finrank k (PointedCotangentFiber k S hzero) = n := by
  letI := pointedAlgebra k S hzero
  letI := pointedScalarTower k S hzero
  exact smooth_rational_cotangent_finrank k (AddMonoidAlgebra k S) K bK

include hzero bK in
theorem pointed_atoms_card_le {ι : Type*} [Fintype ι]
    (p : ι → S) (hpinj : Function.Injective p)
    (hp0 : ∀ i,p i≠0)
    (hpatom : ∀ i,∀ a b : S,a+b=p i → a=0 ∨ b=0) :
    Fintype.card ι ≤ n := by
  letI := pointedAlgebra k S hzero
  letI := pointedScalarTower k S hzero
  have hli := linearIndependent_pointedCotangentAtoms k S hzero p hpinj hp0 hpatom
  have hcard := hli.fintype_card_le_finrank
  rw [pointedCotangentFiber_finrank k S hzero K bK] at hcard
  exact hcard

end Pointed

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.smooth_rational_cotangent_finrank
#print axioms PaperVerification.ToricCharacters.pointed_atoms_card_le
