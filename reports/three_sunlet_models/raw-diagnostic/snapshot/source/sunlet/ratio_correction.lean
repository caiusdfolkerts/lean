module

public import sunlet.ratio_solution_spaces
public import sunlet.contact_linear

/-! Reversal of ratio equations and the rank-one correction in equation (6). -/

@[expose] public section
noncomputable section

namespace Sunlet.RatioSolutionSpaces

variable {Ω K : Type*} [Fintype Ω] [DecidableEq Ω] [Field K] [CharZero K]

lemma ratioValue_reverse (o : Ω) (π : Equiv.Perm Ω) (x : Ω) :
    ratioValue (K := K) o π.symm (π x) = (ratioValue o π x)⁻¹ := by
  simp [ratioValue, TwoRatioRigidity.ratio, inv_div]

lemma ratioValue_inverse_reverse (o : Ω) (π : Equiv.Perm Ω) (x : Ω) :
    (ratioValue (K := K) o π (π.symm x))⁻¹ = ratioValue o π.symm x := by
  simpa using (ratioValue_reverse (K := K) o π (π.symm x)).symm

/-- The inverse-ratio solution space is exactly the forward-ratio space of
the inverse permutation, with a proved equivalence of its defining equations. -/
theorem mem_inverse_solutionSpace_iff (o : Ω) (π : Equiv.Perm Ω) (F : Ω → K) :
    F ∈ solutionSpace (K := K) o π.symm ↔
      F o = 0 ∧ ∃ c d : K, ∀ x, F x - F (π x) = c + (ratioValue o π x)⁻¹ * d := by
  constructor
  · rintro ⟨hFo, c, d, h⟩
    refine ⟨hFo, -c, -d, ?_⟩
    intro x
    have hh := h (π x)
    rw [Equiv.symm_apply_apply, ratioValue_reverse] at hh
    linear_combination -hh
  · rintro ⟨hFo, c, d, h⟩
    refine ⟨hFo, -c, -d, ?_⟩
    intro x
    have hh := h (π.symm x)
    rw [Equiv.apply_symm_apply, ratioValue_inverse_reverse] at hh
    linear_combination -hh

def baseComplement (o : Ω) (x : Ω) : K := if x = o then 0 else 1

def neighborSum (o : Ω) (π : Equiv.Perm Ω) : (Ω → K) →ₗ[K] K :=
  ContactLinear.evaluation (π o) + ContactLinear.evaluation (π.symm o)

@[simp] theorem neighborSum_apply (o : Ω) (π : Equiv.Perm Ω) (H : Ω → K) :
    neighborSum (K := K) o π H = H (π o) + H (π.symm o) := rfl

def corrected (o : Ω) (π : Equiv.Perm Ω) : (Ω → K) →ₗ[K] (Ω → K) :=
  LinearMap.id - (neighborSum (K := K) o π).smulRight (baseComplement o)

@[simp] theorem corrected_apply (o : Ω) (π : Equiv.Perm Ω) (H : Ω → K) (x : Ω) :
    corrected (K := K) o π H x = H x - (H (π o) + H (π.symm o)) * baseComplement o x := rfl

@[simp] theorem corrected_base (o : Ω) (π : Equiv.Perm Ω) (H : Ω → K) :
    corrected (K := K) o π H o = H o := by simp [baseComplement]

lemma inverse_moves {o : Ω} {π : Equiv.Perm Ω} (h : π o ≠ o) : π.symm o ≠ o := by
  intro he
  apply h
  simpa using (congrArg π he).symm

/-- Exact equation (6), checked at both exceptional endpoints and every
ordinary edge. -/
theorem correction_identity (o : Ω) (π : Equiv.Perm Ω) (ho : π o ≠ o)
    (H : Ω → K) (hH : H o = 0) (x : Ω) :
    (ratioValue o π x)⁻¹ * (H x - H (π x)) -
      (corrected o π H x - corrected o π H (π x)) =
        -(2 * H (π o) + H (π.symm o)) * ((ratioValue o π x)⁻¹ - 1) := by
  by_cases hx : x = o
  · subst x
    simp [ratioValue, TwoRatioRigidity.ratio, TwoRatioRigidity.scale, corrected_apply,
      baseComplement, ho, hH]
    ring
  · by_cases hp : π x = o
    · have hxo : x = π.symm o := π.injective (hp.trans (π.apply_symm_apply o).symm)
      subst x
      simp [ratioValue, TwoRatioRigidity.ratio, TwoRatioRigidity.scale, corrected_apply,
        baseComplement, inverse_moves ho, hH]
      ring
    · simp [ratioValue, TwoRatioRigidity.ratio, TwoRatioRigidity.scale, corrected_apply,
        baseComplement, hx, hp]

theorem corrected_difference_surjective (o : Ω) (π σ : Equiv.Perm Ω)
    (hπ : π o ≠ o) (hσ : σ o ≠ o) (p q : K) (hpq : p ≠ q) :
    Function.Surjective (p • corrected (K := K) o π - q • corrected (K := K) o σ) := by
  let μ : (Ω → K) →ₗ[K] K := p • neighborSum o π - q • neighborSum o σ
  have hμ : μ (baseComplement (K := K) o) = 2 * (p - q) := by
    simp [μ, baseComplement, hπ, hσ, inverse_moves hπ, inverse_moves hσ]
    ring
  have he : p • corrected (K := K) o π - q • corrected (K := K) o σ =
      ContactLinear.reflectionOperator (baseComplement o) μ (p - q) := by
    apply LinearMap.ext
    intro H
    funext x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, corrected_apply, ContactLinear.reflectionOperator_apply,
      neighborSum_apply, μ]
    ring
  rw [he]
  exact ContactLinear.reflectionOperator_surjective _ _ _ hμ (sub_ne_zero.mpr hpq)

end Sunlet.RatioSolutionSpaces
