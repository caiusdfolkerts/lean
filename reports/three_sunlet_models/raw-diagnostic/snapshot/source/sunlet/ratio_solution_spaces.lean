module

public import sunlet.one_hole_field
public import sunlet.invariant_functions
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The strict dimension estimate (5) for the single-color solution spaces.
No cycle-count formula is assumed: a noninvariant solution forces the invariant
space to vanish, while derangements have at least two points in each orbit. -/

@[expose] public section
noncomputable section

namespace Sunlet.RatioSolutionSpaces

variable {Ω K : Type*} [Fintype Ω] [DecidableEq Ω] [Field K] [CharZero K]

def ratioValue (o : Ω) (π : Equiv.Perm Ω) (x : Ω) : K :=
  algebraMap ℚ K (TwoRatioRigidity.ratio o π x)

def solutionSpace (o : Ω) (π : Equiv.Perm Ω) : Submodule K (Ω → K) where
  carrier := {F | F o = 0 ∧ ∃ c d : K, ∀ x, F x - F (π x) = c + ratioValue o π x * d}
  zero_mem' := by
    refine ⟨rfl, 0, 0, ?_⟩
    intro x
    simp
  add_mem' := by
    rintro F G ⟨hFo, c, d, hF⟩ ⟨hGo, e, f, hG⟩
    refine ⟨by simp [hFo, hGo], c + e, d + f, ?_⟩
    intro x
    change F x + G x - (F (π x) + G (π x)) = _
    linear_combination hF x + hG x
  smul_mem' := by
    rintro a F ⟨hFo, c, d, hF⟩
    refine ⟨by simp [hFo], a * c, a * d, ?_⟩
    intro x
    change a * F x - a * F (π x) = _
    linear_combination a * hF x

lemma equation_smul {o : Ω} {π : Equiv.Perm Ω} {F : Ω → K} {c d : K}
    (h : ∀ x, F x - F (π x) = c + ratioValue o π x * d) :
    ∀ x, F x - F (π x) = c + TwoRatioRigidity.ratio o π x • d := by
  intro x
  simpa only [ratioValue, Algebra.smul_def] using h x

lemma invariant_of_mem_of_endpoint_zero {o : Ω} {π : Equiv.Perm Ω} {F : Ω → K}
    (ho : π o ≠ o) (hF : F ∈ solutionSpace (K := K) o π) (he : F (π o) = 0) :
    F ∈ InvariantFunctions.normalized (K := K) o π := by
  obtain ⟨hFo, c, d, h⟩ := hF
  have hendpoint : F (π o) = F o := he.trans hFo.symm
  obtain ⟨hc, hd⟩ := OneHoleField.Ratio.coefficients_zero_of_equal_endpoint ho (equation_smul h) hendpoint
  refine ⟨hFo, ?_⟩
  intro x
  have hh := h x
  rw [hc, hd, mul_zero, zero_add] at hh
  exact (sub_eq_zero.mp hh).symm

/-- Either all solutions are invariant, or endpoint evaluation is injective
and the solution space has dimension at most one. -/
theorem finrank_le_one_or_le_invariants (o : Ω) (π : Equiv.Perm Ω) (ho : π o ≠ o) :
    Module.finrank K (solutionSpace (K := K) o π) ≤ 1 ∨
      solutionSpace (K := K) o π ≤ InvariantFunctions.normalized (K := K) o π := by
  classical
  by_cases hall : ∀ F ∈ solutionSpace (K := K) o π, F (π o) = 0
  · exact Or.inr (fun F hF => invariant_of_mem_of_endpoint_zero ho hF (hall F hF))
  · obtain ⟨F, hF⟩ := not_forall.mp hall
    obtain ⟨hF, hFo'⟩ := not_imp.mp hF
    obtain ⟨hFo, c, d, heq⟩ := hF
    have hnon : F (π o) ≠ F o := by simpa only [hFo] using hFo'
    have hconstant : ∀ G ∈ InvariantFunctions.normalized (K := K) o π, G = 0 := by
      intro G hG
      funext x
      have hh := OneHoleField.Ratio.invariant_constant_of_noninvariant_solution
        ho (equation_smul heq) hnon hG.2 x
      simpa only [hG.1, Pi.zero_apply] using hh
    let ev : solutionSpace (K := K) o π →ₗ[K] K :=
      { toFun := fun G => G.1 (π o)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have hinj : Function.Injective ev := by
      apply (injective_iff_map_eq_zero ev).mpr
      intro G hG
      apply Subtype.ext
      exact hconstant G.1 (invariant_of_mem_of_endpoint_zero ho G.2 hG)
    have hdim := LinearMap.finrank_le_finrank_of_injective hinj
    exact Or.inl (by simpa using hdim)

theorem twice_finrank_add_two_le (o : Ω) (π : Equiv.Perm Ω)
    (hm : 4 ≤ Fintype.card Ω) (hder : ∀ x, π x ≠ x) :
    2 * Module.finrank K (solutionSpace (K := K) o π) + 2 ≤ Fintype.card Ω := by
  rcases finrank_le_one_or_le_invariants (K := K) o π (hder o) with h | h
  · omega
  · have hdim := Submodule.finrank_mono h
    have hbound := InvariantFunctions.normalized_rank_bound (K := K) o π hder
    omega

/-- The strict pairwise W-space estimate required in Proposition 4.5. -/
theorem sum_finrank_lt (o : Ω) (π σ : Equiv.Perm Ω)
    (hm : 5 ≤ Fintype.card Ω) (hπ : ∀ x, π x ≠ x) (hσ : ∀ x, σ x ≠ x) :
    Module.finrank K (solutionSpace (K := K) o π) +
      Module.finrank K (solutionSpace (K := K) o σ) < Fintype.card Ω - 1 := by
  have hp := twice_finrank_add_two_le (K := K) o π (by omega) hπ
  have hq := twice_finrank_add_two_le (K := K) o σ (by omega) hσ
  omega

end Sunlet.RatioSolutionSpaces
