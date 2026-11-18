module

public import sunlet.contact_coefficient
public import sunlet.ratio_correction

/-! The two single-color equation spaces arising from the actual sparse
paired differential. The normalization at the distinguished point removes
only constants, whose differences vanish. -/

@[expose] public section
noncomputable section

namespace Sunlet.Contact

open RatioSolutionSpaces

variable {ι Ω K : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
  [Field K] [CharZero K]

lemma mem_tangentSpan_iff_field (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (t : ι × Ω → K) :
    t ∈ tangentSpan π o A B ↔ ∃ (c : ι → K) (J : Ω → K) (d : ι → K) (M : Ω → K),
      J o = 0 ∧ M o = 0 ∧ ∀ a x,
      t (a, x) = c a + (if a ∈ A then J x - J (π a x) else 0) +
        ratioValue o (π a) x * (d a + if a ∈ B then M x - M (π a x) else 0) := by
  constructor
  · intro h
    obtain ⟨c, J, d, M, h⟩ := (mem_tangentSpan_iff π o A B t).mp h
    refine ⟨c, fun x => J x - J o, d, fun x => M x - M o, by simp, by simp, ?_⟩
    intro a x
    have hh := h a x
    simp only [Algebra.smul_def] at hh
    simpa only [sub_sub_sub_cancel_right, ratioValue] using hh
  · rintro ⟨c, J, d, M, _, _, h⟩
    apply (mem_tangentSpan_iff π o A B t).mpr
    refine ⟨c, J, d, M, ?_⟩
    intro a x
    simpa only [ratioValue, Algebra.smul_def] using h a x

/-- The remaining contact condition after the torus velocity has vanished. -/
def TorusContact (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (p : ι → K) : Prop :=
  ∀ H : Ω → K, (fun ax : ι × Ω => p ax.1 * (H ax.2 - H (π ax.1 ax.2))) ∈
    tangentSpan π o A B

lemma forward_solution_of_equation (o : Ω) (π : Equiv.Perm Ω)
    (H J : Ω → K) (hH : H o = 0) (hJ : J o = 0) (p c d : K)
    (h : ∀ x, p * (H x - H (π x)) = c + (J x - J (π x)) + ratioValue o π x * d) :
    (fun x => J x - p * H x) ∈ solutionSpace (K := K) o π := by
  refine ⟨by simp [hH, hJ], -c, -d, ?_⟩
  intro x
  linear_combination -h x

lemma inverse_solution_of_equation (o : Ω) (π : Equiv.Perm Ω) (ho : π o ≠ o)
    (H M : Ω → K) (hH : H o = 0) (hM : M o = 0) (p c d : K)
    (h : ∀ x, p * (H x - H (π x)) = c + ratioValue o π x * (d + M x - M (π x))) :
    (fun x => M x - p * corrected o π H x) ∈ solutionSpace (K := K) o π.symm := by
  apply (mem_inverse_solutionSpace_iff o π _).mpr
  refine ⟨by simp [hH, hM, baseComplement], -d + p * (2 * H (π o) + H (π.symm o)),
    -c - p * (2 * H (π o) + H (π.symm o)), ?_⟩
  intro x
  have hr : ratioValue (K := K) o π x ≠ 0 := by
    exact (map_ne_zero (algebraMap ℚ K)).mpr (SparseTangentPair.ratio_ne_zero o π x)
  have hh := congrArg (fun z : K => (ratioValue o π x)⁻¹ * z) (h x)
  have hh' : (ratioValue o π x)⁻¹ * (p * (H x - H (π x))) =
      (ratioValue o π x)⁻¹ * c + (d + M x - M (π x)) := by
    simpa only [mul_add, ← mul_assoc, inv_mul_cancel₀ hr, one_mul] using hh
  have hc := correction_identity o π ho H hH x
  linear_combination -hh' + p * hc

lemma inverse_derangement {π : Equiv.Perm Ω} (hπ : ∀ x, π x ≠ x) :
    ∀ x, π.symm x ≠ x := by
  intro x hx
  exact hπ x (by simpa using (congrArg π hx).symm)

end Sunlet.Contact
