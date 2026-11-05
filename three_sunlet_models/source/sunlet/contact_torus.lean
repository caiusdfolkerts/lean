module

public import sunlet.contact_equations
public import sunlet.ordinary_edge_rigidity

/-! The coefficient restrictions in the torus half of Proposition 4.5. -/

@[expose] public section
noncomputable section

namespace Sunlet.Contact

open RatioSolutionSpaces

variable {ι Ω K : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
  [Field K] [CharZero K]

lemma scalar_mem_of_nonzero_smul (W : Submodule K (Ω → K)) (p : K) (hp : p ≠ 0)
    (H : Ω → K) (h : p • H ∈ W) : H ∈ W := by
  have hh := W.smul_mem p⁻¹ h
  simpa only [smul_smul, inv_mul_cancel₀ hp, one_smul] using hh

/-- The coefficient velocity is constant on the first support. The strict
W-space bound is applied to an actual normalized test direction. -/
theorem coefficient_constant_on_first
    (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hdis : Disjoint A B) (hm : 5 ≤ Fintype.card Ω)
    (hder : ∀ a, ∀ x, π a x ≠ x) (p : ι → K)
    (hp : TorusContact π o A B p) : ∀ a ∈ A, ∀ b ∈ A, p a = p b := by
  intro a ha b hb
  by_contra hab
  obtain ⟨H, hHo, hH⟩ := ContactLinear.exists_outside_sum o
    (solutionSpace (K := K) o (π a)) (solutionSpace o (π b))
    (sum_finrank_lt o (π a) (π b) hm (hder a) (hder b))
  obtain ⟨c, J, d, M, hJo, _, ht⟩ := (mem_tangentSpan_iff_field π o A B _).mp (hp H)
  have haB : a ∉ B := fun hh => Set.disjoint_left.mp hdis ha hh
  have hbB : b ∉ B := fun hh => Set.disjoint_left.mp hdis hb hh
  have hA : (fun x => J x - p a * H x) ∈ solutionSpace (K := K) o (π a) := by
    apply forward_solution_of_equation o (π a) H J hHo hJo (p a) (c a) (d a)
    intro x
    simpa only [if_pos ha, if_neg haB, add_zero] using ht a x
  have hB : (fun x => J x - p b * H x) ∈ solutionSpace (K := K) o (π b) := by
    apply forward_solution_of_equation o (π b) H J hHo hJo (p b) (c b) (d b)
    intro x
    simpa only [if_pos hb, if_neg hbB, add_zero] using ht b x
  let W := solutionSpace (K := K) o (π a) ⊔ solutionSpace o (π b)
  have hA' : (fun x => J x - p a * H x) ∈ W := Submodule.mem_sup.mpr ⟨_, hA, 0, Submodule.zero_mem _, by simp⟩
  have hB' : (fun x => J x - p b * H x) ∈ W := Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, _, hB, by simp⟩
  have hh : (p a - p b) • H ∈ W := by
    convert W.sub_mem hB' hA' using 1
    funext x
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  exact hH (scalar_mem_of_nonzero_smul W _ (sub_ne_zero.mpr hab) H hh)

/-- The coefficient velocity is constant on the second support. The exact
rank-one correction is used, rather than assuming its invertibility. -/
theorem coefficient_constant_on_second
    (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hdis : Disjoint A B) (hm : 5 ≤ Fintype.card Ω)
    (hder : ∀ a, ∀ x, π a x ≠ x) (p : ι → K)
    (hp : TorusContact π o A B p) : ∀ a ∈ B, ∀ b ∈ B, p a = p b := by
  intro a ha b hb
  by_contra hab
  obtain ⟨Z, hZo, hZ⟩ := ContactLinear.exists_outside_sum o
    (solutionSpace (K := K) o (π a).symm) (solutionSpace o (π b).symm)
    (sum_finrank_lt o (π a).symm (π b).symm hm
      (inverse_derangement (hder a)) (inverse_derangement (hder b)))
  obtain ⟨H, hH⟩ := corrected_difference_surjective o (π a) (π b)
    (hder a o) (hder b o) (p a) (p b) hab Z
  have hHo : H o = 0 := by
    have hh := congrFun hH o
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, corrected_base, hZo] at hh
    exact (mul_eq_zero.mp (show (p a - p b) * H o = 0 by linear_combination hh)).resolve_left
      (sub_ne_zero.mpr hab)
  obtain ⟨c, J, d, M, _, hMo, ht⟩ := (mem_tangentSpan_iff_field π o A B _).mp (hp H)
  have haA : a ∉ A := fun hh => Set.disjoint_left.mp hdis hh ha
  have hbA : b ∉ A := fun hh => Set.disjoint_left.mp hdis hh hb
  have hA : (fun x => M x - p a * corrected o (π a) H x) ∈
      solutionSpace (K := K) o (π a).symm := by
    apply inverse_solution_of_equation o (π a) (hder a o) H M hHo hMo (p a) (c a) (d a)
    intro x
    simpa only [if_neg haA, if_pos ha, add_zero, add_sub_assoc] using ht a x
  have hB : (fun x => M x - p b * corrected o (π b) H x) ∈
      solutionSpace (K := K) o (π b).symm := by
    apply inverse_solution_of_equation o (π b) (hder b o) H M hHo hMo (p b) (c b) (d b)
    intro x
    simpa only [if_neg hbA, if_pos hb, add_zero, add_sub_assoc] using ht b x
  let W := solutionSpace (K := K) o (π a).symm ⊔ solutionSpace o (π b).symm
  have hA' : (fun x => M x - p a * corrected o (π a) H x) ∈ W := Submodule.mem_sup.mpr ⟨_, hA, 0, Submodule.zero_mem _, by simp⟩
  have hB' : (fun x => M x - p b * corrected o (π b) H x) ∈ W := Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, _, hB, by simp⟩
  apply hZ
  convert W.sub_mem hB' hA' using 1
  funext x
  have hh := congrFun hH x
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at hh
  simp only [Pi.sub_apply]
  linear_combination -hh

end Sunlet.Contact
