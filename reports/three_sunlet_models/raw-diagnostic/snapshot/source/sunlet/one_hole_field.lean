module

public import sunlet.two_ratio_rigidity
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination

/-! Characteristic-zero one-hole identities used in the contact calculation. -/

@[expose] public section
noncomputable section

namespace Sunlet.OneHoleField

variable {Ω V K : Type*} [Fintype Ω] [DecidableEq Ω]

theorem outgoing_injective [AddCommGroup V] [Module ℚ V]
    {o : Ω} {π : Equiv.Perm Ω} {F : Ω → V} {c : V}
    (h : ∀ x, x ≠ o → F (π x) - F x = c) (hc : c ≠ 0) : Function.Injective F := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℚ hc
  have hp : PuncturedDifferences.Outgoing o π (fun x => φ (F x)) (φ c) := by
    intro x hx
    simpa only [map_sub] using congrArg φ (h x hx)
  have hi := PuncturedDifferences.injective_of_nonzero hp hφ
  intro x y he
  exact hi (congrArg φ he)

/-- A nonzero one-hole difference forces every invariant field-valued
function to be constant. This avoids any use of permutation cycle syntax. -/
theorem invariant_constant [Field K] [CharZero K]
    {o : Ω} {π : Equiv.Perm Ω} {F G : Ω → K} {c : K}
    (hF : ∀ x, x ≠ o → F (π x) - F x = c) (hc : c ≠ 0)
    (hG : ∀ x, G (π x) = G x) : ∀ x, G x = G o := by
  intro x
  by_contra hx
  let t : K := (F o - F x) / (G x - G o)
  let H : Ω → K := fun z => F z + t * G z
  have hH : ∀ z, z ≠ o → H (π z) - H z = c := by
    intro z hz
    dsimp [H]
    rw [hG]
    linear_combination hF z hz
  have he : H x = H o := by
    dsimp [H, t]
    field_simp [sub_ne_zero.mpr hx]
    ring
  have hxo := outgoing_injective hH hc he
  exact hx (congrArg G hxo)

namespace Ratio

open TwoRatioRigidity

theorem shifted_outgoing [AddCommGroup V] [Module ℚ V]
    {o : Ω} {π : Equiv.Perm Ω} {F : Ω → V} {c d : V}
    (h : ∀ x, F x - F (π x) = c + ratio o π x • d) :
    ∀ x, x ≠ o →
      (F (π x) - if π x = o then 0 else d) - (F x - d) = -(c + d) := by
  intro x hx
  have he := h x
  by_cases hp : π x = o
  · simp only [ratio, scale, if_neg hx, if_pos hp] at he
    norm_num at he
    simp only [if_pos hp, sub_zero]
    calc
      F (π x) - (F x - d) = -(F x - F (π x)) + d := by module
      _ = -(c + (2 : ℚ) • d) + d := by rw [he]
      _ = -(c + d) := by module
  · simp only [ratio, scale, if_neg hx, if_neg hp] at he
    norm_num at he
    simp only [if_neg hp]
    calc
      (F (π x) - d) - (F x - d) = -(F x - F (π x)) := by module
      _ = -(c + d) := by rw [he]

theorem coefficient_relation [AddCommGroup V] [Module ℚ V]
    {o : Ω} {π : Equiv.Perm Ω} {F : Ω → V} {c d : V}
    (ho : π o ≠ o) (h : ∀ x, F x - F (π x) = c + ratio o π x • d) :
    d = (2 * (Fintype.card Ω : ℚ)) • (-(c + d)) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro φ
  have hφ : Equation o π (fun x => φ (F x)) (φ c) (φ d) := by
    intro x
    simpa only [map_sub, map_add, map_smul, smul_eq_mul, mul_comm] using congrArg φ (h x)
  have he := TwoRatioRigidity.coefficient_relation ho hφ
  simpa only [map_sub, map_smul, map_neg, map_add, smul_eq_mul, sub_eq_zero] using he

/-- The exceptional coefficient is zero whenever the two endpoint values
coincide. -/
theorem coefficients_zero_of_equal_endpoint [AddCommGroup V] [Module ℚ V]
    {o : Ω} {π : Equiv.Perm Ω} {F : Ω → V} {c d : V}
    (ho : π o ≠ o) (h : ∀ x, F x - F (π x) = c + ratio o π x • d)
    (he : F (π o) = F o) : c = 0 ∧ d = 0 := by
  have hf (φ : Module.Dual ℚ V) : φ c = 0 ∧ φ d = 0 := by
    have hφ : Equation o π (fun x => φ (F x)) (φ c) (φ d) := by
      intro x
      simpa only [map_sub, map_add, map_smul, smul_eq_mul, mul_comm] using congrArg φ (h x)
    have hd := TwoRatioRigidity.coefficient_relation ho hφ
    have hb := hφ o
    simp [ratio, scale, ho, he] at hb
    have hn : 0 ≤ (Fintype.card Ω : ℚ) := Nat.cast_nonneg _
    have hz : φ d = 0 := by nlinarith
    exact ⟨by linarith, hz⟩
  exact ⟨(Module.forall_dual_apply_eq_zero_iff ℚ c).mp (fun φ => (hf φ).1),
    (Module.forall_dual_apply_eq_zero_iff ℚ d).mp (fun φ => (hf φ).2)⟩

theorem invariant_constant_of_noninvariant_solution [Field K] [CharZero K]
    {o : Ω} {π : Equiv.Perm Ω} {F G : Ω → K} {c d : K}
    (ho : π o ≠ o) (h : ∀ x, F x - F (π x) = c + ratio o π x • d)
    (he : F (π o) ≠ F o) (hG : ∀ x, G (π x) = G x) : ∀ x, G x = G o := by
  have hc : -(c + d) ≠ 0 := by
    intro hc
    have hd : d = 0 := by simpa only [hc, smul_zero] using coefficient_relation ho h
    have hc' : c = 0 := by simpa [hd] using hc
    apply he
    have hb := h o
    rw [hc', hd, smul_zero, zero_add] at hb
    exact (sub_eq_zero.mp hb).symm
  apply invariant_constant (F := fun x => F x - if x = o then 0 else d) (c := -(c + d))
    (hc := hc) (hG := hG)
  intro x hx
  simpa only [if_neg hx] using shifted_outgoing h x hx

end Ratio
end Sunlet.OneHoleField
