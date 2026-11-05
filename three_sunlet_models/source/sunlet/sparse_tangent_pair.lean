module

public import sunlet.two_ratio_rigidity
public import Mathlib.Tactic.Module

/-! The injective sparse tangent pair from Section 4.2.
The equations below are the literal coefficient and logarithmic-torus
differential of the two ratio monomial parameterizations. -/

@[expose] public section
noncomputable section

namespace Sunlet.SparseTangentPair

open TwoRatioRigidity

variable {ι Ω V : Type*} [Fintype Ω] [DecidableEq Ω]
  [AddCommGroup V] [Module ℚ V]

lemma ratio_ne_zero (o : Ω) (π : Equiv.Perm Ω) (x : Ω) : ratio o π x ≠ 0 := by
  unfold ratio scale
  split_ifs <;> norm_num

lemma coefficients_zero {o : Ω} {π : Equiv.Perm Ω} {p q : V}
    (ho : π o ≠ o) (h : ∀ x, p + ratio o π x • q = 0) : p = 0 ∧ q = 0 := by
  have hi : π.symm o ≠ o := by
    intro he
    apply ho
    simpa using (congrArg π he).symm
  have h₁ : p + (1 / 2 : ℚ) • q = 0 := by simpa [ratio, scale, ho] using h o
  have h₂ : p + (2 : ℚ) • q = 0 := by simpa [ratio, scale, hi] using h (π.symm o)
  have hq : q = 0 := by
    calc
      q = (2 / 3 : ℚ) • ((p + (2 : ℚ) • q) - (p + (1 / 2 : ℚ) • q)) := by module
      _ = 0 := by rw [h₁, h₂]; simp
  exact ⟨by simpa [hq] using h₁, hq⟩

/-- The sparse differential has trivial kernel for disjoint transitive support
families with two distinct colors in each family. -/
theorem kernel_eq_zero
    (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hdisjoint : Disjoint A B)
    (hmoves : ∀ a, π a o ≠ o)
    (hAtwo : ∃ a ∈ A, ∃ b ∈ A, π a ≠ π b)
    (hBtwo : ∃ a ∈ B, ∃ b ∈ B, π a ≠ π b)
    (hAtrans : TransitiveFamily π A) (hBtrans : TransitiveFamily π B)
    (p q : ι → V) (K M : Ω → V) (hKo : K o = 0) (hMo : M o = 0)
    (h : ∀ a x, p a + (if a ∈ A then K x - K (π a x) else 0) +
        ratio o (π a) x • (q a + if a ∈ B then M x - M (π a x) else 0) = 0) :
    (∀ a, p a = 0) ∧ (∀ a, q a = 0) ∧ (∀ x, K x = 0) ∧ (∀ x, M x = 0) := by
  have hK : ∀ a ∈ A, ∀ x, K x - K (π a x) = -p a + ratio o (π a) x • (-q a) := by
    intro a ha x
    have hb : a ∉ B := fun hb => Set.disjoint_left.mp hdisjoint ha hb
    have hh := h a x
    simp only [if_pos ha, if_neg hb, add_zero] at hh
    have he : (K x - K (π a x)) + (p a + ratio o (π a) x • q a) = 0 := by
      simpa only [add_assoc, add_comm, add_left_comm] using hh
    have he' := eq_neg_iff_add_eq_zero.mpr he
    simpa only [neg_add, smul_neg, add_comm] using he'
  have hKinv := TwoRatioRigidity.family (fun a _ => hmoves a) hAtwo hK
  have hKzero : ∀ x, K x = 0 := by
    intro x
    rw [invariant_constant_of_transitive hAtrans (fun a ha => (hKinv a ha).2.2) o x, hKo]
  have hM : ∀ a ∈ B, ∀ x, M x - M (π a x) = -q a + (ratio o (π a) x)⁻¹ • (-p a) := by
    intro a hb x
    have ha : a ∉ A := fun ha => Set.disjoint_left.mp hdisjoint ha hb
    have hh := congrArg (fun z : V => (ratio o (π a) x)⁻¹ • z) (h a x)
    simp only [if_neg ha, if_pos hb, add_zero, smul_add, smul_smul, smul_zero] at hh
    simp only [inv_mul_cancel₀ (ratio_ne_zero o (π a) x), one_smul] at hh
    have he : (M x - M (π a x)) + (q a + (ratio o (π a) x)⁻¹ • p a) = 0 := by
      simpa only [add_assoc, add_comm, add_left_comm] using hh
    have he' := eq_neg_iff_add_eq_zero.mpr he
    simpa only [neg_add, smul_neg, add_comm] using he'
  have hMinv := TwoRatioRigidity.family_inverse (fun a _ => hmoves a) hBtwo hM
  have hMzero : ∀ x, M x = 0 := by
    intro x
    rw [invariant_constant_of_transitive hBtrans (fun a ha => (hMinv a ha).2.2) o x, hMo]
  have hpq : ∀ a, p a = 0 ∧ q a = 0 := by
    intro a
    apply coefficients_zero (hmoves a)
    intro x
    simpa only [hKzero, hMzero, sub_self, ite_self, add_zero] using h a x
  exact ⟨fun a => (hpq a).1, fun a => (hpq a).2, hKzero, hMzero⟩

end Sunlet.SparseTangentPair
