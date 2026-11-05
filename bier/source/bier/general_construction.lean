import bier.isolated_nonpolytopal

/-! The final paragraph's literal parameter range: the binomial inequality alone. -/
namespace Bier

theorem general_allSign_construction_unrestricted (m k : ℕ)
    (hchoose : m ^ 2 - m + 2 ≤ m.choose k) :
    ∃ h : (m ^ 2 - m + 1) + 1 ≤ m.choose k,
      (patternInput m k (m ^ 2 - m + 1) h).dimension = k ∧
      (patternSphere m k (m ^ 2 - m + 1) h).IsSphere
        (m + 2 ^ (m ^ 2 - m + 1) - 1) ∧
      (patternSphere m k (m ^ 2 - m + 1) h).vertices.card =
        2 * (m + 2 ^ (m ^ 2 - m + 1)) + 1 ∧
      ¬ Polytopal (patternSphere m k (m ^ 2 - m + 1) h) := by
  have hk : 1 ≤ k := by
    by_cases he : k = 0
    · simp only [he, Nat.choose_zero_right] at hchoose
      omega
    · omega
  have hkm : k < m := by
    by_contra hn
    have hm : m ≤ k := by omega
    by_cases he : m = k
    · rw [← he, Nat.choose_self] at hchoose
      omega
    · have hlt : m < k := lt_of_le_of_ne hm he
      rw [Nat.choose_eq_zero_of_lt hlt] at hchoose
      omega
  exact general_allSign_construction m k hk hkm hchoose

end Bier
