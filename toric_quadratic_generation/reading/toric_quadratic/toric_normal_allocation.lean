module
public import PaperVerification.ToricSimplexParity
@[expose] public section
/-!
# Integral normal-height and fiber allocations

The bounded parity split is the exact token-allocation argument of Section 6.5.
It treats every number of coordinates and every prescribed residue vector.
The ordinary fiber allocation is used in the adjoint argument of Section 7.5.
-/

namespace PaperVerification.Toric

open scoped BigOperators

/-- Split a positive normal-height vector in every prescribed parity, while
keeping both total heights at most `R`. The reserve of three is the one used
in Section 6.5 to compensate for both floor operations. -/
theorem bounded_parity_split_nat {q R : ℕ} (hq : q ≤ R)
    (m e : Fin q → ℕ) (hm : ∀ i, 0 < m i) (he : ∀ i, e i ≤ 1)
    (hbudget : (∑ i, m i) + 3 ≤ 2 * R) :
    ∃ h k : Fin q → ℕ,
      (∀ i, h i + k i = m i) ∧ (∑ i, h i) ≤ R ∧ (∑ i, k i) ≤ R ∧
      (∀ i, h i % 2 = e i) := by
  let c : Fin q → ℕ := fun i => (m i - e i) / 2
  let f : Fin q → ℕ := fun i => (m i - e i) % 2
  have hcoord (i : Fin q) : e i + 2 * c i + f i = m i := by
    have hmi := hm i
    have hei := he i
    dsimp only [c, f]
    omega
  have hf (i : Fin q) : f i ≤ 1 := by dsimp only [f]; omega
  have hE : (∑ i, e i) ≤ R := by
    have h : (∑ i, e i) ≤ q := calc
      _ ≤ ∑ _ : Fin q, 1 := Finset.sum_le_sum (fun i _ => he i)
      _ = q := by simp
    exact h.trans hq
  have hF : (∑ i, f i) ≤ R := by
    have h : (∑ i, f i) ≤ q := calc
      _ ≤ ∑ _ : Fin q, 1 := Finset.sum_le_sum (fun i _ => hf i)
      _ = q := by simp
    exact h.trans hq
  have htotal : (∑ i, e i) + 2 * (∑ i, c i) + (∑ i, f i) = ∑ i, m i := by
    calc
      _ = ∑ i, (e i + 2 * c i + f i) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ i, m i := Finset.sum_congr rfl (fun i _ => hcoord i)
  let U := (R - ∑ i, e i) / 2
  let V := (R - ∑ i, f i) / 2
  have hcapacity : (∑ i, c i) ≤ U + V := by
    dsimp only [U, V]
    omega
  obtain ⟨u, hu, husum⟩ := allocate_le_sum Finset.univ c ((∑ i, c i) - V)
    (Nat.sub_le _ _)
  let h : Fin q → ℕ := fun i => e i + 2 * u i
  let k : Fin q → ℕ := fun i => f i + 2 * (c i - u i)
  have huv (i : Fin q) : u i ≤ c i := hu i (Finset.mem_univ i)
  have hhsum : (∑ i, h i) = (∑ i, e i) + 2 * ((∑ i, c i) - V) := by
    simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, husum]
  have hksum : (∑ i, k i) = (∑ i, f i) +
      2 * ((∑ i, c i) - ((∑ i, c i) - V)) := by
    simp only [k, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_tsub_distrib Finset.univ (fun i _ => huv i), husum]
  refine ⟨h, k, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi := huv i
    have hci := hcoord i
    change e i + 2 * u i + (f i + 2 * (c i - u i)) = m i
    omega
  · rw [hhsum]
    dsimp only [U, V] at hcapacity ⊢
    omega
  · rw [hksum]
    dsimp only [V]
    omega
  · intro i
    have hi := he i
    change (e i + 2 * u i) % 2 = e i
    omega

/-- Section 6.5 in the actual integer normal lattice, with no restriction on
the chosen integer representative of the parity class. -/
theorem bounded_parity_split_integer {q R : ℕ} (hq : q ≤ R)
    (m α : Fin q → ℤ) (hm : ∀ i, 0 < m i)
    (hbudget : (∑ i, m i) + 3 ≤ 2 * (R : ℤ)) :
    ∃ h k : Fin q → ℤ,
      (∀ i, 0 ≤ h i) ∧ (∀ i, 0 ≤ k i) ∧ h + k = m ∧
      (∑ i, h i) ≤ R ∧ (∑ i, k i) ≤ R ∧
      ∃ w : Fin q → ℤ, h - α = w + w := by
  let mN : Fin q → ℕ := fun i => (m i).toNat
  let e : Fin q → ℕ := fun i => (α i % 2).toNat
  have hmcast (i : Fin q) : (mN i : ℤ) = m i :=
    Int.toNat_of_nonneg (hm i).le
  have hmN (i : Fin q) : 0 < mN i := by
    have hi := hm i
    dsimp only [mN]
    omega
  have he (i : Fin q) : e i ≤ 1 := by dsimp only [e]; omega
  have hsumcast : ((∑ i, mN i : ℕ) : ℤ) = ∑ i, m i := by
    simp only [Nat.cast_sum, hmcast]
  have hbudgetN : (∑ i, mN i) + 3 ≤ 2 * R := by omega
  obtain ⟨hN, kN, hsum, hh, hk, hpar⟩ :=
    bounded_parity_split_nat hq mN e hmN he hbudgetN
  refine ⟨fun i => hN i, fun i => kN i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Nat.cast_nonneg _
  · intro i
    exact Nat.cast_nonneg _
  · funext i
    have hi := hsum i
    have hmi := hmcast i
    change (hN i : ℤ) + (kN i : ℤ) = m i
    omega
  · simpa only [← Nat.cast_sum, Nat.cast_le] using hh
  · simpa only [← Nat.cast_sum, Nat.cast_le] using hk
  · apply (integer_parity_iff_double _ α).mp
    intro i
    have hi := hpar i
    have hei : (e i : ℤ) = α i % 2 :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
    change ((hN i : ℤ) - α i) % 2 = 0
    omega

/-- A nonnegative homogeneous fiber vector admits any prescribed first
total between zero and its total degree. No positivity or parity is required. -/
theorem homogeneous_degree_split {q a b : ℕ} (m : Fin q → ℕ)
    (hm : ∑ i, m i = a + b) :
    ∃ u v : Fin q → ℕ, (∀ i, u i + v i = m i) ∧
      (∑ i, u i) = a ∧ (∑ i, v i) = b := by
  obtain ⟨u, hu, hsum⟩ := allocate_le_sum Finset.univ m a (by omega)
  refine ⟨u, fun i => m i - u i, ?_, hsum, ?_⟩
  · intro i
    have hi := hu i (Finset.mem_univ i)
    change u i + (m i - u i) = m i
    omega
  · rw [Finset.sum_tsub_distrib Finset.univ hu, hm, hsum]
    omega

end PaperVerification.Toric
