module

public import Recovery.Unimodular.GraphicSectionRing.NormalForm

/-!
# Strict minimality of the canonical graphic toric monomial

The argument is descent in a nonnegative integral height.  Every nonstandard
multiset admits an actual quadratic replacement, so descent reaches the unique
standard element of its degree-and-sum fiber.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Unimodular.GraphicSectionRing

def totalHeight {n : ℕ} (M : Multiset (Lattice n)) : ℤ := (M.map height).sum

theorem totalHeight_nonneg {n : ℕ} (M : Multiset (Lattice n)) : 0 ≤ totalHeight M := by
  apply Multiset.sum_nonneg
  intro z hz
  obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hz
  exact height_nonneg x

/-- A nonstandard monomial contains two distinct incompatible variables. -/
theorem exists_incompatible_pair {n : ℕ} {M : Multiset (Lattice n)}
    (hM : ¬ Standard M) :
    ∃ x y R, M = x ::ₘ y ::ₘ R ∧ x ≠ y ∧ ¬ Compatible x y := by
  classical
  unfold Standard at hM
  push_neg at hM
  obtain ⟨x, hx, y, hy, hxy⟩ := hM
  have hne : x ≠ y := by rintro rfl; exact hxy (compatible_refl x)
  obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem hx
  have hyR : y ∈ R := (Multiset.mem_cons.mp hy).resolve_left (Ne.symm hne)
  obtain ⟨S, rfl⟩ := Multiset.exists_cons_of_mem hyR
  exact ⟨x, y, S, rfl, hne, hxy⟩

/-- This is the actual quadratic replacement preserving the toric fiber. -/
theorem exists_height_descent {n : ℕ} {M : Multiset (Lattice n)}
    (hM : ¬ Standard M) :
    ∃ N : Multiset (Lattice n), N.card = M.card ∧ N.sum = M.sum ∧
      totalHeight N < totalHeight M := by
  obtain ⟨x, y, R, rfl, _, hxy⟩ := exists_incompatible_pair hM
  refine ⟨lower x y ::ₘ upper x y ::ₘ R, by simp, ?_, ?_⟩
  · simp only [Multiset.sum_cons, ← add_assoc, lower_add_upper]
  · have h := height_balance_lt x y hxy
    simpa only [totalHeight, Multiset.map_cons, Multiset.sum_cons, ← add_assoc,
      add_lt_add_iff_right] using h

/-- Termination is proved by natural-number induction, not supplied as a premise. -/
theorem exists_standard_le {n : ℕ} (M : Multiset (Lattice n)) :
    ∃ N : Multiset (Lattice n), Standard N ∧ N.card = M.card ∧ N.sum = M.sum ∧
      totalHeight N ≤ totalHeight M := by
  classical
  suffices H : ∀ h : ℕ, ∀ M : Multiset (Lattice n), (totalHeight M).toNat = h →
      ∃ N : Multiset (Lattice n), Standard N ∧ N.card = M.card ∧ N.sum = M.sum ∧
        totalHeight N ≤ totalHeight M by
    exact H _ M rfl
  intro h
  induction h using Nat.strong_induction_on with
  | ind h ih =>
    intro M hM
    by_cases hs : Standard M
    · exact ⟨M, hs, rfl, rfl, le_rfl⟩
    · obtain ⟨N, hcard, hsum, hlt⟩ := exists_height_descent hs
      have hnat : (totalHeight N).toNat < h := by
        rw [← hM]
        have hc : ((totalHeight N).toNat : ℤ) < ((totalHeight M).toNat : ℤ) := by
          simpa only [Int.toNat_of_nonneg (totalHeight_nonneg N),
            Int.toNat_of_nonneg (totalHeight_nonneg M)] using hlt
        exact_mod_cast hc
      obtain ⟨N', hs', hc', hsum', hle'⟩ := ih _ hnat N rfl
      exact ⟨N', hs', hc'.trans hcard, hsum'.trans hsum, hle'.trans hlt.le⟩

theorem canonical_height_le {n : ℕ} (M : Multiset (Lattice n)) :
    totalHeight (canonical M.card M.sum) ≤ totalHeight M := by
  obtain ⟨N, hN, hc, hs, hle⟩ := exists_standard_le M
  have he : N = canonical M.card M.sum := by
    simpa only [hc, hs] using eq_canonical_of_standard N hN
  simpa only [he] using hle

/-- Every nonstandard monomial has strictly larger height than its normal form. -/
theorem canonical_height_lt {n : ℕ} (M : Multiset (Lattice n)) (hM : ¬ Standard M) :
    totalHeight (canonical M.card M.sum) < totalHeight M := by
  obtain ⟨N, hc, hs, hlt⟩ := exists_height_descent hM
  have hle := canonical_height_le N
  rw [hc, hs] at hle
  exact hle.trans_lt hlt

theorem standard_height_lt_of_ne {n : ℕ} (M N : Multiset (Lattice n))
    (hM : Standard M) (hc : M.card = N.card) (hs : M.sum = N.sum) (hne : M ≠ N) :
    totalHeight M < totalHeight N := by
  have hN : ¬ Standard N := by
    intro hN
    exact hne (standard_unique M N hM hN hc hs)
  have he : M = canonical N.card N.sum := by
    simpa only [hc, hs] using eq_canonical_of_standard M hM
  rw [he]
  exact canonical_height_lt N hN

def totalHeightNat {n : ℕ} (M : Multiset (Lattice n)) : ℕ :=
  (M.map (fun x => (height x).toNat)).sum

theorem cast_totalHeightNat {n : ℕ} (M : Multiset (Lattice n)) :
    (totalHeightNat M : ℤ) = totalHeight M := by
  induction M using Multiset.induction_on with
  | empty => rfl
  | cons x M ih =>
    simp only [totalHeightNat, totalHeight, Multiset.map_cons, Multiset.sum_cons,
      Nat.cast_add] at *
    rw [Int.toNat_of_nonneg (height_nonneg x), ih]

theorem totalHeightNat_lt {n : ℕ} {M N : Multiset (Lattice n)} :
    totalHeightNat M < totalHeightNat N ↔ totalHeight M < totalHeight N := by
  rw [← cast_totalHeightNat M, ← cast_totalHeightNat N]
  exact (Nat.cast_lt (α := ℤ)).symm

#print axioms exists_height_descent
#print axioms canonical_height_lt
#print axioms standard_height_lt_of_ne

end Unimodular.GraphicSectionRing
