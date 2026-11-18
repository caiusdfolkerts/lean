module

public import sunlet.orbit_height

/-! The complete normalized height conclusion of Lemma 7.3. -/

@[expose] public section
noncomputable section

namespace Sunlet.OrbitHeight.InverseStablePartition

variable {G C : Type*} [AddCommGroup G] [Fintype G] [Fintype C]
  [LinearOrder C] (P : InverseStablePartition G C)

theorem normalized_nonnegative_height {x : C → ℚ} (hx : x ∈ P.heightSpace)
    (hn : ∀ i, 0 ≤ x i) (hzero : x ≠ 0) :
    ∃ r : ℚ, r ≠ 0 ∧
      let y := r • x
      y ∈ P.heightSpace ∧ Monotone y ∧
      (∀ i, y i = 0 ∨ y i = 1 ∨ y i = 2) ∧
      (∀ i, y i = 2 → P.sameClassDifference i) := by
  obtain ⟨a, ha, hlevels⟩ := P.positive_levels hx hn hzero
  let r : ℚ := (x (P.classOf a))⁻¹
  have hr : r ≠ 0 := inv_ne_zero (ne_of_gt ha)
  let y : C → ℚ := r • x
  have hy : y ∈ P.heightSpace := P.heightSpace.smul_mem r hx
  have hyn : ∀ i, 0 ≤ y i := by
    intro i
    exact mul_nonneg (inv_nonneg.mpr ha.le) (hn i)
  have hya : y (P.classOf a) = 1 := by
    simp [y, r, ne_of_gt ha]
  refine ⟨r, hr, hy, P.monotone_of_nonnegative hy hyn, ?_, ?_⟩
  · intro i
    rcases hlevels i with h | h | h
    · exact Or.inl (by simp [y, h])
    · exact Or.inr (Or.inl (by simpa [y, h] using hya))
    · right
      right
      change r * x i = 2
      rw [h]
      dsimp [r]
      field_simp
  · intro i hi
    obtain ⟨c, rfl⟩ := P.surjective i
    apply P.upper_level_mem_sameClassDifference hy hyn a c
    · rw [hya]
      norm_num
    · simpa only [hya, mul_one] using hi

/-- The full assertion of Lemma 7.3 about an arbitrary nonzero vector of (9).
The rescaling is nonzero, the zero set is an actual subgroup of `G`, and the
upper-level condition uses exactly the same-class difference set from the paper. -/
theorem normalized_height {x : C → ℚ} (hx : x ∈ P.heightSpace) (hzero : x ≠ 0) :
    ∃ r : ℚ, r ≠ 0 ∧
      let y := r • x
      y ∈ P.heightSpace ∧ Monotone y ∧
      (∀ i, y i = 0 ∨ y i = 1 ∨ y i = 2) ∧
      (∃ Z : AddSubgroup G, ∀ a, a ∈ Z ↔ x (P.classOf a) = 0) ∧
      (∀ i, y i = 2 → P.sameClassDifference i) := by
  obtain ⟨ε, hε, hεn⟩ : ∃ ε : ℚ, ε ≠ 0 ∧ ∀ i, 0 ≤ (ε • x) i := by
    rcases P.one_sign hx with hp | hn
    · exact ⟨1, one_ne_zero, by simpa using hp⟩
    · refine ⟨-1, neg_ne_zero.mpr one_ne_zero, ?_⟩
      intro i
      simpa using neg_nonneg.mpr (hn i)
  have hεx : ε • x ≠ 0 := smul_ne_zero hε hzero
  have hεmem : ε • x ∈ P.heightSpace := P.heightSpace.smul_mem ε hx
  obtain ⟨r, hr, hy, hmono, hvalues, hR⟩ :=
    P.normalized_nonnegative_height hεmem hεn hεx
  refine ⟨r * ε, mul_ne_zero hr hε, ?_⟩
  simp only [mul_smul]
  refine ⟨hy, hmono, hvalues, ?_, hR⟩
  have hyn : ∀ i, 0 ≤ (r • ε • x) i := by
    intro i
    rcases hvalues i with h | h | h <;> rw [h] <;> norm_num
  refine ⟨P.zeroSubgroup _ hy hyn, ?_⟩
  intro a
  change r * (ε * x (P.classOf a)) = 0 ↔ x (P.classOf a) = 0
  simp [hr, hε]

end Sunlet.OrbitHeight.InverseStablePartition
