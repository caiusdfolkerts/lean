module
public import PaperVerification.LatticeGeometry
public import PaperVerification.DnGaussian
public import Mathlib.Algebra.Group.Subgroup.Basic
@[expose] public section
/-! # Actual translation symmetries and nearest points

The distance and Gaussian symmetries are proved for the underlying real point
sets.  The nearest-point result is an exact attainment theorem, obtained from
coordinate rounding and parity repair, rather than an assumed lattice compactness
principle.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

theorem intVec_add (z w : Fin n → ℤ) : intVec (z + w) = intVec z + intVec w := by
  funext i
  simp [intVec]

theorem dPlusSet_add (heven : Even n) {x y : Fin n → ℝ}
    (hx : x ∈ dPlusSet n) (hy : y ∈ dPlusSet n) : x + y ∈ dPlusSet n := by
  rcases hx with ⟨z, hz, rfl | rfl⟩ <;> rcases hy with ⟨w, hw, rfl | rfl⟩
  · refine ⟨z + w, ?_, Or.inl (intVec_add z w).symm⟩
    simpa only [Pi.add_apply, Finset.sum_add_distrib] using hz.add hw
  · refine ⟨z + w, ?_, Or.inr ?_⟩
    · simpa only [Pi.add_apply, Finset.sum_add_distrib] using hz.add hw
    · funext i
      simp [intVec] <;> ring
  · refine ⟨z + w, ?_, Or.inr ?_⟩
    · simpa only [Pi.add_apply, Finset.sum_add_distrib] using hz.add hw
    · funext i
      simp [intVec] <;> ring
  · refine ⟨fun i => z i + w i + 1, ?_, Or.inl ?_⟩
    · have hn : Even (n : ℤ) := (Int.even_coe_nat n).mpr heven
      simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one] using (hz.add hw).add hn
    · funext i
      simp only [Pi.add_apply, intVec, Int.cast_add, Int.cast_one]
      ring

theorem dPlusSet_neg (heven : Even n) {x : Fin n → ℝ} (hx : x ∈ dPlusSet n) :
    -x ∈ dPlusSet n := by
  rcases hx with ⟨z, hz, rfl | rfl⟩
  · refine ⟨-z, ?_, Or.inl ?_⟩
    · simpa only [Pi.neg_apply, Finset.sum_neg_distrib] using hz.neg
    · funext i
      simp [intVec]
  · refine ⟨fun i => -z i - 1, ?_, Or.inr ?_⟩
    · have hn : Even (n : ℤ) := (Int.even_coe_nat n).mpr heven
      simpa only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using hz.neg.sub hn
    · funext i
      simp only [Pi.neg_apply, Int.cast_sub, Int.cast_neg, Int.cast_one]
      ring

theorem dPlusSet_sub (heven : Even n) {x y : Fin n → ℝ}
    (hx : x ∈ dPlusSet n) (hy : y ∈ dPlusSet n) : x - y ∈ dPlusSet n := by
  simpa only [sub_eq_add_neg] using dPlusSet_add heven hx (dPlusSet_neg heven hy)

def dPlusAddSubgroup (n : ℕ) (heven : Even n) : AddSubgroup (Fin n → ℝ) where
  carrier := dPlusSet n
  zero_mem' := zero_mem_dPlusSet n
  add_mem' := dPlusSet_add heven
  neg_mem' := dPlusSet_neg heven

theorem sqDist_add_add (x y g : Fin n → ℝ) : sqDist (x + g) (y + g) = sqDist x y := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

theorem sqDist_add_left (x y g : Fin n → ℝ) : sqDist (x + g) y = sqDist x (y - g) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem sqDist_sub_left (x y g : Fin n → ℝ) : sqDist (x - g) y = sqDist x (y + g) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem squaredDepth_add_of_subgroup (L : AddSubgroup (Fin n → ℝ))
    (x g : Fin n → ℝ) (hg : g ∈ L) : squaredDepth (L : Set _) (x + g) = squaredDepth (L : Set _) x := by
  unfold squaredDepth
  congr 1
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z - g, L.sub_mem hz hg, ?_⟩
    exact (sqDist_add_left x z g).symm
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z + g, L.add_mem hz hg, ?_⟩
    exact sqDist_add_add x z g

theorem setGaussian_add_of_subgroup (L : AddSubgroup (Fin n → ℝ))
    (α : ℝ) (x g : Fin n → ℝ) (hg : g ∈ L) :
    setGaussian (L : Set _) α (x + g) = setGaussian (L : Set _) α x := by
  let e : L ≃ L := Equiv.addRight ⟨g, hg⟩
  let f : L → ℝ := fun z => Real.exp (-α * sqDist z.val (x + g))
  calc
    _ = ∑' z : L, f (e z) := (e.tsum_eq f).symm
    _ = _ := by
      apply tsum_congr
      intro z
      change Real.exp (-α * sqDist (z.val + g) (x + g)) = Real.exp (-α * sqDist z.val x)
      rw [sqDist_add_add]

theorem exists_integerRepairCost_witness (x : Fin n → ℝ) (j : Fin n) :
    ∃ z ∈ dPlusSet n, sqDist x z ≤ integerRepairCost x (foldedRadius x j) := by
  by_cases he : Even (∑ i, roundedInt x i)
  · refine ⟨intVec (roundedInt x), ⟨roundedInt x, he, Or.inl rfl⟩, ?_⟩
    rw [sqDist_roundedInt]
    simp [integerRepairCost, he]
  · obtain ⟨z, hz, hdist⟩ := exists_even_integer_bound x j
    refine ⟨intVec z, ⟨z, hz, Or.inl rfl⟩, ?_⟩
    simpa [sqDist, intVec, integerRepairCost, integerBaseCost, he,
      sub_eq_add_neg, add_assoc] using hdist

theorem exists_halfRepairCost_witness (x : Fin n → ℝ) (j : Fin n) :
    ∃ z ∈ dPlusSet n, sqDist x z ≤ halfRepairCost x (foldedRadius x j) := by
  by_cases he : Even (∑ i, halfRoundedInt x i)
  · refine ⟨(fun i => (halfRoundedInt x i : ℝ) + 1 / 2),
      ⟨halfRoundedInt x, he, Or.inr rfl⟩, ?_⟩
    rw [sqDist_halfRoundedInt]
    simp [halfRepairCost, he]
  · obtain ⟨z, hz, hdist⟩ := exists_even_half_integer_bound x j
    refine ⟨(fun i => (z i : ℝ) + 1 / 2), ⟨z, hz, Or.inr rfl⟩, ?_⟩
    simpa [sqDist, halfRepairCost, halfBaseCost, he] using hdist

/-- The nearest E8 point exists for every real vector.  The general theorem
holds for every positive dimension in the coordinate realization D_n^+. -/
theorem exists_nearest_dPlus (hn : 0 < n) (x : Fin n → ℝ) :
    ∃ z ∈ dPlusSet n, sqDist x z = squaredDepth (dPlusSet n) x := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ (foldedRadius x) hne
  obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ (foldedRadius x) hne
  have heq := squaredDepth_dPlus_eq x lo hi (fun i => hlo i (Finset.mem_univ _))
    (fun i => hhi i (Finset.mem_univ _))
  rcases le_total (integerRepairCost x (foldedRadius x hi))
    (halfRepairCost x (foldedRadius x lo)) with h | h
  · rw [min_eq_left h] at heq
    obtain ⟨z, hz, hdist⟩ := exists_integerRepairCost_witness x hi
    exact ⟨z, hz, le_antisymm (hdist.trans_eq heq.symm) (squaredDepth_le x hz)⟩
  · rw [min_eq_right h] at heq
    obtain ⟨z, hz, hdist⟩ := exists_halfRepairCost_witness x lo
    exact ⟨z, hz, le_antisymm (hdist.trans_eq heq.symm) (squaredDepth_le x hz)⟩

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.exists_nearest_dPlus
#print axioms PaperVerification.ColdSpots.setGaussian_add_of_subgroup
