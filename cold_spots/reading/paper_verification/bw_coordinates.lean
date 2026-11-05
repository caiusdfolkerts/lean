module
public import PaperVerification.BWCode
public import PaperVerification.LatticeTranslations
public import Mathlib.Tactic.LinearCombination
@[expose] public section
/-! # The exact E8 similarity behind the Barnes–Wall glue

The lattice M is defined by doubled integer coordinates whose residues belong to
RM(1,3).  The half-Hadamard map is proved to carry the actual E8 point set onto M;
its squared scale is one half.  No classification or covering result for M is
assumed in this identification.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

set_option maxRecDepth 65536

/-- The unnormalized pairwise Hadamard transformation. -/
def pairButterfly {R : Type*} [AddGroup R] (x : Fin 8 → R) : Fin 8 → R :=
  ![x 0 + x 1, x 0 - x 1, x 2 + x 3, x 2 - x 3,
    x 4 + x 5, x 4 - x 5, x 6 + x 7, x 6 - x 7]

/-- The similarity with squared norm factor one half. -/
def halfHadamard (x : Fin 8 → ℝ) : Fin 8 → ℝ := fun i => pairButterfly x i / 2

def evenPositionWord : Fin 8 → ℤ := ![1, 0, 1, 0, 1, 0, 1, 0]

def bwMSet : Set (Fin 8 → ℝ) :=
  {x | ∃ z : Fin 8 → ℤ, InRM3 (fun i => (z i : Binary)) ∧
    x = fun i => (z i : ℝ) / 2}

theorem pairButterfly_intCast (z : Fin 8 → ℤ) (i : Fin 8) :
    ((pairButterfly z i : ℤ) : ℝ) = pairButterfly (intVec z) i := by
  fin_cases i <;> simp [pairButterfly, intVec]

theorem pairButterfly_binaryCast (z : Fin 8 → ℤ) (i : Fin 8) :
    ((pairButterfly z i : ℤ) : Binary) = pairButterfly (fun i => (z i : Binary)) i := by
  fin_cases i <;> simp [pairButterfly]

theorem pairButterfly_sum (z : Fin 8 → ℤ) :
    (∑ i, pairButterfly z i) = 2 * (z 0 + z 2 + z 4 + z 6) := by
  simp [pairButterfly, Fin.sum_univ_succ]
  ring

theorem halfHadamard_add (x y : Fin 8 → ℝ) :
    halfHadamard (x + y) = halfHadamard x + halfHadamard y := by
  funext i
  fin_cases i <;> simp [halfHadamard, pairButterfly] <;> ring

theorem halfHadamard_sub (x y : Fin 8 → ℝ) :
    halfHadamard (x - y) = halfHadamard x - halfHadamard y := by
  funext i
  fin_cases i <;> simp [halfHadamard, pairButterfly] <;> ring

theorem halfHadamard_double_inverse (x : Fin 8 → ℝ) :
    halfHadamard (fun i => 2 * halfHadamard x i) = x := by
  funext i
  fin_cases i <;> simp [halfHadamard, pairButterfly] <;> ring

theorem double_halfHadamard_inverse (x : Fin 8 → ℝ) :
    (fun i => 2 * halfHadamard (halfHadamard x) i) = x := by
  funext i
  fin_cases i <;> simp [halfHadamard, pairButterfly] <;> ring

theorem halfHadamard_injective : Function.Injective halfHadamard := by
  intro x y h
  calc
    x = (fun i => 2 * halfHadamard (halfHadamard x) i) := (double_halfHadamard_inverse x).symm
    _ = (fun i => 2 * halfHadamard (halfHadamard y) i) := by rw [h]
    _ = y := double_halfHadamard_inverse y

theorem sqDist_halfHadamard (x y : Fin 8 → ℝ) :
    sqDist (halfHadamard x) (halfHadamard y) = sqDist x y / 2 := by
  simp [sqDist, halfHadamard, pairButterfly, Fin.sum_univ_succ]
  ring

theorem bwMSet_zero : (0 : Fin 8 → ℝ) ∈ bwMSet := by
  refine ⟨0, ?_, ?_⟩
  · simpa only [Pi.zero_apply, Int.cast_zero] using inRM3_zero
  · funext i
    simp

theorem bwMSet_add {x y : Fin 8 → ℝ} (hx : x ∈ bwMSet) (hy : y ∈ bwMSet) :
    x + y ∈ bwMSet := by
  rcases hx with ⟨z, hz, rfl⟩
  rcases hy with ⟨w, hw, rfl⟩
  refine ⟨z + w, ?_, ?_⟩
  · simpa only [Pi.add_apply, Int.cast_add] using inRM3_add hz hw
  · funext i
    simp only [Pi.add_apply, Int.cast_add]
    ring

theorem bwMSet_neg {x : Fin 8 → ℝ} (hx : x ∈ bwMSet) : -x ∈ bwMSet := by
  rcases hx with ⟨z, hz, rfl⟩
  refine ⟨-z, ?_, ?_⟩
  · simpa only [Pi.neg_apply, Int.cast_neg] using inRM3_neg hz
  · funext i
    simp only [Pi.neg_apply, Int.cast_neg]
    ring

def bwMAddSubgroup : AddSubgroup (Fin 8 → ℝ) where
  carrier := bwMSet
  zero_mem' := bwMSet_zero
  add_mem' := bwMSet_add
  neg_mem' := bwMSet_neg

theorem intVec_mem_bwM (z : Fin 8 → ℤ) : intVec z ∈ bwMSet := by
  refine ⟨fun i => 2 * z i, ?_, ?_⟩
  · simpa using (inRM3_zero : InRM3 (fun _ : Fin 8 => (0 : Binary)))
  · funext i
    simp [intVec]

theorem dPlusSet_subset_bwM : dPlusSet 8 ⊆ bwMSet := by
  rintro x ⟨z, hz, rfl | rfl⟩
  · exact intVec_mem_bwM z
  · refine ⟨fun i => 2 * z i + 1, ?_, ?_⟩
    · simpa using (inRM3_one : InRM3 (fun _ : Fin 8 => (1 : Binary)))
    · funext i
      push_cast
      ring

/-- Pairwise parity conditions of a butterfly are constant in all eight slots. -/
theorem binary_pairButterfly_common : ∀ c : BinaryWord8, PairCodeCondition c →
    ∀ i, pairButterfly c i = c 0 + c 1 := by decide

set_option maxHeartbeats 0 in
theorem binary_pairButterfly_code : ∀ c : BinaryWord8, (∑ i, c i) = 0 →
    PairCodeCondition (pairButterfly c) := by decide

theorem evenPositionWord_inRM3 : InRM3 (fun i => (evenPositionWord i : Binary)) := by decide

theorem butterfly_inRM3_of_even_sum (z : Fin 8 → ℤ) (hz : Even (∑ i, z i)) :
    InRM3 (fun i => ((pairButterfly z i : ℤ) : Binary)) := by
  apply (inRM3_iff_pairCondition _).mpr
  have hsum : (∑ i, (z i : Binary)) = 0 := by
    rw [← Int.cast_sum]
    exact hz.intCast_zmod_two
  have hmap : (fun i => ((pairButterfly z i : ℤ) : Binary)) =
      pairButterfly (fun i => (z i : Binary)) := funext (pairButterfly_binaryCast z)
  rw [hmap]
  exact binary_pairButterfly_code _ hsum

theorem halfHadamard_mem_bwM {x : Fin 8 → ℝ} (hx : x ∈ dPlusSet 8) :
    halfHadamard x ∈ bwMSet := by
  rcases hx with ⟨z, hz, rfl | rfl⟩
  · refine ⟨pairButterfly z, butterfly_inRM3_of_even_sum z hz, ?_⟩
    funext i
    simp only [halfHadamard, pairButterfly_intCast]
  · refine ⟨fun i => pairButterfly z i + evenPositionWord i, ?_, ?_⟩
    · simpa only [Int.cast_add] using
        inRM3_add (butterfly_inRM3_of_even_sum z hz) evenPositionWord_inRM3
    · funext i
      fin_cases i <;> simp [halfHadamard, pairButterfly, evenPositionWord] <;> push_cast <;> ring

/-- Inverse inclusion, proved by reconstructing actual even-sum integer coordinates. -/
theorem double_halfHadamard_mem_e8 {x : Fin 8 → ℝ} (hx : x ∈ bwMSet) :
    (fun i => 2 * halfHadamard x i) ∈ dPlusSet 8 := by
  rcases hx with ⟨w, hw, rfl⟩
  let τ : ℤ := ((w 0 : Binary) + (w 1 : Binary)).val
  have hτ : τ = 0 ∨ τ = 1 := by
    have h := binary_val_zero_or_one ((w 0 : Binary) + (w 1 : Binary))
    rcases h with h | h
    · left
      change (((w 0 : Binary) + (w 1 : Binary)).val : ℤ) = 0
      rw [h]
      rfl
    · right
      change (((w 0 : Binary) + (w 1 : Binary)).val : ℤ) = 1
      rw [h]
      rfl
  have hτcast : (τ : Binary) = (w 0 : Binary) + (w 1 : Binary) := binary_val_cast _
  have hcommon (i : Fin 8) : Even (pairButterfly w i - τ) := by
    apply ZMod.intCast_eq_zero_iff_even.mp
    rw [Int.cast_sub, pairButterfly_binaryCast, hτcast,
      binary_pairButterfly_common _ ((inRM3_iff_pairCondition _).mp hw) i, sub_self]
  let z : Fin 8 → ℤ := fun i => (pairButterfly w i - τ) / 2
  have hzcoord (i : Fin 8) : 2 * z i = pairButterfly w i - τ := by
    exact Int.mul_ediv_cancel' (even_iff_two_dvd.mp (hcommon i))
  have hsum : (∑ i, z i) = w 0 + w 2 + w 4 + w 6 - 4 * τ := by
    have h := congrArg (fun f : Fin 8 → ℤ => ∑ i, f i) (funext hzcoord)
    change (∑ i, 2 * z i) = ∑ i, (pairButterfly w i - τ) at h
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, pairButterfly_sum] at h
    simp only [
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    omega
  have he : Even (w 0 + w 2 + w 4 + w 6) := by
    apply ZMod.intCast_eq_zero_iff_even.mp
    simpa only [Int.cast_add] using ((inRM3_iff_pairCondition _).mp hw).2.2.2
  have hz : Even (∑ i, z i) := by
    rw [hsum]
    exact he.sub (show Even (4 * τ) from ⟨2 * τ, by ring⟩)
  have hreal (i : Fin 8) : 2 * halfHadamard (fun i => (w i : ℝ) / 2) i =
      (z i : ℝ) + (τ : ℝ) / 2 := by
    have hi : 2 * (z i : ℝ) = ((pairButterfly w i : ℤ) : ℝ) - (τ : ℝ) := by exact_mod_cast hzcoord i
    have hb : 2 * halfHadamard (fun i => (w i : ℝ) / 2) i = ((pairButterfly w i : ℤ) : ℝ) / 2 := by
      fin_cases i <;> simp [halfHadamard, pairButterfly] <;> push_cast <;> ring
    rw [hb]
    linarith
  refine ⟨z, hz, ?_⟩
  rcases hτ with h | h
  · left
    funext i
    simpa only [h, Int.cast_zero, zero_div, add_zero, intVec] using hreal i
  · right
    funext i
    simpa only [h, Int.cast_one] using hreal i

/-- Exact similarity, as equality of subsets of ordinary R⁸. -/
theorem bwMSet_eq_halfHadamard_image : bwMSet = halfHadamard '' dPlusSet 8 := by
  ext x
  constructor
  · intro hx
    exact ⟨(fun i => 2 * halfHadamard x i), double_halfHadamard_mem_e8 hx,
      halfHadamard_double_inverse x⟩
  · rintro ⟨y, hy, rfl⟩
    exact halfHadamard_mem_bwM hy

def e8ToMEquiv : dPlusSet 8 ≃ bwMSet :=
  Equiv.ofBijective (fun x => ⟨halfHadamard x.val, halfHadamard_mem_bwM x.property⟩)
    ⟨fun x y h => Subtype.ext (halfHadamard_injective (congrArg Subtype.val h)), by
      intro x
      refine ⟨⟨(fun i => 2 * halfHadamard x.val i), double_halfHadamard_mem_e8 x.property⟩, ?_⟩
      exact Subtype.ext (halfHadamard_double_inverse x.val)⟩

theorem sqDist_bwM_correspondence (x y : Fin 8 → ℝ) :
    sqDist x (halfHadamard y) = sqDist (fun i => 2 * halfHadamard x i) y / 2 := by
  simpa only [halfHadamard_double_inverse] using
    sqDist_halfHadamard (fun i => 2 * halfHadamard x i) y

/-- Exact nearest-point distance under the similarity. -/
theorem squaredDepth_bwM (x : Fin 8 → ℝ) :
    squaredDepth bwMSet x = squaredDepth (dPlusSet 8) (fun i => 2 * halfHadamard x i) / 2 := by
  obtain ⟨z, hz, hdist⟩ := exists_nearest_dPlus (by decide : 0 < 8)
    (fun i => 2 * halfHadamard x i)
  apply le_antisymm
  · calc
      _ ≤ sqDist x (halfHadamard z) := squaredDepth_le x (halfHadamard_mem_bwM hz)
      _ = _ := by rw [sqDist_bwM_correspondence, hdist]
  · apply le_csInf ((show bwMSet.Nonempty from ⟨0, bwMSet_zero⟩).image (fun z => sqDist x z))
    rintro r ⟨v, hv, rfl⟩
    rw [bwMSet_eq_halfHadamard_image] at hv
    rcases hv with ⟨y, hy, rfl⟩
    change squaredDepth (dPlusSet 8) (fun i => 2 * halfHadamard x i) / 2 ≤
      sqDist x (halfHadamard y)
    rw [sqDist_bwM_correspondence]
    exact div_le_div_of_nonneg_right (squaredDepth_le _ hy) (by norm_num)

theorem squaredDepth_bwM_le (x : Fin 8 → ℝ) : squaredDepth bwMSet x ≤ 1 / 2 := by
  rw [squaredDepth_bwM]
  have h := squaredDepth_dPlus_le (by decide : 8 ≤ 8) (fun i => 2 * halfHadamard x i)
  norm_num at h
  linarith

/-- The Gaussian of the actual point set transforms with parameter α/2. -/
theorem setGaussian_bwM (α : ℝ) (x : Fin 8 → ℝ) :
    setGaussian bwMSet α x = setGaussian (dPlusSet 8) (α / 2)
      (fun i => 2 * halfHadamard x i) := by
  rw [setGaussian, ← e8ToMEquiv.tsum_eq]
  apply tsum_congr
  intro z
  change Real.exp (-α * sqDist (halfHadamard z.val) x) = _
  rw [sqDist_comm, sqDist_bwM_correspondence, sqDist_comm]
  congr 1
  ring

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.bwMSet_eq_halfHadamard_image
#print axioms PaperVerification.ColdSpots.squaredDepth_bwM
#print axioms PaperVerification.ColdSpots.setGaussian_bwM
