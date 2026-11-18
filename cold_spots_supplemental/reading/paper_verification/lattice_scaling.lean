module

public import PaperVerification.LatticeTranslations

@[expose] public section
/-! # Similarities of actual Gaussian lattice sums and depth

These lemmas work with arbitrary nonempty subsets of Euclidean coordinate space.
They justify the normalization changes without modifying the Gaussian parameter
or the geometric meaning silently.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

def scaleVec (c : ℝ) (x : Fin n → ℝ) : Fin n → ℝ := fun i => c * x i

def scaledSet (c : ℝ) (L : Set (Fin n → ℝ)) : Set (Fin n → ℝ) := scaleVec c '' L

theorem scaleVec_inv (c : ℝ) (hc : c ≠ 0) (x : Fin n → ℝ) :
    scaleVec c (scaleVec c⁻¹ x) = x := by
  funext i
  simp [scaleVec, hc, mul_assoc]

theorem scaleVec_injective (c : ℝ) (hc : c ≠ 0) : Function.Injective (@scaleVec n c) := by
  intro x y h
  funext i
  exact mul_left_cancel₀ hc (congrFun h i)

theorem sqDist_scaleVec (c : ℝ) (x y : Fin n → ℝ) :
    sqDist (scaleVec c x) (scaleVec c y) = c ^ 2 * sqDist x y := by
  simp only [sqDist, scaleVec, ← mul_sub, mul_pow, Finset.mul_sum]

def scaledSetEquiv (c : ℝ) (hc : c ≠ 0) (L : Set (Fin n → ℝ)) : L ≃ scaledSet c L :=
  Equiv.ofBijective (fun z => ⟨scaleVec c z.val, z.val, z.property, rfl⟩)
    ⟨fun x y h => Subtype.ext (scaleVec_injective c hc (congrArg Subtype.val h)), by
      rintro ⟨z, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩⟩

theorem setGaussian_scaled (c : ℝ) (hc : c ≠ 0) (L : Set (Fin n → ℝ))
    (α : ℝ) (x : Fin n → ℝ) :
    setGaussian (scaledSet c L) α (scaleVec c x) = setGaussian L (α * c ^ 2) x := by
  calc
    _ = ∑' z : L, Real.exp (-α * sqDist (scaleVec c z.val) (scaleVec c x)) :=
      ((scaledSetEquiv c hc L).tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro z
      rw [sqDist_scaleVec]
      congr 1
      ring

theorem summable_scaled_iff (c : ℝ) (hc : c ≠ 0) (L : Set (Fin n → ℝ))
    (α : ℝ) (x : Fin n → ℝ) :
    Summable (fun z : scaledSet c L => Real.exp (-α * sqDist z.val (scaleVec c x))) ↔
      Summable (fun z : L => Real.exp (-(α * c ^ 2) * sqDist z.val x)) := by
  rw [← (scaledSetEquiv c hc L).summable_iff]
  have he : (fun z : L => Real.exp (-α * sqDist
      ((scaledSetEquiv c hc L) z).val (scaleVec c x))) =
      fun z : L => Real.exp (-(α * c ^ 2) * sqDist z.val x) := by
    funext z
    change Real.exp (-α * sqDist (scaleVec c z.val) (scaleVec c x)) = _
    rw [sqDist_scaleVec]
    congr 1
    ring
  dsimp only [Function.comp_def]
  rw [he]

theorem squaredDepth_scaled (c : ℝ) (hc : c ≠ 0) (L : Set (Fin n → ℝ))
    (hL : L.Nonempty) (x : Fin n → ℝ) :
    squaredDepth (scaledSet c L) (scaleVec c x) = c ^ 2 * squaredDepth L x := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  apply le_antisymm
  · have h : squaredDepth (scaledSet c L) (scaleVec c x) / c ^ 2 ≤ squaredDepth L x := by
      apply le_csInf (hL.image (fun z => sqDist x z))
      rintro r ⟨z, hz, rfl⟩
      apply (div_le_iff₀ hc2).mpr
      have hd := squaredDepth_le (scaleVec c x)
        (show scaleVec c z ∈ scaledSet c L from ⟨z, hz, rfl⟩)
      rw [sqDist_scaleVec] at hd
      simpa only [mul_comm] using hd
    have h' := (div_le_iff₀ hc2).mp h
    simpa only [mul_comm] using h'
  · apply le_csInf ((hL.image (scaleVec c)).image (fun z => sqDist (scaleVec c x) z))
    rintro r ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    change c ^ 2 * squaredDepth L x ≤ sqDist (scaleVec c x) (scaleVec c w)
    rw [sqDist_scaleVec]
    exact mul_le_mul_of_nonneg_left (squaredDepth_le x hw) hc2.le

theorem isColdSpot_scaled_iff (c : ℝ) (hc : c ≠ 0) (L : Set (Fin n → ℝ))
    (α : ℝ) (x : Fin n → ℝ) :
    IsColdSpot (scaledSet c L) α (scaleVec c x) ↔ IsColdSpot L (α * c ^ 2) x := by
  constructor
  · intro h y
    have hy := h (scaleVec c y)
    simpa only [setGaussian_scaled c hc] using hy
  · intro h y
    have hy := h (scaleVec c⁻¹ y)
    rw [← setGaussian_scaled c hc, ← setGaussian_scaled c hc, scaleVec_inv c hc y] at hy
    exact hy

theorem isDeepHole_scaled_iff (c : ℝ) (hc : c ≠ 0) (L : Set (Fin n → ℝ))
    (hL : L.Nonempty) (x : Fin n → ℝ) :
    IsDeepHole (scaledSet c L) (scaleVec c x) ↔ IsDeepHole L x := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  constructor
  · intro h y
    have hy := h (scaleVec c y)
    rw [squaredDepth_scaled c hc L hL, squaredDepth_scaled c hc L hL] at hy
    exact (mul_le_mul_iff_of_pos_left hc2).mp hy
  · intro h y
    have hy := mul_le_mul_of_nonneg_left (h (scaleVec c⁻¹ y)) hc2.le
    rw [← squaredDepth_scaled c hc L hL, ← squaredDepth_scaled c hc L hL,
      scaleVec_inv c hc y] at hy
    exact hy

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.setGaussian_scaled
#print axioms PaperVerification.ColdSpots.squaredDepth_scaled
