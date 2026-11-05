import CommAlg.Polymatroid.FiniteMinimum
import Mathlib.Algebra.Order.Floor.Div

/-! # Exact stabilization of capped minima of integer affine functions -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def cappedAffineMinimum (κ : ℕ) (δ b : ι → ℕ) (s : ℕ) : ℕ :=
  min κ (finiteMinimum (fun j => s * δ j + b j))

/-- Every positive integer slope has passed the cap once `s ≥ κ`. -/
theorem cappedAffineMinimum_stable (κ : ℕ) (δ b : ι → ℕ) {s : ℕ} (hs : κ ≤ s) :
    cappedAffineMinimum κ δ b (s + 1) = cappedAffineMinimum κ δ b s := by
  unfold cappedAffineMinimum
  rw [← finiteMinimum_min_left, ← finiteMinimum_min_left]
  congr 1
  funext j
  by_cases hd : δ j = 0
  · simp [hd]
  · have hp : 1 ≤ δ j := by omega
    have h0 : κ ≤ s * δ j + b j := by nlinarith
    have h1 : κ ≤ (s + 1) * δ j + b j := by nlinarith
    simp [min_eq_left h0, min_eq_left h1]

/-- The maximum of the clamped ceiling thresholds, with a zero entry for
each zero slope. `⌈/⌉` is Mathlib's exact natural ceiling division. -/
def affineThreshold (κ : ℕ) (δ b : ι → ℕ) : ℕ :=
  univ.sup (fun j => if δ j = 0 then 0 else (κ - b j) ⌈/⌉ δ j)

theorem affineThreshold_le_iff (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) (s : ℕ) :
    affineThreshold κ δ b ≤ s ↔ ∀ j, κ ≤ s * δ j + b j := by
  simp only [affineThreshold, Finset.sup_le_iff, Finset.mem_univ, forall_true_left]
  apply forall_congr'
  intro j
  by_cases hd : δ j = 0
  · simp [hd, hz j hd]
  · rw [if_neg hd, ceilDiv_le_iff_le_mul (by omega : 0 < δ j)]
    rw [Nat.mul_comm (δ j) s]
    omega

theorem affineThreshold_le_cap (κ : ℕ) (δ b : ι → ℕ) :
    affineThreshold κ δ b ≤ κ := by
  apply Finset.sup_le
  intro j hj
  by_cases hd : δ j = 0
  · simp [hd]
  · rw [if_neg hd, ceilDiv_le_iff_le_mul (by omega : 0 < δ j)]
    have hp : 1 ≤ δ j := by omega
    nlinarith [Nat.sub_le κ (b j)]

theorem cappedAffineMinimum_le_cap (κ : ℕ) (δ b : ι → ℕ) (s : ℕ) :
    cappedAffineMinimum κ δ b s ≤ κ := min_le_left _ _

theorem cappedAffineMinimum_eq_cap_iff (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) (s : ℕ) :
    cappedAffineMinimum κ δ b s = κ ↔ affineThreshold κ δ b ≤ s := by
  rw [cappedAffineMinimum, min_eq_left_iff, le_finiteMinimum_iff,
    affineThreshold_le_iff κ δ b hz s]

theorem cappedAffineMinimum_lt_cap_iff (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) (s : ℕ) :
    cappedAffineMinimum κ δ b s < κ ↔ s < affineThreshold κ δ b := by
  have he := cappedAffineMinimum_eq_cap_iff κ δ b hz s
  have hl := cappedAffineMinimum_le_cap κ δ b s
  omega

theorem cappedAffineMinimum_mono (κ : ℕ) (δ b : ι → ℕ) :
    Monotone (cappedAffineMinimum κ δ b) := by
  intro s t hst
  exact min_le_min_left κ (finiteMinimum_mono (fun j => by
    exact Nat.add_le_add_right (Nat.mul_le_mul_right (δ j) hst) (b j)))

/-- There are no gaps before stabilization: the value strictly increases
at every integer step below the exact ceiling threshold. -/
theorem cappedAffineMinimum_strict_step (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) {s : ℕ} (hs : s < affineThreshold κ δ b) :
    cappedAffineMinimum κ δ b s < cappedAffineMinimum κ δ b (s + 1) := by
  have hlt := (cappedAffineMinimum_lt_cap_iff κ δ b hz s).mpr hs
  by_cases hn : κ ≤ finiteMinimum (fun j => (s + 1) * δ j + b j)
  · simpa only [cappedAffineMinimum, min_eq_left hn] using hlt
  · obtain ⟨j, hj⟩ := finiteMinimum_attained (fun j => (s + 1) * δ j + b j)
    have hsmall : (s + 1) * δ j + b j < κ := by omega
    have hd : δ j ≠ 0 := by
      intro heq
      have hzj := hz j heq
      simp only [heq, Nat.mul_zero, Nat.zero_add] at hsmall
      omega
    have hprev : cappedAffineMinimum κ δ b s ≤ s * δ j + b j :=
      (min_le_right _ _).trans (finiteMinimum_le _ j)
    have hnext : cappedAffineMinimum κ δ b (s + 1) =
        finiteMinimum (fun j => (s + 1) * δ j + b j) := min_eq_right (by omega)
    rw [hnext, ← hj]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem cappedAffineMinimum_step_eq_iff (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) (s : ℕ) :
    cappedAffineMinimum κ δ b (s + 1) = cappedAffineMinimum κ δ b s ↔
      affineThreshold κ δ b ≤ s := by
  constructor
  · intro heq
    by_contra hn
    have hlt := cappedAffineMinimum_strict_step κ δ b hz (by omega : s < affineThreshold κ δ b)
    omega
  · intro hs
    rw [(cappedAffineMinimum_eq_cap_iff κ δ b hz s).mpr hs,
      (cappedAffineMinimum_eq_cap_iff κ δ b hz (s + 1)).mpr (by omega)]

end CommAlg.Polymatroid
