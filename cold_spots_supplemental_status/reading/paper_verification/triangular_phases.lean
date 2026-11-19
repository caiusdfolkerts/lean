module
public import PaperVerification.TriangularCubic
public import Mathlib.Algebra.Order.Floor.Ring
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

def TriPhase (z : TriPoint) : Prop :=
  ∃ r : ZMod 3, ∃ m : EisInt, z = eisEmbed m + (r.val : ℝ) • triC

theorem triPhase_iff_theta_integral (z : TriPoint) :
    TriPhase z ↔ triTheta z ∈ triIntegerLattice := by
  constructor
  · rintro ⟨r,m,rfl⟩
    refine ⟨eisTheta m + ((r.val : ℤ),(r.val : ℤ)), ?_⟩
    rw [map_add, triTheta_add, triTheta_embed, triTheta_smul, triTheta_c]
    congr 1
    ext <;> simp [eisEmbed]
  · rintro ⟨m,hm⟩
    let r : ZMod 3 := -eisResidue m
    let d : EisInt := ((r.val : ℤ),(r.val : ℤ))
    have hd : eisResidue d = 2*r := by simp [d,eisResidue,two_mul]
    have hz : eisResidue (m-d) = 0 := by
      rw [map_sub,hd]
      dsimp [r]
      have h3 : (3 : ZMod 3) = 0 := by decide
      linear_combination eisResidue m * h3
    refine ⟨r,eisThetaDiv (m-d) hz, ?_⟩
    apply triTheta_injective
    rw [← hm,triTheta_add,triTheta_embed,triTheta_smul,triTheta_c,eisTheta_div,map_sub]
    have he : (r.val : ℝ) • eisEmbed (1,1) = eisEmbed d := by ext <;> simp [d,eisEmbed]
    rw [he,sub_add_cancel]

theorem triPhase_iff_integer_multiple (z : TriPoint) :
    TriPhase z ↔ ∃ m : EisInt, ∃ k : ℤ, z = eisEmbed m + (k : ℝ) • triC := by
  constructor
  · rintro ⟨r,m,h⟩
    exact ⟨m,(r.val : ℤ),by simpa using h⟩
  · rintro ⟨m,k,rfl⟩
    rw [triPhase_iff_theta_integral]
    refine ⟨eisTheta m + (k,k), ?_⟩
    rw [map_add,triTheta_add,triTheta_embed,triTheta_smul,triTheta_c]
    congr 1
    ext <;> simp [eisEmbed]

theorem triangularProduct_periodic (α : ℝ) (z : TriPoint) (m : EisInt) :
    triangularProduct α (z + eisEmbed m) = triangularProduct α z := by
  unfold triangularProduct
  rw [show z + eisEmbed m + triC = (z+triC)+eisEmbed m by abel,
    show z + eisEmbed m - triC = (z-triC)+eisEmbed m by abel]
  simp only [triangularGaussian_periodic]

theorem triangularProduct_c_periodic (α : ℝ) (z : TriPoint) :
    triangularProduct α (z+triC) = triangularProduct α z := by
  unfold triangularProduct
  rw [show z+triC+triC = z+(2:ℝ)•triC by module,
    triangularGaussian_two_c,add_sub_cancel_right]
  ring

theorem triangularProduct_zero (α : ℝ) :
    triangularProduct α 0 = triangularGaussian α 0 * triangularGaussian α triC ^ 2 := by
  simp only [triangularProduct,zero_add,zero_sub,triangularGaussian_even]
  ring

theorem triangularProduct_phase (α : ℝ) {z : TriPoint} (hz : TriPhase z) :
    triangularProduct α z = triangularGaussian α 0 * triangularGaussian α triC ^ 2 := by
  obtain ⟨r,m,rfl⟩ := hz
  rw [add_comm,triangularProduct_periodic]
  rcases (show ∀ r : ZMod 3, r = 0 ∨ r = 1 ∨ r = 2 by decide) r with
    rfl | rfl | rfl
  · change triangularProduct α (((0 : ZMod 3).val : ℝ) • triC) = _
    rw [ZMod.val_zero]
    simpa only [Nat.cast_zero, zero_smul] using triangularProduct_zero α
  · change triangularProduct α (((1 : ZMod 3).val : ℝ) • triC) = _
    rw [zmodThree_val_one]
    have h := (triangularProduct_c_periodic α 0).trans (triangularProduct_zero α)
    simpa only [Nat.cast_one, one_smul, zero_add] using h
  · change triangularProduct α (((2 : ZMod 3).val : ℝ) • triC) = _
    rw [zmodThree_val_two]
    have h1 : triangularProduct α triC =
        triangularGaussian α 0 * triangularGaussian α triC ^ 2 := by
      simpa only [zero_add] using
        (triangularProduct_c_periodic α 0).trans (triangularProduct_zero α)
    have he : (2:ℝ)•triC = triC+triC := by module
    simpa only [Nat.cast_ofNat, he] using (triangularProduct_c_periodic α triC).trans h1

def triFraction (z : TriPoint) : TriPoint := (Int.fract z.1,Int.fract z.2)

def triFloor (z : TriPoint) : EisInt := (⌊z.1⌋,⌊z.2⌋)

theorem triFraction_add_floor (z : TriPoint) : triFraction z + eisEmbed (triFloor z) = z := by
  apply Prod.ext
  · change Int.fract z.1 + (⌊z.1⌋ : ℝ) = z.1
    exact Int.fract_add_floor z.1
  · change Int.fract z.2 + (⌊z.2⌋ : ℝ) = z.2
    exact Int.fract_add_floor z.2

theorem triFraction_mem (z : TriPoint) :
    triFraction z ∈ (Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1) :=
  ⟨⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩,
    ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩⟩

end PaperVerification.ColdSpots
