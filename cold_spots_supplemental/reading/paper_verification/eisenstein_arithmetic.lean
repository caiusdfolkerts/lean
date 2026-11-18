module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
@[expose] public section
/-!
# Exact Eisenstein coordinates

`(u,v)` denotes the physical complex number `u+v*ω`, with
`ω=(-1+i*sqrt(3))/2`. The quadratic form is proved to be its actual squared
Euclidean norm. Integral coordinates therefore describe the literal triangular
lattice, rather than an abstract theta function with assumed identities.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

abbrev EisInt := ℤ × ℤ
abbrev TriPoint := ℝ × ℝ

@[simp] theorem zmodThree_three_eq_zero : (3 : ZMod 3) = 0 := by decide

@[simp] theorem zmodThree_val_one : (1 : ZMod 3).val = 1 := by decide

@[simp] theorem zmodThree_val_two : (2 : ZMod 3).val = 2 := by decide

def eisEmbed : EisInt →+ TriPoint where
  toFun z := ((z.1 : ℝ), (z.2 : ℝ))
  map_zero' := by ext <;> simp
  map_add' := by intro z w; ext <;> simp

lemma eisEmbed_injective : Function.Injective eisEmbed := by
  intro z w h
  apply Prod.ext
  · exact Int.cast_injective (congrArg Prod.fst h)
  · exact Int.cast_injective (congrArg Prod.snd h)

def eisOmega : EisInt →+ EisInt where
  toFun z := (-z.2, z.1 - z.2)
  map_zero' := by ext <;> simp
  map_add' := by intro z w; ext <;> simp <;> ring

def eisTheta : EisInt →+ EisInt where
  toFun z := (z.1 - 2 * z.2, 2 * z.1 - z.2)
  map_zero' := by ext <;> simp
  map_add' := by intro z w; ext <;> simp <;> ring

def eisResidue : EisInt →+ ZMod 3 where
  toFun z := ((z.1 + z.2 : ℤ) : ZMod 3)
  map_zero' := by simp
  map_add' := by intro z w; simp; ring

lemma eisOmega_cube (z : EisInt) : eisOmega (eisOmega (eisOmega z)) = z := by
  ext <;> dsimp [eisOmega] <;> ring

lemma eisOmega_sum (z : EisInt) : z + eisOmega z + eisOmega (eisOmega z) = 0 := by
  ext <;> dsimp [eisOmega] <;> ring

lemma eisTheta_sq (z : EisInt) : eisTheta (eisTheta z) = (-3 : ℤ) • z := by
  ext <;> dsimp [eisTheta] <;> ring

lemma eisTheta_injective : Function.Injective eisTheta := by
  intro z w h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [eisTheta] at h₁ h₂
  apply Prod.ext <;> omega

@[simp] lemma eisResidue_omega (z : EisInt) : eisResidue (eisOmega z) = eisResidue z := by
  change ((-z.2 + (z.1 - z.2) : ℤ) : ZMod 3) = ((z.1 + z.2 : ℤ) : ZMod 3)
  push_cast
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination -((z.2 : ℤ) : ZMod 3) * h3

@[simp] lemma eisResidue_theta (z : EisInt) : eisResidue (eisTheta z) = 0 := by
  change ((z.1 - 2 * z.2 + (2 * z.1 - z.2) : ℤ) : ZMod 3) = 0
  rw [show z.1 - 2 * z.2 + (2 * z.1 - z.2) = 3 * (z.1 - z.2) by ring]
  simp

theorem eisTheta_range_iff (z : EisInt) : (∃ w, eisTheta w = z) ↔ eisResidue z = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    exact eisResidue_theta w
  · intro hz
    have hd : (3 : ℤ) ∣ z.1 + z.2 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (z.1 + z.2) 3).mp hz
    obtain ⟨k, hk⟩ := hd
    refine ⟨(z.2 - k, k - z.1), ?_⟩
    ext <;> dsimp [eisTheta] <;> omega

def eisThetaDiv (z : EisInt) (hz : eisResidue z = 0) : EisInt :=
  Classical.choose ((eisTheta_range_iff z).mpr hz)

lemma eisTheta_div (z : EisInt) (hz : eisResidue z = 0) :
    eisTheta (eisThetaDiv z hz) = z := Classical.choose_spec ((eisTheta_range_iff z).mpr hz)

def triOmega (z : TriPoint) : TriPoint := (-z.2, z.1 - z.2)

def triTheta (z : TriPoint) : TriPoint := (z.1 - 2 * z.2, 2 * z.1 - z.2)

def triThetaInv (z : TriPoint) : TriPoint := ((-z.1 + 2 * z.2) / 3, (-2 * z.1 + z.2) / 3)

def triC : TriPoint := (1 / 3, -(1 / 3))

def triQ (z : TriPoint) : ℝ := z.1 ^ 2 - z.1 * z.2 + z.2 ^ 2

def triComplex (z : TriPoint) : ℂ :=
  ((z.1 - z.2 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 * z.2 / 2 : ℝ) : ℂ) * Complex.I

def eisensteinOmega : ℂ := triComplex (0, 1)

theorem triComplex_coordinates (z : TriPoint) :
    triComplex z = (z.1 : ℂ) + (z.2 : ℂ) * eisensteinOmega := by
  apply Complex.ext <;> simp [triComplex, eisensteinOmega] <;> ring

theorem triQ_eq_norm_sq (z : TriPoint) : triQ z = ‖triComplex z‖ ^ 2 := by
  rw [Complex.sq_norm]
  simp only [triComplex, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
  have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold triQ
  nlinarith only [congrArg (fun r : ℝ ↦ r * z.2 ^ 2) h3]

theorem triQ_lower (z : TriPoint) : (z.1 ^ 2 + z.2 ^ 2) / 2 ≤ triQ z := by
  unfold triQ
  nlinarith [sq_nonneg (z.1 - z.2)]

theorem triQ_nonneg (z : TriPoint) : 0 ≤ triQ z :=
  (by positivity : (0 : ℝ) ≤ (z.1 ^ 2 + z.2 ^ 2) / 2).trans (triQ_lower z)

theorem triQ_omega (z : TriPoint) : triQ (triOmega z) = triQ z := by
  dsimp [triOmega, triQ]
  ring

theorem triQ_theta (z : TriPoint) : triQ (triTheta z) = 3 * triQ z := by
  dsimp [triTheta, triQ]
  ring

@[simp] theorem triTheta_inv (z : TriPoint) : triTheta (triThetaInv z) = z := by
  ext <;> dsimp [triTheta, triThetaInv] <;> ring

@[simp] theorem triThetaInv_theta (z : TriPoint) : triThetaInv (triTheta z) = z := by
  ext <;> dsimp [triTheta, triThetaInv] <;> ring

theorem triTheta_injective : Function.Injective triTheta :=
  Function.LeftInverse.injective triThetaInv_theta

@[simp] theorem triTheta_embed (z : EisInt) : triTheta (eisEmbed z) = eisEmbed (eisTheta z) := by
  ext <;> simp [triTheta, eisEmbed, eisTheta]

@[simp] theorem triOmega_embed (z : EisInt) : triOmega (eisEmbed z) = eisEmbed (eisOmega z) := by
  ext <;> simp [triOmega, eisEmbed, eisOmega]

@[simp] theorem triTheta_c : triTheta triC = eisEmbed (1, 1) := by
  ext <;> norm_num [triTheta, triC, eisEmbed]

theorem triC_three : (3 : ℝ) • triC = eisEmbed (1, -1) := by
  ext <;> norm_num [triC, eisEmbed]

theorem triQ_c : triQ triC = 1 / 3 := by norm_num [triQ, triC]

theorem triThetaInv_embed_integral (z : EisInt) (hz : eisResidue z = 0) :
    triThetaInv (eisEmbed z) = eisEmbed (eisThetaDiv z hz) := by
  apply triTheta_injective
  rw [triTheta_inv, triTheta_embed, eisTheta_div]

def triIntegerLattice : Set TriPoint := Set.range eisEmbed

theorem triIntegerLattice_complex (z : TriPoint) : z ∈ triIntegerLattice ↔
    ∃ a b : ℤ, z = ((a : ℝ), (b : ℝ)) := by
  constructor
  · rintro ⟨⟨a,b⟩, rfl⟩
    exact ⟨a,b,rfl⟩
  · rintro ⟨a,b,rfl⟩
    exact ⟨(a,b),rfl⟩

def triDFT (v : Fin 3 → TriPoint) : Fin 3 → TriPoint :=
  ![triThetaInv (v 0 + v 1 + v 2),
    triThetaInv (v 0 + triOmega (v 1) + triOmega (triOmega (v 2))),
    triThetaInv (v 0 + triOmega (triOmega (v 1)) + triOmega (v 2))]

def triDFTInv (v : Fin 3 → TriPoint) : Fin 3 → TriPoint :=
  ![-triThetaInv (v 0 + v 1 + v 2),
    -triThetaInv (v 0 + triOmega (triOmega (v 1)) + triOmega (v 2)),
    -triThetaInv (v 0 + triOmega (v 1) + triOmega (triOmega (v 2)))]

theorem triDFT_left_inv (v : Fin 3 → TriPoint) : triDFTInv (triDFT v) = v := by
  ext i <;> fin_cases i <;> simp [triDFT, triDFTInv, triThetaInv, triOmega] <;> ring

theorem triDFT_right_inv (v : Fin 3 → TriPoint) : triDFT (triDFTInv v) = v := by
  ext i <;> fin_cases i <;> simp [triDFT, triDFTInv, triThetaInv, triOmega] <;> ring

theorem triDFT_injective : Function.Injective triDFT :=
  Function.LeftInverse.injective triDFT_left_inv

/-- The true Euclidean isometry of the three-point Eisenstein transform. -/
theorem triDFT_preserves_norm (v : Fin 3 → TriPoint) :
    (∑ i, triQ (triDFT v i)) = ∑ i, triQ (v i) := by
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Finset.univ_unique,
    Finset.sum_singleton, Fin.succ_zero_eq_one]
  norm_num [triDFT, triQ, triThetaInv, triOmega]
  ring

theorem triDFT_sub (v w : Fin 3 → TriPoint) : triDFT (v - w) = triDFT v - triDFT w := by
  ext i <;> fin_cases i <;> simp [triDFT, triThetaInv, triOmega] <;> ring

theorem triDFT_centers (z : TriPoint) :
    triDFT ![z, z + triC, z - triC] = ![-triTheta z, triC, -triC] := by
  ext i <;> fin_cases i <;> simp [triDFT, triThetaInv, triTheta, triOmega, triC] <;> ring

end PaperVerification.ColdSpots
