module

public import VolumePolynomials.AxisSimplexPolynomial
public import VolumePolynomials.BinarySequences
public import VolumePolynomials.BinaryPolynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Realization from ordered positive ratios

The volume identity retains the binomial normalization used in Appendix A.
Both realizing bodies are literal diagonal images of the coordinate simplex.
The diagonal factors may differ by coordinate; this form also supports the
degenerate limiting construction without fractional powers of its parameter.
-/

open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.BinarySimplex

open AxisSimplex SimplexCoordinates BinarySequences

def DecreasingRatios (d : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ i j : ℕ, i ≤ j → j < d → a (j + 1) / a j ≤ a (i + 1) / a i

def ratioAxes (d : ℕ) (a : ℕ → ℝ) (j : Fin d) : ℝ :=
  a (d - j.val) / a (d - j.val - 1)

theorem decreasingRatios_of_criterion {d : ℕ} {a : ℕ → ℝ}
    (ha : ∀ i ≤ d, 0 < a i) (hc : Criterion d a) : DecreasingRatios d a := by
  first
  | intro i j hij hjd
    exact ratios_antitone_on_interval (l := 0) (r := d)
      (fun k _ hkd => ha k hkd)
      (fun k hk hkd => by simpa only [pow_two] using hc.adjacent hk hkd)
      i j (Nat.zero_le _) hij hjd

theorem ratioAxes_pos {d : ℕ} {a : ℕ → ℝ} (ha : ∀ i ≤ d, 0 < a i) :
    ∀ j : Fin d, 0 < ratioAxes d a j := by
  first
  | intro j
    exact div_pos (ha _ (Nat.sub_le _ _)) (ha _ (by omega))

theorem ratioAxes_monotone {d : ℕ} {a : ℕ → ℝ} (hr : DecreasingRatios d a) :
    Monotone (ratioAxes d a) := by
  first
  | intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hval : i.val ≤ j.val := hij
    have h := hr (d - j.val - 1) (d - i.val - 1) (by omega) (by omega)
    have hei : d - i.val - 1 + 1 = d - i.val := by omega
    have hej : d - j.val - 1 + 1 = d - j.val := by omega
    simpa only [hei, hej, ratioAxes] using h

theorem upperProduct_succ {d i : ℕ} (lam : Fin d → ℝ) (hi : i < d) :
    upperProduct lam (i + 1) = lam ⟨d - i - 1, by omega⟩ * upperProduct lam i := by
  first
  | let j : Fin d := ⟨d - i - 1, by omega⟩
    have hset : Finset.univ.filter (fun k : Fin d => d - (i + 1) ≤ k.val) =
        insert j (Finset.univ.filter (fun k : Fin d => d - i ≤ k.val)) := by
      first
      | ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        have heq : k = j ↔ k.val = d - i - 1 := Fin.ext_iff
        rw [heq]
        omega
    have hj : j ∉ Finset.univ.filter (fun k : Fin d => d - i ≤ k.val) := by
      first
      | simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp [j]
        omega
    simp only [upperProduct, hset, Finset.prod_insert hj, j]

theorem upperProduct_ratioAxes {d : ℕ} {a : ℕ → ℝ}
    (ha : ∀ i ≤ d, 0 < a i) :
    ∀ i : ℕ, i ≤ d → upperProduct (ratioAxes d a) i = a i / a 0 := by
  first
  | intro i
    induction i with
    | zero =>
        intro _
        rw [upperProduct_zero, div_self (ha 0 (Nat.zero_le _)).ne']
    | succ i ih =>
        intro hid
        rw [upperProduct_succ _ (by omega), ih (by omega)]
        have hnum : d - (d - i - 1) = i + 1 := by omega
        have hden : d - (d - i - 1) - 1 = i := by omega
        simp only [ratioAxes, hnum, hden, Nat.add_sub_cancel]
        field_simp [(ha i (by omega)).ne', (ha 0 (Nat.zero_le _)).ne']

theorem map_axisBody {d : ℕ} (k lam : Fin d → ℝ) :
    mapBody (diagonalMap k) (axisBody lam) = axisBody (fun i => k i * lam i) := by
  first
  | apply ConvexBody.ext
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      ext i
      simp only [diagonalMap_apply]
      ring
    · rintro ⟨y, hy, rfl⟩
      refine ⟨diagonalMap lam y, ⟨y, hy, rfl⟩, ?_⟩
      ext i
      simp only [diagonalMap_apply]
      ring

theorem volume_sum_diagonal {d : ℕ} (k lam : Fin d → ℝ) (t s : ℝ) :
    bodyVolume (t • axisBody k + s • axisBody (fun i => k i * lam i)) =
      |∏ i, k i| * bodyVolume (t • body d + s • axisBody lam) := by
  first
  | have hmap : t • axisBody k + s • axisBody (fun i => k i * lam i) =
        mapBody (diagonalMap k) (t • body d + s • axisBody lam) := by
      first
      | rw [mapBody_add, mapBody_smul, mapBody_smul, map_axisBody]
        rfl
    rw [hmap, bodyVolume_map, det_diagonalMap]

theorem realizes_ratio_axes {d : ℕ} {a : ℕ → ℝ}
    (ha : ∀ i ≤ d, 0 < a i) (hr : DecreasingRatios d a)
    (k : Fin d → ℝ) (hk : ∀ i, 0 < k i)
    (hprod : ∏ i, k i = (d.factorial : ℝ) * a 0) :
    Realizes d a (axisBody k) (axisBody (fun i => k i * ratioAxes d a i)) := by
  first
  | intro t s ht hs
    rw [volume_sum_diagonal, abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hk i).le)),
      hprod, volume_sum_choose (fun i => (ratioAxes_pos ha i).le) (ratioAxes_monotone hr) ht hs]
    unfold value
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [upperProduct_ratioAxes ha i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
    field_simp [hfac, (ha 0 (Nat.zero_le _)).ne']

def commonScale (d : ℕ) (b : ℝ) : ℝ := ((d.factorial : ℝ) * b) ^ ((d : ℝ)⁻¹)

theorem commonScale_pos {d : ℕ} {b : ℝ} (hb : 0 < b) : 0 < commonScale d b := by
  first
  | apply Real.rpow_pos_of_pos
    exact mul_pos (by exact_mod_cast Nat.factorial_pos d) hb

theorem commonScale_pow {d : ℕ} (hd : 0 < d) {b : ℝ} (hb : 0 ≤ b) :
    commonScale d b ^ d = (d.factorial : ℝ) * b :=
  Real.rpow_inv_natCast_pow (mul_nonneg (Nat.cast_nonneg _) hb) hd.ne'

/-- The positive part of Appendix A, as an actual realization by two
coordinate simplices. -/
theorem exists_positive_axis_realization {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ}
    (ha : ∀ i ≤ d, 0 < a i) (hc : Criterion d a) :
    ∃ k lam : Fin d → ℝ, (∀ i, 0 < k i) ∧ (∀ i, 0 < lam i) ∧
      Realizes d a (axisBody k) (axisBody lam) := by
  first
  | let C := commonScale d (a 0)
    have hC : 0 < C := commonScale_pos (ha 0 (Nat.zero_le _))
    refine ⟨fun _ => C, fun i => C * ratioAxes d a i,
      fun _ => hC, fun i => mul_pos hC (ratioAxes_pos ha i), ?_⟩
    apply realizes_ratio_axes ha (decreasingRatios_of_criterion ha hc) _ (fun _ => hC)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      commonScale_pow hd (ha 0 (Nat.zero_le _)).le

theorem value_eq_zero {d : ℕ} {a : ℕ → ℝ} (ha : ∀ i ≤ d, a i = 0) (t s : ℝ) :
    value d a t s = 0 := by
  first
  | apply Finset.sum_eq_zero
    intro i hi
    rw [ha i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    ring

theorem zero_axis_realization {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ}
    (ha : ∀ i ≤ d, a i = 0) :
    Realizes d a (axisBody (fun _ => 0)) (axisBody (fun _ => 0)) := by
  first
  | have hz : axisBody (fun _ : Fin d => (0 : ℝ)) = (0 : Body d) := by
      first
      | have h := axisBody_scalar (fun _ : Fin d => (1 : ℝ)) 0
        simpa only [zero_mul, body_zero_smul] using h
    have hs0 (r : ℝ) : r • (0 : Body d) = 0 := by
      calc
        r • (0 : Body d) = (r * 0) • body d := by rw [← smul_smul, body_zero_smul]
        _ = 0 := by rw [mul_zero, body_zero_smul]
    intro t s ht hs
    simp only [hz, hs0, add_zero, value_eq_zero ha]
    have h := bodyVolume_smul (body d) (r := 0) le_rfl
    simpa only [body_zero_smul, zero_pow hd.ne', zero_mul] using h

end VolumePolynomials.BinarySimplex
