import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! UNCOMPILED auxiliary linear certificate. Actual row correspondence,
geometric wrappers, and all unbounded theorems still require Lean checking. -/

@[expose] public section

namespace GraphicalZonotopes.DiamondGenerated

set_option maxRecDepth 100000

def cliqueMasks : Fin 57 → ℕ :=
  ![3, 5, 6, 7, 9, 10, 11, 17, 18, 19, 24, 25, 26, 27, 33, 34, 35, 40, 41, 42, 43, 65, 66, 67, 68, 69, 70, 71, 129, 130, 131, 132, 133, 134, 135, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523]

def coefficients : Fin 57 → ℝ :=
  ![1, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, -1, 0, 0, 2, 0, 0, 2, -2, 0, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 1, 0, 1, 0, -1, 1, 1, -1, 1, 0, -1, 1, 1, -1, 0, 1]

theorem kernel_line (x : Fin 57 → ℝ)
    -- h0: tight row 33.
    (h0 : x 0 + x 3 + x 30 + x 34 = 0)
    -- h1: tight row 37.
    (h1 : x 0 + x 3 + x 9 + x 30 + x 34 = 0)
    -- h2: tight row 39.
    (h2 : x 0 + x 3 + x 6 + x 9 + x 13 + x 30 + x 34 = 0)
    -- h3: tight row 47.
    (h3 : x 0 + x 3 + x 6 + x 9 + x 13 + x 16 + x 20 + x 30 + x 34 = 0)
    -- h4: tight row 49.
    (h4 : x 0 + x 3 + x 23 + x 27 + x 30 + x 34 = 0)
    -- h5: tight row 70.
    (h5 : x 0 + x 6 + x 9 + x 13 + x 37 + x 45 = 0)
    -- h6: tight row 102.
    (h6 : x 0 + x 6 + x 9 + x 13 + x 30 + x 37 + x 45 = 0)
    -- h7: tight row 103.
    (h7 : x 0 + x 3 + x 6 + x 9 + x 13 + x 30 + x 34 + x 37 + x 41 + x 45 = 0)
    -- h8: tight row 128.
    (h8 : x 0 + x 48 = 0)
    -- h9: tight row 161.
    (h9 : x 0 + x 3 + x 30 + x 34 + x 48 + x 52 = 0)
    -- h10: tight row 192.
    (h10 : x 0 + x 37 + x 48 = 0)
    -- h11: tight row 198.
    (h11 : x 0 + x 6 + x 9 + x 13 + x 37 + x 45 + x 48 + x 56 = 0)
    -- h12: tight row 256.
    (h12 : x 1 = 0)
    -- h13: tight row 257.
    (h13 : x 1 + x 3 = 0)
    -- h14: tight row 259.
    (h14 : x 1 + x 3 + x 25 + x 27 = 0)
    -- h15: tight row 261.
    (h15 : x 1 + x 3 + x 32 + x 34 = 0)
    -- h16: tight row 264.
    (h16 : x 1 + x 39 = 0)
    -- h17: tight row 272.
    (h17 : x 1 + x 50 = 0)
    -- h18: tight row 295.
    (h18 : x 2 + x 3 + x 26 + x 27 + x 33 + x 34 = 0)
    -- h19: tight row 303.
    (h19 : x 2 + x 3 + x 26 + x 27 + x 33 + x 34 + x 40 + x 41 = 0)
    -- h20: tight row 311.
    (h20 : x 2 + x 3 + x 26 + x 27 + x 33 + x 34 + x 51 + x 52 = 0)
    -- h21: tight row 312.
    (h21 : x 2 + x 40 + x 51 = 0)
    -- h22: tight row 314.
    (h22 : x 2 + x 26 + x 40 + x 51 = 0)
    -- h23: tight row 316.
    (h23 : x 2 + x 33 + x 40 + x 51 = 0)
    -- h24: tight row 325.
    (h24 : x 4 + x 6 + x 18 + x 20 = 0)
    -- h25: tight row 327.
    (h25 : x 4 + x 6 + x 11 + x 13 + x 18 + x 20 = 0)
    -- h26: tight row 333.
    (h26 : x 4 + x 6 + x 18 + x 20 + x 43 + x 45 = 0)
    -- h27: tight row 336.
    (h27 : x 4 + x 54 = 0)
    -- h28: tight row 340.
    (h28 : x 4 + x 18 + x 54 = 0)
    -- h29: tight row 341.
    (h29 : x 4 + x 6 + x 18 + x 20 + x 54 + x 56 = 0)
    -- h30: tight row 352.
    (h30 : x 5 = 0)
    -- h31: tight row 360.
    (h31 : x 5 + x 44 = 0)
    -- h32: tight row 361.
    (h32 : x 5 + x 6 + x 44 + x 45 = 0)
    -- h33: tight row 363.
    (h33 : x 5 + x 6 + x 12 + x 13 + x 44 + x 45 = 0)
    -- h34: tight row 365.
    (h34 : x 5 + x 6 + x 19 + x 20 + x 44 + x 45 = 0)
    -- h35: tight row 368.
    (h35 : x 5 + x 55 = 0)
    -- h36: tight row 384.
    (h36 : x 7 = 0)
    -- h37: tight row 388.
    (h37 : x 8 = 0)
    -- h38: tight row 392.
    (h38 : x 14 = 0)
    -- h39: tight row 396.
    (h39 : x 15 = 0)
    -- h40: tight row 400.
    (h40 : x 21 = 0)
    -- h41: tight row 404.
    (h41 : x 22 = 0)
    -- h42: tight row 408.
    (h42 : x 28 = 0)
    -- h43: tight row 415.
    (h43 : x 29 + x 30 + x 33 + x 34 = 0)
    -- h44: tight row 416.
    (h44 : x 35 = 0)
    -- h45: tight row 426.
    (h45 : x 36 + x 40 = 0)
    -- h46: tight row 433.
    (h46 : x 46 + x 48 = 0)
    -- h47: tight row 441.
    (h47 : x 47 + x 48 = 0)
    -- h48: tight row 448.
    (h48 : x 10 = 0)
    -- h49: tight row 452.
    (h49 : x 17 = 0)
    -- h50: tight row 456.
    (h50 : x 24 = 0)
    -- h51: tight row 460.
    (h51 : x 31 = 0)
    -- h52: tight row 466.
    (h52 : x 38 + x 40 = 0)
    -- h53: tight row 468.
    (h53 : x 42 = 0)
    -- h54: tight row 474.
    (h54 : x 49 + x 51 = 0)
    -- h55: tight row 477.
    (h55 : x 53 + x 54 = 0)
    : ∀ i : Fin 57, x i = coefficients i * x 0 := by
  intro i
  fin_cases i
  · norm_num [coefficients]
  · norm_num [coefficients]
    linear_combination h12
  · norm_num [coefficients]
    linear_combination -2 * h0 - h5 + h7 - h8 + h9 + 2 * h18 - h19 - h20 + h21
  · norm_num [coefficients]
    linear_combination -h12 + h13
  · norm_num [coefficients]
    linear_combination -h5 - h8 + h11 + h24 + h27 - h29
  · norm_num [coefficients]
    linear_combination h30
  · norm_num [coefficients]
    linear_combination -h0 + h2 - h5 - h8 + h10 - h31 + h32
  · norm_num [coefficients]
    linear_combination h36
  · norm_num [coefficients]
    linear_combination h37
  · norm_num [coefficients]
    linear_combination -h0 + h1
  · norm_num [coefficients]
    linear_combination h48
  · norm_num [coefficients]
    linear_combination -h0 + h1 - h5 - h8 + h10 - h24 + h25 - h31 + h32
  · norm_num [coefficients]
    linear_combination -h0 + h1 - h5 - h8 + h10 - h31 + h33
  · norm_num [coefficients]
    linear_combination h0 - h1 + h5 + h8 - h10 + h31 - h32
  · norm_num [coefficients]
    linear_combination h38
  · norm_num [coefficients]
    linear_combination h39
  · norm_num [coefficients]
    linear_combination -h0 + h3 - 2 * h5 - 2 * h8 + h10 + h11 + h28 - h29 - h31 + h32
  · norm_num [coefficients]
    linear_combination h49
  · norm_num [coefficients]
    linear_combination -h27 + h28
  · norm_num [coefficients]
    linear_combination -h0 + h2 - 2 * h5 - 2 * h8 + h10 + h11 + h28 - h29 - h31 + h34
  · norm_num [coefficients]
    linear_combination h0 - h2 + 2 * h5 + 2 * h8 - h10 - h11 - h28 + h29 + h31 - h32
  · norm_num [coefficients]
    linear_combination h40
  · norm_num [coefficients]
    linear_combination h41
  · norm_num [coefficients]
    linear_combination -2 * h0 + h4 - h6 + h7 - h8 + h9 + h18 - h19 - h20 - h21 + h22 + h23
  · norm_num [coefficients]
    linear_combination h50
  · norm_num [coefficients]
    linear_combination -h0 - h6 + h7 - h8 + h9 - h13 + h14 + h18 - h19 - h20 - h21 + h22 + h23
  · norm_num [coefficients]
    linear_combination -h21 + h22
  · norm_num [coefficients]
    linear_combination h0 + h6 - h7 + h8 - h9 - h18 + h19 + h20 + h21 - h22 - h23
  · norm_num [coefficients]
    linear_combination h42
  · norm_num [coefficients]
    linear_combination -h0 - h12 + h13 + h21 - h23 + h43
  · norm_num [coefficients]
    linear_combination -h5 + h6
  · norm_num [coefficients]
    linear_combination h51
  · norm_num [coefficients]
    linear_combination -h0 - h5 + h6 - h12 + h15
  · norm_num [coefficients]
    linear_combination -h21 + h23
  · norm_num [coefficients]
    linear_combination h0 + h5 - h6 + h12 - h13
  · norm_num [coefficients]
    linear_combination h44
  · norm_num [coefficients]
    linear_combination -h0 - h5 + h7 + h18 - h19 + h45
  · norm_num [coefficients]
    linear_combination -h8 + h10
  · norm_num [coefficients]
    linear_combination -h0 - h5 + h7 + h18 - h19 + h52
  · norm_num [coefficients]
    linear_combination -h12 + h16
  · norm_num [coefficients]
    linear_combination h0 + h5 - h7 - h18 + h19
  · norm_num [coefficients]
    linear_combination -h0 - h5 + h7
  · norm_num [coefficients]
    linear_combination h53
  · norm_num [coefficients]
    linear_combination -h0 + h2 - h5 - h8 + h10 - h24 + h26
  · norm_num [coefficients]
    linear_combination -h30 + h31
  · norm_num [coefficients]
    linear_combination h0 - h2 + h5 + h8 - h10
  · norm_num [coefficients]
    linear_combination -h8 + h46
  · norm_num [coefficients]
    linear_combination -h8 + h47
  · norm_num [coefficients]
    linear_combination h8
  · norm_num [coefficients]
    linear_combination -h0 - h8 + h9 + h18 - h20 + h54
  · norm_num [coefficients]
    linear_combination -h12 + h17
  · norm_num [coefficients]
    linear_combination h0 + h8 - h9 - h18 + h20
  · norm_num [coefficients]
    linear_combination -h0 - h8 + h9
  · norm_num [coefficients]
    linear_combination -h5 - h8 + h11 + h24 - h29 + h55
  · norm_num [coefficients]
    linear_combination h5 + h8 - h11 - h24 + h29
  · norm_num [coefficients]
    linear_combination -h30 + h35
  · norm_num [coefficients]
    linear_combination -h5 - h8 + h11

#print axioms kernel_line

end GraphicalZonotopes.DiamondGenerated

