module
public import verification_bundle.PalomarPart019
import all verification_bundle.PalomarPart019
public import foundation_bundle
public import incidence_bundle
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
@[expose] public section

noncomputable section

/-!
# Consolidated verification sources

Generated only to avoid repeatedly loading the same pinned Mathlib files.
Public theorem statements and proofs preserve their original content.
See VerificationBundle.sources.json for exact source ranges, hashes, and private
helper alpha-renamings, topological source order, and scope adjustments.
-/

/- Original source: CubicalIndecomposability/FaceDataChecks/LowerFacets.lean -/
section VerificationSource015


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

/-! Each coordinate identity below is an exact linear consequence
of edge equations and identities in earlier modules. No rank result or
external solver is assumed. -/

/-- Coordinate 98.3, recovered from skew spokes on cycle 32. -/
theorem value_395 (h : Assignment) (H : Constraints h) :
    h 98 3 = ((95192236161132 : ℝ) / 2455684594895333) * (h 1 0) + ((588757460640426 : ℝ) / 2455684594895333) * (h 1 1) + ((-108824997255192 : ℝ) / 2455684594895333) * (h 1 2) + h 1 3 + ((-95192236161132 : ℝ) / 2455684594895333) * (h 3 0) + ((-588757460640426 : ℝ) / 2455684594895333) * (h 5 1) + ((108824997255192 : ℝ) / 2455684594895333) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 230 3
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 3 - h 77 3) - ((948365989152 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 260 3
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 3 - h 86 3) - ((-6606317480432832 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 270 3
  change ((1 : ℤ) : ℝ) * (h 98 3 - h 90 3) - ((0 : ℤ) : ℝ) * (h 98 0 - h 90 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-4407740686834813285207738 : ℝ) / 19216975503653625171936133390014635399525) * r0 + ((-1 : ℝ) / 20647248309825) * r1 + ((2203870343417406642603869 : ℝ) / 66932725679225576473853552597420975096545575) * r2 + ((1 : ℝ) / 143828731726240950) * r3 + ((29636437161 : ℝ) / 47467136345716841559563887967) * r4 + (1 : ℝ) * r5 + ((224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_309 h H) + ((2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_308 h H) + (1 : ℝ) * (value_311 h H) + ((-224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_353 h H) + ((-2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_352 h H)

/-- Coordinate 87.0, recovered from skew spokes on cycle 33. -/
theorem value_348 (h : Assignment) (H : Constraints h) :
    h 87 0 = ((26941969465273 : ℝ) / 13520913290240) * (h 1 0) + ((-1639676546271 : ℝ) / 1352091329024) * (h 1 2) + ((-13421056175033 : ℝ) / 13520913290240) * (h 3 0) + ((1639676546271 : ℝ) / 1352091329024) * (h 9 2) := by
  have r0 := H 28 2
  change ((425101326811 : ℤ) : ℝ) * (h 87 2 - h 5 2) - ((425101326811 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 262 2
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 2 - h 87 2) - ((17519635479827047 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 267 2
  change ((1 : ℤ) : ℝ) * (h 91 2 - h 89 2) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((-3483 : ℝ) / 19000263401109760) * r0 + ((1 : ℝ) / 19000263401109760) * r1 + ((2502805068546721 : ℝ) / 2714323343015680) * r2 + ((211518274468959 : ℝ) / 2714323343015680) * r3 + ((-211518274468959 : ℝ) / 2714323343015680) * (value_022 h H) + ((211518274468959 : ℝ) / 2714323343015680) * (value_020 h H) + ((2502805068546721 : ℝ) / 2714323343015680) * (value_356 h H) + ((211518274468959 : ℝ) / 2714323343015680) * (value_358 h H)

/-- Coordinate 87.1, recovered from skew spokes on cycle 33. -/
theorem value_349 (h : Assignment) (H : Constraints h) :
    h 87 1 = ((-104828961357081 : ℝ) / 47323196515840) * (h 1 0) + ((12807158174847 : ℝ) / 4732319651584) * (h 1 2) + ((104828961357081 : ℝ) / 47323196515840) * (h 3 0) + h 5 1 + ((-12807158174847 : ℝ) / 4732319651584) * (h 9 2) := by
  have r0 := H 28 1
  change ((425101326811 : ℤ) : ℝ) * (h 87 1 - h 5 1) - ((-948678383322 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 28 2
  change ((425101326811 : ℤ) : ℝ) * (h 87 2 - h 5 2) - ((425101326811 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 262 2
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 2 - h 87 2) - ((17519635479827047 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 267 2
  change ((1 : ℤ) : ℝ) * (h 91 2 - h 89 2) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((1 : ℝ) / 425101326811) * r0 + ((1652123404555263 : ℝ) / 4038518590785121232920887680) * r1 + ((-474339191661 : ℝ) / 4038518590785121232920887680) * r2 + ((-1187178533099505335152093581 : ℝ) / 576931227255017318988698240) * r3 + ((-1652123404555263 : ℝ) / 9500131700554880) * r4 + ((1187178533099505335152093581 : ℝ) / 576931227255017318988698240) * (value_020 h H) + ((1652123404555263 : ℝ) / 9500131700554880) * (value_022 h H) + ((-1187178533099505335152093581 : ℝ) / 576931227255017318988698240) * (value_356 h H) + ((-1652123404555263 : ℝ) / 9500131700554880) * (value_358 h H)

/-- Coordinate 87.2, recovered from skew spokes on cycle 33. -/
theorem value_350 (h : Assignment) (H : Constraints h) :
    h 87 2 = ((13421056175033 : ℝ) / 13520913290240) * (h 1 0) + ((-287585217247 : ℝ) / 1352091329024) * (h 1 2) + ((-13421056175033 : ℝ) / 13520913290240) * (h 3 0) + ((1639676546271 : ℝ) / 1352091329024) * (h 9 2) := by
  have r0 := H 28 2
  change ((425101326811 : ℤ) : ℝ) * (h 87 2 - h 5 2) - ((425101326811 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 262 2
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 2 - h 87 2) - ((17519635479827047 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 267 2
  change ((1 : ℤ) : ℝ) * (h 91 2 - h 89 2) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((2502805068546721 : ℝ) / 1153862454510034637977396480) * r0 + ((1 : ℝ) / 19000263401109760) * r1 + ((2502805068546721 : ℝ) / 2714323343015680) * r2 + ((211518274468959 : ℝ) / 2714323343015680) * r3 + ((2502805068546721 : ℝ) / 2714323343015680) * (value_022 h H) + ((-2502805068546721 : ℝ) / 2714323343015680) * (value_020 h H) + ((2502805068546721 : ℝ) / 2714323343015680) * (value_356 h H) + ((211518274468959 : ℝ) / 2714323343015680) * (value_358 h H)

/-- Coordinate 87.3, recovered from skew spokes on cycle 33. -/
theorem value_351 (h : Assignment) (H : Constraints h) :
    h 87 3 = ((-6549652612581 : ℝ) / 6760456645120) * (h 1 0) + ((800183803347 : ℝ) / 676045664512) * (h 1 2) + h 1 3 + ((6549652612581 : ℝ) / 6760456645120) * (h 3 0) + ((-800183803347 : ℝ) / 676045664512) * (h 9 2) := by
  have r0 := H 28 2
  change ((425101326811 : ℤ) : ℝ) * (h 87 2 - h 5 2) - ((425101326811 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 28 3
  change ((425101326811 : ℤ) : ℝ) * (h 87 3 - h 5 3) - ((-414910120254 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 262 2
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 2 - h 87 2) - ((17519635479827047 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 267 2
  change ((1 : ℤ) : ℝ) * (h 91 2 - h 89 2) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((103223710631763 : ℝ) / 576931227255017318988698240) * r0 + ((1 : ℝ) / 425101326811) * r1 + ((-29636437161 : ℝ) / 576931227255017318988698240) * r2 + ((-74174225140217194509099081 : ℝ) / 82418746750716759855528320) * r3 + ((-103223710631763 : ℝ) / 1357161671507840) * r4 + ((103223710631763 : ℝ) / 1357161671507840) * (value_022 h H) + ((74174225140217194509099081 : ℝ) / 82418746750716759855528320) * (value_020 h H) + (1 : ℝ) * (value_023 h H) + ((-74174225140217194509099081 : ℝ) / 82418746750716759855528320) * (value_356 h H) + ((-103223710631763 : ℝ) / 1357161671507840) * (value_358 h H)

/-- Coordinate 91.0, recovered from skew spokes on cycle 33. -/
theorem value_364 (h : Assignment) (H : Constraints h) :
    h 91 0 = ((89998332273229 : ℝ) / 41233137211910) * (h 1 0) + ((-27874501286607 : ℝ) / 20616568605955) * (h 1 2) + ((-48765195061319 : ℝ) / 41233137211910) * (h 3 0) + ((27874501286607 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_356 h H)

/-- Coordinate 91.1, recovered from skew spokes on cycle 33. -/
theorem value_365 (h : Assignment) (H : Constraints h) :
    h 91 1 = ((-380894370903783 : ℝ) / 144315980241685) * (h 1 0) + ((435443377944798 : ℝ) / 144315980241685) * (h 1 2) + ((380894370903783 : ℝ) / 144315980241685) * (h 3 0) + h 5 1 + ((-435443377944798 : ℝ) / 144315980241685) * (h 9 2) := by
  have r0 := H 28 1
  change ((425101326811 : ℤ) : ℝ) * (h 87 1 - h 5 1) - ((-948678383322 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 262 1
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 1 - h 87 1) - ((3304246809110526 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((1 : ℝ) / 425101326811) * r0 + ((-1 : ℝ) / 1480627921282713) * r1 + ((-948678383322 : ℝ) / 425101326811) * r2 + ((948678383322 : ℝ) / 425101326811) * (value_020 h H) + ((-948678383322 : ℝ) / 425101326811) * (value_356 h H)

/-- Coordinate 91.2, recovered from skew spokes on cycle 33. -/
theorem value_366 (h : Assignment) (H : Constraints h) :
    h 91 2 = ((-103596562034867 : ℝ) / 82466274423820) * (h 1 0) + ((59216465721051 : ℝ) / 41233137211910) * (h 1 2) + ((103596562034867 : ℝ) / 82466274423820) * (h 3 0) + ((-17983328509141 : ℝ) / 41233137211910) * (h 9 2) := by
  have r0 := H 267 2
  change ((1 : ℤ) : ℝ) * (h 91 2 - h 89 2) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_358 h H)

/-- Coordinate 91.3, recovered from skew spokes on cycle 33. -/
theorem value_367 (h : Assignment) (H : Constraints h) :
    h 91 3 = ((-23798059040283 : ℝ) / 20616568605955) * (h 1 0) + ((27206249313798 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((23798059040283 : ℝ) / 20616568605955) * (h 3 0) + ((-27206249313798 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 28 3
  change ((425101326811 : ℤ) : ℝ) * (h 87 3 - h 5 3) - ((-414910120254 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 262 3
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 3 - h 87 3) - ((1445131948844682 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((1 : ℝ) / 425101326811) * r0 + ((-1 : ℝ) / 1480627921282713) * r1 + ((-59272874322 : ℝ) / 60728760973) * r2 + (1 : ℝ) * (value_023 h H) + ((59272874322 : ℝ) / 60728760973) * (value_020 h H) + ((-59272874322 : ℝ) / 60728760973) * (value_356 h H)

/-- Coordinate 95.0, recovered from skew spokes on cycle 33. -/
theorem value_380 (h : Assignment) (H : Constraints h) :
    h 95 0 = ((-12483568010518 : ℝ) / 20616568605955) * (h 1 0) + ((14271376629708 : ℝ) / 20616568605955) * (h 1 2) + ((33100136616473 : ℝ) / 20616568605955) * (h 3 0) + ((-14271376629708 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 28 2
  change ((425101326811 : ℤ) : ℝ) * (h 87 2 - h 5 2) - ((425101326811 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 262 1
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 1 - h 87 1) - ((3304246809110526 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 262 2
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 2 - h 87 2) - ((17519635479827047 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 263 1
  change ((749656269610661 : ℤ) : ℝ) * (h 95 1 - h 87 1) - ((122379511448538 : ℤ) : ℝ) * (h 95 0 - h 87 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 267 2
  change ((1 : ℤ) : ℝ) * (h 91 2 - h 89 2) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 271 1
  change ((1 : ℤ) : ℝ) * (h 99 1 - h 91 1) - ((0 : ℤ) : ℝ) * (h 99 0 - h 91 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 287 1
  change ((1 : ℤ) : ℝ) * (h 99 1 - h 95 1) - ((0 : ℤ) : ℝ) * (h 99 2 - h 95 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((-918 : ℝ) / 341356365429233) * r0 + ((-107093752801523 : ℝ) / 25885503091948970892806931942) * r1 + ((34 : ℝ) / 44034971140371057) * r2 + ((-1 : ℝ) / 122379511448538) * r3 + ((-115 : ℝ) / 803) * r4 + ((918 : ℝ) / 803) * r5 + ((749656269610661 : ℝ) / 122379511448538) * r6 + ((-749656269610661 : ℝ) / 122379511448538) * r7 + ((-918 : ℝ) / 803) * (value_022 h H) + ((918 : ℝ) / 803) * (value_020 h H) + ((-115 : ℝ) / 803) * (value_356 h H) + ((918 : ℝ) / 803) * (value_358 h H)

/-- Coordinate 95.1, recovered from skew spokes on cycle 33. -/
theorem value_381 (h : Assignment) (H : Constraints h) :
    h 95 1 = ((-380894370903783 : ℝ) / 144315980241685) * (h 1 0) + ((435443377944798 : ℝ) / 144315980241685) * (h 1 2) + ((380894370903783 : ℝ) / 144315980241685) * (h 3 0) + h 5 1 + ((-435443377944798 : ℝ) / 144315980241685) * (h 9 2) := by
  have r0 := H 28 1
  change ((425101326811 : ℤ) : ℝ) * (h 87 1 - h 5 1) - ((-948678383322 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 262 1
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 1 - h 87 1) - ((3304246809110526 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 271 1
  change ((1 : ℤ) : ℝ) * (h 99 1 - h 91 1) - ((0 : ℤ) : ℝ) * (h 99 0 - h 91 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 287 1
  change ((1 : ℤ) : ℝ) * (h 99 1 - h 95 1) - ((0 : ℤ) : ℝ) * (h 99 2 - h 95 2) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((1 : ℝ) / 425101326811) * r0 + ((-1 : ℝ) / 1480627921282713) * r1 + ((-948678383322 : ℝ) / 425101326811) * r2 + (1 : ℝ) * r3 + (-1 : ℝ) * r4 + ((948678383322 : ℝ) / 425101326811) * (value_020 h H) + ((-948678383322 : ℝ) / 425101326811) * (value_356 h H)

/-- Coordinate 95.2, recovered from skew spokes on cycle 33. -/
theorem value_382 (h : Assignment) (H : Constraints h) :
    h 95 2 = ((48765195061319 : ℝ) / 41233137211910) * (h 1 0) + ((-7257932680652 : ℝ) / 20616568605955) * (h 1 2) + ((-48765195061319 : ℝ) / 41233137211910) * (h 3 0) + ((27874501286607 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 28 2
  change ((425101326811 : ℤ) : ℝ) * (h 87 2 - h 5 2) - ((425101326811 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 262 1
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 1 - h 87 1) - ((3304246809110526 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 263 1
  change ((749656269610661 : ℤ) : ℝ) * (h 95 1 - h 87 1) - ((122379511448538 : ℤ) : ℝ) * (h 95 0 - h 87 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 263 2
  change ((749656269610661 : ℤ) : ℝ) * (h 95 2 - h 87 2) - ((-54838071158619 : ℤ) : ℝ) * (h 95 0 - h 87 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 271 1
  change ((1 : ℤ) : ℝ) * (h 99 1 - h 91 1) - ((0 : ℤ) : ℝ) * (h 99 0 - h 91 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 287 1
  change ((1 : ℤ) : ℝ) * (h 99 1 - h 95 1) - ((0 : ℤ) : ℝ) * (h 99 2 - h 95 2) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((1 : ℝ) / 425101326811) * r0 + ((1 : ℝ) / 3304246809110526) * r1 + ((60728760973 : ℝ) / 101597528271634747979399406) * r2 + ((1 : ℝ) / 749656269610661) * r3 + (1 : ℝ) * r4 + ((-425101326811 : ℝ) / 948678383322) * r5 + ((425101326811 : ℝ) / 948678383322) * r6 + (1 : ℝ) * (value_022 h H) + (-1 : ℝ) * (value_020 h H) + (1 : ℝ) * (value_356 h H)

/-- Coordinate 95.3, recovered from skew spokes on cycle 33. -/
theorem value_383 (h : Assignment) (H : Constraints h) :
    h 95 3 = ((-23798059040283 : ℝ) / 20616568605955) * (h 1 0) + ((27206249313798 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((23798059040283 : ℝ) / 20616568605955) * (h 3 0) + ((-27206249313798 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 28 3
  change ((425101326811 : ℤ) : ℝ) * (h 87 3 - h 5 3) - ((-414910120254 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 262 1
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 1 - h 87 1) - ((3304246809110526 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 263 1
  change ((749656269610661 : ℤ) : ℝ) * (h 95 1 - h 87 1) - ((122379511448538 : ℤ) : ℝ) * (h 95 0 - h 87 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 263 3
  change ((749656269610661 : ℤ) : ℝ) * (h 95 3 - h 87 3) - ((53523405512766 : ℤ) : ℝ) * (h 95 0 - h 87 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 271 1
  change ((1 : ℤ) : ℝ) * (h 99 1 - h 91 1) - ((0 : ℤ) : ℝ) * (h 99 0 - h 91 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 287 1
  change ((1 : ℤ) : ℝ) * (h 99 1 - h 95 1) - ((0 : ℤ) : ℝ) * (h 99 2 - h 95 2) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((1 : ℝ) / 425101326811) * r0 + ((-9878812387 : ℝ) / 33443802444378515365383633) * r1 + ((-9878812387 : ℝ) / 16932921378605791329899901) * r2 + ((1 : ℝ) / 749656269610661) * r3 + ((-59272874322 : ℝ) / 60728760973) * r4 + ((69151686709 : ℝ) / 158113063887) * r5 + ((-69151686709 : ℝ) / 158113063887) * r6 + (1 : ℝ) * (value_023 h H) + ((59272874322 : ℝ) / 60728760973) * (value_020 h H) + ((-59272874322 : ℝ) / 60728760973) * (value_356 h H)

/-- Coordinate 99.0, recovered from skew spokes on cycle 33. -/
theorem value_396 (h : Assignment) (H : Constraints h) :
    h 99 0 = ((-12483568010518 : ℝ) / 20616568605955) * (h 1 0) + ((14271376629708 : ℝ) / 20616568605955) * (h 1 2) + ((33100136616473 : ℝ) / 20616568605955) * (h 3 0) + ((-14271376629708 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 28 2
  change ((425101326811 : ℤ) : ℝ) * (h 87 2 - h 5 2) - ((425101326811 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 262 1
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 1 - h 87 1) - ((3304246809110526 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 262 2
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 2 - h 87 2) - ((17519635479827047 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 263 1
  change ((749656269610661 : ℤ) : ℝ) * (h 95 1 - h 87 1) - ((122379511448538 : ℤ) : ℝ) * (h 95 0 - h 87 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 267 2
  change ((1 : ℤ) : ℝ) * (h 91 2 - h 89 2) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 271 1
  change ((1 : ℤ) : ℝ) * (h 99 1 - h 91 1) - ((0 : ℤ) : ℝ) * (h 99 0 - h 91 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 287 0
  change ((1 : ℤ) : ℝ) * (h 99 0 - h 95 0) - ((0 : ℤ) : ℝ) * (h 99 2 - h 95 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 287 1
  change ((1 : ℤ) : ℝ) * (h 99 1 - h 95 1) - ((0 : ℤ) : ℝ) * (h 99 2 - h 95 2) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-918 : ℝ) / 341356365429233) * r0 + ((-107093752801523 : ℝ) / 25885503091948970892806931942) * r1 + ((34 : ℝ) / 44034971140371057) * r2 + ((-1 : ℝ) / 122379511448538) * r3 + ((-115 : ℝ) / 803) * r4 + ((918 : ℝ) / 803) * r5 + ((749656269610661 : ℝ) / 122379511448538) * r6 + (1 : ℝ) * r7 + ((-749656269610661 : ℝ) / 122379511448538) * r8 + ((-918 : ℝ) / 803) * (value_022 h H) + ((918 : ℝ) / 803) * (value_020 h H) + ((-115 : ℝ) / 803) * (value_356 h H) + ((918 : ℝ) / 803) * (value_358 h H)

/-- Coordinate 99.1, recovered from skew spokes on cycle 33. -/
theorem value_397 (h : Assignment) (H : Constraints h) :
    h 99 1 = ((-380894370903783 : ℝ) / 144315980241685) * (h 1 0) + ((435443377944798 : ℝ) / 144315980241685) * (h 1 2) + ((380894370903783 : ℝ) / 144315980241685) * (h 3 0) + h 5 1 + ((-435443377944798 : ℝ) / 144315980241685) * (h 9 2) := by
  have r0 := H 28 1
  change ((425101326811 : ℤ) : ℝ) * (h 87 1 - h 5 1) - ((-948678383322 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 262 1
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 1 - h 87 1) - ((3304246809110526 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 271 1
  change ((1 : ℤ) : ℝ) * (h 99 1 - h 91 1) - ((0 : ℤ) : ℝ) * (h 99 0 - h 91 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((1 : ℝ) / 425101326811) * r0 + ((-1 : ℝ) / 1480627921282713) * r1 + ((-948678383322 : ℝ) / 425101326811) * r2 + (1 : ℝ) * r3 + ((948678383322 : ℝ) / 425101326811) * (value_020 h H) + ((-948678383322 : ℝ) / 425101326811) * (value_356 h H)

/-- Coordinate 99.2, recovered from skew spokes on cycle 33. -/
theorem value_398 (h : Assignment) (H : Constraints h) :
    h 99 2 = ((-103596562034867 : ℝ) / 82466274423820) * (h 1 0) + ((59216465721051 : ℝ) / 41233137211910) * (h 1 2) + ((103596562034867 : ℝ) / 82466274423820) * (h 3 0) + ((-17983328509141 : ℝ) / 41233137211910) * (h 9 2) := by
  have r0 := H 267 2
  change ((1 : ℤ) : ℝ) * (h 91 2 - h 89 2) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 271 2
  change ((1 : ℤ) : ℝ) * (h 99 2 - h 91 2) - ((0 : ℤ) : ℝ) * (h 99 0 - h 91 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1 + (1 : ℝ) * (value_358 h H)

/-- Coordinate 99.3, recovered from skew spokes on cycle 33. -/
theorem value_399 (h : Assignment) (H : Constraints h) :
    h 99 3 = ((-23798059040283 : ℝ) / 20616568605955) * (h 1 0) + ((27206249313798 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((23798059040283 : ℝ) / 20616568605955) * (h 3 0) + ((-27206249313798 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 28 3
  change ((425101326811 : ℤ) : ℝ) * (h 87 3 - h 5 3) - ((-414910120254 : ℤ) : ℝ) * (h 87 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 262 3
  change ((-1480627921282713 : ℤ) : ℝ) * (h 91 3 - h 87 3) - ((1445131948844682 : ℤ) : ℝ) * (h 91 0 - h 87 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 267 0
  change ((1 : ℤ) : ℝ) * (h 91 0 - h 89 0) - ((0 : ℤ) : ℝ) * (h 91 1 - h 89 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 271 3
  change ((1 : ℤ) : ℝ) * (h 99 3 - h 91 3) - ((0 : ℤ) : ℝ) * (h 99 0 - h 91 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((1 : ℝ) / 425101326811) * r0 + ((-1 : ℝ) / 1480627921282713) * r1 + ((-59272874322 : ℝ) / 60728760973) * r2 + (1 : ℝ) * r3 + (1 : ℝ) * (value_023 h H) + ((59272874322 : ℝ) / 60728760973) * (value_020 h H) + ((-59272874322 : ℝ) / 60728760973) * (value_356 h H)

/-- Coordinate 116.0, recovered from nonplanar cycle 34. -/
theorem value_464 (h : Assignment) (H : Constraints h) :
    h 116 0 = ((116253836556504342053382163315 : ℝ) / 65351055111426675551837387222) * (h 1 0) + ((2061667070398959704986122573 : ℝ) / 4216197103963011325924992724) * (h 1 1) + ((-134213750884978747507484829423 : ℝ) / 65351055111426675551837387222) * (h 1 2) + ((-50902781445077666501544776093 : ℝ) / 65351055111426675551837387222) * (h 3 0) + ((-2061667070398959704986122573 : ℝ) / 4216197103963011325924992724) * (h 5 1) + ((134213750884978747507484829423 : ℝ) / 65351055111426675551837387222) * (h 9 2) := by
  have r0 := H 276 1
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 1 - h 92 1) - ((5791516054445555661356452960 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 276 2
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 2 - h 92 2) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 293 1
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 1 - h 96 1) - ((102861978325137390546130736 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 293 2
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 2 - h 96 2) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 354 1
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 1 - h 116 1) - ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 354 2
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 2 - h 116 2) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-185432343740432322623282248997 : ℝ) / 1002825941787319483260942817785920174851655797344555963648) * r0 + ((-9 : ℝ) / 522808440891413404414699097776) * r1 + ((2410819607718430417322749417151299737186306259291463 : ℝ) / 236763026277289733244812763688159604455387781721472792122051971040221631630336) * r2 + ((117009665260111260838611 : ℝ) / 123432894454394120504573513167138058035567654452032) * r3 + ((-2410819607718430417322749417151299737186306259291463 : ℝ) / 331763561915586775348892884080476032925937182561860466200997159527500815746025162496) * r4 + ((-8567707711823702321404961 : ℝ) / 12664516698848120955719666646803138850142207655682862831152) * r5 + ((-2410819607718430417322749417151299737186306259291463 : ℝ) / 11189256692262334678891176669038652312457107441584352) * (value_369 h H) + ((9071627019691587129581543371759847814228267476278391 : ℝ) / 5594628346131167339445588334519326156228553720792176) * (value_368 h H) + ((-1310859279909026455174959033 : ℝ) / 65351055111426675551837387222) * (value_370 h H) + ((2410819607718430417322749417151299737186306259291463 : ℝ) / 11189256692262334678891176669038652312457107441584352) * (value_385 h H) + ((-3476998673560419790135955037240521657999713755486215 : ℝ) / 5594628346131167339445588334519326156228553720792176) * (value_384 h H) + ((1310859279909026455174959033 : ℝ) / 65351055111426675551837387222) * (value_386 h H)

/-- Coordinate 116.1, recovered from nonplanar cycle 34. -/
theorem value_465 (h : Assignment) (H : Constraints h) :
    h 116 1 = ((25730972583399966856700360524 : ℝ) / 32675527555713337775918693611) * (h 1 0) + ((777343598631346184615358841 : ℝ) / 1054049275990752831481248181) * (h 1 1) + ((-32673708890913507468542806734 : ℝ) / 32675527555713337775918693611) * (h 1 2) + ((-25730972583399966856700360524 : ℝ) / 32675527555713337775918693611) * (h 3 0) + ((276705677359406646865889340 : ℝ) / 1054049275990752831481248181) * (h 5 1) + ((32673708890913507468542806734 : ℝ) / 32675527555713337775918693611) * (h 9 2) := by
  have r0 := H 276 1
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 1 - h 92 1) - ((5791516054445555661356452960 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 276 2
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 2 - h 92 2) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 293 1
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 1 - h 96 1) - ((102861978325137390546130736 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 293 2
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 2 - h 96 2) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 354 1
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 1 - h 116 1) - ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 354 2
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 2 - h 116 2) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-198352154553638402281892030013241633118676490791757 : ℝ) / 3259453548963613169563978204862363490981174829137421921286768989775302714189248) * r0 + ((-145395330742909268031465 : ℝ) / 1699267796218470737900206548171056565916493967917476) * r1 + ((2995666327619222072004686197272904711232953351187845 : ℝ) / 59190756569322433311203190922039901113846945430368198030512992760055407907584) * r2 + ((145395330742909268031465 : ℝ) / 30858223613598530126143378291784514508891913613008) * r3 + ((-2995666327619222072004686197272904711232953351187845 : ℝ) / 82940890478896693837223221020119008231484295640465116550249289881875203936506290624) * r4 + ((-10646169217730800848081715 : ℝ) / 3166129174712030238929916661700784712535551913920715707788) * r5 + ((-198352154553638402281892030013241633118676490791757 : ℝ) / 2797314173065583669722794167259663078114276860396088) * (value_369 h H) + ((4320492422665814130338926851884235183322783273142725 : ℝ) / 1398657086532791834861397083629831539057138430198044) * (value_368 h H) + ((-3257727780625625059513004790 : ℝ) / 32675527555713337775918693611) * (value_370 h H) + ((2995666327619222072004686197272904711232953351187845 : ℝ) / 2797314173065583669722794167259663078114276860396088) * (value_385 h H) + ((-4320492422665814130338926851884235183322783273142725 : ℝ) / 1398657086532791834861397083629831539057138430198044) * (value_384 h H) + ((3257727780625625059513004790 : ℝ) / 32675527555713337775918693611) * (value_386 h H)

/-- Coordinate 116.2, recovered from nonplanar cycle 34. -/
theorem value_466 (h : Assignment) (H : Constraints h) :
    h 116 2 = ((-69685528373866284575206709495 : ℝ) / 522808440891413404414699097776) * (h 1 0) + ((181991951077660052977278309 : ℝ) / 33729576831704090607399941792) * (h 1 1) + ((314625604589592308369047275445 : ℝ) / 522808440891413404414699097776) * (h 1 2) + ((69685528373866284575206709495 : ℝ) / 522808440891413404414699097776) * (h 3 0) + ((-181991951077660052977278309 : ℝ) / 33729576831704090607399941792) * (h 5 1) + ((208182836301821096045651822331 : ℝ) / 522808440891413404414699097776) * (h 9 2) := by
  have r0 := H 276 1
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 1 - h 92 1) - ((5791516054445555661356452960 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 276 2
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 2 - h 92 2) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 293 1
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 1 - h 96 1) - ((102861978325137390546130736 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 293 2
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 2 - h 96 2) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 354 1
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 1 - h 116 1) - ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 354 2
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 2 - h 116 2) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-1976902697510699784209606353945204353703043213119051571911 : ℝ) / 389500353163086488945335976843445954020929083848816403031207178586162307275329550336) * r0 + ((234960206025197228368997761975 : ℝ) / 609180707873136885654272446693131094654799421522543476096) * r1 + ((1976902697510699784209606353945204353703043213119051571911 : ℝ) / 7073216489025271684111033044262538796569891516335092507048928617502941171079077888) * r2 + ((287848234866216176045701335801 : ℝ) / 11062549732580618656101896544091581313379715462608915968) * r3 + ((-1976902697510699784209606353945204353703043213119051571911 : ℝ) / 9911325824374183051289725280942861324984731349974727474266056475164244370140586387847168) * r4 + ((-10661045735785784297988938363 : ℝ) / 574124757014448149992624887988408961206446747057623115012224) * r5 + ((-1976902697510699784209606353945204353703043213119051571911 : ℝ) / 334275313929106494420314272595306724950551932448185321216) * (value_369 h H) + ((2851183072759181480736314442747041324746534269242873662855 : ℝ) / 167137656964553247210157136297653362475275966224092660608) * (value_368 h H) + ((234960206025197228368997761975 : ℝ) / 522808440891413404414699097776) * (value_370 h H) + ((1976902697510699784209606353945204353703043213119051571911 : ℝ) / 334275313929106494420314272595306724950551932448185321216) * (value_385 h H) + ((-2851183072759181480736314442747041324746534269242873662855 : ℝ) / 167137656964553247210157136297653362475275966224092660608) * (value_384 h H) + ((287848234866216176045701335801 : ℝ) / 522808440891413404414699097776) * (value_386 h H)

/-- Coordinate 116.3, recovered from nonplanar cycle 34. -/
theorem value_467 (h : Assignment) (H : Constraints h) :
    h 116 3 = ((3450783330695605018723130577 : ℝ) / 32675527555713337775918693611) * (h 1 0) + ((267782522729277245542412112 : ℝ) / 1054049275990752831481248181) * (h 1 1) + ((-4002714589940938903161736386 : ℝ) / 32675527555713337775918693611) * (h 1 2) + h 1 3 + ((-3450783330695605018723130577 : ℝ) / 32675527555713337775918693611) * (h 3 0) + ((-267782522729277245542412112 : ℝ) / 1054049275990752831481248181) * (h 5 1) + ((4002714589940938903161736386 : ℝ) / 32675527555713337775918693611) * (h 9 2) := by
  have r0 := H 276 1
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 1 - h 92 1) - ((5791516054445555661356452960 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 276 2
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 2 - h 92 2) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 276 3
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 3 - h 92 3) - ((102638922139772590676165376 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 293 1
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 1 - h 96 1) - ((102861978325137390546130736 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 293 2
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 2 - h 96 2) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 354 1
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 1 - h 116 1) - ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 354 2
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 2 - h 116 2) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-130122707985541696692457325660606294035143748679 : ℝ) / 7988856737655914631284260306035204634757781443964269414918551445527702730856) * r0 + ((-644184523159221662226 : ℝ) / 424816949054617684475051637042764141479123491979369) * r1 + ((1 : ℝ) / 1165208248808023515711074696) * r2 + ((130122707985541696692457325660606294035143748679 : ℝ) / 145075383748339297331380369906960541945703297623451465761061256764841686048) * r3 + ((322092261579610831113 : ℝ) / 3857277951699816265767922286473064313611489201626) * r4 + ((-130122707985541696692457325660606294035143748679 : ℝ) / 203286496271805622150056914264997569194814450099179207231003161475184323373789928) * r5 + ((-15722874102293595385442 : ℝ) / 263844097892669186577493055141732059377962659493392975649) * r6 + ((-2212086035754208843771774536230306998597443727543 : ℝ) / 116554757211065986238449756969152628254761535849837) * (value_369 h H) + ((6380751332446624302386649685042684269644645781230 : ℝ) / 116554757211065986238449756969152628254761535849837) * (value_368 h H) + ((-57734393703622082255343024 : ℝ) / 32675527555713337775918693611) * (value_370 h H) + (1 : ℝ) * (value_371 h H) + ((2212086035754208843771774536230306998597443727543 : ℝ) / 116554757211065986238449756969152628254761535849837) * (value_385 h H) + ((-6380751332446624302386649685042684269644645781230 : ℝ) / 116554757211065986238449756969152628254761535849837) * (value_384 h H) + ((57734393703622082255343024 : ℝ) / 32675527555713337775918693611) * (value_386 h H)

/-- Coordinate 120.0, recovered from nonplanar cycle 34. -/
theorem value_480 (h : Assignment) (H : Constraints h) :
    h 120 0 = ((129308514503944045342629379669 : ℝ) / 72674441298858640087278575651) * (h 1 0) + ((35551202651472366183311254002 : ℝ) / 72674441298858640087278575651) * (h 1 1) + ((-149303068254927490314397680882 : ℝ) / 72674441298858640087278575651) * (h 1 2) + ((-56634073205085405255350804018 : ℝ) / 72674441298858640087278575651) * (h 3 0) + ((-35551202651472366183311254002 : ℝ) / 72674441298858640087278575651) * (h 5 1) + ((149303068254927490314397680882 : ℝ) / 72674441298858640087278575651) * (h 9 2) := by
  have r0 := H 276 1
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 1 - h 92 1) - ((5791516054445555661356452960 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 276 2
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 2 - h 92 2) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 293 1
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 1 - h 96 1) - ((102861978325137390546130736 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 293 2
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 2 - h 96 2) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 354 1
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 1 - h 116 1) - ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 354 2
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 2 - h 116 2) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-5225763190878743665149810666045011232913848353287 : ℝ) / 58463149081136610561139092582838737957598600698865214180440695061681857718032) * r0 + ((-531215624692007731647 : ℝ) / 30478896234211666365432904034646416562077791631759) * r1 + ((88536305281263499132801929089 : ℝ) / 17987175352072421713610264593329652285533580263906877632) * r2 + ((9 : ℝ) / 9377347264368856785455300084) * r3 + ((-5225763190878743665149810666045011232913848353287 : ℝ) / 1487668276951442154493416912589387392990802525473941935262725329464431703886848016) * r4 + ((-38896788519114788350597 : ℝ) / 56789237573329143996372293649361648532777077414653704517) * r5 + ((-5225763190878743665149810666045011232913848353287 : ℝ) / 50173991765800515803831185266584989192441701619842) * (value_369 h H) + ((26971307225574726851197741885015239650414750917387 : ℝ) / 25086995882900257901915592633292494596220850809921) * (value_368 h H) + ((-47609669147396500941130728 : ℝ) / 2344336816092214196363825021) * (value_370 h H) + ((5225763190878743665149810666045011232913848353287 : ℝ) / 50173991765800515803831185266584989192441701619842) * (value_385 h H) + ((-1884311342674468949282149251722745054193900107466 : ℝ) / 25086995882900257901915592633292494596220850809921) * (value_384 h H) + ((47609669147396500941130728 : ℝ) / 2344336816092214196363825021) * (value_386 h H)

/-- Coordinate 120.1, recovered from nonplanar cycle 34. -/
theorem value_481 (h : Assignment) (H : Constraints h) :
    h 120 1 = ((57123224158121650301803519610 : ℝ) / 72674441298858640087278575651) * (h 1 0) + ((53540161796728255588055464436 : ℝ) / 72674441298858640087278575651) * (h 1 1) + ((-72478632673303706561023043496 : ℝ) / 72674441298858640087278575651) * (h 1 2) + ((-57123224158121650301803519610 : ℝ) / 72674441298858640087278575651) * (h 3 0) + ((19134279502130384499223111215 : ℝ) / 72674441298858640087278575651) * (h 5 1) + ((72478632673303706561023043496 : ℝ) / 72674441298858640087278575651) * (h 9 2) := by
  have r0 := H 276 1
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 1 - h 92 1) - ((5791516054445555661356452960 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 276 2
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 2 - h 92 2) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 293 1
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 1 - h 96 1) - ((102861978325137390546130736 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 293 2
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 2 - h 96 2) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 354 1
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 1 - h 116 1) - ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 354 2
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 2 - h 116 2) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-50806812432100068774808749244587847252382269177873 : ℝ) / 116926298162273221122278185165677475915197201397730428360881390123363715436064) * r0 + ((-5164675783976593964313 : ℝ) / 60957792468423332730865808069292833124155583263518) * r1 + ((151154795963701100382471119777757825637265672417557 : ℝ) / 2123348575799074579535798033167143409957395248413493046810517418702827293312) * r2 + ((5164675783976593964313 : ℝ) / 1106976307776798229496525504320630837609450790744) * r3 + ((-50806812432100068774808749244587847252382269177873 : ℝ) / 2975336553902884308986833825178774785981605050947883870525450658928863407773696032) * r4 + ((-378169037960063935831363 : ℝ) / 113578475146658287992744587298723297065554154829307409034) * r5 + ((-50806812432100068774808749244587847252382269177873 : ℝ) / 100347983531601031607662370533169978384883403239684) * (value_369 h H) + ((262225075497133620067646859384886027659872923001773 : ℝ) / 50173991765800515803831185266584989192441701619842) * (value_368 h H) + ((-231439451231559128728794156 : ℝ) / 2344336816092214196363825021) * (value_370 h H) + ((151154795963701100382471119777757825637265672417557 : ℝ) / 100347983531601031607662370533169978384883403239684) * (value_385 h H) + ((-262225075497133620067646859384886027659872923001773 : ℝ) / 50173991765800515803831185266584989192441701619842) * (value_384 h H) + ((231439451231559128728794156 : ℝ) / 2344336816092214196363825021) * (value_386 h H)

/-- Coordinate 120.2, recovered from nonplanar cycle 34. -/
theorem value_482 (h : Assignment) (H : Constraints h) :
    h 120 2 = ((-30859835989602710605426082479 : ℝ) / 290697765195434560349114302604) * (h 1 0) + ((11499865489163555859586557291 : ℝ) / 581395530390869120698228605208) * (h 1 1) + ((160626840066267720921754585353 : ℝ) / 290697765195434560349114302604) * (h 1 2) + ((30859835989602710605426082479 : ℝ) / 290697765195434560349114302604) * (h 3 0) + ((-11499865489163555859586557291 : ℝ) / 581395530390869120698228605208) * (h 5 1) + ((130070925129166839427359717251 : ℝ) / 290697765195434560349114302604) * (h 9 2) := by
  have r0 := H 276 1
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 1 - h 92 1) - ((5791516054445555661356452960 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 276 2
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 2 - h 92 2) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 293 1
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 1 - h 96 1) - ((102861978325137390546130736 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 293 2
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 2 - h 96 2) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 354 1
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 1 - h 116 1) - ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 354 2
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 2 - h 116 2) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((13259023167373046758818870178652679467588702490059917663 : ℝ) / 6986268364330383446575373378192452067615755985380127940943755805610899754827866624) * r0 + ((4043466963996211447571115909 : ℝ) / 10926562384379945545342234364804601751838639988819074464) * r1 + ((-13259023167373046758818870178652679467588702490059917663 : ℝ) / 126868661838277506744210908616381373982681061162540600551563875422548128890529792) * r2 + ((313757664727802666934363775 : ℝ) / 11671958189198560531811364917556731551754049137604736) * r3 + ((13259023167373046758818870178652679467588702490059917663 : ℝ) / 177774375537994735539090663165215007612543580724102096007981993237226969372206488781312) * r4 + ((149758035703563386947078367 : ℝ) / 10297781746630351444675509248417578933943576704523871752416) * r5 + ((13259023167373046758818870178652679467588702490059917663 : ℝ) / 5995725117357473904536754864443217428511193421302292544) * (value_369 h H) + ((-68432719642256988318816280107856171565161774948167938563 : ℝ) / 2997862558678736952268377432221608714255596710651146272) * (value_368 h H) + ((4043466963996211447571115909 : ℝ) / 9377347264368856785455300084) * (value_370 h H) + ((-13259023167373046758818870178652679467588702490059917663 : ℝ) / 5995725117357473904536754864443217428511193421302292544) * (value_385 h H) + ((68432719642256988318816280107856171565161774948167938563 : ℝ) / 2997862558678736952268377432221608714255596710651146272) * (value_384 h H) + ((5333880300372645337884184175 : ℝ) / 9377347264368856785455300084) * (value_386 h H)

/-- Coordinate 120.3, recovered from nonplanar cycle 34. -/
theorem value_483 (h : Assignment) (H : Constraints h) :
    h 120 3 = ((7670180634305715487985049609 : ℝ) / 72674441298858640087278575651) * (h 1 0) + ((18460491794733377438954686152 : ℝ) / 72674441298858640087278575651) * (h 1 1) + ((-8893840324418822981414494530 : ℝ) / 72674441298858640087278575651) * (h 1 2) + h 1 3 + ((-7670180634305715487985049609 : ℝ) / 72674441298858640087278575651) * (h 3 0) + ((-18460491794733377438954686152 : ℝ) / 72674441298858640087278575651) * (h 5 1) + ((8893840324418822981414494530 : ℝ) / 72674441298858640087278575651) * (h 9 2) := by
  have r0 := H 276 1
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 1 - h 92 1) - ((5791516054445555661356452960 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 276 2
  change ((1165208248808023515711074696 : ℤ) : ℝ) * (h 116 2 - h 92 2) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 116 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 293 1
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 1 - h 96 1) - ((102861978325137390546130736 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 293 2
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 2 - h 96 2) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 293 3
  change ((21159852954398444862724768 : ℤ) : ℝ) * (h 120 3 - h 96 3) - ((1794845640955164300638976 : ℤ) : ℝ) * (h 120 0 - h 96 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 354 1
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 1 - h 116 1) - ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 354 2
  change ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 120 2 - h 116 2) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 120 0 - h 116 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-1086435684246644336070409917316842168521102323 : ℝ) / 143292032061609339610635030840291024405878923281532387697158566327651612054) * r0 + ((-45059389138502183304 : ℝ) / 30478896234211666365432904034646416562077791631759) * r1 + ((1086435684246644336070409917316842168521102323 : ℝ) / 2602142862498865906293870138685224767104651039722417949522692915076994232) * r2 + ((11264847284625545826 : ℝ) / 138372038472099778687065688040078854701181348843) * r3 + ((1 : ℝ) / 21159852954398444862724768) * r4 + ((-1086435684246644336070409917316842168521102323 : ℝ) / 3646245776841769986503472824973988708310790503612602782506679729079489470310902) * r5 + ((-1099782868232331066568 : ℝ) / 18929745857776381332124097883120549510925692471551234839) * r6 + ((-73877626528771814852787874377545267459434957964 : ℝ) / 8362331960966752633971864211097498198740283603307) * (value_369 h H) + ((762597189892453068140151798891492078645436326328 : ℝ) / 8362331960966752633971864211097498198740283603307) * (value_368 h H) + ((-4038402692149119676437696 : ℝ) / 2344336816092214196363825021) * (value_370 h H) + ((73877626528771814852787874377545267459434957964 : ℝ) / 8362331960966752633971864211097498198740283603307) * (value_385 h H) + ((-762597189892453068140151798891492078645436326328 : ℝ) / 8362331960966752633971864211097498198740283603307) * (value_384 h H) + ((4038402692149119676437696 : ℝ) / 2344336816092214196363825021) * (value_386 h H) + (1 : ℝ) * (value_387 h H)

/-- Coordinate 136.0, recovered from nonplanar cycle 35. -/
theorem value_544 (h : Assignment) (H : Constraints h) :
    h 136 0 = ((4791476193002496478955552254 : ℝ) / 2542319556248685007085857319) * (h 1 0) + ((213187919756061655496661927 : ℝ) / 391126085576720770320901126) * (h 1 1) + ((-5709290239179495222494681169 : ℝ) / 2542319556248685007085857319) * (h 1 2) + ((-2249156636753811471869694935 : ℝ) / 2542319556248685007085857319) * (h 3 0) + ((-213187919756061655496661927 : ℝ) / 391126085576720770320901126) * (h 5 1) + ((5709290239179495222494681169 : ℝ) / 2542319556248685007085857319) * (h 9 2) := by
  have r0 := H 277 1
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 1 - h 92 1) - ((187932088937137115075554968 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 277 2
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 2 - h 92 2) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 294 1
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 1 - h 96 1) - ((180917515443547556532383808 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 294 2
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 2 - h 96 2) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 394 1
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 1 - h 136 1) - ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 394 2
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 2 - h 136 2) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-787129328216055339669224351 : ℝ) / 100357982672465440801225704295538722498632474981184512) * r0 + ((-27 : ℝ) / 40677112899978960113373717104) * r1 + ((602712465732737609454320642470915528617649335995 : ℝ) / 82291128726224131028463754128518773813624955074724917438195622525344038912) * r2 + ((20674158605759831496615 : ℝ) / 33354252892746870880822240249555896169901642971904) * r3 + ((-602712465732737609454320642470915528617649335995 : ℝ) / 4849419167760348738161839108171307135901640569668423455644931028939875875161088) * r4 + ((-504602611896138109491455 : ℝ) / 47974402352351617965399620990660713062976300810088717232) * r5 + ((-602712465732737609454320642470915528617649335995 : ℝ) / 559883416676701780779845266310021436772697463744) * (value_369 h H) + ((9513805022008255181599634814519463778016068386073 : ℝ) / 4852322944531415433425325641353519118696711352448) * (value_368 h H) + ((-231612598860327392256577845 : ℝ) / 2542319556248685007085857319) * (value_370 h H) + ((602712465732737609454320642470915528617649335995 : ℝ) / 559883416676701780779845266310021436772697463744) * (value_385 h H) + ((-4661482077476839748174309173165944659319357033625 : ℝ) / 4852322944531415433425325641353519118696711352448) * (value_384 h H) + ((231612598860327392256577845 : ℝ) / 2542319556248685007085857319) * (value_386 h H)

/-- Coordinate 136.1, recovered from nonplanar cycle 35. -/
theorem value_545 (h : Assignment) (H : Constraints h) :
    h 136 1 = ((4193580421215274133070474349 : ℝ) / 5084639112497370014171714638) * (h 1 0) + ((592360119142457741376988247 : ℝ) / 782252171153441540641802252) * (h 1 1) + ((-5428426250568344182008510411 : ℝ) / 5084639112497370014171714638) * (h 1 2) + ((-4193580421215274133070474349 : ℝ) / 5084639112497370014171714638) * (h 3 0) + ((189892052010983799264814005 : ℝ) / 782252171153441540641802252) * (h 5 1) + ((5428426250568344182008510411 : ℝ) / 5084639112497370014171714638) * (h 9 2) := by
  have r0 := H 277 1
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 1 - h 92 1) - ((187932088937137115075554968 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 277 2
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 2 - h 92 2) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 294 1
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 1 - h 96 1) - ((180917515443547556532383808 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 294 2
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 2 - h 96 2) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 394 1
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 1 - h 136 1) - ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 394 2
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 2 - h 136 2) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-10407068012871040788731875528684474913099315669 : ℝ) / 3013532100398906965398780163027826222915172556497493213672216022829946880) * r0 + ((-56616156401217331373739 : ℝ) / 62293709905078835119972247786033586775106514340960) * r1 + ((550175767336608880595005394860983698037820008869 : ℝ) / 54860752484149420685642502752345849209083303383149944958797081683562692608) * r2 + ((56616156401217331373739 : ℝ) / 66708505785493741761644480499111792339803285943808) * r3 + ((-550175767336608880595005394860983698037820008869 : ℝ) / 3232946111840232492107892738780871423934427046445615637096620685959917250107392) * r4 + ((-460617865042002733028321 : ℝ) / 31982934901567745310266413993773808708650867206725811488) * r5 + ((-176920156218807693408441883987636073522688366373 : ℝ) / 373255611117801187186563510873347624515131642496) * (value_369 h H) + ((12765462594756979924651734781598071183850682827925 : ℝ) / 9704645889062830866850651282707038237393422704896) * (value_368 h H) + ((-634270800162837763379998017 : ℝ) / 5084639112497370014171714638) * (value_370 h H) + ((550175767336608880595005394860983698037820008869 : ℝ) / 373255611117801187186563510873347624515131642496) * (value_385 h H) + ((-12765462594756979924651734781598071183850682827925 : ℝ) / 9704645889062830866850651282707038237393422704896) * (value_384 h H) + ((634270800162837763379998017 : ℝ) / 5084639112497370014171714638) * (value_386 h H)

/-- Coordinate 136.2, recovered from nonplanar cycle 35. -/
theorem value_546 (h : Assignment) (H : Constraints h) :
    h 136 2 = ((-9291944721704916188588246191 : ℝ) / 40677112899978960113373717104) * (h 1 0) + ((-281873812034490437149632993 : ℝ) / 6258017369227532325134418016) * (h 1 1) + ((31503118265292785232231262877 : ℝ) / 40677112899978960113373717104) * (h 1 2) + ((9291944721704916188588246191 : ℝ) / 40677112899978960113373717104) * (h 3 0) + ((281873812034490437149632993 : ℝ) / 6258017369227532325134418016) * (h 5 1) + ((9173994634686174881142454227 : ℝ) / 40677112899978960113373717104) * (h 9 2) := by
  have r0 := H 277 1
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 1 - h 92 1) - ((187932088937137115075554968 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 277 2
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 2 - h 92 2) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 294 1
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 1 - h 96 1) - ((180917515443547556532383808 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 294 2
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 2 - h 96 2) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 394 1
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 1 - h 136 1) - ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 394 2
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 2 - h 136 2) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-577130983509152204314062725969921177174050064615895949 : ℝ) / 13774324849273733531211913939891500767530020685380097920890093130335669117829120) * r0 + ((20880446715448310685376954031 : ℝ) / 5583011456532785518792392735575474181132146241294199040) * r1 + ((577130983509152204314062725969921177174050064615895949 : ℝ) / 14750520241918223038590071000028733168544645947234292000961688946422868286898176) * r2 + ((19796666184530649427996763073 : ℝ) / 5978683122519091111645624920252395276662529699427848192) * r3 + ((-577130983509152204314062725969921177174050064615895949 : ℝ) / 869248686982706990618033336461490461496097268831925567577442597075414870870874701824) * r4 + ((-733209858686320349185065299 : ℝ) / 13049037439839640086588696909459713953129553820344131087104) * r5 + ((-577130983509152204314062725969921177174050064615895949 : ℝ) / 100357982672465440801225704295538722498632474981184512) * (value_369 h H) + ((4463630485415337523083213045920005038690122236128062975 : ℝ) / 869769183161367153610622770561335594988148116503599104) * (value_368 h H) + ((20880446715448310685376954031 : ℝ) / 40677112899978960113373717104) * (value_370 h H) + ((577130983509152204314062725969921177174050064615895949 : ℝ) / 100357982672465440801225704295538722498632474981184512) * (value_385 h H) + ((-4463630485415337523083213045920005038690122236128062975 : ℝ) / 869769183161367153610622770561335594988148116503599104) * (value_384 h H) + ((19796666184530649427996763073 : ℝ) / 40677112899978960113373717104) * (value_386 h H)

/-- Coordinate 136.3, recovered from nonplanar cycle 35. -/
theorem value_547 (h : Assignment) (H : Constraints h) :
    h 136 3 = ((400840909230863343986102535 : ℝ) / 2542319556248685007085857319) * (h 1 0) + ((55080332269817589302385951 : ℝ) / 195563042788360385160450563) * (h 1 1) + ((-551634595776523028599468848 : ℝ) / 2542319556248685007085857319) * (h 1 2) + h 1 3 + ((-400840909230863343986102535 : ℝ) / 2542319556248685007085857319) * (h 3 0) + ((-55080332269817589302385951 : ℝ) / 195563042788360385160450563) * (h 5 1) + ((551634595776523028599468848 : ℝ) / 2542319556248685007085857319) * (h 9 2) := by
  have r0 := H 277 1
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 1 - h 92 1) - ((187932088937137115075554968 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 277 2
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 2 - h 92 2) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 277 3
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 3 - h 92 3) - ((55341082595537432543614304 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 294 1
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 1 - h 96 1) - ((180917515443547556532383808 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 294 2
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 2 - h 96 2) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 394 1
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 1 - h 136 1) - ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 394 2
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 2 - h 136 2) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-246469118302120358695880378486256638542195043 : ℝ) / 77936175010316559449968452492098954040909635081831721043246966107671040) * r0 + ((-4167994147994707552323 : ℝ) / 15573427476269708779993061946508396693776628585240) * r1 + ((1 : ℝ) / 137251910435749565781675760) * r2 + ((246469118302120358695880378486256638542195043 : ℝ) / 83459562602661390495399344957929790886029366201546569409934708443553792) * r3 + ((4167994147994707552323 : ℝ) / 16677126446373435440411120124777948084950821485952) * r4 + ((-246469118302120358695880378486256638542195043 : ℝ) / 4918275018012524075214846965690980868054402200475074498625690698721983646208) * r5 + ((-101729931241796750999291 : ℝ) / 23987201176175808982699810495330356531488150405044358616) * r6 + ((-4189975011136046097829966434266362855217315731 : ℝ) / 9653162356494858289307677005345197185736163168) * (value_369 h H) + ((32405988808845050435534542426410902916025789025 : ℝ) / 83660740422955438507333200712991708943046747456) * (value_368 h H) + ((-93388076879969417417349138 : ℝ) / 2542319556248685007085857319) * (value_370 h H) + (1 : ℝ) * (value_371 h H) + ((4189975011136046097829966434266362855217315731 : ℝ) / 9653162356494858289307677005345197185736163168) * (value_385 h H) + ((-32405988808845050435534542426410902916025789025 : ℝ) / 83660740422955438507333200712991708943046747456) * (value_384 h H) + ((93388076879969417417349138 : ℝ) / 2542319556248685007085857319) * (value_386 h H)

/-- Coordinate 140.0, recovered from nonplanar cycle 35. -/
theorem value_560 (h : Assignment) (H : Constraints h) :
    h 140 0 = ((19216447856148906407574853279 : ℝ) / 10142285318032214414898904385) * (h 1 0) + ((85875961378985222076361338 : ℝ) / 156035158738957144844598529) * (h 1 1) + ((-22960600609335036967202013198 : ℝ) / 10142285318032214414898904385) * (h 1 2) + ((-9074162538116691992675948894 : ℝ) / 10142285318032214414898904385) * (h 3 0) + ((-85875961378985222076361338 : ℝ) / 156035158738957144844598529) * (h 5 1) + ((22960600609335036967202013198 : ℝ) / 10142285318032214414898904385) * (h 9 2) := by
  have r0 := H 277 1
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 1 - h 92 1) - ((187932088937137115075554968 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 277 2
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 2 - h 92 2) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 294 1
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 1 - h 96 1) - ((180917515443547556532383808 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 294 2
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 2 - h 96 2) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 394 1
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 1 - h 136 1) - ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 394 2
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 2 - h 136 2) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-282640543507080379369776304332055506279811675091 : ℝ) / 62270889056130662847060890871980513126567813314647878748815565298994689200) * r0 + ((-5534837430071341931388 : ℝ) / 7766045010735825746121629000810192370288086524325) * r1 + ((5515099419708018981062833631 : ℝ) / 1301190756307432354158609531475410322812938020278562560) * r2 + ((27 : ℝ) / 40569141272128857659595617540) * r3 + ((-282640543507080379369776304332055506279811675091 : ℝ) / 3929694496216371886768688313628195378802503504092704933930405968534244939697840) * r4 + ((-135091032089519049362396 : ℝ) / 11961765276116182256169486638004647615647615394795864205) * r5 + ((-282640543507080379369776304332055506279811675091 : ℝ) / 453697794503785381900568462226709057706689203045) * (value_369 h H) + ((416058743801485280314444486468117907813820579077 : ℝ) / 302465196335856921267045641484472705137792802030) * (value_368 h H) + ((-992108539665427898517436224 : ℝ) / 10142285318032214414898904385) * (value_370 h H) + ((282640543507080379369776304332055506279811675091 : ℝ) / 453697794503785381900568462226709057706689203045) * (value_385 h H) + ((-113593547465628359047398844983645202676027777047 : ℝ) / 302465196335856921267045641484472705137792802030) * (value_384 h H) + ((992108539665427898517436224 : ℝ) / 10142285318032214414898904385) * (value_386 h H)

/-- Coordinate 140.1, recovered from nonplanar cycle 35. -/
theorem value_561 (h : Assignment) (H : Constraints h) :
    h 140 1 = ((8299416986506909385423492114 : ℝ) / 10142285318032214414898904385) * (h 1 0) + ((117623495268038676963969274 : ℝ) / 156035158738957144844598529) * (h 1 1) + ((-10709194217554460098522315188 : ℝ) / 10142285318032214414898904385) * (h 1 2) + ((-8299416986506909385423492114 : ℝ) / 10142285318032214414898904385) * (h 3 0) + ((38411663470918467880629255 : ℝ) / 156035158738957144844598529) * (h 5 1) + ((10709194217554460098522315188 : ℝ) / 10142285318032214414898904385) * (h 9 2) := by
  have r0 := H 277 1
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 1 - h 92 1) - ((187932088937137115075554968 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 277 2
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 2 - h 92 2) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 294 1
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 1 - h 96 1) - ((180917515443547556532383808 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 294 2
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 2 - h 96 2) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 394 1
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 1 - h 136 1) - ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 394 2
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 2 - h 136 2) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-27286603149610597872270393767997917272114587319 : ℝ) / 4883991298520051988004775754665138284436691240364539509711024729332916800) * r0 + ((-6812869483865627547273 : ℝ) / 7766045010735825746121629000810192370288086524325) * r1 + ((1068802646215094006362687977024910003901533588483 : ℝ) / 88912090144113761020361393318638259468857207315643884433160871145713402880) * r2 + ((6812869483865627547273 : ℝ) / 8316429689586329557428826615711193000235709975760) * r3 + ((-27286603149610597872270393767997917272114587319 : ℝ) / 308211333036578187197544181461034931670784588556290583053365174002685877623360) * r4 + ((-55428160368733932761147 : ℝ) / 3987255092038727418723162212668215871882538464931954735) * r5 + ((-463872253543380163828596694055964593625947984423 : ℝ) / 604930392671713842534091282968945410275585604060) * (value_369 h H) + ((2048518284378278531316176364272780009530929561843 : ℝ) / 1209860785343427685068182565937890820551171208120) * (value_368 h H) + ((-1221193229243946006593590704 : ℝ) / 10142285318032214414898904385) * (value_370 h H) + ((1068802646215094006362687977024910003901533588483 : ℝ) / 604930392671713842534091282968945410275585604060) * (value_385 h H) + ((-2048518284378278531316176364272780009530929561843 : ℝ) / 1209860785343427685068182565937890820551171208120) * (value_384 h H) + ((1221193229243946006593590704 : ℝ) / 10142285318032214414898904385) * (value_386 h H)

/-- Coordinate 140.2, recovered from nonplanar cycle 35. -/
theorem value_562 (h : Assignment) (H : Constraints h) :
    h 140 2 = ((-1894604078825100633048058891 : ℝ) / 40569141272128857659595617540) * (h 1 0) + ((64037000728352545155776199 : ℝ) / 1248281269911657158756788232) * (h 1 1) + ((18039024383610170800030847157 : ℝ) / 40569141272128857659595617540) * (h 1 2) + ((1894604078825100633048058891 : ℝ) / 40569141272128857659595617540) * (h 3 0) + ((-64037000728352545155776199 : ℝ) / 1248281269911657158756788232) * (h 5 1) + ((22530116888518686859564770383 : ℝ) / 40569141272128857659595617540) * (h 9 2) := by
  have r0 := H 277 1
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 1 - h 92 1) - ((187932088937137115075554968 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 277 2
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 2 - h 92 2) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 294 1
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 1 - h 96 1) - ((180917515443547556532383808 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 294 2
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 2 - h 96 2) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 394 1
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 1 - h 136 1) - ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 394 2
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 2 - h 136 2) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1080761246549379330859226378090605431750980959201692161 : ℝ) / 59530305714844314954719843024110736090192146138794682506494359726475733598515200) * r0 + ((15873088462861176552038172111 : ℝ) / 5568192144337501173363239020548901447957595733248830400) * r1 + ((-1080761246549379330859226378090605431750980959201692161 : ℝ) / 63749257336608413741510956118317082933094866787658139987500879324507344157736960) * r2 + ((24696052809267681107557445429 : ℝ) / 5962813555995881602040009252851999691625002166940113920) * r3 + ((154394463792768475837032339727229347392997279885956023 : ℝ) / 536678003091651221302486737402839440197783731886940323045453264036439113867396894720) * r4 + ((27994865013864508910120233 : ℝ) / 619733362876876490224400069626145552658314549977995250240) * r5 + ((1080761246549379330859226378090605431750980959201692161 : ℝ) / 433730252102477451386203177158470107604312673426187520) * (value_369 h H) + ((-4772777758730120649636472987051128849048098848176982101 : ℝ) / 867460504204954902772406354316940215208625346852375040) * (value_368 h H) + ((15873088462861176552038172111 : ℝ) / 40569141272128857659595617540) * (value_370 h H) + ((-1080761246549379330859226378090605431750980959201692161 : ℝ) / 433730252102477451386203177158470107604312673426187520) * (value_385 h H) + ((4772777758730120649636472987051128849048098848176982101 : ℝ) / 867460504204954902772406354316940215208625346852375040) * (value_384 h H) + ((24696052809267681107557445429 : ℝ) / 40569141272128857659595617540) * (value_386 h H)

/-- Coordinate 140.3, recovered from nonplanar cycle 35. -/
theorem value_563 (h : Assignment) (H : Constraints h) :
    h 140 3 = ((1652783455024682952663638331 : ℝ) / 10142285318032214414898904385) * (h 1 0) + ((44385079091353524376344828 : ℝ) / 156035158738957144844598529) * (h 1 1) + ((-2298096067182135113927703582 : ℝ) / 10142285318032214414898904385) * (h 1 2) + h 1 3 + ((-1652783455024682952663638331 : ℝ) / 10142285318032214414898904385) * (h 3 0) + ((-44385079091353524376344828 : ℝ) / 156035158738957144844598529) * (h 5 1) + ((2298096067182135113927703582 : ℝ) / 10142285318032214414898904385) * (h 9 2) := by
  have r0 := H 277 1
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 1 - h 92 1) - ((187932088937137115075554968 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 277 2
  change ((137251910435749565781675760 : ℤ) : ℝ) * (h 136 2 - h 92 2) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 136 0 - h 92 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 294 1
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 1 - h 96 1) - ((180917515443547556532383808 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 294 2
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 2 - h 96 2) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 294 3
  change ((146979042913396725706286848 : ℤ) : ℝ) * (h 140 3 - h 96 3) - ((60535202294100003863055392 : ℤ) : ℝ) * (h 140 0 - h 96 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 394 1
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 1 - h 136 1) - ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 394 2
  change ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 140 2 - h 136 2) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 140 0 - h 136 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-1888991963563815981763386314922186198756987209 : ℝ) / 1010480958314493514759608776827269989883453360075421967526418909517155200) * r0 + ((-4559187444045958962729 : ℝ) / 15532090021471651492243258001620384740576173048650) * r1 + ((1888991963563815981763386314922186198756987209 : ℝ) / 1082094403376638065156528113411418979337004551508850520484716484532008960) * r2 + ((4559187444045958962729 : ℝ) / 16632859379172659114857653231422386000471419951520) * r3 + ((1 : ℝ) / 146979042913396725706286848) * r4 + ((-1888991963563815981763386314922186198756987209 : ℝ) / 63767862007567900799491899612627916897403707977163568907592794621245353991040) * r5 + ((-111277945393566183571793 : ℝ) / 23923530552232364512338973276009295231295230789591728410) * r6 + ((-32112863380584871689977567353677165378868782553 : ℝ) / 125158012276906312248432679234954222815638400840) * (value_369 h H) + ((47271482824827498948905163476173552021646313391 : ℝ) / 83438674851270874832288452823302815210425600560) * (value_368 h H) + ((-408612615485175026075623896 : ℝ) / 10142285318032214414898904385) * (value_370 h H) + ((32112863380584871689977567353677165378868782553 : ℝ) / 125158012276906312248432679234954222815638400840) * (value_385 h H) + ((-47271482824827498948905163476173552021646313391 : ℝ) / 83438674851270874832288452823302815210425600560) * (value_384 h H) + ((408612615485175026075623896 : ℝ) / 10142285318032214414898904385) * (value_386 h H) + (1 : ℝ) * (value_387 h H)

/-- Coordinate 132.0, recovered from nonplanar cycle 36. -/
theorem value_528 (h : Assignment) (H : Constraints h) :
    h 132 0 = ((9018608418867289852888476 : ℝ) / 5742396841739446764092893) * (h 1 0) + ((109175811564558021538052 : ℝ) / 249669427901715076699691) * (h 1 1) + ((-10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (h 1 2) + ((-3276211577127843088795583 : ℝ) / 5742396841739446764092893) * (h 3 0) + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (h 5 1) + ((10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (h 9 2) := by
  have r0 := H 281 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 1 - h 93 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 281 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 2 - h 93 2) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 289 1
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 1 - h 95 1) - ((-16173338539794183554831816 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 289 2
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 2 - h 95 2) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 388 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 1 - h 132 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 388 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 2 - h 132 2) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-7 : ℝ) / 16977521097316625215578988) * r0 + ((811393683605415051318460 : ℝ) / 663681344105394983865718511197506853970787067503) * r1 + ((3899136127305643626359 : ℝ) / 125778150211791524602780748119317401946662492527) * r2 + ((-12654937700853914989149250039754856794237148560 : ℝ) / 137672933331573714400202972907225171958741493577418890241217212799993061) * r3 + ((27293952891139505384513 : ℝ) / 165182849961609417340162214604631186978140158538) * r4 + ((-107566970457258277407768625337916282751015762760 : ℝ) / 219547857354880508140780884327092461202405528194691391336165816638550177) * r5 + ((109175811564558021538052 : ℝ) / 249669427901715076699691) * (value_373 h H) + ((-2133964769959912496142557094722119097136748943993 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_372 h H) + ((-860535763658066219262149002703330262008126102080 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_374 h H) + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (value_381 h H) + ((2797646114065307480008275605919625951107536011496 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_380 h H) + ((860535763658066219262149002703330262008126102080 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_382 h H)

/-- Coordinate 132.1, recovered from nonplanar cycle 36. -/
theorem value_529 (h : Assignment) (H : Constraints h) :
    h 132 1 = ((-255174997716761229511173 : ℝ) / 28711984208697233820464465) * (h 1 0) + ((131972807462839763526612 : ℝ) / 249669427901715076699691) * (h 1 1) + ((291719362271465515182138 : ℝ) / 28711984208697233820464465) * (h 1 2) + ((255174997716761229511173 : ℝ) / 28711984208697233820464465) * (h 3 0) + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (h 5 1) + ((-291719362271465515182138 : ℝ) / 28711984208697233820464465) * (h 9 2) := by
  have r0 := H 281 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 1 - h 93 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 281 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 2 - h 93 2) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 289 1
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 1 - h 95 1) - ((-16173338539794183554831816 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 289 2
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 2 - h 95 2) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 388 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 1 - h 132 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 388 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 2 - h 132 2) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-32993201865709940881653 : ℝ) / 66197665862641007250553477607808738034123344692) * r0 + ((-148289277027651276764431664770561842927216985 : ℝ) / 112512343731309306519764931103809543857092600002292339080088532309199) * r1 + ((-16813802919839330453297 : ℝ) / 503112600847166098411122992477269607786649970108) * r2 + ((13642613486543917462327713158891689549303962620 : ℝ) / 137672933331573714400202972907225171958741493577418890241217212799993061) * r3 + ((-117696620438875313173079 : ℝ) / 660731399846437669360648858418524747912560634152) * r4 + ((115962214635623298429785561850579361169083682270 : ℝ) / 219547857354880508140780884327092461202405528194691391336165816638550177) * r5 + ((131972807462839763526612 : ℝ) / 249669427901715076699691) * (value_373 h H) + ((3015993085746217856391483570845306956342598271542 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_372 h H) + ((927697717084986387438284494804634889352669458160 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_374 h H) + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (value_381 h H) + ((-3015993085746217856391483570845306956342598271542 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_380 h H) + ((-927697717084986387438284494804634889352669458160 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_382 h H)

/-- Coordinate 132.2, recovered from nonplanar cycle 36. -/
theorem value_530 (h : Assignment) (H : Constraints h) :
    h 132 2 = ((-19542286684597921862853605579 : ℝ) / 3904829852382823799583167240) * (h 1 0) + ((-21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (h 1 1) + ((771936032082788798665478471 : ℝ) / 114847936834788935281857860) * (h 1 2) + ((19542286684597921862853605579 : ℝ) / 3904829852382823799583167240) * (h 3 0) + ((21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (h 5 1) + ((-657088095247999863383620611 : ℝ) / 114847936834788935281857860) * (h 9 2) := by
  have r0 := H 281 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 1 - h 93 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 281 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 2 - h 93 2) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 289 1
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 1 - h 95 1) - ((-16173338539794183554831816 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 289 2
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 2 - h 95 2) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 388 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 1 - h 132 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 388 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 2 - h 132 2) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((21109129961762864834309105 : ℝ) / 18005765114638353972150545909323976745281549756224) * r0 + ((-135239652957254471780683139353780237678689081061 : ℝ) / 30603357494916131373376061260236195929129187200623516229784080788102128) * r1 + ((-3015589994537552119187015 : ℝ) / 34211656857607294691956363488454333329492197967344) * r2 + ((611707668477864466772498423484859653159765449225 : ℝ) / 2340439866636753144803450539422827923298605390816121134100692617599882037) * r3 + ((-21109129961762864834309105 : ℝ) / 44929735189557761516524122372459682858054123122336) * r4 + ((611707668477864466772498423484859653159765449225 : ℝ) / 439095714709761016281561768654184922404811056389382782672331633277100354) * r5 + ((-21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (value_373 h H) + ((270462268896917764219351757482958214605698358821645 : ℝ) / 22565165699583429451434429380715233035006760295102) * (value_372 h H) + ((3110512018016852850955712205136945466609848864403 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_374 h H) + ((21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (value_381 h H) + ((-270462268896917764219351757482958214605698358821645 : ℝ) / 22565165699583429451434429380715233035006760295102) * (value_380 h H) + ((-2446830673911457867089993693939438612639061796900 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_382 h H)

/-- Coordinate 132.3, recovered from nonplanar cycle 36. -/
theorem value_531 (h : Assignment) (H : Constraints h) :
    h 132 3 = ((36813195939601494408633 : ℝ) / 428537077741749758514395) * (h 1 0) + ((928717562452291111080 : ℝ) / 3726409371667389204473) * (h 1 1) + ((-42085322381761110668898 : ℝ) / 428537077741749758514395) * (h 1 2) + h 1 3 + ((-36813195939601494408633 : ℝ) / 428537077741749758514395) * (h 3 0) + ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (h 5 1) + ((42085322381761110668898 : ℝ) / 428537077741749758514395) * (h 9 2) := by
  have r0 := H 281 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 1 - h 93 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 281 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 2 - h 93 2) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 281 3
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 3 - h 93 3) - ((-604462459218948328868640 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 289 1
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 1 - h 95 1) - ((-16173338539794183554831816 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 289 2
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 2 - h 95 2) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 388 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 1 - h 132 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 388 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 2 - h 132 2) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-6828805606266846405 : ℝ) / 29059554812397281497170095525815951727007614) * r0 + ((8970899571752459370711573936427398718030200 : ℝ) / 12874546795124945522162156295460793575687212935585690541502667876177) * r1 + ((-1 : ℝ) / 1060565026627135066369648) * r2 + ((1951087316076241830 : ℝ) / 110428577885681759967322869288250572385129493) * r3 + ((-35883598287009837482846295745709594872120800 : ℝ) / 684939966823749822886581954762314288351947729240890001200085635820861) * r4 + ((38696565102178796295 : ℝ) / 410902611844799545622294066180674594472985469) * r5 + ((-101670195146527872868064504612843852137675600 : ℝ) / 364092632429320909022853871189208061695531555878426851303757573198259) * r6 + ((928717562452291111080 : ℝ) / 3726409371667389204473) * (value_373 h H) + ((-7932841052197327214846783698902774550337327280 : ℝ) / 3301897234355198924705067219888093800849686903) * (value_372 h H) + ((-2440084683516668948833548110708252451304214400 : ℝ) / 3301897234355198924705067219888093800849686903) * (value_374 h H) + (1 : ℝ) * (value_375 h H) + ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (value_381 h H) + ((7932841052197327214846783698902774550337327280 : ℝ) / 3301897234355198924705067219888093800849686903) * (value_380 h H) + ((2440084683516668948833548110708252451304214400 : ℝ) / 3301897234355198924705067219888093800849686903) * (value_382 h H)

/-- Coordinate 133.0, recovered from nonplanar cycle 36. -/
theorem value_532 (h : Assignment) (H : Constraints h) :
    h 133 0 = ((170624048649954562499929323 : ℝ) / 110318384109134813329057925) * (h 1 0) + ((414876610754063195580374 : ℝ) / 959290296601172289817895) * (h 1 1) + ((-195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (h 1 2) + ((-60305664540819749170871398 : ℝ) / 110318384109134813329057925) * (h 3 0) + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (h 5 1) + ((195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (h 9 2) := by
  have r0 := H 281 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 1 - h 93 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 281 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 2 - h 93 2) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 289 1
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 1 - h 95 1) - ((-16173338539794183554831816 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 289 2
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 2 - h 95 2) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 388 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 1 - h 132 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 388 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 2 - h 132 2) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-207438305377031597790187 : ℝ) / 508694869478987292503965422575308421696337625480) * r0 + ((1471648253006534054395790270040846241199990873 : ℝ) / 864599246262456192552614576530943336803216550010458680484317114208310) * r1 + ((1 : ℝ) / 32615870084439857853808430) * r2 + ((-14188780132307047460758 : ℝ) / 110870615699676288638897051091202587665906802045) * r3 + ((207438305377031597790187 : ℝ) / 1269344881067921306611865300474840633776922573220) * r4 + ((-25018020301111078924728434590694386100399844841 : ℝ) / 36676345262184742659579974528407094905317269256292052431804232163583155) * r5 + ((414876610754063195580374 : ℝ) / 959290296601172289817895) * (value_373 h H) + ((-517394072576382095788525389758503863472695483757 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_372 h H) + ((-200144162408888631397827476725555088803198758728 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_374 h H) + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (value_381 h H) + ((628264688276058384427422440849706451138602285802 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_380 h H) + ((200144162408888631397827476725555088803198758728 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_382 h H)

/-- Coordinate 133.1, recovered from nonplanar cycle 36. -/
theorem value_533 (h : Assignment) (H : Constraints h) :
    h 133 1 = ((-823533213543044848835519 : ℝ) / 4796451483005861449089475) * (h 1 0) + ((20682018593087191246588 : ℝ) / 41708273765268360426865) * (h 1 1) + ((941473835656930474758414 : ℝ) / 4796451483005861449089475) * (h 1 2) + ((823533213543044848835519 : ℝ) / 4796451483005861449089475) * (h 3 0) + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (h 5 1) + ((-941473835656930474758414 : ℝ) / 4796451483005861449089475) * (h 9 2) := by
  have r0 := H 281 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 1 - h 93 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 281 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 2 - h 93 2) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 289 1
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 1 - h 95 1) - ((-16173338539794183554831816 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 289 2
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 2 - h 95 2) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 388 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 1 - h 132 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 388 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 2 - h 132 2) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-5170504648271797811647 : ℝ) / 11058584119108419402260117882071922210789948380) * r0 + ((502487353612329611293885775537628715807181 : ℝ) / 257474462853620069253309879848404805480409931509963871496223083445) * r1 + ((-3003750738883024168611 : ℝ) / 84046966692094715514142602551538047861987973620) * r2 + ((-46228836532334324239037491349461841854260652 : ℝ) / 315052227902040599303757589647861427112883036890394204015741288390855) * r3 + ((70828830798243805639 : ℝ) / 378006218304919984101210631469577317980024590) * r4 + ((-392945110524841756031818676470425655761215542 : ℝ) / 502415688523078666569588692169960204182428345976603457969920988542235) * r5 + ((20682018593087191246588 : ℝ) / 41708273765268360426865) * (value_373 h H) + ((-8126441204638216001750425879336055987755718734 : ℝ) / 1518775557529812173135576042345240926930230165) * (value_372 h H) + ((-3143560884198734048254549411763405246089724336 : ℝ) / 1518775557529812173135576042345240926930230165) * (value_374 h H) + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (value_381 h H) + ((8126441204638216001750425879336055987755718734 : ℝ) / 1518775557529812173135576042345240926930230165) * (value_380 h H) + ((3143560884198734048254549411763405246089724336 : ℝ) / 1518775557529812173135576042345240926930230165) * (value_382 h H)

/-- Coordinate 133.2, recovered from nonplanar cycle 36. -/
theorem value_534 (h : Assignment) (H : Constraints h) :
    h 133 2 = ((-1624896392393843136959898023 : ℝ) / 326158700844398578538084300) * (h 1 0) + ((-1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (h 1 1) + ((64228273569540695124725957 : ℝ) / 9592902966011722898178950) * (h 1 2) + ((1624896392393843136959898023 : ℝ) / 326158700844398578538084300) * (h 3 0) + ((1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (h 5 1) + ((-54635370603528972226547007 : ℝ) / 9592902966011722898178950) * (h 9 2) := by
  have r0 := H 281 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 1 - h 93 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 281 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 2 - h 93 2) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 289 1
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 1 - h 95 1) - ((-16173338539794183554831816 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 289 2
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 2 - h 95 2) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 388 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 1 - h 132 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 388 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 2 - h 132 2) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1756706192469233448233147 : ℝ) / 1503967440198745038707376031961781420667432979680) * r0 + ((-12462758961004109873627929604877056113958672713 : ℝ) / 2556206467210740047546860487134962908809509800030921316214502772441960) * r1 + ((-250958027495604778319021 : ℝ) / 2857596867531220327480848486752293627307591103080) * r2 + ((462416296506512765547987710733141993576192142753 : ℝ) / 1563919259305729534943852675011984124188351395123916828734139755572204220) * r3 + ((-1756706192469233448233147 : ℝ) / 3752845735331245602156819149229963612905684129520) * r4 + ((286643456103094527093442380912172290621049472399 : ℝ) / 146705381048738970638319898113628379621269077025168209727216928654332620) * r5 + ((-1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (value_373 h H) + ((100776544141958768543664328009042765885888475323291 : ℝ) / 7539201867577987627444999474201775961281662539060) * (value_372 h H) + ((573286912206189054186884761824344581242098944798 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_374 h H) + ((1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (value_381 h H) + ((-100776544141958768543664328009042765885888475323291 : ℝ) / 7539201867577987627444999474201775961281662539060) * (value_380 h H) + ((-462416296506512765547987710733141993576192142753 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_382 h H)

/-- Coordinate 133.3, recovered from nonplanar cycle 36. -/
theorem value_535 (h : Assignment) (H : Constraints h) :
    h 133 3 = ((8067963623346575635148407 : ℝ) / 110318384109134813329057925) * (h 1 0) + ((236618073705471893872696 : ℝ) / 959290296601172289817895) * (h 1 1) + ((-9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (h 1 2) + h 1 3 + ((-8067963623346575635148407 : ℝ) / 110318384109134813329057925) * (h 3 0) + ((-236618073705471893872696 : ℝ) / 959290296601172289817895) * (h 5 1) + ((9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (h 9 2) := by
  have r0 := H 281 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 1 - h 93 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 281 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 132 2 - h 93 2) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 132 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 289 1
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 1 - h 95 1) - ((-16173338539794183554831816 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 289 2
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 2 - h 95 2) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 289 3
  change ((-14105804765638148649732716 : ℤ) : ℝ) * (h 133 3 - h 95 3) - ((-8045014505986044391671664 : ℤ) : ℝ) * (h 133 0 - h 95 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 388 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 1 - h 132 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 388 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 133 2 - h 132 2) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 133 0 - h 132 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-1739838777246116866711 : ℝ) / 7480806904102754301528903273166300319063788610) * r0 + ((419665227892120525770754496882452570713457946 : ℝ) / 432299623131228096276307288265471668401608275005229340242158557104155) * r1 + ((497096793498890533346 : ℝ) / 28427650498796742012136468510079045600378285195) * r2 + ((-239808701652640300440431141075687183264833112 : ℝ) / 3285544662406994821310614863470554882748637384714110984735587721790345) * r3 + ((-1 : ℝ) / 14105804765638148649732716) * r4 + ((29577259213183986734087 : ℝ) / 317336220266980326652966325118710158444230643305) * r5 + ((-14268617748332097876205652894003387404257570164 : ℝ) / 36676345262184742659579974528407094905317269256292052431804232163583155) * r6 + ((236618073705471893872696 : ℝ) / 959290296601172289817895) * (value_373 h H) + ((-295087227446103156726980833654734644558545426628 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_372 h H) + ((-114148941986656783009645223152027099234060561312 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_374 h H) + ((-236618073705471893872696 : ℝ) / 959290296601172289817895) * (value_381 h H) + ((295087227446103156726980833654734644558545426628 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_380 h H) + ((114148941986656783009645223152027099234060561312 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_382 h H) + (1 : ℝ) * (value_383 h H)

/-- Coordinate 118.0, recovered from nonplanar cycle 37. -/
theorem value_472 (h : Assignment) (H : Constraints h) :
    h 118 0 = ((1694800603370947737245720625373 : ℝ) / 1037509863370409750592837102046) * (h 1 0) + ((7559445924796185584949116101 : ℝ) / 16734030054361447590207050033) * (h 1 1) + ((-970664285983757617368809643177 : ℝ) / 518754931685204875296418551023) * (h 1 2) + ((-657290740000537986652883523327 : ℝ) / 1037509863370409750592837102046) * (h 3 0) + ((-7559445924796185584949116101 : ℝ) / 16734030054361447590207050033) * (h 5 1) + ((970664285983757617368809643177 : ℝ) / 518754931685204875296418551023) * (h 9 2) := by
  have r0 := H 285 1
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 1 - h 94 1) - ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 285 2
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 2 - h 94 2) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 300 1
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 1 - h 98 1) - ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 300 2
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 2 - h 98 2) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 358 1
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 1 - h 118 1) - ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 358 2
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 2 - h 118 2) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((4806591067387312008068511347 : ℝ) / 211472186869053483379201452993631467362228795182725534768) * r0 + ((-9 : ℝ) / 5706304248537253628260604061253) * r1 + ((-260602116878991520663437885933274294769127798239 : ℝ) / 7130087863766060233105047986742861972288119765772105019534159251459140647872) * r2 + ((487958933686823525133 : ℝ) / 192396226056175396597474575081710741506644590979812) * r3 + ((23691101534453774605767080539388572251738890749 : ℝ) / 94511868658684359783532771160627639762570174610082735025895802844678604628257984) * r4 + ((-796403197436194528964293 : ℝ) / 45785759608856580152395308669341209951726720737281076013884) * r5 + ((11205891025796635388527829095130794675072495324277 : ℝ) / 211715235959935489320941894288274406380753900660684) * (value_377 h H) + ((1246711731698262907024159653267567057260701628037341 : ℝ) / 1164433797779645191265180418585509235094146453633762) * (value_376 h H) + ((-20958146543730895224224334588 : ℝ) / 5706304248537253628260604061253) * (value_378 h H) + ((-11205891025796635388527829095130794675072495324277 : ℝ) / 211715235959935489320941894288274406380753900660684) * (value_393 h H) + ((-82277933918617715758979234682057822166555174403579 : ℝ) / 1164433797779645191265180418585509235094146453633762) * (value_392 h H) + ((20958146543730895224224334588 : ℝ) / 5706304248537253628260604061253) * (value_394 h H)

/-- Coordinate 118.1, recovered from nonplanar cycle 37. -/
theorem value_473 (h : Assignment) (H : Constraints h) :
    h 118 1 = ((-216546615514887264628724421488 : ℝ) / 518754931685204875296418551023) * (h 1 0) + ((7175518310899585132906597738 : ℝ) / 16734030054361447590207050033) * (h 1 1) + ((266286651705594267031295217288 : ℝ) / 518754931685204875296418551023) * (h 1 2) + ((216546615514887264628724421488 : ℝ) / 518754931685204875296418551023) * (h 3 0) + ((9558511743461862457300452295 : ℝ) / 16734030054361447590207050033) * (h 5 1) + ((-266286651705594267031295217288 : ℝ) / 518754931685204875296418551023) * (h 9 2) := by
  have r0 := H 285 1
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 1 - h 94 1) - ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 285 2
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 2 - h 94 2) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 300 1
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 1 - h 98 1) - ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 300 2
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 2 - h 98 2) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 358 1
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 1 - h 118 1) - ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 358 2
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 2 - h 118 2) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((50784208957724455858551476381938255773094952373497 : ℝ) / 246508830043827384270742040778158002319132169295428196350780409867073526274344) * r0 + ((18749280434119798541130 : ℝ) / 1209404160258380312104064103823633202931623776058393) * r1 + ((55073409022243288801919470762198947417281997956845 : ℝ) / 153296889070970295011758531714971532404194574964100257919984423906371523929248) * r2 + ((-9374640217059899270565 : ℝ) / 376047169109797366076882124023343722035714427824178) * r3 + ((-5006673547476662618356315523836267947025636177895 : ℝ) / 2032005176161713735345954579953494254895258754116778803056759761160589999507546656) * r4 + ((15300454460932540042814365 : ℝ) / 89490348326401497570590830580985092178374954168322103118046) * r5 + ((50784208957724455858551476381938255773094952373497 : ℝ) / 105857617979967744660470947144137203190376950330342) * (value_377 h H) + ((-1580719144667027412002914435713724664411022348706595 : ℝ) / 2275938786569306510200125363598949868593104432102353) * (value_376 h H) + ((18727756260181429012404782760 : ℝ) / 518754931685204875296418551023) * (value_378 h H) + ((55073409022243288801919470762198947417281997956845 : ℝ) / 105857617979967744660470947144137203190376950330342) * (value_393 h H) + ((1580719144667027412002914435713724664411022348706595 : ℝ) / 2275938786569306510200125363598949868593104432102353) * (value_392 h H) + ((-18727756260181429012404782760 : ℝ) / 518754931685204875296418551023) * (value_394 h H)

/-- Coordinate 118.2, recovered from nonplanar cycle 37. -/
theorem value_474 (h : Assignment) (H : Constraints h) :
    h 118 2 = ((-1119638926192710425104328795061 : ℝ) / 8300078906963278004742696816368) * (h 1 0) + ((667303820618086860916687133 : ℝ) / 133872240434891580721656400264) * (h 1 1) + ((2505851061725781184189277630845 : ℝ) / 4150039453481639002371348408184) * (h 1 2) + ((1119638926192710425104328795061 : ℝ) / 8300078906963278004742696816368) * (h 3 0) + ((-667303820618086860916687133 : ℝ) / 133872240434891580721656400264) * (h 5 1) + ((1644188391755857818182070777339 : ℝ) / 4150039453481639002371348408184) * (h 9 2) := by
  have r0 := H 285 1
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 1 - h 94 1) - ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 285 2
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 2 - h 94 2) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 300 1
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 1 - h 98 1) - ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 300 2
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 2 - h 98 2) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 358 1
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 1 - h 118 1) - ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 358 2
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 2 - h 118 2) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((559122116882098227437080796108418848029603117461565508539 : ℝ) / 164150558604624713622399485943563117954979870376718029854246475971030750577454035392) * r0 + ((1282777513222044696730396421777 : ℝ) / 6644086703553220303281727510278440196080620495799128806598) * r1 + ((-559122116882098227437080796108418848029603117461565508539 : ℝ) / 102080602828211214075390021947041830056663039728027647215928187858484672946518148864) * r2 + ((3140749222093164234799811217699 : ℝ) / 8263540273112505011413768993589228315741983408542788560432) * r3 + ((50829283352918020676098254191674440729963919769233228049 : ℝ) / 1353114956146320058651851616063805095660425998044701827327233733969851761458741328292608) * r4 + ((-116324045262709786474067082137 : ℝ) / 44625853698765546788534627516384565966282977145269955421532272) * r5 + ((559122116882098227437080796108418848029603117461565508539 : ℝ) / 70490728956351161126400484331210489120742931727575178256) * (value_377 h H) + ((176527394083388202929762878568836410235629937618932179431879 : ℝ) / 16671057398177049606393714544331280677055703353571529657544) * (value_376 h H) + ((2565555026444089393460792843554 : ℝ) / 5706304248537253628260604061253) * (value_378 h H) + ((-559122116882098227437080796108418848029603117461565508539 : ℝ) / 70490728956351161126400484331210489120742931727575178256) * (value_393 h H) + ((-176527394083388202929762878568836410235629937618932179431879 : ℝ) / 16671057398177049606393714544331280677055703353571529657544) * (value_392 h H) + ((3140749222093164234799811217699 : ℝ) / 5706304248537253628260604061253) * (value_394 h H)

/-- Coordinate 118.3, recovered from nonplanar cycle 37. -/
theorem value_475 (h : Assignment) (H : Constraints h) :
    h 118 3 = ((15600554891686645608115909725 : ℝ) / 518754931685204875296418551023) * (h 1 0) + ((3927477000029399601288710976 : ℝ) / 16734030054361447590207050033) * (h 1 1) + ((-14335061367662622798576402618 : ℝ) / 518754931685204875296418551023) * (h 1 2) + h 1 3 + ((-15600554891686645608115909725 : ℝ) / 518754931685204875296418551023) * (h 3 0) + ((-3927477000029399601288710976 : ℝ) / 16734030054361447590207050033) * (h 5 1) + ((14335061367662622798576402618 : ℝ) / 518754931685204875296418551023) * (h 9 2) := by
  have r0 := H 285 1
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 1 - h 94 1) - ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 285 2
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 2 - h 94 2) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 285 3
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 3 - h 94 3) - ((-4277405041606171325713171728 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 300 1
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 1 - h 98 1) - ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 300 2
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 2 - h 98 2) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 358 1
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 1 - h 118 1) - ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 358 2
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 2 - h 118 2) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-100898855732369371618183062265582723236166761377 : ℝ) / 2416753235723797885007274909589784336462080091131648983831180488892877708572) * r0 + ((38540890316538928621476 : ℝ) / 13303445762842183433144705142059965232247861536642323) * r1 + ((1 : ℝ) / 2328682949303432802691592732) * r2 + ((100898855732369371618183062265582723236166761377 : ℝ) / 1502910677166375441291750310931093454943084068275492724705729646140897293424) * r3 + ((-9635222579134732155369 : ℝ) / 2068259430103885513422851682128390471196429353032979) * r4 + ((-9172623248397215601653005660507520294196978307 : ℝ) / 19921619374134448385744652744642100538188811314870380422125095697652843132426928) * r5 + ((5241917943144817801119083 : ℝ) / 164065638598402745546083189398472668993687415975257189049751) * r6 + ((-1715280547450279317509112058514906295014834943409 : ℝ) / 17642936329994624110078491190689533865062825055057) * (value_377 h H) + ((-1083105089284727113785537751855395484004422747177898 : ℝ) / 8345108884087457204067126333196149518174716251041961) * (value_376 h H) + ((38496645374455541931418545552 : ℝ) / 5706304248537253628260604061253) * (value_378 h H) + (1 : ℝ) * (value_379 h H) + ((1715280547450279317509112058514906295014834943409 : ℝ) / 17642936329994624110078491190689533865062825055057) * (value_393 h H) + ((1083105089284727113785537751855395484004422747177898 : ℝ) / 8345108884087457204067126333196149518174716251041961) * (value_392 h H) + ((-38496645374455541931418545552 : ℝ) / 5706304248537253628260604061253) * (value_394 h H)

/-- Coordinate 122.0, recovered from nonplanar cycle 37. -/
theorem value_488 (h : Assignment) (H : Constraints h) :
    h 122 0 = ((471192179276402318567845397545 : ℝ) / 288351569402810574529240132192) * (h 1 0) + ((65177204861032671336070632337 : ℝ) / 144175784701405287264620066096) * (h 1 1) + ((-269928922810662604454177689353 : ℝ) / 144175784701405287264620066096) * (h 1 2) + ((-182840609873591744038605265353 : ℝ) / 288351569402810574529240132192) * (h 3 0) + ((-65177204861032671336070632337 : ℝ) / 144175784701405287264620066096) * (h 5 1) + ((269928922810662604454177689353 : ℝ) / 144175784701405287264620066096) * (h 9 2) := by
  have r0 := H 285 1
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 1 - h 94 1) - ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 285 2
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 2 - h 94 2) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 300 1
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 1 - h 98 1) - ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 300 2
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 2 - h 98 2) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 358 1
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 1 - h 118 1) - ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 358 2
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 2 - h 118 2) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-3873926708180564813199900903699908156028421883 : ℝ) / 227612479724301838154988959890996184374361744008871200350201460151497730688) * r0 + ((-75861974716360676109 : ℝ) / 42992804657219247271001077807036083550877997172136) * r1 + ((3217124040441584482027088281 : ℝ) / 117547483877684612380426260632502816964636145939829468672) * r2 + ((9 : ℝ) / 3171867263430916319821641454112) * r3 + ((-352175155289142255745445536699991650548038353 : ℝ) / 1876240039257635352210821577143265328100420526154825815556963284109560851661312) * r4 + ((-123815171845402441262789 : ℝ) / 6362539820404635391978192326582287825302502704060621567584) * r5 + ((-166578848451764286967595738859096050709222140969 : ℝ) / 4202949410125846342330504727731107345684136314912) * (value_377 h H) + ((5228789527554336187013797930739844573045051179479 : ℝ) / 23116221755692154882817776002521090401262749732016) * (value_376 h H) + ((-814580015570902661067888831 : ℝ) / 198241703964432269988852590882) * (value_378 h H) + ((166578848451764286967595738859096050709222140969 : ℝ) / 4202949410125846342330504727731107345684136314912) * (value_393 h H) + ((17887432228137818695803978071781245828217698552537 : ℝ) / 23116221755692154882817776002521090401262749732016) * (value_392 h H) + ((814580015570902661067888831 : ℝ) / 198241703964432269988852590882) * (value_394 h H)

/-- Coordinate 122.1, recovered from nonplanar cycle 37. -/
theorem value_489 (h : Assignment) (H : Constraints h) :
    h 122 1 = ((-120126910384208960708621950915 : ℝ) / 288351569402810574529240132192) * (h 1 0) + ((61892404734917835710766598981 : ℝ) / 144175784701405287264620066096) * (h 1 1) + ((73776641543489070940041714339 : ℝ) / 144175784701405287264620066096) * (h 1 2) + ((120126910384208960708621950915 : ℝ) / 288351569402810574529240132192) * (h 3 0) + ((82283379966487451553853467115 : ℝ) / 144175784701405287264620066096) * (h 5 1) + ((-73776641543489070940041714339 : ℝ) / 144175784701405287264620066096) * (h 9 2) := by
  have r0 := H 285 1
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 1 - h 94 1) - ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 285 2
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 2 - h 94 2) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 300 1
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 1 - h 98 1) - ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 300 2
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 2 - h 98 2) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 358 1
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 1 - h 118 1) - ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 358 2
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 2 - h 118 2) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1437215905628960793266328964637293386289813708427 : ℝ) / 9787336628144979040664525275312835928097554992381461615058662786514402419584) * r0 + ((2558598100675497637911 : ℝ) / 168062781841857057513913304154777417517068534400168) * r1 + ((395104786356697935580596537584830565627760372355 : ℝ) / 869495516430229350602625274918593447419735213307027334954667603935498043904) * r2 + ((-365514014382213948273 : ℝ) / 14930500588900543991953787307258290274418082803808) * r3 + ((130655991420814617569666269512481216935437609857 : ℝ) / 80678321688078320145065327817160409108318082624657510068949421216711116621436416) * r4 + ((379628762634569543467421 : ℝ) / 2261067870061151420289770826801970053619897655162039069472) * r5 + ((1437215905628960793266328964637293386289813708427 : ℝ) / 4202949410125846342330504727731107345684136314912) * (value_377 h H) + ((-176351472579677363257855977830582230689185624333141 : ℝ) / 90363412317705696360105851646218807932208930770608) * (value_376 h H) + ((638915207513980541655669543 : ℝ) / 18021973087675660908077508262) * (value_378 h H) + ((2765733504496885549064175763093813959394322606485 : ℝ) / 4202949410125846342330504727731107345684136314912) * (value_393 h H) + ((176351472579677363257855977830582230689185624333141 : ℝ) / 90363412317705696360105851646218807932208930770608) * (value_392 h H) + ((-638915207513980541655669543 : ℝ) / 18021973087675660908077508262) * (value_394 h H)

/-- Coordinate 122.2, recovered from nonplanar cycle 37. -/
theorem value_490 (h : Assignment) (H : Constraints h) :
    h 122 2 = ((-516858231467655607560504108645 : ℝ) / 4613625110444969192467842115072) * (h 1 0) + ((42166173460266371485150710067 : ℝ) / 2306812555222484596233921057536) * (h 1 1) + ((1291636951393455771186204299781 : ℝ) / 2306812555222484596233921057536) * (h 1 2) + ((516858231467655607560504108645 : ℝ) / 4613625110444969192467842115072) * (h 3 0) + ((-42166173460266371485150710067 : ℝ) / 2306812555222484596233921057536) * (h 5 1) + ((1015175603829028825047716757755 : ℝ) / 2306812555222484596233921057536) * (h 9 2) := by
  have r0 := H 285 1
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 1 - h 94 1) - ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 285 2
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 2 - h 94 2) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 300 1
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 1 - h 98 1) - ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 300 2
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 2 - h 98 2) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 358 1
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 1 - h 118 1) - ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 358 2
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 2 - h 118 2) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((163212027960856735574917150558898029156774064200447177721 : ℝ) / 91243607146494773644107862402769916729552923993001938506496037455264516265658963968) * r0 + ((1369771478981662774644264840507 : ℝ) / 7386273213805314646923042593990740253837393347797770713984) * r1 + ((-163212027960856735574917150558898029156774064200447177721 : ℝ) / 56741825924388006557464719458728477606617027342433856681510456841043766020440416256) * r2 + ((106005634379367855598669212565 : ℝ) / 270194999721243631739700911923782575836022332951927197184) * r3 + ((14837457087350612324992468232627093559706733109131561611 : ℝ) / 752133227764617124846362066327712216947509512347507763642309161290773767755846731948032) * r4 + ((50732276999320843505343142241 : ℝ) / 24805421913150871848192312483902146134912690542231009951487488) * r5 + ((163212027960856735574917150558898029156774064200447177721 : ℝ) / 39182494625894870793475420210834272321545381979943156224) * (value_377 h H) + ((-220293621139116275099655691756821976044580630501799614275373 : ℝ) / 9266659979024136942656936879862305404045482838256556446976) * (value_376 h H) + ((1369771478981662774644264840507 : ℝ) / 3171867263430916319821641454112) * (value_378 h H) + ((-163212027960856735574917150558898029156774064200447177721 : ℝ) / 39182494625894870793475420210834272321545381979943156224) * (value_393 h H) + ((220293621139116275099655691756821976044580630501799614275373 : ℝ) / 9266659979024136942656936879862305404045482838256556446976) * (value_392 h H) + ((1802095784449253545177376613605 : ℝ) / 3171867263430916319821641454112) * (value_394 h H)

/-- Coordinate 122.3, recovered from nonplanar cycle 37. -/
theorem value_491 (h : Assignment) (H : Constraints h) :
    h 122 3 = ((2173216697008202992100235825 : ℝ) / 72087892350702643632310033048) * (h 1 0) + ((8461058739252797992854231153 : ℝ) / 36043946175351321816155016524) * (h 1 1) + ((-1001121979882274265817398609 : ℝ) / 36043946175351321816155016524) * (h 1 2) + h 1 3 + ((-2173216697008202992100235825 : ℝ) / 72087892350702643632310033048) * (h 3 0) + ((-8461058739252797992854231153 : ℝ) / 36043946175351321816155016524) * (h 5 1) + ((1001121979882274265817398609 : ℝ) / 36043946175351321816155016524) * (h 9 2) := by
  have r0 := H 285 1
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 1 - h 94 1) - ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 285 2
  change ((2328682949303432802691592732 : ℤ) : ℝ) * (h 118 2 - h 94 2) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 118 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 300 1
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 1 - h 98 1) - ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 300 2
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 2 - h 98 2) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 300 3
  change ((1448142249903826953009580144 : ℤ) : ℝ) * (h 122 3 - h 98 3) - ((-2357449182116273216713998912 : ℤ) : ℝ) * (h 122 0 - h 98 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 358 1
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 1 - h 118 1) - ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 358 2
  change ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 122 2 - h 118 2) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 122 0 - h 118 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((9305052835343226004689576185410060572173136971 : ℝ) / 335839982338308104336527828074460056356288651699363878948091370125494200672) * r0 + ((1327589237384921574369 : ℝ) / 462172650065106908163261586425637898171938469600462) * r1 + ((-9305052835343226004689576185410060572173136971 : ℝ) / 208849413260202147938865874857897445703759928686491859866562316631565706624) * r2 + ((-1327589237384921574369 : ℝ) / 287412136336335471845110405664722087782548093973304) * r3 + ((1 : ℝ) / 1448142249903826953009580144) * r4 + ((845913894122111454971779653219096415652103361 : ℝ) / 2768373783414452161840476934902563057638365580257855737660029159396950080147328) * r5 + ((722257715109152333552083 : ℝ) / 22799101023116610154588522503586531374000634689550560617176) * r6 + ((158185898200834842079722795151971029726943328507 : ℝ) / 2451720489240077033026127757843145951649079517032) * (value_377 h H) + ((-213509658345541730108441594570236961217478825925591 : ℝ) / 579831895705278218310679214729904017565007305778068) * (value_376 h H) + ((663032582470201842200812194 : ℝ) / 99120851982216134994426295441) * (value_378 h H) + ((-158185898200834842079722795151971029726943328507 : ℝ) / 2451720489240077033026127757843145951649079517032) * (value_393 h H) + ((213509658345541730108441594570236961217478825925591 : ℝ) / 579831895705278218310679214729904017565007305778068) * (value_392 h H) + ((-663032582470201842200812194 : ℝ) / 99120851982216134994426295441) * (value_394 h H) + (1 : ℝ) * (value_395 h H)

/-- Coordinate 138.0, recovered from nonplanar cycle 38. -/
theorem value_552 (h : Assignment) (H : Constraints h) :
    h 138 0 = ((139000283339831846805438863309 : ℝ) / 80657737443519335659690486109) * (h 1 0) + ((3126756156422237613951041596 : ℝ) / 6204441341809179666130037393) * (h 1 1) + ((-164826048525223839798807150750 : ℝ) / 80657737443519335659690486109) * (h 1 2) + ((-58342545896312511145748377200 : ℝ) / 80657737443519335659690486109) * (h 3 0) + ((-3126756156422237613951041596 : ℝ) / 6204441341809179666130037393) * (h 5 1) + ((164826048525223839798807150750 : ℝ) / 80657737443519335659690486109) * (h 9 2) := by
  have r0 := H 286 1
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 1 - h 94 1) - ((-62662212923063117229264058 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 286 2
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 2 - h 94 2) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 301 1
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 1 - h 98 1) - ((2145573734180397378650012 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 301 2
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 2 - h 98 2) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 398 1
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 1 - h 138 1) - ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 398 2
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 2 - h 138 2) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((20798443761100748397955071077 : ℝ) / 8477992271283199789246697488648632107580679985438856060) * r0 + ((-108 : ℝ) / 887235111878712692256595347199) * r1 + ((-16737663305534602825380752413048590659463469855651 : ℝ) / 7545123113923015217094771174359078223744264865145066126322930838588742393880) * r2 + ((43456800368367250819002 : ℝ) / 394804449916473061527312181348167524885444879225251) * r3 + ((16737663305534602825380752413048590659463469855651 : ℝ) / 969815623851602691921306842733861484227754792685875805615207157205323569935859520) * r4 + ((-11821054455758269394080007 : ℝ) / 13803949310911227264420364218480037099067635687320395265564) * r5 + ((16737663305534602825380752413048590659463469855651 : ℝ) / 11316981589909482471539590768400299687482136139540) * (value_377 h H) + ((141647942138152594705359580999092964383120712661813 : ℝ) / 220681141003234908195022019983805843905901654721030) * (value_376 h H) + ((-65110367942316547822592678556 : ℝ) / 887235111878712692256595347199) * (value_378 h H) + ((-16737663305534602825380752413048590659463469855651 : ℝ) / 11316981589909482471539590768400299687482136139540) * (value_393 h H) + ((79033198865082313489662438984712879522780942059217 : ℝ) / 220681141003234908195022019983805843905901654721030) * (value_392 h H) + ((65110367942316547822592678556 : ℝ) / 887235111878712692256595347199) * (value_394 h H)

/-- Coordinate 138.1, recovered from nonplanar cycle 38. -/
theorem value_553 (h : Assignment) (H : Constraints h) :
    h 138 1 = ((-30710762120847743456314792043 : ℝ) / 80657737443519335659690486109) * (h 1 0) + ((2792769390001120810127813548 : ℝ) / 6204441341809179666130037393) * (h 1 1) + ((35724170004512650198172474382 : ℝ) / 80657737443519335659690486109) * (h 1 2) + ((30710762120847743456314792043 : ℝ) / 80657737443519335659690486109) * (h 3 0) + ((3411671951808058856002223845 : ℝ) / 6204441341809179666130037393) * (h 5 1) + ((-35724170004512650198172474382 : ℝ) / 80657737443519335659690486109) * (h 9 2) := by
  have r0 := H 286 1
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 1 - h 94 1) - ((-62662212923063117229264058 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 286 2
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 2 - h 94 2) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 301 1
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 1 - h 98 1) - ((2145573734180397378650012 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 301 2
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 2 - h 98 2) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 398 1
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 1 - h 138 1) - ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 398 2
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 2 - h 138 2) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1305993054546028114482003644609955014672541255479 : ℝ) / 930369741559885005148168654433269179395804687678347254462503836874820683970) * r0 + ((821248125659264916216 : ℝ) / 64909762856429630837891366615665451168395513967467) * r1 + ((237231707714355858909758732899176760893204581731 : ℝ) / 1028880424625865711422014251048965212328763390701599926316763296171192144620) * r2 + ((-410624062829632458108 : ℝ) / 35891313628770278320664743758924320444131352656841) * r3 + ((-237231707714355858909758732899176760893204581731 : ℝ) / 132247585070673094352905478554617475121966562638983064402073703255271395900344480) * r4 + ((167546023858457532698567 : ℝ) / 1882356724215167354239140575247277786236495775543690263486) * r5 + ((1305993054546028114482003644609955014672541255479 : ℝ) / 1543224762260383973391762377509131775565745837210) * (value_377 h H) + ((1120179106882381970990518927857763347969031554577 : ℝ) / 30092882864077487481139366361428069623532043825595) * (value_376 h H) + ((615228999608256060069138024 : ℝ) / 80657737443519335659690486109) * (value_378 h H) + ((237231707714355858909758732899176760893204581731 : ℝ) / 1543224762260383973391762377509131775565745837210) * (value_393 h H) + ((-1120179106882381970990518927857763347969031554577 : ℝ) / 30092882864077487481139366361428069623532043825595) * (value_392 h H) + ((-615228999608256060069138024 : ℝ) / 80657737443519335659690486109) * (value_394 h H)

/-- Coordinate 138.2, recovered from nonplanar cycle 38. -/
theorem value_554 (h : Assignment) (H : Constraints h) :
    h 138 2 = ((-138794665687244804416753760493 : ℝ) / 645261899548154685277523888872) * (h 1 0) + ((-1033537310793131602881987641 : ℝ) / 24817765367236718664520149572) * (h 1 1) + ((244477053615011092885956197129 : ℝ) / 322630949774077342638761944436) * (h 1 2) + ((138794665687244804416753760493 : ℝ) / 645261899548154685277523888872) * (h 3 0) + ((1033537310793131602881987641 : ℝ) / 24817765367236718664520149572) * (h 5 1) + ((78153896159066249752805747307 : ℝ) / 322630949774077342638761944436) * (h 9 2) := by
  have r0 := H 286 1
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 1 - h 94 1) - ((-62662212923063117229264058 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 286 2
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 2 - h 94 2) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 301 1
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 1 - h 98 1) - ((2145573734180397378650012 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 301 2
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 2 - h 98 2) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 398 1
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 1 - h 138 1) - ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 398 2
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 2 - h 138 2) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((83405037377805661034005518349144588093441252798931217631 : ℝ) / 5111159224031158414392422062498888825078220671432908814979094853585486144036413420) * r0 + ((454138090761673090274427569275 : ℝ) / 534890783201531209378938105446023004651247116318816870043) * r1 + ((-83405037377805661034005518349144588093441252798931217631 : ℝ) / 5652345984441173696719159782788185501457554836809909692807434085489531888208869320) * r2 + ((72182836852839933663694629654 : ℝ) / 98587803601992237613169706740994957141719097125975102963) * r3 + ((83405037377805661034005518349144588093441252798931217631 : ℝ) / 726526706636565789023235886858802258432895997637904315142770674541638893858179864953280) * r4 + ((-4010157602935551870205257203 : ℝ) / 704001414856472590485438575142481892052449420053340158543764) * r5 + ((83405037377805661034005518349144588093441252798931217631 : ℝ) / 8477992271283199789246697488648632107580679985438856060) * (value_377 h H) + ((-393828384828965618762076641804617040396907681559203699877 : ℝ) / 165320849290022395890310601028648326097823259716057693170) * (value_376 h H) + ((454138090761673090274427569275 : ℝ) / 887235111878712692256595347199) * (value_378 h H) + ((-83405037377805661034005518349144588093441252798931217631 : ℝ) / 8477992271283199789246697488648632107580679985438856060) * (value_393 h H) + ((393828384828965618762076641804617040396907681559203699877 : ℝ) / 165320849290022395890310601028648326097823259716057693170) * (value_392 h H) + ((433097021117039601982167777924 : ℝ) / 887235111878712692256595347199) * (value_394 h H)

/-- Coordinate 138.3, recovered from nonplanar cycle 38. -/
theorem value_555 (h : Assignment) (H : Constraints h) :
    h 138 3 = ((5992215956008704915417834675 : ℝ) / 80657737443519335659690486109) * (h 1 0) + ((1615689746581315952869987896 : ℝ) / 6204441341809179666130037393) * (h 1 1) + ((-9074791502589585430862011494 : ℝ) / 80657737443519335659690486109) * (h 1 2) + h 1 3 + ((-5992215956008704915417834675 : ℝ) / 80657737443519335659690486109) * (h 3 0) + ((-1615689746581315952869987896 : ℝ) / 6204441341809179666130037393) * (h 5 1) + ((9074791502589585430862011494 : ℝ) / 80657737443519335659690486109) * (h 9 2) := by
  have r0 := H 286 1
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 1 - h 94 1) - ((-62662212923063117229264058 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 286 2
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 2 - h 94 2) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 286 3
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 3 - h 94 3) - ((226560544008554793078211948 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 301 1
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 1 - h 98 1) - ((2145573734180397378650012 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 301 2
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 2 - h 98 2) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 398 1
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 1 - h 138 1) - ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 398 2
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 2 - h 138 2) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((277501320518680031651210563101588229218081615719 : ℝ) / 301001975210551031077348682316645910980995634248877052914339476635971397755) * r0 + ((-32662214559546249297456 : ℝ) / 714007391420725939216805032772319962852350653642137) * r1 + ((1 : ℝ) / 602873777243671739098080357) * r2 + ((-277501320518680031651210563101588229218081615719 : ℝ) / 332873078555427141930651669457018156929894038168164682043658713467150399730) * r3 + ((16331107279773124648728 : ℝ) / 394804449916473061527312181348167524885444879225251) * r4 + ((277501320518680031651210563101588229218081615719 : ℝ) / 42785983405217765820057654826493889010048005559670991424200315759058392791287920) * r5 + ((-3331772706008158721738411 : ℝ) / 10352961983183420448315273163860027824300726765490296449173) * r6 + ((4717522448817560538070579572726999896707387467223 : ℝ) / 8487736192432111853654693076300224765611602104655) * (value_377 h H) + ((-44551127961165518546540307993062669088317934915482 : ℝ) / 331021711504852362292533029975708765858852482081545) * (value_376 h H) + ((-24468538752923917652446890384 : ℝ) / 887235111878712692256595347199) * (value_378 h H) + (1 : ℝ) * (value_379 h H) + ((-4717522448817560538070579572726999896707387467223 : ℝ) / 8487736192432111853654693076300224765611602104655) * (value_393 h H) + ((44551127961165518546540307993062669088317934915482 : ℝ) / 331021711504852362292533029975708765858852482081545) * (value_392 h H) + ((24468538752923917652446890384 : ℝ) / 887235111878712692256595347199) * (value_394 h H)

/-- Coordinate 142.0, recovered from nonplanar cycle 38. -/
theorem value_568 (h : Assignment) (H : Constraints h) :
    h 142 0 = ((69571840443901781045647078438 : ℝ) / 40125038554912127264482075795) * (h 1 0) + ((314878525056279147613324906 : ℝ) / 617308285460186573299724243) * (h 1 1) + ((-82808359645249467612955649736 : ℝ) / 40125038554912127264482075795) * (h 1 2) + ((-29446801888989653781165002643 : ℝ) / 40125038554912127264482075795) * (h 3 0) + ((-314878525056279147613324906 : ℝ) / 617308285460186573299724243) * (h 5 1) + ((82808359645249467612955649736 : ℝ) / 40125038554912127264482075795) * (h 9 2) := by
  have r0 := H 286 1
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 1 - h 94 1) - ((-62662212923063117229264058 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 286 2
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 2 - h 94 2) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 301 1
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 1 - h 98 1) - ((2145573734180397378650012 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 301 2
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 2 - h 98 2) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 398 1
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 1 - h 138 1) - ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 398 2
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 2 - h 138 2) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((8831796800468169136271684327905010020524144680749 : ℝ) / 8824696517259967232543017421220790257825328933540536257629352161191250318140) * r0 + ((-48058152816666181055292 : ℝ) / 355199327644303892767637850190396534747623901718935) * r1 + ((-19847497220487847892195446801 : ℝ) / 21931371287929104607090408747517268752646213293777359560) * r2 + ((54 : ℝ) / 441375424104033399909302833745) * r3 + ((8831796800468169136271684327905010020524144680749 : ℝ) / 1254388176288395607595311112269473359169615279263269659825117634508428867019565760) * r4 + ((-6536353765963051236307261 : ℝ) / 6867090695399477699726629472709506740722958853812580246820) * r5 + ((8831796800468169136271684327905010020524144680749 : ℝ) / 14637718292552586774343885946077609597582166523020) * (value_377 h H) + ((13289951495936405795540667827846574975326637691847 : ℝ) / 21956577438828880161515828919116414396373249784530) * (value_376 h H) + ((-36002236542924486209580393588 : ℝ) / 441375424104033399909302833745) * (value_378 h H) + ((-8831796800468169136271684327905010020524144680749 : ℝ) / 14637718292552586774343885946077609597582166523020) * (value_393 h H) + ((8666625942892474365975161091269839421046612092683 : ℝ) / 21956577438828880161515828919116414396373249784530) * (value_392 h H) + ((36002236542924486209580393588 : ℝ) / 441375424104033399909302833745) * (value_394 h H)

/-- Coordinate 142.1, recovered from nonplanar cycle 38. -/
theorem value_569 (h : Assignment) (H : Constraints h) :
    h 142 1 = ((-14869921899585899311348736212 : ℝ) / 40125038554912127264482075795) * (h 1 0) + ((281513443010244406222779958 : ℝ) / 617308285460186573299724243) * (h 1 1) + ((16988954485877604534684310704 : ℝ) / 40125038554912127264482075795) * (h 1 2) + ((14869921899585899311348736212 : ℝ) / 40125038554912127264482075795) * (h 3 0) + ((335794842449942167076944285 : ℝ) / 617308285460186573299724243) * (h 5 1) + ((-16988954485877604534684310704 : ℝ) / 40125038554912127264482075795) * (h 9 2) := by
  have r0 := H 286 1
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 1 - h 94 1) - ((-62662212923063117229264058 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 286 2
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 2 - h 94 2) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 301 1
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 1 - h 98 1) - ((2145573734180397378650012 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 301 2
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 2 - h 98 2) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 398 1
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 1 - h 138 1) - ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 398 2
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 2 - h 138 2) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((3875746513861291815278596306243072245532474421 : ℝ) / 1203367706899086440801320557439198671521635763664618580585820749253352316110) * r0 + ((-14059896111735236712 : ℝ) / 32290847967663990251603440926399684977056718338085) * r1 + ((1992176747925127813777069487249794600152035687809 : ℝ) / 1330784334386795340214891137379444709392280435528679897102316719152245107060) * r2 + ((7029948055867618356 : ℝ) / 17854955876357308889409844400744314473730850276455) * r3 + ((3875746513861291815278596306243072245532474421 : ℝ) / 171052933130235764672087878945837276250402083535900408157970586523876663684486240) * r4 + ((-2868414083128873500869 : ℝ) / 936421458463565140871813109914932737371312570974442760930) * r5 + ((3875746513861291815278596306243072245532474421 : ℝ) / 1996052494438989105592348083556037672397568162230) * (value_377 h H) + ((5832163527248582748141590948067132266801341663 : ℝ) / 2994078741658483658388522125334056508596352243345) * (value_376 h H) + ((-10532816513249223495190968 : ℝ) / 40125038554912127264482075795) * (value_378 h H) + ((1992176747925127813777069487249794600152035687809 : ℝ) / 1996052494438989105592348083556037672397568162230) * (value_393 h H) + ((-5832163527248582748141590948067132266801341663 : ℝ) / 2994078741658483658388522125334056508596352243345) * (value_392 h H) + ((10532816513249223495190968 : ℝ) / 40125038554912127264482075795) * (value_394 h H)

/-- Coordinate 142.2, recovered from nonplanar cycle 38. -/
theorem value_570 (h : Assignment) (H : Constraints h) :
    h 142 2 = ((-39605003468736493200344541993 : ℝ) / 642000616878594036231713212720) * (h 1 0) + ((234802336003959332237846063 : ℝ) / 4938466283681492586397793944) * (h 1 1) + ((148719343766200154698074751953 : ℝ) / 321000308439297018115856606360) * (h 1 2) + ((39605003468736493200344541993 : ℝ) / 642000616878594036231713212720) * (h 3 0) + ((-234802336003959332237846063 : ℝ) / 4938466283681492586397793944) * (h 5 1) + ((172280964673096863417781854407 : ℝ) / 321000308439297018115856606360) * (h 9 2) := by
  have r0 := H 286 1
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 1 - h 94 1) - ((-62662212923063117229264058 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 286 2
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 2 - h 94 2) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 301 1
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 1 - h 98 1) - ((2145573734180397378650012 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 301 2
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 2 - h 98 2) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 398 1
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 1 - h 138 1) - ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 398 2
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 2 - h 138 2) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-63718255321767336390046129736069442460104761696085335627 : ℝ) / 13221848648487229185240087055831843185914018183887247583008390497365304144162162920) * r0 + ((57787064184993535298856096486 : ℝ) / 88697889704042057974685150484594489881433407369940415655) * r1 + ((63718255321767336390046129736069442460104761696085335627 : ℝ) / 14621822533680112290807568865891064175524879073475622698384875855145241626448046320) * r2 + ((268014231549052794012734544287 : ℝ) / 294268563385685636530279231339642290011797619795570889390) * r3 + ((-63718255321767336390046129736069442460104761696085335627 : ℝ) / 1879422207993024794156687542668882005629932841384013139383457599196019786020340947761280) * r4 + ((3210392454721863072158672027 : ℝ) / 700443250930746725372116206216369687553741803088883185175640) * r5 + ((-63718255321767336390046129736069442460104761696085335627 : ℝ) / 21931371287929104607090408747517268752646213293777359560) * (value_377 h H) + ((-95882247040272773608590228623848218085380745020171307681 : ℝ) / 32897056931893656910635613121275903128969319940666039340) * (value_376 h H) + ((173361192554980605896568289458 : ℝ) / 441375424104033399909302833745) * (value_378 h H) + ((63718255321767336390046129736069442460104761696085335627 : ℝ) / 21931371287929104607090408747517268752646213293777359560) * (value_393 h H) + ((95882247040272773608590228623848218085380745020171307681 : ℝ) / 32897056931893656910635613121275903128969319940666039340) * (value_392 h H) + ((268014231549052794012734544287 : ℝ) / 441375424104033399909302833745) * (value_394 h H)

/-- Coordinate 142.3, recovered from nonplanar cycle 38. -/
theorem value_571 (h : Assignment) (H : Constraints h) :
    h 142 3 = ((3203773603528562030662615047 : ℝ) / 40125038554912127264482075795) * (h 1 0) + ((162745290001629589379931036 : ℝ) / 617308285460186573299724243) * (h 1 1) + ((-4942135071977515637471305614 : ℝ) / 40125038554912127264482075795) * (h 1 2) + h 1 3 + ((-3203773603528562030662615047 : ℝ) / 40125038554912127264482075795) * (h 3 0) + ((-162745290001629589379931036 : ℝ) / 617308285460186573299724243) * (h 5 1) + ((4942135071977515637471305614 : ℝ) / 40125038554912127264482075795) * (h 9 2) := by
  have r0 := H 286 1
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 1 - h 94 1) - ((-62662212923063117229264058 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 286 2
  change ((602873777243671739098080357 : ℤ) : ℝ) * (h 138 2 - h 94 2) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 138 0 - h 94 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 301 1
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 1 - h 98 1) - ((2145573734180397378650012 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 301 2
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 2 - h 98 2) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 301 3
  change ((666708084128231226103340622 : ℤ) : ℝ) * (h 142 3 - h 98 3) - ((260646954530371667362044088 : ℤ) : ℝ) * (h 142 0 - h 98 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 398 1
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 1 - h 138 1) - ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 398 2
  change ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 142 2 - h 138 2) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 142 0 - h 138 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((152327510381040203003334270432158687846259568391 : ℝ) / 389324846349704436729839003877387805492293923538553070189530242405496337565) * r0 + ((-18788149521837829878768 : ℝ) / 355199327644303892767637850190396534747623901718935) * r1 + ((-152327510381040203003334270432158687846259568391 : ℝ) / 430547872889845551245994191505114464803384846788690554944867173843373416990) * r2 + ((9394074760918914939384 : ℝ) / 196404514639930397783508288408187459211039353041005) * r3 + ((1 : ℝ) / 666708084128231226103340622) * r4 + ((152327510381040203003334270432158687846259568391 : ℝ) / 55340654836252747393910784364829707022188909379261896756990483875371861780274960) * r5 + ((-1916521724488026965897383 : ℝ) / 5150318021549608274794972104532130055542219140359435185115) * r6 + ((2589567676477683451056682597346697693386412662647 : ℝ) / 10978288719414440080757914459558207198186624892265) * (value_377 h H) + ((7793482932942664081237480925791398689277514193482 : ℝ) / 32934866158243320242273743378674621594559874676795) * (value_376 h H) + ((-14074935544640070037550380752 : ℝ) / 441375424104033399909302833745) * (value_378 h H) + ((-2589567676477683451056682597346697693386412662647 : ℝ) / 10978288719414440080757914459558207198186624892265) * (value_393 h H) + ((-7793482932942664081237480925791398689277514193482 : ℝ) / 32934866158243320242273743378674621594559874676795) * (value_392 h H) + ((14074935544640070037550380752 : ℝ) / 441375424104033399909302833745) * (value_394 h H) + (1 : ℝ) * (value_395 h H)

/-- Coordinate 134.0, recovered from nonplanar cycle 39. -/
theorem value_536 (h : Assignment) (H : Constraints h) :
    h 134 0 = ((9018608418867289852888476 : ℝ) / 5742396841739446764092893) * (h 1 0) + ((109175811564558021538052 : ℝ) / 249669427901715076699691) * (h 1 1) + ((-10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (h 1 2) + ((-3276211577127843088795583 : ℝ) / 5742396841739446764092893) * (h 3 0) + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (h 5 1) + ((10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (h 9 2) := by
  have r0 := H 297 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 1 - h 97 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 297 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 2 - h 97 2) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 303 1
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 1 - h 99 1) - ((-8086669269897091777415908 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 303 2
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 2 - h 99 2) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 391 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 1 - h 134 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 391 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 2 - h 134 2) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-7 : ℝ) / 16977521097316625215578988) * r0 + ((-811393683605415051318460 : ℝ) / 517873774355332710498418715050165112570420769167) * r1 + ((7798272254611287252718 : ℝ) / 125778150211791524602780748119317401946662492527) * r2 + ((25309875401707829978298500079509713588474297120 : ℝ) / 107426858151477461775673544872359003542407954188254079302685446024764229) * r3 + ((27293952891139505384513 : ℝ) / 165182849961609417340162214604631186978140158538) * r4 + ((107566970457258277407768625337916282751015762760 : ℝ) / 171314258792759583379977276609743047547526507421419529584071654346388353) * r5 + ((109175811564558021538052 : ℝ) / 249669427901715076699691) * (value_389 h H) + ((-1711034131545649310462252613069204540838157091977 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_388 h H) + ((860535763658066219262149002703330262008126102080 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_390 h H) + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (value_397 h H) + ((2228907905900982020960671328119369653408577861144 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_396 h H) + ((-860535763658066219262149002703330262008126102080 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_398 h H)

/-- Coordinate 134.1, recovered from nonplanar cycle 39. -/
theorem value_537 (h : Assignment) (H : Constraints h) :
    h 134 1 = ((-255174997716761229511173 : ℝ) / 28711984208697233820464465) * (h 1 0) + ((131972807462839763526612 : ℝ) / 249669427901715076699691) * (h 1 1) + ((291719362271465515182138 : ℝ) / 28711984208697233820464465) * (h 1 2) + ((255174997716761229511173 : ℝ) / 28711984208697233820464465) * (h 3 0) + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (h 5 1) + ((-291719362271465515182138 : ℝ) / 28711984208697233820464465) * (h 9 2) := by
  have r0 := H 297 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 1 - h 97 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 297 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 2 - h 97 2) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 303 1
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 1 - h 99 1) - ((-8086669269897091777415908 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 303 2
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 2 - h 99 2) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 391 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 1 - h 134 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 391 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 2 - h 134 2) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-32993201865709940881653 : ℝ) / 66197665862641007250553477607808738034123344692) * r0 + ((148289277027651276764431664770561842927216985 : ℝ) / 87793927955348205434756651099640296267020652532952532863290953724911) * r1 + ((-16813802919839330453297 : ℝ) / 251556300423583049205561496238634803893324985054) * r2 + ((-27285226973087834924655426317783379098607925240 : ℝ) / 107426858151477461775673544872359003542407954188254079302685446024764229) * r3 + ((-117696620438875313173079 : ℝ) / 660731399846437669360648858418524747912560634152) * r4 + ((-115962214635623298429785561850579361169083682270 : ℝ) / 171314258792759583379977276609743047547526507421419529584071654346388353) * r5 + ((131972807462839763526612 : ℝ) / 249669427901715076699691) * (value_389 h H) + ((2402866752576526259373679149025436733323975305738 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_388 h H) + ((-927697717084986387438284494804634889352669458160 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_390 h H) + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (value_397 h H) + ((-2402866752576526259373679149025436733323975305738 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_396 h H) + ((927697717084986387438284494804634889352669458160 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_398 h H)

/-- Coordinate 134.2, recovered from nonplanar cycle 39. -/
theorem value_538 (h : Assignment) (H : Constraints h) :
    h 134 2 = ((214929259610135377181499163 : ℝ) / 58281042572877967157957720) * (h 1 0) + ((251753206123348448905855 : ℝ) / 253395837273382465904164) * (h 1 1) + ((-7226762153765448547821267 : ℝ) / 1714148310966999034057580) * (h 1 2) + ((-214929259610135377181499163 : ℝ) / 58281042572877967157957720) * (h 3 0) + ((-251753206123348448905855 : ℝ) / 253395837273382465904164) * (h 5 1) + ((8940910464732447581878847 : ℝ) / 1714148310966999034057580) * (h 9 2) := by
  have r0 := H 297 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 1 - h 97 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 297 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 2 - h 97 2) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 303 1
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 1 - h 99 1) - ((-8086669269897091777415908 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 303 2
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 2 - h 99 2) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 391 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 1 - h 134 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 391 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 2 - h 134 2) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-251753206123348448905855 : ℝ) / 268742762905050059285829043422745921571366414272) * r0 + ((-1604827183273609902100805769552786138329276487 : ℝ) / 356417140356040475794832971628390456487009216253180431922614021092176) * r1 + ((35964743731906921272265 : ℝ) / 255310872071696229044450473794435323354419387816) * r2 + ((14590782948278359318200917730079689004440255950 : ℝ) / 27257561023509206719200750191494075525685600316422676837994814662999879) * r3 + ((251753206123348448905855 : ℝ) / 670593062530712858455583916006860938179912285408) * r4 + ((7295391474139179659100458865039844502220127975 : ℝ) / 5113858471425659205372456018201285001418701714072224763703631473026518) * r5 + ((251753206123348448905855 : ℝ) / 253395837273382465904164) * (value_389 h H) + ((-2569867369991748443419461387910468335595507969405 : ℝ) / 262801616837034509805167706144859907871556808234) * (value_388 h H) + ((36911025215293027748318532699714081181573359201 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_390 h H) + ((-251753206123348448905855 : ℝ) / 253395837273382465904164) * (value_397 h H) + ((2569867369991748443419461387910468335595507969405 : ℝ) / 262801616837034509805167706144859907871556808234) * (value_396 h H) + ((-29181565896556718636401835460159378008880511900 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_398 h H)

/-- Coordinate 134.3, recovered from nonplanar cycle 39. -/
theorem value_539 (h : Assignment) (H : Constraints h) :
    h 134 3 = ((36813195939601494408633 : ℝ) / 428537077741749758514395) * (h 1 0) + ((928717562452291111080 : ℝ) / 3726409371667389204473) * (h 1 1) + ((-42085322381761110668898 : ℝ) / 428537077741749758514395) * (h 1 2) + h 1 3 + ((-36813195939601494408633 : ℝ) / 428537077741749758514395) * (h 3 0) + ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (h 5 1) + ((42085322381761110668898 : ℝ) / 428537077741749758514395) * (h 9 2) := by
  have r0 := H 297 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 1 - h 97 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 297 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 2 - h 97 2) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 297 3
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 3 - h 97 3) - ((-604462459218948328868640 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 303 1
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 1 - h 99 1) - ((-8086669269897091777415908 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 303 2
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 2 - h 99 2) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 391 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 1 - h 134 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 391 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 2 - h 134 2) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-6828805606266846405 : ℝ) / 29059554812397281497170095525815951727007614) * r0 + ((-26912698715257378112134721809282196154090600 : ℝ) / 30138214074224010820886611571518310658827985197879227699338685607059) * r1 + ((-1 : ℝ) / 1060565026627135066369648) * r2 + ((3902174632152483660 : ℝ) / 110428577885681759967322869288250572385129493) * r3 + ((215301589722059024897077774474257569232724800 : ℝ) / 1603385942559365101129455893617298560334447077436628049293812627235287) * r4 + ((38696565102178796295 : ℝ) / 410902611844799545622294066180674594472985469) * r5 + ((305010585439583618604193513838531556413026800 : ℝ) / 852309745237609867562076003033547500236450285678704127283938578837753) * r6 + ((928717562452291111080 : ℝ) / 3726409371667389204473) * (value_389 h H) + ((-18960481150854092975152388164777159697683403760 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_388 h H) + ((7320254050550006846500644332124757353912643200 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_390 h H) + (1 : ℝ) * (value_391 h H) + ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (value_397 h H) + ((18960481150854092975152388164777159697683403760 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_396 h H) + ((-7320254050550006846500644332124757353912643200 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_398 h H)

/-- Coordinate 135.0, recovered from nonplanar cycle 39. -/
theorem value_540 (h : Assignment) (H : Constraints h) :
    h 135 0 = ((170624048649954562499929323 : ℝ) / 110318384109134813329057925) * (h 1 0) + ((414876610754063195580374 : ℝ) / 959290296601172289817895) * (h 1 1) + ((-195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (h 1 2) + ((-60305664540819749170871398 : ℝ) / 110318384109134813329057925) * (h 3 0) + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (h 5 1) + ((195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (h 9 2) := by
  have r0 := H 297 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 1 - h 97 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 297 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 2 - h 97 2) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 303 1
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 1 - h 99 1) - ((-8086669269897091777415908 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 303 2
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 2 - h 99 2) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 391 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 1 - h 134 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 391 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 2 - h 134 2) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-207438305377031597790187 : ℝ) / 508694869478987292503965422575308421696337625480) * r0 + ((-1471648253006534054395790270040846241199990873 : ℝ) / 674650988676290329097593134385135199274728445653012829878033148617590) * r1 + ((1 : ℝ) / 16307935042219928926904215) * r2 + ((28377560264614094921516 : ℝ) / 86512879603216544560540780902143301688406903005) * r3 + ((207438305377031597790187 : ℝ) / 1269344881067921306611865300474840633776922573220) * r4 + ((25018020301111078924728434590694386100399844841 : ℝ) / 28618730237308985933925678646748279589971759509914306451279915421139795) * r5 + ((414876610754063195580374 : ℝ) / 959290296601172289817895) * (value_389 h H) + ((-414398489997543223485972233841662647776360685843 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_388 h H) + ((200144162408888631397827476725555088803198758728 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_390 h H) + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (value_397 h H) + ((500911369600759768046513014743805949464767588848 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_396 h H) + ((-200144162408888631397827476725555088803198758728 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_398 h H)

/-- Coordinate 135.1, recovered from nonplanar cycle 39. -/
theorem value_541 (h : Assignment) (H : Constraints h) :
    h 135 1 = ((-823533213543044848835519 : ℝ) / 4796451483005861449089475) * (h 1 0) + ((20682018593087191246588 : ℝ) / 41708273765268360426865) * (h 1 1) + ((941473835656930474758414 : ℝ) / 4796451483005861449089475) * (h 1 2) + ((823533213543044848835519 : ℝ) / 4796451483005861449089475) * (h 3 0) + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (h 5 1) + ((-941473835656930474758414 : ℝ) / 4796451483005861449089475) * (h 9 2) := by
  have r0 := H 297 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 1 - h 97 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 297 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 2 - h 97 2) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 303 1
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 1 - h 99 1) - ((-8086669269897091777415908 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 303 2
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 2 - h 99 2) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 391 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 1 - h 134 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 391 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 2 - h 134 2) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-5170504648271797811647 : ℝ) / 11058584119108419402260117882071922210789948380) * r0 + ((-502487353612329611293885775537628715807181 : ℝ) / 200908573161492057503750188917550684715523658622100306693875267605) * r1 + ((-3003750738883024168611 : ℝ) / 42023483346047357757071301275769023930993986810) * r2 + ((92457673064668648478074982698923683708521304 : ℝ) / 245836782714772627093511813715427436618753341189196803863786773285095) * r3 + ((70828830798243805639 : ℝ) / 378006218304919984101210631469577317980024590) * r4 + ((392945110524841756031818676470425655761215542 : ℝ) / 392037400511081999094872310229428487533859719313894608921642677001915) * r5 + ((20682018593087191246588 : ℝ) / 41708273765268360426865) * (value_389 h H) + ((-6508742837904741242696228675124354443769036466 : ℝ) / 1185107939770089651514257272632100023128861685) * (value_388 h H) + ((3143560884198734048254549411763405246089724336 : ℝ) / 1185107939770089651514257272632100023128861685) * (value_390 h H) + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (value_397 h H) + ((6508742837904741242696228675124354443769036466 : ℝ) / 1185107939770089651514257272632100023128861685) * (value_396 h H) + ((-3143560884198734048254549411763405246089724336 : ℝ) / 1185107939770089651514257272632100023128861685) * (value_398 h H)

/-- Coordinate 135.2, recovered from nonplanar cycle 39. -/
theorem value_542 (h : Assignment) (H : Constraints h) :
    h 135 2 = ((27522063213634645341565356741 : ℝ) / 7501650119421167306375938900) * (h 1 0) + ((16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (h 1 1) + ((-925399385763555945482272269 : ℝ) / 220636768218269626658115850) * (h 1 2) + ((-27522063213634645341565356741 : ℝ) / 7501650119421167306375938900) * (h 3 0) + ((-16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (h 5 1) + ((1146036153981825572140388119 : ℝ) / 220636768218269626658115850) * (h 9 2) := by
  have r0 := H 297 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 1 - h 97 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 297 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 2 - h 97 2) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 303 1
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 1 - h 99 1) - ((-8086669269897091777415908 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 303 2
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 2 - h 99 2) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 391 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 1 - h 134 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 391 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 2 - h 134 2) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-16139933799702809877368987 : ℝ) / 17295625562285567945134824367560486337675479266320) * r0 + ((-114502986016987110991293702763225036414084356073 : ℝ) / 22938133614993871189318166569094596775340767152202436215853127052998060) * r1 + ((2305704828528972839624141 : ℝ) / 16431181988304516883014878798825688357018648842710) * r2 + ((371499064464731899404634030150756843967930521287 : ℝ) / 610166894698065660446096321641690897687745792831586467189918771293605790) * r3 + ((16139933799702809877368987 : ℝ) / 43157725956309324424803420216144581548415367489480) * r4 + ((114502986016987110991293702763225036414084356073 : ℝ) / 57237460474617971867851357293496559179943519019828612902559830842279590) * r5 + ((16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (value_389 h H) + ((-32242666961150933094358397585000489763123313279043 : ℝ) / 2941437906509362515058386550672872257405834702170) * (value_388 h H) + ((458011944067948443965174811052900145656337424292 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_390 h H) + ((-16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (value_397 h H) + ((32242666961150933094358397585000489763123313279043 : ℝ) / 2941437906509362515058386550672872257405834702170) * (value_396 h H) + ((-371499064464731899404634030150756843967930521287 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_398 h H)

/-- Coordinate 135.3, recovered from nonplanar cycle 39. -/
theorem value_543 (h : Assignment) (H : Constraints h) :
    h 135 3 = ((8067963623346575635148407 : ℝ) / 110318384109134813329057925) * (h 1 0) + ((236618073705471893872696 : ℝ) / 959290296601172289817895) * (h 1 1) + ((-9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (h 1 2) + h 1 3 + ((-8067963623346575635148407 : ℝ) / 110318384109134813329057925) * (h 3 0) + ((-236618073705471893872696 : ℝ) / 959290296601172289817895) * (h 5 1) + ((9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (h 9 2) := by
  have r0 := H 297 1
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 1 - h 97 1) - ((1143338598549074470824196 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 297 2
  change ((-1060565026627135066369648 : ℤ) : ℝ) * (h 134 2 - h 97 2) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 134 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 303 1
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 1 - h 99 1) - ((-8086669269897091777415908 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 303 2
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 2 - h 99 2) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 303 3
  change ((-7052902382819074324866358 : ℤ) : ℝ) * (h 135 3 - h 99 3) - ((-4022507252993022195835832 : ℤ) : ℝ) * (h 135 0 - h 99 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 391 1
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 1 - h 134 1) - ((18043352961358164180899072 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 391 2
  change ((2646424936362418154180472 : ℤ) : ℝ) * (h 135 2 - h 134 2) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 135 0 - h 134 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-1739838777246116866711 : ℝ) / 7480806904102754301528903273166300319063788610) * r0 + ((-419665227892120525770754496882452570713457946 : ℝ) / 337325494338145164548796567192567599637364222826506414939016574308795) * r1 + ((994193586997781066692 : ℝ) / 28427650498796742012136468510079045600378285195) * r2 + ((479617403305280600880862282151374366529666224 : ℝ) / 2563726448311200253975194628746600410452713415258766668865204921401705) * r3 + ((-1 : ℝ) / 7052902382819074324866358) * r4 + ((29577259213183986734087 : ℝ) / 317336220266980326652966325118710158444230643305) * r5 + ((14268617748332097876205652894003387404257570164 : ℝ) / 28618730237308985933925678646748279589971759509914306451279915421139795) * r6 + ((236618073705471893872696 : ℝ) / 959290296601172289817895) * (value_389 h H) + ((-236345385370015396334882790099389194933475731772 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_388 h H) + ((114148941986656783009645223152027099234060561312 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_390 h H) + ((-236618073705471893872696 : ℝ) / 959290296601172289817895) * (value_397 h H) + ((236345385370015396334882790099389194933475731772 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_396 h H) + ((-114148941986656783009645223152027099234060561312 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_398 h H) + (1 : ℝ) * (value_399 h H)

/-- Coordinate 108.0, recovered from skew spokes on cycle 42. -/
theorem value_432 (h : Assignment) (H : Constraints h) :
    h 108 0 = ((102955657658522908490713 : ℝ) / 64806544522658559272684) * (h 1 0) + ((621191793265828350363 : ℝ) / 1408837924405620853754) * (h 1 1) + ((-58850120629217951428689 : ℝ) / 32403272261329279636342) * (h 1 2) + ((-38149113135864349218029 : ℝ) / 64806544522658559272684) * (h 3 0) + ((-621191793265828350363 : ℝ) / 1408837924405620853754) * (h 5 1) + ((58850120629217951428689 : ℝ) / 32403272261329279636342) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-39941049842128006313378827261452396873023125 : ℝ) / 71291586266619291650521117544621067655891663199437175206547386402464) * r0 + ((306212940345609350569647250125149301875 : ℝ) / 3798571305766160041055046757492597381494653836287147016546642498) * r1 + ((-753604714002415213459977872857592393830625 : ℝ) / 7229389552019937945103808193768295500345132712285925168853562513248) * r2 + ((306212940345609350569647250125149301875 : ℝ) / 20415475610456985885043789123493161845603795489724746054413832758) * r3 + ((-20822461528162872754591 : ℝ) / 21385816326904635451711243342288641398027409120) * r4 + ((159637946297717369 : ℝ) / 1139482967119812204375066247990656510977590) * r5 + ((-39941049842128006313378827261452396873023125 : ℝ) / 31449729892506816840751828444542119702981484) * (value_321 h H) + ((8862142132122065577274454984829539105906875 : ℝ) / 15724864946253408420375914222271059851490742) * (value_320 h H) + ((20822479943501435838736013008510152527500 : ℝ) / 113948296711981220437506624799065651097759) * (value_322 h H) + ((39941049842128006313378827261452396873023125 : ℝ) / 31449729892506816840751828444542119702981484) * (value_529 h H) + ((6862722814131342843101459237441520745583867 : ℝ) / 15724864946253408420375914222271059851490742) * (value_528 h H) + ((-20822479943501435838736013008510152527500 : ℝ) / 113948296711981220437506624799065651097759) * (value_530 h H)

/-- Coordinate 108.1, recovered from skew spokes on cycle 42. -/
theorem value_433 (h : Assignment) (H : Constraints h) :
    h 108 1 = ((-125552494446375169052 : ℝ) / 81008180653323199090855) * (h 1 0) + ((373387608157540981246 : ℝ) / 704418962202810426877) * (h 1 1) + ((143533237735706606712 : ℝ) / 81008180653323199090855) * (h 1 2) + ((125552494446375169052 : ℝ) / 81008180653323199090855) * (h 3 0) + ((331031354045269445631 : ℝ) / 704418962202810426877) * (h 5 1) + ((-143533237735706606712 : ℝ) / 81008180653323199090855) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-1188519579592976903762691539958022219698107 : ℝ) / 5242028401957300856655964525339784386462622294076262882834366647240) * r0 + ((309805641143044417206569801191167439642 : ℝ) / 9496428264415400102637616893731493453736634590717867541366606245) * r1 + ((-22424897728169375542692293206755136220719 : ℝ) / 531572761177936613610574131894727610319495052373965085945114890680) * r2 + ((309805641143044417206569801191167439642 : ℝ) / 51038689026142464712609472808732904614009488724311865136034581895) * r3 + ((-29758497609357064207452770867482013681797337 : ℝ) / 25638538059975675596437931725921096567581685469691552299186940562500) * r4 + ((309805641143044417206569801191167439642 : ℝ) / 5464309049440681073409618867417113505452192129090271163509578125) * r5 + ((-20204832853080607363965756179286377734867819 : ℝ) / 39312162365633521050939785555677649628726855) * (value_321 h H) + ((8966118878072522507774614688838824125262474 : ℝ) / 39312162365633521050939785555677649628726855) * (value_320 h H) + ((42133567195454040740093492961998771791312 : ℝ) / 569741483559906102187533123995328255488795) * (value_322 h H) + ((59516995218714128414905541734964027363594674 : ℝ) / 39312162365633521050939785555677649628726855) * (value_529 h H) + ((-8966118878072522507774614688838824125262474 : ℝ) / 39312162365633521050939785555677649628726855) * (value_528 h H) + ((-42133567195454040740093492961998771791312 : ℝ) / 569741483559906102187533123995328255488795) * (value_530 h H)

/-- Coordinate 108.2, recovered from skew spokes on cycle 42. -/
theorem value_434 (h : Assignment) (H : Constraints h) :
    h 108 2 = ((-216391415190288059972887769 : ℝ) / 44068450275407820305425120) * (h 1 0) + ((-234599035402598809246983 : ℝ) / 191601957719164436110544) * (h 1 1) + ((8572056432343305206958001 : ℝ) / 1296130890453171185453680) * (h 1 2) + ((216391415190288059972887769 : ℝ) / 44068450275407820305425120) * (h 3 0) + ((234599035402598809246983 : ℝ) / 191601957719164436110544) * (h 5 1) + ((-7275925541890134021504321 : ℝ) / 1296130890453171185453680) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-20179236550439498456702478086347359745383464009 : ℝ) / 6925468380185874046050622847191760858000904425088182734350317536239360) * r0 + ((154706583388856995742109334463313373080031 : ℝ) / 369004069702998403988204542156423745630909229810751424464530985520) * r1 + ((-380740312272443367107593926157497353686480453 : ℝ) / 702283556481936828952941367394634420033527177764918444974346072715520) * r2 + ((154706583388856995742109334463313373080031 : ℝ) / 1983217630730107200261396657710764293572940133287546759571629467920) * r3 + ((-20179236550439498456702478086347359745383464009 : ℝ) / 3984961344179076435560638531114593295075553398717772700216484476000000) * r4 + ((-8076697628259033454328700963923271345339 : ℝ) / 212327437349695035995345190276779267640428037016079108067800750000) * r5 + ((-20179236550439498456702478086347359745383464009 : ℝ) / 3055116618129233635958749048898377342575344160) * (value_321 h H) + ((4477380117311896862036579785633266487097857607 : ℝ) / 1527558309064616817979374524449188671287672080) * (value_320 h H) + ((154706583388856995742109334463313373080031 : ℝ) / 162783281017116029196438035427236644425370) * (value_322 h H) + ((20179236550439498456702478086347359745383464009 : ℝ) / 3055116618129233635958749048898377342575344160) * (value_529 h H) + ((-4477380117311896862036579785633266487097857607 : ℝ) / 1527558309064616817979374524449188671287672080) * (value_528 h H) + ((8076697628259033454328700963923271345339 : ℝ) / 162783281017116029196438035427236644425370) * (value_530 h H)

/-- Coordinate 108.3, recovered from skew spokes on cycle 42. -/
theorem value_435 (h : Assignment) (H : Constraints h) :
    h 108 3 = ((7576641911662506870429 : ℝ) / 81008180653323199090855) * (h 1 0) + ((176638774353111342216 : ℝ) / 704418962202810426877) * (h 1 1) + ((-8661715161776066384874 : ℝ) / 81008180653323199090855) * (h 1 2) + h 1 3 + ((-7576641911662506870429 : ℝ) / 81008180653323199090855) * (h 3 0) + ((-176638774353111342216 : ℝ) / 704418962202810426877) * (h 5 1) + ((8661715161776066384874 : ℝ) / 81008180653323199090855) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 335 3
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 3 - h 108 3) - ((548544797169282558194688 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-51461815777876713764696125484553615622404 : ℝ) / 218417850081554202360665188555824349435942595586510953451431943635) * r0 + ((321943253207361013513613644390293754176 : ℝ) / 9496428264415400102637616893731493453736634590717867541366606245) * r1 + ((-970977656186353089899926895934973879668 : ℝ) / 22148865049080692233773922162280317096645627182248545247713120445) * r2 + ((321943253207361013513613644390293754176 : ℝ) / 51038689026142464712609472808732904614009488724311865136034581895) * r3 + ((-51461815777876713764696125484553615622404 : ℝ) / 125679108137135664688421233950593610625400418969076236760720296875) * r4 + ((321943253207361013513613644390293754176 : ℝ) / 5464309049440681073409618867417113505452192129090271163509578125) * r5 + ((-1 : ℝ) / 1304356540935979975475000) * r6 + ((-6998806945791233071998673065899291724646944 : ℝ) / 13104054121877840350313261851892549876242285) * (value_321 h H) + ((3105798277914292346098249191397392855052224 : ℝ) / 13104054121877840350313261851892549876242285) * (value_320 h H) + ((43784282436201097837851455637079950567936 : ℝ) / 569741483559906102187533123995328255488795) * (value_322 h H) + ((6998806945791233071998673065899291724646944 : ℝ) / 13104054121877840350313261851892549876242285) * (value_529 h H) + ((-3105798277914292346098249191397392855052224 : ℝ) / 13104054121877840350313261851892549876242285) * (value_528 h H) + ((-43784282436201097837851455637079950567936 : ℝ) / 569741483559906102187533123995328255488795) * (value_530 h H) + (1 : ℝ) * (value_531 h H)

/-- Coordinate 109.0, recovered from skew spokes on cycle 42. -/
theorem value_436 (h : Assignment) (H : Constraints h) :
    h 109 0 = ((-524424025816764199423282393 : ℝ) / 99870641772172291672211820) * (h 1 0) + ((-4764387564147266187978403 : ℝ) / 9552843995599088768646348) * (h 1 1) + ((1099135286985820856325509673 : ℝ) / 183096176582315868065721670) * (h 1 2) + ((624294667588936491095494213 : ℝ) / 99870641772172291672211820) * (h 3 0) + ((4764387564147266187978403 : ℝ) / 9552843995599088768646348) * (h 5 1) + ((-1099135286985820856325509673 : ℝ) / 183096176582315868065721670) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-34931221489966592572297871 : ℝ) / 12084153634140630070720531227057656670603330531120) * r0 + ((-266002993616693518817 : ℝ) / 7726440942545159891765045541596967180692666580) * r1 + ((-10985513262637544757531592694689047746876443277 : ℝ) / 20424998674882147480587315995035840738860151439855704929941683596360240) * r2 + ((-4433727260330465767884803007764554873198687 : ℝ) / 692151489621965355799953802900830920178764722706107647881655518290980) * r3 + ((-582232202919789872149174412818519530584451493681 : ℝ) / 115897388487989881871941665254271542418062331404487654329198649443250000) * r4 + ((-4433727260330465767884803007764554873198687 : ℝ) / 74103189570326011427072675993779758579323741307217170287211412687500) * r5 + ((-582232202919789872149174412818519530584451493681 : ℝ) / 88854070839269338755298023728365122577965665670) * (value_321 h H) + ((18489432165304017223271092706074278344089301573 : ℝ) / 4556619017398427628476821729659749875793111060) * (value_320 h H) + ((-150746726851235836108083302263994865688755358 : ℝ) / 1931610235636289972941261385399241795173166645) * (value_322 h H) + ((582232202919789872149174412818519530584451493681 : ℝ) / 88854070839269338755298023728365122577965665670) * (value_529 h H) + ((-13932813147905589594794270976414528468296190513 : ℝ) / 4556619017398427628476821729659749875793111060) * (value_528 h H) + ((150746726851235836108083302263994865688755358 : ℝ) / 1931610235636289972941261385399241795173166645) * (value_530 h H)

/-- Coordinate 109.1, recovered from skew spokes on cycle 42. -/
theorem value_437 (h : Assignment) (H : Constraints h) :
    h 109 1 = ((-6109836224447014583212136 : ℝ) / 1920589264849467147542535) * (h 1 0) + ((17126635218530564174956 : ℝ) / 183708538376905553243199) * (h 1 1) + ((25611094310695704965245392 : ℝ) / 7042160637781379540989295) * (h 1 2) + ((6109836224447014583212136 : ℝ) / 1920589264849467147542535) * (h 3 0) + ((166581903158374989068243 : ℝ) / 183708538376905553243199) * (h 5 1) + ((-25611094310695704965245392 : ℝ) / 7042160637781379540989295) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-85287428915130875127148551460287765440099591 : ℝ) / 65099608770864055178264261736416485980366895336413411159033107252280) * r0 + ((-7379346834652140381213665726248313459432 : ℝ) / 353802221580782908577523161610959162936776605089203321516484278545) * r1 + ((-4570979886775402581363980431610194236595918 : ℝ) / 14028158430550925467436343403183956551414939175725072067267639832665) * r2 + ((-7379346834652140381213665726248313459432 : ℝ) / 1901515081379025702747125832145139890601001985456339691982570105195) * r3 + ((-242261933999096336812290962875340294539583654 : ℝ) / 79599854730762281505454440421889795616801051788796465885438632859375) * r4 + ((-7379346834652140381213665726248313459432 : ℝ) / 203580191127269262162287571411482853239900388206640577712119265625) * r5 + ((-1449886291557224877161525374824892012481693047 : ℝ) / 488209180435545817336802328177830343834976185) * (value_321 h H) + ((301460985155576831096503652011694440295532984 : ℝ) / 162736393478515272445600776059276781278325395) * (value_320 h H) + ((-1003591169512691091845058538769770630482752 : ℝ) / 21226486105893296405947927312079580166738095) * (value_322 h H) + ((1938095471992770694498327703002722356316669232 : ℝ) / 488209180435545817336802328177830343834976185) * (value_529 h H) + ((-301460985155576831096503652011694440295532984 : ℝ) / 162736393478515272445600776059276781278325395) * (value_528 h H) + ((1003591169512691091845058538769770630482752 : ℝ) / 21226486105893296405947927312079580166738095) * (value_530 h H)

/-- Coordinate 109.2, recovered from skew spokes on cycle 42. -/
theorem value_438 (h : Assignment) (H : Constraints h) :
    h 109 2 = ((-6179510915861363677618869439 : ℝ) / 1044800560078110128263139040) * (h 1 0) + ((-136151565219732618160718185 : ℝ) / 99937444877036620964300256) * (h 1 1) + ((874532080379190745238977007 : ℝ) / 112674570204502072655828720) * (h 1 2) + ((6179510915861363677618869439 : ℝ) / 1044800560078110128263139040) * (h 3 0) + ((136151565219732618160718185 : ℝ) / 99937444877036620964300256) * (h 5 1) + ((-761857510174688672583148287 : ℝ) / 112674570204502072655828720) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-6860689206420862829106872475863004696875416119463 : ℝ) / 2107144136695327738010057623884328818212515668249029292395583615541799040) * r0 + ((31888065913250155144681234667091152358000427 : ℝ) / 79251697634095371521365188200854852497837959539981544019692478394080) * r1 + ((-129446966158884204322771178789868013148592756971 : ℝ) / 213676909214151696719990382717298026191152353524644297728620689931153280) * r2 + ((-52244490439759661906960975397678654582659401 : ℝ) / 7240969429891329876061055168808692703408615560617741547069626960582560) * r3 + ((-6860689206420862829106872475863004696875416119463 : ℝ) / 1212464987258971071891082036506225366835113620846947768367001255714000000) * r4 + ((-52244490439759661906960975397678654582659401 : ℝ) / 775233367812641350313991071934926705137540678290887319927750163500000) * r5 + ((-6860689206420862829106872475863004696875416119463 : ℝ) / 929550279549279236209271632850588974661794656240) * (value_321 h H) + ((2134291273986920124964815056908770743386032478587 : ℝ) / 619700186366186157472847755233725983107863104160) * (value_320 h H) + ((542097120525252637459580989340549590086007259 : ℝ) / 594341610965012299366541964738228244668666660) * (value_322 h H) + ((6860689206420862829106872475863004696875416119463 : ℝ) / 929550279549279236209271632850588974661794656240) * (value_529 h H) + ((-2134291273986920124964815056908770743386032478587 : ℝ) / 619700186366186157472847755233725983107863104160) * (value_528 h H) + ((52244490439759661906960975397678654582659401 : ℝ) / 594341610965012299366541964738228244668666660) * (value_530 h H)

end CubicalIndecomposability.Rigidity
end VerificationSource015

/- Original source: CubicalIndecomposability/Rigidity/Values06.lean -/
section VerificationSource016


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

/-! Each coordinate identity below is an exact linear consequence
of edge equations and identities in earlier modules. No rank result or
external solver is assumed. -/

/-- Coordinate 109.3, recovered from skew spokes on cycle 42. -/
theorem value_439 (h : Assignment) (H : Constraints h) :
    h 109 3 = ((-88726955960883908139193 : ℝ) / 286984602793598539287965) * (h 1 0) + ((5364791332306573317908 : ℝ) / 27450701136778990714501) * (h 1 1) + ((1115771857151937365366838 : ℝ) / 3156830630729583932167615) * (h 1 2) + h 1 3 + ((88726955960883908139193 : ℝ) / 286984602793598539287965) * (h 3 0) + ((-5364791332306573317908 : ℝ) / 27450701136778990714501) * (h 5 1) + ((-1115771857151937365366838 : ℝ) / 3156830630729583932167615) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 332 3
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 3 - h 108 3) - ((-717306105909058847318400 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 335 3
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 3 - h 108 3) - ((548544797169282558194688 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((-6346563024968631689573290806230298316705229 : ℝ) / 17023173557898359256385194879350288000613182401188564412275898735510) * r0 + ((10039346146225185317853455592888817804988 : ℝ) / 370068990389094766443156410420658434795938747851925313310345624685) * r1 + ((-6346563024968631689573290806230298316705229 : ℝ) / 91491288858075880364361709578845466460411428863451010926885499544210) * r2 + ((10039346146225185317853455592888817804988 : ℝ) / 1988941062132084355746993686496640575226335410075021976671423903135) * r3 + ((-1 : ℝ) / 12183177647841976940712616) * r4 + ((-6346563024968631689573290806230298316705229 : ℝ) / 9795249196077576223118801999177784180025552011873534003481968343750) * r5 + ((10039346146225185317853455592888817804988 : ℝ) / 212940199914729917893886999982125743044033739388555087032216703125) * r6 + ((-1 : ℝ) / 1304356540935979975475000) * r7 + ((-431566285697866954890983774823660285535955572 : ℝ) / 510655579536030682501712780048075417114745205) * (value_321 h H) + ((17391113153049685255437785049303762306904324 : ℝ) / 39281198425848514038593290772928878239595785) * (value_320 h H) + ((1365351075886625203228069960632879221478368 : ℝ) / 22202416501566551413117946958611974657162835) * (value_322 h H) + ((431566285697866954890983774823660285535955572 : ℝ) / 510655579536030682501712780048075417114745205) * (value_529 h H) + ((-17391113153049685255437785049303762306904324 : ℝ) / 39281198425848514038593290772928878239595785) * (value_528 h H) + ((-1365351075886625203228069960632879221478368 : ℝ) / 22202416501566551413117946958611974657162835) * (value_530 h H) + (1 : ℝ) * (value_531 h H)

/-- Coordinate 110.0, recovered from skew spokes on cycle 42. -/
theorem value_440 (h : Assignment) (H : Constraints h) :
    h 110 0 = ((54965293097119131924855289 : ℝ) / 31143641414917327246934100) * (h 1 0) + ((1385622525909000961769227 : ℝ) / 2978957004905135649706740) * (h 1 1) + ((-12800136748644181407158081 : ℝ) / 6344075103038714809560650) * (h 1 2) + ((-23821651682201804677921189 : ℝ) / 31143641414917327246934100) * (h 3 0) + ((-1385622525909000961769227 : ℝ) / 2978957004905135649706740) * (h 5 1) + ((12800136748644181407158081 : ℝ) / 6344075103038714809560650) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 333 1
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 1 - h 108 1) - ((853677112946252813688448 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 333 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 2 - h 108 2) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 337 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 1 - h 109 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 337 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 2 - h 109 2) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 339 1
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 1 - h 110 1) - ((37752814767527211137468056 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 339 2
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 2 - h 110 2) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((-1013478390600740177026180976496382275683551117 : ℝ) / 2026135769900760380859150802081604495411061806860601102813436918363600) * r0 + ((108272397154631915757354749494685799117241 : ℝ) / 1295483228836803312569789515397445329546714710268926536325726929900) * r1 + ((-1717045255384242938816997912182704226407347121209383146029246265631 : ℝ) / 18964914068534460267805781288121391071159604207804594443100245571705040212127227348870492800) * r2 + ((8273717177553385611897575483645138638033837343397272281253258731 : ℝ) / 160668229800563681936334144544506669880348309305249920953374842599163543996602149854561400) * r3 + ((1963540105453304206366501 : ℝ) / 6232623308408712814914506652078744742433644844160) * r4 + ((1496607505916803958401615 : ℝ) / 334545221701350026094675724707167916321805936488) * r5 + ((-1013478390600740177026180976496382275683551117 : ℝ) / 1165852225130849609825809219014060043660367821557886506116478791250000) * r6 + ((108272397154631915757354749494685799117241 : ℝ) / 745429811464737602190415101671393889808419323246730502632019687500) * r7 + ((-19360873004062091187801455378290617190704601 : ℝ) / 3276406830400012420791973274505973926019920534170598385208150827793280) * r8 + ((-250866112810547468114153249209376213089612955 : ℝ) / 2989721232740011333972675612986701207493177487430671026502437630361368) * r9 + ((-1413343729296532656709506242615215054921435873 : ℝ) / 6644724025037062752545865612023868377564856091582469429157333411967170240) * r10 + ((-14756830165326321653773720541728012534683115 : ℝ) / 4885826488997840259224901185311667924680041243810639286145098097034684) * r11 + ((-1013478390600740177026180976496382275683551117 : ℝ) / 893814067351751493488664424483389559607605350) * (value_321 h H) + ((65116916093092929718238564590885896661040183 : ℝ) / 137509856515654075921332988382059932247323900) * (value_320 h H) + ((3681261503257485135750061482819317169986194 : ℝ) / 19430740594603293336710096184421512165382725) * (value_322 h H) + ((1013478390600740177026180976496382275683551117 : ℝ) / 893814067351751493488664424483389559607605350) * (value_529 h H) + ((72392940422561146203094423791174035586283717 : ℝ) / 137509856515654075921332988382059932247323900) * (value_528 h H) + ((-3681261503257485135750061482819317169986194 : ℝ) / 19430740594603293336710096184421512165382725) * (value_530 h H)

/-- Coordinate 110.1, recovered from skew spokes on cycle 42. -/
theorem value_441 (h : Assignment) (H : Constraints h) :
    h 110 1 = ((519734538873226253932652 : ℝ) / 338517841466492687466675) * (h 1 0) + ((50182337158358922070838 : ℝ) / 67703568293298537493335) * (h 1 1) + ((-22006194672091771648456 : ℝ) / 12537697832092321758025) * (h 1 2) + ((-519734538873226253932652 : ℝ) / 338517841466492687466675) * (h 3 0) + ((17521231134939615422497 : ℝ) / 67703568293298537493335) * (h 5 1) + ((22006194672091771648456 : ℝ) / 12537697832092321758025) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 333 1
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 1 - h 108 1) - ((853677112946252813688448 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 333 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 2 - h 108 2) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 337 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 1 - h 109 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 337 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 2 - h 109 2) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 339 1
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 1 - h 110 1) - ((37752814767527211137468056 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 339 2
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 2 - h 110 2) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((2168005649808920312124086260178596768206119 : ℝ) / 7301814562534709579938813632240146402899664730606676841108642695800) * r0 + ((2320423189631634653031449061394601304598 : ℝ) / 39683774796384291195319639305652969580976438753297156745155666825) * r1 + ((1403693973422300782278681275244724122055914718136324557072314026 : ℝ) / 18154407612542251368020603382280234782792358276986858563985536460068436467883647721559575) * r2 + ((58265031532396037576984973750112730620743878626677860049642922232 : ℝ) / 179640417015155934892255024260977566175508015789417278220102405534539081059442028221774925) * r3 + ((165208317112012666072823659827080698464980839 : ℝ) / 12744894247301542351478068458912877755490106685001223453591744681340) * r4 + ((106752972498725700111922222858986884111519890 : ℝ) / 2736403764861801740170291169119529635737581729426733270918227534523) * r5 + ((-8951631905383363412309493230166785521469101 : ℝ) / 35712864603810610577668068961893143629912453031911543171552215937500) * r6 + ((2320423189631634653031449061394601304598 : ℝ) / 22834312406528523387255798568985385952629445672577713025289140625) * r7 + ((-70029631031816407725756500299267315110374243 : ℝ) / 1358964196700005151805761642266682367042353403377577739319289831982440) * r8 + ((-1814800532478336901902677788602777029895838130 : ℝ) / 2480109658977509402045514997136695319852294961164079374257703943367953) * r9 + ((-70029631031816407725756500299267315110374243 : ℝ) / 37754113778619674730374236431953797599800318702173121756575758022540740) * r10 + ((-213505944997451400223844445717973768223039780 : ℝ) / 8106030311291871339168586057448903602310068427231287906558912751898453) * r11 + ((36856096046751645306109466423036145059504023 : ℝ) / 54759359857518372130728452883369716102442225) * (value_321 h H) + ((-2346455601152589635544220671449346392791126 : ℝ) / 4212258450578336317748342529489978161726325) * (value_320 h H) + ((315577553789902312812277072349665777425328 : ℝ) / 2380841732935581396988193603624770265323575) * (value_322 h H) + ((17903263810766726824618986460333571042938202 : ℝ) / 54759359857518372130728452883369716102442225) * (value_529 h H) + ((2346455601152589635544220671449346392791126 : ℝ) / 4212258450578336317748342529489978161726325) * (value_528 h H) + ((-315577553789902312812277072349665777425328 : ℝ) / 2380841732935581396988193603624770265323575) * (value_530 h H)

/-- Coordinate 110.2, recovered from skew spokes on cycle 42. -/
theorem value_442 (h : Assignment) (H : Constraints h) :
    h 110 2 = ((-994381301605265439714838003 : ℝ) / 184153705757772021981871200) * (h 1 0) + ((-523293629333666712175409207 : ℝ) / 405138152667098448360116640) * (h 1 1) + ((15828296484273802598108811 : ℝ) / 2206634818448248629412400) * (h 1 2) + ((994381301605265439714838003 : ℝ) / 184153705757772021981871200) * (h 3 0) + ((523293629333666712175409207 : ℝ) / 405138152667098448360116640) * (h 5 1) + ((-13621661665825553968696411 : ℝ) / 2206634818448248629412400) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 333 1
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 1 - h 108 1) - ((853677112946252813688448 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 333 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 2 - h 108 2) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 337 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 1 - h 109 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 337 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 2 - h 109 2) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 339 1
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 1 - h 110 1) - ((37752814767527211137468056 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 339 2
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 2 - h 110 2) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((-1144102031860781283542548758069246665632208931221 : ℝ) / 371399495908765468074007816590262806637088546857578010846150002079171200) * r0 + ((97604725296758743287492124486942253219269283 : ℝ) / 237467708381563598512792721605027369972563009499730185963011510280800) * r1 + ((-2016980369748441033851166488146579793857910145883555146896234932472653 : ℝ) / 3476351204910490629959529300466077598087343101743659572700462405665584762362103934905999897600) * r2 + ((-687386778178714978206115447624401045858491497224904544453496672847 : ℝ) / 29451185079964194914938467539114787835458629218736246379975145060785804412594550599427428800) * r3 + ((-7311819281169243059352661831580189728544865341 : ℝ) / 8357857224750951170547371140617497039874279277046281769456767142261760) * r4 + ((-990247113092859417787720941486415504966389359 : ℝ) / 448620277505014290772028009753733296993251755312043065566429412783168) * r5 + ((-1144102031860781283542548758069246665632208931221 : ℝ) / 213705781789202693696765724667968571481396118942958674338568460170000000) * r6 + ((-7152310952406838179988394072547638454968017 : ℝ) / 136640525440666683949338698636808549540534602904705034743330217500000) * r7 + ((7311819281169243059352661831580189728544865341 : ℝ) / 445591328934401689227708365332812453938709192647201380388308512579886080) * r8 + ((5573058369275736487577799362132551344991128215 : ℝ) / 23917769861920090671781404903893609659945419899445368212019501042890944) * r9 + ((533762807525354743332744313705353850183775169893 : ℝ) / 903682467405040534346237723235246099348820428455215842365397344027535152640) * r10 + ((5573058369275736487577799362132551344991128215 : ℝ) / 664472402503706275254586561202386837756485609158246942915733341196717024) * r11 + ((-1144102031860781283542548758069246665632208931221 : ℝ) / 163840004693694969415139531027042190578507137200) * (value_321 h H) + ((80182769162546921837936109873086676978965565229 : ℝ) / 25206154568260764525406081696468029319770328800) * (value_320 h H) + ((97604725296758743287492124486942253219269283 : ℝ) / 104757036249165581467480518559489891674237300) * (value_322 h H) + ((1144102031860781283542548758069246665632208931221 : ℝ) / 163840004693694969415139531027042190578507137200) * (value_529 h H) + ((-80182769162546921837936109873086676978965565229 : ℝ) / 25206154568260764525406081696468029319770328800) * (value_528 h H) + ((7152310952406838179988394072547638454968017 : ℝ) / 104757036249165581467480518559489891674237300) * (value_530 h H)

/-- Coordinate 110.3, recovered from skew spokes on cycle 42. -/
theorem value_443 (h : Assignment) (H : Constraints h) :
    h 110 3 = ((1508564293234293310535119 : ℝ) / 7785910353729331811733525) * (h 1 0) + ((197004103519997441171332 : ℝ) / 744739251226283912426685) * (h 1 1) + ((-702618985889944829564302 : ℝ) / 3172037551519357404780325) * (h 1 2) + h 1 3 + ((-1508564293234293310535119 : ℝ) / 7785910353729331811733525) * (h 3 0) + ((-197004103519997441171332 : ℝ) / 744739251226283912426685) * (h 5 1) + ((702618985889944829564302 : ℝ) / 3172037551519357404780325) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 333 1
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 1 - h 108 1) - ((853677112946252813688448 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 333 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 2 - h 108 2) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 333 3
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 3 - h 108 3) - ((55672055611990139857792 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 335 3
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 3 - h 108 3) - ((548544797169282558194688 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 337 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 1 - h 109 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 337 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 2 - h 109 2) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 339 1
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 1 - h 110 1) - ((37752814767527211137468056 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  have r13 := H 339 2
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 2 - h 110 2) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r13
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r13
  linear_combination ((-93043508296612293502938320229538337224749313 : ℝ) / 461839771080320380931129962239189259983403794210872310200121650509350) * r0 + ((357295982750818942219247247131708854959916 : ℝ) / 10039995023485225672415868744330201303987039004584180656524383706725) * r1 + ((-77909659113714499713857416247244098992409070875918431471964129767 : ℝ) / 2161442412222677456992570661513835011786572538389494219618042693834030318293911940496269400) * r2 + ((16849625887406003039362268660302107238681862849634554141652551078 : ℝ) / 622589390477184267503294810109963345786349698557843443694327515071758732986833330686425425) * r3 + ((40480545940762214214890775062092416028187 : ℝ) / 225936884319608325328378328844547389702483760733301302158757762280) * r4 + ((1049043315606393184108059843651373423143170 : ℝ) / 412334813883285193724290450141298986207032863338274876439732916161) * r5 + ((1 : ℝ) / 97891938468938791466728) * r6 + ((-93043508296612293502938320229538337224749313 : ℝ) / 265745727787178955180882983745851921716701488737459424188315018593750) * r7 + ((357295982750818942219247247131708854959916 : ℝ) / 5777081038851716416975717037953302646015249755162161395398152578125) * r8 + ((-1 : ℝ) / 1304356540935979975475000) * r9 + ((-688169280992957641653143176055571072479179 : ℝ) / 204775426900000776299498329656623370376245033385662399075509426737080) * r10 + ((-17833736365308684129837017342073348193433890 : ℝ) / 373715154092501416746584451623337650936647185928833878312804703795171) * r11 + ((-2955079853675641637687026579532746370057651 : ℝ) / 24429132444989201296124505926558339623400206219053196430725490485173420) * r12 + ((-2098086631212786368216119687302746846286340 : ℝ) / 1221456622249460064806225296327916981170010310952659821536274524258671) * r13 + ((-6326958564169635958199805775608606931282953284 : ℝ) / 13854118043952148149074298579492538173917882925) * (value_321 h H) + ((198016653705318816565834904339371685160943508 : ℝ) / 1065701387996319088390330659960964474916760225) * (value_320 h H) + ((48592253654111376141817625609912404274548576 : ℝ) / 602352958432702093438012981717066877126864475) * (value_322 h H) + ((6326958564169635958199805775608606931282953284 : ℝ) / 13854118043952148149074298579492538173917882925) * (value_529 h H) + ((-198016653705318816565834904339371685160943508 : ℝ) / 1065701387996319088390330659960964474916760225) * (value_528 h H) + ((-48592253654111376141817625609912404274548576 : ℝ) / 602352958432702093438012981717066877126864475) * (value_530 h H) + (1 : ℝ) * (value_531 h H)

/-- Coordinate 111.0, recovered from skew spokes on cycle 42. -/
theorem value_444 (h : Assignment) (H : Constraints h) :
    h 111 0 = ((-51019593198921921642827329967 : ℝ) / 15949518144260424813804379860) * (h 1 0) + ((-30068092897903049031194683 : ℝ) / 138691462124003694033081564) * (h 1 1) + ((3240347762322562893878199039 : ℝ) / 886084341347801378544687770) * (h 1 2) + ((66969111343182346456631709827 : ℝ) / 15949518144260424813804379860) * (h 3 0) + ((30068092897903049031194683 : ℝ) / 138691462124003694033081564) * (h 5 1) + ((-3240347762322562893878199039 : ℝ) / 886084341347801378544687770) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 333 1
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 1 - h 108 1) - ((853677112946252813688448 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 333 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 2 - h 108 2) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 337 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 1 - h 109 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 337 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 2 - h 109 2) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 339 1
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 1 - h 110 1) - ((37752814767527211137468056 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 339 2
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 2 - h 110 2) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((-915474330674066817838730914121232867510910144817 : ℝ) / 417751183658470683958919518276551991817521936189414941192188676631165680) * r0 + ((23941221499942420981960299765321546008591 : ℝ) / 267104337377538800485242658744598460241382312141569655493726775339620) * r1 + ((-112756057922689786839008461453820362682882363757439752834838911763717 : ℝ) / 300785344800595147407788660267993956105403975340550008988399698792316975054983537529479377280) * r2 + ((3354571768400888256762485640165182516482943049352391811022732266461 : ℝ) / 33126774707098794207795138574911738452145674394123874071772281404716495494386773874330449320) * r3 + ((11705765645095884524160356826648369459462206015 : ℝ) / 2861155956538263704873300522616672432685730490878141605891532990587776) * r4 + ((9675992856565255837223417615658952041429000457 : ℝ) / 767883767747401656087319625555209880831096786154795357463536427620984) * r5 + ((-915474330674066817838730914121232867510910144817 : ℝ) / 240376856405397341194319478076445563381565676618806007883180511931750000) * r6 + ((23941221499942420981960299765321546008591 : ℝ) / 153693642202939476466956188028417879399978054104095912968785493562500) * r7 + ((-1309857226833695677894865 : ℝ) / 17068975287975618181420369668531494013084823840128) * r8 + ((-18406388989996713080235479 : ℝ) / 77877199751388757952730436612674941434699508770584) * r9 + ((-854520892091999570263706048345330970540741039095 : ℝ) / 309358775210732617300455893048888588664345167918981687329432731810629657664) * r10 + ((-9675992856565255837223417615658952041429000457 : ℝ) / 1137348438274752269486970195032678634795386646760962085769973278715550212) * r11 + ((-915474330674066817838730914121232867510910144817 : ℝ) / 184287691947255274087239315442621927516171779330) * (value_321 h H) + ((85319857379214133879197319199820611634564095233 : ℝ) / 28351952607270042167267586991172604233257196820) * (value_320 h H) + ((814001530998042313386650192020932564292094 : ℝ) / 4006254172766419001896506857448302772090690855) * (value_322 h H) + ((915474330674066817838730914121232867510910144817 : ℝ) / 184287691947255274087239315442621927516171779330) * (value_529 h H) + ((-56967904771944091711929732208648007401306898413 : ℝ) / 28351952607270042167267586991172604233257196820) * (value_528 h H) + ((-814001530998042313386650192020932564292094 : ℝ) / 4006254172766419001896506857448302772090690855) * (value_530 h H)

/-- Coordinate 111.1, recovered from skew spokes on cycle 42. -/
theorem value_445 (h : Assignment) (H : Constraints h) :
    h 111 1 = ((867336605631166208965192568 : ℝ) / 306721502774238938727007305) * (h 1 0) + ((2450485155582961681814836 : ℝ) / 2667143502384686423713107) * (h 1 1) + ((-110172271200970053940784112 : ℝ) / 34080166974915437636334145) * (h 1 2) + ((-867336605631166208965192568 : ℝ) / 306721502774238938727007305) * (h 3 0) + ((216658346801724741898271 : ℝ) / 2667143502384686423713107) * (h 5 1) + ((110172271200970053940784112 : ℝ) / 34080166974915437636334145) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 333 1
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 1 - h 108 1) - ((853677112946252813688448 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 333 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 2 - h 108 2) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 337 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 1 - h 109 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 337 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 2 - h 109 2) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 339 1
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 1 - h 110 1) - ((37752814767527211137468056 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 339 2
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 2 - h 110 2) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((4877774685253401108753744165601419871731359771 : ℝ) / 6615968971966730288942164316596977245978854193045033005306155512258280) * r0 + ((2884097942380072831618834572497629286195872 : ℝ) / 35956353108514838526859588677157485032493772788288222854924758218795) * r1 + ((517848004653596177464224635378991336427153853497639501752582416569217 : ℝ) / 3421433297106769801763596010548431250698970219498756352243046573762605591250437739397827916560) * r2 + ((658879626463814573502802636975594209017889243888129168907843388747909 : ℝ) / 2115972734415935480022914476472487293630804951924662456334454474726266149703955181222857450315) * r3 + ((312760287832041197311259095845788230875230444615 : ℝ) / 26108048103411656306968867268877135948257290729263042153760238539113456) * r4 + ((258527840265448532519643628120952174956309331137 : ℝ) / 7006939380695040111796791583191290162583758173662507636854769902041479) * r5 + ((4163281573323155632011921697584010051404127709 : ℝ) / 8089605744412410520962674742957302613802691040055971419145497997703125) * r6 + ((2884097942380072831618834572497629286195872 : ℝ) / 20689528758088006447474871465363945303843199590935988284259585671875) * r7 + ((-46057548957422163226565819774983636920780072113 : ℝ) / 1391926128605187209067405875176516369193427773762500602912285263472112848) * r8 + ((-4394973284512625052833941678056186974257258629329 : ℝ) / 6350662961761166641370039305492855934445014217791409000787301514591514869) * r9 + ((-312760287832041197311259095845788230875230444615 : ℝ) / 38669846901341577162556986631111073583043145989872710916179091476328707208) * r10 + ((-517055680530897065039287256241904349912618662274 : ℝ) / 20756608998514228918137206059346385085015806303387558065302012336558791369) * r11 + ((82922169649307818848813650815224137819433116107 : ℝ) / 49615917062722573792718277234552057408200094435) * (value_321 h H) + ((-60398067383883120476442030522601375822278067072 : ℝ) / 49615917062722573792718277234552057408200094435) * (value_320 h H) + ((392237320163689905100161501859677582922638592 : ℝ) / 2157213785335764077944272923241393800356525845) * (value_322 h H) + ((-33306252586585245056095373580672080411233021672 : ℝ) / 49615917062722573792718277234552057408200094435) * (value_529 h H) + ((60398067383883120476442030522601375822278067072 : ℝ) / 49615917062722573792718277234552057408200094435) * (value_528 h H) + ((-392237320163689905100161501859677582922638592 : ℝ) / 2157213785335764077944272923241393800356525845) * (value_530 h H)

/-- Coordinate 111.2, recovered from skew spokes on cycle 42. -/
theorem value_446 (h : Assignment) (H : Constraints h) :
    h 111 2 = ((-22581126527363584798105121117 : ℝ) / 3707922166870799614833154976) * (h 1 0) + ((-223518282605868375278937481 : ℝ) / 161214007255252157166658912) * (h 1 1) + ((868322307967072849438558517 : ℝ) / 109056534319729400436269264) * (h 1 2) + ((22581126527363584798105121117 : ℝ) / 3707922166870799614833154976) * (h 3 0) + ((223518282605868375278937481 : ℝ) / 161214007255252157166658912) * (h 5 1) + ((-759265773647343449002289253 : ℝ) / 109056534319729400436269264) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 333 1
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 1 - h 108 1) - ((853677112946252813688448 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 333 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 2 - h 108 2) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 337 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 1 - h 109 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 337 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 2 - h 109 2) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 339 1
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 1 - h 110 1) - ((37752814767527211137468056 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 339 2
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 2 - h 110 2) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((-6762294746594300064566584712392999677755557237655 : ℝ) / 2039482701758277390404571186662961519027081452576015507769044205912152448) * r0 + ((10212595914251833956131919864071606576394607 : ℝ) / 25568962210499440730211263059311989356440016205004958474613161400032) * r1 + ((-153799283116712118339982610401153126877562754327222817900458095086451175 : ℝ) / 248167961816811036287919497298446213384031973254309794082695644816914325552031750697655784881152) * r2 + ((-11506832808491372181811510375772427489017182312053684547233238186591 : ℝ) / 700815322692401157462688264962577222365392933849020624807271375495335638014582416185835283392) * r3 + ((-2668412088017153620070580132871598174329393205 : ℝ) / 7629749217435369879662134726977793153828614642341710949044087974900736) * r4 + ((-2205711021802612176793318825846353088657041379 : ℝ) / 2047690047326404416232852334813893015549591429746120953236097140322624) * r5 + ((-1352458949318860012913316942478599935551111447531 : ℝ) / 234706427997885403914863736542334539835128742708823917440808048573360000) * r6 + ((-3627641186401792601494102208670205202152129 : ℝ) / 50022682863999446699672578120702161090180891455418567229498731580000) * r7 + ((2668412088017153620070580132871598174329393205 : ℝ) / 406772932560420006302803543430580126156983458999086934184412131790937088) * r8 + ((393100739203469785785077454800460794446436866779 : ℝ) / 1855901504806916278756541166902021825591237031683334137216380351296150464) * r9 + ((194794082425252214265152349699626666726045703965 : ℝ) / 824956733895286979467882381463702903104920447783951166211820618161679087104) * r10 + ((2205711021802612176793318825846353088657041379 : ℝ) / 3032929168732672718631920520087143026121031058029232228719928743241467232) * r11 + ((-6762294746594300064566584712392999677755557237655 : ℝ) / 899701962737369338107958093853210641002028379088) * (value_321 h H) + ((6358538906805665800547868451646356474056834402551 : ℝ) / 1799403925474738676215916187706421282004056758176) * (value_320 h H) + ((173614130542281177254242637689217311798708319 : ℝ) / 191752336474290140261713148732568337809468964) * (value_322 h H) + ((6762294746594300064566584712392999677755557237655 : ℝ) / 899701962737369338107958093853210641002028379088) * (value_529 h H) + ((-6358538906805665800547868451646356474056834402551 : ℝ) / 1799403925474738676215916187706421282004056758176) * (value_528 h H) + ((18138205932008963007470511043351026010760645 : ℝ) / 191752336474290140261713148732568337809468964) * (value_530 h H)

/-- Coordinate 111.3, recovered from skew spokes on cycle 42. -/
theorem value_447 (h : Assignment) (H : Constraints h) :
    h 111 3 = ((149823184785024998043208093 : ℝ) / 1329126512021702067817031655) * (h 1 0) + ((2928643917064840870245608 : ℝ) / 11557621843666974502756797) * (h 1 1) + ((-57093268423683249565655886 : ℝ) / 443042170673900689272343885) * (h 1 2) + h 1 3 + ((-149823184785024998043208093 : ℝ) / 1329126512021702067817031655) * (h 3 0) + ((-2928643917064840870245608 : ℝ) / 11557621843666974502756797) * (h 5 1) + ((57093268423683249565655886 : ℝ) / 443042170673900689272343885) * (h 9 2) := by
  have r0 := H 239 1
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 1 - h 80 1) - ((1373319828982909675888384 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 239 2
  change ((2266842561455675908895096 : ℤ) : ℝ) * (h 109 2 - h 80 2) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 109 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 332 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 1 - h 108 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 332 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 2 - h 108 2) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 332 3
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 109 3 - h 108 3) - ((-717306105909058847318400 : ℤ) : ℝ) * (h 109 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 333 1
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 1 - h 108 1) - ((853677112946252813688448 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 333 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 110 2 - h 108 2) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 110 0 - h 108 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 335 1
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 1 - h 108 1) - ((527864059549812689780896 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 335 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 2 - h 108 2) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 335 3
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 132 3 - h 108 3) - ((548544797169282558194688 : ℤ) : ℝ) * (h 132 0 - h 108 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 337 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 1 - h 109 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 337 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 2 - h 109 2) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 337 3
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 111 3 - h 109 3) - ((1072921154218855975526496 : ℤ) : ℝ) * (h 111 0 - h 109 0) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  have r13 := H 339 1
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 1 - h 110 1) - ((37752814767527211137468056 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r13
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r13
  have r14 := H 339 2
  change ((-144992312656829719974358604 : ℤ) : ℝ) * (h 111 2 - h 110 2) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 111 0 - h 110 0) = 0 at r14
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r14
  linear_combination ((-820914228129952134724977923538555340142351128 : ℝ) / 3583649859815312239843672338156696008238546021232726211207500902473235) * r0 + ((5332523668009772013565249691352578096436512 : ℝ) / 155810863470230966949724884267682435140806348749248965704673952281445) * r1 + ((-19618107329609459012490650842186186282944699014865365424766594784161 : ℝ) / 547016484906964704354360749801106655466200366918353202621060236529164694830386727565866906720) * r2 + ((525270831129503210399036611137051232477973290158732628588546435787 : ℝ) / 19323951912474296621213830835365180763751643396572259875200497486084622371725618093359428770) * r3 + ((-1 : ℝ) / 12183177647841976940712616) * r4 + ((11796379999969099298204489553218255327502265 : ℝ) / 14025274296756194631731865306944472709243776916069321597507514659744) * r5 + ((165765210516959744095647250084527468070345519 : ℝ) / 63990313978950138007276635462934156735924732179566279788628035635082) * r6 + ((-820914228129952134724977923538555340142351128 : ℝ) / 2062056366222771309264995522714606548616372225896620165664538705296875) * r7 + ((5332523668009772013565249691352578096436512 : ℝ) / 89654624618381361272391109683243762983320531560722615898458204578125) * r8 + ((-1 : ℝ) / 1304356540935979975475000) * r9 + ((-200538459999474688069476322404710340567538505 : ℝ) / 12711654142513125196962610732205628942405733093721466693262879118466784) * r10 + ((-2818008578788315649626003251436966957195873823 : ℝ) / 57996922025216133711141911465688182049726157240104191788011885978004702) * r11 + ((1 : ℝ) / 5219017001769721614586424) * r12 + ((-861135739997744248768927737384932638907665345 : ℝ) / 1516464584366336359315960260043571513060515529014616114359964371620733616) * r13 + ((-165765210516959744095647250084527468070345519 : ℝ) / 94779036522896022457247516252723219566282220563413507147497773226295851) * r14 + ((-111644335025673490322596997601243526259359753408 : ℝ) / 215002307271797819768445868016392248768867075885) * (value_321 h H) + ((3757664377694619546458362923652317988264098016 : ℝ) / 16538639020907524597572759078184019136066698145) * (value_320 h H) + ((725223218849328993844873958023950621115365632 : ℝ) / 9347926403121644337758516000712706468211611995) * (value_322 h H) + ((111644335025673490322596997601243526259359753408 : ℝ) / 215002307271797819768445868016392248768867075885) * (value_529 h H) + ((-3757664377694619546458362923652317988264098016 : ℝ) / 16538639020907524597572759078184019136066698145) * (value_528 h H) + ((-725223218849328993844873958023950621115365632 : ℝ) / 9347926403121644337758516000712706468211611995) * (value_530 h H) + (1 : ℝ) * (value_531 h H)

/-- Coordinate 112.0, recovered from skew spokes on cycle 43. -/
theorem value_448 (h : Assignment) (H : Constraints h) :
    h 112 0 = ((102955657658522908490713 : ℝ) / 64806544522658559272684) * (h 1 0) + ((621191793265828350363 : ℝ) / 1408837924405620853754) * (h 1 1) + ((-58850120629217951428689 : ℝ) / 32403272261329279636342) * (h 1 2) + ((-38149113135864349218029 : ℝ) / 64806544522658559272684) * (h 3 0) + ((-621191793265828350363 : ℝ) / 1408837924405620853754) * (h 5 1) + ((58850120629217951428689 : ℝ) / 32403272261329279636342) * (h 9 2) := by
  have r0 := H 334 0
  change ((1 : ℤ) : ℝ) * (h 112 0 - h 108 0) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_432 h H)

/-- Coordinate 112.1, recovered from skew spokes on cycle 43. -/
theorem value_449 (h : Assignment) (H : Constraints h) :
    h 112 1 = ((-125552494446375169052 : ℝ) / 81008180653323199090855) * (h 1 0) + ((373387608157540981246 : ℝ) / 704418962202810426877) * (h 1 1) + ((143533237735706606712 : ℝ) / 81008180653323199090855) * (h 1 2) + ((125552494446375169052 : ℝ) / 81008180653323199090855) * (h 3 0) + ((331031354045269445631 : ℝ) / 704418962202810426877) * (h 5 1) + ((-143533237735706606712 : ℝ) / 81008180653323199090855) * (h 9 2) := by
  have r0 := H 334 1
  change ((1 : ℤ) : ℝ) * (h 112 1 - h 108 1) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_433 h H)

/-- Coordinate 112.2, recovered from skew spokes on cycle 43. -/
theorem value_450 (h : Assignment) (H : Constraints h) :
    h 112 2 = ((159315987679964401072678111 : ℝ) / 44068450275407820305425120) * (h 1 0) + ((187564067094409291744857 : ℝ) / 191601957719164436110544) * (h 1 1) + ((-5356826484880496673676599 : ℝ) / 1296130890453171185453680) * (h 1 2) + ((-159315987679964401072678111 : ℝ) / 44068450275407820305425120) * (h 3 0) + ((-187564067094409291744857 : ℝ) / 191601957719164436110544) * (h 5 1) + ((6652957375333667859130279 : ℝ) / 1296130890453171185453680) * (h 9 2) := by
  have r0 := H 334 0
  change ((1 : ℤ) : ℝ) * (h 112 0 - h 108 0) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 346 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 134 2 - h 112 2) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 134 0 - h 112 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-5223844288728131369092327 : ℝ) / 1304356540935979975475000) * r0 + ((-1 : ℝ) / 1304356540935979975475000) * r1 + ((-5223844288728131369092327 : ℝ) / 1304356540935979975475000) * (value_432 h H) + (1 : ℝ) * (value_538 h H) + ((5223844288728131369092327 : ℝ) / 1304356540935979975475000) * (value_536 h H)

/-- Coordinate 112.3, recovered from skew spokes on cycle 43. -/
theorem value_451 (h : Assignment) (H : Constraints h) :
    h 112 3 = ((7576641911662506870429 : ℝ) / 81008180653323199090855) * (h 1 0) + ((176638774353111342216 : ℝ) / 704418962202810426877) * (h 1 1) + ((-8661715161776066384874 : ℝ) / 81008180653323199090855) * (h 1 2) + h 1 3 + ((-7576641911662506870429 : ℝ) / 81008180653323199090855) * (h 3 0) + ((-176638774353111342216 : ℝ) / 704418962202810426877) * (h 5 1) + ((8661715161776066384874 : ℝ) / 81008180653323199090855) * (h 9 2) := by
  have r0 := H 334 3
  change ((1 : ℤ) : ℝ) * (h 112 3 - h 108 3) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_435 h H)

/-- Coordinate 137.0, recovered from skew spokes on cycle 43. -/
theorem value_548 (h : Assignment) (H : Constraints h) :
    h 137 0 = ((874649178610136512651819408 : ℝ) / 92929579232735367585149843) * (h 1 0) + ((457728542401119020019870777 : ℝ) / 185859158465470735170299686) * (h 1 1) + ((-1085185267384402951048261791 : ℝ) / 92929579232735367585149843) * (h 1 2) + ((-781719599377401145066669565 : ℝ) / 92929579232735367585149843) * (h 3 0) + ((-457728542401119020019870777 : ℝ) / 185859158465470735170299686) * (h 5 1) + ((1085185267384402951048261791 : ℝ) / 92929579232735367585149843) * (h 9 2) := by
  have r0 := H 334 0
  change ((1 : ℤ) : ℝ) * (h 112 0 - h 108 0) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 334 1
  change ((1 : ℤ) : ℝ) * (h 112 1 - h 108 1) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 336 1
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 1 - h 108 1) - ((806571564938315825113514976 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 336 2
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 2 - h 108 2) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 346 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 134 2 - h 112 2) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 134 0 - h 112 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 347 1
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 1 - h 112 1) - ((3802895776609746356935872 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 347 2
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 2 - h 112 2) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 396 1
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 1 - h 137 1) - ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 396 2
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 2 - h 137 2) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-127746834417734824849421931966243129676316766416390413602720562109294148129 : ℝ) / 3446707276818481907945239049138655494010937748358435084680801783088137500) * r0 + ((258700106205980820615306410920573516690387200311426303 : ℝ) / 4312491331343619393528305649804866904261611738255664) * r1 + ((-126588684655357000299313901249 : ℝ) / 2932494105313661187599247841867309494897895982013851520) * r2 + ((-27 : ℝ) / 40889014862403561737465930920) * r3 + ((-55177940165648872745676069 : ℝ) / 78432138217947919117157126819523863545808300275000) * r4 + ((258700106205980820615306410920573516690387200311426303 : ℝ) / 29211103188021632490234633322406323351900791814590900398702347910273492608128) * r5 + ((55177940165648872745676069 : ℝ) / 407302858763791273310723710069816718204569716539288) * r6 + ((258700106205980820615306410920573516690387200311426303 : ℝ) / 7196868195352167454296763821769585908482532543554593169487533066715441725580074112) * r7 + ((2043627413542550842432447 : ℝ) / 3716629624936287979609223201725591306630702517491423176) * r8 + ((-209808829380159507705490097091709776879690195147563 : ℝ) / 78432138217947919117157126819523863545808300275000) * (value_432 h H) + ((-938024982816030836676493173 : ℝ) / 1022225371560089043436648273) * (value_434 h H) + ((938024982816030836676493173 : ℝ) / 1022225371560089043436648273) * (value_538 h H) + ((288240967598107426822647223911233640425498495422563 : ℝ) / 78432138217947919117157126819523863545808300275000) * (value_536 h H)

/-- Coordinate 137.1, recovered from skew spokes on cycle 43. -/
theorem value_549 (h : Assignment) (H : Constraints h) :
    h 137 1 = ((421820523190100863556743991 : ℝ) / 92929579232735367585149843) * (h 1 0) + ((158310860611951215976033802 : ℝ) / 92929579232735367585149843) * (h 1 1) + ((-2658624247514620828316061234 : ℝ) / 464647896163676837925749215) * (h 1 2) + ((-421820523190100863556743991 : ℝ) / 92929579232735367585149843) * (h 3 0) + ((-65381281379215848390883959 : ℝ) / 92929579232735367585149843) * (h 5 1) + ((2658624247514620828316061234 : ℝ) / 464647896163676837925749215) * (h 9 2) := by
  have r0 := H 334 0
  change ((1 : ℤ) : ℝ) * (h 112 0 - h 108 0) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 334 1
  change ((1 : ℤ) : ℝ) * (h 112 1 - h 108 1) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 336 1
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 1 - h 108 1) - ((806571564938315825113514976 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 336 2
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 2 - h 108 2) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 346 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 134 2 - h 112 2) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 134 0 - h 112 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 347 1
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 1 - h 112 1) - ((3802895776609746356935872 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 347 2
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 2 - h 112 2) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 396 1
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 1 - h 137 1) - ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 396 2
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 2 - h 137 2) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-92681367869807714691028033115206893097995084900289666378521081672400613553 : ℝ) / 4308384096023102384931548811423319367513672185448043855851002228860171875) * r0 + ((62563010714432759069970549854931293983353293959403557 : ℝ) / 1796871388059841413970127354085361210109004890939860) * r1 + ((-3574478783904289273882377794167407810190840533439041 : ℝ) / 146885425089973875334266430823931164389559985663468197798869122097375585496800) * r2 + ((-40032044583335528084678133 : ℝ) / 104452389606945889119191479945424083487052205085701550) * r3 + ((-40032044583335528084678133 : ℝ) / 98040172772434898896446408524404829432260375343750) * r4 + ((62563010714432759069970549854931293983353293959403557 : ℝ) / 12171292995009013537597763884335968063291996589412875166125978295947288586720) * r5 + ((40032044583335528084678133 : ℝ) / 509128573454739091638404637587270897755712145674110) * r6 + ((62563010714432759069970549854931293983353293959403557 : ℝ) / 2998695081396736439290318259070660795201055226481080487286472111131434052325030880) * r7 + ((494222772633771951662693 : ℝ) / 1548595677056786658170509667385663044429459382288092990) * r8 + ((-209121167462767225802638616621434560207128154985491 : ℝ) / 98040172772434898896446408524404829432260375343750) * (value_432 h H) + (1 : ℝ) * (value_433 h H) + ((-2722179031666815909758113044 : ℝ) / 5111126857800445217183241365) * (value_434 h H) + ((2722179031666815909758113044 : ℝ) / 5111126857800445217183241365) * (value_538 h H) + ((209121167462767225802638616621434560207128154985491 : ℝ) / 98040172772434898896446408524404829432260375343750) * (value_536 h H)

/-- Coordinate 137.2, recovered from skew spokes on cycle 43. -/
theorem value_550 (h : Assignment) (H : Constraints h) :
    h 137 2 = ((-796472063505222428400640036 : ℝ) / 92929579232735367585149843) * (h 1 0) + ((-3227092233895563801660850797 : ℝ) / 1486873267723765881362397488) * (h 1 1) + ((41734606533185916892637085959 : ℝ) / 3717183169309414703405993720) * (h 1 2) + ((796472063505222428400640036 : ℝ) / 92929579232735367585149843) * (h 3 0) + ((3227092233895563801660850797 : ℝ) / 1486873267723765881362397488) * (h 5 1) + ((-38017423363876502189231092239 : ℝ) / 3717183169309414703405993720) * (h 9 2) := by
  have r0 := H 334 0
  change ((1 : ℤ) : ℝ) * (h 112 0 - h 108 0) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 334 1
  change ((1 : ℤ) : ℝ) * (h 112 1 - h 108 1) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 336 1
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 1 - h 108 1) - ((806571564938315825113514976 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 336 2
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 2 - h 108 2) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 346 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 134 2 - h 112 2) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 134 0 - h 112 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 347 1
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 1 - h 112 1) - ((3802895776609746356935872 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 347 2
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 2 - h 112 2) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 396 1
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 1 - h 137 1) - ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 396 2
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 2 - h 137 2) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((217345811153882188417992944310243207829529157479212079350362517009237438227 : ℝ) / 12533481006612661483437232905958747250948864539485218489748370120320500000) * r0 + ((-7482498800449207336572650874060679668945972939620016413 : ℝ) / 266590373210332835236295258351573590445263271092168320) * r1 + ((7482498800449207336572650874060679668945972939620016413 : ℝ) / 370471748517839563388535259707195111347632022022478334521074993042689840365747200) * r2 + ((5313119395064164002386149319 : ℝ) / 5165645449652596698258196826391881946996036324238331200) * r3 + ((1595936225754749298980155599 : ℝ) / 4848532180745871363606076930661475201013604017000000) * r4 + ((-7482498800449207336572650874060679668945972939620016413 : ℝ) / 1805777287986791826669050059930572716299321675811073842828872416271452270320640) * r5 + ((-1595936225754749298980155599 : ℝ) / 25178722178125278713753829349770488034464309749701440) * r6 + ((-7482498800449207336572650874060679668945972939620016413 : ℝ) / 444897306621770351720163581709392583433465648147011214113774771396954579399495490560) * r7 + ((-59108749102027751814079837 : ℝ) / 229755285905152347830388343379400189864443428354015250880) * r8 + ((8336922338083276843392336720420838250659825856988873 : ℝ) / 4848532180745871363606076930661475201013604017000000) * (value_432 h H) + ((5313119395064164002386149319 : ℝ) / 3717183169309414703405993720) * (value_434 h H) + ((-1595936225754749298980155599 : ℝ) / 3717183169309414703405993720) * (value_538 h H) + ((-8336922338083276843392336720420838250659825856988873 : ℝ) / 4848532180745871363606076930661475201013604017000000) * (value_536 h H)

/-- Coordinate 137.3, recovered from skew spokes on cycle 43. -/
theorem value_551 (h : Assignment) (H : Constraints h) :
    h 137 3 = ((377060251595859534768709821 : ℝ) / 92929579232735367585149843) * (h 1 0) + ((118503728264286481403345688 : ℝ) / 92929579232735367585149843) * (h 1 1) + ((-2371339062383857627979294082 : ℝ) / 464647896163676837925749215) * (h 1 2) + h 1 3 + ((-377060251595859534768709821 : ℝ) / 92929579232735367585149843) * (h 3 0) + ((-118503728264286481403345688 : ℝ) / 92929579232735367585149843) * (h 5 1) + ((2371339062383857627979294082 : ℝ) / 464647896163676837925749215) * (h 9 2) := by
  have r0 := H 334 0
  change ((1 : ℤ) : ℝ) * (h 112 0 - h 108 0) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 334 1
  change ((1 : ℤ) : ℝ) * (h 112 1 - h 108 1) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 336 1
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 1 - h 108 1) - ((806571564938315825113514976 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 336 2
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 2 - h 108 2) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 336 3
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 3 - h 108 3) - ((704124656597635355368828288 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 346 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 134 2 - h 112 2) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 134 0 - h 112 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 347 1
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 1 - h 112 1) - ((3802895776609746356935872 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 347 2
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 2 - h 112 2) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 396 1
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 1 - h 137 1) - ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 396 2
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 2 - h 137 2) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-80909418532896461380528453880436342773182140940574538240919440832722161364 : ℝ) / 4308384096023102384931548811423319367513672185448043855851002228860171875) * r0 + ((40962414573575183792565771654500394036117873238634987 : ℝ) / 1347653541044881060477595515564020907581753668204895) * r1 + ((-2409553798445599046621515979676493766830463131684411 : ℝ) / 110164068817480406500699823117948373292169989247601148349151841573031689122600) * r2 + ((-17473681735419259738013202 : ℝ) / 52226194803472944559595739972712041743526102542850775) * r3 + ((1 : ℝ) / 1389666641208934572854063960) * r4 + ((-17473681735419259738013202 : ℝ) / 49020086386217449448223204262202414716130187671875) * r5 + ((2409553798445599046621515979676493766830463131684411 : ℝ) / 536968808603338832541077818426586826321705731885862139682028454232968614120) * r6 + ((17473681735419259738013202 : ℝ) / 254564286727369545819202318793635448877856072837055) * r7 + ((2409553798445599046621515979676493766830463131684411 : ℝ) / 132295371238091313498102276135470329200046554109459433262638475491092678779045480) * r8 + ((647173397608120731037526 : ℝ) / 2322893515585179987255764501078494566644189073432139485) * r9 + ((-91279792536622963072703055731882364106165082901054 : ℝ) / 49020086386217449448223204262202414716130187671875) * (value_432 h H) + ((-2376420716017019324369795472 : ℝ) / 5111126857800445217183241365) * (value_434 h H) + (1 : ℝ) * (value_435 h H) + ((2376420716017019324369795472 : ℝ) / 5111126857800445217183241365) * (value_538 h H) + ((91279792536622963072703055731882364106165082901054 : ℝ) / 49020086386217449448223204262202414716130187671875) * (value_536 h H)

/-- Coordinate 141.0, recovered from skew spokes on cycle 43. -/
theorem value_564 (h : Assignment) (H : Constraints h) :
    h 141 0 = ((2258753901926311137915028019 : ℝ) / 395721527383211771598374440) * (h 1 0) + ((1295134093827935973718659 : ℝ) / 860264189963503851300814) * (h 1 1) + ((-277343704725602265677456865 : ℝ) / 39572152738321177159837444) * (h 1 2) + ((-1863032374543099366316653579 : ℝ) / 395721527383211771598374440) * (h 3 0) + ((-1295134093827935973718659 : ℝ) / 860264189963503851300814) * (h 5 1) + ((277343704725602265677456865 : ℝ) / 39572152738321177159837444) * (h 9 2) := by
  have r0 := H 334 0
  change ((1 : ℤ) : ℝ) * (h 112 0 - h 108 0) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 334 1
  change ((1 : ℤ) : ℝ) * (h 112 1 - h 108 1) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 336 1
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 1 - h 108 1) - ((806571564938315825113514976 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 336 2
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 2 - h 108 2) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 346 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 134 2 - h 112 2) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 134 0 - h 112 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 347 1
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 1 - h 112 1) - ((3802895776609746356935872 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 347 2
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 2 - h 112 2) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 396 1
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 1 - h 137 1) - ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 396 2
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 2 - h 137 2) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-5347893477277454911277637087896792137528701158708435724864755785732416549 : ℝ) / 159533641926202066141522593946011445331207351710182140007694808399875000) * r0 + ((11284712285588890478075419870171512031662405992717303 : ℝ) / 199607159125934591503361643686871155751967207563360) * r1 + ((-11284712285588890478075419870171512031662405992717303 : ℝ) / 277387410383794856290774034333768632318900424142225071835347675563625192505600) * r2 + ((-1344759371634311116420689 : ℝ) / 3867730859296464602262886629442623318131516446087600) * r3 + ((-1344759371634311116420689 : ℝ) / 3630295133597286857946505460353177435365559750000) * r4 + ((226573793154241397155282744829 : ℝ) / 27146573641127104444457183541414477182267540228616960) * r5 + ((27 : ℝ) / 378516243583941694572358160) * r6 + ((11284712285588890478075419870171512031662405992717303 : ℝ) / 333112881789946897846302559645754679092909547209599745766834213675667263624218880) * r7 + ((49805902653122633941507 : ℝ) / 172027216742411660354918106068276481402356076585348240) * r8 + ((-3394518429628239974750442096397450268573454203303 : ℝ) / 3630295133597286857946505460353177435365559750000) * (value_432 h H) + ((-22860909317783288979151713 : ℝ) / 47314530447992711821544770) * (value_434 h H) + ((22860909317783288979151713 : ℝ) / 47314530447992711821544770) * (value_538 h H) + ((7024813563225526832696947556750627703939013953303 : ℝ) / 3630295133597286857946505460353177435365559750000) * (value_536 h H)

/-- Coordinate 141.1, recovered from skew spokes on cycle 43. -/
theorem value_565 (h : Assignment) (H : Constraints h) :
    h 141 1 = ((114320518036606348086814481 : ℝ) / 49465190922901471449796805) * (h 1 0) + ((485082301003056610789154 : ℝ) / 430132094981751925650407) * (h 1 1) + ((-144110868863848355564920998 : ℝ) / 49465190922901471449796805) * (h 1 2) + ((-114320518036606348086814481 : ℝ) / 49465190922901471449796805) * (h 3 0) + ((-54950206021304685138747 : ℝ) / 430132094981751925650407) * (h 5 1) + ((144110868863848355564920998 : ℝ) / 49465190922901471449796805) * (h 9 2) := by
  have r0 := H 334 0
  change ((1 : ℤ) : ℝ) * (h 112 0 - h 108 0) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 334 1
  change ((1 : ℤ) : ℝ) * (h 112 1 - h 108 1) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 336 1
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 1 - h 108 1) - ((806571564938315825113514976 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 336 2
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 2 - h 108 2) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 346 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 134 2 - h 112 2) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 134 0 - h 112 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 347 1
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 1 - h 112 1) - ((3802895776609746356935872 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 347 2
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 2 - h 112 2) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 396 1
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 1 - h 137 1) - ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 396 2
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 2 - h 137 2) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-386503535694785134822214046046814049888573472045946605275278269138539933 : ℝ) / 19941705240775258267690324243251430666400918963772767500961851049984375) * r0 + ((272298742254240801202071340914195172835152238456257 : ℝ) / 8316964963580607979306735153619631489665300315140) * r1 + ((-263981777290660193222764605760575541345486938141117 : ℝ) / 11557808765991452345448918097240359679954184339259377993139486481817716354400) * r2 + ((-94373332691602161431313 : ℝ) / 483466357412058075282860828680327914766439555760950) * r3 + ((-94373332691602161431313 : ℝ) / 453786891699660857243313182544147179420694968750) * r4 + ((272298742254240801202071340914195172835152238456257 : ℝ) / 56335816838991725520184149092759878601737109688961285762117327570006173280) * r5 + ((94373332691602161431313 : ℝ) / 2356542897570931851596731431428360438746561768390) * r6 + ((792738069941922502170464281563289913950411225649 : ℝ) / 41680791014758120351138958914633968855469162563763731952807083793251659612640) * r7 + ((31489266830698085229 : ℝ) / 193724343178391509408691560887698740317968554713230) * r8 + ((-492991594989265800499960262683902486915965835351 : ℝ) / 453786891699660857243313182544147179420694968750) * (value_432 h H) + (1 : ℝ) * (value_433 h H) + ((-6417386623028946977329284 : ℝ) / 23657265223996355910772385) * (value_434 h H) + ((6417386623028946977329284 : ℝ) / 23657265223996355910772385) * (value_538 h H) + ((492991594989265800499960262683902486915965835351 : ℝ) / 453786891699660857243313182544147179420694968750) * (value_536 h H)

/-- Coordinate 141.2, recovered from skew spokes on cycle 43. -/
theorem value_566 (h : Assignment) (H : Constraints h) :
    h 141 2 = ((124284974950167962944205166943 : ℝ) / 53818127724116800937378923840) * (h 1 0) + ((75046433451119088004039581 : ℝ) / 116995929835036523776910704) * (h 1 1) + ((-3936498959634851487470940513 : ℝ) / 1582886109532847086393497760) * (h 1 2) + ((-124284974950167962944205166943 : ℝ) / 53818127724116800937378923840) * (h 3 0) + ((-75046433451119088004039581 : ℝ) / 116995929835036523776910704) * (h 5 1) + ((5519385069167698573864438273 : ℝ) / 1582886109532847086393497760) * (h 9 2) := by
  have r0 := H 334 0
  change ((1 : ℤ) : ℝ) * (h 112 0 - h 108 0) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 334 1
  change ((1 : ℤ) : ℝ) * (h 112 1 - h 108 1) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 336 1
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 1 - h 108 1) - ((806571564938315825113514976 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 336 2
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 2 - h 108 2) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 346 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 134 2 - h 112 2) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 134 0 - h 112 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 347 1
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 1 - h 112 1) - ((3802895776609746356935872 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 347 2
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 2 - h 112 2) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 396 1
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 1 - h 137 1) - ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 396 2
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 2 - h 137 2) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((150548889510122162585978462472766026891200158771389400102666790670488560459 : ℝ) / 21696575301963480995247072776657556565044199832584771041046493942383000000) * r0 + ((-162172766886938068483226667515296405706436897992428131 : ℝ) / 9048857880375701481485727847138159060755846742872320) * r1 + ((23167538126705438354746666787899486529490985427489733 : ℝ) / 1796413705342671450264060412828215904541450365873457608076537327459667913369600) * r2 + ((8282381479951895475809337 : ℝ) / 75144485266331312272536083086313824466555176666844800) * r3 + ((-320539573224278426241692801 : ℝ) / 493720138169231012680724742608032131209716126000000) * r4 + ((-162172766886938068483226667515296405706436897992428131 : ℝ) / 61293368720822997365960354212922747918689975341589878909183652396166716528640) * r5 + ((320539573224278426241692801 : ℝ) / 2563918672557173854537243797394056157356259204008320) * r6 + ((-54057588962312689494408889171765468568812299330809377 : ℝ) / 5033705769270308678566349790202515150737299824500618380476605895543416428099307520) * r7 + ((-715761362464978621366239 : ℝ) / 7798567158989328602756287475095200490240142138535786880) * r8 + ((-1674448818898999518144360297668177946329191340237927 : ℝ) / 493720138169231012680724742608032131209716126000000) * (value_432 h H) + ((57976670359663268330665359 : ℝ) / 378516243583941694572358160) * (value_434 h H) + ((320539573224278426241692801 : ℝ) / 378516243583941694572358160) * (value_538 h H) + ((1674448818898999518144360297668177946329191340237927 : ℝ) / 493720138169231012680724742608032131209716126000000) * (value_536 h H)

/-- Coordinate 141.3, recovered from skew spokes on cycle 43. -/
theorem value_567 (h : Assignment) (H : Constraints h) :
    h 141 3 = ((105973566221906182221802206 : ℝ) / 49465190922901471449796805) * (h 1 0) + ((335616215828377762979568 : ℝ) / 430132094981751925650407) * (h 1 1) + ((-133037823446536300935042744 : ℝ) / 49465190922901471449796805) * (h 1 2) + h 1 3 + ((-105973566221906182221802206 : ℝ) / 49465190922901471449796805) * (h 3 0) + ((-335616215828377762979568 : ℝ) / 430132094981751925650407) * (h 5 1) + ((133037823446536300935042744 : ℝ) / 49465190922901471449796805) * (h 9 2) := by
  have r0 := H 334 0
  change ((1 : ℤ) : ℝ) * (h 112 0 - h 108 0) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 334 1
  change ((1 : ℤ) : ℝ) * (h 112 1 - h 108 1) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 334 3
  change ((1 : ℤ) : ℝ) * (h 112 3 - h 108 3) - ((0 : ℤ) : ℝ) * (h 112 2 - h 108 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 336 1
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 1 - h 108 1) - ((806571564938315825113514976 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 336 2
  change ((1389666641208934572854063960 : ℤ) : ℝ) * (h 137 2 - h 108 2) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 137 0 - h 108 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 346 2
  change ((1304356540935979975475000 : ℤ) : ℝ) * (h 134 2 - h 112 2) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 134 0 - h 112 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 347 1
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 1 - h 112 1) - ((3802895776609746356935872 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 347 2
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 2 - h 112 2) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 347 3
  change ((6773602760824678216044952 : ℤ) : ℝ) * (h 141 3 - h 112 3) - ((3369073632315099153808448 : ℤ) : ℝ) * (h 141 0 - h 112 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 396 1
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 1 - h 137 1) - ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 396 2
  change ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 141 2 - h 137 2) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 141 0 - h 137 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((-342412452877350059925767022189843398350723888570136913691225182859994047 : ℝ) / 19941705240775258267690324243251430666400918963772767500961851049984375) * r0 + ((701602750266148906816888508857623713553793248463709 : ℝ) / 24950894890741823937920205460858894468995900945420) * r1 + (1 : ℝ) * r2 + ((-41270750015655818048052265226919041973752544027277 : ℝ) / 2039613311645550413902750252454181119991914883398713763495203496791361709600) * r3 + ((-83607525801937203265467 : ℝ) / 483466357412058075282860828680327914766439555760950) * r4 + ((-83607525801937203265467 : ℝ) / 453786891699660857243313182544147179420694968750) * r5 + ((41270750015655818048052265226919041973752544027277 : ℝ) / 9941614736292657444738379251663507988541842886287285722726587218236383520) * r6 + ((83607525801937203265467 : ℝ) / 2356542897570931851596731431428360438746561768390) * r7 + ((1 : ℝ) / 6773602760824678216044952) * r8 + ((41270750015655818048052265226919041973752544027277 : ℝ) / 2449359424926080131222812938571725581565511376541174601226722159379906350178080) * r9 + ((3096575029701377898721 : ℝ) / 21503402092801457544364763258534560175294509573168530) * r10 + ((-436752696155139540841591326302927213300213771709 : ℝ) / 453786891699660857243313182544147179420694968750) * (value_432 h H) + (1 : ℝ) * (value_435 h H) + ((-5685311754531729822051756 : ℝ) / 23657265223996355910772385) * (value_434 h H) + ((5685311754531729822051756 : ℝ) / 23657265223996355910772385) * (value_538 h H) + ((436752696155139540841591326302927213300213771709 : ℝ) / 453786891699660857243313182544147179420694968750) * (value_536 h H)

/-- Coordinate 114.0, recovered from skew spokes on cycle 44. -/
theorem value_456 (h : Assignment) (H : Constraints h) :
    h 114 0 = ((54965293097119131924855289 : ℝ) / 31143641414917327246934100) * (h 1 0) + ((1385622525909000961769227 : ℝ) / 2978957004905135649706740) * (h 1 1) + ((-12800136748644181407158081 : ℝ) / 6344075103038714809560650) * (h 1 2) + ((-23821651682201804677921189 : ℝ) / 31143641414917327246934100) * (h 3 0) + ((-1385622525909000961769227 : ℝ) / 2978957004905135649706740) * (h 5 1) + ((12800136748644181407158081 : ℝ) / 6344075103038714809560650) * (h 9 2) := by
  have r0 := H 340 0
  change ((1 : ℤ) : ℝ) * (h 114 0 - h 110 0) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_440 h H)

/-- Coordinate 114.1, recovered from skew spokes on cycle 44. -/
theorem value_457 (h : Assignment) (H : Constraints h) :
    h 114 1 = ((519734538873226253932652 : ℝ) / 338517841466492687466675) * (h 1 0) + ((50182337158358922070838 : ℝ) / 67703568293298537493335) * (h 1 1) + ((-22006194672091771648456 : ℝ) / 12537697832092321758025) * (h 1 2) + ((-519734538873226253932652 : ℝ) / 338517841466492687466675) * (h 3 0) + ((17521231134939615422497 : ℝ) / 67703568293298537493335) * (h 5 1) + ((22006194672091771648456 : ℝ) / 12537697832092321758025) * (h 9 2) := by
  have r0 := H 340 1
  change ((1 : ℤ) : ℝ) * (h 114 1 - h 110 1) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_441 h H)

/-- Coordinate 114.2, recovered from skew spokes on cycle 44. -/
theorem value_458 (h : Assignment) (H : Constraints h) :
    h 114 2 = ((1885502045648956021241156539 : ℝ) / 470615025825417389509226400) * (h 1 0) + ((46486447366095334287530017 : ℝ) / 45015350296344272040012960) * (h 1 1) + ((-232459156312884988920142587 : ℝ) / 50752600824309718476485200) * (h 1 2) + ((-1885502045648956021241156539 : ℝ) / 470615025825417389509226400) * (h 3 0) + ((-46486447366095334287530017 : ℝ) / 45015350296344272040012960) * (h 5 1) + ((283211757137194707396627787 : ℝ) / 50752600824309718476485200) * (h 9 2) := by
  have r0 := H 340 0
  change ((1 : ℤ) : ℝ) * (h 114 0 - h 110 0) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 345 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 114 2 - h 112 2) - ((217336141236379020593247 : ℤ) : ℝ) * (h 114 0 - h 112 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((2977207414196972884839 : ℝ) / 1340985458478613581736) * r0 + ((1 : ℝ) / 97891938468938791466728) * r1 + ((2977207414196972884839 : ℝ) / 1340985458478613581736) * (value_440 h H) + (1 : ℝ) * (value_450 h H) + ((-2977207414196972884839 : ℝ) / 1340985458478613581736) * (value_448 h H)

/-- Coordinate 114.3, recovered from skew spokes on cycle 44. -/
theorem value_459 (h : Assignment) (H : Constraints h) :
    h 114 3 = ((1508564293234293310535119 : ℝ) / 7785910353729331811733525) * (h 1 0) + ((197004103519997441171332 : ℝ) / 744739251226283912426685) * (h 1 1) + ((-702618985889944829564302 : ℝ) / 3172037551519357404780325) * (h 1 2) + h 1 3 + ((-1508564293234293310535119 : ℝ) / 7785910353729331811733525) * (h 3 0) + ((-197004103519997441171332 : ℝ) / 744739251226283912426685) * (h 5 1) + ((702618985889944829564302 : ℝ) / 3172037551519357404780325) * (h 9 2) := by
  have r0 := H 340 3
  change ((1 : ℤ) : ℝ) * (h 114 3 - h 110 3) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_443 h H)

/-- Coordinate 139.0, recovered from skew spokes on cycle 44. -/
theorem value_556 (h : Assignment) (H : Constraints h) :
    h 139 0 = ((4078643275538802490675336547185 : ℝ) / 453072125141249539929630724188) * (h 1 0) + ((1021003474254000833751307629833 : ℝ) / 453072125141249539929630724188) * (h 1 1) + ((-66287825663355286117291959149 : ℝ) / 5993017528323406612825803230) * (h 1 2) + ((-3625571150397552950745705822997 : ℝ) / 453072125141249539929630724188) * (h 3 0) + ((-1021003474254000833751307629833 : ℝ) / 453072125141249539929630724188) * (h 5 1) + ((66287825663355286117291959149 : ℝ) / 5993017528323406612825803230) * (h 9 2) := by
  have r0 := H 340 0
  change ((1 : ℤ) : ℝ) * (h 114 0 - h 110 0) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 340 1
  change ((1 : ℤ) : ℝ) * (h 114 1 - h 110 1) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 342 1
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 1 - h 110 1) - ((5456423068271333707049592784 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 342 2
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 2 - h 110 2) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 345 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 114 2 - h 112 2) - ((217336141236379020593247 : ℤ) : ℝ) * (h 114 0 - h 112 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 351 1
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 1 - h 114 1) - ((3002683007968666256370224 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 351 2
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 2 - h 114 2) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 399 1
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 1 - h 139 1) - ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 399 2
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 2 - h 139 2) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((8308039890949018069739175797080980409282791797739299773878230479837209833 : ℝ) / 738833975193251093414602771025371940277156045689719859973628889610411660) * r0 + ((-45316227117406756943255114565000589125000269697196364591 : ℝ) / 1648482643716499637804205945906607383399008985514844520) * r1 + ((338476643339118932536437979259 : ℝ) / 224193639545443950741372008643298604142265222030018854720) * r2 + ((-3 : ℝ) / 70994207643215739875013361340) * r3 + ((401648633746387087923735447 : ℝ) / 51101180928387788689826975525948011294198353319820) * r4 + ((-45316227117406756943255114565000589125000269697196364591 : ℝ) / 14728230765866882981090058266584870818425464531774606888465308609624765201288480) * r5 + ((401648633746387087923735447 : ℝ) / 4663910516503325484160947829530755214040121385270310) * r6 + ((-45316227117406756943255114565000589125000269697196364591 : ℝ) / 479848553076706621621327014290471085000288034159643045171193224491646095195803725160) * r7 + ((267765755830924725282490298 : ℝ) / 101300726412205168848040856785617446684171500156217078805) * r8 + ((1895807467393030708753234182055443270476884603373 : ℝ) / 700016177101202584792150349670520702660251415340) * (value_440 h H) + ((-13656053547377160989407005198 : ℝ) / 17748551910803934968753340335) * (value_442 h H) + ((13656053547377160989407005198 : ℝ) / 17748551910803934968753340335) * (value_450 h H) + ((-1195791290291828123961083832384922567816633188033 : ℝ) / 700016177101202584792150349670520702660251415340) * (value_448 h H)

/-- Coordinate 139.1, recovered from skew spokes on cycle 44. -/
theorem value_557 (h : Assignment) (H : Constraints h) :
    h 139 1 = ((59937059233222266171502165333 : ℝ) / 16181147326473197854629668721) * (h 1 0) + ((20665430186437121202991110230 : ℝ) / 16181147326473197854629668721) * (h 1 1) + ((-13379951895815089576602050242 : ℝ) / 2996508764161703306412901615) * (h 1 2) + ((-59937059233222266171502165333 : ℝ) / 16181147326473197854629668721) * (h 3 0) + ((-4484282859963923348361441509 : ℝ) / 16181147326473197854629668721) * (h 5 1) + ((13379951895815089576602050242 : ℝ) / 2996508764161703306412901615) * (h 9 2) := by
  have r0 := H 340 0
  change ((1 : ℤ) : ℝ) * (h 114 0 - h 110 0) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 340 1
  change ((1 : ℤ) : ℝ) * (h 114 1 - h 110 1) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 342 1
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 1 - h 110 1) - ((5456423068271333707049592784 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 342 2
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 2 - h 110 2) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 345 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 114 2 - h 112 2) - ((217336141236379020593247 : ℤ) : ℝ) * (h 114 0 - h 112 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 351 1
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 1 - h 114 1) - ((3002683007968666256370224 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 351 2
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 2 - h 114 2) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 399 1
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 1 - h 139 1) - ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 399 2
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 2 - h 139 2) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((177833929979769328680992602406541076140502882564813453625576539616110207 : ℝ) / 52773855370946506672471626501812281448368288977837132855259206400743690) * r0 + ((-88181424980262471957327250655140839384622026544489499 : ℝ) / 10704432751405841803923415233159788203889668737109380) * r1 + ((98885857731668313761250665888300627588511695281598879 : ℝ) / 194907075796661346200733615090339302014473344082500714863071458341971244206076320) * r2 + ((-781573204966291115410083 : ℝ) / 61720187237672973045791136295505894085545904866617790) * r3 + ((781573204966291115410083 : ℝ) / 331825850184336290193681659259402670741547748830) * r4 + ((-88181424980262471957327250655140839384622026544489499 : ℝ) / 95637862116018720656428949783018641678087432024510434340683822140420553255120) * r5 + ((781573204966291115410083 : ℝ) / 30285133224047568078967193698251657234026762242015) * r6 + ((-88181424980262471957327250655140839384622026544489499 : ℝ) / 3115899695303289750787837755132929123378493728309370423189566392802896722050673540) * r7 + ((1042097606621721487213444 : ℝ) / 1315593849509158036987543594618408398495733768262559465) * r8 + ((2326905540563332257776302160707981137018431637 : ℝ) / 4545559591566250550598378893964420147144489710) * (value_440 h H) + (1 : ℝ) * (value_441 h H) + ((-53146977937707795847885644 : ℝ) / 230500674166284869724069355) * (value_442 h H) + ((53146977937707795847885644 : ℝ) / 230500674166284869724069355) * (value_450 h H) + ((-2326905540563332257776302160707981137018431637 : ℝ) / 4545559591566250550598378893964420147144489710) * (value_448 h H)

/-- Coordinate 139.2, recovered from skew spokes on cycle 44. -/
theorem value_558 (h : Assignment) (H : Constraints h) :
    h 139 2 = ((-4250899001679056885007915587155 : ℝ) / 517796714447142331348149399072) * (h 1 0) + ((-1028330136854063252507923764059 : ℝ) / 517796714447142331348149399072) * (h 1 1) + ((512236822229444639308343220177 : ℝ) / 47944140226587252902606425840) * (h 1 2) + ((4250899001679056885007915587155 : ℝ) / 517796714447142331348149399072) * (h 3 0) + ((1028330136854063252507923764059 : ℝ) / 517796714447142331348149399072) * (h 5 1) + ((-464292682002857386405736794337 : ℝ) / 47944140226587252902606425840) * (h 9 2) := by
  have r0 := H 340 0
  change ((1 : ℤ) : ℝ) * (h 114 0 - h 110 0) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 340 1
  change ((1 : ℤ) : ℝ) * (h 114 1 - h 110 1) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 342 1
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 1 - h 110 1) - ((5456423068271333707049592784 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 342 2
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 2 - h 110 2) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 345 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 114 2 - h 112 2) - ((217336141236379020593247 : ℤ) : ℝ) * (h 114 0 - h 112 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 351 1
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 1 - h 114 1) - ((3002683007968666256370224 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 351 2
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 2 - h 114 2) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 399 1
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 1 - h 139 1) - ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 399 2
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 2 - h 139 2) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-3686361942162723770493217663443845281821083399929581786201412988669466647 : ℝ) / 844381685935144106759546024028996503173892623645394125684147302411899040) * r0 + ((341823618135250005584849996709472167906026028309604738273 : ℝ) / 32027662792206278677338858377614086306037888861431264960) * r1 + ((-341823618135250005584849996709472167906026028309604738273 : ℝ) / 583161970783610747832594976350295191627304245494842138870309803359177962664580349440) * r2 + ((13171694706934723429643514461 : ℝ) / 184666800215117535353007079796153635103953347360920427680) * r3 + ((-3029665043618189161784462841 : ℝ) / 992822943751534180259495524504132790858710864499360) * r4 + ((341823618135250005584849996709472167906026028309604738273 : ℝ) / 286148483451128012204035417750791775900837596617335219547325995844138295339319040) * r5 + ((-3029665043618189161784462841 : ℝ) / 90613118606350323692269843545168958444208072628108880) * r6 + ((341823618135250005584849996709472167906026028309604738273 : ℝ) / 9322771888347442934357210563357723937148453235101636306183182647266266992375615231680) * r7 + ((-1009888347872729720594820947 : ℝ) / 984064199432850211666682608774569482074808858660394479820) * r8 + ((-9019941230393468021456497725882592112919767767599 : ℝ) / 13600314297966221647390349650741545080256313212320) * (value_440 h H) + ((13171694706934723429643514461 : ℝ) / 10142029663316534267859051620) * (value_442 h H) + ((-3029665043618189161784462841 : ℝ) / 10142029663316534267859051620) * (value_450 h H) + ((9019941230393468021456497725882592112919767767599 : ℝ) / 13600314297966221647390349650741545080256313212320) * (value_448 h H)

/-- Coordinate 139.3, recovered from skew spokes on cycle 44. -/
theorem value_559 (h : Assignment) (H : Constraints h) :
    h 139 3 = ((435550986958983084455269195813 : ℝ) / 113268031285312384982407681047) * (h 1 0) + ((132166455728534812477523488076 : ℝ) / 113268031285312384982407681047) * (h 1 1) + ((-14335953079860154106054582218 : ℝ) / 2996508764161703306412901615) * (h 1 2) + h 1 3 + ((-435550986958983084455269195813 : ℝ) / 113268031285312384982407681047) * (h 3 0) + ((-132166455728534812477523488076 : ℝ) / 113268031285312384982407681047) * (h 5 1) + ((14335953079860154106054582218 : ℝ) / 2996508764161703306412901615) * (h 9 2) := by
  have r0 := H 340 0
  change ((1 : ℤ) : ℝ) * (h 114 0 - h 110 0) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 340 1
  change ((1 : ℤ) : ℝ) * (h 114 1 - h 110 1) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 342 1
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 1 - h 110 1) - ((5456423068271333707049592784 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 342 2
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 2 - h 110 2) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 342 3
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 3 - h 110 3) - ((9186827508067161043536414976 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 345 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 114 2 - h 112 2) - ((217336141236379020593247 : ℤ) : ℝ) * (h 114 0 - h 112 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 351 1
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 1 - h 114 1) - ((3002683007968666256370224 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 351 2
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 2 - h 114 2) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 399 1
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 1 - h 139 1) - ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 399 2
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 2 - h 139 2) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((1047949117540105672577678701976855087162861225510978581618849337916953768 : ℝ) / 184708493798312773353650692756342985069289011422429964993407222402602915) * r0 + ((-2858020714950418406699175377680167747078608276568662668 : ℝ) / 206060330464562454725525743238325922924876123189355565) * r1 + ((42029716396329682451458461436473055104097180537774451 : ℝ) / 55175900133613689917119442507191640643803115788060864134031258427690388984808370) * r2 + ((-50662651698899785166561112 : ℝ) / 2376227208650409462262958747376976922293517337364784915) * r3 + ((1 : ℝ) / 18208071396502881319209340264) * r4 + ((50662651698899785166561112 : ℝ) / 12775295232096947172456743881487002823549588329955) * r5 + ((-42029716396329682451458461436473055104097180537774451 : ℝ) / 27073953613725887832886136519457483122105633330468027368502405532398465443545) * r6 + ((101325303397799570333122224 : ℝ) / 2331955258251662742080473914765377607020060692635155) * r7 + ((-2509236799780876564266176802177495827110279435091012 : ℝ) / 52661166931157443110330005958128960162454788647897612507813128236572222914377055) * r8 + ((2016423948214916822549696 : ℝ) / 1511951140480674161911057563964439502748828360540553415) * r9 + ((150833222260843304699618722617099250347631780968 : ℝ) / 175004044275300646198037587417630175665062853835) * (value_440 h H) + ((-6890120631050370782652311232 : ℝ) / 17748551910803934968753340335) * (value_442 h H) + (1 : ℝ) * (value_443 h H) + ((6890120631050370782652311232 : ℝ) / 17748551910803934968753340335) * (value_450 h H) + ((-150833222260843304699618722617099250347631780968 : ℝ) / 175004044275300646198037587417630175665062853835) * (value_448 h H)

/-- Coordinate 143.0, recovered from skew spokes on cycle 44. -/
theorem value_572 (h : Assignment) (H : Constraints h) :
    h 143 0 = ((329575769576386775712360349048 : ℝ) / 55690153653248219793162170475) * (h 1 0) + ((2888909663545370771091460211 : ℝ) / 1937048822721677210196945060) * (h 1 1) + ((-14865341638549968439249778579 : ℝ) / 2062598283453637770117117425) * (h 1 2) + ((-273885615923138555919198178573 : ℝ) / 55690153653248219793162170475) * (h 3 0) + ((-2888909663545370771091460211 : ℝ) / 1937048822721677210196945060) * (h 5 1) + ((14865341638549968439249778579 : ℝ) / 2062598283453637770117117425) * (h 9 2) := by
  have r0 := H 340 0
  change ((1 : ℤ) : ℝ) * (h 114 0 - h 110 0) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 340 1
  change ((1 : ℤ) : ℝ) * (h 114 1 - h 110 1) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 342 1
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 1 - h 110 1) - ((5456423068271333707049592784 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 342 2
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 2 - h 110 2) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 345 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 114 2 - h 112 2) - ((217336141236379020593247 : ℤ) : ℝ) * (h 114 0 - h 112 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 351 1
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 1 - h 114 1) - ((3002683007968666256370224 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 351 2
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 2 - h 114 2) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 399 1
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 1 - h 139 1) - ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 399 2
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 2 - h 139 2) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((1009488761380231905089598780455625583763566589618783381772009166395413 : ℝ) / 97193387944490291718218870742787966781101494326843630988132422640360) * r0 + ((-5959061760147749318892068290860634585503628686505871 : ℝ) / 216857397588665019688119605660032231682369031535920) * r1 + ((5959061760147749318892068290860634585503628686505871 : ℝ) / 3948554978154224452988719702256719232686941550788797267796752342685633818282880) * r2 + ((-394165440082830106531479 : ℝ) / 16254782800775501291361981116951789731847503235268680) * r3 + ((394165440082830106531479 : ℝ) / 87390485412150505162284340821935345324151356360) * r4 + ((-45354522397210998597012633947 : ℝ) / 14746303036029221338792133184882191754401094144442560) * r5 + ((3 : ℝ) / 60705233760508402598764660) * r6 + ((-5959061760147749318892068290860634585503628686505871 : ℝ) / 63123933305297605060472279599675370211207498058185559488824805377470934284461360) * r7 + ((131388480027610035510493 : ℝ) / 86619521241320196755069000755865823968558209060435695) * r8 + ((2370642207787561117163567752680817297317968201 : ℝ) / 1197129937152746646058689600300484182522621320) * (value_440 h H) + ((-6700812481408111811035143 : ℝ) / 15176308440127100649691165) * (value_442 h H) + ((6700812481408111811035143 : ℝ) / 15176308440127100649691165) * (value_450 h H) + ((-1173512270634814471104878152380333114795346881 : ℝ) / 1197129937152746646058689600300484182522621320) * (value_448 h H)

/-- Coordinate 143.1, recovered from skew spokes on cycle 44. -/
theorem value_573 (h : Assignment) (H : Constraints h) :
    h 143 1 = ((163233951289965804929195203843 : ℝ) / 55690153653248219793162170475) * (h 1 0) + ((525963403612626633064709654 : ℝ) / 484262205680419302549236265) * (h 1 1) + ((-7217593650578870064146152214 : ℝ) / 2062598283453637770117117425) * (h 1 2) + ((-163233951289965804929195203843 : ℝ) / 55690153653248219793162170475) * (h 3 0) + ((-41701197932207330515473389 : ℝ) / 484262205680419302549236265) * (h 5 1) + ((7217593650578870064146152214 : ℝ) / 2062598283453637770117117425) * (h 9 2) := by
  have r0 := H 340 0
  change ((1 : ℤ) : ℝ) * (h 114 0 - h 110 0) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 340 1
  change ((1 : ℤ) : ℝ) * (h 114 1 - h 110 1) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 342 1
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 1 - h 110 1) - ((5456423068271333707049592784 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 342 2
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 2 - h 110 2) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 345 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 114 2 - h 112 2) - ((217336141236379020593247 : ℤ) : ℝ) * (h 114 0 - h 112 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 351 1
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 1 - h 114 1) - ((3002683007968666256370224 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 351 2
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 2 - h 114 2) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 399 1
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 1 - h 139 1) - ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 399 2
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 2 - h 139 2) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((76651166099197200281023862231618876867080454916593213652069035676707 : ℝ) / 24298346986122572929554717685696991695275373581710907747033105660090) * r0 + ((-40587884592450048048771523825220779588675903635679 : ℝ) / 4928577217924204992911809219546187083690205262180) * r1 + ((45516461810374253041683333044766966672366108897859 : ℝ) / 89739885867141464840652720505834528015612307972472665177198916879218950415520) * r2 + ((-3010711572161095845291 : ℝ) / 369426881835806847530954116294358857541988709892470) * r3 + ((3010711572161095845291 : ℝ) / 1986147395730693299142825927771257848276167190) * r4 + ((-2387522623085296944045383754424751740510347272687 : ℝ) / 2590233077447072964920749937269643178532839974787431463040951724824218960) * r5 + ((3010711572161095845291 : ℝ) / 181272008943499016010912592426499981527596990395) * r6 + ((-45516461810374253041683333044766966672366108897859 : ℝ) / 1434634847847672842283460899992622050254715864958762715655109213124339415555940) * r7 + ((4014282096214794460388 : ℝ) / 7874501931029108795915363705078711269868928096403245) * r8 + ((8963512814646639096751694357764545503443149 : ℝ) / 27207498571653332864970218188647367784605030) * (value_440 h H) + (1 : ℝ) * (value_441 h H) + ((-204728386906954517479788 : ℝ) / 1379664403647918240881015) * (value_442 h H) + ((204728386906954517479788 : ℝ) / 1379664403647918240881015) * (value_450 h H) + ((-8963512814646639096751694357764545503443149 : ℝ) / 27207498571653332864970218188647367784605030) * (value_448 h H)

/-- Coordinate 143.2, recovered from skew spokes on cycle 44. -/
theorem value_574 (h : Assignment) (H : Constraints h) :
    h 143 2 = ((8074956830011493968555468420447 : ℝ) / 3366160398596336840831135637600) * (h 1 0) + ((18599735720609192380853033861 : ℝ) / 29270959987794233398531614240) * (h 1 1) + ((-84863619960320346321878670681 : ℝ) / 33001572535258204321873878800) * (h 1 2) + ((-8074956830011493968555468420447 : ℝ) / 3366160398596336840831135637600) * (h 3 0) + ((-18599735720609192380853033861 : ℝ) / 29270959987794233398531614240) * (h 5 1) + ((117865192495578550643752549481 : ℝ) / 33001572535258204321873878800) * (h 9 2) := by
  have r0 := H 340 0
  change ((1 : ℤ) : ℝ) * (h 114 0 - h 110 0) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 340 1
  change ((1 : ℤ) : ℝ) * (h 114 1 - h 110 1) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 342 1
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 1 - h 110 1) - ((5456423068271333707049592784 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 342 2
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 2 - h 110 2) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 345 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 114 2 - h 112 2) - ((217336141236379020593247 : ℤ) : ℝ) * (h 114 0 - h 112 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 351 1
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 1 - h 114 1) - ((3002683007968666256370224 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 351 2
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 2 - h 114 2) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 399 1
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 1 - h 139 1) - ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 399 2
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 2 - h 139 2) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-1037738234317768590123009156941348636207378194845539228303499181674611 : ℝ) / 734350042247259981870987023389953526790544623802818545243667193282720) * r0 + ((17427980382249694872275024063127500794104083841527237 : ℝ) / 1638478115114357926532459242764687972711232682715840) * r1 + ((-17427980382249694872275024063127500794104083841527237 : ℝ) / 29833526501609695867025882194828545313634669494848690467797684366958122182581760) * r2 + ((10375050721505950475398917 : ℝ) / 1105325230452734087812614715952721701765630219998270240) * r3 + ((50330183039002452123365743 : ℝ) / 5942553008026234351035335175891603482042292232480) * r4 + ((17427980382249694872275024063127500794104083841527237 : ℝ) / 14638846139029768809747669423253681181432708053065323770679440947939897020160) * r5 + ((50330183039002452123365743 : ℝ) / 542365850758949055904650476540087944730570195261840) * r6 + ((17427980382249694872275024063127500794104083841527237 : ℝ) / 476936384973359682679123890308658352706901096439624227248898529518669281260374720) * r7 + ((-1152783413500661163933213 : ℝ) / 1963375814803257793114897350466292009953986072036542420) * r8 + ((149843394101608832973531753740752933517016670377 : ℝ) / 81404835726386771931990892820432924411538249760) * (value_440 h H) + ((10375050721505950475398917 : ℝ) / 60705233760508402598764660) * (value_442 h H) + ((50330183039002452123365743 : ℝ) / 60705233760508402598764660) * (value_450 h H) + ((-149843394101608832973531753740752933517016670377 : ℝ) / 81404835726386771931990892820432924411538249760) * (value_448 h H)

/-- Coordinate 143.3, recovered from skew spokes on cycle 44. -/
theorem value_575 (h : Assignment) (H : Constraints h) :
    h 143 3 = ((125373544643667335704090026622 : ℝ) / 55690153653248219793162170475) * (h 1 0) + ((374310634616781284906585336 : ℝ) / 484262205680419302549236265) * (h 1 1) + ((-5759642033963314397148106256 : ℝ) / 2062598283453637770117117425) * (h 1 2) + h 1 3 + ((-125373544643667335704090026622 : ℝ) / 55690153653248219793162170475) * (h 3 0) + ((-374310634616781284906585336 : ℝ) / 484262205680419302549236265) * (h 5 1) + ((5759642033963314397148106256 : ℝ) / 2062598283453637770117117425) * (h 9 2) := by
  have r0 := H 340 0
  change ((1 : ℤ) : ℝ) * (h 114 0 - h 110 0) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 340 1
  change ((1 : ℤ) : ℝ) * (h 114 1 - h 110 1) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 340 3
  change ((1 : ℤ) : ℝ) * (h 114 3 - h 110 3) - ((0 : ℤ) : ℝ) * (h 114 2 - h 110 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 342 1
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 1 - h 110 1) - ((5456423068271333707049592784 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 342 2
  change ((18208071396502881319209340264 : ℤ) : ℝ) * (h 139 2 - h 110 2) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 139 0 - h 110 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 345 2
  change ((97891938468938791466728 : ℤ) : ℝ) * (h 114 2 - h 112 2) - ((217336141236379020593247 : ℤ) : ℝ) * (h 114 0 - h 112 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 351 1
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 1 - h 114 1) - ((3002683007968666256370224 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 351 2
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 2 - h 114 2) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 351 3
  change ((8934416641877482414713524 : ℤ) : ℝ) * (h 143 3 - h 114 3) - ((4426224833314726983043856 : ℤ) : ℝ) * (h 143 0 - h 114 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 399 1
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 1 - h 139 1) - ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 399 2
  change ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 143 2 - h 139 2) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 143 0 - h 139 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((112990713302207823845084724150696777892099188890186292616166953725233 : ℝ) / 24298346986122572929554717685696991695275373581710907747033105660090) * r0 + ((-738048946094354058574612842382563641545931169027131 : ℝ) / 54214349397166254922029901415008057920592257883980) * r1 + (1 : ℝ) * r2 + ((43414643887903179916153696610739037737995951119243 : ℝ) / 58066984972856241955716466209657635774807963982188195114658122686553438504160) * r3 + ((-48818656249794782901219 : ℝ) / 4063695700193875322840495279237947432961875808817170) * r4 + ((48818656249794782901219 : ℝ) / 21847621353037626290571085205483836331037839090) * r5 + ((-43414643887903179916153696610739037737995951119243 : ℝ) / 28492563851917802614128249309966074963861239722661746093450468973066408560) * r6 + ((48818656249794782901219 : ℝ) / 1993992098378489176120038516691499796803566894345) * r7 + ((1 : ℝ) / 8934416641877482414713524) * r8 + ((-647979759520942983823189501652821458776058971929 : ℝ) / 13855121445412117001859587269463426297455552690558726841269711452473866173060) * r9 + ((971515547259597669676 : ℝ) / 1292828675243585026195059712774116775650122523290085) * r10 + ((145343265338022415187515191827450816399718741 : ℝ) / 299282484288186661514672400075121045630655330) * (value_440 h H) + (1 : ℝ) * (value_443 h H) + ((-3319668624986045237282892 : ℝ) / 15176308440127100649691165) * (value_442 h H) + ((3319668624986045237282892 : ℝ) / 15176308440127100649691165) * (value_450 h H) + ((-145343265338022415187515191827450816399718741 : ℝ) / 299282484288186661514672400075121045630655330) * (value_448 h H)

/-- Coordinate 113.0, recovered from nonplanar cycle 45. -/
theorem value_452 (h : Assignment) (H : Constraints h) :
    h 113 0 = ((-524424025816764199423282393 : ℝ) / 99870641772172291672211820) * (h 1 0) + ((-4764387564147266187978403 : ℝ) / 9552843995599088768646348) * (h 1 1) + ((1099135286985820856325509673 : ℝ) / 183096176582315868065721670) * (h 1 2) + ((624294667588936491095494213 : ℝ) / 99870641772172291672211820) * (h 3 0) + ((4764387564147266187978403 : ℝ) / 9552843995599088768646348) * (h 5 1) + ((-1099135286985820856325509673 : ℝ) / 183096176582315868065721670) * (h 9 2) := by
  have r0 := H 344 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 1 - h 112 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 344 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 2 - h 112 2) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 348 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 1 - h 113 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 348 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 2 - h 113 2) - ((25775781830954580063993 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 349 1
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 1 - h 114 1) - ((18876407383763605568734028 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 349 2
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 2 - h 114 2) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((193365993857710271952903 : ℝ) / 1411030068688931859148591984245184259911785892096) * r0 + ((-7483037529584019792008075 : ℝ) / 4165651268960339275354115306429716767313103203504) * r1 + ((-10542999956231448891039831449033422340834601 : ℝ) / 32957063471124527837028196012265287088571985594664838320401489800448) * r2 + ((215016923510355368360366069134565958235594637675 : ℝ) / 51275011311668929465446430208332486968488902337999488769359642850159504) * r3 + ((-17322148928088270527978443070761912905991249443 : ℝ) / 752163650321814426326337510017889152570523056690406571529414948505710272) * r4 + ((670346879179343207241141274360705634499206811575 : ℝ) / 2220541952972121265956062575530753637919595641626457635801912513419431428) * r5 + ((-17322148928088270527978443070761912905991249443 : ℝ) / 10375221093300969552563176354744001911116072736) * (value_449 h H) + ((24079540079147162459958779282716795839841904893051 : ℝ) / 4165651268960339275354115306429716767313103203504) * (value_448 h H) + ((11395896946048834523099401664131995786486515796775 : ℝ) / 520706408620042409419264413303714595914137900438) * (value_450 h H) + ((17322148928088270527978443070761912905991249443 : ℝ) / 10375221093300969552563176354744001911116072736) * (value_457 h H) + ((-19913888810186823184604663976287079072528801689547 : ℝ) / 4165651268960339275354115306429716767313103203504) * (value_456 h H) + ((-11395896946048834523099401664131995786486515796775 : ℝ) / 520706408620042409419264413303714595914137900438) * (value_458 h H)

/-- Coordinate 113.1, recovered from nonplanar cycle 45. -/
theorem value_453 (h : Assignment) (H : Constraints h) :
    h 113 1 = ((-6109836224447014583212136 : ℝ) / 1920589264849467147542535) * (h 1 0) + ((17126635218530564174956 : ℝ) / 183708538376905553243199) * (h 1 1) + ((25611094310695704965245392 : ℝ) / 7042160637781379540989295) * (h 1 2) + ((6109836224447014583212136 : ℝ) / 1920589264849467147542535) * (h 3 0) + ((166581903158374989068243 : ℝ) / 183708538376905553243199) * (h 5 1) + ((-25611094310695704965245392 : ℝ) / 7042160637781379540989295) * (h 9 2) := by
  have r0 := H 344 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 1 - h 112 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 344 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 2 - h 112 2) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 348 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 1 - h 113 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 348 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 2 - h 113 2) - ((25775781830954580063993 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 349 1
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 1 - h 114 1) - ((18876407383763605568734028 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 349 2
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 2 - h 114 2) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-22330687354138031378279951826364750392791363 : ℝ) / 1215415016493490102034325337672693678782227768012973526586217299315744) * r0 + ((-2996491114781331413045107804852129878845816525 : ℝ) / 3588155361192178499755747228496959647287238594538300521502692982906406) * r1 + ((-2497775933148453563654485534988234451074991 : ℝ) / 16795426576630768993870138352404425150906877274204196451743066917536) * r2 + ((50940348951282634021766832682486207940378880925 : ℝ) / 26130534610754358285275584625400209705095305999172816392077510298638978) * r3 + ((-77431053927602060473289051584635267983324721 : ℝ) / 7232342791555907945445552980941241851639644775869293957013605274093368) * r4 + ((5992982229562662826090215609704259757691633050 : ℝ) / 42702729864848485883770434144822185344607608492816492996190625258065989) * r5 + ((22330687354138031378279951826364750392791363 : ℝ) / 99761741281740091851569003411000018376116084) * (value_449 h H) + ((89016288035114024366069897813115997964182744809 : ℝ) / 40054339124618646878404954869516507378010607726) * (value_448 h H) + ((203761395805130536087067330729944831761515523700 : ℝ) / 20027169562309323439202477434758253689005303863) * (value_450 h H) + ((77431053927602060473289051584635267983324721 : ℝ) / 99761741281740091851569003411000018376116084) * (value_457 h H) + ((-89016288035114024366069897813115997964182744809 : ℝ) / 40054339124618646878404954869516507378010607726) * (value_456 h H) + ((-203761395805130536087067330729944831761515523700 : ℝ) / 20027169562309323439202477434758253689005303863) * (value_458 h H)

/-- Coordinate 113.2, recovered from nonplanar cycle 45. -/
theorem value_454 (h : Assignment) (H : Constraints h) :
    h 113 2 = ((14069096150486344956551728177 : ℝ) / 2716481456203086333484161504) * (h 1 0) + ((1550956070874721031953414451 : ℝ) / 1299186783401476072535903328) * (h 1 1) + ((-1734546100744891843958432241 : ℝ) / 292953882531705388905154672) * (h 1 2) + ((-14069096150486344956551728177 : ℝ) / 2716481456203086333484161504) * (h 3 0) + ((-1550956070874721031953414451 : ℝ) / 1299186783401476072535903328) * (h 5 1) + ((2027499983276597232863586913 : ℝ) / 292953882531705388905154672) * (h 9 2) := by
  have r0 := H 344 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 1 - h 112 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 344 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 2 - h 112 2) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 348 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 1 - h 113 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 348 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 2 - h 113 2) - ((25775781830954580063993 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 349 1
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 1 - h 114 1) - ((18876407383763605568734028 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 349 2
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 2 - h 114 2) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-538681131527151335838120303108603666326897196459 : ℝ) / 17190829993283924003173497576042579392695829550775497560035457481521883136) * r0 + ((981216336610933620440118019901120518977476155263 : ℝ) / 2985345260511892511796781694109470426542982510655866033890240561778129792) * r1 + ((17376810694424236639939364616406569881512812789 : ℝ) / 237554513499865596649299236856408189334426872166344154613453938481629184) * r2 + ((-20846328991346210822836121644748765589930197842975 : ℝ) / 21740604796147626093349286408332974474639294591311783238208488568467629696) * r3 + ((538681131527151335838120303108603666326897196459 : ℝ) / 102294256443766761980381901362432924749591135709895293728000432996776596992) * r4 + ((-20846328991346210822836121644748765589930197842975 : ℝ) / 301993705604208492170024510272182494757065007261198238469060101825042674208) * r5 + ((538681131527151335838120303108603666326897196459 : ℝ) / 1411030068688931859148591984245184259911785892096) * (value_449 h H) + ((-619278601166097264102159731139435340418631004251411 : ℝ) / 566528572578606141448159681674441480354582035676544) * (value_448 h H) + ((-16680677722385871547482006338319048822617094639471 : ℝ) / 4165651268960339275354115306429716767313103203504) * (value_450 h H) + ((-538681131527151335838120303108603666326897196459 : ℝ) / 1411030068688931859148591984245184259911785892096) * (value_457 h H) + ((619278601166097264102159731139435340418631004251411 : ℝ) / 566528572578606141448159681674441480354582035676544) * (value_456 h H) + ((20846328991346210822836121644748765589930197842975 : ℝ) / 4165651268960339275354115306429716767313103203504) * (value_458 h H)

/-- Coordinate 113.3, recovered from nonplanar cycle 45. -/
theorem value_455 (h : Assignment) (H : Constraints h) :
    h 113 3 = ((-88726955960883908139193 : ℝ) / 286984602793598539287965) * (h 1 0) + ((5364791332306573317908 : ℝ) / 27450701136778990714501) * (h 1 1) + ((1115771857151937365366838 : ℝ) / 3156830630729583932167615) * (h 1 2) + h 1 3 + ((88726955960883908139193 : ℝ) / 286984602793598539287965) * (h 3 0) + ((-5364791332306573317908 : ℝ) / 27450701136778990714501) * (h 5 1) + ((-1115771857151937365366838 : ℝ) / 3156830630729583932167615) * (h 9 2) := by
  have r0 := H 344 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 1 - h 112 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 344 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 2 - h 112 2) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 344 3
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 3 - h 112 3) - ((-717306105909058847318400 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 348 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 1 - h 113 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 348 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 2 - h 113 2) - ((25775781830954580063993 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 349 1
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 1 - h 114 1) - ((18876407383763605568734028 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 349 2
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 2 - h 114 2) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((129294132626354577019350417516809216972025 : ℝ) / 16024741596770153475097595729964521119846816413964154001643838631952) * r0 + ((-85060035983729351203286621735000433822973125 : ℝ) / 804241718887902077531460585697594403702312098775825978957500151341091) * r1 + ((-1 : ℝ) / 12183177647841976940712616) * r2 + ((-70903234020904122881579261218895377049175 : ℝ) / 3764492163727586153798479285883750464858438009735423342632066722896) * r3 + ((1446020611723398970455872569495007374990543125 : ℝ) / 5856843964479425132906596553969012520107568586021493329258752308315633) * r4 + ((-129294132626354577019350417516809216972025 : ℝ) / 95355432343029212262466722872450450376587608606795964950483639516444) * r5 + ((340240143934917404813146486940001735291892500 : ℝ) / 19142603042863114361690194616644427913099962427814289963809590632926133) * r6 + ((-2198000254648027809328957097785756688524425 : ℝ) / 22360390287286572311558569730051728256715674) * (value_449 h H) + ((2526865047606644222024404195003578140004765825 : ℝ) / 8977696700345558783090765746615768895071343111) * (value_448 h H) + ((11568164893787191763646980555960058999924345000 : ℝ) / 8977696700345558783090765746615768895071343111) * (value_450 h H) + (1 : ℝ) * (value_451 h H) + ((2198000254648027809328957097785756688524425 : ℝ) / 22360390287286572311558569730051728256715674) * (value_457 h H) + ((-2526865047606644222024404195003578140004765825 : ℝ) / 8977696700345558783090765746615768895071343111) * (value_456 h H) + ((-11568164893787191763646980555960058999924345000 : ℝ) / 8977696700345558783090765746615768895071343111) * (value_458 h H)

/-- Coordinate 115.0, recovered from nonplanar cycle 45. -/
theorem value_460 (h : Assignment) (H : Constraints h) :
    h 115 0 = ((-51019593198921921642827329967 : ℝ) / 15949518144260424813804379860) * (h 1 0) + ((-30068092897903049031194683 : ℝ) / 138691462124003694033081564) * (h 1 1) + ((3240347762322562893878199039 : ℝ) / 886084341347801378544687770) * (h 1 2) + ((66969111343182346456631709827 : ℝ) / 15949518144260424813804379860) * (h 3 0) + ((30068092897903049031194683 : ℝ) / 138691462124003694033081564) * (h 5 1) + ((-3240347762322562893878199039 : ℝ) / 886084341347801378544687770) * (h 9 2) := by
  have r0 := H 344 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 1 - h 112 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 344 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 2 - h 112 2) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 348 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 1 - h 113 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 348 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 2 - h 113 2) - ((25775781830954580063993 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 349 1
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 1 - h 114 1) - ((18876407383763605568734028 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 349 2
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 2 - h 114 2) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((2088671181383921037208824928665330629941930585 : ℝ) / 15870132476767588871626346677385528946142327070890302822842917684065184) * r0 + ((-5910800359409966987420979142912417872057519513 : ℝ) / 4259263495603066130987953336210086812751433368290412154660047760796906) * r1 + ((-67376489722061968942220158989204213869094535 : ℝ) / 219304222144585540682691076348469091595908261796165263001335477540896) * r2 + ((100483606109969438786156645429511103824977831721 : ℝ) / 31017840919574817410308119111036597142596274777795124385751386604690478) * r3 + ((-51917034770829780324335 : ℝ) / 2347333310714778468245233742886864392087510291048) * r4 + ((293843502527374669106526 : ℝ) / 1259965674133667854278691641402508092811678317989) * r5 + ((-110699572613347814972067721219262523386922321005 : ℝ) / 69039215021022896124859815967260717414338537972) * (value_449 h H) + ((11620479483148868819983290099273062305976805297617 : ℝ) / 2519931348267335708557383282805016185623356635978) * (value_448 h H) + ((21302524495313521022665208831056354010895300324852 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_450 h H) + ((110699572613347814972067721219262523386922321005 : ℝ) / 69039215021022896124859815967260717414338537972) * (value_457 h H) + ((-9100548134881533111425906816468046120353448661639 : ℝ) / 2519931348267335708557383282805016185623356635978) * (value_456 h H) + ((-21302524495313521022665208831056354010895300324852 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_458 h H)

/-- Coordinate 115.1, recovered from nonplanar cycle 45. -/
theorem value_461 (h : Assignment) (H : Constraints h) :
    h 115 1 = ((867336605631166208965192568 : ℝ) / 306721502774238938727007305) * (h 1 0) + ((2450485155582961681814836 : ℝ) / 2667143502384686423713107) * (h 1 1) + ((-110172271200970053940784112 : ℝ) / 34080166974915437636334145) * (h 1 2) + ((-867336605631166208965192568 : ℝ) / 306721502774238938727007305) * (h 3 0) + ((216658346801724741898271 : ℝ) / 2667143502384686423713107) * (h 5 1) + ((110172271200970053940784112 : ℝ) / 34080166974915437636334145) * (h 9 2) := by
  have r0 := H 344 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 1 - h 112 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 344 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 2 - h 112 2) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 348 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 1 - h 113 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 348 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 2 - h 113 2) - ((25775781830954580063993 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 349 1
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 1 - h 114 1) - ((18876407383763605568734028 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 349 2
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 2 - h 114 2) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-271922058404884327195812738623736596528632345 : ℝ) / 7935066238383794435813173338692764473071163535445151411421458842032592) * r0 + ((769521318088054231186990028871604136008836441 : ℝ) / 2129631747801533065493976668105043406375716684145206077330023880398453) * r1 + ((8771679303383365393413314149152793436407495 : ℝ) / 109652111072292770341345538174234545797954130898082631500667738770448) * r2 + ((-13081862407496921930178830490817270312150219497 : ℝ) / 15508920459787408705154059555518298571298137388897562192875693302345239) * r3 + ((-20107738415052578721051832836572319091151754701 : ℝ) / 2502538862477561645896816629096302320276649192953880513723244327449727772) * r4 + ((-163138519434667497011641886120780076833873325492 : ℝ) / 2686549072953852943389229616529853961473461633612254080908776998585737167) * r5 + ((14411869095458869341378075147058039616017514285 : ℝ) / 34519607510511448062429907983630358707169268986) * (value_449 h H) + ((-1512858859198645880466744236336765908903108781969 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_448 h H) + ((-5546709660778694898395824128106522612351693066728 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_450 h H) + ((20107738415052578721051832836572319091151754701 : ℝ) / 34519607510511448062429907983630358707169268986) * (value_457 h H) + ((1512858859198645880466744236336765908903108781969 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_456 h H) + ((5546709660778694898395824128106522612351693066728 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_458 h H)

/-- Coordinate 115.2, recovered from nonplanar cycle 45. -/
theorem value_462 (h : Assignment) (H : Constraints h) :
    h 115 2 = ((54378178819898928565889508157 : ℝ) / 10478910471591390215832829280) * (h 1 0) + ((2504841805677907691351358515 : ℝ) / 2095782094318278043166565856) * (h 1 1) + ((-1828407008888257872078476613 : ℝ) / 308203249164452653406847920) * (h 1 2) + ((-54378178819898928565889508157 : ℝ) / 10478910471591390215832829280) * (h 3 0) + ((-2504841805677907691351358515 : ℝ) / 2095782094318278043166565856) * (h 5 1) + ((2136610258052710525485324533 : ℝ) / 308203249164452653406847920) * (h 9 2) := by
  have r0 := H 344 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 1 - h 112 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 344 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 2 - h 112 2) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 348 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 1 - h 113 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 348 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 2 - h 113 2) - ((25775781830954580063993 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 349 1
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 1 - h 114 1) - ((18876407383763605568734028 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 349 2
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 2 - h 114 2) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-16922550627768389790755187467101399668709773915 : ℝ) / 539584504210098021635295787031107984168839120410270295976659201258216256) * r0 + ((2817040671157056207920784212598025253141711211 : ℝ) / 8518526991206132261975906672420173625502866736580824309320095521593812) * r1 + ((545888729928012573895328627971012892539024965 : ℝ) / 7456343552915908383211496595847949114260880901069618942045406236390464) * r2 + ((-47889691409669955534653331614166429303409090587 : ℝ) / 62035681839149634820616238222073194285192549555590248771502773209380956) * r3 + ((896895183271724658910024935756374182441618017495 : ℝ) / 170172642648474191920983530778548557778812145120863874933180614266581488496) * r4 + ((-6336272963558683140951944792504149598973041920211 : ℝ) / 91342668480431000075233806962015034690097695542816638750898417951915063678) * r5 + ((896895183271724658910024935756374182441618017495 : ℝ) / 2347333310714778468245233742886864392087510291048) * (value_449 h H) + ((-94149885403328338509470180812746042814702923593283 : ℝ) / 85677665841089414090951031615370550311194125623252) * (value_448 h H) + ((-5076307289425015286673253151101641506161363602222 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_450 h H) + ((-896895183271724658910024935756374182441618017495 : ℝ) / 2347333310714778468245233742886864392087510291048) * (value_457 h H) + ((94149885403328338509470180812746042814702923593283 : ℝ) / 85677665841089414090951031615370550311194125623252) * (value_456 h H) + ((6336272963558683140951944792504149598973041920211 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_458 h H)

/-- Coordinate 115.3, recovered from nonplanar cycle 45. -/
theorem value_463 (h : Assignment) (H : Constraints h) :
    h 115 3 = ((149823184785024998043208093 : ℝ) / 1329126512021702067817031655) * (h 1 0) + ((2928643917064840870245608 : ℝ) / 11557621843666974502756797) * (h 1 1) + ((-57093268423683249565655886 : ℝ) / 443042170673900689272343885) * (h 1 2) + h 1 3 + ((-149823184785024998043208093 : ℝ) / 1329126512021702067817031655) * (h 3 0) + ((-2928643917064840870245608 : ℝ) / 11557621843666974502756797) * (h 5 1) + ((57093268423683249565655886 : ℝ) / 443042170673900689272343885) * (h 9 2) := by
  have r0 := H 344 1
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 1 - h 112 1) - ((-5663792298235764294550208 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 344 2
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 2 - h 112 2) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 344 3
  change ((-12183177647841976940712616 : ℤ) : ℝ) * (h 113 3 - h 112 3) - ((-717306105909058847318400 : ℤ) : ℝ) * (h 113 0 - h 112 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 348 1
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 1 - h 113 1) - ((15281557418007073892361664 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 348 2
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 2 - h 113 2) - ((25775781830954580063993 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 348 3
  change ((5219017001769721614586424 : ℤ) : ℝ) * (h 115 3 - h 113 3) - ((1072921154218855975526496 : ℤ) : ℝ) * (h 115 0 - h 113 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 349 1
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 1 - h 114 1) - ((18876407383763605568734028 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 349 2
  change ((-72496156328414859987179302 : ℤ) : ℝ) * (h 115 2 - h 114 2) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 115 0 - h 114 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((687972329152577951369732482330278864220120881 : ℝ) / 98954943678668495317199573400168592252416862912610123483608780853582912) * r0 + ((-9824938264218145343539986921992677748265577287 : ℝ) / 451481930533925009884723053638269202151651937038783688393965062644472036) * r1 + ((-1 : ℝ) / 12183177647841976940712616) * r2 + ((-11695529595593825173285452199614740691742054977 : ℝ) / 720633673967108086683322876881069434984154548262199054222388379199384256) * r3 + ((167023950491708470840179777673875521720514813879 : ℝ) / 3287891137474930645492660625769879297115205126446283184889646980097190668) * r4 + ((1 : ℝ) / 5219017001769721614586424) * r5 + ((-687972329152577951369732482330278864220120881 : ℝ) / 588832673524132151975721559787365251829799810106795414993704547635230064) * r6 + ((9824938264218145343539986921992677748265577287 : ℝ) / 2686549072953852943389229616529853961473461633612254080908776998585737167) * r7 + ((-11695529595593825173285452199614740691742054977 : ℝ) / 138078430042045792249719631934521434828677075944) * (value_449 h H) + ((207257213798367542030667600168001071892698679755 : ℝ) / 5039862696534671417114766565610032371246713271956) * (value_448 h H) + ((334047900983416941680359555347751043441029627758 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_450 h H) + (1 : ℝ) * (value_451 h H) + ((11695529595593825173285452199614740691742054977 : ℝ) / 138078430042045792249719631934521434828677075944) * (value_457 h H) + ((-207257213798367542030667600168001071892698679755 : ℝ) / 5039862696534671417114766565610032371246713271956) * (value_456 h H) + ((-334047900983416941680359555347751043441029627758 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_458 h H)

/-- Coordinate 124.0, recovered from skew spokes on cycle 46. -/
theorem value_496 (h : Assignment) (H : Constraints h) :
    h 124 0 = ((-9545790293705793165213571 : ℝ) / 13821623836049824562735500) * (h 1 0) + ((-16401952160911844438037 : ℝ) / 168725508366494513892925) * (h 1 1) + ((480774751631741289653908389 : ℝ) / 504489270015818596539845750) * (h 1 2) + ((23367414129755617727949071 : ℝ) / 13821623836049824562735500) * (h 3 0) + ((16401952160911844438037 : ℝ) / 168725508366494513892925) * (h 5 1) + ((-480774751631741289653908389 : ℝ) / 504489270015818596539845750) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-27717240363677397092657069 : ℝ) / 59376225205767225643557269761513700414609484444000) * r0 + ((-7070833869954043322835181 : ℝ) / 5675668585845396568869444903674103716102377189500) * r1 + ((-3092631635901574695581212263146474984363677099 : ℝ) / 12331678217294918954291228682628821011456627082095099893027429308371964000) * r2 + ((-5522641851082922881729109757127026561358008557 : ℝ) / 8251343513042923712062513309700167000312890179931280075481588728395946500) * r3 + ((21648421451311022869068485842025324890545739693 : ℝ) / 104593698369500186367068358502432718051388971675300329614802374221823102000) * r4 + ((5522641851082922881729109757127026561358008557 : ℝ) / 9997927050025753108616828386261950990206298763080178566120815182968384750) * r5 + ((21648421451311022869068485842025324890545739693 : ℝ) / 218294945609438329571901727064388604465476045750) * (value_373 h H) + ((3531362122061217394818013154062731977365677036773 : ℝ) / 2837834292922698284434722451837051858051188594750) * (value_372 h H) + ((375539645873638755957579463484637806172344581876 : ℝ) / 1418917146461349142217361225918525929025594297375) * (value_374 h H) + ((-21648421451311022869068485842025324890545739693 : ℝ) / 218294945609438329571901727064388604465476045750) * (value_549 h H) + ((-693527829138519110383290702225680119314488442023 : ℝ) / 2837834292922698284434722451837051858051188594750) * (value_548 h H) + ((-375539645873638755957579463484637806172344581876 : ℝ) / 1418917146461349142217361225918525929025594297375) * (value_550 h H)

/-- Coordinate 124.1, recovered from skew spokes on cycle 46. -/
theorem value_497 (h : Assignment) (H : Constraints h) :
    h 124 1 = ((68764358380088094269000213 : ℝ) / 27643247672099649125471000) * (h 1 0) + ((395474070089323488804761 : ℝ) / 337451016732989027785850) * (h 1 1) + ((-3161039314271773420806596667 : ℝ) / 1008978540031637193079691500) * (h 1 2) + ((-68764358380088094269000213 : ℝ) / 27643247672099649125471000) * (h 3 0) + ((-58023053356334461018911 : ℝ) / 337451016732989027785850) * (h 5 1) + ((3161039314271773420806596667 : ℝ) / 1008978540031637193079691500) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-120002361890228715074412627109210117320253128407 : ℝ) / 30917016041921335612922626076410932625406679431675814548814268996712000) * r0 + ((6512243982700322845865023475482811535723446157 : ℝ) / 2955303004007186492411721610245162677428579651557246978930775712921000) * r1 + ((3646800264199548281931693942911755093818700299 : ℝ) / 8221118811529945969527485788419214007637751388063399928684952872247976000) * r2 + ((6512243982700322845865023475482811535723446157 : ℝ) / 5500895675361949141375008873133444666875260119954186716987725818930631000) * r3 + ((-25527601849396837973521857600382285656730902093 : ℝ) / 69729132246333457578045572334955145367592647783533553076534916147882068000) * r4 + ((-6512243982700322845865023475482811535723446157 : ℝ) / 6665284700017168739077885590841300660137532508720119044080543455312256500) * r5 + ((120002361890228715074412627109210117320253128407 : ℝ) / 145529963739625553047934484709592402976984030500) * (value_373 h H) + ((-817801073096370210792463118607667489378551948423 : ℝ) / 1891889528615132189623148301224701238700792396500) * (value_372 h H) + ((-221416295411810976759410798166415592214597169338 : ℝ) / 472972382153783047405787075306175309675198099125) * (value_374 h H) + ((25527601849396837973521857600382285656730902093 : ℝ) / 145529963739625553047934484709592402976984030500) * (value_549 h H) + ((817801073096370210792463118607667489378551948423 : ℝ) / 1891889528615132189623148301224701238700792396500) * (value_548 h H) + ((221416295411810976759410798166415592214597169338 : ℝ) / 472972382153783047405787075306175309675198099125) * (value_550 h H)

/-- Coordinate 124.2, recovered from skew spokes on cycle 46. -/
theorem value_498 (h : Assignment) (H : Constraints h) :
    h 124 2 = ((5738876243940075067449936857 : ℝ) / 3759481683405552281064056000) * (h 1 0) + ((18019105745549530002971079 : ℝ) / 45893338275686507778875600) * (h 1 1) + ((-11343011263264265908812981439 : ℝ) / 8071828320253097544637532000) * (h 1 2) + ((-5738876243940075067449936857 : ℝ) / 3759481683405552281064056000) * (h 3 0) + ((-18019105745549530002971079 : ℝ) / 45893338275686507778875600) * (h 5 1) + ((19414839583517363453450513439 : ℝ) / 8071828320253097544637532000) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((23782851670853177640873573339979215304963070090831 : ℝ) / 12614142545103904930072431439175660511165925208123732335916221750658496000) * r0 + ((391479186150561539799228958036451098016471702419 : ℝ) / 1205763625634932088903982416980026372390860497835356767403756490871768000) * r1 + ((3397550238693311091553367619997030757851867155833 : ℝ) / 3354216475104217955567214201675039315116202566329867170903460771877174208000) * r2 + ((6067147771995958108668673861710554814118848891919 : ℝ) / 2244365435547675249681003620238445424085106128941308180530992134123697448000) * r3 + ((-23782851670853177640873573339979215304963070090831 : ℝ) / 28449485956504050691842593512661699309977800295681689655226245788335883744000) * r4 + ((-6067147771995958108668673861710554814118848891919 : ℝ) / 2719436157607004845543777321063250669336113263557808569984861729767400652000) * r5 + ((-23782851670853177640873573339979215304963070090831 : ℝ) / 59376225205767225643557269761513700414609484444000) * (value_373 h H) + ((-761906337009682047322800895110567244910535291380941 : ℝ) / 771890927674973933366244506899678105389923297772000) * (value_372 h H) + ((-391479186150561539799228958036451098016471702419 : ℝ) / 5675668585845396568869444903674103716102377189500) * (value_374 h H) + ((23782851670853177640873573339979215304963070090831 : ℝ) / 59376225205767225643557269761513700414609484444000) * (value_549 h H) + ((761906337009682047322800895110567244910535291380941 : ℝ) / 771890927674973933366244506899678105389923297772000) * (value_548 h H) + ((6067147771995958108668673861710554814118848891919 : ℝ) / 5675668585845396568869444903674103716102377189500) * (value_550 h H)

/-- Coordinate 124.3, recovered from skew spokes on cycle 46. -/
theorem value_499 (h : Assignment) (H : Constraints h) :
    h 124 3 = ((-8329980296380684811405877 : ℝ) / 6910811918024912281367750) * (h 1 0) + ((-9833358418001256641538 : ℝ) / 168725508366494513892925) * (h 1 1) + ((372304208406275240464072143 : ℝ) / 252244635007909298269922875) * (h 1 2) + h 1 3 + ((8329980296380684811405877 : ℝ) / 6910811918024912281367750) * (h 3 0) + ((9833358418001256641538 : ℝ) / 168725508366494513892925) * (h 5 1) + ((-372304208406275240464072143 : ℝ) / 252244635007909298269922875) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 280 3
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 3 - h 93 3) - ((-127365404271254371738016 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-381727673464889838617602020562990469618620073 : ℝ) / 1363986001849470688805409973959305851120882916103344759506511867502000) * r0 + ((-1655477232319071302030650006045099624580294009 : ℝ) / 2216477253005389869308791207683872008071434738667935234198081784690750) * r1 + ((-1 : ℝ) / 212444332750858175578384) * r2 + ((-54532524780698548373943145794712924231231439 : ℝ) / 362696418155732910420330255371435912101665502414561761559630273775646000) * r3 + ((-1655477232319071302030650006045099624580294009 : ℝ) / 4125671756521461856031256654850083500156445089965640037740794364197973250) * r4 + ((381727673464889838617602020562990469618620073 : ℝ) / 3076285246161770187266716426542138766217322696332362635729481594759503000) * r5 + ((1655477232319071302030650006045099624580294009 : ℝ) / 4998963525012876554308414193130975495103149381540089283060407591484192375) * r6 + ((6489370448903127256499234349570837983516541241 : ℝ) / 109147472804719164785950863532194302232738022875) * (value_373 h H) + ((207893171796638798183215346544220358180924533451 : ℝ) / 1418917146461349142217361225918525929025594297375) * (value_372 h H) + ((225144903595393697076168400822133548942919985224 : ℝ) / 1418917146461349142217361225918525929025594297375) * (value_374 h H) + (1 : ℝ) * (value_375 h H) + ((-6489370448903127256499234349570837983516541241 : ℝ) / 109147472804719164785950863532194302232738022875) * (value_549 h H) + ((-207893171796638798183215346544220358180924533451 : ℝ) / 1418917146461349142217361225918525929025594297375) * (value_548 h H) + ((-225144903595393697076168400822133548942919985224 : ℝ) / 1418917146461349142217361225918525929025594297375) * (value_550 h H)

/-- Coordinate 125.0, recovered from skew spokes on cycle 46. -/
theorem value_500 (h : Assignment) (H : Constraints h) :
    h 125 0 = ((201456234728327216730076966 : ℝ) / 31979186935482304481556645) * (h 1 0) + ((33569999458194540553426690 : ℝ) / 20299831706871375888292479) * (h 1 1) + ((-154529642813639551120678656 : ℝ) / 19952826036668446385928505) * (h 1 2) + ((-169477047792844912248520321 : ℝ) / 31979186935482304481556645) * (h 3 0) + ((-33569999458194540553426690 : ℝ) / 20299831706871375888292479) * (h 5 1) + ((154529642813639551120678656 : ℝ) / 19952826036668446385928505) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-7029915616690198549779752986054290628971820809823 : ℝ) / 1046168873902858239734790175569558028387104085525731489179133947426334870) * r0 + ((119456251844757316554880824591677542624993064869 : ℝ) / 30769672761848771756905593399104647893738355456639161446445116100774555) * r1 + ((-1004273659527171221397107569436327232710260115689 : ℝ) / 278185921876094460272683795356918876214991241172538640144201584999228325510) * r2 + ((119456251844757316554880824591677542624993064869 : ℝ) / 57273572150960624173787840220542121573674667300228543559100326323370537605) * r3 + ((1995387195123100707253703 : ℝ) / 669723522432791186013458546837302228486986295649355) * r4 + ((-67813466990277639241018 : ℝ) / 39395501319575952118438738049253072263940370332315) * r5 + ((56239324933521588398238023888434325031774566478584 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_373 h H) + ((-31758790244986427261219470608293115879208312607747 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_372 h H) + ((-32492100501773990102927584288936291593998113644368 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_374 h H) + ((-56239324933521588398238023888434325031774566478584 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_549 h H) + ((71154291564562379379658208657546188143148682940062 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_548 h H) + ((32492100501773990102927584288936291593998113644368 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_550 h H)

/-- Coordinate 125.1, recovered from skew spokes on cycle 46. -/
theorem value_501 (h : Assignment) (H : Constraints h) :
    h 125 1 = ((85289296303667014747598497 : ℝ) / 31979186935482304481556645) * (h 1 0) + ((24702794285873566689225010 : ℝ) / 20299831706871375888292479) * (h 1 1) + ((-13393165800162739382713734 : ℝ) / 3990565207333689277185701) * (h 1 2) + ((-85289296303667014747598497 : ℝ) / 31979186935482304481556645) * (h 3 0) + ((-4402962579002190800932531 : ℝ) / 20299831706871375888292479) * (h 5 1) + ((13393165800162739382713734 : ℝ) / 3990565207333689277185701) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-2114288574982608763582093618008343891260973855808 : ℝ) / 523084436951429119867395087784779014193552042762865744589566973713167435) * r0 + ((71854344278609529760244010788407116212000011648 : ℝ) / 30769672761848771756905593399104647893738355456639161446445116100774555) * r1 + ((-302041224997515537654584802572620555894424836544 : ℝ) / 139092960938047230136341897678459438107495620586269320072100792499614162755) * r2 + ((71854344278609529760244010788407116212000011648 : ℝ) / 57273572150960624173787840220542121573674667300228543559100326323370537605) * r3 + ((-5566884119854211901125240161119570003764788639387 : ℝ) / 18875934899139581402154106470082902471440173797265030781003097824063815228440) * r4 + ((-143708688557219059520488021576814232424000023296 : ℝ) / 138793638964261627957015488750609576995883630862242873389728660471057464915) * r5 + ((33828617199721740217313497888133502260175581692928 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_373 h H) + ((-19103286876111316073586366167518714191662959965824 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_372 h H) + ((-19544381643781792094786370934446735609664003168256 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_374 h H) + ((5566884119854211901125240161119570003764788639387 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_549 h H) + ((19103286876111316073586366167518714191662959965824 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_548 h H) + ((19544381643781792094786370934446735609664003168256 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_550 h H)

/-- Coordinate 125.2, recovered from skew spokes on cycle 46. -/
theorem value_502 (h : Assignment) (H : Constraints h) :
    h 125 2 = ((-1206980366386691997475730201 : ℝ) / 241620523512532967193983540) * (h 1 0) + ((-380670708372338388420360203 : ℝ) / 306753012459389680089753016) * (h 1 1) + ((535508976048016260738090661 : ℝ) / 79811304146673785543714020) * (h 1 2) + ((1206980366386691997475730201 : ℝ) / 241620523512532967193983540) * (h 3 0) + ((380670708372338388420360203 : ℝ) / 306753012459389680089753016) * (h 5 1) + ((-455697671901342475194376641 : ℝ) / 79811304146673785543714020) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((122032746562821944089709163691988107803857589910421 : ℝ) / 15808774094532080067103495986384432428960683959055498058706912983331282480) * r0 + ((-2073648575824479953463595042745149215720727847063 : ℝ) / 464963943956825884326573411364248012616490704678102884079615087745037720) * r1 + ((17433249508974563441387023384569729686265369987203 : ℝ) / 4203698375016538510787221796504551907248756533273917228845712839988339141040) * r2 + ((-2073648575824479953463595042745149215720727847063 : ℝ) / 865467312503404987515016252221525392668861639203453547115293819997599234920) * r3 + ((-122032746562821944089709163691988107803857589910421 : ℝ) / 35654543698374764870735534443489926890498106061500613697450295889898317653720) * r4 + ((-229980772748368106232669697760042931218585453909 : ℝ) / 2097326099904397933572678496675878052382241533029447864555899758229312803160) * r5 + ((-122032746562821944089709163691988107803857589910421 : ℝ) / 74413724714754576223717616315255803165220699516595) * (value_373 h H) + ((551302833835856686708975518416131143893223631831969 : ℝ) / 595309797718036609789740930522046425321765596132760) * (value_372 h H) + ((4147297151648959906927190085490298431441455694126 : ℝ) / 4377277924397328013159859783250341362660041148035) * (value_374 h H) + ((122032746562821944089709163691988107803857589910421 : ℝ) / 74413724714754576223717616315255803165220699516595) * (value_549 h H) + ((-551302833835856686708975518416131143893223631831969 : ℝ) / 595309797718036609789740930522046425321765596132760) * (value_548 h H) + ((229980772748368106232669697760042931218585453909 : ℝ) / 4377277924397328013159859783250341362660041148035) * (value_550 h H)

/-- Coordinate 125.3, recovered from skew spokes on cycle 46. -/
theorem value_503 (h : Assignment) (H : Constraints h) :
    h 125 3 = ((2699812471334852541906743 : ℝ) / 1102730583982148430398505) * (h 1 0) + ((599816457482315935619492 : ℝ) / 699994196788668134079051) * (h 1 1) + ((-2112356982453003366864414 : ℝ) / 688028484023049875376845) * (h 1 2) + h 1 3 + ((-2699812471334852541906743 : ℝ) / 1102730583982148430398505) * (h 3 0) + ((-599816457482315935619492 : ℝ) / 699994196788668134079051) * (h 5 1) + ((2112356982453003366864414 : ℝ) / 688028484023049875376845) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 280 3
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 3 - h 93 3) - ((-127365404271254371738016 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 364 3
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 3 - h 124 3) - ((-206686098914908403040993376 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((-3764619142059369560538456222010531733905388546 : ℝ) / 1061023198684440405410537703417401651508219153677212463670521244854295) * r0 + ((2051431064240502644355188853490551722323241522 : ℝ) / 1061023198684440405410537703417401651508219153677212463670521244854295) * r1 + ((-1 : ℝ) / 212444332750858175578384) * r2 + ((-3764619142059369560538456222010531733905388546 : ℝ) / 1974950763826228419785787593811797295643954044835467019279321597357604745) * r3 + ((2051431064240502644355188853490551722323241522 : ℝ) / 1974950763826228419785787593811797295643954044835467019279321597357604745) * r4 + ((-1 : ℝ) / 395436308798036478554666224) * r5 + ((203492926597803760029105741730299012643534516 : ℝ) / 129351014878156223631887687558816008383861724941512463550539292144508355) * r6 + ((-110888165634621764559739938026516309314769812 : ℝ) / 129351014878156223631887687558816008383861724941512463550539292144508355) * r7 + ((1023976406640148520466460092386864631622265684512 : ℝ) / 1358465562743998348911680622388036974618633459735) * (value_373 h H) + ((-1256930456321226603173715500756702484687331482796 : ℝ) / 1358465562743998348911680622388036974618633459735) * (value_372 h H) + ((-557989249473416719264611368149430068471921693984 : ℝ) / 1358465562743998348911680622388036974618633459735) * (value_374 h H) + (1 : ℝ) * (value_375 h H) + ((-1023976406640148520466460092386864631622265684512 : ℝ) / 1358465562743998348911680622388036974618633459735) * (value_549 h H) + ((1256930456321226603173715500756702484687331482796 : ℝ) / 1358465562743998348911680622388036974618633459735) * (value_548 h H) + ((557989249473416719264611368149430068471921693984 : ℝ) / 1358465562743998348911680622388036974618633459735) * (value_550 h H)

/-- Coordinate 126.0, recovered from skew spokes on cycle 46. -/
theorem value_504 (h : Assignment) (H : Constraints h) :
    h 126 0 = ((-82173261632986900318333999 : ℝ) / 141586781036886034142974850) * (h 1 0) + ((-240561965026707051757876 : ℝ) / 3456801008592869729912095) * (h 1 1) + ((4215936139788936757521194181 : ℝ) / 5167917507846340246218582025) * (h 1 2) + ((223760042669872934461308849 : ℝ) / 141586781036886034142974850) * (h 3 0) + ((240561965026707051757876 : ℝ) / 3456801008592869729912095) * (h 5 1) + ((-4215936139788936757521194181 : ℝ) / 5167917507846340246218582025) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 365 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 1 - h 124 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 365 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 2 - h 124 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 368 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 1 - h 125 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 368 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 2 - h 125 2) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 372 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 1 - h 126 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 372 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 2 - h 126 2) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((-1031778414857513748633231503 : ℝ) / 1824725234182424223245435084338643204669363744372400) * r0 + ((-203188321104670251960114097 : ℝ) / 174422265032143491927872471297076188681630357917950) * r1 + ((-2204011855195549877372272611385541109030733055249200370069833270360499461 : ℝ) / 12890228172126446744900908333700820376482130199336175143149972055863660484643072690069535302368302800) * r2 + ((-15517058435700926999704783602080493105609436060288847767290258800520829043 : ℝ) / 8625079144584607748426343076226284222499072412791117191372407772673478706636173638208292003790555550) * r3 + ((-54145133338315036589774187 : ℝ) / 219050352175370363886433048070743418539639152961480) * r4 + ((45725570889250235206517378 : ℝ) / 20938636604998637724438453124409297360406683738965) * r5 + ((-579312385362841659383848707577667094876545043 : ℝ) / 59507256719988440148419457251648386376734134300982676782433905547810540) * r6 + ((1214267299652353866809245466786998823818937144644 : ℝ) / 14118096656817257425212516232953579667880173362908140066632444091218050615) * r7 + ((805865723864495006214237370188588892222683803791 : ℝ) / 3214329642712859858103878583483628265190280770765449445767859647555002834200) * r8 + ((158699291543561712652300342861445759834160319409 : ℝ) / 307252098200493957024635452832993878290247426617285608786633642780992917975) * r9 + ((-42289804131487441135020955653169697925987788139 : ℝ) / 482497307128790307208867671858568023787772598614911417355157088709717056360) * r10 + ((35713744107422172553213101964323494818204033666 : ℝ) / 46121066122604955836141762751186649332654733691131238423654721714899424505) * r11 + ((805865723864495006214237370188588892222683803791 : ℝ) / 6708548655082441997225864280656776487755013766075) * (value_373 h H) + ((105703380630219495989816162538570145661416115299826 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_372 h H) + ((21583103649924392920712846629156623337445803439624 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_374 h H) + ((-805865723864495006214237370188588892222683803791 : ℝ) / 6708548655082441997225864280656776487755013766075) * (value_549 h H) + ((-18492248114147750025879926890032051320600936340851 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_548 h H) + ((-21583103649924392920712846629156623337445803439624 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_550 h H)

/-- Coordinate 126.1, recovered from skew spokes on cycle 46. -/
theorem value_505 (h : Assignment) (H : Constraints h) :
    h 126 1 = ((-368427272927502107194965529 : ℝ) / 141586781036886034142974850) * (h 1 0) + ((-355785217299252588876116 : ℝ) / 3456801008592869729912095) * (h 1 1) + ((16537522489458809905008878751 : ℝ) / 5167917507846340246218582025) * (h 1 2) + ((368427272927502107194965529 : ℝ) / 141586781036886034142974850) * (h 3 0) + ((3812586225892122318788211 : ℝ) / 3456801008592869729912095) * (h 5 1) + ((-16537522489458809905008878751 : ℝ) / 5167917507846340246218582025) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 365 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 1 - h 124 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 365 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 2 - h 124 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 368 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 1 - h 125 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 368 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 2 - h 125 2) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 372 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 1 - h 126 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 372 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 2 - h 126 2) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((318941984643491542758080435169736872204451599883 : ℝ) / 475064380918552132987806222709453350303179786755545377496215765067507600) * r0 + ((-69489617249844888865723226945149686765141783433 : ℝ) / 45410565823096895065010888935462452602509832557515366966550036366747050) * r1 + ((-13921385505541737345394279437648789029094301421577846664079254372755244007 : ℝ) / 4296742724042148914966969444566940125494043399778725047716657351954553494881024230023178434122767600) * r2 + ((153327496248766545379756974048630909957029786749065605343725116368512815559 : ℝ) / 2875026381528202582808781025408761407499690804263705730457469257557826235545391212736097334596851850) * r3 + ((1146660862160249442910091728589994483428749210981 : ℝ) / 171088257010062689715629717020461075644214785239819563497034448328943560) * r4 + ((-1648458330225551161103213289843397930120900279449 : ℝ) / 16354024567138345340464605303426426348344060353806281804863586972619605) * r5 + ((53479261350015935974816478469704061042733575579 : ℝ) / 119014513439976880296838914503296772753468268601965353564867811095621080) * r6 + ((-56047583227668739477509251854675529624110609501266 : ℝ) / 14118096656817257425212516232953579667880173362908140066632444091218050615) * r7 + ((-638781217417743052125008798847165592030697380477 : ℝ) / 267860803559404988175323215290302355432523397563787453813988303962916902850) * r8 + ((69489617249844888865723226945149686765141783433 : ℝ) / 102417366066831319008211817610997959430082475539095202928877880926997639325) * r9 + ((3903986078551163326161602928288396456119551017267 : ℝ) / 964994614257580614417735343717136047575545197229822834710314177419434112720) * r10 + ((-1648458330225551161103213289843397930120900279449 : ℝ) / 46121066122604955836141762751186649332654733691131238423654721714899424505) * r11 + ((-318941984643491542758080435169736872204451599883 : ℝ) / 2236182885027480665741954760218925495918337922025) * (value_373 h H) + ((30836662313597510814675288690922642166550991128187 : ℝ) / 29070377505357248654645411882846031446938392986325) * (value_372 h H) + ((9450587945978904885738358864540357400059282546888 : ℝ) / 29070377505357248654645411882846031446938392986325) * (value_374 h H) + ((2555124869670972208500035195388662368122789521908 : ℝ) / 2236182885027480665741954760218925495918337922025) * (value_549 h H) + ((-30836662313597510814675288690922642166550991128187 : ℝ) / 29070377505357248654645411882846031446938392986325) * (value_548 h H) + ((-9450587945978904885738358864540357400059282546888 : ℝ) / 29070377505357248654645411882846031446938392986325) * (value_550 h H)

/-- Coordinate 126.2, recovered from skew spokes on cycle 46. -/
theorem value_506 (h : Assignment) (H : Constraints h) :
    h 126 2 = ((41636451361200205751305460393 : ℝ) / 38511604442033001286889159200) * (h 1 0) + ((66070054400348276677560623 : ℝ) / 235062468584315141634022460) * (h 1 1) + ((-70374903524614779867548090651 : ℝ) / 82686680125541443939497312400) * (h 1 2) + ((-41636451361200205751305460393 : ℝ) / 38511604442033001286889159200) * (h 3 0) + ((-66070054400348276677560623 : ℝ) / 235062468584315141634022460) * (h 5 1) + ((153061583650156223807045403051 : ℝ) / 82686680125541443939497312400) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 365 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 1 - h 124 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 365 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 2 - h 124 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 368 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 1 - h 125 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 368 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 2 - h 125 2) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 372 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 1 - h 126 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 372 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 2 - h 126 2) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((885320207775857739990271065949769120648526800985797 : ℝ) / 387652534829538540518049877730913933847394705992525028036912064295086201600) * r0 + ((-75986734727941350471164937687076669829699289347 : ℝ) / 37055021711647066373048885371337361323648023366932539444704829675265592800) * r1 + ((2421316822143782381214397765646587282430409388324666468924374593609619761687 : ℝ) / 3506142062818393514613047066766623142403139414219439638936792399194915651822915771698913602244178361600) * r2 + ((17046965755643454764276579094204176969562120277737948036932066752220169707281 : ℝ) / 2346021527327013307571965316733549308519747696279183876053294914167186208205039229592655425031031109600) * r3 + ((46459375391903708558045666280726220218010461987513 : ℝ) / 46536005906737051602651283029565412575226421585230921271193369945472648320) * r4 + ((-60173584087332982727247144198087240422286895401387 : ℝ) / 4448294682261629932606372642531987966749584416235308650922895656552532560) * r5 + ((636429799889091898055420086037345482438499479281 : ℝ) / 16185973827836855720370092372448361094471684529867288084822022309004466880) * r6 + ((-19617473741167172501404345536838971530940105831211 : ℝ) / 56472386627269029700850064931814318671520693451632560266529776364872202460) * r7 + ((-885320207775857739990271065949769120648526800985797 : ℝ) / 874297662817897881404254974707546888131756369648202249248857824134960770902400) * r8 + ((-174346278297415550577401306359389112011800658628603 : ℝ) / 83572570710534356310700843170574334894947300039901685589964350836430073689200) * r9 + ((46459375391903708558045666280726220218010461987513 : ℝ) / 131239267539030963560812006745530502470274146823255905520602728129043039329920) * r10 + ((-19617473741167172501404345536838971530940105831211 : ℝ) / 6272464992674273993715279734161384309241043781993848425617042153226321732680) * r11 + ((-885320207775857739990271065949769120648526800985797 : ℝ) / 1824725234182424223245435084338643204669363744372400) * (value_373 h H) + ((-1195029107341698040143874483797036148538401165350401 : ℝ) / 1395378120257147935422979770376609509453042863343600) * (value_372 h H) + ((75986734727941350471164937687076669829699289347 : ℝ) / 174422265032143491927872471297076188681630357917950) * (value_374 h H) + ((885320207775857739990271065949769120648526800985797 : ℝ) / 1824725234182424223245435084338643204669363744372400) * (value_549 h H) + ((1195029107341698040143874483797036148538401165350401 : ℝ) / 1395378120257147935422979770376609509453042863343600) * (value_548 h H) + ((174346278297415550577401306359389112011800658628603 : ℝ) / 174422265032143491927872471297076188681630357917950) * (value_550 h H)

/-- Coordinate 126.3, recovered from skew spokes on cycle 46. -/
theorem value_507 (h : Assignment) (H : Constraints h) :
    h 126 3 = ((-80651127640777593610839848 : ℝ) / 70793390518443017071487425) * (h 1 0) + ((-144222590130685097409224 : ℝ) / 3456801008592869729912095) * (h 1 1) + ((7202570310470526750271528524 : ℝ) / 5167917507846340246218582025) * (h 1 2) + h 1 3 + ((80651127640777593610839848 : ℝ) / 70793390518443017071487425) * (h 3 0) + ((144222590130685097409224 : ℝ) / 3456801008592869729912095) * (h 5 1) + ((-7202570310470526750271528524 : ℝ) / 5167917507846340246218582025) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 280 3
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 3 - h 93 3) - ((-127365404271254371738016 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 365 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 1 - h 124 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 365 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 2 - h 124 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 365 3
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 3 - h 124 3) - ((-127365404271254371738016 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 368 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 1 - h 125 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 368 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 2 - h 125 2) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 372 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 1 - h 126 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  have r13 := H 372 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 2 - h 126 2) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r13
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r13
  linear_combination ((-14209869693629027543819950620022102049627226851 : ℝ) / 41917445375166364675394666709657648556162922360783415661430802800074200) * r0 + ((-47571990185098848002631084920472013126035941933 : ℝ) / 68115848734645342597516333403193678903764748836273050449825054550120575) * r1 + ((-1 : ℝ) / 212444332750858175578384) * r2 + ((-38863448758379658218672882094624904523069089077563130591773090386834721 : ℝ) / 379124358003719021908850245108847658131827358804005151269116825172460602489502137943221626540244200) * r3 + ((-4651421845838208302180100366856294712436428528448251149177289899813017191 : ℝ) / 4312539572292303874213171538113142111249536206395558595686203886336739353318086819104146001895277775) * r4 + ((-745698183061793624663399845570679084186868879 : ℝ) / 5032007559119490873989109324131208107182787801171163632265719068498340) * r5 + ((21411234639129619368010277279182132559310173684 : ℝ) / 16354024567138345340464605303426426348344060353806281804863586972619605) * r6 + ((-1 : ℝ) / 212444332750858175578384) * r7 + ((-173655741260965638620243799653445814125709191 : ℝ) / 29753628359994220074209728625824193188367067150491338391216952773905270) * r8 + ((727981977730407058512349427492192507016545905256 : ℝ) / 14118096656817257425212516232953579667880173362908140066632444091218050615) * r9 + ((14209869693629027543819950620022102049627226851 : ℝ) / 94539107138613525238349370102459654858537669728395571934348813163382436300) * r10 + ((95143980370197696005262169840944026252071883866 : ℝ) / 307252098200493957024635452832993878290247426617285608786633642780992917975) * r11 + ((-1660797735104217426867260235124006869013071 : ℝ) / 31606007279496286336228722118339317685560893398068349099643461857049460) * r12 + ((47686491401179553158152065209759760711158516 : ℝ) / 102719523658362930592743346884602782478072903543722134573841251035410745) * r13 + ((483135569583386936489878321080751469687325712934 : ℝ) / 6708548655082441997225864280656776487755013766075) * (value_373 h H) + ((11086540301853522820453047785488006741428480839374 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_372 h H) + ((12939581330346886656715655098368387570281776205776 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_374 h H) + (1 : ℝ) * (value_375 h H) + ((-483135569583386936489878321080751469687325712934 : ℝ) / 6708548655082441997225864280656776487755013766075) * (value_549 h H) + ((-11086540301853522820453047785488006741428480839374 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_548 h H) + ((-12939581330346886656715655098368387570281776205776 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_550 h H)

/-- Coordinate 127.0, recovered from skew spokes on cycle 46. -/
theorem value_508 (h : Assignment) (H : Constraints h) :
    h 127 0 = ((753062971344274112653576967 : ℝ) / 126654397743060166634518825) * (h 1 0) + ((125830091135666335619816958 : ℝ) / 80398009002116453602781515) * (h 1 1) + ((-67536049194508108851727272846 : ℝ) / 9245771035243392164319874225) * (h 1 2) + ((-626408573601213946019058142 : ℝ) / 126654397743060166634518825) * (h 3 0) + ((-125830091135666335619816958 : ℝ) / 80398009002116453602781515) * (h 5 1) + ((67536049194508108851727272846 : ℝ) / 9245771035243392164319874225) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 365 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 1 - h 124 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 365 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 2 - h 124 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 368 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 1 - h 125 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 368 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 2 - h 125 2) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 372 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 1 - h 126 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 372 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 2 - h 126 2) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((-35374520734680672708343406531423245144532505027937 : ℝ) / 5524505211426970654001519329327329037425816031271065860227098726634250600) * r0 + ((147160080699636381208568305649951302672097804974 : ℝ) / 40621361848727725397069995068583301745778059053463719560493372989957725) * r1 + ((-3184575953090931189603363544357093604024550859047970031863356481245693437 : ℝ) / 703755690794582204399415651757139170946630855707411158146925212204188529562168450708618600160458600) * r2 + ((605864891557381484062823784965846034422338740252858501937091944371475203799 : ℝ) / 33433569986939673695769297985315266055045455578864584505788851441553397716920370294326358644387669225) * r3 + ((4018327255485577682325133575475745995726880050721 : ℝ) / 1989578687500242654706739161038024822715869537599038905939209193192071860) * r4 + ((-11451860482778314742464999735028505542028436956483 : ℝ) / 380360631433869919282170721963151804342739764540992732017789992816131385) * r5 + ((5959606043775444849813811 : ℝ) / 74921412559722168023317757507082482694185674544570) * r6 + ((-577467057463769222908070802 : ℝ) / 486989181638194092151565423796036137512206884539705) * r7 + ((35374520734680672708343406531423245144532505027937 : ℝ) / 12459771472150460888185235542760260465482401094699558397941267851655788850900) * r8 + ((-294320161399272762417136611299902605344195609948 : ℝ) / 183231933413977366002724052099415595080623545510287623499136291936114541925) * r9 + ((4018327255485577682325133575475745995726880050721 : ℝ) / 5610942421274646105748529649010212985483282921181066039355592921031602238660) * r10 + ((-11451860482778314742464999735028505542028436956483 : ℝ) / 1072680168773094108451924785840187776636509970225792036935628058432512192685) * r11 + ((70749041469361345416686813062846490289065010055874 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_373 h H) + ((-36529514641256263148008464071435830721348547649847 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_372 h H) + ((-40027541950301095688730579136786754326810602952928 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_374 h H) + ((-70749041469361345416686813062846490289065010055874 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_549 h H) + ((88538482260136218806112747511915135095981769594772 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_548 h H) + ((40027541950301095688730579136786754326810602952928 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_550 h H)

/-- Coordinate 127.1, recovered from skew spokes on cycle 46. -/
theorem value_509 (h : Assignment) (H : Constraints h) :
    h 127 1 = ((159344708955709399123588597 : ℝ) / 126654397743060166634518825) * (h 1 0) + ((69463083005130850032370138 : ℝ) / 80398009002116453602781515) * (h 1 1) + ((-14822215821356797205531829486 : ℝ) / 9245771035243392164319874225) * (h 1 2) + ((-159344708955709399123588597 : ℝ) / 126654397743060166634518825) * (h 3 0) + ((10934925996985603570411377 : ℝ) / 80398009002116453602781515) * (h 5 1) + ((14822215821356797205531829486 : ℝ) / 9245771035243392164319874225) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 365 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 1 - h 124 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 365 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 2 - h 124 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 368 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 1 - h 125 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 368 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 2 - h 125 2) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 372 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 1 - h 126 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 372 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 2 - h 126 2) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((-1920917126829930095131224861014057146982149823684 : ℝ) / 690563151428371331750189916165916129678227003908883232528387340829281325) * r0 + ((52874438705483954564507522362381271617679227744 : ℝ) / 40621361848727725397069995068583301745778059053463719560493372989957725) * r1 + ((-511582417120590174583950443055104877258925922433555000387980664960779284 : ℝ) / 87969461349322775549926956469642396368328856963426394768365651525523566195271056338577325020057325) * r2 + ((2176986677004605392135049377169449939226690826785617151525369899397117153344 : ℝ) / 33433569986939673695769297985315266055045455578864584505788851441553397716920370294326358644387669225) * r3 + ((4000551570920213169376004430865350476129999319464 : ℝ) / 497394671875060663676684790259506205678967384399759726484802298298017965) * r4 + ((-45604805712920192578779703248344302426866882437088 : ℝ) / 380360631433869919282170721963151804342739764540992732017789992816131385) * r5 + ((1389993581021705407146232186950504780344833238133 : ℝ) / 2768030297128601596092619435522446749557685126155888793752919078932555960) * r6 + ((-1550563394239286547678509910443706282513474002860992 : ℝ) / 328357593996880364336486980538850245666280398090242308158940025738374450755) * r7 + ((-21274293589601074136004685664254390022918824765981 : ℝ) / 24919542944300921776370471085520520930964802189399116795882535703311577701800) * r8 + ((-105748877410967909129015044724762543235358455488 : ℝ) / 183231933413977366002724052099415595080623545510287623499136291936114541925) * r9 + ((4000551570920213169376004430865350476129999319464 : ℝ) / 1402735605318661526437132412252553246370820730295266509838898230257900559665) * r10 + ((-45604805712920192578779703248344302426866882437088 : ℝ) / 1072680168773094108451924785840187776636509970225792036935628058432512192685) * r11 + ((30734674029278881522099597776224914351714397178944 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_373 h H) + ((-3724574131552542424644150786646359742765239472832 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_372 h H) + ((-14381847327891635641546046082567705880008749946368 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_374 h H) + ((21274293589601074136004685664254390022918824765981 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_549 h H) + ((3724574131552542424644150786646359742765239472832 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_548 h H) + ((14381847327891635641546046082567705880008749946368 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_550 h H)

/-- Coordinate 127.2, recovered from skew spokes on cycle 46. -/
theorem value_510 (h : Assignment) (H : Constraints h) :
    h 127 2 = ((-82881235079194589895477500167 : ℝ) / 17224998093056182662294560200) * (h 1 0) + ((-13065867661683706731400226723 : ℝ) / 10934129224287837689978286040) * (h 1 1) + ((59923238221578451462311092536 : ℝ) / 9245771035243392164319874225) * (h 1 2) + ((82881235079194589895477500167 : ℝ) / 17224998093056182662294560200) * (h 3 0) + ((13065867661683706731400226723 : ℝ) / 10934129224287837689978286040) * (h 5 1) + ((-50677467186335059297991218311 : ℝ) / 9245771035243392164319874225) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 365 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 1 - h 124 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 365 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 2 - h 124 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 368 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 1 - h 125 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 368 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 2 - h 125 2) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 372 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 1 - h 126 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 372 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 2 - h 126 2) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((17028973315664964466471119961010194258674554701537991 : ℝ) / 2253998126262204026832619886365550247269732940758594870972656280466774244800) * r0 + ((-8960185697822957016618681523669940081630666478154 : ℝ) / 2071689454285113995250569748497748389034681011726649697585162022487843975) * r1 + ((1327171812306822806449559280739267835540288934699125927910698889874277971291 : ℝ) / 287132321844189539394961585916912781746225389128623752523945486579308920061364727889116388865467108800) * r2 + ((-146242950345485929734385855207370238293766548420088922486988231752377960531107 : ℝ) / 13640896554671386867873873578008628550458545876176750478361851388153786268503511080085154326910169043800) * r3 + ((-16688871520582385350282932272157251864945343816933 : ℝ) / 15916629500001941237653913288304198581726956300792311247513673545536574880) * r4 + ((47561738036099039582790343311321584964135203622159 : ℝ) / 3042885051470959354257365775705214434741918116327941856142319942529051080) * r5 + ((-228614678364142265072368935235030847465004709821 : ℝ) / 5536060594257203192185238871044893499115370252311777587505838157865111920) * r6 + ((2104088274865561437966437096380970026292803807693111 : ℝ) / 2626860751975042914691895844310801965330243184721938465271520205906995606040) * r7 + ((-17028973315664964466471119961010194258674554701537991 : ℝ) / 5083586760637388042379576101446186269916819646637419826360037283475561851167200) * r8 + ((-12663931691472554708413945942718871817809002184311 : ℝ) / 74758628832902765329111413256561562792894406568197350387647607109934733105400) * r9 + ((-16688871520582385350282932272157251864945343816933 : ℝ) / 44887539370197168845988237192081703883866263369448528314844743368252817909280) * r10 + ((47561738036099039582790343311321584964135203622159 : ℝ) / 8581441350184752867615398286721502213092079761806336295485024467460097541480) * r11 + ((-17028973315664964466471119961010194258674554701537991 : ℝ) / 10609829394251510954253273821857778092425177276764700) * (value_373 h H) + ((18507750689315434267356830205165496736193703179643771 : ℝ) / 21219658788503021908506547643715556184850354553529400) * (value_372 h H) + ((143362971165167312265898904378719041306090663650464 : ℝ) / 156026902856639866974312850321437913123899665834775) * (value_374 h H) + ((17028973315664964466471119961010194258674554701537991 : ℝ) / 10609829394251510954253273821857778092425177276764700) * (value_549 h H) + ((-18507750689315434267356830205165496736193703179643771 : ℝ) / 21219658788503021908506547643715556184850354553529400) * (value_548 h H) + ((12663931691472554708413945942718871817809002184311 : ℝ) / 156026902856639866974312850321437913123899665834775) * (value_550 h H)

/-- Coordinate 127.3, recovered from skew spokes on cycle 46. -/
theorem value_511 (h : Assignment) (H : Constraints h) :
    h 127 3 = ((286839626563733418382593063 : ℝ) / 126654397743060166634518825) * (h 1 0) + ((65195622996738853600374372 : ℝ) / 80398009002116453602781515) * (h 1 1) + ((-26274335083844763094555047894 : ℝ) / 9245771035243392164319874225) * (h 1 2) + h 1 3 + ((-286839626563733418382593063 : ℝ) / 126654397743060166634518825) * (h 3 0) + ((-65195622996738853600374372 : ℝ) / 80398009002116453602781515) * (h 5 1) + ((26274335083844763094555047894 : ℝ) / 9245771035243392164319874225) * (h 9 2) := by
  have r0 := H 280 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 1 - h 93 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 280 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 2 - h 93 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 280 3
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 124 3 - h 93 3) - ((-127365404271254371738016 : ℤ) : ℝ) * (h 124 0 - h 93 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 364 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 1 - h 124 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 364 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 2 - h 124 2) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 364 3
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 125 3 - h 124 3) - ((-206686098914908403040993376 : ℤ) : ℝ) * (h 125 0 - h 124 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 365 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 1 - h 124 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 365 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 126 2 - h 124 2) - ((858052654549977619189099 : ℤ) : ℝ) * (h 126 0 - h 124 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 368 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 1 - h 125 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 368 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 2 - h 125 2) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 368 3
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 127 3 - h 125 3) - ((2798542402819443398557312 : ℤ) : ℝ) * (h 127 0 - h 125 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 371 1
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 1 - h 125 1) - ((288207969761874200450849792 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 371 2
  change ((479139350100362155476101576 : ℤ) : ℝ) * (h 137 2 - h 125 2) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 137 0 - h 125 0) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  have r13 := H 372 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 1 - h 126 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r13
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r13
  have r14 := H 372 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 127 2 - h 126 2) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 127 0 - h 126 0) = 0 at r14
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r14
  linear_combination ((-45819683363438855985063499609524367741746551876 : ℝ) / 13540453949575908465689998356194433915259353017821239853497790996652575) * r0 + ((24356421539081523004522644325961379437698082322 : ℝ) / 13540453949575908465689998356194433915259353017821239853497790996652575) * r1 + ((-1 : ℝ) / 212444332750858175578384) * r2 + ((-28747792012918495547960841771948406457120648617797214266479380941946232 : ℝ) / 12074239793044302526460562652696015187809843112627152223109010993699313007194066556275319120400025) * r3 + ((104294227850666829703972063193603332166083698281232859809507793471546818822 : ℝ) / 11144523328979891231923099328438422018348485192954861501929617147184465905640123431442119548129223075) * r4 + ((-1 : ℝ) / 395436308798036478554666224) * r5 + ((30658474664714357369835513104550793517112523228 : ℝ) / 29258510110297686098628517074088600334056904964691748616753076370471645) * r6 + ((-5941419288763714401374365889897071826370617466192 : ℝ) / 380360631433869919282170721963151804342739764540992732017789992816131385) * r7 + ((14279289569866960966772704733626396980572956024 : ℝ) / 346003787141075199511577429440305843694710640769486099219114884866569495) * r8 + ((-2767236381068031365023677263787677288994534162336 : ℝ) / 4498049232833977593650506582723975968031238330003319289848493503265403435) * r9 + ((1 : ℝ) / 5394084408894845884406488) * r10 + ((91639366726877711970126999219048735483493103752 : ℝ) / 61077311137992455334241350699805198360207848503429207833045430645371513975) * r11 + ((-48712843078163046009045288651922758875396164644 : ℝ) / 61077311137992455334241350699805198360207848503429207833045430645371513975) * r12 + ((30658474664714357369835513104550793517112523228 : ℝ) / 82513859136391854496301906603091367433577690017368618225817542956347091745) * r13 + ((-5941419288763714401374365889897071826370617466192 : ℝ) / 1072680168773094108451924785840187776636509970225792036935628058432512192685) * r14 + ((12462953874855368827937271893790628025755062110272 : ℝ) / 17336322539626651886034761146826434791544407314975) * (value_373 h H) + ((-15107097449015077726320069496070856049447101889516 : ℝ) / 17336322539626651886034761146826434791544407314975) * (value_372 h H) + ((-6624946658630174257230159256661495207053878391584 : ℝ) / 17336322539626651886034761146826434791544407314975) * (value_374 h H) + (1 : ℝ) * (value_375 h H) + ((-12462953874855368827937271893790628025755062110272 : ℝ) / 17336322539626651886034761146826434791544407314975) * (value_549 h H) + ((15107097449015077726320069496070856049447101889516 : ℝ) / 17336322539626651886034761146826434791544407314975) * (value_548 h H) + ((6624946658630174257230159256661495207053878391584 : ℝ) / 17336322539626651886034761146826434791544407314975) * (value_550 h H)

/-- Coordinate 128.0, recovered from skew spokes on cycle 47. -/
theorem value_512 (h : Assignment) (H : Constraints h) :
    h 128 0 = ((-9545790293705793165213571 : ℝ) / 13821623836049824562735500) * (h 1 0) + ((-16401952160911844438037 : ℝ) / 168725508366494513892925) * (h 1 1) + ((480774751631741289653908389 : ℝ) / 504489270015818596539845750) * (h 1 2) + ((23367414129755617727949071 : ℝ) / 13821623836049824562735500) * (h 3 0) + ((16401952160911844438037 : ℝ) / 168725508366494513892925) * (h 5 1) + ((-480774751631741289653908389 : ℝ) / 504489270015818596539845750) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((-1453809958816310582921567 : ℝ) / 554224971822121369643170335070246050263653584800) * r0 + ((58303006321547036247620777432378554128307703 : ℝ) / 4075183616339127717964487757869456251938629300) * r1 + ((-1135491495026778330175747990639452007179163999 : ℝ) / 2037591808169563858982243878934728125969314650) * r2 + ((-781045340995802116097 : ℝ) / 554224971822121369643170335070246050263653584800) * r3 + ((1135491495026778330175747990639452007179163999 : ℝ) / 2037591808169563858982243878934728125969314650) * (value_389 h H) + ((4016880610017580681716866980437077697810321597 : ℝ) / 4075183616339127717964487757869456251938629300) * (value_388 h H) + ((58303006321547036247620777432378554128307703 : ℝ) / 4075183616339127717964487757869456251938629300) * (value_500 h H) + ((-1135491495026778330175747990639452007179163999 : ℝ) / 2037591808169563858982243878934728125969314650) * (value_501 h H)

/-- Coordinate 128.1, recovered from skew spokes on cycle 47. -/
theorem value_513 (h : Assignment) (H : Constraints h) :
    h 128 1 = ((68764358380088094269000213 : ℝ) / 27643247672099649125471000) * (h 1 0) + ((395474070089323488804761 : ℝ) / 337451016732989027785850) * (h 1 1) + ((-3161039314271773420806596667 : ℝ) / 1008978540031637193079691500) * (h 1 2) + ((-68764358380088094269000213 : ℝ) / 27643247672099649125471000) * (h 3 0) + ((-58023053356334461018911 : ℝ) / 337451016732989027785850) * (h 5 1) + ((3161039314271773420806596667 : ℝ) / 1008978540031637193079691500) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((-74647402988427015505399 : ℝ) / 1108449943644242739286340670140492100527307169600) * r0 + ((-206250964119490534173532133762673264055314309 : ℝ) / 8150367232678255435928975515738912503877258600) * r1 + ((4016880610017580681716866980437077697810321597 : ℝ) / 4075183616339127717964487757869456251938629300) * r2 + ((2763002540777831477091 : ℝ) / 1108449943644242739286340670140492100527307169600) * r3 + ((58303006321547036247620777432378554128307703 : ℝ) / 4075183616339127717964487757869456251938629300) * (value_389 h H) + ((206250964119490534173532133762673264055314309 : ℝ) / 8150367232678255435928975515738912503877258600) * (value_388 h H) + ((-206250964119490534173532133762673264055314309 : ℝ) / 8150367232678255435928975515738912503877258600) * (value_500 h H) + ((4016880610017580681716866980437077697810321597 : ℝ) / 4075183616339127717964487757869456251938629300) * (value_501 h H)

/-- Coordinate 128.2, recovered from skew spokes on cycle 47. -/
theorem value_514 (h : Assignment) (H : Constraints h) :
    h 128 2 = ((-5784129614890699131802604323 : ℝ) / 3759481683405552281064056000) * (h 1 0) + ((-14794973814770092723650381 : ℝ) / 45893338275686507778875600) * (h 1 1) + ((18572494168528014899067680421 : ℝ) / 8071828320253097544637532000) * (h 1 2) + ((5784129614890699131802604323 : ℝ) / 3759481683405552281064056000) * (h 3 0) + ((14794973814770092723650381 : ℝ) / 45893338275686507778875600) * (h 5 1) + ((-10500665848274917354430148421 : ℝ) / 8071828320253097544637532000) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 296 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 2 - h 97 2) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((-1024241917730442951489074296632725510461335841287 : ℝ) / 117741954332613748399107732537351720488579186883435744650828754990963200) * r0 + ((-1 : ℝ) / 212444332750858175578384) * r1 + ((52590779645446117206349311003910385137280662239 : ℝ) / 1108449943644242739286340670140492100527307169600) * r2 + ((-1024241917730442951489074296632725510461335841287 : ℝ) / 554224971822121369643170335070246050263653584800) * r3 + ((-704522562608099653507161 : ℝ) / 150749192335617012542942331139106925671713775065600) * r4 + ((1024241917730442951489074296632725510461335841287 : ℝ) / 554224971822121369643170335070246050263653584800) * (value_389 h H) + ((-52590779645446117206349311003910385137280662239 : ℝ) / 1108449943644242739286340670140492100527307169600) * (value_388 h H) + (1 : ℝ) * (value_390 h H) + ((52590779645446117206349311003910385137280662239 : ℝ) / 1108449943644242739286340670140492100527307169600) * (value_500 h H) + ((-1024241917730442951489074296632725510461335841287 : ℝ) / 554224971822121369643170335070246050263653584800) * (value_501 h H)

/-- Coordinate 128.3, recovered from skew spokes on cycle 47. -/
theorem value_515 (h : Assignment) (H : Constraints h) :
    h 128 3 = ((-8329980296380684811405877 : ℝ) / 6910811918024912281367750) * (h 1 0) + ((-9833358418001256641538 : ℝ) / 168725508366494513892925) * (h 1 1) + ((372304208406275240464072143 : ℝ) / 252244635007909298269922875) * (h 1 2) + h 1 3 + ((8329980296380684811405877 : ℝ) / 6910811918024912281367750) * (h 3 0) + ((9833358418001256641538 : ℝ) / 168725508366494513892925) * (h 5 1) + ((-372304208406275240464072143 : ℝ) / 252244635007909298269922875) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 296 3
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 3 - h 97 3) - ((-127365404271254371738016 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((-20022177026191075496158101594385734221972339 : ℝ) / 12731612708976400129661303258796682578782351522862861662070583368400) * r0 + ((-1 : ℝ) / 212444332750858175578384) * r1 + ((17477015918051927488712639614755891772539611 : ℝ) / 2037591808169563858982243878934728125969314650) * r2 + ((-340377009445248283434687727104557481773529763 : ℝ) / 1018795904084781929491121939467364062984657325) * r3 + ((-13772210669469547117 : ℝ) / 16300734465356510871857951031477825007754517200) * r4 + ((340377009445248283434687727104557481773529763 : ℝ) / 1018795904084781929491121939467364062984657325) * (value_389 h H) + ((-17477015918051927488712639614755891772539611 : ℝ) / 2037591808169563858982243878934728125969314650) * (value_388 h H) + (1 : ℝ) * (value_391 h H) + ((17477015918051927488712639614755891772539611 : ℝ) / 2037591808169563858982243878934728125969314650) * (value_500 h H) + ((-340377009445248283434687727104557481773529763 : ℝ) / 1018795904084781929491121939467364062984657325) * (value_501 h H)

/-- Coordinate 129.0, recovered from skew spokes on cycle 47. -/
theorem value_516 (h : Assignment) (H : Constraints h) :
    h 129 0 = ((201456234728327216730076966 : ℝ) / 31979186935482304481556645) * (h 1 0) + ((33569999458194540553426690 : ℝ) / 20299831706871375888292479) * (h 1 1) + ((-154529642813639551120678656 : ℝ) / 19952826036668446385928505) * (h 1 2) + ((-169477047792844912248520321 : ℝ) / 31979186935482304481556645) * (h 3 0) + ((-33569999458194540553426690 : ℝ) / 20299831706871375888292479) * (h 5 1) + ((154529642813639551120678656 : ℝ) / 19952826036668446385928505) * (h 9 2) := by
  have r0 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_500 h H)

/-- Coordinate 129.1, recovered from skew spokes on cycle 47. -/
theorem value_517 (h : Assignment) (H : Constraints h) :
    h 129 1 = ((85289296303667014747598497 : ℝ) / 31979186935482304481556645) * (h 1 0) + ((24702794285873566689225010 : ℝ) / 20299831706871375888292479) * (h 1 1) + ((-13393165800162739382713734 : ℝ) / 3990565207333689277185701) * (h 1 2) + ((-85289296303667014747598497 : ℝ) / 31979186935482304481556645) * (h 3 0) + ((-4402962579002190800932531 : ℝ) / 20299831706871375888292479) * (h 5 1) + ((13393165800162739382713734 : ℝ) / 3990565207333689277185701) * (h 9 2) := by
  have r0 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_501 h H)

/-- Coordinate 129.2, recovered from skew spokes on cycle 47. -/
theorem value_518 (h : Assignment) (H : Constraints h) :
    h 129 2 = ((5827470807254752012871525461 : ℝ) / 2174584711612796704745851860) * (h 1 0) + ((2027064785014945318712380073 : ℝ) / 2760777112134507120807777144) * (h 1 1) + ((-235272579258668511597182619 : ℝ) / 79811304146673785543714020) * (h 1 2) + ((-5827470807254752012871525461 : ℝ) / 2174584711612796704745851860) * (h 3 0) + ((-2027064785014945318712380073 : ℝ) / 2760777112134507120807777144) * (h 5 1) + ((315083883405342297140896639 : ℝ) / 79811304146673785543714020) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 296 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 2 - h 97 2) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 378 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 2 - h 128 2) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-871405633609100756943061 : ℝ) / 122455987343310977170009075586749173093879116752) * r0 + ((-1 : ℝ) / 212444332750858175578384) * r1 + ((5923460125997298171044253 : ℝ) / 9222631510677758936778448) * r2 + ((-871405633609100756943061 : ℝ) / 576414469417359933548653) * r3 + ((-871405633609100756943061 : ℝ) / 227935210124179496591390951331295596154456279796272) * r4 + ((-1 : ℝ) / 395436308798036478554666224) * r5 + ((871405633609100756943061 : ℝ) / 576414469417359933548653) * (value_389 h H) + ((-5923460125997298171044253 : ℝ) / 9222631510677758936778448) * (value_388 h H) + (1 : ℝ) * (value_390 h H) + ((5923460125997298171044253 : ℝ) / 9222631510677758936778448) * (value_500 h H) + ((-871405633609100756943061 : ℝ) / 576414469417359933548653) * (value_501 h H)

/-- Coordinate 129.3, recovered from skew spokes on cycle 47. -/
theorem value_519 (h : Assignment) (H : Constraints h) :
    h 129 3 = ((2699812471334852541906743 : ℝ) / 1102730583982148430398505) * (h 1 0) + ((599816457482315935619492 : ℝ) / 699994196788668134079051) * (h 1 1) + ((-2112356982453003366864414 : ℝ) / 688028484023049875376845) * (h 1 2) + h 1 3 + ((-2699812471334852541906743 : ℝ) / 1102730583982148430398505) * (h 3 0) + ((-599816457482315935619492 : ℝ) / 699994196788668134079051) * (h 5 1) + ((2112356982453003366864414 : ℝ) / 688028484023049875376845) * (h 9 2) := by
  have r0 := H 369 3
  change ((1 : ℤ) : ℝ) * (h 129 3 - h 125 3) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_503 h H)

/-- Coordinate 130.0, recovered from skew spokes on cycle 47. -/
theorem value_520 (h : Assignment) (H : Constraints h) :
    h 130 0 = ((-82173261632986900318333999 : ℝ) / 141586781036886034142974850) * (h 1 0) + ((-240561965026707051757876 : ℝ) / 3456801008592869729912095) * (h 1 1) + ((4215936139788936757521194181 : ℝ) / 5167917507846340246218582025) * (h 1 2) + ((223760042669872934461308849 : ℝ) / 141586781036886034142974850) * (h 3 0) + ((240561965026707051757876 : ℝ) / 3456801008592869729912095) * (h 5 1) + ((-4215936139788936757521194181 : ℝ) / 5167917507846340246218582025) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 378 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 2 - h 128 2) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 379 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 1 - h 128 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 379 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 2 - h 128 2) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 381 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 1 - h 129 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 381 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 2 - h 129 2) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 384 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 1 - h 130 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 384 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 2 - h 130 2) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((-14657701538247532435880383 : ℝ) / 5677403079505292682362515210983163763988217765360) * r0 + ((1246344286574326462988625494104847885209030657 : ℝ) / 41745610878715387370312611845464439441089836510) * r1 + ((-11448329496155237184448366720203550360570825151 : ℝ) / 20872805439357693685156305922732219720544918255) * r2 + ((-118345028465243689846604457743433198359840561531320884960792635217115091 : ℝ) / 115724444119886442254786828000953705815048784902131708706657020101199882131732810674340861187751280) * r3 + ((5101963443917453221887585994903356402600576238 : ℝ) / 965221293576344389174934918708223111411346521736274576638628143668032095) * r4 + ((-428690486673682807340237077 : ℝ) / 632056938331086249669138736882728306687852457659320) * r5 + ((-45725570889250235206517378 : ℝ) / 4647477487728575365214255418255355196234209247495) * r6 + ((-4586667223913739056048165503502011308633670253 : ℝ) / 171704697652373259015896169415878879511742765293740889219743077460107860) * r7 + ((-1214267299652353866809245466786998823818937144644 : ℝ) / 3133610732155811977040105091839789551089305466610771228260311163646968445) * r8 + ((-334826707345702951091516081755646825530257928469 : ℝ) / 1392217668989015264816925775045410467048830163161982029374886559241650249240) * r9 + ((-35713744107422172553213101964323494818204033666 : ℝ) / 10236894624919229888359748345922135787123751199720456098344754112070957715) * r10 + ((11448329496155237184448366720203550360570825151 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_389 h H) + ((40499266592141060907323986351359591555880805853 : ℝ) / 41745610878715387370312611845464439441089836510) * (value_388 h H) + ((1246344286574326462988625494104847885209030657 : ℝ) / 41745610878715387370312611845464439441089836510) * (value_500 h H) + ((-11448329496155237184448366720203550360570825151 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_501 h H)

/-- Coordinate 130.1, recovered from skew spokes on cycle 47. -/
theorem value_521 (h : Assignment) (H : Constraints h) :
    h 130 1 = ((-368427272927502107194965529 : ℝ) / 141586781036886034142974850) * (h 1 0) + ((-355785217299252588876116 : ℝ) / 3456801008592869729912095) * (h 1 1) + ((16537522489458809905008878751 : ℝ) / 5167917507846340246218582025) * (h 1 2) + ((368427272927502107194965529 : ℝ) / 141586781036886034142974850) * (h 3 0) + ((3812586225892122318788211 : ℝ) / 3456801008592869729912095) * (h 5 1) + ((-16537522489458809905008878751 : ℝ) / 5167917507846340246218582025) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 378 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 2 - h 128 2) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 379 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 1 - h 128 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 379 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 2 - h 128 2) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 381 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 1 - h 129 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 381 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 2 - h 129 2) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 384 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 1 - h 130 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 384 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 2 - h 130 2) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((-11225865095908060396188103 : ℝ) / 5677403079505292682362515210983163763988217765360) * r0 + ((-31017093782423145710315601904681450822371248373 : ℝ) / 41745610878715387370312611845464439441089836510) * r1 + ((12104895807551309826750335912859206560688724264 : ℝ) / 20872805439357693685156305922732219720544918255) * r2 + ((-1776645118430941022147239182352085660110278943107747564864040899756532251 : ℝ) / 115724444119886442254786828000953705815048784902131708706657020101199882131732810674340861187751280) * r3 + ((-235494047175078737300459041406199704302985754207 : ℝ) / 965221293576344389174934918708223111411346521736274576638628143668032095) * r4 + ((13131036125044199741831834459453773649746363140131 : ℝ) / 493665126927565929126044071272889090727932545792844268150472951514074040) * r5 + ((1648458330225551161103213289843397930120900279449 : ℝ) / 3629890639173278890632676994653596255352445189653266677577006996427015) * r6 + ((423418489559136641765451018317300034188040212709 : ℝ) / 343409395304746518031792338831757759023485530587481778439486154920215720) * r7 + ((56047583227668739477509251854675529624110609501266 : ℝ) / 3133610732155811977040105091839789551089305466610771228260311163646968445) * r8 + ((30909549737816974848877924337162902495726935527757 : ℝ) / 2784435337978030529633851550090820934097660326323964058749773118483300498480) * r9 + ((1648458330225551161103213289843397930120900279449 : ℝ) / 10236894624919229888359748345922135787123751199720456098344754112070957715) * r10 + ((8767909631806383858405970009873013159856193991 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_389 h H) + ((31017093782423145710315601904681450822371248373 : ℝ) / 41745610878715387370312611845464439441089836510) * (value_388 h H) + ((-31017093782423145710315601904681450822371248373 : ℝ) / 41745610878715387370312611845464439441089836510) * (value_500 h H) + ((12104895807551309826750335912859206560688724264 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_501 h H)

/-- Coordinate 130.2, recovered from skew spokes on cycle 47. -/
theorem value_522 (h : Assignment) (H : Constraints h) :
    h 130 2 = ((-45168965696159126417226512027 : ℝ) / 38511604442033001286889159200) * (h 1 0) + ((-54248237320823673320051397 : ℝ) / 235062468584315141634022460) * (h 1 1) + ((152631455522264344757678195889 : ℝ) / 82686680125541443939497312400) * (h 1 2) + ((45168965696159126417226512027 : ℝ) / 38511604442033001286889159200) * (h 3 0) + ((54248237320823673320051397 : ℝ) / 235062468584315141634022460) * (h 5 1) + ((-69944775396722900818180883489 : ℝ) / 82686680125541443939497312400) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 296 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 2 - h 97 2) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 378 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 2 - h 128 2) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 379 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 1 - h 128 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 379 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 2 - h 128 2) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 381 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 1 - h 129 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 381 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 2 - h 129 2) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 384 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 1 - h 130 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 384 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 2 - h 130 2) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((-10326681449670835768524253428905508449520629922663 : ℝ) / 1206132108983169312669435794893319351611201876376048042791349161999978240) * r0 + ((-1 : ℝ) / 212444332750858175578384) * r1 + ((1124233926739507451270858505952632411555173988441 : ℝ) / 11354806159010585364725030421966327527976435530720) * r2 + ((-10326681449670835768524253428905508449520629922663 : ℝ) / 5677403079505292682362515210983163763988217765360) * r3 + ((-106750195347122758210989373319499024987615549069002228540750806179449249883 : ℝ) / 31477048800609112293302017216259407981693269493379824768210709467526367939831324503420714243068348160) * r4 + ((2301049741400921270069172711649791102703028138847 : ℝ) / 131270095926382836927791148944318343151943126956133342422853427538852364920) * r5 + ((-302022120237056405810778966463006939714916257208397 : ℝ) / 134276914524297932722283987386225832677997652455653640936928642811828138880) * r6 + ((-36862173867341473146182673381352430634076603191353 : ℝ) / 987330253855131858252088142545778181455865091585688536300945903028148080) * r7 + ((-4137289318315841175490122828260369037190633660389 : ℝ) / 46703677761445526452323758081119055227194032159897521867770117069149337920) * r8 + ((-16107348189806448890484208981548537718921196971929 : ℝ) / 12534442928623247908160420367359158204357221866443084913041244654587873780) * r9 + ((-302022120237056405810778966463006939714916257208397 : ℝ) / 378683205965012152030203810812351647037281804380059111989969144113728867793280) * r10 + ((-16107348189806448890484208981548537718921196971929 : ℝ) / 1392217668989015264816925775045410467048830163161982029374886559241650249240) * r11 + ((10326681449670835768524253428905508449520629922663 : ℝ) / 5677403079505292682362515210983163763988217765360) * (value_389 h H) + ((-1124233926739507451270858505952632411555173988441 : ℝ) / 11354806159010585364725030421966327527976435530720) * (value_388 h H) + (1 : ℝ) * (value_390 h H) + ((1124233926739507451270858505952632411555173988441 : ℝ) / 11354806159010585364725030421966327527976435530720) * (value_500 h H) + ((-10326681449670835768524253428905508449520629922663 : ℝ) / 5677403079505292682362515210983163763988217765360) * (value_501 h H)

/-- Coordinate 130.3, recovered from skew spokes on cycle 47. -/
theorem value_523 (h : Assignment) (H : Constraints h) :
    h 130 3 = ((-80651127640777593610839848 : ℝ) / 70793390518443017071487425) * (h 1 0) + ((-144222590130685097409224 : ℝ) / 3456801008592869729912095) * (h 1 1) + ((7202570310470526750271528524 : ℝ) / 5167917507846340246218582025) * (h 1 2) + h 1 3 + ((80651127640777593610839848 : ℝ) / 70793390518443017071487425) * (h 3 0) + ((144222590130685097409224 : ℝ) / 3456801008592869729912095) * (h 5 1) + ((-7202570310470526750271528524 : ℝ) / 5167917507846340246218582025) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 296 3
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 3 - h 97 3) - ((-127365404271254371738016 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 378 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 2 - h 128 2) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 379 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 1 - h 128 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 379 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 2 - h 128 2) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 379 3
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 3 - h 128 3) - ((-127365404271254371738016 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 381 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 1 - h 129 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 381 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 2 - h 129 2) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 384 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 1 - h 130 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 384 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 2 - h 130 2) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  linear_combination ((-201868953514952859275485963248037848194505811 : ℝ) / 130420859535377304570656984741924670373183593898794122274151077205880) * r0 + ((-1 : ℝ) / 212444332750858175578384) * r1 + ((373606445192560596926631351043637374742331709 : ℝ) / 20872805439357693685156305922732219720544918255) * r2 + ((-6863544419508397215366522750433286838613197574 : ℝ) / 20872805439357693685156305922732219720544918255) * r3 + ((-2086783670752946061678086419555419047895532437047263528084137016296151 : ℝ) / 3403660121173130654552553764733932523972023085356814961960500591211761239168612078657084152580920) * r4 + ((3058747805589945624001468182740304651330024812 : ℝ) / 965221293576344389174934918708223111411346521736274576638628143668032095) * r5 + ((-5904015694467387062876039266807849270601857009 : ℝ) / 14519562556693115562530707978614385021409780758613066710308027985708060) * r6 + ((-21411234639129619368010277279182132559310173684 : ℝ) / 3629890639173278890632676994653596255352445189653266677577006996427015) * r7 + ((-1 : ℝ) / 212444332750858175578384) * r8 + ((-1374907764465007946149214623777170378085363961 : ℝ) / 85852348826186629507948084707939439755871382646870444609871538730053930) * r9 + ((-727981977730407058512349427492192507016545905256 : ℝ) / 3133610732155811977040105091839789551089305466610771228260311163646968445) * r10 + ((-13149255444248078091037949369282515079291441 : ℝ) / 91197279509302716154652546511555775386403128728021880608861952000632140) * r11 + ((-47686491401179553158152065209759760711158516 : ℝ) / 22799319877325679038663136627888943846600782182005470152215488000158035) * r12 + ((6863544419508397215366522750433286838613197574 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_389 h H) + ((-373606445192560596926631351043637374742331709 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_388 h H) + (1 : ℝ) * (value_391 h H) + ((373606445192560596926631351043637374742331709 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_500 h H) + ((-6863544419508397215366522750433286838613197574 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_501 h H)

/-- Coordinate 131.0, recovered from skew spokes on cycle 47. -/
theorem value_524 (h : Assignment) (H : Constraints h) :
    h 131 0 = ((753062971344274112653576967 : ℝ) / 126654397743060166634518825) * (h 1 0) + ((125830091135666335619816958 : ℝ) / 80398009002116453602781515) * (h 1 1) + ((-67536049194508108851727272846 : ℝ) / 9245771035243392164319874225) * (h 1 2) + ((-626408573601213946019058142 : ℝ) / 126654397743060166634518825) * (h 3 0) + ((-125830091135666335619816958 : ℝ) / 80398009002116453602781515) * (h 5 1) + ((67536049194508108851727272846 : ℝ) / 9245771035243392164319874225) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 378 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 2 - h 128 2) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 379 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 1 - h 128 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 379 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 2 - h 128 2) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 381 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 1 - h 129 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 381 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 2 - h 129 2) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 384 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 1 - h 130 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 384 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 2 - h 130 2) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((-674260551111855735550811 : ℝ) / 5078638433004611854704413442041998392609904827320) * r0 + ((35479946038577357100382348591456225286224564694 : ℝ) / 37342929654445675402238334132661752886837535495) * r1 + ((-1053256124126353649204297264753648051329009334 : ℝ) / 37342929654445675402238334132661752886837535495) * r2 + ((-3151633265184018625622257973261462647910069307675099115589023006493693769 : ℝ) / 724637340207299908975935047671168996892323138987840430323671342551429134448591323474399440608680520) * r3 + ((-11451860482778314742464999735028505542028436956483 : ℝ) / 157143292425449463409791239290003972799831251123278292866370603450840550605) * r4 + ((3516373979500414672590234644033969021588099655487 : ℝ) / 441600966417008298132178145923649946937235502011356618144224213705777980) * r5 + ((11451860482778314742464999735028505542028436956483 : ℝ) / 84423714167957468760563469073638960443883257737465235821689923208457555) * r6 + ((5215156030857675905684717 : ℝ) / 16629333838145397629453752129505348921811456472510) * r7 + ((577467057463769222908070802 : ℝ) / 108090669947945084591449388841784767991774467071315) * r8 + ((3516373979500414672590234644033969021588099655487 : ℝ) / 1245388087092066833541119848318583930773227954807692585717357791062572390380) * r9 + ((11451860482778314742464999735028505542028436956483 : ℝ) / 238088899002895129941684676884435163236058285477941229622436048291374133455) * r10 + ((1053256124126353649204297264753648051329009334 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_389 h H) + ((1862983615868318301855985541205527600612970801 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_388 h H) + ((35479946038577357100382348591456225286224564694 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_500 h H) + ((-1053256124126353649204297264753648051329009334 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_501 h H)

/-- Coordinate 131.1, recovered from skew spokes on cycle 47. -/
theorem value_525 (h : Assignment) (H : Constraints h) :
    h 131 1 = ((159344708955709399123588597 : ℝ) / 126654397743060166634518825) * (h 1 0) + ((69463083005130850032370138 : ℝ) / 80398009002116453602781515) * (h 1 1) + ((-14822215821356797205531829486 : ℝ) / 9245771035243392164319874225) * (h 1 2) + ((-159344708955709399123588597 : ℝ) / 126654397743060166634518825) * (h 3 0) + ((10934925996985603570411377 : ℝ) / 80398009002116453602781515) * (h 5 1) + ((14822215821356797205531829486 : ℝ) / 9245771035243392164319874225) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 378 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 2 - h 128 2) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 379 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 1 - h 128 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 379 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 2 - h 128 2) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 381 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 1 - h 129 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 381 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 2 - h 129 2) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 384 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 1 - h 130 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 384 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 2 - h 130 2) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((-335638928272668225154012 : ℝ) / 634829804125576481838051680255249799076238103415) * r0 + ((-7418969692810645136203174191726452119397912736 : ℝ) / 37342929654445675402238334132661752886837535495) * r1 + ((33148542115498607855981308940328018593568236871 : ℝ) / 37342929654445675402238334132661752886837535495) * r2 + ((-224120823850348529174298938172906130062957043533176835468323293780582764 : ℝ) / 12939952503701784088855982994128017801648627481925721970065559688418377400867702204899990010869295) * r3 + ((-6514972244702884654111386178334900346695268919584 : ℝ) / 22449041775064209058541605612857710399975893017611184695195800492977221515) * r4 + ((3500818761943625200781303694632295151207279269208 : ℝ) / 110400241604252074533044536480912486734308875502839154536056053426444495) * r5 + ((45604805712920192578779703248344302426866882437088 : ℝ) / 84423714167957468760563469073638960443883257737465235821689923208457555) * r6 + ((881202289180420575715448427107799957263317760871 : ℝ) / 614383769771558739284127409824121185101289600742616859897808410735874280) * r7 + ((1550563394239286547678509910443706282513474002860992 : ℝ) / 72881274689151155447579613990386375582640478888092925005377522723543086465) * r8 + ((3500818761943625200781303694632295151207279269208 : ℝ) / 311347021773016708385279962079645982693306988701923146429339447765643097595) * r9 + ((45604805712920192578779703248344302426866882437088 : ℝ) / 238088899002895129941684676884435163236058285477941229622436048291374133455) * r10 + ((4194387538947067546257025192333734293269298624 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_389 h H) + ((7418969692810645136203174191726452119397912736 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_388 h H) + ((-7418969692810645136203174191726452119397912736 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_500 h H) + ((33148542115498607855981308940328018593568236871 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_501 h H)

/-- Coordinate 131.2, recovered from skew spokes on cycle 47. -/
theorem value_526 (h : Assignment) (H : Constraints h) :
    h 131 2 = ((44098331053156324319269247573 : ℝ) / 17224998093056182662294560200) * (h 1 0) + ((7700484084216196182764171737 : ℝ) / 10934129224287837689978286040) * (h 1 1) + ((-25878497438885413121565821784 : ℝ) / 9245771035243392164319874225) * (h 1 2) + ((-44098331053156324319269247573 : ℝ) / 17224998093056182662294560200) * (h 3 0) + ((-7700484084216196182764171737 : ℝ) / 10934129224287837689978286040) * (h 5 1) + ((35124268474128805285885696009 : ℝ) / 9245771035243392164319874225) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 296 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 2 - h 97 2) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 378 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 2 - h 128 2) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 379 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 1 - h 128 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 379 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 2 - h 128 2) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 381 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 1 - h 129 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 381 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 2 - h 129 2) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 384 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 1 - h 130 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 384 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 2 - h 130 2) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((-3863090877156687933645459717594030951720889283013 : ℝ) / 539463976591264353310033003194046764485782809156799287058236267322325440) * r0 + ((-1 : ℝ) / 212444332750858175578384) * r1 + ((6352354232648255576835714411000468110750443229457 : ℝ) / 10157276866009223709408826884083996785219809654640) * r2 + ((-3863090877156687933645459717594030951720889283013 : ℝ) / 2539319216502305927352206721020999196304952413660) * r3 + ((-521747021118760510520173978152492706270141987649236830191991106418661054911 : ℝ) / 98550678268192787620727166483278983577355946902346298524019302586994362285008419992518323922780550720) * r4 + ((-1161724448936658625685936296593810347052893560063829 : ℝ) / 42742975539722254047463217086881080601554100305531695659652804138628629764560) * r5 + ((9515459775215152482492494267453143630328069521669 : ℝ) / 3532807731336066385057425167389199575497884016090852945153793709646223840) * r6 + ((30989228793785692385131967875059575854738796852721 : ℝ) / 675389713343659750084507752589111683551066061899721886573519385667660440) * r7 + ((130348764044043184691678003663741693566137938653 : ℝ) / 1228767539543117478568254819648242370202579201485233719795616821471748560) * r8 + ((1161724448936658625685936296593810347052893560063829 : ℝ) / 583050197513209243580636911923091004661123831104743400043020181788344691720) * r9 + ((9515459775215152482492494267453143630328069521669 : ℝ) / 9963104696736534668328958786548671446185823638461540685738862328500579123040) * r10 + ((30989228793785692385131967875059575854738796852721 : ℝ) / 1904711192023161039533477415075481305888466283823529836979488386330993067640) * r11 + ((3863090877156687933645459717594030951720889283013 : ℝ) / 2539319216502305927352206721020999196304952413660) * (value_389 h H) + ((-6352354232648255576835714411000468110750443229457 : ℝ) / 10157276866009223709408826884083996785219809654640) * (value_388 h H) + (1 : ℝ) * (value_390 h H) + ((6352354232648255576835714411000468110750443229457 : ℝ) / 10157276866009223709408826884083996785219809654640) * (value_500 h H) + ((-3863090877156687933645459717594030951720889283013 : ℝ) / 2539319216502305927352206721020999196304952413660) * (value_501 h H)

end CubicalIndecomposability.Rigidity
end VerificationSource016

/- Original source: CubicalIndecomposability/Rigidity/Values07.lean -/
section VerificationSource017


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

/-! Each coordinate identity below is an exact linear consequence
of edge equations and identities in earlier modules. No rank result or
external solver is assumed. -/

/-- Coordinate 131.3, recovered from skew spokes on cycle 47. -/
theorem value_527 (h : Assignment) (H : Constraints h) :
    h 131 3 = ((286839626563733418382593063 : ℝ) / 126654397743060166634518825) * (h 1 0) + ((65195622996738853600374372 : ℝ) / 80398009002116453602781515) * (h 1 1) + ((-26274335083844763094555047894 : ℝ) / 9245771035243392164319874225) * (h 1 2) + h 1 3 + ((-286839626563733418382593063 : ℝ) / 126654397743060166634518825) * (h 3 0) + ((-65195622996738853600374372 : ℝ) / 80398009002116453602781515) * (h 5 1) + ((26274335083844763094555047894 : ℝ) / 9245771035243392164319874225) * (h 9 2) := by
  have r0 := H 296 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 128 1 - h 97 1) - ((375768345545785080884376 : ℤ) : ℝ) * (h 128 0 - h 97 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 369 0
  change ((1 : ℤ) : ℝ) * (h 129 0 - h 125 0) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 369 1
  change ((1 : ℤ) : ℝ) * (h 129 1 - h 125 1) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 369 3
  change ((1 : ℤ) : ℝ) * (h 129 3 - h 125 3) - ((0 : ℤ) : ℝ) * (h 129 2 - h 125 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 378 1
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 1 - h 128 1) - ((-10152046806426074108734264 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 378 2
  change ((-395436308798036478554666224 : ℤ) : ℝ) * (h 129 2 - h 128 2) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 129 0 - h 128 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 379 1
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 1 - h 128 1) - ((9805906347399177090242376 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 379 2
  change ((-212444332750858175578384 : ℤ) : ℝ) * (h 130 2 - h 128 2) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 130 0 - h 128 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 381 1
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 1 - h 129 1) - ((21480891409450766409856768 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 381 2
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 2 - h 129 2) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 381 3
  change ((5394084408894845884406488 : ℤ) : ℝ) * (h 131 3 - h 129 3) - ((2798542402819443398557312 : ℤ) : ℝ) * (h 131 0 - h 129 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 384 1
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 1 - h 130 1) - ((-354384320256255433150255536 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 384 2
  change ((-599128311074166242988148304 : ℤ) : ℝ) * (h 131 2 - h 130 2) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 131 0 - h 130 0) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  linear_combination ((-2572189708473753123674 : ℝ) / 37342929654445675402238334132661752886837535495) * r0 + ((-966547471183077455310866171655847876422317424 : ℝ) / 37342929654445675402238334132661752886837535495) * r1 + ((-546447126325330893637933993956292161633062816 : ℝ) / 37342929654445675402238334132661752886837535495) * r2 + (1 : ℝ) * r3 + ((-12022946672798937031965841614448094099757829242139217876742154611350046 : ℝ) / 5328215736818381683646581232876242624208258374910591399438759871701684812121995025547054710357945) * r4 + ((-5941419288763714401374365889897071826370617466192 : ℝ) / 157143292425449463409791239290003972799831251123278292866370603450840550605) * r5 + ((26828741341313881674935862507861395385105380516 : ℝ) / 6494131859073651443120266851818381572606404441343479678591532554496735) * r6 + ((5941419288763714401374365889897071826370617466192 : ℝ) / 84423714167957468760563469073638960443883257737465235821689923208457555) * r7 + ((12495578158968109273257798976264211549227163528 : ℝ) / 76797971221444842410515926228015148137661200092827107487226051341984285) * r8 + ((2767236381068031365023677263787677288994534162336 : ℝ) / 998373625878782951336707040964196925789595601206752397333938667445795705) * r9 + ((1 : ℝ) / 5394084408894845884406488) * r10 + ((26828741341313881674935862507861395385105380516 : ℝ) / 18314530692530394610898821298802704864312175805995479201725849868567241035) * r11 + ((5941419288763714401374365889897071826370617466192 : ℝ) / 238088899002895129941684676884435163236058285477941229622436048291374133455) * r12 + ((546447126325330893637933993956292161633062816 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_389 h H) + ((966547471183077455310866171655847876422317424 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_388 h H) + ((-966547471183077455310866171655847876422317424 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_500 h H) + ((-546447126325330893637933993956292161633062816 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_501 h H) + (1 : ℝ) * (value_503 h H)

/-- Coordinate 32.0, recovered from two neighbors at 32. -/
theorem value_128 (h : Assignment) (H : Constraints h) :
    h 32 0 = ((112817147970305496707393382 : ℝ) / 99448739493259146500761579) * (h 1 0) + ((-1984243624967293010630333118 : ℝ) / 672741473042635402799269505) * (h 1 1) + ((366881573866853714432956137 : ℝ) / 156665822489380847227227145) * (h 1 2) + ((-13368408477046350206631803 : ℝ) / 99448739493259146500761579) * (h 3 0) + ((1984243624967293010630333118 : ℝ) / 672741473042635402799269505) * (h 5 1) + ((-366881573866853714432956137 : ℝ) / 156665822489380847227227145) * (h 9 2) := by
  have r0 := H 127 1
  change ((-12035581224106133733304720 : ℤ) : ℝ) * (h 40 1 - h 32 1) - ((-20032669745265332008074039 : ℤ) : ℝ) * (h 40 0 - h 32 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 128 1
  change ((99899854154610765433865151968 : ℤ) : ℝ) * (h 48 1 - h 32 1) - ((-56343171481588377127991079093 : ℤ) : ℝ) * (h 48 0 - h 32 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-367278875568421931742151294 : ℝ) / 9850675009815762891401758136805159333529898233532271) * r0 + ((-486246817392781744235 : ℝ) / 108249175932041350454964375129727025643185694873981) * r1 + ((-2857410949451914678224745998016663928457316641440 : ℝ) / 6367598584237726497350845595866295626069746757293) * (value_161 h H) + ((26950829372434419600671039786575070924839104365042 : ℝ) / 36083058644013783484988125043242341881061898291327) * (value_160 h H) + ((2857410949451914678224745998016663928457316641440 : ℝ) / 6367598584237726497350845595866295626069746757293) * (value_193 h H) + ((9132229271579363884317085256667270956222793926285 : ℝ) / 36083058644013783484988125043242341881061898291327) * (value_192 h H)

/-- Coordinate 32.1, recovered from two neighbors at 32. -/
theorem value_129 (h : Assignment) (H : Constraints h) :
    h 32 1 = ((-5909849546842025310538840485 : ℝ) / 27050057142166487848207149488) * (h 1 0) + ((311320032115710761794896047581 : ℝ) / 182985680667596829561401305360) * (h 1 1) + ((-86072801708468017563560514833 : ℝ) / 85226207434223180891611566880) * (h 1 2) + ((5909849546842025310538840485 : ℝ) / 27050057142166487848207149488) * (h 3 0) + ((-128334351448113932233494742221 : ℝ) / 182985680667596829561401305360) * (h 5 1) + ((86072801708468017563560514833 : ℝ) / 85226207434223180891611566880) * (h 9 2) := by
  have r0 := H 127 1
  change ((-12035581224106133733304720 : ℤ) : ℝ) * (h 40 1 - h 32 1) - ((-20032669745265332008074039 : ℤ) : ℝ) * (h 40 0 - h 32 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 128 1
  change ((99899854154610765433865151968 : ℤ) : ℝ) * (h 48 1 - h 32 1) - ((-56343171481588377127991079093 : ℤ) : ℝ) * (h 48 0 - h 32 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((18781057160529459042663693031 : ℝ) / 893127867556629168820426071070334446240044106506925904) * r0 + ((-73379742656649567795143 : ℝ) / 9814591951171749107916770011761916991648836335240944) * r1 + ((9132229271579363884317085256667270956222793926285 : ℝ) / 36083058644013783484988125043242341881061898291327) * (value_161 h H) + ((-4134447423778432065443321076858606626963413334245299 : ℝ) / 9814591951171749107916770011761916991648836335240944) * (value_160 h H) + ((26950829372434419600671039786575070924839104365042 : ℝ) / 36083058644013783484988125043242341881061898291327) * (value_193 h H) + ((4134447423778432065443321076858606626963413334245299 : ℝ) / 9814591951171749107916770011761916991648836335240944) * (value_192 h H)

/-- Coordinate 32.2, recovered from two neighbors at 32. -/
theorem value_130 (h : Assignment) (H : Constraints h) :
    h 32 2 = ((77075308907547833268126965 : ℝ) / 198897478986518293001523158) * (h 1 0) + ((-2092699072455672553385462919 : ℝ) / 1345482946085270805598539010) * (h 1 1) + ((865772837261564378051233647 : ℝ) / 626663289957523388908908580) * (h 1 2) + ((-77075308907547833268126965 : ℝ) / 198897478986518293001523158) * (h 3 0) + ((2092699072455672553385462919 : ℝ) / 1345482946085270805598539010) * (h 5 1) + ((-239109547304040989142325067 : ℝ) / 626663289957523388908908580) * (h 9 2) := by
  have r0 := H 127 1
  change ((-12035581224106133733304720 : ℤ) : ℝ) * (h 40 1 - h 32 1) - ((-20032669745265332008074039 : ℤ) : ℝ) * (h 40 0 - h 32 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 127 2
  change ((-12035581224106133733304720 : ℤ) : ℝ) * (h 40 2 - h 32 2) - ((1063681291848446559935824 : ℤ) : ℝ) * (h 40 0 - h 32 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 128 1
  change ((99899854154610765433865151968 : ℤ) : ℝ) * (h 48 1 - h 32 1) - ((-56343171481588377127991079093 : ℤ) : ℝ) * (h 48 0 - h 32 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((1436278194239940800372538643440972722435163009398 : ℝ) / 435877202915110663490272821760366913540628664762155721928043456937204399335) * r0 + ((1 : ℝ) / 12035581224106133733304720) * r1 + ((3910592984736935882117 : ℝ) / 9850675009815762891401758136805159333529898233532271) * r2 + ((22980451107839052805960618295055563558962608150368 : ℝ) / 579451471165633111258926949223832901972346954913663) * (value_161 h H) + ((73445070377909899183240570812928485465168890426627 : ℝ) / 3283558336605254297133919378935053111176632744510757) * (value_160 h H) + (1 : ℝ) * (value_162 h H) + ((-22980451107839052805960618295055563558962608150368 : ℝ) / 579451471165633111258926949223832901972346954913663) * (value_193 h H) + ((-73445070377909899183240570812928485465168890426627 : ℝ) / 3283558336605254297133919378935053111176632744510757) * (value_192 h H)

/-- Coordinate 32.3, recovered from two neighbors at 32. -/
theorem value_131 (h : Assignment) (H : Constraints h) :
    h 32 3 = ((-1591472348546978811637752 : ℝ) / 5849925852544655676515387) * (h 1 0) + ((141879948728109196051564326 : ℝ) / 672741473042635402799269505) * (h 1 1) + ((-1622753227103486375895987 : ℝ) / 9215636617022402778072185) * (h 1 2) + h 1 3 + ((1591472348546978811637752 : ℝ) / 5849925852544655676515387) * (h 3 0) + ((-141879948728109196051564326 : ℝ) / 672741473042635402799269505) * (h 5 1) + ((1622753227103486375895987 : ℝ) / 9215636617022402778072185) * (h 9 2) := by
  have r0 := H 127 1
  change ((-12035581224106133733304720 : ℤ) : ℝ) * (h 40 1 - h 32 1) - ((-20032669745265332008074039 : ℤ) : ℝ) * (h 40 0 - h 32 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 127 3
  change ((-12035581224106133733304720 : ℤ) : ℝ) * (h 40 3 - h 32 3) - ((424018814222015381435136 : ℤ) : ℝ) * (h 40 0 - h 32 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 128 1
  change ((99899854154610765433865151968 : ℤ) : ℝ) * (h 48 1 - h 32 1) - ((-56343171481588377127991079093 : ℤ) : ℝ) * (h 48 0 - h 32 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((23936968842656066399540697561727305604270688 : ℝ) / 18223052925085106546689778910504908798052956426362127259837094232083465) * r0 + ((1 : ℝ) / 12035581224106133733304720) * r1 + ((4366646216654467184 : ℝ) / 27592927198363481488520330915420614379635569281603) * r2 + ((436227320188564154065229672364918417332229018112 : ℝ) / 27592927198363481488520330915420614379635569281603) * (value_161 h H) + ((246030696584391757432707446229291491199116984112 : ℝ) / 27592927198363481488520330915420614379635569281603) * (value_160 h H) + (1 : ℝ) * (value_163 h H) + ((-436227320188564154065229672364918417332229018112 : ℝ) / 27592927198363481488520330915420614379635569281603) * (value_193 h H) + ((-246030696584391757432707446229291491199116984112 : ℝ) / 27592927198363481488520330915420614379635569281603) * (value_192 h H)

/-- Coordinate 33.0, recovered from two neighbors at 33. -/
theorem value_132 (h : Assignment) (H : Constraints h) :
    h 33 0 = ((248188985144700158346517812229 : ℝ) / 136327612943766967013763139239) * (h 1 0) + ((-1964305101213638443870359895770 : ℝ) / 348392788634071137924061355833) * (h 1 1) + ((16975711837127100659582949221 : ℝ) / 3904775962274769914466441099) * (h 1 2) + ((-111861372200933191332754672990 : ℝ) / 136327612943766967013763139239) * (h 3 0) + ((1964305101213638443870359895770 : ℝ) / 348392788634071137924061355833) * (h 5 1) + ((-16975711837127100659582949221 : ℝ) / 3904775962274769914466441099) * (h 9 2) := by
  have r0 := H 124 1
  change ((-1951492631223785880474865952 : ℤ) : ℝ) * (h 33 1 - h 32 1) - ((160826491989070654333407771 : ℤ) : ℝ) * (h 33 0 - h 32 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 131 1
  change ((-20353902448394358239263696 : ℤ) : ℝ) * (h 41 1 - h 33 1) - ((-12812860834909581313518873 : ℤ) : ℝ) * (h 41 0 - h 33 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-1272118903024647389953981 : ℝ) / 1767353139580307103791189070204704177874022978855857) * r0 + ((-121968289451486617529679122 : ℝ) / 1767353139580307103791189070204704177874022978855857) * r1 + ((2482530665293085241650668682406560659883092423754912 : ℝ) / 1767353139580307103791189070204704177874022978855857) * (value_129 h H) + ((68196806855479600681030771905420287306366199262117 : ℝ) / 589117713193435701263729690068234725958007659618619) * (value_128 h H) + ((-2482530665293085241650668682406560659883092423754912 : ℝ) / 1767353139580307103791189070204704177874022978855857) * (value_165 h H) + ((520920906337956100582698918162814438651641460356502 : ℝ) / 589117713193435701263729690068234725958007659618619) * (value_164 h H)

/-- Coordinate 33.1, recovered from two neighbors at 33. -/
theorem value_133 (h : Assignment) (H : Constraints h) :
    h 33 1 = ((-6798743945144548393304339320733 : ℝ) / 24720740480469743351829049248672) * (h 1 0) + ((53594430646451029868762249627027 : ℝ) / 27871423090725691033924908466640) * (h 1 1) + ((-4160667383113056795758699869223 : ℝ) / 3540330205795791389116239929760) * (h 1 2) + ((6798743945144548393304339320733 : ℝ) / 24720740480469743351829049248672) * (h 3 0) + ((-25723007555725338834837341160387 : ℝ) / 27871423090725691033924908466640) * (h 5 1) + ((4160667383113056795758699869223 : ℝ) / 3540330205795791389116239929760) * (h 9 2) := by
  have r0 := H 124 1
  change ((-1951492631223785880474865952 : ℤ) : ℝ) * (h 33 1 - h 32 1) - ((160826491989070654333407771 : ℤ) : ℝ) * (h 33 0 - h 32 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 131 1
  change ((-20353902448394358239263696 : ℤ) : ℝ) * (h 41 1 - h 33 1) - ((-12812860834909581313518873 : ℤ) : ℝ) * (h 41 0 - h 33 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-4270953611636527104506291 : ℝ) / 9425883411094971220219675041091755615328122553897904) * r0 + ((53608830663023551444469257 : ℝ) / 9425883411094971220219675041091755615328122553897904) * r1 + ((520920906337956100582698918162814438651641460356502 : ℝ) / 589117713193435701263729690068234725958007659618619) * (value_129 h H) + ((686882486807554304933108066197778750578840537787361 : ℝ) / 9425883411094971220219675041091755615328122553897904) * (value_128 h H) + ((68196806855479600681030771905420287306366199262117 : ℝ) / 589117713193435701263729690068234725958007659618619) * (value_165 h H) + ((-686882486807554304933108066197778750578840537787361 : ℝ) / 9425883411094971220219675041091755615328122553897904) * (value_164 h H)

/-- Coordinate 33.2, recovered from two neighbors at 33. -/
theorem value_134 (h : Assignment) (H : Constraints h) :
    h 33 2 = ((1263524282708508219959261271881 : ℝ) / 545310451775067868055052556956) * (h 1 0) + ((-31762477745279768535251075617161 : ℝ) / 3483927886340711379240613558330) * (h 1 1) + ((548386529897423773218425216531 : ℝ) / 78095519245495398289328821980) * (h 1 2) + ((-1263524282708508219959261271881 : ℝ) / 545310451775067868055052556956) * (h 3 0) + ((31762477745279768535251075617161 : ℝ) / 3483927886340711379240613558330) * (h 5 1) + ((-470291010651928374929096394551 : ℝ) / 78095519245495398289328821980) * (h 9 2) := by
  have r0 := H 124 1
  change ((-1951492631223785880474865952 : ℤ) : ℝ) * (h 33 1 - h 32 1) - ((160826491989070654333407771 : ℤ) : ℝ) * (h 33 0 - h 32 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 124 2
  change ((-1951492631223785880474865952 : ℤ) : ℝ) * (h 33 2 - h 32 2) - ((-5488233813412626149001534664 : ℤ) : ℝ) * (h 33 0 - h 32 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 131 1
  change ((-20353902448394358239263696 : ℤ) : ℝ) * (h 41 1 - h 33 1) - ((-12812860834909581313518873 : ℤ) : ℝ) * (h 41 0 - h 33 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((-51335926310744465455696706013554094740523715708069 : ℝ) / 25360122269567591354532759707877763678473355891042942591601261836936929449124) * r0 + ((-1 : ℝ) / 1951492631223785880474865952) * r1 + ((-686029226676578268625191833 : ℝ) / 3534706279160614207582378140409408355748045957711714) * r2 + ((6981685978261247301974752017843356884711225336297384 : ℝ) / 1767353139580307103791189070204704177874022978855857) * (value_129 h H) + ((-2929999003362545682772023397879697870104458630321403 : ℝ) / 1178235426386871402527459380136469451916015319237238) * (value_128 h H) + (1 : ℝ) * (value_130 h H) + ((-6981685978261247301974752017843356884711225336297384 : ℝ) / 1767353139580307103791189070204704177874022978855857) * (value_165 h H) + ((2929999003362545682772023397879697870104458630321403 : ℝ) / 1178235426386871402527459380136469451916015319237238) * (value_164 h H)

/-- Coordinate 33.3, recovered from two neighbors at 33. -/
theorem value_135 (h : Assignment) (H : Constraints h) :
    h 33 3 = ((-17152950526243690493712896468 : ℝ) / 45442537647922322337921046413) * (h 1 0) + ((1086975051893597234230446355038 : ℝ) / 1741963943170355689620306779165) * (h 1 1) + ((-3151362603300167409011141063 : ℝ) / 6507959937124616524110735165) * (h 1 2) + h 1 3 + ((17152950526243690493712896468 : ℝ) / 45442537647922322337921046413) * (h 3 0) + ((-1086975051893597234230446355038 : ℝ) / 1741963943170355689620306779165) * (h 5 1) + ((3151362603300167409011141063 : ℝ) / 6507959937124616524110735165) * (h 9 2) := by
  have r0 := H 124 1
  change ((-1951492631223785880474865952 : ℤ) : ℝ) * (h 33 1 - h 32 1) - ((160826491989070654333407771 : ℤ) : ℝ) * (h 33 0 - h 32 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 124 3
  change ((-1951492631223785880474865952 : ℤ) : ℝ) * (h 33 3 - h 32 3) - ((299829981649537190485234560 : ℤ) : ℝ) * (h 33 0 - h 32 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 131 1
  change ((-20353902448394358239263696 : ℤ) : ℝ) * (h 41 1 - h 33 1) - ((-12812860834909581313518873 : ℤ) : ℝ) * (h 41 0 - h 33 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((233712859895777823342763319051931062176996562980 : ℝ) / 2113343522463965946211063308989813639872779657586911882633438486411410787427) * r0 + ((-1 : ℝ) / 1951492631223785880474865952) * r1 + ((6246457951032024801775720 : ℝ) / 589117713193435701263729690068234725958007659618619) * r2 + ((-127139795783303135898463245564250497824286130261120 : ℝ) / 589117713193435701263729690068234725958007659618619) * (value_129 h H) + ((80034996437687781890328853640824043934092133163560 : ℝ) / 589117713193435701263729690068234725958007659618619) * (value_128 h H) + (1 : ℝ) * (value_131 h H) + ((127139795783303135898463245564250497824286130261120 : ℝ) / 589117713193435701263729690068234725958007659618619) * (value_165 h H) + ((-80034996437687781890328853640824043934092133163560 : ℝ) / 589117713193435701263729690068234725958007659618619) * (value_164 h H)

/-- Coordinate 34.0, recovered from two neighbors at 34. -/
theorem value_136 (h : Assignment) (H : Constraints h) :
    h 34 0 = ((47128427535330902937778671320 : ℝ) / 107586134162768353110510708801) * (h 1 0) + ((-101071459026990958765575291254 : ℝ) / 458237238100680022507730796745) * (h 1 1) + ((51895347364531141739643630871 : ℝ) / 169485005872854254900119609755) * (h 1 2) + ((60457706627437450172732037481 : ℝ) / 107586134162768353110510708801) * (h 3 0) + ((101071459026990958765575291254 : ℝ) / 458237238100680022507730796745) * (h 5 1) + ((-51895347364531141739643630871 : ℝ) / 169485005872854254900119609755) * (h 9 2) := by
  have r0 := H 125 1
  change ((17194150916834982391170515008 : ℤ) : ℝ) * (h 34 1 - h 32 1) - ((-844264220977432187219834355 : ℤ) : ℝ) * (h 34 0 - h 32 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 135 1
  change ((21558470988799150178836624 : ℤ) : ℝ) * (h 42 1 - h 34 1) - ((-78748605165696715580633179 : ℤ) : ℝ) * (h 42 0 - h 34 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-7205371319785812225547 : ℝ) / 446462017377813210530560160114498579532763037525011) * r0 + ((-5746708194129339034482124 : ℝ) / 446462017377813210530560160114498579532763037525011) * r1 + ((-123890241884231710375559155699252513672802644509376 : ℝ) / 446462017377813210530560160114498579532763037525011) * (value_129 h H) + ((-6083237204152101174497213000148354250043239267185 : ℝ) / 446462017377813210530560160114498579532763037525011) * (value_128 h H) + ((123890241884231710375559155699252513672802644509376 : ℝ) / 446462017377813210530560160114498579532763037525011) * (value_169 h H) + ((452545254581965311705057373114646933782806276792196 : ℝ) / 446462017377813210530560160114498579532763037525011) * (value_168 h H)

/-- Coordinate 34.1, recovered from two neighbors at 34. -/
theorem value_137 (h : Assignment) (H : Constraints h) :
    h 34 1 = ((-39547306060431870991147220801695 : ℝ) / 214598475610001941671098693821728) * (h 1 0) + ((126405614996135471007217995458297 : ℝ) / 80649753905719683961360620227120) * (h 1 1) + ((-27966703486858654046268158158399 : ℝ) / 30733281064944238221888355902240) * (h 1 2) + ((39547306060431870991147220801695 : ℝ) / 214598475610001941671098693821728) * (h 3 0) + ((-45755861090415787045857375231177 : ℝ) / 80649753905719683961360620227120) * (h 5 1) + ((27966703486858654046268158158399 : ℝ) / 30733281064944238221888355902240) * (h 9 2) := by
  have r0 := H 125 1
  change ((17194150916834982391170515008 : ℤ) : ℝ) * (h 34 1 - h 32 1) - ((-844264220977432187219834355 : ℤ) : ℝ) * (h 34 0 - h 32 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 135 1
  change ((21558470988799150178836624 : ℤ) : ℝ) * (h 42 1 - h 34 1) - ((-78748605165696715580633179 : ℤ) : ℝ) * (h 42 0 - h 34 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((78748605165696715580633179 : ℝ) / 1335814355994417125907435999062579749962027008274832912) * r0 + ((844264220977432187219834355 : ℝ) / 1335814355994417125907435999062579749962027008274832912) * r1 + ((452545254581965311705057373114646933782806276792196 : ℝ) / 446462017377813210530560160114498579532763037525011) * (value_129 h H) + ((66484629793276329723863204887001248590019418397064545 : ℝ) / 1335814355994417125907435999062579749962027008274832912) * (value_128 h H) + ((-6083237204152101174497213000148354250043239267185 : ℝ) / 446462017377813210530560160114498579532763037525011) * (value_169 h H) + ((-66484629793276329723863204887001248590019418397064545 : ℝ) / 1335814355994417125907435999062579749962027008274832912) * (value_168 h H)

/-- Coordinate 34.2, recovered from two neighbors at 34. -/
theorem value_138 (h : Assignment) (H : Constraints h) :
    h 34 2 = ((1547308847835853480810011144365 : ℝ) / 4733789903161807536862471187244) * (h 1 0) + ((-13283879343489716995631629035751 : ℝ) / 10081219238214960495170077528390) * (h 1 1) + ((816426342946694642186882152823 : ℝ) / 677940023491417019600478439020) * (h 1 2) + ((-1547308847835853480810011144365 : ℝ) / 4733789903161807536862471187244) * (h 3 0) + ((13283879343489716995631629035751 : ℝ) / 10081219238214960495170077528390) * (h 5 1) + ((-138486319455277622586403713803 : ℝ) / 677940023491417019600478439020) * (h 9 2) := by
  have r0 := H 125 1
  change ((17194150916834982391170515008 : ℤ) : ℝ) * (h 34 1 - h 32 1) - ((-844264220977432187219834355 : ℤ) : ℝ) * (h 34 0 - h 32 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 125 2
  change ((17194150916834982391170515008 : ℤ) : ℝ) * (h 34 2 - h 32 2) - ((1497463144489500760637895320 : ℤ) : ℝ) * (h 34 0 - h 32 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 135 1
  change ((21558470988799150178836624 : ℤ) : ℝ) * (h 42 1 - h 34 1) - ((-78748605165696715580633179 : ℤ) : ℝ) * (h 42 0 - h 34 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((-7212418445013988317897646059588329503205358115 : ℝ) / 5131373867265189074036009573777326120208440803022984898846357040566164806728) * r0 + ((1 : ℝ) / 17194150916834982391170515008) * r1 + ((-11010758415363976181160995 : ℝ) / 9822164382311890631672323522518968749720786825550242) * r2 + ((-10789777993740926523574878505144140936795215740040 : ℝ) / 446462017377813210530560160114498579532763037525011) * (value_129 h H) + ((-867081867026370196997283681132384689779213437653105 : ℝ) / 9822164382311890631672323522518968749720786825550242) * (value_128 h H) + (1 : ℝ) * (value_130 h H) + ((10789777993740926523574878505144140936795215740040 : ℝ) / 446462017377813210530560160114498579532763037525011) * (value_169 h H) + ((867081867026370196997283681132384689779213437653105 : ℝ) / 9822164382311890631672323522518968749720786825550242) * (value_168 h H)

/-- Coordinate 34.3, recovered from two neighbors at 34. -/
theorem value_139 (h : Assignment) (H : Constraints h) :
    h 34 3 = ((-90522909293153379877888390004 : ℝ) / 394482491930150628071872598937) * (h 1 0) + ((44404666411918119634893459450 : ℝ) / 1008121923821496049517007752839) * (h 1 1) + ((-583319456784811150219555663 : ℝ) / 11299000391523616993341307317) * (h 1 2) + h 1 3 + ((90522909293153379877888390004 : ℝ) / 394482491930150628071872598937) * (h 3 0) + ((-44404666411918119634893459450 : ℝ) / 1008121923821496049517007752839) * (h 5 1) + ((583319456784811150219555663 : ℝ) / 11299000391523616993341307317) * (h 9 2) := by
  have r0 := H 125 1
  change ((17194150916834982391170515008 : ℤ) : ℝ) * (h 34 1 - h 32 1) - ((-844264220977432187219834355 : ℤ) : ℝ) * (h 34 0 - h 32 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 125 3
  change ((17194150916834982391170515008 : ℤ) : ℝ) * (h 34 3 - h 32 3) - ((-1051281162811604289287566464 : ℤ) : ℝ) * (h 34 0 - h 32 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 135 1
  change ((21558470988799150178836624 : ℤ) : ℝ) * (h 42 1 - h 34 1) - ((-78748605165696715580633179 : ℤ) : ℝ) * (h 42 0 - h 34 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((21825071280753885466515982739761201797181914 : ℝ) / 22117990807177539112224179197316060862967417254409417667441194140371400029) * r0 + ((1 : ℝ) / 17194150916834982391170515008) * r1 + ((133276009484229752698728 : ℝ) / 169347661763998114339177991767568426719323910785349) * r2 + ((261202453088062501263263281429462063108673146752 : ℝ) / 15395241978545283121743453797051675156302173707759) * (value_129 h H) + ((10495299848933259561750002673144085954366267896312 : ℝ) / 169347661763998114339177991767568426719323910785349) * (value_128 h H) + (1 : ℝ) * (value_131 h H) + ((-261202453088062501263263281429462063108673146752 : ℝ) / 15395241978545283121743453797051675156302173707759) * (value_169 h H) + ((-10495299848933259561750002673144085954366267896312 : ℝ) / 169347661763998114339177991767568426719323910785349) * (value_168 h H)

/-- Coordinate 35.0, recovered from two neighbors at 35. -/
theorem value_140 (h : Assignment) (H : Constraints h) :
    h 35 0 = ((995241164561013775600388003 : ℝ) / 6447805832543473930300854657) * (h 1 0) + ((220271233488555718042254873846 : ℝ) / 247165890247499833994866095185) * (h 1 1) + ((-483042981283910047794284161 : ℝ) / 923409303539849940204979185) * (h 1 2) + ((5452564667982460154700466654 : ℝ) / 6447805832543473930300854657) * (h 3 0) + ((-220271233488555718042254873846 : ℝ) / 247165890247499833994866095185) * (h 5 1) + ((483042981283910047794284161 : ℝ) / 923409303539849940204979185) * (h 9 2) := by
  have r0 := H 129 1
  change ((73729387007466512522564224 : ℤ) : ℝ) * (h 35 1 - h 33 1) - ((-1291497930333323163387291 : ℤ) : ℝ) * (h 35 0 - h 33 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 133 1
  change ((3705282971359406668600901392 : ℤ) : ℝ) * (h 35 1 - h 34 1) - ((803888495173389799591003707 : ℤ) : ℝ) * (h 35 0 - h 34 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((33082883672851845255365191 : ℝ) / 571924743395524212425355512908177134891696501130245) * r0 + ((-658298098280951004665752 : ℝ) / 571924743395524212425355512908177134891696501130245) * r1 + ((2439180733638688857722817804575338645821784871526784 : ℝ) / 571924743395524212425355512908177134891696501130245) * (value_133 h H) + ((14242158597648748927931067654000654061671591062527 : ℝ) / 190641581131841404141785170969392378297232167043415) * (value_132 h H) + ((-2439180733638688857722817804575338645821784871526784 : ℝ) / 571924743395524212425355512908177134891696501130245) * (value_137 h H) + ((176399422534192655213854103315391724235560575980888 : ℝ) / 190641581131841404141785170969392378297232167043415) * (value_136 h H)

/-- Coordinate 35.1, recovered from two neighbors at 35. -/
theorem value_141 (h : Assignment) (H : Constraints h) :
    h 35 1 = ((-6036067200865735745129766329731 : ℝ) / 24553244610325548726585654533856) * (h 1 0) + ((50065150264149713684641216176353 : ℝ) / 27682579707719981407425002660720) * (h 1 1) + ((-3832477161397923488018079703357 : ℝ) / 3516342627879748572300560736480) * (h 1 2) + ((6036067200865735745129766329731 : ℝ) / 24553244610325548726585654533856) * (h 3 0) + ((-22382570556429732277216213515633 : ℝ) / 27682579707719981407425002660720) * (h 5 1) + ((3832477161397923488018079703357 : ℝ) / 3516342627879748572300560736480) * (h 9 2) := by
  have r0 := H 129 1
  change ((73729387007466512522564224 : ℤ) : ℝ) * (h 35 1 - h 33 1) - ((-1291497930333323163387291 : ℤ) : ℝ) * (h 35 0 - h 33 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 133 1
  change ((3705282971359406668600901392 : ℤ) : ℝ) * (h 35 1 - h 34 1) - ((803888495173389799591003707 : ℤ) : ℝ) * (h 35 0 - h 34 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((267962831724463266530334569 : ℝ) / 21351857086766237263879939148571946369290002708862480) * r0 + ((430499310111107721129097 : ℝ) / 21351857086766237263879939148571946369290002708862480) * r1 + ((176399422534192655213854103315391724235560575980888 : ℝ) / 190641581131841404141785170969392378297232167043415) * (value_133 h H) + ((115357814192800285941859937203181475648373850854193 : ℝ) / 7117285695588745754626646382857315456430000902954160) * (value_132 h H) + ((14242158597648748927931067654000654061671591062527 : ℝ) / 190641581131841404141785170969392378297232167043415) * (value_137 h H) + ((-115357814192800285941859937203181475648373850854193 : ℝ) / 7117285695588745754626646382857315456430000902954160) * (value_136 h H)

/-- Coordinate 35.2, recovered from two neighbors at 35. -/
theorem value_142 (h : Assignment) (H : Constraints h) :
    h 35 2 = ((308714914906482671272344739813 : ℝ) / 180538563311217270048423930396) * (h 1 0) + ((-23314774412723819810537136333987 : ℝ) / 3460322463464997675928125332590) * (h 1 1) + ((135671876390153544723917112379 : ℝ) / 25855460499115798325739417180) * (h 1 2) + ((-308714914906482671272344739813 : ℝ) / 180538563311217270048423930396) * (h 3 0) + ((23314774412723819810537136333987 : ℝ) / 3460322463464997675928125332590) * (h 5 1) + ((-109816415891037746398177695199 : ℝ) / 25855460499115798325739417180) * (h 9 2) := by
  have r0 := H 129 1
  change ((73729387007466512522564224 : ℤ) : ℝ) * (h 35 1 - h 33 1) - ((-1291497930333323163387291 : ℤ) : ℝ) * (h 35 0 - h 33 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 129 2
  change ((73729387007466512522564224 : ℤ) : ℝ) * (h 35 2 - h 33 2) - ((26864806154821569968945336 : ℤ) : ℝ) * (h 35 0 - h 33 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 133 1
  change ((3705282971359406668600901392 : ℤ) : ℝ) * (h 35 1 - h 34 1) - ((803888495173389799591003707 : ℤ) : ℝ) * (h 35 0 - h 34 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((111095657114209534857289692323641977223063724524897 : ℝ) / 5270957593119322748038282152629523577955401927644476173135586751510200169360) * r0 + ((1 : ℝ) / 73729387007466512522564224) * r1 + ((-3358100769352696246118167 : ℝ) / 8006946407537338973954977180714479888483751015823430) * r2 + ((888765256913676278858317538589135817784509796199176 : ℝ) / 571924743395524212425355512908177134891696501130245) * (value_133 h H) + ((-899846191371847176296180742392714659426418019015023 : ℝ) / 2668982135845779657984992393571493296161250338607810) * (value_132 h H) + (1 : ℝ) * (value_134 h H) + ((-888765256913676278858317538589135817784509796199176 : ℝ) / 571924743395524212425355512908177134891696501130245) * (value_137 h H) + ((899846191371847176296180742392714659426418019015023 : ℝ) / 2668982135845779657984992393571493296161250338607810) * (value_136 h H)

/-- Coordinate 35.3, recovered from two neighbors at 35. -/
theorem value_143 (h : Assignment) (H : Constraints h) :
    h 35 3 = ((-3903285373919911398449457656 : ℝ) / 15044880275934772504035327533) * (h 1 0) + ((55881888235985827100922492258 : ℝ) / 346032246346499767592812533259) * (h 1 1) + ((-59999240782588592547411283 : ℝ) / 430924341651929972095656953) * (h 1 2) + h 1 3 + ((3903285373919911398449457656 : ℝ) / 15044880275934772504035327533) * (h 3 0) + ((-55881888235985827100922492258 : ℝ) / 346032246346499767592812533259) * (h 5 1) + ((59999240782588592547411283 : ℝ) / 430924341651929972095656953) * (h 9 2) := by
  have r0 := H 129 1
  change ((73729387007466512522564224 : ℤ) : ℝ) * (h 35 1 - h 33 1) - ((-1291497930333323163387291 : ℤ) : ℝ) * (h 35 0 - h 33 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 129 3
  change ((73729387007466512522564224 : ℤ) : ℝ) * (h 35 3 - h 33 3) - ((-5222532513945999136338528 : ℤ) : ℝ) * (h 35 0 - h 33 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 133 1
  change ((3705282971359406668600901392 : ℤ) : ℝ) * (h 35 1 - h 34 1) - ((803888495173389799591003707 : ℤ) : ℝ) * (h 35 0 - h 34 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((-1799754537880854131878076379141034817927950451863 : ℝ) / 439246466093276895669856846052460298162950160637039681094632229292516680780) * r0 + ((1 : ℝ) / 73729387007466512522564224) * r1 + ((108802760707208315340386 : ℝ) / 1334491067922889828992496196785746648080625169303905) * r2 + ((-57592145212187332220098444132513114173694414459616 : ℝ) / 190641581131841404141785170969392378297232167043415) * (value_133 h H) + ((29155095858542705714813032272287400369935697603634 : ℝ) / 444830355974296609664165398928582216026875056434635) * (value_132 h H) + (1 : ℝ) * (value_135 h H) + ((57592145212187332220098444132513114173694414459616 : ℝ) / 190641581131841404141785170969392378297232167043415) * (value_137 h H) + ((-29155095858542705714813032272287400369935697603634 : ℝ) / 444830355974296609664165398928582216026875056434635) * (value_136 h H)

/-- Coordinate 36.0, recovered from two neighbors at 36. -/
theorem value_144 (h : Assignment) (H : Constraints h) :
    h 36 0 = ((112817147970305496707393382 : ℝ) / 99448739493259146500761579) * (h 1 0) + ((-1984243624967293010630333118 : ℝ) / 672741473042635402799269505) * (h 1 1) + ((366881573866853714432956137 : ℝ) / 156665822489380847227227145) * (h 1 2) + ((-13368408477046350206631803 : ℝ) / 99448739493259146500761579) * (h 3 0) + ((1984243624967293010630333118 : ℝ) / 672741473042635402799269505) * (h 5 1) + ((-366881573866853714432956137 : ℝ) / 156665822489380847227227145) * (h 9 2) := by
  have r0 := H 126 0
  change ((1 : ℤ) : ℝ) * (h 36 0 - h 32 0) - ((0 : ℤ) : ℝ) * (h 36 1 - h 32 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_128 h H)

/-- Coordinate 36.1, recovered from two neighbors at 36. -/
theorem value_145 (h : Assignment) (H : Constraints h) :
    h 36 1 = ((2372784085995988745127732027 : ℝ) / 27050057142166487848207149488) * (h 1 0) + ((40088177460136010626570783269 : ℝ) / 182985680667596829561401305360) * (h 1 1) + ((13602766033558799983759603543 : ℝ) / 85226207434223180891611566880) * (h 1 2) + ((-2372784085995988745127732027 : ℝ) / 27050057142166487848207149488) * (h 3 0) + ((142897503207460818934830522091 : ℝ) / 182985680667596829561401305360) * (h 5 1) + ((-13602766033558799983759603543 : ℝ) / 85226207434223180891611566880) * (h 9 2) := by
  have r0 := H 126 0
  change ((1 : ℤ) : ℝ) * (h 36 0 - h 32 0) - ((0 : ℤ) : ℝ) * (h 36 1 - h 32 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 142 1
  change ((-12035581224106133733304720 : ℤ) : ℝ) * (h 44 1 - h 36 1) - ((17748015699771271771053753 : ℤ) : ℝ) * (h 44 0 - h 36 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-17748015699771271771053753 : ℝ) / 12035581224106133733304720) * r0 + ((1 : ℝ) / 12035581224106133733304720) * r1 + ((-17748015699771271771053753 : ℝ) / 12035581224106133733304720) * (value_128 h H) + (1 : ℝ) * (value_177 h H) + ((17748015699771271771053753 : ℝ) / 12035581224106133733304720) * (value_176 h H)

/-- Coordinate 36.2, recovered from two neighbors at 36. -/
theorem value_146 (h : Assignment) (H : Constraints h) :
    h 36 2 = ((77075308907547833268126965 : ℝ) / 198897478986518293001523158) * (h 1 0) + ((-2092699072455672553385462919 : ℝ) / 1345482946085270805598539010) * (h 1 1) + ((865772837261564378051233647 : ℝ) / 626663289957523388908908580) * (h 1 2) + ((-77075308907547833268126965 : ℝ) / 198897478986518293001523158) * (h 3 0) + ((2092699072455672553385462919 : ℝ) / 1345482946085270805598539010) * (h 5 1) + ((-239109547304040989142325067 : ℝ) / 626663289957523388908908580) * (h 9 2) := by
  have r0 := H 126 2
  change ((1 : ℤ) : ℝ) * (h 36 2 - h 32 2) - ((0 : ℤ) : ℝ) * (h 36 1 - h 32 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_130 h H)

/-- Coordinate 36.3, recovered from two neighbors at 36. -/
theorem value_147 (h : Assignment) (H : Constraints h) :
    h 36 3 = ((-1591472348546978811637752 : ℝ) / 5849925852544655676515387) * (h 1 0) + ((141879948728109196051564326 : ℝ) / 672741473042635402799269505) * (h 1 1) + ((-1622753227103486375895987 : ℝ) / 9215636617022402778072185) * (h 1 2) + h 1 3 + ((1591472348546978811637752 : ℝ) / 5849925852544655676515387) * (h 3 0) + ((-141879948728109196051564326 : ℝ) / 672741473042635402799269505) * (h 5 1) + ((1622753227103486375895987 : ℝ) / 9215636617022402778072185) * (h 9 2) := by
  have r0 := H 126 3
  change ((1 : ℤ) : ℝ) * (h 36 3 - h 32 3) - ((0 : ℤ) : ℝ) * (h 36 1 - h 32 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_131 h H)

/-- Coordinate 37.0, recovered from two neighbors at 37. -/
theorem value_148 (h : Assignment) (H : Constraints h) :
    h 37 0 = ((248188985144700158346517812229 : ℝ) / 136327612943766967013763139239) * (h 1 0) + ((-1964305101213638443870359895770 : ℝ) / 348392788634071137924061355833) * (h 1 1) + ((16975711837127100659582949221 : ℝ) / 3904775962274769914466441099) * (h 1 2) + ((-111861372200933191332754672990 : ℝ) / 136327612943766967013763139239) * (h 3 0) + ((1964305101213638443870359895770 : ℝ) / 348392788634071137924061355833) * (h 5 1) + ((-16975711837127100659582949221 : ℝ) / 3904775962274769914466441099) * (h 9 2) := by
  have r0 := H 130 0
  change ((1 : ℤ) : ℝ) * (h 37 0 - h 33 0) - ((0 : ℤ) : ℝ) * (h 37 1 - h 33 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_132 h H)

/-- Coordinate 37.1, recovered from two neighbors at 37. -/
theorem value_149 (h : Assignment) (H : Constraints h) :
    h 37 1 = ((-1252121310167180136020707511333 : ℝ) / 24720740480469743351829049248672) * (h 1 0) + ((21218914265760986020066504979307 : ℝ) / 27871423090725691033924908466640) * (h 1 1) + ((-866914767777074946709400332943 : ℝ) / 3540330205795791389116239929760) * (h 1 2) + ((1252121310167180136020707511333 : ℝ) / 24720740480469743351829049248672) * (h 3 0) + ((6652508824964705013858403487333 : ℝ) / 27871423090725691033924908466640) * (h 5 1) + ((866914767777074946709400332943 : ℝ) / 3540330205795791389116239929760) * (h 9 2) := by
  have r0 := H 130 0
  change ((1 : ℤ) : ℝ) * (h 37 0 - h 33 0) - ((0 : ℤ) : ℝ) * (h 37 1 - h 33 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 140 1
  change ((-1951492631223785880474865952 : ℤ) : ℝ) * (h 37 1 - h 36 1) - ((393561582780227386244117187 : ℤ) : ℝ) * (h 37 0 - h 36 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-393561582780227386244117187 : ℝ) / 1951492631223785880474865952) * r0 + ((-1 : ℝ) / 1951492631223785880474865952) * r1 + ((-393561582780227386244117187 : ℝ) / 1951492631223785880474865952) * (value_132 h H) + (1 : ℝ) * (value_145 h H) + ((393561582780227386244117187 : ℝ) / 1951492631223785880474865952) * (value_144 h H)

/-- Coordinate 37.2, recovered from two neighbors at 37. -/
theorem value_150 (h : Assignment) (H : Constraints h) :
    h 37 2 = ((1263524282708508219959261271881 : ℝ) / 545310451775067868055052556956) * (h 1 0) + ((-31762477745279768535251075617161 : ℝ) / 3483927886340711379240613558330) * (h 1 1) + ((548386529897423773218425216531 : ℝ) / 78095519245495398289328821980) * (h 1 2) + ((-1263524282708508219959261271881 : ℝ) / 545310451775067868055052556956) * (h 3 0) + ((31762477745279768535251075617161 : ℝ) / 3483927886340711379240613558330) * (h 5 1) + ((-470291010651928374929096394551 : ℝ) / 78095519245495398289328821980) * (h 9 2) := by
  have r0 := H 130 2
  change ((1 : ℤ) : ℝ) * (h 37 2 - h 33 2) - ((0 : ℤ) : ℝ) * (h 37 1 - h 33 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_134 h H)

/-- Coordinate 37.3, recovered from two neighbors at 37. -/
theorem value_151 (h : Assignment) (H : Constraints h) :
    h 37 3 = ((-17152950526243690493712896468 : ℝ) / 45442537647922322337921046413) * (h 1 0) + ((1086975051893597234230446355038 : ℝ) / 1741963943170355689620306779165) * (h 1 1) + ((-3151362603300167409011141063 : ℝ) / 6507959937124616524110735165) * (h 1 2) + h 1 3 + ((17152950526243690493712896468 : ℝ) / 45442537647922322337921046413) * (h 3 0) + ((-1086975051893597234230446355038 : ℝ) / 1741963943170355689620306779165) * (h 5 1) + ((3151362603300167409011141063 : ℝ) / 6507959937124616524110735165) * (h 9 2) := by
  have r0 := H 130 3
  change ((1 : ℤ) : ℝ) * (h 37 3 - h 33 3) - ((0 : ℤ) : ℝ) * (h 37 1 - h 33 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_135 h H)

/-- Coordinate 38.0, recovered from two neighbors at 38. -/
theorem value_152 (h : Assignment) (H : Constraints h) :
    h 38 0 = ((47128427535330902937778671320 : ℝ) / 107586134162768353110510708801) * (h 1 0) + ((-101071459026990958765575291254 : ℝ) / 458237238100680022507730796745) * (h 1 1) + ((51895347364531141739643630871 : ℝ) / 169485005872854254900119609755) * (h 1 2) + ((60457706627437450172732037481 : ℝ) / 107586134162768353110510708801) * (h 3 0) + ((101071459026990958765575291254 : ℝ) / 458237238100680022507730796745) * (h 5 1) + ((-51895347364531141739643630871 : ℝ) / 169485005872854254900119609755) * (h 9 2) := by
  have r0 := H 134 0
  change ((1 : ℤ) : ℝ) * (h 38 0 - h 34 0) - ((0 : ℤ) : ℝ) * (h 38 1 - h 34 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_136 h H)

/-- Coordinate 38.1, recovered from two neighbors at 38. -/
theorem value_153 (h : Assignment) (H : Constraints h) :
    h 38 1 = ((15878106154893252875550704693249 : ℝ) / 214598475610001941671098693821728) * (h 1 0) + ((22007446485715685045187302588049 : ℝ) / 80649753905719683961360620227120) * (h 1 1) + ((3671927105646530133536206652777 : ℝ) / 30733281064944238221888355902240) * (h 1 2) + ((-15878106154893252875550704693249 : ℝ) / 214598475610001941671098693821728) * (h 3 0) + ((58642307420003998916173317639071 : ℝ) / 80649753905719683961360620227120) * (h 5 1) + ((-3671927105646530133536206652777 : ℝ) / 30733281064944238221888355902240) * (h 9 2) := by
  have r0 := H 134 0
  change ((1 : ℤ) : ℝ) * (h 38 0 - h 34 0) - ((0 : ℤ) : ℝ) * (h 38 1 - h 34 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 141 1
  change ((17194150916834982391170515008 : ℤ) : ℝ) * (h 38 1 - h 36 1) - ((338969155142284106446818861 : ℤ) : ℝ) * (h 38 0 - h 36 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((338969155142284106446818861 : ℝ) / 17194150916834982391170515008) * r0 + ((1 : ℝ) / 17194150916834982391170515008) * r1 + ((338969155142284106446818861 : ℝ) / 17194150916834982391170515008) * (value_136 h H) + (1 : ℝ) * (value_145 h H) + ((-338969155142284106446818861 : ℝ) / 17194150916834982391170515008) * (value_144 h H)

/-- Coordinate 38.2, recovered from two neighbors at 38. -/
theorem value_154 (h : Assignment) (H : Constraints h) :
    h 38 2 = ((1547308847835853480810011144365 : ℝ) / 4733789903161807536862471187244) * (h 1 0) + ((-13283879343489716995631629035751 : ℝ) / 10081219238214960495170077528390) * (h 1 1) + ((816426342946694642186882152823 : ℝ) / 677940023491417019600478439020) * (h 1 2) + ((-1547308847835853480810011144365 : ℝ) / 4733789903161807536862471187244) * (h 3 0) + ((13283879343489716995631629035751 : ℝ) / 10081219238214960495170077528390) * (h 5 1) + ((-138486319455277622586403713803 : ℝ) / 677940023491417019600478439020) * (h 9 2) := by
  have r0 := H 134 2
  change ((1 : ℤ) : ℝ) * (h 38 2 - h 34 2) - ((0 : ℤ) : ℝ) * (h 38 1 - h 34 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_138 h H)

/-- Coordinate 38.3, recovered from two neighbors at 38. -/
theorem value_155 (h : Assignment) (H : Constraints h) :
    h 38 3 = ((-90522909293153379877888390004 : ℝ) / 394482491930150628071872598937) * (h 1 0) + ((44404666411918119634893459450 : ℝ) / 1008121923821496049517007752839) * (h 1 1) + ((-583319456784811150219555663 : ℝ) / 11299000391523616993341307317) * (h 1 2) + h 1 3 + ((90522909293153379877888390004 : ℝ) / 394482491930150628071872598937) * (h 3 0) + ((-44404666411918119634893459450 : ℝ) / 1008121923821496049517007752839) * (h 5 1) + ((583319456784811150219555663 : ℝ) / 11299000391523616993341307317) * (h 9 2) := by
  have r0 := H 134 3
  change ((1 : ℤ) : ℝ) * (h 38 3 - h 34 3) - ((0 : ℤ) : ℝ) * (h 38 1 - h 34 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_139 h H)

/-- Coordinate 39.0, recovered from two neighbors at 39. -/
theorem value_156 (h : Assignment) (H : Constraints h) :
    h 39 0 = ((995241164561013775600388003 : ℝ) / 6447805832543473930300854657) * (h 1 0) + ((220271233488555718042254873846 : ℝ) / 247165890247499833994866095185) * (h 1 1) + ((-483042981283910047794284161 : ℝ) / 923409303539849940204979185) * (h 1 2) + ((5452564667982460154700466654 : ℝ) / 6447805832543473930300854657) * (h 3 0) + ((-220271233488555718042254873846 : ℝ) / 247165890247499833994866095185) * (h 5 1) + ((483042981283910047794284161 : ℝ) / 923409303539849940204979185) * (h 9 2) := by
  have r0 := H 137 0
  change ((1 : ℤ) : ℝ) * (h 39 0 - h 35 0) - ((0 : ℤ) : ℝ) * (h 39 1 - h 35 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_140 h H)

/-- Coordinate 39.1, recovered from two neighbors at 39. -/
theorem value_157 (h : Assignment) (H : Constraints h) :
    h 39 1 = ((-788878170848256898961871452059 : ℝ) / 24553244610325548726585654533856) * (h 1 0) + ((19065916879806632535296457286761 : ℝ) / 27682579707719981407425002660720) * (h 1 1) + ((-670662280877636424841122383989 : ℝ) / 3516342627879748572300560736480) * (h 1 2) + ((788878170848256898961871452059 : ℝ) / 24553244610325548726585654533856) * (h 3 0) + ((8616662827913348872128545373959 : ℝ) / 27682579707719981407425002660720) * (h 5 1) + ((670662280877636424841122383989 : ℝ) / 3516342627879748572300560736480) * (h 9 2) := by
  have r0 := H 137 0
  change ((1 : ℤ) : ℝ) * (h 39 0 - h 35 0) - ((0 : ℤ) : ℝ) * (h 39 1 - h 35 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 144 1
  change ((73729387007466512522564224 : ℤ) : ℝ) * (h 39 1 - h 37 1) - ((-819580206232539830401275 : ℤ) : ℝ) * (h 39 0 - h 37 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-819580206232539830401275 : ℝ) / 73729387007466512522564224) * r0 + ((1 : ℝ) / 73729387007466512522564224) * r1 + ((-819580206232539830401275 : ℝ) / 73729387007466512522564224) * (value_140 h H) + (1 : ℝ) * (value_149 h H) + ((819580206232539830401275 : ℝ) / 73729387007466512522564224) * (value_148 h H)

/-- Coordinate 39.2, recovered from two neighbors at 39. -/
theorem value_158 (h : Assignment) (H : Constraints h) :
    h 39 2 = ((308714914906482671272344739813 : ℝ) / 180538563311217270048423930396) * (h 1 0) + ((-23314774412723819810537136333987 : ℝ) / 3460322463464997675928125332590) * (h 1 1) + ((135671876390153544723917112379 : ℝ) / 25855460499115798325739417180) * (h 1 2) + ((-308714914906482671272344739813 : ℝ) / 180538563311217270048423930396) * (h 3 0) + ((23314774412723819810537136333987 : ℝ) / 3460322463464997675928125332590) * (h 5 1) + ((-109816415891037746398177695199 : ℝ) / 25855460499115798325739417180) * (h 9 2) := by
  have r0 := H 137 2
  change ((1 : ℤ) : ℝ) * (h 39 2 - h 35 2) - ((0 : ℤ) : ℝ) * (h 39 1 - h 35 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_142 h H)

/-- Coordinate 39.3, recovered from two neighbors at 39. -/
theorem value_159 (h : Assignment) (H : Constraints h) :
    h 39 3 = ((-3903285373919911398449457656 : ℝ) / 15044880275934772504035327533) * (h 1 0) + ((55881888235985827100922492258 : ℝ) / 346032246346499767592812533259) * (h 1 1) + ((-59999240782588592547411283 : ℝ) / 430924341651929972095656953) * (h 1 2) + h 1 3 + ((3903285373919911398449457656 : ℝ) / 15044880275934772504035327533) * (h 3 0) + ((-55881888235985827100922492258 : ℝ) / 346032246346499767592812533259) * (h 5 1) + ((59999240782588592547411283 : ℝ) / 430924341651929972095656953) * (h 9 2) := by
  have r0 := H 137 3
  change ((1 : ℤ) : ℝ) * (h 39 3 - h 35 3) - ((0 : ℤ) : ℝ) * (h 39 1 - h 35 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_143 h H)

/-- Coordinate 100.0, recovered from two neighbors at 100. -/
theorem value_400 (h : Assignment) (H : Constraints h) :
    h 100 0 = ((865772837261564378051233647 : ℝ) / 626663289957523388908908580) * (h 1 0) + ((77075308907547833268126965 : ℝ) / 198897478986518293001523158) * (h 1 1) + ((-2092699072455672553385462919 : ℝ) / 1345482946085270805598539010) * (h 1 2) + ((-239109547304040989142325067 : ℝ) / 626663289957523388908908580) * (h 3 0) + ((-77075308907547833268126965 : ℝ) / 198897478986518293001523158) * (h 5 1) + ((2092699072455672553385462919 : ℝ) / 1345482946085270805598539010) * (h 9 2) := by
  have r0 := H 307 1
  change ((1063681291848446559935824 : ℤ) : ℝ) * (h 108 1 - h 100 1) - ((-12035581224106133733304720 : ℤ) : ℝ) * (h 108 0 - h 100 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 308 1
  change ((-25538490756680155028498688968 : ℤ) : ℝ) * (h 116 1 - h 100 1) - ((99899854154610765433865151968 : ℤ) : ℝ) * (h 116 0 - h 100 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-187783020269707022268372713 : ℝ) / 1478742455297499570783975406611093198686917484992848) * r0 + ((-3910592984736935882117 : ℝ) / 739371227648749785391987703305546599343458742496424) * r1 + ((734342961719430114707281132263338199564787473421 : ℝ) / 5436553144476101363176380171364313230466608400709) * (value_433 h H) + ((8309109532955982963921457458246258675336934419505 : ℝ) / 5436553144476101363176380171364313230466608400709) * (value_432 h H) + ((-734342961719430114707281132263338199564787473421 : ℝ) / 5436553144476101363176380171364313230466608400709) * (value_465 h H) + ((-2872556388479881600745077286881945444870326018796 : ℝ) / 5436553144476101363176380171364313230466608400709) * (value_464 h H)

/-- Coordinate 100.1, recovered from two neighbors at 100. -/
theorem value_401 (h : Assignment) (H : Constraints h) :
    h 100 1 = ((366881573866853714432956137 : ℝ) / 156665822489380847227227145) * (h 1 0) + ((112817147970305496707393382 : ℝ) / 99448739493259146500761579) * (h 1 1) + ((-1984243624967293010630333118 : ℝ) / 672741473042635402799269505) * (h 1 2) + ((-366881573866853714432956137 : ℝ) / 156665822489380847227227145) * (h 3 0) + ((-13368408477046350206631803 : ℝ) / 99448739493259146500761579) * (h 5 1) + ((1984243624967293010630333118 : ℝ) / 672741473042635402799269505) * (h 9 2) := by
  have r0 := H 307 1
  change ((1063681291848446559935824 : ℤ) : ℝ) * (h 108 1 - h 100 1) - ((-12035581224106133733304720 : ℤ) : ℝ) * (h 108 0 - h 100 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 308 1
  change ((-25538490756680155028498688968 : ℤ) : ℝ) * (h 116 1 - h 100 1) - ((99899854154610765433865151968 : ℤ) : ℝ) * (h 116 0 - h 100 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((183639437784210965871075647 : ℝ) / 369685613824374892695993851652773299671729371248212) * r0 + ((44248460382743138725385 : ℝ) / 739371227648749785391987703305546599343458742496424) * r1 + ((-2872556388479881600745077286881945444870326018796 : ℝ) / 5436553144476101363176380171364313230466608400709) * (value_433 h H) + ((-32503049550015529464806485727439552186201976796380 : ℝ) / 5436553144476101363176380171364313230466608400709) * (value_432 h H) + ((8309109532955982963921457458246258675336934419505 : ℝ) / 5436553144476101363176380171364313230466608400709) * (value_465 h H) + ((32503049550015529464806485727439552186201976796380 : ℝ) / 5436553144476101363176380171364313230466608400709) * (value_464 h H)

/-- Coordinate 100.2, recovered from two neighbors at 100. -/
theorem value_402 (h : Assignment) (H : Constraints h) :
    h 100 2 = ((-86072801708468017563560514833 : ℝ) / 85226207434223180891611566880) * (h 1 0) + ((-5909849546842025310538840485 : ℝ) / 27050057142166487848207149488) * (h 1 1) + ((311320032115710761794896047581 : ℝ) / 182985680667596829561401305360) * (h 1 2) + ((86072801708468017563560514833 : ℝ) / 85226207434223180891611566880) * (h 3 0) + ((5909849546842025310538840485 : ℝ) / 27050057142166487848207149488) * (h 5 1) + ((-128334351448113932233494742221 : ℝ) / 182985680667596829561401305360) * (h 9 2) := by
  have r0 := H 307 1
  change ((1063681291848446559935824 : ℤ) : ℝ) * (h 108 1 - h 100 1) - ((-12035581224106133733304720 : ℤ) : ℝ) * (h 108 0 - h 100 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 307 2
  change ((1063681291848446559935824 : ℤ) : ℝ) * (h 108 2 - h 100 2) - ((-20032669745265332008074039 : ℤ) : ℝ) * (h 108 0 - h 100 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 308 1
  change ((-25538490756680155028498688968 : ℤ) : ℝ) * (h 116 1 - h 100 1) - ((99899854154610765433865151968 : ℤ) : ℝ) * (h 116 0 - h 100 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((1253931742943835483620013550308861690018141917099269 : ℝ) / 524303561720662693917220784746101884303256923939434608811289964561992995584) * r0 + ((-1 : ℝ) / 1063681291848446559935824) * r1 + ((6677556581755110669358013 : ℝ) / 67036324640153313875540218433036225007140259319675776) * r2 + ((-1253931742943835483620013550308861690018141917099269 : ℝ) / 492914151765833190261325135537031066228972494997616) * (value_433 h H) + ((-1226262736445766091830532310289165727080179248609411 : ℝ) / 123228537941458297565331283884257766557243123749404) * (value_432 h H) + (1 : ℝ) * (value_434 h H) + ((1253931742943835483620013550308861690018141917099269 : ℝ) / 492914151765833190261325135537031066228972494997616) * (value_465 h H) + ((1226262736445766091830532310289165727080179248609411 : ℝ) / 123228537941458297565331283884257766557243123749404) * (value_464 h H)

/-- Coordinate 100.3, recovered from two neighbors at 100. -/
theorem value_403 (h : Assignment) (H : Constraints h) :
    h 100 3 = ((1622753227103486375895987 : ℝ) / 9215636617022402778072185) * (h 1 0) + ((1591472348546978811637752 : ℝ) / 5849925852544655676515387) * (h 1 1) + ((-141879948728109196051564326 : ℝ) / 672741473042635402799269505) * (h 1 2) + h 1 3 + ((-1622753227103486375895987 : ℝ) / 9215636617022402778072185) * (h 3 0) + ((-1591472348546978811637752 : ℝ) / 5849925852544655676515387) * (h 5 1) + ((141879948728109196051564326 : ℝ) / 672741473042635402799269505) * (h 9 2) := by
  have r0 := H 307 1
  change ((1063681291848446559935824 : ℤ) : ℝ) * (h 108 1 - h 100 1) - ((-12035581224106133733304720 : ℤ) : ℝ) * (h 108 0 - h 100 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 307 3
  change ((1063681291848446559935824 : ℤ) : ℝ) * (h 108 3 - h 100 3) - ((-424018814222015381435136 : ℤ) : ℝ) * (h 108 0 - h 100 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 308 1
  change ((-25538490756680155028498688968 : ℤ) : ℝ) * (h 116 1 - h 100 1) - ((99899854154610765433865151968 : ℤ) : ℝ) * (h 116 0 - h 100 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((358742131568041065554389539592298645511053209 : ℝ) / 7086715529312590477903611385517164309894800550651960002315229841073651) * r0 + ((-1 : ℝ) / 1063681291848446559935824) * r1 + ((3820815439572658786 : ℝ) / 1812184381492033787725460057121437743488869466903) * r2 + ((-5739874105088657048870232633476778328176851344 : ℝ) / 106599081264237281630909415124790455499345262759) * (value_433 h H) + ((-22452876774411390282769174312900212656805905344 : ℝ) / 106599081264237281630909415124790455499345262759) * (value_432 h H) + (1 : ℝ) * (value_435 h H) + ((5739874105088657048870232633476778328176851344 : ℝ) / 106599081264237281630909415124790455499345262759) * (value_465 h H) + ((22452876774411390282769174312900212656805905344 : ℝ) / 106599081264237281630909415124790455499345262759) * (value_464 h H)

/-- Coordinate 101.0, recovered from two neighbors at 101. -/
theorem value_404 (h : Assignment) (H : Constraints h) :
    h 101 0 = ((548386529897423773218425216531 : ℝ) / 78095519245495398289328821980) * (h 1 0) + ((1263524282708508219959261271881 : ℝ) / 545310451775067868055052556956) * (h 1 1) + ((-31762477745279768535251075617161 : ℝ) / 3483927886340711379240613558330) * (h 1 2) + ((-470291010651928374929096394551 : ℝ) / 78095519245495398289328821980) * (h 3 0) + ((-1263524282708508219959261271881 : ℝ) / 545310451775067868055052556956) * (h 5 1) + ((31762477745279768535251075617161 : ℝ) / 3483927886340711379240613558330) * (h 9 2) := by
  have r0 := H 304 1
  change ((-5488233813412626149001534664 : ℤ) : ℝ) * (h 101 1 - h 100 1) - ((-1951492631223785880474865952 : ℤ) : ℝ) * (h 101 0 - h 100 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 311 1
  change ((-33180446547412124083427456 : ℤ) : ℝ) * (h 109 1 - h 101 1) - ((-20353902448394358239263696 : ℤ) : ℝ) * (h 109 0 - h 101 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-259222238651657219401777 : ℝ) / 366840458704613196230999018986062469211245461440469) * r0 + ((-40354660392739898154423049 : ℝ) / 345261608192577125864469664928058794551760434296912) * r1 + ((83686603256267209063340132566656613773042882864584 : ℝ) / 21578850512036070366529354058003674659485027143557) * (value_401 h H) + ((-29757075798708395089167351955550420081038688564512 : ℝ) / 21578850512036070366529354058003674659485027143557) * (value_400 h H) + ((-83686603256267209063340132566656613773042882864584 : ℝ) / 21578850512036070366529354058003674659485027143557) * (value_437 h H) + ((51335926310744465455696706013554094740523715708069 : ℝ) / 21578850512036070366529354058003674659485027143557) * (value_436 h H)

/-- Coordinate 101.1, recovered from two neighbors at 101. -/
theorem value_405 (h : Assignment) (H : Constraints h) :
    h 101 1 = ((16975711837127100659582949221 : ℝ) / 3904775962274769914466441099) * (h 1 0) + ((248188985144700158346517812229 : ℝ) / 136327612943766967013763139239) * (h 1 1) + ((-1964305101213638443870359895770 : ℝ) / 348392788634071137924061355833) * (h 1 2) + ((-16975711837127100659582949221 : ℝ) / 3904775962274769914466441099) * (h 3 0) + ((-111861372200933191332754672990 : ℝ) / 136327612943766967013763139239) * (h 5 1) + ((1964305101213638443870359895770 : ℝ) / 348392788634071137924061355833) * (h 9 2) := by
  have r0 := H 304 1
  change ((-5488233813412626149001534664 : ℤ) : ℝ) * (h 101 1 - h 100 1) - ((-1951492631223785880474865952 : ℤ) : ℝ) * (h 101 0 - h 100 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 311 1
  change ((-33180446547412124083427456 : ℤ) : ℝ) * (h 109 1 - h 101 1) - ((-20353902448394358239263696 : ℤ) : ℝ) * (h 109 0 - h 101 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-1272118903024647389953981 : ℝ) / 2934723669636905569847992151888499753689963691523752) * r0 + ((-3587302630926076986167033 : ℝ) / 86315402048144281466117416232014698637940108574228) * r1 + ((51335926310744465455696706013554094740523715708069 : ℝ) / 21578850512036070366529354058003674659485027143557) * (value_401 h H) + ((-18253901950684450306254916782401181322669797233492 : ℝ) / 21578850512036070366529354058003674659485027143557) * (value_400 h H) + ((-29757075798708395089167351955550420081038688564512 : ℝ) / 21578850512036070366529354058003674659485027143557) * (value_437 h H) + ((18253901950684450306254916782401181322669797233492 : ℝ) / 21578850512036070366529354058003674659485027143557) * (value_436 h H)

/-- Coordinate 101.2, recovered from two neighbors at 101. -/
theorem value_406 (h : Assignment) (H : Constraints h) :
    h 101 2 = ((-4160667383113056795758699869223 : ℝ) / 3540330205795791389116239929760) * (h 1 0) + ((-6798743945144548393304339320733 : ℝ) / 24720740480469743351829049248672) * (h 1 1) + ((53594430646451029868762249627027 : ℝ) / 27871423090725691033924908466640) * (h 1 2) + ((4160667383113056795758699869223 : ℝ) / 3540330205795791389116239929760) * (h 3 0) + ((6798743945144548393304339320733 : ℝ) / 24720740480469743351829049248672) * (h 5 1) + ((-25723007555725338834837341160387 : ℝ) / 27871423090725691033924908466640) * (h 9 2) := by
  have r0 := H 304 1
  change ((-5488233813412626149001534664 : ℤ) : ℝ) * (h 101 1 - h 100 1) - ((-1951492631223785880474865952 : ℤ) : ℝ) * (h 101 0 - h 100 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 304 2
  change ((-5488233813412626149001534664 : ℤ) : ℝ) * (h 101 2 - h 100 2) - ((160826491989070654333407771 : ℤ) : ℝ) * (h 101 0 - h 100 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 311 1
  change ((-33180446547412124083427456 : ℤ) : ℝ) * (h 109 1 - h 101 1) - ((-20353902448394358239263696 : ℤ) : ℝ) * (h 109 0 - h 101 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((13896601095966570377390102344841048376320807669689 : ℝ) / 671102069863485429471404674436744305129535424180970053733151774342905691972472) * r0 + ((-1 : ℝ) / 5488233813412626149001534664) * r1 + ((53608830663023551444469257 : ℝ) / 15651859571396829705855958143405332019679806354793344) * r2 + ((-13896601095966570377390102344841048376320807669689 : ℝ) / 122280152901537732076999672995354156403748487146823) * (value_401 h H) + ((68196806855479600681030771905420287306366199262117 : ℝ) / 978241223212301856615997383962833251229987897174584) * (value_400 h H) + (1 : ℝ) * (value_402 h H) + ((13896601095966570377390102344841048376320807669689 : ℝ) / 122280152901537732076999672995354156403748487146823) * (value_437 h H) + ((-68196806855479600681030771905420287306366199262117 : ℝ) / 978241223212301856615997383962833251229987897174584) * (value_436 h H)

/-- Coordinate 101.3, recovered from two neighbors at 101. -/
theorem value_407 (h : Assignment) (H : Constraints h) :
    h 101 3 = ((3151362603300167409011141063 : ℝ) / 6507959937124616524110735165) * (h 1 0) + ((17152950526243690493712896468 : ℝ) / 45442537647922322337921046413) * (h 1 1) + ((-1086975051893597234230446355038 : ℝ) / 1741963943170355689620306779165) * (h 1 2) + h 1 3 + ((-3151362603300167409011141063 : ℝ) / 6507959937124616524110735165) * (h 3 0) + ((-17152950526243690493712896468 : ℝ) / 45442537647922322337921046413) * (h 5 1) + ((1086975051893597234230446355038 : ℝ) / 1741963943170355689620306779165) * (h 9 2) := by
  have r0 := H 304 1
  change ((-5488233813412626149001534664 : ℤ) : ℝ) * (h 101 1 - h 100 1) - ((-1951492631223785880474865952 : ℤ) : ℝ) * (h 101 0 - h 100 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 304 3
  change ((-5488233813412626149001534664 : ℤ) : ℝ) * (h 101 3 - h 100 3) - ((-299829981649537190485234560 : ℤ) : ℝ) * (h 101 0 - h 100 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 311 1
  change ((-33180446547412124083427456 : ℤ) : ℝ) * (h 109 1 - h 101 1) - ((-20353902448394358239263696 : ℤ) : ℝ) * (h 109 0 - h 101 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((-11205680371695261579705599383511043499693587920 : ℝ) / 290269061359639026587977800361913626786131238832599504209840732847277548431) * r0 + ((-1 : ℝ) / 5488233813412626149001534664) * r1 + ((-45929837875235476483645 : ℝ) / 7192950170678690122176451352667891553161675714519) * r2 + ((1523972530550555574839961516157501915958327957120 : ℝ) / 7192950170678690122176451352667891553161675714519) * (value_401 h H) + ((-934851439583111293371053276207724248707986251920 : ℝ) / 7192950170678690122176451352667891553161675714519) * (value_400 h H) + (1 : ℝ) * (value_403 h H) + ((-1523972530550555574839961516157501915958327957120 : ℝ) / 7192950170678690122176451352667891553161675714519) * (value_437 h H) + ((934851439583111293371053276207724248707986251920 : ℝ) / 7192950170678690122176451352667891553161675714519) * (value_436 h H)

/-- Coordinate 102.0, recovered from two neighbors at 102. -/
theorem value_408 (h : Assignment) (H : Constraints h) :
    h 102 0 = ((816426342946694642186882152823 : ℝ) / 677940023491417019600478439020) * (h 1 0) + ((1547308847835853480810011144365 : ℝ) / 4733789903161807536862471187244) * (h 1 1) + ((-13283879343489716995631629035751 : ℝ) / 10081219238214960495170077528390) * (h 1 2) + ((-138486319455277622586403713803 : ℝ) / 677940023491417019600478439020) * (h 3 0) + ((-1547308847835853480810011144365 : ℝ) / 4733789903161807536862471187244) * (h 5 1) + ((13283879343489716995631629035751 : ℝ) / 10081219238214960495170077528390) * (h 9 2) := by
  have r0 := H 305 1
  change ((1497463144489500760637895320 : ℤ) : ℝ) * (h 102 1 - h 100 1) - ((17194150916834982391170515008 : ℤ) : ℝ) * (h 102 0 - h 100 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 315 1
  change ((9833081243719260440899584 : ℤ) : ℝ) * (h 110 1 - h 102 1) - ((21558470988799150178836624 : ℤ) : ℝ) * (h 110 0 - h 102 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-4518879248032748364384 : ℝ) / 62862347024235082117488400437894835845665503032517) * r0 + ((-11010758415363976181160995 : ℝ) / 1005797552387761313879814407006317373530648048520272) * r1 + ((-398050301666321765284361942147996136483424016640 : ℝ) / 3697785119072651889264023555170284461509735472501) * (value_401 h H) + ((415498886447213134157239884398224757399780345856 : ℝ) / 336162283552059262660365777742753132864521406591) * (value_400 h H) + ((398050301666321765284361942147996136483424016640 : ℝ) / 3697785119072651889264023555170284461509735472501) * (value_441 h H) + ((-79336602895153871496874106655471624535258939265 : ℝ) / 336162283552059262660365777742753132864521406591) * (value_440 h H)

/-- Coordinate 102.1, recovered from two neighbors at 102. -/
theorem value_409 (h : Assignment) (H : Constraints h) :
    h 102 1 = ((51895347364531141739643630871 : ℝ) / 169485005872854254900119609755) * (h 1 0) + ((47128427535330902937778671320 : ℝ) / 107586134162768353110510708801) * (h 1 1) + ((-101071459026990958765575291254 : ℝ) / 458237238100680022507730796745) * (h 1 2) + ((-51895347364531141739643630871 : ℝ) / 169485005872854254900119609755) * (h 3 0) + ((60457706627437450172732037481 : ℝ) / 107586134162768353110510708801) * (h 5 1) + ((101071459026990958765575291254 : ℝ) / 458237238100680022507730796745) * (h 9 2) := by
  have r0 := H 305 1
  change ((1497463144489500760637895320 : ℤ) : ℝ) * (h 102 1 - h 100 1) - ((17194150916834982391170515008 : ℤ) : ℝ) * (h 102 0 - h 100 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 315 1
  change ((9833081243719260440899584 : ℤ) : ℝ) * (h 110 1 - h 102 1) - ((21558470988799150178836624 : ℤ) : ℝ) * (h 110 0 - h 102 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-7205371319785812225547 : ℝ) / 45718070563080059721809745773014426069574911296376) * r0 + ((-1436677048532334758620531 : ℝ) / 11429517640770014930452436443253606517393727824094) * r1 + ((-79336602895153871496874106655471624535258939265 : ℝ) / 336162283552059262660365777742753132864521406591) * (value_401 h H) + ((910957660913468458643817321318033188770607680216 : ℝ) / 336162283552059262660365777742753132864521406591) * (value_400 h H) + ((415498886447213134157239884398224757399780345856 : ℝ) / 336162283552059262660365777742753132864521406591) * (value_441 h H) + ((-910957660913468458643817321318033188770607680216 : ℝ) / 336162283552059262660365777742753132864521406591) * (value_440 h H)

/-- Coordinate 102.2, recovered from two neighbors at 102. -/
theorem value_410 (h : Assignment) (H : Constraints h) :
    h 102 2 = ((-27966703486858654046268158158399 : ℝ) / 30733281064944238221888355902240) * (h 1 0) + ((-39547306060431870991147220801695 : ℝ) / 214598475610001941671098693821728) * (h 1 1) + ((126405614996135471007217995458297 : ℝ) / 80649753905719683961360620227120) * (h 1 2) + ((27966703486858654046268158158399 : ℝ) / 30733281064944238221888355902240) * (h 3 0) + ((39547306060431870991147220801695 : ℝ) / 214598475610001941671098693821728) * (h 5 1) + ((-45755861090415787045857375231177 : ℝ) / 80649753905719683961360620227120) * (h 9 2) := by
  have r0 := H 305 1
  change ((1497463144489500760637895320 : ℤ) : ℝ) * (h 102 1 - h 100 1) - ((17194150916834982391170515008 : ℤ) : ℝ) * (h 102 0 - h 100 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 305 2
  change ((1497463144489500760637895320 : ℤ) : ℝ) * (h 102 2 - h 100 2) - ((-844264220977432187219834355 : ℤ) : ℝ) * (h 102 0 - h 100 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 315 1
  change ((9833081243719260440899584 : ℤ) : ℝ) * (h 110 1 - h 102 1) - ((21558470988799150178836624 : ℤ) : ℝ) * (h 110 0 - h 102 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((95378201700786321487497578167867257084241540308 : ℝ) / 2353351196122531923664969139735236109872738967089050348294141072070210053011) * r0 + ((1 : ℝ) / 1497463144489500760637895320) * r1 + ((844264220977432187219834355 : ℝ) / 136788467124735538687654759352859162800168134598756992) * r2 + ((3815128068031452859499903126714690283369661612320 : ℝ) / 62862347024235082117488400437894835845665503032517) * (value_401 h H) + ((-6083237204152101174497213000148354250043239267185 : ℝ) / 45718070563080059721809745773014426069574911296376) * (value_400 h H) + (1 : ℝ) * (value_402 h H) + ((-3815128068031452859499903126714690283369661612320 : ℝ) / 62862347024235082117488400437894835845665503032517) * (value_441 h H) + ((6083237204152101174497213000148354250043239267185 : ℝ) / 45718070563080059721809745773014426069574911296376) * (value_440 h H)

/-- Coordinate 102.3, recovered from two neighbors at 102. -/
theorem value_411 (h : Assignment) (H : Constraints h) :
    h 102 3 = ((583319456784811150219555663 : ℝ) / 11299000391523616993341307317) * (h 1 0) + ((90522909293153379877888390004 : ℝ) / 394482491930150628071872598937) * (h 1 1) + ((-44404666411918119634893459450 : ℝ) / 1008121923821496049517007752839) * (h 1 2) + h 1 3 + ((-583319456784811150219555663 : ℝ) / 11299000391523616993341307317) * (h 3 0) + ((-90522909293153379877888390004 : ℝ) / 394482491930150628071872598937) * (h 5 1) + ((44404666411918119634893459450 : ℝ) / 1008121923821496049517007752839) * (h 9 2) := by
  have r0 := H 305 1
  change ((1497463144489500760637895320 : ℤ) : ℝ) * (h 102 1 - h 100 1) - ((17194150916834982391170515008 : ℤ) : ℝ) * (h 102 0 - h 100 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 305 3
  change ((1497463144489500760637895320 : ℤ) : ℝ) * (h 102 3 - h 100 3) - ((1051281162811604289287566464 : ℤ) : ℝ) * (h 102 0 - h 100 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 315 1
  change ((9833081243719260440899584 : ℤ) : ℝ) * (h 110 1 - h 102 1) - ((21558470988799150178836624 : ℤ) : ℝ) * (h 110 0 - h 102 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((-2054763248476252463252232891781810400659035648 : ℝ) / 40715418618036884492473514528291282177729047873512981804396904361076298495) * r0 + ((1 : ℝ) / 1497463144489500760637895320) * r1 + ((-28419149081196050207817 : ℝ) / 3697785119072651889264023555170284461509735472501) * r2 + ((-279447801792770335002303673282326214489628848128 : ℝ) / 3697785119072651889264023555170284461509735472501) * (value_401 h H) + ((55697581908483915710548787951870586986408244528 : ℝ) / 336162283552059262660365777742753132864521406591) * (value_400 h H) + (1 : ℝ) * (value_403 h H) + ((279447801792770335002303673282326214489628848128 : ℝ) / 3697785119072651889264023555170284461509735472501) * (value_441 h H) + ((-55697581908483915710548787951870586986408244528 : ℝ) / 336162283552059262660365777742753132864521406591) * (value_440 h H)

/-- Coordinate 103.0, recovered from two neighbors at 103. -/
theorem value_412 (h : Assignment) (H : Constraints h) :
    h 103 0 = ((135671876390153544723917112379 : ℝ) / 25855460499115798325739417180) * (h 1 0) + ((308714914906482671272344739813 : ℝ) / 180538563311217270048423930396) * (h 1 1) + ((-23314774412723819810537136333987 : ℝ) / 3460322463464997675928125332590) * (h 1 2) + ((-109816415891037746398177695199 : ℝ) / 25855460499115798325739417180) * (h 3 0) + ((-308714914906482671272344739813 : ℝ) / 180538563311217270048423930396) * (h 5 1) + ((23314774412723819810537136333987 : ℝ) / 3460322463464997675928125332590) * (h 9 2) := by
  have r0 := H 309 1
  change ((26864806154821569968945336 : ℤ) : ℝ) * (h 103 1 - h 101 1) - ((73729387007466512522564224 : ℤ) : ℝ) * (h 103 0 - h 101 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 313 1
  change ((-18064125918624577397286760816 : ℤ) : ℝ) * (h 103 1 - h 102 1) - ((3705282971359406668600901392 : ℤ) : ℝ) * (h 103 0 - h 102 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-66412227642002122784142503 : ℝ) / 5262494998456653456796791456019826491201304266400568) * r0 + ((-3358100769352696246118167 : ℝ) / 178924829947526217531090909504674100700844345057619312) * r1 + ((-223018952739033728606740674663655400980177505152001 : ℝ) / 657811874807081682099598932002478311400163033300071) * (value_405 h H) + ((87438086318663208837749193258627205489422903314512 : ℝ) / 93973124972440240299942704571782615914309004757153) * (value_404 h H) + ((223018952739033728606740674663655400980177505152001 : ℝ) / 657811874807081682099598932002478311400163033300071) * (value_409 h H) + ((6535038653777031462193511313155410424886101442641 : ℝ) / 93973124972440240299942704571782615914309004757153) * (value_408 h H)

/-- Coordinate 103.1, recovered from two neighbors at 103. -/
theorem value_413 (h : Assignment) (H : Constraints h) :
    h 103 1 = ((-483042981283910047794284161 : ℝ) / 923409303539849940204979185) * (h 1 0) + ((995241164561013775600388003 : ℝ) / 6447805832543473930300854657) * (h 1 1) + ((220271233488555718042254873846 : ℝ) / 247165890247499833994866095185) * (h 1 2) + ((483042981283910047794284161 : ℝ) / 923409303539849940204979185) * (h 3 0) + ((5452564667982460154700466654 : ℝ) / 6447805832543473930300854657) * (h 5 1) + ((-220271233488555718042254873846 : ℝ) / 247165890247499833994866095185) * (h 9 2) := by
  have r0 := H 309 1
  change ((26864806154821569968945336 : ℤ) : ℝ) * (h 103 1 - h 101 1) - ((73729387007466512522564224 : ℤ) : ℝ) * (h 103 0 - h 101 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 313 1
  change ((-18064125918624577397286760816 : ℤ) : ℝ) * (h 103 1 - h 102 1) - ((3705282971359406668600901392 : ℤ) : ℝ) * (h 103 0 - h 102 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((1946051980755990897374423 : ℝ) / 751784999779521922399541636574260927314472038057224) * r0 + ((-82287262285118875583219 : ℝ) / 1597543124531484085099025977720304470543253080871601) * r1 + ((6535038653777031462193511313155410424886101442641 : ℝ) / 93973124972440240299942704571782615914309004757153) * (value_405 h H) + ((-17935152453225653365608954445406901807513124055344 : ℝ) / 93973124972440240299942704571782615914309004757153) * (value_404 h H) + ((87438086318663208837749193258627205489422903314512 : ℝ) / 93973124972440240299942704571782615914309004757153) * (value_409 h H) + ((17935152453225653365608954445406901807513124055344 : ℝ) / 93973124972440240299942704571782615914309004757153) * (value_408 h H)

/-- Coordinate 103.2, recovered from two neighbors at 103. -/
theorem value_414 (h : Assignment) (H : Constraints h) :
    h 103 2 = ((-3832477161397923488018079703357 : ℝ) / 3516342627879748572300560736480) * (h 1 0) + ((-6036067200865735745129766329731 : ℝ) / 24553244610325548726585654533856) * (h 1 1) + ((50065150264149713684641216176353 : ℝ) / 27682579707719981407425002660720) * (h 1 2) + ((3832477161397923488018079703357 : ℝ) / 3516342627879748572300560736480) * (h 3 0) + ((6036067200865735745129766329731 : ℝ) / 24553244610325548726585654533856) * (h 5 1) + ((-22382570556429732277216213515633 : ℝ) / 27682579707719981407425002660720) * (h 9 2) := by
  have r0 := H 309 1
  change ((26864806154821569968945336 : ℤ) : ℝ) * (h 103 1 - h 101 1) - ((73729387007466512522564224 : ℤ) : ℝ) * (h 103 0 - h 101 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 309 2
  change ((26864806154821569968945336 : ℤ) : ℝ) * (h 103 2 - h 101 2) - ((-1291497930333323163387291 : ℤ) : ℝ) * (h 103 0 - h 101 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 313 1
  change ((-18064125918624577397286760816 : ℤ) : ℝ) * (h 103 1 - h 102 1) - ((3705282971359406668600901392 : ℤ) : ℝ) * (h 103 0 - h 102 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((391649564148270577335867199654530499899042571367 : ℝ) / 645552091434959050871492397428697275607745934312484936799482768479104435392) * r0 + ((1 : ℝ) / 26864806154821569968945336) * r1 + ((430499310111107721129097 : ℝ) / 477132879860069913416242425345797601868918253486984832) * r2 + ((28590418182823752145518305574780726492630107709791 : ℝ) / 1754164999485551152265597152006608830400434755466856) * (value_405 h H) + ((837774035155808760466533391411803180098328886031 : ℝ) / 250594999926507307466513878858086975771490679352408) * (value_404 h H) + (1 : ℝ) * (value_406 h H) + ((-28590418182823752145518305574780726492630107709791 : ℝ) / 1754164999485551152265597152006608830400434755466856) * (value_409 h H) + ((-837774035155808760466533391411803180098328886031 : ℝ) / 250594999926507307466513878858086975771490679352408) * (value_408 h H)

/-- Coordinate 103.3, recovered from two neighbors at 103. -/
theorem value_415 (h : Assignment) (H : Constraints h) :
    h 103 3 = ((59999240782588592547411283 : ℝ) / 430924341651929972095656953) * (h 1 0) + ((3903285373919911398449457656 : ℝ) / 15044880275934772504035327533) * (h 1 1) + ((-55881888235985827100922492258 : ℝ) / 346032246346499767592812533259) * (h 1 2) + h 1 3 + ((-59999240782588592547411283 : ℝ) / 430924341651929972095656953) * (h 3 0) + ((-3903285373919911398449457656 : ℝ) / 15044880275934772504035327533) * (h 5 1) + ((55881888235985827100922492258 : ℝ) / 346032246346499767592812533259) * (h 9 2) := by
  have r0 := H 309 1
  change ((26864806154821569968945336 : ℤ) : ℝ) * (h 103 1 - h 101 1) - ((73729387007466512522564224 : ℤ) : ℝ) * (h 103 0 - h 101 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 309 3
  change ((26864806154821569968945336 : ℤ) : ℝ) * (h 103 3 - h 101 3) - ((5222532513945999136338528 : ℤ) : ℝ) * (h 103 0 - h 101 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 313 1
  change ((-18064125918624577397286760816 : ℤ) : ℝ) * (h 103 1 - h 102 1) - ((3705282971359406668600901392 : ℤ) : ℝ) * (h 103 0 - h 102 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((-49492011727160291188192640811337964606271061823 : ℝ) / 20173502857342470339734137419646789862742060447265154274983836514972013606) * r0 + ((1 : ℝ) / 26864806154821569968945336) * r1 + ((-3200081197270832804129 : ℝ) / 877082499742775576132798576003304415200217377733428) * r2 + ((-14451667424330805026952251116910685665031150052316 : ℝ) / 219270624935693894033199644000826103800054344433357) * (value_405 h H) + ((-423471655971965678088959148033184663041870694556 : ℝ) / 31324374990813413433314234857260871971436334919051) * (value_404 h H) + (1 : ℝ) * (value_407 h H) + ((14451667424330805026952251116910685665031150052316 : ℝ) / 219270624935693894033199644000826103800054344433357) * (value_409 h H) + ((423471655971965678088959148033184663041870694556 : ℝ) / 31324374990813413433314234857260871971436334919051) * (value_408 h H)

/-- Coordinate 104.0, recovered from two neighbors at 104. -/
theorem value_416 (h : Assignment) (H : Constraints h) :
    h 104 0 = ((865772837261564378051233647 : ℝ) / 626663289957523388908908580) * (h 1 0) + ((77075308907547833268126965 : ℝ) / 198897478986518293001523158) * (h 1 1) + ((-2092699072455672553385462919 : ℝ) / 1345482946085270805598539010) * (h 1 2) + ((-239109547304040989142325067 : ℝ) / 626663289957523388908908580) * (h 3 0) + ((-77075308907547833268126965 : ℝ) / 198897478986518293001523158) * (h 5 1) + ((2092699072455672553385462919 : ℝ) / 1345482946085270805598539010) * (h 9 2) := by
  have r0 := H 306 0
  change ((1 : ℤ) : ℝ) * (h 104 0 - h 100 0) - ((0 : ℤ) : ℝ) * (h 104 2 - h 100 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_400 h H)

/-- Coordinate 104.1, recovered from two neighbors at 104. -/
theorem value_417 (h : Assignment) (H : Constraints h) :
    h 104 1 = ((366881573866853714432956137 : ℝ) / 156665822489380847227227145) * (h 1 0) + ((112817147970305496707393382 : ℝ) / 99448739493259146500761579) * (h 1 1) + ((-1984243624967293010630333118 : ℝ) / 672741473042635402799269505) * (h 1 2) + ((-366881573866853714432956137 : ℝ) / 156665822489380847227227145) * (h 3 0) + ((-13368408477046350206631803 : ℝ) / 99448739493259146500761579) * (h 5 1) + ((1984243624967293010630333118 : ℝ) / 672741473042635402799269505) * (h 9 2) := by
  have r0 := H 306 1
  change ((1 : ℤ) : ℝ) * (h 104 1 - h 100 1) - ((0 : ℤ) : ℝ) * (h 104 2 - h 100 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_401 h H)

/-- Coordinate 104.2, recovered from two neighbors at 104. -/
theorem value_418 (h : Assignment) (H : Constraints h) :
    h 104 2 = ((13602766033558799983759603543 : ℝ) / 85226207434223180891611566880) * (h 1 0) + ((2372784085995988745127732027 : ℝ) / 27050057142166487848207149488) * (h 1 1) + ((40088177460136010626570783269 : ℝ) / 182985680667596829561401305360) * (h 1 2) + ((-13602766033558799983759603543 : ℝ) / 85226207434223180891611566880) * (h 3 0) + ((-2372784085995988745127732027 : ℝ) / 27050057142166487848207149488) * (h 5 1) + ((142897503207460818934830522091 : ℝ) / 182985680667596829561401305360) * (h 9 2) := by
  have r0 := H 306 0
  change ((1 : ℤ) : ℝ) * (h 104 0 - h 100 0) - ((0 : ℤ) : ℝ) * (h 104 2 - h 100 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 322 2
  change ((1063681291848446559935824 : ℤ) : ℝ) * (h 112 2 - h 104 2) - ((17748015699771271771053753 : ℤ) : ℝ) * (h 112 0 - h 104 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((17748015699771271771053753 : ℝ) / 1063681291848446559935824) * r0 + ((-1 : ℝ) / 1063681291848446559935824) * r1 + ((17748015699771271771053753 : ℝ) / 1063681291848446559935824) * (value_400 h H) + (1 : ℝ) * (value_450 h H) + ((-17748015699771271771053753 : ℝ) / 1063681291848446559935824) * (value_448 h H)

/-- Coordinate 104.3, recovered from two neighbors at 104. -/
theorem value_419 (h : Assignment) (H : Constraints h) :
    h 104 3 = ((1622753227103486375895987 : ℝ) / 9215636617022402778072185) * (h 1 0) + ((1591472348546978811637752 : ℝ) / 5849925852544655676515387) * (h 1 1) + ((-141879948728109196051564326 : ℝ) / 672741473042635402799269505) * (h 1 2) + h 1 3 + ((-1622753227103486375895987 : ℝ) / 9215636617022402778072185) * (h 3 0) + ((-1591472348546978811637752 : ℝ) / 5849925852544655676515387) * (h 5 1) + ((141879948728109196051564326 : ℝ) / 672741473042635402799269505) * (h 9 2) := by
  have r0 := H 306 3
  change ((1 : ℤ) : ℝ) * (h 104 3 - h 100 3) - ((0 : ℤ) : ℝ) * (h 104 2 - h 100 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_403 h H)

/-- Coordinate 105.0, recovered from two neighbors at 105. -/
theorem value_420 (h : Assignment) (H : Constraints h) :
    h 105 0 = ((548386529897423773218425216531 : ℝ) / 78095519245495398289328821980) * (h 1 0) + ((1263524282708508219959261271881 : ℝ) / 545310451775067868055052556956) * (h 1 1) + ((-31762477745279768535251075617161 : ℝ) / 3483927886340711379240613558330) * (h 1 2) + ((-470291010651928374929096394551 : ℝ) / 78095519245495398289328821980) * (h 3 0) + ((-1263524282708508219959261271881 : ℝ) / 545310451775067868055052556956) * (h 5 1) + ((31762477745279768535251075617161 : ℝ) / 3483927886340711379240613558330) * (h 9 2) := by
  have r0 := H 310 0
  change ((1 : ℤ) : ℝ) * (h 105 0 - h 101 0) - ((0 : ℤ) : ℝ) * (h 105 2 - h 101 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_404 h H)

/-- Coordinate 105.1, recovered from two neighbors at 105. -/
theorem value_421 (h : Assignment) (H : Constraints h) :
    h 105 1 = ((16975711837127100659582949221 : ℝ) / 3904775962274769914466441099) * (h 1 0) + ((248188985144700158346517812229 : ℝ) / 136327612943766967013763139239) * (h 1 1) + ((-1964305101213638443870359895770 : ℝ) / 348392788634071137924061355833) * (h 1 2) + ((-16975711837127100659582949221 : ℝ) / 3904775962274769914466441099) * (h 3 0) + ((-111861372200933191332754672990 : ℝ) / 136327612943766967013763139239) * (h 5 1) + ((1964305101213638443870359895770 : ℝ) / 348392788634071137924061355833) * (h 9 2) := by
  have r0 := H 310 1
  change ((1 : ℤ) : ℝ) * (h 105 1 - h 101 1) - ((0 : ℤ) : ℝ) * (h 105 2 - h 101 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_405 h H)

/-- Coordinate 105.2, recovered from two neighbors at 105. -/
theorem value_422 (h : Assignment) (H : Constraints h) :
    h 105 2 = ((-866914767777074946709400332943 : ℝ) / 3540330205795791389116239929760) * (h 1 0) + ((-1252121310167180136020707511333 : ℝ) / 24720740480469743351829049248672) * (h 1 1) + ((21218914265760986020066504979307 : ℝ) / 27871423090725691033924908466640) * (h 1 2) + ((866914767777074946709400332943 : ℝ) / 3540330205795791389116239929760) * (h 3 0) + ((1252121310167180136020707511333 : ℝ) / 24720740480469743351829049248672) * (h 5 1) + ((6652508824964705013858403487333 : ℝ) / 27871423090725691033924908466640) * (h 9 2) := by
  have r0 := H 310 0
  change ((1 : ℤ) : ℝ) * (h 105 0 - h 101 0) - ((0 : ℤ) : ℝ) * (h 105 2 - h 101 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 320 2
  change ((-5488233813412626149001534664 : ℤ) : ℝ) * (h 105 2 - h 104 2) - ((393561582780227386244117187 : ℤ) : ℝ) * (h 105 0 - h 104 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-393561582780227386244117187 : ℝ) / 5488233813412626149001534664) * r0 + ((-1 : ℝ) / 5488233813412626149001534664) * r1 + ((-393561582780227386244117187 : ℝ) / 5488233813412626149001534664) * (value_404 h H) + (1 : ℝ) * (value_418 h H) + ((393561582780227386244117187 : ℝ) / 5488233813412626149001534664) * (value_416 h H)

/-- Coordinate 105.3, recovered from two neighbors at 105. -/
theorem value_423 (h : Assignment) (H : Constraints h) :
    h 105 3 = ((3151362603300167409011141063 : ℝ) / 6507959937124616524110735165) * (h 1 0) + ((17152950526243690493712896468 : ℝ) / 45442537647922322337921046413) * (h 1 1) + ((-1086975051893597234230446355038 : ℝ) / 1741963943170355689620306779165) * (h 1 2) + h 1 3 + ((-3151362603300167409011141063 : ℝ) / 6507959937124616524110735165) * (h 3 0) + ((-17152950526243690493712896468 : ℝ) / 45442537647922322337921046413) * (h 5 1) + ((1086975051893597234230446355038 : ℝ) / 1741963943170355689620306779165) * (h 9 2) := by
  have r0 := H 310 3
  change ((1 : ℤ) : ℝ) * (h 105 3 - h 101 3) - ((0 : ℤ) : ℝ) * (h 105 2 - h 101 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_407 h H)

/-- Coordinate 106.0, recovered from two neighbors at 106. -/
theorem value_424 (h : Assignment) (H : Constraints h) :
    h 106 0 = ((816426342946694642186882152823 : ℝ) / 677940023491417019600478439020) * (h 1 0) + ((1547308847835853480810011144365 : ℝ) / 4733789903161807536862471187244) * (h 1 1) + ((-13283879343489716995631629035751 : ℝ) / 10081219238214960495170077528390) * (h 1 2) + ((-138486319455277622586403713803 : ℝ) / 677940023491417019600478439020) * (h 3 0) + ((-1547308847835853480810011144365 : ℝ) / 4733789903161807536862471187244) * (h 5 1) + ((13283879343489716995631629035751 : ℝ) / 10081219238214960495170077528390) * (h 9 2) := by
  have r0 := H 314 0
  change ((1 : ℤ) : ℝ) * (h 106 0 - h 102 0) - ((0 : ℤ) : ℝ) * (h 106 2 - h 102 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_408 h H)

/-- Coordinate 106.1, recovered from two neighbors at 106. -/
theorem value_425 (h : Assignment) (H : Constraints h) :
    h 106 1 = ((51895347364531141739643630871 : ℝ) / 169485005872854254900119609755) * (h 1 0) + ((47128427535330902937778671320 : ℝ) / 107586134162768353110510708801) * (h 1 1) + ((-101071459026990958765575291254 : ℝ) / 458237238100680022507730796745) * (h 1 2) + ((-51895347364531141739643630871 : ℝ) / 169485005872854254900119609755) * (h 3 0) + ((60457706627437450172732037481 : ℝ) / 107586134162768353110510708801) * (h 5 1) + ((101071459026990958765575291254 : ℝ) / 458237238100680022507730796745) * (h 9 2) := by
  have r0 := H 314 1
  change ((1 : ℤ) : ℝ) * (h 106 1 - h 102 1) - ((0 : ℤ) : ℝ) * (h 106 2 - h 102 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_409 h H)

/-- Coordinate 106.2, recovered from two neighbors at 106. -/
theorem value_426 (h : Assignment) (H : Constraints h) :
    h 106 2 = ((3671927105646530133536206652777 : ℝ) / 30733281064944238221888355902240) * (h 1 0) + ((15878106154893252875550704693249 : ℝ) / 214598475610001941671098693821728) * (h 1 1) + ((22007446485715685045187302588049 : ℝ) / 80649753905719683961360620227120) * (h 1 2) + ((-3671927105646530133536206652777 : ℝ) / 30733281064944238221888355902240) * (h 3 0) + ((-15878106154893252875550704693249 : ℝ) / 214598475610001941671098693821728) * (h 5 1) + ((58642307420003998916173317639071 : ℝ) / 80649753905719683961360620227120) * (h 9 2) := by
  have r0 := H 314 0
  change ((1 : ℤ) : ℝ) * (h 106 0 - h 102 0) - ((0 : ℤ) : ℝ) * (h 106 2 - h 102 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 321 2
  change ((1497463144489500760637895320 : ℤ) : ℝ) * (h 106 2 - h 104 2) - ((338969155142284106446818861 : ℤ) : ℝ) * (h 106 0 - h 104 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((338969155142284106446818861 : ℝ) / 1497463144489500760637895320) * r0 + ((1 : ℝ) / 1497463144489500760637895320) * r1 + ((338969155142284106446818861 : ℝ) / 1497463144489500760637895320) * (value_408 h H) + (1 : ℝ) * (value_418 h H) + ((-338969155142284106446818861 : ℝ) / 1497463144489500760637895320) * (value_416 h H)

/-- Coordinate 106.3, recovered from two neighbors at 106. -/
theorem value_427 (h : Assignment) (H : Constraints h) :
    h 106 3 = ((583319456784811150219555663 : ℝ) / 11299000391523616993341307317) * (h 1 0) + ((90522909293153379877888390004 : ℝ) / 394482491930150628071872598937) * (h 1 1) + ((-44404666411918119634893459450 : ℝ) / 1008121923821496049517007752839) * (h 1 2) + h 1 3 + ((-583319456784811150219555663 : ℝ) / 11299000391523616993341307317) * (h 3 0) + ((-90522909293153379877888390004 : ℝ) / 394482491930150628071872598937) * (h 5 1) + ((44404666411918119634893459450 : ℝ) / 1008121923821496049517007752839) * (h 9 2) := by
  have r0 := H 314 3
  change ((1 : ℤ) : ℝ) * (h 106 3 - h 102 3) - ((0 : ℤ) : ℝ) * (h 106 2 - h 102 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_411 h H)

/-- Coordinate 107.0, recovered from two neighbors at 107. -/
theorem value_428 (h : Assignment) (H : Constraints h) :
    h 107 0 = ((135671876390153544723917112379 : ℝ) / 25855460499115798325739417180) * (h 1 0) + ((308714914906482671272344739813 : ℝ) / 180538563311217270048423930396) * (h 1 1) + ((-23314774412723819810537136333987 : ℝ) / 3460322463464997675928125332590) * (h 1 2) + ((-109816415891037746398177695199 : ℝ) / 25855460499115798325739417180) * (h 3 0) + ((-308714914906482671272344739813 : ℝ) / 180538563311217270048423930396) * (h 5 1) + ((23314774412723819810537136333987 : ℝ) / 3460322463464997675928125332590) * (h 9 2) := by
  have r0 := H 317 0
  change ((1 : ℤ) : ℝ) * (h 107 0 - h 103 0) - ((0 : ℤ) : ℝ) * (h 107 2 - h 103 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_412 h H)

/-- Coordinate 107.1, recovered from two neighbors at 107. -/
theorem value_429 (h : Assignment) (H : Constraints h) :
    h 107 1 = ((-483042981283910047794284161 : ℝ) / 923409303539849940204979185) * (h 1 0) + ((995241164561013775600388003 : ℝ) / 6447805832543473930300854657) * (h 1 1) + ((220271233488555718042254873846 : ℝ) / 247165890247499833994866095185) * (h 1 2) + ((483042981283910047794284161 : ℝ) / 923409303539849940204979185) * (h 3 0) + ((5452564667982460154700466654 : ℝ) / 6447805832543473930300854657) * (h 5 1) + ((-220271233488555718042254873846 : ℝ) / 247165890247499833994866095185) * (h 9 2) := by
  have r0 := H 317 1
  change ((1 : ℤ) : ℝ) * (h 107 1 - h 103 1) - ((0 : ℤ) : ℝ) * (h 107 2 - h 103 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_413 h H)

/-- Coordinate 107.2, recovered from two neighbors at 107. -/
theorem value_430 (h : Assignment) (H : Constraints h) :
    h 107 2 = ((-670662280877636424841122383989 : ℝ) / 3516342627879748572300560736480) * (h 1 0) + ((-788878170848256898961871452059 : ℝ) / 24553244610325548726585654533856) * (h 1 1) + ((19065916879806632535296457286761 : ℝ) / 27682579707719981407425002660720) * (h 1 2) + ((670662280877636424841122383989 : ℝ) / 3516342627879748572300560736480) * (h 3 0) + ((788878170848256898961871452059 : ℝ) / 24553244610325548726585654533856) * (h 5 1) + ((8616662827913348872128545373959 : ℝ) / 27682579707719981407425002660720) * (h 9 2) := by
  have r0 := H 317 0
  change ((1 : ℤ) : ℝ) * (h 107 0 - h 103 0) - ((0 : ℤ) : ℝ) * (h 107 2 - h 103 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 324 2
  change ((26864806154821569968945336 : ℤ) : ℝ) * (h 107 2 - h 105 2) - ((-819580206232539830401275 : ℤ) : ℝ) * (h 107 0 - h 105 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-11227126112774518224675 : ℝ) / 368011043216733835191032) * r0 + ((1 : ℝ) / 26864806154821569968945336) * r1 + ((-11227126112774518224675 : ℝ) / 368011043216733835191032) * (value_412 h H) + (1 : ℝ) * (value_422 h H) + ((11227126112774518224675 : ℝ) / 368011043216733835191032) * (value_420 h H)

/-- Coordinate 107.3, recovered from two neighbors at 107. -/
theorem value_431 (h : Assignment) (H : Constraints h) :
    h 107 3 = ((59999240782588592547411283 : ℝ) / 430924341651929972095656953) * (h 1 0) + ((3903285373919911398449457656 : ℝ) / 15044880275934772504035327533) * (h 1 1) + ((-55881888235985827100922492258 : ℝ) / 346032246346499767592812533259) * (h 1 2) + h 1 3 + ((-59999240782588592547411283 : ℝ) / 430924341651929972095656953) * (h 3 0) + ((-3903285373919911398449457656 : ℝ) / 15044880275934772504035327533) * (h 5 1) + ((55881888235985827100922492258 : ℝ) / 346032246346499767592812533259) * (h 9 2) := by
  have r0 := H 317 3
  change ((1 : ℤ) : ℝ) * (h 107 3 - h 103 3) - ((0 : ℤ) : ℝ) * (h 107 2 - h 103 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_415 h H)

end CubicalIndecomposability.Rigidity
end VerificationSource017

/- Original source: CubicalIndecomposability/Rigidity/ScaleCompatibility.lean -/
section VerificationSource018


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

theorem residual0 (h : Assignment) (H : Constraints h) :
    ((-89453649138583686649772245 : ℝ) / 6) * (h 1 0) + (119012246245246122238392639 : ℝ) * (h 1 1) + ((-624619828332893046780583589 : ℝ) / 6) * (h 1 2) + ((89453649138583686649772245 : ℝ) / 6) * (h 3 0) + (-119012246245246122238392639 : ℝ) * (h 5 1) + ((624619828332893046780583589 : ℝ) / 6) * (h 9 2) = 0 := by
  have r := H 50 1
  change ((-13686096792730261051639696 : ℤ) : ℝ) * (h 43 1 - h 10 1) - ((66289502033667579980694885 : ℤ) : ℝ) * (h 43 0 - h 10 0) = 0 at r
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r
  linear_combination r + (13686096792730261051639696 : ℝ) * (value_173 h H) + (-13686096792730261051639696 : ℝ) * (value_041 h H) + (66289502033667579980694885 : ℝ) * (value_172 h H) + (-66289502033667579980694885 : ℝ) * (value_040 h H)

theorem residual1 (h : Assignment) (H : Constraints h) :
    ((938188934778543954396183172 : ℝ) / 13) * (h 1 0) + ((134360806350600939919752260 : ℝ) / 13) * (h 1 1) + ((-1072549741129144894315935432 : ℝ) / 13) * (h 1 2) + ((-938188934778543954396183172 : ℝ) / 13) * (h 3 0) + ((-134360806350600939919752260 : ℝ) / 13) * (h 5 1) + ((1072549741129144894315935432 : ℝ) / 13) * (h 9 2) = 0 := by
  have r := H 243 1
  change ((41003288748152153775469552 : ℤ) : ℝ) * (h 111 1 - h 81 1) - ((-13686096792730261051639696 : ℤ) : ℝ) * (h 111 0 - h 81 0) = 0 at r
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r
  linear_combination r + (-41003288748152153775469552 : ℝ) * (value_445 h H) + (41003288748152153775469552 : ℝ) * (value_325 h H) + (-13686096792730261051639696 : ℝ) * (value_444 h H) + (13686096792730261051639696 : ℝ) * (value_324 h H)

/-- The explicit plane condition on the three interface scales. -/
theorem cube_scale_relation0 (h : Assignment) (H : Constraints h) :
    (115 : ℝ) * (h 3 0 - h 1 0) + (-918 : ℝ) * (h 5 1 - h 1 1) + (803 : ℝ) * (h 9 2 - h 1 2) = 0 := by
  linear_combination ((6 : ℝ) / 777857818596379883911063) * (residual0 h H)

/-- The explicit plane condition on the three interface scales. -/
theorem cube_scale_relation1 (h : Assignment) (H : Constraints h) :
    (-803 : ℝ) * (h 3 0 - h 1 0) + (-115 : ℝ) * (h 5 1 - h 1 1) + (918 : ℝ) * (h 9 2 - h 1 2) = 0 := by
  linear_combination ((13 : ℝ) / 1168354837831312521041324) * (residual1 h H)

/-- The surviving cube scales must agree (relation 1). -/
theorem scales0 (h : Assignment) (H : Constraints h) :
    h 1 0 + (-1 : ℝ) * (h 1 1) + (-1 : ℝ) * (h 3 0) + h 5 1 = 0 := by
  linear_combination ((-918 : ℝ) / 750379) * (cube_scale_relation0 h H) + ((803 : ℝ) / 750379) * (cube_scale_relation1 h H)

/-- The surviving cube scales must agree (relation 2). -/
theorem scales1 (h : Assignment) (H : Constraints h) :
    h 1 0 + (-1 : ℝ) * (h 1 2) + (-1 : ℝ) * (h 3 0) + h 9 2 = 0 := by
  linear_combination ((-115 : ℝ) / 750379) * (cube_scale_relation0 h H) + ((918 : ℝ) / 750379) * (cube_scale_relation1 h H)

end CubicalIndecomposability.Rigidity
end VerificationSource018

/- Original source: CubicalIndecomposability/Rigidity/Complete.lean -/

end -- global noncomputable section
end -- global public section
