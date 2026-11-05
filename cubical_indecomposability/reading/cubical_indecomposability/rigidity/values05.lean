import cubical_indecomposability.rigidity.values04

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
