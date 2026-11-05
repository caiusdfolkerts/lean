import cubical_indecomposability.rigidity.values01

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

/-! Each coordinate identity below is an exact linear consequence
of edge equations and identities in earlier modules. No rank result or
external solver is assumed. -/

/-- Coordinate 22.3, recovered from skew spokes on cycle 12. -/
theorem value_091 (h : Assignment) (H : Constraints h) :
    h 22 3 = ((-588757460640426 : ℝ) / 2455684594895333) * (h 1 0) + ((108824997255192 : ℝ) / 2455684594895333) * (h 1 1) + ((-95192236161132 : ℝ) / 2455684594895333) * (h 1 2) + h 1 3 + ((588757460640426 : ℝ) / 2455684594895333) * (h 3 0) + ((-108824997255192 : ℝ) / 2455684594895333) * (h 5 1) + ((95192236161132 : ℝ) / 2455684594895333) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 3
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 3 - h 2 3) - ((-948365989152 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 80 3
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 3 - h 18 3) - ((6606317480432832 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((520362964425266072908540710 : ℝ) / 107688519996203866147786022137656192234289) * r0 + ((-1 : ℝ) / 9074785486268) * r1 + ((-86727160737544345484756785 : ℝ) / 125026371715592688597579571701818839184009529) * r2 + ((1 : ℝ) / 63214955697342888) * r3 + ((29636437161 : ℝ) / 47467136345716841559563887967) * r4 + ((-2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_010 h H) + ((-224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_008 h H) + (1 : ℝ) * (value_011 h H) + ((2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_082 h H) + ((224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_080 h H)

/-- Coordinate 26.0, recovered from skew spokes on cycle 12. -/
theorem value_104 (h : Assignment) (H : Constraints h) :
    h 26 0 = ((1119392371268413 : ℝ) / 2455684594895333) * (h 1 0) + ((1041331634549253 : ℝ) / 2455684594895333) * (h 1 1) + ((-1821763186368301 : ℝ) / 4911369189790666) * (h 1 2) + ((1336292223626920 : ℝ) / 2455684594895333) * (h 3 0) + ((-1041331634549253 : ℝ) / 2455684594895333) * (h 5 1) + ((1821763186368301 : ℝ) / 4911369189790666) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 90 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 22 0) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 103 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 26 0) - ((0 : ℤ) : ℝ) * (h 30 1 - h 26 1) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((8779107987886555 : ℝ) / 189868545382867366238255551868) * r0 + ((-8779107987886555 : ℝ) / 1322624287137054073215688174312488) * r1 + ((2268696371567 : ℝ) / 379737090765734732476511103736) * r2 + (1 : ℝ) * r3 + (-1 : ℝ) * r4 + ((-19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_010 h H) + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_008 h H) + ((19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_082 h H) + ((8604122818205536940663648993 : ℝ) / 189868545382867366238255551868) * (value_080 h H)

/-- Coordinate 26.1, recovered from skew spokes on cycle 12. -/
theorem value_105 (h : Assignment) (H : Constraints h) :
    h 26 1 = ((-4000350913637771 : ℝ) / 9822738379581332) * (h 1 0) + ((19299825353791007 : ℝ) / 9822738379581332) * (h 1 1) + ((-16579740392789475 : ℝ) / 19645476759162664) * (h 1 2) + ((4000350913637771 : ℝ) / 9822738379581332) * (h 3 0) + ((-9477086974209675 : ℝ) / 9822738379581332) * (h 5 1) + ((16579740392789475 : ℝ) / 19645476759162664) * (h 9 2) := by
  have r0 := H 14 1
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 1 - h 2 1) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 81 1
  change ((1170647327728572 : ℤ) : ℝ) * (h 26 1 - h 18 1) - ((2663495031967425 : ℤ) : ℝ) * (h 26 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 90 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 22 0) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 103 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 26 0) - ((0 : ℤ) : ℝ) * (h 30 1 - h 26 1) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-1 : ℝ) / 9074785486268) * r0 + ((181264422564661829297591902875 : ℝ) / 1723016319939261858364576354202499075748624) * r1 + ((-60421474188220609765863967625 : ℝ) / 4000843894898966035122546294458202853888304928) * r2 + ((1 : ℝ) / 1170647327728572) * r3 + ((20647248309825 : ℝ) / 1518948363062938929906044414944) * r4 + ((20647248309825 : ℝ) / 9074785486268) * r5 + ((-20647248309825 : ℝ) / 9074785486268) * r6 + (1 : ℝ) * (value_009 h H) + ((-78305524944713615753353496175 : ℝ) / 759474181531469464953022207472) * (value_008 h H) + ((-181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_010 h H) + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_082 h H) + ((78305524944713615753353496175 : ℝ) / 759474181531469464953022207472) * (value_080 h H)

/-- Coordinate 26.2, recovered from skew spokes on cycle 12. -/
theorem value_106 (h : Assignment) (H : Constraints h) :
    h 26 2 = ((2205155887507727 : ℝ) / 4911369189790666) * (h 1 0) + ((-9145265966661627 : ℝ) / 4911369189790666) * (h 1 1) + ((15999234359976659 : ℝ) / 9822738379581332) * (h 1 2) + ((-2205155887507727 : ℝ) / 4911369189790666) * (h 3 0) + ((9145265966661627 : ℝ) / 4911369189790666) * (h 5 1) + ((-6176495980395327 : ℝ) / 9822738379581332) * (h 9 2) := by
  have r0 := H 14 1
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 1 - h 2 1) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 1
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 1 - h 18 1) - ((2095105532813019049 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 81 2
  change ((1170647327728572 : ℤ) : ℝ) * (h 26 2 - h 18 2) - ((43973215602920386 : ℤ) : ℝ) * (h 26 0 - h 18 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 85 1
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 1 - h 20 1) - ((6364630054597567 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 90 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 22 0) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 103 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 26 0) - ((0 : ℤ) : ℝ) * (h 30 1 - h 26 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((459 : ℝ) / 3643526372736602) * r0 + ((-83341079959661609825314960756589 : ℝ) / 691791052455613636133377406212303378913072536) * r1 + ((-17 : ℝ) / 940029804166043316) * r2 + ((2369619662813454093551785560529 : ℝ) / 1606338823801934863101702337224968445836154428592) * r3 + ((1 : ℝ) / 1170647327728572) * r4 + ((459 : ℝ) / 28198494857091614660) * r5 + ((-7108858988440362280655356681587 : ℝ) / 5354007200502251265012530579584508004253499184880) * r6 + ((21986607801460193 : ℝ) / 585323663864286) * r7 + ((-21986607801460193 : ℝ) / 585323663864286) * r8 + ((-918 : ℝ) / 803) * (value_009 h H) + ((43165185525985106255370893475 : ℝ) / 379737090765734732476511103736) * (value_008 h H) + ((83341079959661609825314960756589 : ℝ) / 76232220971221247544659604075002) * (value_010 h H) + ((918 : ℝ) / 803) * (value_081 h H) + ((-43165185525985106255370893475 : ℝ) / 379737090765734732476511103736) * (value_080 h H) + ((-7108858988440362280655356681587 : ℝ) / 76232220971221247544659604075002) * (value_082 h H)

/-- Coordinate 26.3, recovered from skew spokes on cycle 12. -/
theorem value_107 (h : Assignment) (H : Constraints h) :
    h 26 3 = ((-588757460640426 : ℝ) / 2455684594895333) * (h 1 0) + ((108824997255192 : ℝ) / 2455684594895333) * (h 1 1) + ((-95192236161132 : ℝ) / 2455684594895333) * (h 1 2) + h 1 3 + ((588757460640426 : ℝ) / 2455684594895333) * (h 3 0) + ((-108824997255192 : ℝ) / 2455684594895333) * (h 5 1) + ((95192236161132 : ℝ) / 2455684594895333) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 3
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 3 - h 2 3) - ((-948365989152 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 81 3
  change ((1170647327728572 : ℤ) : ℝ) * (h 26 3 - h 18 3) - ((122339212600608 : ℤ) : ℝ) * (h 26 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 90 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 22 0) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 103 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 26 0) - ((0 : ℤ) : ℝ) * (h 30 1 - h 26 1) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((520362964425266072908540710 : ℝ) / 107688519996203866147786022137656192234289) * r0 + ((-1 : ℝ) / 9074785486268) * r1 + ((-86727160737544345484756785 : ℝ) / 125026371715592688597579571701818839184009529) * r2 + ((1 : ℝ) / 1170647327728572) * r3 + ((29636437161 : ℝ) / 47467136345716841559563887967) * r4 + ((237091497288 : ℝ) / 2268696371567) * r5 + ((-237091497288 : ℝ) / 2268696371567) * r6 + ((-2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_010 h H) + ((-224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_008 h H) + (1 : ℝ) * (value_011 h H) + ((2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_082 h H) + ((224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_080 h H)

/-- Coordinate 30.0, recovered from skew spokes on cycle 12. -/
theorem value_120 (h : Assignment) (H : Constraints h) :
    h 30 0 = ((1119392371268413 : ℝ) / 2455684594895333) * (h 1 0) + ((1041331634549253 : ℝ) / 2455684594895333) * (h 1 1) + ((-1821763186368301 : ℝ) / 4911369189790666) * (h 1 2) + ((1336292223626920 : ℝ) / 2455684594895333) * (h 3 0) + ((-1041331634549253 : ℝ) / 2455684594895333) * (h 5 1) + ((1821763186368301 : ℝ) / 4911369189790666) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 90 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 22 0) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((8779107987886555 : ℝ) / 189868545382867366238255551868) * r0 + ((-8779107987886555 : ℝ) / 1322624287137054073215688174312488) * r1 + ((2268696371567 : ℝ) / 379737090765734732476511103736) * r2 + (1 : ℝ) * r3 + ((-19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_010 h H) + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_008 h H) + ((19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_082 h H) + ((8604122818205536940663648993 : ℝ) / 189868545382867366238255551868) * (value_080 h H)

/-- Coordinate 30.1, recovered from skew spokes on cycle 12. -/
theorem value_121 (h : Assignment) (H : Constraints h) :
    h 30 1 = ((6713376906904283 : ℝ) / 19645476759162664) * (h 1 0) + ((-9978558405160779 : ℝ) / 19645476759162664) * (h 1 1) + ((17457042264366243 : ℝ) / 39290953518325328) * (h 1 2) + ((-6713376906904283 : ℝ) / 19645476759162664) * (h 3 0) + ((29624035164323443 : ℝ) / 19645476759162664) * (h 5 1) + ((-17457042264366243 : ℝ) / 39290953518325328) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 85 1
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 1 - h 20 1) - ((6364630054597567 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 90 1
  change ((1 : ℤ) : ℝ) * (h 30 1 - h 22 1) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((6364630054597567 : ℝ) / 1518948363062938929906044414944) * r0 + ((-6364630054597567 : ℝ) / 10580994297096432585725505394499904) * r1 + ((1 : ℝ) / 70232863903092440) * r2 + ((14439413111231777359286177489 : ℝ) / 26670023414706108418493303011628931528037355840) * r3 + (1 : ℝ) * r4 + ((-14439413111231777359286177489 : ℝ) / 379737090765734732476511103736) * (value_010 h H) + ((131412097137451012711307195775 : ℝ) / 1518948363062938929906044414944) * (value_008 h H) + (1 : ℝ) * (value_081 h H) + ((-131412097137451012711307195775 : ℝ) / 1518948363062938929906044414944) * (value_080 h H) + ((14439413111231777359286177489 : ℝ) / 379737090765734732476511103736) * (value_082 h H)

/-- Coordinate 30.2, recovered from skew spokes on cycle 12. -/
theorem value_122 (h : Assignment) (H : Constraints h) :
    h 30 2 = ((2205155887507727 : ℝ) / 4911369189790666) * (h 1 0) + ((-9145265966661627 : ℝ) / 4911369189790666) * (h 1 1) + ((15999234359976659 : ℝ) / 9822738379581332) * (h 1 2) + ((-2205155887507727 : ℝ) / 4911369189790666) * (h 3 0) + ((9145265966661627 : ℝ) / 4911369189790666) * (h 5 1) + ((-6176495980395327 : ℝ) / 9822738379581332) * (h 9 2) := by
  have r0 := H 14 1
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 1 - h 2 1) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 1
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 1 - h 18 1) - ((2095105532813019049 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 81 2
  change ((1170647327728572 : ℤ) : ℝ) * (h 26 2 - h 18 2) - ((43973215602920386 : ℤ) : ℝ) * (h 26 0 - h 18 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 85 1
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 1 - h 20 1) - ((6364630054597567 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 90 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 22 0) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 103 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 26 0) - ((0 : ℤ) : ℝ) * (h 30 1 - h 26 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 103 2
  change ((1 : ℤ) : ℝ) * (h 30 2 - h 26 2) - ((0 : ℤ) : ℝ) * (h 30 1 - h 26 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((459 : ℝ) / 3643526372736602) * r0 + ((-83341079959661609825314960756589 : ℝ) / 691791052455613636133377406212303378913072536) * r1 + ((-17 : ℝ) / 940029804166043316) * r2 + ((2369619662813454093551785560529 : ℝ) / 1606338823801934863101702337224968445836154428592) * r3 + ((1 : ℝ) / 1170647327728572) * r4 + ((459 : ℝ) / 28198494857091614660) * r5 + ((-7108858988440362280655356681587 : ℝ) / 5354007200502251265012530579584508004253499184880) * r6 + ((21986607801460193 : ℝ) / 585323663864286) * r7 + ((-21986607801460193 : ℝ) / 585323663864286) * r8 + (1 : ℝ) * r9 + ((-918 : ℝ) / 803) * (value_009 h H) + ((43165185525985106255370893475 : ℝ) / 379737090765734732476511103736) * (value_008 h H) + ((83341079959661609825314960756589 : ℝ) / 76232220971221247544659604075002) * (value_010 h H) + ((918 : ℝ) / 803) * (value_081 h H) + ((-43165185525985106255370893475 : ℝ) / 379737090765734732476511103736) * (value_080 h H) + ((-7108858988440362280655356681587 : ℝ) / 76232220971221247544659604075002) * (value_082 h H)

/-- Coordinate 30.3, recovered from skew spokes on cycle 12. -/
theorem value_123 (h : Assignment) (H : Constraints h) :
    h 30 3 = ((-588757460640426 : ℝ) / 2455684594895333) * (h 1 0) + ((108824997255192 : ℝ) / 2455684594895333) * (h 1 1) + ((-95192236161132 : ℝ) / 2455684594895333) * (h 1 2) + h 1 3 + ((588757460640426 : ℝ) / 2455684594895333) * (h 3 0) + ((-108824997255192 : ℝ) / 2455684594895333) * (h 5 1) + ((95192236161132 : ℝ) / 2455684594895333) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 3
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 3 - h 2 3) - ((-948365989152 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 80 3
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 3 - h 18 3) - ((6606317480432832 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 90 3
  change ((1 : ℤ) : ℝ) * (h 30 3 - h 22 3) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((520362964425266072908540710 : ℝ) / 107688519996203866147786022137656192234289) * r0 + ((-1 : ℝ) / 9074785486268) * r1 + ((-86727160737544345484756785 : ℝ) / 125026371715592688597579571701818839184009529) * r2 + ((1 : ℝ) / 63214955697342888) * r3 + ((29636437161 : ℝ) / 47467136345716841559563887967) * r4 + (1 : ℝ) * r5 + ((-2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_010 h H) + ((-224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_008 h H) + (1 : ℝ) * (value_011 h H) + ((2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_082 h H) + ((224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_080 h H)

/-- Coordinate 19.0, recovered from skew spokes on cycle 13. -/
theorem value_076 (h : Assignment) (H : Constraints h) :
    h 19 0 = ((12807158174847 : ℝ) / 4732319651584) * (h 1 1) + ((-104828961357081 : ℝ) / 47323196515840) * (h 1 2) + h 3 0 + ((-12807158174847 : ℝ) / 4732319651584) * (h 5 1) + ((104828961357081 : ℝ) / 47323196515840) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 1
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 1 - h 19 1) - ((17519635479827047 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-3483 : ℝ) / 19000263401109760) * r0 + ((-2502805068546721 : ℝ) / 1153862454510034637977396480) * r1 + ((1 : ℝ) / 19000263401109760) * r2 + ((2502805068546721 : ℝ) / 4018902929058450644075271939840) * r3 + ((-1652123404555263 : ℝ) / 9500131700554880) * r4 + ((-1187178533099505335152093581 : ℝ) / 576931227255017318988698240) * r5 + ((1652123404555263 : ℝ) / 9500131700554880) * (value_013 h H) + ((1187178533099505335152093581 : ℝ) / 576931227255017318988698240) * (value_014 h H) + ((-1652123404555263 : ℝ) / 9500131700554880) * (value_085 h H) + ((-1187178533099505335152093581 : ℝ) / 576931227255017318988698240) * (value_086 h H)

/-- Coordinate 19.1, recovered from skew spokes on cycle 13. -/
theorem value_077 (h : Assignment) (H : Constraints h) :
    h 19 1 = ((-287585217247 : ℝ) / 1352091329024) * (h 1 1) + ((13421056175033 : ℝ) / 13520913290240) * (h 1 2) + ((1639676546271 : ℝ) / 1352091329024) * (h 5 1) + ((-13421056175033 : ℝ) / 13520913290240) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 1
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 1 - h 19 1) - ((17519635479827047 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-2502805068546721 : ℝ) / 2575019880865281762496488960) * r0 + ((2502805068546721 : ℝ) / 2575019880865281762496488960) * r1 + ((-60728760973 : ℝ) / 2575019880865281762496488960) * r2 + ((-2502805068546721 : ℝ) / 8968794245053776378775271047680) * r3 + ((211518274468959 : ℝ) / 2714323343015680) * r4 + ((2502805068546721 : ℝ) / 2714323343015680) * r5 + ((2502805068546721 : ℝ) / 2714323343015680) * (value_013 h H) + ((-2502805068546721 : ℝ) / 2714323343015680) * (value_014 h H) + ((211518274468959 : ℝ) / 2714323343015680) * (value_085 h H) + ((2502805068546721 : ℝ) / 2714323343015680) * (value_086 h H)

/-- Coordinate 19.2, recovered from skew spokes on cycle 13. -/
theorem value_078 (h : Assignment) (H : Constraints h) :
    h 19 2 = ((-1639676546271 : ℝ) / 1352091329024) * (h 1 1) + ((26941969465273 : ℝ) / 13520913290240) * (h 1 2) + ((1639676546271 : ℝ) / 1352091329024) * (h 5 1) + ((-13421056175033 : ℝ) / 13520913290240) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 1
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 1 - h 19 1) - ((17519635479827047 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((23502030496551 : ℝ) / 286113320096142418055165440) * r0 + ((-23502030496551 : ℝ) / 286113320096142418055165440) * r1 + ((-60728760973 : ℝ) / 2575019880865281762496488960) * r2 + ((-2502805068546721 : ℝ) / 8968794245053776378775271047680) * r3 + ((211518274468959 : ℝ) / 2714323343015680) * r4 + ((2502805068546721 : ℝ) / 2714323343015680) * r5 + ((-211518274468959 : ℝ) / 2714323343015680) * (value_013 h H) + ((211518274468959 : ℝ) / 2714323343015680) * (value_014 h H) + ((211518274468959 : ℝ) / 2714323343015680) * (value_085 h H) + ((2502805068546721 : ℝ) / 2714323343015680) * (value_086 h H)

/-- Coordinate 19.3, recovered from skew spokes on cycle 13. -/
theorem value_079 (h : Assignment) (H : Constraints h) :
    h 19 3 = ((-800183803347 : ℝ) / 676045664512) * (h 1 1) + ((6549652612581 : ℝ) / 6760456645120) * (h 1 2) + h 1 3 + ((800183803347 : ℝ) / 676045664512) * (h 5 1) + ((-6549652612581 : ℝ) / 6760456645120) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 17 3
  change ((-948678383322 : ℤ) : ℝ) * (h 19 3 - h 3 3) - ((414910120254 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 1
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 1 - h 19 1) - ((17519635479827047 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((11469301181307 : ℝ) / 143056660048071209027582720) * r0 + ((24724741713405731503033027 : ℝ) / 26062961140965105428157572300595559680) * r1 + ((-1 : ℝ) / 948678383322) * r2 + ((-9878812387 : ℝ) / 429169980144213627082748160) * r3 + ((-24724741713405731503033027 : ℝ) / 90777293653981462206272824322974334365440) * r4 + ((103223710631763 : ℝ) / 1357161671507840) * r5 + ((74174225140217194509099081 : ℝ) / 82418746750716759855528320) * r6 + ((-103223710631763 : ℝ) / 1357161671507840) * (value_013 h H) + ((-74174225140217194509099081 : ℝ) / 82418746750716759855528320) * (value_014 h H) + (1 : ℝ) * (value_015 h H) + ((103223710631763 : ℝ) / 1357161671507840) * (value_085 h H) + ((74174225140217194509099081 : ℝ) / 82418746750716759855528320) * (value_086 h H)

/-- Coordinate 23.0, recovered from skew spokes on cycle 13. -/
theorem value_092 (h : Assignment) (H : Constraints h) :
    h 23 0 = ((435443377944798 : ℝ) / 144315980241685) * (h 1 1) + ((-380894370903783 : ℝ) / 144315980241685) * (h 1 2) + h 3 0 + ((-435443377944798 : ℝ) / 144315980241685) * (h 5 1) + ((380894370903783 : ℝ) / 144315980241685) * (h 9 2) := by
  have r0 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((-1 : ℝ) / 425101326811) * r0 + ((1 : ℝ) / 1480627921282713) * r1 + ((-948678383322 : ℝ) / 425101326811) * r2 + ((948678383322 : ℝ) / 425101326811) * (value_014 h H) + ((-948678383322 : ℝ) / 425101326811) * (value_086 h H)

/-- Coordinate 23.1, recovered from skew spokes on cycle 13. -/
theorem value_093 (h : Assignment) (H : Constraints h) :
    h 23 1 = ((59216465721051 : ℝ) / 41233137211910) * (h 1 1) + ((-103596562034867 : ℝ) / 82466274423820) * (h 1 2) + ((-17983328509141 : ℝ) / 41233137211910) * (h 5 1) + ((103596562034867 : ℝ) / 82466274423820) * (h 9 2) := by
  have r0 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_085 h H)

/-- Coordinate 23.2, recovered from skew spokes on cycle 13. -/
theorem value_094 (h : Assignment) (H : Constraints h) :
    h 23 2 = ((-27874501286607 : ℝ) / 20616568605955) * (h 1 1) + ((89998332273229 : ℝ) / 41233137211910) * (h 1 2) + ((27874501286607 : ℝ) / 20616568605955) * (h 5 1) + ((-48765195061319 : ℝ) / 41233137211910) * (h 9 2) := by
  have r0 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_086 h H)

/-- Coordinate 23.3, recovered from skew spokes on cycle 13. -/
theorem value_095 (h : Assignment) (H : Constraints h) :
    h 23 3 = ((-27206249313798 : ℝ) / 20616568605955) * (h 1 1) + ((23798059040283 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((27206249313798 : ℝ) / 20616568605955) * (h 5 1) + ((-23798059040283 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 3
  change ((-948678383322 : ℤ) : ℝ) * (h 19 3 - h 3 3) - ((414910120254 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 3
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 3 - h 19 3) - ((-1445131948844682 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((9878812387 : ℝ) / 9602010463502301282051) * r0 + ((-1 : ℝ) / 948678383322) * r1 + ((-9878812387 : ℝ) / 33443802444378515365383633) * r2 + ((1 : ℝ) / 3304246809110526) * r3 + ((59272874322 : ℝ) / 60728760973) * r4 + ((-59272874322 : ℝ) / 60728760973) * (value_014 h H) + (1 : ℝ) * (value_015 h H) + ((59272874322 : ℝ) / 60728760973) * (value_086 h H)

/-- Coordinate 27.0, recovered from skew spokes on cycle 13. -/
theorem value_108 (h : Assignment) (H : Constraints h) :
    h 27 0 = ((435443377944798 : ℝ) / 144315980241685) * (h 1 1) + ((-380894370903783 : ℝ) / 144315980241685) * (h 1 2) + h 3 0 + ((-435443377944798 : ℝ) / 144315980241685) * (h 5 1) + ((380894370903783 : ℝ) / 144315980241685) * (h 9 2) := by
  have r0 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 91 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 23 0) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 107 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 27 0) - ((0 : ℤ) : ℝ) * (h 31 1 - h 27 1) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((-1 : ℝ) / 425101326811) * r0 + ((1 : ℝ) / 1480627921282713) * r1 + ((-948678383322 : ℝ) / 425101326811) * r2 + (1 : ℝ) * r3 + (-1 : ℝ) * r4 + ((948678383322 : ℝ) / 425101326811) * (value_014 h H) + ((-948678383322 : ℝ) / 425101326811) * (value_086 h H)

/-- Coordinate 27.1, recovered from skew spokes on cycle 13. -/
theorem value_109 (h : Assignment) (H : Constraints h) :
    h 27 1 = ((-7257932680652 : ℝ) / 20616568605955) * (h 1 1) + ((48765195061319 : ℝ) / 41233137211910) * (h 1 2) + ((27874501286607 : ℝ) / 20616568605955) * (h 5 1) + ((-48765195061319 : ℝ) / 41233137211910) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 83 1
  change ((122379511448538 : ℤ) : ℝ) * (h 27 1 - h 19 1) - ((-54838071158619 : ℤ) : ℝ) * (h 27 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 91 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 23 0) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 107 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 27 0) - ((0 : ℤ) : ℝ) * (h 31 1 - h 27 1) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-1 : ℝ) / 948678383322) * r0 + ((1 : ℝ) / 948678383322) * r1 + ((-1 : ℝ) / 3304246809110526) * r2 + ((1 : ℝ) / 122379511448538) * r3 + (1 : ℝ) * r4 + ((-425101326811 : ℝ) / 948678383322) * r5 + ((425101326811 : ℝ) / 948678383322) * r6 + (1 : ℝ) * (value_013 h H) + (-1 : ℝ) * (value_014 h H) + (1 : ℝ) * (value_086 h H)

/-- Coordinate 27.2, recovered from skew spokes on cycle 13. -/
theorem value_110 (h : Assignment) (H : Constraints h) :
    h 27 2 = ((14271376629708 : ℝ) / 20616568605955) * (h 1 1) + ((-12483568010518 : ℝ) / 20616568605955) * (h 1 2) + ((-14271376629708 : ℝ) / 20616568605955) * (h 5 1) + ((33100136616473 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 1
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 1 - h 19 1) - ((17519635479827047 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 83 2
  change ((122379511448538 : ℤ) : ℝ) * (h 27 2 - h 19 2) - ((749656269610661 : ℤ) : ℝ) * (h 27 0 - h 19 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 91 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 23 0) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 107 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 27 0) - ((0 : ℤ) : ℝ) * (h 31 1 - h 27 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((51 : ℝ) / 42321596767087) * r0 + ((-51 : ℝ) / 42321596767087) * r1 + ((-17 : ℝ) / 49135373846588007) * r2 + ((115 : ℝ) / 2653310187715752378) * r3 + ((1 : ℝ) / 122379511448538) * r4 + ((918 : ℝ) / 803) * r5 + ((-115 : ℝ) / 803) * r6 + ((749656269610661 : ℝ) / 122379511448538) * r7 + ((-749656269610661 : ℝ) / 122379511448538) * r8 + ((-918 : ℝ) / 803) * (value_013 h H) + ((918 : ℝ) / 803) * (value_014 h H) + ((918 : ℝ) / 803) * (value_085 h H) + ((-115 : ℝ) / 803) * (value_086 h H)

/-- Coordinate 27.3, recovered from skew spokes on cycle 13. -/
theorem value_111 (h : Assignment) (H : Constraints h) :
    h 27 3 = ((-27206249313798 : ℝ) / 20616568605955) * (h 1 1) + ((23798059040283 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((27206249313798 : ℝ) / 20616568605955) * (h 5 1) + ((-23798059040283 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 3
  change ((-948678383322 : ℤ) : ℝ) * (h 19 3 - h 3 3) - ((414910120254 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 83 3
  change ((122379511448538 : ℤ) : ℝ) * (h 27 3 - h 19 3) - ((-53523405512766 : ℤ) : ℝ) * (h 27 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 91 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 23 0) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 107 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 27 0) - ((0 : ℤ) : ℝ) * (h 31 1 - h 27 1) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((9878812387 : ℝ) / 9602010463502301282051) * r0 + ((-1 : ℝ) / 948678383322) * r1 + ((-9878812387 : ℝ) / 33443802444378515365383633) * r2 + ((1 : ℝ) / 122379511448538) * r3 + ((59272874322 : ℝ) / 60728760973) * r4 + ((-69151686709 : ℝ) / 158113063887) * r5 + ((69151686709 : ℝ) / 158113063887) * r6 + ((-59272874322 : ℝ) / 60728760973) * (value_014 h H) + (1 : ℝ) * (value_015 h H) + ((59272874322 : ℝ) / 60728760973) * (value_086 h H)

/-- Coordinate 31.0, recovered from skew spokes on cycle 13. -/
theorem value_124 (h : Assignment) (H : Constraints h) :
    h 31 0 = ((435443377944798 : ℝ) / 144315980241685) * (h 1 1) + ((-380894370903783 : ℝ) / 144315980241685) * (h 1 2) + h 3 0 + ((-435443377944798 : ℝ) / 144315980241685) * (h 5 1) + ((380894370903783 : ℝ) / 144315980241685) * (h 9 2) := by
  have r0 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 91 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 23 0) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((-1 : ℝ) / 425101326811) * r0 + ((1 : ℝ) / 1480627921282713) * r1 + ((-948678383322 : ℝ) / 425101326811) * r2 + (1 : ℝ) * r3 + ((948678383322 : ℝ) / 425101326811) * (value_014 h H) + ((-948678383322 : ℝ) / 425101326811) * (value_086 h H)

/-- Coordinate 31.1, recovered from skew spokes on cycle 13. -/
theorem value_125 (h : Assignment) (H : Constraints h) :
    h 31 1 = ((59216465721051 : ℝ) / 41233137211910) * (h 1 1) + ((-103596562034867 : ℝ) / 82466274423820) * (h 1 2) + ((-17983328509141 : ℝ) / 41233137211910) * (h 5 1) + ((103596562034867 : ℝ) / 82466274423820) * (h 9 2) := by
  have r0 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 91 1
  change ((1 : ℤ) : ℝ) * (h 31 1 - h 23 1) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1 + (1 : ℝ) * (value_085 h H)

/-- Coordinate 31.2, recovered from skew spokes on cycle 13. -/
theorem value_126 (h : Assignment) (H : Constraints h) :
    h 31 2 = ((14271376629708 : ℝ) / 20616568605955) * (h 1 1) + ((-12483568010518 : ℝ) / 20616568605955) * (h 1 2) + ((-14271376629708 : ℝ) / 20616568605955) * (h 5 1) + ((33100136616473 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 1
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 1 - h 19 1) - ((17519635479827047 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 83 2
  change ((122379511448538 : ℤ) : ℝ) * (h 27 2 - h 19 2) - ((749656269610661 : ℤ) : ℝ) * (h 27 0 - h 19 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 91 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 23 0) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 107 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 27 0) - ((0 : ℤ) : ℝ) * (h 31 1 - h 27 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 107 2
  change ((1 : ℤ) : ℝ) * (h 31 2 - h 27 2) - ((0 : ℤ) : ℝ) * (h 31 1 - h 27 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((51 : ℝ) / 42321596767087) * r0 + ((-51 : ℝ) / 42321596767087) * r1 + ((-17 : ℝ) / 49135373846588007) * r2 + ((115 : ℝ) / 2653310187715752378) * r3 + ((1 : ℝ) / 122379511448538) * r4 + ((918 : ℝ) / 803) * r5 + ((-115 : ℝ) / 803) * r6 + ((749656269610661 : ℝ) / 122379511448538) * r7 + ((-749656269610661 : ℝ) / 122379511448538) * r8 + (1 : ℝ) * r9 + ((-918 : ℝ) / 803) * (value_013 h H) + ((918 : ℝ) / 803) * (value_014 h H) + ((918 : ℝ) / 803) * (value_085 h H) + ((-115 : ℝ) / 803) * (value_086 h H)

/-- Coordinate 31.3, recovered from skew spokes on cycle 13. -/
theorem value_127 (h : Assignment) (H : Constraints h) :
    h 31 3 = ((-27206249313798 : ℝ) / 20616568605955) * (h 1 1) + ((23798059040283 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((27206249313798 : ℝ) / 20616568605955) * (h 5 1) + ((-23798059040283 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 3
  change ((-948678383322 : ℤ) : ℝ) * (h 19 3 - h 3 3) - ((414910120254 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 3
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 3 - h 19 3) - ((-1445131948844682 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 91 3
  change ((1 : ℤ) : ℝ) * (h 31 3 - h 23 3) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((9878812387 : ℝ) / 9602010463502301282051) * r0 + ((-1 : ℝ) / 948678383322) * r1 + ((-9878812387 : ℝ) / 33443802444378515365383633) * r2 + ((1 : ℝ) / 3304246809110526) * r3 + ((59272874322 : ℝ) / 60728760973) * r4 + (1 : ℝ) * r5 + ((-59272874322 : ℝ) / 60728760973) * (value_014 h H) + (1 : ℝ) * (value_015 h H) + ((59272874322 : ℝ) / 60728760973) * (value_086 h H)

/-- Coordinate 48.0, recovered from nonplanar cycle 14. -/
theorem value_192 (h : Assignment) (H : Constraints h) :
    h 48 0 = ((777343598631346184615358841 : ℝ) / 1054049275990752831481248181) * (h 1 0) + ((-32673708890913507468542806734 : ℝ) / 32675527555713337775918693611) * (h 1 1) + ((25730972583399966856700360524 : ℝ) / 32675527555713337775918693611) * (h 1 2) + ((276705677359406646865889340 : ℝ) / 1054049275990752831481248181) * (h 3 0) + ((32673708890913507468542806734 : ℝ) / 32675527555713337775918693611) * (h 5 1) + ((-25730972583399966856700360524 : ℝ) / 32675527555713337775918693611) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-9 : ℝ) / 522808440891413404414699097776) * r0 + ((267439343514741224767662154085 : ℝ) / 501412970893659741630471408892960087425827898672277981824) * r1 + ((11184256210993020617805 : ℝ) / 11539043138164279103797546460233995068179864280632) * r2 + ((-332345570974293394641455911683402706409444867164825 : ℝ) / 11066818070710449644632182349654680334373993382286172124277612784854030421568) * r3 + ((10646169217730800848081715 : ℝ) / 12385064011883937207218790974912140348853335290175364478288) * r4 + ((-4320492422665814130338926851884235183322783273142725 : ℝ) / 162221466829005846075564634489692492763163736289417250659005536461023638980163037312) * r5 + ((-3257727780625625059513004790 : ℝ) / 32675527555713337775918693611) * (value_097 h H) + ((-198352154553638402281892030013241633118676490791757 : ℝ) / 2797314173065583669722794167259663078114276860396088) * (value_096 h H) + ((4320492422665814130338926851884235183322783273142725 : ℝ) / 1398657086532791834861397083629831539057138430198044) * (value_098 h H) + ((3257727780625625059513004790 : ℝ) / 32675527555713337775918693611) * (value_113 h H) + ((2995666327619222072004686197272904711232953351187845 : ℝ) / 2797314173065583669722794167259663078114276860396088) * (value_112 h H) + ((-4320492422665814130338926851884235183322783273142725 : ℝ) / 1398657086532791834861397083629831539057138430198044) * (value_114 h H)

/-- Coordinate 48.1, recovered from nonplanar cycle 14. -/
theorem value_193 (h : Assignment) (H : Constraints h) :
    h 48 1 = ((181991951077660052977278309 : ℝ) / 33729576831704090607399941792) * (h 1 0) + ((314625604589592308369047275445 : ℝ) / 522808440891413404414699097776) * (h 1 1) + ((-69685528373866284575206709495 : ℝ) / 522808440891413404414699097776) * (h 1 2) + ((-181991951077660052977278309 : ℝ) / 33729576831704090607399941792) * (h 3 0) + ((208182836301821096045651822331 : ℝ) / 522808440891413404414699097776) * (h 5 1) + ((69685528373866284575206709495 : ℝ) / 522808440891413404414699097776) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((46992041205039445673799552395 : ℝ) / 605570695764454212612526808649200123423397174169516923392) * r0 + ((6266336423646552704914976797246244669772602789544777281 : ℝ) / 2127429502445327844927176384425105846429191706444308938222988407322821877090103296) * r1 + ((22142171912785859695823179677 : ℝ) / 4136700808859341401595005215808046295962208625149449472) * r2 + ((-219321774827629344672024187903618563442041097634067204835 : ℝ) / 1322470003692471118600686281207268093717246377192021187288342357639676830003480576) * r3 + ((10661045735785784297988938363 : ℝ) / 2245824940821620613575674096784068116592071465951799425396224) * r4 + ((-2851183072759181480736314442747041324746534269242873662855 : ℝ) / 19385248990777093264901873068672266628541048934936975564083616266377043493277509408067584) * r5 + ((234960206025197228368997761975 : ℝ) / 522808440891413404414699097776) * (value_097 h H) + ((-1976902697510699784209606353945204353703043213119051571911 : ℝ) / 334275313929106494420314272595306724950551932448185321216) * (value_096 h H) + ((2851183072759181480736314442747041324746534269242873662855 : ℝ) / 167137656964553247210157136297653362475275966224092660608) * (value_098 h H) + ((287848234866216176045701335801 : ℝ) / 522808440891413404414699097776) * (value_113 h H) + ((1976902697510699784209606353945204353703043213119051571911 : ℝ) / 334275313929106494420314272595306724950551932448185321216) * (value_112 h H) + ((-2851183072759181480736314442747041324746534269242873662855 : ℝ) / 167137656964553247210157136297653362475275966224092660608) * (value_114 h H)

/-- Coordinate 48.2, recovered from nonplanar cycle 14. -/
theorem value_194 (h : Assignment) (H : Constraints h) :
    h 48 2 = ((2061667070398959704986122573 : ℝ) / 4216197103963011325924992724) * (h 1 0) + ((-134213750884978747507484829423 : ℝ) / 65351055111426675551837387222) * (h 1 1) + ((116253836556504342053382163315 : ℝ) / 65351055111426675551837387222) * (h 1 2) + ((-2061667070398959704986122573 : ℝ) / 4216197103963011325924992724) * (h 3 0) + ((134213750884978747507484829423 : ℝ) / 65351055111426675551837387222) * (h 5 1) + ((-50902781445077666501544776093 : ℝ) / 65351055111426675551837387222) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-117009665260111260838611 : ℝ) / 33783958301596347664271110899379637341749820035343040) * r0 + ((99688209007599858566830146942415910046464477761301 : ℝ) / 356059119618404865593006848236818125685506957920474806673935844303337589890560) * r1 + ((117009665260111260838611 : ℝ) / 600030243184542513397472415932167743545352942592864) * r2 + ((-3476998673560419790135955037240521657999713755486215 : ℝ) / 575474539676943381520873482182043377387447655878880950462435864812409581921536) * r3 + ((8567707711823702321404961 : ℝ) / 49540256047535748828875163899648561395413341160701457913152) * r4 + ((-3476998673560419790135955037240521657999713755486215 : ℝ) / 648885867316023384302258537958769971052654945157669002636022145844094555920652149248) * r5 + ((-1310859279909026455174959033 : ℝ) / 65351055111426675551837387222) * (value_097 h H) + ((-2410819607718430417322749417151299737186306259291463 : ℝ) / 11189256692262334678891176669038652312457107441584352) * (value_096 h H) + ((9071627019691587129581543371759847814228267476278391 : ℝ) / 5594628346131167339445588334519326156228553720792176) * (value_098 h H) + ((1310859279909026455174959033 : ℝ) / 65351055111426675551837387222) * (value_113 h H) + ((2410819607718430417322749417151299737186306259291463 : ℝ) / 11189256692262334678891176669038652312457107441584352) * (value_112 h H) + ((-3476998673560419790135955037240521657999713755486215 : ℝ) / 5594628346131167339445588334519326156228553720792176) * (value_114 h H)

/-- Coordinate 48.3, recovered from nonplanar cycle 14. -/
theorem value_195 (h : Assignment) (H : Constraints h) :
    h 48 3 = ((-267782522729277245542412112 : ℝ) / 1054049275990752831481248181) * (h 1 0) + ((4002714589940938903161736386 : ℝ) / 32675527555713337775918693611) * (h 1 1) + ((-3450783330695605018723130577 : ℝ) / 32675527555713337775918693611) * (h 1 2) + h 1 3 + ((267782522729277245542412112 : ℝ) / 1054049275990752831481248181) * (h 3 0) + ((-4002714589940938903161736386 : ℝ) / 32675527555713337775918693611) * (h 5 1) + ((3450783330695605018723130577 : ℝ) / 32675527555713337775918693611) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 96 3
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 3 - h 24 3) - ((-102638922139772590676165376 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((46013180225658690159 : ℝ) / 150821242417840837786924602229373380989954553729210) * r0 + ((-5361975909619012018812310659699734680373651917 : ℝ) / 567251048411674418224153067043950445332302751588991726318770340189140768208) * r1 + ((1 : ℝ) / 5791516054445555661356452960) * r2 + ((-322092261579610831113 : ℝ) / 18750945099516953543671012997880241985792279456027) * r3 + ((187669156836665420658430873089490713813077817095 : ℝ) / 352619203233421189657397967023310893007014495023824111802963152458584302648) * r4 + ((-7861437051146797692721 : ℝ) / 516044333828497383634116290621339181202222303757306853262) * r5 + ((187669156836665420658430873089490713813077817095 : ℝ) / 397601634384818250185207437474736501870499353650532477105405726620155977892556464) * r6 + ((57734393703622082255343024 : ℝ) / 32675527555713337775918693611) * (value_097 h H) + ((2212086035754208843771774536230306998597443727543 : ℝ) / 116554757211065986238449756969152628254761535849837) * (value_096 h H) + ((-6380751332446624302386649685042684269644645781230 : ℝ) / 116554757211065986238449756969152628254761535849837) * (value_098 h H) + (1 : ℝ) * (value_099 h H) + ((-57734393703622082255343024 : ℝ) / 32675527555713337775918693611) * (value_113 h H) + ((-2212086035754208843771774536230306998597443727543 : ℝ) / 116554757211065986238449756969152628254761535849837) * (value_112 h H) + ((6380751332446624302386649685042684269644645781230 : ℝ) / 116554757211065986238449756969152628254761535849837) * (value_114 h H)

/-- Coordinate 52.0, recovered from nonplanar cycle 14. -/
theorem value_208 (h : Assignment) (H : Constraints h) :
    h 52 0 = ((53540161796728255588055464436 : ℝ) / 72674441298858640087278575651) * (h 1 0) + ((-72478632673303706561023043496 : ℝ) / 72674441298858640087278575651) * (h 1 1) + ((57123224158121650301803519610 : ℝ) / 72674441298858640087278575651) * (h 1 2) + ((19134279502130384499223111215 : ℝ) / 72674441298858640087278575651) * (h 3 0) + ((72478632673303706561023043496 : ℝ) / 72674441298858640087278575651) * (h 5 1) + ((-57123224158121650301803519610 : ℝ) / 72674441298858640087278575651) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-397282752613584151101 : ℝ) / 23306367640923510534925481437863313348361188532360) * r0 + ((2881594236232237583160954498735011292965636516503 : ℝ) / 3193225042057723093664543934838762696429799470233973351668959639509796435520) * r1 + ((9 : ℝ) / 9377347264368856785455300084) * r2 + ((-456955243308046941546612221789 : ℝ) / 8993587676036210856805132296664826142766790131953438816) * r3 + ((378169037960063935831363 : ℝ) / 444289101120289438585768456621287728747991486724359221784) * r4 + ((-262225075497133620067646859384886027659872923001773 : ℝ) / 5819366747779169185697650401617087170798893366554321428601425899777186130307054016) * r5 + ((-231439451231559128728794156 : ℝ) / 2344336816092214196363825021) * (value_097 h H) + ((-50806812432100068774808749244587847252382269177873 : ℝ) / 100347983531601031607662370533169978384883403239684) * (value_096 h H) + ((262225075497133620067646859384886027659872923001773 : ℝ) / 50173991765800515803831185266584989192441701619842) * (value_098 h H) + ((231439451231559128728794156 : ℝ) / 2344336816092214196363825021) * (value_113 h H) + ((151154795963701100382471119777757825637265672417557 : ℝ) / 100347983531601031607662370533169978384883403239684) * (value_112 h H) + ((-262225075497133620067646859384886027659872923001773 : ℝ) / 50173991765800515803831185266584989192441701619842) * (value_114 h H)

/-- Coordinate 52.1, recovered from nonplanar cycle 14. -/
theorem value_209 (h : Assignment) (H : Constraints h) :
    h 52 1 = ((11499865489163555859586557291 : ℝ) / 581395530390869120698228605208) * (h 1 0) + ((160626840066267720921754585353 : ℝ) / 290697765195434560349114302604) * (h 1 1) + ((-30859835989602710605426082479 : ℝ) / 290697765195434560349114302604) * (h 1 2) + ((-11499865489163555859586557291 : ℝ) / 581395530390869120698228605208) * (h 3 0) + ((130070925129166839427359717251 : ℝ) / 290697765195434560349114302604) * (h 5 1) + ((30859835989602710605426082479 : ℝ) / 290697765195434560349114302604) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((4043466963996211447571115909 : ℝ) / 54309057229703346412736195058063601483871602186630048640) * r0 + ((-752007908156670201305673407778639247968810713716131193 : ℝ) / 190793067446254249697727390410659511936549565146833085113319225820950663824696320) * r1 + ((24135204979061743610335675 : ℝ) / 4364581407487763576164893452252862962433655610750144) * r2 + ((5264055357096691409139713854450474735781674996012918351 : ℝ) / 23720467194811781461289858175694786448502236212859104855335972237953817905462784) * r3 + ((-149758035703563386947078367 : ℝ) / 40282211834906242431776340066996754073151228129675236108416) * r4 + ((68432719642256988318816280107856171565161774948167938563 : ℝ) / 347703283601973506065977479729686547063786679389376335811316129894420353161759606086656) * r5 + ((4043466963996211447571115909 : ℝ) / 9377347264368856785455300084) * (value_097 h H) + ((13259023167373046758818870178652679467588702490059917663 : ℝ) / 5995725117357473904536754864443217428511193421302292544) * (value_096 h H) + ((-68432719642256988318816280107856171565161774948167938563 : ℝ) / 2997862558678736952268377432221608714255596710651146272) * (value_098 h H) + ((5333880300372645337884184175 : ℝ) / 9377347264368856785455300084) * (value_113 h H) + ((-13259023167373046758818870178652679467588702490059917663 : ℝ) / 5995725117357473904536754864443217428511193421302292544) * (value_112 h H) + ((68432719642256988318816280107856171565161774948167938563 : ℝ) / 2997862558678736952268377432221608714255596710651146272) * (value_114 h H)

/-- Coordinate 52.2, recovered from nonplanar cycle 14. -/
theorem value_210 (h : Assignment) (H : Constraints h) :
    h 52 2 = ((35551202651472366183311254002 : ℝ) / 72674441298858640087278575651) * (h 1 0) + ((-149303068254927490314397680882 : ℝ) / 72674441298858640087278575651) * (h 1 1) + ((129308514503944045342629379669 : ℝ) / 72674441298858640087278575651) * (h 1 2) + ((-35551202651472366183311254002 : ℝ) / 72674441298858640087278575651) * (h 3 0) + ((149303068254927490314397680882 : ℝ) / 72674441298858640087278575651) * (h 5 1) + ((-56634073205085405255350804018 : ℝ) / 72674441298858640087278575651) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-531215624692007731647 : ℝ) / 151491389666002818477015629346111536764347725460340) * r0 + ((296387991489832163199975185549618018136425834257 : ℝ) / 1596612521028861546832271967419381348214899735116986675834479819754898217760) * r1 + ((531215624692007731647 : ℝ) / 2690608796345833008826992359602011499982811216794) * r2 + ((-55420921843366733802416154462433678064526473749 : ℝ) / 75897000786755802426731848747520414658132801572115751669565179928186818584) * r3 + ((38896788519114788350597 : ℝ) / 222144550560144719292884228310643864373995743362179610892) * r4 + ((-26971307225574726851197741885015239650414750917387 : ℝ) / 2909683373889584592848825200808543585399446683277160714300712949888593065153527008) * r5 + ((-47609669147396500941130728 : ℝ) / 2344336816092214196363825021) * (value_097 h H) + ((-5225763190878743665149810666045011232913848353287 : ℝ) / 50173991765800515803831185266584989192441701619842) * (value_096 h H) + ((26971307225574726851197741885015239650414750917387 : ℝ) / 25086995882900257901915592633292494596220850809921) * (value_098 h H) + ((47609669147396500941130728 : ℝ) / 2344336816092214196363825021) * (value_113 h H) + ((5225763190878743665149810666045011232913848353287 : ℝ) / 50173991765800515803831185266584989192441701619842) * (value_112 h H) + ((-1884311342674468949282149251722745054193900107466 : ℝ) / 25086995882900257901915592633292494596220850809921) * (value_114 h H)

/-- Coordinate 52.3, recovered from nonplanar cycle 14. -/
theorem value_211 (h : Assignment) (H : Constraints h) :
    h 52 3 = ((-18460491794733377438954686152 : ℝ) / 72674441298858640087278575651) * (h 1 0) + ((8893840324418822981414494530 : ℝ) / 72674441298858640087278575651) * (h 1 1) + ((-7670180634305715487985049609 : ℝ) / 72674441298858640087278575651) * (h 1 2) + h 1 3 + ((18460491794733377438954686152 : ℝ) / 72674441298858640087278575651) * (h 3 0) + ((-8893840324418822981414494530 : ℝ) / 72674441298858640087278575651) * (h 5 1) + ((7670180634305715487985049609 : ℝ) / 72674441298858640087278575651) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 113 3
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 3 - h 28 3) - ((-1794845640955164300638976 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((212544288389161242 : ℝ) / 714582026726428389042526553519394041341262855945) * r0 + ((-1162623321298150205724030379693338413126801 : ℝ) / 73835207224790119627833516806297694608532174209997534028601545493659740) * r1 + ((-22529694569251091652 : ℝ) / 1345304398172916504413496179801005749991405608397) * r2 + ((431333252201613726323615270866228551270043171 : ℝ) / 486519235812537195043152876586669324731620522898177895317725512360171914) * r3 + ((1 : ℝ) / 102861978325137390546130736) * r4 + ((-274945717058082766642 : ℝ) / 18512045880012059941073685692553655364499645280181634241) * r5 + ((5607332278620978442206998521260971166510561223 : ℝ) / 7131576896788197531492218629432704866175114419796962535050767034040669277337076) * r6 + ((4038402692149119676437696 : ℝ) / 2344336816092214196363825021) * (value_097 h H) + ((73877626528771814852787874377545267459434957964 : ℝ) / 8362331960966752633971864211097498198740283603307) * (value_096 h H) + ((-762597189892453068140151798891492078645436326328 : ℝ) / 8362331960966752633971864211097498198740283603307) * (value_098 h H) + ((-4038402692149119676437696 : ℝ) / 2344336816092214196363825021) * (value_113 h H) + ((-73877626528771814852787874377545267459434957964 : ℝ) / 8362331960966752633971864211097498198740283603307) * (value_112 h H) + ((762597189892453068140151798891492078645436326328 : ℝ) / 8362331960966752633971864211097498198740283603307) * (value_114 h H) + (1 : ℝ) * (value_115 h H)

/-- Coordinate 68.0, recovered from nonplanar cycle 15. -/
theorem value_272 (h : Assignment) (H : Constraints h) :
    h 68 0 = ((592360119142457741376988247 : ℝ) / 782252171153441540641802252) * (h 1 0) + ((-5428426250568344182008510411 : ℝ) / 5084639112497370014171714638) * (h 1 1) + ((4193580421215274133070474349 : ℝ) / 5084639112497370014171714638) * (h 1 2) + ((189892052010983799264814005 : ℝ) / 782252171153441540641802252) * (h 3 0) + ((5428426250568344182008510411 : ℝ) / 5084639112497370014171714638) * (h 5 1) + ((-4193580421215274133070474349 : ℝ) / 5084639112497370014171714638) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-27 : ℝ) / 40677112899978960113373717104) * r0 + ((6087793873111237828341919525 : ℝ) / 869769183161367153610622770561335594988148116503599104) * r1 + ((18872052133739110457913 : ℝ) / 27370652954866520312911971639344348244341579126656) * r2 + ((-4255154198252326641550578260532690394616894275975 : ℝ) / 585246807502895003467259267114234357508686894825473556632216135987397574656) * r3 + ((460617865042002733028321 : ℝ) / 20650386866775547166195602454984750793380867468338957232) * r4 + ((-4255154198252326641550578260532690394616894275975 : ℝ) / 18090910996698616947368282418177661958544807042412458222981809939761628410116096) * r5 + ((-634270800162837763379998017 : ℝ) / 5084639112497370014171714638) * (value_097 h H) + ((-176920156218807693408441883987636073522688366373 : ℝ) / 373255611117801187186563510873347624515131642496) * (value_096 h H) + ((12765462594756979924651734781598071183850682827925 : ℝ) / 9704645889062830866850651282707038237393422704896) * (value_098 h H) + ((634270800162837763379998017 : ℝ) / 5084639112497370014171714638) * (value_113 h H) + ((550175767336608880595005394860983698037820008869 : ℝ) / 373255611117801187186563510873347624515131642496) * (value_112 h H) + ((-12765462594756979924651734781598071183850682827925 : ℝ) / 9704645889062830866850651282707038237393422704896) * (value_114 h H)

/-- Coordinate 68.1, recovered from nonplanar cycle 15. -/
theorem value_273 (h : Assignment) (H : Constraints h) :
    h 68 1 = ((-281873812034490437149632993 : ℝ) / 6258017369227532325134418016) * (h 1 0) + ((31503118265292785232231262877 : ℝ) / 40677112899978960113373717104) * (h 1 1) + ((-9291944721704916188588246191 : ℝ) / 40677112899978960113373717104) * (h 1 2) + ((281873812034490437149632993 : ℝ) / 6258017369227532325134418016) * (h 3 0) + ((9173994634686174881142454227 : ℝ) / 40677112899978960113373717104) * (h 5 1) + ((9291944721704916188588246191 : ℝ) / 40677112899978960113373717104) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((20880446715448310685376954031 : ℝ) / 7644534799224813362863963584513448847707942527833772672) * r0 + ((4463630485415337523083213045920005038690122236128062975 : ℝ) / 163457539484663153202126652843500821119303668711623277139106394760834662187548672) * r1 + ((6598888728176883142665587691 : ℝ) / 2453067400426957016524422546204597867050869687647417344) * r2 + ((-4463630485415337523083213045920005038690122236128062975 : ℝ) / 157356479626918385372248933667538420172075662785514726118817216915203560692908032) * r3 + ((733209858686320349185065299 : ℝ) / 8425357841644423243807805801633778323699393927082294550656) * r4 + ((-4463630485415337523083213045920005038690122236128062975 : ℝ) / 4864139421504350535872804830340264326117859359107522467329565202123588553884734963712) * r5 + ((20880446715448310685376954031 : ℝ) / 40677112899978960113373717104) * (value_097 h H) + ((-577130983509152204314062725969921177174050064615895949 : ℝ) / 100357982672465440801225704295538722498632474981184512) * (value_096 h H) + ((4463630485415337523083213045920005038690122236128062975 : ℝ) / 869769183161367153610622770561335594988148116503599104) * (value_098 h H) + ((19796666184530649427996763073 : ℝ) / 40677112899978960113373717104) * (value_113 h H) + ((577130983509152204314062725969921177174050064615895949 : ℝ) / 100357982672465440801225704295538722498632474981184512) * (value_112 h H) + ((-4463630485415337523083213045920005038690122236128062975 : ℝ) / 869769183161367153610622770561335594988148116503599104) * (value_114 h H)

/-- Coordinate 68.2, recovered from nonplanar cycle 15. -/
theorem value_274 (h : Assignment) (H : Constraints h) :
    h 68 2 = ((213187919756061655496661927 : ℝ) / 391126085576720770320901126) * (h 1 0) + ((-5709290239179495222494681169 : ℝ) / 2542319556248685007085857319) * (h 1 1) + ((4791476193002496478955552254 : ℝ) / 2542319556248685007085857319) * (h 1 2) + ((-213187919756061655496661927 : ℝ) / 391126085576720770320901126) * (h 3 0) + ((5709290239179495222494681169 : ℝ) / 2542319556248685007085857319) * (h 5 1) + ((-2249156636753811471869694935 : ℝ) / 2542319556248685007085857319) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-6891386201919943832205 : ℝ) / 14215936949970270914903678301410055431037710374888) * r0 + ((9513805022008255181599634814519463778016068386073 : ℝ) / 911907187163389009652139230805927101665311014413679801945385135459445361664) * r1 + ((6891386201919943832205 : ℝ) / 13685326477433260156455985819672174122170789563328) * r2 + ((-4661482077476839748174309173165944659319357033625 : ℝ) / 877870211254342505200888900671351536263030342238210334948324203981096361984) * r3 + ((504602611896138109491455 : ℝ) / 30975580300163320749293403682477126190071301202508435848) * r4 + ((-4661482077476839748174309173165944659319357033625 : ℝ) / 27136366495047925421052423627266492937817210563618687334472714909642442615174144) * r5 + ((-231612598860327392256577845 : ℝ) / 2542319556248685007085857319) * (value_097 h H) + ((-602712465732737609454320642470915528617649335995 : ℝ) / 559883416676701780779845266310021436772697463744) * (value_096 h H) + ((9513805022008255181599634814519463778016068386073 : ℝ) / 4852322944531415433425325641353519118696711352448) * (value_098 h H) + ((231612598860327392256577845 : ℝ) / 2542319556248685007085857319) * (value_113 h H) + ((602712465732737609454320642470915528617649335995 : ℝ) / 559883416676701780779845266310021436772697463744) * (value_112 h H) + ((-4661482077476839748174309173165944659319357033625 : ℝ) / 4852322944531415433425325641353519118696711352448) * (value_114 h H)

/-- Coordinate 68.3, recovered from nonplanar cycle 15. -/
theorem value_275 (h : Assignment) (H : Constraints h) :
    h 68 3 = ((-55080332269817589302385951 : ℝ) / 195563042788360385160450563) * (h 1 0) + ((551634595776523028599468848 : ℝ) / 2542319556248685007085857319) * (h 1 1) + ((-400840909230863343986102535 : ℝ) / 2542319556248685007085857319) * (h 1 2) + h 1 3 + ((55080332269817589302385951 : ℝ) / 195563042788360385160450563) * (h 3 0) + ((-551634595776523028599468848 : ℝ) / 2542319556248685007085857319) * (h 5 1) + ((400840909230863343986102535 : ℝ) / 2542319556248685007085857319) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 97 3
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 3 - h 24 3) - ((-55341082595537432543614304 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((1389331382664902517441 : ℝ) / 7107968474985135457451839150705027715518855187444) * r0 + ((-1906234635814414731502031907435935465648575825 : ℝ) / 924855159394917859687767982561792192358327600825233064853331780384833024) * r1 + ((1 : ℝ) / 187932088937137115075554968) * r2 + ((-81725375450876618673 : ℝ) / 402509602277448828131058406460946297710905575392) * r3 + ((1906234635814414731502031907435935465648575825 : ℝ) / 890334899852274346045526268429362612842829961702038879257935298155270144) * r4 + ((-101729931241796750999291 : ℝ) / 15487790150081660374646701841238563095035650601254217924) * r5 + ((1906234635814414731502031907435935465648575825 : ℝ) / 27521669873273758033521727816700297097177698340384064233745146967183004680704) * r6 + ((93388076879969417417349138 : ℝ) / 2542319556248685007085857319) * (value_097 h H) + ((4189975011136046097829966434266362855217315731 : ℝ) / 9653162356494858289307677005345197185736163168) * (value_096 h H) + ((-32405988808845050435534542426410902916025789025 : ℝ) / 83660740422955438507333200712991708943046747456) * (value_098 h H) + (1 : ℝ) * (value_099 h H) + ((-93388076879969417417349138 : ℝ) / 2542319556248685007085857319) * (value_113 h H) + ((-4189975011136046097829966434266362855217315731 : ℝ) / 9653162356494858289307677005345197185736163168) * (value_112 h H) + ((32405988808845050435534542426410902916025789025 : ℝ) / 83660740422955438507333200712991708943046747456) * (value_114 h H)

/-- Coordinate 72.0, recovered from nonplanar cycle 15. -/
theorem value_288 (h : Assignment) (H : Constraints h) :
    h 72 0 = ((117623495268038676963969274 : ℝ) / 156035158738957144844598529) * (h 1 0) + ((-10709194217554460098522315188 : ℝ) / 10142285318032214414898904385) * (h 1 1) + ((8299416986506909385423492114 : ℝ) / 10142285318032214414898904385) * (h 1 2) + ((38411663470918467880629255 : ℝ) / 156035158738957144844598529) * (h 3 0) + ((10709194217554460098522315188 : ℝ) / 10142285318032214414898904385) * (h 5 1) + ((-8299416986506909385423492114 : ℝ) / 10142285318032214414898904385) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-4541912989243751698182 : ℝ) / 7089101380635581650263011196688282659059235320315) * r0 + ((40167025183887814339532869887701568814331952193 : ℝ) / 4458267935543443293169707252919769335572309810419150614566252093961332160) * r1 + ((27 : ℝ) / 40569141272128857659595617540) * r2 + ((-8118457840591213861853242457 : ℝ) / 867460504204954902772406354316940215208625346852375040) * r3 + ((110856320737467865522294 : ℝ) / 5148893335807301758810605447365792965709344244681464205) * r4 + ((-40167025183887814339532869887701568814331952193 : ℝ) / 132668317933051923064163599297345806623153564864708889338977748131014632823360) * r5 + ((-1221193229243946006593590704 : ℝ) / 10142285318032214414898904385) * (value_097 h H) + ((-463872253543380163828596694055964593625947984423 : ℝ) / 604930392671713842534091282968945410275585604060) * (value_096 h H) + ((2048518284378278531316176364272780009530929561843 : ℝ) / 1209860785343427685068182565937890820551171208120) * (value_098 h H) + ((1221193229243946006593590704 : ℝ) / 10142285318032214414898904385) * (value_113 h H) + ((1068802646215094006362687977024910003901533588483 : ℝ) / 604930392671713842534091282968945410275585604060) * (value_112 h H) + ((-2048518284378278531316176364272780009530929561843 : ℝ) / 1209860785343427685068182565937890820551171208120) * (value_114 h H)

/-- Coordinate 72.1, recovered from nonplanar cycle 15. -/
theorem value_289 (h : Assignment) (H : Constraints h) :
    h 72 1 = ((64037000728352545155776199 : ℝ) / 1248281269911657158756788232) * (h 1 0) + ((18039024383610170800030847157 : ℝ) / 40569141272128857659595617540) * (h 1 1) + ((-1894604078825100633048058891 : ℝ) / 40569141272128857659595617540) * (h 1 2) + ((-64037000728352545155776199 : ℝ) / 1248281269911657158756788232) * (h 3 0) + ((22530116888518686859564770383 : ℝ) / 40569141272128857659595617540) * (h 5 1) + ((1894604078825100633048058891 : ℝ) / 40569141272128857659595617540) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((5291029487620392184012724037 : ℝ) / 2541414488552333479292688461967962580142099625391646240) * r0 + ((-1590925919576706883212157662350376283016032949392327367 : ℝ) / 54341221541899796392157690625652671342661246445064809836464465763009898957066240) * r1 + ((24696052809267681107557445429 : ℝ) / 7339668242631835169432594679958654715683214846056792320) * r2 + ((1590925919576706883212157662350376283016032949392327367 : ℝ) / 52312933055389159575035921642127570813834012802364812493985439463330159213117440) * r3 + ((-195964055097051562370841631 : ℝ) / 2800997974679172156792969363366991373345883269106716527520) * r4 + ((1590925919576706883212157662350376283016032949392327367 : ℝ) / 1617076084394730995167553385585843597899918053251115051743849670995191541493871063040) * r5 + ((15873088462861176552038172111 : ℝ) / 40569141272128857659595617540) * (value_097 h H) + ((1080761246549379330859226378090605431750980959201692161 : ℝ) / 433730252102477451386203177158470107604312673426187520) * (value_096 h H) + ((-4772777758730120649636472987051128849048098848176982101 : ℝ) / 867460504204954902772406354316940215208625346852375040) * (value_098 h H) + ((24696052809267681107557445429 : ℝ) / 40569141272128857659595617540) * (value_113 h H) + ((-1080761246549379330859226378090605431750980959201692161 : ℝ) / 433730252102477451386203177158470107604312673426187520) * (value_112 h H) + ((4772777758730120649636472987051128849048098848176982101 : ℝ) / 867460504204954902772406354316940215208625346852375040) * (value_114 h H)

/-- Coordinate 72.2, recovered from nonplanar cycle 15. -/
theorem value_290 (h : Assignment) (H : Constraints h) :
    h 72 2 = ((85875961378985222076361338 : ℝ) / 156035158738957144844598529) * (h 1 0) + ((-22960600609335036967202013198 : ℝ) / 10142285318032214414898904385) * (h 1 1) + ((19216447856148906407574853279 : ℝ) / 10142285318032214414898904385) * (h 1 2) + ((-85875961378985222076361338 : ℝ) / 156035158738957144844598529) * (h 3 0) + ((22960600609335036967202013198 : ℝ) / 10142285318032214414898904385) * (h 5 1) + ((-9074162538116691992675948894 : ℝ) / 10142285318032214414898904385) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-3689891620047561287592 : ℝ) / 7089101380635581650263011196688282659059235320315) * r0 + ((416058743801485280314444486468117907813820579077 : ℝ) / 56842916178178901987913767474727059028546950082844170335719714198006985040) * r1 + ((461236452505945160949 : ℝ) / 853062544936790922984797910339150078346203635705) * r2 + ((-113593547465628359047398844983645202676027777047 : ℝ) / 54721251829228038362041614455385385207053230164037547658117635339721530240) * r3 + ((270182064179038098724792 : ℝ) / 15446680007421905276431816342097378897128032734044392615) * r4 + ((-416058743801485280314444486468117907813820579077 : ℝ) / 1691521053646412019068085891041159034445207952025038339071966288670436568497840) * r5 + ((-992108539665427898517436224 : ℝ) / 10142285318032214414898904385) * (value_097 h H) + ((-282640543507080379369776304332055506279811675091 : ℝ) / 453697794503785381900568462226709057706689203045) * (value_096 h H) + ((416058743801485280314444486468117907813820579077 : ℝ) / 302465196335856921267045641484472705137792802030) * (value_098 h H) + ((992108539665427898517436224 : ℝ) / 10142285318032214414898904385) * (value_113 h H) + ((282640543507080379369776304332055506279811675091 : ℝ) / 453697794503785381900568462226709057706689203045) * (value_112 h H) + ((-113593547465628359047398844983645202676027777047 : ℝ) / 302465196335856921267045641484472705137792802030) * (value_114 h H)

/-- Coordinate 72.3, recovered from nonplanar cycle 15. -/
theorem value_291 (h : Assignment) (H : Constraints h) :
    h 72 3 = ((-44385079091353524376344828 : ℝ) / 156035158738957144844598529) * (h 1 0) + ((2298096067182135113927703582 : ℝ) / 10142285318032214414898904385) * (h 1 1) + ((-1652783455024682952663638331 : ℝ) / 10142285318032214414898904385) * (h 1 2) + h 1 3 + ((44385079091353524376344828 : ℝ) / 156035158738957144844598529) * (h 3 0) + ((-2298096067182135113927703582 : ℝ) / 10142285318032214414898904385) * (h 5 1) + ((1652783455024682952663638331 : ℝ) / 10142285318032214414898904385) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 114 3
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 3 - h 28 3) - ((-60535202294100003863055392 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((1519729148015319654243 : ℝ) / 7089101380635581650263011196688282659059235320315) * r0 + ((-2780675460283970526406186086833738354214489023 : ℝ) / 922400262526229646862698052328228138394270995259134609910259053923034240) * r1 + ((-89395832236195273779 : ℝ) / 401441197617313375522257840159600036868801710920) * r2 + ((2780675460283970526406186086833738354214489023 : ℝ) / 887971632117290683359701654448444384698632538158824302768643169812925440) * r3 + ((1 : ℝ) / 180917515443547556532383808) * r4 + ((-111277945393566183571793 : ℝ) / 15446680007421905276431816342097378897128032734044392615) * r5 + ((2780675460283970526406186086833738354214489023 : ℝ) / 27448617503390053047757986061519822059962806523732873656340223751244406791040) * r6 + ((408612615485175026075623896 : ℝ) / 10142285318032214414898904385) * (value_097 h H) + ((32112863380584871689977567353677165378868782553 : ℝ) / 125158012276906312248432679234954222815638400840) * (value_096 h H) + ((-47271482824827498948905163476173552021646313391 : ℝ) / 83438674851270874832288452823302815210425600560) * (value_098 h H) + ((-408612615485175026075623896 : ℝ) / 10142285318032214414898904385) * (value_113 h H) + ((-32112863380584871689977567353677165378868782553 : ℝ) / 125158012276906312248432679234954222815638400840) * (value_112 h H) + ((47271482824827498948905163476173552021646313391 : ℝ) / 83438674851270874832288452823302815210425600560) * (value_114 h H) + (1 : ℝ) * (value_115 h H)

/-- Coordinate 64.0, recovered from nonplanar cycle 16. -/
theorem value_256 (h : Assignment) (H : Constraints h) :
    h 64 0 = ((131972807462839763526612 : ℝ) / 249669427901715076699691) * (h 1 0) + ((291719362271465515182138 : ℝ) / 28711984208697233820464465) * (h 1 1) + ((-255174997716761229511173 : ℝ) / 28711984208697233820464465) * (h 1 2) + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (h 3 0) + ((-291719362271465515182138 : ℝ) / 28711984208697233820464465) * (h 5 1) + ((255174997716761229511173 : ℝ) / 28711984208697233820464465) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((811393683605415051318460 : ℝ) / 663681344105394983865718511197506853970787067503) * r0 + ((89688011097938993820652043 : ℝ) / 22565165699583429451434429380715233035006760295102) * r1 + ((296578554055302553528863329541123685854433970 : ℝ) / 3431567474668219302912368509547622398314593017054094771357523868607441) * r2 + ((65565067081439518617206164583593629485708658077 : ℝ) / 233346588277438912598041058649238323085392325159678444452311623065305988) * r3 + ((2520917709470071704995338301099551329762688745 : ℝ) / 32540860721636536313036856703228127524509756998986286691801739437212112) * r4 + ((65565067081439518617206164583593629485708658077 : ℝ) / 260326885773092290504294853625825020196078055991890293534413915497696896) * r5 + ((927697717084986387438284494804634889352669458160 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_101 h H) + ((131972807462839763526612 : ℝ) / 249669427901715076699691) * (value_100 h H) + ((3015993085746217856391483570845306956342598271542 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_102 h H) + ((-927697717084986387438284494804634889352669458160 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_109 h H) + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (value_108 h H) + ((-3015993085746217856391483570845306956342598271542 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_110 h H)

/-- Coordinate 64.1, recovered from nonplanar cycle 16. -/
theorem value_257 (h : Assignment) (H : Constraints h) :
    h 64 1 = ((-21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (h 1 0) + ((771936032082788798665478471 : ℝ) / 114847936834788935281857860) * (h 1 1) + ((-19542286684597921862853605579 : ℝ) / 3904829852382823799583167240) * (h 1 2) + ((21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (h 3 0) + ((-657088095247999863383620611 : ℝ) / 114847936834788935281857860) * (h 5 1) + ((19542286684597921862853605579 : ℝ) / 3904829852382823799583167240) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((135239652957254471780683139353780237678689081061 : ℝ) / 32991847732722971647818439428183602362673925823292567147016120273813156) * r0 + ((11759229082474685400841380760128618026334711253115 : ℝ) / 1121722822912581036025826940558242480330913477991947282998548089309647304) * r1 + ((611707668477864466772498423484859653159765449225 : ℝ) / 2683485765190547494877472174466240715482011739336302111201583665251018862) * r2 + ((11759229082474685400841380760128618026334711253115 : ℝ) / 15867568002865846056666791988148205969806678110858134222757190368440807184) * r3 + ((611707668477864466772498423484859653159765449225 : ℝ) / 2993759186390561340799390816696987732254897643906738375645760028223514304) * r4 + ((11759229082474685400841380760128618026334711253115 : ℝ) / 17702228232570275754292050046556101373333307807448539960340146253843388928) * r5 + ((3110512018016852850955712205136945466609848864403 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_101 h H) + ((-21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (value_100 h H) + ((270462268896917764219351757482958214605698358821645 : ℝ) / 22565165699583429451434429380715233035006760295102) * (value_102 h H) + ((-2446830673911457867089993693939438612639061796900 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_109 h H) + ((21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (value_108 h H) + ((-270462268896917764219351757482958214605698358821645 : ℝ) / 22565165699583429451434429380715233035006760295102) * (value_110 h H)

/-- Coordinate 64.2, recovered from nonplanar cycle 16. -/
theorem value_258 (h : Assignment) (H : Constraints h) :
    h 64 2 = ((109175811564558021538052 : ℝ) / 249669427901715076699691) * (h 1 0) + ((-10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (h 1 1) + ((9018608418867289852888476 : ℝ) / 5742396841739446764092893) * (h 1 2) + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (h 3 0) + ((10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (h 5 1) + ((-3276211577127843088795583 : ℝ) / 5742396841739446764092893) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-550214682645822390832576088684993773662484720 : ℝ) / 485174231363573112467918226885052975921675379754302458044354709909017) * r0 + ((-125527339409406617420150417336595241008044055529 : ℝ) / 44636029285448726347048476873424873784794134937395826140080633311629564) * r1 + ((-275107341322911195416288044342496886831242360 : ℝ) / 3431567474668219302912368509547622398314593017054094771357523868607441) * r2 + ((-15204598446007105869610193510432749734280087019 : ℝ) / 58336647069359728149510264662309580771348081289919611113077905766326497) * r3 + ((-584603100311186290259612094227805884516390015 : ℝ) / 8135215180409134078259214175807031881127439249746571672950434859303028) * r4 + ((-15204598446007105869610193510432749734280087019 : ℝ) / 65081721443273072626073713406456255049019513997972573383603478874424224) * r5 + ((-860535763658066219262149002703330262008126102080 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_101 h H) + ((109175811564558021538052 : ℝ) / 249669427901715076699691) * (value_100 h H) + ((-2133964769959912496142557094722119097136748943993 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_102 h H) + ((860535763658066219262149002703330262008126102080 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_109 h H) + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (value_108 h H) + ((2797646114065307480008275605919625951107536011496 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_110 h H)

/-- Coordinate 64.3, recovered from nonplanar cycle 16. -/
theorem value_259 (h : Assignment) (H : Constraints h) :
    h 64 3 = ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (h 1 0) + ((42085322381761110668898 : ℝ) / 428537077741749758514395) * (h 1 1) + ((-36813195939601494408633 : ℝ) / 428537077741749758514395) * (h 1 2) + h 1 3 + ((928717562452291111080 : ℝ) / 3726409371667389204473) * (h 3 0) + ((-42085322381761110668898 : ℝ) / 428537077741749758514395) * (h 5 1) + ((36813195939601494408633 : ℝ) / 428537077741749758514395) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 101 3
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 3 - h 25 3) - ((604462459218948328868640 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((35883598287009837482846295745709594872120800 : ℝ) / 55517449360010853665483180190826957443773799673377893209055514069191) * r0 + ((5072149010356347324070833567073385262364020 : ℝ) / 2413802146087428420238399138731606845381469551016430139524152785617) * r1 + ((1 : ℝ) / 1143338598549074470824196) * r2 + ((17941799143504918741423147872854797436060400 : ℝ) / 392666924962035044611863063281568732145450942249971043488671885462543) * r3 + ((2536074505178173662035416783536692631182010 : ℝ) / 17072474998349349765733176664416031832410910532607436673420516759241) * r4 + ((19063161589973976162762094614908222275814175 : ℝ) / 465447634700025084079507278715327694691370902348684448949900501900422) * r5 + ((21556633294014476127301042660061887365047085 : ℝ) / 161894829460878290114611227379244415544824661686498938765182783269712) * r6 + ((2440084683516668948833548110708252451304214400 : ℝ) / 3301897234355198924705067219888093800849686903) * (value_101 h H) + ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (value_100 h H) + ((7932841052197327214846783698902774550337327280 : ℝ) / 3301897234355198924705067219888093800849686903) * (value_102 h H) + (1 : ℝ) * (value_103 h H) + ((-2440084683516668948833548110708252451304214400 : ℝ) / 3301897234355198924705067219888093800849686903) * (value_109 h H) + ((928717562452291111080 : ℝ) / 3726409371667389204473) * (value_108 h H) + ((-7932841052197327214846783698902774550337327280 : ℝ) / 3301897234355198924705067219888093800849686903) * (value_110 h H)

/-- Coordinate 65.0, recovered from nonplanar cycle 16. -/
theorem value_260 (h : Assignment) (H : Constraints h) :
    h 65 0 = ((20682018593087191246588 : ℝ) / 41708273765268360426865) * (h 1 0) + ((941473835656930474758414 : ℝ) / 4796451483005861449089475) * (h 1 1) + ((-823533213543044848835519 : ℝ) / 4796451483005861449089475) * (h 1 2) + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (h 3 0) + ((-941473835656930474758414 : ℝ) / 4796451483005861449089475) * (h 5 1) + ((823533213543044848835519 : ℝ) / 4796451483005861449089475) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-2009949414449318445175543102150514863228724 : ℝ) / 1110277952338059257536807956365218747323331043121299051047043178435) * r0 + ((-176661765318222086994574475637740347559906929 : ℝ) / 37749450379494014756251470516417437408993255466124167735599468066790) * r1 + ((-14188780132307047460758 : ℝ) / 110870615699676288638897051091202587665906802045) * r2 + ((-2494206996321085668079111 : ℝ) / 7539201867577987627444999474201775961281662539060) * r3 + ((-8542285011409603391996058184139688168722077 : ℝ) / 74466857210853079683293035920367470585175353818217648967161699986160) * r4 + ((-176661765318222086994574475637740347559906929 : ℝ) / 595734857686824637466344287362939764681402830545741191737293599889280) * r5 + ((-3143560884198734048254549411763405246089724336 : ℝ) / 1518775557529812173135576042345240926930230165) * (value_101 h H) + ((20682018593087191246588 : ℝ) / 41708273765268360426865) * (value_100 h H) + ((-8126441204638216001750425879336055987755718734 : ℝ) / 1518775557529812173135576042345240926930230165) * (value_102 h H) + ((3143560884198734048254549411763405246089724336 : ℝ) / 1518775557529812173135576042345240926930230165) * (value_109 h H) + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (value_108 h H) + ((8126441204638216001750425879336055987755718734 : ℝ) / 1518775557529812173135576042345240926930230165) * (value_110 h H)

/-- Coordinate 65.1, recovered from nonplanar cycle 16. -/
theorem value_261 (h : Assignment) (H : Constraints h) :
    h 65 1 = ((-1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (h 1 0) + ((64228273569540695124725957 : ℝ) / 9592902966011722898178950) * (h 1 1) + ((-1624896392393843136959898023 : ℝ) / 326158700844398578538084300) * (h 1 2) + ((1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (h 3 0) + ((-54635370603528972226547007 : ℝ) / 9592902966011722898178950) * (h 5 1) + ((1624896392393843136959898023 : ℝ) / 326158700844398578538084300) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((12462758961004109873627929604877056113958672713 : ℝ) / 2755709877703063077206357347698472930856507649027064244698761168875670) * r0 + ((4381588875737337762768014261262728951560368492317 : ℝ) / 374776543367616578500064599286992318596485040267680737279031518967091120) * r1 + ((462416296506512765547987710733141993576192142753 : ℝ) / 1793148001826284588570722594496409829339720176553628712597776500379863720) * r2 + ((4381588875737337762768014261262728951560368492317 : ℝ) / 5301481048877710957513440714163298625873955304593337063332556609818727520) * r3 + ((12462758961004109873627929604877056113958672713 : ℝ) / 43488644611138198535043132977494602821742406629839106996822432791917440) * r4 + ((4381588875737337762768014261262728951560368492317 : ℝ) / 5914455667114795000765866084939265983756967301658118551567850859700771840) * r5 + ((573286912206189054186884761824344581242098944798 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_101 h H) + ((-1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (value_100 h H) + ((100776544141958768543664328009042765885888475323291 : ℝ) / 7539201867577987627444999474201775961281662539060) * (value_102 h H) + ((-462416296506512765547987710733141993576192142753 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_109 h H) + ((1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (value_108 h H) + ((-100776544141958768543664328009042765885888475323291 : ℝ) / 7539201867577987627444999474201775961281662539060) * (value_110 h H)

/-- Coordinate 65.2, recovered from nonplanar cycle 16. -/
theorem value_262 (h : Assignment) (H : Constraints h) :
    h 65 2 = ((414876610754063195580374 : ℝ) / 959290296601172289817895) * (h 1 0) + ((-195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (h 1 1) + ((170624048649954562499929323 : ℝ) / 110318384109134813329057925) * (h 1 2) + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (h 3 0) + ((195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (h 5 1) + ((-60305664540819749170871398 : ℝ) / 110318384109134813329057925) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-2943296506013068108791580540081692482399981746 : ℝ) / 1864156681975601493404300558737202276755872821400661106707985496592365) * r0 + ((-517394072576382095788525389758503863472695483757 : ℝ) / 126762654374340901551492437994129754819399351855244955256143013768280820) * r1 + ((-1471648253006534054395790270040846241199990873 : ℝ) / 13184911778134445504196489665414778156909707180541387592630709561616645) * r2 + ((-314132344138029192213711220424853225569301142901 : ℝ) / 896574000913142294285361297248204914669860088276814356298888250189931860) * r3 + ((-25018020301111078924728434590694386100399844841 : ℝ) / 250059706514044641576498014620593966225018838121574865231728988553525280) * r4 + ((-517394072576382095788525389758503863472695483757 : ℝ) / 2000477652112357132611984116964751729800150704972598921853831908428202240) * r5 + ((-200144162408888631397827476725555088803198758728 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_101 h H) + ((414876610754063195580374 : ℝ) / 959290296601172289817895) * (value_100 h H) + ((-517394072576382095788525389758503863472695483757 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_102 h H) + ((200144162408888631397827476725555088803198758728 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_109 h H) + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (value_108 h H) + ((628264688276058384427422440849706451138602285802 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_110 h H)

/-- Coordinate 65.3, recovered from nonplanar cycle 16. -/
theorem value_263 (h : Assignment) (H : Constraints h) :
    h 65 3 = ((-236618073705471893872696 : ℝ) / 959290296601172289817895) * (h 1 0) + ((9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (h 1 1) + ((-8067963623346575635148407 : ℝ) / 110318384109134813329057925) * (h 1 2) + h 1 3 + ((236618073705471893872696 : ℝ) / 959290296601172289817895) * (h 3 0) + ((-9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (h 5 1) + ((8067963623346575635148407 : ℝ) / 110318384109134813329057925) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 109 3
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 3 - h 27 3) - ((8045014505986044391671664 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((1678660911568482103083017987529810282853831784 : ℝ) / 1864156681975601493404300558737202276755872821400661106707985496592365) * r0 + ((4339518050677987598926188730216685949390373921 : ℝ) / 1864156681975601493404300558737202276755872821400661106707985496592365) * r1 + ((839330455784241051541508993764905141426915892 : ℝ) / 13184911778134445504196489665414778156909707180541387592630709561616645) * r2 + ((4339518050677987598926188730216685949390373921 : ℝ) / 26369823556268891008392979330829556313819414361082775185261419123233290) * r3 + ((-1 : ℝ) / 16173338539794183554831816) * r4 + ((3567154437083024469051413223500846851064392541 : ℝ) / 62514926628511160394124503655148491556254709530393716307932247138381320) * r5 + ((73771806861525789181745208413683661139636356657 : ℝ) / 500119413028089283152996029241187932450037676243149730463457977107050560) * r6 + ((114148941986656783009645223152027099234060561312 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_101 h H) + ((-236618073705471893872696 : ℝ) / 959290296601172289817895) * (value_100 h H) + ((295087227446103156726980833654734644558545426628 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_102 h H) + ((-114148941986656783009645223152027099234060561312 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_109 h H) + ((236618073705471893872696 : ℝ) / 959290296601172289817895) * (value_108 h H) + ((-295087227446103156726980833654734644558545426628 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_110 h H) + (1 : ℝ) * (value_111 h H)

/-- Coordinate 50.0, recovered from nonplanar cycle 17. -/
theorem value_200 (h : Assignment) (H : Constraints h) :
    h 50 0 = ((7175518310899585132906597738 : ℝ) / 16734030054361447590207050033) * (h 1 0) + ((266286651705594267031295217288 : ℝ) / 518754931685204875296418551023) * (h 1 1) + ((-216546615514887264628724421488 : ℝ) / 518754931685204875296418551023) * (h 1 2) + ((9558511743461862457300452295 : ℝ) / 16734030054361447590207050033) * (h 3 0) + ((-266286651705594267031295217288 : ℝ) / 518754931685204875296418551023) * (h 5 1) + ((216546615514887264628724421488 : ℝ) / 518754931685204875296418551023) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-9 : ℝ) / 5706304248537253628260604061253) * r0 + ((1517548617611374584103080195167 : ℝ) / 50013172194531148819181143632993842031167110060714588972632) * r1 + ((9374640217059899270565 : ℝ) / 3244475380485319989683134790833635986269870013102774) * r2 + ((-1580719144667027412002914435713724664411022348706595 : ℝ) / 28436357196818668320314669527705604645769614658021618950262679077100036494367056) * r3 + ((15300454460932540042814365 : ℝ) / 133212909051698342703971478945377750877275312585922626826198) * r4 + ((-1580719144667027412002914435713724664411022348706595 : ℝ) / 715362332906282584242466264286318290404543945012678844466481124325816585576585176272) * r5 + ((18727756260181429012404782760 : ℝ) / 518754931685204875296418551023) * (value_105 h H) + ((50784208957724455858551476381938255773094952373497 : ℝ) / 105857617979967744660470947144137203190376950330342) * (value_104 h H) + ((-1580719144667027412002914435713724664411022348706595 : ℝ) / 2275938786569306510200125363598949868593104432102353) * (value_106 h H) + ((-18727756260181429012404782760 : ℝ) / 518754931685204875296418551023) * (value_121 h H) + ((55073409022243288801919470762198947417281997956845 : ℝ) / 105857617979967744660470947144137203190376950330342) * (value_120 h H) + ((1580719144667027412002914435713724664411022348706595 : ℝ) / 2275938786569306510200125363598949868593104432102353) * (value_122 h H)

/-- Coordinate 50.1, recovered from nonplanar cycle 17. -/
theorem value_201 (h : Assignment) (H : Constraints h) :
    h 50 1 = ((667303820618086860916687133 : ℝ) / 133872240434891580721656400264) * (h 1 0) + ((2505851061725781184189277630845 : ℝ) / 4150039453481639002371348408184) * (h 1 1) + ((-1119638926192710425104328795061 : ℝ) / 8300078906963278004742696816368) * (h 1 2) + ((-667303820618086860916687133 : ℝ) / 133872240434891580721656400264) * (h 3 0) + ((1644188391755857818182070777339 : ℝ) / 4150039453481639002371348408184) * (h 5 1) + ((1119638926192710425104328795061 : ℝ) / 8300078906963278004742696816368) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-1282777513222044696730396421777 : ℝ) / 65307168124637655714763570906091129438313348134188287910060) * r0 + ((-176527394083388202929762878568836410235629937618932179431879 : ℝ) / 381591832786455092797068495790095095909038669994034267460829291755233922765115074061760) * r1 + ((-3140749222093164234799811217699 : ℝ) / 71296515900467502531369528146062697387467908451210104339856) * r2 + ((176527394083388202929762878568836410235629937618932179431879 : ℝ) / 208293889897549283586608287438643856485332655029557540965857035157809854784791165877888) * r3 + ((-116324045262709786474067082137 : ℝ) / 66428837313780240228380444167428371770801289209513416577330736) * r4 + ((176527394083388202929762878568836410235629937618932179431879 : ℝ) / 5239968044286111926795543362109395711385836542801231453788913095963997352999850547590691456) * r5 + ((2565555026444089393460792843554 : ℝ) / 5706304248537253628260604061253) * (value_105 h H) + ((559122116882098227437080796108418848029603117461565508539 : ℝ) / 70490728956351161126400484331210489120742931727575178256) * (value_104 h H) + ((176527394083388202929762878568836410235629937618932179431879 : ℝ) / 16671057398177049606393714544331280677055703353571529657544) * (value_106 h H) + ((3140749222093164234799811217699 : ℝ) / 5706304248537253628260604061253) * (value_121 h H) + ((-559122116882098227437080796108418848029603117461565508539 : ℝ) / 70490728956351161126400484331210489120742931727575178256) * (value_120 h H) + ((-176527394083388202929762878568836410235629937618932179431879 : ℝ) / 16671057398177049606393714544331280677055703353571529657544) * (value_122 h H)

/-- Coordinate 50.2, recovered from nonplanar cycle 17. -/
theorem value_202 (h : Assignment) (H : Constraints h) :
    h 50 2 = ((7559445924796185584949116101 : ℝ) / 16734030054361447590207050033) * (h 1 0) + ((-970664285983757617368809643177 : ℝ) / 518754931685204875296418551023) * (h 1 1) + ((1694800603370947737245720625373 : ℝ) / 1037509863370409750592837102046) * (h 1 2) + ((-7559445924796185584949116101 : ℝ) / 16734030054361447590207050033) * (h 3 0) + ((970664285983757617368809643177 : ℝ) / 518754931685204875296418551023) * (h 5 1) + ((-657290740000537986652883523327 : ℝ) / 1037509863370409750592837102046) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((20982234148533411580719 : ℝ) / 130764453842286256051474234233081836825302143128688310) * r0 + ((-73335984217544876883774097251033356309453036943373 : ℝ) / 1567840234021440852664118993242115118781691080378198662327673475943408708019440) * r1 + ((-20982234148533411580719 : ℝ) / 71378458370677039773028965398339991697937140288261028) * r2 + ((82277933918617715758979234682057822166555174403579 : ℝ) / 14548833914651411698765644874640076795510035406429665509436719527818623322699424) * r3 + ((-796403197436194528964293 : ℝ) / 68155441840403803243892384576704895797675741323030181166892) * r4 + ((82277933918617715758979234682057822166555174403579 : ℝ) / 365999333114842252403122274751139590439534111401835687866571738027161974015927299488) * r5 + ((-20958146543730895224224334588 : ℝ) / 5706304248537253628260604061253) * (value_105 h H) + ((11205891025796635388527829095130794675072495324277 : ℝ) / 211715235959935489320941894288274406380753900660684) * (value_104 h H) + ((1246711731698262907024159653267567057260701628037341 : ℝ) / 1164433797779645191265180418585509235094146453633762) * (value_106 h H) + ((20958146543730895224224334588 : ℝ) / 5706304248537253628260604061253) * (value_121 h H) + ((-11205891025796635388527829095130794675072495324277 : ℝ) / 211715235959935489320941894288274406380753900660684) * (value_120 h H) + ((-82277933918617715758979234682057822166555174403579 : ℝ) / 1164433797779645191265180418585509235094146453633762) * (value_122 h H)

/-- Coordinate 50.3, recovered from nonplanar cycle 17. -/
theorem value_203 (h : Assignment) (H : Constraints h) :
    h 50 3 = ((-3927477000029399601288710976 : ℝ) / 16734030054361447590207050033) * (h 1 0) + ((14335061367662622798576402618 : ℝ) / 518754931685204875296418551023) * (h 1 1) + ((-15600554891686645608115909725 : ℝ) / 518754931685204875296418551023) * (h 1 2) + h 1 3 + ((3927477000029399601288710976 : ℝ) / 16734030054361447590207050033) * (h 3 0) + ((-14335061367662622798576402618 : ℝ) / 518754931685204875296418551023) * (h 5 1) + ((15600554891686645608115909725 : ℝ) / 518754931685204875296418551023) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 105 3
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 3 - h 26 3) - ((4277405041606171325713171728 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((19270445158269464310738 : ℝ) / 65382226921143128025737117116540918412651071564344155) * r0 + ((-31856032037786091581927580936923396588365374916997 : ℝ) / 5618094171910163055379759725784245842301059704688545206674163288797214537069660) * r1 + ((-1 : ℝ) / 22889479873555079904050290040) * r2 + ((-9635222579134732155369 : ℝ) / 17844614592669259943257241349584997924484285072065257) * r3 + ((31856032037786091581927580936923396588365374916997 : ℝ) / 3066665972205934818857464360830996579445742757237625573067543822040200014098408) * r4 + ((-5241917943144817801119083 : ℝ) / 244223666594780294957281044733192543275004739740858149181363) * r5 + ((31856032037786091581927580936923396588365374916997 : ℝ) / 77146918254599102222226753991661776416176307795484973422855807525333161189631734696) * r6 + ((-38496645374455541931418545552 : ℝ) / 5706304248537253628260604061253) * (value_105 h H) + ((1715280547450279317509112058514906295014834943409 : ℝ) / 17642936329994624110078491190689533865062825055057) * (value_104 h H) + ((1083105089284727113785537751855395484004422747177898 : ℝ) / 8345108884087457204067126333196149518174716251041961) * (value_106 h H) + (1 : ℝ) * (value_107 h H) + ((38496645374455541931418545552 : ℝ) / 5706304248537253628260604061253) * (value_121 h H) + ((-1715280547450279317509112058514906295014834943409 : ℝ) / 17642936329994624110078491190689533865062825055057) * (value_120 h H) + ((-1083105089284727113785537751855395484004422747177898 : ℝ) / 8345108884087457204067126333196149518174716251041961) * (value_122 h H)

/-- Coordinate 54.0, recovered from nonplanar cycle 17. -/
theorem value_216 (h : Assignment) (H : Constraints h) :
    h 54 0 = ((61892404734917835710766598981 : ℝ) / 144175784701405287264620066096) * (h 1 0) + ((73776641543489070940041714339 : ℝ) / 144175784701405287264620066096) * (h 1 1) + ((-120126910384208960708621950915 : ℝ) / 288351569402810574529240132192) * (h 1 2) + ((82283379966487451553853467115 : ℝ) / 144175784701405287264620066096) * (h 3 0) + ((-73776641543489070940041714339 : ℝ) / 144175784701405287264620066096) * (h 5 1) + ((120126910384208960708621950915 : ℝ) / 288351569402810574529240132192) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-232599827334136148901 : ℝ) / 150177345509773707416010650654038312102556943029360) * r0 + ((16031952052697942114350543439143839153562329484831 : ℝ) / 188033773413807612055551011496496721678013456805291779770230803552585737013120) * r1 + ((9 : ℝ) / 3171867263430916319821641454112) * r2 + ((-4342277425120606374804115512653 : ℝ) / 27799979937072410827970810639586916212136448514769669340928) * r3 + ((4175916388980264978141631 : ℝ) / 37023408399209845576155098142071340424354213851888696777696) * r4 + ((-176351472579677363257855977830582230689185624333141 : ℝ) / 28402601083312472258539969612409683856371284358727865456004595002898763206792347392) * r5 + ((638915207513980541655669543 : ℝ) / 18021973087675660908077508262) * (value_105 h H) + ((1437215905628960793266328964637293386289813708427 : ℝ) / 4202949410125846342330504727731107345684136314912) * (value_104 h H) + ((-176351472579677363257855977830582230689185624333141 : ℝ) / 90363412317705696360105851646218807932208930770608) * (value_106 h H) + ((-638915207513980541655669543 : ℝ) / 18021973087675660908077508262) * (value_121 h H) + ((2765733504496885549064175763093813959394322606485 : ℝ) / 4202949410125846342330504727731107345684136314912) * (value_120 h H) + ((176351472579677363257855977830582230689185624333141 : ℝ) / 90363412317705696360105851646218807932208930770608) * (value_122 h H)

/-- Coordinate 54.1, recovered from nonplanar cycle 17. -/
theorem value_217 (h : Assignment) (H : Constraints h) :
    h 54 1 = ((42166173460266371485150710067 : ℝ) / 2306812555222484596233921057536) * (h 1 0) + ((1291636951393455771186204299781 : ℝ) / 2306812555222484596233921057536) * (h 1 1) + ((-516858231467655607560504108645 : ℝ) / 4613625110444969192467842115072) * (h 1 2) + ((-42166173460266371485150710067 : ℝ) / 2306812555222484596233921057536) * (h 3 0) + ((1015175603829028825047716757755 : ℝ) / 2306812555222484596233921057536) * (h 5 1) + ((516858231467655607560504108645 : ℝ) / 4613625110444969192467842115072) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-1369771478981662774644264840507 : ℝ) / 72602391887890187804750182086710338442207392506840950644480) * r0 + ((220293621139116275099655691756821976044580630501799614275373 : ℝ) / 212109027084951321462165092504264047593297935281702361562100304087761254924284680919040) * r1 + ((-106005634379367855598669212565 : ℝ) / 2331199638069481864864098287886009750841025799896907254272) * r2 + ((-220293621139116275099655691756821976044580630501799614275373 : ℝ) / 115780817454323120548958573347774633292063643681547587716992334754520173048787616305152) * r3 + ((50732276999320843505343142241 : ℝ) / 36924679310145285987952017880359150183222602614950326919622144) * r4 + ((-220293621139116275099655691756821976044580630501799614275373 : ℝ) / 2912652809452933166146415681335582787368561466093162042290006444057771370467444177125249024) * r5 + ((1369771478981662774644264840507 : ℝ) / 3171867263430916319821641454112) * (value_105 h H) + ((163212027960856735574917150558898029156774064200447177721 : ℝ) / 39182494625894870793475420210834272321545381979943156224) * (value_104 h H) + ((-220293621139116275099655691756821976044580630501799614275373 : ℝ) / 9266659979024136942656936879862305404045482838256556446976) * (value_106 h H) + ((1802095784449253545177376613605 : ℝ) / 3171867263430916319821641454112) * (value_121 h H) + ((-163212027960856735574917150558898029156774064200447177721 : ℝ) / 39182494625894870793475420210834272321545381979943156224) * (value_120 h H) + ((220293621139116275099655691756821976044580630501799614275373 : ℝ) / 9266659979024136942656936879862305404045482838256556446976) * (value_122 h H)

/-- Coordinate 54.2, recovered from nonplanar cycle 17. -/
theorem value_218 (h : Assignment) (H : Constraints h) :
    h 54 2 = ((65177204861032671336070632337 : ℝ) / 144175784701405287264620066096) * (h 1 0) + ((-269928922810662604454177689353 : ℝ) / 144175784701405287264620066096) * (h 1 1) + ((471192179276402318567845397545 : ℝ) / 288351569402810574529240132192) * (h 1 2) + ((-65177204861032671336070632337 : ℝ) / 144175784701405287264620066096) * (h 3 0) + ((269928922810662604454177689353 : ℝ) / 144175784701405287264620066096) * (h 5 1) + ((-182840609873591744038605265353 : ℝ) / 288351569402810574529240132192) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((3262064912803509072687 : ℝ) / 18171458806682618597337288729138635764409390106552560) * r0 + ((-5228789527554336187013797930739844573045051179479 : ℝ) / 529118292629551652528410985838979147047433215661402450051114586740997073920640) * r1 + ((-466009273257644153241 : ℝ) / 1416997922442864111667682746008924165095009020292704) * r2 + ((-17887432228137818695803978071781245828217698552537 : ℝ) / 288821976568443897220982877748409243476120994746356494291141416611685929023232) * r3 + ((-123815171845402441262789 : ℝ) / 9471104474216472124132699524715924294602240752808736384992) * r4 + ((5228789527554336187013797930739844573045051179479 : ℝ) / 7265781672475283601021852691546663312094979719674570232931408023997358029644553984) * r5 + ((-814580015570902661067888831 : ℝ) / 198241703964432269988852590882) * (value_105 h H) + ((-166578848451764286967595738859096050709222140969 : ℝ) / 4202949410125846342330504727731107345684136314912) * (value_104 h H) + ((5228789527554336187013797930739844573045051179479 : ℝ) / 23116221755692154882817776002521090401262749732016) * (value_106 h H) + ((814580015570902661067888831 : ℝ) / 198241703964432269988852590882) * (value_121 h H) + ((166578848451764286967595738859096050709222140969 : ℝ) / 4202949410125846342330504727731107345684136314912) * (value_120 h H) + ((17887432228137818695803978071781245828217698552537 : ℝ) / 23116221755692154882817776002521090401262749732016) * (value_122 h H)

/-- Coordinate 54.3, recovered from nonplanar cycle 17. -/
theorem value_219 (h : Assignment) (H : Constraints h) :
    h 54 3 = ((-8461058739252797992854231153 : ℝ) / 36043946175351321816155016524) * (h 1 0) + ((1001121979882274265817398609 : ℝ) / 36043946175351321816155016524) * (h 1 1) + ((-2173216697008202992100235825 : ℝ) / 72087892350702643632310033048) * (h 1 2) + h 1 3 + ((8461058739252797992854231153 : ℝ) / 36043946175351321816155016524) * (h 3 0) + ((-1001121979882274265817398609 : ℝ) / 36043946175351321816155016524) * (h 5 1) + ((2173216697008202992100235825 : ℝ) / 72087892350702643632310033048) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 120 3
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 3 - h 30 3) - ((2357449182116273216713998912 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((1327589237384921574369 : ℝ) / 4542864701670654649334322182284658941102347526638140) * r0 + ((-12559391667384807653437740857072762424557577995623 : ℝ) / 780708853340661997112998562438885898339595087814128124830321032397255486520160) * r1 + ((-1327589237384921574369 : ℝ) / 2479746364275012195418444805515617288916265785512232) * r2 + ((12559391667384807653437740857072762424557577995623 : ℝ) / 426153994838733397370175716677799913168198134405163258733497874510379728607808) * r3 + ((-1 : ℝ) / 12494341835828952814599759952) * r4 + ((-722257715109152333552083 : ℝ) / 33938124365942358444808839963565395388991362697564638712888) * r5 + ((12559391667384807653437740857072762424557577995623 : ℝ) / 10720589624583629234841066961546792435983278900108066863295852035407866504524562496) * r6 + ((-663032582470201842200812194 : ℝ) / 99120851982216134994426295441) * (value_105 h H) + ((-158185898200834842079722795151971029726943328507 : ℝ) / 2451720489240077033026127757843145951649079517032) * (value_104 h H) + ((213509658345541730108441594570236961217478825925591 : ℝ) / 579831895705278218310679214729904017565007305778068) * (value_106 h H) + ((663032582470201842200812194 : ℝ) / 99120851982216134994426295441) * (value_121 h H) + ((158185898200834842079722795151971029726943328507 : ℝ) / 2451720489240077033026127757843145951649079517032) * (value_120 h H) + ((-213509658345541730108441594570236961217478825925591 : ℝ) / 579831895705278218310679214729904017565007305778068) * (value_122 h H) + (1 : ℝ) * (value_123 h H)

/-- Coordinate 70.0, recovered from nonplanar cycle 18. -/
theorem value_280 (h : Assignment) (H : Constraints h) :
    h 70 0 = ((2792769390001120810127813548 : ℝ) / 6204441341809179666130037393) * (h 1 0) + ((35724170004512650198172474382 : ℝ) / 80657737443519335659690486109) * (h 1 1) + ((-30710762120847743456314792043 : ℝ) / 80657737443519335659690486109) * (h 1 2) + ((3411671951808058856002223845 : ℝ) / 6204441341809179666130037393) * (h 3 0) + ((-35724170004512650198172474382 : ℝ) / 80657737443519335659690486109) * (h 5 1) + ((30710762120847743456314792043 : ℝ) / 80657737443519335659690486109) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-108 : ℝ) / 887235111878712692256595347199) * r0 + ((-98207707482786162666627588359 : ℝ) / 165320849290022395890310601028648326097823259716057693170) * r1 + ((-615936094244448687162 : ℝ) / 173256020829145698777409744428212803701084599579) * r2 + ((-1120179106882381970990518927857763347969031554577 : ℝ) / 64566499058932026464947888965153318851347007442544719118979738161072657140) * r3 + ((167546023858457532698567 : ℝ) / 1815083188973145165763269636249208054296535712931590525706) * r4 + ((160025586697483138712931275408251906852718793511 : ℝ) / 355237599186509864734980813519763567630060940303274759952318783494875148300052080) * r5 + ((615228999608256060069138024 : ℝ) / 80657737443519335659690486109) * (value_105 h H) + ((1305993054546028114482003644609955014672541255479 : ℝ) / 1543224762260383973391762377509131775565745837210) * (value_104 h H) + ((1120179106882381970990518927857763347969031554577 : ℝ) / 30092882864077487481139366361428069623532043825595) * (value_106 h H) + ((-615228999608256060069138024 : ℝ) / 80657737443519335659690486109) * (value_121 h H) + ((237231707714355858909758732899176760893204581731 : ℝ) / 1543224762260383973391762377509131775565745837210) * (value_120 h H) + ((-1120179106882381970990518927857763347969031554577 : ℝ) / 30092882864077487481139366361428069623532043825595) * (value_122 h H)

/-- Coordinate 70.1, recovered from nonplanar cycle 18. -/
theorem value_281 (h : Assignment) (H : Constraints h) :
    h 70 1 = ((-1033537310793131602881987641 : ℝ) / 24817765367236718664520149572) * (h 1 0) + ((244477053615011092885956197129 : ℝ) / 322630949774077342638761944436) * (h 1 1) + ((-138794665687244804416753760493 : ℝ) / 645261899548154685277523888872) * (h 1 2) + ((1033537310793131602881987641 : ℝ) / 24817765367236718664520149572) * (h 3 0) + ((78153896159066249752805747307 : ℝ) / 322630949774077342638761944436) * (h 5 1) + ((138794665687244804416753760493 : ℝ) / 645261899548154685277523888872) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-454138090761673090274427569275 : ℝ) / 55596115493361621095292921855629684824058385845761673542) * r0 + ((393828384828965618762076641804617040396907681559203699877 : ℝ) / 10359370258833011344664010158059626359729595295794741498348506738621125388273083860) * r1 + ((108274255279259900495541944481 : ℝ) / 475907088022393058666836514614425342356698324761379097) * r2 + ((393828384828965618762076641804617040396907681559203699877 : ℝ) / 354708071949068048742113708337417275627181135929003727797871321819150601512818040) * r3 + ((-4010157602935551870205257203 : ℝ) / 678841112675956291995462843957203812306904356636414856614044) * r4 + ((-56261197832709374108868091686373862913843954508457671411 : ℝ) / 1951563825324540632756457805502135834799318966890936302903414368422826673963919911166880) * r5 + ((454138090761673090274427569275 : ℝ) / 887235111878712692256595347199) * (value_105 h H) + ((83405037377805661034005518349144588093441252798931217631 : ℝ) / 8477992271283199789246697488648632107580679985438856060) * (value_104 h H) + ((-393828384828965618762076641804617040396907681559203699877 : ℝ) / 165320849290022395890310601028648326097823259716057693170) * (value_106 h H) + ((433097021117039601982167777924 : ℝ) / 887235111878712692256595347199) * (value_121 h H) + ((-83405037377805661034005518349144588093441252798931217631 : ℝ) / 8477992271283199789246697488648632107580679985438856060) * (value_120 h H) + ((393828384828965618762076641804617040396907681559203699877 : ℝ) / 165320849290022395890310601028648326097823259716057693170) * (value_122 h H)

/-- Coordinate 70.2, recovered from nonplanar cycle 18. -/
theorem value_282 (h : Assignment) (H : Constraints h) :
    h 70 2 = ((3126756156422237613951041596 : ℝ) / 6204441341809179666130037393) * (h 1 0) + ((-164826048525223839798807150750 : ℝ) / 80657737443519335659690486109) * (h 1 1) + ((139000283339831846805438863309 : ℝ) / 80657737443519335659690486109) * (h 1 2) + ((-3126756156422237613951041596 : ℝ) / 6204441341809179666130037393) * (h 3 0) + ((164826048525223839798807150750 : ℝ) / 80657737443519335659690486109) * (h 5 1) + ((-58342545896312511145748377200 : ℝ) / 80657737443519335659690486109) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((130370401105101752457006 : ℝ) / 111320026377004042831756700403322383744655636362067) * r0 + ((-141647942138152594705359580999092964383120712661813 : ℝ) / 13828368645649220431273782513071174187606833038721440878593300760768195739740) * r1 + ((65185200552550876228503 : ℝ) / 1905816229120602686551507188710340840711930595369) * r2 + ((79033198865082313489662438984712879522780942059217 : ℝ) / 473487659765501527409617852411124338243211387911994606872518079847866152360) * r3 + ((-11821054455758269394080007 : ℝ) / 13310610052469731215597310665827525731507928561498330521844) * r4 + ((-11290456980726044784237491283530411360397277437031 : ℝ) / 2605075727367739008056525965811599495953780228890681572983671078962417754200381920) * r5 + ((-65110367942316547822592678556 : ℝ) / 887235111878712692256595347199) * (value_105 h H) + ((16737663305534602825380752413048590659463469855651 : ℝ) / 11316981589909482471539590768400299687482136139540) * (value_104 h H) + ((141647942138152594705359580999092964383120712661813 : ℝ) / 220681141003234908195022019983805843905901654721030) * (value_106 h H) + ((65110367942316547822592678556 : ℝ) / 887235111878712692256595347199) * (value_121 h H) + ((-16737663305534602825380752413048590659463469855651 : ℝ) / 11316981589909482471539590768400299687482136139540) * (value_120 h H) + ((79033198865082313489662438984712879522780942059217 : ℝ) / 220681141003234908195022019983805843905901654721030) * (value_122 h H)

/-- Coordinate 70.3, recovered from nonplanar cycle 18. -/
theorem value_283 (h : Assignment) (H : Constraints h) :
    h 70 3 = ((-1615689746581315952869987896 : ℝ) / 6204441341809179666130037393) * (h 1 0) + ((9074791502589585430862011494 : ℝ) / 80657737443519335659690486109) * (h 1 1) + ((-5992215956008704915417834675 : ℝ) / 80657737443519335659690486109) * (h 1 2) + h 1 3 + ((1615689746581315952869987896 : ℝ) / 6204441341809179666130037393) * (h 3 0) + ((-9074791502589585430862011494 : ℝ) / 80657737443519335659690486109) * (h 5 1) + ((5992215956008704915417834675 : ℝ) / 80657737443519335659690486109) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 106 3
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 3 - h 26 3) - ((-226560544008554793078211948 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-48993321839319373946184 : ℝ) / 111320026377004042831756700403322383744655636362067) * r0 + ((-1310327292975456427839420823325372620244645144573 : ℝ) / 610075087308053842556196287341375331806183810531828274055586798269185106165) * r1 + ((-1 : ℝ) / 62662212923063117229264058) * r2 + ((-24496660919659686973092 : ℝ) / 1905816229120602686551507188710340840711930595369) * r3 + ((-1310327292975456427839420823325372620244645144573 : ℝ) / 20889161460242714444541964076961367863671090643176232656140503522699977310) * r4 + ((49727950835942667488633 : ℝ) / 148999366258989528532805716408517079084043976434682804349) * r5 + ((2793874825107583001789809857836615394977921417 : ℝ) / 1715370320918177573347141768532659896369916744221256523035779902740836975987960) * r6 + ((24468538752923917652446890384 : ℝ) / 887235111878712692256595347199) * (value_105 h H) + ((-4717522448817560538070579572726999896707387467223 : ℝ) / 8487736192432111853654693076300224765611602104655) * (value_104 h H) + ((44551127961165518546540307993062669088317934915482 : ℝ) / 331021711504852362292533029975708765858852482081545) * (value_106 h H) + (1 : ℝ) * (value_107 h H) + ((-24468538752923917652446890384 : ℝ) / 887235111878712692256595347199) * (value_121 h H) + ((4717522448817560538070579572726999896707387467223 : ℝ) / 8487736192432111853654693076300224765611602104655) * (value_120 h H) + ((-44551127961165518546540307993062669088317934915482 : ℝ) / 331021711504852362292533029975708765858852482081545) * (value_122 h H)

/-- Coordinate 74.0, recovered from nonplanar cycle 18. -/
theorem value_296 (h : Assignment) (H : Constraints h) :
    h 74 0 = ((281513443010244406222779958 : ℝ) / 617308285460186573299724243) * (h 1 0) + ((16988954485877604534684310704 : ℝ) / 40125038554912127264482075795) * (h 1 1) + ((-14869921899585899311348736212 : ℝ) / 40125038554912127264482075795) * (h 1 2) + ((335794842449942167076944285 : ℝ) / 617308285460186573299724243) * (h 3 0) + ((-16988954485877604534684310704 : ℝ) / 40125038554912127264482075795) * (h 5 1) + ((14869921899585899311348736212 : ℝ) / 40125038554912127264482075795) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((21089844167602855068 : ℝ) / 5034426941076396758397738451793612955734288923735) * r0 + ((-5832163527248582748141590948067132266801341663 : ℝ) / 187615599618220791105629469274203263444801636855116576474089805671678194010) * r1 + ((54 : ℝ) / 441375424104033399909302833745) * r2 + ((-29866207447394361881616210803 : ℝ) / 32897056931893656910635613121275903128969319940666039340) * r3 + ((-2868414083128873500869 : ℝ) / 902954697792258126647372669685319987396114004809256067030) * r4 + ((833166218178368964020227278295304609543048809 : ℝ) / 35344215732543832349837673358301042152449600664328141855518498852917231165088080) * r5 + ((-10532816513249223495190968 : ℝ) / 40125038554912127264482075795) * (value_105 h H) + ((3875746513861291815278596306243072245532474421 : ℝ) / 1996052494438989105592348083556037672397568162230) * (value_104 h H) + ((5832163527248582748141590948067132266801341663 : ℝ) / 2994078741658483658388522125334056508596352243345) * (value_106 h H) + ((10532816513249223495190968 : ℝ) / 40125038554912127264482075795) * (value_121 h H) + ((1992176747925127813777069487249794600152035687809 : ℝ) / 1996052494438989105592348083556037672397568162230) * (value_120 h H) + ((-5832163527248582748141590948067132266801341663 : ℝ) / 2994078741658483658388522125334056508596352243345) * (value_122 h H)

/-- Coordinate 74.1, recovered from nonplanar cycle 18. -/
theorem value_297 (h : Assignment) (H : Constraints h) :
    h 74 1 = ((234802336003959332237846063 : ℝ) / 4938466283681492586397793944) * (h 1 0) + ((148719343766200154698074751953 : ℝ) / 321000308439297018115856606360) * (h 1 1) + ((-39605003468736493200344541993 : ℝ) / 642000616878594036231713212720) * (h 1 2) + ((-234802336003959332237846063 : ℝ) / 4938466283681492586397793944) * (h 3 0) + ((172280964673096863417781854407 : ℝ) / 321000308439297018115856606360) * (h 5 1) + ((39605003468736493200344541993 : ℝ) / 642000616878594036231713212720) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-86680596277490302948284144729 : ℝ) / 13828780402107112901027519082140123192168041390139018605) * r0 + ((95882247040272773608590228623848218085380745020171307681 : ℝ) / 2061402386008449810011842273078241259082037050336075929087273056322438181876041720) * r1 + ((268014231549052794012734544287 : ℝ) / 947003516870347515813023089075815481187413674178254940) * r2 + ((95882247040272773608590228623848218085380745020171307681 : ℝ) / 70583061284908199984481178809919638956941632451770345978121570223853064083472080) * r3 + ((3210392454721863072158672027 : ℝ) / 675410113948609078732234756924619350572293275597323538138440) * r4 + ((-13697463862896110515512889803406888297911535002881615383 : ℝ) / 388340046301711592333300656802142838116644473750420424635351999778574904020816147725760) * r5 + ((173361192554980605896568289458 : ℝ) / 441375424104033399909302833745) * (value_105 h H) + ((-63718255321767336390046129736069442460104761696085335627 : ℝ) / 21931371287929104607090408747517268752646213293777359560) * (value_104 h H) + ((-95882247040272773608590228623848218085380745020171307681 : ℝ) / 32897056931893656910635613121275903128969319940666039340) * (value_106 h H) + ((268014231549052794012734544287 : ℝ) / 441375424104033399909302833745) * (value_121 h H) + ((63718255321767336390046129736069442460104761696085335627 : ℝ) / 21931371287929104607090408747517268752646213293777359560) * (value_120 h H) + ((95882247040272773608590228623848218085380745020171307681 : ℝ) / 32897056931893656910635613121275903128969319940666039340) * (value_122 h H)

/-- Coordinate 74.2, recovered from nonplanar cycle 18. -/
theorem value_298 (h : Assignment) (H : Constraints h) :
    h 74 2 = ((314878525056279147613324906 : ℝ) / 617308285460186573299724243) * (h 1 0) + ((-82808359645249467612955649736 : ℝ) / 40125038554912127264482075795) * (h 1 1) + ((69571840443901781045647078438 : ℝ) / 40125038554912127264482075795) * (h 1 2) + ((-314878525056279147613324906 : ℝ) / 617308285460186573299724243) * (h 3 0) + ((82808359645249467612955649736 : ℝ) / 40125038554912127264482075795) * (h 5 1) + ((-29446801888989653781165002643 : ℝ) / 40125038554912127264482075795) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((72087229224999271582938 : ℝ) / 55378696351840364342375122969729742513077178161085) * r0 + ((-13289951495936405795540667827846574975326637691847 : ℝ) / 1375847730533619134774616108010823931928545336937521560809991908258973422740) * r1 + ((36043614612499635791469 : ℝ) / 948091926401856847473923152855293357962354457095) * r2 + ((8666625942892474365975161091269839421046612092683 : ℝ) / 47109455845249146009272764340075499311170311819148613260103645801281914360) * r3 + ((-6536353765963051236307261 : ℝ) / 6621667783809892928747399577692346574238169368601211158220) * r4 + ((1898564499419486542220095403978082139332376813121 : ℝ) / 259190915371988103898809604627540975784630404871739706940468991588059695210645920) * r5 + ((-36002236542924486209580393588 : ℝ) / 441375424104033399909302833745) * (value_105 h H) + ((8831796800468169136271684327905010020524144680749 : ℝ) / 14637718292552586774343885946077609597582166523020) * (value_104 h H) + ((13289951495936405795540667827846574975326637691847 : ℝ) / 21956577438828880161515828919116414396373249784530) * (value_106 h H) + ((36002236542924486209580393588 : ℝ) / 441375424104033399909302833745) * (value_121 h H) + ((-8831796800468169136271684327905010020524144680749 : ℝ) / 14637718292552586774343885946077609597582166523020) * (value_120 h H) + ((8666625942892474365975161091269839421046612092683 : ℝ) / 21956577438828880161515828919116414396373249784530) * (value_122 h H)

/-- Coordinate 74.3, recovered from nonplanar cycle 18. -/
theorem value_299 (h : Assignment) (H : Constraints h) :
    h 74 3 = ((-162745290001629589379931036 : ℝ) / 617308285460186573299724243) * (h 1 0) + ((4942135071977515637471305614 : ℝ) / 40125038554912127264482075795) * (h 1 1) + ((-3203773603528562030662615047 : ℝ) / 40125038554912127264482075795) * (h 1 2) + h 1 3 + ((162745290001629589379931036 : ℝ) / 617308285460186573299724243) * (h 3 0) + ((-4942135071977515637471305614 : ℝ) / 40125038554912127264482075795) * (h 5 1) + ((3203773603528562030662615047 : ℝ) / 40125038554912127264482075795) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 121 3
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 3 - h 30 3) - ((-260646954530371667362044088 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-28182224282756744818152 : ℝ) / 55378696351840364342375122969729742513077178161085) * r0 + ((229220086263019531801102380170335255566985711573 : ℝ) / 60699164582365550063586004765183408761553470747243598271029054776131180415) * r1 + ((-14091112141378372409076 : ℝ) / 948091926401856847473923152855293357962354457095) * r2 + ((229220086263019531801102380170335255566985711573 : ℝ) / 2078358346113932912173798426768036734316337286138909408533984373585966810) * r3 + ((1 : ℝ) / 2145573734180397378650012) * r4 + ((28604801858030253222349 : ℝ) / 74123146833692831291948502735362088517591448155983706995) * r5 + ((-488742188194071496377617015288561312509564417 : ℝ) / 170670049630369690890348730000575708374427395657422985254918124399512529769960) * r6 + ((14074935544640070037550380752 : ℝ) / 441375424104033399909302833745) * (value_105 h H) + ((-2589567676477683451056682597346697693386412662647 : ℝ) / 10978288719414440080757914459558207198186624892265) * (value_104 h H) + ((-7793482932942664081237480925791398689277514193482 : ℝ) / 32934866158243320242273743378674621594559874676795) * (value_106 h H) + ((-14074935544640070037550380752 : ℝ) / 441375424104033399909302833745) * (value_121 h H) + ((2589567676477683451056682597346697693386412662647 : ℝ) / 10978288719414440080757914459558207198186624892265) * (value_120 h H) + ((7793482932942664081237480925791398689277514193482 : ℝ) / 32934866158243320242273743378674621594559874676795) * (value_122 h H) + (1 : ℝ) * (value_123 h H)

/-- Coordinate 66.0, recovered from nonplanar cycle 19. -/
theorem value_264 (h : Assignment) (H : Constraints h) :
    h 66 0 = ((131972807462839763526612 : ℝ) / 249669427901715076699691) * (h 1 0) + ((291719362271465515182138 : ℝ) / 28711984208697233820464465) * (h 1 1) + ((-255174997716761229511173 : ℝ) / 28711984208697233820464465) * (h 1 2) + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (h 3 0) + ((-291719362271465515182138 : ℝ) / 28711984208697233820464465) * (h 5 1) + ((255174997716761229511173 : ℝ) / 28711984208697233820464465) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-811393683605415051318460 : ℝ) / 517873774355332710498418715050165112570420769167) * r0 + ((71455183697356183931117077 : ℝ) / 17607708328081312156946236311705613827394306151678) * r1 + ((-593157108110605107057726659082247371708867940 : ℝ) / 2677668757522307941797664061715133457117348355716374364457589131088049) * r2 + ((52236233751663614334210416283161668115738593603 : ℝ) / 91040737755758470021120578098314537541989844094356728391558030456993666) * r3 + ((-2520917709470071704995338301099551329762688745 : ℝ) / 25391791576423973272589368714560470566582147455845819153857557553903568) * r4 + ((52236233751663614334210416283161668115738593603 : ℝ) / 203134332611391786180714949716483764532657179646766553230860460431228544) * r5 + ((-927697717084986387438284494804634889352669458160 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_117 h H) + ((131972807462839763526612 : ℝ) / 249669427901715076699691) * (value_116 h H) + ((2402866752576526259373679149025436733323975305738 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_118 h H) + ((927697717084986387438284494804634889352669458160 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_125 h H) + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (value_124 h H) + ((-2402866752576526259373679149025436733323975305738 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_126 h H)

/-- Coordinate 66.1, recovered from nonplanar cycle 19. -/
theorem value_265 (h : Assignment) (H : Constraints h) :
    h 66 1 = ((251753206123348448905855 : ℝ) / 253395837273382465904164) * (h 1 0) + ((-7226762153765448547821267 : ℝ) / 1714148310966999034057580) * (h 1 1) + ((214929259610135377181499163 : ℝ) / 58281042572877967157957720) * (h 1 2) + ((-251753206123348448905855 : ℝ) / 253395837273382465904164) * (h 3 0) + ((8940910464732447581878847 : ℝ) / 1714148310966999034057580) * (h 5 1) + ((-214929259610135377181499163 : ℝ) / 58281042572877967157957720) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1604827183273609902100805769552786138329276487 : ℝ) / 384234312392437198995902224465650726762480338972134597335141714960652) * r0 + ((-2569867369991748443419461387910468335595507969405 : ℝ) / 300471232290885889614795539532138868328259625076209255116080821099229864) * r1 + ((7295391474139179659100458865039844502220127975 : ℝ) / 15626395286436155302132636539262943010938555329628393679148020153066077) * r2 + ((-2569867369991748443419461387910468335595507969405 : ℝ) / 2125189758955317121090038569339760249487643524829461540364130740816986472) * r3 + ((7295391474139179659100458865039844502220127975 : ℝ) / 34866340672104560314600327190142735703366530834892766599326795447151168) * r4 + ((-2569867369991748443419461387910468335595507969405 : ℝ) / 4741822331406220202785644497859412055657848193545416257508444180812558848) * r5 + ((36911025215293027748318532699714081181573359201 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_117 h H) + ((251753206123348448905855 : ℝ) / 253395837273382465904164) * (value_116 h H) + ((-2569867369991748443419461387910468335595507969405 : ℝ) / 262801616837034509805167706144859907871556808234) * (value_118 h H) + ((-29181565896556718636401835460159378008880511900 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_125 h H) + ((-251753206123348448905855 : ℝ) / 253395837273382465904164) * (value_124 h H) + ((2569867369991748443419461387910468335595507969405 : ℝ) / 262801616837034509805167706144859907871556808234) * (value_126 h H)

/-- Coordinate 66.2, recovered from nonplanar cycle 19. -/
theorem value_266 (h : Assignment) (H : Constraints h) :
    h 66 2 = ((109175811564558021538052 : ℝ) / 249669427901715076699691) * (h 1 0) + ((-10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (h 1 1) + ((9018608418867289852888476 : ℝ) / 5742396841739446764092893) * (h 1 2) + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (h 3 0) + ((10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (h 5 1) + ((-3276211577127843088795583 : ℝ) / 5742396841739446764092893) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((550214682645822390832576088684993773662484720 : ℝ) / 378583807798430769598903662341155863133620333987250265021389630917113) * r0 + ((-100649066561508782968367800768776737696362181881 : ℝ) / 34829710317455630803099136935386339408293070726827024381967846044374396) * r1 + ((550214682645822390832576088684993773662484720 : ℝ) / 2677668757522307941797664061715133457117348355716374364457589131088049) * r2 + ((-24227259846749804575659470957819235363136715882 : ℝ) / 45520368877879235010560289049157268770994922047178364195779015228496833) * r3 + ((584603100311186290259612094227805884516390015 : ℝ) / 6347947894105993318147342178640117641645536863961454788464389388475892) * r4 + ((-12113629923374902287829735478909617681568357941 : ℝ) / 50783583152847946545178737429120941133164294911691638307715115107807136) * r5 + ((860535763658066219262149002703330262008126102080 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_117 h H) + ((109175811564558021538052 : ℝ) / 249669427901715076699691) * (value_116 h H) + ((-1711034131545649310462252613069204540838157091977 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_118 h H) + ((-860535763658066219262149002703330262008126102080 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_125 h H) + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (value_124 h H) + ((2228907905900982020960671328119369653408577861144 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_126 h H)

/-- Coordinate 66.3, recovered from nonplanar cycle 19. -/
theorem value_267 (h : Assignment) (H : Constraints h) :
    h 66 3 = ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (h 1 0) + ((42085322381761110668898 : ℝ) / 428537077741749758514395) * (h 1 1) + ((-36813195939601494408633 : ℝ) / 428537077741749758514395) * (h 1 2) + h 1 3 + ((928717562452291111080 : ℝ) / 3726409371667389204473) * (h 3 0) + ((-42085322381761110668898 : ℝ) / 428537077741749758514395) * (h 5 1) + ((36813195939601494408633 : ℝ) / 428537077741749758514395) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 117 3
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 3 - h 29 3) - ((604462459218948328868640 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-107650794861029512448538887237128784616362400 : ℝ) / 129961605662147876130966928863381863463780114652339643216297933001397) * r0 + ((278830605159619014340476296540840583789461820 : ℝ) / 129961605662147876130966928863381863463780114652339643216297933001397) * r1 + ((1 : ℝ) / 1143338598549074470824196) * r2 + ((-107650794861029512448538887237128784616362400 : ℝ) / 919199722731538547184272737603702530055209137036964334067530597239181) * r3 + ((278830605159619014340476296540840583789461820 : ℝ) / 919199722731538547184272737603702530055209137036964334067530597239181) * r4 + ((-57189484769921928488286283844724666827442525 : ℝ) / 1089573146003267509831260224691960490730204088590398956228962357723474) * r5 + ((1185030071928380810947024260298572481105212735 : ℝ) / 8716585168026140078650081797535683925841632708723191649831698861787792) * r6 + ((-7320254050550006846500644332124757353912643200 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_117 h H) + ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (value_116 h H) + ((18960481150854092975152388164777159697683403760 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_118 h H) + (1 : ℝ) * (value_119 h H) + ((7320254050550006846500644332124757353912643200 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_125 h H) + ((928717562452291111080 : ℝ) / 3726409371667389204473) * (value_124 h H) + ((-18960481150854092975152388164777159697683403760 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_126 h H)

/-- Coordinate 67.0, recovered from nonplanar cycle 19. -/
theorem value_268 (h : Assignment) (H : Constraints h) :
    h 67 0 = ((20682018593087191246588 : ℝ) / 41708273765268360426865) * (h 1 0) + ((941473835656930474758414 : ℝ) / 4796451483005861449089475) * (h 1 1) + ((-823533213543044848835519 : ℝ) / 4796451483005861449089475) * (h 1 2) + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (h 3 0) + ((-941473835656930474758414 : ℝ) / 4796451483005861449089475) * (h 5 1) + ((823533213543044848835519 : ℝ) / 4796451483005861449089475) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((2009949414449318445175543102150514863228724 : ℝ) / 866355275566569858948487600950711847873069632048958703361507183715) * r0 + ((-141494409519668287884700623372268574864544271 : ℝ) / 29456079369263375204248578432324202827684367489664595914291244246310) * r1 + ((28377560264614094921516 : ℝ) / 86512879603216544560540780902143301688406903005) * r2 + ((-1997695118287574906381689 : ℝ) / 2941437906509362515058386550672872257405834702170) * r3 + ((8542285011409603391996058184139688168722077 : ℝ) / 58106850148314456487527100565348505362765907145885914393304226176240) * r4 + ((-141494409519668287884700623372268574864544271 : ℝ) / 464854801186515651900216804522788042902127257167087315146433809409920) * r5 + ((3143560884198734048254549411763405246089724336 : ℝ) / 1185107939770089651514257272632100023128861685) * (value_117 h H) + ((20682018593087191246588 : ℝ) / 41708273765268360426865) * (value_116 h H) + ((-6508742837904741242696228675124354443769036466 : ℝ) / 1185107939770089651514257272632100023128861685) * (value_118 h H) + ((-3143560884198734048254549411763405246089724336 : ℝ) / 1185107939770089651514257272632100023128861685) * (value_125 h H) + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (value_124 h H) + ((6508742837904741242696228675124354443769036466 : ℝ) / 1185107939770089651514257272632100023128861685) * (value_126 h H)

/-- Coordinate 67.1, recovered from nonplanar cycle 19. -/
theorem value_269 (h : Assignment) (H : Constraints h) :
    h 67 1 = ((16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (h 1 0) + ((-925399385763555945482272269 : ℝ) / 220636768218269626658115850) * (h 1 1) + ((27522063213634645341565356741 : ℝ) / 7501650119421167306375938900) * (h 1 2) + ((-16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (h 3 0) + ((1146036153981825572140388119 : ℝ) / 220636768218269626658115850) * (h 5 1) + ((-27522063213634645341565356741 : ℝ) / 7501650119421167306375938900) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((114502986016987110991293702763225036414084356073 : ℝ) / 24728378630496603483966681593936168273841026507573428270047499544777245) * r0 + ((-32242666961150933094358397585000489763123313279043 : ℝ) / 3363059493747538073819468696775318885242379605029986244726459938089705320) * r1 + ((371499064464731899404634030150756843967930521287 : ℝ) / 699601044937638137382712226548254133833392708821745918579444028100003540) * r2 + ((-32242666961150933094358397585000489763123313279043 : ℝ) / 23786435527879696671012215702640640550335352099939361231701096955400120360) * r3 + ((114502986016987110991293702763225036414084356073 : ℝ) / 390245605596079889770232007396880562016335832391769801065431182999627840) * r4 + ((-32242666961150933094358397585000489763123313279043 : ℝ) / 53073402361066865008751553005975756434221673205280692944898640887949386240) * r5 + ((458011944067948443965174811052900145656337424292 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_117 h H) + ((16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (value_116 h H) + ((-32242666961150933094358397585000489763123313279043 : ℝ) / 2941437906509362515058386550672872257405834702170) * (value_118 h H) + ((-371499064464731899404634030150756843967930521287 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_125 h H) + ((-16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (value_124 h H) + ((32242666961150933094358397585000489763123313279043 : ℝ) / 2941437906509362515058386550672872257405834702170) * (value_126 h H)

/-- Coordinate 67.2, recovered from nonplanar cycle 19. -/
theorem value_270 (h : Assignment) (H : Constraints h) :
    h 67 2 = ((414876610754063195580374 : ℝ) / 959290296601172289817895) * (h 1 0) + ((-195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (h 1 1) + ((170624048649954562499929323 : ℝ) / 110318384109134813329057925) * (h 1 2) + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (h 3 0) + ((195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (h 5 1) + ((-60305664540819749170871398 : ℝ) / 110318384109134813329057925) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((2943296506013068108791580540081692482399981746 : ℝ) / 1454610507676270793174510681996245192578883912210201662943970561457485) * r0 + ((-414398489997543223485972233841662647776360685843 : ℝ) / 98913514521986413935866726375744673095364106030293713080189998179108980) * r1 + ((2943296506013068108791580540081692482399981746 : ℝ) / 10288250660847619667392826861003737262255775129731557626168294530882405) * r2 + ((-125227842400189942011628253685951487366191897212 : ℝ) / 174900261234409534345678056637063533458348177205436479644861007025000885) * r3 + ((25018020301111078924728434590694386100399844841 : ℝ) / 195122802798039944885116003698440281008167916195884900532715591499813920) * r4 + ((-414398489997543223485972233841662647776360685843 : ℝ) / 1560982422384319559080928029587522248065343329567079204261724731998511360) * r5 + ((200144162408888631397827476725555088803198758728 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_117 h H) + ((414876610754063195580374 : ℝ) / 959290296601172289817895) * (value_116 h H) + ((-414398489997543223485972233841662647776360685843 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_118 h H) + ((-200144162408888631397827476725555088803198758728 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_125 h H) + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (value_124 h H) + ((500911369600759768046513014743805949464767588848 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_126 h H)

end CubicalIndecomposability.Rigidity
