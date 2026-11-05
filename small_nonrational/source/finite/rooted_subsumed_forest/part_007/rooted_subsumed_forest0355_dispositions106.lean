module
prelude
public import RootedSubsumedForest0355DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_3392 : dispositionTest 3392 = true := by decide +kernel


theorem disposition_at_3393 : dispositionTest 3393 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3393).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1057.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1057) = true
  rw [Nonrational.OldTerminalMatches.M016.r1057_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3394 : dispositionTest 3394 = true := by decide +kernel

theorem disposition_at_3395 : dispositionTest 3395 = true := by decide +kernel

theorem disposition_at_3396 : dispositionTest 3396 = true := by decide +kernel

theorem disposition_at_3397 : dispositionTest 3397 = true := by decide +kernel

theorem disposition_at_3398 : dispositionTest 3398 = true := by decide +kernel

theorem disposition_at_3399 : dispositionTest 3399 = true := by decide +kernel

theorem disposition_at_3400 : dispositionTest 3400 = true := by decide +kernel

theorem disposition_at_3401 : dispositionTest 3401 = true := by decide +kernel

theorem disposition_at_3402 : dispositionTest 3402 = true := by decide +kernel

theorem disposition_at_3403 : dispositionTest 3403 = true := by decide +kernel

theorem disposition_at_3404 : dispositionTest 3404 = true := by decide +kernel

theorem disposition_at_3405 : dispositionTest 3405 = true := by decide +kernel


theorem disposition_at_3406 : dispositionTest 3406 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3406).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1058.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1058) = true
  rw [Nonrational.OldTerminalMatches.M016.r1058_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3407 : dispositionTest 3407 = true := by decide +kernel

theorem disposition_at_3408 : dispositionTest 3408 = true := by decide +kernel


theorem disposition_at_3409 : dispositionTest 3409 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3409).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1059.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1059) = true
  rw [Nonrational.OldTerminalMatches.M016.r1059_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3410 : dispositionTest 3410 = true := by decide +kernel

theorem disposition_at_3411 : dispositionTest 3411 = true := by decide +kernel

theorem disposition_at_3412 : dispositionTest 3412 = true := by decide +kernel

theorem disposition_at_3413 : dispositionTest 3413 = true := by decide +kernel

theorem disposition_at_3414 : dispositionTest 3414 = true := by decide +kernel

theorem disposition_at_3415 : dispositionTest 3415 = true := by decide +kernel

theorem disposition_at_3416 : dispositionTest 3416 = true := by decide +kernel

theorem disposition_at_3417 : dispositionTest 3417 = true := by decide +kernel


theorem disposition_at_3418 : dispositionTest 3418 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3418).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1060.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1060) = true
  rw [Nonrational.OldTerminalMatches.M016.r1060_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3419 : dispositionTest 3419 = true := by decide +kernel


theorem disposition_at_3420 : dispositionTest 3420 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3420).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1061.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1061) = true
  rw [Nonrational.OldTerminalMatches.M016.r1061_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_3421 : dispositionTest 3421 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3421).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1062.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1062) = true
  rw [Nonrational.OldTerminalMatches.M016.r1062_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_3422 : dispositionTest 3422 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3422).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1063.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1063) = true
  rw [Nonrational.OldTerminalMatches.M016.r1063_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3423 : dispositionTest 3423 = true := by decide +kernel

theorem disposition_interval_3392 : Interval dispositionTest 3392 3393 := by
  intro i hlo hhi
  have h : i = 3392 := by omega
  subst i
  exact disposition_at_3392


theorem disposition_interval_3393 : Interval dispositionTest 3393 3394 := by
  intro i hlo hhi
  have h : i = 3393 := by omega
  subst i
  exact disposition_at_3393


theorem disposition_interval_3394 : Interval dispositionTest 3394 3395 := by
  intro i hlo hhi
  have h : i = 3394 := by omega
  subst i
  exact disposition_at_3394


theorem disposition_interval_3395 : Interval dispositionTest 3395 3396 := by
  intro i hlo hhi
  have h : i = 3395 := by omega
  subst i
  exact disposition_at_3395


theorem disposition_interval_3396 : Interval dispositionTest 3396 3397 := by
  intro i hlo hhi
  have h : i = 3396 := by omega
  subst i
  exact disposition_at_3396


theorem disposition_interval_3397 : Interval dispositionTest 3397 3398 := by
  intro i hlo hhi
  have h : i = 3397 := by omega
  subst i
  exact disposition_at_3397


theorem disposition_interval_3398 : Interval dispositionTest 3398 3399 := by
  intro i hlo hhi
  have h : i = 3398 := by omega
  subst i
  exact disposition_at_3398


theorem disposition_interval_3399 : Interval dispositionTest 3399 3400 := by
  intro i hlo hhi
  have h : i = 3399 := by omega
  subst i
  exact disposition_at_3399


theorem disposition_interval_3400 : Interval dispositionTest 3400 3401 := by
  intro i hlo hhi
  have h : i = 3400 := by omega
  subst i
  exact disposition_at_3400


theorem disposition_interval_3401 : Interval dispositionTest 3401 3402 := by
  intro i hlo hhi
  have h : i = 3401 := by omega
  subst i
  exact disposition_at_3401


theorem disposition_interval_3402 : Interval dispositionTest 3402 3403 := by
  intro i hlo hhi
  have h : i = 3402 := by omega
  subst i
  exact disposition_at_3402


theorem disposition_interval_3403 : Interval dispositionTest 3403 3404 := by
  intro i hlo hhi
  have h : i = 3403 := by omega
  subst i
  exact disposition_at_3403


theorem disposition_interval_3404 : Interval dispositionTest 3404 3405 := by
  intro i hlo hhi
  have h : i = 3404 := by omega
  subst i
  exact disposition_at_3404


theorem disposition_interval_3405 : Interval dispositionTest 3405 3406 := by
  intro i hlo hhi
  have h : i = 3405 := by omega
  subst i
  exact disposition_at_3405


theorem disposition_interval_3406 : Interval dispositionTest 3406 3407 := by
  intro i hlo hhi
  have h : i = 3406 := by omega
  subst i
  exact disposition_at_3406


theorem disposition_interval_3407 : Interval dispositionTest 3407 3408 := by
  intro i hlo hhi
  have h : i = 3407 := by omega
  subst i
  exact disposition_at_3407


theorem disposition_interval_3408 : Interval dispositionTest 3408 3409 := by
  intro i hlo hhi
  have h : i = 3408 := by omega
  subst i
  exact disposition_at_3408


theorem disposition_interval_3409 : Interval dispositionTest 3409 3410 := by
  intro i hlo hhi
  have h : i = 3409 := by omega
  subst i
  exact disposition_at_3409


theorem disposition_interval_3410 : Interval dispositionTest 3410 3411 := by
  intro i hlo hhi
  have h : i = 3410 := by omega
  subst i
  exact disposition_at_3410


theorem disposition_interval_3411 : Interval dispositionTest 3411 3412 := by
  intro i hlo hhi
  have h : i = 3411 := by omega
  subst i
  exact disposition_at_3411


theorem disposition_interval_3412 : Interval dispositionTest 3412 3413 := by
  intro i hlo hhi
  have h : i = 3412 := by omega
  subst i
  exact disposition_at_3412


theorem disposition_interval_3413 : Interval dispositionTest 3413 3414 := by
  intro i hlo hhi
  have h : i = 3413 := by omega
  subst i
  exact disposition_at_3413


theorem disposition_interval_3414 : Interval dispositionTest 3414 3415 := by
  intro i hlo hhi
  have h : i = 3414 := by omega
  subst i
  exact disposition_at_3414


theorem disposition_interval_3415 : Interval dispositionTest 3415 3416 := by
  intro i hlo hhi
  have h : i = 3415 := by omega
  subst i
  exact disposition_at_3415


theorem disposition_interval_3416 : Interval dispositionTest 3416 3417 := by
  intro i hlo hhi
  have h : i = 3416 := by omega
  subst i
  exact disposition_at_3416


theorem disposition_interval_3417 : Interval dispositionTest 3417 3418 := by
  intro i hlo hhi
  have h : i = 3417 := by omega
  subst i
  exact disposition_at_3417


theorem disposition_interval_3418 : Interval dispositionTest 3418 3419 := by
  intro i hlo hhi
  have h : i = 3418 := by omega
  subst i
  exact disposition_at_3418


theorem disposition_interval_3419 : Interval dispositionTest 3419 3420 := by
  intro i hlo hhi
  have h : i = 3419 := by omega
  subst i
  exact disposition_at_3419


theorem disposition_interval_3420 : Interval dispositionTest 3420 3421 := by
  intro i hlo hhi
  have h : i = 3420 := by omega
  subst i
  exact disposition_at_3420


theorem disposition_interval_3421 : Interval dispositionTest 3421 3422 := by
  intro i hlo hhi
  have h : i = 3421 := by omega
  subst i
  exact disposition_at_3421


theorem disposition_interval_3422 : Interval dispositionTest 3422 3423 := by
  intro i hlo hhi
  have h : i = 3422 := by omega
  subst i
  exact disposition_at_3422


theorem disposition_interval_3423 : Interval dispositionTest 3423 3424 := by
  intro i hlo hhi
  have h : i = 3423 := by omega
  subst i
  exact disposition_at_3423

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
