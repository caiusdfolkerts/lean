module
prelude
public import RootedSubsumedForest0708DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_512 : dispositionTest 512 = true := by decide +kernel

theorem disposition_at_513 : dispositionTest 513 = true := by decide +kernel

theorem disposition_at_514 : dispositionTest 514 = true := by decide +kernel

theorem disposition_at_515 : dispositionTest 515 = true := by decide +kernel

theorem disposition_at_516 : dispositionTest 516 = true := by decide +kernel

theorem disposition_at_517 : dispositionTest 517 = true := by decide +kernel

theorem disposition_at_518 : dispositionTest 518 = true := by decide +kernel

theorem disposition_at_519 : dispositionTest 519 = true := by decide +kernel

theorem disposition_at_520 : dispositionTest 520 = true := by decide +kernel

theorem disposition_at_521 : dispositionTest 521 = true := by decide +kernel

theorem disposition_at_522 : dispositionTest 522 = true := by decide +kernel

theorem disposition_at_523 : dispositionTest 523 = true := by decide +kernel

theorem disposition_at_524 : dispositionTest 524 = true := by decide +kernel

theorem disposition_at_525 : dispositionTest 525 = true := by decide +kernel

theorem disposition_at_526 : dispositionTest 526 = true := by decide +kernel

theorem disposition_at_527 : dispositionTest 527 = true := by decide +kernel

theorem disposition_at_528 : dispositionTest 528 = true := by decide +kernel

theorem disposition_at_529 : dispositionTest 529 = true := by decide +kernel

theorem disposition_at_530 : dispositionTest 530 = true := by decide +kernel

theorem disposition_at_531 : dispositionTest 531 = true := by decide +kernel

theorem disposition_at_532 : dispositionTest 532 = true := by decide +kernel

theorem disposition_at_533 : dispositionTest 533 = true := by decide +kernel

theorem disposition_at_534 : dispositionTest 534 = true := by decide +kernel

theorem disposition_at_535 : dispositionTest 535 = true := by decide +kernel

theorem disposition_at_536 : dispositionTest 536 = true := by decide +kernel

theorem disposition_at_537 : dispositionTest 537 = true := by decide +kernel

theorem disposition_at_538 : dispositionTest 538 = true := by decide +kernel

theorem disposition_at_539 : dispositionTest 539 = true := by decide +kernel

theorem disposition_at_540 : dispositionTest 540 = true := by decide +kernel

theorem disposition_at_541 : dispositionTest 541 = true := by decide +kernel

theorem disposition_at_542 : dispositionTest 542 = true := by decide +kernel

theorem disposition_at_543 : dispositionTest 543 = true := by decide +kernel

theorem disposition_interval_512 : Interval dispositionTest 512 513 := by
  intro i hlo hhi
  have h : i = 512 := by omega
  subst i
  exact disposition_at_512


theorem disposition_interval_513 : Interval dispositionTest 513 514 := by
  intro i hlo hhi
  have h : i = 513 := by omega
  subst i
  exact disposition_at_513


theorem disposition_interval_514 : Interval dispositionTest 514 515 := by
  intro i hlo hhi
  have h : i = 514 := by omega
  subst i
  exact disposition_at_514


theorem disposition_interval_515 : Interval dispositionTest 515 516 := by
  intro i hlo hhi
  have h : i = 515 := by omega
  subst i
  exact disposition_at_515


theorem disposition_interval_516 : Interval dispositionTest 516 517 := by
  intro i hlo hhi
  have h : i = 516 := by omega
  subst i
  exact disposition_at_516


theorem disposition_interval_517 : Interval dispositionTest 517 518 := by
  intro i hlo hhi
  have h : i = 517 := by omega
  subst i
  exact disposition_at_517


theorem disposition_interval_518 : Interval dispositionTest 518 519 := by
  intro i hlo hhi
  have h : i = 518 := by omega
  subst i
  exact disposition_at_518


theorem disposition_interval_519 : Interval dispositionTest 519 520 := by
  intro i hlo hhi
  have h : i = 519 := by omega
  subst i
  exact disposition_at_519


theorem disposition_interval_520 : Interval dispositionTest 520 521 := by
  intro i hlo hhi
  have h : i = 520 := by omega
  subst i
  exact disposition_at_520


theorem disposition_interval_521 : Interval dispositionTest 521 522 := by
  intro i hlo hhi
  have h : i = 521 := by omega
  subst i
  exact disposition_at_521


theorem disposition_interval_522 : Interval dispositionTest 522 523 := by
  intro i hlo hhi
  have h : i = 522 := by omega
  subst i
  exact disposition_at_522


theorem disposition_interval_523 : Interval dispositionTest 523 524 := by
  intro i hlo hhi
  have h : i = 523 := by omega
  subst i
  exact disposition_at_523


theorem disposition_interval_524 : Interval dispositionTest 524 525 := by
  intro i hlo hhi
  have h : i = 524 := by omega
  subst i
  exact disposition_at_524


theorem disposition_interval_525 : Interval dispositionTest 525 526 := by
  intro i hlo hhi
  have h : i = 525 := by omega
  subst i
  exact disposition_at_525


theorem disposition_interval_526 : Interval dispositionTest 526 527 := by
  intro i hlo hhi
  have h : i = 526 := by omega
  subst i
  exact disposition_at_526


theorem disposition_interval_527 : Interval dispositionTest 527 528 := by
  intro i hlo hhi
  have h : i = 527 := by omega
  subst i
  exact disposition_at_527


theorem disposition_interval_528 : Interval dispositionTest 528 529 := by
  intro i hlo hhi
  have h : i = 528 := by omega
  subst i
  exact disposition_at_528


theorem disposition_interval_529 : Interval dispositionTest 529 530 := by
  intro i hlo hhi
  have h : i = 529 := by omega
  subst i
  exact disposition_at_529


theorem disposition_interval_530 : Interval dispositionTest 530 531 := by
  intro i hlo hhi
  have h : i = 530 := by omega
  subst i
  exact disposition_at_530


theorem disposition_interval_531 : Interval dispositionTest 531 532 := by
  intro i hlo hhi
  have h : i = 531 := by omega
  subst i
  exact disposition_at_531


theorem disposition_interval_532 : Interval dispositionTest 532 533 := by
  intro i hlo hhi
  have h : i = 532 := by omega
  subst i
  exact disposition_at_532


theorem disposition_interval_533 : Interval dispositionTest 533 534 := by
  intro i hlo hhi
  have h : i = 533 := by omega
  subst i
  exact disposition_at_533


theorem disposition_interval_534 : Interval dispositionTest 534 535 := by
  intro i hlo hhi
  have h : i = 534 := by omega
  subst i
  exact disposition_at_534


theorem disposition_interval_535 : Interval dispositionTest 535 536 := by
  intro i hlo hhi
  have h : i = 535 := by omega
  subst i
  exact disposition_at_535


theorem disposition_interval_536 : Interval dispositionTest 536 537 := by
  intro i hlo hhi
  have h : i = 536 := by omega
  subst i
  exact disposition_at_536


theorem disposition_interval_537 : Interval dispositionTest 537 538 := by
  intro i hlo hhi
  have h : i = 537 := by omega
  subst i
  exact disposition_at_537


theorem disposition_interval_538 : Interval dispositionTest 538 539 := by
  intro i hlo hhi
  have h : i = 538 := by omega
  subst i
  exact disposition_at_538


theorem disposition_interval_539 : Interval dispositionTest 539 540 := by
  intro i hlo hhi
  have h : i = 539 := by omega
  subst i
  exact disposition_at_539


theorem disposition_interval_540 : Interval dispositionTest 540 541 := by
  intro i hlo hhi
  have h : i = 540 := by omega
  subst i
  exact disposition_at_540


theorem disposition_interval_541 : Interval dispositionTest 541 542 := by
  intro i hlo hhi
  have h : i = 541 := by omega
  subst i
  exact disposition_at_541


theorem disposition_interval_542 : Interval dispositionTest 542 543 := by
  intro i hlo hhi
  have h : i = 542 := by omega
  subst i
  exact disposition_at_542


theorem disposition_interval_543 : Interval dispositionTest 543 544 := by
  intro i hlo hhi
  have h : i = 543 := by omega
  subst i
  exact disposition_at_543

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
