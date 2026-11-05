module
prelude
public import RootedSubsumedForest0353DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_544 : dispositionTest 544 = true := by decide +kernel

theorem disposition_at_545 : dispositionTest 545 = true := by decide +kernel

theorem disposition_at_546 : dispositionTest 546 = true := by decide +kernel

theorem disposition_at_547 : dispositionTest 547 = true := by decide +kernel

theorem disposition_at_548 : dispositionTest 548 = true := by decide +kernel

theorem disposition_at_549 : dispositionTest 549 = true := by decide +kernel

theorem disposition_at_550 : dispositionTest 550 = true := by decide +kernel

theorem disposition_at_551 : dispositionTest 551 = true := by decide +kernel

theorem disposition_at_552 : dispositionTest 552 = true := by decide +kernel

theorem disposition_at_553 : dispositionTest 553 = true := by decide +kernel

theorem disposition_at_554 : dispositionTest 554 = true := by decide +kernel

theorem disposition_at_555 : dispositionTest 555 = true := by decide +kernel

theorem disposition_at_556 : dispositionTest 556 = true := by decide +kernel

theorem disposition_at_557 : dispositionTest 557 = true := by decide +kernel

theorem disposition_at_558 : dispositionTest 558 = true := by decide +kernel

theorem disposition_at_559 : dispositionTest 559 = true := by decide +kernel

theorem disposition_at_560 : dispositionTest 560 = true := by decide +kernel

theorem disposition_at_561 : dispositionTest 561 = true := by decide +kernel

theorem disposition_at_562 : dispositionTest 562 = true := by decide +kernel


theorem disposition_at_563 : dispositionTest 563 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 563).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M013.r0878.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M013.r0878) = true
  rw [Nonrational.OldTerminalMatches.M013.r0878_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_564 : dispositionTest 564 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 564).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M013.r0879.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M013.r0879) = true
  rw [Nonrational.OldTerminalMatches.M013.r0879_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_565 : dispositionTest 565 = true := by decide +kernel

theorem disposition_at_566 : dispositionTest 566 = true := by decide +kernel


theorem disposition_at_567 : dispositionTest 567 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 567).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M013.r0880.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M013.r0880) = true
  rw [Nonrational.OldTerminalMatches.M013.r0880_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_568 : dispositionTest 568 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 568).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M013.r0881.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M013.r0881) = true
  rw [Nonrational.OldTerminalMatches.M013.r0881_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_569 : dispositionTest 569 = true := by decide +kernel

theorem disposition_at_570 : dispositionTest 570 = true := by decide +kernel

theorem disposition_at_571 : dispositionTest 571 = true := by decide +kernel

theorem disposition_at_572 : dispositionTest 572 = true := by decide +kernel

theorem disposition_at_573 : dispositionTest 573 = true := by decide +kernel

theorem disposition_at_574 : dispositionTest 574 = true := by decide +kernel

theorem disposition_at_575 : dispositionTest 575 = true := by decide +kernel

theorem disposition_interval_544 : Interval dispositionTest 544 545 := by
  intro i hlo hhi
  have h : i = 544 := by omega
  subst i
  exact disposition_at_544


theorem disposition_interval_545 : Interval dispositionTest 545 546 := by
  intro i hlo hhi
  have h : i = 545 := by omega
  subst i
  exact disposition_at_545


theorem disposition_interval_546 : Interval dispositionTest 546 547 := by
  intro i hlo hhi
  have h : i = 546 := by omega
  subst i
  exact disposition_at_546


theorem disposition_interval_547 : Interval dispositionTest 547 548 := by
  intro i hlo hhi
  have h : i = 547 := by omega
  subst i
  exact disposition_at_547


theorem disposition_interval_548 : Interval dispositionTest 548 549 := by
  intro i hlo hhi
  have h : i = 548 := by omega
  subst i
  exact disposition_at_548


theorem disposition_interval_549 : Interval dispositionTest 549 550 := by
  intro i hlo hhi
  have h : i = 549 := by omega
  subst i
  exact disposition_at_549


theorem disposition_interval_550 : Interval dispositionTest 550 551 := by
  intro i hlo hhi
  have h : i = 550 := by omega
  subst i
  exact disposition_at_550


theorem disposition_interval_551 : Interval dispositionTest 551 552 := by
  intro i hlo hhi
  have h : i = 551 := by omega
  subst i
  exact disposition_at_551


theorem disposition_interval_552 : Interval dispositionTest 552 553 := by
  intro i hlo hhi
  have h : i = 552 := by omega
  subst i
  exact disposition_at_552


theorem disposition_interval_553 : Interval dispositionTest 553 554 := by
  intro i hlo hhi
  have h : i = 553 := by omega
  subst i
  exact disposition_at_553


theorem disposition_interval_554 : Interval dispositionTest 554 555 := by
  intro i hlo hhi
  have h : i = 554 := by omega
  subst i
  exact disposition_at_554


theorem disposition_interval_555 : Interval dispositionTest 555 556 := by
  intro i hlo hhi
  have h : i = 555 := by omega
  subst i
  exact disposition_at_555


theorem disposition_interval_556 : Interval dispositionTest 556 557 := by
  intro i hlo hhi
  have h : i = 556 := by omega
  subst i
  exact disposition_at_556


theorem disposition_interval_557 : Interval dispositionTest 557 558 := by
  intro i hlo hhi
  have h : i = 557 := by omega
  subst i
  exact disposition_at_557


theorem disposition_interval_558 : Interval dispositionTest 558 559 := by
  intro i hlo hhi
  have h : i = 558 := by omega
  subst i
  exact disposition_at_558


theorem disposition_interval_559 : Interval dispositionTest 559 560 := by
  intro i hlo hhi
  have h : i = 559 := by omega
  subst i
  exact disposition_at_559


theorem disposition_interval_560 : Interval dispositionTest 560 561 := by
  intro i hlo hhi
  have h : i = 560 := by omega
  subst i
  exact disposition_at_560


theorem disposition_interval_561 : Interval dispositionTest 561 562 := by
  intro i hlo hhi
  have h : i = 561 := by omega
  subst i
  exact disposition_at_561


theorem disposition_interval_562 : Interval dispositionTest 562 563 := by
  intro i hlo hhi
  have h : i = 562 := by omega
  subst i
  exact disposition_at_562


theorem disposition_interval_563 : Interval dispositionTest 563 564 := by
  intro i hlo hhi
  have h : i = 563 := by omega
  subst i
  exact disposition_at_563


theorem disposition_interval_564 : Interval dispositionTest 564 565 := by
  intro i hlo hhi
  have h : i = 564 := by omega
  subst i
  exact disposition_at_564


theorem disposition_interval_565 : Interval dispositionTest 565 566 := by
  intro i hlo hhi
  have h : i = 565 := by omega
  subst i
  exact disposition_at_565


theorem disposition_interval_566 : Interval dispositionTest 566 567 := by
  intro i hlo hhi
  have h : i = 566 := by omega
  subst i
  exact disposition_at_566


theorem disposition_interval_567 : Interval dispositionTest 567 568 := by
  intro i hlo hhi
  have h : i = 567 := by omega
  subst i
  exact disposition_at_567


theorem disposition_interval_568 : Interval dispositionTest 568 569 := by
  intro i hlo hhi
  have h : i = 568 := by omega
  subst i
  exact disposition_at_568


theorem disposition_interval_569 : Interval dispositionTest 569 570 := by
  intro i hlo hhi
  have h : i = 569 := by omega
  subst i
  exact disposition_at_569


theorem disposition_interval_570 : Interval dispositionTest 570 571 := by
  intro i hlo hhi
  have h : i = 570 := by omega
  subst i
  exact disposition_at_570


theorem disposition_interval_571 : Interval dispositionTest 571 572 := by
  intro i hlo hhi
  have h : i = 571 := by omega
  subst i
  exact disposition_at_571


theorem disposition_interval_572 : Interval dispositionTest 572 573 := by
  intro i hlo hhi
  have h : i = 572 := by omega
  subst i
  exact disposition_at_572


theorem disposition_interval_573 : Interval dispositionTest 573 574 := by
  intro i hlo hhi
  have h : i = 573 := by omega
  subst i
  exact disposition_at_573


theorem disposition_interval_574 : Interval dispositionTest 574 575 := by
  intro i hlo hhi
  have h : i = 574 := by omega
  subst i
  exact disposition_at_574


theorem disposition_interval_575 : Interval dispositionTest 575 576 := by
  intro i hlo hhi
  have h : i = 575 := by omega
  subst i
  exact disposition_at_575

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0353
