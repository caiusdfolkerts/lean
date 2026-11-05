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
theorem disposition_at_640 : dispositionTest 640 = true := by decide +kernel

theorem disposition_at_641 : dispositionTest 641 = true := by decide +kernel

theorem disposition_at_642 : dispositionTest 642 = true := by decide +kernel

theorem disposition_at_643 : dispositionTest 643 = true := by decide +kernel

theorem disposition_at_644 : dispositionTest 644 = true := by decide +kernel

theorem disposition_at_645 : dispositionTest 645 = true := by decide +kernel

theorem disposition_at_646 : dispositionTest 646 = true := by decide +kernel

theorem disposition_at_647 : dispositionTest 647 = true := by decide +kernel

theorem disposition_at_648 : dispositionTest 648 = true := by decide +kernel

theorem disposition_at_649 : dispositionTest 649 = true := by decide +kernel

theorem disposition_at_650 : dispositionTest 650 = true := by decide +kernel

theorem disposition_at_651 : dispositionTest 651 = true := by decide +kernel

theorem disposition_at_652 : dispositionTest 652 = true := by decide +kernel

theorem disposition_at_653 : dispositionTest 653 = true := by decide +kernel

theorem disposition_at_654 : dispositionTest 654 = true := by decide +kernel

theorem disposition_at_655 : dispositionTest 655 = true := by decide +kernel

theorem disposition_at_656 : dispositionTest 656 = true := by decide +kernel

theorem disposition_at_657 : dispositionTest 657 = true := by decide +kernel

theorem disposition_at_658 : dispositionTest 658 = true := by decide +kernel

theorem disposition_at_659 : dispositionTest 659 = true := by decide +kernel

theorem disposition_at_660 : dispositionTest 660 = true := by decide +kernel

theorem disposition_at_661 : dispositionTest 661 = true := by decide +kernel

theorem disposition_at_662 : dispositionTest 662 = true := by decide +kernel

theorem disposition_at_663 : dispositionTest 663 = true := by decide +kernel

theorem disposition_at_664 : dispositionTest 664 = true := by decide +kernel

theorem disposition_at_665 : dispositionTest 665 = true := by decide +kernel

theorem disposition_at_666 : dispositionTest 666 = true := by decide +kernel

theorem disposition_at_667 : dispositionTest 667 = true := by decide +kernel


theorem disposition_at_668 : dispositionTest 668 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 668).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M014.r0921.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M014.r0921) = true
  rw [Nonrational.OldTerminalMatches.M014.r0921_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_669 : dispositionTest 669 = true := by decide +kernel

theorem disposition_at_670 : dispositionTest 670 = true := by decide +kernel

theorem disposition_at_671 : dispositionTest 671 = true := by decide +kernel

theorem disposition_interval_640 : Interval dispositionTest 640 641 := by
  intro i hlo hhi
  have h : i = 640 := by omega
  subst i
  exact disposition_at_640


theorem disposition_interval_641 : Interval dispositionTest 641 642 := by
  intro i hlo hhi
  have h : i = 641 := by omega
  subst i
  exact disposition_at_641


theorem disposition_interval_642 : Interval dispositionTest 642 643 := by
  intro i hlo hhi
  have h : i = 642 := by omega
  subst i
  exact disposition_at_642


theorem disposition_interval_643 : Interval dispositionTest 643 644 := by
  intro i hlo hhi
  have h : i = 643 := by omega
  subst i
  exact disposition_at_643


theorem disposition_interval_644 : Interval dispositionTest 644 645 := by
  intro i hlo hhi
  have h : i = 644 := by omega
  subst i
  exact disposition_at_644


theorem disposition_interval_645 : Interval dispositionTest 645 646 := by
  intro i hlo hhi
  have h : i = 645 := by omega
  subst i
  exact disposition_at_645


theorem disposition_interval_646 : Interval dispositionTest 646 647 := by
  intro i hlo hhi
  have h : i = 646 := by omega
  subst i
  exact disposition_at_646


theorem disposition_interval_647 : Interval dispositionTest 647 648 := by
  intro i hlo hhi
  have h : i = 647 := by omega
  subst i
  exact disposition_at_647


theorem disposition_interval_648 : Interval dispositionTest 648 649 := by
  intro i hlo hhi
  have h : i = 648 := by omega
  subst i
  exact disposition_at_648


theorem disposition_interval_649 : Interval dispositionTest 649 650 := by
  intro i hlo hhi
  have h : i = 649 := by omega
  subst i
  exact disposition_at_649


theorem disposition_interval_650 : Interval dispositionTest 650 651 := by
  intro i hlo hhi
  have h : i = 650 := by omega
  subst i
  exact disposition_at_650


theorem disposition_interval_651 : Interval dispositionTest 651 652 := by
  intro i hlo hhi
  have h : i = 651 := by omega
  subst i
  exact disposition_at_651


theorem disposition_interval_652 : Interval dispositionTest 652 653 := by
  intro i hlo hhi
  have h : i = 652 := by omega
  subst i
  exact disposition_at_652


theorem disposition_interval_653 : Interval dispositionTest 653 654 := by
  intro i hlo hhi
  have h : i = 653 := by omega
  subst i
  exact disposition_at_653


theorem disposition_interval_654 : Interval dispositionTest 654 655 := by
  intro i hlo hhi
  have h : i = 654 := by omega
  subst i
  exact disposition_at_654


theorem disposition_interval_655 : Interval dispositionTest 655 656 := by
  intro i hlo hhi
  have h : i = 655 := by omega
  subst i
  exact disposition_at_655


theorem disposition_interval_656 : Interval dispositionTest 656 657 := by
  intro i hlo hhi
  have h : i = 656 := by omega
  subst i
  exact disposition_at_656


theorem disposition_interval_657 : Interval dispositionTest 657 658 := by
  intro i hlo hhi
  have h : i = 657 := by omega
  subst i
  exact disposition_at_657


theorem disposition_interval_658 : Interval dispositionTest 658 659 := by
  intro i hlo hhi
  have h : i = 658 := by omega
  subst i
  exact disposition_at_658


theorem disposition_interval_659 : Interval dispositionTest 659 660 := by
  intro i hlo hhi
  have h : i = 659 := by omega
  subst i
  exact disposition_at_659


theorem disposition_interval_660 : Interval dispositionTest 660 661 := by
  intro i hlo hhi
  have h : i = 660 := by omega
  subst i
  exact disposition_at_660


theorem disposition_interval_661 : Interval dispositionTest 661 662 := by
  intro i hlo hhi
  have h : i = 661 := by omega
  subst i
  exact disposition_at_661


theorem disposition_interval_662 : Interval dispositionTest 662 663 := by
  intro i hlo hhi
  have h : i = 662 := by omega
  subst i
  exact disposition_at_662


theorem disposition_interval_663 : Interval dispositionTest 663 664 := by
  intro i hlo hhi
  have h : i = 663 := by omega
  subst i
  exact disposition_at_663


theorem disposition_interval_664 : Interval dispositionTest 664 665 := by
  intro i hlo hhi
  have h : i = 664 := by omega
  subst i
  exact disposition_at_664


theorem disposition_interval_665 : Interval dispositionTest 665 666 := by
  intro i hlo hhi
  have h : i = 665 := by omega
  subst i
  exact disposition_at_665


theorem disposition_interval_666 : Interval dispositionTest 666 667 := by
  intro i hlo hhi
  have h : i = 666 := by omega
  subst i
  exact disposition_at_666


theorem disposition_interval_667 : Interval dispositionTest 667 668 := by
  intro i hlo hhi
  have h : i = 667 := by omega
  subst i
  exact disposition_at_667


theorem disposition_interval_668 : Interval dispositionTest 668 669 := by
  intro i hlo hhi
  have h : i = 668 := by omega
  subst i
  exact disposition_at_668


theorem disposition_interval_669 : Interval dispositionTest 669 670 := by
  intro i hlo hhi
  have h : i = 669 := by omega
  subst i
  exact disposition_at_669


theorem disposition_interval_670 : Interval dispositionTest 670 671 := by
  intro i hlo hhi
  have h : i = 670 := by omega
  subst i
  exact disposition_at_670


theorem disposition_interval_671 : Interval dispositionTest 671 672 := by
  intro i hlo hhi
  have h : i = 671 := by omega
  subst i
  exact disposition_at_671

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0353
