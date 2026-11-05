module
prelude
public import RootedSubsumedForest0724DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_672 : dispositionTest 672 = true := by decide +kernel

theorem disposition_at_673 : dispositionTest 673 = true := by decide +kernel

theorem disposition_at_674 : dispositionTest 674 = true := by decide +kernel

theorem disposition_at_675 : dispositionTest 675 = true := by decide +kernel

theorem disposition_at_676 : dispositionTest 676 = true := by decide +kernel

theorem disposition_at_677 : dispositionTest 677 = true := by decide +kernel

theorem disposition_at_678 : dispositionTest 678 = true := by decide +kernel

theorem disposition_at_679 : dispositionTest 679 = true := by decide +kernel

theorem disposition_at_680 : dispositionTest 680 = true := by decide +kernel

theorem disposition_at_681 : dispositionTest 681 = true := by decide +kernel

theorem disposition_at_682 : dispositionTest 682 = true := by decide +kernel

theorem disposition_at_683 : dispositionTest 683 = true := by decide +kernel

theorem disposition_at_684 : dispositionTest 684 = true := by decide +kernel


theorem disposition_at_685 : dispositionTest 685 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 685).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M023.r1498.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M023.r1498) = true
  rw [Nonrational.OldTerminalMatches.M023.r1498_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_686 : dispositionTest 686 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 686).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M023.r1499.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M023.r1499) = true
  rw [Nonrational.OldTerminalMatches.M023.r1499_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_687 : dispositionTest 687 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 687).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M023.r1500.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M023.r1500) = true
  rw [Nonrational.OldTerminalMatches.M023.r1500_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_688 : dispositionTest 688 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 688).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M023.r1501.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M023.r1501) = true
  rw [Nonrational.OldTerminalMatches.M023.r1501_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_689 : dispositionTest 689 = true := by decide +kernel

theorem disposition_at_690 : dispositionTest 690 = true := by decide +kernel

theorem disposition_at_691 : dispositionTest 691 = true := by decide +kernel

theorem disposition_at_692 : dispositionTest 692 = true := by decide +kernel

theorem disposition_at_693 : dispositionTest 693 = true := by decide +kernel

theorem disposition_at_694 : dispositionTest 694 = true := by decide +kernel

theorem disposition_at_695 : dispositionTest 695 = true := by decide +kernel

theorem disposition_at_696 : dispositionTest 696 = true := by decide +kernel

theorem disposition_at_697 : dispositionTest 697 = true := by decide +kernel

theorem disposition_at_698 : dispositionTest 698 = true := by decide +kernel

theorem disposition_at_699 : dispositionTest 699 = true := by decide +kernel

theorem disposition_at_700 : dispositionTest 700 = true := by decide +kernel

theorem disposition_at_701 : dispositionTest 701 = true := by decide +kernel

theorem disposition_at_702 : dispositionTest 702 = true := by decide +kernel

theorem disposition_at_703 : dispositionTest 703 = true := by decide +kernel

theorem disposition_interval_672 : Interval dispositionTest 672 673 := by
  intro i hlo hhi
  have h : i = 672 := by omega
  subst i
  exact disposition_at_672


theorem disposition_interval_673 : Interval dispositionTest 673 674 := by
  intro i hlo hhi
  have h : i = 673 := by omega
  subst i
  exact disposition_at_673


theorem disposition_interval_674 : Interval dispositionTest 674 675 := by
  intro i hlo hhi
  have h : i = 674 := by omega
  subst i
  exact disposition_at_674


theorem disposition_interval_675 : Interval dispositionTest 675 676 := by
  intro i hlo hhi
  have h : i = 675 := by omega
  subst i
  exact disposition_at_675


theorem disposition_interval_676 : Interval dispositionTest 676 677 := by
  intro i hlo hhi
  have h : i = 676 := by omega
  subst i
  exact disposition_at_676


theorem disposition_interval_677 : Interval dispositionTest 677 678 := by
  intro i hlo hhi
  have h : i = 677 := by omega
  subst i
  exact disposition_at_677


theorem disposition_interval_678 : Interval dispositionTest 678 679 := by
  intro i hlo hhi
  have h : i = 678 := by omega
  subst i
  exact disposition_at_678


theorem disposition_interval_679 : Interval dispositionTest 679 680 := by
  intro i hlo hhi
  have h : i = 679 := by omega
  subst i
  exact disposition_at_679


theorem disposition_interval_680 : Interval dispositionTest 680 681 := by
  intro i hlo hhi
  have h : i = 680 := by omega
  subst i
  exact disposition_at_680


theorem disposition_interval_681 : Interval dispositionTest 681 682 := by
  intro i hlo hhi
  have h : i = 681 := by omega
  subst i
  exact disposition_at_681


theorem disposition_interval_682 : Interval dispositionTest 682 683 := by
  intro i hlo hhi
  have h : i = 682 := by omega
  subst i
  exact disposition_at_682


theorem disposition_interval_683 : Interval dispositionTest 683 684 := by
  intro i hlo hhi
  have h : i = 683 := by omega
  subst i
  exact disposition_at_683


theorem disposition_interval_684 : Interval dispositionTest 684 685 := by
  intro i hlo hhi
  have h : i = 684 := by omega
  subst i
  exact disposition_at_684


theorem disposition_interval_685 : Interval dispositionTest 685 686 := by
  intro i hlo hhi
  have h : i = 685 := by omega
  subst i
  exact disposition_at_685


theorem disposition_interval_686 : Interval dispositionTest 686 687 := by
  intro i hlo hhi
  have h : i = 686 := by omega
  subst i
  exact disposition_at_686


theorem disposition_interval_687 : Interval dispositionTest 687 688 := by
  intro i hlo hhi
  have h : i = 687 := by omega
  subst i
  exact disposition_at_687


theorem disposition_interval_688 : Interval dispositionTest 688 689 := by
  intro i hlo hhi
  have h : i = 688 := by omega
  subst i
  exact disposition_at_688


theorem disposition_interval_689 : Interval dispositionTest 689 690 := by
  intro i hlo hhi
  have h : i = 689 := by omega
  subst i
  exact disposition_at_689


theorem disposition_interval_690 : Interval dispositionTest 690 691 := by
  intro i hlo hhi
  have h : i = 690 := by omega
  subst i
  exact disposition_at_690


theorem disposition_interval_691 : Interval dispositionTest 691 692 := by
  intro i hlo hhi
  have h : i = 691 := by omega
  subst i
  exact disposition_at_691


theorem disposition_interval_692 : Interval dispositionTest 692 693 := by
  intro i hlo hhi
  have h : i = 692 := by omega
  subst i
  exact disposition_at_692


theorem disposition_interval_693 : Interval dispositionTest 693 694 := by
  intro i hlo hhi
  have h : i = 693 := by omega
  subst i
  exact disposition_at_693


theorem disposition_interval_694 : Interval dispositionTest 694 695 := by
  intro i hlo hhi
  have h : i = 694 := by omega
  subst i
  exact disposition_at_694


theorem disposition_interval_695 : Interval dispositionTest 695 696 := by
  intro i hlo hhi
  have h : i = 695 := by omega
  subst i
  exact disposition_at_695


theorem disposition_interval_696 : Interval dispositionTest 696 697 := by
  intro i hlo hhi
  have h : i = 696 := by omega
  subst i
  exact disposition_at_696


theorem disposition_interval_697 : Interval dispositionTest 697 698 := by
  intro i hlo hhi
  have h : i = 697 := by omega
  subst i
  exact disposition_at_697


theorem disposition_interval_698 : Interval dispositionTest 698 699 := by
  intro i hlo hhi
  have h : i = 698 := by omega
  subst i
  exact disposition_at_698


theorem disposition_interval_699 : Interval dispositionTest 699 700 := by
  intro i hlo hhi
  have h : i = 699 := by omega
  subst i
  exact disposition_at_699


theorem disposition_interval_700 : Interval dispositionTest 700 701 := by
  intro i hlo hhi
  have h : i = 700 := by omega
  subst i
  exact disposition_at_700


theorem disposition_interval_701 : Interval dispositionTest 701 702 := by
  intro i hlo hhi
  have h : i = 701 := by omega
  subst i
  exact disposition_at_701


theorem disposition_interval_702 : Interval dispositionTest 702 703 := by
  intro i hlo hhi
  have h : i = 702 := by omega
  subst i
  exact disposition_at_702


theorem disposition_interval_703 : Interval dispositionTest 703 704 := by
  intro i hlo hhi
  have h : i = 703 := by omega
  subst i
  exact disposition_at_703

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
