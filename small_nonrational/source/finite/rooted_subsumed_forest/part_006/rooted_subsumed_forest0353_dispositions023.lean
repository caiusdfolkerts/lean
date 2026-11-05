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
theorem disposition_at_736 : dispositionTest 736 = true := by decide +kernel

theorem disposition_at_737 : dispositionTest 737 = true := by decide +kernel

theorem disposition_at_738 : dispositionTest 738 = true := by decide +kernel

theorem disposition_at_739 : dispositionTest 739 = true := by decide +kernel

theorem disposition_at_740 : dispositionTest 740 = true := by decide +kernel

theorem disposition_at_741 : dispositionTest 741 = true := by decide +kernel


theorem disposition_at_742 : dispositionTest 742 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 742).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M014.r0943.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M014.r0943) = true
  rw [Nonrational.OldTerminalMatches.M014.r0943_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_743 : dispositionTest 743 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 743).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M014.r0944.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M014.r0944) = true
  rw [Nonrational.OldTerminalMatches.M014.r0944_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_744 : dispositionTest 744 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 744).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M014.r0945.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M014.r0945) = true
  rw [Nonrational.OldTerminalMatches.M014.r0945_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_745 : dispositionTest 745 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 745).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M014.r0946.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M014.r0946) = true
  rw [Nonrational.OldTerminalMatches.M014.r0946_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_746 : dispositionTest 746 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 746).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M014.r0947.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M014.r0947) = true
  rw [Nonrational.OldTerminalMatches.M014.r0947_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_747 : dispositionTest 747 = true := by decide +kernel

theorem disposition_at_748 : dispositionTest 748 = true := by decide +kernel

theorem disposition_at_749 : dispositionTest 749 = true := by decide +kernel

theorem disposition_at_750 : dispositionTest 750 = true := by decide +kernel

theorem disposition_at_751 : dispositionTest 751 = true := by decide +kernel


theorem disposition_at_752 : dispositionTest 752 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 752).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M014.r0948.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M014.r0948) = true
  rw [Nonrational.OldTerminalMatches.M014.r0948_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_753 : dispositionTest 753 = true := by decide +kernel


theorem disposition_at_754 : dispositionTest 754 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 754).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M014.r0949.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M014.r0949) = true
  rw [Nonrational.OldTerminalMatches.M014.r0949_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_755 : dispositionTest 755 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 755).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M014.r0950.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M014.r0950) = true
  rw [Nonrational.OldTerminalMatches.M014.r0950_checked, Bool.and_true]
  decide +kernel

theorem disposition_interval_736 : Interval dispositionTest 736 737 := by
  intro i hlo hhi
  have h : i = 736 := by omega
  subst i
  exact disposition_at_736


theorem disposition_interval_737 : Interval dispositionTest 737 738 := by
  intro i hlo hhi
  have h : i = 737 := by omega
  subst i
  exact disposition_at_737


theorem disposition_interval_738 : Interval dispositionTest 738 739 := by
  intro i hlo hhi
  have h : i = 738 := by omega
  subst i
  exact disposition_at_738


theorem disposition_interval_739 : Interval dispositionTest 739 740 := by
  intro i hlo hhi
  have h : i = 739 := by omega
  subst i
  exact disposition_at_739


theorem disposition_interval_740 : Interval dispositionTest 740 741 := by
  intro i hlo hhi
  have h : i = 740 := by omega
  subst i
  exact disposition_at_740


theorem disposition_interval_741 : Interval dispositionTest 741 742 := by
  intro i hlo hhi
  have h : i = 741 := by omega
  subst i
  exact disposition_at_741


theorem disposition_interval_742 : Interval dispositionTest 742 743 := by
  intro i hlo hhi
  have h : i = 742 := by omega
  subst i
  exact disposition_at_742


theorem disposition_interval_743 : Interval dispositionTest 743 744 := by
  intro i hlo hhi
  have h : i = 743 := by omega
  subst i
  exact disposition_at_743


theorem disposition_interval_744 : Interval dispositionTest 744 745 := by
  intro i hlo hhi
  have h : i = 744 := by omega
  subst i
  exact disposition_at_744


theorem disposition_interval_745 : Interval dispositionTest 745 746 := by
  intro i hlo hhi
  have h : i = 745 := by omega
  subst i
  exact disposition_at_745


theorem disposition_interval_746 : Interval dispositionTest 746 747 := by
  intro i hlo hhi
  have h : i = 746 := by omega
  subst i
  exact disposition_at_746


theorem disposition_interval_747 : Interval dispositionTest 747 748 := by
  intro i hlo hhi
  have h : i = 747 := by omega
  subst i
  exact disposition_at_747


theorem disposition_interval_748 : Interval dispositionTest 748 749 := by
  intro i hlo hhi
  have h : i = 748 := by omega
  subst i
  exact disposition_at_748


theorem disposition_interval_749 : Interval dispositionTest 749 750 := by
  intro i hlo hhi
  have h : i = 749 := by omega
  subst i
  exact disposition_at_749


theorem disposition_interval_750 : Interval dispositionTest 750 751 := by
  intro i hlo hhi
  have h : i = 750 := by omega
  subst i
  exact disposition_at_750


theorem disposition_interval_751 : Interval dispositionTest 751 752 := by
  intro i hlo hhi
  have h : i = 751 := by omega
  subst i
  exact disposition_at_751


theorem disposition_interval_752 : Interval dispositionTest 752 753 := by
  intro i hlo hhi
  have h : i = 752 := by omega
  subst i
  exact disposition_at_752


theorem disposition_interval_753 : Interval dispositionTest 753 754 := by
  intro i hlo hhi
  have h : i = 753 := by omega
  subst i
  exact disposition_at_753


theorem disposition_interval_754 : Interval dispositionTest 754 755 := by
  intro i hlo hhi
  have h : i = 754 := by omega
  subst i
  exact disposition_at_754


theorem disposition_interval_755 : Interval dispositionTest 755 756 := by
  intro i hlo hhi
  have h : i = 755 := by omega
  subst i
  exact disposition_at_755

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0353
