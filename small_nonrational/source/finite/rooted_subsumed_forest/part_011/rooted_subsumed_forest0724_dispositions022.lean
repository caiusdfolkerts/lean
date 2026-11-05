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
theorem disposition_at_704 : dispositionTest 704 = true := by decide +kernel

theorem disposition_at_705 : dispositionTest 705 = true := by decide +kernel

theorem disposition_at_706 : dispositionTest 706 = true := by decide +kernel

theorem disposition_at_707 : dispositionTest 707 = true := by decide +kernel

theorem disposition_at_708 : dispositionTest 708 = true := by decide +kernel

theorem disposition_at_709 : dispositionTest 709 = true := by decide +kernel

theorem disposition_at_710 : dispositionTest 710 = true := by decide +kernel

theorem disposition_at_711 : dispositionTest 711 = true := by decide +kernel

theorem disposition_at_712 : dispositionTest 712 = true := by decide +kernel

theorem disposition_at_713 : dispositionTest 713 = true := by decide +kernel

theorem disposition_at_714 : dispositionTest 714 = true := by decide +kernel

theorem disposition_at_715 : dispositionTest 715 = true := by decide +kernel

theorem disposition_at_716 : dispositionTest 716 = true := by decide +kernel

theorem disposition_at_717 : dispositionTest 717 = true := by decide +kernel

theorem disposition_at_718 : dispositionTest 718 = true := by decide +kernel

theorem disposition_at_719 : dispositionTest 719 = true := by decide +kernel

theorem disposition_at_720 : dispositionTest 720 = true := by decide +kernel

theorem disposition_at_721 : dispositionTest 721 = true := by decide +kernel

theorem disposition_at_722 : dispositionTest 722 = true := by decide +kernel

theorem disposition_at_723 : dispositionTest 723 = true := by decide +kernel

theorem disposition_at_724 : dispositionTest 724 = true := by decide +kernel

theorem disposition_at_725 : dispositionTest 725 = true := by decide +kernel

theorem disposition_at_726 : dispositionTest 726 = true := by decide +kernel

theorem disposition_at_727 : dispositionTest 727 = true := by decide +kernel

theorem disposition_at_728 : dispositionTest 728 = true := by decide +kernel

theorem disposition_at_729 : dispositionTest 729 = true := by decide +kernel

theorem disposition_at_730 : dispositionTest 730 = true := by decide +kernel

theorem disposition_at_731 : dispositionTest 731 = true := by decide +kernel

theorem disposition_at_732 : dispositionTest 732 = true := by decide +kernel

theorem disposition_at_733 : dispositionTest 733 = true := by decide +kernel

theorem disposition_at_734 : dispositionTest 734 = true := by decide +kernel

theorem disposition_at_735 : dispositionTest 735 = true := by decide +kernel

theorem disposition_interval_704 : Interval dispositionTest 704 705 := by
  intro i hlo hhi
  have h : i = 704 := by omega
  subst i
  exact disposition_at_704


theorem disposition_interval_705 : Interval dispositionTest 705 706 := by
  intro i hlo hhi
  have h : i = 705 := by omega
  subst i
  exact disposition_at_705


theorem disposition_interval_706 : Interval dispositionTest 706 707 := by
  intro i hlo hhi
  have h : i = 706 := by omega
  subst i
  exact disposition_at_706


theorem disposition_interval_707 : Interval dispositionTest 707 708 := by
  intro i hlo hhi
  have h : i = 707 := by omega
  subst i
  exact disposition_at_707


theorem disposition_interval_708 : Interval dispositionTest 708 709 := by
  intro i hlo hhi
  have h : i = 708 := by omega
  subst i
  exact disposition_at_708


theorem disposition_interval_709 : Interval dispositionTest 709 710 := by
  intro i hlo hhi
  have h : i = 709 := by omega
  subst i
  exact disposition_at_709


theorem disposition_interval_710 : Interval dispositionTest 710 711 := by
  intro i hlo hhi
  have h : i = 710 := by omega
  subst i
  exact disposition_at_710


theorem disposition_interval_711 : Interval dispositionTest 711 712 := by
  intro i hlo hhi
  have h : i = 711 := by omega
  subst i
  exact disposition_at_711


theorem disposition_interval_712 : Interval dispositionTest 712 713 := by
  intro i hlo hhi
  have h : i = 712 := by omega
  subst i
  exact disposition_at_712


theorem disposition_interval_713 : Interval dispositionTest 713 714 := by
  intro i hlo hhi
  have h : i = 713 := by omega
  subst i
  exact disposition_at_713


theorem disposition_interval_714 : Interval dispositionTest 714 715 := by
  intro i hlo hhi
  have h : i = 714 := by omega
  subst i
  exact disposition_at_714


theorem disposition_interval_715 : Interval dispositionTest 715 716 := by
  intro i hlo hhi
  have h : i = 715 := by omega
  subst i
  exact disposition_at_715


theorem disposition_interval_716 : Interval dispositionTest 716 717 := by
  intro i hlo hhi
  have h : i = 716 := by omega
  subst i
  exact disposition_at_716


theorem disposition_interval_717 : Interval dispositionTest 717 718 := by
  intro i hlo hhi
  have h : i = 717 := by omega
  subst i
  exact disposition_at_717


theorem disposition_interval_718 : Interval dispositionTest 718 719 := by
  intro i hlo hhi
  have h : i = 718 := by omega
  subst i
  exact disposition_at_718


theorem disposition_interval_719 : Interval dispositionTest 719 720 := by
  intro i hlo hhi
  have h : i = 719 := by omega
  subst i
  exact disposition_at_719


theorem disposition_interval_720 : Interval dispositionTest 720 721 := by
  intro i hlo hhi
  have h : i = 720 := by omega
  subst i
  exact disposition_at_720


theorem disposition_interval_721 : Interval dispositionTest 721 722 := by
  intro i hlo hhi
  have h : i = 721 := by omega
  subst i
  exact disposition_at_721


theorem disposition_interval_722 : Interval dispositionTest 722 723 := by
  intro i hlo hhi
  have h : i = 722 := by omega
  subst i
  exact disposition_at_722


theorem disposition_interval_723 : Interval dispositionTest 723 724 := by
  intro i hlo hhi
  have h : i = 723 := by omega
  subst i
  exact disposition_at_723


theorem disposition_interval_724 : Interval dispositionTest 724 725 := by
  intro i hlo hhi
  have h : i = 724 := by omega
  subst i
  exact disposition_at_724


theorem disposition_interval_725 : Interval dispositionTest 725 726 := by
  intro i hlo hhi
  have h : i = 725 := by omega
  subst i
  exact disposition_at_725


theorem disposition_interval_726 : Interval dispositionTest 726 727 := by
  intro i hlo hhi
  have h : i = 726 := by omega
  subst i
  exact disposition_at_726


theorem disposition_interval_727 : Interval dispositionTest 727 728 := by
  intro i hlo hhi
  have h : i = 727 := by omega
  subst i
  exact disposition_at_727


theorem disposition_interval_728 : Interval dispositionTest 728 729 := by
  intro i hlo hhi
  have h : i = 728 := by omega
  subst i
  exact disposition_at_728


theorem disposition_interval_729 : Interval dispositionTest 729 730 := by
  intro i hlo hhi
  have h : i = 729 := by omega
  subst i
  exact disposition_at_729


theorem disposition_interval_730 : Interval dispositionTest 730 731 := by
  intro i hlo hhi
  have h : i = 730 := by omega
  subst i
  exact disposition_at_730


theorem disposition_interval_731 : Interval dispositionTest 731 732 := by
  intro i hlo hhi
  have h : i = 731 := by omega
  subst i
  exact disposition_at_731


theorem disposition_interval_732 : Interval dispositionTest 732 733 := by
  intro i hlo hhi
  have h : i = 732 := by omega
  subst i
  exact disposition_at_732


theorem disposition_interval_733 : Interval dispositionTest 733 734 := by
  intro i hlo hhi
  have h : i = 733 := by omega
  subst i
  exact disposition_at_733


theorem disposition_interval_734 : Interval dispositionTest 734 735 := by
  intro i hlo hhi
  have h : i = 734 := by omega
  subst i
  exact disposition_at_734


theorem disposition_interval_735 : Interval dispositionTest 735 736 := by
  intro i hlo hhi
  have h : i = 735 := by omega
  subst i
  exact disposition_at_735

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
