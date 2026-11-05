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
theorem disposition_at_832 : dispositionTest 832 = true := by decide +kernel

theorem disposition_at_833 : dispositionTest 833 = true := by decide +kernel

theorem disposition_at_834 : dispositionTest 834 = true := by decide +kernel

theorem disposition_at_835 : dispositionTest 835 = true := by decide +kernel

theorem disposition_at_836 : dispositionTest 836 = true := by decide +kernel

theorem disposition_at_837 : dispositionTest 837 = true := by decide +kernel

theorem disposition_at_838 : dispositionTest 838 = true := by decide +kernel

theorem disposition_at_839 : dispositionTest 839 = true := by decide +kernel

theorem disposition_at_840 : dispositionTest 840 = true := by decide +kernel

theorem disposition_at_841 : dispositionTest 841 = true := by decide +kernel

theorem disposition_at_842 : dispositionTest 842 = true := by decide +kernel

theorem disposition_at_843 : dispositionTest 843 = true := by decide +kernel

theorem disposition_at_844 : dispositionTest 844 = true := by decide +kernel

theorem disposition_at_845 : dispositionTest 845 = true := by decide +kernel

theorem disposition_at_846 : dispositionTest 846 = true := by decide +kernel

theorem disposition_at_847 : dispositionTest 847 = true := by decide +kernel

theorem disposition_at_848 : dispositionTest 848 = true := by decide +kernel

theorem disposition_at_849 : dispositionTest 849 = true := by decide +kernel

theorem disposition_at_850 : dispositionTest 850 = true := by decide +kernel

theorem disposition_at_851 : dispositionTest 851 = true := by decide +kernel

theorem disposition_at_852 : dispositionTest 852 = true := by decide +kernel


theorem disposition_at_853 : dispositionTest 853 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 853).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M015.r0973.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M015.r0973) = true
  rw [Nonrational.OldTerminalMatches.M015.r0973_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_854 : dispositionTest 854 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 854).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M015.r0974.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M015.r0974) = true
  rw [Nonrational.OldTerminalMatches.M015.r0974_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_855 : dispositionTest 855 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 855).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M015.r0975.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M015.r0975) = true
  rw [Nonrational.OldTerminalMatches.M015.r0975_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_856 : dispositionTest 856 = true := by decide +kernel

theorem disposition_at_857 : dispositionTest 857 = true := by decide +kernel


theorem disposition_at_858 : dispositionTest 858 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 858).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M015.r0976.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M015.r0976) = true
  rw [Nonrational.OldTerminalMatches.M015.r0976_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_859 : dispositionTest 859 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 859).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M015.r0977.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M015.r0977) = true
  rw [Nonrational.OldTerminalMatches.M015.r0977_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_860 : dispositionTest 860 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 860).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M015.r0978.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M015.r0978) = true
  rw [Nonrational.OldTerminalMatches.M015.r0978_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_861 : dispositionTest 861 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 861).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M015.r0979.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M015.r0979) = true
  rw [Nonrational.OldTerminalMatches.M015.r0979_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_862 : dispositionTest 862 = true := by decide +kernel

theorem disposition_at_863 : dispositionTest 863 = true := by decide +kernel

theorem disposition_interval_832 : Interval dispositionTest 832 833 := by
  intro i hlo hhi
  have h : i = 832 := by omega
  subst i
  exact disposition_at_832


theorem disposition_interval_833 : Interval dispositionTest 833 834 := by
  intro i hlo hhi
  have h : i = 833 := by omega
  subst i
  exact disposition_at_833


theorem disposition_interval_834 : Interval dispositionTest 834 835 := by
  intro i hlo hhi
  have h : i = 834 := by omega
  subst i
  exact disposition_at_834


theorem disposition_interval_835 : Interval dispositionTest 835 836 := by
  intro i hlo hhi
  have h : i = 835 := by omega
  subst i
  exact disposition_at_835


theorem disposition_interval_836 : Interval dispositionTest 836 837 := by
  intro i hlo hhi
  have h : i = 836 := by omega
  subst i
  exact disposition_at_836


theorem disposition_interval_837 : Interval dispositionTest 837 838 := by
  intro i hlo hhi
  have h : i = 837 := by omega
  subst i
  exact disposition_at_837


theorem disposition_interval_838 : Interval dispositionTest 838 839 := by
  intro i hlo hhi
  have h : i = 838 := by omega
  subst i
  exact disposition_at_838


theorem disposition_interval_839 : Interval dispositionTest 839 840 := by
  intro i hlo hhi
  have h : i = 839 := by omega
  subst i
  exact disposition_at_839


theorem disposition_interval_840 : Interval dispositionTest 840 841 := by
  intro i hlo hhi
  have h : i = 840 := by omega
  subst i
  exact disposition_at_840


theorem disposition_interval_841 : Interval dispositionTest 841 842 := by
  intro i hlo hhi
  have h : i = 841 := by omega
  subst i
  exact disposition_at_841


theorem disposition_interval_842 : Interval dispositionTest 842 843 := by
  intro i hlo hhi
  have h : i = 842 := by omega
  subst i
  exact disposition_at_842


theorem disposition_interval_843 : Interval dispositionTest 843 844 := by
  intro i hlo hhi
  have h : i = 843 := by omega
  subst i
  exact disposition_at_843


theorem disposition_interval_844 : Interval dispositionTest 844 845 := by
  intro i hlo hhi
  have h : i = 844 := by omega
  subst i
  exact disposition_at_844


theorem disposition_interval_845 : Interval dispositionTest 845 846 := by
  intro i hlo hhi
  have h : i = 845 := by omega
  subst i
  exact disposition_at_845


theorem disposition_interval_846 : Interval dispositionTest 846 847 := by
  intro i hlo hhi
  have h : i = 846 := by omega
  subst i
  exact disposition_at_846


theorem disposition_interval_847 : Interval dispositionTest 847 848 := by
  intro i hlo hhi
  have h : i = 847 := by omega
  subst i
  exact disposition_at_847


theorem disposition_interval_848 : Interval dispositionTest 848 849 := by
  intro i hlo hhi
  have h : i = 848 := by omega
  subst i
  exact disposition_at_848


theorem disposition_interval_849 : Interval dispositionTest 849 850 := by
  intro i hlo hhi
  have h : i = 849 := by omega
  subst i
  exact disposition_at_849


theorem disposition_interval_850 : Interval dispositionTest 850 851 := by
  intro i hlo hhi
  have h : i = 850 := by omega
  subst i
  exact disposition_at_850


theorem disposition_interval_851 : Interval dispositionTest 851 852 := by
  intro i hlo hhi
  have h : i = 851 := by omega
  subst i
  exact disposition_at_851


theorem disposition_interval_852 : Interval dispositionTest 852 853 := by
  intro i hlo hhi
  have h : i = 852 := by omega
  subst i
  exact disposition_at_852


theorem disposition_interval_853 : Interval dispositionTest 853 854 := by
  intro i hlo hhi
  have h : i = 853 := by omega
  subst i
  exact disposition_at_853


theorem disposition_interval_854 : Interval dispositionTest 854 855 := by
  intro i hlo hhi
  have h : i = 854 := by omega
  subst i
  exact disposition_at_854


theorem disposition_interval_855 : Interval dispositionTest 855 856 := by
  intro i hlo hhi
  have h : i = 855 := by omega
  subst i
  exact disposition_at_855


theorem disposition_interval_856 : Interval dispositionTest 856 857 := by
  intro i hlo hhi
  have h : i = 856 := by omega
  subst i
  exact disposition_at_856


theorem disposition_interval_857 : Interval dispositionTest 857 858 := by
  intro i hlo hhi
  have h : i = 857 := by omega
  subst i
  exact disposition_at_857


theorem disposition_interval_858 : Interval dispositionTest 858 859 := by
  intro i hlo hhi
  have h : i = 858 := by omega
  subst i
  exact disposition_at_858


theorem disposition_interval_859 : Interval dispositionTest 859 860 := by
  intro i hlo hhi
  have h : i = 859 := by omega
  subst i
  exact disposition_at_859


theorem disposition_interval_860 : Interval dispositionTest 860 861 := by
  intro i hlo hhi
  have h : i = 860 := by omega
  subst i
  exact disposition_at_860


theorem disposition_interval_861 : Interval dispositionTest 861 862 := by
  intro i hlo hhi
  have h : i = 861 := by omega
  subst i
  exact disposition_at_861


theorem disposition_interval_862 : Interval dispositionTest 862 863 := by
  intro i hlo hhi
  have h : i = 862 := by omega
  subst i
  exact disposition_at_862


theorem disposition_interval_863 : Interval dispositionTest 863 864 := by
  intro i hlo hhi
  have h : i = 863 := by omega
  subst i
  exact disposition_at_863

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
