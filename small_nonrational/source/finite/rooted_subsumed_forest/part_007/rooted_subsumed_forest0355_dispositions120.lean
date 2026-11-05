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
theorem disposition_at_3840 : dispositionTest 3840 = true := by decide +kernel

theorem disposition_at_3841 : dispositionTest 3841 = true := by decide +kernel

theorem disposition_at_3842 : dispositionTest 3842 = true := by decide +kernel

theorem disposition_at_3843 : dispositionTest 3843 = true := by decide +kernel

theorem disposition_at_3844 : dispositionTest 3844 = true := by decide +kernel

theorem disposition_at_3845 : dispositionTest 3845 = true := by decide +kernel

theorem disposition_at_3846 : dispositionTest 3846 = true := by decide +kernel

theorem disposition_at_3847 : dispositionTest 3847 = true := by decide +kernel

theorem disposition_at_3848 : dispositionTest 3848 = true := by decide +kernel

theorem disposition_at_3849 : dispositionTest 3849 = true := by decide +kernel

theorem disposition_at_3850 : dispositionTest 3850 = true := by decide +kernel

theorem disposition_at_3851 : dispositionTest 3851 = true := by decide +kernel

theorem disposition_at_3852 : dispositionTest 3852 = true := by decide +kernel

theorem disposition_at_3853 : dispositionTest 3853 = true := by decide +kernel

theorem disposition_at_3854 : dispositionTest 3854 = true := by decide +kernel

theorem disposition_at_3855 : dispositionTest 3855 = true := by decide +kernel

theorem disposition_at_3856 : dispositionTest 3856 = true := by decide +kernel

theorem disposition_at_3857 : dispositionTest 3857 = true := by decide +kernel

theorem disposition_at_3858 : dispositionTest 3858 = true := by decide +kernel

theorem disposition_at_3859 : dispositionTest 3859 = true := by decide +kernel

theorem disposition_at_3860 : dispositionTest 3860 = true := by decide +kernel

theorem disposition_at_3861 : dispositionTest 3861 = true := by decide +kernel

theorem disposition_at_3862 : dispositionTest 3862 = true := by decide +kernel


theorem disposition_at_3863 : dispositionTest 3863 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3863).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1082.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1082) = true
  rw [Nonrational.OldTerminalMatches.M016.r1082_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_3864 : dispositionTest 3864 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3864).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1083.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1083) = true
  rw [Nonrational.OldTerminalMatches.M016.r1083_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3865 : dispositionTest 3865 = true := by decide +kernel

theorem disposition_at_3866 : dispositionTest 3866 = true := by decide +kernel

theorem disposition_at_3867 : dispositionTest 3867 = true := by decide +kernel

theorem disposition_at_3868 : dispositionTest 3868 = true := by decide +kernel


theorem disposition_at_3869 : dispositionTest 3869 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3869).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1084.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1084) = true
  rw [Nonrational.OldTerminalMatches.M016.r1084_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3870 : dispositionTest 3870 = true := by decide +kernel

theorem disposition_at_3871 : dispositionTest 3871 = true := by decide +kernel

theorem disposition_interval_3840 : Interval dispositionTest 3840 3841 := by
  intro i hlo hhi
  have h : i = 3840 := by omega
  subst i
  exact disposition_at_3840


theorem disposition_interval_3841 : Interval dispositionTest 3841 3842 := by
  intro i hlo hhi
  have h : i = 3841 := by omega
  subst i
  exact disposition_at_3841


theorem disposition_interval_3842 : Interval dispositionTest 3842 3843 := by
  intro i hlo hhi
  have h : i = 3842 := by omega
  subst i
  exact disposition_at_3842


theorem disposition_interval_3843 : Interval dispositionTest 3843 3844 := by
  intro i hlo hhi
  have h : i = 3843 := by omega
  subst i
  exact disposition_at_3843


theorem disposition_interval_3844 : Interval dispositionTest 3844 3845 := by
  intro i hlo hhi
  have h : i = 3844 := by omega
  subst i
  exact disposition_at_3844


theorem disposition_interval_3845 : Interval dispositionTest 3845 3846 := by
  intro i hlo hhi
  have h : i = 3845 := by omega
  subst i
  exact disposition_at_3845


theorem disposition_interval_3846 : Interval dispositionTest 3846 3847 := by
  intro i hlo hhi
  have h : i = 3846 := by omega
  subst i
  exact disposition_at_3846


theorem disposition_interval_3847 : Interval dispositionTest 3847 3848 := by
  intro i hlo hhi
  have h : i = 3847 := by omega
  subst i
  exact disposition_at_3847


theorem disposition_interval_3848 : Interval dispositionTest 3848 3849 := by
  intro i hlo hhi
  have h : i = 3848 := by omega
  subst i
  exact disposition_at_3848


theorem disposition_interval_3849 : Interval dispositionTest 3849 3850 := by
  intro i hlo hhi
  have h : i = 3849 := by omega
  subst i
  exact disposition_at_3849


theorem disposition_interval_3850 : Interval dispositionTest 3850 3851 := by
  intro i hlo hhi
  have h : i = 3850 := by omega
  subst i
  exact disposition_at_3850


theorem disposition_interval_3851 : Interval dispositionTest 3851 3852 := by
  intro i hlo hhi
  have h : i = 3851 := by omega
  subst i
  exact disposition_at_3851


theorem disposition_interval_3852 : Interval dispositionTest 3852 3853 := by
  intro i hlo hhi
  have h : i = 3852 := by omega
  subst i
  exact disposition_at_3852


theorem disposition_interval_3853 : Interval dispositionTest 3853 3854 := by
  intro i hlo hhi
  have h : i = 3853 := by omega
  subst i
  exact disposition_at_3853


theorem disposition_interval_3854 : Interval dispositionTest 3854 3855 := by
  intro i hlo hhi
  have h : i = 3854 := by omega
  subst i
  exact disposition_at_3854


theorem disposition_interval_3855 : Interval dispositionTest 3855 3856 := by
  intro i hlo hhi
  have h : i = 3855 := by omega
  subst i
  exact disposition_at_3855


theorem disposition_interval_3856 : Interval dispositionTest 3856 3857 := by
  intro i hlo hhi
  have h : i = 3856 := by omega
  subst i
  exact disposition_at_3856


theorem disposition_interval_3857 : Interval dispositionTest 3857 3858 := by
  intro i hlo hhi
  have h : i = 3857 := by omega
  subst i
  exact disposition_at_3857


theorem disposition_interval_3858 : Interval dispositionTest 3858 3859 := by
  intro i hlo hhi
  have h : i = 3858 := by omega
  subst i
  exact disposition_at_3858


theorem disposition_interval_3859 : Interval dispositionTest 3859 3860 := by
  intro i hlo hhi
  have h : i = 3859 := by omega
  subst i
  exact disposition_at_3859


theorem disposition_interval_3860 : Interval dispositionTest 3860 3861 := by
  intro i hlo hhi
  have h : i = 3860 := by omega
  subst i
  exact disposition_at_3860


theorem disposition_interval_3861 : Interval dispositionTest 3861 3862 := by
  intro i hlo hhi
  have h : i = 3861 := by omega
  subst i
  exact disposition_at_3861


theorem disposition_interval_3862 : Interval dispositionTest 3862 3863 := by
  intro i hlo hhi
  have h : i = 3862 := by omega
  subst i
  exact disposition_at_3862


theorem disposition_interval_3863 : Interval dispositionTest 3863 3864 := by
  intro i hlo hhi
  have h : i = 3863 := by omega
  subst i
  exact disposition_at_3863


theorem disposition_interval_3864 : Interval dispositionTest 3864 3865 := by
  intro i hlo hhi
  have h : i = 3864 := by omega
  subst i
  exact disposition_at_3864


theorem disposition_interval_3865 : Interval dispositionTest 3865 3866 := by
  intro i hlo hhi
  have h : i = 3865 := by omega
  subst i
  exact disposition_at_3865


theorem disposition_interval_3866 : Interval dispositionTest 3866 3867 := by
  intro i hlo hhi
  have h : i = 3866 := by omega
  subst i
  exact disposition_at_3866


theorem disposition_interval_3867 : Interval dispositionTest 3867 3868 := by
  intro i hlo hhi
  have h : i = 3867 := by omega
  subst i
  exact disposition_at_3867


theorem disposition_interval_3868 : Interval dispositionTest 3868 3869 := by
  intro i hlo hhi
  have h : i = 3868 := by omega
  subst i
  exact disposition_at_3868


theorem disposition_interval_3869 : Interval dispositionTest 3869 3870 := by
  intro i hlo hhi
  have h : i = 3869 := by omega
  subst i
  exact disposition_at_3869


theorem disposition_interval_3870 : Interval dispositionTest 3870 3871 := by
  intro i hlo hhi
  have h : i = 3870 := by omega
  subst i
  exact disposition_at_3870


theorem disposition_interval_3871 : Interval dispositionTest 3871 3872 := by
  intro i hlo hhi
  have h : i = 3871 := by omega
  subst i
  exact disposition_at_3871

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
