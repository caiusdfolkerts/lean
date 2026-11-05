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
theorem disposition_at_3872 : dispositionTest 3872 = true := by decide +kernel

theorem disposition_at_3873 : dispositionTest 3873 = true := by decide +kernel

theorem disposition_at_3874 : dispositionTest 3874 = true := by decide +kernel

theorem disposition_at_3875 : dispositionTest 3875 = true := by decide +kernel

theorem disposition_at_3876 : dispositionTest 3876 = true := by decide +kernel

theorem disposition_at_3877 : dispositionTest 3877 = true := by decide +kernel


theorem disposition_at_3878 : dispositionTest 3878 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3878).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1085.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1085) = true
  rw [Nonrational.OldTerminalMatches.M016.r1085_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3879 : dispositionTest 3879 = true := by decide +kernel

theorem disposition_at_3880 : dispositionTest 3880 = true := by decide +kernel

theorem disposition_at_3881 : dispositionTest 3881 = true := by decide +kernel

theorem disposition_at_3882 : dispositionTest 3882 = true := by decide +kernel

theorem disposition_at_3883 : dispositionTest 3883 = true := by decide +kernel

theorem disposition_at_3884 : dispositionTest 3884 = true := by decide +kernel

theorem disposition_at_3885 : dispositionTest 3885 = true := by decide +kernel

theorem disposition_at_3886 : dispositionTest 3886 = true := by decide +kernel

theorem disposition_at_3887 : dispositionTest 3887 = true := by decide +kernel

theorem disposition_at_3888 : dispositionTest 3888 = true := by decide +kernel

theorem disposition_at_3889 : dispositionTest 3889 = true := by decide +kernel

theorem disposition_at_3890 : dispositionTest 3890 = true := by decide +kernel

theorem disposition_at_3891 : dispositionTest 3891 = true := by decide +kernel

theorem disposition_at_3892 : dispositionTest 3892 = true := by decide +kernel

theorem disposition_at_3893 : dispositionTest 3893 = true := by decide +kernel

theorem disposition_at_3894 : dispositionTest 3894 = true := by decide +kernel

theorem disposition_at_3895 : dispositionTest 3895 = true := by decide +kernel

theorem disposition_at_3896 : dispositionTest 3896 = true := by decide +kernel

theorem disposition_at_3897 : dispositionTest 3897 = true := by decide +kernel

theorem disposition_at_3898 : dispositionTest 3898 = true := by decide +kernel

theorem disposition_at_3899 : dispositionTest 3899 = true := by decide +kernel

theorem disposition_at_3900 : dispositionTest 3900 = true := by decide +kernel

theorem disposition_at_3901 : dispositionTest 3901 = true := by decide +kernel

theorem disposition_at_3902 : dispositionTest 3902 = true := by decide +kernel

theorem disposition_at_3903 : dispositionTest 3903 = true := by decide +kernel

theorem disposition_interval_3872 : Interval dispositionTest 3872 3873 := by
  intro i hlo hhi
  have h : i = 3872 := by omega
  subst i
  exact disposition_at_3872


theorem disposition_interval_3873 : Interval dispositionTest 3873 3874 := by
  intro i hlo hhi
  have h : i = 3873 := by omega
  subst i
  exact disposition_at_3873


theorem disposition_interval_3874 : Interval dispositionTest 3874 3875 := by
  intro i hlo hhi
  have h : i = 3874 := by omega
  subst i
  exact disposition_at_3874


theorem disposition_interval_3875 : Interval dispositionTest 3875 3876 := by
  intro i hlo hhi
  have h : i = 3875 := by omega
  subst i
  exact disposition_at_3875


theorem disposition_interval_3876 : Interval dispositionTest 3876 3877 := by
  intro i hlo hhi
  have h : i = 3876 := by omega
  subst i
  exact disposition_at_3876


theorem disposition_interval_3877 : Interval dispositionTest 3877 3878 := by
  intro i hlo hhi
  have h : i = 3877 := by omega
  subst i
  exact disposition_at_3877


theorem disposition_interval_3878 : Interval dispositionTest 3878 3879 := by
  intro i hlo hhi
  have h : i = 3878 := by omega
  subst i
  exact disposition_at_3878


theorem disposition_interval_3879 : Interval dispositionTest 3879 3880 := by
  intro i hlo hhi
  have h : i = 3879 := by omega
  subst i
  exact disposition_at_3879


theorem disposition_interval_3880 : Interval dispositionTest 3880 3881 := by
  intro i hlo hhi
  have h : i = 3880 := by omega
  subst i
  exact disposition_at_3880


theorem disposition_interval_3881 : Interval dispositionTest 3881 3882 := by
  intro i hlo hhi
  have h : i = 3881 := by omega
  subst i
  exact disposition_at_3881


theorem disposition_interval_3882 : Interval dispositionTest 3882 3883 := by
  intro i hlo hhi
  have h : i = 3882 := by omega
  subst i
  exact disposition_at_3882


theorem disposition_interval_3883 : Interval dispositionTest 3883 3884 := by
  intro i hlo hhi
  have h : i = 3883 := by omega
  subst i
  exact disposition_at_3883


theorem disposition_interval_3884 : Interval dispositionTest 3884 3885 := by
  intro i hlo hhi
  have h : i = 3884 := by omega
  subst i
  exact disposition_at_3884


theorem disposition_interval_3885 : Interval dispositionTest 3885 3886 := by
  intro i hlo hhi
  have h : i = 3885 := by omega
  subst i
  exact disposition_at_3885


theorem disposition_interval_3886 : Interval dispositionTest 3886 3887 := by
  intro i hlo hhi
  have h : i = 3886 := by omega
  subst i
  exact disposition_at_3886


theorem disposition_interval_3887 : Interval dispositionTest 3887 3888 := by
  intro i hlo hhi
  have h : i = 3887 := by omega
  subst i
  exact disposition_at_3887


theorem disposition_interval_3888 : Interval dispositionTest 3888 3889 := by
  intro i hlo hhi
  have h : i = 3888 := by omega
  subst i
  exact disposition_at_3888


theorem disposition_interval_3889 : Interval dispositionTest 3889 3890 := by
  intro i hlo hhi
  have h : i = 3889 := by omega
  subst i
  exact disposition_at_3889


theorem disposition_interval_3890 : Interval dispositionTest 3890 3891 := by
  intro i hlo hhi
  have h : i = 3890 := by omega
  subst i
  exact disposition_at_3890


theorem disposition_interval_3891 : Interval dispositionTest 3891 3892 := by
  intro i hlo hhi
  have h : i = 3891 := by omega
  subst i
  exact disposition_at_3891


theorem disposition_interval_3892 : Interval dispositionTest 3892 3893 := by
  intro i hlo hhi
  have h : i = 3892 := by omega
  subst i
  exact disposition_at_3892


theorem disposition_interval_3893 : Interval dispositionTest 3893 3894 := by
  intro i hlo hhi
  have h : i = 3893 := by omega
  subst i
  exact disposition_at_3893


theorem disposition_interval_3894 : Interval dispositionTest 3894 3895 := by
  intro i hlo hhi
  have h : i = 3894 := by omega
  subst i
  exact disposition_at_3894


theorem disposition_interval_3895 : Interval dispositionTest 3895 3896 := by
  intro i hlo hhi
  have h : i = 3895 := by omega
  subst i
  exact disposition_at_3895


theorem disposition_interval_3896 : Interval dispositionTest 3896 3897 := by
  intro i hlo hhi
  have h : i = 3896 := by omega
  subst i
  exact disposition_at_3896


theorem disposition_interval_3897 : Interval dispositionTest 3897 3898 := by
  intro i hlo hhi
  have h : i = 3897 := by omega
  subst i
  exact disposition_at_3897


theorem disposition_interval_3898 : Interval dispositionTest 3898 3899 := by
  intro i hlo hhi
  have h : i = 3898 := by omega
  subst i
  exact disposition_at_3898


theorem disposition_interval_3899 : Interval dispositionTest 3899 3900 := by
  intro i hlo hhi
  have h : i = 3899 := by omega
  subst i
  exact disposition_at_3899


theorem disposition_interval_3900 : Interval dispositionTest 3900 3901 := by
  intro i hlo hhi
  have h : i = 3900 := by omega
  subst i
  exact disposition_at_3900


theorem disposition_interval_3901 : Interval dispositionTest 3901 3902 := by
  intro i hlo hhi
  have h : i = 3901 := by omega
  subst i
  exact disposition_at_3901


theorem disposition_interval_3902 : Interval dispositionTest 3902 3903 := by
  intro i hlo hhi
  have h : i = 3902 := by omega
  subst i
  exact disposition_at_3902


theorem disposition_interval_3903 : Interval dispositionTest 3903 3904 := by
  intro i hlo hhi
  have h : i = 3903 := by omega
  subst i
  exact disposition_at_3903

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
