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
theorem disposition_at_3904 : dispositionTest 3904 = true := by decide +kernel

theorem disposition_at_3905 : dispositionTest 3905 = true := by decide +kernel

theorem disposition_at_3906 : dispositionTest 3906 = true := by decide +kernel

theorem disposition_at_3907 : dispositionTest 3907 = true := by decide +kernel

theorem disposition_at_3908 : dispositionTest 3908 = true := by decide +kernel

theorem disposition_at_3909 : dispositionTest 3909 = true := by decide +kernel

theorem disposition_at_3910 : dispositionTest 3910 = true := by decide +kernel

theorem disposition_at_3911 : dispositionTest 3911 = true := by decide +kernel

theorem disposition_at_3912 : dispositionTest 3912 = true := by decide +kernel


theorem disposition_at_3913 : dispositionTest 3913 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3913).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1086.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1086) = true
  rw [Nonrational.OldTerminalMatches.M016.r1086_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3914 : dispositionTest 3914 = true := by decide +kernel

theorem disposition_at_3915 : dispositionTest 3915 = true := by decide +kernel

theorem disposition_at_3916 : dispositionTest 3916 = true := by decide +kernel

theorem disposition_at_3917 : dispositionTest 3917 = true := by decide +kernel

theorem disposition_at_3918 : dispositionTest 3918 = true := by decide +kernel

theorem disposition_at_3919 : dispositionTest 3919 = true := by decide +kernel

theorem disposition_at_3920 : dispositionTest 3920 = true := by decide +kernel

theorem disposition_at_3921 : dispositionTest 3921 = true := by decide +kernel

theorem disposition_at_3922 : dispositionTest 3922 = true := by decide +kernel

theorem disposition_at_3923 : dispositionTest 3923 = true := by decide +kernel

theorem disposition_at_3924 : dispositionTest 3924 = true := by decide +kernel

theorem disposition_at_3925 : dispositionTest 3925 = true := by decide +kernel


theorem disposition_at_3926 : dispositionTest 3926 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3926).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1087.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1087) = true
  rw [Nonrational.OldTerminalMatches.M016.r1087_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_3927 : dispositionTest 3927 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3927).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M017.r1088.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M017.r1088) = true
  rw [Nonrational.OldTerminalMatches.M017.r1088_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3928 : dispositionTest 3928 = true := by decide +kernel

theorem disposition_at_3929 : dispositionTest 3929 = true := by decide +kernel

theorem disposition_at_3930 : dispositionTest 3930 = true := by decide +kernel

theorem disposition_at_3931 : dispositionTest 3931 = true := by decide +kernel

theorem disposition_at_3932 : dispositionTest 3932 = true := by decide +kernel

theorem disposition_at_3933 : dispositionTest 3933 = true := by decide +kernel

theorem disposition_at_3934 : dispositionTest 3934 = true := by decide +kernel

theorem disposition_at_3935 : dispositionTest 3935 = true := by decide +kernel

theorem disposition_interval_3904 : Interval dispositionTest 3904 3905 := by
  intro i hlo hhi
  have h : i = 3904 := by omega
  subst i
  exact disposition_at_3904


theorem disposition_interval_3905 : Interval dispositionTest 3905 3906 := by
  intro i hlo hhi
  have h : i = 3905 := by omega
  subst i
  exact disposition_at_3905


theorem disposition_interval_3906 : Interval dispositionTest 3906 3907 := by
  intro i hlo hhi
  have h : i = 3906 := by omega
  subst i
  exact disposition_at_3906


theorem disposition_interval_3907 : Interval dispositionTest 3907 3908 := by
  intro i hlo hhi
  have h : i = 3907 := by omega
  subst i
  exact disposition_at_3907


theorem disposition_interval_3908 : Interval dispositionTest 3908 3909 := by
  intro i hlo hhi
  have h : i = 3908 := by omega
  subst i
  exact disposition_at_3908


theorem disposition_interval_3909 : Interval dispositionTest 3909 3910 := by
  intro i hlo hhi
  have h : i = 3909 := by omega
  subst i
  exact disposition_at_3909


theorem disposition_interval_3910 : Interval dispositionTest 3910 3911 := by
  intro i hlo hhi
  have h : i = 3910 := by omega
  subst i
  exact disposition_at_3910


theorem disposition_interval_3911 : Interval dispositionTest 3911 3912 := by
  intro i hlo hhi
  have h : i = 3911 := by omega
  subst i
  exact disposition_at_3911


theorem disposition_interval_3912 : Interval dispositionTest 3912 3913 := by
  intro i hlo hhi
  have h : i = 3912 := by omega
  subst i
  exact disposition_at_3912


theorem disposition_interval_3913 : Interval dispositionTest 3913 3914 := by
  intro i hlo hhi
  have h : i = 3913 := by omega
  subst i
  exact disposition_at_3913


theorem disposition_interval_3914 : Interval dispositionTest 3914 3915 := by
  intro i hlo hhi
  have h : i = 3914 := by omega
  subst i
  exact disposition_at_3914


theorem disposition_interval_3915 : Interval dispositionTest 3915 3916 := by
  intro i hlo hhi
  have h : i = 3915 := by omega
  subst i
  exact disposition_at_3915


theorem disposition_interval_3916 : Interval dispositionTest 3916 3917 := by
  intro i hlo hhi
  have h : i = 3916 := by omega
  subst i
  exact disposition_at_3916


theorem disposition_interval_3917 : Interval dispositionTest 3917 3918 := by
  intro i hlo hhi
  have h : i = 3917 := by omega
  subst i
  exact disposition_at_3917


theorem disposition_interval_3918 : Interval dispositionTest 3918 3919 := by
  intro i hlo hhi
  have h : i = 3918 := by omega
  subst i
  exact disposition_at_3918


theorem disposition_interval_3919 : Interval dispositionTest 3919 3920 := by
  intro i hlo hhi
  have h : i = 3919 := by omega
  subst i
  exact disposition_at_3919


theorem disposition_interval_3920 : Interval dispositionTest 3920 3921 := by
  intro i hlo hhi
  have h : i = 3920 := by omega
  subst i
  exact disposition_at_3920


theorem disposition_interval_3921 : Interval dispositionTest 3921 3922 := by
  intro i hlo hhi
  have h : i = 3921 := by omega
  subst i
  exact disposition_at_3921


theorem disposition_interval_3922 : Interval dispositionTest 3922 3923 := by
  intro i hlo hhi
  have h : i = 3922 := by omega
  subst i
  exact disposition_at_3922


theorem disposition_interval_3923 : Interval dispositionTest 3923 3924 := by
  intro i hlo hhi
  have h : i = 3923 := by omega
  subst i
  exact disposition_at_3923


theorem disposition_interval_3924 : Interval dispositionTest 3924 3925 := by
  intro i hlo hhi
  have h : i = 3924 := by omega
  subst i
  exact disposition_at_3924


theorem disposition_interval_3925 : Interval dispositionTest 3925 3926 := by
  intro i hlo hhi
  have h : i = 3925 := by omega
  subst i
  exact disposition_at_3925


theorem disposition_interval_3926 : Interval dispositionTest 3926 3927 := by
  intro i hlo hhi
  have h : i = 3926 := by omega
  subst i
  exact disposition_at_3926


theorem disposition_interval_3927 : Interval dispositionTest 3927 3928 := by
  intro i hlo hhi
  have h : i = 3927 := by omega
  subst i
  exact disposition_at_3927


theorem disposition_interval_3928 : Interval dispositionTest 3928 3929 := by
  intro i hlo hhi
  have h : i = 3928 := by omega
  subst i
  exact disposition_at_3928


theorem disposition_interval_3929 : Interval dispositionTest 3929 3930 := by
  intro i hlo hhi
  have h : i = 3929 := by omega
  subst i
  exact disposition_at_3929


theorem disposition_interval_3930 : Interval dispositionTest 3930 3931 := by
  intro i hlo hhi
  have h : i = 3930 := by omega
  subst i
  exact disposition_at_3930


theorem disposition_interval_3931 : Interval dispositionTest 3931 3932 := by
  intro i hlo hhi
  have h : i = 3931 := by omega
  subst i
  exact disposition_at_3931


theorem disposition_interval_3932 : Interval dispositionTest 3932 3933 := by
  intro i hlo hhi
  have h : i = 3932 := by omega
  subst i
  exact disposition_at_3932


theorem disposition_interval_3933 : Interval dispositionTest 3933 3934 := by
  intro i hlo hhi
  have h : i = 3933 := by omega
  subst i
  exact disposition_at_3933


theorem disposition_interval_3934 : Interval dispositionTest 3934 3935 := by
  intro i hlo hhi
  have h : i = 3934 := by omega
  subst i
  exact disposition_at_3934


theorem disposition_interval_3935 : Interval dispositionTest 3935 3936 := by
  intro i hlo hhi
  have h : i = 3935 := by omega
  subst i
  exact disposition_at_3935

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
