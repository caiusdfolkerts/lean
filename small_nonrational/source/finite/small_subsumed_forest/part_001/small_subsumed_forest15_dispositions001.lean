module
prelude
public import SmallSubsumedForest15DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_32 : dispositionTest 32 = true := by decide +kernel


theorem disposition_at_33 : dispositionTest 33 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 33).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0042.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0042) = true
  rw [Nonrational.OldTerminalMatches.M000.r0042_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_34 : dispositionTest 34 = true := by decide +kernel

theorem disposition_at_35 : dispositionTest 35 = true := by decide +kernel

theorem disposition_at_36 : dispositionTest 36 = true := by decide +kernel

theorem disposition_at_37 : dispositionTest 37 = true := by decide +kernel


theorem disposition_at_38 : dispositionTest 38 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 38).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0043.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0043) = true
  rw [Nonrational.OldTerminalMatches.M000.r0043_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_39 : dispositionTest 39 = true := by decide +kernel


theorem disposition_at_40 : dispositionTest 40 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 40).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0044.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0044) = true
  rw [Nonrational.OldTerminalMatches.M000.r0044_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_41 : dispositionTest 41 = true := by decide +kernel

theorem disposition_at_42 : dispositionTest 42 = true := by decide +kernel

theorem disposition_at_43 : dispositionTest 43 = true := by decide +kernel

theorem disposition_at_44 : dispositionTest 44 = true := by decide +kernel

theorem disposition_at_45 : dispositionTest 45 = true := by decide +kernel

theorem disposition_at_46 : dispositionTest 46 = true := by decide +kernel

theorem disposition_at_47 : dispositionTest 47 = true := by decide +kernel


theorem disposition_at_48 : dispositionTest 48 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 48).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0045.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0045) = true
  rw [Nonrational.OldTerminalMatches.M000.r0045_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_49 : dispositionTest 49 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 49).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0046.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0046) = true
  rw [Nonrational.OldTerminalMatches.M000.r0046_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_50 : dispositionTest 50 = true := by decide +kernel

theorem disposition_at_51 : dispositionTest 51 = true := by decide +kernel


theorem disposition_at_52 : dispositionTest 52 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 52).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0047.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0047) = true
  rw [Nonrational.OldTerminalMatches.M000.r0047_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_53 : dispositionTest 53 = true := by decide +kernel

theorem disposition_at_54 : dispositionTest 54 = true := by decide +kernel


theorem disposition_at_55 : dispositionTest 55 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 55).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0048.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0048) = true
  rw [Nonrational.OldTerminalMatches.M000.r0048_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_56 : dispositionTest 56 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 56).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0049.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0049) = true
  rw [Nonrational.OldTerminalMatches.M000.r0049_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_57 : dispositionTest 57 = true := by decide +kernel


theorem disposition_at_58 : dispositionTest 58 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 58).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0050.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0050) = true
  rw [Nonrational.OldTerminalMatches.M000.r0050_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_59 : dispositionTest 59 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 59).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0051.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0051) = true
  rw [Nonrational.OldTerminalMatches.M000.r0051_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_60 : dispositionTest 60 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 60).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0052.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0052) = true
  rw [Nonrational.OldTerminalMatches.M000.r0052_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_61 : dispositionTest 61 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 61).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0053.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0053) = true
  rw [Nonrational.OldTerminalMatches.M000.r0053_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_62 : dispositionTest 62 = true := by decide +kernel


theorem disposition_at_63 : dispositionTest 63 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 63).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0054.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0054) = true
  rw [Nonrational.OldTerminalMatches.M000.r0054_checked, Bool.and_true]
  decide +kernel

theorem disposition_interval_32 : Interval dispositionTest 32 33 := by
  intro i hlo hhi
  have h : i = 32 := by omega
  subst i
  exact disposition_at_32


theorem disposition_interval_33 : Interval dispositionTest 33 34 := by
  intro i hlo hhi
  have h : i = 33 := by omega
  subst i
  exact disposition_at_33


theorem disposition_interval_34 : Interval dispositionTest 34 35 := by
  intro i hlo hhi
  have h : i = 34 := by omega
  subst i
  exact disposition_at_34


theorem disposition_interval_35 : Interval dispositionTest 35 36 := by
  intro i hlo hhi
  have h : i = 35 := by omega
  subst i
  exact disposition_at_35


theorem disposition_interval_36 : Interval dispositionTest 36 37 := by
  intro i hlo hhi
  have h : i = 36 := by omega
  subst i
  exact disposition_at_36


theorem disposition_interval_37 : Interval dispositionTest 37 38 := by
  intro i hlo hhi
  have h : i = 37 := by omega
  subst i
  exact disposition_at_37


theorem disposition_interval_38 : Interval dispositionTest 38 39 := by
  intro i hlo hhi
  have h : i = 38 := by omega
  subst i
  exact disposition_at_38


theorem disposition_interval_39 : Interval dispositionTest 39 40 := by
  intro i hlo hhi
  have h : i = 39 := by omega
  subst i
  exact disposition_at_39


theorem disposition_interval_40 : Interval dispositionTest 40 41 := by
  intro i hlo hhi
  have h : i = 40 := by omega
  subst i
  exact disposition_at_40


theorem disposition_interval_41 : Interval dispositionTest 41 42 := by
  intro i hlo hhi
  have h : i = 41 := by omega
  subst i
  exact disposition_at_41


theorem disposition_interval_42 : Interval dispositionTest 42 43 := by
  intro i hlo hhi
  have h : i = 42 := by omega
  subst i
  exact disposition_at_42


theorem disposition_interval_43 : Interval dispositionTest 43 44 := by
  intro i hlo hhi
  have h : i = 43 := by omega
  subst i
  exact disposition_at_43


theorem disposition_interval_44 : Interval dispositionTest 44 45 := by
  intro i hlo hhi
  have h : i = 44 := by omega
  subst i
  exact disposition_at_44


theorem disposition_interval_45 : Interval dispositionTest 45 46 := by
  intro i hlo hhi
  have h : i = 45 := by omega
  subst i
  exact disposition_at_45


theorem disposition_interval_46 : Interval dispositionTest 46 47 := by
  intro i hlo hhi
  have h : i = 46 := by omega
  subst i
  exact disposition_at_46


theorem disposition_interval_47 : Interval dispositionTest 47 48 := by
  intro i hlo hhi
  have h : i = 47 := by omega
  subst i
  exact disposition_at_47


theorem disposition_interval_48 : Interval dispositionTest 48 49 := by
  intro i hlo hhi
  have h : i = 48 := by omega
  subst i
  exact disposition_at_48


theorem disposition_interval_49 : Interval dispositionTest 49 50 := by
  intro i hlo hhi
  have h : i = 49 := by omega
  subst i
  exact disposition_at_49


theorem disposition_interval_50 : Interval dispositionTest 50 51 := by
  intro i hlo hhi
  have h : i = 50 := by omega
  subst i
  exact disposition_at_50


theorem disposition_interval_51 : Interval dispositionTest 51 52 := by
  intro i hlo hhi
  have h : i = 51 := by omega
  subst i
  exact disposition_at_51


theorem disposition_interval_52 : Interval dispositionTest 52 53 := by
  intro i hlo hhi
  have h : i = 52 := by omega
  subst i
  exact disposition_at_52


theorem disposition_interval_53 : Interval dispositionTest 53 54 := by
  intro i hlo hhi
  have h : i = 53 := by omega
  subst i
  exact disposition_at_53


theorem disposition_interval_54 : Interval dispositionTest 54 55 := by
  intro i hlo hhi
  have h : i = 54 := by omega
  subst i
  exact disposition_at_54


theorem disposition_interval_55 : Interval dispositionTest 55 56 := by
  intro i hlo hhi
  have h : i = 55 := by omega
  subst i
  exact disposition_at_55


theorem disposition_interval_56 : Interval dispositionTest 56 57 := by
  intro i hlo hhi
  have h : i = 56 := by omega
  subst i
  exact disposition_at_56


theorem disposition_interval_57 : Interval dispositionTest 57 58 := by
  intro i hlo hhi
  have h : i = 57 := by omega
  subst i
  exact disposition_at_57


theorem disposition_interval_58 : Interval dispositionTest 58 59 := by
  intro i hlo hhi
  have h : i = 58 := by omega
  subst i
  exact disposition_at_58


theorem disposition_interval_59 : Interval dispositionTest 59 60 := by
  intro i hlo hhi
  have h : i = 59 := by omega
  subst i
  exact disposition_at_59


theorem disposition_interval_60 : Interval dispositionTest 60 61 := by
  intro i hlo hhi
  have h : i = 60 := by omega
  subst i
  exact disposition_at_60


theorem disposition_interval_61 : Interval dispositionTest 61 62 := by
  intro i hlo hhi
  have h : i = 61 := by omega
  subst i
  exact disposition_at_61


theorem disposition_interval_62 : Interval dispositionTest 62 63 := by
  intro i hlo hhi
  have h : i = 62 := by omega
  subst i
  exact disposition_at_62


theorem disposition_interval_63 : Interval dispositionTest 63 64 := by
  intro i hlo hhi
  have h : i = 63 := by omega
  subst i
  exact disposition_at_63

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
