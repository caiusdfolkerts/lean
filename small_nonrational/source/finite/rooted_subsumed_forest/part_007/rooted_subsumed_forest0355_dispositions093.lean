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
theorem disposition_at_2976 : dispositionTest 2976 = true := by decide +kernel

theorem disposition_at_2977 : dispositionTest 2977 = true := by decide +kernel

theorem disposition_at_2978 : dispositionTest 2978 = true := by decide +kernel

theorem disposition_at_2979 : dispositionTest 2979 = true := by decide +kernel

theorem disposition_at_2980 : dispositionTest 2980 = true := by decide +kernel

theorem disposition_at_2981 : dispositionTest 2981 = true := by decide +kernel

theorem disposition_at_2982 : dispositionTest 2982 = true := by decide +kernel

theorem disposition_at_2983 : dispositionTest 2983 = true := by decide +kernel

theorem disposition_at_2984 : dispositionTest 2984 = true := by decide +kernel

theorem disposition_at_2985 : dispositionTest 2985 = true := by decide +kernel

theorem disposition_at_2986 : dispositionTest 2986 = true := by decide +kernel

theorem disposition_at_2987 : dispositionTest 2987 = true := by decide +kernel

theorem disposition_at_2988 : dispositionTest 2988 = true := by decide +kernel

theorem disposition_at_2989 : dispositionTest 2989 = true := by decide +kernel

theorem disposition_at_2990 : dispositionTest 2990 = true := by decide +kernel

theorem disposition_at_2991 : dispositionTest 2991 = true := by decide +kernel

theorem disposition_at_2992 : dispositionTest 2992 = true := by decide +kernel

theorem disposition_at_2993 : dispositionTest 2993 = true := by decide +kernel

theorem disposition_at_2994 : dispositionTest 2994 = true := by decide +kernel

theorem disposition_at_2995 : dispositionTest 2995 = true := by decide +kernel

theorem disposition_at_2996 : dispositionTest 2996 = true := by decide +kernel

theorem disposition_at_2997 : dispositionTest 2997 = true := by decide +kernel

theorem disposition_at_2998 : dispositionTest 2998 = true := by decide +kernel

theorem disposition_at_2999 : dispositionTest 2999 = true := by decide +kernel

theorem disposition_at_3000 : dispositionTest 3000 = true := by decide +kernel

theorem disposition_at_3001 : dispositionTest 3001 = true := by decide +kernel

theorem disposition_at_3002 : dispositionTest 3002 = true := by decide +kernel

theorem disposition_at_3003 : dispositionTest 3003 = true := by decide +kernel


theorem disposition_at_3004 : dispositionTest 3004 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3004).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1050.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1050) = true
  rw [Nonrational.OldTerminalMatches.M016.r1050_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_3005 : dispositionTest 3005 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3005).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1051.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1051) = true
  rw [Nonrational.OldTerminalMatches.M016.r1051_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3006 : dispositionTest 3006 = true := by decide +kernel

theorem disposition_at_3007 : dispositionTest 3007 = true := by decide +kernel

theorem disposition_interval_2976 : Interval dispositionTest 2976 2977 := by
  intro i hlo hhi
  have h : i = 2976 := by omega
  subst i
  exact disposition_at_2976


theorem disposition_interval_2977 : Interval dispositionTest 2977 2978 := by
  intro i hlo hhi
  have h : i = 2977 := by omega
  subst i
  exact disposition_at_2977


theorem disposition_interval_2978 : Interval dispositionTest 2978 2979 := by
  intro i hlo hhi
  have h : i = 2978 := by omega
  subst i
  exact disposition_at_2978


theorem disposition_interval_2979 : Interval dispositionTest 2979 2980 := by
  intro i hlo hhi
  have h : i = 2979 := by omega
  subst i
  exact disposition_at_2979


theorem disposition_interval_2980 : Interval dispositionTest 2980 2981 := by
  intro i hlo hhi
  have h : i = 2980 := by omega
  subst i
  exact disposition_at_2980


theorem disposition_interval_2981 : Interval dispositionTest 2981 2982 := by
  intro i hlo hhi
  have h : i = 2981 := by omega
  subst i
  exact disposition_at_2981


theorem disposition_interval_2982 : Interval dispositionTest 2982 2983 := by
  intro i hlo hhi
  have h : i = 2982 := by omega
  subst i
  exact disposition_at_2982


theorem disposition_interval_2983 : Interval dispositionTest 2983 2984 := by
  intro i hlo hhi
  have h : i = 2983 := by omega
  subst i
  exact disposition_at_2983


theorem disposition_interval_2984 : Interval dispositionTest 2984 2985 := by
  intro i hlo hhi
  have h : i = 2984 := by omega
  subst i
  exact disposition_at_2984


theorem disposition_interval_2985 : Interval dispositionTest 2985 2986 := by
  intro i hlo hhi
  have h : i = 2985 := by omega
  subst i
  exact disposition_at_2985


theorem disposition_interval_2986 : Interval dispositionTest 2986 2987 := by
  intro i hlo hhi
  have h : i = 2986 := by omega
  subst i
  exact disposition_at_2986


theorem disposition_interval_2987 : Interval dispositionTest 2987 2988 := by
  intro i hlo hhi
  have h : i = 2987 := by omega
  subst i
  exact disposition_at_2987


theorem disposition_interval_2988 : Interval dispositionTest 2988 2989 := by
  intro i hlo hhi
  have h : i = 2988 := by omega
  subst i
  exact disposition_at_2988


theorem disposition_interval_2989 : Interval dispositionTest 2989 2990 := by
  intro i hlo hhi
  have h : i = 2989 := by omega
  subst i
  exact disposition_at_2989


theorem disposition_interval_2990 : Interval dispositionTest 2990 2991 := by
  intro i hlo hhi
  have h : i = 2990 := by omega
  subst i
  exact disposition_at_2990


theorem disposition_interval_2991 : Interval dispositionTest 2991 2992 := by
  intro i hlo hhi
  have h : i = 2991 := by omega
  subst i
  exact disposition_at_2991


theorem disposition_interval_2992 : Interval dispositionTest 2992 2993 := by
  intro i hlo hhi
  have h : i = 2992 := by omega
  subst i
  exact disposition_at_2992


theorem disposition_interval_2993 : Interval dispositionTest 2993 2994 := by
  intro i hlo hhi
  have h : i = 2993 := by omega
  subst i
  exact disposition_at_2993


theorem disposition_interval_2994 : Interval dispositionTest 2994 2995 := by
  intro i hlo hhi
  have h : i = 2994 := by omega
  subst i
  exact disposition_at_2994


theorem disposition_interval_2995 : Interval dispositionTest 2995 2996 := by
  intro i hlo hhi
  have h : i = 2995 := by omega
  subst i
  exact disposition_at_2995


theorem disposition_interval_2996 : Interval dispositionTest 2996 2997 := by
  intro i hlo hhi
  have h : i = 2996 := by omega
  subst i
  exact disposition_at_2996


theorem disposition_interval_2997 : Interval dispositionTest 2997 2998 := by
  intro i hlo hhi
  have h : i = 2997 := by omega
  subst i
  exact disposition_at_2997


theorem disposition_interval_2998 : Interval dispositionTest 2998 2999 := by
  intro i hlo hhi
  have h : i = 2998 := by omega
  subst i
  exact disposition_at_2998


theorem disposition_interval_2999 : Interval dispositionTest 2999 3000 := by
  intro i hlo hhi
  have h : i = 2999 := by omega
  subst i
  exact disposition_at_2999


theorem disposition_interval_3000 : Interval dispositionTest 3000 3001 := by
  intro i hlo hhi
  have h : i = 3000 := by omega
  subst i
  exact disposition_at_3000


theorem disposition_interval_3001 : Interval dispositionTest 3001 3002 := by
  intro i hlo hhi
  have h : i = 3001 := by omega
  subst i
  exact disposition_at_3001


theorem disposition_interval_3002 : Interval dispositionTest 3002 3003 := by
  intro i hlo hhi
  have h : i = 3002 := by omega
  subst i
  exact disposition_at_3002


theorem disposition_interval_3003 : Interval dispositionTest 3003 3004 := by
  intro i hlo hhi
  have h : i = 3003 := by omega
  subst i
  exact disposition_at_3003


theorem disposition_interval_3004 : Interval dispositionTest 3004 3005 := by
  intro i hlo hhi
  have h : i = 3004 := by omega
  subst i
  exact disposition_at_3004


theorem disposition_interval_3005 : Interval dispositionTest 3005 3006 := by
  intro i hlo hhi
  have h : i = 3005 := by omega
  subst i
  exact disposition_at_3005


theorem disposition_interval_3006 : Interval dispositionTest 3006 3007 := by
  intro i hlo hhi
  have h : i = 3006 := by omega
  subst i
  exact disposition_at_3006


theorem disposition_interval_3007 : Interval dispositionTest 3007 3008 := by
  intro i hlo hhi
  have h : i = 3007 := by omega
  subst i
  exact disposition_at_3007

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
