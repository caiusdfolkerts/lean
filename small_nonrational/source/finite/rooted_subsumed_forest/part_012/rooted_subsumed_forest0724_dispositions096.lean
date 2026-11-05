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
theorem disposition_at_3072 : dispositionTest 3072 = true := by decide +kernel


theorem disposition_at_3073 : dispositionTest 3073 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3073).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M024.r1559.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M024.r1559) = true
  rw [Nonrational.OldTerminalMatches.M024.r1559_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_3074 : dispositionTest 3074 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3074).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M024.r1560.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M024.r1560) = true
  rw [Nonrational.OldTerminalMatches.M024.r1560_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3075 : dispositionTest 3075 = true := by decide +kernel

theorem disposition_at_3076 : dispositionTest 3076 = true := by decide +kernel

theorem disposition_at_3077 : dispositionTest 3077 = true := by decide +kernel

theorem disposition_at_3078 : dispositionTest 3078 = true := by decide +kernel

theorem disposition_at_3079 : dispositionTest 3079 = true := by decide +kernel

theorem disposition_at_3080 : dispositionTest 3080 = true := by decide +kernel


theorem disposition_at_3081 : dispositionTest 3081 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3081).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M024.r1561.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M024.r1561) = true
  rw [Nonrational.OldTerminalMatches.M024.r1561_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3082 : dispositionTest 3082 = true := by decide +kernel

theorem disposition_at_3083 : dispositionTest 3083 = true := by decide +kernel

theorem disposition_at_3084 : dispositionTest 3084 = true := by decide +kernel


theorem disposition_at_3085 : dispositionTest 3085 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3085).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M024.r1562.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M024.r1562) = true
  rw [Nonrational.OldTerminalMatches.M024.r1562_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3086 : dispositionTest 3086 = true := by decide +kernel


theorem disposition_at_3087 : dispositionTest 3087 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3087).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M024.r1563.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M024.r1563) = true
  rw [Nonrational.OldTerminalMatches.M024.r1563_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3088 : dispositionTest 3088 = true := by decide +kernel

theorem disposition_at_3089 : dispositionTest 3089 = true := by decide +kernel


theorem disposition_at_3090 : dispositionTest 3090 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3090).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M024.r1564.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M024.r1564) = true
  rw [Nonrational.OldTerminalMatches.M024.r1564_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3091 : dispositionTest 3091 = true := by decide +kernel

theorem disposition_at_3092 : dispositionTest 3092 = true := by decide +kernel

theorem disposition_at_3093 : dispositionTest 3093 = true := by decide +kernel


theorem disposition_at_3094 : dispositionTest 3094 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3094).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M024.r1565.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M024.r1565) = true
  rw [Nonrational.OldTerminalMatches.M024.r1565_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3095 : dispositionTest 3095 = true := by decide +kernel

theorem disposition_at_3096 : dispositionTest 3096 = true := by decide +kernel

theorem disposition_at_3097 : dispositionTest 3097 = true := by decide +kernel

theorem disposition_at_3098 : dispositionTest 3098 = true := by decide +kernel

theorem disposition_at_3099 : dispositionTest 3099 = true := by decide +kernel

theorem disposition_at_3100 : dispositionTest 3100 = true := by decide +kernel

theorem disposition_at_3101 : dispositionTest 3101 = true := by decide +kernel

theorem disposition_at_3102 : dispositionTest 3102 = true := by decide +kernel

theorem disposition_at_3103 : dispositionTest 3103 = true := by decide +kernel

theorem disposition_interval_3072 : Interval dispositionTest 3072 3073 := by
  intro i hlo hhi
  have h : i = 3072 := by omega
  subst i
  exact disposition_at_3072


theorem disposition_interval_3073 : Interval dispositionTest 3073 3074 := by
  intro i hlo hhi
  have h : i = 3073 := by omega
  subst i
  exact disposition_at_3073


theorem disposition_interval_3074 : Interval dispositionTest 3074 3075 := by
  intro i hlo hhi
  have h : i = 3074 := by omega
  subst i
  exact disposition_at_3074


theorem disposition_interval_3075 : Interval dispositionTest 3075 3076 := by
  intro i hlo hhi
  have h : i = 3075 := by omega
  subst i
  exact disposition_at_3075


theorem disposition_interval_3076 : Interval dispositionTest 3076 3077 := by
  intro i hlo hhi
  have h : i = 3076 := by omega
  subst i
  exact disposition_at_3076


theorem disposition_interval_3077 : Interval dispositionTest 3077 3078 := by
  intro i hlo hhi
  have h : i = 3077 := by omega
  subst i
  exact disposition_at_3077


theorem disposition_interval_3078 : Interval dispositionTest 3078 3079 := by
  intro i hlo hhi
  have h : i = 3078 := by omega
  subst i
  exact disposition_at_3078


theorem disposition_interval_3079 : Interval dispositionTest 3079 3080 := by
  intro i hlo hhi
  have h : i = 3079 := by omega
  subst i
  exact disposition_at_3079


theorem disposition_interval_3080 : Interval dispositionTest 3080 3081 := by
  intro i hlo hhi
  have h : i = 3080 := by omega
  subst i
  exact disposition_at_3080


theorem disposition_interval_3081 : Interval dispositionTest 3081 3082 := by
  intro i hlo hhi
  have h : i = 3081 := by omega
  subst i
  exact disposition_at_3081


theorem disposition_interval_3082 : Interval dispositionTest 3082 3083 := by
  intro i hlo hhi
  have h : i = 3082 := by omega
  subst i
  exact disposition_at_3082


theorem disposition_interval_3083 : Interval dispositionTest 3083 3084 := by
  intro i hlo hhi
  have h : i = 3083 := by omega
  subst i
  exact disposition_at_3083


theorem disposition_interval_3084 : Interval dispositionTest 3084 3085 := by
  intro i hlo hhi
  have h : i = 3084 := by omega
  subst i
  exact disposition_at_3084


theorem disposition_interval_3085 : Interval dispositionTest 3085 3086 := by
  intro i hlo hhi
  have h : i = 3085 := by omega
  subst i
  exact disposition_at_3085


theorem disposition_interval_3086 : Interval dispositionTest 3086 3087 := by
  intro i hlo hhi
  have h : i = 3086 := by omega
  subst i
  exact disposition_at_3086


theorem disposition_interval_3087 : Interval dispositionTest 3087 3088 := by
  intro i hlo hhi
  have h : i = 3087 := by omega
  subst i
  exact disposition_at_3087


theorem disposition_interval_3088 : Interval dispositionTest 3088 3089 := by
  intro i hlo hhi
  have h : i = 3088 := by omega
  subst i
  exact disposition_at_3088


theorem disposition_interval_3089 : Interval dispositionTest 3089 3090 := by
  intro i hlo hhi
  have h : i = 3089 := by omega
  subst i
  exact disposition_at_3089


theorem disposition_interval_3090 : Interval dispositionTest 3090 3091 := by
  intro i hlo hhi
  have h : i = 3090 := by omega
  subst i
  exact disposition_at_3090


theorem disposition_interval_3091 : Interval dispositionTest 3091 3092 := by
  intro i hlo hhi
  have h : i = 3091 := by omega
  subst i
  exact disposition_at_3091


theorem disposition_interval_3092 : Interval dispositionTest 3092 3093 := by
  intro i hlo hhi
  have h : i = 3092 := by omega
  subst i
  exact disposition_at_3092


theorem disposition_interval_3093 : Interval dispositionTest 3093 3094 := by
  intro i hlo hhi
  have h : i = 3093 := by omega
  subst i
  exact disposition_at_3093


theorem disposition_interval_3094 : Interval dispositionTest 3094 3095 := by
  intro i hlo hhi
  have h : i = 3094 := by omega
  subst i
  exact disposition_at_3094


theorem disposition_interval_3095 : Interval dispositionTest 3095 3096 := by
  intro i hlo hhi
  have h : i = 3095 := by omega
  subst i
  exact disposition_at_3095


theorem disposition_interval_3096 : Interval dispositionTest 3096 3097 := by
  intro i hlo hhi
  have h : i = 3096 := by omega
  subst i
  exact disposition_at_3096


theorem disposition_interval_3097 : Interval dispositionTest 3097 3098 := by
  intro i hlo hhi
  have h : i = 3097 := by omega
  subst i
  exact disposition_at_3097


theorem disposition_interval_3098 : Interval dispositionTest 3098 3099 := by
  intro i hlo hhi
  have h : i = 3098 := by omega
  subst i
  exact disposition_at_3098


theorem disposition_interval_3099 : Interval dispositionTest 3099 3100 := by
  intro i hlo hhi
  have h : i = 3099 := by omega
  subst i
  exact disposition_at_3099


theorem disposition_interval_3100 : Interval dispositionTest 3100 3101 := by
  intro i hlo hhi
  have h : i = 3100 := by omega
  subst i
  exact disposition_at_3100


theorem disposition_interval_3101 : Interval dispositionTest 3101 3102 := by
  intro i hlo hhi
  have h : i = 3101 := by omega
  subst i
  exact disposition_at_3101


theorem disposition_interval_3102 : Interval dispositionTest 3102 3103 := by
  intro i hlo hhi
  have h : i = 3102 := by omega
  subst i
  exact disposition_at_3102


theorem disposition_interval_3103 : Interval dispositionTest 3103 3104 := by
  intro i hlo hhi
  have h : i = 3103 := by omega
  subst i
  exact disposition_at_3103

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
