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
theorem disposition_at_3040 : dispositionTest 3040 = true := by decide +kernel

theorem disposition_at_3041 : dispositionTest 3041 = true := by decide +kernel

theorem disposition_at_3042 : dispositionTest 3042 = true := by decide +kernel

theorem disposition_at_3043 : dispositionTest 3043 = true := by decide +kernel

theorem disposition_at_3044 : dispositionTest 3044 = true := by decide +kernel


theorem disposition_at_3045 : dispositionTest 3045 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3045).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M024.r1558.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M024.r1558) = true
  rw [Nonrational.OldTerminalMatches.M024.r1558_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3046 : dispositionTest 3046 = true := by decide +kernel

theorem disposition_at_3047 : dispositionTest 3047 = true := by decide +kernel

theorem disposition_at_3048 : dispositionTest 3048 = true := by decide +kernel

theorem disposition_at_3049 : dispositionTest 3049 = true := by decide +kernel

theorem disposition_at_3050 : dispositionTest 3050 = true := by decide +kernel

theorem disposition_at_3051 : dispositionTest 3051 = true := by decide +kernel

theorem disposition_at_3052 : dispositionTest 3052 = true := by decide +kernel

theorem disposition_at_3053 : dispositionTest 3053 = true := by decide +kernel

theorem disposition_at_3054 : dispositionTest 3054 = true := by decide +kernel

theorem disposition_at_3055 : dispositionTest 3055 = true := by decide +kernel

theorem disposition_at_3056 : dispositionTest 3056 = true := by decide +kernel

theorem disposition_at_3057 : dispositionTest 3057 = true := by decide +kernel

theorem disposition_at_3058 : dispositionTest 3058 = true := by decide +kernel

theorem disposition_at_3059 : dispositionTest 3059 = true := by decide +kernel

theorem disposition_at_3060 : dispositionTest 3060 = true := by decide +kernel

theorem disposition_at_3061 : dispositionTest 3061 = true := by decide +kernel

theorem disposition_at_3062 : dispositionTest 3062 = true := by decide +kernel

theorem disposition_at_3063 : dispositionTest 3063 = true := by decide +kernel

theorem disposition_at_3064 : dispositionTest 3064 = true := by decide +kernel

theorem disposition_at_3065 : dispositionTest 3065 = true := by decide +kernel

theorem disposition_at_3066 : dispositionTest 3066 = true := by decide +kernel

theorem disposition_at_3067 : dispositionTest 3067 = true := by decide +kernel

theorem disposition_at_3068 : dispositionTest 3068 = true := by decide +kernel

theorem disposition_at_3069 : dispositionTest 3069 = true := by decide +kernel

theorem disposition_at_3070 : dispositionTest 3070 = true := by decide +kernel

theorem disposition_at_3071 : dispositionTest 3071 = true := by decide +kernel

theorem disposition_interval_3040 : Interval dispositionTest 3040 3041 := by
  intro i hlo hhi
  have h : i = 3040 := by omega
  subst i
  exact disposition_at_3040


theorem disposition_interval_3041 : Interval dispositionTest 3041 3042 := by
  intro i hlo hhi
  have h : i = 3041 := by omega
  subst i
  exact disposition_at_3041


theorem disposition_interval_3042 : Interval dispositionTest 3042 3043 := by
  intro i hlo hhi
  have h : i = 3042 := by omega
  subst i
  exact disposition_at_3042


theorem disposition_interval_3043 : Interval dispositionTest 3043 3044 := by
  intro i hlo hhi
  have h : i = 3043 := by omega
  subst i
  exact disposition_at_3043


theorem disposition_interval_3044 : Interval dispositionTest 3044 3045 := by
  intro i hlo hhi
  have h : i = 3044 := by omega
  subst i
  exact disposition_at_3044


theorem disposition_interval_3045 : Interval dispositionTest 3045 3046 := by
  intro i hlo hhi
  have h : i = 3045 := by omega
  subst i
  exact disposition_at_3045


theorem disposition_interval_3046 : Interval dispositionTest 3046 3047 := by
  intro i hlo hhi
  have h : i = 3046 := by omega
  subst i
  exact disposition_at_3046


theorem disposition_interval_3047 : Interval dispositionTest 3047 3048 := by
  intro i hlo hhi
  have h : i = 3047 := by omega
  subst i
  exact disposition_at_3047


theorem disposition_interval_3048 : Interval dispositionTest 3048 3049 := by
  intro i hlo hhi
  have h : i = 3048 := by omega
  subst i
  exact disposition_at_3048


theorem disposition_interval_3049 : Interval dispositionTest 3049 3050 := by
  intro i hlo hhi
  have h : i = 3049 := by omega
  subst i
  exact disposition_at_3049


theorem disposition_interval_3050 : Interval dispositionTest 3050 3051 := by
  intro i hlo hhi
  have h : i = 3050 := by omega
  subst i
  exact disposition_at_3050


theorem disposition_interval_3051 : Interval dispositionTest 3051 3052 := by
  intro i hlo hhi
  have h : i = 3051 := by omega
  subst i
  exact disposition_at_3051


theorem disposition_interval_3052 : Interval dispositionTest 3052 3053 := by
  intro i hlo hhi
  have h : i = 3052 := by omega
  subst i
  exact disposition_at_3052


theorem disposition_interval_3053 : Interval dispositionTest 3053 3054 := by
  intro i hlo hhi
  have h : i = 3053 := by omega
  subst i
  exact disposition_at_3053


theorem disposition_interval_3054 : Interval dispositionTest 3054 3055 := by
  intro i hlo hhi
  have h : i = 3054 := by omega
  subst i
  exact disposition_at_3054


theorem disposition_interval_3055 : Interval dispositionTest 3055 3056 := by
  intro i hlo hhi
  have h : i = 3055 := by omega
  subst i
  exact disposition_at_3055


theorem disposition_interval_3056 : Interval dispositionTest 3056 3057 := by
  intro i hlo hhi
  have h : i = 3056 := by omega
  subst i
  exact disposition_at_3056


theorem disposition_interval_3057 : Interval dispositionTest 3057 3058 := by
  intro i hlo hhi
  have h : i = 3057 := by omega
  subst i
  exact disposition_at_3057


theorem disposition_interval_3058 : Interval dispositionTest 3058 3059 := by
  intro i hlo hhi
  have h : i = 3058 := by omega
  subst i
  exact disposition_at_3058


theorem disposition_interval_3059 : Interval dispositionTest 3059 3060 := by
  intro i hlo hhi
  have h : i = 3059 := by omega
  subst i
  exact disposition_at_3059


theorem disposition_interval_3060 : Interval dispositionTest 3060 3061 := by
  intro i hlo hhi
  have h : i = 3060 := by omega
  subst i
  exact disposition_at_3060


theorem disposition_interval_3061 : Interval dispositionTest 3061 3062 := by
  intro i hlo hhi
  have h : i = 3061 := by omega
  subst i
  exact disposition_at_3061


theorem disposition_interval_3062 : Interval dispositionTest 3062 3063 := by
  intro i hlo hhi
  have h : i = 3062 := by omega
  subst i
  exact disposition_at_3062


theorem disposition_interval_3063 : Interval dispositionTest 3063 3064 := by
  intro i hlo hhi
  have h : i = 3063 := by omega
  subst i
  exact disposition_at_3063


theorem disposition_interval_3064 : Interval dispositionTest 3064 3065 := by
  intro i hlo hhi
  have h : i = 3064 := by omega
  subst i
  exact disposition_at_3064


theorem disposition_interval_3065 : Interval dispositionTest 3065 3066 := by
  intro i hlo hhi
  have h : i = 3065 := by omega
  subst i
  exact disposition_at_3065


theorem disposition_interval_3066 : Interval dispositionTest 3066 3067 := by
  intro i hlo hhi
  have h : i = 3066 := by omega
  subst i
  exact disposition_at_3066


theorem disposition_interval_3067 : Interval dispositionTest 3067 3068 := by
  intro i hlo hhi
  have h : i = 3067 := by omega
  subst i
  exact disposition_at_3067


theorem disposition_interval_3068 : Interval dispositionTest 3068 3069 := by
  intro i hlo hhi
  have h : i = 3068 := by omega
  subst i
  exact disposition_at_3068


theorem disposition_interval_3069 : Interval dispositionTest 3069 3070 := by
  intro i hlo hhi
  have h : i = 3069 := by omega
  subst i
  exact disposition_at_3069


theorem disposition_interval_3070 : Interval dispositionTest 3070 3071 := by
  intro i hlo hhi
  have h : i = 3070 := by omega
  subst i
  exact disposition_at_3070


theorem disposition_interval_3071 : Interval dispositionTest 3071 3072 := by
  intro i hlo hhi
  have h : i = 3071 := by omega
  subst i
  exact disposition_at_3071

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
