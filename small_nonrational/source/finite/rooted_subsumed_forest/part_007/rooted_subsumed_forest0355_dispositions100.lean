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
theorem disposition_at_3200 : dispositionTest 3200 = true := by decide +kernel

theorem disposition_at_3201 : dispositionTest 3201 = true := by decide +kernel

theorem disposition_at_3202 : dispositionTest 3202 = true := by decide +kernel

theorem disposition_at_3203 : dispositionTest 3203 = true := by decide +kernel

theorem disposition_at_3204 : dispositionTest 3204 = true := by decide +kernel

theorem disposition_at_3205 : dispositionTest 3205 = true := by decide +kernel

theorem disposition_at_3206 : dispositionTest 3206 = true := by decide +kernel

theorem disposition_at_3207 : dispositionTest 3207 = true := by decide +kernel

theorem disposition_at_3208 : dispositionTest 3208 = true := by decide +kernel

theorem disposition_at_3209 : dispositionTest 3209 = true := by decide +kernel

theorem disposition_at_3210 : dispositionTest 3210 = true := by decide +kernel

theorem disposition_at_3211 : dispositionTest 3211 = true := by decide +kernel

theorem disposition_at_3212 : dispositionTest 3212 = true := by decide +kernel

theorem disposition_at_3213 : dispositionTest 3213 = true := by decide +kernel

theorem disposition_at_3214 : dispositionTest 3214 = true := by decide +kernel

theorem disposition_at_3215 : dispositionTest 3215 = true := by decide +kernel

theorem disposition_at_3216 : dispositionTest 3216 = true := by decide +kernel

theorem disposition_at_3217 : dispositionTest 3217 = true := by decide +kernel

theorem disposition_at_3218 : dispositionTest 3218 = true := by decide +kernel

theorem disposition_at_3219 : dispositionTest 3219 = true := by decide +kernel

theorem disposition_at_3220 : dispositionTest 3220 = true := by decide +kernel

theorem disposition_at_3221 : dispositionTest 3221 = true := by decide +kernel

theorem disposition_at_3222 : dispositionTest 3222 = true := by decide +kernel

theorem disposition_at_3223 : dispositionTest 3223 = true := by decide +kernel

theorem disposition_at_3224 : dispositionTest 3224 = true := by decide +kernel

theorem disposition_at_3225 : dispositionTest 3225 = true := by decide +kernel

theorem disposition_at_3226 : dispositionTest 3226 = true := by decide +kernel

theorem disposition_at_3227 : dispositionTest 3227 = true := by decide +kernel

theorem disposition_at_3228 : dispositionTest 3228 = true := by decide +kernel

theorem disposition_at_3229 : dispositionTest 3229 = true := by decide +kernel

theorem disposition_at_3230 : dispositionTest 3230 = true := by decide +kernel

theorem disposition_at_3231 : dispositionTest 3231 = true := by decide +kernel

theorem disposition_interval_3200 : Interval dispositionTest 3200 3201 := by
  intro i hlo hhi
  have h : i = 3200 := by omega
  subst i
  exact disposition_at_3200


theorem disposition_interval_3201 : Interval dispositionTest 3201 3202 := by
  intro i hlo hhi
  have h : i = 3201 := by omega
  subst i
  exact disposition_at_3201


theorem disposition_interval_3202 : Interval dispositionTest 3202 3203 := by
  intro i hlo hhi
  have h : i = 3202 := by omega
  subst i
  exact disposition_at_3202


theorem disposition_interval_3203 : Interval dispositionTest 3203 3204 := by
  intro i hlo hhi
  have h : i = 3203 := by omega
  subst i
  exact disposition_at_3203


theorem disposition_interval_3204 : Interval dispositionTest 3204 3205 := by
  intro i hlo hhi
  have h : i = 3204 := by omega
  subst i
  exact disposition_at_3204


theorem disposition_interval_3205 : Interval dispositionTest 3205 3206 := by
  intro i hlo hhi
  have h : i = 3205 := by omega
  subst i
  exact disposition_at_3205


theorem disposition_interval_3206 : Interval dispositionTest 3206 3207 := by
  intro i hlo hhi
  have h : i = 3206 := by omega
  subst i
  exact disposition_at_3206


theorem disposition_interval_3207 : Interval dispositionTest 3207 3208 := by
  intro i hlo hhi
  have h : i = 3207 := by omega
  subst i
  exact disposition_at_3207


theorem disposition_interval_3208 : Interval dispositionTest 3208 3209 := by
  intro i hlo hhi
  have h : i = 3208 := by omega
  subst i
  exact disposition_at_3208


theorem disposition_interval_3209 : Interval dispositionTest 3209 3210 := by
  intro i hlo hhi
  have h : i = 3209 := by omega
  subst i
  exact disposition_at_3209


theorem disposition_interval_3210 : Interval dispositionTest 3210 3211 := by
  intro i hlo hhi
  have h : i = 3210 := by omega
  subst i
  exact disposition_at_3210


theorem disposition_interval_3211 : Interval dispositionTest 3211 3212 := by
  intro i hlo hhi
  have h : i = 3211 := by omega
  subst i
  exact disposition_at_3211


theorem disposition_interval_3212 : Interval dispositionTest 3212 3213 := by
  intro i hlo hhi
  have h : i = 3212 := by omega
  subst i
  exact disposition_at_3212


theorem disposition_interval_3213 : Interval dispositionTest 3213 3214 := by
  intro i hlo hhi
  have h : i = 3213 := by omega
  subst i
  exact disposition_at_3213


theorem disposition_interval_3214 : Interval dispositionTest 3214 3215 := by
  intro i hlo hhi
  have h : i = 3214 := by omega
  subst i
  exact disposition_at_3214


theorem disposition_interval_3215 : Interval dispositionTest 3215 3216 := by
  intro i hlo hhi
  have h : i = 3215 := by omega
  subst i
  exact disposition_at_3215


theorem disposition_interval_3216 : Interval dispositionTest 3216 3217 := by
  intro i hlo hhi
  have h : i = 3216 := by omega
  subst i
  exact disposition_at_3216


theorem disposition_interval_3217 : Interval dispositionTest 3217 3218 := by
  intro i hlo hhi
  have h : i = 3217 := by omega
  subst i
  exact disposition_at_3217


theorem disposition_interval_3218 : Interval dispositionTest 3218 3219 := by
  intro i hlo hhi
  have h : i = 3218 := by omega
  subst i
  exact disposition_at_3218


theorem disposition_interval_3219 : Interval dispositionTest 3219 3220 := by
  intro i hlo hhi
  have h : i = 3219 := by omega
  subst i
  exact disposition_at_3219


theorem disposition_interval_3220 : Interval dispositionTest 3220 3221 := by
  intro i hlo hhi
  have h : i = 3220 := by omega
  subst i
  exact disposition_at_3220


theorem disposition_interval_3221 : Interval dispositionTest 3221 3222 := by
  intro i hlo hhi
  have h : i = 3221 := by omega
  subst i
  exact disposition_at_3221


theorem disposition_interval_3222 : Interval dispositionTest 3222 3223 := by
  intro i hlo hhi
  have h : i = 3222 := by omega
  subst i
  exact disposition_at_3222


theorem disposition_interval_3223 : Interval dispositionTest 3223 3224 := by
  intro i hlo hhi
  have h : i = 3223 := by omega
  subst i
  exact disposition_at_3223


theorem disposition_interval_3224 : Interval dispositionTest 3224 3225 := by
  intro i hlo hhi
  have h : i = 3224 := by omega
  subst i
  exact disposition_at_3224


theorem disposition_interval_3225 : Interval dispositionTest 3225 3226 := by
  intro i hlo hhi
  have h : i = 3225 := by omega
  subst i
  exact disposition_at_3225


theorem disposition_interval_3226 : Interval dispositionTest 3226 3227 := by
  intro i hlo hhi
  have h : i = 3226 := by omega
  subst i
  exact disposition_at_3226


theorem disposition_interval_3227 : Interval dispositionTest 3227 3228 := by
  intro i hlo hhi
  have h : i = 3227 := by omega
  subst i
  exact disposition_at_3227


theorem disposition_interval_3228 : Interval dispositionTest 3228 3229 := by
  intro i hlo hhi
  have h : i = 3228 := by omega
  subst i
  exact disposition_at_3228


theorem disposition_interval_3229 : Interval dispositionTest 3229 3230 := by
  intro i hlo hhi
  have h : i = 3229 := by omega
  subst i
  exact disposition_at_3229


theorem disposition_interval_3230 : Interval dispositionTest 3230 3231 := by
  intro i hlo hhi
  have h : i = 3230 := by omega
  subst i
  exact disposition_at_3230


theorem disposition_interval_3231 : Interval dispositionTest 3231 3232 := by
  intro i hlo hhi
  have h : i = 3231 := by omega
  subst i
  exact disposition_at_3231

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
