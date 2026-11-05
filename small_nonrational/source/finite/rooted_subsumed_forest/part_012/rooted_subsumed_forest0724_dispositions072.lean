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
theorem disposition_at_2304 : dispositionTest 2304 = true := by decide +kernel

theorem disposition_at_2305 : dispositionTest 2305 = true := by decide +kernel

theorem disposition_at_2306 : dispositionTest 2306 = true := by decide +kernel

theorem disposition_at_2307 : dispositionTest 2307 = true := by decide +kernel

theorem disposition_at_2308 : dispositionTest 2308 = true := by decide +kernel

theorem disposition_at_2309 : dispositionTest 2309 = true := by decide +kernel

theorem disposition_at_2310 : dispositionTest 2310 = true := by decide +kernel

theorem disposition_at_2311 : dispositionTest 2311 = true := by decide +kernel

theorem disposition_at_2312 : dispositionTest 2312 = true := by decide +kernel

theorem disposition_at_2313 : dispositionTest 2313 = true := by decide +kernel

theorem disposition_at_2314 : dispositionTest 2314 = true := by decide +kernel

theorem disposition_at_2315 : dispositionTest 2315 = true := by decide +kernel

theorem disposition_at_2316 : dispositionTest 2316 = true := by decide +kernel

theorem disposition_at_2317 : dispositionTest 2317 = true := by decide +kernel

theorem disposition_at_2318 : dispositionTest 2318 = true := by decide +kernel

theorem disposition_at_2319 : dispositionTest 2319 = true := by decide +kernel

theorem disposition_at_2320 : dispositionTest 2320 = true := by decide +kernel

theorem disposition_at_2321 : dispositionTest 2321 = true := by decide +kernel

theorem disposition_at_2322 : dispositionTest 2322 = true := by decide +kernel

theorem disposition_at_2323 : dispositionTest 2323 = true := by decide +kernel

theorem disposition_at_2324 : dispositionTest 2324 = true := by decide +kernel

theorem disposition_at_2325 : dispositionTest 2325 = true := by decide +kernel

theorem disposition_at_2326 : dispositionTest 2326 = true := by decide +kernel

theorem disposition_at_2327 : dispositionTest 2327 = true := by decide +kernel

theorem disposition_at_2328 : dispositionTest 2328 = true := by decide +kernel

theorem disposition_at_2329 : dispositionTest 2329 = true := by decide +kernel

theorem disposition_at_2330 : dispositionTest 2330 = true := by decide +kernel

theorem disposition_at_2331 : dispositionTest 2331 = true := by decide +kernel

theorem disposition_at_2332 : dispositionTest 2332 = true := by decide +kernel

theorem disposition_at_2333 : dispositionTest 2333 = true := by decide +kernel

theorem disposition_at_2334 : dispositionTest 2334 = true := by decide +kernel

theorem disposition_at_2335 : dispositionTest 2335 = true := by decide +kernel

theorem disposition_interval_2304 : Interval dispositionTest 2304 2305 := by
  intro i hlo hhi
  have h : i = 2304 := by omega
  subst i
  exact disposition_at_2304


theorem disposition_interval_2305 : Interval dispositionTest 2305 2306 := by
  intro i hlo hhi
  have h : i = 2305 := by omega
  subst i
  exact disposition_at_2305


theorem disposition_interval_2306 : Interval dispositionTest 2306 2307 := by
  intro i hlo hhi
  have h : i = 2306 := by omega
  subst i
  exact disposition_at_2306


theorem disposition_interval_2307 : Interval dispositionTest 2307 2308 := by
  intro i hlo hhi
  have h : i = 2307 := by omega
  subst i
  exact disposition_at_2307


theorem disposition_interval_2308 : Interval dispositionTest 2308 2309 := by
  intro i hlo hhi
  have h : i = 2308 := by omega
  subst i
  exact disposition_at_2308


theorem disposition_interval_2309 : Interval dispositionTest 2309 2310 := by
  intro i hlo hhi
  have h : i = 2309 := by omega
  subst i
  exact disposition_at_2309


theorem disposition_interval_2310 : Interval dispositionTest 2310 2311 := by
  intro i hlo hhi
  have h : i = 2310 := by omega
  subst i
  exact disposition_at_2310


theorem disposition_interval_2311 : Interval dispositionTest 2311 2312 := by
  intro i hlo hhi
  have h : i = 2311 := by omega
  subst i
  exact disposition_at_2311


theorem disposition_interval_2312 : Interval dispositionTest 2312 2313 := by
  intro i hlo hhi
  have h : i = 2312 := by omega
  subst i
  exact disposition_at_2312


theorem disposition_interval_2313 : Interval dispositionTest 2313 2314 := by
  intro i hlo hhi
  have h : i = 2313 := by omega
  subst i
  exact disposition_at_2313


theorem disposition_interval_2314 : Interval dispositionTest 2314 2315 := by
  intro i hlo hhi
  have h : i = 2314 := by omega
  subst i
  exact disposition_at_2314


theorem disposition_interval_2315 : Interval dispositionTest 2315 2316 := by
  intro i hlo hhi
  have h : i = 2315 := by omega
  subst i
  exact disposition_at_2315


theorem disposition_interval_2316 : Interval dispositionTest 2316 2317 := by
  intro i hlo hhi
  have h : i = 2316 := by omega
  subst i
  exact disposition_at_2316


theorem disposition_interval_2317 : Interval dispositionTest 2317 2318 := by
  intro i hlo hhi
  have h : i = 2317 := by omega
  subst i
  exact disposition_at_2317


theorem disposition_interval_2318 : Interval dispositionTest 2318 2319 := by
  intro i hlo hhi
  have h : i = 2318 := by omega
  subst i
  exact disposition_at_2318


theorem disposition_interval_2319 : Interval dispositionTest 2319 2320 := by
  intro i hlo hhi
  have h : i = 2319 := by omega
  subst i
  exact disposition_at_2319


theorem disposition_interval_2320 : Interval dispositionTest 2320 2321 := by
  intro i hlo hhi
  have h : i = 2320 := by omega
  subst i
  exact disposition_at_2320


theorem disposition_interval_2321 : Interval dispositionTest 2321 2322 := by
  intro i hlo hhi
  have h : i = 2321 := by omega
  subst i
  exact disposition_at_2321


theorem disposition_interval_2322 : Interval dispositionTest 2322 2323 := by
  intro i hlo hhi
  have h : i = 2322 := by omega
  subst i
  exact disposition_at_2322


theorem disposition_interval_2323 : Interval dispositionTest 2323 2324 := by
  intro i hlo hhi
  have h : i = 2323 := by omega
  subst i
  exact disposition_at_2323


theorem disposition_interval_2324 : Interval dispositionTest 2324 2325 := by
  intro i hlo hhi
  have h : i = 2324 := by omega
  subst i
  exact disposition_at_2324


theorem disposition_interval_2325 : Interval dispositionTest 2325 2326 := by
  intro i hlo hhi
  have h : i = 2325 := by omega
  subst i
  exact disposition_at_2325


theorem disposition_interval_2326 : Interval dispositionTest 2326 2327 := by
  intro i hlo hhi
  have h : i = 2326 := by omega
  subst i
  exact disposition_at_2326


theorem disposition_interval_2327 : Interval dispositionTest 2327 2328 := by
  intro i hlo hhi
  have h : i = 2327 := by omega
  subst i
  exact disposition_at_2327


theorem disposition_interval_2328 : Interval dispositionTest 2328 2329 := by
  intro i hlo hhi
  have h : i = 2328 := by omega
  subst i
  exact disposition_at_2328


theorem disposition_interval_2329 : Interval dispositionTest 2329 2330 := by
  intro i hlo hhi
  have h : i = 2329 := by omega
  subst i
  exact disposition_at_2329


theorem disposition_interval_2330 : Interval dispositionTest 2330 2331 := by
  intro i hlo hhi
  have h : i = 2330 := by omega
  subst i
  exact disposition_at_2330


theorem disposition_interval_2331 : Interval dispositionTest 2331 2332 := by
  intro i hlo hhi
  have h : i = 2331 := by omega
  subst i
  exact disposition_at_2331


theorem disposition_interval_2332 : Interval dispositionTest 2332 2333 := by
  intro i hlo hhi
  have h : i = 2332 := by omega
  subst i
  exact disposition_at_2332


theorem disposition_interval_2333 : Interval dispositionTest 2333 2334 := by
  intro i hlo hhi
  have h : i = 2333 := by omega
  subst i
  exact disposition_at_2333


theorem disposition_interval_2334 : Interval dispositionTest 2334 2335 := by
  intro i hlo hhi
  have h : i = 2334 := by omega
  subst i
  exact disposition_at_2334


theorem disposition_interval_2335 : Interval dispositionTest 2335 2336 := by
  intro i hlo hhi
  have h : i = 2335 := by omega
  subst i
  exact disposition_at_2335

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
