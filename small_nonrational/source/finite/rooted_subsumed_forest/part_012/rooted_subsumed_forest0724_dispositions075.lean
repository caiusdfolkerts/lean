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
theorem disposition_at_2400 : dispositionTest 2400 = true := by decide +kernel

theorem disposition_at_2401 : dispositionTest 2401 = true := by decide +kernel

theorem disposition_at_2402 : dispositionTest 2402 = true := by decide +kernel

theorem disposition_at_2403 : dispositionTest 2403 = true := by decide +kernel

theorem disposition_at_2404 : dispositionTest 2404 = true := by decide +kernel

theorem disposition_at_2405 : dispositionTest 2405 = true := by decide +kernel

theorem disposition_at_2406 : dispositionTest 2406 = true := by decide +kernel

theorem disposition_at_2407 : dispositionTest 2407 = true := by decide +kernel

theorem disposition_at_2408 : dispositionTest 2408 = true := by decide +kernel

theorem disposition_at_2409 : dispositionTest 2409 = true := by decide +kernel

theorem disposition_at_2410 : dispositionTest 2410 = true := by decide +kernel

theorem disposition_at_2411 : dispositionTest 2411 = true := by decide +kernel

theorem disposition_at_2412 : dispositionTest 2412 = true := by decide +kernel

theorem disposition_at_2413 : dispositionTest 2413 = true := by decide +kernel

theorem disposition_at_2414 : dispositionTest 2414 = true := by decide +kernel

theorem disposition_at_2415 : dispositionTest 2415 = true := by decide +kernel

theorem disposition_at_2416 : dispositionTest 2416 = true := by decide +kernel

theorem disposition_at_2417 : dispositionTest 2417 = true := by decide +kernel

theorem disposition_at_2418 : dispositionTest 2418 = true := by decide +kernel

theorem disposition_at_2419 : dispositionTest 2419 = true := by decide +kernel

theorem disposition_at_2420 : dispositionTest 2420 = true := by decide +kernel

theorem disposition_at_2421 : dispositionTest 2421 = true := by decide +kernel

theorem disposition_at_2422 : dispositionTest 2422 = true := by decide +kernel

theorem disposition_at_2423 : dispositionTest 2423 = true := by decide +kernel

theorem disposition_at_2424 : dispositionTest 2424 = true := by decide +kernel

theorem disposition_at_2425 : dispositionTest 2425 = true := by decide +kernel

theorem disposition_at_2426 : dispositionTest 2426 = true := by decide +kernel

theorem disposition_at_2427 : dispositionTest 2427 = true := by decide +kernel

theorem disposition_at_2428 : dispositionTest 2428 = true := by decide +kernel

theorem disposition_at_2429 : dispositionTest 2429 = true := by decide +kernel

theorem disposition_at_2430 : dispositionTest 2430 = true := by decide +kernel

theorem disposition_at_2431 : dispositionTest 2431 = true := by decide +kernel

theorem disposition_interval_2400 : Interval dispositionTest 2400 2401 := by
  intro i hlo hhi
  have h : i = 2400 := by omega
  subst i
  exact disposition_at_2400


theorem disposition_interval_2401 : Interval dispositionTest 2401 2402 := by
  intro i hlo hhi
  have h : i = 2401 := by omega
  subst i
  exact disposition_at_2401


theorem disposition_interval_2402 : Interval dispositionTest 2402 2403 := by
  intro i hlo hhi
  have h : i = 2402 := by omega
  subst i
  exact disposition_at_2402


theorem disposition_interval_2403 : Interval dispositionTest 2403 2404 := by
  intro i hlo hhi
  have h : i = 2403 := by omega
  subst i
  exact disposition_at_2403


theorem disposition_interval_2404 : Interval dispositionTest 2404 2405 := by
  intro i hlo hhi
  have h : i = 2404 := by omega
  subst i
  exact disposition_at_2404


theorem disposition_interval_2405 : Interval dispositionTest 2405 2406 := by
  intro i hlo hhi
  have h : i = 2405 := by omega
  subst i
  exact disposition_at_2405


theorem disposition_interval_2406 : Interval dispositionTest 2406 2407 := by
  intro i hlo hhi
  have h : i = 2406 := by omega
  subst i
  exact disposition_at_2406


theorem disposition_interval_2407 : Interval dispositionTest 2407 2408 := by
  intro i hlo hhi
  have h : i = 2407 := by omega
  subst i
  exact disposition_at_2407


theorem disposition_interval_2408 : Interval dispositionTest 2408 2409 := by
  intro i hlo hhi
  have h : i = 2408 := by omega
  subst i
  exact disposition_at_2408


theorem disposition_interval_2409 : Interval dispositionTest 2409 2410 := by
  intro i hlo hhi
  have h : i = 2409 := by omega
  subst i
  exact disposition_at_2409


theorem disposition_interval_2410 : Interval dispositionTest 2410 2411 := by
  intro i hlo hhi
  have h : i = 2410 := by omega
  subst i
  exact disposition_at_2410


theorem disposition_interval_2411 : Interval dispositionTest 2411 2412 := by
  intro i hlo hhi
  have h : i = 2411 := by omega
  subst i
  exact disposition_at_2411


theorem disposition_interval_2412 : Interval dispositionTest 2412 2413 := by
  intro i hlo hhi
  have h : i = 2412 := by omega
  subst i
  exact disposition_at_2412


theorem disposition_interval_2413 : Interval dispositionTest 2413 2414 := by
  intro i hlo hhi
  have h : i = 2413 := by omega
  subst i
  exact disposition_at_2413


theorem disposition_interval_2414 : Interval dispositionTest 2414 2415 := by
  intro i hlo hhi
  have h : i = 2414 := by omega
  subst i
  exact disposition_at_2414


theorem disposition_interval_2415 : Interval dispositionTest 2415 2416 := by
  intro i hlo hhi
  have h : i = 2415 := by omega
  subst i
  exact disposition_at_2415


theorem disposition_interval_2416 : Interval dispositionTest 2416 2417 := by
  intro i hlo hhi
  have h : i = 2416 := by omega
  subst i
  exact disposition_at_2416


theorem disposition_interval_2417 : Interval dispositionTest 2417 2418 := by
  intro i hlo hhi
  have h : i = 2417 := by omega
  subst i
  exact disposition_at_2417


theorem disposition_interval_2418 : Interval dispositionTest 2418 2419 := by
  intro i hlo hhi
  have h : i = 2418 := by omega
  subst i
  exact disposition_at_2418


theorem disposition_interval_2419 : Interval dispositionTest 2419 2420 := by
  intro i hlo hhi
  have h : i = 2419 := by omega
  subst i
  exact disposition_at_2419


theorem disposition_interval_2420 : Interval dispositionTest 2420 2421 := by
  intro i hlo hhi
  have h : i = 2420 := by omega
  subst i
  exact disposition_at_2420


theorem disposition_interval_2421 : Interval dispositionTest 2421 2422 := by
  intro i hlo hhi
  have h : i = 2421 := by omega
  subst i
  exact disposition_at_2421


theorem disposition_interval_2422 : Interval dispositionTest 2422 2423 := by
  intro i hlo hhi
  have h : i = 2422 := by omega
  subst i
  exact disposition_at_2422


theorem disposition_interval_2423 : Interval dispositionTest 2423 2424 := by
  intro i hlo hhi
  have h : i = 2423 := by omega
  subst i
  exact disposition_at_2423


theorem disposition_interval_2424 : Interval dispositionTest 2424 2425 := by
  intro i hlo hhi
  have h : i = 2424 := by omega
  subst i
  exact disposition_at_2424


theorem disposition_interval_2425 : Interval dispositionTest 2425 2426 := by
  intro i hlo hhi
  have h : i = 2425 := by omega
  subst i
  exact disposition_at_2425


theorem disposition_interval_2426 : Interval dispositionTest 2426 2427 := by
  intro i hlo hhi
  have h : i = 2426 := by omega
  subst i
  exact disposition_at_2426


theorem disposition_interval_2427 : Interval dispositionTest 2427 2428 := by
  intro i hlo hhi
  have h : i = 2427 := by omega
  subst i
  exact disposition_at_2427


theorem disposition_interval_2428 : Interval dispositionTest 2428 2429 := by
  intro i hlo hhi
  have h : i = 2428 := by omega
  subst i
  exact disposition_at_2428


theorem disposition_interval_2429 : Interval dispositionTest 2429 2430 := by
  intro i hlo hhi
  have h : i = 2429 := by omega
  subst i
  exact disposition_at_2429


theorem disposition_interval_2430 : Interval dispositionTest 2430 2431 := by
  intro i hlo hhi
  have h : i = 2430 := by omega
  subst i
  exact disposition_at_2430


theorem disposition_interval_2431 : Interval dispositionTest 2431 2432 := by
  intro i hlo hhi
  have h : i = 2431 := by omega
  subst i
  exact disposition_at_2431

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
