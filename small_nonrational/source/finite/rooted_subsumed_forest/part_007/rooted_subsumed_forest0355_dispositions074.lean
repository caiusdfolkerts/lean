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
theorem disposition_at_2368 : dispositionTest 2368 = true := by decide +kernel

theorem disposition_at_2369 : dispositionTest 2369 = true := by decide +kernel

theorem disposition_at_2370 : dispositionTest 2370 = true := by decide +kernel

theorem disposition_at_2371 : dispositionTest 2371 = true := by decide +kernel

theorem disposition_at_2372 : dispositionTest 2372 = true := by decide +kernel

theorem disposition_at_2373 : dispositionTest 2373 = true := by decide +kernel

theorem disposition_at_2374 : dispositionTest 2374 = true := by decide +kernel

theorem disposition_at_2375 : dispositionTest 2375 = true := by decide +kernel

theorem disposition_at_2376 : dispositionTest 2376 = true := by decide +kernel

theorem disposition_at_2377 : dispositionTest 2377 = true := by decide +kernel

theorem disposition_at_2378 : dispositionTest 2378 = true := by decide +kernel

theorem disposition_at_2379 : dispositionTest 2379 = true := by decide +kernel

theorem disposition_at_2380 : dispositionTest 2380 = true := by decide +kernel

theorem disposition_at_2381 : dispositionTest 2381 = true := by decide +kernel

theorem disposition_at_2382 : dispositionTest 2382 = true := by decide +kernel

theorem disposition_at_2383 : dispositionTest 2383 = true := by decide +kernel

theorem disposition_at_2384 : dispositionTest 2384 = true := by decide +kernel

theorem disposition_at_2385 : dispositionTest 2385 = true := by decide +kernel

theorem disposition_at_2386 : dispositionTest 2386 = true := by decide +kernel

theorem disposition_at_2387 : dispositionTest 2387 = true := by decide +kernel

theorem disposition_at_2388 : dispositionTest 2388 = true := by decide +kernel

theorem disposition_at_2389 : dispositionTest 2389 = true := by decide +kernel


theorem disposition_at_2390 : dispositionTest 2390 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2390).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1040.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1040) = true
  rw [Nonrational.OldTerminalMatches.M016.r1040_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_2391 : dispositionTest 2391 = true := by decide +kernel

theorem disposition_at_2392 : dispositionTest 2392 = true := by decide +kernel

theorem disposition_at_2393 : dispositionTest 2393 = true := by decide +kernel

theorem disposition_at_2394 : dispositionTest 2394 = true := by decide +kernel

theorem disposition_at_2395 : dispositionTest 2395 = true := by decide +kernel

theorem disposition_at_2396 : dispositionTest 2396 = true := by decide +kernel

theorem disposition_at_2397 : dispositionTest 2397 = true := by decide +kernel

theorem disposition_at_2398 : dispositionTest 2398 = true := by decide +kernel

theorem disposition_at_2399 : dispositionTest 2399 = true := by decide +kernel

theorem disposition_interval_2368 : Interval dispositionTest 2368 2369 := by
  intro i hlo hhi
  have h : i = 2368 := by omega
  subst i
  exact disposition_at_2368


theorem disposition_interval_2369 : Interval dispositionTest 2369 2370 := by
  intro i hlo hhi
  have h : i = 2369 := by omega
  subst i
  exact disposition_at_2369


theorem disposition_interval_2370 : Interval dispositionTest 2370 2371 := by
  intro i hlo hhi
  have h : i = 2370 := by omega
  subst i
  exact disposition_at_2370


theorem disposition_interval_2371 : Interval dispositionTest 2371 2372 := by
  intro i hlo hhi
  have h : i = 2371 := by omega
  subst i
  exact disposition_at_2371


theorem disposition_interval_2372 : Interval dispositionTest 2372 2373 := by
  intro i hlo hhi
  have h : i = 2372 := by omega
  subst i
  exact disposition_at_2372


theorem disposition_interval_2373 : Interval dispositionTest 2373 2374 := by
  intro i hlo hhi
  have h : i = 2373 := by omega
  subst i
  exact disposition_at_2373


theorem disposition_interval_2374 : Interval dispositionTest 2374 2375 := by
  intro i hlo hhi
  have h : i = 2374 := by omega
  subst i
  exact disposition_at_2374


theorem disposition_interval_2375 : Interval dispositionTest 2375 2376 := by
  intro i hlo hhi
  have h : i = 2375 := by omega
  subst i
  exact disposition_at_2375


theorem disposition_interval_2376 : Interval dispositionTest 2376 2377 := by
  intro i hlo hhi
  have h : i = 2376 := by omega
  subst i
  exact disposition_at_2376


theorem disposition_interval_2377 : Interval dispositionTest 2377 2378 := by
  intro i hlo hhi
  have h : i = 2377 := by omega
  subst i
  exact disposition_at_2377


theorem disposition_interval_2378 : Interval dispositionTest 2378 2379 := by
  intro i hlo hhi
  have h : i = 2378 := by omega
  subst i
  exact disposition_at_2378


theorem disposition_interval_2379 : Interval dispositionTest 2379 2380 := by
  intro i hlo hhi
  have h : i = 2379 := by omega
  subst i
  exact disposition_at_2379


theorem disposition_interval_2380 : Interval dispositionTest 2380 2381 := by
  intro i hlo hhi
  have h : i = 2380 := by omega
  subst i
  exact disposition_at_2380


theorem disposition_interval_2381 : Interval dispositionTest 2381 2382 := by
  intro i hlo hhi
  have h : i = 2381 := by omega
  subst i
  exact disposition_at_2381


theorem disposition_interval_2382 : Interval dispositionTest 2382 2383 := by
  intro i hlo hhi
  have h : i = 2382 := by omega
  subst i
  exact disposition_at_2382


theorem disposition_interval_2383 : Interval dispositionTest 2383 2384 := by
  intro i hlo hhi
  have h : i = 2383 := by omega
  subst i
  exact disposition_at_2383


theorem disposition_interval_2384 : Interval dispositionTest 2384 2385 := by
  intro i hlo hhi
  have h : i = 2384 := by omega
  subst i
  exact disposition_at_2384


theorem disposition_interval_2385 : Interval dispositionTest 2385 2386 := by
  intro i hlo hhi
  have h : i = 2385 := by omega
  subst i
  exact disposition_at_2385


theorem disposition_interval_2386 : Interval dispositionTest 2386 2387 := by
  intro i hlo hhi
  have h : i = 2386 := by omega
  subst i
  exact disposition_at_2386


theorem disposition_interval_2387 : Interval dispositionTest 2387 2388 := by
  intro i hlo hhi
  have h : i = 2387 := by omega
  subst i
  exact disposition_at_2387


theorem disposition_interval_2388 : Interval dispositionTest 2388 2389 := by
  intro i hlo hhi
  have h : i = 2388 := by omega
  subst i
  exact disposition_at_2388


theorem disposition_interval_2389 : Interval dispositionTest 2389 2390 := by
  intro i hlo hhi
  have h : i = 2389 := by omega
  subst i
  exact disposition_at_2389


theorem disposition_interval_2390 : Interval dispositionTest 2390 2391 := by
  intro i hlo hhi
  have h : i = 2390 := by omega
  subst i
  exact disposition_at_2390


theorem disposition_interval_2391 : Interval dispositionTest 2391 2392 := by
  intro i hlo hhi
  have h : i = 2391 := by omega
  subst i
  exact disposition_at_2391


theorem disposition_interval_2392 : Interval dispositionTest 2392 2393 := by
  intro i hlo hhi
  have h : i = 2392 := by omega
  subst i
  exact disposition_at_2392


theorem disposition_interval_2393 : Interval dispositionTest 2393 2394 := by
  intro i hlo hhi
  have h : i = 2393 := by omega
  subst i
  exact disposition_at_2393


theorem disposition_interval_2394 : Interval dispositionTest 2394 2395 := by
  intro i hlo hhi
  have h : i = 2394 := by omega
  subst i
  exact disposition_at_2394


theorem disposition_interval_2395 : Interval dispositionTest 2395 2396 := by
  intro i hlo hhi
  have h : i = 2395 := by omega
  subst i
  exact disposition_at_2395


theorem disposition_interval_2396 : Interval dispositionTest 2396 2397 := by
  intro i hlo hhi
  have h : i = 2396 := by omega
  subst i
  exact disposition_at_2396


theorem disposition_interval_2397 : Interval dispositionTest 2397 2398 := by
  intro i hlo hhi
  have h : i = 2397 := by omega
  subst i
  exact disposition_at_2397


theorem disposition_interval_2398 : Interval dispositionTest 2398 2399 := by
  intro i hlo hhi
  have h : i = 2398 := by omega
  subst i
  exact disposition_at_2398


theorem disposition_interval_2399 : Interval dispositionTest 2399 2400 := by
  intro i hlo hhi
  have h : i = 2399 := by omega
  subst i
  exact disposition_at_2399

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
