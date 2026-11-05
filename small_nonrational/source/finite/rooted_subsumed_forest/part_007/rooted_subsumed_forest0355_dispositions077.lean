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
theorem disposition_at_2464 : dispositionTest 2464 = true := by decide +kernel

theorem disposition_at_2465 : dispositionTest 2465 = true := by decide +kernel

theorem disposition_at_2466 : dispositionTest 2466 = true := by decide +kernel

theorem disposition_at_2467 : dispositionTest 2467 = true := by decide +kernel

theorem disposition_at_2468 : dispositionTest 2468 = true := by decide +kernel


theorem disposition_at_2469 : dispositionTest 2469 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2469).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1041.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1041) = true
  rw [Nonrational.OldTerminalMatches.M016.r1041_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_2470 : dispositionTest 2470 = true := by decide +kernel

theorem disposition_at_2471 : dispositionTest 2471 = true := by decide +kernel

theorem disposition_at_2472 : dispositionTest 2472 = true := by decide +kernel

theorem disposition_at_2473 : dispositionTest 2473 = true := by decide +kernel

theorem disposition_at_2474 : dispositionTest 2474 = true := by decide +kernel

theorem disposition_at_2475 : dispositionTest 2475 = true := by decide +kernel

theorem disposition_at_2476 : dispositionTest 2476 = true := by decide +kernel

theorem disposition_at_2477 : dispositionTest 2477 = true := by decide +kernel

theorem disposition_at_2478 : dispositionTest 2478 = true := by decide +kernel

theorem disposition_at_2479 : dispositionTest 2479 = true := by decide +kernel

theorem disposition_at_2480 : dispositionTest 2480 = true := by decide +kernel

theorem disposition_at_2481 : dispositionTest 2481 = true := by decide +kernel

theorem disposition_at_2482 : dispositionTest 2482 = true := by decide +kernel

theorem disposition_at_2483 : dispositionTest 2483 = true := by decide +kernel

theorem disposition_at_2484 : dispositionTest 2484 = true := by decide +kernel


theorem disposition_at_2485 : dispositionTest 2485 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2485).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1042.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1042) = true
  rw [Nonrational.OldTerminalMatches.M016.r1042_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_2486 : dispositionTest 2486 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2486).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1043.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1043) = true
  rw [Nonrational.OldTerminalMatches.M016.r1043_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_2487 : dispositionTest 2487 = true := by decide +kernel

theorem disposition_at_2488 : dispositionTest 2488 = true := by decide +kernel

theorem disposition_at_2489 : dispositionTest 2489 = true := by decide +kernel

theorem disposition_at_2490 : dispositionTest 2490 = true := by decide +kernel

theorem disposition_at_2491 : dispositionTest 2491 = true := by decide +kernel

theorem disposition_at_2492 : dispositionTest 2492 = true := by decide +kernel

theorem disposition_at_2493 : dispositionTest 2493 = true := by decide +kernel

theorem disposition_at_2494 : dispositionTest 2494 = true := by decide +kernel

theorem disposition_at_2495 : dispositionTest 2495 = true := by decide +kernel

theorem disposition_interval_2464 : Interval dispositionTest 2464 2465 := by
  intro i hlo hhi
  have h : i = 2464 := by omega
  subst i
  exact disposition_at_2464


theorem disposition_interval_2465 : Interval dispositionTest 2465 2466 := by
  intro i hlo hhi
  have h : i = 2465 := by omega
  subst i
  exact disposition_at_2465


theorem disposition_interval_2466 : Interval dispositionTest 2466 2467 := by
  intro i hlo hhi
  have h : i = 2466 := by omega
  subst i
  exact disposition_at_2466


theorem disposition_interval_2467 : Interval dispositionTest 2467 2468 := by
  intro i hlo hhi
  have h : i = 2467 := by omega
  subst i
  exact disposition_at_2467


theorem disposition_interval_2468 : Interval dispositionTest 2468 2469 := by
  intro i hlo hhi
  have h : i = 2468 := by omega
  subst i
  exact disposition_at_2468


theorem disposition_interval_2469 : Interval dispositionTest 2469 2470 := by
  intro i hlo hhi
  have h : i = 2469 := by omega
  subst i
  exact disposition_at_2469


theorem disposition_interval_2470 : Interval dispositionTest 2470 2471 := by
  intro i hlo hhi
  have h : i = 2470 := by omega
  subst i
  exact disposition_at_2470


theorem disposition_interval_2471 : Interval dispositionTest 2471 2472 := by
  intro i hlo hhi
  have h : i = 2471 := by omega
  subst i
  exact disposition_at_2471


theorem disposition_interval_2472 : Interval dispositionTest 2472 2473 := by
  intro i hlo hhi
  have h : i = 2472 := by omega
  subst i
  exact disposition_at_2472


theorem disposition_interval_2473 : Interval dispositionTest 2473 2474 := by
  intro i hlo hhi
  have h : i = 2473 := by omega
  subst i
  exact disposition_at_2473


theorem disposition_interval_2474 : Interval dispositionTest 2474 2475 := by
  intro i hlo hhi
  have h : i = 2474 := by omega
  subst i
  exact disposition_at_2474


theorem disposition_interval_2475 : Interval dispositionTest 2475 2476 := by
  intro i hlo hhi
  have h : i = 2475 := by omega
  subst i
  exact disposition_at_2475


theorem disposition_interval_2476 : Interval dispositionTest 2476 2477 := by
  intro i hlo hhi
  have h : i = 2476 := by omega
  subst i
  exact disposition_at_2476


theorem disposition_interval_2477 : Interval dispositionTest 2477 2478 := by
  intro i hlo hhi
  have h : i = 2477 := by omega
  subst i
  exact disposition_at_2477


theorem disposition_interval_2478 : Interval dispositionTest 2478 2479 := by
  intro i hlo hhi
  have h : i = 2478 := by omega
  subst i
  exact disposition_at_2478


theorem disposition_interval_2479 : Interval dispositionTest 2479 2480 := by
  intro i hlo hhi
  have h : i = 2479 := by omega
  subst i
  exact disposition_at_2479


theorem disposition_interval_2480 : Interval dispositionTest 2480 2481 := by
  intro i hlo hhi
  have h : i = 2480 := by omega
  subst i
  exact disposition_at_2480


theorem disposition_interval_2481 : Interval dispositionTest 2481 2482 := by
  intro i hlo hhi
  have h : i = 2481 := by omega
  subst i
  exact disposition_at_2481


theorem disposition_interval_2482 : Interval dispositionTest 2482 2483 := by
  intro i hlo hhi
  have h : i = 2482 := by omega
  subst i
  exact disposition_at_2482


theorem disposition_interval_2483 : Interval dispositionTest 2483 2484 := by
  intro i hlo hhi
  have h : i = 2483 := by omega
  subst i
  exact disposition_at_2483


theorem disposition_interval_2484 : Interval dispositionTest 2484 2485 := by
  intro i hlo hhi
  have h : i = 2484 := by omega
  subst i
  exact disposition_at_2484


theorem disposition_interval_2485 : Interval dispositionTest 2485 2486 := by
  intro i hlo hhi
  have h : i = 2485 := by omega
  subst i
  exact disposition_at_2485


theorem disposition_interval_2486 : Interval dispositionTest 2486 2487 := by
  intro i hlo hhi
  have h : i = 2486 := by omega
  subst i
  exact disposition_at_2486


theorem disposition_interval_2487 : Interval dispositionTest 2487 2488 := by
  intro i hlo hhi
  have h : i = 2487 := by omega
  subst i
  exact disposition_at_2487


theorem disposition_interval_2488 : Interval dispositionTest 2488 2489 := by
  intro i hlo hhi
  have h : i = 2488 := by omega
  subst i
  exact disposition_at_2488


theorem disposition_interval_2489 : Interval dispositionTest 2489 2490 := by
  intro i hlo hhi
  have h : i = 2489 := by omega
  subst i
  exact disposition_at_2489


theorem disposition_interval_2490 : Interval dispositionTest 2490 2491 := by
  intro i hlo hhi
  have h : i = 2490 := by omega
  subst i
  exact disposition_at_2490


theorem disposition_interval_2491 : Interval dispositionTest 2491 2492 := by
  intro i hlo hhi
  have h : i = 2491 := by omega
  subst i
  exact disposition_at_2491


theorem disposition_interval_2492 : Interval dispositionTest 2492 2493 := by
  intro i hlo hhi
  have h : i = 2492 := by omega
  subst i
  exact disposition_at_2492


theorem disposition_interval_2493 : Interval dispositionTest 2493 2494 := by
  intro i hlo hhi
  have h : i = 2493 := by omega
  subst i
  exact disposition_at_2493


theorem disposition_interval_2494 : Interval dispositionTest 2494 2495 := by
  intro i hlo hhi
  have h : i = 2494 := by omega
  subst i
  exact disposition_at_2494


theorem disposition_interval_2495 : Interval dispositionTest 2495 2496 := by
  intro i hlo hhi
  have h : i = 2495 := by omega
  subst i
  exact disposition_at_2495

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
