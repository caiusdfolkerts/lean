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
theorem disposition_at_2496 : dispositionTest 2496 = true := by decide +kernel

theorem disposition_at_2497 : dispositionTest 2497 = true := by decide +kernel

theorem disposition_at_2498 : dispositionTest 2498 = true := by decide +kernel

theorem disposition_at_2499 : dispositionTest 2499 = true := by decide +kernel

theorem disposition_at_2500 : dispositionTest 2500 = true := by decide +kernel

theorem disposition_at_2501 : dispositionTest 2501 = true := by decide +kernel

theorem disposition_at_2502 : dispositionTest 2502 = true := by decide +kernel

theorem disposition_at_2503 : dispositionTest 2503 = true := by decide +kernel

theorem disposition_at_2504 : dispositionTest 2504 = true := by decide +kernel

theorem disposition_at_2505 : dispositionTest 2505 = true := by decide +kernel

theorem disposition_at_2506 : dispositionTest 2506 = true := by decide +kernel

theorem disposition_at_2507 : dispositionTest 2507 = true := by decide +kernel

theorem disposition_at_2508 : dispositionTest 2508 = true := by decide +kernel

theorem disposition_at_2509 : dispositionTest 2509 = true := by decide +kernel

theorem disposition_at_2510 : dispositionTest 2510 = true := by decide +kernel

theorem disposition_at_2511 : dispositionTest 2511 = true := by decide +kernel

theorem disposition_at_2512 : dispositionTest 2512 = true := by decide +kernel

theorem disposition_at_2513 : dispositionTest 2513 = true := by decide +kernel

theorem disposition_at_2514 : dispositionTest 2514 = true := by decide +kernel

theorem disposition_at_2515 : dispositionTest 2515 = true := by decide +kernel

theorem disposition_at_2516 : dispositionTest 2516 = true := by decide +kernel

theorem disposition_at_2517 : dispositionTest 2517 = true := by decide +kernel

theorem disposition_at_2518 : dispositionTest 2518 = true := by decide +kernel

theorem disposition_at_2519 : dispositionTest 2519 = true := by decide +kernel

theorem disposition_at_2520 : dispositionTest 2520 = true := by decide +kernel

theorem disposition_at_2521 : dispositionTest 2521 = true := by decide +kernel

theorem disposition_at_2522 : dispositionTest 2522 = true := by decide +kernel

theorem disposition_at_2523 : dispositionTest 2523 = true := by decide +kernel

theorem disposition_at_2524 : dispositionTest 2524 = true := by decide +kernel


theorem disposition_at_2525 : dispositionTest 2525 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2525).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1044.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1044) = true
  rw [Nonrational.OldTerminalMatches.M016.r1044_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_2526 : dispositionTest 2526 = true := by decide +kernel


theorem disposition_at_2527 : dispositionTest 2527 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2527).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1045.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1045) = true
  rw [Nonrational.OldTerminalMatches.M016.r1045_checked, Bool.and_true]
  decide +kernel

theorem disposition_interval_2496 : Interval dispositionTest 2496 2497 := by
  intro i hlo hhi
  have h : i = 2496 := by omega
  subst i
  exact disposition_at_2496


theorem disposition_interval_2497 : Interval dispositionTest 2497 2498 := by
  intro i hlo hhi
  have h : i = 2497 := by omega
  subst i
  exact disposition_at_2497


theorem disposition_interval_2498 : Interval dispositionTest 2498 2499 := by
  intro i hlo hhi
  have h : i = 2498 := by omega
  subst i
  exact disposition_at_2498


theorem disposition_interval_2499 : Interval dispositionTest 2499 2500 := by
  intro i hlo hhi
  have h : i = 2499 := by omega
  subst i
  exact disposition_at_2499


theorem disposition_interval_2500 : Interval dispositionTest 2500 2501 := by
  intro i hlo hhi
  have h : i = 2500 := by omega
  subst i
  exact disposition_at_2500


theorem disposition_interval_2501 : Interval dispositionTest 2501 2502 := by
  intro i hlo hhi
  have h : i = 2501 := by omega
  subst i
  exact disposition_at_2501


theorem disposition_interval_2502 : Interval dispositionTest 2502 2503 := by
  intro i hlo hhi
  have h : i = 2502 := by omega
  subst i
  exact disposition_at_2502


theorem disposition_interval_2503 : Interval dispositionTest 2503 2504 := by
  intro i hlo hhi
  have h : i = 2503 := by omega
  subst i
  exact disposition_at_2503


theorem disposition_interval_2504 : Interval dispositionTest 2504 2505 := by
  intro i hlo hhi
  have h : i = 2504 := by omega
  subst i
  exact disposition_at_2504


theorem disposition_interval_2505 : Interval dispositionTest 2505 2506 := by
  intro i hlo hhi
  have h : i = 2505 := by omega
  subst i
  exact disposition_at_2505


theorem disposition_interval_2506 : Interval dispositionTest 2506 2507 := by
  intro i hlo hhi
  have h : i = 2506 := by omega
  subst i
  exact disposition_at_2506


theorem disposition_interval_2507 : Interval dispositionTest 2507 2508 := by
  intro i hlo hhi
  have h : i = 2507 := by omega
  subst i
  exact disposition_at_2507


theorem disposition_interval_2508 : Interval dispositionTest 2508 2509 := by
  intro i hlo hhi
  have h : i = 2508 := by omega
  subst i
  exact disposition_at_2508


theorem disposition_interval_2509 : Interval dispositionTest 2509 2510 := by
  intro i hlo hhi
  have h : i = 2509 := by omega
  subst i
  exact disposition_at_2509


theorem disposition_interval_2510 : Interval dispositionTest 2510 2511 := by
  intro i hlo hhi
  have h : i = 2510 := by omega
  subst i
  exact disposition_at_2510


theorem disposition_interval_2511 : Interval dispositionTest 2511 2512 := by
  intro i hlo hhi
  have h : i = 2511 := by omega
  subst i
  exact disposition_at_2511


theorem disposition_interval_2512 : Interval dispositionTest 2512 2513 := by
  intro i hlo hhi
  have h : i = 2512 := by omega
  subst i
  exact disposition_at_2512


theorem disposition_interval_2513 : Interval dispositionTest 2513 2514 := by
  intro i hlo hhi
  have h : i = 2513 := by omega
  subst i
  exact disposition_at_2513


theorem disposition_interval_2514 : Interval dispositionTest 2514 2515 := by
  intro i hlo hhi
  have h : i = 2514 := by omega
  subst i
  exact disposition_at_2514


theorem disposition_interval_2515 : Interval dispositionTest 2515 2516 := by
  intro i hlo hhi
  have h : i = 2515 := by omega
  subst i
  exact disposition_at_2515


theorem disposition_interval_2516 : Interval dispositionTest 2516 2517 := by
  intro i hlo hhi
  have h : i = 2516 := by omega
  subst i
  exact disposition_at_2516


theorem disposition_interval_2517 : Interval dispositionTest 2517 2518 := by
  intro i hlo hhi
  have h : i = 2517 := by omega
  subst i
  exact disposition_at_2517


theorem disposition_interval_2518 : Interval dispositionTest 2518 2519 := by
  intro i hlo hhi
  have h : i = 2518 := by omega
  subst i
  exact disposition_at_2518


theorem disposition_interval_2519 : Interval dispositionTest 2519 2520 := by
  intro i hlo hhi
  have h : i = 2519 := by omega
  subst i
  exact disposition_at_2519


theorem disposition_interval_2520 : Interval dispositionTest 2520 2521 := by
  intro i hlo hhi
  have h : i = 2520 := by omega
  subst i
  exact disposition_at_2520


theorem disposition_interval_2521 : Interval dispositionTest 2521 2522 := by
  intro i hlo hhi
  have h : i = 2521 := by omega
  subst i
  exact disposition_at_2521


theorem disposition_interval_2522 : Interval dispositionTest 2522 2523 := by
  intro i hlo hhi
  have h : i = 2522 := by omega
  subst i
  exact disposition_at_2522


theorem disposition_interval_2523 : Interval dispositionTest 2523 2524 := by
  intro i hlo hhi
  have h : i = 2523 := by omega
  subst i
  exact disposition_at_2523


theorem disposition_interval_2524 : Interval dispositionTest 2524 2525 := by
  intro i hlo hhi
  have h : i = 2524 := by omega
  subst i
  exact disposition_at_2524


theorem disposition_interval_2525 : Interval dispositionTest 2525 2526 := by
  intro i hlo hhi
  have h : i = 2525 := by omega
  subst i
  exact disposition_at_2525


theorem disposition_interval_2526 : Interval dispositionTest 2526 2527 := by
  intro i hlo hhi
  have h : i = 2526 := by omega
  subst i
  exact disposition_at_2526


theorem disposition_interval_2527 : Interval dispositionTest 2527 2528 := by
  intro i hlo hhi
  have h : i = 2527 := by omega
  subst i
  exact disposition_at_2527

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
