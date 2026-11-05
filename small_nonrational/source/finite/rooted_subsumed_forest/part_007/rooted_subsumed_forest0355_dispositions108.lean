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
theorem disposition_at_3456 : dispositionTest 3456 = true := by decide +kernel


theorem disposition_at_3457 : dispositionTest 3457 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3457).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1081.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1081) = true
  rw [Nonrational.OldTerminalMatches.M016.r1081_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3458 : dispositionTest 3458 = true := by decide +kernel

theorem disposition_at_3459 : dispositionTest 3459 = true := by decide +kernel

theorem disposition_at_3460 : dispositionTest 3460 = true := by decide +kernel

theorem disposition_at_3461 : dispositionTest 3461 = true := by decide +kernel

theorem disposition_at_3462 : dispositionTest 3462 = true := by decide +kernel

theorem disposition_at_3463 : dispositionTest 3463 = true := by decide +kernel

theorem disposition_at_3464 : dispositionTest 3464 = true := by decide +kernel

theorem disposition_at_3465 : dispositionTest 3465 = true := by decide +kernel

theorem disposition_at_3466 : dispositionTest 3466 = true := by decide +kernel

theorem disposition_at_3467 : dispositionTest 3467 = true := by decide +kernel

theorem disposition_at_3468 : dispositionTest 3468 = true := by decide +kernel

theorem disposition_at_3469 : dispositionTest 3469 = true := by decide +kernel

theorem disposition_at_3470 : dispositionTest 3470 = true := by decide +kernel

theorem disposition_at_3471 : dispositionTest 3471 = true := by decide +kernel

theorem disposition_at_3472 : dispositionTest 3472 = true := by decide +kernel

theorem disposition_at_3473 : dispositionTest 3473 = true := by decide +kernel

theorem disposition_at_3474 : dispositionTest 3474 = true := by decide +kernel

theorem disposition_at_3475 : dispositionTest 3475 = true := by decide +kernel

theorem disposition_at_3476 : dispositionTest 3476 = true := by decide +kernel

theorem disposition_at_3477 : dispositionTest 3477 = true := by decide +kernel

theorem disposition_at_3478 : dispositionTest 3478 = true := by decide +kernel

theorem disposition_at_3479 : dispositionTest 3479 = true := by decide +kernel

theorem disposition_at_3480 : dispositionTest 3480 = true := by decide +kernel

theorem disposition_at_3481 : dispositionTest 3481 = true := by decide +kernel

theorem disposition_at_3482 : dispositionTest 3482 = true := by decide +kernel

theorem disposition_at_3483 : dispositionTest 3483 = true := by decide +kernel

theorem disposition_at_3484 : dispositionTest 3484 = true := by decide +kernel

theorem disposition_at_3485 : dispositionTest 3485 = true := by decide +kernel

theorem disposition_at_3486 : dispositionTest 3486 = true := by decide +kernel

theorem disposition_at_3487 : dispositionTest 3487 = true := by decide +kernel

theorem disposition_interval_3456 : Interval dispositionTest 3456 3457 := by
  intro i hlo hhi
  have h : i = 3456 := by omega
  subst i
  exact disposition_at_3456


theorem disposition_interval_3457 : Interval dispositionTest 3457 3458 := by
  intro i hlo hhi
  have h : i = 3457 := by omega
  subst i
  exact disposition_at_3457


theorem disposition_interval_3458 : Interval dispositionTest 3458 3459 := by
  intro i hlo hhi
  have h : i = 3458 := by omega
  subst i
  exact disposition_at_3458


theorem disposition_interval_3459 : Interval dispositionTest 3459 3460 := by
  intro i hlo hhi
  have h : i = 3459 := by omega
  subst i
  exact disposition_at_3459


theorem disposition_interval_3460 : Interval dispositionTest 3460 3461 := by
  intro i hlo hhi
  have h : i = 3460 := by omega
  subst i
  exact disposition_at_3460


theorem disposition_interval_3461 : Interval dispositionTest 3461 3462 := by
  intro i hlo hhi
  have h : i = 3461 := by omega
  subst i
  exact disposition_at_3461


theorem disposition_interval_3462 : Interval dispositionTest 3462 3463 := by
  intro i hlo hhi
  have h : i = 3462 := by omega
  subst i
  exact disposition_at_3462


theorem disposition_interval_3463 : Interval dispositionTest 3463 3464 := by
  intro i hlo hhi
  have h : i = 3463 := by omega
  subst i
  exact disposition_at_3463


theorem disposition_interval_3464 : Interval dispositionTest 3464 3465 := by
  intro i hlo hhi
  have h : i = 3464 := by omega
  subst i
  exact disposition_at_3464


theorem disposition_interval_3465 : Interval dispositionTest 3465 3466 := by
  intro i hlo hhi
  have h : i = 3465 := by omega
  subst i
  exact disposition_at_3465


theorem disposition_interval_3466 : Interval dispositionTest 3466 3467 := by
  intro i hlo hhi
  have h : i = 3466 := by omega
  subst i
  exact disposition_at_3466


theorem disposition_interval_3467 : Interval dispositionTest 3467 3468 := by
  intro i hlo hhi
  have h : i = 3467 := by omega
  subst i
  exact disposition_at_3467


theorem disposition_interval_3468 : Interval dispositionTest 3468 3469 := by
  intro i hlo hhi
  have h : i = 3468 := by omega
  subst i
  exact disposition_at_3468


theorem disposition_interval_3469 : Interval dispositionTest 3469 3470 := by
  intro i hlo hhi
  have h : i = 3469 := by omega
  subst i
  exact disposition_at_3469


theorem disposition_interval_3470 : Interval dispositionTest 3470 3471 := by
  intro i hlo hhi
  have h : i = 3470 := by omega
  subst i
  exact disposition_at_3470


theorem disposition_interval_3471 : Interval dispositionTest 3471 3472 := by
  intro i hlo hhi
  have h : i = 3471 := by omega
  subst i
  exact disposition_at_3471


theorem disposition_interval_3472 : Interval dispositionTest 3472 3473 := by
  intro i hlo hhi
  have h : i = 3472 := by omega
  subst i
  exact disposition_at_3472


theorem disposition_interval_3473 : Interval dispositionTest 3473 3474 := by
  intro i hlo hhi
  have h : i = 3473 := by omega
  subst i
  exact disposition_at_3473


theorem disposition_interval_3474 : Interval dispositionTest 3474 3475 := by
  intro i hlo hhi
  have h : i = 3474 := by omega
  subst i
  exact disposition_at_3474


theorem disposition_interval_3475 : Interval dispositionTest 3475 3476 := by
  intro i hlo hhi
  have h : i = 3475 := by omega
  subst i
  exact disposition_at_3475


theorem disposition_interval_3476 : Interval dispositionTest 3476 3477 := by
  intro i hlo hhi
  have h : i = 3476 := by omega
  subst i
  exact disposition_at_3476


theorem disposition_interval_3477 : Interval dispositionTest 3477 3478 := by
  intro i hlo hhi
  have h : i = 3477 := by omega
  subst i
  exact disposition_at_3477


theorem disposition_interval_3478 : Interval dispositionTest 3478 3479 := by
  intro i hlo hhi
  have h : i = 3478 := by omega
  subst i
  exact disposition_at_3478


theorem disposition_interval_3479 : Interval dispositionTest 3479 3480 := by
  intro i hlo hhi
  have h : i = 3479 := by omega
  subst i
  exact disposition_at_3479


theorem disposition_interval_3480 : Interval dispositionTest 3480 3481 := by
  intro i hlo hhi
  have h : i = 3480 := by omega
  subst i
  exact disposition_at_3480


theorem disposition_interval_3481 : Interval dispositionTest 3481 3482 := by
  intro i hlo hhi
  have h : i = 3481 := by omega
  subst i
  exact disposition_at_3481


theorem disposition_interval_3482 : Interval dispositionTest 3482 3483 := by
  intro i hlo hhi
  have h : i = 3482 := by omega
  subst i
  exact disposition_at_3482


theorem disposition_interval_3483 : Interval dispositionTest 3483 3484 := by
  intro i hlo hhi
  have h : i = 3483 := by omega
  subst i
  exact disposition_at_3483


theorem disposition_interval_3484 : Interval dispositionTest 3484 3485 := by
  intro i hlo hhi
  have h : i = 3484 := by omega
  subst i
  exact disposition_at_3484


theorem disposition_interval_3485 : Interval dispositionTest 3485 3486 := by
  intro i hlo hhi
  have h : i = 3485 := by omega
  subst i
  exact disposition_at_3485


theorem disposition_interval_3486 : Interval dispositionTest 3486 3487 := by
  intro i hlo hhi
  have h : i = 3486 := by omega
  subst i
  exact disposition_at_3486


theorem disposition_interval_3487 : Interval dispositionTest 3487 3488 := by
  intro i hlo hhi
  have h : i = 3487 := by omega
  subst i
  exact disposition_at_3487

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
