module
prelude
public import RootedSubsumedForest0870DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_480 : dispositionTest 480 = true := by decide +kernel

theorem disposition_at_481 : dispositionTest 481 = true := by decide +kernel

theorem disposition_at_482 : dispositionTest 482 = true := by decide +kernel

theorem disposition_at_483 : dispositionTest 483 = true := by decide +kernel

theorem disposition_at_484 : dispositionTest 484 = true := by decide +kernel

theorem disposition_at_485 : dispositionTest 485 = true := by decide +kernel

theorem disposition_at_486 : dispositionTest 486 = true := by decide +kernel

theorem disposition_at_487 : dispositionTest 487 = true := by decide +kernel

theorem disposition_at_488 : dispositionTest 488 = true := by decide +kernel

theorem disposition_at_489 : dispositionTest 489 = true := by decide +kernel

theorem disposition_at_490 : dispositionTest 490 = true := by decide +kernel

theorem disposition_at_491 : dispositionTest 491 = true := by decide +kernel

theorem disposition_at_492 : dispositionTest 492 = true := by decide +kernel

theorem disposition_at_493 : dispositionTest 493 = true := by decide +kernel

theorem disposition_at_494 : dispositionTest 494 = true := by decide +kernel

theorem disposition_at_495 : dispositionTest 495 = true := by decide +kernel

theorem disposition_at_496 : dispositionTest 496 = true := by decide +kernel

theorem disposition_at_497 : dispositionTest 497 = true := by decide +kernel

theorem disposition_at_498 : dispositionTest 498 = true := by decide +kernel

theorem disposition_at_499 : dispositionTest 499 = true := by decide +kernel

theorem disposition_at_500 : dispositionTest 500 = true := by decide +kernel

theorem disposition_at_501 : dispositionTest 501 = true := by decide +kernel


theorem disposition_at_502 : dispositionTest 502 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 502).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) Nonrational.OldTerminalMatches.M026.r1669.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M026.r1669) = true
  rw [Nonrational.OldTerminalMatches.M026.r1669_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_503 : dispositionTest 503 = true := by decide +kernel

theorem disposition_at_504 : dispositionTest 504 = true := by decide +kernel

theorem disposition_at_505 : dispositionTest 505 = true := by decide +kernel

theorem disposition_at_506 : dispositionTest 506 = true := by decide +kernel

theorem disposition_at_507 : dispositionTest 507 = true := by decide +kernel

theorem disposition_at_508 : dispositionTest 508 = true := by decide +kernel

theorem disposition_at_509 : dispositionTest 509 = true := by decide +kernel

theorem disposition_at_510 : dispositionTest 510 = true := by decide +kernel

theorem disposition_at_511 : dispositionTest 511 = true := by decide +kernel

theorem disposition_interval_480 : Interval dispositionTest 480 481 := by
  intro i hlo hhi
  have h : i = 480 := by omega
  subst i
  exact disposition_at_480


theorem disposition_interval_481 : Interval dispositionTest 481 482 := by
  intro i hlo hhi
  have h : i = 481 := by omega
  subst i
  exact disposition_at_481


theorem disposition_interval_482 : Interval dispositionTest 482 483 := by
  intro i hlo hhi
  have h : i = 482 := by omega
  subst i
  exact disposition_at_482


theorem disposition_interval_483 : Interval dispositionTest 483 484 := by
  intro i hlo hhi
  have h : i = 483 := by omega
  subst i
  exact disposition_at_483


theorem disposition_interval_484 : Interval dispositionTest 484 485 := by
  intro i hlo hhi
  have h : i = 484 := by omega
  subst i
  exact disposition_at_484


theorem disposition_interval_485 : Interval dispositionTest 485 486 := by
  intro i hlo hhi
  have h : i = 485 := by omega
  subst i
  exact disposition_at_485


theorem disposition_interval_486 : Interval dispositionTest 486 487 := by
  intro i hlo hhi
  have h : i = 486 := by omega
  subst i
  exact disposition_at_486


theorem disposition_interval_487 : Interval dispositionTest 487 488 := by
  intro i hlo hhi
  have h : i = 487 := by omega
  subst i
  exact disposition_at_487


theorem disposition_interval_488 : Interval dispositionTest 488 489 := by
  intro i hlo hhi
  have h : i = 488 := by omega
  subst i
  exact disposition_at_488


theorem disposition_interval_489 : Interval dispositionTest 489 490 := by
  intro i hlo hhi
  have h : i = 489 := by omega
  subst i
  exact disposition_at_489


theorem disposition_interval_490 : Interval dispositionTest 490 491 := by
  intro i hlo hhi
  have h : i = 490 := by omega
  subst i
  exact disposition_at_490


theorem disposition_interval_491 : Interval dispositionTest 491 492 := by
  intro i hlo hhi
  have h : i = 491 := by omega
  subst i
  exact disposition_at_491


theorem disposition_interval_492 : Interval dispositionTest 492 493 := by
  intro i hlo hhi
  have h : i = 492 := by omega
  subst i
  exact disposition_at_492


theorem disposition_interval_493 : Interval dispositionTest 493 494 := by
  intro i hlo hhi
  have h : i = 493 := by omega
  subst i
  exact disposition_at_493


theorem disposition_interval_494 : Interval dispositionTest 494 495 := by
  intro i hlo hhi
  have h : i = 494 := by omega
  subst i
  exact disposition_at_494


theorem disposition_interval_495 : Interval dispositionTest 495 496 := by
  intro i hlo hhi
  have h : i = 495 := by omega
  subst i
  exact disposition_at_495


theorem disposition_interval_496 : Interval dispositionTest 496 497 := by
  intro i hlo hhi
  have h : i = 496 := by omega
  subst i
  exact disposition_at_496


theorem disposition_interval_497 : Interval dispositionTest 497 498 := by
  intro i hlo hhi
  have h : i = 497 := by omega
  subst i
  exact disposition_at_497


theorem disposition_interval_498 : Interval dispositionTest 498 499 := by
  intro i hlo hhi
  have h : i = 498 := by omega
  subst i
  exact disposition_at_498


theorem disposition_interval_499 : Interval dispositionTest 499 500 := by
  intro i hlo hhi
  have h : i = 499 := by omega
  subst i
  exact disposition_at_499


theorem disposition_interval_500 : Interval dispositionTest 500 501 := by
  intro i hlo hhi
  have h : i = 500 := by omega
  subst i
  exact disposition_at_500


theorem disposition_interval_501 : Interval dispositionTest 501 502 := by
  intro i hlo hhi
  have h : i = 501 := by omega
  subst i
  exact disposition_at_501


theorem disposition_interval_502 : Interval dispositionTest 502 503 := by
  intro i hlo hhi
  have h : i = 502 := by omega
  subst i
  exact disposition_at_502


theorem disposition_interval_503 : Interval dispositionTest 503 504 := by
  intro i hlo hhi
  have h : i = 503 := by omega
  subst i
  exact disposition_at_503


theorem disposition_interval_504 : Interval dispositionTest 504 505 := by
  intro i hlo hhi
  have h : i = 504 := by omega
  subst i
  exact disposition_at_504


theorem disposition_interval_505 : Interval dispositionTest 505 506 := by
  intro i hlo hhi
  have h : i = 505 := by omega
  subst i
  exact disposition_at_505


theorem disposition_interval_506 : Interval dispositionTest 506 507 := by
  intro i hlo hhi
  have h : i = 506 := by omega
  subst i
  exact disposition_at_506


theorem disposition_interval_507 : Interval dispositionTest 507 508 := by
  intro i hlo hhi
  have h : i = 507 := by omega
  subst i
  exact disposition_at_507


theorem disposition_interval_508 : Interval dispositionTest 508 509 := by
  intro i hlo hhi
  have h : i = 508 := by omega
  subst i
  exact disposition_at_508


theorem disposition_interval_509 : Interval dispositionTest 509 510 := by
  intro i hlo hhi
  have h : i = 509 := by omega
  subst i
  exact disposition_at_509


theorem disposition_interval_510 : Interval dispositionTest 510 511 := by
  intro i hlo hhi
  have h : i = 510 := by omega
  subst i
  exact disposition_at_510


theorem disposition_interval_511 : Interval dispositionTest 511 512 := by
  intro i hlo hhi
  have h : i = 511 := by omega
  subst i
  exact disposition_at_511

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
