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
theorem disposition_at_3360 : dispositionTest 3360 = true := by decide +kernel

theorem disposition_at_3361 : dispositionTest 3361 = true := by decide +kernel

theorem disposition_at_3362 : dispositionTest 3362 = true := by decide +kernel

theorem disposition_at_3363 : dispositionTest 3363 = true := by decide +kernel

theorem disposition_at_3364 : dispositionTest 3364 = true := by decide +kernel

theorem disposition_at_3365 : dispositionTest 3365 = true := by decide +kernel


theorem disposition_at_3366 : dispositionTest 3366 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3366).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1055.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1055) = true
  rw [Nonrational.OldTerminalMatches.M016.r1055_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3367 : dispositionTest 3367 = true := by decide +kernel

theorem disposition_at_3368 : dispositionTest 3368 = true := by decide +kernel

theorem disposition_at_3369 : dispositionTest 3369 = true := by decide +kernel


theorem disposition_at_3370 : dispositionTest 3370 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 3370).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1056.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1056) = true
  rw [Nonrational.OldTerminalMatches.M016.r1056_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_3371 : dispositionTest 3371 = true := by decide +kernel

theorem disposition_at_3372 : dispositionTest 3372 = true := by decide +kernel

theorem disposition_at_3373 : dispositionTest 3373 = true := by decide +kernel

theorem disposition_at_3374 : dispositionTest 3374 = true := by decide +kernel

theorem disposition_at_3375 : dispositionTest 3375 = true := by decide +kernel

theorem disposition_at_3376 : dispositionTest 3376 = true := by decide +kernel

theorem disposition_at_3377 : dispositionTest 3377 = true := by decide +kernel

theorem disposition_at_3378 : dispositionTest 3378 = true := by decide +kernel

theorem disposition_at_3379 : dispositionTest 3379 = true := by decide +kernel

theorem disposition_at_3380 : dispositionTest 3380 = true := by decide +kernel

theorem disposition_at_3381 : dispositionTest 3381 = true := by decide +kernel

theorem disposition_at_3382 : dispositionTest 3382 = true := by decide +kernel

theorem disposition_at_3383 : dispositionTest 3383 = true := by decide +kernel

theorem disposition_at_3384 : dispositionTest 3384 = true := by decide +kernel

theorem disposition_at_3385 : dispositionTest 3385 = true := by decide +kernel

theorem disposition_at_3386 : dispositionTest 3386 = true := by decide +kernel

theorem disposition_at_3387 : dispositionTest 3387 = true := by decide +kernel

theorem disposition_at_3388 : dispositionTest 3388 = true := by decide +kernel

theorem disposition_at_3389 : dispositionTest 3389 = true := by decide +kernel

theorem disposition_at_3390 : dispositionTest 3390 = true := by decide +kernel

theorem disposition_at_3391 : dispositionTest 3391 = true := by decide +kernel

theorem disposition_interval_3360 : Interval dispositionTest 3360 3361 := by
  intro i hlo hhi
  have h : i = 3360 := by omega
  subst i
  exact disposition_at_3360


theorem disposition_interval_3361 : Interval dispositionTest 3361 3362 := by
  intro i hlo hhi
  have h : i = 3361 := by omega
  subst i
  exact disposition_at_3361


theorem disposition_interval_3362 : Interval dispositionTest 3362 3363 := by
  intro i hlo hhi
  have h : i = 3362 := by omega
  subst i
  exact disposition_at_3362


theorem disposition_interval_3363 : Interval dispositionTest 3363 3364 := by
  intro i hlo hhi
  have h : i = 3363 := by omega
  subst i
  exact disposition_at_3363


theorem disposition_interval_3364 : Interval dispositionTest 3364 3365 := by
  intro i hlo hhi
  have h : i = 3364 := by omega
  subst i
  exact disposition_at_3364


theorem disposition_interval_3365 : Interval dispositionTest 3365 3366 := by
  intro i hlo hhi
  have h : i = 3365 := by omega
  subst i
  exact disposition_at_3365


theorem disposition_interval_3366 : Interval dispositionTest 3366 3367 := by
  intro i hlo hhi
  have h : i = 3366 := by omega
  subst i
  exact disposition_at_3366


theorem disposition_interval_3367 : Interval dispositionTest 3367 3368 := by
  intro i hlo hhi
  have h : i = 3367 := by omega
  subst i
  exact disposition_at_3367


theorem disposition_interval_3368 : Interval dispositionTest 3368 3369 := by
  intro i hlo hhi
  have h : i = 3368 := by omega
  subst i
  exact disposition_at_3368


theorem disposition_interval_3369 : Interval dispositionTest 3369 3370 := by
  intro i hlo hhi
  have h : i = 3369 := by omega
  subst i
  exact disposition_at_3369


theorem disposition_interval_3370 : Interval dispositionTest 3370 3371 := by
  intro i hlo hhi
  have h : i = 3370 := by omega
  subst i
  exact disposition_at_3370


theorem disposition_interval_3371 : Interval dispositionTest 3371 3372 := by
  intro i hlo hhi
  have h : i = 3371 := by omega
  subst i
  exact disposition_at_3371


theorem disposition_interval_3372 : Interval dispositionTest 3372 3373 := by
  intro i hlo hhi
  have h : i = 3372 := by omega
  subst i
  exact disposition_at_3372


theorem disposition_interval_3373 : Interval dispositionTest 3373 3374 := by
  intro i hlo hhi
  have h : i = 3373 := by omega
  subst i
  exact disposition_at_3373


theorem disposition_interval_3374 : Interval dispositionTest 3374 3375 := by
  intro i hlo hhi
  have h : i = 3374 := by omega
  subst i
  exact disposition_at_3374


theorem disposition_interval_3375 : Interval dispositionTest 3375 3376 := by
  intro i hlo hhi
  have h : i = 3375 := by omega
  subst i
  exact disposition_at_3375


theorem disposition_interval_3376 : Interval dispositionTest 3376 3377 := by
  intro i hlo hhi
  have h : i = 3376 := by omega
  subst i
  exact disposition_at_3376


theorem disposition_interval_3377 : Interval dispositionTest 3377 3378 := by
  intro i hlo hhi
  have h : i = 3377 := by omega
  subst i
  exact disposition_at_3377


theorem disposition_interval_3378 : Interval dispositionTest 3378 3379 := by
  intro i hlo hhi
  have h : i = 3378 := by omega
  subst i
  exact disposition_at_3378


theorem disposition_interval_3379 : Interval dispositionTest 3379 3380 := by
  intro i hlo hhi
  have h : i = 3379 := by omega
  subst i
  exact disposition_at_3379


theorem disposition_interval_3380 : Interval dispositionTest 3380 3381 := by
  intro i hlo hhi
  have h : i = 3380 := by omega
  subst i
  exact disposition_at_3380


theorem disposition_interval_3381 : Interval dispositionTest 3381 3382 := by
  intro i hlo hhi
  have h : i = 3381 := by omega
  subst i
  exact disposition_at_3381


theorem disposition_interval_3382 : Interval dispositionTest 3382 3383 := by
  intro i hlo hhi
  have h : i = 3382 := by omega
  subst i
  exact disposition_at_3382


theorem disposition_interval_3383 : Interval dispositionTest 3383 3384 := by
  intro i hlo hhi
  have h : i = 3383 := by omega
  subst i
  exact disposition_at_3383


theorem disposition_interval_3384 : Interval dispositionTest 3384 3385 := by
  intro i hlo hhi
  have h : i = 3384 := by omega
  subst i
  exact disposition_at_3384


theorem disposition_interval_3385 : Interval dispositionTest 3385 3386 := by
  intro i hlo hhi
  have h : i = 3385 := by omega
  subst i
  exact disposition_at_3385


theorem disposition_interval_3386 : Interval dispositionTest 3386 3387 := by
  intro i hlo hhi
  have h : i = 3386 := by omega
  subst i
  exact disposition_at_3386


theorem disposition_interval_3387 : Interval dispositionTest 3387 3388 := by
  intro i hlo hhi
  have h : i = 3387 := by omega
  subst i
  exact disposition_at_3387


theorem disposition_interval_3388 : Interval dispositionTest 3388 3389 := by
  intro i hlo hhi
  have h : i = 3388 := by omega
  subst i
  exact disposition_at_3388


theorem disposition_interval_3389 : Interval dispositionTest 3389 3390 := by
  intro i hlo hhi
  have h : i = 3389 := by omega
  subst i
  exact disposition_at_3389


theorem disposition_interval_3390 : Interval dispositionTest 3390 3391 := by
  intro i hlo hhi
  have h : i = 3390 := by omega
  subst i
  exact disposition_at_3390


theorem disposition_interval_3391 : Interval dispositionTest 3391 3392 := by
  intro i hlo hhi
  have h : i = 3391 := by omega
  subst i
  exact disposition_at_3391

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
