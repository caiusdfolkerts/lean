module
prelude
public import RootedSubsumedForest0708DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_384 : dispositionTest 384 = true := by decide +kernel

theorem disposition_at_385 : dispositionTest 385 = true := by decide +kernel

theorem disposition_at_386 : dispositionTest 386 = true := by decide +kernel

theorem disposition_at_387 : dispositionTest 387 = true := by decide +kernel

theorem disposition_at_388 : dispositionTest 388 = true := by decide +kernel

theorem disposition_at_389 : dispositionTest 389 = true := by decide +kernel

theorem disposition_at_390 : dispositionTest 390 = true := by decide +kernel

theorem disposition_at_391 : dispositionTest 391 = true := by decide +kernel

theorem disposition_at_392 : dispositionTest 392 = true := by decide +kernel

theorem disposition_at_393 : dispositionTest 393 = true := by decide +kernel

theorem disposition_at_394 : dispositionTest 394 = true := by decide +kernel

theorem disposition_at_395 : dispositionTest 395 = true := by decide +kernel

theorem disposition_at_396 : dispositionTest 396 = true := by decide +kernel

theorem disposition_at_397 : dispositionTest 397 = true := by decide +kernel

theorem disposition_at_398 : dispositionTest 398 = true := by decide +kernel

theorem disposition_at_399 : dispositionTest 399 = true := by decide +kernel

theorem disposition_at_400 : dispositionTest 400 = true := by decide +kernel

theorem disposition_at_401 : dispositionTest 401 = true := by decide +kernel

theorem disposition_at_402 : dispositionTest 402 = true := by decide +kernel

theorem disposition_at_403 : dispositionTest 403 = true := by decide +kernel

theorem disposition_at_404 : dispositionTest 404 = true := by decide +kernel

theorem disposition_at_405 : dispositionTest 405 = true := by decide +kernel

theorem disposition_at_406 : dispositionTest 406 = true := by decide +kernel


theorem disposition_at_407 : dispositionTest 407 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 407).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M019.r1249.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M019.r1249) = true
  rw [Nonrational.OldTerminalMatches.M019.r1249_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_408 : dispositionTest 408 = true := by decide +kernel

theorem disposition_at_409 : dispositionTest 409 = true := by decide +kernel

theorem disposition_at_410 : dispositionTest 410 = true := by decide +kernel

theorem disposition_at_411 : dispositionTest 411 = true := by decide +kernel

theorem disposition_at_412 : dispositionTest 412 = true := by decide +kernel

theorem disposition_at_413 : dispositionTest 413 = true := by decide +kernel

theorem disposition_at_414 : dispositionTest 414 = true := by decide +kernel

theorem disposition_at_415 : dispositionTest 415 = true := by decide +kernel

theorem disposition_interval_384 : Interval dispositionTest 384 385 := by
  intro i hlo hhi
  have h : i = 384 := by omega
  subst i
  exact disposition_at_384


theorem disposition_interval_385 : Interval dispositionTest 385 386 := by
  intro i hlo hhi
  have h : i = 385 := by omega
  subst i
  exact disposition_at_385


theorem disposition_interval_386 : Interval dispositionTest 386 387 := by
  intro i hlo hhi
  have h : i = 386 := by omega
  subst i
  exact disposition_at_386


theorem disposition_interval_387 : Interval dispositionTest 387 388 := by
  intro i hlo hhi
  have h : i = 387 := by omega
  subst i
  exact disposition_at_387


theorem disposition_interval_388 : Interval dispositionTest 388 389 := by
  intro i hlo hhi
  have h : i = 388 := by omega
  subst i
  exact disposition_at_388


theorem disposition_interval_389 : Interval dispositionTest 389 390 := by
  intro i hlo hhi
  have h : i = 389 := by omega
  subst i
  exact disposition_at_389


theorem disposition_interval_390 : Interval dispositionTest 390 391 := by
  intro i hlo hhi
  have h : i = 390 := by omega
  subst i
  exact disposition_at_390


theorem disposition_interval_391 : Interval dispositionTest 391 392 := by
  intro i hlo hhi
  have h : i = 391 := by omega
  subst i
  exact disposition_at_391


theorem disposition_interval_392 : Interval dispositionTest 392 393 := by
  intro i hlo hhi
  have h : i = 392 := by omega
  subst i
  exact disposition_at_392


theorem disposition_interval_393 : Interval dispositionTest 393 394 := by
  intro i hlo hhi
  have h : i = 393 := by omega
  subst i
  exact disposition_at_393


theorem disposition_interval_394 : Interval dispositionTest 394 395 := by
  intro i hlo hhi
  have h : i = 394 := by omega
  subst i
  exact disposition_at_394


theorem disposition_interval_395 : Interval dispositionTest 395 396 := by
  intro i hlo hhi
  have h : i = 395 := by omega
  subst i
  exact disposition_at_395


theorem disposition_interval_396 : Interval dispositionTest 396 397 := by
  intro i hlo hhi
  have h : i = 396 := by omega
  subst i
  exact disposition_at_396


theorem disposition_interval_397 : Interval dispositionTest 397 398 := by
  intro i hlo hhi
  have h : i = 397 := by omega
  subst i
  exact disposition_at_397


theorem disposition_interval_398 : Interval dispositionTest 398 399 := by
  intro i hlo hhi
  have h : i = 398 := by omega
  subst i
  exact disposition_at_398


theorem disposition_interval_399 : Interval dispositionTest 399 400 := by
  intro i hlo hhi
  have h : i = 399 := by omega
  subst i
  exact disposition_at_399


theorem disposition_interval_400 : Interval dispositionTest 400 401 := by
  intro i hlo hhi
  have h : i = 400 := by omega
  subst i
  exact disposition_at_400


theorem disposition_interval_401 : Interval dispositionTest 401 402 := by
  intro i hlo hhi
  have h : i = 401 := by omega
  subst i
  exact disposition_at_401


theorem disposition_interval_402 : Interval dispositionTest 402 403 := by
  intro i hlo hhi
  have h : i = 402 := by omega
  subst i
  exact disposition_at_402


theorem disposition_interval_403 : Interval dispositionTest 403 404 := by
  intro i hlo hhi
  have h : i = 403 := by omega
  subst i
  exact disposition_at_403


theorem disposition_interval_404 : Interval dispositionTest 404 405 := by
  intro i hlo hhi
  have h : i = 404 := by omega
  subst i
  exact disposition_at_404


theorem disposition_interval_405 : Interval dispositionTest 405 406 := by
  intro i hlo hhi
  have h : i = 405 := by omega
  subst i
  exact disposition_at_405


theorem disposition_interval_406 : Interval dispositionTest 406 407 := by
  intro i hlo hhi
  have h : i = 406 := by omega
  subst i
  exact disposition_at_406


theorem disposition_interval_407 : Interval dispositionTest 407 408 := by
  intro i hlo hhi
  have h : i = 407 := by omega
  subst i
  exact disposition_at_407


theorem disposition_interval_408 : Interval dispositionTest 408 409 := by
  intro i hlo hhi
  have h : i = 408 := by omega
  subst i
  exact disposition_at_408


theorem disposition_interval_409 : Interval dispositionTest 409 410 := by
  intro i hlo hhi
  have h : i = 409 := by omega
  subst i
  exact disposition_at_409


theorem disposition_interval_410 : Interval dispositionTest 410 411 := by
  intro i hlo hhi
  have h : i = 410 := by omega
  subst i
  exact disposition_at_410


theorem disposition_interval_411 : Interval dispositionTest 411 412 := by
  intro i hlo hhi
  have h : i = 411 := by omega
  subst i
  exact disposition_at_411


theorem disposition_interval_412 : Interval dispositionTest 412 413 := by
  intro i hlo hhi
  have h : i = 412 := by omega
  subst i
  exact disposition_at_412


theorem disposition_interval_413 : Interval dispositionTest 413 414 := by
  intro i hlo hhi
  have h : i = 413 := by omega
  subst i
  exact disposition_at_413


theorem disposition_interval_414 : Interval dispositionTest 414 415 := by
  intro i hlo hhi
  have h : i = 414 := by omega
  subst i
  exact disposition_at_414


theorem disposition_interval_415 : Interval dispositionTest 415 416 := by
  intro i hlo hhi
  have h : i = 415 := by omega
  subst i
  exact disposition_at_415

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
