module
prelude
public import SmallSubsumedForest18DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_416 : dispositionTest 416 = true := by decide +kernel

theorem disposition_at_417 : dispositionTest 417 = true := by decide +kernel

theorem disposition_at_418 : dispositionTest 418 = true := by decide +kernel

theorem disposition_at_419 : dispositionTest 419 = true := by decide +kernel

theorem disposition_at_420 : dispositionTest 420 = true := by decide +kernel

theorem disposition_at_421 : dispositionTest 421 = true := by decide +kernel

theorem disposition_at_422 : dispositionTest 422 = true := by decide +kernel

theorem disposition_at_423 : dispositionTest 423 = true := by decide +kernel

theorem disposition_at_424 : dispositionTest 424 = true := by decide +kernel

theorem disposition_at_425 : dispositionTest 425 = true := by decide +kernel

theorem disposition_at_426 : dispositionTest 426 = true := by decide +kernel

theorem disposition_at_427 : dispositionTest 427 = true := by decide +kernel

theorem disposition_at_428 : dispositionTest 428 = true := by decide +kernel

theorem disposition_at_429 : dispositionTest 429 = true := by decide +kernel

theorem disposition_at_430 : dispositionTest 430 = true := by decide +kernel

theorem disposition_at_431 : dispositionTest 431 = true := by decide +kernel

theorem disposition_interval_416 : Interval dispositionTest 416 417 := by
  intro i hlo hhi
  have h : i = 416 := by omega
  subst i
  exact disposition_at_416


theorem disposition_interval_417 : Interval dispositionTest 417 418 := by
  intro i hlo hhi
  have h : i = 417 := by omega
  subst i
  exact disposition_at_417


theorem disposition_interval_418 : Interval dispositionTest 418 419 := by
  intro i hlo hhi
  have h : i = 418 := by omega
  subst i
  exact disposition_at_418


theorem disposition_interval_419 : Interval dispositionTest 419 420 := by
  intro i hlo hhi
  have h : i = 419 := by omega
  subst i
  exact disposition_at_419


theorem disposition_interval_420 : Interval dispositionTest 420 421 := by
  intro i hlo hhi
  have h : i = 420 := by omega
  subst i
  exact disposition_at_420


theorem disposition_interval_421 : Interval dispositionTest 421 422 := by
  intro i hlo hhi
  have h : i = 421 := by omega
  subst i
  exact disposition_at_421


theorem disposition_interval_422 : Interval dispositionTest 422 423 := by
  intro i hlo hhi
  have h : i = 422 := by omega
  subst i
  exact disposition_at_422


theorem disposition_interval_423 : Interval dispositionTest 423 424 := by
  intro i hlo hhi
  have h : i = 423 := by omega
  subst i
  exact disposition_at_423


theorem disposition_interval_424 : Interval dispositionTest 424 425 := by
  intro i hlo hhi
  have h : i = 424 := by omega
  subst i
  exact disposition_at_424


theorem disposition_interval_425 : Interval dispositionTest 425 426 := by
  intro i hlo hhi
  have h : i = 425 := by omega
  subst i
  exact disposition_at_425


theorem disposition_interval_426 : Interval dispositionTest 426 427 := by
  intro i hlo hhi
  have h : i = 426 := by omega
  subst i
  exact disposition_at_426


theorem disposition_interval_427 : Interval dispositionTest 427 428 := by
  intro i hlo hhi
  have h : i = 427 := by omega
  subst i
  exact disposition_at_427


theorem disposition_interval_428 : Interval dispositionTest 428 429 := by
  intro i hlo hhi
  have h : i = 428 := by omega
  subst i
  exact disposition_at_428


theorem disposition_interval_429 : Interval dispositionTest 429 430 := by
  intro i hlo hhi
  have h : i = 429 := by omega
  subst i
  exact disposition_at_429


theorem disposition_interval_430 : Interval dispositionTest 430 431 := by
  intro i hlo hhi
  have h : i = 430 := by omega
  subst i
  exact disposition_at_430


theorem disposition_interval_431 : Interval dispositionTest 431 432 := by
  intro i hlo hhi
  have h : i = 431 := by omega
  subst i
  exact disposition_at_431

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
