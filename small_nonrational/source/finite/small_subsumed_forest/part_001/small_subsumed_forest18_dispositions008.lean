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
theorem disposition_at_256 : dispositionTest 256 = true := by decide +kernel

theorem disposition_at_257 : dispositionTest 257 = true := by decide +kernel

theorem disposition_at_258 : dispositionTest 258 = true := by decide +kernel

theorem disposition_at_259 : dispositionTest 259 = true := by decide +kernel

theorem disposition_at_260 : dispositionTest 260 = true := by decide +kernel

theorem disposition_at_261 : dispositionTest 261 = true := by decide +kernel

theorem disposition_at_262 : dispositionTest 262 = true := by decide +kernel

theorem disposition_at_263 : dispositionTest 263 = true := by decide +kernel

theorem disposition_at_264 : dispositionTest 264 = true := by decide +kernel

theorem disposition_at_265 : dispositionTest 265 = true := by decide +kernel

theorem disposition_at_266 : dispositionTest 266 = true := by decide +kernel

theorem disposition_at_267 : dispositionTest 267 = true := by decide +kernel

theorem disposition_at_268 : dispositionTest 268 = true := by decide +kernel

theorem disposition_at_269 : dispositionTest 269 = true := by decide +kernel

theorem disposition_at_270 : dispositionTest 270 = true := by decide +kernel

theorem disposition_at_271 : dispositionTest 271 = true := by decide +kernel


theorem disposition_at_272 : dispositionTest 272 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 272).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M004.r0270.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M004.r0270) = true
  rw [Nonrational.OldTerminalMatches.M004.r0270_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_273 : dispositionTest 273 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 273).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M004.r0271.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M004.r0271) = true
  rw [Nonrational.OldTerminalMatches.M004.r0271_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_274 : dispositionTest 274 = true := by decide +kernel

theorem disposition_at_275 : dispositionTest 275 = true := by decide +kernel

theorem disposition_at_276 : dispositionTest 276 = true := by decide +kernel

theorem disposition_at_277 : dispositionTest 277 = true := by decide +kernel

theorem disposition_at_278 : dispositionTest 278 = true := by decide +kernel

theorem disposition_at_279 : dispositionTest 279 = true := by decide +kernel

theorem disposition_at_280 : dispositionTest 280 = true := by decide +kernel

theorem disposition_at_281 : dispositionTest 281 = true := by decide +kernel

theorem disposition_at_282 : dispositionTest 282 = true := by decide +kernel

theorem disposition_at_283 : dispositionTest 283 = true := by decide +kernel

theorem disposition_at_284 : dispositionTest 284 = true := by decide +kernel

theorem disposition_at_285 : dispositionTest 285 = true := by decide +kernel

theorem disposition_at_286 : dispositionTest 286 = true := by decide +kernel

theorem disposition_at_287 : dispositionTest 287 = true := by decide +kernel

theorem disposition_interval_256 : Interval dispositionTest 256 257 := by
  intro i hlo hhi
  have h : i = 256 := by omega
  subst i
  exact disposition_at_256


theorem disposition_interval_257 : Interval dispositionTest 257 258 := by
  intro i hlo hhi
  have h : i = 257 := by omega
  subst i
  exact disposition_at_257


theorem disposition_interval_258 : Interval dispositionTest 258 259 := by
  intro i hlo hhi
  have h : i = 258 := by omega
  subst i
  exact disposition_at_258


theorem disposition_interval_259 : Interval dispositionTest 259 260 := by
  intro i hlo hhi
  have h : i = 259 := by omega
  subst i
  exact disposition_at_259


theorem disposition_interval_260 : Interval dispositionTest 260 261 := by
  intro i hlo hhi
  have h : i = 260 := by omega
  subst i
  exact disposition_at_260


theorem disposition_interval_261 : Interval dispositionTest 261 262 := by
  intro i hlo hhi
  have h : i = 261 := by omega
  subst i
  exact disposition_at_261


theorem disposition_interval_262 : Interval dispositionTest 262 263 := by
  intro i hlo hhi
  have h : i = 262 := by omega
  subst i
  exact disposition_at_262


theorem disposition_interval_263 : Interval dispositionTest 263 264 := by
  intro i hlo hhi
  have h : i = 263 := by omega
  subst i
  exact disposition_at_263


theorem disposition_interval_264 : Interval dispositionTest 264 265 := by
  intro i hlo hhi
  have h : i = 264 := by omega
  subst i
  exact disposition_at_264


theorem disposition_interval_265 : Interval dispositionTest 265 266 := by
  intro i hlo hhi
  have h : i = 265 := by omega
  subst i
  exact disposition_at_265


theorem disposition_interval_266 : Interval dispositionTest 266 267 := by
  intro i hlo hhi
  have h : i = 266 := by omega
  subst i
  exact disposition_at_266


theorem disposition_interval_267 : Interval dispositionTest 267 268 := by
  intro i hlo hhi
  have h : i = 267 := by omega
  subst i
  exact disposition_at_267


theorem disposition_interval_268 : Interval dispositionTest 268 269 := by
  intro i hlo hhi
  have h : i = 268 := by omega
  subst i
  exact disposition_at_268


theorem disposition_interval_269 : Interval dispositionTest 269 270 := by
  intro i hlo hhi
  have h : i = 269 := by omega
  subst i
  exact disposition_at_269


theorem disposition_interval_270 : Interval dispositionTest 270 271 := by
  intro i hlo hhi
  have h : i = 270 := by omega
  subst i
  exact disposition_at_270


theorem disposition_interval_271 : Interval dispositionTest 271 272 := by
  intro i hlo hhi
  have h : i = 271 := by omega
  subst i
  exact disposition_at_271


theorem disposition_interval_272 : Interval dispositionTest 272 273 := by
  intro i hlo hhi
  have h : i = 272 := by omega
  subst i
  exact disposition_at_272


theorem disposition_interval_273 : Interval dispositionTest 273 274 := by
  intro i hlo hhi
  have h : i = 273 := by omega
  subst i
  exact disposition_at_273


theorem disposition_interval_274 : Interval dispositionTest 274 275 := by
  intro i hlo hhi
  have h : i = 274 := by omega
  subst i
  exact disposition_at_274


theorem disposition_interval_275 : Interval dispositionTest 275 276 := by
  intro i hlo hhi
  have h : i = 275 := by omega
  subst i
  exact disposition_at_275


theorem disposition_interval_276 : Interval dispositionTest 276 277 := by
  intro i hlo hhi
  have h : i = 276 := by omega
  subst i
  exact disposition_at_276


theorem disposition_interval_277 : Interval dispositionTest 277 278 := by
  intro i hlo hhi
  have h : i = 277 := by omega
  subst i
  exact disposition_at_277


theorem disposition_interval_278 : Interval dispositionTest 278 279 := by
  intro i hlo hhi
  have h : i = 278 := by omega
  subst i
  exact disposition_at_278


theorem disposition_interval_279 : Interval dispositionTest 279 280 := by
  intro i hlo hhi
  have h : i = 279 := by omega
  subst i
  exact disposition_at_279


theorem disposition_interval_280 : Interval dispositionTest 280 281 := by
  intro i hlo hhi
  have h : i = 280 := by omega
  subst i
  exact disposition_at_280


theorem disposition_interval_281 : Interval dispositionTest 281 282 := by
  intro i hlo hhi
  have h : i = 281 := by omega
  subst i
  exact disposition_at_281


theorem disposition_interval_282 : Interval dispositionTest 282 283 := by
  intro i hlo hhi
  have h : i = 282 := by omega
  subst i
  exact disposition_at_282


theorem disposition_interval_283 : Interval dispositionTest 283 284 := by
  intro i hlo hhi
  have h : i = 283 := by omega
  subst i
  exact disposition_at_283


theorem disposition_interval_284 : Interval dispositionTest 284 285 := by
  intro i hlo hhi
  have h : i = 284 := by omega
  subst i
  exact disposition_at_284


theorem disposition_interval_285 : Interval dispositionTest 285 286 := by
  intro i hlo hhi
  have h : i = 285 := by omega
  subst i
  exact disposition_at_285


theorem disposition_interval_286 : Interval dispositionTest 286 287 := by
  intro i hlo hhi
  have h : i = 286 := by omega
  subst i
  exact disposition_at_286


theorem disposition_interval_287 : Interval dispositionTest 287 288 := by
  intro i hlo hhi
  have h : i = 287 := by omega
  subst i
  exact disposition_at_287

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
