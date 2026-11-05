module
prelude
public import RootedSubsumedForest0722DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_224 : dispositionTest 224 = true := by decide +kernel

theorem disposition_at_225 : dispositionTest 225 = true := by decide +kernel

theorem disposition_at_226 : dispositionTest 226 = true := by decide +kernel

theorem disposition_at_227 : dispositionTest 227 = true := by decide +kernel

theorem disposition_at_228 : dispositionTest 228 = true := by decide +kernel

theorem disposition_at_229 : dispositionTest 229 = true := by decide +kernel

theorem disposition_at_230 : dispositionTest 230 = true := by decide +kernel

theorem disposition_at_231 : dispositionTest 231 = true := by decide +kernel

theorem disposition_at_232 : dispositionTest 232 = true := by decide +kernel

theorem disposition_at_233 : dispositionTest 233 = true := by decide +kernel

theorem disposition_at_234 : dispositionTest 234 = true := by decide +kernel

theorem disposition_at_235 : dispositionTest 235 = true := by decide +kernel

theorem disposition_at_236 : dispositionTest 236 = true := by decide +kernel


theorem disposition_at_237 : dispositionTest 237 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 237).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M021.r1384.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M021.r1384) = true
  rw [Nonrational.OldTerminalMatches.M021.r1384_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_238 : dispositionTest 238 = true := by decide +kernel

theorem disposition_at_239 : dispositionTest 239 = true := by decide +kernel

theorem disposition_at_240 : dispositionTest 240 = true := by decide +kernel

theorem disposition_at_241 : dispositionTest 241 = true := by decide +kernel

theorem disposition_at_242 : dispositionTest 242 = true := by decide +kernel

theorem disposition_at_243 : dispositionTest 243 = true := by decide +kernel


theorem disposition_at_244 : dispositionTest 244 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 244).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M021.r1385.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M021.r1385) = true
  rw [Nonrational.OldTerminalMatches.M021.r1385_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_245 : dispositionTest 245 = true := by decide +kernel

theorem disposition_at_246 : dispositionTest 246 = true := by decide +kernel

theorem disposition_at_247 : dispositionTest 247 = true := by decide +kernel

theorem disposition_at_248 : dispositionTest 248 = true := by decide +kernel

theorem disposition_at_249 : dispositionTest 249 = true := by decide +kernel

theorem disposition_at_250 : dispositionTest 250 = true := by decide +kernel

theorem disposition_at_251 : dispositionTest 251 = true := by decide +kernel

theorem disposition_at_252 : dispositionTest 252 = true := by decide +kernel

theorem disposition_at_253 : dispositionTest 253 = true := by decide +kernel

theorem disposition_at_254 : dispositionTest 254 = true := by decide +kernel

theorem disposition_at_255 : dispositionTest 255 = true := by decide +kernel

theorem disposition_interval_224 : Interval dispositionTest 224 225 := by
  intro i hlo hhi
  have h : i = 224 := by omega
  subst i
  exact disposition_at_224


theorem disposition_interval_225 : Interval dispositionTest 225 226 := by
  intro i hlo hhi
  have h : i = 225 := by omega
  subst i
  exact disposition_at_225


theorem disposition_interval_226 : Interval dispositionTest 226 227 := by
  intro i hlo hhi
  have h : i = 226 := by omega
  subst i
  exact disposition_at_226


theorem disposition_interval_227 : Interval dispositionTest 227 228 := by
  intro i hlo hhi
  have h : i = 227 := by omega
  subst i
  exact disposition_at_227


theorem disposition_interval_228 : Interval dispositionTest 228 229 := by
  intro i hlo hhi
  have h : i = 228 := by omega
  subst i
  exact disposition_at_228


theorem disposition_interval_229 : Interval dispositionTest 229 230 := by
  intro i hlo hhi
  have h : i = 229 := by omega
  subst i
  exact disposition_at_229


theorem disposition_interval_230 : Interval dispositionTest 230 231 := by
  intro i hlo hhi
  have h : i = 230 := by omega
  subst i
  exact disposition_at_230


theorem disposition_interval_231 : Interval dispositionTest 231 232 := by
  intro i hlo hhi
  have h : i = 231 := by omega
  subst i
  exact disposition_at_231


theorem disposition_interval_232 : Interval dispositionTest 232 233 := by
  intro i hlo hhi
  have h : i = 232 := by omega
  subst i
  exact disposition_at_232


theorem disposition_interval_233 : Interval dispositionTest 233 234 := by
  intro i hlo hhi
  have h : i = 233 := by omega
  subst i
  exact disposition_at_233


theorem disposition_interval_234 : Interval dispositionTest 234 235 := by
  intro i hlo hhi
  have h : i = 234 := by omega
  subst i
  exact disposition_at_234


theorem disposition_interval_235 : Interval dispositionTest 235 236 := by
  intro i hlo hhi
  have h : i = 235 := by omega
  subst i
  exact disposition_at_235


theorem disposition_interval_236 : Interval dispositionTest 236 237 := by
  intro i hlo hhi
  have h : i = 236 := by omega
  subst i
  exact disposition_at_236


theorem disposition_interval_237 : Interval dispositionTest 237 238 := by
  intro i hlo hhi
  have h : i = 237 := by omega
  subst i
  exact disposition_at_237


theorem disposition_interval_238 : Interval dispositionTest 238 239 := by
  intro i hlo hhi
  have h : i = 238 := by omega
  subst i
  exact disposition_at_238


theorem disposition_interval_239 : Interval dispositionTest 239 240 := by
  intro i hlo hhi
  have h : i = 239 := by omega
  subst i
  exact disposition_at_239


theorem disposition_interval_240 : Interval dispositionTest 240 241 := by
  intro i hlo hhi
  have h : i = 240 := by omega
  subst i
  exact disposition_at_240


theorem disposition_interval_241 : Interval dispositionTest 241 242 := by
  intro i hlo hhi
  have h : i = 241 := by omega
  subst i
  exact disposition_at_241


theorem disposition_interval_242 : Interval dispositionTest 242 243 := by
  intro i hlo hhi
  have h : i = 242 := by omega
  subst i
  exact disposition_at_242


theorem disposition_interval_243 : Interval dispositionTest 243 244 := by
  intro i hlo hhi
  have h : i = 243 := by omega
  subst i
  exact disposition_at_243


theorem disposition_interval_244 : Interval dispositionTest 244 245 := by
  intro i hlo hhi
  have h : i = 244 := by omega
  subst i
  exact disposition_at_244


theorem disposition_interval_245 : Interval dispositionTest 245 246 := by
  intro i hlo hhi
  have h : i = 245 := by omega
  subst i
  exact disposition_at_245


theorem disposition_interval_246 : Interval dispositionTest 246 247 := by
  intro i hlo hhi
  have h : i = 246 := by omega
  subst i
  exact disposition_at_246


theorem disposition_interval_247 : Interval dispositionTest 247 248 := by
  intro i hlo hhi
  have h : i = 247 := by omega
  subst i
  exact disposition_at_247


theorem disposition_interval_248 : Interval dispositionTest 248 249 := by
  intro i hlo hhi
  have h : i = 248 := by omega
  subst i
  exact disposition_at_248


theorem disposition_interval_249 : Interval dispositionTest 249 250 := by
  intro i hlo hhi
  have h : i = 249 := by omega
  subst i
  exact disposition_at_249


theorem disposition_interval_250 : Interval dispositionTest 250 251 := by
  intro i hlo hhi
  have h : i = 250 := by omega
  subst i
  exact disposition_at_250


theorem disposition_interval_251 : Interval dispositionTest 251 252 := by
  intro i hlo hhi
  have h : i = 251 := by omega
  subst i
  exact disposition_at_251


theorem disposition_interval_252 : Interval dispositionTest 252 253 := by
  intro i hlo hhi
  have h : i = 252 := by omega
  subst i
  exact disposition_at_252


theorem disposition_interval_253 : Interval dispositionTest 253 254 := by
  intro i hlo hhi
  have h : i = 253 := by omega
  subst i
  exact disposition_at_253


theorem disposition_interval_254 : Interval dispositionTest 254 255 := by
  intro i hlo hhi
  have h : i = 254 := by omega
  subst i
  exact disposition_at_254


theorem disposition_interval_255 : Interval dispositionTest 255 256 := by
  intro i hlo hhi
  have h : i = 255 := by omega
  subst i
  exact disposition_at_255

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0722
