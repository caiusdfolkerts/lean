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
theorem disposition_at_2208 : dispositionTest 2208 = true := by decide +kernel

theorem disposition_at_2209 : dispositionTest 2209 = true := by decide +kernel

theorem disposition_at_2210 : dispositionTest 2210 = true := by decide +kernel

theorem disposition_at_2211 : dispositionTest 2211 = true := by decide +kernel

theorem disposition_at_2212 : dispositionTest 2212 = true := by decide +kernel

theorem disposition_at_2213 : dispositionTest 2213 = true := by decide +kernel

theorem disposition_at_2214 : dispositionTest 2214 = true := by decide +kernel

theorem disposition_at_2215 : dispositionTest 2215 = true := by decide +kernel

theorem disposition_at_2216 : dispositionTest 2216 = true := by decide +kernel

theorem disposition_at_2217 : dispositionTest 2217 = true := by decide +kernel

theorem disposition_at_2218 : dispositionTest 2218 = true := by decide +kernel

theorem disposition_at_2219 : dispositionTest 2219 = true := by decide +kernel

theorem disposition_at_2220 : dispositionTest 2220 = true := by decide +kernel

theorem disposition_at_2221 : dispositionTest 2221 = true := by decide +kernel

theorem disposition_at_2222 : dispositionTest 2222 = true := by decide +kernel

theorem disposition_at_2223 : dispositionTest 2223 = true := by decide +kernel

theorem disposition_at_2224 : dispositionTest 2224 = true := by decide +kernel

theorem disposition_at_2225 : dispositionTest 2225 = true := by decide +kernel

theorem disposition_at_2226 : dispositionTest 2226 = true := by decide +kernel

theorem disposition_at_2227 : dispositionTest 2227 = true := by decide +kernel

theorem disposition_at_2228 : dispositionTest 2228 = true := by decide +kernel

theorem disposition_at_2229 : dispositionTest 2229 = true := by decide +kernel

theorem disposition_at_2230 : dispositionTest 2230 = true := by decide +kernel

theorem disposition_at_2231 : dispositionTest 2231 = true := by decide +kernel

theorem disposition_at_2232 : dispositionTest 2232 = true := by decide +kernel

theorem disposition_at_2233 : dispositionTest 2233 = true := by decide +kernel

theorem disposition_at_2234 : dispositionTest 2234 = true := by decide +kernel

theorem disposition_at_2235 : dispositionTest 2235 = true := by decide +kernel

theorem disposition_at_2236 : dispositionTest 2236 = true := by decide +kernel

theorem disposition_at_2237 : dispositionTest 2237 = true := by decide +kernel

theorem disposition_at_2238 : dispositionTest 2238 = true := by decide +kernel

theorem disposition_at_2239 : dispositionTest 2239 = true := by decide +kernel

theorem disposition_interval_2208 : Interval dispositionTest 2208 2209 := by
  intro i hlo hhi
  have h : i = 2208 := by omega
  subst i
  exact disposition_at_2208


theorem disposition_interval_2209 : Interval dispositionTest 2209 2210 := by
  intro i hlo hhi
  have h : i = 2209 := by omega
  subst i
  exact disposition_at_2209


theorem disposition_interval_2210 : Interval dispositionTest 2210 2211 := by
  intro i hlo hhi
  have h : i = 2210 := by omega
  subst i
  exact disposition_at_2210


theorem disposition_interval_2211 : Interval dispositionTest 2211 2212 := by
  intro i hlo hhi
  have h : i = 2211 := by omega
  subst i
  exact disposition_at_2211


theorem disposition_interval_2212 : Interval dispositionTest 2212 2213 := by
  intro i hlo hhi
  have h : i = 2212 := by omega
  subst i
  exact disposition_at_2212


theorem disposition_interval_2213 : Interval dispositionTest 2213 2214 := by
  intro i hlo hhi
  have h : i = 2213 := by omega
  subst i
  exact disposition_at_2213


theorem disposition_interval_2214 : Interval dispositionTest 2214 2215 := by
  intro i hlo hhi
  have h : i = 2214 := by omega
  subst i
  exact disposition_at_2214


theorem disposition_interval_2215 : Interval dispositionTest 2215 2216 := by
  intro i hlo hhi
  have h : i = 2215 := by omega
  subst i
  exact disposition_at_2215


theorem disposition_interval_2216 : Interval dispositionTest 2216 2217 := by
  intro i hlo hhi
  have h : i = 2216 := by omega
  subst i
  exact disposition_at_2216


theorem disposition_interval_2217 : Interval dispositionTest 2217 2218 := by
  intro i hlo hhi
  have h : i = 2217 := by omega
  subst i
  exact disposition_at_2217


theorem disposition_interval_2218 : Interval dispositionTest 2218 2219 := by
  intro i hlo hhi
  have h : i = 2218 := by omega
  subst i
  exact disposition_at_2218


theorem disposition_interval_2219 : Interval dispositionTest 2219 2220 := by
  intro i hlo hhi
  have h : i = 2219 := by omega
  subst i
  exact disposition_at_2219


theorem disposition_interval_2220 : Interval dispositionTest 2220 2221 := by
  intro i hlo hhi
  have h : i = 2220 := by omega
  subst i
  exact disposition_at_2220


theorem disposition_interval_2221 : Interval dispositionTest 2221 2222 := by
  intro i hlo hhi
  have h : i = 2221 := by omega
  subst i
  exact disposition_at_2221


theorem disposition_interval_2222 : Interval dispositionTest 2222 2223 := by
  intro i hlo hhi
  have h : i = 2222 := by omega
  subst i
  exact disposition_at_2222


theorem disposition_interval_2223 : Interval dispositionTest 2223 2224 := by
  intro i hlo hhi
  have h : i = 2223 := by omega
  subst i
  exact disposition_at_2223


theorem disposition_interval_2224 : Interval dispositionTest 2224 2225 := by
  intro i hlo hhi
  have h : i = 2224 := by omega
  subst i
  exact disposition_at_2224


theorem disposition_interval_2225 : Interval dispositionTest 2225 2226 := by
  intro i hlo hhi
  have h : i = 2225 := by omega
  subst i
  exact disposition_at_2225


theorem disposition_interval_2226 : Interval dispositionTest 2226 2227 := by
  intro i hlo hhi
  have h : i = 2226 := by omega
  subst i
  exact disposition_at_2226


theorem disposition_interval_2227 : Interval dispositionTest 2227 2228 := by
  intro i hlo hhi
  have h : i = 2227 := by omega
  subst i
  exact disposition_at_2227


theorem disposition_interval_2228 : Interval dispositionTest 2228 2229 := by
  intro i hlo hhi
  have h : i = 2228 := by omega
  subst i
  exact disposition_at_2228


theorem disposition_interval_2229 : Interval dispositionTest 2229 2230 := by
  intro i hlo hhi
  have h : i = 2229 := by omega
  subst i
  exact disposition_at_2229


theorem disposition_interval_2230 : Interval dispositionTest 2230 2231 := by
  intro i hlo hhi
  have h : i = 2230 := by omega
  subst i
  exact disposition_at_2230


theorem disposition_interval_2231 : Interval dispositionTest 2231 2232 := by
  intro i hlo hhi
  have h : i = 2231 := by omega
  subst i
  exact disposition_at_2231


theorem disposition_interval_2232 : Interval dispositionTest 2232 2233 := by
  intro i hlo hhi
  have h : i = 2232 := by omega
  subst i
  exact disposition_at_2232


theorem disposition_interval_2233 : Interval dispositionTest 2233 2234 := by
  intro i hlo hhi
  have h : i = 2233 := by omega
  subst i
  exact disposition_at_2233


theorem disposition_interval_2234 : Interval dispositionTest 2234 2235 := by
  intro i hlo hhi
  have h : i = 2234 := by omega
  subst i
  exact disposition_at_2234


theorem disposition_interval_2235 : Interval dispositionTest 2235 2236 := by
  intro i hlo hhi
  have h : i = 2235 := by omega
  subst i
  exact disposition_at_2235


theorem disposition_interval_2236 : Interval dispositionTest 2236 2237 := by
  intro i hlo hhi
  have h : i = 2236 := by omega
  subst i
  exact disposition_at_2236


theorem disposition_interval_2237 : Interval dispositionTest 2237 2238 := by
  intro i hlo hhi
  have h : i = 2237 := by omega
  subst i
  exact disposition_at_2237


theorem disposition_interval_2238 : Interval dispositionTest 2238 2239 := by
  intro i hlo hhi
  have h : i = 2238 := by omega
  subst i
  exact disposition_at_2238


theorem disposition_interval_2239 : Interval dispositionTest 2239 2240 := by
  intro i hlo hhi
  have h : i = 2239 := by omega
  subst i
  exact disposition_at_2239

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
