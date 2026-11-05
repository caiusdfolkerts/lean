module
prelude
public import RootedSubsumedForest0724DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_2048 : dispositionTest 2048 = true := by decide +kernel

theorem disposition_at_2049 : dispositionTest 2049 = true := by decide +kernel

theorem disposition_at_2050 : dispositionTest 2050 = true := by decide +kernel

theorem disposition_at_2051 : dispositionTest 2051 = true := by decide +kernel

theorem disposition_at_2052 : dispositionTest 2052 = true := by decide +kernel

theorem disposition_at_2053 : dispositionTest 2053 = true := by decide +kernel

theorem disposition_at_2054 : dispositionTest 2054 = true := by decide +kernel

theorem disposition_at_2055 : dispositionTest 2055 = true := by decide +kernel

theorem disposition_at_2056 : dispositionTest 2056 = true := by decide +kernel

theorem disposition_at_2057 : dispositionTest 2057 = true := by decide +kernel

theorem disposition_at_2058 : dispositionTest 2058 = true := by decide +kernel

theorem disposition_at_2059 : dispositionTest 2059 = true := by decide +kernel

theorem disposition_at_2060 : dispositionTest 2060 = true := by decide +kernel

theorem disposition_at_2061 : dispositionTest 2061 = true := by decide +kernel

theorem disposition_at_2062 : dispositionTest 2062 = true := by decide +kernel

theorem disposition_at_2063 : dispositionTest 2063 = true := by decide +kernel

theorem disposition_at_2064 : dispositionTest 2064 = true := by decide +kernel

theorem disposition_at_2065 : dispositionTest 2065 = true := by decide +kernel

theorem disposition_at_2066 : dispositionTest 2066 = true := by decide +kernel

theorem disposition_at_2067 : dispositionTest 2067 = true := by decide +kernel

theorem disposition_at_2068 : dispositionTest 2068 = true := by decide +kernel

theorem disposition_at_2069 : dispositionTest 2069 = true := by decide +kernel

theorem disposition_at_2070 : dispositionTest 2070 = true := by decide +kernel

theorem disposition_at_2071 : dispositionTest 2071 = true := by decide +kernel

theorem disposition_at_2072 : dispositionTest 2072 = true := by decide +kernel

theorem disposition_at_2073 : dispositionTest 2073 = true := by decide +kernel

theorem disposition_at_2074 : dispositionTest 2074 = true := by decide +kernel

theorem disposition_at_2075 : dispositionTest 2075 = true := by decide +kernel

theorem disposition_at_2076 : dispositionTest 2076 = true := by decide +kernel

theorem disposition_at_2077 : dispositionTest 2077 = true := by decide +kernel

theorem disposition_at_2078 : dispositionTest 2078 = true := by decide +kernel

theorem disposition_at_2079 : dispositionTest 2079 = true := by decide +kernel

theorem disposition_interval_2048 : Interval dispositionTest 2048 2049 := by
  intro i hlo hhi
  have h : i = 2048 := by omega
  subst i
  exact disposition_at_2048


theorem disposition_interval_2049 : Interval dispositionTest 2049 2050 := by
  intro i hlo hhi
  have h : i = 2049 := by omega
  subst i
  exact disposition_at_2049


theorem disposition_interval_2050 : Interval dispositionTest 2050 2051 := by
  intro i hlo hhi
  have h : i = 2050 := by omega
  subst i
  exact disposition_at_2050


theorem disposition_interval_2051 : Interval dispositionTest 2051 2052 := by
  intro i hlo hhi
  have h : i = 2051 := by omega
  subst i
  exact disposition_at_2051


theorem disposition_interval_2052 : Interval dispositionTest 2052 2053 := by
  intro i hlo hhi
  have h : i = 2052 := by omega
  subst i
  exact disposition_at_2052


theorem disposition_interval_2053 : Interval dispositionTest 2053 2054 := by
  intro i hlo hhi
  have h : i = 2053 := by omega
  subst i
  exact disposition_at_2053


theorem disposition_interval_2054 : Interval dispositionTest 2054 2055 := by
  intro i hlo hhi
  have h : i = 2054 := by omega
  subst i
  exact disposition_at_2054


theorem disposition_interval_2055 : Interval dispositionTest 2055 2056 := by
  intro i hlo hhi
  have h : i = 2055 := by omega
  subst i
  exact disposition_at_2055


theorem disposition_interval_2056 : Interval dispositionTest 2056 2057 := by
  intro i hlo hhi
  have h : i = 2056 := by omega
  subst i
  exact disposition_at_2056


theorem disposition_interval_2057 : Interval dispositionTest 2057 2058 := by
  intro i hlo hhi
  have h : i = 2057 := by omega
  subst i
  exact disposition_at_2057


theorem disposition_interval_2058 : Interval dispositionTest 2058 2059 := by
  intro i hlo hhi
  have h : i = 2058 := by omega
  subst i
  exact disposition_at_2058


theorem disposition_interval_2059 : Interval dispositionTest 2059 2060 := by
  intro i hlo hhi
  have h : i = 2059 := by omega
  subst i
  exact disposition_at_2059


theorem disposition_interval_2060 : Interval dispositionTest 2060 2061 := by
  intro i hlo hhi
  have h : i = 2060 := by omega
  subst i
  exact disposition_at_2060


theorem disposition_interval_2061 : Interval dispositionTest 2061 2062 := by
  intro i hlo hhi
  have h : i = 2061 := by omega
  subst i
  exact disposition_at_2061


theorem disposition_interval_2062 : Interval dispositionTest 2062 2063 := by
  intro i hlo hhi
  have h : i = 2062 := by omega
  subst i
  exact disposition_at_2062


theorem disposition_interval_2063 : Interval dispositionTest 2063 2064 := by
  intro i hlo hhi
  have h : i = 2063 := by omega
  subst i
  exact disposition_at_2063


theorem disposition_interval_2064 : Interval dispositionTest 2064 2065 := by
  intro i hlo hhi
  have h : i = 2064 := by omega
  subst i
  exact disposition_at_2064


theorem disposition_interval_2065 : Interval dispositionTest 2065 2066 := by
  intro i hlo hhi
  have h : i = 2065 := by omega
  subst i
  exact disposition_at_2065


theorem disposition_interval_2066 : Interval dispositionTest 2066 2067 := by
  intro i hlo hhi
  have h : i = 2066 := by omega
  subst i
  exact disposition_at_2066


theorem disposition_interval_2067 : Interval dispositionTest 2067 2068 := by
  intro i hlo hhi
  have h : i = 2067 := by omega
  subst i
  exact disposition_at_2067


theorem disposition_interval_2068 : Interval dispositionTest 2068 2069 := by
  intro i hlo hhi
  have h : i = 2068 := by omega
  subst i
  exact disposition_at_2068


theorem disposition_interval_2069 : Interval dispositionTest 2069 2070 := by
  intro i hlo hhi
  have h : i = 2069 := by omega
  subst i
  exact disposition_at_2069


theorem disposition_interval_2070 : Interval dispositionTest 2070 2071 := by
  intro i hlo hhi
  have h : i = 2070 := by omega
  subst i
  exact disposition_at_2070


theorem disposition_interval_2071 : Interval dispositionTest 2071 2072 := by
  intro i hlo hhi
  have h : i = 2071 := by omega
  subst i
  exact disposition_at_2071


theorem disposition_interval_2072 : Interval dispositionTest 2072 2073 := by
  intro i hlo hhi
  have h : i = 2072 := by omega
  subst i
  exact disposition_at_2072


theorem disposition_interval_2073 : Interval dispositionTest 2073 2074 := by
  intro i hlo hhi
  have h : i = 2073 := by omega
  subst i
  exact disposition_at_2073


theorem disposition_interval_2074 : Interval dispositionTest 2074 2075 := by
  intro i hlo hhi
  have h : i = 2074 := by omega
  subst i
  exact disposition_at_2074


theorem disposition_interval_2075 : Interval dispositionTest 2075 2076 := by
  intro i hlo hhi
  have h : i = 2075 := by omega
  subst i
  exact disposition_at_2075


theorem disposition_interval_2076 : Interval dispositionTest 2076 2077 := by
  intro i hlo hhi
  have h : i = 2076 := by omega
  subst i
  exact disposition_at_2076


theorem disposition_interval_2077 : Interval dispositionTest 2077 2078 := by
  intro i hlo hhi
  have h : i = 2077 := by omega
  subst i
  exact disposition_at_2077


theorem disposition_interval_2078 : Interval dispositionTest 2078 2079 := by
  intro i hlo hhi
  have h : i = 2078 := by omega
  subst i
  exact disposition_at_2078


theorem disposition_interval_2079 : Interval dispositionTest 2079 2080 := by
  intro i hlo hhi
  have h : i = 2079 := by omega
  subst i
  exact disposition_at_2079

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
