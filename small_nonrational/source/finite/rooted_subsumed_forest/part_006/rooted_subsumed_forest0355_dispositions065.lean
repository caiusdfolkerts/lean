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
theorem disposition_at_2080 : dispositionTest 2080 = true := by decide +kernel

theorem disposition_at_2081 : dispositionTest 2081 = true := by decide +kernel

theorem disposition_at_2082 : dispositionTest 2082 = true := by decide +kernel

theorem disposition_at_2083 : dispositionTest 2083 = true := by decide +kernel

theorem disposition_at_2084 : dispositionTest 2084 = true := by decide +kernel

theorem disposition_at_2085 : dispositionTest 2085 = true := by decide +kernel

theorem disposition_at_2086 : dispositionTest 2086 = true := by decide +kernel

theorem disposition_at_2087 : dispositionTest 2087 = true := by decide +kernel

theorem disposition_at_2088 : dispositionTest 2088 = true := by decide +kernel

theorem disposition_at_2089 : dispositionTest 2089 = true := by decide +kernel

theorem disposition_at_2090 : dispositionTest 2090 = true := by decide +kernel

theorem disposition_at_2091 : dispositionTest 2091 = true := by decide +kernel

theorem disposition_at_2092 : dispositionTest 2092 = true := by decide +kernel

theorem disposition_at_2093 : dispositionTest 2093 = true := by decide +kernel

theorem disposition_at_2094 : dispositionTest 2094 = true := by decide +kernel

theorem disposition_at_2095 : dispositionTest 2095 = true := by decide +kernel

theorem disposition_at_2096 : dispositionTest 2096 = true := by decide +kernel

theorem disposition_at_2097 : dispositionTest 2097 = true := by decide +kernel

theorem disposition_at_2098 : dispositionTest 2098 = true := by decide +kernel

theorem disposition_at_2099 : dispositionTest 2099 = true := by decide +kernel

theorem disposition_at_2100 : dispositionTest 2100 = true := by decide +kernel

theorem disposition_at_2101 : dispositionTest 2101 = true := by decide +kernel

theorem disposition_at_2102 : dispositionTest 2102 = true := by decide +kernel

theorem disposition_at_2103 : dispositionTest 2103 = true := by decide +kernel

theorem disposition_at_2104 : dispositionTest 2104 = true := by decide +kernel

theorem disposition_at_2105 : dispositionTest 2105 = true := by decide +kernel

theorem disposition_at_2106 : dispositionTest 2106 = true := by decide +kernel

theorem disposition_at_2107 : dispositionTest 2107 = true := by decide +kernel

theorem disposition_at_2108 : dispositionTest 2108 = true := by decide +kernel

theorem disposition_at_2109 : dispositionTest 2109 = true := by decide +kernel

theorem disposition_at_2110 : dispositionTest 2110 = true := by decide +kernel

theorem disposition_at_2111 : dispositionTest 2111 = true := by decide +kernel

theorem disposition_interval_2080 : Interval dispositionTest 2080 2081 := by
  intro i hlo hhi
  have h : i = 2080 := by omega
  subst i
  exact disposition_at_2080


theorem disposition_interval_2081 : Interval dispositionTest 2081 2082 := by
  intro i hlo hhi
  have h : i = 2081 := by omega
  subst i
  exact disposition_at_2081


theorem disposition_interval_2082 : Interval dispositionTest 2082 2083 := by
  intro i hlo hhi
  have h : i = 2082 := by omega
  subst i
  exact disposition_at_2082


theorem disposition_interval_2083 : Interval dispositionTest 2083 2084 := by
  intro i hlo hhi
  have h : i = 2083 := by omega
  subst i
  exact disposition_at_2083


theorem disposition_interval_2084 : Interval dispositionTest 2084 2085 := by
  intro i hlo hhi
  have h : i = 2084 := by omega
  subst i
  exact disposition_at_2084


theorem disposition_interval_2085 : Interval dispositionTest 2085 2086 := by
  intro i hlo hhi
  have h : i = 2085 := by omega
  subst i
  exact disposition_at_2085


theorem disposition_interval_2086 : Interval dispositionTest 2086 2087 := by
  intro i hlo hhi
  have h : i = 2086 := by omega
  subst i
  exact disposition_at_2086


theorem disposition_interval_2087 : Interval dispositionTest 2087 2088 := by
  intro i hlo hhi
  have h : i = 2087 := by omega
  subst i
  exact disposition_at_2087


theorem disposition_interval_2088 : Interval dispositionTest 2088 2089 := by
  intro i hlo hhi
  have h : i = 2088 := by omega
  subst i
  exact disposition_at_2088


theorem disposition_interval_2089 : Interval dispositionTest 2089 2090 := by
  intro i hlo hhi
  have h : i = 2089 := by omega
  subst i
  exact disposition_at_2089


theorem disposition_interval_2090 : Interval dispositionTest 2090 2091 := by
  intro i hlo hhi
  have h : i = 2090 := by omega
  subst i
  exact disposition_at_2090


theorem disposition_interval_2091 : Interval dispositionTest 2091 2092 := by
  intro i hlo hhi
  have h : i = 2091 := by omega
  subst i
  exact disposition_at_2091


theorem disposition_interval_2092 : Interval dispositionTest 2092 2093 := by
  intro i hlo hhi
  have h : i = 2092 := by omega
  subst i
  exact disposition_at_2092


theorem disposition_interval_2093 : Interval dispositionTest 2093 2094 := by
  intro i hlo hhi
  have h : i = 2093 := by omega
  subst i
  exact disposition_at_2093


theorem disposition_interval_2094 : Interval dispositionTest 2094 2095 := by
  intro i hlo hhi
  have h : i = 2094 := by omega
  subst i
  exact disposition_at_2094


theorem disposition_interval_2095 : Interval dispositionTest 2095 2096 := by
  intro i hlo hhi
  have h : i = 2095 := by omega
  subst i
  exact disposition_at_2095


theorem disposition_interval_2096 : Interval dispositionTest 2096 2097 := by
  intro i hlo hhi
  have h : i = 2096 := by omega
  subst i
  exact disposition_at_2096


theorem disposition_interval_2097 : Interval dispositionTest 2097 2098 := by
  intro i hlo hhi
  have h : i = 2097 := by omega
  subst i
  exact disposition_at_2097


theorem disposition_interval_2098 : Interval dispositionTest 2098 2099 := by
  intro i hlo hhi
  have h : i = 2098 := by omega
  subst i
  exact disposition_at_2098


theorem disposition_interval_2099 : Interval dispositionTest 2099 2100 := by
  intro i hlo hhi
  have h : i = 2099 := by omega
  subst i
  exact disposition_at_2099


theorem disposition_interval_2100 : Interval dispositionTest 2100 2101 := by
  intro i hlo hhi
  have h : i = 2100 := by omega
  subst i
  exact disposition_at_2100


theorem disposition_interval_2101 : Interval dispositionTest 2101 2102 := by
  intro i hlo hhi
  have h : i = 2101 := by omega
  subst i
  exact disposition_at_2101


theorem disposition_interval_2102 : Interval dispositionTest 2102 2103 := by
  intro i hlo hhi
  have h : i = 2102 := by omega
  subst i
  exact disposition_at_2102


theorem disposition_interval_2103 : Interval dispositionTest 2103 2104 := by
  intro i hlo hhi
  have h : i = 2103 := by omega
  subst i
  exact disposition_at_2103


theorem disposition_interval_2104 : Interval dispositionTest 2104 2105 := by
  intro i hlo hhi
  have h : i = 2104 := by omega
  subst i
  exact disposition_at_2104


theorem disposition_interval_2105 : Interval dispositionTest 2105 2106 := by
  intro i hlo hhi
  have h : i = 2105 := by omega
  subst i
  exact disposition_at_2105


theorem disposition_interval_2106 : Interval dispositionTest 2106 2107 := by
  intro i hlo hhi
  have h : i = 2106 := by omega
  subst i
  exact disposition_at_2106


theorem disposition_interval_2107 : Interval dispositionTest 2107 2108 := by
  intro i hlo hhi
  have h : i = 2107 := by omega
  subst i
  exact disposition_at_2107


theorem disposition_interval_2108 : Interval dispositionTest 2108 2109 := by
  intro i hlo hhi
  have h : i = 2108 := by omega
  subst i
  exact disposition_at_2108


theorem disposition_interval_2109 : Interval dispositionTest 2109 2110 := by
  intro i hlo hhi
  have h : i = 2109 := by omega
  subst i
  exact disposition_at_2109


theorem disposition_interval_2110 : Interval dispositionTest 2110 2111 := by
  intro i hlo hhi
  have h : i = 2110 := by omega
  subst i
  exact disposition_at_2110


theorem disposition_interval_2111 : Interval dispositionTest 2111 2112 := by
  intro i hlo hhi
  have h : i = 2111 := by omega
  subst i
  exact disposition_at_2111

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
