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
theorem disposition_at_2016 : dispositionTest 2016 = true := by decide +kernel

theorem disposition_at_2017 : dispositionTest 2017 = true := by decide +kernel

theorem disposition_at_2018 : dispositionTest 2018 = true := by decide +kernel

theorem disposition_at_2019 : dispositionTest 2019 = true := by decide +kernel

theorem disposition_at_2020 : dispositionTest 2020 = true := by decide +kernel

theorem disposition_at_2021 : dispositionTest 2021 = true := by decide +kernel

theorem disposition_at_2022 : dispositionTest 2022 = true := by decide +kernel

theorem disposition_at_2023 : dispositionTest 2023 = true := by decide +kernel

theorem disposition_at_2024 : dispositionTest 2024 = true := by decide +kernel

theorem disposition_at_2025 : dispositionTest 2025 = true := by decide +kernel

theorem disposition_at_2026 : dispositionTest 2026 = true := by decide +kernel

theorem disposition_at_2027 : dispositionTest 2027 = true := by decide +kernel

theorem disposition_at_2028 : dispositionTest 2028 = true := by decide +kernel

theorem disposition_at_2029 : dispositionTest 2029 = true := by decide +kernel

theorem disposition_at_2030 : dispositionTest 2030 = true := by decide +kernel

theorem disposition_at_2031 : dispositionTest 2031 = true := by decide +kernel

theorem disposition_at_2032 : dispositionTest 2032 = true := by decide +kernel

theorem disposition_at_2033 : dispositionTest 2033 = true := by decide +kernel

theorem disposition_at_2034 : dispositionTest 2034 = true := by decide +kernel

theorem disposition_at_2035 : dispositionTest 2035 = true := by decide +kernel

theorem disposition_at_2036 : dispositionTest 2036 = true := by decide +kernel

theorem disposition_at_2037 : dispositionTest 2037 = true := by decide +kernel

theorem disposition_at_2038 : dispositionTest 2038 = true := by decide +kernel

theorem disposition_at_2039 : dispositionTest 2039 = true := by decide +kernel

theorem disposition_at_2040 : dispositionTest 2040 = true := by decide +kernel

theorem disposition_at_2041 : dispositionTest 2041 = true := by decide +kernel

theorem disposition_at_2042 : dispositionTest 2042 = true := by decide +kernel

theorem disposition_at_2043 : dispositionTest 2043 = true := by decide +kernel

theorem disposition_at_2044 : dispositionTest 2044 = true := by decide +kernel

theorem disposition_at_2045 : dispositionTest 2045 = true := by decide +kernel

theorem disposition_at_2046 : dispositionTest 2046 = true := by decide +kernel

theorem disposition_at_2047 : dispositionTest 2047 = true := by decide +kernel

theorem disposition_interval_2016 : Interval dispositionTest 2016 2017 := by
  intro i hlo hhi
  have h : i = 2016 := by omega
  subst i
  exact disposition_at_2016


theorem disposition_interval_2017 : Interval dispositionTest 2017 2018 := by
  intro i hlo hhi
  have h : i = 2017 := by omega
  subst i
  exact disposition_at_2017


theorem disposition_interval_2018 : Interval dispositionTest 2018 2019 := by
  intro i hlo hhi
  have h : i = 2018 := by omega
  subst i
  exact disposition_at_2018


theorem disposition_interval_2019 : Interval dispositionTest 2019 2020 := by
  intro i hlo hhi
  have h : i = 2019 := by omega
  subst i
  exact disposition_at_2019


theorem disposition_interval_2020 : Interval dispositionTest 2020 2021 := by
  intro i hlo hhi
  have h : i = 2020 := by omega
  subst i
  exact disposition_at_2020


theorem disposition_interval_2021 : Interval dispositionTest 2021 2022 := by
  intro i hlo hhi
  have h : i = 2021 := by omega
  subst i
  exact disposition_at_2021


theorem disposition_interval_2022 : Interval dispositionTest 2022 2023 := by
  intro i hlo hhi
  have h : i = 2022 := by omega
  subst i
  exact disposition_at_2022


theorem disposition_interval_2023 : Interval dispositionTest 2023 2024 := by
  intro i hlo hhi
  have h : i = 2023 := by omega
  subst i
  exact disposition_at_2023


theorem disposition_interval_2024 : Interval dispositionTest 2024 2025 := by
  intro i hlo hhi
  have h : i = 2024 := by omega
  subst i
  exact disposition_at_2024


theorem disposition_interval_2025 : Interval dispositionTest 2025 2026 := by
  intro i hlo hhi
  have h : i = 2025 := by omega
  subst i
  exact disposition_at_2025


theorem disposition_interval_2026 : Interval dispositionTest 2026 2027 := by
  intro i hlo hhi
  have h : i = 2026 := by omega
  subst i
  exact disposition_at_2026


theorem disposition_interval_2027 : Interval dispositionTest 2027 2028 := by
  intro i hlo hhi
  have h : i = 2027 := by omega
  subst i
  exact disposition_at_2027


theorem disposition_interval_2028 : Interval dispositionTest 2028 2029 := by
  intro i hlo hhi
  have h : i = 2028 := by omega
  subst i
  exact disposition_at_2028


theorem disposition_interval_2029 : Interval dispositionTest 2029 2030 := by
  intro i hlo hhi
  have h : i = 2029 := by omega
  subst i
  exact disposition_at_2029


theorem disposition_interval_2030 : Interval dispositionTest 2030 2031 := by
  intro i hlo hhi
  have h : i = 2030 := by omega
  subst i
  exact disposition_at_2030


theorem disposition_interval_2031 : Interval dispositionTest 2031 2032 := by
  intro i hlo hhi
  have h : i = 2031 := by omega
  subst i
  exact disposition_at_2031


theorem disposition_interval_2032 : Interval dispositionTest 2032 2033 := by
  intro i hlo hhi
  have h : i = 2032 := by omega
  subst i
  exact disposition_at_2032


theorem disposition_interval_2033 : Interval dispositionTest 2033 2034 := by
  intro i hlo hhi
  have h : i = 2033 := by omega
  subst i
  exact disposition_at_2033


theorem disposition_interval_2034 : Interval dispositionTest 2034 2035 := by
  intro i hlo hhi
  have h : i = 2034 := by omega
  subst i
  exact disposition_at_2034


theorem disposition_interval_2035 : Interval dispositionTest 2035 2036 := by
  intro i hlo hhi
  have h : i = 2035 := by omega
  subst i
  exact disposition_at_2035


theorem disposition_interval_2036 : Interval dispositionTest 2036 2037 := by
  intro i hlo hhi
  have h : i = 2036 := by omega
  subst i
  exact disposition_at_2036


theorem disposition_interval_2037 : Interval dispositionTest 2037 2038 := by
  intro i hlo hhi
  have h : i = 2037 := by omega
  subst i
  exact disposition_at_2037


theorem disposition_interval_2038 : Interval dispositionTest 2038 2039 := by
  intro i hlo hhi
  have h : i = 2038 := by omega
  subst i
  exact disposition_at_2038


theorem disposition_interval_2039 : Interval dispositionTest 2039 2040 := by
  intro i hlo hhi
  have h : i = 2039 := by omega
  subst i
  exact disposition_at_2039


theorem disposition_interval_2040 : Interval dispositionTest 2040 2041 := by
  intro i hlo hhi
  have h : i = 2040 := by omega
  subst i
  exact disposition_at_2040


theorem disposition_interval_2041 : Interval dispositionTest 2041 2042 := by
  intro i hlo hhi
  have h : i = 2041 := by omega
  subst i
  exact disposition_at_2041


theorem disposition_interval_2042 : Interval dispositionTest 2042 2043 := by
  intro i hlo hhi
  have h : i = 2042 := by omega
  subst i
  exact disposition_at_2042


theorem disposition_interval_2043 : Interval dispositionTest 2043 2044 := by
  intro i hlo hhi
  have h : i = 2043 := by omega
  subst i
  exact disposition_at_2043


theorem disposition_interval_2044 : Interval dispositionTest 2044 2045 := by
  intro i hlo hhi
  have h : i = 2044 := by omega
  subst i
  exact disposition_at_2044


theorem disposition_interval_2045 : Interval dispositionTest 2045 2046 := by
  intro i hlo hhi
  have h : i = 2045 := by omega
  subst i
  exact disposition_at_2045


theorem disposition_interval_2046 : Interval dispositionTest 2046 2047 := by
  intro i hlo hhi
  have h : i = 2046 := by omega
  subst i
  exact disposition_at_2046


theorem disposition_interval_2047 : Interval dispositionTest 2047 2048 := by
  intro i hlo hhi
  have h : i = 2047 := by omega
  subst i
  exact disposition_at_2047

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
