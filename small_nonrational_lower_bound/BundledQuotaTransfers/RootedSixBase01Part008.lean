module
prelude
public import BundledQuotaTransfers.RootedSixBase01Part005

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0353Proof016. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test2048 (i : Nat) := routeTest (i + 2048)
theorem test2048_block_0 : Interval test2048 0 16 :=
  interval_of_check test2048 0 16 (by decide +kernel)

theorem test2048_block_1 : Interval test2048 16 32 :=
  interval_of_check test2048 16 16 (by decide +kernel)

theorem test2048_block_2 : Interval test2048 32 48 :=
  interval_of_check test2048 32 16 (by decide +kernel)

theorem test2048_block_3 : Interval test2048 48 64 :=
  interval_of_check test2048 48 16 (by decide +kernel)

theorem test2048_block_4 : Interval test2048 64 80 :=
  interval_of_check test2048 64 16 (by decide +kernel)

theorem test2048_block_5 : Interval test2048 80 96 :=
  interval_of_check test2048 80 16 (by decide +kernel)

theorem test2048_block_6 : Interval test2048 96 112 :=
  interval_of_check test2048 96 16 (by decide +kernel)

theorem test2048_block_7 : Interval test2048 112 128 :=
  interval_of_check test2048 112 16 (by decide +kernel)

theorem test2048_complete : Interval test2048 0 128 :=
  (interval_append test2048 0 64 128
  (interval_append test2048 0 32 64
  (interval_append test2048 0 16 32
  test2048_block_0
  test2048_block_1)
  (interval_append test2048 32 48 64
  test2048_block_2
  test2048_block_3))
  (interval_append test2048 64 96 128
  (interval_append test2048 64 80 96
  test2048_block_4
  test2048_block_5)
  (interval_append test2048 96 112 128
  test2048_block_6
  test2048_block_7)))
theorem routeInterval2048 : Interval routeTest 2048 2176 := by
  intro i hlo hhi
  have h := test2048_complete (i - 2048) (Nat.zero_le _) (by omega)
  simpa only [test2048, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof017. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test2176 (i : Nat) := routeTest (i + 2176)
theorem test2176_block_0 : Interval test2176 0 16 :=
  interval_of_check test2176 0 16 (by decide +kernel)

theorem test2176_block_1 : Interval test2176 16 32 :=
  interval_of_check test2176 16 16 (by decide +kernel)

theorem test2176_block_2 : Interval test2176 32 48 :=
  interval_of_check test2176 32 16 (by decide +kernel)

theorem test2176_block_3 : Interval test2176 48 64 :=
  interval_of_check test2176 48 16 (by decide +kernel)

theorem test2176_block_4 : Interval test2176 64 80 :=
  interval_of_check test2176 64 16 (by decide +kernel)

theorem test2176_block_5 : Interval test2176 80 96 :=
  interval_of_check test2176 80 16 (by decide +kernel)

theorem test2176_block_6 : Interval test2176 96 112 :=
  interval_of_check test2176 96 16 (by decide +kernel)

theorem test2176_block_7 : Interval test2176 112 128 :=
  interval_of_check test2176 112 16 (by decide +kernel)

theorem test2176_complete : Interval test2176 0 128 :=
  (interval_append test2176 0 64 128
  (interval_append test2176 0 32 64
  (interval_append test2176 0 16 32
  test2176_block_0
  test2176_block_1)
  (interval_append test2176 32 48 64
  test2176_block_2
  test2176_block_3))
  (interval_append test2176 64 96 128
  (interval_append test2176 64 80 96
  test2176_block_4
  test2176_block_5)
  (interval_append test2176 96 112 128
  test2176_block_6
  test2176_block_7)))
theorem routeInterval2176 : Interval routeTest 2176 2304 := by
  intro i hlo hhi
  have h := test2176_complete (i - 2176) (Nat.zero_le _) (by omega)
  simpa only [test2176, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof018. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test2304 (i : Nat) := routeTest (i + 2304)
theorem test2304_block_0 : Interval test2304 0 16 :=
  interval_of_check test2304 0 16 (by decide +kernel)

theorem test2304_block_1 : Interval test2304 16 32 :=
  interval_of_check test2304 16 16 (by decide +kernel)

theorem test2304_block_2 : Interval test2304 32 48 :=
  interval_of_check test2304 32 16 (by decide +kernel)

theorem test2304_block_3 : Interval test2304 48 64 :=
  interval_of_check test2304 48 16 (by decide +kernel)

theorem test2304_block_4 : Interval test2304 64 80 :=
  interval_of_check test2304 64 16 (by decide +kernel)

theorem test2304_block_5 : Interval test2304 80 96 :=
  interval_of_check test2304 80 16 (by decide +kernel)

theorem test2304_block_6 : Interval test2304 96 112 :=
  interval_of_check test2304 96 16 (by decide +kernel)

theorem test2304_block_7 : Interval test2304 112 128 :=
  interval_of_check test2304 112 16 (by decide +kernel)

theorem test2304_complete : Interval test2304 0 128 :=
  (interval_append test2304 0 64 128
  (interval_append test2304 0 32 64
  (interval_append test2304 0 16 32
  test2304_block_0
  test2304_block_1)
  (interval_append test2304 32 48 64
  test2304_block_2
  test2304_block_3))
  (interval_append test2304 64 96 128
  (interval_append test2304 64 80 96
  test2304_block_4
  test2304_block_5)
  (interval_append test2304 96 112 128
  test2304_block_6
  test2304_block_7)))
theorem routeInterval2304 : Interval routeTest 2304 2432 := by
  intro i hlo hhi
  have h := test2304_complete (i - 2304) (Nat.zero_le _) (by omega)
  simpa only [test2304, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof019. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test2432 (i : Nat) := routeTest (i + 2432)
theorem test2432_block_0 : Interval test2432 0 16 :=
  interval_of_check test2432 0 16 (by decide +kernel)

theorem test2432_block_1 : Interval test2432 16 32 :=
  interval_of_check test2432 16 16 (by decide +kernel)

theorem test2432_block_2 : Interval test2432 32 48 :=
  interval_of_check test2432 32 16 (by decide +kernel)

theorem test2432_block_3 : Interval test2432 48 64 :=
  interval_of_check test2432 48 16 (by decide +kernel)

theorem test2432_block_4 : Interval test2432 64 80 :=
  interval_of_check test2432 64 16 (by decide +kernel)

theorem test2432_block_5 : Interval test2432 80 96 :=
  interval_of_check test2432 80 16 (by decide +kernel)

theorem test2432_block_6 : Interval test2432 96 112 :=
  interval_of_check test2432 96 16 (by decide +kernel)

theorem test2432_block_7 : Interval test2432 112 128 :=
  interval_of_check test2432 112 16 (by decide +kernel)

theorem test2432_complete : Interval test2432 0 128 :=
  (interval_append test2432 0 64 128
  (interval_append test2432 0 32 64
  (interval_append test2432 0 16 32
  test2432_block_0
  test2432_block_1)
  (interval_append test2432 32 48 64
  test2432_block_2
  test2432_block_3))
  (interval_append test2432 64 96 128
  (interval_append test2432 64 80 96
  test2432_block_4
  test2432_block_5)
  (interval_append test2432 96 112 128
  test2432_block_6
  test2432_block_7)))
theorem routeInterval2432 : Interval routeTest 2432 2560 := by
  intro i hlo hhi
  have h := test2432_complete (i - 2432) (Nat.zero_le _) (by omega)
  simpa only [test2432, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof020. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test2560 (i : Nat) := routeTest (i + 2560)
theorem test2560_block_0 : Interval test2560 0 16 :=
  interval_of_check test2560 0 16 (by decide +kernel)

theorem test2560_block_1 : Interval test2560 16 32 :=
  interval_of_check test2560 16 16 (by decide +kernel)

theorem test2560_block_2 : Interval test2560 32 48 :=
  interval_of_check test2560 32 16 (by decide +kernel)

theorem test2560_block_3 : Interval test2560 48 64 :=
  interval_of_check test2560 48 16 (by decide +kernel)

theorem test2560_block_4 : Interval test2560 64 80 :=
  interval_of_check test2560 64 16 (by decide +kernel)

theorem test2560_block_5 : Interval test2560 80 96 :=
  interval_of_check test2560 80 16 (by decide +kernel)

theorem test2560_block_6 : Interval test2560 96 112 :=
  interval_of_check test2560 96 16 (by decide +kernel)

theorem test2560_block_7 : Interval test2560 112 128 :=
  interval_of_check test2560 112 16 (by decide +kernel)

theorem test2560_complete : Interval test2560 0 128 :=
  (interval_append test2560 0 64 128
  (interval_append test2560 0 32 64
  (interval_append test2560 0 16 32
  test2560_block_0
  test2560_block_1)
  (interval_append test2560 32 48 64
  test2560_block_2
  test2560_block_3))
  (interval_append test2560 64 96 128
  (interval_append test2560 64 80 96
  test2560_block_4
  test2560_block_5)
  (interval_append test2560 96 112 128
  test2560_block_6
  test2560_block_7)))
theorem routeInterval2560 : Interval routeTest 2560 2688 := by
  intro i hlo hhi
  have h := test2560_complete (i - 2560) (Nat.zero_le _) (by omega)
  simpa only [test2560, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof021. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test2688 (i : Nat) := routeTest (i + 2688)
theorem test2688_block_0 : Interval test2688 0 16 :=
  interval_of_check test2688 0 16 (by decide +kernel)

theorem test2688_block_1 : Interval test2688 16 32 :=
  interval_of_check test2688 16 16 (by decide +kernel)

theorem test2688_block_2 : Interval test2688 32 48 :=
  interval_of_check test2688 32 16 (by decide +kernel)

theorem test2688_block_3 : Interval test2688 48 64 :=
  interval_of_check test2688 48 16 (by decide +kernel)

theorem test2688_block_4 : Interval test2688 64 80 :=
  interval_of_check test2688 64 16 (by decide +kernel)

theorem test2688_block_5 : Interval test2688 80 96 :=
  interval_of_check test2688 80 16 (by decide +kernel)

theorem test2688_block_6 : Interval test2688 96 112 :=
  interval_of_check test2688 96 16 (by decide +kernel)

theorem test2688_block_7 : Interval test2688 112 128 :=
  interval_of_check test2688 112 16 (by decide +kernel)

theorem test2688_complete : Interval test2688 0 128 :=
  (interval_append test2688 0 64 128
  (interval_append test2688 0 32 64
  (interval_append test2688 0 16 32
  test2688_block_0
  test2688_block_1)
  (interval_append test2688 32 48 64
  test2688_block_2
  test2688_block_3))
  (interval_append test2688 64 96 128
  (interval_append test2688 64 80 96
  test2688_block_4
  test2688_block_5)
  (interval_append test2688 96 112 128
  test2688_block_6
  test2688_block_7)))
theorem routeInterval2688 : Interval routeTest 2688 2816 := by
  intro i hlo hhi
  have h := test2688_complete (i - 2688) (Nat.zero_le _) (by omega)
  simpa only [test2688, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof022. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test2816 (i : Nat) := routeTest (i + 2816)
theorem test2816_block_0 : Interval test2816 0 16 :=
  interval_of_check test2816 0 16 (by decide +kernel)

theorem test2816_block_1 : Interval test2816 16 32 :=
  interval_of_check test2816 16 16 (by decide +kernel)

theorem test2816_block_2 : Interval test2816 32 48 :=
  interval_of_check test2816 32 16 (by decide +kernel)

theorem test2816_block_3 : Interval test2816 48 64 :=
  interval_of_check test2816 48 16 (by decide +kernel)

theorem test2816_block_4 : Interval test2816 64 80 :=
  interval_of_check test2816 64 16 (by decide +kernel)

theorem test2816_block_5 : Interval test2816 80 96 :=
  interval_of_check test2816 80 16 (by decide +kernel)

theorem test2816_block_6 : Interval test2816 96 112 :=
  interval_of_check test2816 96 16 (by decide +kernel)

theorem test2816_block_7 : Interval test2816 112 128 :=
  interval_of_check test2816 112 16 (by decide +kernel)

theorem test2816_complete : Interval test2816 0 128 :=
  (interval_append test2816 0 64 128
  (interval_append test2816 0 32 64
  (interval_append test2816 0 16 32
  test2816_block_0
  test2816_block_1)
  (interval_append test2816 32 48 64
  test2816_block_2
  test2816_block_3))
  (interval_append test2816 64 96 128
  (interval_append test2816 64 80 96
  test2816_block_4
  test2816_block_5)
  (interval_append test2816 96 112 128
  test2816_block_6
  test2816_block_7)))
theorem routeInterval2816 : Interval routeTest 2816 2944 := by
  intro i hlo hhi
  have h := test2816_complete (i - 2816) (Nat.zero_le _) (by omega)
  simpa only [test2816, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof023. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test2944 (i : Nat) := routeTest (i + 2944)
theorem test2944_block_0 : Interval test2944 0 16 :=
  interval_of_check test2944 0 16 (by decide +kernel)

theorem test2944_block_1 : Interval test2944 16 32 :=
  interval_of_check test2944 16 16 (by decide +kernel)

theorem test2944_block_2 : Interval test2944 32 48 :=
  interval_of_check test2944 32 16 (by decide +kernel)

theorem test2944_block_3 : Interval test2944 48 64 :=
  interval_of_check test2944 48 16 (by decide +kernel)

theorem test2944_block_4 : Interval test2944 64 80 :=
  interval_of_check test2944 64 16 (by decide +kernel)

theorem test2944_block_5 : Interval test2944 80 96 :=
  interval_of_check test2944 80 16 (by decide +kernel)

theorem test2944_block_6 : Interval test2944 96 112 :=
  interval_of_check test2944 96 16 (by decide +kernel)

theorem test2944_block_7 : Interval test2944 112 128 :=
  interval_of_check test2944 112 16 (by decide +kernel)

theorem test2944_complete : Interval test2944 0 128 :=
  (interval_append test2944 0 64 128
  (interval_append test2944 0 32 64
  (interval_append test2944 0 16 32
  test2944_block_0
  test2944_block_1)
  (interval_append test2944 32 48 64
  test2944_block_2
  test2944_block_3))
  (interval_append test2944 64 96 128
  (interval_append test2944 64 80 96
  test2944_block_4
  test2944_block_5)
  (interval_append test2944 96 112 128
  test2944_block_6
  test2944_block_7)))
theorem routeInterval2944 : Interval routeTest 2944 3072 := by
  intro i hlo hhi
  have h := test2944_complete (i - 2944) (Nat.zero_le _) (by omega)
  simpa only [test2944, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353
