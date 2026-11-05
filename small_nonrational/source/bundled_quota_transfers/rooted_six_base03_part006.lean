module
prelude
public import BundledQuotaTransfers.RootedSixBase03Part004

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0722Proof010. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1280 (i : Nat) := routeTest (i + 1280)
theorem test1280_block_0 : Interval test1280 0 16 :=
  interval_of_check test1280 0 16 (by decide +kernel)

theorem test1280_block_1 : Interval test1280 16 32 :=
  interval_of_check test1280 16 16 (by decide +kernel)

theorem test1280_block_2 : Interval test1280 32 48 :=
  interval_of_check test1280 32 16 (by decide +kernel)

theorem test1280_block_3 : Interval test1280 48 64 :=
  interval_of_check test1280 48 16 (by decide +kernel)

theorem test1280_block_4 : Interval test1280 64 80 :=
  interval_of_check test1280 64 16 (by decide +kernel)

theorem test1280_block_5 : Interval test1280 80 96 :=
  interval_of_check test1280 80 16 (by decide +kernel)

theorem test1280_block_6 : Interval test1280 96 112 :=
  interval_of_check test1280 96 16 (by decide +kernel)

theorem test1280_block_7 : Interval test1280 112 128 :=
  interval_of_check test1280 112 16 (by decide +kernel)

theorem test1280_complete : Interval test1280 0 128 :=
  (interval_append test1280 0 64 128
  (interval_append test1280 0 32 64
  (interval_append test1280 0 16 32
  test1280_block_0
  test1280_block_1)
  (interval_append test1280 32 48 64
  test1280_block_2
  test1280_block_3))
  (interval_append test1280 64 96 128
  (interval_append test1280 64 80 96
  test1280_block_4
  test1280_block_5)
  (interval_append test1280 96 112 128
  test1280_block_6
  test1280_block_7)))
theorem routeInterval1280 : Interval routeTest 1280 1408 := by
  intro i hlo hhi
  have h := test1280_complete (i - 1280) (Nat.zero_le _) (by omega)
  simpa only [test1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0722

/- Original module: RootedQuotaTransfer0722Proof011. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1408 (i : Nat) := routeTest (i + 1408)
theorem test1408_block_0 : Interval test1408 0 16 :=
  interval_of_check test1408 0 16 (by decide +kernel)

theorem test1408_block_1 : Interval test1408 16 32 :=
  interval_of_check test1408 16 16 (by decide +kernel)

theorem test1408_block_2 : Interval test1408 32 48 :=
  interval_of_check test1408 32 16 (by decide +kernel)

theorem test1408_block_3 : Interval test1408 48 64 :=
  interval_of_check test1408 48 16 (by decide +kernel)

theorem test1408_block_4 : Interval test1408 64 80 :=
  interval_of_check test1408 64 16 (by decide +kernel)

theorem test1408_block_5 : Interval test1408 80 96 :=
  interval_of_check test1408 80 16 (by decide +kernel)

theorem test1408_block_6 : Interval test1408 96 112 :=
  interval_of_check test1408 96 16 (by decide +kernel)

theorem test1408_block_7 : Interval test1408 112 128 :=
  interval_of_check test1408 112 16 (by decide +kernel)

theorem test1408_complete : Interval test1408 0 128 :=
  (interval_append test1408 0 64 128
  (interval_append test1408 0 32 64
  (interval_append test1408 0 16 32
  test1408_block_0
  test1408_block_1)
  (interval_append test1408 32 48 64
  test1408_block_2
  test1408_block_3))
  (interval_append test1408 64 96 128
  (interval_append test1408 64 80 96
  test1408_block_4
  test1408_block_5)
  (interval_append test1408 96 112 128
  test1408_block_6
  test1408_block_7)))
theorem routeInterval1408 : Interval routeTest 1408 1536 := by
  intro i hlo hhi
  have h := test1408_complete (i - 1408) (Nat.zero_le _) (by omega)
  simpa only [test1408, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0722

/- Original module: RootedQuotaTransfer0722Proof012. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1536 (i : Nat) := routeTest (i + 1536)
theorem test1536_block_0 : Interval test1536 0 16 :=
  interval_of_check test1536 0 16 (by decide +kernel)

theorem test1536_block_1 : Interval test1536 16 32 :=
  interval_of_check test1536 16 16 (by decide +kernel)

theorem test1536_block_2 : Interval test1536 32 48 :=
  interval_of_check test1536 32 16 (by decide +kernel)

theorem test1536_block_3 : Interval test1536 48 64 :=
  interval_of_check test1536 48 16 (by decide +kernel)

theorem test1536_block_4 : Interval test1536 64 80 :=
  interval_of_check test1536 64 16 (by decide +kernel)

theorem test1536_block_5 : Interval test1536 80 96 :=
  interval_of_check test1536 80 16 (by decide +kernel)

theorem test1536_block_6 : Interval test1536 96 112 :=
  interval_of_check test1536 96 16 (by decide +kernel)

theorem test1536_block_7 : Interval test1536 112 128 :=
  interval_of_check test1536 112 16 (by decide +kernel)

theorem test1536_complete : Interval test1536 0 128 :=
  (interval_append test1536 0 64 128
  (interval_append test1536 0 32 64
  (interval_append test1536 0 16 32
  test1536_block_0
  test1536_block_1)
  (interval_append test1536 32 48 64
  test1536_block_2
  test1536_block_3))
  (interval_append test1536 64 96 128
  (interval_append test1536 64 80 96
  test1536_block_4
  test1536_block_5)
  (interval_append test1536 96 112 128
  test1536_block_6
  test1536_block_7)))
theorem routeInterval1536 : Interval routeTest 1536 1664 := by
  intro i hlo hhi
  have h := test1536_complete (i - 1536) (Nat.zero_le _) (by omega)
  simpa only [test1536, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0722

/- Original module: RootedQuotaTransfer0722Proof013. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1664 (i : Nat) := routeTest (i + 1664)
theorem test1664_block_0 : Interval test1664 0 16 :=
  interval_of_check test1664 0 16 (by decide +kernel)

theorem test1664_block_1 : Interval test1664 16 32 :=
  interval_of_check test1664 16 16 (by decide +kernel)

theorem test1664_block_2 : Interval test1664 32 48 :=
  interval_of_check test1664 32 16 (by decide +kernel)

theorem test1664_block_3 : Interval test1664 48 64 :=
  interval_of_check test1664 48 16 (by decide +kernel)

theorem test1664_block_4 : Interval test1664 64 80 :=
  interval_of_check test1664 64 16 (by decide +kernel)

theorem test1664_block_5 : Interval test1664 80 96 :=
  interval_of_check test1664 80 16 (by decide +kernel)

theorem test1664_block_6 : Interval test1664 96 112 :=
  interval_of_check test1664 96 16 (by decide +kernel)

theorem test1664_block_7 : Interval test1664 112 128 :=
  interval_of_check test1664 112 16 (by decide +kernel)

theorem test1664_complete : Interval test1664 0 128 :=
  (interval_append test1664 0 64 128
  (interval_append test1664 0 32 64
  (interval_append test1664 0 16 32
  test1664_block_0
  test1664_block_1)
  (interval_append test1664 32 48 64
  test1664_block_2
  test1664_block_3))
  (interval_append test1664 64 96 128
  (interval_append test1664 64 80 96
  test1664_block_4
  test1664_block_5)
  (interval_append test1664 96 112 128
  test1664_block_6
  test1664_block_7)))
theorem routeInterval1664 : Interval routeTest 1664 1792 := by
  intro i hlo hhi
  have h := test1664_complete (i - 1664) (Nat.zero_le _) (by omega)
  simpa only [test1664, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0722

/- Original module: RootedQuotaTransfer0722Proof014. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1792 (i : Nat) := routeTest (i + 1792)
theorem test1792_block_0 : Interval test1792 0 16 :=
  interval_of_check test1792 0 16 (by decide +kernel)

theorem test1792_block_1 : Interval test1792 16 32 :=
  interval_of_check test1792 16 16 (by decide +kernel)

theorem test1792_block_2 : Interval test1792 32 48 :=
  interval_of_check test1792 32 16 (by decide +kernel)

theorem test1792_block_3 : Interval test1792 48 64 :=
  interval_of_check test1792 48 16 (by decide +kernel)

theorem test1792_block_4 : Interval test1792 64 80 :=
  interval_of_check test1792 64 16 (by decide +kernel)

theorem test1792_block_5 : Interval test1792 80 96 :=
  interval_of_check test1792 80 16 (by decide +kernel)

theorem test1792_block_6 : Interval test1792 96 112 :=
  interval_of_check test1792 96 16 (by decide +kernel)

theorem test1792_block_7 : Interval test1792 112 128 :=
  interval_of_check test1792 112 16 (by decide +kernel)

theorem test1792_complete : Interval test1792 0 128 :=
  (interval_append test1792 0 64 128
  (interval_append test1792 0 32 64
  (interval_append test1792 0 16 32
  test1792_block_0
  test1792_block_1)
  (interval_append test1792 32 48 64
  test1792_block_2
  test1792_block_3))
  (interval_append test1792 64 96 128
  (interval_append test1792 64 80 96
  test1792_block_4
  test1792_block_5)
  (interval_append test1792 96 112 128
  test1792_block_6
  test1792_block_7)))
theorem routeInterval1792 : Interval routeTest 1792 1920 := by
  intro i hlo hhi
  have h := test1792_complete (i - 1792) (Nat.zero_le _) (by omega)
  simpa only [test1792, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0722

/- Original module: RootedQuotaTransfer0722Proof015. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1920 (i : Nat) := routeTest (i + 1920)
theorem test1920_block_0 : Interval test1920 0 16 :=
  interval_of_check test1920 0 16 (by decide +kernel)

theorem test1920_block_1 : Interval test1920 16 32 :=
  interval_of_check test1920 16 16 (by decide +kernel)

theorem test1920_block_2 : Interval test1920 32 48 :=
  interval_of_check test1920 32 16 (by decide +kernel)

theorem test1920_block_3 : Interval test1920 48 64 :=
  interval_of_check test1920 48 16 (by decide +kernel)

theorem test1920_block_4 : Interval test1920 64 80 :=
  interval_of_check test1920 64 16 (by decide +kernel)

theorem test1920_block_5 : Interval test1920 80 96 :=
  interval_of_check test1920 80 16 (by decide +kernel)

theorem test1920_block_6 : Interval test1920 96 112 :=
  interval_of_check test1920 96 16 (by decide +kernel)

theorem test1920_block_7 : Interval test1920 112 128 :=
  interval_of_check test1920 112 16 (by decide +kernel)

theorem test1920_complete : Interval test1920 0 128 :=
  (interval_append test1920 0 64 128
  (interval_append test1920 0 32 64
  (interval_append test1920 0 16 32
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 32 48 64
  test1920_block_2
  test1920_block_3))
  (interval_append test1920 64 96 128
  (interval_append test1920 64 80 96
  test1920_block_4
  test1920_block_5)
  (interval_append test1920 96 112 128
  test1920_block_6
  test1920_block_7)))
theorem routeInterval1920 : Interval routeTest 1920 2048 := by
  intro i hlo hhi
  have h := test1920_complete (i - 1920) (Nat.zero_le _) (by omega)
  simpa only [test1920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0722

/- Original module: RootedQuotaTransfer0722Proof016. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0722

/- Original module: RootedQuotaTransfer0722Proof017. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0722
