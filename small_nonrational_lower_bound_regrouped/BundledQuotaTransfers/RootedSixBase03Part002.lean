module
prelude
public import BundledQuotaTransfers.RootedSixBase03Part001

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0717Proof006. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test768 (i : Nat) := routeTest (i + 768)
theorem test768_block_0 : Interval test768 0 16 :=
  interval_of_check test768 0 16 (by decide +kernel)

theorem test768_block_1 : Interval test768 16 32 :=
  interval_of_check test768 16 16 (by decide +kernel)

theorem test768_block_2 : Interval test768 32 48 :=
  interval_of_check test768 32 16 (by decide +kernel)

theorem test768_block_3 : Interval test768 48 64 :=
  interval_of_check test768 48 16 (by decide +kernel)

theorem test768_block_4 : Interval test768 64 80 :=
  interval_of_check test768 64 16 (by decide +kernel)

theorem test768_block_5 : Interval test768 80 96 :=
  interval_of_check test768 80 16 (by decide +kernel)

theorem test768_block_6 : Interval test768 96 112 :=
  interval_of_check test768 96 16 (by decide +kernel)

theorem test768_block_7 : Interval test768 112 128 :=
  interval_of_check test768 112 16 (by decide +kernel)

theorem test768_complete : Interval test768 0 128 :=
  (interval_append test768 0 64 128
  (interval_append test768 0 32 64
  (interval_append test768 0 16 32
  test768_block_0
  test768_block_1)
  (interval_append test768 32 48 64
  test768_block_2
  test768_block_3))
  (interval_append test768 64 96 128
  (interval_append test768 64 80 96
  test768_block_4
  test768_block_5)
  (interval_append test768 96 112 128
  test768_block_6
  test768_block_7)))
theorem routeInterval768 : Interval routeTest 768 896 := by
  intro i hlo hhi
  have h := test768_complete (i - 768) (Nat.zero_le _) (by omega)
  simpa only [test768, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof007. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test896 (i : Nat) := routeTest (i + 896)
theorem test896_block_0 : Interval test896 0 16 :=
  interval_of_check test896 0 16 (by decide +kernel)

theorem test896_block_1 : Interval test896 16 32 :=
  interval_of_check test896 16 16 (by decide +kernel)

theorem test896_block_2 : Interval test896 32 48 :=
  interval_of_check test896 32 16 (by decide +kernel)

theorem test896_block_3 : Interval test896 48 64 :=
  interval_of_check test896 48 16 (by decide +kernel)

theorem test896_block_4 : Interval test896 64 80 :=
  interval_of_check test896 64 16 (by decide +kernel)

theorem test896_block_5 : Interval test896 80 96 :=
  interval_of_check test896 80 16 (by decide +kernel)

theorem test896_block_6 : Interval test896 96 112 :=
  interval_of_check test896 96 16 (by decide +kernel)

theorem test896_block_7 : Interval test896 112 128 :=
  interval_of_check test896 112 16 (by decide +kernel)

theorem test896_complete : Interval test896 0 128 :=
  (interval_append test896 0 64 128
  (interval_append test896 0 32 64
  (interval_append test896 0 16 32
  test896_block_0
  test896_block_1)
  (interval_append test896 32 48 64
  test896_block_2
  test896_block_3))
  (interval_append test896 64 96 128
  (interval_append test896 64 80 96
  test896_block_4
  test896_block_5)
  (interval_append test896 96 112 128
  test896_block_6
  test896_block_7)))
theorem routeInterval896 : Interval routeTest 896 1024 := by
  intro i hlo hhi
  have h := test896_complete (i - 896) (Nat.zero_le _) (by omega)
  simpa only [test896, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof008. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1024 (i : Nat) := routeTest (i + 1024)
theorem test1024_block_0 : Interval test1024 0 16 :=
  interval_of_check test1024 0 16 (by decide +kernel)

theorem test1024_block_1 : Interval test1024 16 32 :=
  interval_of_check test1024 16 16 (by decide +kernel)

theorem test1024_block_2 : Interval test1024 32 48 :=
  interval_of_check test1024 32 16 (by decide +kernel)

theorem test1024_block_3 : Interval test1024 48 64 :=
  interval_of_check test1024 48 16 (by decide +kernel)

theorem test1024_block_4 : Interval test1024 64 80 :=
  interval_of_check test1024 64 16 (by decide +kernel)

theorem test1024_block_5 : Interval test1024 80 96 :=
  interval_of_check test1024 80 16 (by decide +kernel)

theorem test1024_block_6 : Interval test1024 96 112 :=
  interval_of_check test1024 96 16 (by decide +kernel)

theorem test1024_block_7 : Interval test1024 112 128 :=
  interval_of_check test1024 112 16 (by decide +kernel)

theorem test1024_complete : Interval test1024 0 128 :=
  (interval_append test1024 0 64 128
  (interval_append test1024 0 32 64
  (interval_append test1024 0 16 32
  test1024_block_0
  test1024_block_1)
  (interval_append test1024 32 48 64
  test1024_block_2
  test1024_block_3))
  (interval_append test1024 64 96 128
  (interval_append test1024 64 80 96
  test1024_block_4
  test1024_block_5)
  (interval_append test1024 96 112 128
  test1024_block_6
  test1024_block_7)))
theorem routeInterval1024 : Interval routeTest 1024 1152 := by
  intro i hlo hhi
  have h := test1024_complete (i - 1024) (Nat.zero_le _) (by omega)
  simpa only [test1024, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof009. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1152 (i : Nat) := routeTest (i + 1152)
theorem test1152_block_0 : Interval test1152 0 16 :=
  interval_of_check test1152 0 16 (by decide +kernel)

theorem test1152_block_1 : Interval test1152 16 32 :=
  interval_of_check test1152 16 16 (by decide +kernel)

theorem test1152_block_2 : Interval test1152 32 48 :=
  interval_of_check test1152 32 16 (by decide +kernel)

theorem test1152_block_3 : Interval test1152 48 64 :=
  interval_of_check test1152 48 16 (by decide +kernel)

theorem test1152_block_4 : Interval test1152 64 80 :=
  interval_of_check test1152 64 16 (by decide +kernel)

theorem test1152_block_5 : Interval test1152 80 96 :=
  interval_of_check test1152 80 16 (by decide +kernel)

theorem test1152_block_6 : Interval test1152 96 112 :=
  interval_of_check test1152 96 16 (by decide +kernel)

theorem test1152_block_7 : Interval test1152 112 128 :=
  interval_of_check test1152 112 16 (by decide +kernel)

theorem test1152_complete : Interval test1152 0 128 :=
  (interval_append test1152 0 64 128
  (interval_append test1152 0 32 64
  (interval_append test1152 0 16 32
  test1152_block_0
  test1152_block_1)
  (interval_append test1152 32 48 64
  test1152_block_2
  test1152_block_3))
  (interval_append test1152 64 96 128
  (interval_append test1152 64 80 96
  test1152_block_4
  test1152_block_5)
  (interval_append test1152 96 112 128
  test1152_block_6
  test1152_block_7)))
theorem routeInterval1152 : Interval routeTest 1152 1280 := by
  intro i hlo hhi
  have h := test1152_complete (i - 1152) (Nat.zero_le _) (by omega)
  simpa only [test1152, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof010. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof011. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof012. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof013. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0717
