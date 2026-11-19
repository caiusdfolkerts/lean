module
prelude
public import BundledQuotaTransfers.RootedSixBase02Part002

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0364Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 64 :=
  interval_of_check test0 48 16 (by decide +kernel)

theorem test0_block_4 : Interval test0 64 80 :=
  interval_of_check test0 64 16 (by decide +kernel)

theorem test0_block_5 : Interval test0 80 96 :=
  interval_of_check test0 80 16 (by decide +kernel)

theorem test0_block_6 : Interval test0 96 112 :=
  interval_of_check test0 96 16 (by decide +kernel)

theorem test0_block_7 : Interval test0 112 128 :=
  interval_of_check test0 112 16 (by decide +kernel)

theorem test0_complete : Interval test0 0 128 :=
  (interval_append test0 0 64 128
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 128
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 128
  test0_block_6
  test0_block_7)))
theorem routeInterval0 : Interval routeTest 0 128 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0364

/- Original module: RootedQuotaTransfer0364Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 32 :=
  interval_of_check test128 16 16 (by decide +kernel)

theorem test128_block_2 : Interval test128 32 48 :=
  interval_of_check test128 32 16 (by decide +kernel)

theorem test128_block_3 : Interval test128 48 64 :=
  interval_of_check test128 48 16 (by decide +kernel)

theorem test128_block_4 : Interval test128 64 80 :=
  interval_of_check test128 64 16 (by decide +kernel)

theorem test128_block_5 : Interval test128 80 96 :=
  interval_of_check test128 80 16 (by decide +kernel)

theorem test128_block_6 : Interval test128 96 112 :=
  interval_of_check test128 96 16 (by decide +kernel)

theorem test128_block_7 : Interval test128 112 128 :=
  interval_of_check test128 112 16 (by decide +kernel)

theorem test128_complete : Interval test128 0 128 :=
  (interval_append test128 0 64 128
  (interval_append test128 0 32 64
  (interval_append test128 0 16 32
  test128_block_0
  test128_block_1)
  (interval_append test128 32 48 64
  test128_block_2
  test128_block_3))
  (interval_append test128 64 96 128
  (interval_append test128 64 80 96
  test128_block_4
  test128_block_5)
  (interval_append test128 96 112 128
  test128_block_6
  test128_block_7)))
theorem routeInterval128 : Interval routeTest 128 256 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0364

/- Original module: RootedQuotaTransfer0364Proof002. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test256 (i : Nat) := routeTest (i + 256)
theorem test256_block_0 : Interval test256 0 16 :=
  interval_of_check test256 0 16 (by decide +kernel)

theorem test256_block_1 : Interval test256 16 32 :=
  interval_of_check test256 16 16 (by decide +kernel)

theorem test256_block_2 : Interval test256 32 48 :=
  interval_of_check test256 32 16 (by decide +kernel)

theorem test256_block_3 : Interval test256 48 64 :=
  interval_of_check test256 48 16 (by decide +kernel)

theorem test256_block_4 : Interval test256 64 80 :=
  interval_of_check test256 64 16 (by decide +kernel)

theorem test256_block_5 : Interval test256 80 96 :=
  interval_of_check test256 80 16 (by decide +kernel)

theorem test256_block_6 : Interval test256 96 112 :=
  interval_of_check test256 96 16 (by decide +kernel)

theorem test256_block_7 : Interval test256 112 128 :=
  interval_of_check test256 112 16 (by decide +kernel)

theorem test256_complete : Interval test256 0 128 :=
  (interval_append test256 0 64 128
  (interval_append test256 0 32 64
  (interval_append test256 0 16 32
  test256_block_0
  test256_block_1)
  (interval_append test256 32 48 64
  test256_block_2
  test256_block_3))
  (interval_append test256 64 96 128
  (interval_append test256 64 80 96
  test256_block_4
  test256_block_5)
  (interval_append test256 96 112 128
  test256_block_6
  test256_block_7)))
theorem routeInterval256 : Interval routeTest 256 384 := by
  intro i hlo hhi
  have h := test256_complete (i - 256) (Nat.zero_le _) (by omega)
  simpa only [test256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0364

/- Original module: RootedQuotaTransfer0364Proof003. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test384 (i : Nat) := routeTest (i + 384)
theorem test384_block_0 : Interval test384 0 16 :=
  interval_of_check test384 0 16 (by decide +kernel)

theorem test384_block_1 : Interval test384 16 32 :=
  interval_of_check test384 16 16 (by decide +kernel)

theorem test384_block_2 : Interval test384 32 48 :=
  interval_of_check test384 32 16 (by decide +kernel)

theorem test384_block_3 : Interval test384 48 64 :=
  interval_of_check test384 48 16 (by decide +kernel)

theorem test384_block_4 : Interval test384 64 80 :=
  interval_of_check test384 64 16 (by decide +kernel)

theorem test384_block_5 : Interval test384 80 96 :=
  interval_of_check test384 80 16 (by decide +kernel)

theorem test384_block_6 : Interval test384 96 112 :=
  interval_of_check test384 96 16 (by decide +kernel)

theorem test384_block_7 : Interval test384 112 128 :=
  interval_of_check test384 112 16 (by decide +kernel)

theorem test384_complete : Interval test384 0 128 :=
  (interval_append test384 0 64 128
  (interval_append test384 0 32 64
  (interval_append test384 0 16 32
  test384_block_0
  test384_block_1)
  (interval_append test384 32 48 64
  test384_block_2
  test384_block_3))
  (interval_append test384 64 96 128
  (interval_append test384 64 80 96
  test384_block_4
  test384_block_5)
  (interval_append test384 96 112 128
  test384_block_6
  test384_block_7)))
theorem routeInterval384 : Interval routeTest 384 512 := by
  intro i hlo hhi
  have h := test384_complete (i - 384) (Nat.zero_le _) (by omega)
  simpa only [test384, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0364

/- Original module: RootedQuotaTransfer0364Proof004. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test512 (i : Nat) := routeTest (i + 512)
theorem test512_block_0 : Interval test512 0 16 :=
  interval_of_check test512 0 16 (by decide +kernel)

theorem test512_block_1 : Interval test512 16 32 :=
  interval_of_check test512 16 16 (by decide +kernel)

theorem test512_block_2 : Interval test512 32 48 :=
  interval_of_check test512 32 16 (by decide +kernel)

theorem test512_block_3 : Interval test512 48 64 :=
  interval_of_check test512 48 16 (by decide +kernel)

theorem test512_block_4 : Interval test512 64 80 :=
  interval_of_check test512 64 16 (by decide +kernel)

theorem test512_block_5 : Interval test512 80 96 :=
  interval_of_check test512 80 16 (by decide +kernel)

theorem test512_block_6 : Interval test512 96 112 :=
  interval_of_check test512 96 16 (by decide +kernel)

theorem test512_block_7 : Interval test512 112 128 :=
  interval_of_check test512 112 16 (by decide +kernel)

theorem test512_complete : Interval test512 0 128 :=
  (interval_append test512 0 64 128
  (interval_append test512 0 32 64
  (interval_append test512 0 16 32
  test512_block_0
  test512_block_1)
  (interval_append test512 32 48 64
  test512_block_2
  test512_block_3))
  (interval_append test512 64 96 128
  (interval_append test512 64 80 96
  test512_block_4
  test512_block_5)
  (interval_append test512 96 112 128
  test512_block_6
  test512_block_7)))
theorem routeInterval512 : Interval routeTest 512 640 := by
  intro i hlo hhi
  have h := test512_complete (i - 512) (Nat.zero_le _) (by omega)
  simpa only [test512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0364

/- Original module: RootedQuotaTransfer0364Proof005. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test640 (i : Nat) := routeTest (i + 640)
theorem test640_block_0 : Interval test640 0 16 :=
  interval_of_check test640 0 16 (by decide +kernel)

theorem test640_block_1 : Interval test640 16 32 :=
  interval_of_check test640 16 16 (by decide +kernel)

theorem test640_block_2 : Interval test640 32 48 :=
  interval_of_check test640 32 16 (by decide +kernel)

theorem test640_block_3 : Interval test640 48 64 :=
  interval_of_check test640 48 16 (by decide +kernel)

theorem test640_block_4 : Interval test640 64 80 :=
  interval_of_check test640 64 16 (by decide +kernel)

theorem test640_block_5 : Interval test640 80 96 :=
  interval_of_check test640 80 16 (by decide +kernel)

theorem test640_block_6 : Interval test640 96 112 :=
  interval_of_check test640 96 16 (by decide +kernel)

theorem test640_block_7 : Interval test640 112 128 :=
  interval_of_check test640 112 16 (by decide +kernel)

theorem test640_complete : Interval test640 0 128 :=
  (interval_append test640 0 64 128
  (interval_append test640 0 32 64
  (interval_append test640 0 16 32
  test640_block_0
  test640_block_1)
  (interval_append test640 32 48 64
  test640_block_2
  test640_block_3))
  (interval_append test640 64 96 128
  (interval_append test640 64 80 96
  test640_block_4
  test640_block_5)
  (interval_append test640 96 112 128
  test640_block_6
  test640_block_7)))
theorem routeInterval640 : Interval routeTest 640 768 := by
  intro i hlo hhi
  have h := test640_complete (i - 640) (Nat.zero_le _) (by omega)
  simpa only [test640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0364

/- Original module: RootedQuotaTransfer0364Proof006. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0364

/- Original module: RootedQuotaTransfer0364Proof007. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0364
