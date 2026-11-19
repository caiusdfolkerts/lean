module
prelude
public import RootedQuotaTransfer0712Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0712
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 10 :=
  interval_of_check test0 0 10 (by decide +kernel)

theorem test0_complete : Interval test0 0 10 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 10 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0712
