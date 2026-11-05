module
prelude
public import SharedSmallRoots28Part000
public import SharedSmallRoots28Part001
public import SharedSmallRoots28Part002
public import SharedSmallRoots28Part003

@[expose] public section
namespace Papers.RationalityTen.SharedSmallRootCertificates.Row28
open Papers.RationalityTen ConcreteGrowth FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
abbrev rootCount : Nat := 877
noncomputable def quota (j : Nat) : Nat := ([0,5,10,0,0] : List Nat).getD j 0
noncomputable def checkRecord (r : Nat × Nat) : Bool :=
  decide (r.1 < GraphCatalogue.Generated.Graph13.Level10.count) &&
  (decide (SharedSmallRootReplay.complement r.2 = (GraphCatalogue.Generated.Graph13.Level10.lookup r.1).mask) &&
  SharedSmallRootReplay.check quota 10 r.2)
noncomputable def entry (i : Fin rootCount) : {r : Nat × Nat // checkRecord r = true} :=
  if h0 : i.val < 256 then
    ⟨Part000.lookup i.val, by
      have hlo : 0 ≤ i.val := by omega
      have hhi : i.val < 256 := h0
      have h := Part000.checked i.val hlo hhi
      have hquota : Part000.quota = quota := rfl
      simpa only [checkRecord, Part000.test, hquota] using h⟩
  else
  if h1 : i.val < 512 then
    ⟨Part001.lookup i.val, by
      have hlo : 256 ≤ i.val := by omega
      have hhi : i.val < 512 := h1
      have h := Part001.checked i.val hlo hhi
      have hquota : Part001.quota = quota := rfl
      simpa only [checkRecord, Part001.test, hquota] using h⟩
  else
  if h2 : i.val < 768 then
    ⟨Part002.lookup i.val, by
      have hlo : 512 ≤ i.val := by omega
      have hhi : i.val < 768 := h2
      have h := Part002.checked i.val hlo hhi
      have hquota : Part002.quota = quota := rfl
      simpa only [checkRecord, Part002.test, hquota] using h⟩
  else
    ⟨Part003.lookup i.val, by
      have hlo : 768 ≤ i.val := by omega
      have hhi : i.val < 877 := i.isLt
      have h := Part003.checked i.val hlo hhi
      have hquota : Part003.quota = quota := rfl
      simpa only [checkRecord, Part003.test, hquota] using h⟩
theorem entry_checked (i : Fin rootCount) : checkRecord (entry i).val = true := (entry i).property
end Papers.RationalityTen.SharedSmallRootCertificates.Row28
