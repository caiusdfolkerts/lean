module
prelude
public import SharedSmallRoots26Part000
public import SharedSmallRoots26Part001
public import SharedSmallRoots26Part002
public import SharedSmallRoots26Part003
public import SharedSmallRoots26Part004
public import SharedSmallRoots26Part005
public import SharedSmallRoots26Part006
public import SharedSmallRoots26Part007
public import SharedSmallRoots26Part008
public import SharedSmallRoots26Part009
public import SharedSmallRoots26Part010
public import SharedSmallRoots26Part011
public import SharedSmallRoots26Part012
public import SharedSmallRoots26Part013
public import SharedSmallRoots26Part014
public import SharedSmallRoots26Part015
public import SharedSmallRoots26Part016

@[expose] public section
namespace Papers.RationalityTen.SharedSmallRootCertificates.Row26
open Papers.RationalityTen ConcreteGrowth FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
abbrev rootCount : Nat := 4331
noncomputable def quota (j : Nat) : Nat := ([0,3,7,4,0] : List Nat).getD j 0
noncomputable def checkRecord (r : Nat × Nat) : Bool :=
  decide (r.1 < GraphCatalogue.Generated.Graph13.Level12.count) &&
  (decide (SharedSmallRootReplay.complement r.2 = (GraphCatalogue.Generated.Graph13.Level12.lookup r.1).mask) &&
  SharedSmallRootReplay.check quota 11 r.2)
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
  if h3 : i.val < 1024 then
    ⟨Part003.lookup i.val, by
      have hlo : 768 ≤ i.val := by omega
      have hhi : i.val < 1024 := h3
      have h := Part003.checked i.val hlo hhi
      have hquota : Part003.quota = quota := rfl
      simpa only [checkRecord, Part003.test, hquota] using h⟩
  else
  if h4 : i.val < 1280 then
    ⟨Part004.lookup i.val, by
      have hlo : 1024 ≤ i.val := by omega
      have hhi : i.val < 1280 := h4
      have h := Part004.checked i.val hlo hhi
      have hquota : Part004.quota = quota := rfl
      simpa only [checkRecord, Part004.test, hquota] using h⟩
  else
  if h5 : i.val < 1536 then
    ⟨Part005.lookup i.val, by
      have hlo : 1280 ≤ i.val := by omega
      have hhi : i.val < 1536 := h5
      have h := Part005.checked i.val hlo hhi
      have hquota : Part005.quota = quota := rfl
      simpa only [checkRecord, Part005.test, hquota] using h⟩
  else
  if h6 : i.val < 1792 then
    ⟨Part006.lookup i.val, by
      have hlo : 1536 ≤ i.val := by omega
      have hhi : i.val < 1792 := h6
      have h := Part006.checked i.val hlo hhi
      have hquota : Part006.quota = quota := rfl
      simpa only [checkRecord, Part006.test, hquota] using h⟩
  else
  if h7 : i.val < 2048 then
    ⟨Part007.lookup i.val, by
      have hlo : 1792 ≤ i.val := by omega
      have hhi : i.val < 2048 := h7
      have h := Part007.checked i.val hlo hhi
      have hquota : Part007.quota = quota := rfl
      simpa only [checkRecord, Part007.test, hquota] using h⟩
  else
  if h8 : i.val < 2304 then
    ⟨Part008.lookup i.val, by
      have hlo : 2048 ≤ i.val := by omega
      have hhi : i.val < 2304 := h8
      have h := Part008.checked i.val hlo hhi
      have hquota : Part008.quota = quota := rfl
      simpa only [checkRecord, Part008.test, hquota] using h⟩
  else
  if h9 : i.val < 2560 then
    ⟨Part009.lookup i.val, by
      have hlo : 2304 ≤ i.val := by omega
      have hhi : i.val < 2560 := h9
      have h := Part009.checked i.val hlo hhi
      have hquota : Part009.quota = quota := rfl
      simpa only [checkRecord, Part009.test, hquota] using h⟩
  else
  if h10 : i.val < 2816 then
    ⟨Part010.lookup i.val, by
      have hlo : 2560 ≤ i.val := by omega
      have hhi : i.val < 2816 := h10
      have h := Part010.checked i.val hlo hhi
      have hquota : Part010.quota = quota := rfl
      simpa only [checkRecord, Part010.test, hquota] using h⟩
  else
  if h11 : i.val < 3072 then
    ⟨Part011.lookup i.val, by
      have hlo : 2816 ≤ i.val := by omega
      have hhi : i.val < 3072 := h11
      have h := Part011.checked i.val hlo hhi
      have hquota : Part011.quota = quota := rfl
      simpa only [checkRecord, Part011.test, hquota] using h⟩
  else
  if h12 : i.val < 3328 then
    ⟨Part012.lookup i.val, by
      have hlo : 3072 ≤ i.val := by omega
      have hhi : i.val < 3328 := h12
      have h := Part012.checked i.val hlo hhi
      have hquota : Part012.quota = quota := rfl
      simpa only [checkRecord, Part012.test, hquota] using h⟩
  else
  if h13 : i.val < 3584 then
    ⟨Part013.lookup i.val, by
      have hlo : 3328 ≤ i.val := by omega
      have hhi : i.val < 3584 := h13
      have h := Part013.checked i.val hlo hhi
      have hquota : Part013.quota = quota := rfl
      simpa only [checkRecord, Part013.test, hquota] using h⟩
  else
  if h14 : i.val < 3840 then
    ⟨Part014.lookup i.val, by
      have hlo : 3584 ≤ i.val := by omega
      have hhi : i.val < 3840 := h14
      have h := Part014.checked i.val hlo hhi
      have hquota : Part014.quota = quota := rfl
      simpa only [checkRecord, Part014.test, hquota] using h⟩
  else
  if h15 : i.val < 4096 then
    ⟨Part015.lookup i.val, by
      have hlo : 3840 ≤ i.val := by omega
      have hhi : i.val < 4096 := h15
      have h := Part015.checked i.val hlo hhi
      have hquota : Part015.quota = quota := rfl
      simpa only [checkRecord, Part015.test, hquota] using h⟩
  else
    ⟨Part016.lookup i.val, by
      have hlo : 4096 ≤ i.val := by omega
      have hhi : i.val < 4331 := i.isLt
      have h := Part016.checked i.val hlo hhi
      have hquota : Part016.quota = quota := rfl
      simpa only [checkRecord, Part016.test, hquota] using h⟩
theorem entry_checked (i : Fin rootCount) : checkRecord (entry i).val = true := (entry i).property
end Papers.RationalityTen.SharedSmallRootCertificates.Row26
