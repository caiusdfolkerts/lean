module
prelude
public meta import Init.TacticsExtra
public import GraphRouteRow16Verified
public import GraphRouteRow19Verified
public import GraphRouteRow23Verified
public import GraphRouteRow24Verified
public import GraphRouteRow25Verified
public import GraphRouteRow26Verified
public import GraphRouteRow27Verified
public import GraphRouteRow28Verified
public import GraphRouteRow29Verified
public import GraphRouteRow30Verified
public import GraphRouteRow31Verified
public import GraphRouteRow32Verified
public import GraphEmptyRow16Verified
public import GraphEmptyRow19Verified
public import GraphEmptyRow23Verified
public import GraphEmptyRow24Verified
public import GraphEmptyRow25Verified
public import GraphEmptyRow26Verified
public import GraphEmptyRow27Verified
public import GraphEmptyRow28Verified
public import GraphEmptyRow29Verified
public import GraphEmptyRow30Verified
public import GraphEmptyRow31Verified

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedEmptyKeys
theorem resolved (Result : GraphRouteSelector.Key → Prop)
    (h16 : ∀ i : Fin SharedSmallRootCertificates.Row16.rootCount,
      Result (16, SharedSmallRootReplay.complement (Row16.rootCode i)))
    (h19 : ∀ i : Fin SharedSmallRootCertificates.Row19.rootCount,
      Result (19, SharedSmallRootReplay.complement (Row19.rootCode i)))
    (h23 : ∀ i : Fin SharedSmallRootCertificates.Row23.rootCount,
      Result (23, SharedSmallRootReplay.complement (Row23.rootCode i)))
    (h24 : ∀ i : Fin SharedSmallRootCertificates.Row24.rootCount,
      Result (24, SharedSmallRootReplay.complement (Row24.rootCode i)))
    (h25 : ∀ i : Fin SharedSmallRootCertificates.Row25.rootCount,
      Result (25, SharedSmallRootReplay.complement (Row25.rootCode i)))
    (h26 : ∀ i : Fin SharedSmallRootCertificates.Row26.rootCount,
      Result (26, SharedSmallRootReplay.complement (Row26.rootCode i)))
    (h27 : ∀ i : Fin SharedSmallRootCertificates.Row27.rootCount,
      Result (27, SharedSmallRootReplay.complement (Row27.rootCode i)))
    (h28 : ∀ i : Fin SharedSmallRootCertificates.Row28.rootCount,
      Result (28, SharedSmallRootReplay.complement (Row28.rootCode i)))
    (h29 : ∀ i : Fin SharedSmallRootCertificates.Row29.rootCount,
      Result (29, SharedSmallRootReplay.complement (Row29.rootCode i)))
    (h30 : ∀ i : Fin SharedSmallRootCertificates.Row30.rootCount,
      Result (30, SharedSmallRootReplay.complement (Row30.rootCode i)))
    (h31 : ∀ i : Fin SharedSmallRootCertificates.Row31.rootCount,
      Result (31, SharedSmallRootReplay.complement (Row31.rootCode i)))
    (i : Nat) (hi : i < GraphRoutes.emptyRootKeys.count) :
    Result (GraphRoutes.emptyRootKeys.entry i) := by
  change i < 28587 at hi
  if hbound16 : i < 1263 then
    let j : Fin SharedSmallRootCertificates.Row16.rootCount := ⟨i - 0, by dsimp only [SharedSmallRootCertificates.Row16.rootCount]; omega⟩
    have hj : 0 + j.val = i := by dsimp [j]; omega
    have h := Row16.resolved Result h16 j
    change Result (GraphRoutes.emptyRootKeys.entry (0 + j.val)) at h
    simpa only [hj] using h
  else if hbound19 : i < 6694 then
    let j : Fin SharedSmallRootCertificates.Row19.rootCount := ⟨i - 1263, by dsimp only [SharedSmallRootCertificates.Row19.rootCount]; omega⟩
    have hj : 1263 + j.val = i := by dsimp [j]; omega
    have h := Row19.resolved Result h19 j
    change Result (GraphRoutes.emptyRootKeys.entry (1263 + j.val)) at h
    simpa only [hj] using h
  else if hbound23 : i < 8209 then
    let j : Fin SharedSmallRootCertificates.Row23.rootCount := ⟨i - 6694, by dsimp only [SharedSmallRootCertificates.Row23.rootCount]; omega⟩
    have hj : 6694 + j.val = i := by dsimp [j]; omega
    have h := Row23.resolved Result h23 j
    change Result (GraphRoutes.emptyRootKeys.entry (6694 + j.val)) at h
    simpa only [hj] using h
  else if hbound24 : i < 10105 then
    let j : Fin SharedSmallRootCertificates.Row24.rootCount := ⟨i - 8209, by dsimp only [SharedSmallRootCertificates.Row24.rootCount]; omega⟩
    have hj : 8209 + j.val = i := by dsimp [j]; omega
    have h := Row24.resolved Result h24 j
    change Result (GraphRoutes.emptyRootKeys.entry (8209 + j.val)) at h
    simpa only [hj] using h
  else if hbound25 : i < 12471 then
    let j : Fin SharedSmallRootCertificates.Row25.rootCount := ⟨i - 10105, by dsimp only [SharedSmallRootCertificates.Row25.rootCount]; omega⟩
    have hj : 10105 + j.val = i := by dsimp [j]; omega
    have h := Row25.resolved Result h25 j
    change Result (GraphRoutes.emptyRootKeys.entry (10105 + j.val)) at h
    simpa only [hj] using h
  else if hbound26 : i < 16802 then
    let j : Fin SharedSmallRootCertificates.Row26.rootCount := ⟨i - 12471, by dsimp only [SharedSmallRootCertificates.Row26.rootCount]; omega⟩
    have hj : 12471 + j.val = i := by dsimp [j]; omega
    have h := Row26.resolved Result h26 j
    change Result (GraphRoutes.emptyRootKeys.entry (12471 + j.val)) at h
    simpa only [hj] using h
  else if hbound27 : i < 23485 then
    let j : Fin SharedSmallRootCertificates.Row27.rootCount := ⟨i - 16802, by dsimp only [SharedSmallRootCertificates.Row27.rootCount]; omega⟩
    have hj : 16802 + j.val = i := by dsimp [j]; omega
    have h := Row27.resolved Result h27 j
    change Result (GraphRoutes.emptyRootKeys.entry (16802 + j.val)) at h
    simpa only [hj] using h
  else if hbound28 : i < 24362 then
    let j : Fin SharedSmallRootCertificates.Row28.rootCount := ⟨i - 23485, by dsimp only [SharedSmallRootCertificates.Row28.rootCount]; omega⟩
    have hj : 23485 + j.val = i := by dsimp [j]; omega
    have h := Row28.resolved Result h28 j
    change Result (GraphRoutes.emptyRootKeys.entry (23485 + j.val)) at h
    simpa only [hj] using h
  else if hbound29 : i < 25499 then
    let j : Fin SharedSmallRootCertificates.Row29.rootCount := ⟨i - 24362, by dsimp only [SharedSmallRootCertificates.Row29.rootCount]; omega⟩
    have hj : 24362 + j.val = i := by dsimp [j]; omega
    have h := Row29.resolved Result h29 j
    change Result (GraphRoutes.emptyRootKeys.entry (24362 + j.val)) at h
    simpa only [hj] using h
  else if hbound30 : i < 27927 then
    let j : Fin SharedSmallRootCertificates.Row30.rootCount := ⟨i - 25499, by dsimp only [SharedSmallRootCertificates.Row30.rootCount]; omega⟩
    have hj : 25499 + j.val = i := by dsimp [j]; omega
    have h := Row30.resolved Result h30 j
    change Result (GraphRoutes.emptyRootKeys.entry (25499 + j.val)) at h
    simpa only [hj] using h
  else
    let j : Fin SharedSmallRootCertificates.Row31.rootCount := ⟨i - 27927, by dsimp only [SharedSmallRootCertificates.Row31.rootCount]; omega⟩
    have hj : 27927 + j.val = i := by dsimp [j]; omega
    have h := Row31.resolved Result h31 j
    change Result (GraphRoutes.emptyRootKeys.entry (27927 + j.val)) at h
    simpa only [hj] using h

#print axioms resolved
end Papers.RationalityTen.SharedEmptyKeys
