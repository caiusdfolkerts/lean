module
prelude
public import CachedGraphTriangles
public import Graph13Level10
public import Graph13Level11
public import Graph13Level12
public import Graph13Level13

@[expose] public section
noncomputable section
namespace Papers.RationalityTen.TriangleCountCertificate

structure Record where
  level : Nat
  graphIndex : Nat
  complement : Nat
  triangles : Nat

def catalogueSize (level : Nat) : Nat :=
  if level = 10 then GraphCatalogue.Generated.Graph13.Level10.count
  else if level = 11 then GraphCatalogue.Generated.Graph13.Level11.count
  else if level = 12 then GraphCatalogue.Generated.Graph13.Level12.count
  else GraphCatalogue.Generated.Graph13.Level13.count

def catalogueMask (level index : Nat) : Nat :=
  if level = 10 then (GraphCatalogue.Generated.Graph13.Level10.lookup index).mask
  else if level = 11 then (GraphCatalogue.Generated.Graph13.Level11.lookup index).mask
  else if level = 12 then (GraphCatalogue.Generated.Graph13.Level12.lookup index).mask
  else (GraphCatalogue.Generated.Graph13.Level13.lookup index).mask

def check (record : Record) : Bool :=
  decide (10 ≤ record.level ∧ record.level ≤ 13) &&
  (decide (record.graphIndex < catalogueSize record.level) &&
  (decide (record.complement = catalogueMask record.level record.graphIndex) &&
   decide (CachedGraphTriangles.count record.complement = record.triangles)))

structure Valid (record : Record) : Prop where
  level : 10 ≤ record.level ∧ record.level ≤ 13
  index : record.graphIndex < catalogueSize record.level
  mask : record.complement = catalogueMask record.level record.graphIndex
  count : TenGraphTriangles.count record.complement = record.triangles

theorem valid_of_check (record : Record) (h : check record = true) : Valid record := by
  simp only [check, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  obtain ⟨hl, hi, hm, hc⟩ := h
  exact ⟨hl, hi, hm, (CachedGraphTriangles.count_eq record.complement).symm.trans hc⟩

#print axioms valid_of_check
end Papers.RationalityTen.TriangleCountCertificate
