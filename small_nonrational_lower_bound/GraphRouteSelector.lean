module
prelude
public import TriangleCountCertificate
public import FiniteChecks

@[expose] public section

/-!
# Complete dispatch of the finite graph catalogue

Each catalogue graph must be matched to an exact verified triangle exclusion,
empty-root certificate, compact growth certificate, or large growth certificate.
A successful selector cannot omit a graph or change its row parameters.
-/
namespace Papers.RationalityTen.GraphRouteSelector

noncomputable section

abbrev Key := Nat × Nat

structure Row where
  code : Nat
  level : Nat
  quota : List Nat
  internalMissingCount : Nat

def Row.facetCount (row : Row) : Nat :=
  row.quota.getD 0 0 + row.quota.getD 1 0 + row.quota.getD 2 0 +
    row.quota.getD 3 0 + row.quota.getD 4 0

def Row.minimum (row : Row) : Nat :=
  2 * row.facetCount + 2 * row.quota.getD 2 0 + 2 * row.quota.getD 4 0

def Row.graphCount (row : Row) : Nat := TriangleCountCertificate.catalogueSize row.level

def Row.key (row : Row) (index : Nat) : Key :=
  (row.code, TriangleCountCertificate.catalogueMask row.level index)

structure TriangleTable where
  count : Nat
  entry : Nat → TriangleCountCertificate.Record

structure KeyTable where
  count : Nat
  entry : Nat → Key

structure Route where
  tag : Nat
  index : Nat

structure Cases where
  emptyRoot : KeyTable
  compact : KeyTable
  large : KeyTable

structure Resolved (Result : Key → Prop) (cases : Cases) : Prop where
  emptyRoot : ∀ i, i < cases.emptyRoot.count → Result (cases.emptyRoot.entry i)
  compact : ∀ i, i < cases.compact.count → Result (cases.compact.entry i)
  large : ∀ i, i < cases.large.count → Result (cases.large.entry i)

def TriangleCountsValid (triangles : TriangleTable) : Prop :=
  ∀ i, i < triangles.count → TriangleCountCertificate.Valid (triangles.entry i)

def keyCheck (table : KeyTable) (key : Key) (index : Nat) : Bool :=
  decide (index < table.count) && decide (table.entry index = key)

def check (row : Row) (cases : Cases) (triangles : TriangleTable)
    (route : Route) (graphIndex : Nat) : Bool :=
  if route.tag = 0 then
    decide (route.index < triangles.count) &&
      (decide ((triangles.entry route.index).complement =
        TriangleCountCertificate.catalogueMask row.level graphIndex) &&
       decide ((triangles.entry route.index).triangles < row.minimum))
  else if route.tag = 1 then keyCheck cases.emptyRoot (row.key graphIndex) route.index
  else if route.tag = 2 then keyCheck cases.compact (row.key graphIndex) route.index
  else if route.tag = 3 then keyCheck cases.large (row.key graphIndex) route.index
  else false

theorem result_of_keyCheck (Result : Key → Prop) (table : KeyTable)
    (hresult : ∀ i, i < table.count → Result (table.entry i))
    (key : Key) (index : Nat) (h : keyCheck table key index = true) : Result key := by
  obtain ⟨hi, hk⟩ := Bool.and_eq_true_iff.mp h
  have hi' := of_decide_eq_true hi
  have hk' := of_decide_eq_true hk
  exact hk' ▸ hresult index hi'

theorem result_of_check (Result : Key → Prop) (row : Row) (cases : Cases)
    (triangles : TriangleTable) (hcounts : TriangleCountsValid triangles)
    (hcases : Resolved Result cases)
    (htriangle : ∀ complement, TenGraphTriangles.count complement < row.minimum →
      Result (row.code, complement))
    (route : Route) (graphIndex : Nat)
    (h : check row cases triangles route graphIndex = true) : Result (row.key graphIndex) := by
  by_cases h0 : route.tag = 0
  · simp only [check, h0, ite_true, Bool.and_eq_true_iff, decide_eq_true_eq] at h
    obtain ⟨hi, hm, ht⟩ := h
    have hc := (hcounts route.index hi).count
    apply htriangle
    rw [← hm, hc]
    exact ht
  · by_cases h1 : route.tag = 1
    · apply result_of_keyCheck Result cases.emptyRoot hcases.emptyRoot
      simpa [check, h0, h1] using h
    · by_cases h2 : route.tag = 2
      · apply result_of_keyCheck Result cases.compact hcases.compact
        simpa [check, h0, h1, h2] using h
      · by_cases h3 : route.tag = 3
        · apply result_of_keyCheck Result cases.large hcases.large
          simpa [check, h0, h1, h2, h3] using h
        · simp only [check, h0, h1, h2, h3, ite_false] at h
          exact False.elim (Bool.noConfusion h)

theorem row_complete (Result : Key → Prop) (row : Row) (cases : Cases)
    (triangles : TriangleTable) (routes : Nat → Route)
    (hcounts : TriangleCountsValid triangles) (hcases : Resolved Result cases)
    (htriangle : ∀ complement, TenGraphTriangles.count complement < row.minimum →
      Result (row.code, complement))
    (hchecked : FiniteChecks.Interval
      (fun i => check row cases triangles (routes i) i) 0 row.graphCount)
    (i : Fin row.graphCount) : Result (row.key i.val) :=
  result_of_check Result row cases triangles hcounts hcases htriangle
    (routes i.val) i.val (hchecked i.val (Nat.zero_le _) i.isLt)

#print axioms row_complete
end
end Papers.RationalityTen.GraphRouteSelector
