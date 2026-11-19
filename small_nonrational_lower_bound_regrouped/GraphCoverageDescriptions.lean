module
prelude
public import GraphSixEmbeddingCoverage

@[expose] public section

/-! Candidate coverage depends only on the complete global cell catalogue,
its induced graph, the positive facet kinds and the local embedding. The
remaining search data play no role. This interface makes that dependence
explicit, so an identical embedding can reuse its exact coverage proof. -/
namespace Papers.RationalityTen.GraphCoverageDescriptions
open ConcreteGrowth PackedGraphCertificate SharedGraphCellPool
open GraphCandidateCoverage GraphCaseCertificate GrowthBitsets

structure Description where
  cellPred : Nat
  fields : Fields

def ofData (D : RawData) : Description := ⟨D.cellPred, D.embedding⟩

def Description.cells (S : Description) (N : Nat) [NeZero N] : List (Fin N) :=
  (List.finRange (S.cellPred + 1)).map fun c => Fin.ofNat N (S.fields.get c.val)

structure Checked {N : Nat} [NeZero N] (S : Description)
    (rows : IncidenceRows N 10 45) (allowed complement : Nat) : Prop where
  nodup : (S.cells N).Nodup
  mask : eligibleMask rows allowed complement = ofList (S.cells N)

theorem coverage_of_checked {N : Nat} [NeZero N] (D : RawData) (S : Description)
    (cells : Fin N → Cell) (rows : IncidenceRows N 10 45) (allowed complement : Nat)
    (hs : ofData D = S)
    (hcells : ∀ c, D.data.cells c = cells (embedding D c))
    (hallowed : ∀ c, allowed.testBit c.val = true ↔ 0 < D.data.quota (cells c).kind)
    (hedges : ∀ c q, (rows.edges c).testBit q.val = true →
      (rows.vertices c).testBit (rows.first q).val = true ∧
      (rows.vertices c).testBit (rows.second q).val = true)
    (h : Checked S rows allowed complement) : Coverage D cells rows complement := by
  subst S
  exact GraphEmbeddingCoverage.coverage_of_mask D cells rows complement allowed
    hcells h.nodup hallowed h.mask hedges

def quota (pattern j : Nat) : Nat := if pattern.testBit j then 1 else 0

theorem small_allowed (D : RawData) (pattern : Nat)
    (h : ∀ j : Fin 5, (0 < quota pattern j.val) ↔ 0 < D.data.quota j.val)
    (c : Fin 6510) :
    (SharedSmallGraph.allowedMask (quota pattern)).testBit c.val = true ↔
      0 < D.data.quota (FacetUniverses.FullSmall.cells c).kind := by
  rw [GraphEmbeddingCoverage.small_allowed]
  exact h ⟨_, SharedSmallGraph.kind_lt c⟩

theorem six_allowed (D : RawData) (pattern : Nat)
    (h : ∀ j : Fin 5, (0 < quota pattern j.val) ↔ 0 < D.data.quota j.val)
    (c : Fin 44310) :
    (GraphEmbeddingCoverage.sixAllowed (quota pattern)).testBit c.val = true ↔
      0 < D.data.quota (FacetUniverses.FullSix0.cells c).kind := by
  rw [GraphEmbeddingCoverage.six_allowed]
  have hc := (SharedSix0CellPool.facts c).kind_lt
  rw [(SharedSix0CellPool.facts c).cell_eq] at hc
  exact h ⟨_, hc⟩

#print axioms coverage_of_checked
#print axioms small_allowed
#print axioms six_allowed
end Papers.RationalityTen.GraphCoverageDescriptions
