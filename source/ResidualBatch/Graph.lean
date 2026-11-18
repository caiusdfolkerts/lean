module
prelude
public import ResidualBatch.NodeAndFrame
public import GraphCompactBlocks
public import GraphSixEmbeddingCoverage

/-! Reconstruct an original graph dispatch block from uniform finite checks.
The source prototype uses the complete literal metadata check. -/

@[expose] public section
noncomputable section
namespace Papers.RationalityTen.ResidualBatch

open ConcreteGrowth FiniteChecks PackedGraphCertificate GraphCaseCertificate
open RawGraphSemanticCertificate GraphCandidateCoverage SharedGraphCellPool
open GraphRowSpecifications GraphFiniteDispatch

structure Packet where
  data : RawData
  complement : Nat
  frame : Fin data.g → FrameWitness
  leaf : Fin data.l → RawLeafCertificate.Certificate

def sideCheck (p : Packet) : Bool :=
  allFin (literalCellTest p.data.data) &&
    (allFin (fun f => frameCheck p.data f (p.frame f)) &&
    (decide ((p.data.nodes p.data.rootNode).cells = []) &&
     allFin (fun j => RawLeafCertificate.check p.data.data.quota
       ((p.data.leaf j).map p.data.data.cells) (p.leaf j))))

theorem core_of_checks {m : Nat} [NeZero m] (packets : Fin m → Packet)
    (metaOk : ∀ i, (packets i).data.metadataCheck = true)
    (nodes : Interval (batchNodeTest (fun i => (packets i).data) metaOk) 0 m)
    (side : ∀ i, sideCheck (packets i) = true) (i : Fin m) : Core (packets i).data := by
  let D := (packets i).data
  have h := metaOk i
  obtain ⟨lit, frames, root, leaves⟩ := (by
    simpa only [sideCheck, Bool.and_eq_true_iff] using side i)
  refine {
    matrix := D.metadata_checked h
    valid := D.valid_of_metadata h
    literal := literalFacts_of_checks D.data (allFin_at _ lit)
    nodes := ?_
    leaf_nodup := D.leaves_nodup h
    frames := ?_
    root_empty := of_decide_eq_true root
    leaves_checked := ⟨(packets i).leaf, allFin_at _ leaves⟩ }
  · exact rawNodesOfBatch (fun i => (packets i).data) metaOk nodes i
  · intro f
    exact supported_of_frameCheck D f _ (allFin_at _ frames f)

def parameterCheck (row : Nat) (p : Packet) : Bool :=
  decide (p.data.k = 5) &&
    (allFin (n := 5) (fun j => decide (p.data.data.quota j.val = (rowOfCode row).quota.getD j.val 0)) &&
    (decide (p.data.inputs.requiredEdges = SharedSmallGraph.requiredMask p.complement) &&
    (decide (p.data.inputs.missingCount = (rowOfCode row).internalMissingCount) &&
     decide (p.data.inputs.minimumIncidence = 5))))

private theorem parameters_of_check (row : Nat) (p : Packet) (ok : parameterCheck row p = true) :
    Parameters p.data (rowOfCode row) p.complement := by
  obtain ⟨k, quota, required, missing, incidence⟩ := (by
    simpa only [parameterCheck, Bool.and_eq_true_iff] using ok)
  exact ⟨of_decide_eq_true k, fun j => of_decide_eq_true (allFin_at _ quota j),
    of_decide_eq_true required, of_decide_eq_true missing, of_decide_eq_true incidence⟩

def universeCheck {N : Nat} [NeZero N] (p : Packet) (cells : Fin N → Cell)
    (rows : IncidenceRows N 10 45) (allowed : Nat) : Bool :=
  let emb := (List.finRange p.data.n).map (embedding (N := N) p.data)
  allFin (fun c => decide (p.data.data.cells c = cells (embedding p.data c))) &&
    (decide emb.Nodup && decide (eligibleMask rows allowed p.complement = GrowthBitsets.ofList emb))

private theorem coverage_of_check {N : Nat} [NeZero N] (p : Packet) (cells : Fin N → Cell)
    (rows : IncidenceRows N 10 45) (allowed : Nat)
    (hallowed : ∀ c, allowed.testBit c.val = true ↔ 0 < p.data.data.quota (cells c).kind)
    (hedges : ∀ c q, (rows.edges c).testBit q.val = true →
      (rows.vertices c).testBit (rows.first q).val = true ∧
      (rows.vertices c).testBit (rows.second q).val = true)
    (ok : universeCheck p cells rows allowed = true) : Coverage p.data cells rows p.complement := by
  obtain ⟨cell, nd, mask⟩ := (by simpa only [universeCheck, Bool.and_eq_true_iff] using ok)
  exact GraphEmbeddingCoverage.coverage_of_mask p.data cells rows p.complement allowed
    (fun c => of_decide_eq_true (allFin_at _ cell c)) (of_decide_eq_true nd) hallowed
    (of_decide_eq_true mask) hedges

def rowCheck (row : Nat) (p : Packet) : Bool := parameterCheck row p &&
  (if row = 32 then universeCheck p FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed p.data.data.quota)
   else universeCheck p FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask p.data.data.quota))

theorem result_of_rowCheck (row : Nat) (p : Packet) (core : Core p.data)
    (ok : rowCheck row p = true) : Result (row, p.complement) := by
  obtain ⟨param, covered⟩ := Bool.and_eq_true_iff.mp ok
  have hp := parameters_of_check row p param
  by_cases h : row = 32
  · subst row
    exact of_six _ ⟨p.data, core, hp, coverage_of_check p _ _ _
      (GraphEmbeddingCoverage.six_allowed _) GraphEmbeddingCoverage.six_edges (by simpa using covered)⟩
  · exact of_small _ _ h ⟨p.data, core, hp, coverage_of_check p _ _ _
      (GraphEmbeddingCoverage.small_allowed _) GraphEmbeddingCoverage.small_edges
      (by simpa only [ite_eq_right h] using covered)⟩

def metadataAt {m : Nat} [NeZero m] (p : Fin m → Packet) (j : Nat) : Bool :=
  (p (Fin.ofNat m j)).data.metadataCheck

theorem checkedMetadata {m : Nat} [NeZero m] (p : Fin m → Packet)
    (metadata : Interval (metadataAt p) 0 m) : ∀ i, (p i).data.metadataCheck = true :=
  batch_metadata (fun i => (p i).data) metadata

def keysCheck (offset row : Nat) (p : Packet) (j : Nat) : Bool :=
  decide ((row, p.complement) = GraphRoutes.compactKeys.entry (offset + j))

/-- Pointwise coverage of the original global compact key table. -/
theorem completeBlock {m : Nat} [NeZero m] (offset row : Nat) (p : Fin m → Packet)
    (metadata : Interval (metadataAt p) 0 m)
    (nodes : Interval (batchNodeTest (fun i => (p i).data) (checkedMetadata p metadata)) 0 m)
    (side : Interval (fun j => sideCheck (p (Fin.ofNat m j))) 0 m)
    (rows : Interval (fun j => rowCheck row (p (Fin.ofNat m j))) 0 m)
    (keys : Interval (fun j => keysCheck offset row (p (Fin.ofNat m j)) j) 0 m) :
    Block offset (offset + m) := by
  intro i lo hi
  let j : Fin m := ⟨i - offset, by omega⟩
  have hsum : offset + j.val = i := by dsimp [j]; omega
  have hk := of_decide_eq_true (keys j.val (Nat.zero_le _) j.isLt)
  simp only [Fin.ofNat_val_eq_self, hsum] at hk
  rw [← hk]
  exact result_of_rowCheck row (p j)
    (core_of_checks p (checkedMetadata p metadata) nodes (fin_of_interval _ side) j)
    (fin_of_interval (fun i => rowCheck row (p i)) rows j)

end Papers.RationalityTen.ResidualBatch
