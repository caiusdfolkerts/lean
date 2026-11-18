module
prelude
public import MatrixGraphProblem
public import CachedCellRelabel
public import FastTenGraphEdges

@[expose] public section

/-!
# Literal meanings of graph data and relabelings

The replay cache checks incidence internally.  The checks in this module
add its independent interpretation: vertex bits are the cell's vertices,
edge slots name exactly its edges, and missing slots name all other pairs
of its vertices.  Frame checks retain the complete edge and polygon families.

These are finite checks only.  Geometric coverage of the candidate list and
the interpretation of terminal leaves are proved in separate modules.
-/

namespace Papers.RationalityTen.RawGraphSemanticCertificate

open ConcreteGrowth FiniteChecks MatrixGraphProblem RawGraphGrowthFrames

def fastPairMask (q : Fin 45) : Nat :=
  2 ^ (FastTenGraphEdges.first q).val + 2 ^ (FastTenGraphEdges.second q).val

variable {n k : Nat}

/-- Literal incidence facts, independent of all cache implementations. -/
structure LiteralFacts (D : MatrixGraphProblem.Data n 45 10 k) : Prop where
  vertices : ∀ a c,
    (D.vertexRows a).testBit c.val = (D.cells c).vertices.testBit a.val
  edgeMap : ∀ c, (D.edgeLists c).map fastPairMask = (D.cells c).edges
  missing : ∀ c q,
    (D.missingMasks c).testBit q.val =
      ((D.cells c).vertices.testBit (FastTenGraphEdges.first q).val &&
       (D.cells c).vertices.testBit (FastTenGraphEdges.second q).val &&
       !(D.edgeMasks c).testBit q.val)

def literalCellTest (D : MatrixGraphProblem.Data n 45 10 k) (c : Fin n) : Bool :=
  decide ((D.edgeLists c).map fastPairMask = (D.cells c).edges) &&
    ((List.finRange 10).all (fun a =>
      decide ((D.vertexRows a).testBit c.val = (D.cells c).vertices.testBit a.val)) &&
    (List.finRange 45).all (fun q =>
      decide ((D.missingMasks c).testBit q.val =
        ((D.cells c).vertices.testBit (FastTenGraphEdges.first q).val &&
         (D.cells c).vertices.testBit (FastTenGraphEdges.second q).val &&
         !(D.edgeMasks c).testBit q.val))))

theorem literalFacts_of_checks (D : MatrixGraphProblem.Data n 45 10 k)
    (h : ∀ c, literalCellTest D c = true) : LiteralFacts D where
  vertices a c := by
    have hc := (Bool.and_eq_true_iff.mp (h c)).2
    exact of_decide_eq_true
      (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).1 a (List.mem_finRange a))
  edgeMap c := of_decide_eq_true (Bool.and_eq_true_iff.mp (h c)).1
  missing c q := by
    have hc := (Bool.and_eq_true_iff.mp (h c)).2
    exact of_decide_eq_true
      (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 q (List.mem_finRange q))

theorem literalFacts_of_interval [NeZero n]
    (D : MatrixGraphProblem.Data n 45 10 k)
    (h : Interval (fun i => literalCellTest D (Fin.ofNat n i)) 0 n) :
    LiteralFacts D :=
  literalFacts_of_checks D (fin_of_interval (literalCellTest D) h)

/-- The head of a frame verifies the vertex permutation and every graph bit. -/
def frameHeadTest (required vertexForward vertexInverse : Nat) : Bool :=
  TenGraphEdges.permutationCheck vertexForward vertexInverse &&
    (List.finRange 45).all
      (graphCheckAt required (TenGraphEdges.vertexMap vertexForward))

/-- The cell part verifies both inverse laws and the complete relabeled cell. -/
def frameCellTest (cells : Fin n → Cell) (vertexForward : Nat)
    (forward inverse : Fin n → Fin n) (c : Fin n) : Bool :=
  inverseCheckAt forward inverse c &&
    CachedCellRelabel.bitsetCellCheck
      (RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap vertexForward))
      (cells c) (cells (forward c))

structure FrameFacts (cells : Fin n → Cell) (required vertexForward vertexInverse : Nat)
    (forward inverse : Fin n → Fin n) : Prop where
  vertices : TenGraphEdges.permutationCheck vertexForward vertexInverse = true
  inverse : ∀ c, inverseCheckAt forward inverse c = true
  cells : ∀ c, cellRelabelCheck (TenGraphEdges.vertexMap vertexForward)
    (cells c) (cells (forward c)) = true
  graph : ∀ q, graphCheckAt required (TenGraphEdges.vertexMap vertexForward) q = true

theorem frameFacts_of_checks (cells : Fin n → Cell)
    (required vertexForward vertexInverse : Nat) (forward inverse : Fin n → Fin n)
    (hhead : frameHeadTest required vertexForward vertexInverse = true)
    (hcell : ∀ c, frameCellTest cells vertexForward forward inverse c = true) :
    FrameFacts cells required vertexForward vertexInverse forward inverse where
  vertices := (Bool.and_eq_true_iff.mp hhead).1
  inverse c := (Bool.and_eq_true_iff.mp (hcell c)).1
  cells c := by
    have hc := (Bool.and_eq_true_iff.mp (hcell c)).2
    rw [CachedCellRelabel.bitsetCellCheck_eq] at hc
    exact hc
  graph q := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hhead).2 q (List.mem_finRange q)

theorem frameFacts_of_interval [NeZero n] (cells : Fin n → Cell)
    (required vertexForward vertexInverse : Nat) (forward inverse : Fin n → Fin n)
    (hhead : frameHeadTest required vertexForward vertexInverse = true)
    (hcell : Interval
      (fun i => frameCellTest cells vertexForward forward inverse (Fin.ofNat n i)) 0 n) :
    FrameFacts cells required vertexForward vertexInverse forward inverse :=
  frameFacts_of_checks cells required vertexForward vertexInverse forward inverse hhead
    (fin_of_interval (frameCellTest cells vertexForward forward inverse) hcell)

#print axioms literalFacts_of_interval
#print axioms frameFacts_of_interval

end Papers.RationalityTen.RawGraphSemanticCertificate
