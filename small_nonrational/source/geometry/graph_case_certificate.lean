module
prelude
public import GraphCoreCertificate
public import SharedSmallRootReplay
public import SharedSix0IncidenceChecked
public import GraphRowSpecifications

@[expose] public section

/-!
# Complete finite evidence for a graph case

These propositions retain every input needed by geometric soundness. A packed
case carries exact incidence meanings, complete candidate coverage, all growth
checks, genuine frame witnesses, and a checked disposition for every leaf.
An empty-root case uses the original root-exclusion checker on the complete
global eligible universe. A triangle exclusion records the original exact
triangle count. The row code fixes every numerical parameter.

Concrete certificate modules can prove this small public interface with
private imports of their large tables. No table equality or producer result
is accepted as an assumption in a closed case theorem.
-/

namespace Papers.RationalityTen.GraphCaseCertificate

open ConcreteGrowth PackedGraphCertificate SharedGraphCellPool
open GraphRouteSelector GraphRowSpecifications GraphCandidateCoverage

structure Parameters (D : RawData) (row : Row) (complement : Nat) : Prop where
  kind_count : D.k = 5
  quota : ∀ j : Fin 5, D.data.quota j.val = row.quota.getD j.val 0
  required : D.inputs.requiredEdges = SharedSmallGraph.requiredMask complement
  internal_missing : D.inputs.missingCount = row.internalMissingCount
  minimum_incidence : D.inputs.minimumIncidence = 5

structure Coverage {N : Nat} [NeZero N] (D : RawData)
    (cells : Fin N → Cell) (rows : IncidenceRows N 10 45)
    (complement : Nat) : Prop where
  cells_exact : ∀ c, D.data.cells c = cells (embedding D c)
  embedding_nodup : ((List.finRange D.n).map (embedding (N := N) D)).Nodup
  complete : ∀ c, (∃ a : Fin D.n, embedding D a = c) ↔
    0 < D.data.quota (cells c).kind ∧ Induced rows complement c

def Small (row : Row) (complement : Nat) : Prop :=
  ∃ D : RawData, Core D ∧ Parameters D row complement ∧
    Coverage D FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows complement

def Six (row : Row) (complement : Nat) : Prop :=
  ∃ D : RawData, Core D ∧ Parameters D row complement ∧
    Coverage D FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows complement

def EmptyRoot (row : Row) (complement : Nat) : Prop :=
  ∃ code : Nat, SharedSmallRootReplay.complement code = complement ∧
    SharedSmallRootReplay.check (fun j => row.quota.getD j 0)
      row.internalMissingCount code = true

def Result (key : Key) : Prop :=
  let row := rowOfCode key.1
  TenGraphTriangles.count key.2 < row.minimum ∨
    if key.1 = 32 then Six row key.2
    else Small row key.2 ∨ EmptyRoot row key.2

theorem of_triangle (row : Row) (hrow : rowOfCode row.code = row)
    (complement : Nat) (h : TenGraphTriangles.count complement < row.minimum) :
    Result (row.code, complement) := by
  apply Or.inl
  change TenGraphTriangles.count complement < (rowOfCode row.code).minimum
  rw [hrow]
  exact h

theorem of_small (code complement : Nat) (hcode : code ≠ 32)
    (h : Small (rowOfCode code) complement) : Result (code, complement) := by
  apply Or.inr
  simp only [hcode, ite_false]
  exact Or.inl h

theorem of_six (complement : Nat) (h : Six (rowOfCode 32) complement) :
    Result (32, complement) := by
  exact Or.inr h

theorem of_empty (code complement : Nat) (hcode : code ≠ 32)
    (h : EmptyRoot (rowOfCode code) complement) : Result (code, complement) := by
  apply Or.inr
  simp only [hcode, ite_false]
  exact Or.inr h

#print axioms of_triangle
#print axioms of_small
#print axioms of_six
#print axioms of_empty

end Papers.RationalityTen.GraphCaseCertificate
