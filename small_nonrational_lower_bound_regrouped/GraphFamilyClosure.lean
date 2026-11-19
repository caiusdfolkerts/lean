module

public import RootedFamilyClosure
public import CheckedGraphGrowthFrames

@[expose] public section

/-!
# Soundness of complete graph-conditioned families

Graph filtering retains the actual edge and nonedge constraints. This
interface therefore asks for the full graph target, together with exact
literal data, rather than replacing that target by an ordinary boundary
target. The geometric conclusion follows through the same checked leaf
certificates used by rooted growth.
-/

noncomputable section
namespace Papers.RationalityTen.GraphFamilyClosure

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open ActualGraphGrowthTarget LiteralGraphGrowthRenaming
open Nonrational.TerminalData Nonrational.TerminalVerification

/-- Forgetting the graph preserves the complete geometric relabeling. -/
def boundaryFrame {n k : Nat} {D : GraphGrowthConstraints.Problem n 1024 45 10 k}
    {cells : Fin n → ConcreteGrowth.Cell} (F : Frame D cells) :
    BoundaryGeneratorFrames.BoundaryFrame cells where
  vertices := F.vertices
  cellMap := F.cellMap
  ridgeMap := F.ridgeMap
  cell_geometry := F.cell_geometry
  ridge_geometry := F.ridge_geometry
  kind_preserved := F.kind_preserved

theorem applyWord_eq {n k g : Nat}
    {D : GraphGrowthConstraints.Problem n 1024 45 10 k}
    {cells : Fin n → ConcreteGrowth.Cell}
    (frames : Fin g → Frame D cells) (H : LiteralData D cells)
    (hwell : ∀ i, WellFormed (cells i))
    (word : List (Fin g)) (B : List (Fin n)) :
    OrbitGrowthDAG.applyWord (fun f => ((frames f).toRenaming H hwell).boundary) word B =
      OrbitGrowthDAG.applyWord
        (fun f => (boundaryFrame (frames f)).toBoundaryRenaming hwell) word B := by
  induction word generalizing B with
  | nil => rfl
  | cons f rest ih =>
    exact ih (B.map (frames f).cellMap.forward)

/-- A finite graph family, its literal interpretation, and every leaf
disposition. The completeness assertion retains the original graph target. -/
structure FiniteClassification {n k : Nat}
    (D : GraphGrowthConstraints.Problem n 1024 45 10 k)
    (cells : Fin n → ConcreteGrowth.Cell) where
  literal : LiteralData D cells
  wellFormed : ∀ i, WellFormed (cells i)
  generatorCount : Nat
  frames : Fin generatorCount → Frame D cells
  root : List (Fin n)
  leafCount : Nat
  leaves : Fin leafCount → List (Fin n)
  nodup : ∀ j, (leaves j).Nodup
  rawLeaves : Fin leafCount → List ConcreteGrowth.Cell
  raw_exact : ∀ j, (leaves j).map cells = rawLeaves j
  certificates : Fin leafCount → RawLeafCertificate.Certificate
  checked : ∀ j, RawLeafCertificate.check D.quota (rawLeaves j) (certificates j) = true
  complete : ∀ B : List (Fin n), GraphGrowthConstraints.Target D B →
    GrowthDAG.Included (SparseGrowthDAG.family root) (SparseGrowthDAG.family B) →
    ∃ j word, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family (OrbitGrowthDAG.applyWord
        (fun f => ((frames f).toRenaming literal wellFormed).boundary) word B))

/-- An actual complete boundary satisfying the checked graph family's
target is rationally realizable. Every quota is its exact actual count. -/
theorem rationallyRealizable_of_encoding {n k : Nat}
    (hvalid : ∀ j, j < targetCount → ValidTarget j)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (D : GraphGrowthConstraints.Problem n 1024 45 10 k)
    (cells : Fin n → ConcreteGrowth.Cell)
    (classification : FiniteClassification D cells)
    (lab : P.vertices ≃ Fin 10)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (htarget : GraphGrowthConstraints.Target D E.family.toList)
    (hroot : GrowthDAG.Included (SparseGrowthDAG.family classification.root)
      (SparseGrowthDAG.family E.family.toList))
    (hquota : ∀ t, (E.family.filter fun i => (cells i).kind = t).card = D.quota t) :
    RationallyRealizable P := by
  obtain ⟨j, word, hsame⟩ := classification.complete E.family.toList htarget hroot
  rw [applyWord_eq] at hsame
  exact ActualLeafCertificates.rationallyRealizable_of_classification hvalid P hP
    (RootedFamilyClosure.nonsimple_neighbors hP hnonsimple) lab cells
    classification.wellFormed E (fun f => boundaryFrame (classification.frames f))
    classification.leaves classification.rawLeaves classification.raw_exact
    D.quota hquota classification.certificates classification.checked
    ⟨j, word, classification.nodup j, hsame⟩

#print axioms rationallyRealizable_of_encoding

end Papers.RationalityTen.GraphFamilyClosure
