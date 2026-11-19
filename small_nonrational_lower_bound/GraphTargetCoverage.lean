module

public import GraphFamilyClosure
public import ActualLeafTargetCoverage

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

/-- An actual complete boundary satisfying the checked graph family's
target is rationally realizable. Every quota is its exact actual count. -/
theorem hasTerminal_of_encoding {n k : Nat}
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
    ActualLeafTargetCoverage.HasTerminal P := by
  obtain ⟨j, word, hsame⟩ := classification.complete E.family.toList htarget hroot
  rw [applyWord_eq] at hsame
  exact ActualLeafTargetCoverage.hasTerminal_of_classification P hP
    (RootedFamilyClosure.nonsimple_neighbors hP hnonsimple) lab cells
    classification.wellFormed E (fun f => boundaryFrame (classification.frames f))
    classification.leaves classification.rawLeaves classification.raw_exact
    D.quota hquota classification.certificates classification.checked
    ⟨j, word, classification.nodup j, hsame⟩

#print axioms hasTerminal_of_encoding

end Papers.RationalityTen.GraphFamilyClosure
