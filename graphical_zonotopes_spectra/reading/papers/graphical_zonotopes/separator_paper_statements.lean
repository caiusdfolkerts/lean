module

public import Papers.GraphicalZonotopes.SeparatorLifts
public import Papers.GraphicalZonotopes.CliqueSeparatorCapacity
public import Mathlib.Order.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators

/-- An order used only to select one orientation of every unordered edge.
It is supplied for every finite vertex type, rather than assumed as extra
mathematical structure on the graph. -/
def finiteVertexOrder (V : Type*) [Fintype V] : LinearOrder V :=
  LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective

/-- Lemma 5.1 on an arbitrary finite vertex type, with its orientation
convention chosen internally. There is no order hypothesis. -/
theorem induced_separator_capacity_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := finiteVertexOrder V;
    ∀ (G : SimpleGraph V) (B : Finset V) (z : graphicalFunctionSpace G),
      ExtremeSupermodular z.1 →
      Fintype.card (Gluing.ActiveBranch
        (((functionEquiv (componentPartition G B)).symm z).2)) ≤
        (∑ e : BoundaryEdge G B,
          2^(commonNeighbors G e.1.1.1 e.1.1.2 ∩ B).card) -
          (boundaryCliques G B).card + 1 := by
  letI : LinearOrder V := finiteVertexOrder V
  exact fun G B z hz => induced_separator_capacity G B z hz

/-- Theorem 7.2 for an arbitrary finite vertex type; an ordering used to
orient unordered edges is supplied internally. -/
theorem clique_separator_capacity_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := finiteVertexOrder V;
    ∀ (G : SimpleGraph V) (B : Finset V),G.IsClique B → 2≤B.card →
      ∀ z : graphicalFunctionSpace G,ExtremeSupermodular z.1 →
        Fintype.card (Gluing.ActiveBranch
          (((functionEquiv (componentPartition G B)).symm z).2))≤cliqueCapacity B.card := by
  letI : LinearOrder V := finiteVertexOrder V
  exact fun G B hB hs z hz => clique_separator_capacity hB hs z hz

section Ordered
variable {V J : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- The literal closing-function transformation in the paper: adding a
boundary lift to each branch is compensated by subtracting the scaled sum
of those lifts from the closing function. The original function is equal. -/
theorem assembled_boundary_lift_transfer (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (l : J → boundaryIndex G B → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) :
    boundaryFunctionMap h (z - ∑ j, lam j • l j) +
      ∑ j, lam j • branchWithLift h j (f j) (l j) =
      globalFunctionMap h (Gluing.assemble z lam f) := by
  rw [assembled_boundary_lift_eq]
  simp only [sub_add_cancel]

/-- Every conclusion of Theorem 5.4, including membership in the original
normalized graphical cone, the exact dimension, the equivalence, the unique
positive relation, and the branch count. -/
def PositiveResponseGluingConclusion (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) : Prop :=
  let p := globalFunctionMap h (gluedCoordinates f z lam)
  let R := LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))
  TranslationNormalized p ∧ Graphical G p ∧ Supermodular p ∧
    Module.finrank ℝ
      (Polyhedral.tightKernel (contextRow G)
        (functionEquiv h (gluedCoordinates f z lam))) = Module.finrank ℝ R ∧
    (ExtremeSupermodular p ↔ Module.finrank ℝ R = 1) ∧
    (ExtremeSupermodular p →
      R = Submodule.span ℝ {lam} ∧
      Fintype.card J ≤
        (∑ e : BoundaryEdge G B,
          2^(commonNeighbors G e.1.1.1 e.1.1.2 ∩ B).card) -
          (boundaryCliques G B).card + 1)

/-- Theorem 5.4 as one endpoint, using the literal equality of private
kernels with their one-dimensional spans. Boundary lifts are justified by
`lifted_relationLinear_eq` and `assembled_boundary_lift_eq`. -/
theorem positive_response_gluing (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ)
    (hlam : ∀ j, 0 < lam j) (hf : ∀ j, f j ≠ 0)
    (hi : ∀ j r, 0 ≤ (rowData h).internal j r (f j))
    (hprivate : ∀ j, (rowData h).privateKernelSpace f (conditionalMin h f) j =
      Submodule.span ℝ {f j})
    (hclose : (rowData h).Closure (conditionalMin h f) z lam) :
    PositiveResponseGluingConclusion h f z lam := by
  have hline : ∀ j g, (rowData h).PrivateKernel f (conditionalMin h f) j g →
      ∃ c : ℝ, g = c • f j :=
    fun j => (Gluing.privateKernelSpace_eq_span_iff
      (rowData h) f (conditionalMin h f) j).mp (hprivate j)
  have hn := (functionEquiv h (gluedCoordinates f z lam)).2
  exact ⟨hn.1, hn.2, glued_supermodular h f z lam hlam hf hi hline hclose,
    graphical_tight_finrank_eq_relation_finrank h f z lam hlam hf hi hline hclose,
    graphical_extreme_iff_relation_finrank_one h f z lam hlam hf hi hline hclose,
    graphical_positive_relation_and_capacity h f z lam hlam hf hi hline hclose⟩

end Ordered

/-- The same complete gluing theorem for every finite vertex type. The
orientation order is constructed internally and is not an additional
hypothesis on the graph, its separator, or any branch function. -/
theorem positive_response_gluing_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := finiteVertexOrder V;
    ∀ {J : Type*} [Fintype J] [DecidableEq J]
      {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}
      (h : Partition G B A)
      (f : ∀ j, privateIndex G B A j → ℝ)
      (z : boundaryIndex G B → ℝ) (lam : J → ℝ),
      (∀ j, 0 < lam j) → (∀ j, f j ≠ 0) →
      (∀ j r, 0 ≤ (rowData h).internal j r (f j)) →
      (∀ j, (rowData h).privateKernelSpace f (conditionalMin h f) j =
        Submodule.span ℝ {f j}) →
      (rowData h).Closure (conditionalMin h f) z lam →
      PositiveResponseGluingConclusion h f z lam := by
  letI : LinearOrder V := finiteVertexOrder V
  intro J _ _ G B A h f z lam hlam hf hi hprivate hclose
  exact positive_response_gluing h f z lam hlam hf hi hprivate hclose

end Separator
end GraphicalZonotopes
