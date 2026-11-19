module

public import Papers.GraphicalZonotopes.CubeDecisionTree
public import Papers.GraphicalZonotopes.TwoHubPartitionDilation
public import Papers.GraphicalZonotopes.PolytopalWeakSummands

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace CellDecisionTree

def totalDepth {C : Cell I} (T : CellDecisionTree C) : ℕ :=
  ∑ D : T.leaves,D.1.fixed.card

/-- The paper's tree hypotheses imply every property required by the
previously checked geometric partition construction. -/
def partitionData [Nonempty I] (T : CellDecisionTree (Cell.root (I:=I)))
    (h : T.tested=univ) : PartitionData I where
  cells:=T.leaves
  valid:=T.root_valid
  proper:=T.root_proper h
  uses:=by simpa only [h] using T.uses_zero

@[simp] theorem partitionData_card [Nonempty I]
    (T : CellDecisionTree (Cell.root (I:=I))) (h : T.tested=univ) :
    (T.partitionData h).cells.card=T.leafCount := T.leaves_card

@[simp] theorem partitionData_totalDepth [Nonempty I]
    (T : CellDecisionTree (Cell.root (I:=I))) (h : T.tested=univ) :
    (T.partitionData h).totalDepth=T.totalDepth := rfl

end CellDecisionTree

/-- The actual integral summand, in exactly the natural-number multipartite
coordinate system used by Lemma8.6. -/
theorem decision_tree_lattice_summand (p : ℕ) (hp : 1≤p)
    (T : CellDecisionTree (Cell.root (I:=Fin p))) (ht : T.tested=univ) :
    LatticeExtremeAt (twoSingletonGraph p (T.leafCount+p))
      (T.leafCount+2*p+1) (T.totalDepth-T.leafCount+2) := by
  letI : Nonempty (Fin p):=⟨⟨0,hp⟩⟩
  let P:=T.partitionData ht
  have hh:=P.lattice_extreme_at
  let e:=graphIso (I:=Fin p) (J:=P.Index)
  have hm : graph (I:=Fin p) (J:=P.Index)≤
      (twoSingletonGraph (Fintype.card (Fin p)) (Fintype.card P.Index)).comap e := by
    intro x y hxy
    exact e.map_adj_iff.mpr hxy
  have he:=hh.embed e.toEquiv.toEmbedding hm
  have hcard : (Fintype.card (Fin p),Fintype.card P.Index)=(p,T.leafCount+p) := by
    simp [PartitionData.Index,P]
  have he':=Eq.mp (congrArg (fun x : ℕ×ℕ =>
    LatticeExtremeAt (twoSingletonGraph x.1 x.2)
      (P.cells.card+2*Fintype.card (Fin p)+1) (P.totalDepth-P.cells.card+2)) hcard) he
  simpa only [P,CellDecisionTree.partitionData_card,CellDecisionTree.partitionData_totalDepth,
    Fintype.card_fin] using he'

/-- Literal Lemma8.6: every full binary coordinate decision tree testing
all p≥1 coordinates gives a full-dimensional lattice indecomposable weak
summand of K₁,₁,ₚ,ₖ₊ₚ, with a finite polytopal complement at dilation L−k+2.
The two parameters are the actual leaf count and the sum of the sizes of
the leaf fixed-coordinate sets. -/
theorem paper_lemma_8_6 (p : ℕ) (hp : 1≤p)
    (T : CellDecisionTree (Cell.root (I:=Fin p))) (ht : T.tested=univ) :
    ∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,T.leafCount+p] i))→ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=T.leafCount+2*p+1 ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p (T.leafCount+p))) ∧
      ∃ R : Set ((Σ i : Fin 4,Fin (![1,1,p,T.leafCount+p] i))→ℝ),
        IsFinitePolytope R ∧ R.Nonempty ∧
        Q+R=(((T.totalDepth-T.leafCount+2 : ℕ) : ℝ) •
          graphicalZonotope (twoSingletonGraph p (T.leafCount+p))) := by
  letI : Nonempty (Fin p):=⟨⟨0,hp⟩⟩
  obtain ⟨Q,hl,hi,hd,hs⟩ := (decision_tree_lattice_summand p hp T ht).polytope
  have hM : (0 : ℝ)<((T.totalDepth-T.leafCount+2 : ℕ) : ℝ) := by positivity
  have hw : IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p (T.leafCount+p))) :=
    ⟨_,hM,hs⟩
  refine ⟨Q,hl,(weakSummand_indecomposable_iff_polytopal hl.finitePolytope hw).mp hi,
    ?_,hd,hw,?_⟩
  · change Module.finrank ℝ (vectorSpan ℝ Q)=
      Fintype.card (Σ i : Fin 4,Fin (![1,1,p,T.leafCount+p] i))-1
    have hc : Fintype.card (Σ i : Fin 4,Fin (![1,1,p,T.leafCount+p] i))=
        p+(T.leafCount+p)+2 := by
      simp [Fintype.card_sigma,Fin.sum_univ_succ]
      omega
    rw [hd,hc]
    omega
  · exact (isMinkowskiSummand_graphical_iff_finite_complement hl.finitePolytope hM.le).mp hs

end GraphicalZonotopes.TwoHub
