module

public import Papers.GraphicalZonotopes.UnitActiveSupport
public import Papers.GraphicalZonotopes.FourPartActiveSupport
public import Papers.GraphicalZonotopes.SeparatorPaperStatements

/-! # Unit-lattice direction supports without ambient full dimension

This is the active-coordinate formulation stated in the introduction. The
polytope may use only part of the ambient graph. The conclusion classifies its
actual edge directions, including every unused coordinate as an isolated
vertex, rather than imposing full dimension or ambient graph coverage.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise BigOperators
namespace GraphicalZonotopes
open Finset RefinedTriangleComponents FourPartGraphRecognition

/-- Every indecomposable lattice summand of an unscaled K5-free graphical
zonotope, in any actual dimension at least three, has a complete four-partite
actual direction graph on its active coordinates. Each part has one or two
vertices. In particular there are at most eight active coordinates and the
affine dimension is at most seven. The finite vertex order is chosen
internally and is not an added hypothesis. -/
theorem unit_lattice_active_classification_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := Separator.finiteVertexOrder V;
    ∀ (G : SimpleGraph V), G.CliqueFree 5 →
      ∀ (Q : Set (V → ℝ)), LatticePolytope Q →
      PolytopalMinkowskiIndecomposable Q →
      3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) →
      IsMinkowskiSummand Q (graphicalZonotope G) →
      ∃ A : Fin 4 → Finset V,
        (∀ i, (A i).card = 1 ∨ (A i).card = 2) ∧
        (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
        (∀ u v, (actualDirectionGraph Q).Adj u v ↔
          ∃ i j : Fin 4, i ≠ j ∧ u ∈ A i ∧ v ∈ A j) ∧
        (actualDirectionGraph Q).support =
          ((univ.biUnion A : Finset V) : Set V) ∧
        (actualDirectionGraph Q).support.ncard ≤ 8 ∧
        Module.finrank ℝ (vectorSpan ℝ Q) ≤ 7 := by
  letI : LinearOrder V := Separator.finiteVertexOrder V
  intro G hG Q hQ hi hd hsum
  obtain ⟨z,A,hz,hsize,hdis,hprod,hactual,hdep,hdim⟩ :=
    UnitLatticeGeometry.active_coefficient_model hG hQ hi hd hsum
  have hne : ∀ i, (A i).Nonempty := by
    intro i
    apply card_pos.mp
    rcases hsize i with h | h <;> omega
  have hadj : ∀ u v, (actualDirectionGraph Q).Adj u v ↔
      ∃ i j : Fin 4, i ≠ j ∧ u ∈ A i ∧ v ∈ A j := by
    intro u v
    rw [hactual]
    exact product_unionGraph_adj_iff hne hdis hprod u v
  have hsupport : (actualDirectionGraph Q).support =
      ((univ.biUnion A : Finset V) : Set V) := by
    rw [hactual]
    exact product_unionGraph_support hne hdis hprod
  have hU : (univ.biUnion A).card ≤ 8 := by
    apply card_biUnion_le.trans
    calc
      (∑ i : Fin 4, (A i).card) ≤ ∑ _i : Fin 4, 2 := by
        apply sum_le_sum
        intro i _
        rcases hsize i with h | h <;> omega
      _ = 8 := by norm_num
  have hFsub : (family (mobius z)).biUnion id ⊆ univ.biUnion A := by
    intro v hv
    obtain ⟨D,hD,hvD⟩ := mem_biUnion.mp hv
    obtain ⟨w,hw,rfl⟩ := (hprod D).mp hD
    obtain ⟨i,_,hiv⟩ := mem_image.mp hvD
    exact mem_biUnion.mpr ⟨i,mem_univ _,hiv ▸ hw i⟩
  have hFcard := (card_le_card hFsub).trans hU
  have hdimle := finrank_vectorSpan_le_support hz.1 hz.2.1 hdep
  rw [hdim] at hdimle
  refine ⟨A,hsize,hdis,hadj,hsupport,?_,by omega⟩
  rw [hsupport,Set.ncard_coe_finset]
  exact hU

end GraphicalZonotopes
