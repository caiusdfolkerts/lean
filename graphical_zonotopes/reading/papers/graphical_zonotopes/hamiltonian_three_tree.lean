module

public import Papers.GraphicalZonotopes.HamiltonianDeletion
public import Papers.GraphicalZonotopes.ThreeTreeActiveGeometry
public import Papers.GraphicalZonotopes.PolytopalWeakSummands
public import Mathlib.Order.Basic

/-! # Hamiltonian 3-trees

Corollary 6.9's Hamiltonian assertion follows from literal vertex deletion:
a Hamiltonian cycle yields at most three components after deleting any
triangle. The exact 3-tree deletion theorem then gives admissibility, and
the constructive classification produces an integral extreme witness.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset

theorem IsThreeTree.admissible_of_hamiltonian
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsThreeTree G) (hH : G.IsHamiltonian) : Admissible G := by
  apply hG.admissible_iff_triangle_deletion.mpr
  intro S hS hcl
  have hn : 2 ≤ Fintype.card V := by
    have h := hG.active_card_ge_four
    simp only [card_univ] at h
    omega
  have hne : S.Nonempty := card_pos.mp (by omega)
  simpa only [hS] using
    HamiltonianDeletion.hamiltonian_component_card_delete_le G hH hn S hne

/-- Corollary 6.9's Hamiltonian conclusion on every finite vertex type.
The coordinate order is chosen internally. The witness is an actual lattice
polytope, has full affine dimension and the exact graph as its edge-direction
graph, and is indecomposable for ordinary finite polytopal decompositions. -/
theorem hamiltonian_threeTree_lattice_polytopal_finite
    {V : Type*} [Fintype V] :
    letI : LinearOrder V :=
      LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective;
    ∀ (G : SimpleGraph V), IsThreeTree G → G.IsHamiltonian →
      ∃ Q : Set (V → ℝ), LatticePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        actualDirectionGraph Q = G := by
  letI : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  intro G hG hH
  obtain ⟨f,hf,hint,hd,ha,hgraph⟩ :=
    admissible_threeTree_witness_fintype hG (hG.admissible_of_hamiltonian hH)
  have hlat := hint.basePolytope hf.1.1 hf.2.1
  have hw : IsWeakMinkowskiSummand (basePolytope f) (graphicalZonotope G) :=
    (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr hgraph
  exact ⟨basePolytope f,hlat,
    (weakSummand_indecomposable_iff_polytopal hlat.finitePolytope hw).mp
      hf.minkowskiIndecomposable,hd,hw,ha⟩

end GraphicalZonotopes
