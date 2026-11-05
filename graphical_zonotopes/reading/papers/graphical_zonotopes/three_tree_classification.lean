module

public import Papers.GraphicalZonotopes.ThreeTreeConstruction
public import Papers.GraphicalZonotopes.ThreeTreeDeletion
public import Papers.GraphicalZonotopes.SeparatorFullDimension
public import Papers.GraphicalZonotopes.PrincipalTargets

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise

/-- The sufficiency direction is about ordinary real polytopes and actual
Minkowski sums. The coefficient construction supplies the genuine witness. -/
theorem admissible_threeTree_supports {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) (hA : Admissible G) :
    SupportsFullIndecomposable G := by
  obtain ⟨z,hz,hy,hC,hT,hd,hgraph,hsum⟩:=admissible_threeTree_construction hn hG hA
  refine ⟨basePolytope z,?_,hz.minkowskiIndecomposable,hd,
    ((n-3 : ℕ) : ℝ),?_,hsum⟩
  · exact (show IsGeneralizedPermutahedron (basePolytope z) from
      ⟨z,hz.1.1,hz.2.1,rfl⟩).finitePolytope
  · exact_mod_cast (show 0<n-3 by omega)

theorem threeTree_supports_iff_admissible {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) :
    SupportsFullIndecomposable G ↔ Admissible G := by
  constructor
  · intro hs
    exact hG.admissible_iff_triangle_deletion.mpr
      (fun T ht hc => hs.triangle_components_le_three (by omega) T ht hc)
  · exact admissible_threeTree_supports hn hG

/-- The complete equivalence and quantitative conclusion of Theorem6.1,
with its exact global parameter range and no selected-branch hypothesis. -/
theorem threeTree_classification : Targets.ThreeTreeClassification := by
  intro n hn G hG
  exact ⟨threeTree_supports_iff_admissible hn hG,
    hG.admissible_iff_triangle_deletion,
    admissible_threeTree_construction hn hG⟩

/-- The literal finite family of maximal K4's containing a triangle is the
family used by `triangleMultiplicity`; this checks condition(ii) of the
paper against the coefficient indexing convention. -/
theorem maximal_tetrahedra_containing_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : IsThreeTree G) (T : Finset V) :
    (univ.filter (fun C : Finset V => C.card=4 ∧
      Maximal G.IsClique (C : Set V) ∧ T⊆C))=
      (tetrahedra G).filter (fun C => T⊆C) := by
  classical
  ext C
  simp only [mem_filter,mem_univ,true_and,hG.maximalClique_iff C]
  constructor
  · exact fun h => ⟨h.2.1,h.2.2⟩
  · intro h
    exact ⟨(mem_filter.mp h.1).2.1,h.1,h.2⟩

/-- A statement with the paper's literal maximal-clique count, as well as
the actual induced-deletion component count. -/
theorem threeTree_classification_literal {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) :
    (SupportsFullIndecomposable G ↔
      ∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        (univ.filter (fun C : Finset (Fin n) => C.card=4 ∧
          Maximal G.IsClique (C : Set (Fin n)) ∧ T⊆C)).card≤3) ∧
    (SupportsFullIndecomposable G ↔
      ∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        Nat.card (G.induce ((T : Set (Fin n))ᶜ)).ConnectedComponent≤3) := by
  have he : (∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
      (univ.filter (fun C : Finset (Fin n) => C.card=4 ∧
        Maximal G.IsClique (C : Set (Fin n)) ∧ T⊆C)).card≤3) ↔ Admissible G := by
    simp only [maximal_tetrahedra_containing_eq hG,Admissible,triangleMultiplicity]
  exact ⟨(threeTree_supports_iff_admissible hn hG).trans he.symm,
    (threeTree_supports_iff_admissible hn hG).trans hG.admissible_iff_triangle_deletion⟩

/-- The same constructed ray has an actual lattice-polytope representative,
with every ordinary maximal-clique coefficient equal to one. -/
theorem admissible_threeTree_lattice_witness {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) (hA : Admissible G) :
    ∃ z : SetFunction (Fin n),ExtremeSupermodular z ∧ IntegerValued (mobius z) ∧
      LatticePolytope (basePolytope z) ∧ MinkowskiIndecomposable (basePolytope z) ∧
      FullDimension (basePolytope z) ∧ actualDirectionGraph (basePolytope z)=G ∧
      (∀ C : Finset (Fin n),Maximal G.IsClique (C : Set (Fin n)) → mobius z C=1) ∧
      (∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        mobius z T=0 ∨ mobius z T= -1 ∨ mobius z T= -2) ∧
      IsMinkowskiSummand (basePolytope z) (((n-3 : ℕ) : ℝ) • graphicalZonotope G) := by
  obtain ⟨z,hz,hy,hC,hT,hd,hgraph,hsum⟩:=admissible_threeTree_construction hn hG hA
  have hi : IntegerValued z := by
    rw [← zeta_mobius z]
    exact zeta_integerValued hy
  exact ⟨z,hz,hy,hi.basePolytope hz.1.1 hz.2.1,hz.minkowskiIndecomposable,
    hd,hgraph,fun C hc => hC C ((hG.maximalClique_iff C).mp hc),hT,hsum⟩

end GraphicalZonotopes
