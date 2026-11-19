module

public import Papers.GraphicalZonotopes.OptimalK5FreeWitnesses
public import Papers.GraphicalZonotopes.UnitLatticeClassification
public import Papers.GraphicalZonotopes.UnitLatticeDilation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise

/-- Corollary 9.12: exact attainment and the universal lower bound for every
K5-free ambient graph, all n≥4, and every positive real dilation. -/
theorem optimal_k5_free_dilation : Targets.OptimalK5FreeDilation := by
  intro n hn
  refine ⟨optimal_k5_free_dilation_attained hn,?_⟩
  intro G hG a ha hsum
  obtain ⟨Q,hQ,hi,hd,hs⟩ := hsum
  by_cases hn8 : n≤8
  · simpa only [if_pos hn8] using
      UnitLatticeDilation.dilation_at_least_one (by omega : 2≤n) hQ hi.1 hd ha hs
  · rw [if_neg hn8]
    by_contra hn2
    have ha2 : a<2 := lt_of_not_ge hn2
    have hunit := UnitLatticeDilation.unit_summand_of_lt_two hQ hi.1 ha ha2 hs
    exact hn8 (unit_lattice_classification n hn G hG Q hQ hi hd hunit).2.1

/-- The universal bound in the ordinary polytopal convention. The actual
summand equation supplies the generalized-permutahedron presentation needed
for the equivalence of the two indecomposability conventions. -/
theorem optimal_k5_free_dilation_lower_bound_polytopal {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 5) {a : ℝ} (ha : 0<a)
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    (if n≤8 then (1 : ℝ) else 2)≤a := by
  obtain ⟨R,hR,hRc,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,_,_⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hRc hnR ha.le he
  have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hfn,hfs,hbody⟩
  have hi' : MinkowskiIndecomposable Q :=
    (minkowskiIndecomposable_iff_polytopal hgp).mpr hi
  exact (optimal_k5_free_dilation n hn).2 G hG a ha
    ⟨Q,hQ,hi',hd,⟨R,hR,hRc,hnR,he⟩⟩

end GraphicalZonotopes
