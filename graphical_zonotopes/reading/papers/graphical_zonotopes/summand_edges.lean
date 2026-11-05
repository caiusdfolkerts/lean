module

public import Papers.GraphicalZonotopes.ZonotopeEdges
public import Papers.MinkowskiEdges

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An actual exposed edge of a graphical-zonotope summand has one of the
graph's standard-root directions. The complementary summand is an arbitrary
set, and the finite-hull representation of the base polytope is proved earlier. -/
theorem basePolytope_summand_exposed_edge {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) (G : SimpleGraph V)
    {k : ℝ} (hk : 0 ≤ k) (R : Set (V → ℝ))
    (hsum : basePolytope z + R = k • graphicalZonotope G)
    {p q : V → ℝ} (hex : IsExposedSegment (basePolytope z) p q) :
    ∃ u v, G.Adj u v ∧ ∃ t : ℝ, t ≠ 0 ∧
      q-p = t • (basisVector v-basisVector u) := by
  classical
  let f : SetFunction V := k • graphFunction G
  have hfn : Normalized f := by
    change k * graphFunction G ∅ = 0
    rw [graphFunction_normalized,mul_zero]
  have hfs : Supermodular f := (graphFunction_supermodular G).smul hk
  let s : Finset (V → ℝ) := (greedyPoints_finite z).toFinset
  let t : Finset (V → ℝ) := (greedyPoints_finite f).toFinset
  have hsbody : convexHull ℝ (s : Set (V → ℝ)) = basePolytope z := by
    simpa only [s,Set.Finite.coe_toFinset] using (basePolytope_eq_convexHull hn hs).symm
  have htbody : convexHull ℝ (t : Set (V → ℝ)) = k • graphicalZonotope G := by
    calc
      convexHull ℝ (t : Set (V → ℝ)) = basePolytope f := by
        simpa only [t,Set.Finite.coe_toFinset] using (basePolytope_eq_convexHull hfn hfs).symm
      _ = k • graphicalZonotope G := by
        change basePolytope (k • graphFunction G) = _
        rw [basePolytope_smul (graphFunction_normalized G)
          (graphFunction_supermodular G) hk,baseGraphFunction_eq_graphicalZonotope]
  have ht : t.Nonempty := by
    refine ⟨greedyPoint f (Fintype.equivFin V).symm,?_⟩
    change _ ∈ (greedyPoints_finite f).toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨(Fintype.equivFin V).symm,rfl⟩
  obtain ⟨hpq,l,a,hbound,hface⟩ := hex
  let L : (V → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap l
  have hsum' : convexHull ℝ (t : Set (V → ℝ)) =
      convexHull ℝ (s : Set (V → ℝ)) + R := by
    rw [hsbody,htbody]
    exact hsum.symm
  have hex' : Papers.Geometry.ExposesSegment (convexHull ℝ (s : Set (V → ℝ))) L a p q := by
    rw [hsbody]
    exact ⟨hbound,hface⟩
  obtain ⟨x,y,hxy,⟨L',b,hxyface⟩,c,hc,hxyparallel⟩ :=
    Papers.Geometry.minkowski_summand_exposed_edge_direction s t ht R hsum' hpq L a hex'
  have hxy' : IsExposedSegment (k • graphicalZonotope G) x y := by
    refine ⟨hxy,L'.toLinearMap,b,?_⟩
    simpa only [Papers.Geometry.ExposesSegment,htbody,ContinuousLinearMap.coe_coe] using hxyface
  obtain ⟨u,v,huv,d,hd,he⟩ := graphical_zonotope_exposed_edge G k hxy'
  refine ⟨u,v,huv,c⁻¹*d,mul_ne_zero (inv_ne_zero hc) hd,?_⟩
  calc
    q-p = c⁻¹ • (c • (q-p)) := by simp [smul_smul,hc]
    _ = c⁻¹ • (y-x) := by rw [hxyparallel]
    _ = c⁻¹ • (d • (basisVector v-basisVector u)) := by rw [he]
    _ = (c⁻¹*d) • (basisVector v-basisVector u) := by rw [smul_smul]

theorem basePolytope_summand_actualRootEdge {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) (G : SimpleGraph V)
    {k : ℝ} (hk : 0 ≤ k) (R : Set (V → ℝ))
    (hsum : basePolytope z + R = k • graphicalZonotope G)
    {u v : V} (h : ActualRootEdge (basePolytope z) u v) : G.Adj u v := by
  obtain ⟨huv,p,q,hex,c,hc,hpq⟩ := h
  obtain ⟨a,b,hab,d,hd,he⟩ := basePolytope_summand_exposed_edge hn hs G hk R hsum hex
  exact adjacency_of_root_parallel G huv (G.adj_symm hab) hc (hpq.symm.trans he)

end GraphicalZonotopes
