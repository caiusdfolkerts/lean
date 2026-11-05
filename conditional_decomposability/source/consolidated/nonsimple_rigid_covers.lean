module
public import consolidated.four_tail_rigid_cover
public import consolidated.actual_rigid_five_seeds

set_option Elab.async false

section BundlePart0
/- Source: Papers/NonsimpleRigidCovers.lean -/




@[expose] public section
noncomputable section
namespace Papers.PolytopeFourRegularTail
open Set Finset Papers.Polytopes Papers.PolytopeVertexCone
open Papers.ActualRigidSeedLimits Papers.NeighborhoodCounts
open Papers.PolytopeSimpleTailFace
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators
variable {n : ℕ}

theorem full_min_degree (P : ConvexPolytope n) (hP : P.IsFullDim) :
    ∀x∈P.vertices,n≤(P.vertices.filter (GeneralVertexStep P x)).card := by
  intro x hx
  have h := intrinsic_dim_le_neighbor_card P hx
  rw [hP] at h
  exact h

/-- The entire high-dimensional rigid-cover conclusion of Section 8.2. -/
theorem nonsimple_rigid_cover_dimension_ge_six
    (P : ConvexPolytope n) (hP : P.IsFullDim) (hn : 6≤n)
    (hcard : P.vertices.card≤4*n-5)
    (hnonsimple : ∃x∈P.vertices,n+1≤(actualNeighbors P x).card) :
    HasRigidCover P P.vertices (n-1) := by
  have hmin := full_min_degree P hP
  obtain ⟨B,hBT,hBc,hBR⟩ := exists_rigid_five_of_nonsimple_min_large P P.vertices
    (Finset.Subset.refl _) n hn hcard hmin hnonsimple
  obtain ⟨A,hA⟩ := exists_largest_rigid P P.vertices
  have hAc : 5≤A.card := hBc.trans (hA.largest B hBT hBR)
  have hc := Finset.card_sdiff_add_card_eq_card hA.subset
  have hres := hA.residual_min_degree (Finset.Subset.refl _) (n-1) (by
    have he : n-1+1=n := Nat.sub_add_cancel (by omega)
    simpa only [he] using hmin)
  have hbudget := (TailDegreeBudget.full P).remove_largest (Finset.Subset.refl _) hA
  have hcover := rigidCover_of_tail_card_degree_budget P hP (n-1) (by omega)
    (P.vertices\A) Finset.sdiff_subset (by omega) hres 1 (by omega) hbudget
  have hall := hcover.adjoin hA.subset hA.rigid
  convert hall using 1 <;> omega

theorem four_regular_of_min_four_le_eleven_no_rigid_four
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T⊆P.vertices)
    (hcard : T.card≤11)
    (hmin : ∀x∈T,4≤(T.filter (GeneralVertexStep P x)).card)
    (hno : ∀A⊆T,A.card=4→¬RigidInTail P T A) :
    ∀x∈T,(T.filter (GeneralVertexStep P x)).card=4 := by
  let G := smallTailGraph P T hTV
  have hc : Fintype.card T≤11 := by simpa only [Fintype.card_coe] using hcard
  have hGmin (v : T) : 4≤G.degree v := by
    rw [smallTailGraph_degree_eq]
    exact hmin v.val v.property
  have hcap := common_neighbors_le_two_of_no_rigid_four P T hTV hno
  have hmatch := neighbor_matchings_of_no_rigid_four P T hTV hno
  intro x hx
  let v : T := ⟨x,hx⟩
  have hb := neighborhood_cut_bound G v 4 2 hGmin (hcap v)
  rw [outsideStar_card] at hb
  have hlt := G.degree_lt_card_verts v
  have hm := hGmin v
  have hs : (∑w∈G.neighborFinset v,localDegree G (G.neighborFinset v) w)≤G.degree v := by
    calc
      _≤∑w∈G.neighborFinset v,(1:ℕ) := Finset.sum_le_sum (hmatch v)
      _=_ := by simp
  have hreg : G.degree v=4 := by
    obtain ⟨e,he⟩ := Papers.NeighborhoodParity.sum_local_degrees_twice G (G.neighborFinset v)
    omega
  simpa only [G,smallTailGraph_degree_eq] using hreg

theorem exists_rigid_four_nonsimple_dimensions_four_five
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T⊆P.vertices)
    (k : ℕ) (hklo : 4≤k) (hkhi : k≤5) (hcard : T.card≤4*k-5)
    (hmin : ∀x∈T,k≤(T.filter (GeneralVertexStep P x)).card)
    (hnonsimple : ∃x∈T,k+1≤(T.filter (GeneralVertexStep P x)).card) :
    ∃A⊆T,4≤A.card ∧ RigidInTail P T A := by
  by_contra! hno
  have hno4 (A : Finset (E n)) (hAT : A⊆T) (hc : A.card=4) :
      ¬RigidInTail P T A := hno A hAT (by omega)
  obtain ⟨x,hx,hbig⟩ := hnonsimple
  by_cases hk4 : k=4
  · subst k
    have hreg := four_regular_of_min_four_le_eleven_no_rigid_four P T hTV
      hcard hmin hno4 x hx
    omega
  · have hk5 : k=5 := by omega
    subst k
    let G := smallTailGraph P T hTV
    let v : T := ⟨x,hx⟩
    have hGmin (w : T) : 5≤G.degree w := by
      rw [smallTailGraph_degree_eq]
      exact hmin w.val w.property
    have hcap := common_neighbors_le_two_of_no_rigid_four P T hTV hno4
    have hmatch := neighbor_matchings_of_no_rigid_four P T hTV hno4
    have hb := neighborhood_cut_bound G v 5 2 hGmin (hcap v)
    rw [outsideStar_card] at hb
    have hlt := G.degree_lt_card_verts v
    have hc : Fintype.card T≤15 := by simpa only [Fintype.card_coe] using hcard
    have hbigG : 6≤G.degree v := by
      rw [smallTailGraph_degree_eq]
      exact hbig
    have hs : (∑w∈G.neighborFinset v,localDegree G (G.neighborFinset v) w)≤G.degree v := by
      calc
        _≤∑w∈G.neighborFinset v,(1:ℕ) := Finset.sum_le_sum (hmatch v)
        _=_ := by simp
    omega

end Papers.PolytopeFourRegularTail

end
end
end BundlePart0

