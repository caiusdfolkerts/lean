module
public import consolidated.low_dimensional_rigid_covers
public import consolidated.actual_facet_hitting

set_option Elab.async false

section BundlePart0
/- Source: Papers/AllRigidCoverCases.lean -/




@[expose] public section
noncomputable section
namespace Papers.PolytopeFourRegularTail
open Set Finset Papers.Polytopes Papers.PolytopeVertexCone
open Papers.PolytopeSimpleTailFace
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {n : ℕ}

def PaperRigidCoverBound (n : ℕ) : ℕ := if n=3 then 3 else n-1

/-- The complete actual-polytope cover alternatives required in Section 8,
including simple polytopes and every dimension in the statement. -/
theorem all_actual_rigid_cover_cases
    (P : ConvexPolytope n) (hP : P.IsFullDim) (hn : 3≤n)
    (hcard : P.vertices.card≤4*n-5) :
    HasRigidCover P P.vertices (PaperRigidCoverBound n) ∨
      ((n=4 ∨ n=5) ∧ HasRigidBoundaryCover P (n-3)) ∨
      HasRigidSetContainingNonsimple P := by
  by_cases hn3 : n=3
  · subst n
    exact Or.inl (rigidCover_three_of_min_three_card_le_seven P P.vertices
      (Finset.Subset.refl _) hcard (full_min_degree P hP))
  have hn4 : 4≤n := by omega
  by_cases hnon : ∃x∈P.vertices,n+1≤(actualNeighbors P x).card
  · by_cases hn6 : 6≤n
    · apply Or.inl
      simpa only [PaperRigidCoverBound,if_neg hn3] using
        nonsimple_rigid_cover_dimension_ge_six P hP hn6 hcard hnon
    · have hcases : n=4 ∨ n=5 := by omega
      rcases hcases with rfl | rfl
      · rcases nonsimple_four_cover_cases P hP hcard hnon with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨Or.inl rfl,h⟩)
      · rcases nonsimple_five_cover_cases P hP hcard hnon with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨Or.inr rfl,h⟩)
        · exact Or.inr (Or.inr h)
  · have hsimple : ∀x∈P.vertices,(actualNeighbors P x).card=n := by
      intro x hx
      have hlo := intrinsic_dim_le_neighbor_card P hx
      rw [hP] at hlo
      have hhi : ¬n+1≤(actualNeighbors P x).card := fun h => hnon ⟨x,hx,h⟩
      omega
    obtain ⟨x,hx⟩ := P.vertices_nonempty
    have hpos : 0<(actualNeighbors P x).card := by rw [hsimple x hx];omega
    obtain ⟨y,hy⟩ := Finset.card_pos.mp hpos
    have hxy := (mem_actualNeighbors_iff P x y).mp hy
    refine Or.inr (Or.inr ⟨{x,y},?_,?_,rigid_pair hx hxy.1 hxy,?_⟩)
    · intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hxy.1
    · simp [hxy.2.1]
    · intro z hz hzR
      exact hsimple z hz

/-- The exceptional rigid-set alternative produces the literal geometric
Shephard facet, with at least two vertices outside it. -/
theorem HasRigidSetContainingNonsimple.shephard_facet
    {P : ConvexPolytope n} (hP : P.IsFullDim)
    (hR : HasRigidSetContainingNonsimple P)
    (f : E n→E n) (hf : ParallelOnTail P P.vertices f)
    (hnon : ¬∃a : ℝ,∃b : E n,∀x∈P.vertices,f x=a•x+b) :
    ∃F : Set (E n),P.IsFace F ∧ faceDim F+1=n ∧
      2≤(P.vertices.filter (fun x=>x∉F)).card ∧
      ∀v∈P.vertices,v∈F→((actualNeighbors P v).filter (fun y=>y∉F)).card=1 := by
  obtain ⟨R,hRsub,hRc,hRigid,hSimple⟩ := hR
  exact Papers.ActualFacetHitting.actual_shephard_facet_of_homothetic_set_containing_nonsimple
    P hP f hf R hRsub hRc (hRigid f hf) hSimple hnon

end Papers.PolytopeFourRegularTail

end
end
end BundlePart0

