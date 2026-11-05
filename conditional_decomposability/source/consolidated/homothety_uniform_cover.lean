module
public import consolidated.homothety_shared_central_impossible
public import consolidated.homothety_boundary_cover

set_option Elab.async false

section BundlePart0
/- Source: Papers/HomothetyUniformCover.lean -/




@[expose] public section

/-!
# The complete nonempty central-face case of the uniform cover theorem

The original vertex bound yields affine independence and the two central
cardinalities. The deficit case has a common parameter. In the zero
excess case, a new central homothety is treated by the proved fiber-row
and K₂,₃ arguments. A nonhomothetic central face must have four vertices
and dimension at most two; the dimension bound for its owning colors
then supplies the unowned class used for a Shephard facet.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ} {I : Type*} [Fintype I]

theorem uniform_zero_excess_homothetic_shephard
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y∈P.vertices,∃ j,f y=a j•y+b j)
    (hprivate : ∀ i,∃ x∈fullClass P f a b i,∀ j,f x=a j•x+b j→j=i)
    (hm : 4≤Fintype.card I) (hd : Fintype.card I+1≤d)
    (hN : P.vertices.card≤4*d-5)
    (hs : (centralVertices P a b).card=finrank ℝ (parameterDirectionSpan a b))
    (hH : HomotheticOn f (centralVertices P a b : Set (E d))) :
    HasShephardProperty P := by
  obtain ⟨hind,htm,ht,hr,hbudget,i,hi⟩ :=
    uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
  have hmin := uniform_zero_excess P hP f hf a b hcover hprivate hm hd hN hs
  obtain ⟨α,c,hH⟩ := hH
  by_cases hold : ∃ j,(α,c)=parameterVector a b j
  · obtain ⟨j,hj⟩ := hold
    apply uniform_zero_excess_common_parameter_shephard P hP f hf a b hcover hprivate
      hm hd hN hs j
    have hα := congrArg Prod.fst hj
    have hc := congrArg Prod.snd hj
    change α = a j at hα
    change c = b j at hc
    intro z hz
    simpa only [hα,hc] using hH z hz
  have hnew : ∀j,(α,c)≠parameterVector a b j := fun j he=>hold ⟨j,he⟩
  have hunique := central_ownership_unique_of_new_homothety P f a b hH hnew
  have hsingle : ∀ z∈centralVertices P a b,(owners f a b z).card≤1 := by
    intro z hz
    by_contra hn
    obtain ⟨j,hj,k,hk,hjk⟩ := Finset.one_lt_card.mp (by omega : 1<(owners f a b z).card)
    exact shared_central_impossible_of_unique_ownership P hP f hf a b hind hcover
      hmin (by omega) hm hunique hz hjk
      (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
  obtain ⟨j,hj⟩ := exists_unowned_class_of_central_count P f a b (by omega) hsingle
  exact unowned_minimum_unique_central_shephard P hP f hf hnon a b hind hcover
    j hj hmin (by omega) ht hunique

theorem uniform_zero_excess_nonhomothetic_shephard
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y∈P.vertices,∃ j,f y=a j•y+b j)
    (hprivate : ∀ i,∃ x∈fullClass P f a b i,∀ j,f x=a j•x+b j→j=i)
    (hm : 4≤Fintype.card I) (hd : Fintype.card I+1≤d)
    (hN : P.vertices.card≤4*d-5)
    (hs : (centralVertices P a b).card=finrank ℝ (parameterDirectionSpan a b))
    (hF : P.IsFace (centralSection P a b))
    (hnot : ¬HomotheticOn f (centralVertices P a b : Set (E d))) :
    HasShephardProperty P := by
  obtain ⟨hind,htm,ht,hr,hbudget,i,hi⟩ :=
    uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
  have hmin := uniform_zero_excess P hP f hf a b hcover hprivate hm hd hN hs
  have hdeg (z : E d) (hz : z∈centralVertices P a b) :
      finrank ℝ (parameterDirectionSpan a b)-2≤
        (faceNeighbors P (centralSection P a b) z).card := by
    have hh := uniform_zero_excess_degree_owners P hP f hf a b hcover hprivate hm hd hN hs hz
    have ho := owners_card_le_two f a b hind z
    omega
  have ht4 : finrank ℝ (parameterDirectionSpan a b)=4 := by
    have htupper : finrank ℝ (parameterDirectionSpan a b)≤4 := by
      by_contra hn
      apply hnot
      apply homotheticOn_of_vertexSubset_degree P f hf (centralVertices P a b)
        (Finset.filter_subset _ _) (k:=finrank ℝ (parameterDirectionSpan a b)-2)
      · intro z hz
        rw [←central_neighbors_eq_filter]
        exact hdeg z hz
      · omega
    by_contra hn
    have ht3 : finrank ℝ (parameterDirectionSpan a b)=3 := by omega
    exact hnot (central_three_homothetic P f hf a b hF (hs.trans ht3))
  have hm5 : Fintype.card I=5 := by omega
  have hdim : faceDim (centralSection P a b)≤2 :=
    central_nonhomothetic_dim_le_two_of_card_le_five P f hf a b hF (by omega) hnot
  have hne : (centralVertices P a b).Nonempty := Finset.card_pos.mp (by omega)
  have howners := centralOwners_card_le_faceDim_add_two P f hf a b hind hcover hF hne
  obtain ⟨j,hj⟩ : ∃ j,j∉centralOwners P f a b := by
    by_contra hn
    push_neg at hn
    have he := Finset.eq_univ_iff_forall.mpr hn
    rw [he,Finset.card_univ,hm5] at howners
    omega
  have hunowned : ∀ z∈centralVertices P a b,f z≠a j•z+b j := by
    intro z hz hzj
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,z,hz,hzj⟩)
  have hshared : ∀ z∈centralVertices P a b,2≤(owners f a b z).card := by
    intro z hz
    have hlow := uniform_zero_excess_degree_owners P hP f hf a b hcover hprivate hm hd hN hs hz
    have hhigh := faceNeighbors_card_le_two_of_dim_le_two P (centralSection P a b) hdim
      (Finset.mem_filter.mp hz).1
      ⟨subset_convexHull ℝ _ (Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2⟩
    omega
  obtain ⟨h,hh⟩ := Finset.card_pos.mp (show 0<((Finset.univ : Finset I).erase j).card by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ,hm5]
    omega)
  have hjh : j≠h := (Finset.mem_erase.mp hh).1.symm
  exact unowned_minimum_shared_central_shephard P hP f hf a b hind hcover hjh hunowned
    (hmin j) (by omega) (fun k _=>hmin k) hshared

/-- Proposition12, with the nonempty central-face alternative fully
resolved from the original uniform hypotheses. -/
theorem uniform_nonempty_central_shephard
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y∈P.vertices,∃ j,f y=a j•y+b j)
    (hprivate : ∀ i,∃ x∈fullClass P f a b i,∀ j,f x=a j•x+b j→j=i)
    (hm : 4≤Fintype.card I) (hd : Fintype.card I+1≤d)
    (hN : P.vertices.card≤4*d-5)
    (hne : (centralVertices P a b).Nonempty) : HasShephardProperty P := by
  rcases uniform_central_vertex_count P hP f hf a b hcover hprivate hm hd hN hne with hs|hs
  · exact uniform_central_deficit_one_shephard P hP f hf a b hcover hprivate hm hd hN hs
  · by_cases hH : HomotheticOn f (centralVertices P a b : Set (E d))
    · exact uniform_zero_excess_homothetic_shephard P hP f hf hnon a b
        hcover hprivate hm hd hN hs hH
    · obtain ⟨hind,htm,ht,hr,hbudget,i,hi⟩ :=
        uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
      obtain ⟨B,hB,hclique,hpos,hfacets,hfibers,hinter,hF⟩ :=
        minimumClass_fiber_faces P hP f hf a b hcover hprivate i (by omega) hi
      rcases hF with hF|hF
      · obtain ⟨z,hz⟩ := hne
        have hzF : z∈centralSection P a b :=
          ⟨subset_convexHull ℝ _ (Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2⟩
        rw [hF] at hzF
        exact hzF.elim
      · exact uniform_zero_excess_nonhomothetic_shephard P hP f hf a b
          hcover hprivate hm hd hN hs hF hH

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart0

