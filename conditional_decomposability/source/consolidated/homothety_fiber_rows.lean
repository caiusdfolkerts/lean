module
public import consolidated.dense_cone_rigidity

set_option Elab.async false

section BundlePart0
/- Source: Papers/HomothetyFiberRows.lean -/




@[expose] public section

/-!
# Actual rows of the minimum-class fiber faces

The rows below are constructed from actual crossing edges. Equal class
sizes turn the injective crossing maps into bijections. The quotient
basis proves that these bijections place exactly one vertex of each
class in each fiber and that the row is precisely the complement of a
coordinate facet.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ} {I : Type*} [Fintype I]

theorem crossing_target_mem_fiber
    (P : ConvexPolytope d) (f : E d → E d) (hf : IsParallelMap P f)
    (a : I → ℝ) (b : I → E d)
    (hinj : Function.Injective (parameterVector a b))
    {i j : I} {x y : E d} (hx : x ∈ noncentralClass P f a b i)
    (hy : y ∈ fullClass P f a b j) (hji : j ≠ i)
    (hxy : GeneralVertexStep P x y) : y ∈ parameterFiber P a b x := by
  have hxP := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hxi := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hyj := (Finset.mem_filter.mp hy).2
  obtain ⟨μ, hμ⟩ := hf x hxP y hxy.1 hxy
  have hc := edge_target_scale_ne_zero f a b
    (noncentral_not_other_parameter P f a b hinj hx hji) hyj hμ
  let D := parameterDirectionSpan a b
  let M := D ⊔ Submodule.span ℝ {vertexVector x}
  have hp : parameterVector a b j - parameterVector a b i ∈ D :=
    Submodule.subset_span (Set.mem_range_self (j,i))
  have hxM : vertexVector x ∈ M :=
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  have hyM : (a j - μ) • vertexVector y ∈ M := by
    have hh := M.add_mem (Submodule.mem_sup_left hp) (M.smul_mem (a i-μ) hxM)
    rw [edge_parameter_identity f a b hxi hyj hμ] at hh
    simpa only [sub_add_cancel] using hh
  refine ⟨subset_convexHull ℝ _ hxy.1, ?_⟩
  have hh := M.smul_mem (a j-μ)⁻¹ hyM
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

structure MinimumRows (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) (i : I) where
  basis : Basis (noncentralClass P f a b i) ℝ
    ((ℝ × E d) ⧸ parameterDirectionSpan a b)
  basis_points : ∀ u, basis u = quotientVertex a b u.val
  point : noncentralClass P f a b i → I → E d
  class_mem : ∀ u j, point u j ∈ noncentralClass P f a b j
  source : ∀ u, point u i = u.val
  crossing : ∀ u j, j ≠ i → GeneralVertexStep P u.val (point u j)
  onto : ∀ j, ∀ x ∈ noncentralClass P f a b j, ∃ u, point u j = x

theorem exists_minimumRows
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (i : I) (hunowned : ∀ z ∈ centralVertices P a b, f z ≠ a i • z + b i)
    (hmin : ∀ j, (noncentralClass P f a b j).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hr : 2 ≤ d + 1 - finrank ℝ (parameterDirectionSpan a b)) :
    Nonempty (MinimumRows P f a b i) := by
  have hsize : 2 ≤ (noncentralClass P f a b i).card := by rw [hmin]; exact hr
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega :
    0 < (noncentralClass P f a b i).card)
  obtain ⟨B, hB⟩ := exists_classQuotientBasis P hP f hf a b hcover i
    (Finset.mem_filter.mp hx).1 (noncentral_vertex_private P f a b hind.injective hx) (hmin i)
  have hex (j : I) : ∃ M : noncentralClass P f a b i → noncentralClass P f a b j,
      Function.Bijective M ∧ (∀ u, j = i → (M u).val = u.val) ∧
      (∀ u, j ≠ i → GeneralVertexStep P u.val (M u).val) := by
    by_cases hji : j = i
    · subst j
      exact ⟨id, Function.bijective_id, fun _ _ => rfl, fun _ h => (h rfl).elim⟩
    obtain ⟨M, hM, hedge⟩ := exists_unowned_class_crossing_matching
      P hP f hf a b hind hcover hunowned hji (hmin i) hsize
    refine ⟨M, (Fintype.bijective_iff_injective_and_card M).mpr ⟨hM, ?_⟩,
      fun _ h => (hji h).elim, fun u _ => hedge u⟩
    rw [Fintype.card_coe, Fintype.card_coe, hmin i, hmin j]
  choose M hbij hsource hcross using hex
  refine ⟨⟨B, hB, (fun u j => (M j u).val), (fun u j => (M j u).property),
    (fun u => hsource i u rfl), (fun u j hj => hcross j u hj), ?_⟩⟩
  intro j x hx
  obtain ⟨u, hu⟩ := (hbij j).2 ⟨x,hx⟩
  exact ⟨u, congrArg Subtype.val hu⟩

namespace MinimumRows
variable {P : ConvexPolytope d} {f : E d → E d} {a : I → ℝ} {b : I → E d}
    {i : I} (R : MinimumRows P f a b i)

def row (u : noncentralClass P f a b i) : Finset (E d) :=
  Finset.univ.image (R.point u)

theorem point_vertex (u : noncentralClass P f a b i) (j : I) : R.point u j ∈ P.vertices :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp (R.class_mem u j)).1).1

theorem point_injective (hinj : Function.Injective (parameterVector a b))
    (u : noncentralClass P f a b i) : Function.Injective (R.point u) := by
  intro j k hjk
  have hj := R.class_mem u j
  have hk := R.class_mem u k
  have hxk := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
  have he := noncentral_vertex_private P f a b hinj hj k (hjk ▸ hxk)
  exact he.symm

theorem row_card (hinj : Function.Injective (parameterVector a b))
    (u : noncentralClass P f a b i) : (R.row u).card = Fintype.card I := by
  rw [row, Finset.card_image_of_injective _ (R.point_injective hinj u), Finset.card_univ]

theorem row_subset_vertices (u : noncentralClass P f a b i) : R.row u ⊆ P.vertices := by
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact R.point_vertex u j

theorem source_mem_row (u : noncentralClass P f a b i) : u.val ∈ R.row u := by
  rw [← R.source u]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

theorem point_fiber (hf : IsParallelMap P f)
    (hinj : Function.Injective (parameterVector a b))
    (u : noncentralClass P f a b i) (j : I) :
    R.point u j ∈ parameterFiber P a b u.val := by
  by_cases hji : j = i
  · rw [hji, R.source u]
    exact ⟨subset_convexHull ℝ _
      (Finset.mem_filter.mp (Finset.mem_filter.mp u.property).1).1,
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))⟩
  exact crossing_target_mem_fiber P f hf a b hinj u.property
    (Finset.mem_filter.mp (R.class_mem u j)).1 hji (R.crossing u j hji)

theorem point_unique_in_fiber (hf : IsParallelMap P f)
    (hinj : Function.Injective (parameterVector a b))
    (u : noncentralClass P f a b i) (j : I) {x : E d}
    (hx : x ∈ noncentralClass P f a b j) (hxF : x ∈ parameterFiber P a b u.val) :
    R.point u j = x := by
  obtain ⟨v, hv⟩ := R.onto j x hx
  by_cases hvu : v = u
  · simpa only [hvu] using hv
  have hxV : x ∈ parameterFiber P a b v.val := hv ▸ R.point_fiber hf hinj v j
  have hcentral : x ∈ centralSection P a b := by
    rw [← fiber_inter_eq_central P f a b i R.basis R.basis_points v u hvu]
    exact ⟨hxV,hxF⟩
  exact ((Finset.mem_filter.mp hx).2 hcentral.2).elim

theorem fiber_vertex_iff (hf : IsParallelMap P f)
    (hinj : Function.Injective (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (u : noncentralClass P f a b i) {x : E d} (hx : x ∈ P.vertices) :
    x ∈ parameterFiber P a b u.val ↔
      x ∈ centralVertices P a b ∨ x ∈ R.row u := by
  constructor
  · intro hxF
    by_cases hxD : vertexVector x ∈ parameterDirectionSpan a b
    · exact Or.inl (Finset.mem_filter.mpr ⟨hx,hxD⟩)
    obtain ⟨j,hxj⟩ := hcover x hx
    have hxU : x ∈ noncentralClass P f a b j :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hx,hxj⟩,hxD⟩
    exact Or.inr (Finset.mem_image.mpr
      ⟨j,Finset.mem_univ j,R.point_unique_in_fiber hf hinj u j hxU hxF⟩)
  · rintro (hxC | hxR)
    · exact ⟨subset_convexHull ℝ _ hx,
        Submodule.mem_sup_left (Finset.mem_filter.mp hxC).2⟩
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hxR
      exact R.point_fiber hf hinj u j

theorem row_coordinate_facet_complement (hf : IsParallelMap P f)
    (hinj : Function.Injective (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (u : noncentralClass P f a b i) :
    (R.row u : Set (E d)) = (P.vertices : Set (E d)) \
      affineZeroFace P (homogeneousForm (quotientCoordinate (parameterDirectionSpan a b) R.basis u)) := by
  ext x
  let g := homogeneousForm (quotientCoordinate (parameterDirectionSpan a b) R.basis u)
  constructor
  · intro hxR
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hxR
    refine ⟨R.point_vertex u j, ?_⟩
    intro hxF
    have hxzero : quotientCoordinate (parameterDirectionSpan a b) R.basis u
        (vertexVector (R.point u j)) = 0 := by
      rw [← homogeneousForm_apply]
      exact hxF.2
    have hcoords := (mem_fiber_iff_coordinates_zero P f a b i R.basis
      R.basis_points u (R.point u j)).mp (R.point_fiber hf hinj u j)
    have hc : R.point u j ∈ centralSection P a b := by
      apply (mem_central_iff_coordinates_zero P f a b i R.basis (R.point u j)).mpr
      refine ⟨hcoords.1, ?_⟩
      intro q
      by_cases hqu : q = u
      · simpa only [hqu] using hxzero
      · exact hcoords.2 q hqu
    exact (Finset.mem_filter.mp (R.class_mem u j)).2 hc.2
  · rintro ⟨hxP,hxF⟩
    have hxD : vertexVector x ∉ parameterDirectionSpan a b := by
      intro hxD
      apply hxF
      refine ⟨subset_convexHull ℝ _ hxP, ?_⟩
      rw [homogeneousForm_apply]
      exact quotientCoordinate_central P f a b i R.basis u hxD
    obtain ⟨j,hxj⟩ := hcover x hxP
    have hxU : x ∈ noncentralClass P f a b j :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxP,hxj⟩,hxD⟩
    obtain ⟨v,hv⟩ := R.onto j x hxU
    have hvu : v = u := by
      by_contra hvu
      apply hxF
      refine ⟨subset_convexHull ℝ _ hxP, ?_⟩
      rw [homogeneousForm_apply]
      have hxV : x ∈ parameterFiber P a b v.val := hv ▸ R.point_fiber hf hinj v j
      exact ((mem_fiber_iff_coordinates_zero P f a b i R.basis
        R.basis_points v x).mp hxV).2 u (Ne.symm hvu)
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,by simpa only [hvu] using hv⟩

theorem row_min_degree
    (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hinj : Function.Injective (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    (hmin : (noncentralClass P f a b i).card =
      d+1-finrank ℝ (parameterDirectionSpan a b))
    (hunique : ∀ j, ∀ z ∈ centralVertices P a b, ∀ w ∈ centralVertices P a b,
      f z = a j • z+b j → f w = a j • w+b j → z=w)
    (u : noncentralClass P f a b i) :
    ∀ x ∈ R.row u, finrank ℝ (parameterDirectionSpan a b)-1 ≤
      ((R.row u).filter (GeneralVertexStep P x)).card := by
  intro x hx
  obtain ⟨j,_,hxj⟩ := Finset.mem_image.mp hx
  have hxU : x ∈ noncentralClass P f a b j := hxj ▸ R.class_mem u j
  have hxP := R.row_subset_vertices u hx
  have hxF := (R.fiber_vertex_iff hf hinj hcover u hxP).mpr (Or.inr hx)
  have hF := fiber_isFace P f a b i R.basis R.basis_points hf hcover hinj hsize u
  have hdF := fiber_dimension P f a b i R.basis R.basis_points hP hf hcover
    hinj hsize hmin u
  let C := (centralVertices P a b).filter (GeneralVertexStep P x)
  have hC : C.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz w hw
    obtain ⟨hzC,hxz⟩ := Finset.mem_filter.mp hz
    obtain ⟨hwC,hxw⟩ := Finset.mem_filter.mp hw
    have hzj := central_edge_owner P f hf a b hcover
      (Finset.mem_filter.mp hzC).1 (Finset.mem_filter.mp hzC).2
      (Finset.mem_filter.mp hxU).2 (generalVertexStep_symm hxP hxz)
      (Finset.mem_filter.mp (Finset.mem_filter.mp hxU).1).2
    have hwj := central_edge_owner P f hf a b hcover
      (Finset.mem_filter.mp hwC).1 (Finset.mem_filter.mp hwC).2
      (Finset.mem_filter.mp hxU).2 (generalVertexStep_symm hxP hxw)
      (Finset.mem_filter.mp (Finset.mem_filter.mp hxU).1).2
    exact hunique j z hzC w hwC hzj hwj
  have hsub : faceNeighbors P (parameterFiber P a b u.val) x ⊆
      ((R.row u).filter (GeneralVertexStep P x)) ∪ C := by
    intro y hy
    obtain ⟨hyP,hyF,hxy⟩ := Finset.mem_filter.mp hy
    rcases (R.fiber_vertex_iff hf hinj hcover u hyP).mp hyF with hyC | hyR
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hyC,hxy⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyR,hxy⟩)
  have hlow := faceDim_le_faceNeighbors_card P hF hxP hxF
  rw [hdF] at hlow
  have hhigh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

theorem row_rigid
    (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y+b j)
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    (hmin : (noncentralClass P f a b i).card =
      d+1-finrank ℝ (parameterDirectionSpan a b))
    (ht : 3 ≤ finrank ℝ (parameterDirectionSpan a b))
    (hunique : ∀ j, ∀ z ∈ centralVertices P a b, ∀ w ∈ centralVertices P a b,
      f z = a j • z+b j → f w = a j • w+b j → z=w)
    (u : noncentralClass P f a b i) :
    Papers.PolytopeFourRegularTail.RigidInTail P (R.row u) (R.row u) := by
  letI : Nonempty I := ⟨i⟩
  have htm : finrank ℝ (parameterDirectionSpan a b)+1=Fintype.card I := by
    rw [parameterDirectionSpan_eq_vectorSpan]
    exact hind.finrank_vectorSpan_add_one
  apply Papers.PolytopeFourRegularTail.rigid_of_universal_vertex_dense
    P (R.row u) (R.row_subset_vertices u)
    (finrank ℝ (parameterDirectionSpan a b)) ht
    (by rw [R.row_card hind.injective u,htm])
    (R.row_min_degree hP hf hind.injective hcover hsize hmin hunique u)
    (R.source_mem_row u)
  intro x hx hxu
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
  have hji : j ≠ i := by intro he; exact hxu (he ▸ R.source u)
  exact R.crossing u j hji


end MinimumRows
/-- A new central homothety makes each old color own at most one central
vertex, by uniqueness of a homothety at two distinct points. -/
theorem central_ownership_unique_of_new_homothety
    (P : ConvexPolytope d) (f : E d → E d) (a : I → ℝ) (b : I → E d)
    {α : ℝ} {c : E d}
    (hH : ∀ z ∈ centralVertices P a b, f z = α • z+c)
    (hnew : ∀ j, (α,c) ≠ parameterVector a b j) :
    ∀ j, ∀ z ∈ centralVertices P a b, ∀ w ∈ centralVertices P a b,
      f z = a j • z+b j → f w = a j • w+b j → z=w := by
  intro j z hz w hw hzj hwj
  by_contra hzw
  exact hnew j (homothety_parameters_eq_of_two_points hzw
    ((hH z hz).symm.trans hzj) ((hH w hw).symm.trans hwj))

/-- The complete no-shared-vertex branch of the new central homothety
argument. All rows, supporting facets and graph rigidity are derived. -/
theorem unowned_minimum_unique_central_shephard
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f)
    (hnon : ¬IsHomothetyOnVertices P f)
    (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y+b j)
    (i : I) (hunowned : ∀ z ∈ centralVertices P a b, f z ≠ a i • z+b i)
    (hmin : ∀ j, (noncentralClass P f a b j).card =
      d+1-finrank ℝ (parameterDirectionSpan a b))
    (hr : 2 ≤ d+1-finrank ℝ (parameterDirectionSpan a b))
    (ht : 3 ≤ finrank ℝ (parameterDirectionSpan a b))
    (hunique : ∀ j, ∀ z ∈ centralVertices P a b, ∀ w ∈ centralVertices P a b,
      f z = a j • z+b j → f w = a j • w+b j → z=w) :
    HasShephardProperty P := by
  obtain ⟨R⟩ := exists_minimumRows P hP f hf a b hind hcover i hunowned hmin hr
  have hsize : 2 ≤ (noncentralClass P f a b i).card := by rw [hmin]; exact hr
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega :
    0<(noncentralClass P f a b i).card)
  let u : noncentralClass P f a b i := ⟨x,hx⟩
  let F := affineZeroFace P
    (homogeneousForm (quotientCoordinate (parameterDirectionSpan a b) R.basis u))
  have hF : IsFacet P F := minimumClass_coordinate_facet P f a b i R.basis
    R.basis_points hP hf hcover hind.injective hsize u
  have hrigid := R.row_rigid hP hf hind hcover hsize (hmin i) ht hunique u
  have hH : HomotheticOn f ((P.vertices : Set (E d)) \ F) := by
    rw [←R.row_coordinate_facet_complement hf hind.injective hcover u]
    exact hrigid f (fun x hx y hy hxy =>
      hf x (R.row_subset_vertices u hx) y (R.row_subset_vertices u hy) hxy)
  exact ⟨F,hF,facet_shephard_of_parallel_complement P hP f hf hnon hF hH⟩


end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart0

