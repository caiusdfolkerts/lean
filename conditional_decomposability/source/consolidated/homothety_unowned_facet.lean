module
public import consolidated.homothety_unowned_class
public import Mathlib.Data.Fintype.EquivFin

set_option Elab.async false

section BundlePart0
/- Source: Papers/HomothetyUnownedFacet.lean -/




@[expose] public section

/-!
# A facet from an unowned minimum class

The supporting facet omits one color. If all other noncentral classes
are minimum classes and every central vertex has two owners, its
vertices are exactly those outside the omitted full class. Each of
these vertices has one exterior neighbor, giving Shephard's property.
Every matching and every supporting functional is constructed from the
actual edge graph and actual facets of the polytope.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ} {I : Type*}

theorem exists_unowned_supporting_facet [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    {i h : I} (hih : i ≠ h)
    (hunowned : ∀ z ∈ centralVertices P a b, f z ≠ a i • z + b i)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card) :
    ∃ (g : E d →ᵃ[ℝ] ℝ) (L : (ℝ × E d) →ₗ[ℝ] ℝ),
      IsFacet P (affineZeroFace P g) ∧
      (∀ y, L (vertexVector y) = g y) ∧
      (∀ y ∈ P.toSet, 0 ≤ g y) ∧
      (∀ u ∈ noncentralClass P f a b i, g u = 0) ∧
      (∀ j, j ≠ h → L (parameterVector a b j - parameterVector a b i) = 0) ∧
      L (parameterVector a b h - parameterVector a b i) ≠ 0 ∧
      ∃ w ∈ P.vertices, 0 < g w := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega :
    0 < (noncentralClass P f a b i).card)
  have hxP := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  let v : VertexType P := ⟨x, hxP⟩
  have hs : IsSimpleVertex P v := unowned_minimumClass_simple P hP f hf
    a b hind hcover hunowned hmin hsize hx
  obtain ⟨w, ⟨hwh, hxw⟩, _⟩ := unowned_minimumClass_other_neighbor
    P hP f hf a b hind hcover hunowned hmin hsize hx h hih.symm
  let widx : NeighborIndex P v :=
    ⟨⟨w, hxw.1⟩, (adj_iff_generalVertexStep P v ⟨w, hxw.1⟩).mpr hxw⟩
  let g := simpleFacetForm P hP v hs widx
  let L := (Papers.AffineCoordinates.affineLift g).comp
    signedHomogeneousEquiv.symm.toLinearMap
  have hL (y : E d) : L (vertexVector y) = g y := by
    change Papers.AffineCoordinates.homogeneousEvaluation (-(-y), (1 : ℝ)) g = g y
    rw [neg_neg, Papers.AffineCoordinates.homogeneousEvaluation_homogenize]
  have hxg : g x = 0 := simpleFacetForm_at_vertex P hP v hs widx
  have hwg : g w = 1 := by
    exact (simpleFacetForm_at_neighbor P hP v hs widx widx).trans (if_pos rfl)
  have hzero_neighbor {y : E d} (hxy : GeneralVertexStep P x y)
      (hyw : y ≠ w) : g y = 0 := by
    let yidx : NeighborIndex P v :=
      ⟨⟨y, hxy.1⟩, (adj_iff_generalVertexStep P v ⟨y, hxy.1⟩).mpr hxy⟩
    have hwiy : widx ≠ yidx := by
      intro he
      exact hyw (congrArg (fun z : NeighborIndex P v => z.val.val) he).symm
    exact (simpleFacetForm_at_neighbor P hP v hs widx yidx).trans (if_neg hwiy)
  obtain ⟨B, hB⟩ := exists_classQuotientBasis P hP f hf a b hcover i
    (Finset.mem_filter.mp hx).1 (noncentral_vertex_private P f a b hind.injective hx) hmin
  have hclique := minimumClass_clique P f a b i B hB hf hcover hind.injective
  have hAi (u : E d) (hu : u ∈ noncentralClass P f a b i) : g u = 0 := by
    by_cases hux : u = x
    · simpa only [hux] using hxg
    have hxu : GeneralVertexStep P x u :=
      hclique ⟨x, hx⟩ ⟨u, hu⟩ (fun he => hux
        (congrArg Subtype.val he).symm)
    apply hzero_neighbor hxu
    intro huw
    exact noncentral_not_other_parameter P f a b hind.injective hu hih.symm
      (huw.symm ▸ (Finset.mem_filter.mp (Finset.mem_filter.mp hwh).1).2)
  have hother (j : I) (hjh : j ≠ h) :
      L (parameterVector a b j - parameterVector a b i) = 0 := by
    by_cases hji : j = i
    · rw [hji, sub_self, map_zero]
    obtain ⟨y, ⟨hy, hxy⟩, _⟩ := unowned_minimumClass_other_neighbor
      P hP f hf a b hind hcover hunowned hmin hsize hx j hji
    have hyw : y ≠ w := by
      intro hyw
      exact noncentral_not_other_parameter P f a b hind.injective hy hjh.symm
        (hyw.symm ▸ (Finset.mem_filter.mp (Finset.mem_filter.mp hwh).1).2)
    have hyg := hzero_neighbor hxy hyw
    obtain ⟨μ, hμ⟩ := hf x hxP y hxy.1 hxy
    rw [edge_parameter_identity f a b
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2 hμ,
      map_sub, map_smul, map_smul, hL, hL, hxg, hyg,
      smul_zero, smul_zero, sub_self]
  have hcommon : L (parameterVector a b h - parameterVector a b i) ≠ 0 := by
    obtain ⟨μ, hμ⟩ := hf x hxP w hxw.1 hxw
    have hne := edge_target_scale_ne_zero f a b
      (noncentral_not_other_parameter P f a b hind.injective hx hih.symm)
      (Finset.mem_filter.mp (Finset.mem_filter.mp hwh).1).2 hμ
    rw [edge_parameter_identity f a b
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      (Finset.mem_filter.mp (Finset.mem_filter.mp hwh).1).2 hμ,
      map_sub, map_smul, map_smul, hL, hL, hxg, hwg,
      smul_zero, sub_zero, smul_eq_mul, mul_one]
    exact hne
  exact ⟨g, L, simpleFacetSet_isFacet P hP v hs widx, hL,
    simpleFacetForm_nonneg P hP v hs widx, hAi, hother, hcommon,
    w, hxw.1, by rw [hwg]; norm_num⟩

/-- The shared-central boundary case, with all incidence hypotheses derived
from ordinary vertices and homothety parameters. -/
theorem unowned_minimum_shared_central_shephard [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    {i h : I} (hih : i ≠ h)
    (hunowned : ∀ z ∈ centralVertices P a b, f z ≠ a i • z + b i)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hr : 2 ≤ d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hothermin : ∀ k, k ≠ h → (noncentralClass P f a b k).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hshared : ∀ z ∈ centralVertices P a b, 2 ≤ (owners f a b z).card) :
    HasShephardProperty P := by
  classical
  have hsize : 2 ≤ (noncentralClass P f a b i).card := by rw [hmin]; exact hr
  obtain ⟨g, L, hfacet, hL, hnonneg, hAi, hother, hcommon, w, hw, hwg⟩ :=
    exists_unowned_supporting_facet P hP f hf a b hind hcover hih hunowned hmin hsize
  have hall : ∀ j, j ≠ h → ∀ x ∈ noncentralClass P f a b j, g x = 0 := by
    intro j hjh x hx
    by_cases hji : j = i
    · subst j
      exact hAi x hx
    obtain ⟨M, hM, hedge⟩ := exists_unowned_class_crossing_matching
      P hP f hf a b hind hcover hunowned hji hmin hsize
    have hcard : Fintype.card (noncentralClass P f a b i) =
        Fintype.card (noncentralClass P f a b j) := by
      rw [Fintype.card_coe, Fintype.card_coe, hmin, hothermin j hjh]
    have hsur := ((Fintype.bijective_iff_injective_and_card M).mpr ⟨hM, hcard⟩).2
    obtain ⟨u, hu⟩ := hsur ⟨x, hx⟩
    have hux : (M u).val = x := congrArg Subtype.val hu
    have huP := (Finset.mem_filter.mp (Finset.mem_filter.mp u.property).1).1
    have hxP := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
    have hstep : GeneralVertexStep P u.val x := hux ▸ hedge u
    obtain ⟨μ, hμ⟩ := hf u.val huP x hxP hstep
    have he := edge_functional_zero_transfer f a b L
      (Finset.mem_filter.mp (Finset.mem_filter.mp u.property).1).2
      (noncentral_not_other_parameter P f a b hind.injective u.property hji)
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2 hμ
      (hother j hjh) (by rw [hL, hAi u.val u.property])
    rwa [hL] at he
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by omega :
    0 < (noncentralClass P f a b i).card)
  have hx₀P := (Finset.mem_filter.mp (Finset.mem_filter.mp hx₀).1).1
  have hexclude := common_owner_not_on_support_face P f hf a b hcover g L hfacet.1
    hL hother hcommon hx₀P (hAi x₀ hx₀)
    (noncentral_not_other_parameter P f a b hind.injective hx₀ hih.symm)
  have hiff (x : E d) (hx : x ∈ P.vertices) :
      x ∈ affineZeroFace P g ↔ x ∉ fullClass P f a b h := by
    constructor
    · intro hxF hxh
      exact hexclude x hx hxF.2 (Finset.mem_filter.mp hxh).2
    · intro hxnot
      refine ⟨subset_convexHull ℝ _ hx, ?_⟩
      have hxnh : f x ≠ a h • x + b h := fun hxh =>
        hxnot (Finset.mem_filter.mpr ⟨hx, hxh⟩)
      by_cases hxD : vertexVector x ∈ parameterDirectionSpan a b
      · have hxC : x ∈ centralVertices P a b := Finset.mem_filter.mpr ⟨hx, hxD⟩
        obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp (by
          have ht := hshared x hxC
          omega : 1 < (owners f a b x).card)
        have hxj := (Finset.mem_filter.mp hj).2
        have hxk := (Finset.mem_filter.mp hk).2
        have hjh : j ≠ h := by intro he; exact hxnh (he ▸ hxj)
        have hkh : k ≠ h := by intro he; exact hxnh (he ▸ hxk)
        have hz := parameter_difference_support_zero a b L hother hjh hkh
        have hdiff := parameter_difference_at_common_point f a b hxk hxj
        have hcoef : a j - a k ≠ 0 := by
          intro he
          have hp : parameterVector a b j = parameterVector a b k := by
            apply sub_eq_zero.mp
            rw [hdiff, he, zero_smul]
          exact hjk (hind.injective hp)
        rw [hdiff, map_smul, smul_eq_mul, hL] at hz
        exact (mul_eq_zero.mp hz).resolve_left hcoef
      · obtain ⟨j, hxj⟩ := hcover x hx
        have hjh : j ≠ h := by intro he; exact hxnh (he ▸ hxj)
        exact hall j hjh x (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hx, hxj⟩, hxD⟩)
  refine ⟨affineZeroFace P g, hfacet, ?_⟩
  intro x hx hxF
  have hxnot := hexclude x hx hxF.2
  have hlt : g.linear.toContinuousLinearMap x < g.linear.toContinuousLinearMap w := by
    have hxg := hxF.2
    rw [affine_form_apply g x] at hxg
    rw [affine_form_apply g w] at hwg
    change g.linear x < g.linear w
    linarith
  obtain ⟨y, hxy, hxylt⟩ := exists_increasing_edge P g.linear.toContinuousLinearMap hx hw hlt
  have hyg : 0 < g y := by
    have hxg := hxF.2
    rw [affine_form_apply g x] at hxg
    rw [affine_form_apply g y]
    change g.linear x < g.linear y at hxylt
    linarith
  have hyF : y ∉ affineZeroFace P g := by intro hyF; exact hyg.ne' hyF.2
  have hyh : y ∈ fullClass P f a b h := by
    by_contra hn
    exact hyF ((hiff y hxy.1).mpr hn)
  refine ⟨y, ⟨hxy, hyF⟩, ?_⟩
  intro z hz
  have hzh : z ∈ fullClass P f a b h := by
    by_contra hn
    exact hz.2 ((hiff z hz.1.1).mpr hn)
  exact Finset.card_le_one.mp (classNeighbors_card_le_one P f hf a b hx h hxnot)
    z (Finset.mem_filter.mpr ⟨hzh, hz.1⟩) y (Finset.mem_filter.mpr ⟨hyh, hxy⟩)

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/HomothetyCentralOwners.lean -/



@[expose] public section

/-!
# Dimension bound for colors owning a central face

Actual face connectivity puts the parameters of all colors owning the
face in one translate of its homogeneous span. Affine independence then
bounds their number by the face dimension plus two.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ} {I : Type*} [Fintype I]

def centralOwners (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) : Finset I :=
  Finset.univ.filter (fun i => ∃ z ∈ centralVertices P a b, f z = a i • z + b i)

theorem centralOwners_card_le_faceDim_add_two
    (P : ConvexPolytope d) (f : E d → E d) (hf : IsParallelMap P f)
    (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hF : P.IsFace (centralSection P a b))
    (hne : (centralVertices P a b).Nonempty) :
    (centralOwners P f a b).card ≤ faceDim (centralSection P a b) + 2 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀P := (Finset.mem_filter.mp hx₀).1
  have hx₀F : x₀ ∈ centralSection P a b :=
    ⟨subset_convexHull ℝ _ hx₀P, (Finset.mem_filter.mp hx₀).2⟩
  obtain ⟨i₀, hi₀⟩ := hcover x₀ hx₀P
  let F := centralSection P a b
  let D : Submodule ℝ (ℝ × E d) := Submodule.span ℝ (vertexVector '' F)
  let Q := facePolytope P hF
  have hXD {x : E d} (hx : x ∈ F) : vertexVector x ∈ D :=
    Submodule.subset_span (Set.mem_image_of_mem _ hx)
  have hx₀Q : x₀ ∈ Q.vertices := Finset.mem_filter.mpr ⟨hx₀P, hx₀F⟩
  have hwalk : ∀ z, Relation.ReflTransGen (GeneralVertexStep Q) x₀ z →
      z ∈ Q.vertices ∧ ∀ j, f z = a j • z + b j →
        parameterVector a b j - parameterVector a b i₀ ∈ D := by
    intro z hz
    induction hz with
    | refl =>
      refine ⟨hx₀Q, ?_⟩
      intro j hj
      rw [parameter_difference_at_common_point f a b hi₀ hj]
      exact D.smul_mem _ (hXD hx₀F)
    | @tail u v hpath huv ih =>
      have hu := Finset.mem_filter.mp ih.1
      have hv := Finset.mem_filter.mp huv.1
      refine ⟨huv.1, ?_⟩
      intro j hj
      obtain ⟨k, hk⟩ := hcover u hu.1
      have hki := ih.2 k hk
      obtain ⟨_, hne, e, he, hde, hue, hve⟩ := huv
      have hstep : GeneralVertexStep P u v :=
        ⟨hv.1, hne, e, isFace_of_facePolytope P hF he, hde, hue, hve⟩
      obtain ⟨μ, hμ⟩ := hf u hu.1 v hv.1 hstep
      have hjk : parameterVector a b j - parameterVector a b k ∈ D := by
        rw [edge_parameter_identity f a b hk hj hμ]
        exact D.sub_mem (D.smul_mem _ (hXD hv.2)) (D.smul_mem _ (hXD hu.2))
      have hsum := D.add_mem hjk hki
      simpa only [sub_add_sub_cancel] using hsum
  let J := centralOwners P f a b
  have hi₀J : i₀ ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x₀, hx₀, hi₀⟩
  letI : Nonempty J := ⟨⟨i₀, hi₀J⟩⟩
  let p : J → ℝ × E d := fun i => parameterVector a b i.val
  have hp (j : J) : p j - parameterVector a b i₀ ∈ D := by
    obtain ⟨z, hz, hj⟩ := (Finset.mem_filter.mp j.property).2
    have hzP := (Finset.mem_filter.mp hz).1
    have hzF : z ∈ F := ⟨subset_convexHull ℝ _ hzP, (Finset.mem_filter.mp hz).2⟩
    have hzQ : z ∈ Q.vertices := Finset.mem_filter.mpr ⟨hzP, hzF⟩
    exact (hwalk z (balinski_light_general Q hx₀Q hzQ)).2 j.val hj
  have hsub : vectorSpan ℝ (Set.range p) ≤ D := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    intro w hw
    obtain ⟨u, ⟨j, rfl⟩, v, ⟨k, rfl⟩, rfl⟩ := Set.mem_vsub.mp hw
    change p j - p k ∈ D
    have hm := D.sub_mem (hp j) (hp k)
    simpa only [sub_sub_sub_cancel_right] using hm
  have hind' : AffineIndependent ℝ p :=
    hind.comp_embedding ⟨Subtype.val, Subtype.val_injective⟩
  have hc := hind'.finrank_vectorSpan_add_one
  have hdim := Submodule.finrank_mono hsub
  have hD : finrank ℝ D = faceDim F + 1 := finrank_vertexVector_span ⟨x₀, hx₀F⟩
  rw [hD] at hdim
  rw [Fintype.card_coe] at hc
  change (centralOwners P f a b).card ≤ faceDim F + 2
  change finrank ℝ (vectorSpan ℝ (Set.range p)) + 1 = (centralOwners P f a b).card at hc
  omega

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart1

