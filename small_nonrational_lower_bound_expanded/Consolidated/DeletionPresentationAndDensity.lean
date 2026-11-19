module
public import Papers.SimpleDeletionIntrinsic
public import Papers.SimplexFacetPresentation
public import Papers.FacetHalfspaces
public import Papers.FaceVertexDictionary
public import Papers.AffineHomogeneousValues
public import Papers.SimplexFacetTransport
public import Papers.SubfieldAffineForms
public import Papers.FiniteHalfspaceFacets
public import Papers.PolytopeTargets
public import Mathlib.Tactic.FieldSimp
public import Papers.EquivalentExtensions
public import Papers.HomogeneousSpan
public import Mathlib.Analysis.Convex.Combination
public import Papers.ContinuousAffineFrames
public import Papers.AffineSystemContinuity
public import Papers.ExtensionVertexLabels
public import Papers.RationalApproximation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Papers.PolytopeGeometry
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/SimpleDeletionPresentation.lean -/




@[expose] public section

/-!
# The simplex-facet data come from simple deletion

The neighboring facets are obtained by geometric facet separation of the
proper simplex faces.  Every facet visible from the original vertex is
proved to be the new simplex facet.  Thus the original vertex satisfies
the restoration sign conditions without an extra incidence assumption.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem two_le_dimension_of_simple_deletion
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card) : 2 ≤ d := by
  letI := neighborIndex_nonempty_of_vertex_count P hP v hs hcard
  let u : NeighborIndex P v := Classical.choice inferInstance
  obtain ⟨x, hxP, hxv, hxnot⟩ := exists_vertex_outside_corner P hP v hs hcard
  have huv : u.val.val ≠ v.val :=
    ((adj_iff_generalVertexStep P v u.val).mp u.property).2.1.symm
  have hxu : x ≠ u.val.val := by
    intro h
    apply hxnot
    rw [h]
    exact (adj_iff_generalVertexStep P v u.val).mp u.property
  have hnc := vertices_not_collinear P v.property u.val.property hxP huv.symm hxv.symm hxu.symm
  by_contra hd
  apply hnc
  rw [collinear_iff_finrank_le_one]
  have hle := Submodule.finrank_le (vectorSpan ℝ ({v.val, u.val.val, x} : Set (E d)))
  rw [finrank_euclideanSpace_fin] at hle
  omega

theorem deletionFacetSet_isFacet
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) :
    IsFacet (deleteVertex P v.val hne) (deletionFacetSet P v) := by
  refine ⟨deletionFacetSet_isFace P hP v hs hcard hne, ?_⟩
  rw [deleteVertex_fullDim_of_simple P hP v hs hcard hne]
  exact deletionFacetSet_dimension P hP v hs hcard

theorem negative_deletion_facet_eq_new_facet
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty)
    (F : Set (E d)) (hF : IsFacet (deleteVertex P v.val hne) F)
    (f : E d →ᵃ[ℝ] ℝ) (hf : SupportsFace (deleteVertex P v.val hne) F f)
    (hv : f v.val < 0) : F = deletionFacetSet P v := by
  let Q := deleteVertex P v.val hne
  let l : E d →L[ℝ] ℝ := -f.linear.toContinuousLinearMap
  have hneighbors : ∀ u : NeighborIndex P v, l u.val.val ≤ f 0 := by
    intro u
    have h := hf.1 _ (neighbor_mem_deletion P v hne u)
    rw [affine_form_apply f u.val.val] at h
    change -f.linear u.val.val ≤ f 0
    linarith
  have hlv : f 0 < l v.val := by
    rw [affine_form_apply f v.val] at hv
    change f 0 < -f.linear v.val
    linarith
  have hsub : F ⊆ deletionFacetSet P v := by
    rw [face_eq_hull_vertices Q hF.1]
    apply convexHull_mono
    intro x hx
    obtain ⟨hxQ, hxF⟩ := Finset.mem_filter.mp hx
    have hxP : x ∈ P.vertices := Finset.mem_of_mem_erase hxQ
    have hxv : x ≠ v.val := Finset.ne_of_mem_erase hxQ
    have hstep : GeneralVertexStep P v.val x := by
      by_contra hnot
      have hlt := nonneighbor_strict_bound P hP v hs l (f 0) hneighbors hlv hxP hxv hnot
      have hz := hf.eq_zero hxF
      rw [affine_form_apply f x] at hz
      change -f.linear x < f 0 at hlt
      linarith
    let u : NeighborIndex P v :=
      ⟨⟨x, hxP⟩, (adj_iff_generalVertexStep P v ⟨x, hxP⟩).mpr hstep⟩
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have hT := deletionFacetSet_isFacet P hP v hs hcard hne
  exact hF.eq_of_subset hT.1 hT.ne_toSet hsub

theorem deleted_vertex_not_mem_body
    (P : ConvexPolytope d) (v : VertexType P)
    (hne : (P.vertices.erase v.val).Nonempty) :
    v.val ∉ (deleteVertex P v.val hne).toSet := by
  intro hv
  have h := (vertex_mem_hull_vertexSubset_iff P (P.vertices.erase v.val)
    (Finset.erase_subset _ _) v).mp hv
  exact Finset.notMem_erase _ _ h

theorem new_facet_support_negative_at_deleted_vertex
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty)
    (f : E d →ᵃ[ℝ] ℝ)
    (hf : SupportsFace (deleteVertex P v.val hne) (deletionFacetSet P v) f) :
    f v.val < 0 := by
  let Q := deleteVertex P v.val hne
  have hQ := deleteVertex_fullDim_of_simple P hP v hs hcard hne
  obtain ⟨F, g, hF, hg, hgv⟩ := exists_separating_facet Q hQ v.val
    (deleted_vertex_not_mem_body P v hne)
  have hFT := negative_deletion_facet_eq_new_facet P hP v hs hcard hne F hF g hg hgv
  obtain ⟨c, hc, heq⟩ := supportsFacet_positive_proportional Q hQ (deletionFacetSet P v)
    (deletionFacetSet_isFacet P hP v hs hcard hne) f g hf (hFT ▸ hg)
  rw [heq]
  exact mul_neg_of_pos_of_neg hc hgv

def deletionNeighborVertex (P : ConvexPolytope d) (v : VertexType P)
    (hne : (P.vertices.erase v.val).Nonempty) (i : NeighborIndex P v) :
    VertexType (deleteVertex P v.val hne) :=
  ⟨i.val.val, Finset.mem_erase.mpr
    ⟨((adj_iff_generalVertexStep P v i.val).mp i.property).2.1.symm, i.val.property⟩⟩

theorem exists_deletion_simplexFacetPresentation
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) :
    ∃ D : SimplexFacetPresentation (deleteVertex P v.val hne) (NeighborIndex P v),
      D.base = deletionFacetSet P v ∧
      (∀ i, D.vertex i = deletionNeighborVertex P v hne i) ∧ D.AdmissiblePoint v.val := by
  let Q := deleteVertex P v.val hne
  let N := NeighborIndex P v
  let p : N → VertexType Q := deletionNeighborVertex P v hne
  have hd := two_le_dimension_of_simple_deletion P hP v hs hcard
  have hQ := deleteVertex_fullDim_of_simple P hP v hs hcard hne
  have hT := deletionFacetSet_isFacet P hP v hs hcard hne
  let T : FacetType Q := ⟨⟨deletionFacetSet P v, hT.1⟩, hT⟩
  have hfacets (i : N) : ∃ G : FacetType Q,
      (p i).val ∉ G.val.val ∧ ∀ j : N, j ≠ i → (p j).val ∈ G.val.val := by
    let S := (neighborVertices P v).erase (p i).val
    have hiN : (p i).val ∈ neighborVertices P v :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hS : S.Nonempty := by
      apply Finset.card_pos.mp
      change 0 < ((neighborVertices P v).erase (p i).val).card
      rw [Finset.card_erase_of_mem hiN, neighborVertices_card P hP v hs]
      omega
    have hSface := neighbor_subset_isFace P hP v hs hcard hne S hS (Finset.erase_subset _ _)
    have hip : (p i).val ∉ convexHull ℝ (S : Set (E d)) := by
      intro hi
      have hmem := (vertex_mem_hull_vertexSubset_iff P S
        (fun x hx => by
          obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hx)
          exact u.val.property) i.val).mp hi
      exact (Finset.mem_erase.mp hmem).1 rfl
    obtain ⟨G, hG, hSG, hiG⟩ := exists_facet_containing_not_mem Q hQ
      (convexHull ℝ (S : Set (E d))) hSface (p i).val
      (subset_convexHull ℝ _ (p i).property) hip
    refine ⟨⟨⟨G, hG.1⟩, hG⟩, hiG, ?_⟩
    intro j hji
    apply hSG
    apply subset_convexHull ℝ _
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
    intro heq
    exact hji (Subtype.ext (Subtype.ext heq))
  let G : N → FacetType Q := fun i => Classical.choose (hfacets i)
  have hGi (i : N) : (p i).val ∉ (G i).val.val ∧
      ∀ j : N, j ≠ i → (p j).val ∈ (G i).val.val := Classical.choose_spec (hfacets i)
  let F : Option N → FacetType Q := fun i => i.elim T G
  let form : Option N → E d →ᵃ[ℝ] ℝ := fun i => chosenFacetForm Q (F i)
  have hsupp : ∀ i, SupportsFace Q (F i).val.val (form i) :=
    fun i => chosenFacetForm_supports Q (F i)
  have hpT (i : N) : (p i).val ∈ T.val.val :=
    subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let D : SimplexFacetPresentation Q N := {
    fullDim := hQ
    index_card := by simpa only [finrank_euclideanSpace_fin] using card_neighbors_of_simple P hP v hs
    facet := F
    form := form
    supports := hsupp
    vertex := p
    at_base := fun i => (hsupp none).eq_zero (hpT i)
    diagonal := by
      intro i
      exact lt_of_le_of_ne ((hsupp (some i)).1 _ (subset_convexHull ℝ _ (p i).property))
        (fun hz => (hGi i).1 (((hsupp (some i)).mem_iff _).mpr
          ⟨subset_convexHull ℝ _ (p i).property, hz.symm⟩))
    off_diagonal := by
      intro i j hij
      exact (hsupp (some i)).eq_zero ((hGi i).2 j hij.symm) }
  refine ⟨D, rfl, fun _ => rfl, ?_, ?_⟩
  · exact new_facet_support_negative_at_deleted_vertex P hP v hs hcard hne
      (form none) (hsupp none)
  · intro i
    by_contra hi
    have hneg : form (some i) v.val < 0 := lt_of_not_ge hi
    have hGT := negative_deletion_facet_eq_new_facet P hP v hs hcard hne
      (G i).val.val (G i).property (form (some i)) (hsupp (some i)) hneg
    exact (hGi i).1 (hGT.symm ▸ hpT i)

end Papers.Polytopes

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/ProjectivePolytope.lean -/





@[expose] public section

/-!
# Positive projective transformations of finite convex polytopes

The homogeneous linear isomorphism and positive normalizing factors are
explicit.  All target generators are proved to be extreme points, and
every exposed face is transported in both directions.  Thus the resulting
equivalence is an ordinary face-poset isomorphism, with no additional
combinatorial incidence hypothesis.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ}

theorem positive_projective_labels_injective
    (P : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ))
    (q : VertexType P → E e) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) : Function.Injective q := by
  intro v w hq
  have hcross : h w • (v.val, (1 : ℝ)) = h v • (w.val, (1 : ℝ)) := by
    apply L.injective
    rw [map_smul, map_smul, hL v, hL w, hq]
    simp only [smul_smul, mul_comm]
  have hscale : h w = h v := by
    have hs := congrArg Prod.snd hcross
    simpa only [Prod.smul_snd, smul_eq_mul, mul_one] using hs
  have hvalue := congrArg Prod.fst hcross
  simp only [Prod.smul_fst, hscale] at hvalue
  exact Subtype.ext (smul_right_injective _ (ne_of_gt (hh v)) hvalue)

theorem projective_support_nonneg
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (f : E d →ᵃ[ℝ] ℝ)
    (x : E d) (y : E e) (h : ℝ) (hh : 0 < h)
    (hL : L (x, 1) = h • (y, 1)) (hf : 0 ≤ f x) :
    0 ≤ projectiveTransportAffine L f y := by
  have heq := projectiveTransportAffine_scaled L f x y h hL
  rw [heq] at hf
  exact (mul_nonneg_iff_of_pos_left hh).mp hf

theorem projective_support_zero_iff
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (f : E d →ᵃ[ℝ] ℝ)
    (x : E d) (y : E e) (h : ℝ) (hh : h ≠ 0)
    (hL : L (x, 1) = h • (y, 1)) :
    projectiveTransportAffine L f y = 0 ↔ f x = 0 := by
  rw [projectiveTransportAffine_scaled L f x y h hL]
  exact (mul_eq_zero.trans (or_iff_right hh)).symm

def projectivePolytope
    (P : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ))
    (q : VertexType P → E e) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) : ConvexPolytope e := by
  classical
  let s := Finset.univ.image q
  have hs : s.Nonempty := by
    obtain ⟨x, hx⟩ := P.vertices_nonempty
    exact ⟨q ⟨x, hx⟩, Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩⟩
  apply polytopeOfStrictMinima s hs
  intro x hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨f, hf⟩ := exists_supportsFace P (vertex_isFace P v.property)
  let g := projectiveTransportAffine L f
  have hgv : g (q v) = 0 :=
    (projective_support_zero_iff L f v.val (q v) (h v) (ne_of_gt (hh v)) (hL v)).mpr
      (hf.eq_zero (Set.mem_singleton _))
  refine ⟨g.linear.toContinuousLinearMap, ?_⟩
  intro y hy hyne
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hy
  have hwv : w ≠ v := fun heq => hyne (congrArg q heq)
  have hfw : 0 < f w.val := by
    have hfn := hf.1 w.val (subset_convexHull ℝ _ w.property)
    rcases lt_or_eq_of_le hfn with hp | he
    · exact hp
    · have hw : w.val ∈ ({v.val} : Set (E d)) :=
        (hf.mem_iff w.val).mpr ⟨subset_convexHull ℝ _ w.property, he.symm⟩
      exact False.elim (hwv (Subtype.ext hw))
  have hscale := projectiveTransportAffine_scaled L f w.val (q w) (h w) (hL w)
  have hgw : 0 < g (q w) := by
    change 0 < projectiveTransportAffine L f (q w)
    rw [hscale] at hfw
    exact (mul_pos_iff_of_pos_left (hh w)).mp hfw
  change g.linear (q v) < g.linear (q w)
  rw [affine_form_apply g (q v)] at hgv
  rw [affine_form_apply g (q w)] at hgw
  linarith

@[simp] theorem projectivePolytope_vertices
    (P : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ))
    (q : VertexType P → E e) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) :
    (projectivePolytope P L q h hh hL).vertices = Finset.univ.image q := rfl

def projectiveVertexEquiv
    (P : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ))
    (q : VertexType P → E e) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) :
    VertexType P ≃ VertexType (projectivePolytope P L q h hh hL) := by
  classical
  let f : VertexType P → VertexType (projectivePolytope P L q h hh hL) :=
    fun v => ⟨q v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro v w heq
    exact positive_projective_labels_injective P L q h hh hL (congrArg Subtype.val heq)
  · rintro ⟨x, hx⟩
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨v, rfl⟩

@[simp] theorem projectiveVertexEquiv_apply_val
    (P : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ))
    (q : VertexType P → E e) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) (v : VertexType P) :
    (projectiveVertexEquiv P L q h hh hL v).val = q v := rfl

theorem positive_projective_face_forward
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (b : VertexType P ≃ VertexType Q)
    (h : VertexType P → ℝ) (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1))
    (F : FaceType P) : ∃ G : FaceType Q,
      ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val := by
  obtain ⟨f, hf⟩ := exists_supportsFace P F.property
  let g := projectiveTransportAffine L f
  have hgV : ∀ y ∈ Q.vertices, 0 ≤ g y := by
    intro y hy
    obtain ⟨v, hv⟩ := b.surjective ⟨y, hy⟩
    have hby : (b v).val = y := congrArg Subtype.val hv
    rw [← hby]
    exact projective_support_nonneg L f v.val (b v).val (h v) (hh v) (hL v)
      (hf.1 v.val (subset_convexHull ℝ _ v.property))
  have hgP : ∀ y ∈ Q.toSet, 0 ≤ g y := affine_nonneg_on_hull Q.vertices g hgV
  obtain ⟨x, hx⟩ := (facePolytope P F.property).vertices_nonempty
  have hxP : x ∈ P.vertices := (Finset.mem_filter.mp hx).1
  have hxF : x ∈ F.val := (Finset.mem_filter.mp hx).2
  let v : VertexType P := ⟨x, hxP⟩
  have hgv : g (b v).val = 0 :=
    (projective_support_zero_iff L f v.val (b v).val (h v) (ne_of_gt (hh v)) (hL v)).mpr
      (hf.eq_zero hxF)
  have hne : (affineZeroFace Q g).Nonempty :=
    ⟨(b v).val, subset_convexHull ℝ _ (b v).property, hgv⟩
  let G : FaceType Q := ⟨affineZeroFace Q g, affineZeroFace_isFace Q g hgP hne⟩
  refine ⟨G, ?_⟩
  intro w
  have hbwQ : (b w).val ∈ Q.toSet := subset_convexHull ℝ _ (b w).property
  have hwP : w.val ∈ P.toSet := subset_convexHull ℝ _ w.property
  change ((b w).val ∈ Q.toSet ∧ g (b w).val = 0) ↔ w.val ∈ F.val
  rw [and_iff_right hbwQ]
  rw [projective_support_zero_iff L f w.val (b w).val (h w) (ne_of_gt (hh w)) (hL w)]
  exact ((hf.mem_iff w.val).trans (and_iff_right hwP)).symm

def positiveProjectiveFaceOrderIso
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (b : VertexType P ≃ VertexType Q)
    (h : VertexType P → ℝ) (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1)) :
    FaceType P ≃o FaceType Q := by
  apply faceOrderIsoOfVertexIncidence P Q b
    (positive_projective_face_forward P Q L b h hh hL)
  intro G
  let h' : VertexType Q → ℝ := fun w => (h (b.symm w))⁻¹
  have hh' : ∀ w, 0 < h' w := fun w => inv_pos.mpr (hh (b.symm w))
  have hL' : ∀ w, L.symm (w.val, 1) = h' w • ((b.symm w).val, 1) := by
    intro w
    have heq := congrArg L.symm (hL (b.symm w))
    simp only [L.symm_apply_apply, b.apply_symm_apply, map_smul] at heq
    rw [heq]
    simp only [h', smul_smul, inv_mul_cancel₀ (ne_of_gt (hh (b.symm w))), one_smul]
  obtain ⟨F, hF⟩ := positive_projective_face_forward Q P L.symm b.symm h' hh' hL' G
  refine ⟨F, ?_⟩
  intro v
  simpa only [b.symm_apply_apply] using (hF (b v)).symm

def projectivePolytopeFaceOrderIso
    (P : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ))
    (q : VertexType P → E e) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) :
    FaceType P ≃o FaceType (projectivePolytope P L q h hh hL) :=
  positiveProjectiveFaceOrderIso P _ L (projectiveVertexEquiv P L q h hh hL) h hh hL

end Papers.Polytopes

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/ProjectiveFaceSupport.lean -/




@[expose] public section

/-!
# The vertex and support dictionaries of the projective face isomorphism

The induced vertex map is proved to be the explicit projective vertex
map.  Supporting affine forms consequently transport to the exact image
face, so their signs can be used in restoration without an additional
compatibility hypothesis.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ}

theorem imageVertex_eq_of_face_incidence
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (b : VertexType P ≃ VertexType Q)
    (hinc : ∀ (F : FaceType P) (v : VertexType P),
      (b v).val ∈ (φ F).val ↔ v.val ∈ F.val)
    (v : VertexType P) : imageVertex φ v = b v := by
  have hm := (hinc (vertexFace P v) v).mpr (Set.mem_singleton _)
  rw [← imageVertex_face φ v] at hm
  exact Subtype.ext (show (imageVertex φ v).val = (b v).val from hm.symm)

theorem positiveProjectiveFaceOrderIso_incidence
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (b : VertexType P ≃ VertexType Q)
    (h : VertexType P → ℝ) (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1))
    (F : FaceType P) (v : VertexType P) :
    (b v).val ∈ (positiveProjectiveFaceOrderIso P Q L b h hh hL F).val ↔ v.val ∈ F.val := by
  change (b v).val ∈ (Classical.choose
    (positive_projective_face_forward P Q L b h hh hL F)).val ↔ v.val ∈ F.val
  exact Classical.choose_spec (positive_projective_face_forward P Q L b h hh hL F) v

theorem positiveProjectiveFaceOrderIso_vertex
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (b : VertexType P ≃ VertexType Q)
    (h : VertexType P → ℝ) (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1)) (v : VertexType P) :
    imageVertex (positiveProjectiveFaceOrderIso P Q L b h hh hL) v = b v :=
  imageVertex_eq_of_face_incidence _ b
    (positiveProjectiveFaceOrderIso_incidence P Q L b h hh hL) v

theorem positiveProjectiveFaceOrderIso_supports
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (b : VertexType P ≃ VertexType Q)
    (h : VertexType P → ℝ) (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1))
    (F : FaceType P) (f : E d →ᵃ[ℝ] ℝ) (hf : SupportsFace P F.val f) :
    SupportsFace Q (positiveProjectiveFaceOrderIso P Q L b h hh hL F).val
      (projectiveTransportAffine L f) := by
  let g := projectiveTransportAffine L f
  let φ := positiveProjectiveFaceOrderIso P Q L b h hh hL
  have hgV : ∀ x ∈ Q.vertices, 0 ≤ g x := by
    intro x hx
    obtain ⟨v, hv⟩ := b.surjective ⟨x, hx⟩
    have hval : (b v).val = x := congrArg Subtype.val hv
    rw [← hval]
    exact projective_support_nonneg L f v.val (b v).val (h v) (hh v) (hL v)
      (hf.1 v.val (subset_convexHull ℝ _ v.property))
  have hg : ∀ x ∈ Q.toSet, 0 ≤ g x := affine_nonneg_on_hull Q.vertices g hgV
  have hinc (v : VertexType P) : (b v).val ∈ affineZeroFace Q g ↔ v.val ∈ F.val := by
    have hbvQ : (b v).val ∈ Q.toSet := subset_convexHull ℝ _ (b v).property
    have hvP : v.val ∈ P.toSet := subset_convexHull ℝ _ v.property
    change ((b v).val ∈ Q.toSet ∧ g (b v).val = 0) ↔ v.val ∈ F.val
    rw [and_iff_right hbvQ]
    rw [projective_support_zero_iff L f v.val (b v).val (h v) (ne_of_gt (hh v)) (hL v)]
    exact ((hf.mem_iff v.val).trans
      (and_iff_right hvP)).symm
  have hne : (affineZeroFace Q g).Nonempty := by
    obtain ⟨x, hx⟩ := (facePolytope P F.property).vertices_nonempty
    obtain ⟨hxP, hxF⟩ := Finset.mem_filter.mp hx
    exact ⟨(b ⟨x, hxP⟩).val, (hinc ⟨x, hxP⟩).mpr hxF⟩
  let G : FaceType Q := ⟨affineZeroFace Q g, affineZeroFace_isFace Q g hg hne⟩
  have heq : φ F = G := by
    apply face_eq_of_vertex_incidence Q
    intro w
    obtain ⟨v, rfl⟩ := b.surjective w
    exact (positiveProjectiveFaceOrderIso_incidence P Q L b h hh hL F v).trans (hinc v).symm
  exact ⟨hg, congrArg Subtype.val heq⟩

end Papers.Polytopes

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/SubfieldFacetForms.lean -/




@[expose] public section

/-!
# Every facet of a field-coordinate polytope has a form over that field

A field-linear functional separates an outside vertex from the span of
the homogeneous facet vertices.  Its real extension is normalized to one
at that vertex.  The actual facet dimension then makes its kernel the
facet hyperplane, and fixes the inward orientation.  No rational normal
or determinant certificate is assumed.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem homogeneousSpan_facet_eq_ker_of_vanishes
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : IsFacet P F)
    (g : E d →ᵃ[ℝ] ℝ) (hg : ∀ x ∈ F, g x = 0) (hne : g ≠ 0) :
    homogeneousSpan (K := ℝ) F = (affineLift g).ker := by
  have hle : homogeneousSpan (K := ℝ) F ≤ (affineLift g).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    change homogeneousEvaluation (x, (1 : ℝ)) g = 0
    rw [homogeneousEvaluation_homogenize, hg x hx]
  have hdimF : finrank ℝ (homogeneousSpan (K := ℝ) F) = d := by
    rw [finrank_homogeneousSpan hF.1.2]
    exact hF.2.trans hP
  have hrange : (affineLift g).range = ⊤ := LinearMap.range_eq_top.mpr (affineLift_surjective hne)
  have hdim := (affineLift g).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, finrank_self, finrank_prod,
    finrank_euclideanSpace_fin, finrank_self] at hdim
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [hdimF]
  omega

theorem supportsFace_of_vanishes_facet
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : IsFacet P F)
    (g : E d →ᵃ[ℝ] ℝ) (hg : ∀ x ∈ F, g x = 0)
    (q : E d) (hqP : q ∈ P.toSet) (hqF : q ∉ F) (hgq : 0 < g q) :
    SupportsFace P F g := by
  obtain ⟨f, hf⟩ := exists_supportsFace P hF.1
  have hfq : 0 < f q := lt_of_le_of_ne (hf.1 q hqP)
    (fun hz => hqF ((hf.mem_iff q).mpr ⟨hqP, hz.symm⟩))
  have hgne : g ≠ 0 := by
    intro heq
    rw [heq] at hgq
    exact lt_irrefl (0 : ℝ) hgq
  have hker : (affineLift g).ker ≤ (affineLift f).ker := by
    rw [← homogeneousSpan_facet_eq_ker_of_vanishes P hP F hF g hg hgne,
      ← homogeneousSpan_facet_eq_ker P hP F hF f hf]
  have heq := linear_form_eq_scalar_of_ker_le (affineLift f) (affineLift g)
    (q, (1 : ℝ))
    (by simpa only [affineLift_apply, homogeneousEvaluation_homogenize] using ne_of_gt hgq)
    hker
  let c := f q / g q
  have hc : 0 < c := div_pos hfq hgq
  have hfg (x : E d) : f x = c * g x := by
    have h := congrArg (fun l : (E d × ℝ) →ₗ[ℝ] ℝ => l (x, 1)) heq
    simpa only [LinearMap.smul_apply, affineLift_apply, homogeneousEvaluation_homogenize,
      smul_eq_mul] using h
  constructor
  · intro x hx
    have hn := hf.1 x hx
    rw [hfg x] at hn
    exact (mul_nonneg_iff_of_pos_left hc).mp hn
  · rw [hf.2]
    ext x
    change (x ∈ P.toSet ∧ f x = 0) ↔ x ∈ P.toSet ∧ g x = 0
    rw [hfg x, mul_eq_zero, or_iff_right (ne_of_gt hc)]

theorem exists_vertex_outside_facet
    (P : ConvexPolytope d) (F : Set (E d)) (hF : IsFacet P F) :
    ∃ q : VertexType P, q.val ∉ F := by
  by_contra h
  push_neg at h
  have hPF : P.toSet ⊆ F := convexHull_min
    (fun x hx => h ⟨x, hx⟩) (hF.1.1.convex (convex_convexHull ℝ _))
  exact hF.ne_toSet (Set.Subset.antisymm (face_subset_toSet P hF.1) hPF)

theorem exists_field_facet_form
    (K : Subfield ℝ) (P : ConvexPolytope d) (hP : P.IsFullDim)
    (hPK : CoordinatesIn K P) (F : Set (E d)) (hF : IsFacet P F) :
    ∃ f : (Fin d → K) →ᵃ[K] K, SupportsFace P F (extendFieldAffine K f) := by
  let vK : VertexType P → Fin d → K :=
    fun v => fieldPoint K v.val (hPK v.val v.property)
  let h : VertexType P → (Fin d → K) × K := fun v => (vK v, 1)
  let S : Set ((Fin d → K) × K) := h '' {v : VertexType P | v.val ∈ F}
  obtain ⟨q, hqF⟩ := exists_vertex_outside_facet P F hF
  have hembed (v : VertexType P) :
      embedFieldHomogeneous K (h v) = (v.val, (1 : ℝ)) := by
    change (embedFieldPoint K (fieldPoint K v.val (hPK v.val v.property)), 1) = _
    rw [embed_fieldPoint]
  have himage : embedFieldHomogeneous K '' S ⊆
      homogenize (K := ℝ) '' F := by
    rintro z ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    rw [hembed]
    exact ⟨v.val, hv, rfl⟩
  have hqspan : h q ∉ Submodule.span K S := by
    intro hmem
    have hreal := semilinear_mem_span K.subtype (embedFieldHomogeneous K) S (h q) hmem
    have hreal' : embedFieldHomogeneous K (h q) ∈ homogeneousSpan (K := ℝ) F :=
      Submodule.span_mono himage hreal
    rw [hembed] at hreal'
    have haff := (homogenize_mem_span_iff hF.1.2 q.val).mp hreal'
    exact vertex_notMem_affineSpan_face P hF.1 q.property hqF haff
  obtain ⟨l, hlq, hlS⟩ := Submodule.exists_le_ker_of_notMem hqspan
  let l' : ((Fin d → K) × K) →ₗ[K] K := (l (h q))⁻¹ • l
  let f : (Fin d → K) →ᵃ[K] K := affineDehomogenize l'
  have hfq : f (vK q) = 1 := by
    change (l (h q))⁻¹ * l (h q) = 1
    exact inv_mul_cancel₀ hlq
  have hfF (v : VertexType P) (hv : v.val ∈ F) : f (vK v) = 0 := by
    have hzero : l (h v) = 0 := hlS (Submodule.subset_span ⟨v, hv, rfl⟩)
    change (l (h q))⁻¹ * l (h v) = 0
    rw [hzero, mul_zero]
  let g := extendFieldAffine K f
  have hgv (v : VertexType P) : g v.val = (f (vK v) : ℝ) := by
    have he : embedFieldPoint K (vK v) = v.val := embed_fieldPoint K v.val (hPK v.val v.property)
    rw [← he]
    exact extendFieldAffine_embed K f (vK v)
  have hgF : ∀ x ∈ F, g x = 0 := by
    intro x hx
    rw [face_eq_hull_vertices P hF.1] at hx
    apply affine_zero_on_hull (P.vertices.filter (· ∈ F)) g ?_ x hx
    intro y hy
    obtain ⟨hyP, hyF⟩ := Finset.mem_filter.mp hy
    rw [hgv ⟨y, hyP⟩, hfF ⟨y, hyP⟩ hyF, Subfield.coe_zero]
  have hgq : 0 < g q.val := by
    rw [hgv q, hfq, Subfield.coe_one]
    exact zero_lt_one
  exact ⟨f, supportsFace_of_vanishes_facet P hP F hF g hgF q.val
    (subset_convexHull ℝ _ q.property) hqF hgq⟩

theorem exists_facet_coefficients_in
    (K : Subfield ℝ) (P : ConvexPolytope d) (hP : P.IsFullDim)
    (hPK : CoordinatesIn K P) (F : Set (E d)) (hF : IsFacet P F) :
    ∃ f : E d →ᵃ[ℝ] ℝ, SupportsFace P F f ∧ AffineCoefficientsIn K f := by
  obtain ⟨f, hf⟩ := exists_field_facet_form K P hP hPK F hF
  exact ⟨extendFieldAffine K f, hf, extendFieldAffine_coefficients K f⟩

end Papers.Polytopes

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/SubfieldAffineBasis.lean -/



@[expose] public section

/-!
# Solving the restoration equations over the coordinate field

The real affine-form basis descends to a basis over the subfield when its
members are real extensions of subfield forms.  Arbitrary subfield values
therefore determine a homogeneous point over that same field.  This is an
actual linear-algebra construction, not an assumed solution of the system.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem extendFieldLinear_add (K : Subfield ℝ)
    (f g : (Fin d → K) →ₗ[K] K) :
    extendFieldLinear K (f + g) = extendFieldLinear K f + extendFieldLinear K g := by
  apply (PiLp.basisFun 2 ℝ (Fin d)).ext
  intro i
  simp only [LinearMap.add_apply, extendFieldLinear_basis, Subfield.coe_add]

theorem extendFieldLinear_smul (K : Subfield ℝ) (c : K)
    (f : (Fin d → K) →ₗ[K] K) :
    extendFieldLinear K (c • f) = (c : ℝ) • extendFieldLinear K f := by
  apply (PiLp.basisFun 2 ℝ (Fin d)).ext
  intro i
  simp only [LinearMap.smul_apply, extendFieldLinear_basis, smul_eq_mul, Subfield.coe_mul]

def extendFieldAffineMap (K : Subfield ℝ) :
    ((Fin d → K) →ᵃ[K] K) →ₛₗ[K.subtype] (E d →ᵃ[ℝ] ℝ) where
  toFun := extendFieldAffine K
  map_add' f g := by
    ext x
    change extendFieldLinear K (f + g).linear x + ((f + g) 0 : ℝ) =
      (extendFieldLinear K f.linear x + (f 0 : ℝ)) +
        (extendFieldLinear K g.linear x + (g 0 : ℝ))
    rw [AffineMap.add_linear, extendFieldLinear_add, LinearMap.add_apply]
    change _ + ((f 0 + g 0 : K) : ℝ) = _
    rw [Subfield.coe_add]
    ring
  map_smul' c f := by
    ext x
    change extendFieldLinear K (c • f).linear x + ((c • f) 0 : ℝ) =
      (c : ℝ) * (extendFieldLinear K f.linear x + (f 0 : ℝ))
    rw [AffineMap.smul_linear, extendFieldLinear_smul, LinearMap.smul_apply, smul_eq_mul]
    change _ + ((c * f 0 : K) : ℝ) = _
    rw [Subfield.coe_mul, mul_add]

@[simp] theorem extendFieldAffineMap_apply (K : Subfield ℝ)
    (f : (Fin d → K) →ᵃ[K] K) : extendFieldAffineMap K f = extendFieldAffine K f := rfl

theorem field_forms_independent_of_real_basis
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) : LinearIndependent K f := by
  have hLI : LinearIndependent ℝ (fun i => extendFieldAffineMap K (f i)) := by
    have heq : (fun i => extendFieldAffineMap K (f i)) = (fun i => b i) :=
      funext (fun i => (hf i).symm)
    rw [heq]
    exact b.linearIndependent
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (extendFieldAffineMap K) hc
  simp only [map_sum, map_smulₛₗ, map_zero, Subfield.subtype_apply] at h
  have hi := (Fintype.linearIndependent_iff.mp hLI) (fun j => (c j : ℝ)) h i
  apply Subtype.ext
  simpa only [Subfield.coe_zero] using hi

def fieldAffineBasis
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) :
    Basis ι K ((Fin d → K) →ᵃ[K] K) :=
  basisOfLinearIndependentOfCardEqFinrank' f
    (field_forms_independent_of_real_basis K b f hf)
    (by
      rw [← Module.finrank_eq_card_basis b]
      simp [AffineMap.finrank_eq])

@[simp] theorem fieldAffineBasis_apply
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) (i : ι) :
    fieldAffineBasis K b f hf i = f i := by
  simp only [fieldAffineBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

def fieldHomogeneousValues
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) (r : ι → K) : (Fin d → K) × K :=
  realizeAffineValues (fieldAffineBasis K b f hf) r

theorem fieldHomogeneousValues_evaluation
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) (r : ι → K) (i : ι) :
    homogeneousEvaluation (embedFieldHomogeneous K (fieldHomogeneousValues K b f hf r))
      (b i) = (r i : ℝ) := by
  rw [hf i, extendFieldAffine_homogeneous]
  apply congrArg (fun x : K => (x : ℝ))
  rw [← fieldAffineBasis_apply K b f hf i]
  exact realizeAffineValues_basis (fieldAffineBasis K b f hf) r i

theorem fieldHomogeneousValues_eq_real_solution
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) (r : ι → K) :
    embedFieldHomogeneous K (fieldHomogeneousValues K b f hf r) =
      realizeAffineValues b (fun i => (r i : ℝ)) := by
  apply homogeneousEvaluation_injective
  apply b.ext
  intro i
  rw [fieldHomogeneousValues_evaluation, realizeAffineValues_basis]

theorem real_solution_coordinates_in
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) (r : ι → K) :
    (∀ j, (realizeAffineValues b (fun i => (r i : ℝ))).1 j ∈ K) ∧
      (realizeAffineValues b (fun i => (r i : ℝ))).2 ∈ K := by
  rw [← fieldHomogeneousValues_eq_real_solution K b f hf r]
  exact ⟨fun j => ((fieldHomogeneousValues K b f hf r).1 j).property,
    (fieldHomogeneousValues K b f hf r).2.property⟩

end Papers.Polytopes

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/BasisProjectiveChart.lean -/





@[expose] public section

/-!
# An explicit projective chart from an affine-form basis

The chart replaces the distinguished coordinate by a nonzero multiple of
that coordinate plus the sum of all other coordinates.  Its inverse is
written explicitly.  The same construction works over any field; in the
real geometric application the denominator is separately proved positive
on every old vertex and the new homogeneous point.
-/

noncomputable section
namespace Papers.AffineCoordinates

open Module
open scoped Classical BigOperators

section Field
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype ι]

def basisValuesLinear (b : Basis ι K (V →ᵃ[K] K)) : (V × K) →ₗ[K] (ι → K) where
  toFun z i := homogeneousEvaluation z (b i)
  map_add' z w := by
    ext i
    exact congrArg (fun f : Module.Dual K (V →ᵃ[K] K) => f (b i))
      (homogeneousEvaluation.map_add z w)
  map_smul' c z := by
    ext i
    exact congrArg (fun f : Module.Dual K (V →ᵃ[K] K) => f (b i))
      (homogeneousEvaluation.map_smul c z)

def basisValuesEquiv (b : Basis ι K (V →ᵃ[K] K)) : (V × K) ≃ₗ[K] (ι → K) := by
  apply LinearEquiv.ofBijective (basisValuesLinear b)
  constructor
  · intro z w h
    apply homogeneousEvaluation_injective
    apply b.ext
    intro i
    exact congrFun h i
  · intro r
    refine ⟨realizeAffineValues b r, ?_⟩
    ext i
    exact realizeAffineValues_basis b r i

def optionValuesEquiv : (Option ι → K) ≃ₗ[K] ((ι → K) × K) where
  toFun r := (fun i => r (some i), r none)
  invFun z i := i.elim z.2 z.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv r := by ext i; cases i <;> rfl
  right_inv z := rfl

def chartShear (ε : K) (hε : ε ≠ 0) : ((ι → K) × K) ≃ₗ[K] ((ι → K) × K) where
  toFun z := (z.1, ε * z.2 + ∑ i, z.1 i)
  invFun z := (z.1, (z.2 - ∑ i, z.1 i) / ε)
  map_add' z w := by
    apply Prod.ext
    · rfl
    · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, Finset.sum_add_distrib]
      ring
  map_smul' c z := by
    apply Prod.ext
    · rfl
    · simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply, ← Finset.mul_sum]
      ring
  left_inv z := by
    apply Prod.ext
    · rfl
    · change (ε * z.2 + (∑ i, z.1 i) - (∑ i, z.1 i)) / ε = z.2
      rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hε]
  right_inv z := by
    apply Prod.ext
    · rfl
    · change ε * ((z.2 - ∑ i, z.1 i) / ε) + (∑ i, z.1 i) = z.2
      field_simp
      ring

end Field

open LeanEval.Geometry.PlatonicClassification

variable {d : ℕ} {ι : Type*} [Fintype ι]

def euclideanReindex (e : ι ≃ Fin d) : (ι → ℝ) ≃ₗ[ℝ] E d where
  toFun x := WithLp.toLp 2 (fun i => x (e.symm i))
  invFun y i := y (e i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by ext i; simp only [Equiv.symm_apply_apply]
  right_inv y := by ext i; simp only [Equiv.apply_symm_apply]

def basisChartEquiv
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (e : ι ≃ Fin d)
    (ε : ℝ) (hε : ε ≠ 0) : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ) :=
  (basisValuesEquiv b).trans
    (optionValuesEquiv.trans ((chartShear ε hε).trans
      (LinearEquiv.prodCongr (euclideanReindex e) (LinearEquiv.refl ℝ ℝ))))

@[simp] theorem basisChartEquiv_fst
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (e : ι ≃ Fin d)
    (ε : ℝ) (hε : ε ≠ 0) (z : E d × ℝ) (i : Fin d) :
    (basisChartEquiv b e ε hε z).1 i = homogeneousEvaluation z (b (some (e.symm i))) := rfl

@[simp] theorem basisChartEquiv_snd
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (e : ι ≃ Fin d)
    (ε : ℝ) (hε : ε ≠ 0) (z : E d × ℝ) :
    (basisChartEquiv b e ε hε z).2 =
      ε * homogeneousEvaluation z (b none) + ∑ i, homogeneousEvaluation z (b (some i)) := rfl

theorem basisChartEquiv_snd_form
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (e : ι ≃ Fin d)
    (ε : ℝ) (hε : ε ≠ 0) (z : E d × ℝ) :
    (basisChartEquiv b e ε hε z).2 =
      homogeneousEvaluation z (ε • b none + ∑ i, b (some i)) := by
  rw [basisChartEquiv_snd, map_add, map_smul, map_sum]
  rfl

def normalizedImage (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ)) (z : E d × ℝ) : E d :=
  (L z).2⁻¹ • (L z).1

theorem normalizedImage_lift (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (z : E d × ℝ) (hz : (L z).2 ≠ 0) :
    L z = (L z).2 • (normalizedImage L z, (1 : ℝ)) := by
  apply Prod.ext
  · change (L z).1 = (L z).2 • ((L z).2⁻¹ • (L z).1)
    rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
  · change (L z).2 = (L z).2 * 1
    exact (mul_one _).symm

theorem projectiveTransportAffine_homogeneous_scaled
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (f : E d →ᵃ[ℝ] ℝ) (z : E d × ℝ) (y : E d) (h : ℝ)
    (heq : L z = h • (y, 1)) :
    homogeneousEvaluation z f = h * projectiveTransportAffine L f y := by
  have hz : z = h • L.symm (y, 1) := by
    have h' := congrArg L.symm heq
    simpa only [L.symm_apply_apply, map_smul] using h'
  change affineLift f z = _
  calc
    affineLift f z = affineLift f (h • L.symm (y, 1)) := congrArg (affineLift f) hz
    _ = h * affineLift f (L.symm (y, 1)) := by rw [map_smul, smul_eq_mul]
    _ = h * projectiveTransportAffine L f y := rfl

end Papers.AffineCoordinates

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/SubfieldRestorationChart.lean -/






@[expose] public section

/-!
# A positive restoration chart whose coefficients lie in the field

If some prescribed neighboring value is positive, a half-sum gives the
chart coefficient.  Otherwise a further actual facet makes the sum of
neighboring supports strictly positive on the old polytope, and a small
rational coefficient works.  The exceptional all-coplanar simplex case
is excluded by the proved retention-facet theorem for the original
extension.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

namespace SimplexFacetPresentation

variable {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q ι)

theorem other_facet_of_all_coplanar
    (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (ha : D.AdmissiblePoint a) (hzero : ∀ i, D.form (some i) a = 0) :
    ∃ G : FacetType Q, ∀ i, G ≠ D.facet i := by
  obtain ⟨x, hx⟩ := Q.vertices_nonempty
  obtain ⟨G, hGT, _, hGa⟩ := D.retention_facet R a hvertices ha ⟨x, hx⟩
  refine ⟨G, ?_⟩
  intro i hi
  cases i with
  | none => exact hGT (congrArg (fun F : FacetType Q => F.val.val) hi)
  | some j =>
    rw [hi] at hGa
    have hz := (D.chosen_form_zero_iff (some j) a).mpr (hzero j)
    exact (ne_of_gt hGa) hz

theorem exists_field_forms
    (K : Subfield ℝ) (hQK : CoordinatesIn K Q) :
    ∃ f : Option ι → (Fin d → K) →ᵃ[K] K,
      ∀ i, SupportsFace Q (D.facet i).val.val (extendFieldAffine K (f i)) := by
  have h (i : Option ι) := exists_field_facet_form K Q D.fullDim hQK
    (D.facet i).val.val (D.facet i).property
  exact ⟨fun i => Classical.choose (h i), fun i => Classical.choose_spec (h i)⟩

theorem exists_field_positive_chart
    (K : Subfield ℝ) (t : ι → K) (ht : ∀ i, 0 ≤ (t i : ℝ))
    (hcase : (∃ i, 0 < (t i : ℝ)) ∨ ∃ G : FacetType Q, ∀ i, G ≠ D.facet i) :
    ∃ ε : K, ε ≠ 0 ∧
      (∀ x ∈ Q.vertices, 0 < positiveRestorationChart D.basis (ε : ℝ) x) ∧
      0 < homogeneousEvaluation (restorationVector D.basis (fun i => (t i : ℝ)))
        (positiveRestorationChart D.basis (ε : ℝ)) := by
  rcases hcase with hpos | ⟨G, hG⟩
  · have hsum : 0 < ∑ i, (t i : ℝ) := by
      obtain ⟨i, hi⟩ := hpos
      exact lt_of_lt_of_le hi (Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ _))
    let ε : K := (∑ i, t i) / 2
    have hcast : (ε : ℝ) = (∑ i, (t i : ℝ)) / 2 := by
      have htwo : ((2 : K) : ℝ) = 2 := by
        simpa only [Subfield.subtype_apply] using (map_ofNat K.subtype 2)
      dsimp only [ε]
      rw [Subfield.coe_div, subfield_coe_fintype_sum, htwo]
    have hε : 0 < (ε : ℝ) := by rw [hcast]; exact half_pos hsum
    refine ⟨ε, ?_, ?_, ?_⟩
    · intro hz
      rw [hz, Subfield.coe_zero] at hε
      exact lt_irrefl _ hε
    · intro x hx
      let w : Option ι → ℝ := fun i => i.elim (ε : ℝ) (fun _ => 1)
      have hw : ∀ i, 0 < w i := by
        intro i
        cases i with
        | none => exact hε
        | some _ => exact zero_lt_one
      have h := positive_weighted_affine_basis D.basis x
        (fun i => by rw [D.basis_apply]; exact D.form_nonneg i x (subset_convexHull ℝ _ hx)) w hw
      simpa only [Fintype.sum_option, w, Option.elim_none, Option.elim_some,
        one_smul, positiveRestorationChart] using h
    · rw [positiveRestorationChart, map_add, map_smul, map_sum]
      simp only [restorationVector_none, restorationVector_some, smul_eq_mul, mul_neg_one]
      rw [hcast]
      linarith
  · have hGset : ∀ i, G.val.val ≠ (D.facet i).val.val := by
      intro i hi
      exact hG i (Subtype.ext (Subtype.ext hi))
    have hsumPos (x : E d) (hx : x ∈ Q.toSet) : 0 < ∑ i, D.basis (some i) x :=
      neighbor_support_sum_pos_of_other_facet Q (fun i => (D.facet i).val.val)
        D.basis (fun i => (D.vertex i).val)
        (fun i => (D.facet i).property)
        (fun i => by simpa only [D.basis_apply] using D.supports i)
        (fun i => subset_convexHull ℝ _ (D.vertex i).property)
        (by simpa only [D.basis_apply] using D.at_base)
        (by simpa only [D.basis_apply] using D.diagonal)
        (by simpa only [D.basis_apply] using D.off_diagonal)
        G.val.val (chosenFacetForm Q G) G.property (chosenFacetForm_supports Q G) hGset x hx
    obtain ⟨δ, hδ, hbound⟩ := finite_positive_perturbation Q.vertices
      (fun x => ∑ i, D.basis (some i) x) (D.basis none)
      (fun x hx => hsumPos x (subset_convexHull ℝ _ hx))
      (fun x hx => by rw [D.basis_apply]; exact D.form_nonneg none x (subset_convexHull ℝ _ hx))
    obtain ⟨q, hq0, hqδ⟩ := exists_rat_btwn hδ
    let ε : K := -(q : K)
    have hcast : (ε : ℝ) = -(q : ℝ) := by
      simp only [ε, Subfield.coe_neg, SubfieldClass.coe_ratCast]
    refine ⟨ε, ?_, ?_, ?_⟩
    · intro hz
      have hqz : -(q : ℝ) = 0 := by rw [← hcast, hz, Subfield.coe_zero]
      linarith
    · intro x hx
      change 0 < (ε : ℝ) * D.basis none x + (∑ i, D.basis (some i)) x
      rw [affineForm_sum_apply, hcast]
      have hb := hbound x hx
      have hn : 0 ≤ D.basis none x := by
        rw [D.basis_apply]
        exact D.form_nonneg none x (subset_convexHull ℝ _ hx)
      have hsmall := mul_le_mul_of_nonneg_right hqδ.le hn
      linarith
    · rw [positiveRestorationChart, map_add, map_smul, map_sum]
      simp only [restorationVector_none, restorationVector_some, smul_eq_mul, mul_neg_one]
      rw [hcast]
      have hsum : 0 ≤ ∑ i, (t i : ℝ) := Finset.sum_nonneg (fun i _ => ht i)
      linarith

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/FieldProjectiveChart.lean -/




@[expose] public section

/-!
# Coordinates of the explicit projective chart

The chosen chart uses only the supporting-form coefficients and a scalar
in the coordinate field.  Its normalized coordinates therefore remain in
that field.  The statement concerns the actual extreme vertices of the
projective image polytope.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem normalizedBasisChart_coordinates_in
    (K : Subfield ℝ) (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ))
    (hb : ∀ i, AffineCoefficientsIn K (b i)) (e : ι ≃ Fin d)
    (ε : ℝ) (hε : ε ≠ 0) (hεK : ε ∈ K)
    (z : E d × ℝ) (hz : (∀ j, z.1 j ∈ K) ∧ z.2 ∈ K) :
    ∀ j, normalizedImage (basisChartEquiv b e ε hε) z j ∈ K := by
  have heval (i : Option ι) : homogeneousEvaluation z (b i) ∈ K :=
    (hb i).homogeneous z hz
  have hden : (basisChartEquiv b e ε hε z).2 ∈ K := by
    rw [basisChartEquiv_snd]
    exact K.add_mem (K.mul_mem hεK (heval none))
      (K.sum_mem (fun i _ => heval (some i)))
  intro j
  change (basisChartEquiv b e ε hε z).2⁻¹ *
    (basisChartEquiv b e ε hε z).1 j ∈ K
  rw [basisChartEquiv_fst]
  exact K.mul_mem (K.inv_mem hden) (heval (some (e.symm j)))

theorem projectivePolytope_coordinates
    (K : Subfield ℝ) (P : ConvexPolytope d)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (q : VertexType P → E d) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • (q v, 1))
    (hq : ∀ v j, q v j ∈ K) : CoordinatesIn K (projectivePolytope P L q h hh hL) := by
  intro x hx j
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact hq v j

theorem imageVertex_trans
    {P Q R : ConvexPolytope d} (φ : FaceType P ≃o FaceType Q)
    (ψ : FaceType Q ≃o FaceType R) (v : VertexType P) :
    imageVertex (φ.trans ψ) v = imageVertex ψ (imageVertex φ v) := by
  apply vertexFace_injective R
  rw [imageVertex_face, imageVertex_face, imageVertex_face]
  rfl

theorem facetEquivOfFaceOrder_trans
    {P Q R : ConvexPolytope d} (φ : FaceType P ≃o FaceType Q)
    (ψ : FaceType Q ≃o FaceType R) (F : FacetType P) :
    facetEquivOfFaceOrder (φ.trans ψ) F =
      facetEquivOfFaceOrder ψ (facetEquivOfFaceOrder φ F) := rfl

namespace SimplexFacetPresentation

theorem Aligned.trans
    {P Q R : ConvexPolytope d}
    {D₁ : SimplexFacetPresentation P ι} {D₂ : SimplexFacetPresentation Q ι}
    {D₃ : SimplexFacetPresentation R ι}
    {φ : FaceType P ≃o FaceType Q} {ψ : FaceType Q ≃o FaceType R}
    (h₁ : D₁.Aligned D₂ φ) (h₂ : D₂.Aligned D₃ ψ) :
    D₁.Aligned D₃ (φ.trans ψ) := by
  constructor
  · intro i
    rw [h₂.1 i, h₁.1 i, facetEquivOfFaceOrder_trans]
  · intro i
    rw [h₂.2 i, h₁.2 i, imageVertex_trans]

theorem Aligned.withForms_right
    {P Q : ConvexPolytope d}
    {D₁ : SimplexFacetPresentation P ι} {D₂ : SimplexFacetPresentation Q ι}
    {φ : FaceType P ≃o FaceType Q} (h : D₁.Aligned D₂ φ)
    (f : Option ι → E d →ᵃ[ℝ] ℝ)
    (hf : ∀ i, SupportsFace Q (D₂.facet i).val.val (f i)) :
    D₁.Aligned (D₂.withForms f hf) φ := h

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/ProjectiveSimplexPresentation.lean -/



@[expose] public section

/-!
# Transporting a simplex-facet presentation through a positive chart

The transformed supporting forms are the literal inverse homogeneous
transforms of the original forms.  Their zero sets are proved to be the
images of the original faces.  This identifies the admissibility signs
and the coplanarity pattern of a new homogeneous point.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

namespace SimplexFacetPresentation

variable {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q ι)

def projective
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (q : VertexType Q → E d) (h : VertexType Q → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) :
    SimplexFacetPresentation (projectivePolytope Q L q h hh hL) ι :=
  (D.transport (projectivePolytopeFaceOrderIso Q L q h hh hL)).withForms
    (fun i => projectiveTransportAffine L (D.form i))
    (fun i => positiveProjectiveFaceOrderIso_supports Q _ L
      (projectiveVertexEquiv Q L q h hh hL) h hh hL (D.facet i).val
      (D.form i) (D.supports i))

@[simp] theorem projective_form
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (q : VertexType Q → E d) (h : VertexType Q → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • (q v, 1))
    (i : Option ι) :
    (D.projective L q h hh hL).form i = projectiveTransportAffine L (D.form i) := by
  simp only [projective, withForms]

theorem projective_aligned
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (q : VertexType Q → E d) (h : VertexType Q → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) :
    D.Aligned (D.projective L q h hh hL) (projectivePolytopeFaceOrderIso Q L q h hh hL) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem projective_admissible_of_homogeneous
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (q : VertexType Q → E d) (h : VertexType Q → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • (q v, 1))
    (z : E d × ℝ) (a : E d) (c : ℝ) (hc : 0 < c)
    (hz : L z = c • (a, 1))
    (hbase : homogeneousEvaluation z (D.form none) < 0)
    (hsides : ∀ i, 0 ≤ homogeneousEvaluation z (D.form (some i))) :
    (D.projective L q h hh hL).AdmissiblePoint a := by
  constructor
  · change projectiveTransportAffine L (D.form none) a < 0
    rw [projectiveTransportAffine_homogeneous_scaled L (D.form none) z a c hz] at hbase
    by_contra hn
    have hg : 0 ≤ projectiveTransportAffine L (D.form none) a := le_of_not_gt hn
    have hm := mul_nonneg hc.le hg
    linarith
  · intro i
    change 0 ≤ projectiveTransportAffine L (D.form (some i)) a
    have hi := hsides i
    rw [projectiveTransportAffine_homogeneous_scaled L (D.form (some i)) z a c hz] at hi
    exact (mul_nonneg_iff_of_pos_left hc).mp hi

theorem projective_form_zero_iff
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (q : VertexType Q → E d) (h : VertexType Q → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • (q v, 1))
    (z : E d × ℝ) (a : E d) (c : ℝ) (hc : c ≠ 0)
    (hz : L z = c • (a, 1)) (i : Option ι) :
    (D.projective L q h hh hL).form i a = 0 ↔
      homogeneousEvaluation z (D.form i) = 0 := by
  change projectiveTransportAffine L (D.form i) a = 0 ↔ _
  rw [projectiveTransportAffine_homogeneous_scaled L (D.form i) z a c hz]
  exact (mul_eq_zero.trans (or_iff_right hc)).symm

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/FieldExtension.lean -/



@[expose] public section

/-!
# Restoration over every real subfield

For an actual extension of a polytope through a simplex facet, any
realization of the old face lattice over a real subfield can be extended,
after a positive projective change of chart, over that same subfield.
The original actual polytope supplies the vertex-retention condition.
The prescribed coplanarity pattern is copied by the field values zero
and one; it is not an assumed solution of a realization problem.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

namespace SimplexFacetPresentation

variable {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q ι)

theorem extension_realizable_over
    (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : D.AdmissiblePoint a)
    (K : Subfield ℝ) (hQK : RealizableOver Q K) : RealizableOver R K := by
  obtain ⟨Q', ⟨φ⟩, hQ'K⟩ := hQK
  let D₀ := D.transport φ
  obtain ⟨fK, hfK⟩ := D₀.exists_field_forms K hQ'K
  let D₁ := D₀.withForms (fun i => extendFieldAffine K (fK i)) hfK
  have hD₁ : D.Aligned D₁ φ := D.transport_aligned φ
  have hb (i : Option ι) : D₁.basis i = extendFieldAffine K (fK i) := D₁.basis_apply i
  have hbK (i : Option ι) : AffineCoefficientsIn K (D₁.basis i) := by
    rw [hb i]
    exact extendFieldAffine_coefficients K (fK i)
  let t : ι → K := fun i => if D.form (some i) a = 0 then 0 else 1
  have ht (i : ι) : 0 ≤ (t i : ℝ) := by
    by_cases hi : D.form (some i) a = 0 <;> simp [t, hi]
  have hmask (i : ι) : D.form (some i) a = 0 ↔ (t i : ℝ) = 0 := by
    by_cases hi : D.form (some i) a = 0 <;> simp [t, hi]
  have hcase : (∃ i, 0 < (t i : ℝ)) ∨ ∃ G : FacetType Q', ∀ i, G ≠ D₁.facet i := by
    by_cases hzero : ∀ i, D.form (some i) a = 0
    · obtain ⟨G, hG⟩ := D.other_facet_of_all_coplanar R a hvertices ha hzero
      refine Or.inr ⟨facetEquivOfFaceOrder φ G, ?_⟩
      intro i hi
      exact hG i ((facetEquivOfFaceOrder φ).injective (hi.trans (hD₁.1 i)))
    · push_neg at hzero
      obtain ⟨i, hi⟩ := hzero
      exact Or.inl ⟨i, by simp [t, hi]⟩
  obtain ⟨ε, hε, hchart, hchartnew⟩ := D₁.exists_field_positive_chart K t ht hcase
  have hεR : (ε : ℝ) ≠ 0 := by
    intro heq
    apply hε
    exact Subtype.ext (by simpa only [Subfield.coe_zero] using heq)
  let rK : Option ι → K := fun i => i.elim (-1) t
  have hrK : (fun i => (rK i : ℝ)) = restorationValues (fun i => (t i : ℝ)) := by
    funext i
    cases i <;> simp only [rK, restorationValues, Option.elim_none, Option.elim_some,
      Subfield.coe_neg, Subfield.coe_one]
  let z := restorationVector D₁.basis (fun i => (t i : ℝ))
  have hzK : (∀ j, z.1 j ∈ K) ∧ z.2 ∈ K := by
    have hr := real_solution_coordinates_in K D₁.basis fK hb rK
    rw [hrK] at hr
    exact hr
  let e : ι ≃ Fin d := (Fintype.equivFin ι).trans (finCongr D₁.index_card)
  let L := basisChartEquiv D₁.basis e (ε : ℝ) hεR
  let g := positiveRestorationChart D₁.basis (ε : ℝ)
  have hden (w : E d × ℝ) : (L w).2 = homogeneousEvaluation w g :=
    basisChartEquiv_snd_form D₁.basis e (ε : ℝ) hεR w
  let q : VertexType Q' → E d := fun v => normalizedImage L (v.val, 1)
  let h : VertexType Q' → ℝ := fun v => g v.val
  have hh (v : VertexType Q') : 0 < h v := hchart v.val v.property
  have hdenold (v : VertexType Q') : (L (v.val, 1)).2 = h v := by
    rw [hden, homogeneousEvaluation_homogenize]
  have hL (v : VertexType Q') : L (v.val, 1) = h v • (q v, 1) := by
    have hn : (L (v.val, 1)).2 ≠ 0 := by rw [hdenold v]; exact ne_of_gt (hh v)
    simpa only [hdenold v] using normalizedImage_lift L (v.val, 1) hn
  let Q'' := projectivePolytope Q' L q h hh hL
  let ψ := projectivePolytopeFaceOrderIso Q' L q h hh hL
  let D₂ := D₁.projective L q h hh hL
  have hD₂ : D.Aligned D₂ (φ.trans ψ) :=
    hD₁.trans (D₁.projective_aligned L q h hh hL)
  let a' := normalizedImage L z
  let c := (L z).2
  have hc : 0 < c := by
    change 0 < (L z).2
    rw [hden]
    exact hchartnew
  have hzL : L z = c • (a', 1) := normalizedImage_lift L z (ne_of_gt hc)
  have hzbase : homogeneousEvaluation z (D₁.form none) < 0 := by
    rw [← D₁.basis_apply, restorationVector_none]
    norm_num
  have hzside (i : ι) : 0 ≤ homogeneousEvaluation z (D₁.form (some i)) := by
    rw [← D₁.basis_apply, restorationVector_some]
    exact ht i
  have ha' : D₂.AdmissiblePoint a' :=
    D₁.projective_admissible_of_homogeneous L q h hh hL z a' c hc hzL hzbase hzside
  have hsame : D.SameCoplanar a D₂ a' := by
    intro i
    change D.form (some i) a = 0 ↔ (D₁.projective L q h hh hL).form (some i) a' = 0
    rw [D₁.projective_form_zero_iff L q h hh hL z a' c (ne_of_gt hc) hzL (some i)]
    rw [← D₁.basis_apply, restorationVector_some]
    exact hmask i
  have hqK (v : VertexType Q') (j : Fin d) : q v j ∈ K :=
    normalizedBasisChart_coordinates_in K D₁.basis hbK e (ε : ℝ) hεR ε.property
      (v.val, 1) ⟨hQ'K v.val v.property, K.one_mem⟩ j
  have hQ''K : CoordinatesIn K Q'' :=
    projectivePolytope_coordinates K Q' L q h hh hL hqK
  have ha'K : ∀ j, a' j ∈ K :=
    normalizedBasisChart_coordinates_in K D₁.basis hbK e (ε : ℝ) hεR ε.property z hzK
  obtain ⟨R', hR', hRR'⟩ :=
    D.realize_extension_from_admissible_point D₂ (φ.trans ψ) hD₂
      R a a' hvertices ha ha' hsame
  refine ⟨R', hRR', ?_⟩
  intro x hx j
  rw [hR'] at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ha'K j
  · exact hQ''K x hx j

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/SimpleDeletionFields.lean -/




@[expose] public section

/-!
# Simple vertex deletion preserves every real realization field

Both implications concern ordinary convex polytopes, their actual
extreme vertices, and their full face orders.  The simplex-facet
presentation used in restoration is derived from the given simple
vertex.  No coordinate-field or extra incidence hypothesis is retained
in the final statement.

This is the field clause of Theorem 3.  Its separate rational-density
clause is not included in this theorem's name or conclusion.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem RealizableOver.restore_simple_vertex
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) (K : Subfield ℝ)
    (hQK : RealizableOver (deleteVertex P v.val hne) K) : RealizableOver P K := by
  obtain ⟨D, _, _, ha⟩ := exists_deletion_simplexFacetPresentation P hP v hs hcard hne
  apply D.extension_realizable_over P v.val _ ha K hQK
  exact (Finset.insert_erase v.property).symm

theorem simpleDeletion_realizable_iff
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) (K : Subfield ℝ) :
    RealizableOver P K ↔ RealizableOver (deleteVertex P v.val hne) K :=
  ⟨RealizableOver.delete_of_simple P hP v hs hcard hne K,
    RealizableOver.restore_simple_vertex P hP v hs hcard hne K⟩

theorem simpleDeletionFieldsClaim : SimpleDeletionFieldsClaim := by
  intro d P v hP hcard hs hne K
  exact simpleDeletion_realizable_iff P hP v hs hcard hne K

end Papers.Polytopes

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/HomogeneousConvex.lean -/




@[expose] public section

noncomputable section
namespace Papers.Coordinates
open Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem homogeneousSpan_mono {S T : Set V} (h : S ⊆ T) :
    homogeneousSpan (K := ℝ) S ≤ homogeneousSpan (K := ℝ) T :=
  Submodule.span_mono (Set.image_mono h)

theorem homogeneousSpan_convexHull (S : Set V) (hS : S.Nonempty) :
    homogeneousSpan (K := ℝ) (convexHull ℝ S) = homogeneousSpan (K := ℝ) S := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact (homogenize_mem_span_iff hS x).mpr (convexHull_subset_affineSpan (𝕜 := ℝ) S hx)
  · exact homogeneousSpan_mono (subset_convexHull ℝ S)

end Papers.Coordinates

namespace Papers.Coordinates
open Set
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem span_scaled_image (p : ι → V) (c : ι → K) (S : Set ι)
    (hc : ∀ i ∈ S, c i ≠ 0) :
    Submodule.span K ((fun i => c i • p i) '' S) = Submodule.span K (p '' S) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_image_of_mem p hi))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    apply (Submodule.smul_mem_iff _ (hc i hi)).mp
    exact Submodule.subset_span (Set.mem_image_of_mem _ hi)

end Papers.Coordinates

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/FacetFrames.lean -/






@[expose] public section

/-!
# Facet supports from fixed vertex frames

Each actual facet admits a frame consisting of d independent facet
vertices and one outside vertex.  After transport of the vertex labels,
the interpolation formula gives the genuine inward supporting form
whenever that frame remains independent.  Consequently the coefficients
of all chosen facet forms can be varied continuously, and remain in the
coordinate field for field-valued realizations.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Filter Topology
open scoped Classical BigOperators
open Papers.AffineCoordinates Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

structure FacetFrame (P : ConvexPolytope d) (F : Set (E d)) where
  vertex : Option (Fin d) → VertexType P
  inside : ∀ i, (vertex (some i)).val ∈ F
  outside : (vertex none).val ∉ F
  independent : LinearIndependent ℝ (fun i => ((vertex i).val, (1 : ℝ)))

theorem exists_facetFrame
    (P : ConvexPolytope d) (hP : P.IsFullDim) (F : Set (E d)) (hF : IsFacet P F) :
    Nonempty (FacetFrame P F) := by
  let PF := facePolytope P hF.1
  let v : VertexType PF → E d × ℝ := fun u => (u.val, 1)
  have hspan : Submodule.span ℝ (Set.range v) = homogeneousSpan (K := ℝ) F := by
    have hr : Set.range v = homogenize (K := ℝ) '' (PF.vertices : Set (E d)) := by
      ext z
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨u.val, u.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hr]
    change homogeneousSpan (K := ℝ) (PF.vertices : Set (E d)) = _
    rw [← homogeneousSpan_convexHull _ PF.vertices_nonempty]
    exact congrArg (homogeneousSpan (K := ℝ)) (facePolytope_toSet P hF.1)
  obtain ⟨κ, j, hj, hsp, hli⟩ := exists_linearIndependent' ℝ v
  letI : Finite κ := Finite.of_injective j hj
  letI : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = d := by
    have hc := finrank_span_eq_card hli
    rw [hsp, hspan, finrank_homogeneousSpan hF.1.2] at hc
    exact hc.symm.trans (hF.2.trans hP)
  let e : Fin d ≃ κ := ((Fintype.equivFin κ).trans (finCongr hκ)).symm
  let p : Fin d → VertexType P := fun i =>
    ⟨(j (e i)).val, (Finset.mem_filter.mp (j (e i)).property).1⟩
  have hpF (i : Fin d) : (p i).val ∈ F :=
    (Finset.mem_filter.mp (j (e i)).property).2
  have hpi : LinearIndependent ℝ (fun i => ((p i).val, (1 : ℝ))) :=
    hli.comp e e.injective
  have hpspan : Submodule.span ℝ (Set.range (fun i => ((p i).val, (1 : ℝ)))) =
      homogeneousSpan (K := ℝ) F := by
    have hr : Set.range (fun i => ((p i).val, (1 : ℝ))) = Set.range (v ∘ j) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨i, rfl⟩
        obtain ⟨k, rfl⟩ := e.surjective i
        exact ⟨k, rfl⟩
    rw [hr, hsp, hspan]
  obtain ⟨q, hqF⟩ := exists_vertex_outside_facet P F hF
  have hqspan : (q.val, (1 : ℝ)) ∉
      Submodule.span ℝ (Set.range (fun i => ((p i).val, (1 : ℝ)))) := by
    rw [hpspan]
    intro hq
    exact vertex_notMem_affineSpan_face P hF.1 q.property hqF
      ((homogenize_mem_span_iff hF.1.2 q.val).mp hq)
  refine ⟨{
    vertex := fun i => i.elim q p
    inside := hpF
    outside := hqF
    independent := ?_
  }⟩
  exact linearIndependent_option.mpr ⟨hpi, hqspan⟩

theorem selected_facet_span_eq
    (P : ConvexPolytope d) (hP : P.IsFullDim) (F : Set (E d)) (hF : IsFacet P F)
    (p : Fin d → E d) (hp : ∀ i, p i ∈ F)
    (hli : LinearIndependent ℝ (fun i => (p i, (1 : ℝ)))) :
    Submodule.span ℝ (Set.range (fun i => (p i, (1 : ℝ)))) = homogeneousSpan (K := ℝ) F := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact homogenize_mem_span (hp i)
  · rw [finrank_span_eq_card hli, Fintype.card_fin, finrank_homogeneousSpan hF.1.2]
    exact (hF.2.trans hP).symm

namespace FacetFrame

variable {P : ConvexPolytope d} {F : Set (E d)} (A : FacetFrame P F)

def points (q : VertexType P → E d) : Option (Fin d) → E d := fun i => q (A.vertex i)

def values : Option (Fin d) → ℝ := Pi.single none 1

def coefficients (q : VertexType P → E d) : Option (Fin d) → ℝ :=
  affineFrameCoefficients (A.points q) values

def form (q : VertexType P → E d) : E d →ᵃ[ℝ] ℝ :=
  affineFrameForm (A.points q) values

theorem determinant_ne : (affineFrameMatrix (A.points Subtype.val)).det ≠ 0 :=
  affineFrameMatrix_det_ne_zero _ A.independent

theorem continuous_points : Continuous A.points :=
  continuous_pi (fun i => continuous_apply (A.vertex i))

theorem continuousAt_coefficients : ContinuousAt A.coefficients (Subtype.val : VertexType P → E d) :=
  (continuousAt_affineFrameCoefficients (A.points Subtype.val) A.determinant_ne values).comp
    A.continuous_points.continuousAt

theorem eventually_determinant_ne :
    ∀ᶠ q in 𝓝 (Subtype.val : VertexType P → E d), (affineFrameMatrix (A.points q)).det ≠ 0 :=
  A.continuous_points.continuousAt.tendsto.eventually
    (affineFrameMatrix_eventually_nonsingular (A.points Subtype.val) A.determinant_ne)

theorem supports_at_realization
    (hP : P.IsFullDim) (hF : IsFacet P F) (Q : ConvexPolytope d)
    (φ : FaceType P ≃o FaceType Q)
    (hdet : (affineFrameMatrix (A.points (fun v => (imageVertex φ v).val))).det ≠ 0) :
    SupportsFace Q (φ ⟨F, hF.1⟩).val (A.form (fun v => (imageVertex φ v).val)) := by
  let q : VertexType P → E d := fun v => (imageVertex φ v).val
  let G := (φ ⟨F, hF.1⟩).val
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  have hG : IsFacet Q G := (imageFace_isFacet_iff φ ⟨F, hF.1⟩).mpr hF
  have hpG (i : Fin d) : A.points q (some i) ∈ G :=
    (imageVertex_mem_iff φ (A.vertex (some i)) ⟨F, hF.1⟩).mpr (A.inside i)
  have hqG : A.points q none ∉ G := by
    intro h
    exact A.outside ((imageVertex_mem_iff φ (A.vertex none) ⟨F, hF.1⟩).mp h)
  have hli := affineFrameMatrix_linearIndependent (A.points q) hdet
  have hli' : LinearIndependent ℝ (fun i : Fin d => (A.points q (some i), (1 : ℝ))) :=
    hli.comp Option.some (Option.some_injective (Fin d))
  have hspan := selected_facet_span_eq Q hQ G hG (fun i => A.points q (some i)) hpG hli'
  have hzero (i : Fin d) : A.form q (A.points q (some i)) = 0 := by
    exact (affineFrameForm_at_point (A.points q) hdet values (some i)).trans
      (by simp [values])
  have hone : A.form q (A.points q none) = 1 := by
    exact (affineFrameForm_at_point (A.points q) hdet values none).trans
      (by simp only [values, Pi.single_eq_same])
  have hker : homogeneousSpan (K := ℝ) G ≤ (affineLift (A.form q)).ker := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change homogeneousEvaluation (A.points q (some i), (1 : ℝ)) (A.form q) = 0
    rw [homogeneousEvaluation_homogenize, hzero i]
  apply supportsFace_of_vanishes_facet Q hQ G hG (A.form q) _ (A.points q none)
    (subset_convexHull ℝ _ (imageVertex φ (A.vertex none)).property) hqG
    (hone.symm ▸ zero_lt_one)
  intro x hx
  have h := hker (homogenize_mem_span hx)
  simpa only [LinearMap.mem_ker, affineLift_apply, homogenize,
    homogeneousEvaluation_homogenize] using h

theorem form_field (K : Subfield ℝ) (q : VertexType P → E d)
    (hq : ∀ v i, q v i ∈ K) : AffineCoefficientsIn K (A.form q) := by
  apply affineFrameForm_field K (A.points q) values
  · exact fun i j => hq (A.vertex i) j
  · intro i
    cases i <;> simp [values]

end FacetFrame
end Papers.Polytopes

end
end
end BundlePart12

section BundlePart13
/- Source: Papers/ContinuousFacetPresentations.lean -/





@[expose] public section

/-!
# Locally varying simplex-facet presentations

The chosen vertex frames give continuously varying supporting forms near
the original realization.  Their validity in nearby realizations follows
from the transported face incidences and the actual facet dimension.
Every frame and every nonsingularity condition is derived from the
original geometric presentation.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Filter Topology
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem imageVertex_refl (P : ConvexPolytope d) (v : VertexType P) :
    imageVertex (OrderIso.refl (FaceType P)) v = v := by
  apply vertexFace_injective P
  rw [imageVertex_face]
  rfl

namespace FacetFrame

theorem supports_original
    {P : ConvexPolytope d} {F : Set (E d)} (A : FacetFrame P F)
    (hP : P.IsFullDim) (hF : IsFacet P F) : SupportsFace P F (A.form Subtype.val) := by
  have heq : (fun v : VertexType P => (imageVertex (OrderIso.refl (FaceType P)) v).val) =
      Subtype.val := by
    funext v
    rw [imageVertex_refl]
  have hdet : (affineFrameMatrix
      (A.points (fun v => (imageVertex (OrderIso.refl (FaceType P)) v).val))).det ≠ 0 := by
    rw [heq]
    exact A.determinant_ne
  simpa only [heq, OrderIso.refl_apply] using
    A.supports_at_realization hP hF P (OrderIso.refl (FaceType P)) hdet

end FacetFrame

namespace SimplexFacetPresentation

variable {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q ι)

def reindex (e : κ ≃ ι) : SimplexFacetPresentation Q κ where
  fullDim := D.fullDim
  index_card := (Fintype.card_congr e).trans D.index_card
  facet := fun i => D.facet (i.map e)
  form := fun i => D.form (i.map e)
  supports := fun i => D.supports (i.map e)
  vertex := fun i => D.vertex (e i)
  at_base := fun i => D.at_base (e i)
  diagonal := fun i => D.diagonal (e i)
  off_diagonal := fun i j hij => D.off_diagonal (e i) (e j)
    (fun heq => hij (e.injective heq))

theorem reindex_admissible_iff (e : κ ≃ ι) (a : E d) :
    (D.reindex e).AdmissiblePoint a ↔ D.AdmissiblePoint a := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact h.2 j
  · exact fun h => ⟨h.1, fun i => h.2 (e i)⟩

theorem withForms_zero_iff
    (f : Option ι → E d →ᵃ[ℝ] ℝ)
    (hf : ∀ i, SupportsFace Q (D.facet i).val.val (f i))
    (i : Option ι) (a : E d) : f i a = 0 ↔ D.form i a = 0 := by
  obtain ⟨c, hc, heq⟩ := supportsFacet_positive_proportional Q D.fullDim
    (D.facet i).val.val (D.facet i).property (f i) (D.form i) (hf i) (D.supports i)
  rw [heq]
  change c * D.form i a = 0 ↔ D.form i a = 0
  exact mul_eq_zero.trans (or_iff_right (ne_of_gt hc))

theorem withForms_admissible_iff
    (f : Option ι → E d →ᵃ[ℝ] ℝ)
    (hf : ∀ i, SupportsFace Q (D.facet i).val.val (f i)) (a : E d) :
    (D.withForms f hf).AdmissiblePoint a ↔ D.AdmissiblePoint a := by
  have heval (i : Option ι) : ∃ c : ℝ, 0 < c ∧ f i a = c * D.form i a := by
    obtain ⟨c, hc, heq⟩ := supportsFacet_positive_proportional Q D.fullDim
      (D.facet i).val.val (D.facet i).property (f i) (D.form i) (hf i) (D.supports i)
    exact ⟨c, hc, congrArg (fun g : E d →ᵃ[ℝ] ℝ => g a) heq⟩
  have hbase : f none a < 0 ↔ D.form none a < 0 := by
    obtain ⟨c, hc, heq⟩ := heval none
    rw [heq]
    constructor
    · intro h
      by_contra hn
      have hm := mul_nonneg hc.le (le_of_not_gt hn)
      linarith
    · exact mul_neg_of_pos_of_neg hc
  have hsides (i : ι) : 0 ≤ f (some i) a ↔ 0 ≤ D.form (some i) a := by
    obtain ⟨c, hc, heq⟩ := heval (some i)
    rw [heq]
    exact mul_nonneg_iff_of_pos_left hc
  change (f none a < 0 ∧ ∀ i, 0 ≤ f (some i) a) ↔ _
  rw [hbase]
  exact and_congr Iff.rfl (forall_congr' hsides)

def facetFrame (i : Option ι) : FacetFrame Q (D.facet i).val.val :=
  Classical.choice (exists_facetFrame Q D.fullDim (D.facet i).val.val (D.facet i).property)

def localForm (q : VertexType Q → E d) (i : Option ι) : E d →ᵃ[ℝ] ℝ :=
  (D.facetFrame i).form q

def GoodFrames (q : VertexType Q → E d) : Prop :=
  ∀ i : Option ι, (affineFrameMatrix ((D.facetFrame i).points q)).det ≠ 0

theorem goodFrames_original : D.GoodFrames Subtype.val :=
  fun i => (D.facetFrame i).determinant_ne

theorem eventually_goodFrames : ∀ᶠ q in 𝓝 (Subtype.val : VertexType Q → E d), D.GoodFrames q := by
  apply Filter.eventually_all.mpr
  intro i
  exact (D.facetFrame i).eventually_determinant_ne

theorem localForm_original_supports (i : Option ι) :
    SupportsFace Q (D.facet i).val.val (D.localForm Subtype.val i) :=
  (D.facetFrame i).supports_original D.fullDim (D.facet i).property

def frameNormalized : SimplexFacetPresentation Q ι :=
  D.withForms (D.localForm Subtype.val) D.localForm_original_supports

theorem frameNormalized_admissible_iff (a : E d) :
    D.frameNormalized.AdmissiblePoint a ↔ D.AdmissiblePoint a :=
  D.withForms_admissible_iff (D.localForm Subtype.val) D.localForm_original_supports a

theorem continuousAt_localForm_coefficients (i : Option ι) :
    ContinuousAt (fun q => affineCoefficients (D.localForm q i))
      (Subtype.val : VertexType Q → E d) := by
  have h := (D.facetFrame i).continuousAt_coefficients
  change ContinuousAt (fun q => affineFrameCoefficients
    ((D.facetFrame i).points q) FacetFrame.values) Subtype.val at h
  simpa only [localForm, FacetFrame.form, affineFrameForm,
    affineCoefficients_fromCoefficients] using h

theorem localForm_field (K : Subfield ℝ) (q : VertexType Q → E d)
    (hq : ∀ v j, q v j ∈ K) (i : Option ι) : AffineCoefficientsIn K (D.localForm q i) :=
  (D.facetFrame i).form_field K q hq

theorem localForm_supports_realization
    (Q' : ConvexPolytope d) (φ : FaceType Q ≃o FaceType Q')
    (hgood : D.GoodFrames (fun v => (imageVertex φ v).val)) (i : Option ι) :
    SupportsFace Q' (φ (D.facet i).val).val
      (D.localForm (fun v => (imageVertex φ v).val) i) :=
  (D.facetFrame i).supports_at_realization D.fullDim (D.facet i).property Q' φ (hgood i)

def localPresentation
    (Q' : ConvexPolytope d) (φ : FaceType Q ≃o FaceType Q')
    (hgood : D.GoodFrames (fun v => (imageVertex φ v).val)) : SimplexFacetPresentation Q' ι :=
  (D.transport φ).withForms (D.localForm (fun v => (imageVertex φ v).val))
    (D.localForm_supports_realization Q' φ hgood)

theorem localPresentation_aligned
    (Q' : ConvexPolytope d) (φ : FaceType Q ≃o FaceType Q')
    (hgood : D.GoodFrames (fun v => (imageVertex φ v).val)) :
    D.frameNormalized.Aligned (D.localPresentation Q' φ hgood) φ :=
  ⟨fun _ => rfl, fun _ => rfl⟩

end SimplexFacetPresentation

theorem exists_fin_deletion_presentation
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) :
    ∃ D : SimplexFacetPresentation (deleteVertex P v.val hne) (Fin d), D.AdmissiblePoint v.val := by
  obtain ⟨D, _, _, ha⟩ := exists_deletion_simplexFacetPresentation P hP v hs hcard hne
  let e : Fin d ≃ NeighborIndex P v :=
    ((Fintype.equivFin (NeighborIndex P v)).trans (finCongr D.index_card)).symm
  exact ⟨D.reindex e, (D.reindex_admissible_iff e v.val).mpr ha⟩

end Papers.Polytopes

end
end
end BundlePart13

section BundlePart14
/- Source: Papers/LocalRestoration.lean -/




@[expose] public section

/-!
# A local restoration formula

Around a fixed actual extension, the old vertex coordinates and the free
positive values of the neighboring supports are local parameters.  The
coordinates prescribed to be zero remain exactly zero.  Solving the
support equations and dehomogenizing gives the original new vertex at
the base parameter, varies continuously, and preserves each coordinate
subfield.  Positivity and nonsingularity hold on a proved neighborhood.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Filter Topology
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

namespace SimplexFacetPresentation

variable {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q (Fin d))

def localMatrix (q : VertexType Q → E d) : Matrix (Option (Fin d)) (Option (Fin d)) ℝ :=
  affineSystemMatrix (D.localForm q)

theorem localMatrix_original_det_ne : (D.localMatrix Subtype.val).det ≠ 0 := by
  have hb : (fun i => D.frameNormalized.basis i) = D.localForm Subtype.val :=
    funext (fun i => D.frameNormalized.basis_apply i)
  change (affineSystemMatrix (D.localForm Subtype.val)).det ≠ 0
  rw [← hb]
  exact affineSystemMatrix_basis_det_ne D.frameNormalized.basis

theorem continuousAt_localMatrix :
    ContinuousAt D.localMatrix (Subtype.val : VertexType Q → E d) := by
  apply continuousAt_pi.mpr
  intro i
  exact D.continuousAt_localForm_coefficients i

def apexValues (a : E d) (u : Fin d → ℝ) : Option (Fin d) → ℝ :=
  fun i => i.elim (-1) (fun j => if D.frameNormalized.form (some j) a = 0 then 0 else u j)

def originalParameters (a : E d) : Fin d → ℝ :=
  fun i => if D.frameNormalized.form (some i) a = 0 then 1
    else D.frameNormalized.form (some i) a / (-D.frameNormalized.form none a)

def localHomogeneousApex (a : E d) (p : (VertexType Q → E d) × (Fin d → ℝ)) : E d × ℝ :=
  homogeneousMatrixSolution (D.localMatrix p.1) (D.apexValues a p.2)

def localApex (a : E d) (p : (VertexType Q → E d) × (Fin d → ℝ)) : E d :=
  dehomogenizePoint (D.localHomogeneousApex a p)

theorem originalParameters_pos (a : E d) (ha : D.AdmissiblePoint a) (i : Fin d) :
    0 < D.originalParameters a i := by
  have han := (D.frameNormalized_admissible_iff a).mpr ha
  by_cases hi : D.frameNormalized.form (some i) a = 0
  · simp only [originalParameters, hi, ite_true]
    exact zero_lt_one
  · simp only [originalParameters, hi, ite_false]
    exact div_pos (lt_of_le_of_ne (han.2 i) (Ne.symm hi)) (neg_pos.mpr han.1)

theorem original_homogeneous_apex (a : E d) (ha : D.AdmissiblePoint a) :
    D.localHomogeneousApex a (Subtype.val, D.originalParameters a) =
      (-D.frameNormalized.form none a)⁻¹ • (a, (1 : ℝ)) := by
  have han := (D.frameNormalized_admissible_iff a).mpr ha
  have hb : D.frameNormalized.form none a ≠ 0 := ne_of_lt han.1
  apply homogeneousMatrixSolution_unique (D.localForm Subtype.val)
    D.localMatrix_original_det_ne
  intro i
  rw [map_smul]
  change (-D.frameNormalized.form none a)⁻¹ *
    homogeneousEvaluation (a, (1 : ℝ)) (D.frameNormalized.form i) = D.apexValues a _ i
  rw [homogeneousEvaluation_homogenize]
  cases i with
  | none =>
    change (-D.frameNormalized.form none a)⁻¹ * D.frameNormalized.form none a = -1
    field_simp
  | some i =>
    by_cases hi : D.frameNormalized.form (some i) a = 0
    · simp only [apexValues, originalParameters, Option.elim_some, hi, ite_true, mul_zero]
    · simp only [apexValues, originalParameters, Option.elim_some, hi, ite_false]
      rw [div_eq_mul_inv, mul_comm]

theorem original_homogeneous_height_pos (a : E d) (ha : D.AdmissiblePoint a) :
    0 < (D.localHomogeneousApex a (Subtype.val, D.originalParameters a)).2 := by
  rw [D.original_homogeneous_apex a ha]
  change 0 < (-D.frameNormalized.form none a)⁻¹ * 1
  rw [mul_one]
  exact inv_pos.mpr (neg_pos.mpr ((D.frameNormalized_admissible_iff a).mpr ha).1)

theorem localApex_original (a : E d) (ha : D.AdmissiblePoint a) :
    D.localApex a (Subtype.val, D.originalParameters a) = a := by
  have hc : (-D.frameNormalized.form none a)⁻¹ ≠ 0 :=
    ne_of_gt (inv_pos.mpr (neg_pos.mpr ((D.frameNormalized_admissible_iff a).mpr ha).1))
  rw [localApex, D.original_homogeneous_apex a ha]
  change ((-D.frameNormalized.form none a)⁻¹ * 1)⁻¹ •
    ((-D.frameNormalized.form none a)⁻¹ • a) = a
  rw [mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem continuous_apexValues (a : E d) : Continuous (D.apexValues a) := by
  apply continuous_pi
  intro i
  cases i with
  | none => exact continuous_const
  | some i =>
    by_cases hi : D.frameNormalized.form (some i) a = 0
    · simpa only [apexValues, Option.elim_some, hi, ite_true] using
        (continuous_const : Continuous (fun _ : Fin d → ℝ => (0 : ℝ)))
    · simpa only [apexValues, Option.elim_some, hi, ite_false] using continuous_apply i

theorem continuousAt_localHomogeneousApex (a : E d) :
    ContinuousAt (D.localHomogeneousApex a) (Subtype.val, D.originalParameters a) := by
  have hmatrix : ContinuousAt
      (fun p : (VertexType Q → E d) × (Fin d → ℝ) => D.localMatrix p.1)
      (Subtype.val, D.originalParameters a) :=
    ContinuousAt.comp' (f := fun p : (VertexType Q → E d) × (Fin d → ℝ) => p.1)
      (g := D.localMatrix) (continuousAt_localMatrix D) continuous_fst.continuousAt
  have hvalues : ContinuousAt
      (fun p : (VertexType Q → E d) × (Fin d → ℝ) => D.apexValues a p.2)
      (Subtype.val, D.originalParameters a) :=
    ((D.continuous_apexValues a).comp continuous_snd).continuousAt
  have hc : ContinuousAt (fun p : (VertexType Q → E d) × (Fin d → ℝ) =>
      (D.localMatrix p.1, D.apexValues a p.2)) (Subtype.val, D.originalParameters a) :=
    hmatrix.prodMk hvalues
  exact ContinuousAt.comp'
    (f := fun p : (VertexType Q → E d) × (Fin d → ℝ) =>
      (D.localMatrix p.1, D.apexValues a p.2))
    (g := fun z : (Matrix (Option (Fin d)) (Option (Fin d)) ℝ) ×
      (Option (Fin d) → ℝ) => homogeneousMatrixSolution z.1 z.2)
    (continuousAt_homogeneousMatrixSolution (D.localMatrix Subtype.val)
      D.localMatrix_original_det_ne (D.apexValues a (D.originalParameters a))) hc

theorem continuousAt_localApex (a : E d) (ha : D.AdmissiblePoint a) :
    ContinuousAt (D.localApex a) (Subtype.val, D.originalParameters a) :=
  (continuousAt_dehomogenizePoint _ (ne_of_gt (D.original_homogeneous_height_pos a ha))).comp
    (D.continuousAt_localHomogeneousApex a)

theorem localApex_coordinates
    (K : Subfield ℝ) (a : E d) (q : VertexType Q → E d) (u : Fin d → ℝ)
    (hq : ∀ v j, q v j ∈ K) (hu : ∀ i, u i ∈ K) :
    ∀ j, D.localApex a (q, u) j ∈ K := by
  apply dehomogenizePoint_coordinates K
  apply homogeneousMatrixSolution_coordinates K
  · intro i j
    have hF := D.localForm_field K q hq i
    cases j with
    | none => exact hF.1
    | some j => exact hF.2 j
  · intro i
    cases i with
    | none => exact K.neg_mem K.one_mem
    | some i =>
      by_cases hi : D.frameNormalized.form (some i) a = 0
      · simpa only [apexValues, Option.elim_some, hi, ite_true] using K.zero_mem
      · simpa only [apexValues, Option.elim_some, hi, ite_false] using hu i

theorem localApex_admissible_and_coplanar
    (a : E d) (Q' : ConvexPolytope d) (φ : FaceType Q ≃o FaceType Q')
    (u : Fin d → ℝ) (hu : ∀ i, 0 < u i)
    (hgood : D.GoodFrames (fun v => (imageVertex φ v).val))
    (hdet : (D.localMatrix (fun v => (imageVertex φ v).val)).det ≠ 0)
    (hc : 0 < (D.localHomogeneousApex a ((fun v => (imageVertex φ v).val), u)).2) :
    (D.localPresentation Q' φ hgood).AdmissiblePoint
        (D.localApex a ((fun v => (imageVertex φ v).val), u)) ∧
      D.frameNormalized.SameCoplanar a (D.localPresentation Q' φ hgood)
        (D.localApex a ((fun v => (imageVertex φ v).val), u)) := by
  let q : VertexType Q → E d := fun v => (imageVertex φ v).val
  let z := D.localHomogeneousApex a (q, u)
  let a' := D.localApex a (q, u)
  have heval (i : Option (Fin d)) : z.2 * D.localForm q i a' = D.apexValues a u i := by
    have h := homogeneousMatrixSolution_evaluation (D.localForm q) hdet (D.apexValues a u) i
    change homogeneousEvaluation z (D.localForm q i) = D.apexValues a u i at h
    rw [homogeneousEvaluation_dehomogenize _ (ne_of_gt hc)] at h
    exact h
  have hbase : D.localForm q none a' < 0 := by
    have h := heval none
    change z.2 * D.localForm q none a' = -1 at h
    by_contra hn
    have hm := mul_nonneg hc.le (le_of_not_gt hn)
    linarith
  have hside (i : Fin d) : 0 ≤ D.localForm q (some i) a' := by
    have hval : 0 ≤ D.apexValues a u (some i) := by
      by_cases hi : D.frameNormalized.form (some i) a = 0
      · simp only [apexValues, Option.elim_some, hi, ite_true, le_refl]
      · simpa only [apexValues, Option.elim_some, hi, ite_false] using (hu i).le
    rw [← heval (some i)] at hval
    exact (mul_nonneg_iff_of_pos_left hc).mp hval
  refine ⟨⟨hbase, hside⟩, ?_⟩
  intro i
  have h := heval (some i)
  change D.frameNormalized.form (some i) a = 0 ↔ D.localForm q (some i) a' = 0
  by_cases hi : D.frameNormalized.form (some i) a = 0
  · simp only [apexValues, Option.elim_some, hi, ite_true] at h
    exact iff_of_true hi ((mul_eq_zero.mp h).resolve_left (ne_of_gt hc))
  · simp only [apexValues, Option.elim_some, hi, ite_false] at h
    refine iff_of_false hi ?_
    intro hz
    rw [hz, mul_zero] at h
    exact (ne_of_gt (hu i)) h.symm

theorem localRestoration_neighborhood
    (a : E d) (ha : D.AdmissiblePoint a) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 (Subtype.val, D.originalParameters a),
      D.GoodFrames p.1 ∧ (D.localMatrix p.1).det ≠ 0 ∧
      0 < (D.localHomogeneousApex a p).2 ∧ (∀ i, 0 < p.2 i) ∧
      dist (D.localApex a p) a < ε ∧
      ∀ v : VertexType Q, dist (p.1 v) v.val < ε := by
  have hframes : ∀ᶠ p : (VertexType Q → E d) × (Fin d → ℝ)
      in 𝓝 (Subtype.val, D.originalParameters a), D.GoodFrames p.1 :=
    continuous_fst.continuousAt.tendsto.eventually D.eventually_goodFrames
  have hmatrix : ∀ᶠ p : (VertexType Q → E d) × (Fin d → ℝ)
      in 𝓝 (Subtype.val, D.originalParameters a), (D.localMatrix p.1).det ≠ 0 := by
    have hdet : Continuous (fun A : Matrix (Option (Fin d)) (Option (Fin d)) ℝ => A.det) :=
      continuous_id.matrix_det
    have hlocal : ContinuousAt (fun p : (VertexType Q → E d) × (Fin d → ℝ) =>
        D.localMatrix p.1) (Subtype.val, D.originalParameters a) :=
      ContinuousAt.comp'
        (f := fun p : (VertexType Q → E d) × (Fin d → ℝ) => p.1)
        (g := D.localMatrix) (continuousAt_localMatrix D) continuous_fst.continuousAt
    have hc : ContinuousAt (fun p : (VertexType Q → E d) × (Fin d → ℝ) =>
        (D.localMatrix p.1).det) (Subtype.val, D.originalParameters a) :=
      hdet.continuousAt.comp hlocal
    exact hc.eventually_ne D.localMatrix_original_det_ne
  have hheight : ∀ᶠ p in 𝓝 (Subtype.val, D.originalParameters a),
      0 < (D.localHomogeneousApex a p).2 :=
    (D.continuousAt_localHomogeneousApex a).snd.tendsto.eventually
      (Ioi_mem_nhds (D.original_homogeneous_height_pos a ha))
  have hparameters : ∀ᶠ p : (VertexType Q → E d) × (Fin d → ℝ)
      in 𝓝 (Subtype.val, D.originalParameters a), ∀ i : Fin d, 0 < p.2 i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun p : (VertexType Q → E d) × (Fin d → ℝ) => p.2 i) :=
      (continuous_apply i).comp continuous_snd
    exact hc.continuousAt.tendsto.eventually
      (Ioi_mem_nhds (D.originalParameters_pos a ha i))
  have hapex : ∀ᶠ p in 𝓝 (Subtype.val, D.originalParameters a), dist (D.localApex a p) a < ε := by
    have hc := (D.continuousAt_localApex a ha).tendsto
    rw [D.localApex_original a ha] at hc
    exact hc.eventually (Metric.ball_mem_nhds a hε)
  have hold : ∀ᶠ p : (VertexType Q → E d) × (Fin d → ℝ)
      in 𝓝 (Subtype.val, D.originalParameters a),
      ∀ v : VertexType Q, dist (p.1 v) v.val < ε := by
    apply Filter.eventually_all.mpr
    intro v
    have hc : Continuous (fun p : (VertexType Q → E d) × (Fin d → ℝ) => p.1 v) :=
      (continuous_apply v).comp continuous_fst
    have hv : ContinuousAt
        (fun p : (VertexType Q → E d) × (Fin d → ℝ) => p.1 v)
        (Subtype.val, D.originalParameters a) := hc.continuousAt
    exact hv.tendsto.eventually (Metric.ball_mem_nhds v.val hε)
  filter_upwards [hframes, hmatrix, hheight, hparameters, hapex, hold] with p h₁ h₂ h₃ h₄ h₅ h₆
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart14

section BundlePart15
/- Source: Papers/SimpleDeletionDensityRestore.lean -/





@[expose] public section

/-!
# Rational approximation lifts through simple-vertex restoration

The local formula is applied to rational core realizations and rational
free parameters in its proved neighborhood.  Its zero parameters remain
exactly zero.  The extension theorem supplies the complete face order,
and its vertex-label theorem supplies the coordinate error estimate.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

namespace SimplexFacetPresentation

theorem approximable_extension
    {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q (Fin d))
    (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : D.AdmissiblePoint a)
    (hQ : RationallyApproximable Q) : RationallyApproximable R := by
  intro ε hε
  let S : Set ((VertexType Q → E d) × (Fin d → ℝ)) := {p |
    D.GoodFrames p.1 ∧ (D.localMatrix p.1).det ≠ 0 ∧
      0 < (D.localHomogeneousApex a p).2 ∧ (∀ i, 0 < p.2 i) ∧
      dist (D.localApex a p) a < ε ∧
      ∀ v : VertexType Q, dist (p.1 v) v.val < ε}
  have hS : S ∈ 𝓝 (Subtype.val, D.originalParameters a) :=
    D.localRestoration_neighborhood a ha ε hε
  obtain ⟨Q', φ, r, hQ'rat, hparam⟩ :=
    hQ.exists_parameters_in_neighborhood (D.originalParameters a) S hS
  let q : VertexType Q → E d := fun v => (imageVertex φ v).val
  let u : Fin d → ℝ := fun i => (r i : ℝ)
  have hgood : D.GoodFrames q := hparam.1
  have hdet : (D.localMatrix q).det ≠ 0 := hparam.2.1
  have hheight : 0 < (D.localHomogeneousApex a (q, u)).2 := hparam.2.2.1
  have hu : ∀ i, 0 < u i := hparam.2.2.2.1
  have hnew : dist (D.localApex a (q, u)) a < ε := hparam.2.2.2.2.1
  have hold : ∀ v : VertexType Q, dist (q v) v.val < ε := hparam.2.2.2.2.2
  have hqK : ∀ v j, q v j ∈ rationalSubfield :=
    fun v j => hQ'rat (q v) (imageVertex φ v).property j
  have huK : ∀ i, u i ∈ rationalSubfield := fun i => ⟨r i, rfl⟩
  have haK := D.localApex_coordinates rationalSubfield a q u hqK huK
  obtain ⟨ha', hsame⟩ :=
    D.localApex_admissible_and_coplanar a Q' φ u hu hgood hdet hheight
  have han := (D.frameNormalized_admissible_iff a).mpr ha
  exact D.frameNormalized.realize_extension_close (D.localPresentation Q' φ hgood) φ
    (D.localPresentation_aligned Q' φ hgood) R a (D.localApex a (q, u))
    hvertices han ha' hsame rationalSubfield hQ'rat haK ε hnew hold

end SimplexFacetPresentation

theorem RationallyDense.restore_simple_vertex
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty)
    (hQ : RationallyDense (deleteVertex P v.val hne)) : RationallyDense P := by
  intro R hPR
  obtain ⟨φ⟩ := hPR
  have hR : R.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  let w := imageVertex φ v
  have hsw : IsSimpleVertex R w := isSimple_imageVertex φ v hs
  have hcardR : d + 1 < R.vertices.card := by
    rw [← faceOrderIso_vertex_card φ]
    exact hcard
  let hneR := simpleDeletion_nonempty R hR w hsw hcardR
  have hequiv : CombinatoriallyEquivalent (deleteVertex P v.val hne)
      (deleteVertex R w.val hneR) :=
    simpleDeletion_combinatoriallyEquivalent φ hP v hs hcard hne hneR
  have hcore := (hQ.of_equivalent hequiv).approximable
  obtain ⟨D, ha⟩ := exists_fin_deletion_presentation R hR w hsw hcardR hneR
  apply D.approximable_extension R w.val _ ha hcore
  exact (Finset.insert_erase w.property).symm

end Papers.Polytopes

end
end
end BundlePart15

section BundlePart16
/- Source: Papers/SimpleDeletionLabels.lean -/





@[expose] public section

/-!
# Simple deletion with its induced vertex correspondence

The explicit deletion face isomorphism keeps the original labels on all
remaining extreme vertices.  Hence a rational approximation of the
original polytope gives a rational approximation of its deleted hull
with the same coordinate error bound.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def simpleDeletionFaceOrderIso
    {P Q : ConvexPolytope d} (φ : FaceType P ≃o FaceType Q)
    (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hneP : (P.vertices.erase v.val).Nonempty)
    (hneQ : (Q.vertices.erase (imageVertex φ v).val).Nonempty) :
    FaceType (deleteVertex P v.val hneP) ≃o
      FaceType (deleteVertex Q (imageVertex φ v).val hneQ) := by
  let w := imageVertex φ v
  let b := vertexEquivOfFaceOrder φ
  let b' := deleteVertexEquiv b v w rfl hneP hneQ
  have hbback : imageVertex φ.symm w = v := b.symm_apply_apply v
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  have hsQ : IsSimpleVertex Q w := isSimple_imageVertex φ v hs
  have hcardQ : d + 1 < Q.vertices.card := by
    rw [← faceOrderIso_vertex_card φ]
    exact hcard
  apply faceOrderIsoOfVertexIncidence _ _ b'
    (deletion_face_forward φ hP v w rfl hs hcard hneP hneQ)
  intro G
  obtain ⟨F, hF⟩ := deletion_face_forward φ.symm hQ w v hbback hsQ hcardQ hneQ hneP G
  refine ⟨F, ?_⟩
  intro x
  have h := (hF (b' x)).symm
  have heq : deleteVertexEquiv (vertexEquivOfFaceOrder φ.symm) w v hbback hneQ hneP (b' x) = x := by
    apply Subtype.ext
    change (b.symm (b ⟨x.val, Finset.mem_of_mem_erase x.property⟩)).val = x.val
    rw [b.symm_apply_apply]
  simpa only [heq] using h

theorem simpleDeletionFaceOrderIso_vertex
    {P Q : ConvexPolytope d} (φ : FaceType P ≃o FaceType Q)
    (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hneP : (P.vertices.erase v.val).Nonempty)
    (hneQ : (Q.vertices.erase (imageVertex φ v).val).Nonempty)
    (x : VertexType (deleteVertex P v.val hneP)) :
    (imageVertex (simpleDeletionFaceOrderIso φ hP v hs hcard hneP hneQ) x).val =
      (imageVertex φ ⟨x.val, Finset.mem_of_mem_erase x.property⟩).val := by
  unfold simpleDeletionFaceOrderIso
  rw [faceOrderIsoOfVertexIncidence_vertex]
  rfl

theorem RationallyApproximable.delete_of_simple
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) (hPA : RationallyApproximable P) :
    RationallyApproximable (deleteVertex P v.val hne) := by
  intro ε hε
  obtain ⟨Q, φ, hQrat, hclose⟩ := hPA ε hε
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  have hsQ := isSimple_imageVertex φ v hs
  have hcardQ : d + 1 < Q.vertices.card := by
    rw [← faceOrderIso_vertex_card φ]
    exact hcard
  let hneQ := simpleDeletion_nonempty Q hQ (imageVertex φ v) hsQ hcardQ
  refine ⟨deleteVertex Q (imageVertex φ v).val hneQ,
    simpleDeletionFaceOrderIso φ hP v hs hcard hne hneQ, ?_, ?_⟩
  · intro x hx i
    exact hQrat x (Finset.mem_of_mem_erase hx) i
  · intro x
    rw [simpleDeletionFaceOrderIso_vertex]
    exact hclose ⟨x.val, Finset.mem_of_mem_erase x.property⟩

end Papers.Polytopes

end
end
end BundlePart16

section BundlePart17
/- Source: Papers/ProjectiveExtension.lean -/



@[expose] public section

/-!
# Restoring an arbitrary core realization in a positive chart

This version of the global restoration construction retains the explicit
projective transformation and all vertex labels.  It is used to transfer
local rational approximation back to an arbitrary realization of the
deleted type.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

namespace SimplexFacetPresentation

theorem exists_projective_admissible_point
    {Q Q' : ConvexPolytope d} (D : SimplexFacetPresentation Q ι)
    (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : D.AdmissiblePoint a)
    (φ : FaceType Q ≃o FaceType Q') :
    ∃ (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ)) (q : VertexType Q' → E d)
      (h : VertexType Q' → ℝ) (hh : ∀ v, 0 < h v)
      (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) (a' : E d),
      ((D.transport φ).projective L q h hh hL).AdmissiblePoint a' ∧
        D.SameCoplanar a ((D.transport φ).projective L q h hh hL) a' := by
  let D₀ := D.transport φ
  let K : Subfield ℝ := ⊤
  let t : ι → K := fun i => if D.form (some i) a = 0 then 0 else 1
  have ht (i : ι) : 0 ≤ (t i : ℝ) := by
    by_cases hi : D.form (some i) a = 0 <;> simp [t, hi]
  have hmask (i : ι) : D.form (some i) a = 0 ↔ (t i : ℝ) = 0 := by
    by_cases hi : D.form (some i) a = 0 <;> simp [t, hi]
  have hcase : (∃ i, 0 < (t i : ℝ)) ∨ ∃ G : FacetType Q', ∀ i, G ≠ D₀.facet i := by
    by_cases hzero : ∀ i, D.form (some i) a = 0
    · obtain ⟨G, hG⟩ := D.other_facet_of_all_coplanar R a hvertices ha hzero
      refine Or.inr ⟨facetEquivOfFaceOrder φ G, ?_⟩
      intro i hi
      exact hG i ((facetEquivOfFaceOrder φ).injective hi)
    · push_neg at hzero
      obtain ⟨i, hi⟩ := hzero
      exact Or.inl ⟨i, by simp [t, hi]⟩
  obtain ⟨ε, hε, hchart, hchartnew⟩ := D₀.exists_field_positive_chart K t ht hcase
  have hεR : (ε : ℝ) ≠ 0 := by
    intro heq
    exact hε (Subtype.ext (by simpa only [Subfield.coe_zero] using heq))
  let z := restorationVector D₀.basis (fun i => (t i : ℝ))
  let e : ι ≃ Fin d := (Fintype.equivFin ι).trans (finCongr D₀.index_card)
  let L := basisChartEquiv D₀.basis e (ε : ℝ) hεR
  let g := positiveRestorationChart D₀.basis (ε : ℝ)
  have hden (w : E d × ℝ) : (L w).2 = homogeneousEvaluation w g :=
    basisChartEquiv_snd_form D₀.basis e (ε : ℝ) hεR w
  let q : VertexType Q' → E d := fun v => normalizedImage L (v.val, 1)
  let h : VertexType Q' → ℝ := fun v => g v.val
  have hh (v : VertexType Q') : 0 < h v := hchart v.val v.property
  have hdenold (v : VertexType Q') : (L (v.val, 1)).2 = h v := by
    rw [hden, homogeneousEvaluation_homogenize]
  have hL (v : VertexType Q') : L (v.val, 1) = h v • (q v, 1) := by
    have hn : (L (v.val, 1)).2 ≠ 0 := by rw [hdenold v]; exact ne_of_gt (hh v)
    simpa only [hdenold v] using normalizedImage_lift L (v.val, 1) hn
  let a' := normalizedImage L z
  let c := (L z).2
  have hc : 0 < c := by
    change 0 < (L z).2
    rw [hden]
    exact hchartnew
  have hzL : L z = c • (a', 1) := normalizedImage_lift L z (ne_of_gt hc)
  have hzbase : homogeneousEvaluation z (D₀.form none) < 0 := by
    rw [← D₀.basis_apply, restorationVector_none]
    norm_num
  have hzside (i : ι) : 0 ≤ homogeneousEvaluation z (D₀.form (some i)) := by
    rw [← D₀.basis_apply, restorationVector_some]
    exact ht i
  refine ⟨L, q, h, hh, hL, a',
    D₀.projective_admissible_of_homogeneous L q h hh hL z a' c hc hzL hzbase hzside, ?_⟩
  intro i
  rw [D₀.projective_form_zero_iff L q h hh hL z a' c (ne_of_gt hc) hzL (some i)]
  rw [← D₀.basis_apply, restorationVector_some]
  exact hmask i

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart17

section BundlePart18
/- Source: Papers/ProjectiveMatrixCoordinates.lean -/





@[expose] public section

/-!
# Projective maps in matrix coordinates

The matrix action is conjugated by the explicit homogeneous-coordinate
equivalence.  Its normalized point map is continuous where the last
coordinate is nonzero, and preserves every real subfield when the matrix
and the point have coordinates in that subfield.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Filter Topology
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def homogeneousMatrixLinear
    (A : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) : (E d × ℝ) →ₗ[ℝ] (E d × ℝ) :=
  homogeneousCoordinates.symm.toLinearMap.comp
    (A.mulVecLin.comp homogeneousCoordinates.toLinearMap)

def homogeneousMatrixEquiv
    (A : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (hA : A.det ≠ 0) :
    (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ) := by
  have hunit : IsUnit A := A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hA)
  exact homogeneousCoordinates.trans
    ((LinearEquiv.ofBijective A.mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
        Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).trans homogeneousCoordinates.symm)

@[simp] theorem homogeneousMatrixEquiv_apply
    (A : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (hA : A.det ≠ 0) (z : E d × ℝ) :
    homogeneousMatrixEquiv A hA z = homogeneousMatrixLinear A z := rfl

def homogeneousEquivMatrix (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ)) :
    Matrix (Option (Fin d)) (Option (Fin d)) ℝ :=
  LinearMap.toMatrix' (homogeneousCoordinates.toLinearMap.comp
    (L.toLinearMap.comp homogeneousCoordinates.symm.toLinearMap))

theorem homogeneousEquivMatrix_mulVec
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ)) (z : Option (Fin d) → ℝ) :
    (homogeneousEquivMatrix L).mulVec z = homogeneousCoordinates (L (homogeneousCoordinates.symm z)) :=
  LinearMap.toMatrix'_mulVec _ z

theorem homogeneousEquivMatrix_det_ne
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ)) : (homogeneousEquivMatrix L).det ≠ 0 := by
  have hinj : Function.Injective (homogeneousEquivMatrix L).mulVec := by
    intro z w heq
    rw [homogeneousEquivMatrix_mulVec, homogeneousEquivMatrix_mulVec] at heq
    exact homogeneousCoordinates.symm.injective (L.injective (homogeneousCoordinates.injective heq))
  exact isUnit_iff_ne_zero.mp ((homogeneousEquivMatrix L).isUnit_iff_isUnit_det.mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj))

@[simp] theorem homogeneousMatrixLinear_equivMatrix
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ)) (z : E d × ℝ) :
    homogeneousMatrixLinear (homogeneousEquivMatrix L) z = L z := by
  change homogeneousCoordinates.symm
    ((homogeneousEquivMatrix L).mulVec (homogeneousCoordinates z)) = L z
  rw [homogeneousEquivMatrix_mulVec, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

def matrixProjectivePoint
    (A : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (x : E d) : E d :=
  dehomogenizePoint (homogeneousMatrixLinear A (x, 1))

theorem dehomogenize_smul_homogenize (x : E d) (c : ℝ) (hc : c ≠ 0) :
    dehomogenizePoint (c • (x, (1 : ℝ))) = x := by
  change (c * 1)⁻¹ • (c • x) = x
  rw [mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem matrixProjectivePoint_equiv
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ)) (x y : E d) (c : ℝ) (hc : c ≠ 0)
    (hL : L (x, 1) = c • (y, 1)) :
    matrixProjectivePoint (homogeneousEquivMatrix L) x = y := by
  rw [matrixProjectivePoint, homogeneousMatrixLinear_equivMatrix, hL,
    dehomogenize_smul_homogenize y c hc]

theorem homogeneousMatrixLinear_coordinates
    (K : Subfield ℝ) (A : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (hA : ∀ i j, A i j ∈ K) (z : E d × ℝ)
    (hz : (∀ i, z.1 i ∈ K) ∧ z.2 ∈ K) :
    (∀ i, (homogeneousMatrixLinear A z).1 i ∈ K) ∧
      (homogeneousMatrixLinear A z).2 ∈ K := by
  have hz' (i : Option (Fin d)) : homogeneousCoordinates z i ∈ K := by
    cases i with
    | none => exact hz.2
    | some i => exact hz.1 i
  have hcoeff (i : Option (Fin d)) : A.mulVec (homogeneousCoordinates z) i ∈ K := by
    rw [Matrix.mulVec_apply_eq_sum]
    exact K.sum_mem (fun j _ => K.mul_mem (hA i j) (hz' j))
  exact ⟨fun i => hcoeff (some i), hcoeff none⟩

theorem matrixProjectivePoint_coordinates
    (K : Subfield ℝ) (A : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (hA : ∀ i j, A i j ∈ K) (x : E d) (hx : ∀ i, x i ∈ K) :
    ∀ i, matrixProjectivePoint A x i ∈ K :=
  dehomogenizePoint_coordinates K _
    (homogeneousMatrixLinear_coordinates K A hA (x, 1) ⟨hx, K.one_mem⟩)

theorem continuous_homogeneousCoordinates :
    Continuous (homogeneousCoordinates : (E d × ℝ) → Option (Fin d) → ℝ) :=
  homogeneousCoordinates.toLinearMap.continuous_of_finiteDimensional

theorem continuous_homogeneousMatrixLinear :
    Continuous (fun p : (Matrix (Option (Fin d)) (Option (Fin d)) ℝ) × (E d × ℝ) =>
      homogeneousMatrixLinear p.1 p.2) :=
  continuous_homogeneousCoordinates_symm.comp
    (continuous_fst.matrix_mulVec (continuous_homogeneousCoordinates.comp continuous_snd))

theorem continuous_matrixHomogeneousPoint :
    Continuous (fun p : (Matrix (Option (Fin d)) (Option (Fin d)) ℝ) × E d =>
      homogeneousMatrixLinear p.1 (p.2, (1 : ℝ))) :=
  continuous_homogeneousMatrixLinear.comp
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))

theorem continuousAt_matrixProjectivePoint
    (A : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (x : E d)
    (h : (homogeneousMatrixLinear A (x, 1)).2 ≠ 0) :
    ContinuousAt (fun p : (Matrix (Option (Fin d)) (Option (Fin d)) ℝ) × E d =>
      matrixProjectivePoint p.1 p.2) (A, x) := by
  change ContinuousAt (dehomogenizePoint ∘
    (fun p : (Matrix (Option (Fin d)) (Option (Fin d)) ℝ) × E d =>
      homogeneousMatrixLinear p.1 (p.2, (1 : ℝ)))) (A, x)
  exact ContinuousAt.comp
    (f := fun p : (Matrix (Option (Fin d)) (Option (Fin d)) ℝ) × E d =>
      homogeneousMatrixLinear p.1 (p.2, (1 : ℝ)))
    (x := (A, x))
    (continuousAt_dehomogenizePoint (homogeneousMatrixLinear A (x, 1)) h)
    continuous_matrixHomogeneousPoint.continuousAt

def matrixFromEntries {n : Type*} (u : n × n → ℝ) : Matrix n n ℝ := fun i j => u (i, j)

theorem continuous_matrixFromEntries {n : Type*} :
    Continuous (matrixFromEntries : (n × n → ℝ) → Matrix n n ℝ) :=
  continuous_pi (fun i => continuous_pi (fun j => continuous_apply (i, j)))

end Papers.Polytopes

end
end
end BundlePart18

section BundlePart19
/- Source: Papers/ProjectiveRationalApproximation.lean -/





@[expose] public section

/-!
# Rational approximation is invariant under positive projective maps

The projective transformation itself is approximated by rational matrices
at the same time as the old realization is approximated.  Nonsingularity
and positivity hold on a proved neighborhood, so each resulting image is
an actual polytope with the full intended face order.  This argument does
not assume that the original projective transformation is rational.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Filter Topology
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem positiveProjective_approximation_neighborhood
    (P Q : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (b : VertexType P ≃ VertexType Q) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 ((Subtype.val : VertexType P → E d),
        (fun ij => homogeneousEquivMatrix L ij.1 ij.2)),
      (matrixFromEntries p.2).det ≠ 0 ∧
      (∀ v : VertexType P, 0 < (homogeneousMatrixLinear (matrixFromEntries p.2) (p.1 v, 1)).2) ∧
      ∀ v : VertexType P, dist (matrixProjectivePoint (matrixFromEntries p.2) (p.1 v)) (b v).val < ε := by
  let A₀ := homogeneousEquivMatrix L
  let u₀ : (Option (Fin d)) × (Option (Fin d)) → ℝ := fun ij => A₀ ij.1 ij.2
  let p₀ := ((Subtype.val : VertexType P → E d), u₀)
  have hAcont : Continuous (fun p : (VertexType P → E d) ×
      ((Option (Fin d)) × (Option (Fin d)) → ℝ) => matrixFromEntries p.2) :=
    continuous_matrixFromEntries.comp continuous_snd
  have hdet : ∀ᶠ p in 𝓝 p₀, (matrixFromEntries p.2).det ≠ 0 :=
    hAcont.matrix_det.continuousAt.eventually_ne (homogeneousEquivMatrix_det_ne L)
  have hheight (v : VertexType P) : 0 < (homogeneousMatrixLinear A₀ (v.val, 1)).2 := by
    rw [homogeneousMatrixLinear_equivMatrix, hL v]
    simpa only [Prod.smul_snd, smul_eq_mul, mul_one] using hh v
  have hpoint (v : VertexType P) : matrixProjectivePoint A₀ v.val = (b v).val :=
    matrixProjectivePoint_equiv L v.val (b v).val (h v) (ne_of_gt (hh v)) (hL v)
  have hparamcont (v : VertexType P) : Continuous
      (fun p : (VertexType P → E d) × ((Option (Fin d)) × (Option (Fin d)) → ℝ) =>
        (matrixFromEntries p.2, p.1 v)) :=
    hAcont.prodMk ((continuous_apply v).comp continuous_fst)
  have hpositive : ∀ᶠ p in 𝓝 p₀,
      ∀ v : VertexType P, 0 < (homogeneousMatrixLinear (matrixFromEntries p.2) (p.1 v, 1)).2 := by
    apply Filter.eventually_all.mpr
    intro v
    exact (continuous_matrixHomogeneousPoint.comp (hparamcont v)).snd.continuousAt.tendsto.eventually
      (Ioi_mem_nhds (hheight v))
  have hclose : ∀ᶠ p in 𝓝 p₀, ∀ v : VertexType P,
      dist (matrixProjectivePoint (matrixFromEntries p.2) (p.1 v)) (b v).val < ε := by
    apply Filter.eventually_all.mpr
    intro v
    have hcont : ContinuousAt
        (fun p : (VertexType P → E d) ×
          ((Option (Fin d)) × (Option (Fin d)) → ℝ) =>
            matrixProjectivePoint (matrixFromEntries p.2) (p.1 v)) p₀ :=
      ContinuousAt.comp
        (f := fun p : (VertexType P → E d) ×
          ((Option (Fin d)) × (Option (Fin d)) → ℝ) =>
            (matrixFromEntries p.2, p.1 v))
        (x := p₀)
        (continuousAt_matrixProjectivePoint A₀ v.val (ne_of_gt (hheight v)))
        (hparamcont v).continuousAt
    have hc : Tendsto
        (fun p : (VertexType P → E d) ×
          ((Option (Fin d)) × (Option (Fin d)) → ℝ) =>
            matrixProjectivePoint (matrixFromEntries p.2) (p.1 v))
        (𝓝 p₀) (𝓝 (matrixProjectivePoint A₀ v.val)) := hcont.tendsto
    rw [hpoint v] at hc
    exact hc.eventually (Metric.ball_mem_nhds (b v).val hε)
  filter_upwards [hdet, hpositive, hclose] with p hd hp hc
  exact ⟨hd, hp, hc⟩

theorem RationallyApproximable.positiveProjective
    {P Q : ConvexPolytope d} (hP : RationallyApproximable P)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ)) (b : VertexType P ≃ VertexType Q)
    (h : VertexType P → ℝ) (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1)) : RationallyApproximable Q := by
  intro ε hε
  let S : Set ((VertexType P → E d) × ((Option (Fin d)) × (Option (Fin d)) → ℝ)) := {p |
    (matrixFromEntries p.2).det ≠ 0 ∧
      (∀ v : VertexType P, 0 < (homogeneousMatrixLinear (matrixFromEntries p.2) (p.1 v, 1)).2) ∧
      ∀ v : VertexType P, dist (matrixProjectivePoint (matrixFromEntries p.2) (p.1 v)) (b v).val < ε}
  have hS : S ∈ 𝓝 ((Subtype.val : VertexType P → E d),
      (fun ij => homogeneousEquivMatrix L ij.1 ij.2)) :=
    positiveProjective_approximation_neighborhood P Q L b h hh hL ε hε
  obtain ⟨R, φ, r, hRrat, hparams⟩ := hP.exists_parameters_in_neighborhood
    (fun ij => homogeneousEquivMatrix L ij.1 ij.2) S hS
  let A := matrixFromEntries (fun ij => (r ij : ℝ))
  have hA : A.det ≠ 0 := hparams.1
  let M := homogeneousMatrixEquiv A hA
  let q : VertexType R → E d := fun w => matrixProjectivePoint A w.val
  let k : VertexType R → ℝ := fun w => (M (w.val, 1)).2
  have hk (w : VertexType R) : 0 < k w := by
    obtain ⟨v, rfl⟩ := (vertexEquivOfFaceOrder φ).surjective w
    exact hparams.2.1 v
  have hM (w : VertexType R) : M (w.val, 1) = k w • (q w, 1) :=
    dehomogenizePoint_lift _ (ne_of_gt (hk w))
  let R' := projectivePolytope R M q k hk hM
  let ψ := projectivePolytopeFaceOrderIso R M q k hk hM
  let χ := positiveProjectiveFaceOrderIso P Q L b h hh hL
  let τ := χ.symm.trans (φ.trans ψ)
  have hAfield (i j : Option (Fin d)) : A i j ∈ rationalSubfield := ⟨r (i, j), rfl⟩
  have hqfield (w : VertexType R) (i : Fin d) : q w i ∈ rationalSubfield :=
    matrixProjectivePoint_coordinates rationalSubfield A hAfield w.val
      (hRrat w.val w.property) i
  have hR'rat : RationalCoordinates R' :=
    projectivePolytope_coordinates rationalSubfield R M q k hk hM hqfield
  refine ⟨R', τ, hR'rat, ?_⟩
  intro w
  obtain ⟨v, rfl⟩ := b.surjective w
  have hchi : imageVertex χ v = b v :=
    positiveProjectiveFaceOrderIso_vertex P Q L b h hh hL v
  have hchiInv : imageVertex χ.symm (b v) = v := by
    rw [← hchi]
    exact (vertexEquivOfFaceOrder χ).symm_apply_apply v
  change dist (imageVertex (χ.symm.trans (φ.trans ψ)) (b v)).val (b v).val < ε
  rw [imageVertex_trans, imageVertex_trans, hchiInv]
  have hpsi : imageVertex ψ (imageVertex φ v) =
      projectiveVertexEquiv R M q k hk hM (imageVertex φ v) :=
    positiveProjectiveFaceOrderIso_vertex R R' M
      (projectiveVertexEquiv R M q k hk hM) k hk hM (imageVertex φ v)
  rw [hpsi]
  exact hparams.2.2 v

theorem rationallyApproximable_positiveProjective_iff
    (P Q : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (b : VertexType P ≃ VertexType Q) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1)) :
    RationallyApproximable P ↔ RationallyApproximable Q := by
  constructor
  · exact fun hP => hP.positiveProjective L b h hh hL
  · intro hQ
    let k : VertexType Q → ℝ := fun w => (h (b.symm w))⁻¹
    have hk (w : VertexType Q) : 0 < k w := inv_pos.mpr (hh (b.symm w))
    have hinv (w : VertexType Q) : L.symm (w.val, 1) = k w • ((b.symm w).val, 1) := by
      have heq := congrArg L.symm (hL (b.symm w))
      simp only [L.symm_apply_apply, b.apply_symm_apply, map_smul] at heq
      rw [heq]
      simp only [k, smul_smul, inv_mul_cancel₀ (ne_of_gt (hh (b.symm w))), one_smul]
    exact hQ.positiveProjective L.symm b.symm k hk hinv

end Papers.Polytopes

end
end
end BundlePart19

section BundlePart20
/- Source: Papers/SimpleDeletionDensity.lean -/






@[expose] public section

/-!
# Simple deletion preserves rational density in both directions

For an arbitrary realization of the deleted type, global restoration
first supplies an explicitly projective core and an actual realization
of the original polytope.  Rational approximation is then deleted with
the correct vertex labels and transported back through rationally
approximated projective matrices.  The reverse direction uses the local
restoration formula.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem RationallyDense.delete_of_simple
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) (hPD : RationallyDense P) :
    RationallyDense (deleteVertex P v.val hne) := by
  intro C hQC
  obtain ⟨φ⟩ := hQC
  let Q := deleteVertex P v.val hne
  obtain ⟨D, ha⟩ := exists_fin_deletion_presentation P hP v hs hcard hne
  have hvertices : P.vertices = insert v.val Q.vertices := (Finset.insert_erase v.property).symm
  obtain ⟨L, q, h, hh, hL, a', ha', hsame⟩ :=
    D.exists_projective_admissible_point P v.val hvertices ha φ
  let C' := projectivePolytope C L q h hh hL
  let σ := projectivePolytopeFaceOrderIso C L q h hh hL
  let D' := (D.transport φ).projective L q h hh hL
  have hDD' : D.Aligned D' (φ.trans σ) :=
    (D.transport_aligned φ).trans ((D.transport φ).projective_aligned L q h hh hL)
  obtain ⟨P', hP'vertices, _⟩ := D.realize_extension_from_admissible_point D' (φ.trans σ) hDD'
    P v.val a' hvertices ha ha' hsame
  let τ := D.extensionFaceOrderIso D' (φ.trans σ) hDD' P P' v.val a'
    hvertices hP'vertices ha ha' hsame
  let v' : VertexType P' := ⟨a', by rw [hP'vertices]; exact Finset.mem_insert_self _ _⟩
  have hv' : imageVertex τ v = v' := by
    have hvlabel : extensionVertexLabels Q P v.val hvertices
        (D.apex_not_mem_vertices v.val ha) none = v := Subtype.ext rfl
    rw [← hvlabel, D.extensionFaceOrderIso_vertex D' (φ.trans σ) hDD' P P' v.val a'
      hvertices hP'vertices ha ha' hsame,
      D.extensionVertexEquiv_at_label D' (φ.trans σ) P P' v.val a'
        hvertices hP'vertices ha ha']
    exact Subtype.ext rfl
  have hP' : P'.IsFullDim := (faceOrderIso_polytope_dim τ).trans hP
  have hsv' : IsSimpleVertex P' v' := hv' ▸ isSimple_imageVertex τ v hs
  have hcardP' : d + 1 < P'.vertices.card := by
    rw [← faceOrderIso_vertex_card τ]
    exact hcard
  let hneP' := simpleDeletion_nonempty P' hP' v' hsv' hcardP'
  have hdelete : deleteVertex P' v'.val hneP' = C' := by
    apply polytope_eq_of_vertices_eq
    rw [deleteVertex_vertices]
    change P'.vertices.erase a' = C'.vertices
    rw [hP'vertices]
    exact Finset.erase_insert (D'.apex_not_mem_vertices a' ha')
  have hP'approx : RationallyApproximable P' := hPD P' ⟨τ⟩
  have hC'approx : RationallyApproximable C' := by
    rw [← hdelete]
    exact RationallyApproximable.delete_of_simple P' hP' v' hsv' hcardP' hneP' hP'approx
  exact (rationallyApproximable_positiveProjective_iff C C' L
    (projectiveVertexEquiv C L q h hh hL) h hh hL).mpr hC'approx

theorem simpleDeletion_rationallyDense_iff
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) :
    RationallyDense P ↔ RationallyDense (deleteVertex P v.val hne) :=
  ⟨RationallyDense.delete_of_simple P hP v hs hcard hne,
    RationallyDense.restore_simple_vertex P hP v hs hcard hne⟩

end Papers.Polytopes

end
end
end BundlePart20

section BundlePart21
/- Source: Papers/SimpleDeletionTheorem.lean -/




@[expose] public section

/-!
# The complete simple-vertex deletion theorem

The conclusion has all four clauses of Theorem 3: dimension, intrinsic
combinatorial deletion, equality of the sets of real realization fields,
and equivalence of rational density.  Every geometric presentation used
by its proof is constructed from the given ordinary convex polytope and
simple vertex.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

theorem simpleDeletionTheorem : SimpleDeletionClaim := by
  intro d P v hP hcard hs
  obtain ⟨hne, hdim, htype⟩ := simpleDeletion_geometry P hP v hs hcard
  refine ⟨hne, hdim, htype, ?_, ?_⟩
  · exact fun K => simpleDeletion_realizable_iff P hP v hs hcard hne K
  · exact simpleDeletion_rationallyDense_iff P hP v hs hcard hne

end Papers.Polytopes

end
end
end BundlePart21

section BundlePart22
/- Source: Papers/RealizationTopology.lean -/





@[expose] public section

/-!
# The topology of labelled realizations

The realization space is a subspace of the finite product of ordinary
Euclidean vertex coordinates.  Its points are all vertex labellings
induced by actual isomorphisms of the given polytope's face order with
the face order of an actual convex polytope.  The rational points are
defined by rationality of each coordinate, independently of density.

The final theorem identifies topological density of these rational
points with the vertexwise approximation predicate used in Theorem 3.
No choice of a preferred realization or labelling is imposed.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def labeledRealizationSet (P : ConvexPolytope d) : Set (VertexType P → E d) :=
  {q | ∃ Q : ConvexPolytope d, ∃ φ : FaceType P ≃o FaceType Q,
    ∀ v, q v = (imageVertex φ v).val}

/-- The ordinary subspace topology inherited from all labelled vertex coordinates. -/
abbrev LabeledRealizationSpace (P : ConvexPolytope d) := ↥(labeledRealizationSet P)

def rationalLabeledRealizations (P : ConvexPolytope d) :
    Set (LabeledRealizationSpace P) :=
  {q | ∀ v j, ∃ r : ℚ, (r : ℝ) = q.val v j}

namespace LabeledRealizationSpace

private theorem imageVertex_comp {P Q R : ConvexPolytope d}
    (φ : FaceType P ≃o FaceType Q) (ψ : FaceType Q ≃o FaceType R)
    (v : VertexType P) :
    imageVertex (φ.trans ψ) v = imageVertex ψ (imageVertex φ v) := by
  apply vertexFace_injective R
  rw [imageVertex_face, imageVertex_face, imageVertex_face]
  rfl

theorem rational_iff_coordinates {P Q : ConvexPolytope d}
    (q : LabeledRealizationSpace P) (φ : FaceType P ≃o FaceType Q)
    (hq : ∀ v, q.val v = (imageVertex φ v).val) :
    q ∈ rationalLabeledRealizations P ↔ RationalCoordinates Q := by
  constructor
  · intro h x hx j
    obtain ⟨v, hv⟩ := (vertexEquivOfFaceOrder φ).surjective ⟨x, hx⟩
    obtain ⟨r, hr⟩ := h v j
    refine ⟨r, ?_⟩
    rw [hq v] at hr
    exact hr.trans (congrArg (fun w : VertexType Q => w.val j) hv)
  · intro h v j
    rw [hq v]
    exact h _ (imageVertex φ v).property j

end LabeledRealizationSpace

/-- The approximation formulation has exactly the usual topological meaning:
rational points are dense in the entire space of labelled realizations. -/
theorem rationallyDense_iff_dense_labeledRealizations (P : ConvexPolytope d) :
    RationallyDense P ↔ Dense (rationalLabeledRealizations P) := by
  constructor
  · intro h
    apply Metric.dense_iff.mpr
    intro q ε hε
    obtain ⟨Q, φ, hφ⟩ := q.property
    obtain ⟨R, ψ, hR, hclose⟩ := h Q ⟨φ⟩ ε hε
    let r : LabeledRealizationSpace P :=
      ⟨(fun v => (imageVertex (φ.trans ψ) v).val), R, φ.trans ψ, fun _ => rfl⟩
    refine ⟨r, ?_, ?_⟩
    · change dist r.val q.val < ε
      apply (dist_pi_lt_iff hε).mpr
      intro v
      change dist (imageVertex (φ.trans ψ) v).val (q.val v) < ε
      rw [hφ v, LabeledRealizationSpace.imageVertex_comp]
      exact hclose (imageVertex φ v)
    · exact (LabeledRealizationSpace.rational_iff_coordinates r (φ.trans ψ)
        (fun _ => rfl)).mpr hR
  · intro h Q hPQ ε hε
    obtain ⟨φ⟩ := hPQ
    let q : LabeledRealizationSpace P :=
      ⟨(fun v => (imageVertex φ v).val), Q, φ, fun _ => rfl⟩
    obtain ⟨r, hrclose, hr⟩ := Metric.dense_iff.mp h q ε hε
    obtain ⟨R, ψ, hψ⟩ := r.property
    refine ⟨R, φ.symm.trans ψ,
      (LabeledRealizationSpace.rational_iff_coordinates r ψ hψ).mp hr, ?_⟩
    intro w
    let v : VertexType P := imageVertex φ.symm w
    have hv : imageVertex φ v = w := (vertexEquivOfFaceOrder φ).right_inv w
    have hnear : dist r.val q.val < ε := hrclose
    have hnearv := (dist_pi_lt_iff hε).mp hnear v
    rw [hψ v] at hnearv
    change dist (imageVertex ψ v).val (imageVertex φ v).val < ε at hnearv
    rw [hv] at hnearv
    rw [LabeledRealizationSpace.imageVertex_comp]
    exact hnearv

end Papers.Polytopes

end
end
end BundlePart22

section BundlePart23
/- Source: Papers/SimpleDeletionTopology.lean -/




@[expose] public section

/-!
# The density conclusion in the ordinary realization-space topology

This corollary expresses the density clause using Mathlib's `Dense` and
the subspace topology on all labelled Euclidean vertex realizations.
The equivalence with the approximation predicate is proved separately.
-/

noncomputable section
namespace Papers.Polytopes

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

theorem simpleDeletion_dense_labeledRealizations_iff
    {d : ℕ} (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) :
    Dense (rationalLabeledRealizations P) ↔
      Dense (rationalLabeledRealizations (deleteVertex P v.val hne)) := by
  rw [← rationallyDense_iff_dense_labeledRealizations,
    ← rationallyDense_iff_dense_labeledRealizations]
  exact simpleDeletion_rationallyDense_iff P hP v hs hcard hne

end Papers.Polytopes

end
end
end BundlePart23

section BundlePart24
/- Source: Papers/SimpleDeletionPaper.lean -/



@[expose] public section

/-!
# The paper's simple-vertex deletion theorem

This wrapper keeps the entire geometric, combinatorial, field and density
conclusion in one statement.  Realisation fields are literal subfields of the
real numbers, and density is the previously defined quantification over every
realisation and every positive coordinate tolerance.
-/

noncomputable section

namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def realizationFields (P : ConvexPolytope d) : Set (Subfield ℝ) :=
  {K | RealizableOver P K}

theorem simpleDeletion_fields_eq
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) :
    realizationFields P = realizationFields (deleteVertex P v.val hne) := by
  ext K
  exact simpleDeletion_realizable_iff P hP v hs hcard hne K

theorem paper_simple_vertex_deletion
    (d : ℕ) (P : ConvexPolytope d) (v : VertexType P)
    (hP : P.IsFullDim) (hcard : d + 1 < P.vertices.card)
    (hs : IsSimpleVertex P v) :
    ∃ hne : (P.vertices.erase v.val).Nonempty,
      (deleteVertex P v.val hne).IsFullDim ∧
      (∀ (Q : ConvexPolytope d) (φ : FaceType P ≃o FaceType Q)
          (hneQ : (Q.vertices.erase (imageVertex φ v).val).Nonempty),
        CombinatoriallyEquivalent (deleteVertex P v.val hne)
          (deleteVertex Q (imageVertex φ v).val hneQ)) ∧
      realizationFields P = realizationFields (deleteVertex P v.val hne) ∧
      (RationallyDense P ↔ RationallyDense (deleteVertex P v.val hne)) := by
  obtain ⟨hne, hdim, htype, hfields, hdensity⟩ :=
    simpleDeletionTheorem d P v hP hcard hs
  refine ⟨hne, hdim, htype, ?_, hdensity⟩
  ext K
  exact hfields K

end Papers.Polytopes

end
end
end BundlePart24
