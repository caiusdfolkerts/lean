module
public import consolidated.homothety_minimum_class
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option Elab.async false

section BundlePart0
/- Source: Papers/HomothetyFiberFaces.lean -/






@[expose] public section

/-!
# The actual fiber faces

The fiber through a minimum-class vertex is the intersection of the
polytope with the homogeneous subspace `D + R X_u`. It is proved to be
an exposed face, of dimension exactly `dim D`. Distinct fibers intersect
in the actual central section. The central section is either empty or
an exposed face, matching the paper's convention permitting an empty
central face.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*}

def signedHomogeneousEquiv : (E d × ℝ) ≃ₗ[ℝ] (ℝ × E d) where
  toFun z := (z.2, -z.1)
  invFun z := (-z.2, z.1)
  left_inv z := by apply Prod.ext <;> simp
  right_inv z := by apply Prod.ext <;> simp
  map_add' z w := by apply Prod.ext <;> simp [add_comm]
  map_smul' c z := by apply Prod.ext <;> simp

theorem finrank_vertexVector_span {S : Set (E d)} (hS : S.Nonempty) :
    finrank ℝ (Submodule.span ℝ (vertexVector '' S)) = faceDim S + 1 := by
  have hmap : Submodule.map signedHomogeneousEquiv.toLinearMap
      (Papers.Coordinates.homogeneousSpan (K := ℝ) S) =
      Submodule.span ℝ (vertexVector '' S) := by
    rw [Papers.Coordinates.homogeneousSpan, Submodule.map_span]
    simp only [Set.image_image, LinearEquiv.coe_coe]
    rfl
  rw [← hmap, signedHomogeneousEquiv.finrank_map_eq,
    Papers.Coordinates.finrank_homogeneousSpan hS]
  rfl

def parameterFiber (P : ConvexPolytope d) (a : I → ℝ) (b : I → E d)
    (u : E d) : Set (E d) :=
  {x ∈ P.toSet | vertexVector x ∈
    parameterDirectionSpan a b ⊔ Submodule.span ℝ {vertexVector u}}

def centralSection (P : ConvexPolytope d) (a : I → ℝ) (b : I → E d) : Set (E d) :=
  {x ∈ P.toSet | vertexVector x ∈ parameterDirectionSpan a b}

section Coordinates

variable (P : ConvexPolytope d) (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (i : I)
    (B : Basis (noncentralClass P f a b i) ℝ
      ((ℝ × E d) ⧸ parameterDirectionSpan a b))
    (hB : ∀ u, B u = quotientVertex a b u.val)

include hB in
theorem mem_fiber_iff_coordinates_zero (u : noncentralClass P f a b i) (x : E d) :
    x ∈ parameterFiber P a b u.val ↔ x ∈ P.toSet ∧
      ∀ q : noncentralClass P f a b i, q ≠ u →
        quotientCoordinate (parameterDirectionSpan a b) B q (vertexVector x) = 0 := by
  let D := parameterDirectionSpan a b
  let M := D ⊔ Submodule.span ℝ {vertexVector u.val}
  constructor
  · rintro ⟨hxP, hxM⟩
    refine ⟨hxP, ?_⟩
    intro q hqu
    have hMker : M ≤ (quotientCoordinate D B q).ker := by
      apply sup_le (quotientCoordinate_vanishes D B q)
      apply Submodule.span_le.mpr
      rintro z (rfl : z = vertexVector u.val)
      exact (quotientCoordinate_vertex P f a b i B hB q u).trans (if_neg (Ne.symm hqu))
    exact hMker hxM
  · rintro ⟨hxP, hcoords⟩
    refine ⟨hxP, ?_⟩
    let c := quotientCoordinate D B u (vertexVector x)
    have hq : D.mkQ (vertexVector x) = c • B u := by
      apply B.repr.injective
      apply Finsupp.ext
      intro q
      change B.repr (D.mkQ (vertexVector x)) q = B.repr (c • B u) q
      rw [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
        smul_eq_mul]
      by_cases hqu : q = u
      · subst q
        rw [if_pos rfl, mul_one]
        rfl
      · rw [if_neg (Ne.symm hqu), mul_zero]
        exact hcoords q hqu
    have hdiff : vertexVector x - c • vertexVector u.val ∈ D := by
      apply (Submodule.Quotient.mk_eq_zero D).mp
      change D.mkQ (vertexVector x - c • vertexVector u.val) = 0
      rw [map_sub, map_smul]
      change D.mkQ (vertexVector x) - c • quotientVertex a b u.val = 0
      rw [← hB u, hq, sub_self]
    have hsum := M.add_mem (Submodule.mem_sup_left hdiff)
      (Submodule.mem_sup_right
        ((Submodule.span ℝ {vertexVector u.val}).smul_mem c
          (Submodule.subset_span (Set.mem_singleton _))))
    simpa only [sub_add_cancel] using hsum

theorem mem_central_iff_coordinates_zero (x : E d) :
    x ∈ centralSection P a b ↔ x ∈ P.toSet ∧
      ∀ q : noncentralClass P f a b i,
        quotientCoordinate (parameterDirectionSpan a b) B q (vertexVector x) = 0 := by
  constructor
  · rintro ⟨hxP, hxD⟩
    exact ⟨hxP, fun q => quotientCoordinate_vanishes _ B q hxD⟩
  · rintro ⟨hxP, hcoords⟩
    refine ⟨hxP, ?_⟩
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (parameterDirectionSpan a b).mkQ (vertexVector x) = 0
    apply B.repr.injective
    apply Finsupp.ext
    intro q
    rw [map_zero, Finsupp.zero_apply]
    exact hcoords q

def fiberFunctional (u : noncentralClass P f a b i) : (ℝ × E d) →ₗ[ℝ] ℝ :=
  ∑ q ∈ (Finset.univ : Finset (noncentralClass P f a b i)).erase u,
    quotientCoordinate (parameterDirectionSpan a b) B q

include hB in
theorem fiber_eq_affineZeroFace (hf : IsParallelMap P f)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hinj : Function.Injective (parameterVector a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    (u : noncentralClass P f a b i) :
    parameterFiber P a b u.val =
      affineZeroFace P (homogeneousForm (fiberFunctional P f a b i B u)) := by
  ext x
  rw [mem_fiber_iff_coordinates_zero P f a b i B hB]
  change (x ∈ P.toSet ∧ _) ↔ (x ∈ P.toSet ∧ _)
  apply and_congr_right
  intro hxP
  rw [homogeneousForm_apply]
  change (∀ q, q ≠ u → quotientCoordinate _ B q (vertexVector x) = 0) ↔
    (∑ q ∈ (Finset.univ : Finset (noncentralClass P f a b i)).erase u,
      quotientCoordinate _ B q) (vertexVector x) = 0
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun q _ =>
    minimumClass_coordinate_nonnegative P f a b i B hB hf hcover hinj hsize q x hxP)]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]

include hB in
theorem fiber_isFace (hf : IsParallelMap P f)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hinj : Function.Injective (parameterVector a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    (u : noncentralClass P f a b i) : P.IsFace (parameterFiber P a b u.val) := by
  have huP : u.val ∈ P.vertices :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp u.property).1).1
  have huR : u.val ∈ parameterFiber P a b u.val :=
    ⟨subset_convexHull ℝ _ huP,
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))⟩
  rw [fiber_eq_affineZeroFace P f a b i B hB hf hcover hinj hsize u] at huR ⊢
  apply affineZeroFace_isFace P _ _ ⟨u.val, huR⟩
  intro x hx
  rw [homogeneousForm_apply]
  unfold fiberFunctional
  rw [LinearMap.sum_apply]
  exact Finset.sum_nonneg (fun q _ =>
    minimumClass_coordinate_nonnegative P f a b i B hB hf hcover hinj hsize q x hx)

include hB in
theorem fiber_dimension (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hinj : Function.Injective (parameterVector a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    (hcard : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (u : noncentralClass P f a b i) :
    faceDim (parameterFiber P a b u.val) = finrank ℝ (parameterDirectionSpan a b) := by
  classical
  let D := parameterDirectionSpan a b
  let U := noncentralClass P f a b i
  let R := parameterFiber P a b u.val
  let M := D ⊔ Submodule.span ℝ {vertexVector u.val}
  have huP : u.val ∈ P.vertices :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp u.property).1).1
  have huR : u.val ∈ R :=
    ⟨subset_convexHull ℝ _ huP,
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))⟩
  have huD : vertexVector u.val ∉ D := (Finset.mem_filter.mp u.property).2
  have hMdim : finrank ℝ M = finrank ℝ D + 1 :=
    Submodule.finrank_sup_span_singleton huD
  have hspan : Submodule.span ℝ (vertexVector '' R) ≤ M := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, rfl⟩
    exact hx.2
  have hupper : faceDim R ≤ finrank ℝ D := by
    have hrank := Submodule.finrank_mono hspan
    rw [finrank_vertexVector_span ⟨u.val, huR⟩, hMdim] at hrank
    omega
  have hcoverEdges : ∀ y, GeneralVertexStep P u.val y → y ∈ R ∨ y ∈ U.erase u.val := by
    intro y huy
    by_cases hyU : y ∈ U
    · exact Or.inr (Finset.mem_erase.mpr ⟨huy.2.1.symm, hyU⟩)
    · left
      apply (mem_fiber_iff_coordinates_zero P f a b i B hB u y).mpr
      refine ⟨subset_convexHull ℝ _ huy.1, ?_⟩
      intro q hqu
      apply quotientCoordinate_neighbor_zero P f a b i B hB hf hcover hinj
        q u (Ne.symm hqu) huy
      intro he
      exact hyU (he.symm ▸ q.property)
  have hlower := dim_le_faceDim_add_outside_neighbors P hP huP R huR
    (U.erase u.val) hcoverEdges
  have herase : (U.erase u.val).card = U.card - 1 :=
    Finset.card_erase_of_mem u.property
  rw [herase] at hlower
  change U.card = d + 1 - finrank ℝ D at hcard
  change 2 ≤ U.card at hsize
  change faceDim R=finrank ℝ D
  omega

include hB in
theorem fiber_inter_eq_central (u v : noncentralClass P f a b i) (huv : u ≠ v) :
    parameterFiber P a b u.val ∩ parameterFiber P a b v.val = centralSection P a b := by
  ext x
  rw [Set.mem_inter_iff, mem_fiber_iff_coordinates_zero P f a b i B hB,
    mem_fiber_iff_coordinates_zero P f a b i B hB,
    mem_central_iff_coordinates_zero P f a b i B]
  constructor
  · rintro ⟨⟨hxP, hxu⟩, ⟨_, hxv⟩⟩
    refine ⟨hxP, ?_⟩
    intro q
    by_cases hqu : q = u
    · subst q
      exact hxv u huv
    · exact hxu q hqu
  · rintro ⟨hxP, hx⟩
    exact ⟨⟨hxP, fun q _ => hx q⟩, ⟨hxP, fun q _ => hx q⟩⟩

include hB in
theorem centralSection_empty_or_isFace (hf : IsParallelMap P f)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hinj : Function.Injective (parameterVector a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card) :
    centralSection P a b = ∅ ∨ P.IsFace (centralSection P a b) := by
  classical
  by_cases hne : (centralSection P a b).Nonempty
  · right
    let L : (ℝ × E d) →ₗ[ℝ] ℝ :=
      ∑ q : noncentralClass P f a b i, quotientCoordinate (parameterDirectionSpan a b) B q
    let g := homogeneousForm L
    have hg : ∀ x ∈ P.toSet, 0 ≤ g x := by
      intro x hx
      rw [homogeneousForm_apply]
      change 0 ≤ (∑ q, quotientCoordinate (parameterDirectionSpan a b) B q) (vertexVector x)
      rw [LinearMap.sum_apply]
      exact Finset.sum_nonneg (fun q _ =>
        minimumClass_coordinate_nonnegative P f a b i B hB hf hcover hinj hsize q x hx)
    have heq : centralSection P a b = affineZeroFace P g := by
      ext x
      rw [mem_central_iff_coordinates_zero P f a b i B]
      change (x ∈ P.toSet ∧ _) ↔ (x ∈ P.toSet ∧ _)
      apply and_congr_right
      intro hxP
      rw [homogeneousForm_apply]
      change (∀ q, quotientCoordinate _ B q (vertexVector x) = 0) ↔
        (∑ q, quotientCoordinate _ B q) (vertexVector x) = 0
      rw [LinearMap.sum_apply, Finset.sum_eq_zero_iff_of_nonneg (fun q _ =>
        minimumClass_coordinate_nonnegative P f a b i B hB hf hcover hinj hsize q x hxP)]
      simp only [Finset.mem_univ, forall_const]
    rw [heq] at hne ⊢
    exact affineZeroFace_isFace P g hg hne
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

end Coordinates

/-- Lemma 9, with the quotient basis constructed from the hypotheses.
All geometric faces and dimensions refer to the original polytope. -/
theorem minimumClass_fiber_faces (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (i : I)
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    (hcard : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b)) :
    ∃ B : Basis (noncentralClass P f a b i) ℝ
      ((ℝ × E d) ⧸ parameterDirectionSpan a b),
      (∀ u, B u = quotientVertex a b u.val) ∧
      (∀ u v : noncentralClass P f a b i, u ≠ v → GeneralVertexStep P u.val v.val) ∧
      (∀ q : noncentralClass P f a b i, ∀ x ∈ P.toSet,
        0 ≤ quotientCoordinate (parameterDirectionSpan a b) B q (vertexVector x)) ∧
      (∀ q : noncentralClass P f a b i,
        IsFacet P (affineZeroFace P
          (homogeneousForm (quotientCoordinate (parameterDirectionSpan a b) B q)))) ∧
      (∀ u : noncentralClass P f a b i,
        P.IsFace (parameterFiber P a b u.val) ∧
        faceDim (parameterFiber P a b u.val) = finrank ℝ (parameterDirectionSpan a b)) ∧
      (∀ u v : noncentralClass P f a b i, u ≠ v →
        parameterFiber P a b u.val ∩ parameterFiber P a b v.val = centralSection P a b) ∧
      (centralSection P a b = ∅ ∨ P.IsFace (centralSection P a b)) := by
  obtain ⟨x, hxi, hpriv⟩ := hprivate i
  obtain ⟨B, hB⟩ := exists_classQuotientBasis P hP f hf a b hcover i hxi hpriv hcard
  have hinj := parameterVector_injective_of_private P f a b hprivate
  refine ⟨B, hB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact minimumClass_clique P f a b i B hB hf hcover hinj
  · exact minimumClass_coordinate_nonnegative P f a b i B hB hf hcover hinj hsize
  · exact minimumClass_coordinate_facet P f a b i B hB hP hf hcover hinj hsize
  · intro u
    exact ⟨fiber_isFace P f a b i B hB hf hcover hinj hsize u,
      fiber_dimension P f a b i B hB hP hf hcover hinj hsize hcard u⟩
  · exact fiber_inter_eq_central P f a b i B hB
  · exact centralSection_empty_or_isFace P f a b i B hB hf hcover hinj hsize

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/FaceNeighborCount.lean -/





@[expose] public section

/-!
# The number of actual neighbors in a face

The edge-star spanning theorem gives the degree bound in the intrinsic
dimension, including polytopes that are not full dimensional in their
ambient Euclidean space. Applying it to the actual polytope of a face
gives the local count needed by equation (3) of the conditional-
decomposability argument.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem dim_le_neighbor_cover (P : ConvexPolytope d) {x : E d}
    (hx : x ∈ P.vertices) (S : Finset (E d))
    (hcover : ∀ y, GeneralVertexStep P x y → y ∈ S) : P.dim ≤ S.card := by
  let A := S.image (fun y => y - x)
  have hspan : edgeStarSpan P x ≤ Submodule.span ℝ (A : Set (E d)) := by
    apply Submodule.span_le.mpr
    rintro w ⟨y, hy, rfl⟩
    exact Submodule.subset_span (Finset.mem_image_of_mem _ (hcover y hy))
  rw [edgeStarSpan_eq_vectorSpan P hx] at hspan
  exact (Submodule.finrank_mono hspan).trans
    ((finrank_span_finset_le_card (R := ℝ) A).trans
      (Finset.card_image_le (s := S) (f := fun y => y - x)))

def faceNeighbors (P : ConvexPolytope d) (F : Set (E d)) (x : E d) : Finset (E d) :=
  P.vertices.filter (fun y => y ∈ F ∧ GeneralVertexStep P x y)

theorem faceDim_le_neighbor_cover (P : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) {x : E d} (hx : x ∈ P.vertices) (hxF : x ∈ F)
    (S : Finset (E d))
    (hcover : ∀ y, y ∈ F → GeneralVertexStep P x y → y ∈ S) :
    faceDim F ≤ S.card := by
  let Q := facePolytope P hF
  have hxQ : x ∈ Q.vertices := Finset.mem_filter.mpr ⟨hx, hxF⟩
  have hcount := dim_le_neighbor_cover Q hxQ S (by
    intro y hxy
    have hy := Finset.mem_filter.mp hxy.1
    obtain ⟨_, hne, e, he, hde, hxe, hye⟩ := hxy
    exact hcover y hy.2
      ⟨hy.1, hne, e, isFace_of_facePolytope P hF he, hde, hxe, hye⟩)
  have hbody : Q.toSet = F := facePolytope_toSet P hF
  change faceDim Q.toSet ≤ S.card at hcount
  rwa [hbody] at hcount

theorem faceDim_le_faceNeighbors_card (P : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) {x : E d} (hx : x ∈ P.vertices) (hxF : x ∈ F) :
    faceDim F ≤ (faceNeighbors P F x).card := by
  apply faceDim_le_neighbor_cover P hF hx hxF
  intro y hyF hxy
  exact Finset.mem_filter.mpr ⟨hxy.1, hyF, hxy⟩

end Papers.Polytopes

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/HomothetyCentralNeighbors.lean -/






@[expose] public section

/-!
# The central-neighbor inequality

Every actual edge from a central vertex to a noncentral vertex stays in
one of the central vertex's full homothety classes. A minimum class
supplies distinct actual fiber faces of dimension `dim D`. Counting the
neighbors of a central vertex separately in those faces yields equation
(3) of the conditional-decomposability paper.

The inequality is written without truncated subtractions:

  r * t ≤ r * degree_F(z) + r * |I(z)| + ∑ i∈I(z), e_i.

This is the same integer inequality as the paper's displayed formula.
The fibers, their dimensions, and their intersections are proved by
`minimumClass_fiber_faces`; they are not additional hypotheses.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*}

/-- A central-to-noncentral edge belongs to the noncentral endpoint's
full homothety class at both ends. -/
theorem central_edge_owner (P : ConvexPolytope d)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ i, f y = a i • y + b i)
    {x y : E d} (hx : x ∈ P.vertices)
    (hcentral : vertexVector x ∈ parameterDirectionSpan a b)
    (hnoncentral : vertexVector y ∉ parameterDirectionSpan a b)
    (hxy : GeneralVertexStep P x y) {j : I}
    (hyj : f y = a j • y + b j) : f x = a j • x + b j := by
  obtain ⟨i, hxi⟩ := hcover x hx
  obtain ⟨μ, hμ⟩ := hf x hx y hxy.1 hxy
  let D := parameterDirectionSpan a b
  have hdiff : parameterVector a b j - parameterVector a b i ∈ D :=
    Submodule.subset_span (Set.mem_range_self (j, i))
  have hmem : (a j - μ) • vertexVector y ∈ D := by
    have hh := D.add_mem hdiff (D.smul_mem (a i - μ) hcentral)
    rw [edge_parameter_identity f a b hxi hyj hμ] at hh
    simpa only [sub_add_cancel] using hh
  have hz : a j - μ = 0 := by
    by_contra hn
    apply hnoncentral
    have hh := D.smul_mem (a j - μ)⁻¹ hmem
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hh
  have hjμ : a j = μ := sub_eq_zero.mp hz
  calc
    f x = f y - (f y - f x) := by abel
    _ = (a j • y + b j) - μ • (y - x) := by rw [hμ, hyj]
    _ = a j • x + b j := by rw [← hjμ]; module

/-- Equation (3), with the degree taken in the actual central face and
each excess taken from the actual full noncentral class. -/
theorem central_neighbor_inequality [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (i : I)
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    (hcard : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    {z : E d} (hz : z ∈ P.vertices)
    (hzcentral : vertexVector z ∈ parameterDirectionSpan a b) :
    let r := d + 1 - finrank ℝ (parameterDirectionSpan a b)
    r * finrank ℝ (parameterDirectionSpan a b) ≤
      r * (faceNeighbors P (centralSection P a b) z).card +
      r * (owners f a b z).card +
      ∑ j ∈ owners f a b z, ((noncentralClass P f a b j).card - r) := by
  classical
  dsimp only
  let r := d + 1 - finrank ℝ (parameterDirectionSpan a b)
  let t := finrank ℝ (parameterDirectionSpan a b)
  let U := noncentralClass P f a b i
  let F := centralSection P a b
  let C := faceNeighbors P F z
  let O := owners f a b z
  let N : U → Finset (E d) := fun u =>
    P.vertices.filter (fun y =>
      y ∈ parameterFiber P a b u.val ∧ y ∉ F ∧ GeneralVertexStep P z y)
  obtain ⟨B, hB, hclique, hnonneg, hfacets, hfibers, hinter, hF⟩ :=
    minimumClass_fiber_faces P hP f hf a b hcover hprivate i hsize hcard
  have hcount (u : U) : t ≤ C.card + (N u).card := by
    have hzR : z ∈ parameterFiber P a b u.val :=
      ⟨subset_convexHull ℝ _ hz, Submodule.mem_sup_left hzcentral⟩
    have hc := faceDim_le_neighbor_cover P (hfibers u).1 hz hzR (C ∪ N u) (by
      intro y hyR hzy
      by_cases hyF : y ∈ F
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hzy.1, hyF, hzy⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hzy.1, hyR, hyF, hzy⟩))
    rw [(hfibers u).2] at hc
    exact hc.trans (Finset.card_union_le C (N u))
  have hdisjoint : (↑(Finset.univ : Finset U) : Set U).PairwiseDisjoint N := by
    intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro y hyu hyv
    have hyu := (Finset.mem_filter.mp hyu).2
    have hyv := (Finset.mem_filter.mp hyv).2
    apply hyu.2.1
    have hy : y ∈ parameterFiber P a b u.val ∩ parameterFiber P a b v.val :=
      ⟨hyu.1, hyv.1⟩
    rwa [hinter u v huv] at hy
  have hsub : Finset.univ.biUnion N ⊆ O.biUnion (noncentralClass P f a b) := by
    intro y hy
    obtain ⟨u, _, hyu⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨hyP, hyR, hyF, hzy⟩ := Finset.mem_filter.mp hyu
    have hyD : vertexVector y ∉ parameterDirectionSpan a b := by
      intro hyD
      exact hyF ⟨subset_convexHull ℝ _ hyP, hyD⟩
    obtain ⟨j, hyj⟩ := hcover y hyP
    have hzj := central_edge_owner P f hf a b hcover hz hzcentral hyD hzy hyj
    apply Finset.mem_biUnion.mpr
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hzj⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyP, hyj⟩, hyD⟩⟩
  have hownerdisjoint : (↑O : Set I).PairwiseDisjoint (noncentralClass P f a b) := by
    intro j hj k hk hjk
    exact noncentralClasses_disjoint P f a b
      (parameterVector_injective_of_private P f a b hprivate) hjk
  have hupper : (∑ u : U, (N u).card) ≤ ∑ j ∈ O, (noncentralClass P f a b j).card := by
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_biUnion hdisjoint, Finset.card_biUnion hownerdisjoint] at hh
  have htotal : r * t ≤ r * C.card + ∑ j ∈ O, (noncentralClass P f a b j).card := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset U))
      (fun u _ => hcount u)
    have hcU : Fintype.card U = r := by rw [Fintype.card_coe]; exact hcard
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hcU] at hh
    exact hh.trans (Nat.add_le_add_left hupper _)
  have hexpand : (∑ j ∈ O, (noncentralClass P f a b j).card) =
      r * O.card + ∑ j ∈ O, ((noncentralClass P f a b j).card - r) := by
    calc
      (∑ j ∈ O, (noncentralClass P f a b j).card) =
          ∑ j ∈ O, (r + ((noncentralClass P f a b j).card - r)) := by
        apply Finset.sum_congr rfl
        intro j hj
        obtain ⟨x, hxi, hpriv⟩ := hprivate j
        have hb := class_bound P hP f hf a b hcover j hxi hpriv
        change r ≤ (noncentralClass P f a b j).card at hb
        omega
      _ = _ := by rw [Finset.sum_add_distrib]; simp [Nat.mul_comm]
  rw [hexpand] at htotal
  simpa only [Nat.add_assoc] using htotal

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/HomothetyUniformBudget.lean -/




@[expose] public section

/-!
# The numerical reduction in Proposition 12

For the entire range `4 ≤ m ≤ d-1` and the actual vertex budget
`N ≤ 4d-5`, the parameters are affinely independent, the quotient
dimension is at least three, the total excess plus the central vertex
count is at most `t`, and a minimum class exists. Equation (3) then
forces a nonempty central face to have either `t-1` or `t` vertices.

These are the reductions at the start of Proposition 12. The subsequent
Shephard-facet construction and positive-projectivity alternative remain
separate obligations; no full proposition is asserted here.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*}

theorem uniform_parameter_budget [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 4 ≤ Fintype.card I) (hd : Fintype.card I + 1 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5) :
    let t := finrank ℝ (parameterDirectionSpan a b)
    let r := d + 1 - t
    AffineIndependent ℝ (parameterVector a b) ∧
    t + 1 = Fintype.card I ∧ 3 ≤ t ∧ 3 ≤ r ∧
    (∑ j, ((noncentralClass P f a b j).card - r)) +
        (centralVertices P a b).card ≤ t ∧
    ∃ i, (noncentralClass P f a b i).card = r := by
  classical
  dsimp only
  let t := finrank ℝ (parameterDirectionSpan a b)
  let r := d + 1 - t
  let m := Fintype.card I
  let e : I → ℕ := fun j => (noncentralClass P f a b j).card - r
  let s := (centralVertices P a b).card
  letI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hind := parameters_affineIndependent_of_vertex_budget
    P hP f hf a b hcover hprivate hm hd hN
  have htm : t + 1 = m := by
    have hh := hind.finrank_vectorSpan_add_one
    rwa [← parameterDirectionSpan_eq_vectorSpan] at hh
  have ht : 3 ≤ t := by omega
  have htd : t ≤ d + 1 := by omega
  have htr : t + r = d + 1 := by dsimp [r]; omega
  have hr : 3 ≤ r := by omega
  have hcount := essential_cover_vertex_count P hP f hf a b hcover hprivate
  change P.vertices.card = m * r + (∑ j, e j) + s at hcount
  have hbudget : (∑ j, e j) + s ≤ t := by
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le ht
    obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hr
    have hprod := Nat.zero_le (u * v)
    have hnumeric : 4 * d ≤ m * r + t + 5 := by
      have htr' := htr
      rw [hu,hv] at htr'
      rw [←htm,hu,hv]
      nlinarith
    omega
  have hmin : ∃ i, (noncentralClass P f a b i).card = r := by
    by_contra hmin
    push_neg at hmin
    have hepos (j : I) : 1 ≤ e j := by
      obtain ⟨x, hxi, hpriv⟩ := hprivate j
      have hbound := class_bound P hP f hf a b hcover j hxi hpriv
      change r ≤ (noncentralClass P f a b j).card at hbound
      dsimp [e]
      have hh := hmin j
      omega
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset I))
      (fun j _ => hepos j)
    have hmE : m ≤ ∑ j, e j := by
      calc
        m = ∑ _j : I, (1 : ℕ) := by simp [m]
        _ ≤ ∑ j, e j := Finset.sum_le_sum (fun j _ => hepos j)
    omega
  exact ⟨hind, htm, ht, hr, hbudget, hmin⟩

theorem central_face_neighbor_card_lt (P : ConvexPolytope d)
    (a : I → ℝ) (b : I → E d) {z : E d}
    (hz : z ∈ P.vertices) (hzD : vertexVector z ∈ parameterDirectionSpan a b) :
    (faceNeighbors P (centralSection P a b) z).card + 1 ≤
      (centralVertices P a b).card := by
  classical
  have hzC : z ∈ centralVertices P a b := Finset.mem_filter.mpr ⟨hz, hzD⟩
  have hsub : faceNeighbors P (centralSection P a b) z ⊆
      (centralVertices P a b).erase z := by
    intro y hy
    obtain ⟨hyP, hyF, hzy⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_erase.mpr ⟨hzy.2.1.symm,
      Finset.mem_filter.mpr ⟨hyP, hyF.2⟩⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hzC] at hc
  have hs := Finset.card_pos.mpr ⟨z, hzC⟩
  omega

/-- The two possible central vertex counts at the start of Proposition
12, with all parameter and minimum-class hypotheses derived from its
full uniform vertex budget. -/
theorem uniform_central_vertex_count [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 4 ≤ Fintype.card I) (hd : Fintype.card I + 1 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (hcentral : (centralVertices P a b).Nonempty) :
    (centralVertices P a b).card = finrank ℝ (parameterDirectionSpan a b) - 1 ∨
    (centralVertices P a b).card = finrank ℝ (parameterDirectionSpan a b) := by
  classical
  let t := finrank ℝ (parameterDirectionSpan a b)
  let r := d + 1 - t
  let s := (centralVertices P a b).card
  let e : I → ℕ := fun j => (noncentralClass P f a b j).card - r
  obtain ⟨hind, htm, ht, hr, hbudget, i, hi⟩ :=
    uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
  change (∑ j, e j) + s ≤ t at hbudget
  obtain ⟨z, hz⟩ := hcentral
  obtain ⟨hzP, hzD⟩ := Finset.mem_filter.mp hz
  have hsize : 2 ≤ (noncentralClass P f a b i).card := by rw [hi]; omega
  have hineq := central_neighbor_inequality P hP f hf a b hcover hprivate
    i hsize hi hzP hzD
  let deg := (faceNeighbors P (centralSection P a b) z).card
  let O := owners f a b z
  change r * t ≤ r * deg + r * O.card + ∑ j ∈ O, e j at hineq
  have hdeg : deg + 1 ≤ s := central_face_neighbor_card_lt P a b hzP hzD
  have howners : O.card ≤ 2 := owners_card_le_two f a b hind z
  have he : (∑ j ∈ O, e j) ≤ ∑ j, e j :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ O)
  have hdegmul := Nat.mul_le_mul_left r hdeg
  have hownermul := Nat.mul_le_mul_left r howners
  have hs : t ≤ s + 1 := by
    by_contra hn
    have hgap : 1 ≤ t - s - 1 := by omega
    let k := t - s - 1
    have htk : t = s + 1 + k := by dsimp [k]; omega
    have hkmul : 3 * k ≤ r * k := Nat.mul_le_mul_right k hr
    change 1 ≤ k at hgap
    rw [htk] at hineq hbudget
    nlinarith
  change s = t - 1 ∨ s = t
  omega

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/HomothetyCentralClique.lean -/





@[expose] public section

/-!
# The central clique and its common parameter

This develops the geometric consequences of the numerical reduction in
Proposition 12. When the central face has `t-1` vertices, equation (3)
forces every vertex to have exactly two owners and every pair to be an
actual edge. The parallel map is therefore homothetic on the central
vertices, and the independent-parameter incidence argument forces that
homothety to be one of the original parameters.

The central set and its adjacency are the actual vertices and edges of
the polytope. Neither a combinatorial clique nor a common parameter is
assumed. The later construction of a Shephard facet is a separate
obligation; this module does not assert the full proposition.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

/-- A parallel map on an actual clique with at least two vertices has
one homothety on the whole clique. The proof also covers a two-vertex
clique; larger cliques use noncollinearity of actual polytope vertices. -/
theorem homotheticOn_of_vertex_clique (P : ConvexPolytope d)
    (f : E d → E d) (hf : IsParallelMap P f) (S : Finset (E d))
    (hS : S ⊆ P.vertices) (hsize : 2 ≤ S.card)
    (hclique : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → GeneralVertexStep P x y) :
    HomotheticOn f (S : Set (E d)) := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  obtain ⟨α, hα⟩ := hf u (hS hu) v (hS hv) (hclique u hu v hv huv)
  let c := f u - α • u
  have hfu : f u = α • u + c := by dsimp [c]; abel
  have hfv : f v = α • v + c := by
    calc
      f v = (f v - f u) + f u := by abel
      _ = α • (v - u) + (α • u + c) := by rw [hα, hfu]
      _ = α • v + c := by module
  refine ⟨α, c, ?_⟩
  intro z hz
  by_cases hzu : z = u
  · simpa only [hzu] using hfu
  by_cases hzv : z = v
  · simpa only [hzv] using hfv
  exact homothety_at_two_neighbors P f (hS hu) (hS hz) (hS hv)
    huv hzu hzv hfu hfv
    (hf u (hS hu) z (hS hz) (hclique u hu z hz (Ne.symm hzu)))
    (hf v (hS hv) z (hS hz) (hclique v hv z hz (Ne.symm hzv)))

namespace HomothetyParameters

variable {I : Type*}

theorem central_neighbors_subset_erase (P : ConvexPolytope d)
    (a : I → ℝ) (b : I → E d) (z : E d) :
    faceNeighbors P (centralSection P a b) z ⊆
      (centralVertices P a b).erase z := by
  intro y hy
  obtain ⟨hyP, hyF, hzy⟩ := Finset.mem_filter.mp hy
  exact Finset.mem_erase.mpr ⟨hzy.2.1.symm,
    Finset.mem_filter.mpr ⟨hyP, hyF.2⟩⟩

/-- A central vertex attaining the maximal possible central degree is
adjacent to every other central vertex, as an actual polytope edge. -/
theorem central_adjacent_of_full_degree (P : ConvexPolytope d)
    (a : I → ℝ) (b : I → E d) {x y : E d}
    (hx : x ∈ centralVertices P a b) (hy : y ∈ centralVertices P a b)
    (hxy : x ≠ y)
    (hdeg : (faceNeighbors P (centralSection P a b) x).card + 1 =
      (centralVertices P a b).card) : GeneralVertexStep P x y := by
  have heq : faceNeighbors P (centralSection P a b) x =
      (centralVertices P a b).erase x := by
    apply Finset.eq_of_subset_of_card_le (central_neighbors_subset_erase P a b x)
    rw [Finset.card_erase_of_mem hx]
    omega
  have hyN : y ∈ faceNeighbors P (centralSection P a b) x := by
    rw [heq]
    exact Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  exact (Finset.mem_filter.mp hyN).2.2

/-- In the `s=t-1` case, every central vertex has exactly two owners and
all other central vertices as neighbors. All dimension and excess
bounds are derived from the original uniform vertex budget. -/
theorem uniform_central_deficit_one_degree_owners [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 4 ≤ Fintype.card I) (hd : Fintype.card I + 1 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b) - 1)
    {z : E d} (hz : z ∈ centralVertices P a b) :
    (faceNeighbors P (centralSection P a b) z).card + 1 =
      (centralVertices P a b).card ∧ (owners f a b z).card = 2 := by
  classical
  let t := finrank ℝ (parameterDirectionSpan a b)
  let r := d + 1 - t
  let s := (centralVertices P a b).card
  let e : I → ℕ := fun j => (noncentralClass P f a b j).card - r
  let deg := (faceNeighbors P (centralSection P a b) z).card
  let O := owners f a b z
  obtain ⟨hind, htm, ht, hr, hbudget, i, hi⟩ :=
    uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
  change (∑ j, e j) + s ≤ t at hbudget
  change s = t - 1 at hs
  have hE : (∑ j, e j) ≤ 1 := by omega
  have hsize : 2 ≤ (noncentralClass P f a b i).card := by rw [hi]; omega
  obtain ⟨hzP, hzD⟩ := Finset.mem_filter.mp hz
  have hineq := central_neighbor_inequality P hP f hf a b hcover hprivate
    i hsize hi hzP hzD
  change r * t ≤ r * deg + r * O.card + ∑ j ∈ O, e j at hineq
  have hdeg : deg + 1 ≤ s := central_face_neighbor_card_lt P a b hzP hzD
  have hO : O.card ≤ 2 := owners_card_le_two f a b hind z
  have he : (∑ j ∈ O, e j) ≤ 1 :=
    (Finset.sum_le_sum_of_subset (Finset.subset_univ O)).trans hE
  have hlower : t ≤ deg + O.card := by
    by_contra hbad
    have hh : deg + O.card + 1 ≤ t := by omega
    have hmul := Nat.mul_le_mul_left r hh
    nlinarith
  change deg + 1 = s ∧ O.card = 2
  omega

theorem uniform_central_deficit_one_clique [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 4 ≤ Fintype.card I) (hd : Fintype.card I + 1 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b) - 1) :
    ∀ x ∈ centralVertices P a b, ∀ y ∈ centralVertices P a b,
      x ≠ y → GeneralVertexStep P x y := by
  intro x hx y hy hxy
  exact central_adjacent_of_full_degree P a b hx hy hxy
    (uniform_central_deficit_one_degree_owners P hP f hf a b hcover
      hprivate hm hd hN hs hx).1

/-- The common central class in the `s=t-1` case of Proposition 12.
The conclusion uses an actual member of the original parameter family,
not a newly introduced or assumed homothety. -/
theorem uniform_central_deficit_one_common_parameter [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 4 ≤ Fintype.card I) (hd : Fintype.card I + 1 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b) - 1) :
    ∃ h : I, ∀ z ∈ centralVertices P a b, f z = a h • z + b h := by
  classical
  obtain ⟨hind, htm, ht, hr, hbudget, i, hi⟩ :=
    uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
  have hsize : 2 ≤ (centralVertices P a b).card := by rw [hs]; omega
  obtain ⟨α, c, hc⟩ := homotheticOn_of_vertex_clique P f hf
    (centralVertices P a b) (Finset.filter_subset _ _) hsize
    (uniform_central_deficit_one_clique P hP f hf a b hcover hprivate hm hd hN hs)
  have hparam : ∃ h : I, (α, c) = parameterVector a b h := by
    by_contra hn
    push_neg at hn
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp
      (by omega : 1 < (centralVertices P a b).card)
    have hshared (z : E d) (hz : z ∈ centralVertices P a b) :
        ∃ i ∈ ownerSet f a b z, ∃ j ∈ ownerSet f a b z, i ≠ j := by
      have ho := (uniform_central_deficit_one_degree_owners P hP f hf a b
        hcover hprivate hm hd hN hs hz).2
      obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp (by omega :
        1 < (owners f a b z).card)
      exact ⟨j, (Finset.mem_filter.mp hj).2, k,
        (Finset.mem_filter.mp hk).2, hjk⟩
    exact hxy (at_most_one_shared_point_of_new_homothety f a b hind hn
      (hc x hx) (hc y hy) (hshared x hx) (hshared y hy))
  obtain ⟨h, hh⟩ := hparam
  have hα : α = a h := congrArg Prod.fst hh
  have hc' : c = b h := congrArg Prod.snd hh
  refine ⟨h, ?_⟩
  intro z hz
  simpa only [hα, hc'] using hc z hz

end HomothetyParameters
end Papers.Polytopes

end
end
end BundlePart4

