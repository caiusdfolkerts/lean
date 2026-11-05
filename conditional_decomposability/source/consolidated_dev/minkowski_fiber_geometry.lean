module
public import consolidated_dev.exact_shephard_criterion
public import papers.finite_fiber_saturation
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.Linarith

set_option Elab.async false

section BundlePart0
/- Source: Papers/ProperSummandCounting.lean -/




@[expose] public section

/-!
# Integer counts for proper Minkowski summands

The variables below are integer cardinalities.  The additive form
N + 5 ≤ 4d avoids truncated natural-number subtraction.  Geometric
fiber and matching cardinalities are cast into these inequalities in
the polytope adapter.
-/

namespace Papers.ProperSummandCounting

theorem simplex_of_many_fibers
    {r q N a : ℤ}
    (hr : 2 ≤ r) (hq : 3 ≤ q)
    (ha : r + 1 ≤ a) (hcount : a * (q + 1) ≤ N)
    (hN : N + 5 ≤ 4 * (r + q)) :
    a = r + 1 := by
  by_contra hne
  have ha' : r + 2 ≤ a := by omega
  have hp : 0 ≤ (r - 2) * (q - 3) :=
    mul_nonneg (by omega) (by omega)
  have hc : (r + 2) * (q + 1) ≤ a * (q + 1) :=
    mul_le_mul_of_nonneg_right ha' (by omega)
  nlinarith

theorem crossing_family_small
    {r q N m : ℤ}
    (hr : 2 ≤ r) (hq : 3 ≤ q)
    (hcount : 2 * m + (r - 1) * (q + 1) ≤ N)
    (hN : N + 5 ≤ 4 * (r + q)) :
    m ≤ 2 * q - 1 := by
  have hp : 0 ≤ (r - 1) * (q - 3) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

theorem two_simplex_fibers_required
    {r q N : ℤ}
    (hr : 3 ≤ r) (hq : 3 ≤ q)
    (hcount : (r + 1) + 2 * r * q ≤ N)
    (hN : N + 5 ≤ 4 * (r + q)) :
    False := by
  have hp : 0 < (r - 2) * (2 * q - 3) :=
    mul_pos (by omega) (by omega)
  nlinarith

theorem planar_one_simplex_equality
    {q N : ℤ} (hcount : 3 + 4 * q ≤ N)
    (hN : N + 5 ≤ 4 * (2 + q)) :
    N = 3 + 4 * q := by omega

theorem codimension_two_three_fibers
    {r N a k : ℤ}
    (hr : 2 ≤ r) (ha : r + 1 ≤ a)
    (hk : 3 ≤ k) (hcount : k * a ≤ N)
    (hN : N + 5 ≤ 4 * (r + 2)) :
    k = 3 := by
  by_contra hne
  have hk' : 4 ≤ k := by omega
  have hp : 4 * a ≤ k * a :=
    mul_le_mul_of_nonneg_right hk' (by omega)
  nlinarith

theorem codimension_two_summand_below_twice_dimension
    {r N a : ℤ}
    (hr : 2 ≤ r) (hcount : 3 * a ≤ N)
    (hN : N + 5 ≤ 4 * (r + 2)) :
    a < 2 * r := by omega

theorem codimension_two_one_small_fiber
    {r N : ℤ} (hr : 2 ≤ r)
    (hcount : 6 * r ≤ N)
    (hN : N + 5 ≤ 4 * (r + 2)) : False := by omega

theorem extra_vertex_and_large_fiber_equality
    {r N a s₀ s₁ s₂ e : ℤ}
    (hr : 2 ≤ r) (ha : r + 1 ≤ a)
    (h₀ : a ≤ s₀) (h₁ : a ≤ s₁)
    (h₂ : 2 * r ≤ s₂) (he : 1 ≤ e)
    (hcount : s₀ + s₁ + s₂ + e ≤ N)
    (hN : N + 5 ≤ 4 * (r + 2)) :
    a = r + 1 ∧ s₀ = r + 1 ∧ s₁ = r + 1 ∧
      s₂ = 2 * r ∧ e = 1 ∧ N = 4 * r + 3 := by omega

theorem three_small_fibers_extra_facet_equality
    {r N a s₀ s₁ s₂ e : ℤ}
    (ha : r + 1 ≤ a)
    (h₀ : a ≤ s₀) (h₁ : a ≤ s₁) (h₂ : a ≤ s₂)
    (he : r ≤ e) (hcount : s₀ + s₁ + s₂ + e ≤ N)
    (hN : N + 5 ≤ 4 * (r + 2)) :
    a = r + 1 ∧ s₀ = r + 1 ∧ s₁ = r + 1 ∧
      s₂ = r + 1 ∧ e = r ∧ N = 4 * r + 3 := by omega

theorem dimension_three_no_extra_edge
    {N s₀ s₁ e : ℤ} (h₀ : 3 ≤ s₀) (h₁ : 3 ≤ s₁)
    (he : 2 ≤ e) (hcount : s₀ + s₁ + e ≤ N)
    (hN : N ≤ 7) : False := by omega

end Papers.ProperSummandCounting

end
end BundlePart0

section BundlePart1
/- Source: Papers/MinkowskiFiberDichotomy.lean -/




@[expose] public section

/-! The individual homothety dichotomy and the two-small-fiber count. -/
noncomputable section
namespace Papers.MinkowskiFiberDichotomy

open Set Module
open Papers.PolytopeFourRegularTail Papers.PolytopeSimpleTailFace
open Papers.ProperImageFiberCount Papers.LinearImageFibers
open Papers.ParallelFaceDirections Papers.ParallelExposedFiber
open Papers.ParallelSupportEvaluation Papers.FiniteHullPolytope
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators

variable {n : ℕ}

def HomotheticFiber (P : ConvexPolytope n) (f : E n → E n)
    (π : E n →L[ℝ] E n) (q : (imagePolytope P π).vertices) : Prop :=
  ∃ α : ℝ,∃ b : E n,α≠0 ∧ ∀ x∈(vertexFiber P π q).vertices,f x=α•x+b

theorem fiber_image_eq
    (P : ConvexPolytope n) (f : E n → E n)
    (hf : ParallelOnTail P P.vertices f)
    (π : E n →L[ℝ] E n)
    (hvalues : ∀ x∈P.vertices,π (f x)=0)
    (q : (imagePolytope P π).vertices) :
    f '' ((vertexFiber P π q).vertices : Set (E n)) =
      f '' (P.vertices : Set (E n)) :=
  annihilator_fiber_image_eq P f hf (fiberFunctional P π q)
    (fun x hx => fiberFunctional_kernel P π q (f x) (hvalues x hx))

theorem homotheticFiber_of_small
    (P : ConvexPolytope n) (f : E n → E n)
    (hf : ParallelOnTail P P.vertices f)
    (π : E n →L[ℝ] E n)
    (himage : vectorSpan ℝ (f '' (P.vertices : Set (E n)))=π.ker)
    (hvalues : ∀ x∈P.vertices,π (f x)=0)
    (hnonconstant : ¬∃b:E n,∀x∈P.vertices,f x=b)
    (q : (imagePolytope P π).vertices)
    (hsmall : (vertexFiber P π q).vertices.card<2*finrank ℝ π.ker) :
    HomotheticFiber P f π q := by
  let R := vertexFiber P π q
  let r := finrank ℝ π.ker
  have hdim : R.dim=r := vertexFiber_dim_eq P f hf π himage hvalues q
  have hmin : ∀x∈R.vertices,r≤(R.vertices.filter (GeneralVertexStep R x)).card := by
    intro x hx
    have h := intrinsic_dim_le_neighbor_card R hx
    rw [hdim] at h
    exact h
  obtain ⟨α,b,hhom⟩ := (rigid_tail_of_min_degree_card_lt_twice R R.vertices
    (fun _ h => h) r hmin hsmall) f (parallel_on_vertexFiber P f hf π q)
  refine ⟨α,b,?_,hhom⟩
  intro hα
  apply hnonconstant
  refine ⟨b,?_⟩
  intro x hx
  have hmem : f x∈f '' ((vertexFiber P π q).vertices : Set (E n)) := by
    rw [fiber_image_eq P f hf π hvalues q]
    exact ⟨x,hx,rfl⟩
  obtain ⟨y,hy,hfy⟩ := hmem
  have hh := hhom y hy
  rw [hα,zero_smul,zero_add] at hh
  exact hfy.symm.trans hh

theorem fiber_homothetic_or_large
    (P : ConvexPolytope n) (f : E n → E n)
    (hf : ParallelOnTail P P.vertices f)
    (π : E n →L[ℝ] E n)
    (himage : vectorSpan ℝ (f '' (P.vertices : Set (E n)))=π.ker)
    (hvalues : ∀ x∈P.vertices,π (f x)=0)
    (hnonconstant : ¬∃b:E n,∀x∈P.vertices,f x=b)
    (q : (imagePolytope P π).vertices) :
    HomotheticFiber P f π q ∨
      2*finrank ℝ π.ker≤(vertexFiber P π q).vertices.card := by
  by_cases hs : (vertexFiber P π q).vertices.card<2*finrank ℝ π.ker
  · exact Or.inl (homotheticFiber_of_small P f hf π himage hvalues hnonconstant q hs)
  · exact Or.inr (le_of_not_gt hs)

theorem fiber_map_injective_of_homothetic
    (P : ConvexPolytope n) (f : E n → E n) (π : E n →L[ℝ] E n)
    (q : (imagePolytope P π).vertices) (h : HomotheticFiber P f π q) :
    Set.InjOn f ((vertexFiber P π q).vertices : Set (E n)) := by
  obtain ⟨α,b,hα,hhom⟩ := h
  intro x hx y hy hxy
  rw [hhom x hx,hhom y hy] at hxy
  have hh := add_right_cancel hxy
  exact (smul_right_injective _ hα) hh

theorem single_homothetic_count
    (P : ConvexPolytope n) (f : E n → E n)
    (hf : ParallelOnTail P P.vertices f)
    (π : E n →L[ℝ] E n)
    (himage : vectorSpan ℝ (f '' (P.vertices : Set (E n)))=π.ker)
    (hvalues : ∀ x∈P.vertices,π (f x)=0)
    (hnonconstant : ¬∃b:E n,∀x∈P.vertices,f x=b)
    (q0 : (imagePolytope P π).vertices)
    (hother : ∀q,q≠q0→¬HomotheticFiber P f π q) :
    (finrank ℝ π.ker+1)+2*finrank ℝ π.ker*(imagePolytope P π).dim≤P.vertices.card := by
  let Q := imagePolytope P π
  let r := finrank ℝ π.ker
  let sizes : Q.vertices → ℕ := fun q => (vertexFiber P π q).vertices.card
  let S : Finset Q.vertices := Finset.univ.erase q0
  have h0 : r+1≤sizes q0 := by
    have h := dimension_add_one_le_vertices (vertexFiber P π q0)
    rw [vertexFiber_dim_eq P f hf π himage hvalues q0] at h
    exact h
  have hlarge : ∀q∈S,2*r≤sizes q := by
    intro q hq
    exact (fiber_homothetic_or_large P f hf π himage hvalues hnonconstant q).resolve_left
      (hother q (Finset.mem_erase.mp hq).1)
  have hQdim : Q.dim≤S.card := by
    have hh := dimension_add_one_le_vertices Q
    have hS : S.card=Q.vertices.card-1 := by simp only [S,Finset.card_erase_of_mem
      (Finset.mem_univ q0),Finset.card_univ,Fintype.card_coe,Q]
    omega
  have hsum : 2*r*Q.dim≤∑q∈S,sizes q := by
    calc
      2*r*Q.dim ≤ 2*r*S.card := Nat.mul_le_mul_left _ hQdim
      _ = ∑_q∈S,2*r := by simp [Nat.mul_comm]
      _ ≤ ∑q∈S,sizes q := Finset.sum_le_sum hlarge
  calc
    r+1+2*r*Q.dim ≤ sizes q0+∑q∈S,sizes q := Nat.add_le_add h0 hsum
    _ = ∑q : Q.vertices,sizes q := by
      rw [Nat.add_comm]
      exact Finset.sum_erase_add Finset.univ sizes (Finset.mem_univ q0)
    _ ≤ P.vertices.card := total_vertexFiber_card_le P π

theorem two_homothetic_fibers_of_large_dimensions
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    (f : E n → E n) (hf : ParallelOnTail P P.vertices f)
    (π : E n →L[ℝ] E n)
    (himage : vectorSpan ℝ (f '' (P.vertices : Set (E n)))=π.ker)
    (hvalues : ∀ x∈P.vertices,π (f x)=0)
    (hnonconstant : ¬∃b:E n,∀x∈P.vertices,f x=b)
    (hr : 3≤finrank ℝ π.ker) (hq : 3≤(imagePolytope P π).dim)
    (hN : P.vertices.card≤4*n-5) :
    ∃ q0 q1 : (imagePolytope P π).vertices,q0≠q1 ∧
      HomotheticFiber P f π q0 ∧ HomotheticFiber P f π q1 := by
  have hdim := image_dim_add_kernel_dim P hP π
  obtain ⟨q0,α,b,hα,hhom⟩ := exists_nonzero_homothetic_vertexFiber P hP f hf π
    himage hvalues (by omega) (by omega) (by omega) hnonconstant
  have h0 : HomotheticFiber P f π q0 := ⟨α,b,hα,hhom⟩
  by_contra hnone
  have hother : ∀q,q≠q0→¬HomotheticFiber P f π q := by
    intro q hq hhom
    exact hnone ⟨q0,q,hq.symm,h0,hhom⟩
  have hc := single_homothetic_count P f hf π himage hvalues hnonconstant q0 hother
  have hcz : ((finrank ℝ π.ker : ℤ)+1)+2*(finrank ℝ π.ker : ℤ)*
      ((imagePolytope P π).dim : ℤ)≤(P.vertices.card : ℤ) := by exact_mod_cast hc
  exact Papers.ProperSummandCounting.two_simplex_fibers_required
    (by exact_mod_cast hr) (by exact_mod_cast hq) hcz (by omega)

end Papers.MinkowskiFiberDichotomy


end
end
end BundlePart1

section BundlePart2
/- Source: Papers/MinkowskiFiberCounts.lean -/




@[expose] public section

/-!
# Vertex counts in genuine summand fibers

An exposed fiber whose normal annihilates a summand direction contains
every summand label. The proof uses monotone actual edges and therefore
does not assume a combinatorial labeling certificate.
-/

noncomputable section
namespace Papers.MinkowskiFiberCounts

open Set
open Papers.MinkowskiVertexMap Papers.ParallelExposedFiber
open Papers.ParallelFaceDirections Papers.ParallelSupportEvaluation
open Papers.PolytopeFourRegularTail Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

theorem parallel_translate_values
    (P : ConvexPolytope n) (f : E n → E n)
    (hf : ParallelOnTail P P.vertices f) (c : E n) :
    ParallelOnTail P P.vertices (fun x => f x-c) := by
  intro x hx y hy hxy
  obtain ⟨μ,hμ⟩ := hf x hx y hy hxy
  refine ⟨μ,?_⟩
  simpa only [sub_sub_sub_cancel_right] using hμ

theorem constant_functional_fiber_carries_image
    (P : ConvexPolytope n) (f : E n → E n)
    (hf : ParallelOnTail P P.vertices f)
    (w : E n →L[ℝ] ℝ) (t : ℝ)
    (hconst : ∀ x ∈ P.vertices,w (f x)=t)
    (x : E n) (hx : x∈P.vertices) :
    ∃ y∈maxVertices P w,f y=f x := by
  let g : E n → E n := fun z => f z-f x
  have hg := parallel_translate_values P f hf (f x)
  have hwg : ∀ z∈P.vertices,w (g z)=0 := by
    intro z hz
    simp only [g,map_sub,hconst z hz,hconst x hx,sub_self]
  obtain ⟨y,hy,heq⟩ :=
    exposed_fiber_carries_image P g hg w hwg x hx
  refine ⟨y,hy,?_⟩
  have hh : f y-f x=0 := by simpa only [g,sub_self] using heq
  exact sub_eq_zero.mp hh

theorem leftVertexMap_constant_on_annihilator
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (w : E n →L[ℝ] ℝ)
    (hw : vectorSpan ℝ A.toSet ≤ w.ker)
    {a : E n} (ha : a∈A.vertices) :
    ∀ x∈P.vertices,w (leftVertexMap P A B hP x)=w a := by
  intro x hx
  have hfa := (leftVertexMap_spec P A B hP hx).1
  have hv := vsub_mem_vectorSpan ℝ
    (vertex_mem_body_of_mem_vertices A hfa)
    (vertex_mem_body_of_mem_vertices A ha)
  have heq := hw hv
  change w (leftVertexMap P A B hP x-a)=0 at heq
  rw [map_sub] at heq
  exact sub_eq_zero.mp heq

theorem minkowski_exposed_fiber_label_surjective
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (w : E n →L[ℝ] ℝ)
    (hw : vectorSpan ℝ A.toSet ≤ w.ker)
    {a : E n} (ha : a∈A.vertices) :
    ∃ x∈(facePolytope P (maxFace_isFace P w)).vertices,
      leftVertexMap P A B hP x=a := by
  obtain ⟨x,hx,hfx⟩ := leftVertexMap_surjective P A B hP ha
  obtain ⟨y,hy,hfy⟩ := constant_functional_fiber_carries_image
    P (leftVertexMap P A B hP) (leftVertexMap_parallel P A B hP)
    w (w a) (leftVertexMap_constant_on_annihilator P A B hP w hw ha) x hx
  refine ⟨y,?_,hfy.trans hfx⟩
  rw [maxFace_vertices]
  exact hy

theorem minkowski_exposed_fiber_vertex_count
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (w : E n →L[ℝ] ℝ)
    (hw : vectorSpan ℝ A.toSet ≤ w.ker) :
    A.vertices.card≤(facePolytope P (maxFace_isFace P w)).vertices.card := by
  let F := facePolytope P (maxFace_isFace P w)
  have hsub : A.vertices ⊆ F.vertices.image (leftVertexMap P A B hP) := by
    intro a ha
    obtain ⟨x,hx,hfx⟩ := minkowski_exposed_fiber_label_surjective P A B hP w hw ha
    exact Finset.mem_image.mpr ⟨x,hx,hfx⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

theorem minkowski_exposed_fiber_card_ge_dim_add_one
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (w : E n →L[ℝ] ℝ)
    (hw : vectorSpan ℝ A.toSet ≤ w.ker) :
    A.dim+1≤(facePolytope P (maxFace_isFace P w)).vertices.card :=
  (Papers.LinearImageFibers.dimension_add_one_le_vertices A).trans
    (minkowski_exposed_fiber_vertex_count P A B hP w hw)

end Papers.MinkowskiFiberCounts


end
end
end BundlePart2

section BundlePart3
/- Source: Papers/MinkowskiQuotientCounting.lean -/





@[expose] public section

/-!
# Quotient-fiber counts for genuine Minkowski summands

The quotient is the actual orthogonal projection perpendicular to the
summand's affine direction space.  Its vertex fibers are disjoint
actual faces.  Their label-surjectivity gives the paper's cardinality
inequalities without an assumed fiber-count certificate.
-/

noncomputable section
namespace Papers.MinkowskiQuotientCounting

open Set Module
open Papers.MinkowskiFiberCounts Papers.LinearImageFibers Papers.FiniteHullPolytope
open Papers.ParallelSupportEvaluation Papers.ProperSummandCounting
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators Pointwise

variable {n : ℕ}

def summandProjection (A : ConvexPolytope n) : E n →L[ℝ] E n :=
  (vectorSpan ℝ A.toSet)ᗮ.starProjection

theorem summandProjection_kernel (A : ConvexPolytope n) :
    (summandProjection A).ker=vectorSpan ℝ A.toSet := by
  simp only [summandProjection,Submodule.ker_starProjection,
    Submodule.orthogonal_orthogonal]

abbrev quotientPolytope (P A : ConvexPolytope n) : ConvexPolytope n :=
  imagePolytope P (summandProjection A)

theorem quotient_dimension_add_summand_dimension
    (P A : ConvexPolytope n) (hP : P.IsFullDim) :
    (quotientPolytope P A).dim+A.dim=n := by
  have h := image_dim_add_kernel_dim P hP (summandProjection A)
  rw [summandProjection_kernel] at h
  exact h

theorem quotient_vertex_fiber_card
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (q : (quotientPolytope P A).vertices) :
    A.vertices.card≤(vertexFiber P (summandProjection A) q).vertices.card := by
  have hw : vectorSpan ℝ A.toSet ≤ (fiberFunctional P (summandProjection A) q).ker := by
    intro z hz
    apply fiberFunctional_kernel P (summandProjection A) q z
    change z∈(summandProjection A).ker
    rw [summandProjection_kernel]
    exact hz
  exact minkowski_exposed_fiber_vertex_count P A B hP
    (fiberFunctional P (summandProjection A) q) hw

theorem actual_vertex_product_bound
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet) :
    A.vertices.card*(quotientPolytope P A).vertices.card≤P.vertices.card := by
  let Q := quotientPolytope P A
  calc
    A.vertices.card*Q.vertices.card =
        ∑ _q : Q.vertices,A.vertices.card := by simp [Nat.mul_comm]
    _ ≤ ∑ q : Q.vertices,(vertexFiber P (summandProjection A) q).vertices.card :=
      Finset.sum_le_sum (fun q _ => quotient_vertex_fiber_card P A B hP q)
    _ ≤ P.vertices.card := total_vertexFiber_card_le P (summandProjection A)

theorem actual_dimension_product_bound
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet) :
    A.vertices.card*((quotientPolytope P A).dim+1)≤P.vertices.card :=
  (Nat.mul_le_mul_left A.vertices.card
    (dimension_add_one_le_vertices (quotientPolytope P A))).trans
      (actual_vertex_product_bound P A B hP)

theorem summand_minimal_vertices_of_codimension_at_least_three
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hP : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : 3≤(quotientPolytope P A).dim)
    (hN : P.vertices.card≤4*n-5) :
    A.vertices.card=A.dim+1 := by
  have hA := dimension_add_one_le_vertices A
  have hcount := actual_dimension_product_bound P A B hP
  have hdim := quotient_dimension_add_summand_dimension P A hfull
  have hNz : (P.vertices.card : ℤ)+5≤4*(n : ℤ) := by omega
  have hAz : (A.dim : ℤ)+1≤(A.vertices.card : ℤ) := by exact_mod_cast hA
  have hcountz : (A.vertices.card : ℤ)*((quotientPolytope P A).dim+1)≤P.vertices.card := by
    exact_mod_cast hcount
  have hdimz : ((quotientPolytope P A).dim : ℤ)+(A.dim : ℤ)=(n : ℤ) := by
    exact_mod_cast hdim
  have heq := simplex_of_many_fibers (r := (A.dim : ℤ))
    (q := ((quotientPolytope P A).dim : ℤ))
    (N := (P.vertices.card : ℤ)) (a := (A.vertices.card : ℤ))
    (by exact_mod_cast hr) (by exact_mod_cast hq) hAz hcountz (by omega)
  exact_mod_cast heq

theorem quotient_has_three_vertices_of_codimension_two
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hP : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : (quotientPolytope P A).dim=2)
    (hN : P.vertices.card≤4*n-5) :
    (quotientPolytope P A).vertices.card=3 := by
  have hA := dimension_add_one_le_vertices A
  have hQ := dimension_add_one_le_vertices (quotientPolytope P A)
  have hcount := actual_vertex_product_bound P A B hP
  have hdim := quotient_dimension_add_summand_dimension P A hfull
  have hNz : (P.vertices.card : ℤ)+5≤4*((A.dim : ℤ)+2) := by omega
  have hAz : (A.dim : ℤ)+1≤(A.vertices.card : ℤ) := by exact_mod_cast hA
  have hQz : (3:ℤ)≤(quotientPolytope P A).vertices.card := by omega
  have hcountz : ((quotientPolytope P A).vertices.card : ℤ)*
      (A.vertices.card : ℤ)≤P.vertices.card := by
    have h := hcount
    rw [Nat.mul_comm] at h
    exact_mod_cast h
  have heq := codimension_two_three_fibers
    (r := (A.dim : ℤ)) (N := (P.vertices.card : ℤ))
    (a := (A.vertices.card : ℤ)) (k := ((quotientPolytope P A).vertices.card : ℤ))
    (by exact_mod_cast hr) hAz hQz hcountz hNz
  exact_mod_cast heq

theorem summand_card_lt_twice_dim_of_codimension_two
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hP : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : (quotientPolytope P A).dim=2)
    (hN : P.vertices.card≤4*n-5) :
    A.vertices.card<2*A.dim := by
  have hcount := actual_dimension_product_bound P A B hP
  have hdim := quotient_dimension_add_summand_dimension P A hfull
  rw [hq] at hcount hdim
  have hcountz : 3*(A.vertices.card : ℤ)≤(P.vertices.card : ℤ) := by
    norm_num at hcount
    have h := hcount
    rw [Nat.mul_comm] at h
    exact_mod_cast h
  have hNz : (P.vertices.card : ℤ)+5≤4*((A.dim : ℤ)+2) := by omega
  have h := codimension_two_summand_below_twice_dimension
    (r := (A.dim : ℤ)) (N := (P.vertices.card : ℤ)) (a := (A.vertices.card : ℤ))
    (by exact_mod_cast hr) hcountz hNz
  exact_mod_cast h

end Papers.MinkowskiQuotientCounting

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/ProperMinkowskiMap.lean -/





@[expose] public section

/-!
# Proper summands give nonhomothetic actual vertex maps

The dimensions are the actual affine dimensions of the summand and P.
For a segment summand the map has exactly two possible values, which
supplies the two constant homotheties used in the two-colour reduction.
-/

noncomputable section
namespace Papers.ProperMinkowskiMap

open Set Module AffineSubspace
open Papers.MinkowskiVertexMap Papers.PolytopeFourRegularTail
open Papers.FaceVertexCardinality Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

theorem vectorSpan_vertices_eq_body (P : ConvexPolytope n) :
    vectorSpan ℝ (P.vertices : Set (E n)) = vectorSpan ℝ P.toSet := by
  symm
  change vectorSpan ℝ (convexHull ℝ (P.vertices : Set (E n))) = _
  rw [← direction_affineSpan,affineSpan_convexHull,direction_affineSpan]

def homothetyMap (α : ℝ) (b : E n) : E n →ᵃ[ℝ] E n where
  toFun x := α•x+b
  linear := α•LinearMap.id
  map_vadd' p v := by
    change α•(v+p)+b=α•v+(α•p+b)
    module

theorem leftVertexMap_nonhomothetic
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim) (hproper : A.dim<P.dim) :
    ¬ ∃ α : ℝ,∃ b : E n,∀x∈P.vertices,leftVertexMap P A B hP x=α•x+b := by
  rintro ⟨α,b,hhom⟩
  have himage : homothetyMap α b '' (P.vertices : Set (E n)) =
      (A.vertices : Set (E n)) := by
    rw [← leftVertexMap_image P A B hP]
    apply Set.image_congr
    intro x hx
    exact (hhom x hx).symm
  by_cases hα : α=0
  · have hdir : vectorSpan ℝ (A.vertices : Set (E n))=⊥ := by
      rw [← himage,← AffineMap.map_vectorSpan]
      simp only [homothetyMap,hα,zero_smul,Submodule.map_zero]
    rw [vectorSpan_vertices_eq_body] at hdir
    have hz : A.dim=0 := by
      change finrank ℝ (vectorSpan ℝ A.toSet)=0
      rw [hdir,finrank_bot]
    omega
  · have hinj : Function.Injective (homothetyMap α b).linear := by
      intro x y hxy
      have h := congrArg (fun z : E n => α⁻¹•z) hxy
      simpa only [homothetyMap,LinearMap.smul_apply,LinearMap.id_apply,
        smul_smul,inv_mul_cancel₀ hα,one_smul] using h
    have heq := finrank_vectorSpan_affineImage (homothetyMap α b) hinj
      (P.vertices : Set (E n))
    rw [himage,vectorSpan_vertices_eq_body,vectorSpan_vertices_eq_body] at heq
    have hdim : A.dim=P.dim := heq
    omega

theorem actual_vertex_map_of_proper_summand
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim) (hproper : A.dim<P.dim) :
    ∃ f : E n → E n,
      ParallelOnTail P P.vertices f ∧
      ¬ (∃ α : ℝ,∃ b : E n,∀x∈P.vertices,f x=α•x+b) ∧
      f '' (P.vertices : Set (E n))=(A.vertices : Set (E n)) := by
  exact ⟨leftVertexMap P A B hP,leftVertexMap_parallel P A B hP,
    leftVertexMap_nonhomothetic P A B hP hApos hproper,
    leftVertexMap_image P A B hP⟩

theorem vertices_of_dimension_one
    (A : ConvexPolytope n) (hdim : A.dim=1) :
    ∃ a∈A.vertices,∃ b∈A.vertices,a≠b ∧
      ∀ x∈A.vertices,x=a ∨ x=b := by
  obtain ⟨a,ha⟩ := A.vertices_nonempty
  obtain ⟨b,hb,_hbbody,hba,hsegment⟩ := spigolo_segmento A (toSet_isFace A)
    hdim ha (vertex_mem_body_of_mem_vertices A ha)
  refine ⟨a,ha,b,hb,hba.symm,?_⟩
  intro x hx
  have hxseg : x∈segment ℝ a b := by
    rw [← hsegment]
    exact vertex_mem_body_of_mem_vertices A hx
  exact ExposedEdgeCenters.extreme_point_on_segment A.toSet
    (vertex_mem_body_extremePoints A hx)
    (vertex_mem_body_of_mem_vertices A ha)
    (vertex_mem_body_of_mem_vertices A hb) hxseg

theorem actual_two_constant_homotheties_of_segment_summand
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (hAdim : A.dim=1) (hPdim : 2≤P.dim) :
    ∃ f : E n → E n,∃ a b : E n,
      a≠b ∧ ParallelOnTail P P.vertices f ∧
      ¬ (∃ α : ℝ,∃ c : E n,∀x∈P.vertices,f x=α•x+c) ∧
      (∀ x∈P.vertices,f x=a ∨ f x=b) ∧
      (∃ x∈P.vertices,f x=a) ∧ (∃ x∈P.vertices,f x=b) := by
  obtain ⟨a,ha,b,hb,hab,hverts⟩ := vertices_of_dimension_one A hAdim
  refine ⟨leftVertexMap P A B hP,a,b,hab,leftVertexMap_parallel P A B hP,
    leftVertexMap_nonhomothetic P A B hP (by omega) (by omega),?_,
    leftVertexMap_surjective P A B hP ha,leftVertexMap_surjective P A B hP hb⟩
  intro x hx
  exact hverts _ (leftVertexMap_spec P A B hP hx).1

end Papers.ProperMinkowskiMap

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/SimplexQuotientOppositeFace.lean -/








@[expose] public section

/-!
# The opposite face of a simplex quotient

An affinely independent actual quotient vertex set supplies a supporting
functional constant on all vertices except one.  Pulling it back to P
makes its exterior vertex set exactly the distinguished quotient fiber,
provided every P vertex projects to a quotient vertex.
-/

noncomputable section
namespace Papers.SimplexQuotientOppositeFace

open Set Module AffineSubspace
open Papers.FiniteHullPolytope Papers.LinearImageFibers
open Papers.ParallelSupportEvaluation Papers.ProperMinkowskiMap
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ}

theorem exists_other_vertex
    (Q : ConvexPolytope n) (hcard : 2≤Q.vertices.card) (q : E n) :
    ∃ b∈Q.vertices,b≠q := by
  by_contra! h
  have hsub : Q.vertices⊆{q} := fun b hb => Finset.mem_singleton.mpr (h b hb)
  have hle := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hle
  omega

theorem actual_vertices_affineIndependent_of_minimal_card
    (Q : ConvexPolytope n) (hcard : Q.vertices.card=Q.dim+1) :
    AffineIndependent ℝ (fun v : Q.vertices => v.val) :=
  (vertices_affineIndependent_iff Q).mpr hcard

theorem opposite_vertex_functional
    (Q : ConvexPolytope n)
    (hAI : AffineIndependent ℝ (fun v : Q.vertices => v.val))
    (hcard : 2≤Q.vertices.card) {q : E n} (hq : q∈Q.vertices) :
    ∃ u : E n →L[ℝ] ℝ,∃ c : ℝ,
      u q<c ∧ ∀ z∈Q.vertices,z≠q → u z=c := by
  obtain ⟨b,hb,hbq⟩ := exists_other_vertex Q hcard q
  let S : Set (E n) := (Q.vertices : Set (E n))\{q}
  let L := vectorSpan ℝ S
  have hbS : b∈S := ⟨hb,by simpa using hbq⟩
  let qq : Q.vertices := ⟨q,hq⟩
  have himage :
      (fun v : Q.vertices => v.val) '' ((Set.univ : Set Q.vertices)\{qq})=S := by
    ext z
    constructor
    · rintro ⟨v,⟨_,hv⟩,rfl⟩
      refine ⟨v.property,?_⟩
      intro heq
      apply hv
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact Set.mem_singleton_iff.mp heq
    · rintro ⟨hz,hzq⟩
      refine ⟨⟨z,hz⟩,⟨Set.mem_univ _,?_⟩,rfl⟩
      intro heq
      apply hzq
      have hv : (⟨z,hz⟩ : Q.vertices)=qq := Set.mem_singleton_iff.mp heq
      exact Set.mem_singleton_iff.mpr (congrArg Subtype.val hv)
  have hnot : q∉affineSpan ℝ S := by
    have h := hAI.notMem_affineSpan_sdiff qq Set.univ
    rwa [himage] at h
  have hvec : q-b∉L := by
    intro hqb
    apply hnot
    apply (vsub_right_mem_direction_iff_mem (mem_affineSpan ℝ hbS) q).mp
    rw [direction_affineSpan]
    exact hqb
  have hdual : ∃ l : E n →ₗ[ℝ] ℝ,l∈L.dualAnnihilator ∧ l (q-b)≠0 := by
    by_contra! h
    exact hvec ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff L (q-b)).mp h)
  obtain ⟨l,hl,hlq⟩ := hdual
  have hconst : ∀ z∈Q.vertices,z≠q → l z=l b := by
    intro z hz hzq
    have hzS : z∈S := ⟨hz,by simpa using hzq⟩
    have hd : z-b∈L := vsub_mem_vectorSpan ℝ hzS hbS
    have hzero := (Submodule.mem_dualAnnihilator l).mp hl (z-b) hd
    exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  rcases lt_or_gt_of_ne hlq with hneg | hpos
  · refine ⟨l.toContinuousLinearMap,l b,?_,hconst⟩
    change l q<l b
    exact sub_neg.mp (by simpa only [map_sub] using hneg)
  · refine ⟨-l.toContinuousLinearMap,-l b,?_,?_⟩
    · change -l q < -l b
      have hqb : l b<l q := sub_pos.mp (by simpa only [map_sub] using hpos)
      exact neg_lt_neg hqb
    · intro z hz hzq
      change -l z= -l b
      rw [hconst z hz hzq]

theorem opposite_quotient_face
    (P : ConvexPolytope n) (π : E n →L[ℝ] E n)
    (hAI : AffineIndependent ℝ
      (fun v : (imagePolytope P π).vertices => v.val))
    (hcard : 2≤(imagePolytope P π).vertices.card)
    (q : (imagePolytope P π).vertices)
    (hcover : ∀ x∈P.vertices,π x∈(imagePolytope P π).vertices) :
    ∃ w : E n →L[ℝ] ℝ,
      (∀ z,π z=0 → w z=0) ∧
      ∀ x∈P.vertices,
        x∉Papers.MinkowskiFaces.maxFace P.toSet w.toLinearMap ↔ π x=q.val := by
  let Q := imagePolytope P π
  obtain ⟨u,c,huq,hother⟩ := opposite_vertex_functional Q hAI hcard q.property
  obtain ⟨b,hb,hbq⟩ := exists_other_vertex Q hcard q.val
  obtain ⟨v,hv,hπv⟩ := image_vertex_has_vertex_preimage P π ⟨b,hb⟩
  let w : E n →L[ℝ] ℝ := u.comp π
  have hwv : w v=c := by
    change u (π v)=c
    rw [hπv]
    exact hother b hb hbq
  have hbound : ∀ x∈P.vertices,w x≤c := by
    intro x hx
    change u (π x)≤c
    by_cases hπx : π x=q.val
    · rw [hπx]
      exact huq.le
    · exact (hother (π x) (hcover x hx) hπx).le
  refine ⟨w,fun z hz => by change u (π z)=0; rw [hz,map_zero],?_⟩
  intro x hx
  constructor
  · intro hxout
    by_contra hπx
    apply hxout
    apply vertex_mem_maxFace P w hx
    intro z hz
    have hwx : w x=c := hother (π x) (hcover x hx) hπx
    rw [hwx]
    exact hbound z hz
  · intro hπx hxface
    have hbad := hxface.2 v (subset_convexHull ℝ _ hv)
    have hwx : w x=u q.val := by change u (π x)=u q.val; rw [hπx]
    change w v≤w x at hbad
    rw [hwv,hwx] at hbad
    exact (not_lt_of_ge hbad) huq

end Papers.SimplexQuotientOppositeFace

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/MinkowskiSummandFibers.lean -/






@[expose] public section

/-! Actual summand fibers, centered maps, and their exact label cardinalities. -/
noncomputable section
namespace Papers.MinkowskiSummandFibers

open Set Module
open Papers.MinkowskiVertexMap Papers.MinkowskiFiberCounts
open Papers.MinkowskiQuotientCounting Papers.ProperMinkowskiMap
open Papers.MinkowskiFiberDichotomy Papers.ProperImageFiberCount
open Papers.LinearImageFibers Papers.ParallelSupportEvaluation
open Papers.PolytopeFourRegularTail Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

def centeredSummandMap (P A B : ConvexPolytope n)
    (hP : P.toSet=A.toSet+B.toSet) (a0 : E n) (x : E n) : E n :=
  leftVertexMap P A B hP x-a0

theorem centeredSummandMap_parallel
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet) (a0 : E n) :
    ParallelOnTail P P.vertices (centeredSummandMap P A B hP a0) :=
  parallel_translate_values P _ (leftVertexMap_parallel P A B hP) a0

theorem centeredSummandMap_image
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet) (a0 : E n) :
    centeredSummandMap P A B hP a0 '' (P.vertices : Set (E n)) =
      homothetyMap 1 (-a0) '' (A.vertices : Set (E n)) := by
  rw [← leftVertexMap_image P A B hP,Set.image_image]
  apply Set.image_congr
  intro x hx
  change leftVertexMap P A B hP x-a0=((1:ℝ))•leftVertexMap P A B hP x+(-a0)
  simp only [one_smul,sub_eq_add_neg]

theorem centeredSummandMap_direction
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet) (a0 : E n) :
    vectorSpan ℝ (centeredSummandMap P A B hP a0 '' (P.vertices : Set (E n))) =
      (summandProjection A).ker := by
  rw [centeredSummandMap_image,← AffineMap.map_vectorSpan,summandProjection_kernel]
  simpa only [homothetyMap,one_smul,Submodule.map_id] using vectorSpan_vertices_eq_body A

theorem centeredSummandMap_values
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    {a0 : E n} (ha0 : a0∈A.vertices) :
    ∀x∈P.vertices,summandProjection A (centeredSummandMap P A B hP a0 x)=0 := by
  intro x hx
  change centeredSummandMap P A B hP a0 x∈(summandProjection A).ker
  rw [summandProjection_kernel]
  exact vsub_mem_vectorSpan ℝ
    (vertex_mem_body_of_mem_vertices A (leftVertexMap_spec P A B hP hx).1)
    (vertex_mem_body_of_mem_vertices A ha0)

theorem centeredSummandMap_nonconstant
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim) (hproper : A.dim<P.dim) (a0 : E n) :
    ¬∃b:E n,∀x∈P.vertices,centeredSummandMap P A B hP a0 x=b := by
  rintro ⟨b,hb⟩
  apply leftVertexMap_nonhomothetic P A B hP hApos hproper
  refine ⟨0,b+a0,?_⟩
  intro x hx
  have hh := hb x hx
  change leftVertexMap P A B hP x-a0=b at hh
  simp only [zero_smul,zero_add]
  exact sub_eq_iff_eq_add.mp hh

def SummandHomotheticFiber
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (q : (quotientPolytope P A).vertices) : Prop :=
  HomotheticFiber P (leftVertexMap P A B hP) (summandProjection A) q

theorem summandHomotheticFiber_iff_centered
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (a0 : E n) (q : (quotientPolytope P A).vertices) :
    SummandHomotheticFiber P A B hP q ↔
      HomotheticFiber P (centeredSummandMap P A B hP a0) (summandProjection A) q := by
  constructor
  · rintro ⟨α,b,hα,hh⟩
    exact ⟨α,b-a0,hα,fun x hx => by rw [centeredSummandMap,hh x hx]; module⟩
  · rintro ⟨α,b,hα,hh⟩
    refine ⟨α,b+a0,hα,?_⟩
    intro x hx
    have hv := hh x hx
    change leftVertexMap P A B hP x-a0=α•x+b at hv
    calc
      leftVertexMap P A B hP x = (α•x+b)+a0 := sub_eq_iff_eq_add.mp hv
      _ = α•x+(b+a0) := by abel

theorem summand_vertexFiber_dim
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (q : (quotientPolytope P A).vertices) :
    (vertexFiber P (summandProjection A) q).dim=A.dim := by
  obtain ⟨a0,ha0⟩ := A.vertices_nonempty
  have h := vertexFiber_dim_eq P (centeredSummandMap P A B hP a0)
    (centeredSummandMap_parallel P A B hP a0) (summandProjection A)
    (centeredSummandMap_direction P A B hP a0)
    (centeredSummandMap_values P A B hP ha0) q
  rw [summandProjection_kernel] at h
  exact h

theorem summand_fiber_homothetic_or_large
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim) (hproper : A.dim<P.dim)
    (q : (quotientPolytope P A).vertices) :
    SummandHomotheticFiber P A B hP q ∨
      2*A.dim≤(vertexFiber P (summandProjection A) q).vertices.card := by
  obtain ⟨a0,ha0⟩ := A.vertices_nonempty
  have h := fiber_homothetic_or_large P (centeredSummandMap P A B hP a0)
    (centeredSummandMap_parallel P A B hP a0) (summandProjection A)
    (centeredSummandMap_direction P A B hP a0)
    (centeredSummandMap_values P A B hP ha0)
    (centeredSummandMap_nonconstant P A B hP hApos hproper a0) q
  rw [← summandHomotheticFiber_iff_centered,summandProjection_kernel] at h
  exact h

theorem summand_vertexFiber_image
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (q : (quotientPolytope P A).vertices) :
    leftVertexMap P A B hP ''
      ((vertexFiber P (summandProjection A) q).vertices : Set (E n)) =
      (A.vertices : Set (E n)) := by
  let w := fiberFunctional P (summandProjection A) q
  have hw : vectorSpan ℝ A.toSet≤w.ker := by
    intro z hz
    apply fiberFunctional_kernel P (summandProjection A) q z
    change z∈(summandProjection A).ker
    rwa [summandProjection_kernel]
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [vertexFiber_vertices] at hx
    exact (leftVertexMap_spec P A B hP (Finset.mem_filter.mp hx).1).1
  · intro ha
    exact minkowski_exposed_fiber_label_surjective P A B hP w hw ha

theorem homothetic_summand_fiber_card
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (q : (quotientPolytope P A).vertices)
    (hh : SummandHomotheticFiber P A B hP q) :
    (vertexFiber P (summandProjection A) q).vertices.card=A.vertices.card := by
  let R := vertexFiber P (summandProjection A) q
  have hinj := fiber_map_injective_of_homothetic P
    (leftVertexMap P A B hP) (summandProjection A) q hh
  have himage : R.vertices.image (leftVertexMap P A B hP)=A.vertices := by
    apply Finset.coe_injective
    rw [Finset.coe_image]
    exact summand_vertexFiber_image P A B hP q
  rw [← himage,Finset.card_image_of_injOn hinj]

theorem exists_homothetic_summand_fiber
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hP : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim) (hproper : A.dim<n)
    (hN : P.vertices.card≤4*n-5) :
    ∃q:(quotientPolytope P A).vertices,SummandHomotheticFiber P A B hP q := by
  obtain ⟨a0,ha0⟩ := A.vertices_nonempty
  have hkernel : finrank ℝ (summandProjection A).ker=A.dim := by
    rw [summandProjection_kernel]; rfl
  obtain ⟨q,α,b,hα,hh⟩ := exists_nonzero_homothetic_vertexFiber P hfull
    (centeredSummandMap P A B hP a0) (centeredSummandMap_parallel P A B hP a0)
    (summandProjection A) (centeredSummandMap_direction P A B hP a0)
    (centeredSummandMap_values P A B hP ha0)
    (by rw [hkernel]; omega) (by rwa [hkernel]) (by omega)
    (centeredSummandMap_nonconstant P A B hP hApos (by rwa [hfull]) a0)
  exact ⟨q,(summandHomotheticFiber_iff_centered P A B hP a0 q).mpr ⟨α,b,hα,hh⟩⟩

theorem exists_two_homothetic_summand_fibers
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hP : P.toSet=A.toSet+B.toSet)
    (hr : 3≤A.dim) (hq : 3≤(quotientPolytope P A).dim)
    (hN : P.vertices.card≤4*n-5) :
    ∃q0 q1:(quotientPolytope P A).vertices,q0≠q1 ∧
      SummandHomotheticFiber P A B hP q0 ∧ SummandHomotheticFiber P A B hP q1 := by
  obtain ⟨a0,ha0⟩ := A.vertices_nonempty
  have hdim := quotient_dimension_add_summand_dimension P A hfull
  obtain ⟨q0,q1,hne,h0,h1⟩ := two_homothetic_fibers_of_large_dimensions P hfull
    (centeredSummandMap P A B hP a0) (centeredSummandMap_parallel P A B hP a0)
    (summandProjection A) (centeredSummandMap_direction P A B hP a0)
    (centeredSummandMap_values P A B hP ha0)
    (centeredSummandMap_nonconstant P A B hP (by omega) (by rw [hfull]; omega) a0)
    (by rwa [summandProjection_kernel]) hq hN
  exact ⟨q0,q1,hne,(summandHomotheticFiber_iff_centered P A B hP a0 q0).mpr h0,
    (summandHomotheticFiber_iff_centered P A B hP a0 q1).mpr h1⟩

end Papers.MinkowskiSummandFibers


end
end
end BundlePart6

section BundlePart7
/- Source: Papers/MinkowskiPositiveFibers.lean -/





@[expose] public section

/-! A homothetic summand fiber is a positive homothetic copy of the actual summand. -/
noncomputable section
namespace Papers.MinkowskiPositiveFibers

open Set
open Papers.MinkowskiVertexMap Papers.MinkowskiSummandFibers
open Papers.MinkowskiQuotientCounting Papers.ProperMinkowskiMap
open Papers.LinearImageFibers Papers.PolytopeVertexCone
open Papers.PolytopeSimpleTailFace Papers.ParallelSupportEvaluation Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

theorem positive_scale_on_summand_fiber
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim) (q : (quotientPolytope P A).vertices)
    (α : ℝ) (b : E n) (hα : α≠0)
    (hhom : ∀x∈(vertexFiber P (summandProjection A) q).vertices,
      leftVertexMap P A B hP x=α•x+b) : 0<α := by
  let R := vertexFiber P (summandProjection A) q
  obtain ⟨x,hx⟩ := R.vertices_nonempty
  have hdim : 0<R.dim := by rw [summand_vertexFiber_dim P A B hP q]; exact hApos
  have hcount := intrinsic_dim_le_neighbor_card R hx
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0<(actualNeighbors R x).card by omega)
  have hxy := (mem_actualNeighbors_iff R x y).mp hy
  have hxP : x∈P.vertices := by
    dsimp only [R] at hx
    rw [vertexFiber_vertices] at hx
    exact (Finset.mem_filter.mp hx).1
  have hyP : GeneralVertexStep P x y :=
    facePolytope_step P (maxFace_isFace P (fiberFunctional P (summandProjection A) q)) hxy
  obtain ⟨μ,hμnonneg,hμ⟩ := leftVertexMap_nonnegative P A B hP x hxP y hyP
  have hz : (α-μ)•(y-x)=0 := by
    calc
      (α-μ)•(y-x) =
          (leftVertexMap P A B hP y-leftVertexMap P A B hP x)-μ•(y-x) := by
        rw [hhom y hxy.1,hhom x hx]; module
      _ = 0 := by rw [hμ]; abel
  have hαμ : α=μ := sub_eq_zero.mp
    ((smul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hxy.2.1.symm))
  exact lt_of_le_of_ne (by rwa [hαμ]) (Ne.symm hα)

theorem positive_homothety_image_of_fiber
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim) (q : (quotientPolytope P A).vertices)
    (hh : SummandHomotheticFiber P A B hP q) :
    ∃α:ℝ,∃b:E n,0<α ∧
      homothetyMap α b '' (vertexFiber P (summandProjection A) q).toSet=A.toSet := by
  obtain ⟨α,b,hα,hhom⟩ := hh
  have hpos := positive_scale_on_summand_fiber P A B hP hApos q α b hα hhom
  let R := vertexFiber P (summandProjection A) q
  have himage : homothetyMap α b '' (R.vertices : Set (E n))=(A.vertices : Set (E n)) := by
    rw [← summand_vertexFiber_image P A B hP q]
    apply Set.image_congr
    intro x hx
    exact (hhom x hx).symm
  refine ⟨α,b,hpos,?_⟩
  change homothetyMap α b '' convexHull ℝ (R.vertices : Set (E n))=
    convexHull ℝ (A.vertices : Set (E n))
  rw [AffineMap.image_convexHull,himage]

theorem summand_fiber_is_positive_homothetic_copy
    (P A B : ConvexPolytope n) (hP : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim) (q : (quotientPolytope P A).vertices)
    (hh : SummandHomotheticFiber P A B hP q) :
    ∃lam:ℝ,∃t:E n,0<lam ∧
      (vertexFiber P (summandProjection A) q).toSet=homothetyMap lam t '' A.toSet := by
  obtain ⟨α,b,hα,hbody⟩ := positive_homothety_image_of_fiber P A B hP hApos q hh
  let H := homothetyMap α⁻¹ (-(α⁻¹•b))
  have hinverse (x:E n) : H (homothetyMap α b x)=x := by
    change α⁻¹•(α•x+b)-(α⁻¹•b)=x
    simp only [smul_add,smul_smul,inv_mul_cancel₀ hα.ne',one_smul,add_sub_cancel_right]
  refine ⟨α⁻¹,-(α⁻¹•b),inv_pos.mpr hα,?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨homothetyMap α b x,?_,hinverse x⟩
    rw [← hbody]
    exact ⟨x,hx,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    rw [← hbody] at ha
    obtain ⟨y,hy,rfl⟩ := ha
    change H (homothetyMap α b y)∈(vertexFiber P (summandProjection A) q).toSet
    rwa [hinverse y]

end Papers.MinkowskiPositiveFibers


end
end
end BundlePart7

section BundlePart8
/- Source: Papers/MinkowskiFiberPartition.lean -/




@[expose] public section

/-! Exact finite partition by quotient vertex fibers and the planar equality case. -/
noncomputable section
namespace Papers.MinkowskiFiberPartition

open Set Module
open Papers.Polytopes Papers.MinkowskiSummandFibers
open Papers.MinkowskiQuotientCounting Papers.LinearImageFibers
open Papers.FiniteHullPolytope Papers.FiniteFiberSaturation
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators Pointwise

variable {n : ℕ}

theorem vertexFiber_union_card
    (P : ConvexPolytope n) (π : E n →L[ℝ] E n) :
    (P.vertices.filter fun x => π x∈(imagePolytope P π).vertices).card =
      ∑q:(imagePolytope P π).vertices,(vertexFiber P π q).vertices.card := by
  let I := (imagePolytope P π).vertices
  let fibers : I → Finset (E n) := fun q => (vertexFiber P π q).vertices
  have hdis : ∀a∈(Finset.univ:Finset I),∀b∈Finset.univ,a≠b →
      Disjoint (fibers a) (fibers b) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    dsimp only [fibers] at hxa hxb
    rw [vertexFiber_vertices] at hxa hxb
    exact hab (Subtype.ext ((Finset.mem_filter.mp hxa).2.symm.trans
      (Finset.mem_filter.mp hxb).2))
  have heq : P.vertices.filter (fun x => π x∈(imagePolytope P π).vertices)=
      Finset.univ.biUnion fibers := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      obtain ⟨hx,hπx⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨π x,hπx⟩,Finset.mem_univ _,?_⟩
      dsimp only [fibers]
      rw [vertexFiber_vertices]
      exact Finset.mem_filter.mpr ⟨hx,rfl⟩
    · intro hx
      obtain ⟨q,hq,hxq⟩ := Finset.mem_biUnion.mp hx
      dsimp only [fibers] at hxq
      rw [vertexFiber_vertices] at hxq
      obtain ⟨hx,hπx⟩ := Finset.mem_filter.mp hxq
      exact Finset.mem_filter.mpr ⟨hx,hπx.symm ▸ q.property⟩
  rw [heq,Finset.card_biUnion hdis]

theorem all_vertices_project_to_vertices_of_saturated_fibers
    (P : ConvexPolytope n) (π : E n →L[ℝ] E n)
    (hsum : (∑q:(imagePolytope P π).vertices,
      (vertexFiber P π q).vertices.card)=P.vertices.card) :
    ∀x∈P.vertices,π x∈(imagePolytope P π).vertices := by
  have heq : P.vertices.filter (fun x => π x∈(imagePolytope P π).vertices)=P.vertices := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    rw [vertexFiber_union_card,hsum]
  intro x hx
  have hm : x∈P.vertices.filter (fun x => π x∈(imagePolytope P π).vertices) := by
    rw [heq]
    exact hx
  exact (Finset.mem_filter.mp hm).2

theorem planar_unique_homothetic_fiber_saturation
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hsum : P.toSet=A.toSet+B.toSet)
    (hr : A.dim=2) (hq : 3≤(quotientPolytope P A).dim)
    (hN : P.vertices.card≤4*n-5)
    (q0 : (quotientPolytope P A).vertices)
    (hother : ∀q,q≠q0→¬SummandHomotheticFiber P A B hsum q) :
    (quotientPolytope P A).vertices.card=(quotientPolytope P A).dim+1 ∧
      ∀x∈P.vertices,summandProjection A x∈(quotientPolytope P A).vertices := by
  let Q := quotientPolytope P A
  let π := summandProjection A
  let sizes : Q.vertices → ℕ := fun q => (vertexFiber P π q).vertices.card
  have hdim := quotient_dimension_add_summand_dimension P A hfull
  have hA := dimension_add_one_le_vertices A
  have hzero : 3≤sizes q0 := by
    have h := quotient_vertex_fiber_card P A B hsum q0
    dsimp only [sizes,π]
    omega
  have hothers : ∀q,q≠q0→4≤sizes q := by
    intro q hq0
    have hh := (summand_fiber_homothetic_or_large P A B hsum
      (by omega) (by rw [hfull]; omega) q).resolve_left (hother q hq0)
    dsimp only [sizes,π]
    omega
  obtain ⟨hcard,hqzero,hqother,hsizes⟩ := finite_fiber_saturation q0 sizes Q.dim P.vertices.card
    (by simpa only [Fintype.card_coe] using dimension_add_one_le_vertices Q)
    hzero hothers (total_vertexFiber_card_le P π) (by dsimp only [Q]; omega)
  refine ⟨by simpa only [Fintype.card_coe] using hcard,?_⟩
  exact all_vertices_project_to_vertices_of_saturated_fibers P π hsizes

end Papers.MinkowskiFiberPartition

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/MinkowskiShephardNoExtras.lean -/




@[expose] public section

/-! A simplex quotient with no extra vertices and one homothetic fiber
has an actual Shephard facet opposite that fiber. -/
noncomputable section
namespace Papers.MinkowskiShephardNoExtras

open Set Module
open Papers.Polytopes Papers.ActualPaperCoverReduction
open Papers.PolytopeVertexCone Papers.MinkowskiVertexMap
open Papers.MinkowskiQuotientCounting Papers.MinkowskiSummandFibers
open Papers.MinkowskiFiberDichotomy Papers.SimplexQuotientOppositeFace
open Papers.LinearImageFibers Papers.ParallelSupportEvaluation
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

theorem label_eq_of_distinct_quotient_endpoints
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    {x y : E n} (hx : x∈P.vertices) (hxy : GeneralVertexStep P x y)
    (hne : summandProjection A x≠summandProjection A y) :
    leftVertexMap P A B hsum x=leftVertexMap P A B hsum y := by
  let f := leftVertexMap P A B hsum
  let π := summandProjection A
  have hkill : π (f y-f x)=0 := by
    change f y-f x∈π.ker
    rw [summandProjection_kernel]
    exact vsub_mem_vectorSpan ℝ
      (subset_convexHull ℝ _ (leftVertexMap_spec P A B hsum hxy.1).1)
      (subset_convexHull ℝ _ (leftVertexMap_spec P A B hsum hx).1)
  obtain ⟨μ,hμ⟩ := leftVertexMap_parallel P A B hsum x hx y hxy.1 hxy
  have hp := congrArg π hμ
  change π (f y-f x)=π (μ•(y-x)) at hp
  rw [hkill,map_smul,map_sub] at hp
  have hzero : μ=0 := (smul_eq_zero.mp hp.symm).resolve_right
    (sub_ne_zero.mpr hne.symm)
  rw [hzero,zero_smul] at hμ
  exact (sub_eq_zero.mp hμ).symm

theorem shephardFacet_of_simplex_quotient_no_extras
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hsum : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim)
    (hQcard : (quotientPolytope P A).vertices.card=(quotientPolytope P A).dim+1)
    (hQpos : 0<(quotientPolytope P A).dim)
    (hcover : ∀x∈P.vertices,summandProjection A x∈(quotientPolytope P A).vertices)
    (q : (quotientPolytope P A).vertices)
    (hhom : SummandHomotheticFiber P A B hsum q) :
    ExactShephardFacet P := by
  let π := summandProjection A
  let R := vertexFiber P π q
  let f := leftVertexMap P A B hsum
  obtain ⟨w,hwker,hwout⟩ := opposite_quotient_face P π
    (actual_vertices_affineIndependent_of_minimal_card _ hQcard)
    (by change 2≤(quotientPolytope P A).vertices.card; omega) q hcover
  let F := Papers.MinkowskiFaces.maxFace P.toSet w.toLinearMap
  have hF : P.IsFace F := maxFace_isFace P w
  have hout : P.vertices.filter (fun x => x∉F)=R.vertices := by
    rw [vertexFiber_vertices]
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx,hxF⟩
      exact ⟨hx,(hwout x hx).mp hxF⟩
    · rintro ⟨hx,hπx⟩
      exact ⟨hx,(hwout x hx).mpr hπx⟩
  have hRcard : 2≤R.vertices.card := by
    rw [homothetic_summand_fiber_card P A B hsum q hhom]
    have hdim := dimension_add_one_le_vertices A
    omega
  have hinj := fiber_map_injective_of_homothetic P f π q hhom
  apply exactShephardFacet_of_face_with_one_exit P hfull F hF
  · rwa [hout]
  · intro x hx hxF
    apply Finset.card_le_one.mpr
    intro y hy z hz
    obtain ⟨hyN,hyF⟩ := Finset.mem_filter.mp hy
    obtain ⟨hzN,hzF⟩ := Finset.mem_filter.mp hz
    have hxy := (mem_actualNeighbors_iff P x y).mp hyN
    have hxz := (mem_actualNeighbors_iff P x z).mp hzN
    have hyq := (hwout y hxy.1).mp hyF
    have hzq := (hwout z hxz.1).mp hzF
    have hxq : π x≠q.val := by
      intro hh
      exact (hwout x hx).mpr hh hxF
    have hfy := label_eq_of_distinct_quotient_endpoints P A B hsum hx hxy
      (by rw [hyq]; exact hxq)
    have hfz := label_eq_of_distinct_quotient_endpoints P A B hsum hx hxz
      (by rw [hzq]; exact hxq)
    apply hinj
    · rw [vertexFiber_vertices]
      exact Finset.mem_filter.mpr ⟨hxy.1,hyq⟩
    · rw [vertexFiber_vertices]
      exact Finset.mem_filter.mpr ⟨hxz.1,hzq⟩
    · exact hfy.symm.trans hfz

end Papers.MinkowskiShephardNoExtras

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/MinkowskiCodimensionTwoCounts.lean -/




@[expose] public section

/-! The complete finite budget in codimension two with a nonhomothetic fiber. -/
noncomputable section
namespace Papers.MinkowskiCodimensionTwoCounts

open Set Module
open Papers.Polytopes Papers.MinkowskiSummandFibers
open Papers.MinkowskiQuotientCounting Papers.LinearImageFibers
open Papers.MinkowskiFiberPartition Papers.FiniteFiberSaturation
open Papers.MinkowskiVertexMap Papers.MinkowskiShephardNoExtras
open Papers.PolytopeVertexCone
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators Pointwise

variable {n : ℕ}

def extraVertices (P A : ConvexPolytope n) : Finset (E n) :=
  P.vertices.filter fun x => summandProjection A x∉(quotientPolytope P A).vertices

theorem fiber_extra_partition (P A : ConvexPolytope n) :
    (∑q:(quotientPolytope P A).vertices,
      (vertexFiber P (summandProjection A) q).vertices.card)+
      (extraVertices P A).card=P.vertices.card := by
  rw [← vertexFiber_union_card]
  exact Finset.card_filter_add_card_filter_not _

theorem nonhomothetic_with_extra_saturation
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hsum : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : (quotientPolytope P A).dim=2)
    (hN : P.vertices.card≤4*n-5)
    (q0 : (quotientPolytope P A).vertices)
    (hbad : ¬SummandHomotheticFiber P A B hsum q0)
    (hextra : (extraVertices P A).Nonempty) :
    A.vertices.card=A.dim+1 ∧ (extraVertices P A).card=1 ∧
      (vertexFiber P (summandProjection A) q0).vertices.card=2*A.dim ∧
      (∀q,q≠q0→(vertexFiber P (summandProjection A) q).vertices.card=A.dim+1) ∧
      P.vertices.card=4*A.dim+3 := by
  have hdim := quotient_dimension_add_summand_dimension P A hfull
  have hcard := quotient_has_three_vertices_of_codimension_two P A B hfull hsum hr hq hN
  have hlarge := (summand_fiber_homothetic_or_large P A B hsum
    (by omega) (by rw [hfull]; omega) q0).resolve_left hbad
  exact three_fiber_saturation (by simpa only [Fintype.card_coe] using hcard) q0
    (fun q => (vertexFiber P (summandProjection A) q).vertices.card)
    A.vertices.card A.dim (extraVertices P A).card P.vertices.card hr
    (dimension_add_one_le_vertices A) (quotient_vertex_fiber_card P A B hsum)
    hlarge (Finset.card_pos.mpr hextra) (fiber_extra_partition P A) (by omega)

theorem fiber_label_count_add_labels_le
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    (q : (quotientPolytope P A).vertices) (a : E n) (ha : a∈A.vertices) :
    ((vertexFiber P (summandProjection A) q).vertices.filter
      fun x => leftVertexMap P A B hsum x=a).card+A.vertices.card ≤
      (vertexFiber P (summandProjection A) q).vertices.card+1 := by
  let R := vertexFiber P (summandProjection A) q
  let f := leftVertexMap P A B hsum
  let S := R.vertices.filter fun x => f x≠a
  have himage : A.vertices.erase a⊆S.image f := by
    intro b hb
    obtain ⟨hba,hbA⟩ := Finset.mem_erase.mp hb
    have hbimage : b∈f '' (R.vertices : Set (E n)) := by
      rw [summand_vertexFiber_image]
      exact hbA
    obtain ⟨x,hx,hfx⟩ := hbimage
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,by rwa [hfx]⟩,hfx⟩
  have hcount := (Finset.card_le_card himage).trans (Finset.card_image_le)
  have hAcard := Finset.card_erase_add_one ha
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := R.vertices) (fun x => f x=a)
  change (R.vertices.filter fun x => f x=a).card+A.vertices.card≤R.vertices.card+1
  change (R.vertices.filter fun x => f x=a).card+S.card=R.vertices.card at hpartition
  omega

theorem label_preserved_at_unique_extra
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    {x : E n} (hextra : extraVertices P A={x})
    {y : E n} (hxy : GeneralVertexStep P x y) :
    leftVertexMap P A B hsum x=leftVertexMap P A B hsum y := by
  have hxextra : x∈extraVertices P A := by rw [hextra]; simp
  have hx := (Finset.mem_filter.mp hxextra).1
  have hxq := (Finset.mem_filter.mp hxextra).2
  have hyq : summandProjection A y∈(quotientPolytope P A).vertices := by
    by_contra hn
    have hyextra : y∈extraVertices P A := Finset.mem_filter.mpr ⟨hxy.1,hn⟩
    rw [hextra] at hyextra
    exact hxy.2.1 (Finset.mem_singleton.mp hyextra).symm
  apply label_eq_of_distinct_quotient_endpoints P A B hsum hx hxy
  intro heq
  exact hxq (heq.symm ▸ hyq)

end Papers.MinkowskiCodimensionTwoCounts

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/MinkowskiUniqueExtraSimple.lean -/





@[expose] public section

/-! In the nonhomothetic codimension-two equality case, the unique extra
vertex is genuinely simple. -/
noncomputable section
namespace Papers.MinkowskiUniqueExtraSimple

open Set Module
open Papers.Polytopes Papers.PolytopeVertexCone
open Papers.MinkowskiCodimensionTwoCounts Papers.MinkowskiSummandFibers
open Papers.MinkowskiQuotientCounting Papers.MinkowskiFiberDichotomy
open Papers.MinkowskiVertexMap Papers.LinearImageFibers
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators Pointwise

variable {n : ℕ}

theorem unique_extra_neighbor_card
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hsum : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : (quotientPolytope P A).dim=2)
    (hN : P.vertices.card≤4*n-5)
    (q0 : (quotientPolytope P A).vertices)
    (hbad : ¬SummandHomotheticFiber P A B hsum q0)
    {x : E n} (hextra : extraVertices P A={x}) :
    (actualNeighbors P x).card=n := by
  have hextrane : (extraVertices P A).Nonempty := by rw [hextra]; simp
  obtain ⟨hAcard,hecard,hqzero,hqothers,hcount⟩ :=
    nonhomothetic_with_extra_saturation P A B hfull hsum hr hq hN q0 hbad hextrane
  let Q := quotientPolytope P A
  let π := summandProjection A
  let f := leftVertexMap P A B hsum
  let N := actualNeighbors P x
  have hxextra : x∈extraVertices P A := by rw [hextra]; simp
  have hx : x∈P.vertices := (Finset.mem_filter.mp hxextra).1
  have hax : f x∈A.vertices := (leftVertexMap_spec P A B hsum hx).1
  let labelFiber : Q.vertices → Finset (E n) := fun q =>
    (vertexFiber P π q).vertices.filter fun y => f y=f x
  have hbound0 : (labelFiber q0).card≤A.dim := by
    have hh := fiber_label_count_add_labels_le P A B hsum q0 (f x) hax
    rw [hAcard,hqzero] at hh
    change (labelFiber q0).card+(A.dim+1)≤2*A.dim+1 at hh
    omega
  have hboundOther : ∀q:Q.vertices,q≠q0→(labelFiber q).card≤1 := by
    intro q hqq
    have hhom : SummandHomotheticFiber P A B hsum q := by
      rcases summand_fiber_homothetic_or_large P A B hsum (by omega)
          (by rw [hfull]; have hd := quotient_dimension_add_summand_dimension P A hfull; omega) q with hh | hh
      · exact hh
      · rw [hqothers q hqq] at hh
        omega
    have hinj := fiber_map_injective_of_homothetic P f π q hhom
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨hu,huval⟩ := Finset.mem_filter.mp hu
    obtain ⟨hv,hvval⟩ := Finset.mem_filter.mp hv
    exact hinj hu hv (huval.trans hvval.symm)
  have hcover : N⊆Finset.univ.biUnion labelFiber := by
    intro y hy
    have hxy := (mem_actualNeighbors_iff P x y).mp hy
    have hyQ : π y∈Q.vertices := by
      by_contra hyextra
      have hmem : y∈extraVertices P A := Finset.mem_filter.mpr ⟨hxy.1,hyextra⟩
      rw [hextra] at hmem
      exact hxy.2.1 (Finset.mem_singleton.mp hmem).symm
    refine Finset.mem_biUnion.mpr ⟨⟨π y,hyQ⟩,Finset.mem_univ _,?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,(label_preserved_at_unique_extra P A B hsum hextra hxy).symm⟩
    rw [vertexFiber_vertices]
    exact Finset.mem_filter.mpr ⟨hxy.1,rfl⟩
  have hneighborCount : N.card≤∑q:Q.vertices,(labelFiber q).card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  let S : Finset Q.vertices := Finset.univ.erase q0
  have hS : S.card=2 := by
    have hc := quotient_has_three_vertices_of_codimension_two P A B hfull hsum hr hq hN
    have he := Finset.card_erase_add_one (Finset.mem_univ q0)
    simp only [Finset.card_univ,Fintype.card_coe] at he
    change S.card+1=Q.vertices.card at he
    change Q.vertices.card=3 at hc
    omega
  have hotherSum : (∑q∈S,(labelFiber q).card)≤2 := by
    calc
      _ ≤ ∑_q∈S,(1:ℕ) := Finset.sum_le_sum fun q hq =>
        hboundOther q (Finset.mem_erase.mp hq).1
      _ = 2 := by simp [hS]
  have hsplit := Finset.sum_erase_add Finset.univ (fun q => (labelFiber q).card)
    (Finset.mem_univ q0)
  change (∑q∈S,(labelFiber q).card)+(labelFiber q0).card=
    ∑q:Q.vertices,(labelFiber q).card at hsplit
  have hdim := quotient_dimension_add_summand_dimension P A hfull
  rw [hq] at hdim
  have hlow := actual_neighbor_card_ge_dim P hx
  change P.dim≤N.card at hlow
  change P.dim=n at hfull
  change N.card=n
  omega

end Papers.MinkowskiUniqueExtraSimple

end
end
end BundlePart11
