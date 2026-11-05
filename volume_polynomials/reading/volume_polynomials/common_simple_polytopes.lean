module

public import VolumePolynomials.SimpleMinkowskiRefinement
public import VolumePolynomials.BodyTopology

@[expose] public section
set_option autoImplicit false

/-!
# Constructing a common simple refinement

The data below are constructed from the finite convex hulls in the tuple.
Their generic reference body is a small perturbation of the support heights
of the total sum. Adding a positive multiple of this body to every summand
gives actual simple polytopes with identical feasible normal bases.
-/

noncomputable section
open Set Filter Module Metric
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {κ : Type*} [Fintype κ]

structure CommonRefinement (K : κ → ConvexBody E) where
  facets : PolytopeGeometry.FixedFacets (fun k => (K k : Set E))
  reference : ConvexBody E
  reference_finite : PolytopeGeometry.IsFiniteHull (reference : Set E)
  height : Fin facets.count → ℝ
  height_pos : ∀ i, 0 < height i
  generic : Generic facets.normal height
  strict_facets : StrictFacets facets.normal height
  reference_eq : (reference : Set E) = body facets.normal height
  refines : feasibleBases facets.normal height ⊆
    feasibleBases facets.normal (fun i => ∑ k, BodySupport.support (K k) (facets.normal i))

namespace CommonRefinement

variable {K : κ → ConvexBody E} (D : CommonRefinement K)

theorem reference_strict_inactive : ∀ b ∈ feasibleBases D.facets.normal D.height,
    ∀ i ∉ b.val, D.facets.normal i (vertexMap D.facets.normal b D.height) < D.height i :=
  strict_inactive_of_generic D.facets.normal D.height D.generic

def summandHeight (k : κ) (i : Fin D.facets.count) : ℝ :=
  BodySupport.support (K k) (D.facets.normal i)

theorem total_body_eq : (↑(∑ k, K k) : Set E) =
    body D.facets.normal (fun i => ∑ k, D.summandHeight k i) := by
  first
  | have he := D.facets.body_eq (fun _ => (1 : ℝ)) (fun _ => zero_lt_one)
    simpa only [one_smul, one_mul, ← coe_sum_body,
      summandHeight, BodySupport.support, OAI.Paper092.SupportGeometry.support, body] using he

theorem summand_vertex (k : κ) (b : BasisIndex D.facets.normal)
    (hb : b ∈ feasibleBases D.facets.normal D.height) :
    vertexMap D.facets.normal b (D.summandHeight k) ∈ K k :=
  summand_vertex_mem K D.facets.normal D.total_body_eq b (D.refines hb) k

def approximant (r : ℝ) (k : κ) : ConvexBody E := K k + r • D.reference

def approximantHeight (r : ℝ) (k : κ) : Fin D.facets.count → ℝ :=
  D.summandHeight k + r • D.height

theorem approximant_eq_halfspaces {r : ℝ} (hr : 0 < r) (k : κ) :
    (D.approximant r k : Set E) = body D.facets.normal (D.approximantHeight r k) :=
  minkowski_eq_halfspaces_of_refinement D.facets.normal D.height D.reference_strict_inactive
    D.reference (K k) D.reference_eq (D.summandHeight k)
    (fun x hx i => BodySupport.le_support (K k) (D.facets.normal i) hx)
    (D.summand_vertex k) hr

theorem approximant_feasibleBases {r : ℝ} (hr : 0 < r) (k : κ) :
    feasibleBases D.facets.normal (D.approximantHeight r k) =
      feasibleBases D.facets.normal D.height :=
  feasibleBases_minkowski_refinement D.facets.normal D.height D.reference_strict_inactive
    D.reference (K k) D.reference_eq (D.summandHeight k)
    (fun x hx i => BodySupport.le_support (K k) (D.facets.normal i) hx)
    (D.summand_vertex k) hr

theorem approximant_strict_inactive {r : ℝ} (hr : 0 < r) (k : κ)
    (b : BasisIndex D.facets.normal) (hb : b ∈ feasibleBases D.facets.normal D.height)
    (i : Fin D.facets.count) (hi : i ∉ b.val) :
    D.facets.normal i (vertexMap D.facets.normal b (D.approximantHeight r k)) <
      D.approximantHeight r k i :=
  refinement_vertex_strict_inactive D.facets.normal D.height D.reference_strict_inactive (K k)
    (D.summandHeight k)
    (fun x hx i => BodySupport.le_support (K k) (D.facets.normal i) hx)
    (D.summand_vertex k) hr b hb i hi

theorem approximant_is_simple {r : ℝ} (hr : 0 < r) (k : κ)
    {x : E} (hx : x ∈ (D.approximant r k : Set E).extremePoints ℝ) :
    Function.Bijective
      (evaluation D.facets.normal (active D.facets.normal (D.approximantHeight r k) x)) := by
  first
  | rw [D.approximant_eq_halfspaces hr k] at hx
    obtain ⟨b, rfl⟩ := extreme_eq_vertexMap_without_generic D.facets.normal _ hx
    have hb : b ∈ feasibleBases D.facets.normal D.height := by
      rw [← D.approximant_feasibleBases hr k]
      exact hx.1
    rw [active_eq_basis_of_strict D.facets.normal _ b (D.approximant_strict_inactive hr k b hb)]
    exact b.property

theorem approximant_strictFacets {r : ℝ} (hr : 0 < r) (k : κ) :
    StrictFacets D.facets.normal (D.approximantHeight r k) := by
  first
  | intro i
    obtain ⟨p, hpi, hpj⟩ := D.strict_facets i
    obtain ⟨q, hq, hqi⟩ := BodySupport.exists_support (K k) (D.facets.normal i)
    refine ⟨q + r • p, ?_, fun j hji => ?_⟩
    · simp only [approximantHeight, summandHeight, Pi.add_apply, Pi.smul_apply,
        map_add, map_smul, smul_eq_mul, hqi, hpi]
    · have hqj := BodySupport.le_support (K k) (D.facets.normal j) hq
      have hp := mul_lt_mul_of_pos_left (hpj j hji) hr
      simpa only [approximantHeight, summandHeight, Pi.add_apply, Pi.smul_apply,
        map_add, map_smul, smul_eq_mul] using add_lt_add_of_le_of_lt hqj hp

theorem approximantHeight_pos (h0 : ∀ k, (0 : E) ∈ K k)
    {r : ℝ} (hr : 0 < r) (k : κ) (i : Fin D.facets.count) :
    0 < D.approximantHeight r k i := by
  first
  | have hg : 0 ≤ D.summandHeight k i := by
      simpa only [summandHeight, map_zero] using
        BodySupport.le_support (K k) (D.facets.normal i) (h0 k)
    exact add_pos_of_nonneg_of_pos hg (mul_pos hr (D.height_pos i))

theorem approximant_zero_mem_interior (h0 : ∀ k, (0 : E) ∈ K k)
    {r : ℝ} (hr : 0 < r) (k : κ) :
    (0 : E) ∈ interior (D.approximant r k : Set E) := by
  first
  | rw [D.approximant_eq_halfspaces hr k]
    exact zero_mem_interior_body D.facets.normal _ (D.approximantHeight_pos h0 hr k)

theorem approximant_isFiniteHull
    (hK : ∀ k, PolytopeGeometry.IsFiniteHull (K k : Set E)) (r : ℝ) (k : κ) :
    PolytopeGeometry.IsFiniteHull (D.approximant r k : Set E) :=
  (hK k).add (D.reference_finite.smul r)

theorem continuous_approximant : Continuous (fun r : ℝ => D.approximant r) := by
  first
  | unfold approximant
    fun_prop

theorem tendsto_approximant_zero : Tendsto (fun r : ℝ => D.approximant r) (𝓝 0) (𝓝 K) := by
  first
  | have hzero : D.approximant 0 = K := by
      funext k
      change K k + (0 : ℝ) • D.reference = K k
      rw [body_zero_smul, add_zero]
    have h := D.continuous_approximant.tendsto 0
    rw [hzero] at h
    exact h

end CommonRefinement

/-- The common simple refinement is constructed for every finite-hull tuple
whose centered sum has interior. Individual summands may be lower dimensional. -/
theorem exists_commonRefinement (K : κ → ConvexBody E)
    (hK : ∀ k, PolytopeGeometry.IsFiniteHull (K k : Set E))
    (h0 : ∀ k, (0 : E) ∈ K k)
    (hint : (0 : E) ∈ interior (↑(∑ k, K k) : Set E)) :
    Nonempty (CommonRefinement K) := by
  first
  | have hintSet : (0 : E) ∈ interior (∑ k, (K k : Set E)) := by
      simpa only [coe_sum_body] using hint
    obtain ⟨D⟩ := PolytopeGeometry.exists_fixedFacets (fun k => (K k : Set E))
      hK (fun k => (K k).nonempty) ⟨0, hintSet⟩
    let hbase : Fin D.count → ℝ := fun i => ∑ k, BodySupport.support (K k) (D.normal i)
    have hbody : (↑(∑ k, K k) : Set E) = body D.normal hbase := by
      have he := D.body_eq (fun _ => (1 : ℝ)) (fun _ => zero_lt_one)
      simpa only [one_smul, one_mul, ← coe_sum_body, hbase,
        BodySupport.support, OAI.Paper092.SupportGeometry.support, body] using he
    have hbasepos : ∀ i, 0 < hbase i := by
      intro i
      have hp := D.height_one_pos (fun k => (K k).isCompact) h0
        (by simpa only [coe_sum_body] using hint) i
      simpa only [hbase, PolytopeGeometry.FixedFacets.heightCoefficient,
        BodySupport.support, OAI.Paper092.SupportGeometry.support] using hp
    have hbasecompact : IsCompact (body D.normal hbase) := hbody ▸ (∑ k, K k).isCompact
    have hstrict : StrictFacets D.normal hbase := by
      simpa only [StrictFacets, hbase, BodySupport.support,
        OAI.Paper092.SupportGeometry.support] using D.strict_face_point
    obtain ⟨h, hg, hpos, href, hsf⟩ := exists_generic_refinement_strictFacets
      D.normal hbase D.normal_ne_zero hbasepos hstrict
    exact ⟨{
      facets := D
      reference := toBody D.normal hbase hbasepos hbasecompact h hpos
      reference_finite := toBody_isFiniteHull D.normal hbase hbasepos hbasecompact h hpos
      height := h
      height_pos := hpos
      generic := hg
      strict_facets := hsf
      reference_eq := rfl
      refines := href
    }⟩

end VolumePolynomials.PolyhedralSupport
