module

public import PaperVerification.ToricBundleFanEndpoints


@[expose] public section
/-!
# Endpoint base polytopes are actual saturated faces

Every homogeneous slice is identified with its actual ambient fiber-slack
slice. At an endpoint, it is the face cut out by all other positive rays.
Together with the integral affine chart this proves the exact, saturated
lattice interpretation needed when passing edge lengths to the base.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem point_congr_on_positive (a α β : Lattice n → ℝ)
    (hαβ : ∀ v ∈ R.positive, α v = β v)
    (y : Ambient (n - c.fiberIndices.card)) : c.point a α y = c.point a β y := by
  have hf : c.fiberFunctional a α = c.fiberFunctional a β := by
    unfold fiberFunctional
    apply Finset.sum_congr rfl
    intro i hi
    rw [hαβ _ (c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩))]
  simp only [point, pointFunctional, hf]

def homogeneousSlice (a α : Lattice n → ℝ) : Set (Ambient n) :=
  {x ∈ «Σ».fanPolytope a | ∀ v ∈ R.positive, c.homogeneousWeight a x v = α v}

theorem point_image_basePolytope (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (hα0 : ∀ v ∈ R.positive, 0 ≤ α v) :
    (c.point a α) '' c.baseFan.fanPolytope (c.baseWeight hR hN a α) =
      c.homogeneousSlice a α := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(c.point_mem_fanPolytope_iff hR hN a α hα y).mpr ⟨hα0, hy⟩, ?_⟩
    intro v hv
    rw [homogeneousWeight, c.point_pairing_positive hN a α hα y hv]
    ring
  · rintro ⟨hx, hweights⟩
    have he : c.point a α (c.basePoint x) = x := by
      rw [c.point_congr_on_positive a α (c.homogeneousWeight a x)
        (fun v hv => (hweights v hv).symm), c.point_homogeneousWeight_basePoint]
    refine ⟨c.basePoint x, ?_, he⟩
    apply ((c.point_mem_fanPolytope_iff hR hN a α hα (c.basePoint x)).mp ?_).2
    rw [he]
    exact hx

/-- The endpoint face is given by the literal supporting equalities on all
positive rays other than its vertex label. -/
def endpointFace (c : R.BundleCoordinates) (a : Lattice n → ℝ) (u : Lattice n) : Set (Ambient n) :=
  {x ∈ «Σ».fanPolytope a | ∀ v ∈ R.positive.erase u,
    (dotProductEquiv ℝ (Fin n) (embed n v)) x = -a v}

theorem endpointSlice_eq_face (hN : R.negative = ∅)
    (a : Lattice n → ℝ) {u : Lattice n} (hu : u ∈ R.positive) :
    c.homogeneousSlice a (c.endpointWeight a u) = c.endpointFace a u := by
  ext x
  constructor
  · rintro ⟨hx, hw⟩
    refine ⟨hx, ?_⟩
    intro v hv
    have he := hw v (Finset.mem_of_mem_erase hv)
    simp only [homogeneousWeight, endpointWeight, if_neg (Finset.mem_erase.mp hv).1] at he
    linarith
  · rintro ⟨hx, hface⟩
    refine ⟨hx, ?_⟩
    apply c.weights_eq_endpoint hu (c.homogeneousWeight_total hN a x)
    intro v hv
    rw [homogeneousWeight, hface v hv, add_neg_cancel]

theorem endpointFace_isExtreme (a : Lattice n → ℝ) (u : Lattice n) :
    IsExtreme ℝ («Σ».fanPolytope a) (c.endpointFace a u) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨r, s, hr, hs, hrs, he⟩ := hseg
  refine ⟨hx, ?_⟩
  intro v hv
  have hvrays := R.primitive.1 (Finset.mem_of_mem_erase hv)
  have hxv := hx v hvrays
  have hyv := hy v hvrays
  have hzv := hz.2 v hv
  have hlin := congrArg (dotProductEquiv ℝ (Fin n) (embed n v) : Ambient n → ℝ) he
  simp only [map_add, map_smul, smul_eq_mul] at hlin
  have hy_slack : 0 ≤ (dotProductEquiv ℝ (Fin n) (embed n v)) y + a v := by
    linarith only [hyv]
  have hx_slack : 0 ≤ (dotProductEquiv ℝ (Fin n) (embed n v)) x + a v := by
    linarith only [hxv]
  have hnon := mul_nonneg hs.le hy_slack
  have hxnon := mul_nonneg hr.le hx_slack
  have hbalance :
      r * ((dotProductEquiv ℝ (Fin n) (embed n v)) x + a v) +
        s * ((dotProductEquiv ℝ (Fin n) (embed n v)) y + a v) = 0 := by
    calc
      r * ((dotProductEquiv ℝ (Fin n) (embed n v)) x + a v) +
          s * ((dotProductEquiv ℝ (Fin n) (embed n v)) y + a v) =
          (r * (dotProductEquiv ℝ (Fin n) (embed n v)) x +
            s * (dotProductEquiv ℝ (Fin n) (embed n v)) y) + (r + s) * a v := by ring
      _ = (dotProductEquiv ℝ (Fin n) (embed n v)) z + a v := by
        rw [hlin, hrs, one_mul]
      _ = 0 := by rw [hzv, neg_add_cancel]
  have hzero : r * ((dotProductEquiv ℝ (Fin n) (embed n v)) x + a v) = 0 := by
    linarith only [hxnon, hnon, hbalance]
  have hvzero := (mul_eq_zero.mp hzero).resolve_left hr.ne'
  linarith

theorem endpoint_image_is_face (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a : Lattice n → ℝ)
    (hk : 0 ≤ ∑ v ∈ R.positive, a v) {u : Lattice n} (hu : u ∈ R.positive) :
    (c.point a (c.endpointWeight a u)) ''
      c.baseFan.fanPolytope (c.baseWeight hR hN a (c.endpointWeight a u)) =
        c.endpointFace a u := by
  rw [c.point_image_basePolytope hR hN a (c.endpointWeight a u)
    (c.endpointWeight_total a hu) (fun v hv => c.endpointWeight_nonneg a hk u v),
    c.endpointSlice_eq_face hN a hu]

def endpointIntegerWeight (c : R.BundleCoordinates) (a : Lattice n → ℤ) (u v : Lattice n) : ℤ :=
  if v = u then ∑ w ∈ R.positive, a w else 0

theorem endpointIntegerWeight_cast (a : Lattice n → ℤ) (u v : Lattice n) :
    (c.endpointIntegerWeight a u v : ℝ) = c.endpointWeight (fun w => (a w : ℝ)) u v := by
  simp only [endpointIntegerWeight, endpointWeight]
  split_ifs <;> push_cast <;> rfl

/-- The endpoint base polytope has exactly the saturated affine lattice
of the corresponding original face. -/
theorem endpointChart_image (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a : Lattice n → ℤ)
    (hk : 0 ≤ ∑ v ∈ R.positive, a v) {u : Lattice n} (hu : u ∈ R.positive) :
    (c.fiberChart a (c.endpointIntegerWeight a u)).realMap ''
      c.baseFan.fanPolytope (c.baseWeight hR hN (fun v => (a v : ℝ))
        (c.endpointWeight (fun v => (a v : ℝ)) u)) =
      c.endpointFace (fun v => (a v : ℝ)) u := by
  have hmap : (c.fiberChart a (c.endpointIntegerWeight a u)).realMap =
      c.point (fun v => (a v : ℝ)) (c.endpointWeight (fun v => (a v : ℝ)) u) := by
    funext y
    rw [c.fiberChart_realMap]
    congr 1
    funext v
    exact c.endpointIntegerWeight_cast a u v
  rw [hmap]
  apply c.endpoint_image_is_face hR hN _ _ hu
  exact_mod_cast hk

theorem endpointChart_isExtreme (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a : Lattice n → ℤ)
    (hk : 0 ≤ ∑ v ∈ R.positive, a v) {u : Lattice n} (hu : u ∈ R.positive) :
    IsExtreme ℝ («Σ».fanPolytope (fun v => (a v : ℝ)))
      ((c.fiberChart a (c.endpointIntegerWeight a u)).realMap ''
        c.baseFan.fanPolytope (c.baseWeight hR hN (fun v => (a v : ℝ))
          (c.endpointWeight (fun v => (a v : ℝ)) u))) := by
  rw [c.endpointChart_image hR hN a hk hu]
  exact c.endpointFace_isExtreme _ _

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
