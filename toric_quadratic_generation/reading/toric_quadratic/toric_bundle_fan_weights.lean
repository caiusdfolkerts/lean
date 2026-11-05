module

public import PaperVerification.ToricBundleFan
public import PaperVerification.ToricFanPolytopes


@[expose] public section
/-!
# Actual homogeneous fiber weights and base inequalities

For a zero-focus relation the homogeneous coordinates are the actual slacks
`a(v) + ⟨v,x⟩` on its positive rays.  Their sum is the fiber degree.  The
remaining inequalities are those of the genuine base fan with coefficients
`C_α = C_base + Σ α_i E_i`.  The formulas below hold for arbitrary real
support coefficients and weights; no positivity or convexity is hidden in
the definitions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem dotProductEquiv_dualVector {n : ℕ}
    (f : Ambient n →ₗ[ℝ] ℝ) (z : Ambient n) :
    (dotProductEquiv ℝ (Fin n) z) (dualVector f) = f z := by
  change (∑ i, z i * dualVector f i) = f z
  have h := dualVector_pairing f (0 : Ambient n) z
  simpa only [Pi.zero_apply, sub_zero, mul_comm] using h

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

/-- The fiber part of the dual functional at homogeneous weight `α`. -/
def fiberFunctional (a α : Lattice n → ℝ) : Ambient n →ₗ[ℝ] ℝ :=
  ∑ i ∈ c.fiberIndices,
    (α (c.basis i) - a (c.basis i)) • (integralBasisReal c.basis).coord i

def pointFunctional (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) : Ambient n →ₗ[ℝ] ℝ :=
  c.fiberFunctional a α +
    (dotProductEquiv ℝ (Fin (n - c.fiberIndices.card)) y).comp c.quotientReal

/-- The actual ambient real point determined by fiber and base coordinates. -/
def point (a α : Lattice n → ℝ) (y : Ambient (n - c.fiberIndices.card)) : Ambient n :=
  dualVector (c.pointFunctional a α y)

theorem point_pairing (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) (z : Ambient n) :
    (dotProductEquiv ℝ (Fin n) z) (c.point a α y) =
      (∑ i ∈ c.fiberIndices,
        (α (c.basis i) - a (c.basis i)) * (integralBasisReal c.basis).repr z i) +
        (dotProductEquiv ℝ (Fin (n - c.fiberIndices.card)) (c.quotientReal z)) y := by
  rw [point, dotProductEquiv_dualVector]
  simp only [pointFunctional, fiberFunctional, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    smul_eq_mul, LinearMap.comp_apply]
  congr 1
  change (∑ j, y j * c.quotientReal z j) = ∑ j, c.quotientReal z j * y j
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem point_pairing_lattice (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) (v : Lattice n) :
    (dotProductEquiv ℝ (Fin n) (embed n v)) (c.point a α y) =
      (∑ i ∈ c.fiberIndices,
        (c.basis.repr v i : ℝ) * (α (c.basis i) - a (c.basis i))) +
        (dotProductEquiv ℝ (Fin (n - c.fiberIndices.card))
          (embed (n - c.fiberIndices.card) (c.quotientLattice v))) y := by
  rw [c.point_pairing, coneQuotient_compatible]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [integralBasisReal_repr, mul_comm]

/-- Total homogeneous weight expressed in the independent fiber coordinates. -/
theorem weight_total_iff (a α : Lattice n → ℝ) :
    (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v ↔
      α c.omitted - a c.omitted =
        -(∑ i ∈ c.fiberIndices, (α (c.basis i) - a (c.basis i))) := by
  have hs (f : Lattice n → ℝ) : (∑ v ∈ R.positive, f v) =
      (∑ i ∈ c.fiberIndices, f (c.basis i)) + f c.omitted := by
    rw [← Finset.sum_erase_add R.positive f c.omitted_mem, ← c.fiber_ray_set,
      Finset.sum_image]
    exact fun i _ j _ hij => c.basis.injective hij
  rw [hs α, hs a, Finset.sum_sub_distrib]
  constructor <;> intro h <;> linarith

theorem point_pairing_positive (hN : R.negative = ∅)
    (a α : Lattice n → ℝ)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (y : Ambient (n - c.fiberIndices.card)) {v : Lattice n} (hv : v ∈ R.positive) :
    (dotProductEquiv ℝ (Fin n) (embed n v)) (c.point a α y) = α v - a v := by
  rw [c.point_pairing_lattice, c.quotient_positive hN hv, map_zero,
    map_zero, LinearMap.zero_apply, add_zero]
  by_cases hvu : v = c.omitted
  · subst v
    rw [(c.weight_total_iff a α).mp hα]
    simp only [c.omitted_coordinate hN]
    simp [Finset.sum_neg_distrib]
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp
      (c.fiber_ray_set.symm ▸ Finset.mem_erase.mpr ⟨hvu, hv⟩)
    simp [Module.Basis.repr_self_apply, Finsupp.single_apply, hi]

/-- The literal base coefficient at homogeneous fiber weight `α`. -/
def baseWeight (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a α : Lattice n → ℝ) (q : Lattice (n - c.fiberIndices.card)) : ℝ :=
  a (c.baseRayLift hR hN q) + ∑ i ∈ c.fiberIndices,
    (c.basis.repr (c.baseRayLift hR hN q) i : ℝ) *
      (α (c.basis i) - a (c.basis i))

/-- The integer piecewise-linear twisting coefficient attached to a fiber
ray. The omitted ray has coefficient zero in the chosen splitting. -/
def twistCoefficient (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (v : Lattice n) (q : Lattice (n - c.fiberIndices.card)) : ℤ :=
  ∑ i ∈ c.fiberIndices, if c.basis i = v then
    c.basis.repr (c.baseRayLift hR hN q) i else 0

theorem twistCoefficient_omitted (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (q : Lattice (n - c.fiberIndices.card)) :
    c.twistCoefficient hR hN c.omitted q = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hne : c.basis i ≠ c.omitted := by
    intro he
    have hm := c.fiber_ray_set ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩
    exact (Finset.mem_erase.mp hm).1 he
  simp only [if_neg hne]

theorem baseWeight_affine (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a α : Lattice n → ℝ) (q : Lattice (n - c.fiberIndices.card)) :
    c.baseWeight hR hN a α q = c.baseWeight hR hN a 0 q +
      ∑ i ∈ c.fiberIndices, (c.basis.repr (c.baseRayLift hR hN q) i : ℝ) * α (c.basis i) := by
  unfold baseWeight
  simp only [Pi.zero_apply, zero_sub, mul_sub, mul_neg, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  ring

theorem nonfiber_slack_identity (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) {v : Lattice n}
    (hv : v ∈ «Σ».rays \ R.positive) :
    a v + (dotProductEquiv ℝ (Fin n) (embed n v)) (c.point a α y) =
      c.baseWeight hR hN a α (c.quotientLattice v) +
        (dotProductEquiv ℝ (Fin (n - c.fiberIndices.card))
          (embed (n - c.fiberIndices.card) (c.quotientLattice v))) y := by
  rw [c.point_pairing_lattice]
  unfold baseWeight
  rw [c.baseRayLift_quotient hR hN hv]
  ring

/-- The homogeneous-coordinate description is exactly equivalent to the
original ambient polytope inequalities. -/
theorem point_mem_fanPolytope_iff (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (y : Ambient (n - c.fiberIndices.card)) :
    c.point a α y ∈ «Σ».fanPolytope a ↔
      (∀ v ∈ R.positive, 0 ≤ α v) ∧
        y ∈ c.baseFan.fanPolytope (c.baseWeight hR hN a α) := by
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro v hv
      have h := hx v (R.primitive.1 hv)
      rw [c.point_pairing_positive hN a α hα y hv] at h
      linarith
    · intro q hq
      have hv := c.baseRayLift_mem hR hN hq
      have h := hx (c.baseRayLift hR hN q) (Finset.mem_sdiff.mp hv).1
      have he := c.nonfiber_slack_identity hR hN a α y hv
      rw [c.quotient_baseRayLift hR hN hq] at he
      linarith
  · rintro ⟨hα0, hy⟩ v hv
    by_cases hvP : v ∈ R.positive
    · rw [c.point_pairing_positive hN a α hα y hvP]
      linarith [hα0 v hvP]
    · have hv' := Finset.mem_sdiff.mpr ⟨hv, hvP⟩
      have hq := (c.base_ray_iff hR hN _).mpr ⟨v, hv', rfl⟩
      have h := hy (c.quotientLattice v) hq
      have he := c.nonfiber_slack_identity hR hN a α y hv'
      linarith

/-- Actual homogeneous weights of an ambient point. -/
def homogeneousWeight (c : R.BundleCoordinates) (a : Lattice n → ℝ) (x : Ambient n) (v : Lattice n) : ℝ :=
  a v + (dotProductEquiv ℝ (Fin n) (embed n v)) x

theorem homogeneousWeight_total (hN : R.negative = ∅)
    (a : Lattice n → ℝ) (x : Ambient n) :
    (∑ v ∈ R.positive, c.homogeneousWeight a x v) = ∑ v ∈ R.positive, a v := by
  have hsum : (∑ v ∈ R.positive, embed n v) = 0 := by
    rw [← map_sum, R.equation, hN, Finset.sum_empty, map_zero]
  simp only [homogeneousWeight, Finset.sum_add_distrib]
  have hz : (∑ v ∈ R.positive, (dotProductEquiv ℝ (Fin n) (embed n v)) x) = 0 := by
    have h := congrArg (fun z : Ambient n => (dotProductEquiv ℝ (Fin n) z) x) hsum
    simpa only [map_sum, LinearMap.sum_apply, map_zero, LinearMap.zero_apply] using h
  rw [hz, add_zero]

/-- The actual base coordinates are obtained by pairing with the integral
section of the quotient. -/
def basePoint (x : Ambient n) : Ambient (n - c.fiberIndices.card) :=
  dualVector ((dotProductEquiv ℝ (Fin n) x).comp
    (coneQuotientSectionReal c.basis c.fiberIndices))

theorem point_homogeneousWeight_basePoint (a : Lattice n → ℝ) (x : Ambient n) :
    c.point a (c.homogeneousWeight a x) (c.basePoint x) = x := by
  apply (dotProductEquiv ℝ (Fin n)).injective
  apply LinearMap.ext
  intro z
  have hp := c.point_pairing a (c.homogeneousWeight a x) (c.basePoint x) z
  have hb := dotProductEquiv_dualVector
    ((dotProductEquiv ℝ (Fin n) x).comp
      (coneQuotientSectionReal c.basis c.fiberIndices)) (c.quotientReal z)
  have hd := basisSection_projection_decomposition (integralBasisReal c.basis)
    c.fiberIndices z
  have he := congrArg ((dotProductEquiv ℝ (Fin n) x) : Ambient n → ℝ) hd
  simp only [map_add, map_sum, map_smul, smul_eq_mul] at he
  change (dotProductEquiv ℝ (Fin n) (c.point a (c.homogeneousWeight a x) (c.basePoint x))) z =
    (dotProductEquiv ℝ (Fin n) x) z
  rw [show (dotProductEquiv ℝ (Fin n) (c.point a (c.homogeneousWeight a x) (c.basePoint x))) z =
      (dotProductEquiv ℝ (Fin n) z) (c.point a (c.homogeneousWeight a x) (c.basePoint x)) by
        exact dotProduct_comm
          (c.point a (c.homogeneousWeight a x) (c.basePoint x)) z, hp]
  change _ + (dotProductEquiv ℝ (Fin (n - c.fiberIndices.card)) (c.quotientReal z))
    (dualVector _) = _
  rw [hb]
  have hsec : coneQuotientSectionReal c.basis c.fiberIndices (c.quotientReal z) =
      basisSection (integralBasisReal c.basis) c.fiberIndices
        (basisProjection (integralBasisReal c.basis) c.fiberIndices z) := by
    simp [coneQuotientSectionReal, quotientReal, coneQuotientReal]
  rw [LinearMap.comp_apply, hsec]
  simp only [homogeneousWeight, add_sub_cancel_left]
  have hpair (i : Fin n) :
      (dotProductEquiv ℝ (Fin n) (embed n (c.basis i))) x =
        (dotProductEquiv ℝ (Fin n) x) (integralBasisReal c.basis i) := by
    rw [integralBasisReal_apply]
    exact dotProduct_comm (embed n (c.basis i)) x
  simp only [hpair]
  calc
    _ = (dotProductEquiv ℝ (Fin n) x)
        (basisSection (integralBasisReal c.basis) c.fiberIndices
          (basisProjection (integralBasisReal c.basis) c.fiberIndices z)) +
        ∑ i ∈ c.fiberIndices, (integralBasisReal c.basis).repr z i *
          (dotProductEquiv ℝ (Fin n) x) (integralBasisReal c.basis i) := by
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _
    _ = _ := he

/-- The coefficient identity used in canonical adjunction.  It is a literal
identity of the actual ray coefficients, including the `-1` on each base ray. -/
theorem baseWeight_canonical (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a β : Lattice n → ℝ)
    (q : Lattice (n - c.fiberIndices.card)) :
    c.baseWeight hR hN (fun v => a v - 1) β q =
      c.baseWeight hR hN a (fun v => β v + 1) q - 1 := by
  unfold baseWeight
  have he (i : Fin n) : β (c.basis i) - (a (c.basis i) - 1) =
      (β (c.basis i) + 1) - a (c.basis i) := by ring
  simp only [he]
  ring

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
