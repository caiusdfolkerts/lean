module

public import PaperVerification.ToricQuotientFacePolytopes
public import PaperVerification.ToricNefBoxes
public import PaperVerification.ToricBundleFanPrimitive

@[expose] public section

/-!
# Real displaced face degrees and tangent boxes

Restricting the genuine nef proportional remainder proves the edge-degree
reserve for arbitrary real heights, without pretending a nonintegral slice
is a lattice polytope. The fiber relation and the proved bound on all other
primitive collections then supply whole tangent boxes, including nef endpoints.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

variable {n : ℕ}

theorem quotientFaceOrigin_sub (a c : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    quotientFaceOrigin (a - c) b I = quotientFaceOrigin a b I - quotientFaceOrigin c b I := by
  simp only [quotientFaceOrigin, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, neg_sub]
  abel

theorem quotientFaceOrigin_smul (t : ℝ) (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    quotientFaceOrigin (t • a) b I = t • quotientFaceOrigin a b I := by
  simp only [quotientFaceOrigin, Pi.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, smul_neg]

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

theorem faceSupport_sub (a c : Lattice n → ℝ) :
    «Σ».faceSupport b I hF (a - c) = «Σ».faceSupport b I hF a - «Σ».faceSupport b I hF c := by
  funext u
  by_cases hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays
  · simp only [faceSupport, dif_pos hu, Pi.sub_apply, quotientFaceOrigin_sub, map_sub]
    ring
  · simp only [faceSupport, dif_neg hu, Pi.sub_apply, sub_zero]

theorem faceSupport_smul (t : ℝ) (a : Lattice n → ℝ) :
    «Σ».faceSupport b I hF (t • a) = t • «Σ».faceSupport b I hF a := by
  funext u
  by_cases hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays
  · simp only [faceSupport, dif_pos hu, Pi.smul_apply, quotientFaceOrigin_smul,
      map_smul, smul_eq_mul]
    ring
  · simp only [faceSupport, dif_neg hu, Pi.smul_apply, smul_zero]

/-- Original integral face degrees inherit the literal ambient edge bound. -/
theorem faceSupport_contractible_degree_lower_bound_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : («Σ».completeQuotientStarFan b I hF).PrimitiveRelation)
    (hR : R.IsCombinatoriallyContractible) :
    (e : ℝ) ≤ R.degree («Σ».faceSupport b I hF (fun u => (a u : ℝ))) := by
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let c := «Σ».faceSupportLattice b I hF a
  have hpureΨ : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  have hc : Ψ.IsStrictSupport (fun u => (c u : ℝ)) := by
    rw [show (fun u => (c u : ℝ)) = «Σ».faceSupport b I hF (fun u => (a u : ℝ)) from
      «Σ».faceSupportLattice_cast b I hF a]
    exact «Σ».faceSupport_isStrictSupport b I hF _ ha
  let P := «Σ».supportLatticePolytope hpure a ha
  let Q := Ψ.supportLatticePolytope hpureΨ c hc
  have himage : (quotientFaceIntegralChart a b I).realMap '' Q.carrier =
      «Σ».supportFace (fun u => (a u : ℝ)) (I.image b) := by
    rw [Ψ.supportLatticePolytope_carrier]
    exact «Σ».quotientFaceIntegralChart_image_fanPolytope b I hF hpure a
      (IsStrictSupport.isNef «Σ» ha)
  have hface : IsExtreme ℝ P.carrier
      («Σ».supportFace (fun u => (a u : ℝ)) (I.image b)) := by
    rw [«Σ».supportLatticePolytope_carrier]
    exact «Σ».supportFace_isExtreme _ _ (fun u hu => «Σ».ray_mem_of_mem_cone hF hu)
  have hQedges := P.edgesAtLeast_face_chart hedges _ hface Q
    (quotientFaceIntegralChart a b I) himage
  have hd := Ψ.support_contractible_degree_lower_bound_of_edges hpureΨ c hc hQedges R hR
  rw [show (fun u => (c u : ℝ)) = «Σ».faceSupport b I hF (fun u => (a u : ℝ)) from
    «Σ».faceSupportLattice_cast b I hF a] at hd
  exact hd

/-- Every contracted face degree loses at most the total displacement,
also at arbitrary real heights and at the nef endpoint. -/
theorem displaced_faceSupport_degree_lower_bound (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (h : Lattice n → ℝ) (hh : ∀ u ∈ I.image b, 0 ≤ h u)
    (hbudget : (∑ u ∈ I.image b, h u) ≤ e)
    (R : («Σ».completeQuotientStarFan b I hF).PrimitiveRelation)
    (hR : R.IsCombinatoriallyContractible) :
    (e : ℝ) - ∑ u ∈ I.image b, h u ≤ R.degree
      («Σ».faceSupport b I hF (displacedSupport (fun u => (a u : ℝ)) (I.image b) h)) := by
  let H := ∑ u ∈ I.image b, h u
  let c : ℝ := 1 - H / e
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hc : 0 ≤ c := sub_nonneg.mpr ((div_le_one heR).mpr hbudget)
  have hnef := «Σ».displacedSupport_nef_difference hpure a ha e heR
    («Σ».support_extremal_degree_lower_bound_of_edges hpure a ha hedges)
    (I.image b) h hh
  have hrestricted := «Σ».faceSupport_isNef b I hF _ hnef
  rw [«Σ».faceSupport_sub, «Σ».faceSupport_smul] at hrestricted
  have hd := R.degree_nonneg_of_nef hrestricted
  rw [R.degree_sub, R.degree_smul] at hd
  have hbase := «Σ».faceSupport_contractible_degree_lower_bound_of_edges b I hF hpure
    a ha hedges R hR
  have hm := mul_le_mul_of_nonneg_left hbase hc
  have hcvalue : c * e = (e : ℝ) - H := by
    dsimp only [c]
    rw [sub_mul, one_mul, div_mul_cancel₀ _ heR.ne']
  change 0 ≤ R.degree _ - c * R.degree _ at hd
  rw [hcvalue] at hm
  change (e : ℝ) - H ≤ _
  linarith

end SmoothCompleteFan

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation} (c : R.BundleCoordinates)

/-- Every actual contractible primitive degree satisfies the tangent box
criterion from the fiber degree and the actual base-dimension floor. -/
theorem all_contractible_degrees_of_fiber_and_base
    (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hfiber : side * R.fiberDimension ≤ R.degree a)
    (hbase : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
      S.positive ≠ R.positive → side * ((n - c.fiberIndices.card : ℕ) : ℝ) ≤ S.degree a) :
    ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
      side * S.fiberDimension ≤ S.degree a := by
  intro S hS
  by_cases hSR : S.positive = R.positive
  · have hdim : S.fiberDimension = R.fiberDimension := by simp only [PrimitiveRelation.fiberDimension, hSR]
    rw [hdim, S.degree_unique R hSR]
    exact hfiber
  · have hcard := c.other_primitive_card_le hR hN S.primitive hSR
    have hdim : S.fiberDimension ≤ n - c.fiberIndices.card := by
      unfold PrimitiveRelation.fiberDimension
      omega
    have hdimR : (S.fiberDimension : ℝ) ≤ ((n - c.fiberIndices.card : ℕ) : ℝ) := by exact_mod_cast hdim
    exact (mul_le_mul_of_nonneg_left hdimR hside).trans (hbase S hS hSR)


/-- A fiber degree and the actual nonfiber degree floor imply every
corner box on the genuine bundle fan. Degenerate nef supports are allowed. -/
theorem corner_box_of_fiber_and_base_degrees
    (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅) (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hfiber : side * R.fiberDimension ≤ R.degree a)
    (hbase : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
      S.positive ≠ R.positive → side * ((n - c.fiberIndices.card : ℕ) : ℝ) ≤ S.degree a)
    (s : «Σ».fullCones) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    «Σ».cartierPoint a s + ∑ i, t i • «Σ».cartierBasis s i ∈ «Σ».fanPolytope a :=
  «Σ».corner_box_mem_fanPolytope hpure H hH a side hside
    (c.all_contractible_degrees_of_fiber_and_base hR hN a side hside hfiber hbase) s t ht

/-- The exact canonical tangent degree criterion for every actual
contractible primitive relation. -/
theorem all_adjoint_contractible_degrees_of_fiber_and_base
    (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a : Lattice n → ℝ)
    (hfiber : (2 * R.fiberDimension + 1 : ℕ) ≤ R.degree a)
    (hbase : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
      S.positive ≠ R.positive → (2 * (n - c.fiberIndices.card) + 1 : ℕ) ≤ S.degree a) :
    ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
      (S.fiberDimension : ℝ) ≤ S.degree (fun u => a u - 1) := by
  intro S hS
  have hpositive : 0 < S.positive.card := Finset.card_pos.mpr («Σ».primitiveCollection_nonempty S.primitive)
  have hdim : S.positive.card = S.fiberDimension + 1 := by
    unfold PrimitiveRelation.fiberDimension
    omega
  have hdeg : S.degree (fun u => a u - 1) =
      S.degree a - S.positive.card + ∑ v ∈ S.negative, (S.coefficient v : ℝ) := by
    simp only [PrimitiveRelation.degree, Finset.sum_sub_distrib, mul_sub, mul_one,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  have hneg : 0 ≤ ∑ v ∈ S.negative, (S.coefficient v : ℝ) :=
    Finset.sum_nonneg (fun v hv => Nat.cast_nonneg _)
  rw [hdeg]
  by_cases hSR : S.positive = R.positive
  · have hdimSR : S.fiberDimension = R.fiberDimension := by
      simp only [PrimitiveRelation.fiberDimension, hSR]
    have hdegree := S.degree_unique R hSR a
    have hf : (2 : ℝ) * S.fiberDimension + 1 ≤ S.degree a := by
      simpa only [hdimSR, hdegree, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hfiber
    rw [hdim, Nat.cast_add, Nat.cast_one]
    linarith
  · have hcard := c.other_primitive_card_le hR hN S.primitive hSR
    have hcardR : (S.positive.card : ℝ) ≤ (n - c.fiberIndices.card : ℕ) + 1 := by exact_mod_cast hcard
    have hb := hbase S hS hSR
    have hbR : (2 : ℝ) * (n - c.fiberIndices.card : ℕ) + 1 ≤ S.degree a := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hb
    have hdimR : (S.positive.card : ℝ) = (S.fiberDimension : ℝ) + 1 := by exact_mod_cast hdim
    linarith

/-- The canonical unit-box case: the fiber parent has degree at least
`2r+1`, and every other parent degree is at least `2b+1`. -/
theorem adjoint_unit_box_of_fiber_and_base_degrees
    (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅) (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ)
    (hfiber : (2 * R.fiberDimension + 1 : ℕ) ≤ R.degree a)
    (hbase : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
      S.positive ≠ R.positive → (2 * (n - c.fiberIndices.card) + 1 : ℕ) ≤ S.degree a)
    (s : «Σ».fullCones) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    «Σ».cartierPoint (fun u => a u - 1) s + ∑ i, t i • «Σ».cartierBasis s i ∈
      «Σ».fanPolytope (fun u => a u - 1) := by
  apply «Σ».corner_box_mem_fanPolytope hpure H hH (fun u => a u - 1) 1 (by norm_num) ?_ s t ht
  intro S hS
  simpa only [one_mul] using
    c.all_adjoint_contractible_degrees_of_fiber_and_base hR hN a hfiber hbase S hS

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
