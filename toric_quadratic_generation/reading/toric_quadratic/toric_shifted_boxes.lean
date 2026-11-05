module

public import PaperVerification.ToricFocusSliceBoxes

@[expose] public section

/-!
# Full shifted boxes in the original polytope and its interior

The normal heights are computed from the actual integral shear. Their
budgets and the genuine primitive fiber coefficients put each arbitrary
real box point in the exact quotient slice. The base-dimension zero nef
endpoint is included throughout.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem shifted_box_mem
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative) (hfull : Finset.univ.image b ∈ «Σ».cones)
    (j : Fin n) (hj : j ∈ I) (v : Ambient n)
    (hv : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -(a (b i) : ℝ))
    (side t : ℝ) (hside : 0 ≤ side)
    (ht : side * (R.negative.card - 1 : ℕ) ≤ t)
    (hbudget : t + side + side * ((n - R.fiberDimension - R.negative.card : ℕ) : ℝ) ≤ e)
    (hfiber : side * R.fiberDimension ≤ R.degree (fun u => (a u : ℝ)) +
      (R.minimumCoefficient hne : ℝ) * t)
    («λ» : Fin n → ℝ) («hλ» : ∀ i, 0 ≤ «λ» i ∧ «λ» i ≤ side) :
    v + (t • integralBasisReal (integralDualBasis b) j +
      ∑ k, «λ» k • starShearBasis (integralBasisReal (integralDualBasis b)) I j k) ∈
      «Σ».fanPolytope (fun u => (a u : ℝ)) := by
  let B := integralBasisReal (integralDualBasis b)
  let δ := t • B j + ∑ k, «λ» k • starShearBasis B I j k
  have hcard : I.card = R.negative.card := by
    rw [← hI, Finset.card_image_of_injective _ b.injective]
  have hheight := shifted_star_box_normal_heights B I j hj side t hside
    (by simpa only [hcard] using ht) «λ» «hλ»
  have hsum : (∑ u ∈ R.negative, normalHeight δ u) = ∑ i ∈ I, B.coord i δ := by
    rw [← hI]
    exact normalHeight_sum_image δ b I
  have hh (u : Lattice n) (hu : u ∈ R.negative) : 0 ≤ normalHeight δ u := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hI.symm ▸ hu)
    rw [normalHeight_basis]
    exact hheight.1 i hi
  have htotalLo : t ≤ ∑ u ∈ R.negative, normalHeight δ u := by
    rw [hsum]
    exact hheight.2.1
  have htotalHi : (∑ u ∈ R.negative, normalHeight δ u) ≤ t + side := by
    rw [hsum]
    exact hheight.2.2
  apply «Σ».focus_slice_box_mem hpure a ha he hedges R hR b I hI hfull v δ hv side hside hh
  · intro k
    have hk : complementaryEmbedding I k ∉ I :=
      (mem_range_complementaryEmbedding_iff I _).mp ⟨k, rfl⟩
    have hkj : complementaryEmbedding I k ≠ j := fun h => hk (h.symm ▸ hj)
    rw [normalHeight_basis, show B.coord (complementaryEmbedding I k) δ =
        B.coord (complementaryEmbedding I k)
          (t • B j + ∑ l, «λ» l • starShearBasis B I j l) from rfl,
      coord_shifted_star_box, if_neg hkj, add_zero]
    exact «hλ» _
  · linarith
  · have hlower := R.degree_displaced_focus_lower hne (fun u => (a u : ℝ))
      0 (normalHeight δ) hh
    simp only [zero_mul, add_zero, sub_zero] at hlower
    have hm : (0 : ℝ) ≤ R.minimumCoefficient hne := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left htotalLo hm
    linarith

theorem shifted_inner_unit_box_mem
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative) (hfull : Finset.univ.image b ∈ «Σ».cones)
    (j : Fin n) (hj : j ∈ I) (v : Ambient n)
    (hv : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -(a (b i) : ℝ))
    (t : ℝ) (ht : 2 * (R.negative.card - 1 : ℕ) ≤ t)
    (hbudget : t + 2 + (2 * (n - R.fiberDimension - R.negative.card : ℕ) + 1 : ℕ) ≤ e)
    (hfiber : (2 * R.fiberDimension + 1 : ℕ) ≤
      R.degree (fun u => (a u : ℝ)) + R.negativeCoefficientSum +
        (R.minimumCoefficient hne : ℝ) * (t + 1 - R.negative.card))
    («λ» : Fin n → ℝ) («hλ» : ∀ i, 0 ≤ «λ» i ∧ «λ» i ≤ 1) :
    v + (t • integralBasisReal (integralDualBasis b) j +
      ∑ k, (1 + «λ» k) • starShearBasis (integralBasisReal (integralDualBasis b)) I j k) ∈
      interior («Σ».fanPolytope (fun u => (a u : ℝ))) := by
  let B := integralBasisReal (integralDualBasis b)
  let δ := t • B j + ∑ k, (1 + «λ» k) • starShearBasis B I j k
  have hcard : I.card = R.negative.card := by
    rw [← hI, Finset.card_image_of_injective _ b.injective]
  have hheight := shifted_inner_star_box_normal_heights B I j hj t
    (by simpa only [hcard] using ht) «λ» «hλ»
  have hsum : (∑ u ∈ R.negative, normalHeight δ u) = ∑ i ∈ I, B.coord i δ := by
    rw [← hI]
    exact normalHeight_sum_image δ b I
  have hh (u : Lattice n) (hu : u ∈ R.negative) : 1 ≤ normalHeight δ u := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hI.symm ▸ hu)
    rw [normalHeight_basis]
    exact hheight.1 i hi
  have htotalLo : t + 1 ≤ ∑ u ∈ R.negative, normalHeight δ u := by
    rw [hsum]
    exact hheight.2.1
  have htotalHi : (∑ u ∈ R.negative, normalHeight δ u) ≤ t + 2 := by
    rw [hsum]
    exact hheight.2.2
  apply «Σ».focus_inner_slice_box_mem hpure a ha he hedges R hR b I hI hfull v δ hv hh
  · intro k
    have hk : complementaryEmbedding I k ∉ I :=
      (mem_range_complementaryEmbedding_iff I _).mp ⟨k, rfl⟩
    have hkj : complementaryEmbedding I k ≠ j := fun h => hk (h.symm ▸ hj)
    rw [normalHeight_basis, show B.coord (complementaryEmbedding I k) δ =
        B.coord (complementaryEmbedding I k)
          (t • B j + ∑ l, (1 + «λ» l) • starShearBasis B I j l) from rfl,
      coord_shifted_star_box, if_neg hkj, add_zero]
    obtain ⟨hlo, hhi⟩ := «hλ» (complementaryEmbedding I k)
    constructor <;> linarith
  · linarith
  · have hlower := R.degree_displaced_focus_lower hne (fun u => (a u : ℝ))
      1 (normalHeight δ) hh
    simp only [one_mul] at hlower
    have hm : (0 : ℝ) ≤ R.minimumCoefficient hne := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left
      (sub_le_sub_right htotalLo (R.negative.card : ℝ)) hm
    linarith

end SmoothCompleteFan

end PaperVerification.ToricGeometry
