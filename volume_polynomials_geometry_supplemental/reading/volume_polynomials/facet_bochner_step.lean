module

public import VolumePolynomials.FacetBochnerIdentity
public import VolumePolynomials.WeightedMatrixBochner

@[expose] public section
set_option autoImplicit false

/-! # The dimension step of Alexandrov--Fenchel on a common simple type

The only inductive input is the literal mixed-volume inequality on the
actual lower-dimensional facet spaces. All operator identities, positivity,
off-diagonal signs, and connectivity are derived from the genuine bodies.
The endpoint of this module is an induction step; the dimension induction
and approximation to arbitrary bodies are supplied separately.
-/

noncomputable section
open Set MeasureTheory Module Matrix LinearMap
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  {m n : ℕ}

theorem facet_bochner_summand
    {N α h u v w r s : ℝ} (hN : 0 < N) (hα : 0 < α) (hh : 0 < h)
    (hw : 0 < w) (hr : N * r = α * v) (hs : N * s = α * w)
    (hi : u * w ≤ v ^ 2) : (α * h / N) * u ≤ r ^ 2 / (s / h) := by
  first
  | have hr' : r = α * v / N := by
      first
      | apply (eq_div_iff hN.ne').mpr
        nlinarith [hr]
    have hs' : s = α * w / N := by
      first
      | apply (eq_div_iff hN.ne').mpr
        nlinarith [hs]
    have he : r ^ 2 / (s / h) = (α * h / N) * (v ^ 2 / w) := by
      first
      | rw [hr', hs']
        field_simp [hN.ne', hα.ne', hh.ne', hw.ne']
    rw [he]
    exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hw).mpr hi)
      (div_nonneg (mul_nonneg hα.le hh.le) hN.le)

theorem facetMixedForm_reference_inequality_of_lower_dimension
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (i : Fin m) (v : E) (hv : l i v = 1)
    (hIH : ∀ (K : Fin n → ConvexBody (LinearMap.ker (l i).toLinearMap))
      (A B : ConvexBody (LinearMap.ker (l i).toLinearMap)),
      mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons A K)) *
        mixedVolume (kernelMeasure (l i)) (Fin.cons B (Fin.cons B K)) ≤
      mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons B K)) ^ 2)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc) (x : Fin m → ℝ) :
    facetMixedForm l h₀ hg hp hc i v hv H x x *
        facetMixedForm l h₀ hg hp hc i v hv H h h ≤
      facetMixedForm l h₀ hg hp hc i v hv H x h ^ 2 := by
  first
  | apply OpenConeExtension.bilinear_reference_inequality_of_cone
      (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc)
      (facetMixedForm l h₀ hg hp hc i v hv H)
      (facetMixedForm_symmetric l h₀ hg hp hc i v hv H) hh
    intro y hy
    rw [facetMixedForm_eq l h₀ hg hp hc i v hv H hH hy hy,
      facetMixedForm_eq l h₀ hg hp hc i v hv H hH hh hh,
      facetMixedForm_eq l h₀ hg hp hc i v hv H hH hy hh]
    exact hIH _ _ _

theorem matrixForm_mixedSupportMatrix
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x y : Fin m → ℝ) :
    matrixForm (mixedSupportMatrix volume l h₀ hg hp hc K) x y =
      mixedSupportForm volume l h₀ hg hp hc K x y := by
  first
  | rw [mixedSupportForm_symmetric volume l h₀ hg hp hc K x y,
      mixedSupportForm_eq_dotProduct]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem mixedSupportMatrix_image_pos
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (hdim : finrank ℝ E = n + 3)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) (i : Fin m) :
    0 < (mixedSupportMatrix volume l h₀ hg hp hc
      (coneTuple l h₀ hp hc (Fin.cons h H)) *ᵥ h) i := by
  first
  | have he := mixedSupportMatrix_row_facetMixedForm l h₀ hg hp hc hf hn hray
      H hH hh v hv i h
    have hpos := mul_pos (facetFrameFactor_pos (l i) (v i) (hv i))
      (facetMixedForm_positive l h₀ hg hp hc hf i (v i) (hv i) hdim H hH hh hh)
    rw [← he] at hpos
    exact (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < ((n + 3 : ℕ) : ℝ))).mp hpos

theorem mixedSupportMatrix_bochner_of_lower_dimension
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (hdim : finrank ℝ E = n + 3)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1)
    (hIH : ∀ i (K : Fin n → ConvexBody (LinearMap.ker (l i).toLinearMap))
      (A B : ConvexBody (LinearMap.ker (l i).toLinearMap)),
      mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons A K)) *
        mixedVolume (kernelMeasure (l i)) (Fin.cons B (Fin.cons B K)) ≤
      mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons B K)) ^ 2)
    (x : Fin m → ℝ) :
    matrixForm (mixedSupportMatrix volume l h₀ hg hp hc
        (coneTuple l h₀ hp hc (Fin.cons h H))) x x ≤
      ∑ i, ((mixedSupportMatrix volume l h₀ hg hp hc
        (coneTuple l h₀ hp hc (Fin.cons h H)) *ᵥ x) i) ^ 2 /
        ((mixedSupportMatrix volume l h₀ hg hp hc
          (coneTuple l h₀ hp hc (Fin.cons h H)) *ᵥ h) i / h i) := by
  first
  | let N : ℝ := ((n + 3 : ℕ) : ℝ)
    have hN : 0 < N := by dsimp [N]; positivity
    let α : Fin m → ℝ := fun i => facetFrameFactor (l i) (v i) (hv i)
    let L : Fin m → LinearMap.BilinForm ℝ (Fin m → ℝ) :=
      fun i => facetMixedForm l h₀ hg hp hc i (v i) (hv i) H
    let A := mixedSupportMatrix volume l h₀ hg hp hc (coneTuple l h₀ hp hc (Fin.cons h H))
    have hsum : matrixForm A x x = ∑ i, (α i * h i / N) * L i x x := by
      first
      | rw [matrixForm_mixedSupportMatrix]
        have he := mixedSupportForm_facet_bilinear_identity l h₀ hg hp hc hf hn hray
          H hH hh v hv x x
        calc
          _ = (∑ i, α i * h i * L i x x) / N := by
            apply (eq_div_iff hN.ne').mpr
            nlinarith [he]
          _ = _ := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i _
            ring
    rw [hsum]
    apply Finset.sum_le_sum
    intro i _
    exact facet_bochner_summand hN (facetFrameFactor_pos (l i) (v i) (hv i)) (hh.1 i)
      (facetMixedForm_positive l h₀ hg hp hc hf i (v i) (hv i) hdim H hH hh hh)
      (mixedSupportMatrix_row_facetMixedForm l h₀ hg hp hc hf hn hray H hH hh v hv i x)
      (mixedSupportMatrix_row_facetMixedForm l h₀ hg hp hc hf hn hray H hH hh v hv i h)
      (facetMixedForm_reference_inequality_of_lower_dimension l h₀ hg hp hc
        H hH i (v i) (hv i) (hIH i) hh x)

theorem mixedSupportForm_reverse_cauchy_schwarz_of_lower_dimension
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (hdim : finrank ℝ E = n + 3)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1)
    (hIH : ∀ i (K : Fin n → ConvexBody (LinearMap.ker (l i).toLinearMap))
      (A B : ConvexBody (LinearMap.ker (l i).toLinearMap)),
      mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons A K)) *
        mixedVolume (kernelMeasure (l i)) (Fin.cons B (Fin.cons B K)) ≤
      mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons B K)) ^ 2)
    (x y : Fin m → ℝ)
    (hy : 0 ≤ mixedSupportForm volume l h₀ hg hp hc
      (coneTuple l h₀ hp hc (Fin.cons h H)) y y) :
    mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc (Fin.cons h H)) x x *
        mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc (Fin.cons h H)) y y ≤
      mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc (Fin.cons h H)) x y ^ 2 := by
  first
  | let G : Fin (n + 1) → Fin m → ℝ := Fin.cons h H
    have hG : ∀ j, G j ∈ typeCone l h₀ hp hc := fun j => Fin.cases hh hH j
    let A := mixedSupportMatrix volume l h₀ hg hp hc (coneTuple l h₀ hp hc G)
    have he := matrix_reverse_cauchy_schwarz_of_weighted_bochner A
      (mixedSupportMatrix_symmetric volume l h₀ hg hp hc _) h hh.1
      (mixedSupportMatrix_image_pos l h₀ hg hp hc hf hn hray hdim H hH hh v hv)
      (mixedSupportMatrix_offdiag_nonnegative l h₀ hg hp hc hf hn hray G hG hdim v hv)
      (mixedSupportMatrix_positive_graph_connected l h₀ hg hp hc hf hn hray hdim G hG v hv)
      (mixedSupportMatrix_bochner_of_lower_dimension l h₀ hg hp hc hf hn hray
        hdim H hH hh v hv hIH) x y
      (by simpa only [A, matrixForm_mixedSupportMatrix] using hy)
    simpa only [A, G, matrixForm_mixedSupportMatrix] using he

end VolumePolynomials.PolyhedralSupport
