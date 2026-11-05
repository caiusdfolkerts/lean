module

public import VolumePolynomials.FirstVariableCoefficient
public import VolumePolynomials.FacetWeightPyramid
public import VolumePolynomials.PolytopeVolumeDecomposition

@[expose] public section
set_option autoImplicit false

/-! # The mixed-facet identity from genuine first variation

The first-variable coefficient is identified on the entire positive orthant,
then its squarefree coefficient is extracted. Lower-dimensional coefficient
nonnegativity comes from the proved volume-polynomial theorem, not from
pointwise comparison of unrelated polynomials.
-/

noncomputable section
open Set Filter MeasureTheory Module MvPolynomial
open scoped BigOperators Pointwise Topology

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092
open LinearFrame FacetWeightPyramid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

def facetFrameFactor (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) : ℝ :=
  letI : MeasureSpace (LinearMap.ker l.toLinearMap) := ⟨kernelMeasure l⟩
  letI : Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker l.toLinearMap)) :=
    kernelMeasure_isAddHaarMeasure l
  volumeFactor (continuousEquiv l v hv)

theorem facetFrameFactor_nonneg (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    0 ≤ facetFrameFactor l v hv := by
  first
  | letI : MeasureSpace (LinearMap.ker l.toLinearMap) := ⟨kernelMeasure l⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker l.toLinearMap)) :=
      kernelMeasure_isAddHaarMeasure l
    exact NNReal.coe_nonneg _

def facetDerivativePolynomial {n : ℕ} (K : Fin n → ConvexBody E)
    (D : FixedFacets (fun j => (K j : Set E)))
    (v : Fin D.count → E) (hv : ∀ i, D.normal i (v i) = 1) (A : ConvexBody E) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i, C (facetFrameFactor (D.normal i) (v i) (hv i) *
      SupportGeometry.support (A : Set E) (D.normal i)) *
    volumePolynomial (kernelMeasure (D.normal i))
      (fun j => kernelBody (K j) (D.normal i) (v i) (hv i))

theorem firstVariableCoefficient_eq_facetPolynomial {n : ℕ}
    (K : Fin n → ConvexBody E) (D : FixedFacets (fun j => (K j : Set E)))
    (h0 : ∀ j, (0 : E) ∈ K j) (hint : (0 : E) ∈ interior (∑ j, (K j : Set E)))
    (v : Fin D.count → E) (hv : ∀ i, D.normal i (v i) = 1) (A : ConvexBody E) :
    firstVariableCoefficient (volumePolynomial volume (Fin.cons A K)) =
      facetDerivativePolynomial K D v hv A := by
  first
  | classical
    letI : ∀ i, MeasureSpace (LinearMap.ker (D.normal i).toLinearMap) :=
      fun i => ⟨kernelMeasure (D.normal i)⟩
    letI : ∀ i, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (D.normal i).toLinearMap)) :=
      fun i => kernelMeasure_isAddHaarMeasure (D.normal i)
    apply MvPolynomial.funext_set (fun _ => Ioi (0 : ℝ)) (fun _ => Ioi_infinite 0)
    intro t ht'
    have ht : ∀ j, 0 < t j := fun j => ht' j (mem_univ j)
    have hp : ∀ i, 0 < D.height t i :=
      D.height_pos (fun j => (K j).isCompact) h0 hint t ht
    have hbody : PolyhedralSupport.body D.normal (D.height t) =
        (↑(∑ j, t j • K j) : Set E) := by
      first
      | rw [coe_sum_body]
        exact (D.body_eq t ht).symm
    have hS : IsCompact (PolyhedralSupport.body D.normal (D.height t)) := by
      first
      | rw [hbody]
        exact (∑ j, t j • K j).isCompact
    have hface (i : Fin D.count) : fixedFace D.normal (D.height t) i =
        (D.normal i).toExposed (∑ j, t j • (K j : Set E)) := by
      first
      | have hc : IsCompact (∑ j, t j • (K j : Set E)) := by
          simpa only [coe_sum_body, ConvexBody.coe_smul] using (∑ j, t j • K j).isCompact
        have hn : (∑ j, t j • (K j : Set E)).Nonempty := by
          simpa only [coe_sum_body, ConvexBody.coe_smul] using (∑ j, t j • K j).nonempty
        rw [exposed_eq_support_level hc hn,
          ← D.height_eq_support (fun j => (K j).isCompact) (fun j => (K j).nonempty) t ht i]
        unfold fixedFace
        rw [hbody, coe_sum_body]
        rfl
    have hbase (i : Fin D.count) : fixedFacetBase D.normal (D.height t) i (v i) (hv i) =
        (↑(∑ j, t j • kernelBody (K j) (D.normal i) (v i) (hv i)) :
          Set (LinearMap.ker (D.normal i).toLinearMap)) := by
      first
      | rw [fixedFacetBase, hface, image_exposed_positive_sum K _ _ _ t ht]
    have hd := first_variation_fixed_heights D.normal (D.height t) hp
      D.positive_ray_injective hS v hv A.isCompact A.convex A.nonempty
    rw [hbody] at hd
    have he := eval_firstVariableCoefficient_eq_of_volume_derivative volume A K t
      (fun j => (ht j).le) hd
    rw [he]
    simp only [facetDerivativePolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
      MvPolynomial.eval_C]
    apply Finset.sum_congr rfl
    intro i hi
    rw [volumePolynomial_eval (kernelMeasure (D.normal i)) _ t (fun j => (ht j).le)]
    rw [fixedFacetWeight, hbase]
    let q : ℝ := (kernelMeasure (D.normal i)).real
      (↑(∑ j, t j • kernelBody (K j) (D.normal i) (v i) (hv i)) :
        Set (LinearMap.ker (D.normal i).toLinearMap))
    change (facetFrameFactor (D.normal i) (v i) (hv i) * q) *
        SupportGeometry.support (A : Set E) (D.normal i) =
      (facetFrameFactor (D.normal i) (v i) (hv i) *
        SupportGeometry.support (A : Set E) (D.normal i)) * q
    ring

/-- The genuine mixed-facet identity. The `(n+1)` factor is the exact factorial
normalization in the definition of mixed volume. -/
theorem mixedVolume_facet_identity {n : ℕ}
    (K : Fin n → ConvexBody E) (D : FixedFacets (fun j => (K j : Set E)))
    (h0 : ∀ j, (0 : E) ∈ K j) (hint : (0 : E) ∈ interior (∑ j, (K j : Set E)))
    (v : Fin D.count → E) (hv : ∀ i, D.normal i (v i) = 1) (A : ConvexBody E) :
    ((n + 1 : ℕ) : ℝ) * mixedVolume volume (Fin.cons A K) =
      ∑ i, facetFrameFactor (D.normal i) (v i) (hv i) *
        SupportGeometry.support (A : Set E) (D.normal i) *
        mixedVolume (kernelMeasure (D.normal i))
          (fun j => kernelBody (K j) (D.normal i) (v i) (hv i)) := by
  first
  | classical
    have hc := congrArg (fun p : MvPolynomial (Fin n) ℝ => p.coeff (squarefreeExponent n))
      (firstVariableCoefficient_eq_facetPolynomial K D h0 hint v hv A)
    simp only [firstVariableCoefficient_squarefree, facetDerivativePolynomial,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul] at hc
    have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hn1 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    calc
      ((n + 1 : ℕ) : ℝ) * mixedVolume volume (Fin.cons A K) =
          (volumePolynomial volume (Fin.cons A K)).coeff (squarefreeExponent (n + 1)) /
            (n.factorial : ℝ) := by
        first
        | rw [mixedVolume, Nat.factorial_succ, Nat.cast_mul]
          field_simp [hn, hn1]
      _ = (∑ i, facetFrameFactor (D.normal i) (v i) (hv i) *
          SupportGeometry.support (A : Set E) (D.normal i) *
          (volumePolynomial (kernelMeasure (D.normal i))
            (fun j => kernelBody (K j) (D.normal i) (v i) (hv i))).coeff
              (squarefreeExponent n)) / (n.factorial : ℝ) := congrArg (fun x => x / _) hc
      _ = _ := by
        first
        | rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i hi
          unfold mixedVolume
          ring

/-- Monotonicity in the first argument, for a finite background facet family.
Nonnegativity is coefficientwise on the lower-dimensional volume polynomials. -/
theorem mixedVolume_mono_first_of_fixedFacets {n : ℕ}
    (K : Fin n → ConvexBody E) (D : FixedFacets (fun j => (K j : Set E)))
    (h0 : ∀ j, (0 : E) ∈ K j) (hint : (0 : E) ∈ interior (∑ j, (K j : Set E)))
    (v : Fin D.count → E) (hv : ∀ i, D.normal i (v i) = 1)
    (A B : ConvexBody E) (hAB : A ≤ B) :
    mixedVolume volume (Fin.cons A K) ≤ mixedVolume volume (Fin.cons B K) := by
  first
  | apply Iff.mp (mul_le_mul_iff_right₀ (by positivity : 0 < ((n + 1 : ℕ) : ℝ)))
    rw [mixedVolume_facet_identity K D h0 hint v hv A,
      mixedVolume_facet_identity K D h0 hint v hv B]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right
    · apply mul_le_mul_of_nonneg_left _ (facetFrameFactor_nonneg _ _ _)
      exact SupportGeometry.support_le A.nonempty (D.normal i)
        (fun x hx => SupportGeometry.le_support B.isCompact (D.normal i) (hAB hx))
    · exact mixedVolume_nonnegative (kernelMeasure (D.normal i)) _

theorem mixedVolume_mono_first_of_finite_polytopes {n : ℕ}
    (K : Fin n → ConvexBody E) (hK : ∀ j, IsFiniteHull (K j : Set E))
    (h0 : ∀ j, (0 : E) ∈ K j) (hint : (0 : E) ∈ interior (∑ j, (K j : Set E)))
    (A B : ConvexBody E) (hAB : A ≤ B) :
    mixedVolume volume (Fin.cons A K) ≤ mixedVolume volume (Fin.cons B K) := by
  first
  | classical
    obtain ⟨D⟩ := exists_fixedFacets (fun j => (K j : Set E)) hK
      (fun j => (K j).nonempty) ⟨0, hint⟩
    choose v hv using fun i => LinearFrame.exists_unit_value (D.normal i) (D.normal_ne_zero i)
    exact mixedVolume_mono_first_of_fixedFacets K D h0 hint v hv A B hAB

end VolumePolynomials.PolytopeGeometry
