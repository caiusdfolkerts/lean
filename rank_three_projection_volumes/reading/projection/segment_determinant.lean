module

public import Projection.SegmentSeminorm
public import VolumePolynomials.ProjectionMixedVolumeTransport
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module MvPolynomial
open scoped Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

variable {n : ℕ}

/-- The matrix has the marked vectors as its columns. -/
def columnsMatrix (U : Fin n → Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => U j i

def columnsLinear (U : Fin n → Space n) : Space n →L[ℝ] Space n :=
  (Matrix.toLin' (columnsMatrix U)).toContinuousLinearMap

@[simp] theorem columnsLinear_basis (U : Fin n → Space n) (i : Fin n) :
    columnsLinear U (Pi.single i 1) = U i := by
  ext j
  simp only [columnsLinear, LinearMap.coe_toContinuousLinearMap',
    Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply, columnsMatrix]

@[simp] theorem columnsLinear_det (U : Fin n → Space n) :
    LinearMap.det (columnsLinear U).toLinearMap = (columnsMatrix U).det :=
  LinearMap.det_toLin' _

theorem smul_originSegment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (v : E) : r • originSegment v = originSegment (r • v) := by
  simp only [originSegment, smul_segmentBody, smul_zero]

theorem squarefree_support (n : ℕ) : (squarefreeExponent n).support = Finset.univ := by
  ext i
  simp [Finsupp.mem_support_iff, squarefreeExponent_apply]

/-- The polynomial of the standard coordinate segments is the squarefree
monomial, proved from the volume of the actual coordinate box. -/
theorem volumePolynomial_basis_segments (n : ℕ) :
    volumePolynomial volume (fun i : Fin n => originSegment (Pi.single i (1 : ℝ))) =
      MvPolynomial.monomial (squarefreeExponent n) 1 := by
  apply volumePolynomial_eq_of_eval
  intro t ht
  have hsum : ((∑ i : Fin n, t i • originSegment (Pi.single i (1 : ℝ)) :
      Body n) : Set (Space n)) = parallelepiped (fun i => Pi.single i (t i)) := by
    rw [coe_sum_body, parallelepiped_eq_sum_segment]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_originSegment]
    change segment ℝ 0 (t i • Pi.single i (1 : ℝ)) = segment ℝ 0 (Pi.single i (t i))
    congr 1
    ext j
    by_cases hij : i = j <;> simp [hij]
  rw [hsum, parallelepiped_single, uIcc_of_le (show (0 : Fin n → ℝ) ≤ t from ht)]
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod,
    squarefree_support, squarefreeExponent_apply, pow_one]
  simpa only [measureReal_def, Pi.zero_def, Pi.zero_apply, sub_zero] using
    (Real.volume_Icc_pi_toReal (a := (0 : Fin n → ℝ)) (b := t) ht).symm

theorem mixedVolume_basis_segments (n : ℕ) :
    mixedVolume volume (fun i : Fin n => originSegment (Pi.single i (1 : ℝ))) =
      1 / (n.factorial : ℝ) := by
  simp only [mixedVolume, volumePolynomial_basis_segments,
    MvPolynomial.coeff_monomial, if_pos rfl, ite_true]

theorem mixedVolume_origin_segments (U : Fin n → Space n) :
    mixedVolume volume (fun i => originSegment (U i)) =
      |(columnsMatrix U).det| / (n.factorial : ℝ) := by
  have hm (i : Fin n) : mapBody (columnsLinear U) (originSegment (Pi.single i 1)) =
      originSegment (U i) := by
    simp only [originSegment, map_segmentBody, map_zero, columnsLinear_basis]
  have h := mixedVolume_map_linear volume (columnsLinear U)
    (fun i : Fin n => originSegment (Pi.single i 1))
  simpa only [hm, columnsLinear_det, mixedVolume_basis_segments, mul_one_div] using h

/-- The full determinant identity includes dependent and zero directions. -/
theorem mixedVolume_centered_segments (U : Fin n → Space n) :
    (n.factorial : ℝ) * mixedVolume volume (fun i => centeredSegment (U i)) =
      |(columnsMatrix U).det| := by
  have h := mixedVolume_translate volume (fun i => originSegment (U i))
    (fun i => -(1 / 2 : ℝ) • U i)
  simp only [← centered_eq_translate_origin] at h
  rw [h, mixedVolume_origin_segments]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

end RankThreeProjection
