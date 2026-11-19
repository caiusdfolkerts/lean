module

public import ToricPower.RawPolytope

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n s : ℕ}

/-- One plus the largest absolute divisor coefficient; the empty maximum is zero. -/
def divisorHeight (b : Fin s → ℤ) : ℕ :=
  1 + Finset.univ.sup (fun i => (b i).natAbs)

/-- The explicitly computable constant H_A, depending only on A. -/
def rayThresholdCoefficient (A : Matrix (Fin s) (Fin n) ℤ) : ℕ :=
  (affineThresholdCoefficient (rawConstraintMatrix A)).natAbs

def realStabilizationBound (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) : ℕ :=
  divisorHeight b * rayThresholdCoefficient A + 1

/-- The paper's bound with the stronger uniform choice T_A = n. -/
def periodicityBound (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) : ℕ :=
  realStabilizationBound A b + rayPeriod A * n

lemma divisorHeight_pos (b : Fin s → ℤ) : 0 < divisorHeight b := by
  unfold divisorHeight
  omega

lemma rayThresholdCoefficient_pos (A : Matrix (Fin s) (Fin n) ℤ) :
    0 < rayThresholdCoefficient A :=
  Int.natAbs_pos.mpr (ne_of_gt (affineThresholdCoefficient_pos _))

lemma rayThresholdCoefficient_cast (A : Matrix (Fin s) (Fin n) ℤ) :
    (rayThresholdCoefficient A : ℤ) = affineThresholdCoefficient (rawConstraintMatrix A) := by
  simp only [rayThresholdCoefficient, Int.natCast_natAbs,
    abs_of_pos (affineThresholdCoefficient_pos _)]

lemma realStabilizationBound_pos (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) : 0 < realStabilizationBound A b := by
  unfold realStabilizationBound
  omega

lemma divisor_abs_lt_height (b : Fin s → ℤ) (i : Fin s) :
    |b i| < (divisorHeight b : ℤ) := by
  have h : (b i).natAbs ≤ Finset.univ.sup (fun j => (b j).natAbs) :=
    Finset.le_sup (f := fun j => (b j).natAbs) (Finset.mem_univ i)
  have hh : (b i).natAbs < divisorHeight b := by unfold divisorHeight; omega
  rw [← Int.natCast_natAbs]
  exact_mod_cast hh

lemma rawOffset_bound (b : Fin s → ℤ) (j : RawRow n s) :
    |rawOffset b j| ≤ (divisorHeight b : ℤ) := by
  have hB : (1 : ℤ) ≤ divisorHeight b := by
    exact_mod_cast divisorHeight_pos b
  rcases j with ⟨sign, row⟩
  cases sign <;> cases row with
  | inl i =>
    simp only [rawOffset, abs_zero, abs_neg, abs_one]
    omega
  | inr i =>
    have hi := divisor_abs_lt_height b i
    have hil := neg_abs_le (b i)
    have hiu := le_abs_self (b i)
    simp only [rawOffset]
    apply abs_le.mpr
    constructor <;> omega

lemma base_exceeds_residual_bound (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) :
    ((divisorHeight b : ℤ) *
      affineThresholdCoefficient (rawConstraintMatrix A) : ℝ) <
        (realStabilizationBound A b : ℝ) := by
  rw [← rayThresholdCoefficient_cast]
  norm_cast
  unfold realStabilizationBound
  omega

lemma raw_feasibleBases_stable (A : Matrix (Fin s) (Fin n) ℤ)
    (b c : Fin s → ℤ) (t : ℝ) (ht : (realStabilizationBound A b : ℝ) ≤ t) :
    feasibleBases (rawConstraintMatrix A)
      (fun j => t * (rawSlope c j : ℝ) + rawOffset b j) =
    feasibleBases (rawConstraintMatrix A)
      (fun j => (realStabilizationBound A b : ℝ) * (rawSlope c j : ℝ) + rawOffset b j) := by
  exact affine_basic_feasibility_stable (rawConstraintMatrix A)
    (rawSlope c) (rawOffset b) (divisorHeight b) (by positivity) (rawOffset_bound b)
    t (realStabilizationBound A b)
    ((base_exceeds_residual_bound A b).trans_le ht) (base_exceeds_residual_bound A b)

theorem raw_fixed_vertex_representation (A : Matrix (Fin s) (Fin n) ℤ)
    (b c : Fin s → ℤ) (t : ℝ) (ht : (realStabilizationBound A b : ℝ) ≤ t) :
    rawPolytope A b c t =
      convexHull ℝ ((fun I =>
        t • basicSolution (rawConstraintMatrix A) (fun j => (rawSlope c j : ℝ)) I +
          basicSolution (rawConstraintMatrix A) (fun j => (rawOffset b j : ℝ)) I) ''
        feasibleBases (rawConstraintMatrix A)
          (fun j => (realStabilizationBound A b : ℝ) * (rawSlope c j : ℝ) +
            rawOffset b j)) := by
  change NormalProjective.halfspaceRegion
    (matrixRows ((rawConstraintMatrix A).map (Int.castRingHom ℝ)))
      (fun j => t * (rawSlope c j : ℝ) + rawOffset b j) = _
  rw [compact_halfspace_eq_convexHull_basicSolutions _ _ (rawPolytope_isCompact A b c t),
    raw_feasibleBases_stable A b c t ht]
  congr 1
  ext z
  simp only [Set.mem_image]
  apply exists_congr
  intro I
  rw [basicSolution_affine]

theorem rawPolytope_minkowski (A : Matrix (Fin s) (Fin n) ℤ)
    (b c : Fin s → ℤ) (t : ℝ) (ht : (realStabilizationBound A b : ℝ) ≤ t) :
    rawPolytope A b c t =
      rawPolytope A b c (realStabilizationBound A b) +
        (t - realStabilizationBound A b) • slopePolytope A c := by
  exact parametric_region_minkowski
    (matrixRows ((rawConstraintMatrix A).map (Int.castRingHom ℝ)))
    (fun j => (rawSlope c j : ℝ)) (fun j => (rawOffset b j : ℝ))
    (feasibleBases (rawConstraintMatrix A)
      (fun j => (realStabilizationBound A b : ℝ) * (rawSlope c j : ℝ) + rawOffset b j))
    (basicSolution (rawConstraintMatrix A) (fun j => (rawSlope c j : ℝ)))
    (basicSolution (rawConstraintMatrix A) (fun j => (rawOffset b j : ℝ)))
    (realStabilizationBound A b) (raw_fixed_vertex_representation A b c) t ht

def slopeVertices (A : Matrix (Fin s) (Fin n) ℤ)
    (c : Fin s → ℤ) : Finset (Fin n → ℝ) := by
  classical
  exact (Finset.univ.filter (fun I => I ∈ feasibleBases (rawConstraintMatrix A)
    (fun j => (rawSlope c j : ℝ)))).image
      (basicSolution (rawConstraintMatrix A) (fun j => (rawSlope c j : ℝ)))

lemma slopeVertices_coe (A : Matrix (Fin s) (Fin n) ℤ) (c : Fin s → ℤ) :
    (slopeVertices A c : Set (Fin n → ℝ)) =
      basicSolution (rawConstraintMatrix A) (fun j => (rawSlope c j : ℝ)) ''
        feasibleBases (rawConstraintMatrix A) (fun j => (rawSlope c j : ℝ)) := by
  classical
  ext x
  simp [slopeVertices]

lemma slopePolytope_eq_convexHull (A : Matrix (Fin s) (Fin n) ℤ)
    (c : Fin s → ℤ) :
    slopePolytope A c = convexHull ℝ (slopeVertices A c : Set (Fin n → ℝ)) := by
  rw [slopeVertices_coe]
  exact compact_halfspace_eq_convexHull_basicSolutions _ _ (slopePolytope_isCompact A c)

lemma slope_vertex_denominator (A : Matrix (Fin s) (Fin n) ℤ)
    (c : Fin s → ℤ) (v : Fin n → ℝ) (hv : v ∈ slopeVertices A c) :
    (rayPeriod A : ℝ) • v ∈ integerLattice n := by
  classical
  unfold slopeVertices at hv
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hv
  have hI' : I ∈ feasibleBases (rawConstraintMatrix A)
      (fun j => (rawSlope c j : ℝ)) := (Finset.mem_filter.mp hI).2
  have hd : (basicMatrix (rawConstraintMatrix A) I).det ∣ (rayPeriod A : ℤ) := by
    exact signedRows_minor_dvd_period (augmentedRayMatrix A) I hI'.1
  obtain ⟨z, hz⟩ := integral_multiple_of_solution
    (basicMatrix (rawConstraintMatrix A) I) (fun k => rawSlope c (I k))
    (basicSolution (rawConstraintMatrix A) (fun j => (rawSlope c j : ℝ)) I)
    (basicSolution_solves _ _ I hI'.1) (rayPeriod A) hd
  refine ⟨z, ?_⟩
  intro i
  simpa using hz i

/-- Full raw-coefficient periodicity in Theorem 7.2, for every integer matrix,
every divisor coefficient vector, and every dimension. The period is the exact
lcm of nonzero maximal minors of the ray matrix with the identity adjoined.
This theorem concerns literal coefficients; the derived generation conclusion
requires the separate categorical theorem of the manuscript. -/
theorem paper_theorem_7_2_raw (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) (ell : ℕ) (hell : periodicityBound A b ≤ ell) :
    rawCoefficients A b ((ell + rayPeriod A : ℕ) : ℤ) =
      rawCoefficients A b (ell : ℤ) := by
  classical
  have hb : realStabilizationBound A b ≤ ell := by
    unfold periodicityBound at hell
    omega
  have hep : 0 < ell := (realStabilizationBound_pos A b).trans_le hb
  ext c
  rw [← rawPolytope_integerPoint_iff A b c (ell + rayPeriod A) (by omega),
    ← rawPolytope_integerPoint_iff A b c ell hep]
  by_cases hv : (slopeVertices A c).Nonempty
  · obtain ⟨q, hq⟩ := hv
    have hqc : q ∈ convexHull ℝ (slopeVertices A c : Set (Fin n → ℝ)) :=
      subset_convexHull ℝ _ hq
    apply rational_expansion_eventually_periodic
      (integerLattice n) (slopeVertices A c) q hqc (rayPeriod A) (rayPeriod_pos A)
      (slope_vertex_denominator A c) (slope_vertex_denominator A c q hq)
      (rawPolytope A b c (realStabilizationBound A b))
      (fun m => rawPolytope A b c (m : ℝ)) (realStabilizationBound A b)
    · intro m hm
      have hmr : (realStabilizationBound A b : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      rw [rawPolytope_minkowski A b c m hmr, slopePolytope_eq_convexHull]
      simp only [Nat.cast_sub hm]
    · simpa [periodicityBound] using hell
  · have hv0 : slopeVertices A c = ∅ := Finset.not_nonempty_iff_eq_empty.mp hv
    have hQ : slopePolytope A c = ∅ := by
      rw [slopePolytope_eq_convexHull, hv0]
      simp
    have hempty (m : ℕ) (hm : realStabilizationBound A b ≤ m) :
        rawPolytope A b c m = ∅ := by
      rw [rawPolytope_minkowski A b c m (by exact_mod_cast hm), hQ]
      simp
    rw [hempty (ell + rayPeriod A) (by omega), hempty ell hb]

/-- Integer-indexed form of the same unrestricted theorem. Positivity is
deduced from the explicit bound; passing through natural numbers loses no
integer exponent covered by the manuscript. -/
theorem paper_theorem_7_2_raw_int (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) (ell : ℤ) (hell : (periodicityBound A b : ℤ) ≤ ell) :
    rawCoefficients A b (ell + (rayPeriod A : ℤ)) = rawCoefficients A b ell := by
  have hn : 0 ≤ ell := (Int.natCast_nonneg _).trans hell
  have hnat : periodicityBound A b ≤ ell.toNat := by omega
  have h := paper_theorem_7_2_raw A b ell.toNat hnat
  simpa only [Nat.cast_add, Int.toNat_of_nonneg hn] using h

end ToricPower
