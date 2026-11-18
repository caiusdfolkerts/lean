module

public import ToricPower.AffineFeasibility

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n s : ℕ}

abbrev RawRow (n s : ℕ) := Bool × (Fin n ⊕ Fin s)

def rawConstraintMatrix (A : Matrix (Fin s) (Fin n) ℤ) :
    Matrix (RawRow n s) (Fin n) ℤ :=
  signedRows (augmentedRayMatrix A)

def rawSlope (c : Fin s → ℤ) : RawRow n s → ℤ
  | (false, Sum.inl _) => 0
  | (true, Sum.inl _) => 1
  | (false, Sum.inr i) => -c i
  | (true, Sum.inr i) => c i + 1

def rawOffset (b : Fin s → ℤ) : RawRow n s → ℤ
  | (false, Sum.inl _) => 0
  | (true, Sum.inl _) => -1
  | (false, Sum.inr i) => b i
  | (true, Sum.inr i) => -b i - 1

def realRayMap (A : Matrix (Fin s) (Fin n) ℤ) (x : Fin n → ℝ) : Fin s → ℝ :=
  A.map (Int.castRingHom ℝ) *ᵥ x

def rawPolytope (A : Matrix (Fin s) (Fin n) ℤ) (b c : Fin s → ℤ)
    (t : ℝ) : Set (Fin n → ℝ) :=
  parametricRegion (matrixRows ((rawConstraintMatrix A).map (Int.castRingHom ℝ)))
    (fun j => (rawSlope c j : ℝ)) (fun j => (rawOffset b j : ℝ)) t

def slopePolytope (A : Matrix (Fin s) (Fin n) ℤ) (c : Fin s → ℤ) :
    Set (Fin n → ℝ) :=
  slopeRegion (matrixRows ((rawConstraintMatrix A).map (Int.castRingHom ℝ)))
    (fun j => (rawSlope c j : ℝ))

@[simp] lemma matrixRows_raw_negative_coordinate
    (A : Matrix (Fin s) (Fin n) ℤ) (j : Fin n) (x : Fin n → ℝ) :
    matrixRows ((rawConstraintMatrix A).map (Int.castRingHom ℝ)) (false, Sum.inl j) x =
      -x j := by
  simp [matrixRows, rawConstraintMatrix, signedRows, augmentedRayMatrix,
    constraintSign, Matrix.mulVec, dotProduct]

@[simp] lemma matrixRows_raw_positive_coordinate
    (A : Matrix (Fin s) (Fin n) ℤ) (j : Fin n) (x : Fin n → ℝ) :
    matrixRows ((rawConstraintMatrix A).map (Int.castRingHom ℝ)) (true, Sum.inl j) x =
      x j := by
  simp [matrixRows, rawConstraintMatrix, signedRows, augmentedRayMatrix,
    constraintSign, Matrix.mulVec, dotProduct]

@[simp] lemma matrixRows_raw_negative_ray
    (A : Matrix (Fin s) (Fin n) ℤ) (i : Fin s) (x : Fin n → ℝ) :
    matrixRows ((rawConstraintMatrix A).map (Int.castRingHom ℝ)) (false, Sum.inr i) x =
      -realRayMap A x i := by
  simp [matrixRows, rawConstraintMatrix, signedRows, augmentedRayMatrix,
    constraintSign, realRayMap, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]

@[simp] lemma matrixRows_raw_positive_ray
    (A : Matrix (Fin s) (Fin n) ℤ) (i : Fin s) (x : Fin n → ℝ) :
    matrixRows ((rawConstraintMatrix A).map (Int.castRingHom ℝ)) (true, Sum.inr i) x =
      realRayMap A x i := by
  simp [matrixRows, rawConstraintMatrix, signedRows, augmentedRayMatrix,
    constraintSign, realRayMap, Matrix.mulVec, dotProduct]

lemma mem_rawPolytope_iff (A : Matrix (Fin s) (Fin n) ℤ)
    (b c : Fin s → ℤ) (t : ℝ) (x : Fin n → ℝ) :
    x ∈ rawPolytope A b c t ↔
      (∀ j, 0 ≤ x j ∧ x j ≤ t - 1) ∧
      ∀ i, t * (c i : ℝ) ≤ (b i : ℝ) + realRayMap A x i ∧
        (b i : ℝ) + realRayMap A x i ≤ t * ((c i : ℝ) + 1) - 1 := by
  constructor
  · intro h
    constructor
    · intro j
      have hl := h (false, Sum.inl j)
      have hu := h (true, Sum.inl j)
      simp only [matrixRows_raw_negative_coordinate, matrixRows_raw_positive_coordinate,
        rawSlope, rawOffset, Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero,
        mul_one, add_zero] at hl hu
      constructor <;> linarith
    · intro i
      have hl := h (false, Sum.inr i)
      have hu := h (true, Sum.inr i)
      simp only [matrixRows_raw_negative_ray, matrixRows_raw_positive_ray,
        rawSlope, rawOffset, Int.cast_add, Int.cast_sub, Int.cast_one,
        Int.cast_neg, mul_neg] at hl hu
      constructor <;> linarith
  · rintro ⟨hx, hA⟩ ⟨sign, row⟩
    cases sign <;> cases row with
    | inl j =>
      have hj := hx j
      simp only [matrixRows_raw_negative_coordinate, matrixRows_raw_positive_coordinate,
        rawSlope, rawOffset, Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero,
        mul_one, add_zero]
      linarith
    | inr i =>
      have hi := hA i
      simp only [matrixRows_raw_negative_ray, matrixRows_raw_positive_ray,
        rawSlope, rawOffset, Int.cast_add, Int.cast_sub, Int.cast_one,
        Int.cast_neg, mul_neg]
      linarith

lemma mem_slopePolytope_iff (A : Matrix (Fin s) (Fin n) ℤ)
    (c : Fin s → ℤ) (x : Fin n → ℝ) :
    x ∈ slopePolytope A c ↔
      (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
      ∀ i, (c i : ℝ) ≤ realRayMap A x i ∧ realRayMap A x i ≤ (c i : ℝ) + 1 := by
  constructor
  · intro h
    constructor
    · intro j
      have hl := h (false, Sum.inl j)
      have hu := h (true, Sum.inl j)
      simp only [matrixRows_raw_negative_coordinate, matrixRows_raw_positive_coordinate,
        rawSlope, Int.cast_zero, Int.cast_one] at hl hu
      constructor <;> linarith
    · intro i
      have hl := h (false, Sum.inr i)
      have hu := h (true, Sum.inr i)
      simp only [matrixRows_raw_negative_ray, matrixRows_raw_positive_ray,
        rawSlope, Int.cast_add, Int.cast_one, Int.cast_neg] at hl hu
      constructor <;> linarith
  · rintro ⟨hx, hA⟩ ⟨sign, row⟩
    cases sign <;> cases row with
    | inl j =>
      have hj := hx j
      simp only [matrixRows_raw_negative_coordinate, matrixRows_raw_positive_coordinate,
        rawSlope, Int.cast_zero, Int.cast_one]
      linarith
    | inr i =>
      have hi := hA i
      simp only [matrixRows_raw_negative_ray, matrixRows_raw_positive_ray,
        rawSlope, Int.cast_add, Int.cast_one, Int.cast_neg]
      linarith

lemma rawPolytope_isCompact (A : Matrix (Fin s) (Fin n) ℤ)
    (b c : Fin s → ℤ) (t : ℝ) : IsCompact (rawPolytope A b c t) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Fin n → ℝ) (fun _ => t - 1))).of_isClosed_subset
  · exact NormalProjective.isClosed_halfspaceRegion _ _
  · intro x hx
    have hc := (mem_rawPolytope_iff A b c t x).mp hx
    exact ⟨fun j => (hc.1 j).1, fun j => (hc.1 j).2⟩

lemma slopePolytope_isCompact (A : Matrix (Fin s) (Fin n) ℤ)
    (c : Fin s → ℤ) : IsCompact (slopePolytope A c) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Fin n → ℝ) (1 : Fin n → ℝ))).of_isClosed_subset
  · exact NormalProjective.isClosed_halfspaceRegion _ _
  · intro x hx
    have hc := (mem_slopePolytope_iff A c x).mp hx
    exact ⟨fun j => (hc.1 j).1, fun j => (hc.1 j).2⟩

@[simp] lemma realRayMap_integer (A : Matrix (Fin s) (Fin n) ℤ)
    (u : Fin n → ℤ) (i : Fin s) :
    realRayMap A (fun j => (u j : ℝ)) i = (rayMap A u i : ℝ) := by
  simp [realRayMap, rayMap, Matrix.mulVec, dotProduct]

/-- Integer feasibility is exactly raw coefficient membership, with the strict
upper floor boundary represented by the integer subtraction of one. -/
theorem rawPolytope_integerPoint_iff (A : Matrix (Fin s) (Fin n) ℤ)
    (b c : Fin s → ℤ) (ell : ℕ) (hell : 0 < ell) :
    (rawPolytope A b c ell ∩ (integerLattice n : Set (Fin n → ℝ))).Nonempty ↔
      c ∈ rawCoefficients A b (ell : ℤ) := by
  have hellZ : (0 : ℤ) < ell := by exact_mod_cast hell
  rw [rawCoefficients_iff_feasible A b c ell hellZ]
  constructor
  · rintro ⟨x, hx, u, hu⟩
    have hxu : (fun j => (u j : ℝ)) = x := funext hu
    rw [← hxu] at hx
    have h := (mem_rawPolytope_iff A b c ell _).mp hx
    simp only [realRayMap_integer] at h
    refine ⟨u, ?_, ?_⟩
    · intro j
      exact_mod_cast h.1 j
    · intro i
      exact_mod_cast h.2 i
  · rintro ⟨u, hu, hA⟩
    refine ⟨fun j => (u j : ℝ), ?_, u, fun _ => rfl⟩
    rw [mem_rawPolytope_iff]
    simp only [realRayMap_integer]
    constructor
    · intro j
      exact_mod_cast hu j
    · intro i
      exact_mod_cast hA i

end ToricPower
