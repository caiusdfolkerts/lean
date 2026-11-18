module

public import ToricPower.Circuits

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n s : ℕ}

abbrev OrthantRow (n s : ℕ) := (Bool × Fin n) ⊕ (Fin s ⊕ Bool)

def orthantMatrix (A : Matrix (Fin s) (Fin n) ℤ) (sign : Fin s → ℤ) :
    Matrix (OrthantRow n s) (Fin s) ℤ
  | Sum.inl (false, j), i => A i j
  | Sum.inl (true, j), i => -A i j
  | Sum.inr (Sum.inl j), i => if i = j then -sign j else 0
  | Sum.inr (Sum.inr false), i => sign i
  | Sum.inr (Sum.inr true), i => -sign i

def orthantRhs : OrthantRow n s → ℤ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr false) => 1
  | Sum.inr (Sum.inr true) => -1

def orthantKernel (A : Matrix (Fin s) (Fin n) ℤ) (sign : Fin s → ℤ) :
    Set (Fin s → ℝ) :=
  NormalProjective.halfspaceRegion (matrixRows ((orthantMatrix A sign).map (Int.castRingHom ℝ)))
    (fun i => (orthantRhs i : ℝ))

@[simp] theorem orthant_row_kernel_pos (A : Matrix (Fin s) (Fin n) ℤ)
    (sign : Fin s → ℤ) (j : Fin n) (x : Fin s → ℝ) :
    matrixRows ((orthantMatrix A sign).map (Int.castRingHom ℝ)) (Sum.inl (false, j)) x =
      ∑ i, (A i j : ℝ) * x i := by
  simp [matrixRows, realMatrix, orthantMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem orthant_row_kernel_neg (A : Matrix (Fin s) (Fin n) ℤ)
    (sign : Fin s → ℤ) (j : Fin n) (x : Fin s → ℝ) :
    matrixRows ((orthantMatrix A sign).map (Int.castRingHom ℝ)) (Sum.inl (true, j)) x =
      -(∑ i, (A i j : ℝ) * x i) := by
  simp [matrixRows, realMatrix, orthantMatrix, Matrix.mulVec, dotProduct,
    Finset.sum_neg_distrib]

@[simp] theorem orthant_row_sign (A : Matrix (Fin s) (Fin n) ℤ)
    (sign : Fin s → ℤ) (j : Fin s) (x : Fin s → ℝ) :
    matrixRows ((orthantMatrix A sign).map (Int.castRingHom ℝ)) (Sum.inr (Sum.inl j)) x =
      -(sign j : ℝ) * x j := by
  simp [matrixRows, realMatrix, orthantMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem orthant_row_norm_pos (A : Matrix (Fin s) (Fin n) ℤ)
    (sign : Fin s → ℤ) (x : Fin s → ℝ) :
    matrixRows ((orthantMatrix A sign).map (Int.castRingHom ℝ)) (Sum.inr (Sum.inr false)) x =
      ∑ i, (sign i : ℝ) * x i := by
  simp [matrixRows, realMatrix, orthantMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem orthant_row_norm_neg (A : Matrix (Fin s) (Fin n) ℤ)
    (sign : Fin s → ℤ) (x : Fin s → ℝ) :
    matrixRows ((orthantMatrix A sign).map (Int.castRingHom ℝ)) (Sum.inr (Sum.inr true)) x =
      -(∑ i, (sign i : ℝ) * x i) := by
  simp [matrixRows, realMatrix, orthantMatrix, Matrix.mulVec, dotProduct,
    Finset.sum_neg_distrib]

theorem mem_orthantKernel_iff (A : Matrix (Fin s) (Fin n) ℤ)
    (sign : Fin s → ℤ) (x : Fin s → ℝ) :
    x ∈ orthantKernel A sign ↔
      (∀ j, ∑ i, (A i j : ℝ) * x i = 0) ∧
      (∀ i, 0 ≤ (sign i : ℝ) * x i) ∧
      ∑ i, (sign i : ℝ) * x i = 1 := by
  constructor
  · intro hx
    have hx' : ∀ r, matrixRows ((orthantMatrix A sign).map (Int.castRingHom ℝ)) r x ≤
        (orthantRhs r : ℝ) := hx
    refine ⟨?_, ?_, ?_⟩
    · intro j
      have hp := hx' (Sum.inl (false, j))
      have hm := hx' (Sum.inl (true, j))
      simp only [orthant_row_kernel_pos, orthant_row_kernel_neg, orthantRhs,
        Int.cast_zero] at hp hm
      linarith
    · intro i
      have hi := hx' (Sum.inr (Sum.inl i))
      simp only [orthant_row_sign, orthantRhs, Int.cast_zero] at hi
      linarith
    · have hp := hx' (Sum.inr (Sum.inr false))
      have hm := hx' (Sum.inr (Sum.inr true))
      simp only [orthant_row_norm_pos, orthant_row_norm_neg, orthantRhs,
        Int.cast_one, Int.cast_neg] at hp hm
      linarith
  · rintro ⟨hker, hsign, hnorm⟩
    intro r
    rcases r with ⟨b,j⟩ | (i | b)
    · cases b <;> simp only [orthant_row_kernel_pos, orthant_row_kernel_neg,
        orthantRhs, Int.cast_zero, hker, neg_zero, le_refl]
    · simpa only [orthant_row_sign, orthantRhs, Int.cast_zero, neg_mul,
        neg_nonpos] using hsign i
    · cases b <;> simp only [orthant_row_norm_pos, orthant_row_norm_neg, orthantRhs,
        Int.cast_one, Int.cast_neg, hnorm, le_refl]

theorem isCompact_orthantKernel (A : Matrix (Fin s) (Fin n) ℤ)
    (sign : Fin s → ℤ) (hsign : ∀ i, sign i = 1 ∨ sign i = -1) :
    IsCompact (orthantKernel A sign) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (-1 : Fin s → ℝ) 1)).of_isClosed_subset
    (NormalProjective.isClosed_halfspaceRegion _ _)
  intro x hx
  obtain ⟨_, hp, hn⟩ := (mem_orthantKernel_iff A sign x).mp hx
  have hu (i : Fin s) : (sign i : ℝ) * x i ≤ 1 := by
    rw [← hn]
    exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · change (-1 : ℝ) ≤ x i
    rcases hsign i with hi | hi
    · have hh := hp i
      simp only [hi, Int.cast_one, one_mul] at hh
      change (-1 : ℝ) ≤ x i
      linarith
    · have hh := hu i
      simp [hi] at hh
      linarith
  · change x i ≤ (1 : ℝ)
    rcases hsign i with hi | hi
    · simpa [hi] using hu i
    · have hh := hp i
      simp [hi] at hh
      linarith

/-- At an extreme point, the relations supported on its nonzero coordinates
form a one-dimensional real vector space. -/
theorem orthant_extreme_supported_relation
    (A : Matrix (Fin s) (Fin n) ℤ) (sign : Fin s → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    {q : Fin s → ℝ} (hq : q ∈ (orthantKernel A sign).extremePoints ℝ)
    (k : Fin s → ℝ) (hk : ∀ j, ∑ i, (A i j : ℝ) * k i = 0)
    (hs : Function.support k ⊆ Function.support q) :
    k = (∑ i, (sign i : ℝ) * k i) • q := by
  let l : ℝ := ∑ i, (sign i : ℝ) * k i
  let v := k - l • q
  have hqdata := (mem_orthantKernel_iff A sign q).mp hq.1
  have hker (j : Fin n) : ∑ i, (A i j : ℝ) * v i = 0 := by
    dsimp [v]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib]
    have heq : (∑ i, (A i j : ℝ) * (l * q i)) =
        l * ∑ i, (A i j : ℝ) * q i := by
      rw [Finset.mul_sum]
      congr 1
      ext i
      ring
    rw [heq, hk j, hqdata.1 j]
    ring
  have hnorm : ∑ i, (sign i : ℝ) * v i = 0 := by
    dsimp [v]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib]
    have heq : (∑ i, (sign i : ℝ) * (l * q i)) =
        l * ∑ i, (sign i : ℝ) * q i := by
      rw [Finset.mul_sum]
      congr 1
      ext i
      ring
    rw [heq, hqdata.2.2]
    dsimp [l]
    ring
  have hv : v = 0 := by
    apply NormalProjective.active_normals_separate
      (matrixRows ((orthantMatrix A sign).map (Int.castRingHom ℝ)))
      (fun i => (orthantRhs i : ℝ)) hq
    intro r hr
    rcases r with ⟨b,j⟩ | (i | b)
    · cases b <;> simp only [orthant_row_kernel_pos, orthant_row_kernel_neg,
        hker, neg_zero]
    · have hqi : q i = 0 := by
        have hz : (sign i : ℝ) * q i = 0 := by
          simpa only [orthant_row_sign, orthantRhs, Int.cast_zero, neg_mul,
            neg_eq_zero] using hr
        have hs0 : (sign i : ℝ) ≠ 0 := by
          rcases hsign i with h | h <;> simp [h]
        exact (mul_eq_zero.mp hz).resolve_left hs0
      have hki : k i = 0 := by
        by_contra hn
        exact (hs hn) hqi
      rw [orthant_row_sign]
      simp [v, hqi, hki]
    · cases b <;> simp only [orthant_row_norm_pos, orthant_row_norm_neg,
        hnorm, neg_zero]
  exact sub_eq_zero.mp hv

/-- Every extreme point has a positive integral multiple in the integer lattice. -/
theorem orthant_extreme_integral_multiple
    (A : Matrix (Fin s) (Fin n) ℤ) (sign : Fin s → ℤ)
    {q : Fin s → ℝ} (hq : q ∈ (orthantKernel A sign).extremePoints ℝ) :
    ∃ (D : ℕ) (z : Fin s → ℤ), 0 < D ∧
      (fun i => (z i : ℝ)) = (D : ℝ) • q := by
  obtain ⟨I, hI, hqI⟩ := extremePoint_is_basicSolution
    (orthantMatrix A sign) (fun i => (orthantRhs i : ℝ)) q hq
  let B := basicMatrix (orthantMatrix A sign) I
  have hdet : B.det ≠ 0 := hI.1
  have hsolve : realMatrix B *ᵥ q = fun i => (orthantRhs (I i) : ℝ) := by
    rw [hqI]
    exact basicSolution_solves _ _ _ hI.1
  have hdiv : B.det ∣ (B.det.natAbs : ℤ) := Int.dvd_natAbs.mpr (dvd_refl _)
  obtain ⟨z, hz⟩ := integral_multiple_of_solution B
    (fun i => orthantRhs (I i)) q hsolve (B.det.natAbs : ℤ) hdiv
  refine ⟨B.det.natAbs, z, Int.natAbs_pos.mpr hdet, ?_⟩
  ext i
  simpa only [Pi.smul_apply, smul_eq_mul, Int.cast_natCast] using hz i

end ToricPower

