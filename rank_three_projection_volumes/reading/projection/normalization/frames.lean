module
public import Projection.Normalization.Compactification
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Invertible frames and coordinate marked arrays

Invertible marks are dense, by the finite zero set of the characteristic
polynomial. An invertible marked frame can be pulled back to the standard
coordinate frame while rescaling the repeated body by the exact determinant
power. This proves the marked compactification for standard coordinate marks.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Metric Module MeasureTheory
open scoped Topology Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

def standardMarks (n : ℕ) : Fin n → Space n := fun i => Pi.single i 1

def invertibleMarks (n : ℕ) : Set (Fin n → Space n) :=
  {U | (columnsMatrix U).det ≠ 0}

def basisMarkedLocus (n k : ℕ) : Set (Deleted n k → ℝ) :=
  Set.range (fun K : Body n => allMarkedArray (k := k) K (standardMarks n))

/-- Density of genuinely invertible marked-vector matrices. The only excluded
shift parameters are roots of one nonzero characteristic polynomial. -/
theorem dense_invertibleMarks (n : ℕ) : Dense (invertibleMarks n) := by
  intro U
  let M := columnsMatrix U
  let f : ℝ → Fin n → Space n := fun t i => U i + t • standardMarks n i
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfzero : f 0 = U := by
    funext i
    simp only [f, zero_smul, add_zero]
  have hmatrix (t : ℝ) : columnsMatrix (f t) = Matrix.scalar (Fin n) t + M := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [columnsMatrix, f, standardMarks, Matrix.scalar_apply, Matrix.diagonal_apply,
        Pi.single_apply, add_comm, M]
    · simp [columnsMatrix, f, standardMarks, Matrix.scalar_apply, Matrix.diagonal_apply,
        Pi.single_apply, hij, Ne.symm hij, add_comm, M]
  have hfinite : Set.Finite {t : ℝ | Polynomial.IsRoot (-M).charpoly t} :=
    Polynomial.finite_setOfPred_isRoot (-M).charpoly_monic.ne_zero
  have hdense : Dense {t : ℝ | (-M).charpoly.eval t ≠ 0} := by
    convert (dense_univ : Dense (Set.univ : Set ℝ)).sdiff_finite hfinite using 1
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, true_and, Polynomial.IsRoot]
  have hmaps : MapsTo f {t : ℝ | (-M).charpoly.eval t ≠ 0} (invertibleMarks n) := by
    intro t ht
    change (-M).charpoly.eval t ≠ 0 at ht
    change (columnsMatrix (f t)).det ≠ 0
    rw [hmatrix]
    simpa only [Matrix.eval_charpoly, sub_neg_eq_add] using ht
  have hclosure := map_mem_closure hf (hdense (0 : ℝ)) hmaps
  simpa only [hfzero] using hclosure

/-- Pull an actual invertible marked frame back to standard coordinate marks.
The factor on the repeated body is `|det A|^(1/(n-k))`. -/
theorem invertible_frame_pullback {n k : ℕ} (hkn : k < n)
    (K : Body n) (U : Fin n → Space n) (hU : U ∈ invertibleMarks n) :
    ∃ L : Body n, allMarkedArray (k := k) L (standardMarks n) = allMarkedArray K U := by
  let A := columnsLinear U
  have hA : LinearMap.det A.toLinearMap ≠ 0 := by
    rw [columnsLinear_det]
    exact hU
  let e : Space n ≃L[ℝ] Space n := A.toContinuousLinearEquivOfDetNeZero hA
  let d : ℝ := |LinearMap.det A.toLinearMap|
  have hd : 0 < d := abs_pos.mpr hA
  let r : ℝ := d ^ ((n - k : ℕ) : ℝ)⁻¹
  have hr : 0 < r := Real.rpow_pos_of_pos hd _
  have hnk : n - k ≠ 0 := (Nat.sub_pos_of_lt hkn).ne'
  have hpow : r ^ (n - k) = d := Real.rpow_inv_natCast_pow hd.le hnk
  have hmark (i : Fin n) : e.symm (U i) = standardMarks n i := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (columnsLinear_basis U i).symm
  have hdet : |LinearMap.det e.symm.toContinuousLinearMap.toLinearMap| = d⁻¹ := by
    rw [ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
      ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.det_coe_symm, abs_inv]
    rfl
  have hmarks : (fun i => e.symm.toContinuousLinearMap (U i)) = standardMarks n := by
    funext i
    exact hmark i
  refine ⟨r • mapBody e.symm.toContinuousLinearMap K, ?_⟩
  funext I
  have hmap : allMarkedArray (mapBody e.symm.toContinuousLinearMap K) (standardMarks n) I =
      d⁻¹ * allMarkedArray K U I := by
    simpa only [hmarks, hdet] using allMarkedArray_map K U e.symm.toContinuousLinearMap I
  rw [allMarkedArray_smul_body _ _ r hr.le, hmap, hpow, ← mul_assoc,
    mul_inv_cancel₀ hd.ne', one_mul]

theorem marked_mem_closure_basisMarked {n k : ℕ} (hkn : k < n)
    (K : Body n) (U : Fin n → Space n) :
    allMarkedArray (k := k) K U ∈ closure (basisMarkedLocus n k) := by
  let f : (Fin n → Space n) → Deleted n k → ℝ := fun V => allMarkedArray K V
  have hf : Continuous f := by
    simpa only [f, Function.comp_def, id_eq] using
      (continuous_allMarkedArray (n := n) (k := k)).comp
        ((continuous_const : Continuous (fun _ : Fin n → Space n => K)).prodMk continuous_id)
  apply map_mem_closure (f := f) (x := U) hf (dense_invertibleMarks n U)
  intro V hV
  obtain ⟨L, hL⟩ := invertible_frame_pullback hkn K V hV
  exact ⟨L, hL⟩

theorem closure_basisMarkedLocus_eq_markedArrayLocus {n k : ℕ}
    (hk : 0 < k) (hkn : k < n) :
    closure (basisMarkedLocus n k) = markedArrayLocus n k := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (isClosed_markedArrayLocus hk hkn.le)
    rintro _ ⟨K, rfl⟩
    exact ⟨(K, standardMarks n), rfl⟩
  · rintro _ ⟨⟨K, U⟩, rfl⟩
    exact marked_mem_closure_basisMarked hkn K U

/-- Theorem 3.1's compactification expressed with genuine mixed volumes and
standard coordinate marks. Coordinate extrusion identifies `basisMarkedLocus`
with the paper's literal coordinate projection-volume locus. -/
theorem basis_marked_compactification {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (P : Deleted n k → ℝ) :
    P ∈ closure (basisMarkedLocus n k) ↔
      ∃ (K : Body n) (U : Fin n → Space n),
        n - k + 1 ≤ bodyDimension K ∧ allMarkedArray K U = P := by
  rw [closure_basisMarkedLocus_eq_markedArrayLocus hk hkn]
  constructor
  · exact marked_representation_with_dimension hk hkn.le
  · rintro ⟨K, U, _hdim, hKU⟩
    exact ⟨(K, U), hKU⟩

end RankThreeProjection
