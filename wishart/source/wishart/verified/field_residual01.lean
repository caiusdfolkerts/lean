module

public import wishart.verified.field_analytic01
public import wishart.verified.real_remainder09
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import tau_ceti.analysis.matrix.eigenvalues
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Logic.Equiv.Fin.Basic
public import wishart.verified.field_frontier01
public import tau_ceti.representation_theory.compact.haar
public import Mathlib.Topology.Algebra.Star.Unitary
public import wishart.verified.field_frontier02
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/- Recovered canonical proof stage; see verification/recovery-patches.json. -/

@[expose] public section

set_option maxErrors 1000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000

section CanonicalSource0
/- Source: Wishart/FieldSpectralVariational.lean -/




/-!
# Complex orthonormal compression and leading eigenvalue products

Cauchy–Binet expresses a compressed determinant as a convex combination of
spectral minors.  For a complex frame the weights are the squared norms of
its maximal minors.  The argument includes zero eigenvalues and the empty
compression; no positive-definiteness approximation is used.
-/

noncomputable section
open Matrix Set Set.powersetCard
open scoped Classical ComplexOrder Matrix.Norms.L2Operator

namespace Wishart.FieldSpectral

variable {𝕜 : Type*} [RCLike 𝕜]

open Wishart.Spectral

theorem minorCoordinate_star {j p : ℕ}
    (V : Matrix (Fin p) (Fin j) 𝕜) (s : powersetCard (Fin p) j) :
    minorCoordinate Vᵀ.row s = star (minorCoordinate Vᴴ.row s) := by
  rw [minorCoordinate_apply, minorCoordinate_apply]
  change _ = (starRingEnd 𝕜) _
  rw [(starRingEnd 𝕜).map_det]
  congr 1
  ext i k
  simp [Matrix.row_eq_self, Matrix.transpose_apply, Matrix.conjTranspose_apply]

theorem minorCoordinate_mul_real_diagonal {j p : ℕ}
    (A : Matrix (Fin j) (Fin p) 𝕜) (lam : Fin p → ℝ)
    (s : powersetCard (Fin p) j) :
    minorCoordinate (A * Matrix.diagonal (fun i => (lam i : 𝕜))).row s =
      (∏ i : Fin j, (lam (ofFinEmbEquiv.symm s i) : 𝕜)) *
        minorCoordinate A.row s := by
  rw [minorCoordinate_apply, minorCoordinate_apply]
  convert Matrix.det_mul_row (fun i : Fin j => (lam (ofFinEmbEquiv.symm s i) : 𝕜))
    (Matrix.of fun i k => A i (ofFinEmbEquiv.symm s k)) using 1
  · congr 1
    ext i k
    change (A * Matrix.diagonal (fun i => (lam i : 𝕜))) i _ = _
    simp only [Matrix.mul_diagonal]
    exact mul_comm _ _
  · rfl

theorem det_diagonal_compression_eq_sum {j p : ℕ}
    (V : Matrix (Fin p) (Fin j) 𝕜) (lam : Fin p → ℝ) :
    (Vᴴ * Matrix.diagonal (fun i => (lam i : 𝕜)) * V).det =
      ((∑ s : powersetCard (Fin p) j,
        ‖minorCoordinate Vᴴ.row s‖ ^ 2 *
          ∏ i : Fin j, lam (ofFinEmbEquiv.symm s i) : ℝ) : 𝕜) := by
  have h := det_mul_transpose_eq_sum_minors
    (Vᴴ * Matrix.diagonal (fun i => (lam i : 𝕜))).row Vᵀ.row
  change (Vᴴ * Matrix.diagonal (fun i => (lam i : 𝕜)) * V).det =
    ∑ s : powersetCard (Fin p) j, minorCoordinate (Vᴴ * Matrix.diagonal (fun i => (lam i : 𝕜))).row s * minorCoordinate Vᵀ.row s at h
  rw [h]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [minorCoordinate_mul_real_diagonal, minorCoordinate_star]
  change _ * (minorCoordinate Vᴴ.row s) * (starRingEnd 𝕜) (minorCoordinate Vᴴ.row s) = _
  rw [mul_assoc, RCLike.mul_conj, mul_comm]
  simp only [map_mul, map_pow, map_prod]

theorem sum_normSq_minors_of_orthonormal {j p : ℕ}
    (V : Matrix (Fin p) (Fin j) 𝕜) (hV : Vᴴ * V = 1) :
    (∑ s : powersetCard (Fin p) j, ‖minorCoordinate Vᴴ.row s‖ ^ 2) = 1 := by
  have h := det_diagonal_compression_eq_sum V (fun _ => 1)
  simp only [RCLike.ofReal_one, Matrix.diagonal_one, Matrix.mul_one,
    hV, Matrix.det_one, Finset.prod_const_one, mul_one] at h
  apply RCLike.ofReal_injective (K := 𝕜)
  simpa only [RCLike.ofReal_one] using h.symm

theorem det_diagonal_compression_le {j p : ℕ} (hj : j ≤ p)
    (V : Matrix (Fin p) (Fin j) 𝕜) (hV : Vᴴ * V = 1)
    {lam : Fin p → ℝ} (h0 : ∀ i, 0 ≤ lam i) (hmono : Antitone lam) :
    RCLike.re (Vᴴ * Matrix.diagonal (fun i => (lam i : 𝕜)) * V).det ≤
      ∏ i : Fin j, lam (Fin.castLE hj i) := by
  rw [det_diagonal_compression_eq_sum, RCLike.ofReal_re]
  calc
    _ ≤ ∑ s : powersetCard (Fin p) j,
        ‖minorCoordinate Vᴴ.row s‖ ^ 2 *
          ∏ i : Fin j, lam (Fin.castLE hj i) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left
        (spectral_minor_le_leading_product hj h0 hmono s) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, sum_normSq_minors_of_orthonormal V hV, one_mul]

def permutationUnitary {p : ℕ} (e : Equiv.Perm (Fin p)) :
    unitary (Matrix (Fin p) (Fin p) 𝕜) := by
  refine ⟨e.permMatrix 𝕜, ?_⟩
  change (e.permMatrix 𝕜)ᴴ * e.permMatrix 𝕜 = 1 ∧
    e.permMatrix 𝕜 * (e.permMatrix 𝕜)ᴴ = 1
  constructor <;> simp only [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
    inv_mul_cancel, mul_inv_cancel, Matrix.permMatrix_one]

theorem permutation_diagonal {p : ℕ} (e : Equiv.Perm (Fin p)) (lam : Fin p → ℝ) :
    (permutationUnitary (𝕜 := 𝕜) e : Matrix (Fin p) (Fin p) 𝕜) *
        Matrix.diagonal (fun i => (lam i : 𝕜)) * ((star (permutationUnitary (𝕜 := 𝕜) e)).val) =
      Matrix.diagonal (fun i => (lam (e i) : 𝕜)) := by
  change e.permMatrix 𝕜 * _ * (e.permMatrix 𝕜)ᴴ = _
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.diagonal_apply, Equiv.Perm.inv_def, e.injective.eq_iff]

def orderedIndex (p : ℕ) : Equiv.Perm (Fin p) :=
  (finCongr (Fintype.card_fin p).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin p))))

def orderedValues {p : ℕ} {A : Matrix (Fin p) (Fin p) 𝕜} (hA : A.IsHermitian) : Fin p → ℝ :=
  fun i => hA.eigenvalues₀ (Fin.cast (Fintype.card_fin p).symm i)

theorem orderedValues_eq {p : ℕ} {A : Matrix (Fin p) (Fin p) 𝕜}
    (hA : A.IsHermitian) : orderedValues hA = hA.eigenvalues ∘ orderedIndex p := by
  funext i
  simp [orderedValues, orderedIndex, Matrix.IsHermitian.eigenvalues]

theorem antitone_orderedValues {p : ℕ} {A : Matrix (Fin p) (Fin p) 𝕜}
    (hA : A.IsHermitian) : Antitone (orderedValues hA) :=
  fun _ _ h => hA.eigenvalues₀_antitone h

theorem exists_sorted_diagonalization {p : ℕ}
    {A : Matrix (Fin p) (Fin p) 𝕜} (hA : A.IsHermitian) :
    ∃ U : unitary (Matrix (Fin p) (Fin p) 𝕜),
      (star U.val) * A * U.val =
        Matrix.diagonal (fun i => (orderedValues hA i : 𝕜)) := by
  let O := hA.eigenvectorUnitary
  let P := permutationUnitary (𝕜 := 𝕜) (orderedIndex p)
  refine ⟨O * star P, ?_⟩
  have h : (star O.val) * A * O.val =
      Matrix.diagonal (fun i => (hA.eigenvalues i : 𝕜)) :=
    by
      dsimp only [O]
      have hh := hA.conjStarAlgAut_star_eigenvectorUnitary
      simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star, Function.comp_apply] at hh
      convert hh using 1 <;> rfl
  change star (O.val * star P.val) * A *
    (O.val * star P.val) = _
  simp only [Unitary.coe_star, star_mul, star_star]
  calc
    _ = P.val *
      ((star O.val) * A * O.val) * star P.val := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [h, orderedValues_eq]
      convert permutation_diagonal (𝕜 := 𝕜) (orderedIndex p) hA.eigenvalues using 1 <;> rfl


def coordinateFrame {j p : ℕ} (e : Fin j ↪ Fin p) : Matrix (Fin p) (Fin j) 𝕜 :=
  (1 : Matrix (Fin p) (Fin p) 𝕜).submatrix id e

theorem coordinateFrame_compression {j p : ℕ} (e : Fin j ↪ Fin p)
    (A : Matrix (Fin p) (Fin p) 𝕜) :
    (coordinateFrame (𝕜 := 𝕜) e)ᴴ * A * coordinateFrame e = A.submatrix e e := by
  unfold coordinateFrame
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change (1 : Matrix (Fin p) (Fin p) _).submatrix e (Equiv.refl (Fin p)) * A * (1 : Matrix (Fin p) (Fin p) _).submatrix (Equiv.refl (Fin p)) e = _
  rw [Matrix.one_submatrix_mul e (Equiv.refl (Fin p)) A,
    Matrix.mul_submatrix_one (Equiv.refl (Fin p)) e]
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp,
    Matrix.submatrix_submatrix, Function.comp_id]

theorem coordinateFrame_orthonormal {j p : ℕ} (e : Fin j ↪ Fin p) :
    (coordinateFrame (𝕜 := 𝕜) e)ᴴ * coordinateFrame (𝕜 := 𝕜) e = 1 := by
  simpa only [Matrix.mul_one, Matrix.submatrix_one_embedding] using
    coordinateFrame_compression (𝕜 := 𝕜) e (1 : Matrix (Fin p) (Fin p) 𝕜)

def OrthonormalFrame (𝕜 : Type*) [RCLike 𝕜] (p j : ℕ) :=
  {U : Matrix (Fin p) (Fin j) 𝕜 // Uᴴ * U = 1}

def compressionDeterminant {p j : ℕ} (A : Matrix (Fin p) (Fin p) 𝕜)
    (U : OrthonormalFrame 𝕜 p j) : ℝ := RCLike.re (U.valᴴ * A * U.val).det

def leadingEigenvalueProduct {p j : ℕ} (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) 𝕜} (hA : A.IsHermitian) : ℝ :=
  ∏ i : Fin j, orderedValues hA (Fin.castLE hj i)

theorem compression_le_of_sorted_diagonalization {p j : ℕ} (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) 𝕜} (O : unitary (Matrix (Fin p) (Fin p) 𝕜))
    {lam : Fin p → ℝ}
    (hdiag : (star O.val) * A * O.val =
      Matrix.diagonal (fun i => (lam i : 𝕜)))
    (h0 : ∀ i, 0 ≤ lam i) (hmono : Antitone lam)
    (U : OrthonormalFrame 𝕜 p j) :
    compressionDeterminant A U ≤ ∏ i : Fin j, lam (Fin.castLE hj i) := by
  let V := (star O.val) * U.val
  have hV : Vᴴ * V = 1 := by
    simp only [V, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    calc
      _ = U.valᴴ * (O.val * star O.val) * U.val := by
        simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
      _ = 1 := by rw [O.property.2, Matrix.mul_one, U.property]
  have heq : U.valᴴ * A * U.val =
      Vᴴ * Matrix.diagonal (fun i => (lam i : 𝕜)) * V := by
    rw [← hdiag]
    simp only [V, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    calc
      _ = U.valᴴ * (O.val * star O.val) * A *
          (O.val * star O.val) * U.val := by
            rw [O.property.2]
            simp
      _ = _ := by simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
  rw [compressionDeterminant, heq]
  exact det_diagonal_compression_le hj V hV h0 hmono

theorem exists_compression_eq_of_diagonalization {p j : ℕ} (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) 𝕜} (O : unitary (Matrix (Fin p) (Fin p) 𝕜))
    {lam : Fin p → ℝ}
    (hdiag : (star O.val) * A * O.val =
      Matrix.diagonal (fun i => (lam i : 𝕜))) :
    ∃ U : OrthonormalFrame 𝕜 p j,
      compressionDeterminant A U = ∏ i : Fin j, lam (Fin.castLE hj i) := by
  let E := coordinateFrame (𝕜 := 𝕜) (Fin.castLEEmb hj)
  let U := O.val * E
  have hU : Uᴴ * U = 1 := by
    simp only [U, Matrix.conjTranspose_mul]
    calc
      _ = Eᴴ * ((star O.val) * O.val) * E := by
        simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
      _ = 1 := by rw [O.property.1, Matrix.mul_one]; exact Wishart.FieldSpectral.coordinateFrame_orthonormal (𝕜 := 𝕜) _
  refine ⟨⟨U, hU⟩, ?_⟩
  have heq : Uᴴ * A * U = Eᴴ * Matrix.diagonal (fun i => (lam i : 𝕜)) * E := by
    simp only [U, Matrix.conjTranspose_mul]
    calc
      _ = Eᴴ * ((star O.val) * A * O.val) * E := by
        simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
      _ = _ := by rw [hdiag]
  change RCLike.re (Uᴴ * A * U).det = _
  rw [heq, coordinateFrame_compression,
    Matrix.submatrix_diagonal_embedding, Matrix.det_diagonal]
  simp [E, ← map_prod, RCLike.ofReal_re]

theorem leadingEigenvalueProduct_isGreatest {p j : ℕ} (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) 𝕜} (hA : A.PosSemidef) :
    IsGreatest (Set.range (compressionDeterminant (j := j) A))
      (leadingEigenvalueProduct hj hA.isHermitian) := by
  obtain ⟨O, hO⟩ := exists_sorted_diagonalization hA.isHermitian
  constructor
  · exact exists_compression_eq_of_diagonalization hj O hO
  · rintro t ⟨U, rfl⟩
    exact compression_le_of_sorted_diagonalization hj O hO
      (fun i => hA.eigenvalues₀_nonneg _) (antitone_orderedValues hA.isHermitian) U

/-- Any sorted diagonalization computes the same leading product. -/
theorem leadingEigenvalueProduct_eq_of_diagonalization {p j : ℕ} (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) 𝕜} (hA : A.PosSemidef)
    (O : unitary (Matrix (Fin p) (Fin p) 𝕜)) {lam : Fin p → ℝ}
    (hdiag : (star O.val) * A * O.val =
      Matrix.diagonal (fun i => (lam i : 𝕜)))
    (h0 : ∀ i, 0 ≤ lam i) (hmono : Antitone lam) :
    leadingEigenvalueProduct hj hA.isHermitian = ∏ i : Fin j, lam (Fin.castLE hj i) := by
  apply (leadingEigenvalueProduct_isGreatest hj hA).unique
  constructor
  · exact exists_compression_eq_of_diagonalization hj O hdiag
  · rintro t ⟨U, rfl⟩
    exact compression_le_of_sorted_diagonalization hj O hdiag h0 hmono U

abbrev Hermitian (𝕜 : Type*) [RCLike 𝕜] (p : ℕ) :=
  selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)

theorem continuous_orderedValues (p : ℕ) : Continuous
    (fun A : Hermitian 𝕜 p => orderedValues (WishartVerification.hermitian_matrix_coe A)) := by
  apply continuous_pi
  intro i
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro A B
  have h := (WishartVerification.hermitian_matrix_coe A).abs_eigenvalues₀_sub_le_norm
    (WishartVerification.hermitian_matrix_coe B) (Fin.cast (Fintype.card_fin p).symm i)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs]
  convert h using 1 <;> rfl

theorem continuous_leadingEigenvalueProduct {p j : ℕ} (hj : j ≤ p) : Continuous
    (fun A : Hermitian 𝕜 p => leadingEigenvalueProduct hj (WishartVerification.hermitian_matrix_coe A)) := by
  exact continuous_finsetProd _ fun i _ =>
    (continuous_apply (Fin.castLE hj i)).comp (continuous_orderedValues p)


/-- The canonical decreasing eigenvalue list of an already sorted real
 diagonal is literally that diagonal, with multiplicities. -/
theorem orderedValues_diagonal {p : ℕ} (lam : Fin p → ℝ) (hmono : Antitone lam) :
    orderedValues (Matrix.isHermitian_diagonal_of_self_adjoint
      (fun i => (lam i : 𝕜)) (by ext i; simp)) = lam := by
  let D : Matrix (Fin p) (Fin p) 𝕜 := Matrix.diagonal (fun i => (lam i : 𝕜))
  have hD : D.IsHermitian := Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  have hroots : D.charpoly.roots = Multiset.map (fun i => (lam i : 𝕜)) Finset.univ.val := by
    dsimp only [D]
    rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  apply List.ofFn_injective
  change List.ofFn (orderedValues hD) = List.ofFn lam
  rw [show List.ofFn (orderedValues hD) = List.ofFn hD.eigenvalues₀ from
    (List.ofFn_congr (Fintype.card_fin p) hD.eigenvalues₀).symm,
    ← hD.sort_roots_charpoly_eq_eigenvalues₀, hroots]
  rw [Multiset.map_map]
  simp only [Function.comp_def, RCLike.ofReal_re, Fin.univ_val_map, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact hmono.sortedGE_ofFn

theorem orderedValues_eq_of_sorted_diagonalization {p : ℕ}
    {A : Matrix (Fin p) (Fin p) 𝕜} (hA : A.IsHermitian)
    (U : unitary (Matrix (Fin p) (Fin p) 𝕜)) {lam : Fin p → ℝ}
    (hdiag : (star U.val) * A * U.val =
      Matrix.diagonal (fun i => (lam i : 𝕜))) (hmono : Antitone lam) :
    orderedValues hA = lam := by
  have hD : (Matrix.diagonal (fun i => (lam i : 𝕜))).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  have hchar : A.charpoly = (Matrix.diagonal (fun i => (lam i : 𝕜))).charpoly := by
    rw [← hdiag, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      U.property.2, Matrix.one_mul]
  have h := (hA.eigenvalues_eq_eigenvalues_iff hD).mpr hchar
  rw [orderedValues_eq, h, ← orderedValues_eq, orderedValues_diagonal lam hmono]

end Wishart.FieldSpectral
end
end CanonicalSource0

section CanonicalSource1
/- Source: Wishart/QuaternionVariational.lean -/




/-!
# The quaternion compression variational formula

A quaternion column frame becomes a complex column frame of twice the rank.
The complex compression bound therefore bounds the square of the Moore
determinant.  A quaternion eigenframe attains that bound.  This establishes the
actual maximum over quaternion frames, including singular inputs and rank zero.
-/

noncomputable section
open Matrix
open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius

def permutationUnitary {p : ℕ} (e : Equiv.Perm (Fin p)) :
    unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  refine ⟨e.permMatrix ℍ[ℝ], ?_⟩
  change (e.permMatrix ℍ[ℝ])ᴴ * e.permMatrix ℍ[ℝ] = 1 ∧
    e.permMatrix ℍ[ℝ] * (e.permMatrix ℍ[ℝ])ᴴ = 1
  constructor <;> simp only [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
    inv_mul_cancel, mul_inv_cancel, Matrix.permMatrix_one]

theorem permutation_diagonal {p : ℕ} (e : Equiv.Perm (Fin p)) (lam : Fin p → ℝ) :
    (permutationUnitary e).val *
        Matrix.diagonal (fun i => (lam i : ℍ[ℝ])) * ((permutationUnitary e).valᴴ) =
      Matrix.diagonal (fun i => (lam (e i) : ℍ[ℝ])) := by
  change e.permMatrix ℍ[ℝ] * _ * (e.permMatrix ℍ[ℝ])ᴴ = _
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  apply Matrix.ext
  intro i j
  simp [Matrix.submatrix_apply, Matrix.diagonal_apply, Equiv.Perm.inv_def, e.injective.eq_iff]

def EigenDecomposition.reindex {p : ℕ} {A : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (D : EigenDecomposition A) (e : Equiv.Perm (Fin p)) : EigenDecomposition A where
  frame := D.frame * star (permutationUnitary e)
  values := D.values ∘ e
  diagonalization := by
    change (D.frame.val * (permutationUnitary e).valᴴ)ᴴ * A *
      (D.frame.val * (permutationUnitary e).valᴴ) = _
    simp only [Unitary.coe_star, star_mul, star_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = (permutationUnitary e).val *
          (D.frame.valᴴ * A * D.frame.val) *
          (permutationUnitary e).valᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [D.diagonalization, permutation_diagonal]; rfl

def orderedEigenDecomposition {p : ℕ} (A : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (hA : A.IsHermitian) : EigenDecomposition A :=
  let D := eigenDecomposition A hA
  D.reindex (Tuple.sortDesc D.values)

theorem antitone_orderedEigenDecomposition {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hA : A.IsHermitian) :
    Antitone (orderedEigenDecomposition A hA).values :=
  Tuple.antitone_sortDesc _

/-- Flatten the two scalar coordinates in the actual complex representation. -/
def flatRepresentation {p j : ℕ} (A : Matrix (Fin p) (Fin j) ℍ[ℝ]) :
    Matrix (Fin (p * 2)) (Fin (j * 2)) ℂ :=
  (complexRepresentation A).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

theorem flatRepresentation_mul {p j k : ℕ}
    (A : Matrix (Fin p) (Fin j) ℍ[ℝ]) (B : Matrix (Fin j) (Fin k) ℍ[ℝ]) :
    flatRepresentation (A * B) = flatRepresentation A * flatRepresentation B := by
  rw [flatRepresentation, complexRepresentation_mul,
    Matrix.submatrix_mul _ _ _ finProdFinEquiv.symm _ finProdFinEquiv.symm.bijective]
  rfl

@[simp] theorem flatRepresentation_conjTranspose {p j : ℕ}
    (A : Matrix (Fin p) (Fin j) ℍ[ℝ]) :
    flatRepresentation Aᴴ = (flatRepresentation A)ᴴ := by
  simp only [flatRepresentation, complexRepresentation_conjTranspose, Matrix.conjTranspose_submatrix]

@[simp] theorem flatRepresentation_one {p : ℕ} :
    flatRepresentation (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) = 1 := by
  simp [flatRepresentation]

theorem flatRepresentation_posSemidef {p : ℕ}
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hA : PosSemidef A) :
    (flatRepresentation A).PosSemidef := hA.submatrix _

def flatUnitary {p : ℕ} (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) :
    unitary (Matrix (Fin (p * 2)) (Fin (p * 2)) ℂ) :=
  ⟨flatRepresentation U.val,
    Matrix.submatrix_equiv_mem_unitary.mpr (complexRepresentation_unitary U.property)⟩

def doubleValues {p : ℕ} (lam : Fin p → ℝ) : Fin (p * 2) → ℝ :=
  fun i => lam (finProdFinEquiv.symm i).1

theorem doubleValues_antitone {p : ℕ} {lam : Fin p → ℝ}
    (h : Antitone lam) : Antitone (doubleValues lam) := by
  intro i j hij
  apply h
  change i.val / 2 ≤ j.val / 2
  exact Nat.div_le_div_right hij

theorem flatRepresentation_diagonal {p : ℕ} (lam : Fin p → ℝ) :
    flatRepresentation (Matrix.diagonal (fun i => (lam i : ℍ[ℝ]))) =
      Matrix.diagonal (fun i => (doubleValues lam i : ℂ)) := by
  rw [flatRepresentation, complexRepresentation_diagonal,
    Matrix.submatrix_diagonal_equiv]
  rfl

theorem prod_prefix_doubleValues {p j : ℕ} (hj : j ≤ p) (lam : Fin p → ℝ) :
    (∏ a : Fin (j * 2), doubleValues lam (Fin.castLE (Nat.mul_le_mul_right 2 hj) a)) =
      (∏ i : Fin j, lam (Fin.castLE hj i)) ^ 2 := by
  rw [← Equiv.prod_comp (finProdFinEquiv : Fin j × Fin 2 ≃ Fin (j * 2))
    (fun a : Fin (j * 2) => doubleValues lam (Fin.castLE (Nat.mul_le_mul_right 2 hj) a))]
  rw [Fintype.prod_prod_type]
  have h (i : Fin j) (a : Fin 2) :
      doubleValues lam (Fin.castLE (Nat.mul_le_mul_right 2 hj) (finProdFinEquiv (i,a))) =
        lam (Fin.castLE hj i) := by
    unfold doubleValues
    congr 1
    apply Fin.ext
    change (a.val + 2 * i.val) / 2 = i.val
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt a.isLt]
    simp
  simp_rw [h, Fin.prod_univ_two]
  rw [Finset.prod_mul_distrib, pow_two]

def OrthonormalFrame (p j : ℕ) :=
  {U : Matrix (Fin p) (Fin j) ℍ[ℝ] // Uᴴ * U = 1}

def flatFrame {p j : ℕ} (U : OrthonormalFrame p j) :
    Wishart.FieldSpectral.OrthonormalFrame ℂ (p * 2) (j * 2) :=
  ⟨flatRepresentation U.val, by
    rw [← flatRepresentation_conjTranspose, ← flatRepresentation_mul, U.property,
      flatRepresentation_one]⟩

def compressionDeterminant {p j : ℕ} (A : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (U : OrthonormalFrame p j) : ℝ := positiveDeterminant (U.valᴴ * A * U.val)

/-- A continuous expression in the actual complex spectrum.  The variational
proof below identifies it with the quaternion leading-eigenvalue product. -/
def leadingEigenvalueProduct {p j : ℕ} (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hA : A.IsHermitian) : ℝ :=
  Real.sqrt (Wishart.FieldSpectral.leadingEigenvalueProduct
    (Nat.mul_le_mul_right 2 hj)
    (((isHermitian_complexRepresentation_iff A).mpr hA).submatrix finProdFinEquiv.symm))

theorem leadingEigenvalueProduct_eq_prod {p j : ℕ} (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hA : PosSemidef A) :
    leadingEigenvalueProduct hj hA.isHermitian =
      ∏ i : Fin j, (orderedEigenDecomposition A hA.isHermitian).values (Fin.castLE hj i) := by
  let D := orderedEigenDecomposition A hA.isHermitian
  have hdiag : (star (flatUnitary D.frame) : Matrix (Fin (p * 2)) (Fin (p * 2)) ℂ) *
      flatRepresentation A * flatUnitary D.frame =
        Matrix.diagonal (fun i => (doubleValues D.values i : ℂ)) := by
    change (flatRepresentation D.frame.val)ᴴ * flatRepresentation A * flatRepresentation D.frame.val = _
    rw [← flatRepresentation_conjTranspose, ← flatRepresentation_mul,
      ← flatRepresentation_mul, D.diagonalization, flatRepresentation_diagonal]
  have hc := Wishart.FieldSpectral.leadingEigenvalueProduct_eq_of_diagonalization
    (Nat.mul_le_mul_right 2 hj) (flatRepresentation_posSemidef hA) (flatUnitary D.frame)
    hdiag (fun i => D.values_nonneg hA _) (doubleValues_antitone
      (antitone_orderedEigenDecomposition A hA.isHermitian))
  change _ = ∏ i : Fin (j * 2), doubleValues D.values (Fin.castLE (Nat.mul_le_mul_right 2 hj) i) at hc
  rw [prod_prefix_doubleValues hj] at hc
  have hs := congrArg Real.sqrt hc
  rw [Real.sqrt_sq (Finset.prod_nonneg fun i _ => D.values_nonneg hA _)] at hs
  convert hs using 1 <;> rfl

theorem compressionDeterminant_le {p j : ℕ} (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hA : PosSemidef A)
    (U : OrthonormalFrame p j) :
    compressionDeterminant A U ≤ leadingEigenvalueProduct hj hA.isHermitian := by
  have hbound := (Wishart.FieldSpectral.leadingEigenvalueProduct_isGreatest
    (Nat.mul_le_mul_right 2 hj) (flatRepresentation_posSemidef hA)).2
      (Set.mem_range_self (flatFrame U))
  have hdet : Wishart.FieldSpectral.compressionDeterminant
      (flatRepresentation A) (flatFrame U) = compressionDeterminant A U ^ 2 := by
    unfold Wishart.FieldSpectral.compressionDeterminant compressionDeterminant flatFrame
    rw [← flatRepresentation_conjTranspose, ← flatRepresentation_mul,
      ← flatRepresentation_mul, flatRepresentation, Matrix.det_submatrix_equiv_self]
    exact (hA.congruence U.val).positiveDeterminant_sq.symm
  rw [hdet] at hbound
  unfold leadingEigenvalueProduct
  exact Real.le_sqrt_of_sq_le hbound

def coordinateFrame {j p : ℕ} (e : Fin j ↪ Fin p) : Matrix (Fin p) (Fin j) ℍ[ℝ] :=
  (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]).submatrix id e

theorem coordinateFrame_compression {j p : ℕ} (e : Fin j ↪ Fin p)
    (A : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    (coordinateFrame e)ᴴ * A * coordinateFrame e = A.submatrix e e := by
  unfold coordinateFrame
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change (1 : Matrix (Fin p) (Fin p) _).submatrix e (Equiv.refl (Fin p)) * A * (1 : Matrix (Fin p) (Fin p) _).submatrix (Equiv.refl (Fin p)) e = _
  rw [Matrix.one_submatrix_mul e (Equiv.refl (Fin p)) A,
    Matrix.mul_submatrix_one (Equiv.refl (Fin p)) e]
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp,
    Matrix.submatrix_submatrix, Function.comp_id]

theorem exists_compressionDeterminant_eq {p j : ℕ} (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hA : PosSemidef A) :
    ∃ U : OrthonormalFrame p j,
      compressionDeterminant A U = leadingEigenvalueProduct hj hA.isHermitian := by
  let D := orderedEigenDecomposition A hA.isHermitian
  let E := coordinateFrame (Fin.castLEEmb hj)
  let U := D.frame.val * E
  have hE : Eᴴ * E = 1 := by
    simpa only [Matrix.mul_one, Matrix.submatrix_one_embedding] using
      coordinateFrame_compression (Fin.castLEEmb hj) (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])
  have hU : Uᴴ * U = 1 := by
    simp only [U, Matrix.conjTranspose_mul]
    calc
      _ = Eᴴ * (D.frame.valᴴ * D.frame.val) * E := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        have hD : D.frame.valᴴ * D.frame.val = 1 := by convert D.frame.property.1 using 1 <;> rfl
        rw [hD, Matrix.mul_one, hE]
  refine ⟨⟨U,hU⟩, ?_⟩
  have hcomp : Uᴴ * A * U =
      Matrix.diagonal (fun i : Fin j => (D.values (Fin.castLE hj i) : ℍ[ℝ])) := by
    calc
      _ = Eᴴ * (D.frame.valᴴ * A * D.frame.val) * E := by
        simp only [U, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [D.diagonalization, coordinateFrame_compression,
        Matrix.submatrix_diagonal_embedding]
                  rfl
  change positiveDeterminant (Uᴴ * A * U) = _
  rw [hcomp, leadingEigenvalueProduct_eq_prod hj hA]
  exact positiveDeterminant_diagonal _ (fun i => D.values_nonneg hA _)

theorem leadingEigenvalueProduct_isGreatest {p j : ℕ} (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hA : PosSemidef A) :
    IsGreatest (Set.range (compressionDeterminant (j := j) A))
      (leadingEigenvalueProduct hj hA.isHermitian) := by
  constructor
  · exact exists_compressionDeterminant_eq hj hA
  · rintro t ⟨U,rfl⟩
    exact compressionDeterminant_le hj hA U


def flatHermitian {p : ℕ} (A : Hermitian p) : Wishart.FieldSpectral.Hermitian ℂ (p * 2) :=
  ⟨flatRepresentation (A : Matrix (Fin p) (Fin p) ℍ[ℝ]),
    (((isHermitian_complexRepresentation_iff _).mpr
      (WishartVerification.hermitian_matrix_coe A)).submatrix finProdFinEquiv.symm).eq⟩

theorem continuous_flatHermitian (p : ℕ) : Continuous (@flatHermitian p) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_apply (finProdFinEquiv.symm j)).comp
    (continuous_apply (finProdFinEquiv.symm i))).comp
      (continuous_complexRepresentation.comp continuous_subtype_val)

theorem continuous_leadingEigenvalueProduct {p j : ℕ} (hj : j ≤ p) : Continuous
    (fun A : Hermitian p => leadingEigenvalueProduct hj (WishartVerification.hermitian_matrix_coe A)) := by
  have hc := Real.continuous_sqrt.comp
    ((Wishart.FieldSpectral.continuous_leadingEigenvalueProduct (𝕜 := ℂ)
      (Nat.mul_le_mul_right 2 hj)).comp (continuous_flatHermitian p))
  convert hc using 1 <;> rfl

end Wishart.QuaternionMatrix
end
end CanonicalSource1

section CanonicalSource2
/- Source: Wishart/QuaternionEigenvalues.lean -/




/-!
# Continuous ordered quaternion eigenvalues

Every quaternion eigenvalue occurs twice in the faithful complex Hermitian
spectrum.  The even positions of that actual sorted complex spectrum give a
continuous canonical selector; they are identified with the eigenvalues of
the constructive quaternion diagonalization.  No eigenframe is assumed to be
measurable.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion Matrix ComplexOrder Matrix.Norms.L2Operator

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius

def doubledIndex {p : ℕ} (i : Fin p) : Fin (p * 2) := finProdFinEquiv (i, 0)

def orderedValues {p : ℕ} (A : Hermitian p) : Fin p → ℝ :=
  fun i => Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (flatHermitian A))
    (doubledIndex i)

theorem flat_orderedValues_eq_double {p : ℕ} (A : Hermitian p) :
    Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (flatHermitian A)) =
      doubleValues (orderedEigenDecomposition A.val (WishartVerification.hermitian_matrix_coe A)).values := by
  let D := orderedEigenDecomposition A.val (WishartVerification.hermitian_matrix_coe A)
  have hdiag : (star (flatUnitary D.frame) : Matrix (Fin (p * 2)) (Fin (p * 2)) ℂ) *
      flatRepresentation A.val * flatUnitary D.frame =
        Matrix.diagonal (fun i => (doubleValues D.values i : ℂ)) := by
    change (flatRepresentation D.frame.val)ᴴ * flatRepresentation A.val * flatRepresentation D.frame.val = _
    rw [← flatRepresentation_conjTranspose, ← flatRepresentation_mul,
      ← flatRepresentation_mul, D.diagonalization, flatRepresentation_diagonal]
  exact Wishart.FieldSpectral.orderedValues_eq_of_sorted_diagonalization
    (WishartVerification.hermitian_matrix_coe (flatHermitian A)) (flatUnitary D.frame) hdiag
    (doubleValues_antitone (antitone_orderedEigenDecomposition A.val _))

theorem orderedValues_eq_decomposition {p : ℕ} (A : Hermitian p) :
    orderedValues A = (orderedEigenDecomposition A.val (WishartVerification.hermitian_matrix_coe A)).values := by
  funext i
  rw [orderedValues, flat_orderedValues_eq_double]
  simp only [doubleValues, doubledIndex, Equiv.symm_apply_apply]

theorem orderedValues_antitone {p : ℕ} (A : Hermitian p) : Antitone (orderedValues A) := by
  rw [orderedValues_eq_decomposition]
  exact antitone_orderedEigenDecomposition A.val _

theorem continuous_orderedValues (p : ℕ) : Continuous (@orderedValues p) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (doubledIndex i)).comp
    ((Wishart.FieldSpectral.continuous_orderedValues (𝕜 := ℂ) (p * 2)).comp
      (continuous_flatHermitian p))

theorem orderedValues_nonneg {p : ℕ} (A : Hermitian p) (hA : PosSemidef A.val) (i : Fin p) :
    0 ≤ orderedValues A i := by
  rw [orderedValues_eq_decomposition]
  exact (orderedEigenDecomposition A.val (WishartVerification.hermitian_matrix_coe A)).values_nonneg hA i

/-- The Moore determinant on all Hermitian quaternion matrices is the product
of their real eigenvalues. On the PSD cone it agrees with positiveDeterminant. -/
def mooreDeterminant {p : ℕ} (A : Hermitian p) : ℝ := ∏ i, orderedValues A i

theorem positiveDeterminant_eq_mooreDeterminant {p : ℕ}
    (A : Hermitian p) (hA : PosSemidef A.val) :
    positiveDeterminant A.val = mooreDeterminant A := by
  rw [mooreDeterminant, orderedValues_eq_decomposition]
  exact (orderedEigenDecomposition A.val (WishartVerification.hermitian_matrix_coe A)).positiveDeterminant_eq_prod hA

theorem continuous_mooreDeterminant (p : ℕ) : Continuous (@mooreDeterminant p) :=
  continuous_finsetProd _ fun i _ => (continuous_apply i).comp (continuous_orderedValues p)

theorem leadingEigenvalueProduct_eq_orderedValues {p j : ℕ} (hj : j ≤ p)
    (A : Hermitian p) (hA : PosSemidef A.val) :
    leadingEigenvalueProduct hj (WishartVerification.hermitian_matrix_coe A) =
      ∏ i : Fin j, orderedValues A (Fin.castLE hj i) := by
  rw [orderedValues_eq_decomposition]
  exact leadingEigenvalueProduct_eq_prod hj hA

def diagonalHermitian {p : ℕ} (lam : Fin p → ℝ) : Hermitian p :=
  ⟨Matrix.diagonal (fun i => (lam i : ℍ[ℝ])), by
    change (Matrix.diagonal (fun i => (lam i : ℍ[ℝ])))ᴴ = _
    simp⟩

def conjugate {p : ℕ} (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (A : Hermitian p) : Hermitian p :=
  ⟨U.val * A.val * U.valᴴ,
    Matrix.isHermitian_mul_mul_conjTranspose U.val (WishartVerification.hermitian_matrix_coe A)⟩

theorem exists_conjugate_diagonal {p : ℕ} (A : Hermitian p) :
    ∃ U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]),
      conjugate U (diagonalHermitian (orderedValues A)) = A := by
  let D := orderedEigenDecomposition A.val (WishartVerification.hermitian_matrix_coe A)
  refine ⟨D.frame, Subtype.ext ?_⟩
  change D.frame.val *
    Matrix.diagonal (fun i => (orderedValues A i : ℍ[ℝ])) * star D.frame.val = A.val
  rw [orderedValues_eq_decomposition]
  exact D.reconstruct

theorem orderedValues_conjugate {p : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) (A : Hermitian p) :
    orderedValues (conjugate U A) = orderedValues A := by
  let hA := WishartVerification.hermitian_matrix_coe (flatHermitian A)
  let hB := WishartVerification.hermitian_matrix_coe (flatHermitian (conjugate U A))
  have hchar : (flatRepresentation (conjugate U A).val).charpoly =
      (flatRepresentation A.val).charpoly := by
    change (flatRepresentation (U.val * A.val * U.valᴴ)).charpoly = _
    have hU : (flatRepresentation U.val)ᴴ * flatRepresentation U.val = 1 := by
      convert (flatUnitary U).property.1 using 1 <;> rfl
    rw [flatRepresentation_mul, flatRepresentation_mul, flatRepresentation_conjTranspose,
      Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hvalues := (hB.eigenvalues_eq_eigenvalues_iff hA).mpr hchar
  funext i
  unfold orderedValues
  rw [Wishart.FieldSpectral.orderedValues_eq, Wishart.FieldSpectral.orderedValues_eq, hvalues]

def ascendingValues {p : ℕ} (A : Hermitian p) : Fin p → ℝ := orderedValues A ∘ Fin.rev

theorem continuous_ascendingValues (p : ℕ) : Continuous (@ascendingValues p) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (Fin.rev i)).comp (continuous_orderedValues p)

theorem ascendingValues_monotone {p : ℕ} (A : Hermitian p) : Monotone (ascendingValues A) :=
  fun _ _ h => orderedValues_antitone A (Fin.rev_anti h)

end Wishart.QuaternionMatrix
end
end CanonicalSource2

section CanonicalSource3
set_option backward.isDefEq.respectTransparency false
/- Source: Wishart/QuaternionUnitary.lean -/



/-!
# Quaternion unitary compactness and invariant Hermitian Lebesgue measure

The unitary group is compact because each quaternion entry has norm at most
one.  Conjugation is a real linear Frobenius isometry of the Hermitian space;
therefore it preserves the actual Lebesgue measure used by the density.
-/

noncomputable section
open Matrix MeasureTheory Metric Set
open scoped Classical Quaternion Matrix BigOperators

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem trace_gram_re (A : Matrix n n ℍ[ℝ]) :
    (Aᴴ * A).trace.re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  change (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) (∑ j, ∑ i, star (A i j) * A i j) = _
  simp only [map_sum, Quaternion.star_mul_self, QuaternionAlgebra.re_coe,
    Quaternion.normSq_eq_norm_mul_self, ← pow_two]
  exact Finset.sum_comm

theorem entry_norm_le_one_of_unitary (U : unitary (Matrix n n ℍ[ℝ])) (i j : n) :
    ‖U.val i j‖ ≤ 1 := by
  have hcol := congrArg (fun A : Matrix n n ℍ[ℝ] => (A j j).re) U.property.1
  simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply_eq, Quaternion.re_one] at hcol
  change (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) (∑ k, star (U.val k j) * U.val k j) = 1 at hcol
  simp only [map_sum, Quaternion.star_mul_self, QuaternionAlgebra.re_coe,
    Quaternion.normSq_eq_norm_mul_self, ← pow_two] at hcol
  have hle : ‖U.val i j‖ ^ 2 ≤
      ∑ k, ‖U.val k j‖ ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg ‖U.val k j‖) (Finset.mem_univ i)
  change (∑ k, ‖U.val k j‖ ^ 2) = 1 at hcol
  rw [hcol] at hle
  nlinarith [norm_nonneg (U.val i j)]

theorem isCompact_unitaryGroup :
    IsCompact (unitary (Matrix n n ℍ[ℝ]) : Set (Matrix n n ℍ[ℝ])) := by
  exact ((isCompact_closedBall (0 : ℍ[ℝ]) 1).matrix).of_isClosed_subset isClosed_unitary
    (fun U hU i j => mem_closedBall_zero_iff.mpr
      (entry_norm_le_one_of_unitary ⟨U,hU⟩ i j))

instance quaternionUnitary_compactSpace : CompactSpace (unitary (Matrix n n ℍ[ℝ])) :=
  isCompact_iff_compactSpace.mp isCompact_unitaryGroup

def haarMeasure (p : ℕ) : Measure (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) :=
  TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))

instance haarMeasure_isProbability (p : ℕ) : IsProbabilityMeasure (haarMeasure p) := by
  unfold haarMeasure
  infer_instance

def conjugateLinearEquiv {p : ℕ} (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) :
    Hermitian p ≃ₗ[ℝ] Hermitian p where
  toFun := conjugate U
  invFun := conjugate (star U)
  left_inv A := by
    apply Subtype.ext
    simp only [conjugate, Unitary.coe_star, ← Matrix.star_eq_conjTranspose, star_star]
    change (star U.val) *
      (U.val * A.val * star U.val) * U.val = A.val
    simp only [← Matrix.mul_assoc, U.property.1, Matrix.one_mul]
    rw [Matrix.mul_assoc, U.property.1, Matrix.mul_one]
  right_inv A := by
    apply Subtype.ext
    simp only [conjugate, Unitary.coe_star, ← Matrix.star_eq_conjTranspose, star_star]
    change U.val *
      ((star U.val) * A.val * U.val) * star U.val = A.val
    simp only [← Matrix.mul_assoc, U.property.2, Matrix.one_mul]
    rw [Matrix.mul_assoc, U.property.2, Matrix.mul_one]
  map_add' A B := by apply Subtype.ext; simp [conjugate, Matrix.mul_add, Matrix.add_mul]
  map_smul' r A := by apply Subtype.ext; simp [conjugate, Matrix.mul_smul, Matrix.smul_mul]

theorem continuous_conjugate (p : ℕ) : Continuous
    (fun x : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]) × Hermitian p => conjugate x.1 x.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun x : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]) × Hermitian p =>
    x.1.val * x.2.val * star x.1.val)
  fun_prop

section Frobenius
open scoped Matrix.Norms.Frobenius

theorem frobenius_norm_conjugate {p : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) (A : Hermitian p) :
    ‖(conjugate U A).val‖ =
      ‖A.val‖ := by
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]
  simp_rw [Real.rpow_two]
  congr 1
  rw [← trace_gram_re, ← trace_gram_re]
  change ((U.val * A.val * star U.val)ᴴ *
    (U.val * A.val * star U.val)).trace.re = _
  simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have heq : (U.val * A.valᴴ * star U.val) *
      (U.val * A.val * star U.val) =
        U.val * (A.valᴴ * A.val) * star U.val := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star U.val) U.val,
      U.property.1, Matrix.one_mul]
  simp only [← Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc] at heq ⊢
  rw [heq, real_trace_mul_comm]
  simp only [← Matrix.mul_assoc, U.property.1, Matrix.one_mul]

set_option maxHeartbeats 2000000 in
def conjugateLinearIsometryEquiv {p : ℕ} (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) :
    Hermitian p ≃ₗᵢ[ℝ] Hermitian p :=
  { conjugateLinearEquiv U with norm_map' := frobenius_norm_conjugate U }

theorem map_conjugate_hermitianLebesgue {p : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) :
    (hermitianLebesgue p).map (conjugate U) = hermitianLebesgue p :=
  WishartVerification.linearIsometryEquiv_map_addHaar
    (conjugateLinearIsometryEquiv U) (hermitianLebesgue p)

end Frobenius

end Wishart.QuaternionMatrix
end
end CanonicalSource3

section CanonicalSource4
set_option backward.isDefEq.respectTransparency false
/- Source: Wishart/FieldSpectralBounds.lean -/



/-!
# Trace bounds for the actual leading spectral products

The estimates include zero eigenvalues and the empty product.  They supply
the polynomial envelopes used in Gaussian averaging, without placing a
growth hypothesis on the final spectral profile of Theorem 7.1.
-/

noncomputable section
open Matrix
open scoped Classical Quaternion ComplexOrder BigOperators

namespace Wishart.FieldSpectral

variable {𝕜 : Type*} [RCLike 𝕜] {p j : ℕ}

theorem orderedValues_nonneg {A : Matrix (Fin p) (Fin p) 𝕜}
    (hA : A.PosSemidef) (i : Fin p) : 0 ≤ orderedValues hA.isHermitian i := by
  rw [orderedValues_eq]
  exact hA.eigenvalues_nonneg _

theorem orderedValues_pos {A : Matrix (Fin p) (Fin p) 𝕜}
    (hA : A.PosDef) (i : Fin p) : 0 < orderedValues hA.isHermitian i := by
  rw [orderedValues_eq]
  exact hA.eigenvalues_pos _

theorem leadingEigenvalueProduct_nonneg (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) 𝕜} (hA : A.PosSemidef) :
    0 ≤ leadingEigenvalueProduct hj hA.isHermitian :=
  Finset.prod_nonneg fun i _ => orderedValues_nonneg hA _

theorem leadingEigenvalueProduct_pos (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) 𝕜} (hA : A.PosDef) :
    0 < leadingEigenvalueProduct hj hA.isHermitian :=
  Finset.prod_pos fun i _ => orderedValues_pos hA _

theorem trace_eq_sum_orderedValues {A : Matrix (Fin p) (Fin p) 𝕜}
    (hA : A.IsHermitian) : RCLike.re A.trace = ∑ i, orderedValues hA i := by
  rw [hA.trace_eq_sum_eigenvalues]
  simp only [map_sum, RCLike.ofReal_re, orderedValues_eq, Function.comp_apply]
  exact (Equiv.sum_comp (orderedIndex p) hA.eigenvalues).symm

theorem orderedValues_le_trace {A : Matrix (Fin p) (Fin p) 𝕜}
    (hA : A.PosSemidef) (i : Fin p) :
    orderedValues hA.isHermitian i ≤ RCLike.re A.trace := by
  rw [trace_eq_sum_orderedValues hA.isHermitian]
  exact Finset.single_le_sum (fun j _ => orderedValues_nonneg hA j) (Finset.mem_univ i)

theorem leadingEigenvalueProduct_le_trace_pow (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) 𝕜} (hA : A.PosSemidef) :
    leadingEigenvalueProduct hj hA.isHermitian ≤ (RCLike.re A.trace) ^ j := by
  calc
    _ ≤ ∏ _i : Fin j, RCLike.re A.trace := Finset.prod_le_prod₀
      (fun i _ => orderedValues_nonneg hA _) (fun i _ => orderedValues_le_trace hA _)
    _ = _ := by simp

theorem OrthonormalFrame.injective_mulVec (U : OrthonormalFrame 𝕜 p j) :
    Function.Injective U.val.mulVec := by
  intro x y hxy
  have h := congrArg (fun z => U.valᴴ *ᵥ z) hxy
  simpa only [Matrix.mulVec_mulVec, U.property, Matrix.one_mulVec] using h

end Wishart.FieldSpectral

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius

variable {p j : ℕ}

theorem PosSemidef.add {A B : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hA : PosSemidef A) (hB : PosSemidef B) : PosSemidef (A + B) := by
  unfold PosSemidef
  rw [complexRepresentation_add]
  exact Matrix.PosSemidef.add hA hB

theorem PosSemidef.smul {A : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hA : PosSemidef A) {r : ℝ} (hr : 0 ≤ r) : PosSemidef (r • A) := by
  unfold PosSemidef
  rw [complexRepresentation_smul]
  exact Matrix.PosSemidef.smul hA hr

theorem PosDef.add_posSemidef {A B : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hA : PosDef A) (hB : PosSemidef B) : PosDef (A + B) := by
  unfold PosDef
  rw [complexRepresentation_add]
  exact Matrix.PosDef.add_posSemidef hA hB

theorem PosDef.smul {A : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hA : PosDef A) {r : ℝ} (hr : 0 < r) : PosDef (r • A) := by
  unfold PosDef
  rw [complexRepresentation_smul]
  exact Matrix.PosDef.smul hA hr

theorem posDef_one : PosDef (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  unfold PosDef
  rw [complexRepresentation_one]
  exact Matrix.PosDef.one

theorem posSemidef_gram {r : Type*} [Fintype r]
    (A : Matrix r (Fin p) ℍ[ℝ]) : PosSemidef (Aᴴ * A) :=
  posSemidef_complexRepresentation_gram A

theorem EigenDecomposition.trace_eq_sum {A : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (D : EigenDecomposition A) : A.trace.re = ∑ i, D.values i := by
  calc
    A.trace.re = ((D.frame.val *
        Matrix.diagonal (fun i => (D.values i : ℍ[ℝ]))) * star D.frame.val).trace.re := by
      rw [Matrix.star_eq_conjTranspose, D.reconstruct]
    _ = ((star D.frame.val) *
        (D.frame.val *
          Matrix.diagonal (fun i => (D.values i : ℍ[ℝ])))).trace.re :=
      real_trace_mul_comm _ _
    _ = ∑ i, D.values i := by
      rw [← Matrix.mul_assoc, D.frame.property.1, Matrix.one_mul,
        Matrix.trace_diagonal]
      change (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) (∑ i, (D.values i : ℍ[ℝ])) = _
      simp only [map_sum]
      rfl

theorem leadingEigenvalueProduct_nonneg (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hA : A.IsHermitian) :
    0 ≤ leadingEigenvalueProduct hj hA := Real.sqrt_nonneg _

theorem leadingEigenvalueProduct_pos (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hA : PosDef A) :
    0 < leadingEigenvalueProduct hj hA.isHermitian := by
  apply Real.sqrt_pos.mpr
  exact Wishart.FieldSpectral.leadingEigenvalueProduct_pos _
    (Matrix.PosDef.submatrix hA finProdFinEquiv.symm.injective)

theorem leadingEigenvalueProduct_le_trace_pow (hj : j ≤ p)
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hA : PosSemidef A) :
    leadingEigenvalueProduct hj hA.isHermitian ≤ A.trace.re ^ j := by
  rw [leadingEigenvalueProduct_eq_prod hj hA]
  let D := orderedEigenDecomposition A hA.isHermitian
  have hvalue (i : Fin p) : D.values i ≤ A.trace.re := by
    rw [D.trace_eq_sum]
    exact Finset.single_le_sum (fun a _ => D.values_nonneg hA a) (Finset.mem_univ i)
  calc
    _ ≤ ∏ _i : Fin j, A.trace.re := Finset.prod_le_prod₀
      (fun i _ => D.values_nonneg hA _) (fun i _ => hvalue _)
    _ = _ := by simp

end Wishart.QuaternionMatrix
end
end CanonicalSource4

section CanonicalSource5
set_option backward.isDefEq.respectTransparency false
/- Source: Wishart/FieldDensityMeasurable.lean -/




/-!
# Measurability of the literal densities and Schur maps

The positive cone is tested using the continuous ordered Hermitian spectrum.
The square root is the actual measurable functional calculus, so the Schur
map is measurable without any measurable choice of eigenvectors.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.FieldHermitian
open scoped Matrix.Norms.Frobenius
variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F]
  [StarRing F] [CStarRing F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

set_option backward.isDefEq.respectTransparency false in
theorem measurable_fromBlocks_entries (p q : ℕ) :
    Measurable (fromBlocks F : BlockSpace F p q → Hermitian F (p + q)) := by
  have hS : Measurable (fun z : BlockSpace F p q => (z.1 : Matrix (Fin p) (Fin p) F)) :=
    measurable_subtype_coe.comp measurable_fst
  have hZ : Measurable (fun z : BlockSpace F p q => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hW : Measurable (fun z : BlockSpace F p q => (z.2.2 : Matrix (Fin q) (Fin q) F)) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  unfold fromBlocks
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  simp only [Matrix.submatrix_apply]
  cases hi : finSumFinEquiv.symm i with
  | inl a =>
    cases hj : finSumFinEquiv.symm j with
    | inl b =>
      simpa only [Matrix.fromBlocks_apply₁₁, Function.comp_def, Function.comp_apply] using
        (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hS)
    | inr b =>
      simpa only [Matrix.fromBlocks_apply₁₂, Function.comp_def, Function.comp_apply] using
        (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hZ)
  | inr a =>
    cases hj : finSumFinEquiv.symm j with
    | inl b =>
      simpa only [Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, Function.comp_def, Function.comp_apply] using
        continuous_star.measurable.comp ((measurable_pi_apply a).comp ((measurable_pi_apply b).comp hZ))
    | inr b =>
      simpa only [Matrix.fromBlocks_apply₂₂, Function.comp_def, Function.comp_apply] using
        (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hW)

theorem measurable_matrix_product {Ω : Type*} [MeasurableSpace Ω] {p q r : ℕ}
    {A : Ω → Matrix (Fin p) (Fin q) F} {B : Ω → Matrix (Fin q) (Fin r) F}
    (hA : Measurable A) (hB : Measurable B) : Measurable (fun x => A x * B x) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro k hk
  exact ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA)).mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB))

end Wishart.FieldHermitian

namespace Wishart.FieldSpectral
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}

theorem posDef_iff_orderedValues_pos (A : Hermitian 𝕜 p) :
    (A : Matrix (Fin p) (Fin p) 𝕜).PosDef ↔
      ∀ i, 0 < orderedValues (WishartVerification.hermitian_matrix_coe A) i := by
  constructor
  · exact fun hA => orderedValues_pos hA
  · intro hA
    apply (WishartVerification.hermitian_matrix_coe A).posDef_iff_eigenvalues_pos.mpr
    intro i
    have h := hA ((orderedIndex p).symm i)
    simpa only [orderedValues_eq, Function.comp_apply, Equiv.apply_symm_apply] using h

theorem isOpen_posDef_hermitian (p : ℕ) :
    IsOpen {A : Hermitian 𝕜 p | (A : Matrix (Fin p) (Fin p) 𝕜).PosDef} := by
  have heq : {A : Hermitian 𝕜 p | (A : Matrix (Fin p) (Fin p) 𝕜).PosDef} =
      ⋂ i : Fin p, {A : Hermitian 𝕜 p | 0 < orderedValues (WishartVerification.hermitian_matrix_coe A) i} := by
    ext A
    simp only [mem_setOf_eq, mem_iInter, posDef_iff_orderedValues_pos]
  rw [heq]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
    ((continuous_apply i).comp (continuous_orderedValues p))

end Wishart.FieldSpectral

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.L2Operator
variable {p q : ℕ}

theorem measurable_wishartWeight (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ) :
    Measurable (wishartWeight α Sigma) := by
  unfold wishartWeight
  apply Measurable.ite (Wishart.FieldSpectral.isOpen_posDef_hermitian (𝕜 := ℂ) p).measurableSet
  · apply Measurable.ennreal_ofReal
    apply Measurable.mul
    · exact (continuous_realDeterminant.comp continuous_subtype_val).measurable.pow_const _
    · fun_prop
  · exact measurable_const

theorem measurable_schurInput : Measurable
    (fun z : Hermitian p × Matrix (Fin p) (Fin q) ℂ × Hermitian q =>
      schurInput z.1 z.2.2 z.2.1) := by
  have hfrom : Measurable (Wishart.FieldHermitian.fromBlocks ℂ :
      Wishart.FieldHermitian.BlockSpace ℂ p q → Hermitian (p + q)) :=
    Wishart.FieldHermitian.measurable_fromBlocks_entries ℂ p q
  apply hfrom.comp
  apply Measurable.prodMk measurable_fst
  apply Measurable.prodMk
  · have hs : Measurable (fun z : Wishart.FieldHermitian.BlockSpace ℂ p q =>
        CFC.sqrt (z.1 : Matrix (Fin p) (Fin p) ℂ)) :=
      CFC.measurable_sqrt.comp (measurable_subtype_coe.comp measurable_fst)
    have hz : Measurable (fun z : Wishart.FieldHermitian.BlockSpace ℂ p q => z.2.1) :=
      measurable_fst.comp measurable_snd
    exact Wishart.FieldHermitian.measurable_matrix_product ℂ hs hz
  · apply Measurable.subtype_mk
    change Measurable (fun z : Wishart.FieldHermitian.BlockSpace ℂ p q =>
      (z.2.2 : Matrix (Fin q) (Fin q) ℂ) + z.2.1ᴴ * z.2.1)
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hz : Measurable (fun z : Wishart.FieldHermitian.BlockSpace ℂ p q => z.2.1) :=
      measurable_fst.comp measurable_snd
    have hw : Measurable (fun z : Wishart.FieldHermitian.BlockSpace ℂ p q =>
        (z.2.2 : Matrix (Fin q) (Fin q) ℂ)) :=
      measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
    apply ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hw)).add
    apply Finset.measurable_sum
    intro k hk
    exact (continuous_star.measurable.comp ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp hz))).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hz))

theorem leadingBlock_fromBlocks (z : Wishart.FieldHermitian.BlockSpace ℂ p q) :
    Wishart.FieldHermitian.leadingBlock ℂ (Wishart.FieldHermitian.fromBlocks ℂ z) = z.1 := by
  exact congrArg Prod.fst ((Wishart.FieldHermitian.blockCoordinates ℂ p q).apply_symm_apply z)

theorem wishartWeight_fromBlocks_eq_zero_of_not_posDef (α : ℝ)
    (S : Hermitian p) (hS : ¬ (S : Matrix (Fin p) (Fin p) ℂ).PosDef)
    (Z : Matrix (Fin p) (Fin q) ℂ) (W : Hermitian q) :
    wishartWeight α 1 (Wishart.FieldHermitian.fromBlocks ℂ (S,Z,W)) = 0 := by
  unfold wishartWeight
  apply if_neg
  intro hX
  have h := hX.submatrix (Fin.castAdd_injective p q)
  change (Wishart.FieldHermitian.leadingBlock ℂ
    (Wishart.FieldHermitian.fromBlocks ℂ (S,Z,W)) : Matrix (Fin p) (Fin p) ℂ).PosDef at h
  rw [leadingBlock_fromBlocks] at h
  exact hS h

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false in
local instance suffix5MatrixBorel (p q : ℕ) : BorelSpace (Matrix (Fin p) (Fin q) ℍ[ℝ]) :=
  inferInstanceAs (BorelSpace (Fin p → Fin q → ℍ[ℝ]))
set_option backward.isDefEq.respectTransparency false in
local instance suffix5HermitianBorel (p : ℕ) : BorelSpace (Hermitian p) :=
  inferInstanceAs (BorelSpace {X : Matrix (Fin p) (Fin p) ℍ[ℝ] // X ∈ selfAdjoint.submodule ℝ _})
variable {p q : ℕ}

theorem posDef_flatHermitian_iff (A : Hermitian p) :
    (flatHermitian A : Matrix (Fin (p * 2)) (Fin (p * 2)) ℂ).PosDef ↔ PosDef (A : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  constructor
  · intro h
    have h' := h.submatrix finProdFinEquiv.injective
    simpa only [flatHermitian, flatRepresentation, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id, PosDef] using h'
  · intro h
    exact Matrix.PosDef.submatrix h finProdFinEquiv.symm.injective

theorem isOpen_posDef_hermitian (p : ℕ) : IsOpen {A : Hermitian p | PosDef (A : Matrix (Fin p) (Fin p) ℍ[ℝ])} := by
  have h := (Wishart.FieldSpectral.isOpen_posDef_hermitian (𝕜 := ℂ) (p * 2)).preimage
    (continuous_flatHermitian p)
  simpa only [preimage_setOf_eq, posDef_flatHermitian_iff] using h

theorem measurable_wishartWeight (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    Measurable (wishartWeight α Sigma) := by
  unfold wishartWeight
  apply Measurable.ite (isOpen_posDef_hermitian p).measurableSet
  · apply Measurable.ennreal_ofReal
    apply Measurable.mul
    · exact (continuous_positiveDeterminant.comp continuous_subtype_val).measurable.pow_const _
    · exact ((Quaternion.continuous_re.measurable.comp (by fun_prop)).const_mul (-2)).exp
  · exact measurable_const

theorem measurable_schurInput : Measurable
    (fun z : Hermitian p × Matrix (Fin p) (Fin q) ℍ[ℝ] × Hermitian q =>
      schurInput z.1 z.2.2 z.2.1) := by
  have hfrom : Measurable (Wishart.FieldHermitian.fromBlocks ℍ[ℝ] :
      Wishart.FieldHermitian.BlockSpace ℍ[ℝ] p q → Hermitian (p + q)) :=
    Wishart.FieldHermitian.measurable_fromBlocks_entries ℍ[ℝ] p q
  apply hfrom.comp
  apply Measurable.prodMk measurable_fst
  apply Measurable.prodMk
  · have hs : Measurable (fun z : Wishart.FieldHermitian.BlockSpace ℍ[ℝ] p q =>
        sqrt (z.1 : Matrix (Fin p) (Fin p) ℍ[ℝ])) :=
      measurable_sqrt.comp (measurable_subtype_coe.comp measurable_fst)
    have hz : Measurable (fun z : Wishart.FieldHermitian.BlockSpace ℍ[ℝ] p q => z.2.1) :=
      measurable_fst.comp measurable_snd
    exact Wishart.FieldHermitian.measurable_matrix_product ℍ[ℝ] hs hz
  · apply Measurable.subtype_mk
    change Measurable (fun z : Wishart.FieldHermitian.BlockSpace ℍ[ℝ] p q =>
      (z.2.2 : Matrix (Fin q) (Fin q) ℍ[ℝ]) + z.2.1ᴴ * z.2.1)
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hz : Measurable (fun z : Wishart.FieldHermitian.BlockSpace ℍ[ℝ] p q => z.2.1) :=
      measurable_fst.comp measurable_snd
    have hw : Measurable (fun z : Wishart.FieldHermitian.BlockSpace ℍ[ℝ] p q =>
        (z.2.2 : Matrix (Fin q) (Fin q) ℍ[ℝ])) :=
      measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
    apply ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hw)).add
    apply Finset.measurable_sum
    intro k hk
    exact (continuous_star.measurable.comp ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp hz))).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hz))

theorem leadingBlock_fromBlocks (z : Wishart.FieldHermitian.BlockSpace ℍ[ℝ] p q) :
    Wishart.FieldHermitian.leadingBlock ℍ[ℝ]
      (Wishart.FieldHermitian.fromBlocks ℍ[ℝ] z) = z.1 := by
  exact congrArg Prod.fst ((Wishart.FieldHermitian.blockCoordinates ℍ[ℝ] p q).apply_symm_apply z)

theorem wishartWeight_fromBlocks_eq_zero_of_not_posDef (α : ℝ)
    (S : Hermitian p) (hS : ¬ PosDef (S : Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (Z : Matrix (Fin p) (Fin q) ℍ[ℝ]) (W : Hermitian q) :
    wishartWeight α 1 (Wishart.FieldHermitian.fromBlocks ℍ[ℝ] (S,Z,W)) = 0 := by
  unfold wishartWeight
  apply if_neg
  intro hX
  have hsub : PosDef ((Wishart.FieldHermitian.fromBlocks ℍ[ℝ] (S,Z,W) :
      Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]).submatrix (Fin.castAdd q) (Fin.castAdd q)) := by
    unfold PosDef
    rw [complexRepresentation_submatrix]
    apply Matrix.PosDef.submatrix hX
    intro a b hab
    exact Prod.ext ((Fin.castAdd_injective p q) (congrArg Prod.fst hab)) (congrArg (fun x : Fin (p + q) × Fin 2 => x.2) hab)
  change PosDef (Wishart.FieldHermitian.leadingBlock ℍ[ℝ]
    (Wishart.FieldHermitian.fromBlocks ℍ[ℝ] (S,Z,W)) : Matrix (Fin p) (Fin p) ℍ[ℝ]) at hsub
  rw [leadingBlock_fromBlocks] at hsub
  exact hS hsub

end Wishart.QuaternionMatrix
end
end CanonicalSource5

section CanonicalSource6
set_option backward.isDefEq.respectTransparency false
/- Source: Wishart/FieldSchurIntegration.lean -/



/-!
# The full weighted Schur substitution for complex and quaternion laws

The leading block is integrated over its ordinary Hermitian reference. Its
nonpositive-definite complement contributes zero because it cannot be the
leading block of a positive-definite full matrix. On each positive fiber the
rectangular substitution has the proved real Jacobian, and translation of
the trailing block preserves Lebesgue measure. This yields the weighted test
identity for every admissible real shape, before any normalization argument.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.FieldJacobian
open scoped Matrix.Norms.Frobenius

variable {F : Type*} [NormedRing F] [NormedAlgebra ℝ F] [FiniteDimensional ℝ F]
  {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def leftActionUnitEquiv (U : (Matrix n n F)ˣ) : Matrix n m F ≃ₗ[ℝ] Matrix n m F where
  toFun B := (U : Matrix n n F) * B
  invFun B := ((U⁻¹ : (Matrix n n F)ˣ) : Matrix n n F) * B
  left_inv B := by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv B := by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  map_add' B C := Matrix.mul_add _ _ _
  map_smul' r B := Matrix.mul_smul _ _ _

def leftActionCL (A : Matrix n n F) (hA : IsUnit A) : Matrix n m F ≃L[ℝ] Matrix n m F :=
  (leftActionUnitEquiv hA.unit).toContinuousLinearEquiv

@[simp] theorem leftActionCL_apply (A : Matrix n n F) (hA : IsUnit A) (B : Matrix n m F) :
    leftActionCL A hA B = A * B := by
  change (hA.unit : Matrix n n F) * B = A * B
  rw [hA.unit_spec]

theorem leftActionCL_toLinearMap (A : Matrix n n F) (hA : IsUnit A) :
    (leftActionCL (m := m) A hA : Matrix n m F →ₗ[ℝ] Matrix n m F) = leftAction A := by
  apply LinearMap.ext
  intro B
  change leftActionCL A hA B = A * B
  exact leftActionCL_apply A hA B

end Wishart.FieldJacobian

namespace Wishart.FieldHermitian
open scoped Matrix.Norms.Frobenius
variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F]
  [StarRing F] [CStarRing F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem measurable_fromBlocks (p q : ℕ) :
    Measurable (fromBlocks F : BlockSpace F p q → Hermitian F (p + q)) := by
  exact measurable_fromBlocks_entries F p q

theorem lintegral_fromBlocks (p q : ℕ)
    (f : Hermitian F (p + q) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ X, f X ∂hermitianLebesgue F (p + q)) =
      (blockCoordinateFactor F p q : ℝ≥0∞) *
        ∫⁻ S, ∫⁻ Z, ∫⁻ W, f (fromBlocks F (S,Z,W))
          ∂hermitianLebesgue F q ∂rectangularLebesgue F p q ∂hermitianLebesgue F p := by
  have h := lintegral_blockCoordinates F p q (fun z => f ((blockCoordinates F p q).symm z))
    (hf.comp (measurable_fromBlocks F p q))
  simpa only [LinearEquiv.symm_apply_apply, blockCoordinates_symm_apply] using h

end Wishart.FieldHermitian

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.L2Operator
open Wishart.FieldJacobian Wishart.FieldDensity WishartVerification
variable {p q : ℕ}

def sqrtLeftAction (S : Hermitian p) (hS : (S : Matrix (Fin p) (Fin p) ℂ).PosDef) :
    Matrix (Fin p) (Fin q) ℂ ≃L[ℝ] Matrix (Fin p) (Fin q) ℂ :=
  leftActionCL (CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ))
    ((CFC.isUnit_sqrt_iff _ hS.posSemidef.nonneg).mpr hS.isUnit)

@[simp] theorem sqrtLeftAction_apply (S : Hermitian p)
    (hS : (S : Matrix (Fin p) (Fin p) ℂ).PosDef) (Z : Matrix (Fin p) (Fin q) ℂ) :
    sqrtLeftAction S hS Z = CFC.sqrt (S : Matrix (Fin p) (Fin p) ℂ) * Z :=
  leftActionCL_apply _ _ Z

theorem sqrtLeftAction_jacobian (S : Hermitian p)
    (hS : (S : Matrix (Fin p) (Fin p) ℂ).PosDef) :
    ENNReal.ofReal |LinearMap.det (sqrtLeftAction (q := q) S hS :
      Matrix (Fin p) (Fin q) ℂ →ₗ[ℝ] Matrix (Fin p) (Fin q) ℂ)| =
      ENNReal.ofReal (realDeterminant (S : Matrix (Fin p) (Fin p) ℂ) ^ (q : ℝ)) := by
  unfold sqrtLeftAction
  rw [leftActionCL_toLinearMap, det_real_leftAction_sqrt hS.posSemidef,
    abs_of_nonneg (pow_nonneg (realDeterminant_pos hS).le q), Real.rpow_natCast]

theorem lintegral_wishartWeight_schur (α : ℝ)
    (f : Hermitian (p + q) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ X, wishartWeight α 1 X * f X ∂hermitianLebesgue (p + q)) =
      (Wishart.FieldHermitian.blockCoordinateFactor ℂ p q : ℝ≥0∞) *
        ∫⁻ S, ∫⁻ Z, ∫⁻ W,
          (wishartWeight α 1 S *
            (ENNReal.ofReal (Real.exp (-rectangularNormSquare Z)) * wishartWeight (α - p) 1 W)) *
            f (schurInput S W Z)
          ∂hermitianLebesgue q ∂Wishart.FieldHermitian.rectangularLebesgue ℂ p q
          ∂hermitianLebesgue p := by
  have hmeasure (r : ℕ) : hermitianLebesgue r = Wishart.FieldHermitian.hermitianLebesgue ℂ r := by
    unfold hermitianLebesgue Wishart.FieldHermitian.hermitianLebesgue
    simp only [Module.Basis.addHaar_def]
    rfl
  rw [hmeasure (p + q), Wishart.FieldHermitian.lintegral_fromBlocks ℂ p q (fun X => wishartWeight α 1 X * f X)
    ((measurable_wishartWeight α 1).mul hf)]
  simp only [← hmeasure]
  congr 1
  apply lintegral_congr
  intro S
  by_cases hS : (S : Matrix (Fin p) (Fin p) ℂ).PosDef
  · let G (Z : Matrix (Fin p) (Fin q) ℂ) : Hermitian q :=
      ⟨Zᴴ * Z, Matrix.isHermitian_conjTranspose_mul_self Z⟩
    have htest : Measurable (fun z : Matrix (Fin p) (Fin q) ℂ × Hermitian q =>
        wishartWeight α 1 (Wishart.FieldHermitian.fromBlocks ℂ (S,z.1,z.2)) *
          f (Wishart.FieldHermitian.fromBlocks ℂ (S,z.1,z.2))) :=
      ((measurable_wishartWeight α 1).mul hf).comp
        ((Wishart.FieldHermitian.measurable_fromBlocks ℂ p q).comp
          (measurable_const.prodMk measurable_id))
    rw [← lintegral_schur_fiber
      (Wishart.FieldHermitian.rectangularLebesgue ℂ p q) (hermitianLebesgue q)
      (sqrtLeftAction S hS) G _ htest]
    apply lintegral_congr
    intro Z
    apply lintegral_congr
    intro W
    rw [sqrtLeftAction_jacobian, sqrtLeftAction_apply]
    change ENNReal.ofReal (realDeterminant (S : Matrix (Fin p) (Fin p) ℂ) ^ (q : ℝ)) *
      (wishartWeight α 1 (schurInput S W Z) * f (schurInput S W Z)) = _
    calc
      _ = (wishartWeight α 1 (schurInput S W Z) *
        ENNReal.ofReal (realDeterminant (S : Matrix (Fin p) (Fin p) ℂ) ^ (q : ℝ))) * f (schurInput S W Z) := by ac_rfl
      _ = _ := by rw [wishartWeight_schur_all α S hS W Z]; ac_rfl
  · simp_rw [wishartWeight_fromBlocks_eq_zero_of_not_posDef α S hS,
      show wishartWeight α 1 S = 0 from by rw [wishartWeight, if_neg hS]]
    simp only [zero_mul, lintegral_zero]

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false in
local instance suffix6MatrixBorel (p q : ℕ) : BorelSpace (Matrix (Fin p) (Fin q) ℍ[ℝ]) :=
  inferInstanceAs (BorelSpace (Fin p → Fin q → ℍ[ℝ]))
set_option backward.isDefEq.respectTransparency false in
local instance suffix6HermitianBorel (p : ℕ) : BorelSpace (Hermitian p) :=
  inferInstanceAs (BorelSpace {X : Matrix (Fin p) (Fin p) ℍ[ℝ] // X ∈ selfAdjoint.submodule ℝ _})
open Wishart.FieldJacobian Wishart.FieldDensity WishartVerification
variable {p q : ℕ}

def sqrtLeftAction (S : Hermitian p) (hS : PosDef (S : Matrix (Fin p) (Fin p) ℍ[ℝ])) :
    Matrix (Fin p) (Fin q) ℍ[ℝ] ≃L[ℝ] Matrix (Fin p) (Fin q) ℍ[ℝ] :=
  leftActionCL (sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ])) hS.sqrt.isUnit

@[simp] theorem sqrtLeftAction_apply (S : Hermitian p)
    (hS : PosDef (S : Matrix (Fin p) (Fin p) ℍ[ℝ])) (Z : Matrix (Fin p) (Fin q) ℍ[ℝ]) :
    sqrtLeftAction S hS Z = sqrt (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) * Z :=
  leftActionCL_apply _ _ Z

theorem sqrtLeftAction_jacobian (S : Hermitian p)
    (hS : PosDef (S : Matrix (Fin p) (Fin p) ℍ[ℝ])) :
    ENNReal.ofReal |LinearMap.det (sqrtLeftAction (q := q) S hS :
      Matrix (Fin p) (Fin q) ℍ[ℝ] →ₗ[ℝ] Matrix (Fin p) (Fin q) ℍ[ℝ])| =
      ENNReal.ofReal (positiveDeterminant (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) ^ (2 * (q : ℝ))) := by
  unfold sqrtLeftAction
  rw [leftActionCL_toLinearMap, det_real_leftAction_sqrt hS.posSemidef,
    abs_of_nonneg (pow_nonneg (positiveDeterminant_nonneg _) (2 * q))]
  congr 1
  norm_cast

theorem lintegral_wishartWeight_schur (α : ℝ)
    (f : Hermitian (p + q) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ X, wishartWeight α 1 X * f X ∂hermitianLebesgue (p + q)) =
      (Wishart.FieldHermitian.blockCoordinateFactor ℍ[ℝ] p q : ℝ≥0∞) *
        ∫⁻ S, ∫⁻ Z, ∫⁻ W,
          (wishartWeight α 1 S *
            (ENNReal.ofReal (Real.exp (-2 * rectangularNormSquare Z)) * wishartWeight (α - p) 1 W)) *
            f (schurInput S W Z)
          ∂hermitianLebesgue q ∂Wishart.FieldHermitian.rectangularLebesgue ℍ[ℝ] p q
          ∂hermitianLebesgue p := by
  have hmeasure (r : ℕ) : hermitianLebesgue r = Wishart.FieldHermitian.hermitianLebesgue ℍ[ℝ] r := by rfl
  rw [hmeasure (p + q), Wishart.FieldHermitian.lintegral_fromBlocks ℍ[ℝ] p q (fun X => wishartWeight α 1 X * f X)
    ((measurable_wishartWeight α 1).mul hf)]
  simp only [← hmeasure]
  congr 1
  apply lintegral_congr
  intro S
  by_cases hS : PosDef (S : Matrix (Fin p) (Fin p) ℍ[ℝ])
  · let G (Z : Matrix (Fin p) (Fin q) ℍ[ℝ]) : Hermitian q :=
      ⟨Zᴴ * Z, Matrix.isHermitian_conjTranspose_mul_self Z⟩
    have htest : Measurable (fun z : Matrix (Fin p) (Fin q) ℍ[ℝ] × Hermitian q =>
        wishartWeight α 1 (Wishart.FieldHermitian.fromBlocks ℍ[ℝ] (S,z.1,z.2)) *
          f (Wishart.FieldHermitian.fromBlocks ℍ[ℝ] (S,z.1,z.2))) :=
      ((measurable_wishartWeight α 1).mul hf).comp
        ((Wishart.FieldHermitian.measurable_fromBlocks ℍ[ℝ] p q).comp
          (measurable_const.prodMk measurable_id))
    rw [← lintegral_schur_fiber
      (Wishart.FieldHermitian.rectangularLebesgue ℍ[ℝ] p q) (hermitianLebesgue q)
      (sqrtLeftAction S hS) G _ htest]
    apply lintegral_congr
    intro Z
    apply lintegral_congr
    intro W
    rw [sqrtLeftAction_jacobian, sqrtLeftAction_apply]
    change ENNReal.ofReal (positiveDeterminant (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) ^ (2 * (q : ℝ))) *
      (wishartWeight α 1 (schurInput S W Z) * f (schurInput S W Z)) = _
    calc
      _ = (wishartWeight α 1 (schurInput S W Z) *
        ENNReal.ofReal (positiveDeterminant (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) ^ (2 * (q : ℝ)))) * f (schurInput S W Z) := by ac_rfl
      _ = _ := by rw [wishartWeight_schur_all α S hS W Z]; ac_rfl
  · simp_rw [wishartWeight_fromBlocks_eq_zero_of_not_posDef α S hS,
      show wishartWeight α 1 S = 0 from by rw [wishartWeight, if_neg hS]]
    simp only [zero_mul, lintegral_zero]

end Wishart.QuaternionMatrix
end
end CanonicalSource6

section CanonicalSource7
set_option backward.isDefEq.respectTransparency false
/- Source: Wishart/FieldWishartNormalization.lean -/



/-!
# Normalization at every admissible real shape

The Schur identity determines the literal matrix density by induction in
dimension. The induction begins with the ordinary scalar Gamma integrals,
and its other source is the actual independent field Gaussian matrix. This
does not pass through an integer Gram representation of the Wishart law.
The zero-dimensional case is the positive finite Haar mass of a point.
-/

noncomputable section
open MeasureTheory.Measure
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal

namespace WishartVerification.FieldDensity

theorem finiteDensity_one_of_compact (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompactSpace E] (μ : Measure E) [IsAddHaarMeasure μ] :
    FiniteDensity μ (fun _ => 1) := by
  have hmass : normalizer μ (fun _ => 1) = μ univ := by
    simp [normalizer]
  refine ⟨?_, ?_⟩
  · rw [hmass]
    exact isOpen_univ.measure_pos μ Set.univ_nonempty
  · rw [hmass]
    exact isCompact_univ.measure_lt_top

end WishartVerification.FieldDensity

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.L2Operator
open WishartVerification.FieldDensity Wishart.FieldDensity

variable {p q : ℕ}

theorem normalized_standard_matrix_gaussian (p q : ℕ) :
    normalized (Wishart.FieldHermitian.rectangularLebesgue ℂ p q)
      (fun Z => ENNReal.ofReal (Real.exp (-rectangularNormSquare Z))) =
        Wishart.FieldGaussian.matrixGaussian ℂ p q := by
  have h := (Wishart.FieldGaussian.finiteDensity_matrixKernel_and_law ℂ p q
    (by simp [Complex.finrank_real_complex])).2
  have hk : (Wishart.FieldGaussian.matrixKernel ℂ : Matrix (Fin p) (Fin q) ℂ → ℝ≥0∞) =
      (fun Z => ENNReal.ofReal (Real.exp (-rectangularNormSquare Z))) := by
    funext Z
    simp [Wishart.FieldGaussian.matrixKernel, Complex.finrank_real_complex]
  rw [hk] at h
  exact h

/-- The exact normalized Schur decomposition, provided the two smaller
literal densities have already been normalized. -/
theorem finiteDensity_and_schur_law (α : ℝ)
    (hS : FiniteDensity (hermitianLebesgue p) (wishartWeight α 1))
    (hW : FiniteDensity (hermitianLebesgue q) (wishartWeight (α - p) 1)) :
    FiniteDensity (hermitianLebesgue (p + q)) (wishartWeight α 1) ∧
      wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) =
        ((wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ)).prod
          ((Wishart.FieldGaussian.matrixGaussian ℂ p q).prod
            (wishartMeasure (α - p) (1 : Matrix (Fin q) (Fin q) ℂ)))).map
          (fun z => schurInput z.1 z.2.2 z.2.1) := by
  have hg : Measurable (fun Z : Matrix (Fin p) (Fin q) ℂ =>
      ENNReal.ofReal (Real.exp (-rectangularNormSquare Z))) := by
    unfold rectangularNormSquare
    fun_prop
  have hchange := product_factorization_of_nested
    (hermitianLebesgue (p + q)) (hermitianLebesgue p)
    (Wishart.FieldHermitian.rectangularLebesgue ℂ p q) (hermitianLebesgue q)
    (wishartWeight α 1) (wishartWeight α 1)
    (fun Z => ENNReal.ofReal (Real.exp (-rectangularNormSquare Z)))
    (wishartWeight (α - p) 1) (measurable_wishartWeight α 1) hg
    (measurable_wishartWeight (α - p) 1)
    (fun z => schurInput z.1 z.2.2 z.2.1) measurable_schurInput
    (Wishart.FieldHermitian.blockCoordinateFactor ℂ p q)
    (fun f hf => lintegral_wishartWeight_schur α f hf)
  have h := normalize_product_factorization
    (hermitianLebesgue (p + q)) (hermitianLebesgue p)
    (Wishart.FieldHermitian.rectangularLebesgue ℂ p q) (hermitianLebesgue q)
    (wishartWeight α 1) (wishartWeight α 1)
    (fun Z => ENNReal.ofReal (Real.exp (-rectangularNormSquare Z)))
    (wishartWeight (α - p) 1) (measurable_wishartWeight α 1)
    (measurable_wishartWeight α 1) hg (measurable_wishartWeight (α - p) 1)
    hS (finiteDensity_standard_matrix_gaussian p q) hW
    (fun z => schurInput z.1 z.2.2 z.2.1) measurable_schurInput
    (by exact_mod_cast Wishart.FieldHermitian.blockCoordinateFactor_pos ℂ p q)
    ENNReal.coe_lt_top hchange
  refine ⟨h.2.1, ?_⟩
  have hmap := h.2.2
  rw [normalized_standard_matrix_gaussian] at hmap
  simpa only [wishartMeasure, wishartNormalizer, normalized, normalizer] using hmap

theorem wishartWeight_dimension_zero (α : ℝ) (X : Hermitian 0) :
    wishartWeight α (1 : Matrix (Fin 0) (Fin 0) ℂ) X = 1 := by
  have hX : (X : Matrix (Fin 0) (Fin 0) ℂ) = 1 := Subsingleton.elim _ _
  simp [wishartWeight, hX, Matrix.PosDef.one, realDeterminant, Matrix.trace]

theorem finiteDensity_wishart_standard (p : ℕ) {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    FiniteDensity (hermitianLebesgue p) (wishartWeight α 1) := by
  induction p generalizing α with
  | zero =>
      have h := finiteDensity_one_of_compact (Hermitian 0) (hermitianLebesgue 0)
      simpa only [show wishartWeight α (1 : Matrix (Fin 0) (Fin 0) ℂ) =
        (fun _ => 1) from funext (wishartWeight_dimension_zero α)] using h
  | succ n ih =>
      have hnα : (n : ℝ) < α := by simpa only [Nat.cast_succ, add_sub_cancel_right] using hα
      have hα0 : 0 < α := lt_of_le_of_lt (Nat.cast_nonneg n) hnα
      have hsmall : (n : ℝ) - 1 < α - 1 := by linarith
      have h := (finiteDensity_and_schur_law (p := 1) (q := n) α
        (finiteDensity_wishart_one hα0) (by simpa only [Nat.cast_one] using ih hsmall)).1
      let P : ℕ → Prop := fun r => FiniteDensity (hermitianLebesgue r)
        (wishartWeight α (1 : Matrix (Fin r) (Fin r) ℂ))
      exact Eq.mp (congrArg P (Nat.add_comm 1 n)) h

theorem wishart_standard_probability (p : ℕ) {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    IsProbabilityMeasure (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ)) :=
  isProbability_normalized (finiteDensity_wishart_standard p hα)

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false in
local instance suffix7MatrixBorel (p q : ℕ) : BorelSpace (Matrix (Fin p) (Fin q) ℍ[ℝ]) :=
  inferInstanceAs (BorelSpace (Fin p → Fin q → ℍ[ℝ]))
set_option backward.isDefEq.respectTransparency false in
local instance suffix7HermitianBorel (p : ℕ) : BorelSpace (Hermitian p) :=
  inferInstanceAs (BorelSpace {X : Matrix (Fin p) (Fin p) ℍ[ℝ] // X ∈ selfAdjoint.submodule ℝ _})
open WishartVerification.FieldDensity Wishart.FieldDensity

variable {p q : ℕ}

theorem normalized_standard_matrix_gaussian (p q : ℕ) :
    normalized (Wishart.FieldHermitian.rectangularLebesgue ℍ[ℝ] p q)
      (fun Z => ENNReal.ofReal (Real.exp (-2 * rectangularNormSquare Z))) =
        Wishart.FieldGaussian.matrixGaussian ℍ[ℝ] p q := by
  have h := (Wishart.FieldGaussian.finiteDensity_matrixKernel_and_law ℍ[ℝ] p q
    (by simp [Quaternion.finrank_eq_four])).2
  have hk : (Wishart.FieldGaussian.matrixKernel ℍ[ℝ] : Matrix (Fin p) (Fin q) ℍ[ℝ] → ℝ≥0∞) =
      (fun Z => ENNReal.ofReal (Real.exp (-2 * rectangularNormSquare Z))) := by
    funext Z
    norm_num [Wishart.FieldGaussian.matrixKernel, Quaternion.finrank_eq_four]
  rw [hk] at h
  exact h

theorem finiteDensity_and_schur_law (α : ℝ)
    (hS : FiniteDensity (hermitianLebesgue p) (wishartWeight α 1))
    (hW : FiniteDensity (hermitianLebesgue q) (wishartWeight (α - p) 1)) :
    FiniteDensity (hermitianLebesgue (p + q)) (wishartWeight α 1) ∧
      wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) =
        ((wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])).prod
          ((Wishart.FieldGaussian.matrixGaussian ℍ[ℝ] p q).prod
            (wishartMeasure (α - p) (1 : Matrix (Fin q) (Fin q) ℍ[ℝ])))).map
          (fun z => schurInput z.1 z.2.2 z.2.1) := by
  have hg : Measurable (fun Z : Matrix (Fin p) (Fin q) ℍ[ℝ] =>
      ENNReal.ofReal (Real.exp (-2 * rectangularNormSquare Z))) := by
    unfold rectangularNormSquare
    fun_prop
  have hchange := product_factorization_of_nested
    (hermitianLebesgue (p + q)) (hermitianLebesgue p)
    (Wishart.FieldHermitian.rectangularLebesgue ℍ[ℝ] p q) (hermitianLebesgue q)
    (wishartWeight α 1) (wishartWeight α 1)
    (fun Z => ENNReal.ofReal (Real.exp (-2 * rectangularNormSquare Z)))
    (wishartWeight (α - p) 1) (measurable_wishartWeight α 1) hg
    (measurable_wishartWeight (α - p) 1)
    (fun z => schurInput z.1 z.2.2 z.2.1) measurable_schurInput
    (Wishart.FieldHermitian.blockCoordinateFactor ℍ[ℝ] p q)
    (fun f hf => lintegral_wishartWeight_schur α f hf)
  have h := normalize_product_factorization
    (hermitianLebesgue (p + q)) (hermitianLebesgue p)
    (Wishart.FieldHermitian.rectangularLebesgue ℍ[ℝ] p q) (hermitianLebesgue q)
    (wishartWeight α 1) (wishartWeight α 1)
    (fun Z => ENNReal.ofReal (Real.exp (-2 * rectangularNormSquare Z)))
    (wishartWeight (α - p) 1) (measurable_wishartWeight α 1)
    (measurable_wishartWeight α 1) hg (measurable_wishartWeight (α - p) 1)
    hS (finiteDensity_standard_matrix_gaussian p q) hW
    (fun z => schurInput z.1 z.2.2 z.2.1) measurable_schurInput
    (by exact_mod_cast Wishart.FieldHermitian.blockCoordinateFactor_pos ℍ[ℝ] p q)
    ENNReal.coe_lt_top hchange
  refine ⟨h.2.1, ?_⟩
  have hmap := h.2.2
  rw [normalized_standard_matrix_gaussian] at hmap
  simpa only [wishartMeasure, wishartNormalizer, normalized, normalizer] using hmap

theorem wishartWeight_dimension_zero (α : ℝ) (X : Hermitian 0) :
    wishartWeight α (1 : Matrix (Fin 0) (Fin 0) ℍ[ℝ]) X = 1 := by
  have hX : (X : Matrix (Fin 0) (Fin 0) ℍ[ℝ]) = 1 := Subsingleton.elim _ _
  have hpd : PosDef (1 : Matrix (Fin 0) (Fin 0) ℍ[ℝ]) := by
    rw [PosDef, complexRepresentation_one]
    exact Matrix.PosDef.one
  simp [wishartWeight, hX, hpd, positiveDeterminant, complexRepresentation_one, Matrix.trace]

theorem finiteDensity_wishart_standard (p : ℕ) {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    FiniteDensity (hermitianLebesgue p) (wishartWeight α 1) := by
  induction p generalizing α with
  | zero =>
      letI := hermitianLebesgue_isAddHaar 0
      have h := finiteDensity_one_of_compact (Hermitian 0) (hermitianLebesgue 0)
      simpa only [show wishartWeight α (1 : Matrix (Fin 0) (Fin 0) ℍ[ℝ]) =
        (fun _ => 1) from funext (wishartWeight_dimension_zero α)] using h
  | succ n ih =>
      have hnα : (n : ℝ) < α := by simpa only [Nat.cast_succ, add_sub_cancel_right] using hα
      have hα0 : 0 < α := lt_of_le_of_lt (Nat.cast_nonneg n) hnα
      have hsmall : (n : ℝ) - 1 < α - 1 := by linarith
      have h := (finiteDensity_and_schur_law (p := 1) (q := n) α
        (finiteDensity_wishart_one hα0) (by simpa only [Nat.cast_one] using ih hsmall)).1
      let P : ℕ → Prop := fun r => FiniteDensity (hermitianLebesgue r)
        (wishartWeight α (1 : Matrix (Fin r) (Fin r) ℍ[ℝ]))
      exact Eq.mp (congrArg P (Nat.add_comm 1 n)) h

theorem wishart_standard_probability (p : ℕ) {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    IsProbabilityMeasure (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])) :=
  isProbability_normalized (finiteDensity_wishart_standard p hα)

end Wishart.QuaternionMatrix
end
end CanonicalSource7

section CanonicalSource8
set_option backward.isDefEq.respectTransparency false
/- Source: Wishart/FieldWishartCongruence.lean -/




/-!
# Covariance transport of the literal field Wishart densities

Congruence is an actual real linear equivalence of the Hermitian spaces.
Its Haar scalar is absorbed by normalization. The density comparison uses
the ordinary complex determinant or the positive Moore determinant, and the
real trace cyclic identity in the quaternion case. Thus the positive finite
normalizer at identity covariance implies it for every positive covariance.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder Ring ENNReal
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.FieldHermitian
open scoped Matrix.Norms.Frobenius

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F]
  [StarRing F] [CStarRing F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {p : ℕ}

def congruence (R : Matrix (Fin p) (Fin p) F) (X : Hermitian F p) : Hermitian F p :=
  ⟨Rᴴ * (X : Matrix (Fin p) (Fin p) F) * R,
    Matrix.isHermitian_conjTranspose_mul_mul R (WishartVerification.hermitian_matrix_coe X)⟩

@[simp] theorem congruence_one (X : Hermitian F p) : congruence F 1 X = X := by
  apply Subtype.ext
  simp [congruence]

theorem congruence_comp (R S : Matrix (Fin p) (Fin p) F) (X : Hermitian F p) :
    congruence F S (congruence F R X) = congruence F (R * S) X := by
  apply Subtype.ext
  simp only [congruence, Matrix.conjTranspose_mul, Matrix.mul_assoc]

def congruenceLinearEquiv (U : (Matrix (Fin p) (Fin p) F)ˣ) :
    Hermitian F p ≃ₗ[ℝ] Hermitian F p where
  toFun := congruence F (U : Matrix (Fin p) (Fin p) F)
  invFun := congruence F ((U⁻¹ : (Matrix (Fin p) (Fin p) F)ˣ) : Matrix (Fin p) (Fin p) F)
  left_inv X := by rw [congruence_comp, Units.mul_inv, congruence_one]
  right_inv X := by rw [congruence_comp, Units.inv_mul, congruence_one]
  map_add' X Y := by
    apply Subtype.ext
    change (U : Matrix (Fin p) (Fin p) F)ᴴ * ((X : Matrix (Fin p) (Fin p) F) + Y) * U =
      (U : Matrix (Fin p) (Fin p) F)ᴴ * X * U + (U : Matrix (Fin p) (Fin p) F)ᴴ * Y * U
    simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by
    apply Subtype.ext
    simp only [congruence, Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

def congruenceCL (R : Matrix (Fin p) (Fin p) F) (hR : IsUnit R) :
    Hermitian F p ≃L[ℝ] Hermitian F p :=
  (congruenceLinearEquiv F hR.unit).toContinuousLinearEquiv

@[simp] theorem congruenceCL_apply (R : Matrix (Fin p) (Fin p) F) (hR : IsUnit R)
    (X : Hermitian F p) : congruenceCL F R hR X = congruence F R X := by
  change congruence F (hR.unit : Matrix (Fin p) (Fin p) F) X = congruence F R X
  rw [hR.unit_spec]

end Wishart.FieldHermitian

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.L2Operator
open WishartVerification.FieldDensity
variable {p : ℕ}

theorem realDeterminant_congruence {X : Matrix (Fin p) (Fin p) ℂ}
    (hX : X.PosSemidef) (R : Matrix (Fin p) (Fin p) ℂ) :
    realDeterminant (Rᴴ * X * R) = realDeterminant (Rᴴ * R) * realDeterminant X := by
  have hXi : X.det.im = 0 := (RCLike.nonneg_iff.mp hX.det_nonneg).2
  have hdet : (Rᴴ * X * R).det = (Rᴴ * R).det * X.det := by
    simp only [Matrix.det_mul]
    ring
  unfold realDeterminant
  rw [hdet, Complex.mul_re, hXi, mul_zero, sub_zero]

theorem trace_inverse_gram_congruence (R X : Matrix (Fin p) (Fin p) ℂ)
    (hR : IsUnit R) :
    (((Rᴴ * R)⁻¹ * (Rᴴ * X * R)).trace).re = X.trace.re := by
  have hRt : IsUnit Rᴴ := by simpa only [Matrix.star_eq_conjTranspose] using hR.star
  have hcancel : R * (Rᴴ * R)⁻¹ * Rᴴ = 1 := by
    calc
      _ = (R * R⁻¹) * ((Rᴴ)⁻¹ * Rᴴ) := by
        rw [Matrix.mul_inv_rev]
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR),
          Matrix.nonsing_inv_mul Rᴴ ((Matrix.isUnit_iff_isUnit_det Rᴴ).mp hRt), one_mul]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle,
    ← Matrix.mul_assoc, hcancel, one_mul]

theorem wishartWeight_congruence_standard (α : ℝ) (R : Matrix (Fin p) (Fin p) ℂ)
    (hR : IsUnit R) (X : Hermitian p) :
    wishartWeight α (Rᴴ * R) (Wishart.FieldHermitian.congruence ℂ R X) =
      ENNReal.ofReal (realDeterminant (Rᴴ * R) ^ (α - p)) * wishartWeight α 1 X := by
  have hgram : (Rᴴ * R).PosDef :=
    by simpa only [Matrix.mul_one] using
      Matrix.PosDef.conjTranspose_mul_mul_same Matrix.PosDef.one
        (Matrix.mulVec_injective_of_isUnit hR)
  have hiff : (Rᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * R).PosDef ↔
      (X : Matrix (Fin p) (Fin p) ℂ).PosDef :=
    hR.posDef_star_left_conjugate_iff
  by_cases hX : (X : Matrix (Fin p) (Fin p) ℂ).PosDef
  · simp only [wishartWeight, Wishart.FieldHermitian.congruence]
    rw [if_pos (hiff.mpr hX), if_pos hX]
    change ENNReal.ofReal
      (realDeterminant (Rᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * R) ^ (α - p) *
        Real.exp (-(((Rᴴ * R)⁻¹ * (Rᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * R)).trace).re)) = _
    rw [realDeterminant_congruence hX.posSemidef,
      Real.mul_rpow (realDeterminant_pos hgram).le (realDeterminant_pos hX).le,
      trace_inverse_gram_congruence R _ hR]
    simp only [inv_one, one_mul]
    rw [mul_assoc, ENNReal.ofReal_mul (Real.rpow_nonneg (realDeterminant_pos hgram).le _)]
  · simp only [wishartWeight, Wishart.FieldHermitian.congruence]
    rw [if_neg (hiff.not.mpr hX), if_neg hX, mul_zero]

theorem finiteDensity_wishart_and_covariance_law {α : ℝ}
    (hα : (p : ℝ) - 1 < α) {Sigma : Matrix (Fin p) (Fin p) ℂ} (hSigma : Sigma.PosDef) :
    FiniteDensity (hermitianLebesgue p) (wishartWeight α Sigma) ∧
      wishartMeasure α Sigma = (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ)).map
        (Wishart.FieldHermitian.congruence ℂ (CFC.sqrt Sigma)) := by
  let R := CFC.sqrt Sigma
  have hRpd : R.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (Matrix.isStrictlyPositive_iff_posDef.mpr hSigma).sqrt
  have hR : IsUnit R := hRpd.isUnit
  have hRR : Rᴴ * R = Sigma := by
    rw [hRpd.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self Sigma hSigma.posSemidef.nonneg
  have ha : 0 < realDeterminant Sigma ^ (α - p) := Real.rpow_pos_of_pos (realDeterminant_pos hSigma) _
  have h := normalized_transport_haar_scaled (Wishart.FieldHermitian.congruenceCL ℂ R hR)
    (hermitianLebesgue p) (hermitianLebesgue p)
    (wishartWeight α 1) (wishartWeight α Sigma) (finiteDensity_wishart_standard p hα)
    (ENNReal.ofReal_pos.mpr ha) ENNReal.ofReal_lt_top
    (fun X => by
      rw [Wishart.FieldHermitian.congruenceCL_apply, ← hRR]
      exact wishartWeight_congruence_standard α R hR X)
  refine ⟨h.1, ?_⟩
  have hmap := h.2
  have he : (Wishart.FieldHermitian.congruenceCL ℂ R hR : Hermitian p → Hermitian p) =
      Wishart.FieldHermitian.congruence ℂ R := funext (Wishart.FieldHermitian.congruenceCL_apply ℂ R hR)
  rw [he] at hmap
  simpa only [wishartMeasure, wishartNormalizer, normalized, normalizer] using hmap

theorem wishart_probability {α : ℝ} (hα : (p : ℝ) - 1 < α)
    {Sigma : Matrix (Fin p) (Fin p) ℂ} (hSigma : Sigma.PosDef) :
    IsProbabilityMeasure (wishartMeasure α Sigma) :=
  isProbability_normalized (finiteDensity_wishart_and_covariance_law hα hSigma).1

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false in
local instance suffix8MatrixBorel (p q : ℕ) : BorelSpace (Matrix (Fin p) (Fin q) ℍ[ℝ]) :=
  inferInstanceAs (BorelSpace (Fin p → Fin q → ℍ[ℝ]))
set_option backward.isDefEq.respectTransparency false in
local instance suffix8HermitianBorel (p : ℕ) : BorelSpace (Hermitian p) :=
  inferInstanceAs (BorelSpace {X : Matrix (Fin p) (Fin p) ℍ[ℝ] // X ∈ selfAdjoint.submodule ℝ _})
open WishartVerification.FieldDensity
variable {p : ℕ}

theorem isUnit_posDef_congruence_iff (R : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (hR : IsUnit R) (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    PosDef (Rᴴ * X * R) ↔ PosDef X := by
  unfold PosDef
  rw [complexRepresentation_congruence]
  exact (hR.map complexRepresentationStarAlgHom).posDef_star_left_conjugate_iff

theorem trace_inverse_gram_congruence (R X : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (hR : IsUnit R) :
    (((Rᴴ * R)⁻¹ʳ * (Rᴴ * X * R)).trace).re = X.trace.re := by
  have hRt : IsUnit Rᴴ := by simpa only [Matrix.star_eq_conjTranspose] using hR.star
  have hcancel : R * (Rᴴ * R)⁻¹ʳ * Rᴴ = 1 := by
    calc
      _ = (R * R⁻¹ʳ) * ((Rᴴ)⁻¹ʳ * Rᴴ) := by
        rw [Ring.inverse_mul (Or.inl hRt)]
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Ring.mul_inverse_cancel R hR, Ring.inverse_mul_cancel Rᴴ hRt, one_mul]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, real_trace_mul_comm,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hcancel, one_mul]

theorem wishartWeight_congruence_standard (α : ℝ) (R : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (hR : IsUnit R) (X : Hermitian p) :
    wishartWeight α (Rᴴ * R) (Wishart.FieldHermitian.congruence ℍ[ℝ] R X) =
      ENNReal.ofReal (positiveDeterminant (Rᴴ * R) ^ (2 * (α - p + 1) - 1)) *
        wishartWeight α 1 X := by
  have hgram : PosDef (Rᴴ * R) := by
    simpa only [Matrix.mul_one] using
      (isUnit_posDef_congruence_iff R hR 1).mpr
        (show PosDef (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) from by
          rw [PosDef, complexRepresentation_one]; exact Matrix.PosDef.one)
  have hiff := isUnit_posDef_congruence_iff R hR (X : Matrix (Fin p) (Fin p) ℍ[ℝ])
  by_cases hX : PosDef (X : Matrix (Fin p) (Fin p) ℍ[ℝ])
  · simp only [wishartWeight, Wishart.FieldHermitian.congruence]
    rw [if_pos (hiff.mpr hX), if_pos hX]
    change ENNReal.ofReal
      (positiveDeterminant (Rᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * R) ^ (2 * (α - p + 1) - 1) *
        Real.exp (-2 * (((Rᴴ * R)⁻¹ʳ * (Rᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * R)).trace).re)) = _
    rw [positiveDeterminant_congruence hX.posSemidef,
      Real.mul_rpow (positiveDeterminant_nonneg _) (positiveDeterminant_nonneg _),
      trace_inverse_gram_congruence R _ hR]
    simp only [Ring.inverse_one, one_mul]
    rw [mul_assoc, ENNReal.ofReal_mul (Real.rpow_nonneg (positiveDeterminant_nonneg _) _)]
  · simp only [wishartWeight, Wishart.FieldHermitian.congruence]
    rw [if_neg (hiff.not.mpr hX), if_neg hX, mul_zero]

theorem finiteDensity_wishart_and_covariance_law {α : ℝ}
    (hα : (p : ℝ) - 1 < α) {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hSigma : PosDef Sigma) :
    FiniteDensity (hermitianLebesgue p) (wishartWeight α Sigma) ∧
      wishartMeasure α Sigma = (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])).map
        (Wishart.FieldHermitian.congruence ℍ[ℝ] (sqrt Sigma)) := by
  let R := sqrt Sigma
  have hRpd : PosDef R := hSigma.sqrt
  have hR : IsUnit R := hRpd.isUnit
  have hRR : Rᴴ * R = Sigma := by
    rw [hRpd.isHermitian.eq]
    exact sqrt_mul_self hSigma.posSemidef
  have ha : 0 < positiveDeterminant Sigma ^ (2 * (α - p + 1) - 1) :=
    Real.rpow_pos_of_pos hSigma.positiveDeterminant_pos _
  have h := normalized_transport_haar_scaled (Wishart.FieldHermitian.congruenceCL ℍ[ℝ] R hR)
    (hermitianLebesgue p) (hermitianLebesgue p)
    (wishartWeight α 1) (wishartWeight α Sigma) (finiteDensity_wishart_standard p hα)
    (ENNReal.ofReal_pos.mpr ha) ENNReal.ofReal_lt_top
    (fun X => by
      rw [Wishart.FieldHermitian.congruenceCL_apply, ← hRR]
      exact wishartWeight_congruence_standard α R hR X)
  refine ⟨h.1, ?_⟩
  have hmap := h.2
  have he : (Wishart.FieldHermitian.congruenceCL ℍ[ℝ] R hR : Hermitian p → Hermitian p) =
      Wishart.FieldHermitian.congruence ℍ[ℝ] R := funext (Wishart.FieldHermitian.congruenceCL_apply ℍ[ℝ] R hR)
  rw [he] at hmap
  simpa only [wishartMeasure, wishartNormalizer, normalized, normalizer] using hmap

theorem wishart_probability {α : ℝ} (hα : (p : ℝ) - 1 < α)
    {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hSigma : PosDef Sigma) :
    IsProbabilityMeasure (wishartMeasure α Sigma) :=
  isProbability_normalized (finiteDensity_wishart_and_covariance_law hα hSigma).1

end Wishart.QuaternionMatrix
end
end CanonicalSource8

section CanonicalSource9
/- Source: Wishart/SpectralFaces.lean -/



/-!
# Finite and vanishing faces of a convex logarithmic profile

A face is formed by sending the omitted logarithmic coordinates together to
minus infinity. Convexity shows that the resulting logarithmic profile is
either finite everywhere on the retained coordinates, or unbounded below
everywhere. In the finite case it is convex and increasing and its supporting
planes extend to global minorants by putting zero coefficients outside the
face. These are precisely the planes needed to retain singular boundary
values in Theorem 7.1.
-/

noncomputable section
open Set Filter Topology
open scoped Classical BigOperators

namespace Wishart.Spectral

variable {k : ℕ}

def faceFill (J : Finset (Fin k)) (x : J → ℝ) (t : ℝ) : Fin k → ℝ :=
  fun i => if hi : i ∈ J then x ⟨i, hi⟩ else t

theorem faceFill_mono_parameter (J : Finset (Fin k)) (x : J → ℝ) :
    Monotone (faceFill J x) := by
  intro s t hst i
  by_cases hi : i ∈ J
  · simp only [faceFill, dif_pos hi, le_refl]
  · simpa only [faceFill, dif_neg hi] using hst

theorem faceFill_mono_coordinates (J : Finset (Fin k)) (t : ℝ) :
    Monotone (fun x : J → ℝ => faceFill J x t) := by
  intro x y hxy i
  by_cases hi : i ∈ J
  · simpa only [faceFill, dif_pos hi] using hxy ⟨i, hi⟩
  · simp only [faceFill, dif_neg hi, le_refl]

theorem faceFill_convex_combination (J : Finset (Fin k)) (x y : J → ℝ)
    (t a b : ℝ) (hab : a + b = 1) :
    faceFill J (a • x + b • y) t = a • faceFill J x t + b • faceFill J y t := by
  funext i
  by_cases hi : i ∈ J
  · simp only [faceFill, dif_pos hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · simp only [faceFill, dif_neg hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← add_mul, hab, one_mul]

def FaceFinite (h : (Fin k → ℝ) → ℝ) (J : Finset (Fin k)) : Prop :=
  ∃ x : J → ℝ, BddBelow (Set.range (fun t : ℝ => h (faceFill J x t)))

def faceProfile (h : (Fin k → ℝ) → ℝ) (J : Finset (Fin k)) (x : J → ℝ) : ℝ :=
  ⨅ t : ℝ, h (faceFill J x t)

/-- Boundedness at one point forces boundedness at all points. This proves
the finite-or-minus-infinity dichotomy without treating a missing infimum as
an arbitrary real value. -/
theorem face_bddBelow_everywhere {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) {J : Finset (Fin k)}
    (hfinite : FaceFinite h J) (x : J → ℝ) :
    BddBelow (Set.range (fun t : ℝ => h (faceFill J x t))) := by
  obtain ⟨x₀, L, hL⟩ := hfinite
  let y : J → ℝ := 2 • x₀ - x
  let B : ℝ := min (2 * L - h (faceFill J y 0)) (h (faceFill J x 0))
  refine ⟨B, ?_⟩
  rintro z ⟨t, rfl⟩
  by_cases ht : t ≤ 0
  · have hmid : faceFill J x₀ t =
        (1 / 2 : ℝ) • faceFill J x t + (1 / 2 : ℝ) • faceFill J y t := by
      rw [← faceFill_convex_combination J x y t (1 / 2) (1 / 2) (by norm_num)]
      congr 1
      funext i
      simp only [y, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hcv := hc.2 (Set.mem_univ (faceFill J x t)) (Set.mem_univ (faceFill J y t))
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    rw [← hmid] at hcv
    have hy := hm (faceFill_mono_parameter J y ht)
    have hlow := hL (Set.mem_range_self t)
    have hB := min_le_left (2 * L - h (faceFill J y 0)) (h (faceFill J x 0))
    dsimp only [B]
    simp only [smul_eq_mul] at hcv
    linarith
  · exact (min_le_right _ _).trans (hm (faceFill_mono_parameter J x (le_of_not_ge ht)))

theorem faceProfile_tendsto {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) {J : Finset (Fin k)}
    (hfinite : FaceFinite h J) (x : J → ℝ) :
    Tendsto (fun t : ℝ => h (faceFill J x t)) atBot (𝓝 (faceProfile h J x)) :=
  tendsto_atBot_ciInf (hm.comp (faceFill_mono_parameter J x))
    (face_bddBelow_everywhere hc hm hfinite x)

theorem convexOn_faceProfile {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) {J : Finset (Fin k)}
    (hfinite : FaceFinite h J) : ConvexOn ℝ univ (faceProfile h J) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  apply le_of_tendsto_of_tendsto
    (faceProfile_tendsto hc hm hfinite (a • x + b • y))
    (((faceProfile_tendsto hc hm hfinite x).const_mul a).add
      ((faceProfile_tendsto hc hm hfinite y).const_mul b))
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [faceFill_convex_combination J x y t a b hab]
  exact hc.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem monotone_faceProfile {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) {J : Finset (Fin k)}
    (hfinite : FaceFinite h J) : Monotone (faceProfile h J) := by
  intro x y hxy
  exact le_of_tendsto_of_tendsto (faceProfile_tendsto hc hm hfinite x)
    (faceProfile_tendsto hc hm hfinite y)
    (Filter.Eventually.of_forall fun t => hm (faceFill_mono_coordinates J t hxy))

theorem continuous_faceProfile {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) {J : Finset (Fin k)}
    (hfinite : FaceFinite h J) : Continuous (faceProfile h J) := by
  simpa only [interior_univ, continuousOn_univ] using
    (convexOn_faceProfile hc hm hfinite).continuousOn_interior

theorem faceProfile_le_full {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) {J : Finset (Fin k)}
    (hfinite : FaceFinite h J) (x : Fin k → ℝ) :
    faceProfile h J (fun i => x i) ≤ h x := by
  obtain ⟨t, ht⟩ := (Set.finite_range x).bddBelow
  have hfill : faceFill J (fun i => x i) t ≤ x := by
    intro i
    by_cases hi : i ∈ J
    · simp only [faceFill, dif_pos hi, le_refl]
    · simpa only [faceFill, dif_neg hi] using ht (Set.mem_range_self i)
  exact (ciInf_le (face_bddBelow_everywhere hc hm hfinite _) t).trans (hm hfill)

def faceExponential (h : (Fin k → ℝ) → ℝ) (J : Finset (Fin k)) (x : J → ℝ) : ℝ :=
  ⨅ t : ℝ, Real.exp (h (faceFill J x t))

theorem faceExponential_nonneg (h : (Fin k → ℝ) → ℝ)
    (J : Finset (Fin k)) (x : J → ℝ) : 0 ≤ faceExponential h J x :=
  le_ciInf (fun t => (Real.exp_pos _).le)

theorem faceExponential_tendsto {h : (Fin k → ℝ) → ℝ} (hm : Monotone h)
    (J : Finset (Fin k)) (x : J → ℝ) :
    Tendsto (fun t : ℝ => Real.exp (h (faceFill J x t))) atBot
      (𝓝 (faceExponential h J x)) :=
  tendsto_atBot_ciInf ((Real.exp_monotone.comp hm).comp (faceFill_mono_parameter J x))
    ⟨0, by rintro _ ⟨t, rfl⟩; exact (Real.exp_pos _).le⟩

theorem faceExponential_eq_exp_faceProfile {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) {J : Finset (Fin k)}
    (hfinite : FaceFinite h J) (x : J → ℝ) :
    faceExponential h J x = Real.exp (faceProfile h J x) :=
  tendsto_nhds_unique (faceExponential_tendsto hm J x)
    (Real.continuous_exp.continuousAt.tendsto.comp (faceProfile_tendsto hc hm hfinite x))

theorem faceFinite_of_faceExponential_pos {h : (Fin k → ℝ) → ℝ}
    {J : Finset (Fin k)} {x : J → ℝ} (hpos : 0 < faceExponential h J x) :
    FaceFinite h J := by
  refine ⟨x, Real.log (faceExponential h J x), ?_⟩
  rintro _ ⟨t, rfl⟩
  have hle := ciInf_le
    (show BddBelow (Set.range (fun s => Real.exp (h (faceFill J x s)))) from
      ⟨0, by rintro _ ⟨s, rfl⟩; exact (Real.exp_pos _).le⟩) t
  simpa only [Real.log_exp] using Real.log_le_log hpos hle

theorem faceExponential_eq_zero_of_not_finite {h : (Fin k → ℝ) → ℝ}
    {J : Finset (Fin k)} (hnot : ¬ FaceFinite h J) (x : J → ℝ) :
    faceExponential h J x = 0 := by
  apply le_antisymm _ (faceExponential_nonneg h J x)
  exact le_of_not_gt (fun hpos => hnot (faceFinite_of_faceExponential_pos hpos))

/-- A finite face is positive at every point; every other face vanishes
identically after exponentiation. -/
theorem faceExponential_dichotomy {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (J : Finset (Fin k)) :
    (∀ x, 0 < faceExponential h J x) ∨ (∀ x, faceExponential h J x = 0) := by
  by_cases hfinite : FaceFinite h J
  · left
    intro x
    rw [faceExponential_eq_exp_faceProfile hc hm hfinite]
    exact Real.exp_pos _
  · exact Or.inr (faceExponential_eq_zero_of_not_finite hfinite)

end Wishart.Spectral
end
end CanonicalSource9
