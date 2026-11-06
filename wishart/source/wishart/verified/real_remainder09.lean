module

public import wishart.verified.real_remainder08
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/- Generated ordinary proof stage. See audit/staged_real_remainder/RealRemainder09/manifest.json. -/

@[expose] public section

section CanonicalSource80
/- Source: Wishart/CauchyBinet.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in vendor/TauCeti-LICENSE.

The exterior-coordinate proof below is adapted from
TauCeti/LinearAlgebra/ExteriorPower/Plucker.lean at commit
06d5bb4e3ebb737dc6538567f5c53bf8800b9362. The definitions and proofs have
been restricted to their complete mathematical dependency closure for the
Cauchy–Binet identity, with the namespace and coordinate name changed.
No assertion is imported without its proof.
-/



open Set Set.powersetCard exteriorPower
open scoped Matrix

namespace Wishart.Spectral

variable {R ι : Type*} [CommRing R] [LinearOrder ι] {j : ℕ}

/-- A maximal minor, with its columns listed in increasing order. -/
def minorCoordinate (x : Fin j → ι → R) (s : powersetCard ι j) : R :=
  (Matrix.of fun i k => x i (ofFinEmbEquiv.symm s k)).det

theorem minorCoordinate_apply (x : Fin j → ι → R) (s : powersetCard ι j) :
    minorCoordinate x s =
      (Matrix.of fun i k => x i (ofFinEmbEquiv.symm s k)).det := rfl

theorem minorCoordinate_eq_repr [Finite ι]
    (x : Fin j → ι → R) (s : powersetCard ι j) :
    minorCoordinate x s =
      ((Pi.basisFun R ι).exteriorPower j).repr (ιMulti R j x) s := by
  rw [basis_repr_apply, ιMultiDual_apply_ιMulti, minorCoordinate_apply]
  simp

private theorem pairingDual_ιMulti_basisFun [Fintype ι]
    (y : Fin j → ι → R) (s : powersetCard ι j) :
    pairingDual R (ι → R) j (ιMulti R j fun k => Fintype.linearCombination R (y k))
        ((Pi.basisFun R ι).exteriorPower j s) = minorCoordinate y s := by
  classical
  rw [basis_apply, ιMulti_family, pairingDual_ιMulti_ιMulti,
    minorCoordinate_apply, ← Matrix.det_transpose]
  congr 1
  ext i k
  simp [Fintype.linearCombination_apply, Pi.single_apply]

/-- Cauchy–Binet, in arbitrary dimension and over every commutative ring. -/
theorem det_mul_transpose_eq_sum_minors [Fintype ι]
    (x y : Fin j → ι → R) :
    (Matrix.of x * (Matrix.of y).transpose).det =
      ∑ s, minorCoordinate x s * minorCoordinate y s := by
  classical
  set b := (Pi.basisFun R ι).exteriorPower j
  set φ := pairingDual R (ι → R) j
    (ιMulti R j fun k => Fintype.linearCombination R (y k))
  have h : (Matrix.of x * (Matrix.of y).transpose).det = φ (ιMulti R j x) := by
    rw [pairingDual_ιMulti_ιMulti]
    refine congrArg Matrix.det (Matrix.ext fun i k => ?_)
    simp [Matrix.mul_apply, Fintype.linearCombination_apply]
  rw [h, ← b.sum_repr (ιMulti R j x), map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, pairingDual_ιMulti_basisFun, ← minorCoordinate_eq_repr, smul_eq_mul]

/-- The squared minors of a row frame sum to its Gram determinant. -/
theorem det_gram_eq_sum_sq_minors [Fintype ι] (A : Matrix (Fin j) ι R) :
    (A * A.transpose).det = ∑ s, minorCoordinate A.row s ^ 2 := by
  simpa [sq, Matrix.row_eq_self] using det_mul_transpose_eq_sum_minors A.row A.row

end Wishart.Spectral
end CanonicalSource80

section CanonicalSource81
/- Source: Wishart/SpectralVariational.lean -/



/-!
# The variational formula for products of the largest eigenvalues

Every orthonormal compression of a diagonal positive semidefinite matrix has a
determinant which is a convex combination of its spectral minors. Cauchy–Binet
identifies the weights as squared maximal minors of the frame, and its Gram
identity says that the weights sum to one. Sorting the spectrum then bounds
each spectral minor by the product of the first eigenvalues. The corresponding
eigenframe attains this bound.

This proves the full formula in every dimension, including an empty compression
and singular positive semidefinite inputs. No interlacing or variational
formula is assumed.
-/

open Matrix Set Set.powersetCard
open scoped Classical Matrix.Norms.Operator

namespace Wishart.Spectral

/-- The manuscript's decreasing eigenvalue enumeration. -/
noncomputable def descendingSpectrum {p : ℕ} (S : Sym p) : Fin p → ℝ :=
  ascendingSpectrum S ∘ Fin.rev

theorem antitone_descendingSpectrum {p : ℕ} (S : Sym p) :
    Antitone (descendingSpectrum S) := by
  intro i k hik
  exact monotone_ascendingSpectrum S (Fin.rev_anti hik)

theorem descendingSpectrum_nonneg {p : ℕ} {S : Sym p}
    (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) (i : Fin p) :
    0 ≤ descendingSpectrum S i := by
  simpa only [descendingSpectrum, ascendingSpectrum, coordinateSpectrum,
    Function.comp_apply] using
    hS.eigenvalues_nonneg (ascendingIndexEquiv p (Fin.rev i))

theorem exists_conjugate_diagonal_descendingSpectrum {p : ℕ} (S : Sym p) :
    ∃ O : Orth p, conjugate O (diagonalSym (descendingSpectrum S)) = S := by
  obtain ⟨O, hO⟩ := exists_conjugate_diagonal_ascendingSpectrum S
  refine ⟨O * permutationOrth Fin.revPerm, ?_⟩
  rw [conjugate_mul, conjugate_permutation_diagonal]
  have heq : descendingSpectrum S ∘ Fin.revPerm = ascendingSpectrum S := by
    funext i
    simp only [descendingSpectrum, Function.comp_apply, Fin.revPerm_apply, Fin.rev_rev]
  rw [heq]
  exact hO

/-- Increasing embeddings cannot move the `i`th index to an earlier position. -/
theorem fin_orderEmbedding_index_le {j p : ℕ} (e : Fin j ↪o Fin p) (i : Fin j) :
    i.val ≤ (e i).val := by
  have h : ∀ n (hn : n < j), n ≤ (e ⟨n, hn⟩).val := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have hn' : n < j := Nat.lt_trans (Nat.lt_succ_self n) hn
      have he : (e ⟨n, hn'⟩).val < (e ⟨n + 1, hn⟩).val :=
        e.strictMono (show (⟨n, hn'⟩ : Fin j) < ⟨n + 1, hn⟩ from Nat.lt_succ_self n)
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih hn') he)
  exact h i.val i.isLt

theorem spectral_minor_le_leading_product {j p : ℕ} (hj : j ≤ p)
    {lam : Fin p → ℝ} (h0 : ∀ i, 0 ≤ lam i) (hmono : Antitone lam)
    (s : powersetCard (Fin p) j) :
    (∏ i : Fin j, lam (ofFinEmbEquiv.symm s i)) ≤
      ∏ i : Fin j, lam (Fin.castLE hj i) := by
  apply Finset.prod_le_prod₀
  · intro i hi
    exact h0 _
  · intro i hi
    apply hmono
    exact fin_orderEmbedding_index_le (ofFinEmbEquiv.symm s) i

theorem minorCoordinate_mul_diagonal {j p : ℕ}
    (A : Matrix (Fin j) (Fin p) ℝ) (lam : Fin p → ℝ)
    (s : powersetCard (Fin p) j) :
    minorCoordinate (A * Matrix.diagonal lam).row s =
      (∏ i : Fin j, lam (ofFinEmbEquiv.symm s i)) * minorCoordinate A.row s := by
  rw [minorCoordinate_apply, minorCoordinate_apply]
  simp only [Matrix.row_apply]
  convert Matrix.det_mul_row (fun i : Fin j => lam (ofFinEmbEquiv.symm s i))
    (Matrix.of fun i k => A i (ofFinEmbEquiv.symm s k)) using 1
  congr 1
  ext i k
  simp only [Matrix.row_apply, Matrix.of_apply, Matrix.mul_diagonal, mul_comm]

/-- The determinant of an orthonormal compression is a weighted sum of spectral
minors; the weights are the squares of the frame's maximal minors. -/
theorem det_diagonal_compression_eq_sum {j p : ℕ}
    (V : Matrix (Fin p) (Fin j) ℝ) (lam : Fin p → ℝ) :
    (Vᵀ * Matrix.diagonal lam * V).det =
      ∑ s : powersetCard (Fin p) j,
        minorCoordinate Vᵀ.row s ^ 2 *
          ∏ i : Fin j, lam (ofFinEmbEquiv.symm s i) := by
  have h := det_mul_transpose_eq_sum_minors
    (Vᵀ * Matrix.diagonal lam).row Vᵀ.row
  simp only [Matrix.row_eq_self, Equiv.apply_symm_apply, Matrix.transpose_transpose] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [← Matrix.row_eq_self]
  rw [minorCoordinate_mul_diagonal]
  ring

theorem sum_sq_minors_of_orthonormal {j p : ℕ}
    (V : Matrix (Fin p) (Fin j) ℝ) (hV : Vᵀ * V = 1) :
    (∑ s : powersetCard (Fin p) j, minorCoordinate Vᵀ.row s ^ 2) = 1 := by
  have h := det_gram_eq_sum_sq_minors Vᵀ
  simpa only [Matrix.transpose_transpose, hV, Matrix.det_one] using h.symm

theorem det_diagonal_compression_le {j p : ℕ} (hj : j ≤ p)
    (V : Matrix (Fin p) (Fin j) ℝ) (hV : Vᵀ * V = 1)
    {lam : Fin p → ℝ} (h0 : ∀ i, 0 ≤ lam i) (hmono : Antitone lam) :
    (Vᵀ * Matrix.diagonal lam * V).det ≤
      ∏ i : Fin j, lam (Fin.castLE hj i) := by
  rw [det_diagonal_compression_eq_sum]
  calc
    _ ≤ ∑ s : powersetCard (Fin p) j,
        minorCoordinate Vᵀ.row s ^ 2 *
          ∏ i : Fin j, lam (Fin.castLE hj i) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left
        (spectral_minor_le_leading_product hj h0 hmono s) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, sum_sq_minors_of_orthonormal V hV, one_mul]

/-- The standard coordinate frame associated with an injective selection. -/
def coordinateFrame {j p : ℕ} (e : Fin j ↪ Fin p) : Matrix (Fin p) (Fin j) ℝ :=
  (1 : Matrix (Fin p) (Fin p) ℝ).submatrix id e

theorem coordinateFrame_compression {j p : ℕ} (e : Fin j ↪ Fin p)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    (coordinateFrame e)ᵀ * A * coordinateFrame e = A.submatrix e e := by
  unfold coordinateFrame
  rw [Matrix.transpose_submatrix, Matrix.transpose_one]
  change (1 : Matrix (Fin p) (Fin p) ℝ).submatrix e (Equiv.refl (Fin p)) * A *
    (1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Equiv.refl (Fin p)) e = _
  rw [Matrix.one_submatrix_mul e (Equiv.refl (Fin p)) A]
  rw [Matrix.mul_submatrix_one (Equiv.refl (Fin p)) e]
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp,
    Matrix.submatrix_submatrix, Function.comp_id]

theorem coordinateFrame_orthonormal {j p : ℕ} (e : Fin j ↪ Fin p) :
    (coordinateFrame e)ᵀ * coordinateFrame e = 1 := by
  simpa only [Matrix.mul_one, Matrix.submatrix_one_embedding] using
    coordinateFrame_compression e (1 : Matrix (Fin p) (Fin p) ℝ)

theorem coordinateFrame_diagonal_det {j p : ℕ}
    (e : Fin j ↪ Fin p) (lam : Fin p → ℝ) :
    ((coordinateFrame e)ᵀ * Matrix.diagonal lam * coordinateFrame e).det =
      ∏ i : Fin j, lam (e i) := by
  rw [coordinateFrame_compression, Matrix.submatrix_diagonal_embedding,
    Matrix.det_diagonal]
  rfl

def OrthonormalFrame (p j : ℕ) :=
  {U : Matrix (Fin p) (Fin j) ℝ // Uᵀ * U = 1}

instance (p j : ℕ) : TopologicalSpace (OrthonormalFrame p j) :=
  inferInstanceAs (TopologicalSpace {U : Matrix (Fin p) (Fin j) ℝ // Uᵀ * U = 1})

instance (p j : ℕ) : SecondCountableTopology (OrthonormalFrame p j) := by
  letI : SecondCountableTopology (Matrix (Fin p) (Fin j) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin p → Fin j → ℝ))
  exact TopologicalSpace.Subtype.secondCountableTopology
    {U : Matrix (Fin p) (Fin j) ℝ | Uᵀ * U = 1}

noncomputable def compressionDeterminant {p j : ℕ} (S : Sym p)
    (U : OrthonormalFrame p j) : ℝ :=
  (U.valᵀ * (S : Matrix (Fin p) (Fin p) ℝ) * U.val).det

noncomputable def leadingEigenvalueProduct {p j : ℕ} (hj : j ≤ p) (S : Sym p) : ℝ :=
  ∏ i : Fin j, descendingSpectrum S (Fin.castLE hj i)

theorem compressionDeterminant_le_leadingEigenvalueProduct {p j : ℕ}
    (hj : j ≤ p) (S : Sym p) (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (U : OrthonormalFrame p j) :
    compressionDeterminant S U ≤ leadingEigenvalueProduct hj S := by
  obtain ⟨O, hO⟩ := exists_conjugate_diagonal_descendingSpectrum S
  let V : Matrix (Fin p) (Fin j) ℝ := (O : Matrix (Fin p) (Fin p) ℝ)ᵀ * U.val
  have hV : Vᵀ * V = 1 := by
    simp only [V, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      _ = U.valᵀ * ((O : Matrix (Fin p) (Fin p) ℝ) *
          (O : Matrix (Fin p) (Fin p) ℝ)ᵀ) * U.val := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [orth_mul_transpose, Matrix.mul_one, U.property]
  have heq : U.valᵀ * (S : Matrix (Fin p) (Fin p) ℝ) * U.val =
      Vᵀ * Matrix.diagonal (descendingSpectrum S) * V := by
    have hmat : (S : Matrix (Fin p) (Fin p) ℝ) =
        (O : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal (descendingSpectrum S) *
          (O : Matrix (Fin p) (Fin p) ℝ)ᵀ := by
      simpa only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply, diagonalSym] using
        (congrArg (fun Z : Sym p => (Z : Matrix (Fin p) (Fin p) ℝ)) hO).symm
    rw [hmat]
    simp only [V, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  unfold compressionDeterminant leadingEigenvalueProduct
  rw [heq]
  exact det_diagonal_compression_le hj V hV (descendingSpectrum_nonneg hS)
    (antitone_descendingSpectrum S)

theorem exists_compressionDeterminant_eq_leadingEigenvalueProduct {p j : ℕ}
    (hj : j ≤ p) (S : Sym p) :
    ∃ U : OrthonormalFrame p j,
      compressionDeterminant S U = leadingEigenvalueProduct hj S := by
  obtain ⟨O, hO⟩ := exists_conjugate_diagonal_descendingSpectrum S
  let E := coordinateFrame (Fin.castLEEmb hj)
  let U : Matrix (Fin p) (Fin j) ℝ := (O : Matrix (Fin p) (Fin p) ℝ) * E
  have hU : Uᵀ * U = 1 := by
    simp only [U, Matrix.transpose_mul]
    calc
      _ = Eᵀ * ((O : Matrix (Fin p) (Fin p) ℝ)ᵀ *
          (O : Matrix (Fin p) (Fin p) ℝ)) * E := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [orth_transpose_mul, Matrix.mul_one]; exact coordinateFrame_orthonormal _
  refine ⟨⟨U, hU⟩, ?_⟩
  have heq : Uᵀ * (S : Matrix (Fin p) (Fin p) ℝ) * U =
      Eᵀ * Matrix.diagonal (descendingSpectrum S) * E := by
    have hmat : (S : Matrix (Fin p) (Fin p) ℝ) =
        (O : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal (descendingSpectrum S) *
          (O : Matrix (Fin p) (Fin p) ℝ)ᵀ := by
      simpa only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply, diagonalSym] using
        (congrArg (fun Z : Sym p => (Z : Matrix (Fin p) (Fin p) ℝ)) hO).symm
    have hd : (O : Matrix (Fin p) (Fin p) ℝ)ᵀ *
        (S : Matrix (Fin p) (Fin p) ℝ) * (O : Matrix (Fin p) (Fin p) ℝ) =
          Matrix.diagonal (descendingSpectrum S) := by
      rw [hmat]
      calc
        _ = ((O : Matrix (Fin p) (Fin p) ℝ)ᵀ * (O : Matrix (Fin p) (Fin p) ℝ)) *
            Matrix.diagonal (descendingSpectrum S) *
              ((O : Matrix (Fin p) (Fin p) ℝ)ᵀ * (O : Matrix (Fin p) (Fin p) ℝ)) := by
                simp only [Matrix.mul_assoc]
        _ = _ := by rw [orth_transpose_mul, Matrix.one_mul, Matrix.mul_one]
    calc
      _ = Eᵀ * ((O : Matrix (Fin p) (Fin p) ℝ)ᵀ *
          (S : Matrix (Fin p) (Fin p) ℝ) * (O : Matrix (Fin p) (Fin p) ℝ)) * E := by
            simp only [U, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hd]
  change (Uᵀ * (S : Matrix (Fin p) (Fin p) ℝ) * U).det = _
  rw [heq, coordinateFrame_diagonal_det]
  rfl

/-- The largest-eigenvalue product is literally the attained maximum over all
orthonormal column frames. This is equation (16) of the manuscript. -/
theorem leadingEigenvalueProduct_isGreatest {p j : ℕ}
    (hj : j ≤ p) (S : Sym p) (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    IsGreatest (Set.range (compressionDeterminant (j := j) S))
      (leadingEigenvalueProduct hj S) := by
  constructor
  · exact exists_compressionDeterminant_eq_leadingEigenvalueProduct hj S
  · rintro t ⟨U, rfl⟩
    exact compressionDeterminant_le_leadingEigenvalueProduct hj S hS U

theorem leadingEigenvalueProduct_eq_sup_compressions {p j : ℕ}
    (hj : j ≤ p) (S : Sym p) (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    leadingEigenvalueProduct hj S =
      sSup (Set.range (compressionDeterminant (j := j) S)) :=
  (leadingEigenvalueProduct_isGreatest hj S hS).csSup_eq.symm

end Wishart.Spectral
end CanonicalSource81

section CanonicalSource82
/- Source: Wishart/SpectralFrameApproximation.lean -/



noncomputable section

open Matrix Set Filter Topology
open scoped Classical Matrix.Norms.Operator

namespace Wishart.Spectral

theorem orthonormalFrame_rank {p j : ℕ} (U : OrthonormalFrame p j) : U.val.rank = j := by
  apply le_antisymm
  · simpa only [Fintype.card_fin] using U.val.rank_le_width
  · have h := Matrix.rank_mul_le_right U.valᵀ U.val
    simpa only [U.property, Matrix.rank_one, Fintype.card_fin] using h

theorem compressionDeterminant_nonneg {p j : ℕ} {S : Sym p}
    (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) (U : OrthonormalFrame p j) :
    0 ≤ compressionDeterminant S U := by
  exact (show (U.valᵀ * (S : Matrix (Fin p) (Fin p) ℝ) * U.val).PosSemidef from by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.conjTranspose_mul_mul_same U.val).det_nonneg

theorem compressionDeterminant_pos {p j : ℕ} {S : Sym p}
    (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosDef) (U : OrthonormalFrame p j) :
    0 < compressionDeterminant S U := by
  have hr : U.valᵀ.rank = j := by rw [Matrix.rank_transpose, orthonormalFrame_rank]
  have h := hS.mul_mul_conjTranspose_same
    ((Matrix.rank_eq_card_iff_vecMul_injective U.valᵀ).1 (by simpa using hr))
  exact (show (U.valᵀ * (S : Matrix (Fin p) (Fin p) ℝ) * U.val).PosDef from by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using h).det_pos

theorem continuous_compressionDeterminant {p j : ℕ} (S : Sym p) :
    Continuous (compressionDeterminant (j := j) S) := by
  unfold compressionDeterminant
  fun_prop

def standardOrthonormalFrame {p j : ℕ} (hj : j ≤ p) : OrthonormalFrame p j :=
  ⟨coordinateFrame (Fin.castLEEmb hj), coordinateFrame_orthonormal _⟩

/-- One countable family works simultaneously for every input matrix. -/
def denseFrames {p j : ℕ} (hj : j ≤ p) : ℕ → OrthonormalFrame p j :=
  letI : Nonempty (OrthonormalFrame p j) := ⟨standardOrthonormalFrame hj⟩
  TopologicalSpace.denseSeq (OrthonormalFrame p j)

theorem denseRange_denseFrames {p j : ℕ} (hj : j ≤ p) : DenseRange (denseFrames hj) := by
  letI : Nonempty (OrthonormalFrame p j) := ⟨standardOrthonormalFrame hj⟩
  exact TopologicalSpace.denseRange_denseSeq (OrthonormalFrame p j)

theorem leadingEigenvalueProduct_eq_iSup_denseFrames {p j : ℕ}
    (hj : j ≤ p) (S : Sym p) (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    leadingEigenvalueProduct hj S =
      ⨆ n : ℕ, compressionDeterminant S (denseFrames hj n) := by
  have hbound : BddAbove (Set.range (fun n : ℕ =>
      compressionDeterminant S (denseFrames hj n))) := by
    refine ⟨leadingEigenvalueProduct hj S, ?_⟩
    rintro t ⟨n, rfl⟩
    exact compressionDeterminant_le_leadingEigenvalueProduct hj S hS _
  apply le_antisymm
  · obtain ⟨U, hU⟩ := exists_compressionDeterminant_eq_leadingEigenvalueProduct hj S
    rw [← hU]
    apply le_on_closure
      (s := Set.range (denseFrames hj))
      (f := compressionDeterminant S)
      (g := fun _ => ⨆ n : ℕ, compressionDeterminant S (denseFrames hj n))
    · rintro V ⟨n, rfl⟩
      exact le_ciSup hbound n
    · exact (continuous_compressionDeterminant S).continuousOn
    · exact continuous_const.continuousOn
    · exact denseRange_denseFrames hj U
  · exact ciSup_le (fun n => compressionDeterminant_le_leadingEigenvalueProduct hj S hS _)

def framePartialMaximum {p j : ℕ} (hj : j ≤ p) (n : ℕ) (S : Sym p) : ℝ :=
  (Finset.range (n + 1)).sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n))
    (fun m => compressionDeterminant S (denseFrames hj m))

theorem framePartialMaximum_le {p j : ℕ} (hj : j ≤ p) (n : ℕ)
    (S : Sym p) (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    framePartialMaximum hj n S ≤ leadingEigenvalueProduct hj S :=
  Finset.sup'_le _ _ (fun m _ =>
    compressionDeterminant_le_leadingEigenvalueProduct hj S hS _)

theorem denseFrame_le_partialMaximum {p j : ℕ} (hj : j ≤ p) (n : ℕ) (S : Sym p) :
    compressionDeterminant S (denseFrames hj n) ≤ framePartialMaximum hj n S :=
  Finset.le_sup' (fun m => compressionDeterminant S (denseFrames hj m))
    (Finset.mem_range.mpr (Nat.lt_succ_self n))

theorem framePartialMaximum_monotone {p j : ℕ} (hj : j ≤ p) (S : Sym p) :
    Monotone (fun n => framePartialMaximum hj n S) := by
  intro m n hmn
  exact Finset.sup'_mono (fun m => compressionDeterminant S (denseFrames hj m))
    (Finset.range_mono (Nat.add_le_add_right hmn 1)) _

theorem framePartialMaximum_nonneg {p j : ℕ} (hj : j ≤ p) (n : ℕ)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ framePartialMaximum hj n S :=
  (compressionDeterminant_nonneg hS _).trans (denseFrame_le_partialMaximum hj n S)

theorem framePartialMaximum_pos {p j : ℕ} (hj : j ≤ p) (n : ℕ)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    0 < framePartialMaximum hj n S :=
  (compressionDeterminant_pos hS _).trans_le (denseFrame_le_partialMaximum hj n S)

/-- Finite dense-frame maxima increase to the actual leading product. -/
theorem framePartialMaximum_tendsto {p j : ℕ} (hj : j ≤ p)
    (S : Sym p) (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    Tendsto (fun n => framePartialMaximum hj n S) atTop
      (𝓝 (leadingEigenvalueProduct hj S)) := by
  have hb : BddAbove (Set.range (fun n => framePartialMaximum hj n S)) := by
    refine ⟨leadingEigenvalueProduct hj S, ?_⟩
    rintro t ⟨n, rfl⟩
    exact framePartialMaximum_le hj n S hS
  have heq : (⨆ n, framePartialMaximum hj n S) = leadingEigenvalueProduct hj S := by
    apply le_antisymm
    · exact ciSup_le (fun n => framePartialMaximum_le hj n S hS)
    · rw [leadingEigenvalueProduct_eq_iSup_denseFrames hj S hS]
      exact ciSup_le (fun n => (denseFrame_le_partialMaximum hj n S).trans (le_ciSup hb n))
  simpa only [heq] using tendsto_atTop_ciSup (framePartialMaximum_monotone hj S) hb

end Wishart.Spectral
end
end CanonicalSource82

section CanonicalSource83
/- Source: Wishart/SpectralSlopeProducts.lean -/



noncomputable section

open Matrix Finset
open scoped Classical

namespace Wishart.Spectral

def extendCoordinates {k : ℕ} (a : Fin k → ℝ) (n : ℕ) : ℝ :=
  if h : n < k then a ⟨n, h⟩ else 0

@[simp] theorem extendCoordinates_apply {k : ℕ} (a : Fin k → ℝ) (i : Fin k) :
    extendCoordinates a i.val = a i := by simp [extendCoordinates, i.isLt]

@[simp] theorem extendCoordinates_length {k : ℕ} (a : Fin k → ℝ) :
    extendCoordinates a k = 0 := by simp [extendCoordinates]

def slopeDrop {k : ℕ} (a : Fin k → ℝ) (i : Fin k) : ℝ :=
  a i - extendCoordinates a (i.val + 1)

theorem slopeDrop_nonneg {k : ℕ} {a : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (i : Fin k) : 0 ≤ slopeDrop a i := by
  unfold slopeDrop extendCoordinates
  split_ifs with hi
  · exact sub_nonneg.mpr (hmono (show i ≤ (⟨i.val + 1, hi⟩ : Fin k) from Nat.le_succ _))
  · simpa only [sub_zero] using ha i

/-- The finite summation-by-parts identity with the terminal value retained. -/
theorem sum_range_slope_drop (a s : ℕ → ℝ) (k : ℕ) :
    (∑ i ∈ range k, a i * s i) =
      (∑ j ∈ range k, (a j - a (j + 1)) * ∑ i ∈ range (j + 1), s i) +
        a k * ∑ i ∈ range k, s i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ (f := fun i => a i * s i),
      sum_range_succ (f := fun j => (a j - a (j + 1)) * ∑ i ∈ range (j + 1), s i)]
    rw [ih, sum_range_succ]
    ring

theorem sum_extendCoordinates_prefix {k j : ℕ} (s : Fin k → ℝ) (hj : j ≤ k) :
    (∑ n ∈ range j, extendCoordinates s n) =
      ∑ i : Fin j, s (Fin.castLE hj i) := by
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [extendCoordinates, dif_pos (Nat.lt_of_lt_of_le i.isLt hj)]
  rfl

/-- Telescoping sorted slopes into nonnegative prefix-sum coefficients. -/
theorem coordinate_sum_eq_slopeDrops {k : ℕ} (a s : Fin k → ℝ) :
    (∑ i, a i * s i) =
      ∑ j : Fin k, slopeDrop a j *
        ∑ i : Fin (j.val + 1), s (Fin.castLE (Nat.succ_le_of_lt j.isLt) i) := by
  have h := sum_range_slope_drop (extendCoordinates a) (extendCoordinates s) k
  have hl : (∑ n ∈ range k, extendCoordinates a n * extendCoordinates s n) =
      ∑ i : Fin k, a i * s i := by
    rw [Finset.sum_range]
    simp only [extendCoordinates_apply]
  have hr : (∑ j ∈ range k,
      (extendCoordinates a j - extendCoordinates a (j + 1)) *
        ∑ i ∈ range (j + 1), extendCoordinates s i) =
      ∑ j : Fin k, slopeDrop a j *
        ∑ i : Fin (j.val + 1), s (Fin.castLE (Nat.succ_le_of_lt j.isLt) i) := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    rw [extendCoordinates_apply, sum_extendCoordinates_prefix s (Nat.succ_le_of_lt j.isLt)]
    rfl
  simpa only [hl, hr, extendCoordinates_length, zero_mul, add_zero] using h

def coordinateLeadingProduct {k : ℕ} (x : Fin k → ℝ) (j : Fin k) : ℝ :=
  ∏ i : Fin (j.val + 1), x (Fin.castLE (Nat.succ_le_of_lt j.isLt) i)

theorem coordinateLeadingProduct_pos {k : ℕ} {x : Fin k → ℝ}
    (hx : ∀ i, 0 < x i) (j : Fin k) : 0 < coordinateLeadingProduct x j :=
  Finset.prod_pos (fun i _ => hx _)

theorem log_coordinateLeadingProduct {k : ℕ} {x : Fin k → ℝ}
    (hx : ∀ i, 0 < x i) (j : Fin k) :
    Real.log (coordinateLeadingProduct x j) =
      ∑ i : Fin (j.val + 1), Real.log (x (Fin.castLE (Nat.succ_le_of_lt j.isLt) i)) :=
  Real.log_prod (fun i _ => (hx _).ne')

/-- Exponentiating a supporting plane gives the exact leading-product monomial.
The preceding sign lemma makes all powers nonnegative for sorted slopes. -/
theorem exp_coordinatePlane_log_eq_leadingProducts {k : ℕ}
    (a : Fin k → ℝ) (b : ℝ) {x : Fin k → ℝ} (hx : ∀ i, 0 < x i) :
    Real.exp (coordinatePlane a b (fun i => Real.log (x i))) =
      Real.exp b * ∏ j, (coordinateLeadingProduct x j) ^ (slopeDrop a j) := by
  have hp (j : Fin k) : (coordinateLeadingProduct x j) ^ (slopeDrop a j) =
      Real.exp (Real.log (coordinateLeadingProduct x j) * slopeDrop a j) :=
    Real.rpow_def_of_pos (coordinateLeadingProduct_pos hx j) _
  simp_rw [hp]
  rw [← Real.exp_sum, ← Real.exp_add]
  congr 1
  unfold coordinatePlane
  rw [coordinate_sum_eq_slopeDrops]
  rw [add_comm b]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [log_coordinateLeadingProduct hx]
  ring

theorem descendingSpectrum_pos {p : ℕ} {S : Sym p}
    (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosDef) (i : Fin p) :
    0 < descendingSpectrum S i := by
  simpa only [descendingSpectrum, ascendingSpectrum, coordinateSpectrum, Function.comp_apply] using
    hS.eigenvalues_pos (ascendingIndexEquiv p (Fin.rev i))

theorem coordinateLeadingProduct_descendingSpectrum {p : ℕ} (S : Sym p) (j : Fin p) :
    coordinateLeadingProduct (descendingSpectrum S) j =
      leadingEigenvalueProduct (Nat.succ_le_of_lt j.isLt) S := rfl

theorem exp_coordinatePlane_log_spectrum {p : ℕ}
    (a : Fin p → ℝ) (b : ℝ) {S : Sym p}
    (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    Real.exp (coordinatePlane a b (fun i => Real.log (descendingSpectrum S i))) =
      Real.exp b * ∏ j : Fin p,
        (leadingEigenvalueProduct (Nat.succ_le_of_lt j.isLt) S) ^ (slopeDrop a j) := by
  simpa only [coordinateLeadingProduct_descendingSpectrum] using
    exp_coordinatePlane_log_eq_leadingProducts a b (descendingSpectrum_pos hS)

end Wishart.Spectral
end
end CanonicalSource83

section CanonicalSource84
/- Source: Wishart/SpectralFiniteApproximation.lean -/



/-!
# Finite compression approximations of logarithmic spectral planes

The maximum over a product of finite frame families is an actual finite maximum
of determinant monomials. The frames are chosen independently of the input
matrix. Increasing the finite family converges to the exact spectral supporting
plane, by the proved compression variational formula.
-/

noncomputable section

open Set Filter Topology Matrix
open scoped Classical BigOperators

namespace WishartVerification

theorem finiteMaximum_const_mul {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    finiteMaximum (fun i => c * x i) = c * finiteMaximum x := by
  apply le_antisymm
  · exact finiteMaximum_le fun i => mul_le_mul_of_nonneg_left (le_finiteMaximum x i) hc
  · obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
    change c * Finset.univ.sup' Finset.univ_nonempty x ≤ _
    rw [hmax]
    exact le_finiteMaximum (fun j => c * x j) i

theorem finiteMaximum_prod_rpow {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (x : κ → ι → ℝ) (a : κ → ℝ)
    (hx : ∀ j i, 0 ≤ x j i) (ha : ∀ j, 0 ≤ a j) :
    finiteMaximum (fun θ : κ → ι => ∏ j, x j (θ j) ^ a j) =
      ∏ j, finiteMaximum (x j) ^ a j := by
  apply le_antisymm
  · apply finiteMaximum_le
    intro θ
    exact Finset.prod_le_prod₀
      (fun j _ => Real.rpow_nonneg (hx j (θ j)) _)
      (fun j _ => Real.rpow_le_rpow (hx j (θ j)) (le_finiteMaximum (x j) (θ j)) (ha j))
  · have heach (j : κ) : ∃ i : ι, finiteMaximum (x j) = x j i := by
      obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (x j)
      exact ⟨i, hmax⟩
    choose θ hθ using heach
    calc
      (∏ j, finiteMaximum (x j) ^ a j) = ∏ j, x j (θ j) ^ a j := by simp_rw [hθ]
      _ ≤ finiteMaximum (fun θ : κ → ι => ∏ j, x j (θ j) ^ a j) :=
        le_finiteMaximum (fun θ : κ → ι => ∏ j, x j (θ j) ^ a j) θ

theorem finiteMaximum_pair {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ] (f : ι → κ → ℝ) :
    finiteMaximum (fun z : ι × κ => f z.1 z.2) =
      finiteMaximum (fun i => finiteMaximum (f i)) := by
  apply le_antisymm
  · exact finiteMaximum_le fun z =>
      (le_finiteMaximum (f z.1) z.2).trans
        (le_finiteMaximum (fun i : ι => finiteMaximum (f i)) z.1)
  · exact finiteMaximum_le fun i => finiteMaximum_le fun j =>
      le_finiteMaximum (fun z : ι × κ => f z.1 z.2) (i, j)

end WishartVerification

namespace Wishart.Spectral

open WishartVerification

theorem framePartialMaximum_eq_finiteMaximum {p j : ℕ} (hj : j ≤ p)
    (n : ℕ) (S : Sym p) :
    framePartialMaximum hj n S = finiteMaximum
      (fun m : Fin (n + 1) => compressionDeterminant S (denseFrames hj m.val)) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro m hm
    exact le_finiteMaximum
      (fun l : Fin (n + 1) => compressionDeterminant S (denseFrames hj l.val))
      ⟨m, Finset.mem_range.mp hm⟩
  · apply finiteMaximum_le
    intro m
    exact Finset.le_sup' (fun l => compressionDeterminant S (denseFrames hj l))
      (Finset.mem_range.mpr m.isLt)

def spectralPlaneFrameApprox {p : ℕ} (a : Fin p → ℝ) (b : ℝ)
    (n : ℕ) (S : Sym p) : ℝ :=
  Real.exp b * ∏ j : Fin p,
    framePartialMaximum (Nat.succ_le_of_lt j.isLt) n S ^ slopeDrop a j

def frameMonomial {p : ℕ} (a : Fin p → ℝ) (b : ℝ) (n : ℕ)
    (θ : Fin p → Fin (n + 1)) (S : Sym p) : ℝ :=
  Real.exp b * ∏ j : Fin p,
    compressionDeterminant S
      (denseFrames (Nat.succ_le_of_lt j.isLt) (θ j).val) ^ slopeDrop a j

theorem spectralPlaneFrameApprox_eq_maximum {p : ℕ}
    (a : Fin p → ℝ) (b : ℝ) (n : ℕ)
    (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    spectralPlaneFrameApprox a b n S =
      finiteMaximum (fun θ : Fin p → Fin (n + 1) => frameMonomial a b n θ S) := by
  unfold spectralPlaneFrameApprox frameMonomial
  rw [finiteMaximum_const_mul _ (Real.exp_pos b).le]
  congr 1
  calc
    (∏ j : Fin p, framePartialMaximum (Nat.succ_le_of_lt j.isLt) n S ^ slopeDrop a j) =
        ∏ j : Fin p, finiteMaximum (fun i : Fin (n + 1) =>
          compressionDeterminant S (denseFrames (Nat.succ_le_of_lt j.isLt) i.val)) ^
            slopeDrop a j := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [framePartialMaximum_eq_finiteMaximum]
    _ = _ := (finiteMaximum_prod_rpow
      (fun (j : Fin p) (i : Fin (n + 1)) => compressionDeterminant S
        (denseFrames (Nat.succ_le_of_lt j.isLt) i.val))
      (slopeDrop a) (fun j i => compressionDeterminant_nonneg hS _)
      (slopeDrop_nonneg ha hmono)).symm
  all_goals
    exact congrArg (fun inst : Fintype (Fin p → Fin (n + 1)) =>
      @finiteMaximum (Fin p → Fin (n + 1)) inst inferInstance
        (fun θ => ∏ j : Fin p, compressionDeterminant S
          (denseFrames (Nat.succ_le_of_lt j.isLt) (θ j).val) ^ slopeDrop a j))
      (Subsingleton.elim _ _)

theorem spectralPlaneFrameApprox_pos {p : ℕ} (a : Fin p → ℝ) (b : ℝ) (n : ℕ)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    0 < spectralPlaneFrameApprox a b n S :=
  mul_pos (Real.exp_pos _) (Finset.prod_pos fun j _ =>
    Real.rpow_pos_of_pos (framePartialMaximum_pos _ n hS) _)

theorem spectralPlaneFrameApprox_monotone {p : ℕ} (a : Fin p → ℝ) (b : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    Monotone (fun n => spectralPlaneFrameApprox a b n S) := by
  intro m n hmn
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact Finset.prod_le_prod₀
    (fun j _ => Real.rpow_nonneg (framePartialMaximum_nonneg _ m hS) _)
    (fun j _ => Real.rpow_le_rpow (framePartialMaximum_nonneg _ m hS)
      (framePartialMaximum_monotone _ S hmn) (slopeDrop_nonneg ha hmono j))

theorem spectralPlaneFrameApprox_le {p : ℕ} (a : Fin p → ℝ) (b : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a) (n : ℕ)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    spectralPlaneFrameApprox a b n S ≤
      Real.exp (coordinatePlane a b (fun i => Real.log (descendingSpectrum S i))) := by
  rw [exp_coordinatePlane_log_spectrum a b hS]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact Finset.prod_le_prod₀
    (fun j _ => Real.rpow_nonneg (framePartialMaximum_nonneg _ n hS.posSemidef) _)
    (fun j _ => Real.rpow_le_rpow (framePartialMaximum_nonneg _ n hS.posSemidef)
      (framePartialMaximum_le _ n S hS.posSemidef) (slopeDrop_nonneg ha hmono j))

theorem spectralPlaneFrameApprox_tendsto {p : ℕ} (a : Fin p → ℝ) (b : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    Tendsto (fun n => spectralPlaneFrameApprox a b n S) atTop
      (𝓝 (Real.exp (coordinatePlane a b (fun i => Real.log (descendingSpectrum S i))))) := by
  rw [exp_coordinatePlane_log_spectrum a b hS]
  apply Tendsto.const_mul
  apply tendsto_finsetProd
  intro j hj
  exact (framePartialMaximum_tendsto _ S hS.posSemidef).rpow_const
    (Or.inr (slopeDrop_nonneg ha hmono j))

end Wishart.Spectral
end
end CanonicalSource84

section CanonicalSource85
/- Source: Wishart/SpectralPlaneProducts.lean -/



/-!
# Finite spectral supporting-plane products and their moments

The functions are defined by nonnegative powers of leading eigenvalue products.
On the positive definite cone these are precisely exponentials of supporting
planes in logarithmic eigenvalues. Trace powers give a common moment bound,
including for every finite frame approximation.
-/

noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped BigOperators Classical ENNReal

namespace Wishart.Spectral

open WishartVerification

theorem continuous_descendingSpectrum (p : ℕ) : Continuous (@descendingSpectrum p) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (Fin.rev i)).comp (continuous_ascendingSpectrum p)

theorem continuous_leadingEigenvalueProduct {p j : ℕ} (hj : j ≤ p) :
    Continuous (leadingEigenvalueProduct hj) := by
  apply continuous_finsetProd
  intro i hi
  exact (continuous_apply (Fin.castLE hj i)).comp (continuous_descendingSpectrum p)

theorem leadingEigenvalueProduct_nonneg {p j : ℕ} (hj : j ≤ p)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ leadingEigenvalueProduct hj S :=
  Finset.prod_nonneg fun i _ => descendingSpectrum_nonneg hS _

theorem descendingSpectrum_le_trace {p : ℕ} {S : Sym p}
    (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) (i : Fin p) :
    descendingSpectrum S i ≤ (S : Matrix (Fin p) (Fin p) ℝ).trace := by
  rw [(selfAdjoint.isHermitian_coe S).trace_eq_sum_eigenvalues]
  exact Finset.single_le_sum (fun j _ => hS.eigenvalues_nonneg j)
    (Finset.mem_univ (ascendingIndexEquiv p (Fin.rev i)))

theorem leadingEigenvalueProduct_le_trace_pow {p j : ℕ} (hj : j ≤ p)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    leadingEigenvalueProduct hj S ≤ (S : Matrix (Fin p) (Fin p) ℝ).trace ^ j := by
  calc
    leadingEigenvalueProduct hj S ≤ ∏ _i : Fin j, (S : Matrix (Fin p) (Fin p) ℝ).trace :=
      Finset.prod_le_prod₀ (fun i _ => descendingSpectrum_nonneg hS _)
        (fun i _ => descendingSpectrum_le_trace hS _)
    _ = _ := by simp

def spectralPlaneMonomial {p : ℕ} (a : Fin p → ℝ) (b : ℝ) (S : Sym p) : ℝ :=
  Real.exp b * ∏ j : Fin p,
    leadingEigenvalueProduct (Nat.succ_le_of_lt j.isLt) S ^ slopeDrop a j

theorem spectralPlaneMonomial_eq_exp {p : ℕ} (a : Fin p → ℝ) (b : ℝ)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    spectralPlaneMonomial a b S =
      Real.exp (coordinatePlane a b (fun i => Real.log (descendingSpectrum S i))) :=
  (exp_coordinatePlane_log_spectrum a b hS).symm

theorem spectralPlaneMonomial_nonneg {p : ℕ} (a : Fin p → ℝ) (b : ℝ)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ spectralPlaneMonomial a b S :=
  mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun j _ =>
    Real.rpow_nonneg (leadingEigenvalueProduct_nonneg _ hS) _)

theorem continuous_spectralPlaneMonomial {p : ℕ} (a : Fin p → ℝ) (b : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a) : Continuous (spectralPlaneMonomial a b) := by
  apply continuous_const.mul
  apply continuous_finsetProd
  intro j hj
  exact (Real.continuous_rpow_const (slopeDrop_nonneg ha hmono j)).comp
    (continuous_leadingEigenvalueProduct _)

theorem continuous_framePartialMaximum {p j : ℕ} (hj : j ≤ p) (n : ℕ) :
    Continuous (framePartialMaximum hj n) := by
  apply Continuous.finset_sup'_apply
  intro m hm
  unfold compressionDeterminant
  fun_prop

theorem continuous_spectralPlaneFrameApprox {p : ℕ} (a : Fin p → ℝ) (b : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a) (n : ℕ) :
    Continuous (spectralPlaneFrameApprox a b n) := by
  apply continuous_const.mul
  apply continuous_finsetProd
  intro j hj
  exact (Real.continuous_rpow_const (slopeDrop_nonneg ha hmono j)).comp
    (continuous_framePartialMaximum _ n)

theorem spectralPlaneFrameApprox_nonneg {p : ℕ} (a : Fin p → ℝ) (b : ℝ) (n : ℕ)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ spectralPlaneFrameApprox a b n S :=
  mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun j _ =>
    Real.rpow_nonneg (framePartialMaximum_nonneg _ n hS) _)

theorem spectralPlaneFrameApprox_le_monomial {p : ℕ} (a : Fin p → ℝ) (b : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a) (n : ℕ)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    spectralPlaneFrameApprox a b n S ≤ spectralPlaneMonomial a b S := by
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact Finset.prod_le_prod₀
    (fun j _ => Real.rpow_nonneg (framePartialMaximum_nonneg _ n hS) _)
    (fun j _ => Real.rpow_le_rpow (framePartialMaximum_nonneg _ n hS)
      (framePartialMaximum_le _ n S hS) (slopeDrop_nonneg ha hmono j))

theorem spectralPlaneFrameApprox_tendsto_monomial {p : ℕ} (a : Fin p → ℝ) (b : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a)
    {S : Sym p} (hS : (S : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    Tendsto (fun n => spectralPlaneFrameApprox a b n S) atTop (𝓝 (spectralPlaneMonomial a b S)) := by
  apply Tendsto.const_mul
  exact tendsto_finsetProd _ fun j _ =>
    (framePartialMaximum_tendsto _ S hS).rpow_const (Or.inr (slopeDrop_nonneg ha hmono j))

theorem allFiniteMoments_leadingEigenvalueProduct
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {p j : ℕ} (hj : j ≤ p) (Z : Ω → Sym p) (hZm : Measurable Z)
    (hZ : ∀ᵐ z ∂μ, (Z z : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hmom : ∀ i j, HasAllFiniteMoments (fun z => (Z z : Matrix (Fin p) (Fin p) ℝ) i j) μ) :
    HasAllFiniteMoments (fun z => leadingEigenvalueProduct hj (Z z)) μ := by
  have ht : HasAllFiniteMoments (fun z => (Z z : Matrix (Fin p) (Fin p) ℝ).trace) μ :=
    HasAllFiniteMoments.finset_sum Finset.univ _ (fun i _ => hmom i i)
  have hb : HasAllFiniteMoments (fun z => (Z z : Matrix (Fin p) (Fin p) ℝ).trace ^ j) μ := by
    simpa only [Real.rpow_natCast] using ht.rpow (show (0 : ℝ) ≤ j by positivity)
  intro q hq
  apply (hb q hq).mono'
  · exact ((continuous_leadingEigenvalueProduct hj).measurable.comp hZm).aestronglyMeasurable
  · filter_upwards [hZ] with z hz
    rw [Real.norm_of_nonneg (leadingEigenvalueProduct_nonneg hj hz)]
    exact leadingEigenvalueProduct_le_trace_pow hj hz

theorem allFiniteMoments_spectralPlaneMonomial
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {p : ℕ} (a : Fin p → ℝ) (b : ℝ) (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a)
    (Z : Ω → Sym p) (hZm : Measurable Z)
    (hZ : ∀ᵐ z ∂μ, (Z z : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hmom : ∀ i j, HasAllFiniteMoments (fun z => (Z z : Matrix (Fin p) (Fin p) ℝ) i j) μ) :
    HasAllFiniteMoments (fun z => spectralPlaneMonomial a b (Z z)) μ := by
  apply HasAllFiniteMoments.const_mul
  apply HasAllFiniteMoments.finset_prod Finset.univ
  intro j hj
  exact (allFiniteMoments_leadingEigenvalueProduct _ Z hZm hZ hmom).rpow
    (slopeDrop_nonneg ha hmono j)

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
  (k : κ → ℕ)

def spectralPlaneMaximumProduct (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (S : ∀ i, Sym (k i)) : ℝ :=
  ∏ i, finiteMaximum (fun j => spectralPlaneMonomial (a i j) (b i j) (S i))

def spectralFrameMaximumProduct (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (n : ℕ) (S : ∀ i, Sym (k i)) : ℝ :=
  ∏ i, finiteMaximum (fun j => spectralPlaneFrameApprox (a i j) (b i j) n (S i))

theorem spectralFrameMaximumProduct_nonneg
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ) (n : ℕ)
    {S : ∀ i, Sym (k i)} (hS : ∀ i, (S i : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosSemidef) :
    0 ≤ spectralFrameMaximumProduct k a b n S :=
  Finset.prod_nonneg fun i _ => finiteMaximum_nonneg fun j =>
    spectralPlaneFrameApprox_nonneg _ _ n (hS i)

theorem spectralFrameMaximumProduct_le
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j)) (n : ℕ)
    {S : ∀ i, Sym (k i)} (hS : ∀ i, (S i : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosSemidef) :
    spectralFrameMaximumProduct k a b n S ≤ spectralPlaneMaximumProduct k a b S :=
  Finset.prod_le_prod₀
    (fun i _ => finiteMaximum_nonneg fun j => spectralPlaneFrameApprox_nonneg _ _ n (hS i))
    (fun i _ => finiteMaximum_mono fun j =>
      spectralPlaneFrameApprox_le_monomial _ _ (ha i j) (hmono i j) n (hS i))

theorem continuous_spectralFrameMaximumProduct
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j)) (n : ℕ) :
    Continuous (spectralFrameMaximumProduct k a b n) := by
  apply continuous_finsetProd
  intro i hi
  apply continuous_finiteMaximum
  intro j
  exact (continuous_spectralPlaneFrameApprox _ _ (ha i j) (hmono i j) n).comp (continuous_apply i)

theorem continuous_spectralPlaneMaximumProduct
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j)) :
    Continuous (spectralPlaneMaximumProduct k a b) := by
  apply continuous_finsetProd
  intro i hi
  apply continuous_finiteMaximum
  intro j
  exact (continuous_spectralPlaneMonomial _ _ (ha i j) (hmono i j)).comp (continuous_apply i)

theorem spectralFrameMaximumProduct_tendsto
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j))
    {S : ∀ i, Sym (k i)} (hS : ∀ i, (S i : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosSemidef) :
    Tendsto (fun n => spectralFrameMaximumProduct k a b n S) atTop
      (𝓝 (spectralPlaneMaximumProduct k a b S)) := by
  apply tendsto_finsetProd
  intro i hi
  exact Filter.Tendsto.finset_sup'_nhds_apply Finset.univ_nonempty
    (fun j _ => spectralPlaneFrameApprox_tendsto_monomial _ _ (ha i j) (hmono i j) (hS i))

theorem allFiniteMoments_spectralPlaneMaximumProduct
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j))
    (Z : Ω → ∀ i, Sym (k i)) (hZm : Measurable Z)
    (hZ : ∀ᵐ z ∂μ, ∀ i, (Z z i : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosSemidef)
    (hmom : ∀ i s t, HasAllFiniteMoments
      (fun z => (Z z i : Matrix (Fin (k i)) (Fin (k i)) ℝ) s t) μ) :
    HasAllFiniteMoments (fun z => spectralPlaneMaximumProduct k a b (Z z)) μ := by
  apply HasAllFiniteMoments.finset_prod Finset.univ
  intro i hi
  apply hasAllFiniteMoments_finiteMaximum
  intro j
  exact allFiniteMoments_spectralPlaneMonomial _ _ (ha i j) (hmono i j)
    (fun z => Z z i) ((measurable_pi_apply i).comp hZm) (hZ.mono fun z hz => hz i) (hmom i)

theorem spectralFrameMaximumProduct_integral_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j))
    (Z : Ω → ∀ i, Sym (k i)) (hZm : Measurable Z)
    (hZ : ∀ᵐ z ∂μ, ∀ i, (Z z i : Matrix (Fin (k i)) (Fin (k i)) ℝ).PosSemidef)
    (hmom : ∀ i s t, HasAllFiniteMoments
      (fun z => (Z z i : Matrix (Fin (k i)) (Fin (k i)) ℝ) s t) μ) :
    Tendsto (fun n => ∫ z, spectralFrameMaximumProduct k a b n (Z z) ∂μ) atTop
      (𝓝 (∫ z, spectralPlaneMaximumProduct k a b (Z z) ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun z => spectralPlaneMaximumProduct k a b (Z z))
    (fun n => ((continuous_spectralFrameMaximumProduct k a b ha hmono n).measurable.comp
      hZm).aestronglyMeasurable)
    (allFiniteMoments_spectralPlaneMaximumProduct k a b ha hmono Z hZm hZ hmom).integrable ?_ ?_
  · intro n
    filter_upwards [hZ] with z hz
    rw [Real.norm_of_nonneg (spectralFrameMaximumProduct_nonneg k a b n hz)]
    exact spectralFrameMaximumProduct_le k a b ha hmono n hz
  · filter_upwards [hZ] with z hz
    exact spectralFrameMaximumProduct_tendsto k a b ha hmono hz

end Wishart.Spectral
end
end CanonicalSource85

section CanonicalSource86
/- Source: Wishart/MultiCompressionLogs.lean -/



/-!
# Positive smooth monomials of several compression determinants

Every monomial below has a globally smooth, polynomially bounded extension,
with a genuine positive constant lower bound. On the positive cone its logarithm
agrees locally with the sum of the intended compression logarithms. Consequently
the radial generator inequality follows from the actual compression calculations.
This supplies the primitives for finite maxima of spectral supporting planes.
-/

noncomputable section

open Filter Topology Matrix
open scoped BigOperators Matrix.Norms.Operator

namespace WishartVerification

variable {p : ℕ} {ι : Type*} [Fintype ι]

def smoothCompressionMonomial (ε : ℝ) (D : ι → CompressionData p)
    (b : ℝ) (X : SymmetricMatrix p) : ℝ :=
  Real.exp b * regularizedCompressionProduct ε D X

theorem smoothCompressionMonomial_pos {ε : ℝ} (hε : 0 < ε)
    (D : ι → CompressionData p) (b : ℝ) (X : SymmetricMatrix p) :
    0 < smoothCompressionMonomial ε D b X := by
  apply mul_pos (Real.exp_pos b)
  exact Finset.prod_pos (fun i _ =>
    smoothRegularizedDetPower_pos hε (D i).exponent (D i).offset (D i).linear X)

theorem hasTemperateGrowth_smoothCompressionMonomial {ε : ℝ} (hε : 0 < ε)
    (D : ι → CompressionData p) (b : ℝ) :
    (smoothCompressionMonomial ε D b).HasTemperateGrowth :=
  (Function.HasTemperateGrowth.const (Real.exp b)).mul
    (hasTemperateGrowth_regularizedCompressionProduct hε D)

theorem smoothCompressionMonomial_lower {ε : ℝ} (hε : 0 < ε)
    (D : ι → CompressionData p) (b : ℝ)
    (hη : ∀ i, 0 ≤ (D i).exponent) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X, δ ≤ smoothCompressionMonomial ε D b X := by
  let δ : ℝ := Real.exp b * ∏ i, (ε ^ (D i).size / 2 / 2) ^ (D i).exponent
  have hδ : 0 < δ := by
    apply mul_pos (Real.exp_pos _)
    exact Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨δ, hδ, fun X => ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Real.rpow_nonneg (by positivity) _
  · intro i hi
    simpa only [Fintype.card_fin] using
      smoothRegularizedDetPower_lower hε (hη i) (D i).offset (D i).linear X

theorem smoothCompressionMonomial_eventually_exp {ε : ℝ} (hε : 0 < ε)
    (D : ι → CompressionData p) (b : ℝ)
    (hB : ∀ i, (D i).offset.PosSemidef)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    smoothCompressionMonomial ε D b =ᶠ[𝓝 X]
      (fun Y => Real.exp (compressionLogSum ε D Y + b)) := by
  filter_upwards [regularizedCompressionProduct_eventually_exp hε D hB hX] with Y hY
  simp only [smoothCompressionMonomial, hY, Real.exp_add, mul_comm]

theorem log_smoothCompressionMonomial_eventuallyEq {ε : ℝ} (hε : 0 < ε)
    (D : ι → CompressionData p) (b : ℝ)
    (hB : ∀ i, (D i).offset.PosSemidef)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    (fun Y => Real.log (smoothCompressionMonomial ε D b Y)) =ᶠ[𝓝 X]
      (fun Y => compressionLogSum ε D Y + b) := by
  filter_upwards [smoothCompressionMonomial_eventually_exp hε D b hB hX] with Y hY
  rw [hY, Real.log_exp]

theorem compressionLogSum_sum_differentiable_near (ε : ℝ)
    (D : ι → CompressionData p) {X : SymmetricMatrix p}
    (hunit : ∀ i, IsUnit (regularizedCompression ε (D i).offset (D i).linear X).det) :
    ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ (compressionLogSum ε D) Y := by
  filter_upwards [compressionLogSum_differentiable_near ε D hunit] with Y hY
  exact DifferentiableAt.fun_sum (fun i _ => (hY i).const_mul (D i).exponent)

theorem compressionLogSum_direction_differentiable (ε : ℝ)
    (D : ι → CompressionData p) {X : SymmetricMatrix p}
    (hunit : ∀ i, IsUnit (regularizedCompression ε (D i).offset (D i).linear X).det)
    (H : SymmetricMatrix p) :
    DifferentiableAt ℝ (fun Y => fderiv ℝ (compressionLogSum ε D) Y H) X := by
  let f : ι → SymmetricMatrix p → ℝ := fun i =>
    compressionLog ε (D i).offset (D i).linear
  have hf := compressionLogSum_differentiable_near ε D hunit
  have hD (i : ι) : DifferentiableAt ℝ (fun Y => fderiv ℝ (f i) Y H) X :=
    (hasFDerivAt_compressionLog_direction ε (D i).offset (D i).linear (hunit i) H).differentiableAt
  have heq : (fun Y => fderiv ℝ (compressionLogSum ε D) Y H) =ᶠ[𝓝 X]
      (fun Y => ∑ i, (D i).exponent * fderiv ℝ (f i) Y H) :=
    hf.mono fun Y hY => fderiv_linear_combination_apply _ f hY H
  exact heq.differentiableAt_iff.mpr
    (DifferentiableAt.fun_sum (fun i _ => (hD i).const_mul (D i).exponent))

theorem compressionLogSum_generator_nonneg {ε : ℝ} (hε : 0 < ε)
    (D : ι → CompressionData p)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    {N : ℝ} (hN : ∀ i, min ((D i).size : ℝ) (p : ℝ) + 1 ≤ N)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) :
    0 ≤ symmetricDirectionalGenerator N v (compressionLogSum ε D) X := by
  let f : ι → SymmetricMatrix p → ℝ := fun i =>
    compressionLog ε (D i).offset (D i).linear
  have hunit (i : ι) : IsUnit (regularizedCompression ε (D i).offset (D i).linear X).det :=
    isUnit_iff_ne_zero.mpr (regularizedCompression_posDef hε (hB i) (D i).linear hX).det_pos.ne'
  have hf := compressionLogSum_differentiable_near ε D hunit
  have hD (i : ι) (H : SymmetricMatrix p) :
      DifferentiableAt ℝ (fun Y => fderiv ℝ (f i) Y H) X :=
    (hasFDerivAt_compressionLog_direction ε (D i).offset (D i).linear (hunit i) H).differentiableAt
  change 0 ≤ symmetricDirectionalGenerator N v (fun Y => ∑ i, (D i).exponent * f i Y) X
  rw [symmetricDirectionalGenerator_linear_combination _ f hf hD]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hη i)
    (symmetricDirectionalGenerator_compressionLog_nonneg_min hε (hB i) (D i).linear hX
      (by simpa only [Fintype.card_fin] using hN i) v)

/-- The primitive logarithm has the actual nonnegative radial generator. The
minimum uses the ambient dimension, so rectangular compressions lose no rank
generality. -/
theorem log_smoothCompressionMonomial_generator_nonneg {ε : ℝ} (hε : 0 < ε)
    (D : ι → CompressionData p) (b : ℝ)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    {N : ℝ} (hN : ∀ i, min ((D i).size : ℝ) (p : ℝ) + 1 ≤ N)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) :
    0 ≤ symmetricDirectionalGenerator N v
      (fun Y => Real.log (smoothCompressionMonomial ε D b Y)) X := by
  have hunit (i : ι) : IsUnit (regularizedCompression ε (D i).offset (D i).linear X).det :=
    isUnit_iff_ne_zero.mpr (regularizedCompression_posDef hε (hB i) (D i).linear hX).det_pos.ne'
  rw [symmetricDirectionalGenerator_congr
    (log_smoothCompressionMonomial_eventuallyEq hε D b hB hX)]
  have hlin := symmetricDirectionalGenerator_affine
    (compressionLogSum_sum_differentiable_near ε D hunit)
    (compressionLogSum_direction_differentiable ε D hunit) 1 b N v
  simp only [one_mul] at hlin
  rw [hlin]
  exact compressionLogSum_generator_nonneg hε D hB hη hN hX v

theorem smoothCompressionMonomial_eq {ε : ℝ} (hε : 0 < ε)
    (D : ι → CompressionData p) (b : ℝ)
    (hB : ∀ i, (D i).offset.PosSemidef)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    smoothCompressionMonomial ε D b X =
      Real.exp b * ∏ i,
        (regularizedCompression ε (D i).offset (D i).linear X).det ^ (D i).exponent := by
  unfold smoothCompressionMonomial regularizedCompressionProduct
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact smoothRegularizedDetPower_eq hε _ (hB i) (D i).linear hX

end WishartVerification
end
end CanonicalSource86

section CanonicalSource87
/- Source: Wishart/CompressionMonomialMeans.lean -/



/-!
# Finite maxima of compression monomials under the actual radial law

The analytic power-mean closure is instantiated by the concrete monomials from
`MultiCompressionLogs`. Regularization is removed by dominated convergence;
the dominating function is the same finite maximum at regularization one and
has all finite moments. The conclusion contains no generator premise.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped BigOperators Matrix.Norms.Operator Classical

namespace WishartVerification

variable {p : ℕ} {ρ : Type*} [Fintype ρ]

def compressionMonomialPrimitive (ε : ℝ) (hε : 0 < ε)
    (D : ρ → CompressionData p) (b : ℝ) (hη : ∀ i, 0 ≤ (D i).exponent) :
    PositiveTemperatePrimitive p where
  val := smoothCompressionMonomial ε D b
  growth := hasTemperateGrowth_smoothCompressionMonomial hε D b
  lower := smoothCompressionMonomial_lower hε D b hη

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
  {σ : κ → Type*} [∀ i, Fintype (σ i)]

def monomialMaximumProduct (ε : ℝ)
    (D : ∀ i : κ, ι → σ i → CompressionData p) (b : κ → ι → ℝ)
    (X : SymmetricMatrix p) : ℝ :=
  ∏ i, finiteMaximum (fun j => Real.exp (b i j) * ∏ l,
    (regularizedCompression ε (D i j l).offset (D i j l).linear X).det ^ (D i j l).exponent)

theorem primitiveMaximumProduct_monomial_eq {ε : ℝ} (hε : 0 < ε)
    (D : ∀ i : κ, ι → σ i → CompressionData p) (b : κ → ι → ℝ)
    (hη : ∀ i j l, 0 ≤ (D i j l).exponent)
    (hB : ∀ i j l, (D i j l).offset.PosSemidef)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    primitiveMaximumProduct
      (fun i j => compressionMonomialPrimitive ε hε (D i j) (b i j) (hη i j))
      (fun _ _ => 1) (fun _ _ => 0) X = monomialMaximumProduct ε D b X := by
  unfold primitiveMaximumProduct monomialMaximumProduct
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  funext j
  simp only [Real.exp_zero, Real.rpow_one, one_mul]
  exact smoothCompressionMonomial_eq hε (D i j) (b i j) (hB i j) hX

theorem regularizedCompression_posSemidef {k : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    {B : Matrix (Fin k) (Fin k) ℝ} (hB : B.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    (regularizedCompression ε B M X).PosSemidef := by
  apply Matrix.PosSemidef.add
  · apply hB.add
    simpa only [compressionCLM_apply, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.conjTranspose_mul_mul_same M
  · exact Matrix.PosSemidef.one.smul hε

theorem regularizedCompression_det_mono_epsilon {k : ℕ} {ε δ : ℝ}
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    {B : Matrix (Fin k) (Fin k) ℝ} (hB : B.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    (regularizedCompression ε B M X).det ≤ (regularizedCompression δ B M X).det := by
  let A : SymmetricMatrix k := ⟨regularizedCompression ε B M X,
    Matrix.isHermitian_iff_isSelfAdjoint.mp
      (regularizedCompression_posSemidef hε hB M hX).isHermitian⟩
  let C : SymmetricMatrix k := ⟨regularizedCompression δ B M X,
    Matrix.isHermitian_iff_isSelfAdjoint.mp
      (regularizedCompression_posSemidef (hε.trans hεδ) hB M hX).isHermitian⟩
  apply Wishart.det_le_of_posSemidef_sub A C (regularizedCompression_posSemidef hε hB M hX)
  have heq : (C : Matrix (Fin k) (Fin k) ℝ) - A = (δ - ε) • 1 := by
    change (B + compressionCLM M X + δ • 1) - (B + compressionCLM M X + ε • 1) = _
    rw [sub_smul]
    abel
  rw [heq]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hεδ)

theorem monomialMaximumProduct_nonneg {ε : ℝ} (hε : 0 ≤ ε)
    (D : ∀ i : κ, ι → σ i → CompressionData p) (b : κ → ι → ℝ)
    (hB : ∀ i j l, (D i j l).offset.PosSemidef)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ monomialMaximumProduct ε D b X := by
  apply Finset.prod_nonneg
  intro i hi
  apply finiteMaximum_nonneg
  intro j
  apply mul_nonneg (Real.exp_pos _).le
  exact Finset.prod_nonneg fun l _ => Real.rpow_nonneg
    (regularizedCompression_posSemidef hε (hB i j l) (D i j l).linear hX).det_nonneg _

theorem monomialMaximumProduct_mono_epsilon
    (D : ∀ i : κ, ι → σ i → CompressionData p) (b : κ → ι → ℝ)
    (hη : ∀ i j l, 0 ≤ (D i j l).exponent)
    (hB : ∀ i j l, (D i j l).offset.PosSemidef)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ) :
    monomialMaximumProduct ε D b X ≤ monomialMaximumProduct δ D b X := by
  apply Finset.prod_le_prod₀
  · intro i hi
    apply finiteMaximum_nonneg
    intro j
    exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun l _ =>
      Real.rpow_nonneg (regularizedCompression_posSemidef hε (hB i j l)
        (D i j l).linear hX).det_nonneg _)
  · intro i hi
    apply finiteMaximum_mono
    intro j
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply Finset.prod_le_prod₀
    · intro l hl
      exact Real.rpow_nonneg (regularizedCompression_posSemidef hε (hB i j l)
        (D i j l).linear hX).det_nonneg _
    · intro l hl
      exact Real.rpow_le_rpow
        (regularizedCompression_posSemidef hε (hB i j l) (D i j l).linear hX).det_nonneg
        (regularizedCompression_det_mono_epsilon hε hεδ (hB i j l) (D i j l).linear hX)
        (hη i j l)

theorem monomialMaximumProduct_continuous_epsilon
    (D : ∀ i : κ, ι → σ i → CompressionData p) (b : κ → ι → ℝ)
    (hη : ∀ i j l, 0 ≤ (D i j l).exponent) (X : SymmetricMatrix p) :
    Continuous (fun ε => monomialMaximumProduct ε D b X) := by
  apply continuous_finsetProd
  intro i hi
  apply continuous_finiteMaximum
  intro j
  apply continuous_const.mul
  apply continuous_finsetProd
  intro l hl
  apply (Real.continuous_rpow_const (hη i j l)).comp
  unfold regularizedCompression
  fun_prop

theorem allFiniteMoments_monomialMaximumProduct
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun z : E => ‖z‖) μ)
    {Z : E → SymmetricMatrix p} (hZ : Z.HasTemperateGrowth)
    (ε : ℝ) (D : ∀ i : κ, ι → σ i → CompressionData p) (b : κ → ι → ℝ)
    (hη : ∀ i j l, 0 ≤ (D i j l).exponent) :
    HasAllFiniteMoments (fun z => monomialMaximumProduct ε D b (Z z)) μ := by
  apply HasAllFiniteMoments.finset_prod Finset.univ
  intro i hi
  apply hasAllFiniteMoments_finiteMaximum
  intro j
  apply HasAllFiniteMoments.const_mul
  apply HasAllFiniteMoments.finset_prod Finset.univ
  intro l hl
  apply HasAllFiniteMoments.rpow _ (hη i j l)
  intro u hu
  exact memLp_temperate_of_allNormMoments hμ
    ((hasTemperateGrowth_regularizedCompression_det ε (D i j l).offset
      (D i j l).linear).comp hZ) hu

end WishartVerification

namespace Wishart

open WishartVerification

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
  {σ : κ → Type*} [∀ i, Fintype (σ i)]

theorem monotoneOn_scalarRadial_monomialMaximumProduct_regularized
    {r : ℕ} {N ε : ℝ} (hN : (r : ℝ) < N) (hε : 0 < ε)
    (D : ∀ i : κ, ι → σ i → CompressionData (1 + r)) (b : κ → ι → ℝ)
    (hη : ∀ i j l, 0 ≤ (D i j l).exponent)
    (hB : ∀ i j l, (D i j l).offset.PosSemidef)
    (hsize : ∀ i j l, min ((D i j l).size : ℝ) ((1 + r : ℕ) : ℝ) + 1 ≤ N) :
    MonotoneOn (fun t : ℝ => ∫ z : ScalarRegressionNoise r,
      monomialMaximumProduct ε D b (scalarRadialMatrix (Real.sqrt t) z)
        ∂scalarRegressionNoiseMeasure N r) (Set.Ici 0) := by
  let Q i j := compressionMonomialPrimitive ε hε (D i j) (b i j) (hη i j)
  have hmono := monotoneOn_scalarRadial_primitiveMaximumProduct hN Q
    (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => zero_le_one)
    (fun X hX i j => log_smoothCompressionMonomial_generator_nonneg hε
      (D i j) (b i j) (hB i j) (hη i j) (hsize i j) hX (scalarTransverseAxis r))
  have heq (t : ℝ) : (∫ z : ScalarRegressionNoise r,
      primitiveMaximumProduct Q (fun _ _ => 1) (fun _ _ => 0)
        (scalarRadialMatrix (Real.sqrt t) z) ∂scalarRegressionNoiseMeasure N r) =
      ∫ z : ScalarRegressionNoise r,
        monomialMaximumProduct ε D b (scalarRadialMatrix (Real.sqrt t) z)
          ∂scalarRegressionNoiseMeasure N r := by
    apply integral_congr_ae
    filter_upwards [ae_scalarRadialMatrix_posSemidef N (Real.sqrt t)] with z hz
    exact primitiveMaximumProduct_monomial_eq hε D b hη hB hz
  simpa only [heq] using hmono

theorem scalar_monomialMaximumProduct_integral_tendsto
    {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    (D : ∀ i : κ, ι → σ i → CompressionData (1 + r)) (b : κ → ι → ℝ)
    (hη : ∀ i j l, 0 ≤ (D i j l).exponent)
    (hB : ∀ i j l, (D i j l).offset.PosSemidef) (s : ℝ) :
    Tendsto (fun n => ∫ z : ScalarRegressionNoise r,
      monomialMaximumProduct (determinantRegularization n) D b (scalarRadialMatrix s z)
        ∂scalarRegressionNoiseMeasure N r) atTop
      (𝓝 (∫ z : ScalarRegressionNoise r,
        monomialMaximumProduct 0 D b (scalarRadialMatrix s z)
          ∂scalarRegressionNoiseMeasure N r)) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  have hZ := (hasTemperateGrowth_scalarRadialMatrix r).comp
    (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const s) Function.HasTemperateGrowth.id)
  have hm (ε : ℝ) := allFiniteMoments_monomialMaximumProduct
    (allFiniteNormMoments_scalarRegressionNoise hN) hZ ε D b hη
  refine tendsto_integral_of_dominated_convergence
    (fun z => monomialMaximumProduct 1 D b (scalarRadialMatrix s z))
    (fun n => (hm (determinantRegularization n)).integrable.aestronglyMeasurable)
    (hm 1).integrable ?_ ?_
  · intro n
    filter_upwards [ae_scalarRadialMatrix_posSemidef N s] with z hz
    rw [Real.norm_of_nonneg (monomialMaximumProduct_nonneg
      (determinantRegularization_pos n).le D b hB hz)]
    exact monomialMaximumProduct_mono_epsilon D b hη hB hz
      (determinantRegularization_pos n).le (determinantRegularization_le_one n)
  · exact Filter.Eventually.of_forall fun z =>
      (monomialMaximumProduct_continuous_epsilon D b hη
        (scalarRadialMatrix s z)).continuousAt.tendsto.comp tendsto_determinantRegularization

/-- Finite maxima of arbitrary compression monomials satisfy the exact radial
comparison whenever each genuine compression rank obeys the analytic bound. -/
theorem monotoneOn_scalarRadial_monomialMaximumProduct
    {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    (D : ∀ i : κ, ι → σ i → CompressionData (1 + r)) (b : κ → ι → ℝ)
    (hη : ∀ i j l, 0 ≤ (D i j l).exponent)
    (hB : ∀ i j l, (D i j l).offset.PosSemidef)
    (hsize : ∀ i j l, min ((D i j l).size : ℝ) ((1 + r : ℕ) : ℝ) + 1 ≤ N) :
    MonotoneOn (fun t : ℝ => ∫ z : ScalarRegressionNoise r,
      monomialMaximumProduct 0 D b (scalarRadialMatrix (Real.sqrt t) z)
        ∂scalarRegressionNoiseMeasure N r) (Set.Ici 0) := by
  intro s hs t ht hst
  exact le_of_tendsto_of_tendsto
    (scalar_monomialMaximumProduct_integral_tendsto hN D b hη hB (Real.sqrt s))
    (scalar_monomialMaximumProduct_integral_tendsto hN D b hη hB (Real.sqrt t))
    (Filter.Eventually.of_forall fun n =>
      monotoneOn_scalarRadial_monomialMaximumProduct_regularized hN
        (determinantRegularization_pos n) D b hη hB hsize hs ht hst)

end Wishart
end
end CanonicalSource87

section CanonicalSource88
/- Source: Wishart/SpectralCompressionApproximation.lean -/



/-!
# Realizing finite spectral frame tests as compression monomials

The same finite choice type is shared by all outer factors. Evaluation onto
each factor's own frame family is surjective, so the extra choice coordinates
do not alter its maximum. All matrix identities below are literal rectangular
compression identities; no injectivity or extra rank hypothesis is introduced.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped Classical BigOperators Matrix.Norms.Operator

namespace WishartVerification

theorem finiteMaximum_comp_surjective {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α → β) (hf : Function.Surjective f) (g : β → ℝ) :
    finiteMaximum (fun x => g (f x)) = finiteMaximum g := by
  apply le_antisymm
  · exact finiteMaximum_le fun x => le_finiteMaximum g (f x)
  · apply finiteMaximum_le
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact le_finiteMaximum (fun x => g (f x)) x

end WishartVerification

namespace Wishart.Spectral

open WishartVerification

def frameCompressionData {p k : ℕ}
    (E : Matrix (Fin k) (Fin k) ℝ) (M : Matrix (Fin p) (Fin k) ℝ)
    (a : Fin k → ℝ) (n : ℕ) (θ : Fin k → Fin (n + 1)) (j : Fin k) :
    CompressionData p where
  size := j.val + 1
  offset := (denseFrames (Nat.succ_le_of_lt j.isLt) (θ j).val).valᵀ * E *
    (denseFrames (Nat.succ_le_of_lt j.isLt) (θ j).val).val
  linear := M * (denseFrames (Nat.succ_le_of_lt j.isLt) (θ j).val).val
  exponent := slopeDrop a j

theorem frameCompressionData_offset_posSemidef {p k : ℕ}
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ) (a : Fin k → ℝ)
    (n : ℕ) (θ : Fin k → Fin (n + 1)) (j : Fin k) :
    (frameCompressionData E M a n θ j).offset.PosSemidef := by
  simpa only [frameCompressionData, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hE.conjTranspose_mul_mul_same (denseFrames (Nat.succ_le_of_lt j.isLt) (θ j).val).val

theorem frameCompressionData_matrix {p k : ℕ}
    (E : Matrix (Fin k) (Fin k) ℝ) (M : Matrix (Fin p) (Fin k) ℝ)
    (a : Fin k → ℝ) (n : ℕ) (θ : Fin k → Fin (n + 1))
    (j : Fin k) (X : Sym p) :
    regularizedCompression 0 (frameCompressionData E M a n θ j).offset
      (frameCompressionData E M a n θ j).linear X =
      (denseFrames (Nat.succ_le_of_lt j.isLt) (θ j).val).valᵀ *
        (E + Mᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * M) *
          (denseFrames (Nat.succ_le_of_lt j.isLt) (θ j).val).val := by
  dsimp only [frameCompressionData, regularizedCompression]
  rw [compressionCLM_apply]
  simp only [zero_smul, add_zero, Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]

theorem frameCompressionData_monomial_eq {p k : ℕ}
    (E : Matrix (Fin k) (Fin k) ℝ) (hE : E.IsHermitian)
    (M : Matrix (Fin p) (Fin k) ℝ) (a : Fin k → ℝ) (b : ℝ)
    (n : ℕ) (θ : Fin k → Fin (n + 1)) (X : Sym p) :
    Real.exp b * (∏ j : Fin k,
      (regularizedCompression 0 (frameCompressionData E M a n θ j).offset
        (frameCompressionData E M a n θ j).linear X).det ^
          (frameCompressionData E M a n θ j).exponent) =
      frameMonomial a b n θ (affineCompressionSym E hE M X) := by
  unfold frameMonomial
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [frameCompressionData_matrix]
  simp only [compressionDeterminant, coe_affineCompressionSym, frameCompressionData] <;> rfl

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
  (k : κ → ℕ)

def frameFamilyChoices (n : ℕ) := ∀ i : κ, ι × (Fin (k i) → Fin (n + 1))

instance frameFamilyChoices_fintype (n : ℕ) : Fintype (frameFamilyChoices (ι := ι) k n) :=
  inferInstanceAs (Fintype (∀ i : κ, ι × (Fin (k i) → Fin (n + 1))))

instance frameFamilyChoices_nonempty (n : ℕ) : Nonempty (frameFamilyChoices (ι := ι) k n) :=
  inferInstanceAs (Nonempty (∀ i : κ, ι × (Fin (k i) → Fin (n + 1))))

theorem spectralFrameMaximumProduct_eq_monomialMaximumProduct {p : ℕ}
    (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).PosSemidef)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j))
    (n : ℕ) {X : Sym p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    spectralFrameMaximumProduct k a b n
      (fun i => affineCompressionSym (E i) (hE i).isHermitian (M i) X) =
      monomialMaximumProduct 0
        (fun (i : κ) (ω : frameFamilyChoices (ι := ι) k n) =>
          frameCompressionData (E i) (M i) (a i (ω i).1) n (ω i).2)
        (fun i ω => b i (ω i).1) X := by
  unfold spectralFrameMaximumProduct monomialMaximumProduct
  apply Finset.prod_congr rfl
  intro i hi
  have hS : (affineCompressionSym (E i) (hE i).isHermitian (M i) X :
      Matrix (Fin (k i)) (Fin (k i)) ℝ).PosSemidef := by
    rw [coe_affineCompressionSym]
    apply (hE i).add
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.conjTranspose_mul_mul_same (M i)
  simp_rw [frameCompressionData_monomial_eq _ (hE i).isHermitian]
  let S := affineCompressionSym (E i) (hE i).isHermitian (M i) X
  change finiteMaximum (fun j : ι => spectralPlaneFrameApprox (a i j) (b i j) n S) =
    finiteMaximum (fun ω : ∀ l : κ, ι × (Fin (k l) → Fin (n + 1)) =>
      frameMonomial (a i (ω i).1) (b i (ω i).1) n (ω i).2 S)
  rw [finiteMaximum_comp_surjective
    (fun ω : ∀ l : κ, ι × (Fin (k l) → Fin (n + 1)) => ω i)
    (Function.surjective_eval i)
    (fun z : ι × (Fin (k i) → Fin (n + 1)) =>
      frameMonomial (a i z.1) (b i z.1) n z.2 S)]
  rw [finiteMaximum_pair (fun (j : ι) (θ : Fin (k i) → Fin (n + 1)) =>
    frameMonomial (a i j) (b i j) n θ S)]
  congr 1
  funext j
  exact spectralPlaneFrameApprox_eq_maximum _ _ n (ha i j) (hmono i j) hS

end Wishart.Spectral

namespace Wishart

open WishartVerification Spectral

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem monotoneOn_scalarRadial_spectralFrameMaximumProduct
    {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    (k : κ → ℕ) (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).PosSemidef)
    (M : ∀ i, Matrix (Fin (1 + r)) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j))
    (hsize : ∀ i, min (k i : ℝ) ((1 + r : ℕ) : ℝ) + 1 ≤ N) (n : ℕ) :
    MonotoneOn (fun t : ℝ => ∫ z : ScalarRegressionNoise r,
      spectralFrameMaximumProduct k a b n
        (fun i => affineCompressionSym (E i) (hE i).isHermitian (M i)
          (scalarRadialMatrix (Real.sqrt t) z)) ∂scalarRegressionNoiseMeasure N r)
      (Set.Ici 0) := by
  let D : ∀ i : κ, frameFamilyChoices (ι := ι) k n → Fin (k i) → CompressionData (1 + r) :=
    fun i ω => frameCompressionData (E i) (M i) (a i (ω i).1) n (ω i).2
  let b' : κ → frameFamilyChoices (ι := ι) k n → ℝ := fun i ω => b i (ω i).1
  have hη : ∀ i ω l, 0 ≤ (D i ω l).exponent :=
    fun i ω l => slopeDrop_nonneg (ha i (ω i).1) (hmono i (ω i).1) l
  have hB : ∀ i ω l, (D i ω l).offset.PosSemidef :=
    fun i ω l => frameCompressionData_offset_posSemidef (hE i) _ _ n _ l
  have hsizes : ∀ i ω l,
      min ((D i ω l).size : ℝ) ((1 + r : ℕ) : ℝ) + 1 ≤ N := by
    intro i ω l
    have hk : ((D i ω l).size : ℝ) ≤ (k i : ℝ) := by
      change ((l.val + 1 : ℕ) : ℝ) ≤ (k i : ℝ)
      exact_mod_cast Nat.succ_le_of_lt l.isLt
    have hmin := min_le_min hk (le_refl ((1 + r : ℕ) : ℝ))
    linarith [hsize i]
  have hmono' := monotoneOn_scalarRadial_monomialMaximumProduct hN D b' hη hB hsizes
  have heq (t : ℝ) : (∫ z : ScalarRegressionNoise r,
      spectralFrameMaximumProduct k a b n
        (fun i => affineCompressionSym (E i) (hE i).isHermitian (M i)
          (scalarRadialMatrix (Real.sqrt t) z)) ∂scalarRegressionNoiseMeasure N r) =
      ∫ z : ScalarRegressionNoise r,
        monomialMaximumProduct 0 D b' (scalarRadialMatrix (Real.sqrt t) z)
          ∂scalarRegressionNoiseMeasure N r := by
    apply integral_congr_ae
    filter_upwards [ae_scalarRadialMatrix_posSemidef N (Real.sqrt t)] with z hz
    exact spectralFrameMaximumProduct_eq_monomialMaximumProduct k E hE M a b ha hmono n hz
  simpa only [heq] using hmono'

end Wishart
end
end CanonicalSource88

section CanonicalSource89
/- Source: Wishart/SpectralRegressionComparison.lean -/



/-!
# Actual conditional comparison for finite spectral supporting-plane tests

Finite frame approximations converge under a common integrable spectral bound.
Rectangular congruence preserves their exact affine compression form. The
resulting radial comparison therefore instantiates the generic actual-law
regression assembly without an analytic comparison assumption.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped BigOperators Classical Matrix.Norms.Operator

namespace Wishart.Spectral

open WishartVerification

theorem continuous_affineCompressionSym {p k : ℕ}
    (E : Matrix (Fin k) (Fin k) ℝ) (hE : E.IsHermitian)
    (M : Matrix (Fin p) (Fin k) ℝ) : Continuous (affineCompressionSym E hE M) := by
  unfold affineCompressionSym
  exact continuous_const.add (Matrix.symmetricCongruenceLinearMap Mᵀ).continuous_of_finiteDimensional

theorem affineCompressionSym_posSemidef {p k : ℕ}
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ) {X : Sym p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    (affineCompressionSym E hE.isHermitian M X : Matrix (Fin k) (Fin k) ℝ).PosSemidef := by
  rw [coe_affineCompressionSym]
  apply hE.add
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hX.conjTranspose_mul_mul_same M

theorem allFiniteMoments_affineCompression_entry
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {p k : ℕ} (E : Matrix (Fin k) (Fin k) ℝ) (hE : E.IsHermitian)
    (M : Matrix (Fin p) (Fin k) ℝ) (X : Ω → Sym p)
    (hmom : ∀ i j, HasAllFiniteMoments (fun z => (X z : Matrix (Fin p) (Fin p) ℝ) i j) μ)
    (s t : Fin k) :
    HasAllFiniteMoments (fun z =>
      (affineCompressionSym E hE M (X z) : Matrix (Fin k) (Fin k) ℝ) s t) μ := by
  simp only [coe_affineCompressionSym, Matrix.add_apply]
  exact (HasAllFiniteMoments.const (E s t)).add
    (HasAllFiniteMoments.matrix_right_mul_entry _ M
      (fun i j => HasAllFiniteMoments.matrix_left_mul_entry _ Mᵀ hmom i j) s t)

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
  {p : ℕ} (k : κ → ℕ)

def affineSpectralPlaneTest
    (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).IsHermitian)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ) (X : Sym p) : ℝ :=
  spectralPlaneMaximumProduct k a b (fun i => affineCompressionSym (E i) (hE i) (M i) X)

theorem continuous_affineSpectralPlaneTest
    (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).IsHermitian)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j)) :
    Continuous (affineSpectralPlaneTest k E hE M a b) :=
  (continuous_spectralPlaneMaximumProduct k a b ha hmono).comp
    (continuous_pi fun i => continuous_affineCompressionSym _ _ _)

theorem matrixTestAllMoments_affineSpectralPlaneTest
    (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).PosSemidef)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j)) :
    MatrixTestAllMoments (affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b) := by
  intro Ω _ μ _ X hXm hX hentries
  apply allFiniteMoments_spectralPlaneMaximumProduct k a b ha hmono
  · exact measurable_pi_lambda fun i =>
      (continuous_affineCompressionSym _ _ _).measurable.comp hXm
  · filter_upwards [hX] with z hz i
    exact affineCompressionSym_posSemidef (hE i) (M i) hz
  · intro i s t
    exact allFiniteMoments_affineCompression_entry (E i) (hE i).isHermitian (M i) X hentries s t

theorem affineCompressionSym_add_congruence {r k : ℕ}
    (E : Matrix (Fin k) (Fin k) ℝ) (hE : E.IsHermitian)
    (M : Matrix (Fin p) (Fin k) ℝ) (B : Sym p)
    (T : Matrix (Fin p) (Fin r) ℝ) (X : Sym r)
    (hE' : (E + Mᵀ * (B : Matrix (Fin p) (Fin p) ℝ) * M).IsHermitian) :
    affineCompressionSym E hE M (B + Matrix.symmetricCongruenceLinearMap T X) =
      affineCompressionSym (E + Mᵀ * (B : Matrix (Fin p) (Fin p) ℝ) * M) hE'
        (Tᵀ * M) X := by
  apply Subtype.ext
  simp only [coe_affineCompressionSym, Submodule.coe_add,
    Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
    add_assoc]

end Wishart.Spectral

namespace Wishart

open WishartVerification Spectral

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem allFiniteMoments_scalarRadialMatrix_entry {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) (s : ℝ) (i j : Fin (1 + r)) :
    HasAllFiniteMoments
      (fun z : ScalarRegressionNoise r =>
        (scalarRadialMatrix s z : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ) i j)
      (scalarRegressionNoiseMeasure N r) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  let L : SymmetricMatrix (1 + r) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap {
    toFun X := (X : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ) i j
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hZ := (hasTemperateGrowth_scalarRadialMatrix r).comp
    (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const s) Function.HasTemperateGrowth.id)
  intro q hq
  exact memLp_temperate_of_allNormMoments (allFiniteNormMoments_scalarRegressionNoise hN)
    (L.hasTemperateGrowth.comp hZ) hq

theorem monotoneOn_scalarRadial_affineSpectralPlaneTest
    {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    (k : κ → ℕ) (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).PosSemidef)
    (M : ∀ i, Matrix (Fin (1 + r)) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j))
    (hsize : ∀ i, min (k i : ℝ) ((1 + r : ℕ) : ℝ) + 1 ≤ N) :
    MonotoneOn (fun t : ℝ => ∫ z : ScalarRegressionNoise r,
      affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b
        (scalarRadialMatrix (Real.sqrt t) z) ∂scalarRegressionNoiseMeasure N r)
      (Set.Ici 0) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  have hradial (s : ℝ) : Measurable (scalarRadialMatrix (r := r) s) :=
    ((hasTemperateGrowth_scalarRadialMatrix r).1.continuous.comp
      (continuous_const.prodMk continuous_id)).measurable
  have hlimit (s : ℝ) := spectralFrameMaximumProduct_integral_tendsto k a b ha hmono
    (fun z : ScalarRegressionNoise r => fun i =>
      affineCompressionSym (E i) (hE i).isHermitian (M i) (scalarRadialMatrix s z))
    (measurable_pi_lambda fun i =>
      (continuous_affineCompressionSym _ _ _).measurable.comp (hradial s))
    (by
      filter_upwards [ae_scalarRadialMatrix_posSemidef N s] with z hz i
      exact affineCompressionSym_posSemidef (hE i) (M i) hz)
    (fun i u v => allFiniteMoments_affineCompression_entry _ _ _ (scalarRadialMatrix s)
      (allFiniteMoments_scalarRadialMatrix_entry hN s) u v)
  intro s hs t ht hst
  exact le_of_tendsto_of_tendsto (hlimit (Real.sqrt s)) (hlimit (Real.sqrt t))
    (Filter.Eventually.of_forall fun n =>
      monotoneOn_scalarRadial_spectralFrameMaximumProduct hN k E hE M a b ha hmono hsize n
        hs ht hst)

theorem scalarRadialTestMonotone_affineSpectralPlaneTest
    {p r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    (k : κ → ℕ) (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).PosSemidef)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j))
    (hsize : ∀ i, min (k i : ℝ) ((1 + r : ℕ) : ℝ) + 1 ≤ N) :
    ScalarRadialTestMonotone N r
      (affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b) := by
  intro B hB L v
  let T := radialLiftMatrix v L
  let E' i := E i + (M i)ᵀ * (B : Matrix (Fin p) (Fin p) ℝ) * M i
  let M' i := Tᵀ * M i
  have hE' : ∀ i, (E' i).PosSemidef := by
    intro i
    apply (hE i).add
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hB.conjTranspose_mul_mul_same (M i)
  have heq (t : ℝ) (z : ScalarRegressionNoise r) :
      affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b
        (B + linearRadialInput L v (Real.sqrt t) z) =
      affineSpectralPlaneTest k E' (fun i => (hE' i).isHermitian) M' a b
        (scalarRadialMatrix (Real.sqrt t) z) := by
    rw [← radialLiftMatrix_scalarRadialMatrix]
    unfold affineSpectralPlaneTest
    congr 1
    funext i
    exact affineCompressionSym_add_congruence _ _ _ B T _ (hE' i).isHermitian
  simpa only [heq] using
    monotoneOn_scalarRadial_affineSpectralPlaneTest hN k E' hE' M' a b ha hmono hsize

/-- The exact finite spectral conditional comparison with the paper's residual
dimension bound. No Gaussian integer-shape restriction or generator premise
remains in the statement. -/
theorem monotoneOn_fullRegressionSpectralAverage_affineSpectralPlaneTest
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    (k : κ → ℕ) (E : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hE : ∀ i, (E i).PosSemidef)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ)
    (a : ∀ i, ι → Fin (k i) → ℝ) (b : κ → ι → ℝ)
    (ha : ∀ i j l, 0 ≤ a i j l) (hmono : ∀ i j, Antitone (a i j))
    (hsize : ∀ i, min (k i : ℝ) ((1 + m : ℕ) : ℝ) + 1 ≤ n - q + 1) :
    MonotoneOn (fullRegressionSpectralAverage n C K
      (affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b))
      (Spectral.positiveChamber q) := by
  have hN : (m : ℝ) < n - q + 1 := by push_cast at hn; linarith
  exact monotoneOn_fullRegressionSpectralAverage_test hn hC K
    (continuous_affineSpectralPlaneTest k E (fun i => (hE i).isHermitian) M a b ha hmono).measurable
    (matrixTestAllMoments_affineSpectralPlaneTest k E hE M a b ha hmono)
    (scalarRadialTestMonotone_affineSpectralPlaneTest hN k E hE M a b ha hmono hsize)

end Wishart
end
end CanonicalSource89
