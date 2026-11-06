module

public import wishart.verified.core02
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import Mathlib.Data.Real.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.MeasureTheory.Measure.WithDensityFinite

/- Generated ordinary proof stage. See audit/staged_core/Core03/manifest.json. -/

@[expose] public section

section CanonicalSource50
/- Source: Wishart/SkewCongruence.lean -/



/-!
# Congruence on the real skew-symmetric subspace

Congruence by an invertible matrix preserves real skew symmetry. The angular
part of the Cayley differential is a nonzero scalar multiple of such a
congruence, and hence is a genuine linear equivalence in every dimension.
-/

open Matrix

namespace Wishart.Spectral

noncomputable def skewCongruenceLinearMap {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) : Skew p →ₗ[ℝ] Skew p where
  toFun H := ⟨B * (H : Matrix (Fin p) (Fin p) ℝ) * Bᵀ, by
    change star (B * (H : Matrix (Fin p) (Fin p) ℝ) * Bᵀ) =
      -(B * (H : Matrix (Fin p) (Fin p) ℝ) * Bᵀ)
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (show (B * (H : Matrix (Fin p) (Fin p) ℝ) * Bᵀ)ᵀ =
        -(B * (H : Matrix (Fin p) (Fin p) ℝ) * Bᵀ) by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, transpose_skew,
            Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc])⟩
  map_add' H K := Subtype.ext (by
    simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul])
  map_smul' a H := Subtype.ext (by
    simp only [Submodule.coe_smul, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul])

@[simp] theorem coe_skewCongruenceLinearMap_apply {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (H : Skew p) :
    (skewCongruenceLinearMap B H : Matrix (Fin p) (Fin p) ℝ) =
      B * (H : Matrix (Fin p) (Fin p) ℝ) * Bᵀ := rfl

theorem skewCongruenceLinearMap_mul {p : ℕ}
    (B C : Matrix (Fin p) (Fin p) ℝ) :
    skewCongruenceLinearMap (B * C) =
      (skewCongruenceLinearMap B).comp (skewCongruenceLinearMap C) := by
  apply LinearMap.ext
  intro H
  apply Subtype.ext
  simp only [coe_skewCongruenceLinearMap_apply, LinearMap.comp_apply,
    Matrix.transpose_mul, Matrix.mul_assoc]

@[simp] theorem skewCongruenceLinearMap_one (p : ℕ) :
    skewCongruenceLinearMap (1 : Matrix (Fin p) (Fin p) ℝ) = LinearMap.id := by
  apply LinearMap.ext
  intro H
  apply Subtype.ext
  simp

noncomputable def skewCongruenceEquiv {p : ℕ}
    (B : Matrix.GeneralLinearGroup (Fin p) ℝ) : Skew p ≃L[ℝ] Skew p :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofLinearMap
      (skewCongruenceLinearMap (B : Matrix (Fin p) (Fin p) ℝ))
      (skewCongruenceLinearMap ((B⁻¹ : Matrix.GeneralLinearGroup (Fin p) ℝ) :
        Matrix (Fin p) (Fin p) ℝ))
      (by rw [← skewCongruenceLinearMap_mul, B.mul_inv, skewCongruenceLinearMap_one])
      (by rw [← skewCongruenceLinearMap_mul, B.inv_mul, skewCongruenceLinearMap_one]))

@[simp] theorem coe_skewCongruenceEquiv_apply {p : ℕ}
    (B : Matrix.GeneralLinearGroup (Fin p) ℝ) (H : Skew p) :
    (skewCongruenceEquiv B H : Matrix (Fin p) (Fin p) ℝ) =
      (B : Matrix (Fin p) (Fin p) ℝ) * (H : Matrix (Fin p) (Fin p) ℝ) *
        (B : Matrix (Fin p) (Fin p) ℝ)ᵀ := rfl

/-- The left factor in the angular differential of the Cayley transform. -/
noncomputable def cayleyAngularBase {p : ℕ} (S : Skew p) :
    Matrix.GeneralLinearGroup (Fin p) ℝ :=
  Matrix.GeneralLinearGroup.mk'' (1 - (S : Matrix (Fin p) (Fin p) ℝ))⁻¹
    (Matrix.isUnit_nonsing_inv_det _
      (isUnit_iff_ne_zero.mpr (det_one_sub_skew_ne_zero (transpose_skew S))))

@[simp] theorem coe_cayleyAngularBase {p : ℕ} (S : Skew p) :
    (cayleyAngularBase S : Matrix (Fin p) (Fin p) ℝ) =
      (1 - (S : Matrix (Fin p) (Fin p) ℝ))⁻¹ := rfl

noncomputable def cayleyAngularEquiv {p : ℕ} (S : Skew p) : Skew p ≃L[ℝ] Skew p :=
  (skewCongruenceEquiv (cayleyAngularBase S)).trans
    ((LinearEquiv.smulOfNeZero ℝ (Skew p) (-2) (by norm_num)).toContinuousLinearEquiv)

@[simp] theorem coe_cayleyAngularEquiv_apply {p : ℕ} (S H : Skew p) :
    (cayleyAngularEquiv S H : Matrix (Fin p) (Fin p) ℝ) =
      (-2 : ℝ) • ((1 - (S : Matrix (Fin p) (Fin p) ℝ))⁻¹ *
        (H : Matrix (Fin p) (Fin p) ℝ) * (1 + (S : Matrix (Fin p) (Fin p) ℝ))⁻¹) := by
  simp only [cayleyAngularEquiv, ContinuousLinearEquiv.trans_apply,
    LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
    Submodule.coe_smul, coe_skewCongruenceEquiv_apply, coe_cayleyAngularBase,
    Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one,
    transpose_skew, sub_neg_eq_add]

/-- Diagonal coordinates remain fixed and angular coordinates are transformed by
the invertible angular differential. -/
noncomputable def spectralAngularEquiv {p : ℕ} (S : Skew p) : Sym p ≃L[ℝ] Sym p :=
  (spectralSplit p).trans
    (((ContinuousLinearEquiv.refl ℝ (Fin p → ℝ)).prodCongr (cayleyAngularEquiv S)).trans
      (spectralSplit p).symm)

end Wishart.Spectral
end CanonicalSource50

section CanonicalSource51
/- Source: Wishart/CayleyDerivative.lean -/



/-!
# The genuine Fréchet derivative of the Cayley chart

The derivative is obtained from matrix inversion on its open domain, and its
left-translated restriction to skew directions is the invertible congruence
constructed in `SkewCongruence`. No differential formula is postulated.
-/

open Matrix Filter
open scoped Topology Matrix.Norms.Operator

namespace Wishart.Spectral

noncomputable def cayleyDerivative {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ →L[ℝ] Matrix (Fin p) (Fin p) ℝ :=
  (-2 : ℝ) • ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin p) (Fin p) ℝ)
    (1 + S)⁻¹ (1 + S)⁻¹

@[simp] theorem cayleyDerivative_apply {p : ℕ}
    (S H : Matrix (Fin p) (Fin p) ℝ) :
    cayleyDerivative S H = (-2 : ℝ) • ((1 + S)⁻¹ * H * (1 + S)⁻¹) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_cayleyMatrix {p : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : IsUnit (1 + S).det) :
    HasFDerivAt cayleyMatrix (cayleyDerivative S) S := by
  have hden : HasFDerivAt (fun B : Matrix (Fin p) (Fin p) ℝ => 1 + B)
      (ContinuousLinearMap.id ℝ _) S := (hasFDerivAt_id S).const_add 1
  have hinv : HasFDerivAt
      (fun B : Matrix (Fin p) (Fin p) ℝ => (1 + B)⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin p) (Fin p) ℝ)
        (1 + S)⁻¹ (1 + S)⁻¹) S := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      (WishartVerification.hasFDerivAt_matrix_inv hS).comp S hden
  have hbase : HasFDerivAt
      (fun B : Matrix (Fin p) (Fin p) ℝ => (2 : ℝ) • (1 + B)⁻¹ - 1)
      (cayleyDerivative S) S := by
    simpa only [cayleyDerivative, Pi.smul_apply, Function.comp_def, ContinuousLinearMap.comp_id,
      smul_neg, neg_smul] using ((hinv.const_smul (2 : ℝ)).sub_const 1)
  apply hbase.congr_of_eventuallyEq
  have hc : Continuous (fun B : Matrix (Fin p) (Fin p) ℝ => (1 + B).det) := by
    fun_prop
  filter_upwards [hc.continuousAt.eventually_ne hS.ne_zero] with B hB
  have heq := one_add_cayleyMatrix_of_isUnit (isUnit_iff_ne_zero.mpr hB)
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using heq)

noncomputable def skewInclusion (p : ℕ) :
    Skew p →L[ℝ] Matrix (Fin p) (Fin p) ℝ :=
  LinearMap.toContinuousLinearMap (skewAdjoint.submodule ℝ
    (Matrix (Fin p) (Fin p) ℝ)).subtype

@[simp] theorem skewInclusion_apply {p : ℕ} (S : Skew p) :
    skewInclusion p S = (S : Matrix (Fin p) (Fin p) ℝ) := rfl

theorem hasFDerivAt_cayley_skew {p : ℕ} (S : Skew p) :
    HasFDerivAt (fun H : Skew p => cayleyMatrix (H : Matrix (Fin p) (Fin p) ℝ))
      ((cayleyDerivative (S : Matrix (Fin p) (Fin p) ℝ)).comp (skewInclusion p)) S := by
  exact (hasFDerivAt_cayleyMatrix
    (isUnit_iff_ne_zero.mpr (det_one_add_skew_ne_zero (transpose_skew S)))).comp S
      (skewInclusion p).hasFDerivAt

/-- Translating a Cayley tangent vector back to the identity gives precisely
the invertible angular differential, with its full matrix meaning. -/
theorem transpose_cayley_mul_derivative {p : ℕ} (S H : Skew p) :
    (cayley S : Matrix (Fin p) (Fin p) ℝ)ᵀ *
        cayleyDerivative (S : Matrix (Fin p) (Fin p) ℝ) H =
      (cayleyAngularEquiv S H : Matrix (Fin p) (Fin p) ℝ) := by
  have hplus : IsUnit (1 + (S : Matrix (Fin p) (Fin p) ℝ)).det :=
    isUnit_iff_ne_zero.mpr (det_one_add_skew_ne_zero (transpose_skew S))
  simp only [cayley, cayleyMatrix, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, transpose_skew,
    sub_neg_eq_add, ← sub_eq_add_neg, cayleyDerivative_apply,
    coe_cayleyAngularEquiv_apply, Matrix.mul_smul]
  congr 1
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hplus]

theorem cayley_derivative_eq_mul_angular {p : ℕ} (S H : Skew p) :
    cayleyDerivative (S : Matrix (Fin p) (Fin p) ℝ) H =
      (cayley S : Matrix (Fin p) (Fin p) ℝ) *
        (cayleyAngularEquiv S H : Matrix (Fin p) (Fin p) ℝ) := by
  rw [← transpose_cayley_mul_derivative, ← Matrix.mul_assoc,
    orth_mul_transpose, Matrix.one_mul]

end Wishart.Spectral
end CanonicalSource51

section CanonicalSource52
/- Source: Wishart/SpectralGap.lean -/



/-!
# The eigenvalue-gap factor of the spectral Jacobian

In upper-triangle coordinates the commutator with a diagonal matrix multiplies
each angular coordinate by the corresponding eigenvalue gap. This calculation
is valid with repeated eigenvalues too; their differential determinant vanishes.
-/

open Matrix TauCeti

namespace Wishart.Spectral

noncomputable def gapProduct {p : ℕ} (lam : Fin p → ℝ) : ℝ :=
  ∏ ij : StrictUpper p, (lam ij.1.2 - lam ij.1.1)

def spectralGap {p : ℕ} (lam : Fin p → ℝ) (c : upperTriangle p) : ℝ :=
  if c.1.1 = c.1.2 then 1 else lam c.1.2 - lam c.1.1

noncomputable def spectralGapCoordinateMap {p : ℕ} (lam : Fin p → ℝ) :
    (upperTriangle p → ℝ) →ₗ[ℝ] (upperTriangle p → ℝ) :=
  LinearMap.pi fun c => (LinearMap.mulLeft ℝ (spectralGap lam c)).comp (LinearMap.proj c)

noncomputable def spectralGapLinearMap {p : ℕ} (lam : Fin p → ℝ) :
    Sym p →ₗ[ℝ] Sym p :=
  ((symmetricCoordinates p).symm : (upperTriangle p → ℝ) →ₗ[ℝ] Sym p).comp
    ((spectralGapCoordinateMap lam).comp
      (symmetricCoordinates p : Sym p →ₗ[ℝ] (upperTriangle p → ℝ)))

@[simp] theorem symmetricCoordinates_spectralGapLinearMap {p : ℕ}
    (lam : Fin p → ℝ) (X : Sym p) (c : upperTriangle p) :
    symmetricCoordinates p (spectralGapLinearMap lam X) c =
      spectralGap lam c * symmetricCoordinates p X c := by
  change symmetricCoordinates p
    ((symmetricCoordinates p).symm (spectralGapCoordinateMap lam (symmetricCoordinates p X))) c = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  simp only [spectralGapCoordinateMap, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.proj_apply]

theorem det_spectralGapLinearMap {p : ℕ} (lam : Fin p → ℝ) :
    LinearMap.det (spectralGapLinearMap lam) = gapProduct lam := by
  have hc : LinearMap.det (spectralGapLinearMap lam) =
      ∏ c : upperTriangle p, spectralGap lam c := by
    have hdet := LinearMap.det_conj (spectralGapCoordinateMap lam)
      (symmetricCoordinates p).toLinearEquiv.symm
    change LinearMap.det (spectralGapLinearMap lam) =
      LinearMap.det (spectralGapCoordinateMap lam) at hdet
    rw [hdet]
    simp only [spectralGapCoordinateMap, LinearMap.det_pi, LinearMap.det_mulLeft]
  rw [hc, ← (diagonalStrictUpperEquiv p).prod_comp]
  simp only [Fintype.prod_sum_type, diagonalStrictUpperEquiv_inl,
    diagonalStrictUpperEquiv_inr, spectralGap, ite_true, Finset.prod_const_one,
    one_mul]
  apply Finset.prod_congr rfl
  intro ij hij
  exact if_neg ij.property.ne

noncomputable def diagonalCommutator {p : ℕ} (lam : Fin p → ℝ) (H : Skew p) : Sym p :=
  ⟨(H : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal lam -
      Matrix.diagonal lam * (H : Matrix (Fin p) (Fin p) ℝ), by
    change star ((H : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal lam -
      Matrix.diagonal lam * (H : Matrix (Fin p) (Fin p) ℝ)) =
      (H : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal lam -
        Matrix.diagonal lam * (H : Matrix (Fin p) (Fin p) ℝ)
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (show ((H : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal lam -
          Matrix.diagonal lam * (H : Matrix (Fin p) (Fin p) ℝ))ᵀ =
          (H : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal lam -
            Matrix.diagonal lam * (H : Matrix (Fin p) (Fin p) ℝ) by
        simp only [Matrix.transpose_sub, Matrix.transpose_mul,
          Matrix.diagonal_transpose, transpose_skew]
        noncomm_ring)⟩

/-- The coordinate multiplier is precisely the symmetric commutator formula,
including the independent diagonal variation. -/
theorem spectralGapLinearMap_eq_diagonal_add_commutator {p : ℕ}
    (lam : Fin p → ℝ) (X : Sym p) :
    spectralGapLinearMap lam X = diagonalSym (spectralSplit p X).1 +
      diagonalCommutator lam (spectralSplit p X).2 := by
  apply (symmetricCoordinates p).injective
  funext c
  rcases c with ⟨⟨i, j⟩, hij⟩
  rw [symmetricCoordinates_spectralGapLinearMap]
  simp only [map_add, symmetricCoordinates_apply, diagonalSym, diagonalCommutator,
    Submodule.coe_add, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  by_cases heq : i = j
  · subst j
    simp only [spectralGap, ite_true, Matrix.diagonal_apply_eq, spectralSplit_fst,
      one_mul]
    ring
  · have hlt : i < j := lt_of_le_of_ne hij heq
    have he := spectralSplit_snd_entry X (⟨(i, j), hlt⟩ : StrictUpper p)
    simp only at he
    rw [he]
    simp only [spectralGap, heq, ite_false, Matrix.diagonal_apply_ne _ heq, zero_add]
    ring

theorem gapProduct_pos {p : ℕ} {lam : Fin p → ℝ} (hlam : StrictMono lam) :
    0 < gapProduct lam := by
  apply Finset.prod_pos
  intro ij hij
  exact sub_pos.mpr (hlam ij.property)

theorem gapProduct_eq_zero_of_not_injective {p : ℕ} {lam : Fin p → ℝ}
    (hlam : ¬Function.Injective lam) : gapProduct lam = 0 := by
  classical
  obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hlam
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply Finset.prod_eq_zero (Finset.mem_univ (⟨(i, j), hlt⟩ : StrictUpper p))
    exact sub_eq_zero.mpr heq.symm
  · apply Finset.prod_eq_zero (Finset.mem_univ (⟨(j, i), hgt⟩ : StrictUpper p))
    exact sub_eq_zero.mpr heq

noncomputable def angularJacobian {p : ℕ} (S : Skew p) : ℝ :=
  |LinearMap.det (spectralAngularEquiv S : Sym p →ₗ[ℝ] Sym p)|

theorem angularJacobian_pos {p : ℕ} (S : Skew p) : 0 < angularJacobian S := by
  exact abs_pos.mpr (spectralAngularEquiv S).toLinearEquiv.isUnit_det'.ne_zero

end Wishart.Spectral
end CanonicalSource52

section CanonicalSource53
/- Source: Wishart/SpectralDerivative.lean -/



/-!
# Differential and determinant of the spectral chart

The map is differentiated as an actual matrix-valued function. Its derivative
factors into orthogonal congruence, eigenvalue gaps and an invertible angular
map. The factorization remains valid at repeated spectra.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace Wishart.Spectral

noncomputable def symmetricInclusion (p : ℕ) :
    Sym p →L[ℝ] Matrix (Fin p) (Fin p) ℝ :=
  LinearMap.toContinuousLinearMap
    (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)).subtype

noncomputable def spectralDiagonalProjection (p : ℕ) : Sym p →L[ℝ] (Fin p → ℝ) :=
  (ContinuousLinearMap.fst ℝ (Fin p → ℝ) (Skew p)).comp
    (spectralSplit p).toContinuousLinearMap

noncomputable def spectralSkewProjection (p : ℕ) : Sym p →L[ℝ] Skew p :=
  (ContinuousLinearMap.snd ℝ (Fin p → ℝ) (Skew p)).comp
    (spectralSplit p).toContinuousLinearMap

noncomputable def diagonalMatrixCLM (p : ℕ) :
    (Fin p → ℝ) →L[ℝ] Matrix (Fin p) (Fin p) ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin p) ℝ ℝ)

noncomputable def transposeMatrixCLM (p : ℕ) :
    Matrix (Fin p) (Fin p) ℝ →L[ℝ] Matrix (Fin p) (Fin p) ℝ :=
  (Matrix.transposeLinearEquiv (Fin p) (Fin p) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def matrixMulLeft {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ →L[ℝ] Matrix (Fin p) (Fin p) ℝ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ A)

noncomputable def matrixMulRight {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ →L[ℝ] Matrix (Fin p) (Fin p) ℝ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ A)

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_matrix_mul {p : ℕ}
    {f g : Sym p → Matrix (Fin p) (Fin p) ℝ}
    {f' g' : Sym p →L[ℝ] Matrix (Fin p) (Fin p) ℝ} {X : Sym p}
    (hf : HasFDerivAt f f' X) (hg : HasFDerivAt g g' X) :
    HasFDerivAt (fun Y => f Y * g Y)
      ((matrixMulLeft (f X)).comp g' + (matrixMulRight (g X)).comp f') X := by
  have hm : HasFDerivAt (fun Y => f Y * g Y)
      (f X • g' + MulOpposite.op (g X) • f') X := hf.mul' hg
  have heq : f X • g' + MulOpposite.op (g X) • f' =
      (matrixMulLeft (f X)).comp g' + (matrixMulRight (g X)).comp f' := by
    ext H
    simp only [matrixMulLeft, matrixMulRight, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
  rw [heq] at hm
  exact hm

noncomputable def spectralDerivative {p : ℕ} (S : Skew p) (lam : Fin p → ℝ) :
    Sym p →L[ℝ] Sym p :=
  (LinearMap.toContinuousLinearMap
    (Matrix.symmetricCongruenceLinearMap (cayley S : Matrix (Fin p) (Fin p) ℝ))).comp
      ((LinearMap.toContinuousLinearMap (spectralGapLinearMap lam)).comp
        (spectralAngularEquiv S).toContinuousLinearMap)

theorem coe_spectralDerivative_apply {p : ℕ}
    (S : Skew p) (lam : Fin p → ℝ) (H : Sym p) :
    (spectralDerivative S lam H : Matrix (Fin p) (Fin p) ℝ) =
      (cayley S : Matrix (Fin p) (Fin p) ℝ) *
        (Matrix.diagonal (spectralSplit p H).1 +
          (cayleyAngularEquiv S (spectralSplit p H).2 : Matrix (Fin p) (Fin p) ℝ) *
            Matrix.diagonal lam -
          Matrix.diagonal lam *
            (cayleyAngularEquiv S (spectralSplit p H).2 : Matrix (Fin p) (Fin p) ℝ)) *
        (cayley S : Matrix (Fin p) (Fin p) ℝ)ᵀ := by
  simp only [spectralDerivative, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', Matrix.coe_symmetricCongruenceLinearMap_apply,
    spectralGapLinearMap_eq_diagonal_add_commutator, spectralAngularEquiv,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply,
    Submodule.coe_add, diagonalSym, diagonalCommutator]
  congr 2
  abel

/-- Fréchet differentiation of the actual spectral chart, with no assumption
that its eigenvalue parameters are distinct or positive. -/
theorem hasFDerivAt_spectralChart {p : ℕ} (X : Sym p) :
    HasFDerivAt spectralChart
      (spectralDerivative (spectralSplit p X).2 (spectralSplit p X).1) X := by
  let Q : Sym p → Matrix (Fin p) (Fin p) ℝ :=
    fun Y => cayleyMatrix (spectralSkewProjection p Y : Matrix (Fin p) (Fin p) ℝ)
  let D : Sym p → Matrix (Fin p) (Fin p) ℝ :=
    fun Y => diagonalMatrixCLM p (spectralDiagonalProjection p Y)
  let Q' : Sym p →L[ℝ] Matrix (Fin p) (Fin p) ℝ :=
    ((cayleyDerivative ((spectralSplit p X).2 : Matrix (Fin p) (Fin p) ℝ)).comp
      (skewInclusion p)).comp (spectralSkewProjection p)
  let D' : Sym p →L[ℝ] Matrix (Fin p) (Fin p) ℝ :=
    (diagonalMatrixCLM p).comp (spectralDiagonalProjection p)
  have hQ : HasFDerivAt Q Q' X :=
    (hasFDerivAt_cayley_skew (spectralSkewProjection p X)).comp X
      (spectralSkewProjection p).hasFDerivAt
  have hD : HasFDerivAt D D' X := D'.hasFDerivAt
  have hQT := (transposeMatrixCLM p).hasFDerivAt.comp X hQ
  have hraw := hasFDerivAt_matrix_mul (hasFDerivAt_matrix_mul hQ hD) hQT
  have hambient : HasFDerivAt
      (fun Y : Sym p => (spectralChart Y : Matrix (Fin p) (Fin p) ℝ))
      ((symmetricInclusion p).comp
        (spectralDerivative (spectralSplit p X).2 (spectralSplit p X).1)) X := by
    convert hraw using 1
    · funext Y
      simp only [spectralChart, conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply,
        diagonalSym, Q, D, Function.comp_def]
      rfl
    · apply ContinuousLinearMap.ext
      intro H
      change (spectralDerivative (spectralSplit p X).2 (spectralSplit p X).1 H :
          Matrix (Fin p) (Fin p) ℝ) =
        Q X * D X * (Q' H)ᵀ + (Q X * D' H + Q' H * D X) * (Q X)ᵀ
      rw [coe_spectralDerivative_apply]
      have hder : Q' H = (cayley (spectralSplit p X).2 : Matrix (Fin p) (Fin p) ℝ) *
          (cayleyAngularEquiv (spectralSplit p X).2 (spectralSplit p H).2 :
            Matrix (Fin p) (Fin p) ℝ) := by
        exact cayley_derivative_eq_mul_angular _ _
      rw [hder, Matrix.transpose_mul, transpose_skew]
      change _ = (cayley (spectralSplit p X).2 : Matrix (Fin p) (Fin p) ℝ) *
          Matrix.diagonal (spectralSplit p X).1 *
          (-(cayleyAngularEquiv (spectralSplit p X).2 (spectralSplit p H).2 :
            Matrix (Fin p) (Fin p) ℝ) *
              (cayley (spectralSplit p X).2 : Matrix (Fin p) (Fin p) ℝ)ᵀ) +
        ((cayley (spectralSplit p X).2 : Matrix (Fin p) (Fin p) ℝ) *
            Matrix.diagonal (spectralSplit p H).1 +
          (cayley (spectralSplit p X).2 : Matrix (Fin p) (Fin p) ℝ) *
            (cayleyAngularEquiv (spectralSplit p X).2 (spectralSplit p H).2 :
              Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal (spectralSplit p X).1) *
            (cayley (spectralSplit p X).2 : Matrix (Fin p) (Fin p) ℝ)ᵀ
      noncomm_ring
  exact HasFDerivAt.of_comp_of_isEmbedding
    (continuous_spectralChart p).continuousAt (symmetricInclusion p).hasFDerivAt
    (show Topology.IsEmbedding (symmetricInclusion p) from Topology.IsEmbedding.subtypeVal)
    hambient (Filter.Eventually.of_forall fun _ => rfl)

theorem abs_det_orthogonal {p : ℕ} (O : Orth p) :
    |(O : Matrix (Fin p) (Fin p) ℝ).det| = 1 := by
  exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary O.property)

/-- Exact factorization of the absolute Jacobian. -/
theorem abs_det_spectralDerivative {p : ℕ} (S : Skew p) (lam : Fin p → ℝ) :
    |(spectralDerivative S lam).det| = angularJacobian S * |gapProduct lam| := by
  change |LinearMap.det (Matrix.symmetricCongruenceLinearMap
    (cayley S : Matrix (Fin p) (Fin p) ℝ) ∘ₗ
      (spectralGapLinearMap lam ∘ₗ
        (spectralAngularEquiv S : Sym p →ₗ[ℝ] Sym p)))| = _
  rw [LinearMap.det_comp, LinearMap.det_comp, Matrix.det_symmetricCongruenceLinearMap,
    det_spectralGapLinearMap, abs_mul, abs_mul, abs_pow, abs_det_orthogonal,
    one_pow, one_mul]
  exact mul_comm _ _

end Wishart.Spectral
end CanonicalSource53

section CanonicalSource54
/- Source: Wishart/Vandermonde.lean -/



open scoped Classical

/-!
# Lattice positivity of the ordered Vandermonde density

The algebraic MTP₂ property behind Lemma 2.1. All statements here allow arbitrary
finite dimension and arbitrary nonnegative real Vandermonde exponent. The
finite-grid theorem is an intermediate result, not the continuous association
claim of that lemma.
-/

namespace WishartVerification

/-- The nonnegative difference kernel is log-supermodular in its two arguments. -/
theorem positive_difference_lattice (a b c d : ℝ) :
    max (b - a) 0 * max (d - c) 0 ≤
      max (min b d - min a c) 0 * max (max b d - max a c) 0 := by
  rcases le_total a c with hac | hca
  · rcases le_total b d with hbd | hdb
    · simp [min_eq_left hac, max_eq_right hac, min_eq_left hbd, max_eq_right hbd]
    · simp only [min_eq_left hac, max_eq_right hac, min_eq_right hdb, max_eq_left hdb]
      by_cases hdc : d ≤ c
      · rw [max_eq_right (sub_nonpos.mpr hdc), mul_zero]
        positivity
      · have hcd : c ≤ d := (lt_of_not_ge hdc).le
        rw [max_eq_left (sub_nonneg.mpr (hac.trans (hcd.trans hdb))),
          max_eq_left (sub_nonneg.mpr hcd),
          max_eq_left (sub_nonneg.mpr (hac.trans hcd)),
          max_eq_left (sub_nonneg.mpr (hcd.trans hdb))]
        nlinarith [mul_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hdb)]
  · rcases le_total b d with hbd | hdb
    · simp only [min_eq_right hca, max_eq_left hca, min_eq_left hbd, max_eq_right hbd]
      by_cases hba : b ≤ a
      · rw [max_eq_right (sub_nonpos.mpr hba), zero_mul]
        positivity
      · have hab : a ≤ b := (lt_of_not_ge hba).le
        rw [max_eq_left (sub_nonneg.mpr hab),
          max_eq_left (sub_nonneg.mpr (hca.trans (hab.trans hbd))),
          max_eq_left (sub_nonneg.mpr (hca.trans hab)),
          max_eq_left (sub_nonneg.mpr (hab.trans hbd))]
        nlinarith [mul_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hbd)]
    · simp [min_eq_right hca, max_eq_left hca, min_eq_right hdb, max_eq_left hdb,
        mul_comm]

/-- Every nonnegative real power preserves the lattice inequality. -/
theorem positive_difference_rpow_lattice (a b c d β : ℝ) (hβ : 0 ≤ β) :
    (max (b - a) 0) ^ β * (max (d - c) 0) ^ β ≤
      (max (min b d - min a c) 0) ^ β *
        (max (max b d - max a c) 0) ^ β := by
  rw [← Real.mul_rpow (by positivity) (by positivity),
    ← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (by positivity) (positive_difference_lattice a b c d) hβ

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The Vandermonde product extended by zero off the ordered chamber. For positive
`β`, every non-increasing coordinate pair makes this product vanish. -/
noncomputable def orderedVandermonde (β : ℝ) (x : ι → ℝ) : ℝ :=
  ∏ i, ∏ j, if i < j then (max (x j - x i) 0) ^ β else 1

theorem orderedVandermonde_nonneg (β : ℝ) (x : ι → ℝ) :
    0 ≤ orderedVandermonde β x := by
  apply Finset.prod_nonneg
  intro i hi
  apply Finset.prod_nonneg
  intro j hj
  split_ifs <;> positivity

/-- On the strict ordered chamber the extension is the ordinary Vandermonde
power, with no absolute values or reordered eigenvalues. -/
theorem orderedVandermonde_eq_on_chamber (β : ℝ) (x : ι → ℝ)
    (hx : StrictMono x) :
    orderedVandermonde β x = ∏ i, ∏ j, if i < j then (x j - x i) ^ β else 1 := by
  unfold orderedVandermonde
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp [hij, max_eq_left (sub_nonneg.mpr (hx hij).le)]
  · simp [hij]

/-- Any non-increasing coordinate pair makes the positive-exponent density zero. -/
theorem orderedVandermonde_eq_zero_of_pair (β : ℝ) (hβ : 0 < β)
    (x : ι → ℝ) {i j : ι} (hij : i < j) (hji : x j ≤ x i) :
    orderedVandermonde β x = 0 := by
  classical
  unfold orderedVandermonde
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hij, max_eq_right (sub_nonpos.mpr hji), Real.zero_rpow hβ.ne']

theorem orderedVandermonde_eq_zero_off_chamber (β : ℝ) (hβ : 0 < β)
    (x : ι → ℝ) (hx : ¬StrictMono x) : orderedVandermonde β x = 0 := by
  by_contra hne
  apply hx
  intro i j hij
  by_contra hlt
  exact hne (orderedVandermonde_eq_zero_of_pair β hβ x hij (not_lt.mp hlt))

theorem orderedVandermonde_lattice (β : ℝ) (hβ : 0 ≤ β) (x y : ι → ℝ) :
    orderedVandermonde β x * orderedVandermonde β y ≤
      orderedVandermonde β (x ⊓ y) * orderedVandermonde β (x ⊔ y) := by
  simp only [orderedVandermonde, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro i hi
    positivity
  · intro i hi
    apply Finset.prod_le_prod₀
    · intro j hj
      positivity
    · intro j hj
      by_cases hij : i < j
      · simpa only [hij, ite_true, Pi.inf_apply, Pi.sup_apply] using
          positive_difference_rpow_lattice (x i) (x j) (y i) (y j) β hβ
      · simp [hij]

/-- A product of separate one-coordinate weights is exactly lattice modular. -/
theorem product_weights_lattice (w : ι → ℝ → ℝ) (x y : ι → ℝ) :
    (∏ i, w i (x i)) * (∏ i, w i (y i)) =
      (∏ i, w i ((x ⊓ y) i)) * (∏ i, w i ((x ⊔ y) i)) := by
  simp only [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Pi.inf_apply, Pi.sup_apply]
  rcases le_total (x i) (y i) with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h, mul_comm]

/-- Unnormalized density with arbitrary nonnegative coordinate weights. Interval
cutoffs can be included in these weights, so no rectangular support is lost. -/
noncomputable def vandermondeWeight (w : ι → ℝ → ℝ) (β : ℝ) (x : ι → ℝ) : ℝ :=
  (∏ i, w i (x i)) * orderedVandermonde β x

/-- Exact correspondence with the density formula in Lemma 2.1. Coordinate
weights may already contain the open-interval indicators. -/
theorem vandermondeWeight_eq_chamber_density (w : ι → ℝ → ℝ) (β : ℝ)
    (hβ : 0 < β) (x : ι → ℝ) :
    vandermondeWeight w β x =
      if StrictMono x then (∏ i, w i (x i)) *
        (∏ i, ∏ j, if i < j then (x j - x i) ^ β else 1) else 0 := by
  classical
  by_cases hx : StrictMono x
  · simp [vandermondeWeight, hx, orderedVandermonde_eq_on_chamber β x hx]
  · simp [vandermondeWeight, hx, orderedVandermonde_eq_zero_off_chamber β hβ x hx]

theorem vandermondeWeight_nonneg (w : ι → ℝ → ℝ) (β : ℝ)
    (hw : ∀ i t, 0 ≤ w i t) (x : ι → ℝ) :
    0 ≤ vandermondeWeight w β x :=
  mul_nonneg (Finset.prod_nonneg (fun i _ ↦ hw i (x i)))
    (orderedVandermonde_nonneg β x)

/-- The complete Vandermonde density satisfies the FKG lattice condition. -/
theorem vandermondeWeight_lattice (w : ι → ℝ → ℝ) (β : ℝ)
    (hw : ∀ i t, 0 ≤ w i t) (hβ : 0 ≤ β) (x y : ι → ℝ) :
    vandermondeWeight w β x * vandermondeWeight w β y ≤
      vandermondeWeight w β (x ⊓ y) * vandermondeWeight w β (x ⊔ y) := by
  unfold vandermondeWeight
  calc
    _ = ((∏ i, w i (x i)) * (∏ i, w i (y i))) *
        (orderedVandermonde β x * orderedVandermonde β y) := by ring
    _ ≤ ((∏ i, w i (x i)) * (∏ i, w i (y i))) *
        (orderedVandermonde β (x ⊓ y) * orderedVandermonde β (x ⊔ y)) :=
      mul_le_mul_of_nonneg_left (orderedVandermonde_lattice β hβ x y)
        (mul_nonneg (Finset.prod_nonneg (fun i _ ↦ hw i _))
          (Finset.prod_nonneg (fun i _ ↦ hw i _)))
    _ = _ := by rw [product_weights_lattice w x y]; ring

end WishartVerification
end CanonicalSource54

section CanonicalSource55
/- Source: Wishart/FiniteGridFKG.lean -/



open scoped Classical

/-!
# FKG on arbitrary sampled Cartesian grids

The samples may repeat and need not arrive in increasing order. Sorting is used
only inside the proof; all conclusions use the original, unsorted samples, so
their measurability does not depend on the sorting construction.
-/

namespace WishartVerification

variable {ι : Type*} [Fintype ι]

/-- Coordinate monotonicity is only required where the density is positive.
This avoids extending functions outside an ordered chamber. -/
def SupportedMonotone (w f : (ι → ℝ) → ℝ) : Prop :=
  ∀ x y, 0 < w x → 0 < w y → x ≤ y → f x ≤ f y

theorem supportedMonotone_of_monotone (w f : (ι → ℝ) → ℝ) (hf : Monotone f) :
    SupportedMonotone w f := fun _ _ _ _ hxy ↦ hf hxy

def sampledPoint {N : ℕ} (samples : ι → Fin N → ℝ) (a : ι → Fin N) : ι → ℝ :=
  fun i ↦ samples i (a i)

/-- Coordinatewise increasing sample arrays preserve meets. -/
theorem sampledPoint_inf {N : ℕ} (samples : ι → Fin N → ℝ)
    (hs : ∀ i, Monotone (samples i)) (a b : ι → Fin N) :
    sampledPoint samples (a ⊓ b) = sampledPoint samples a ⊓ sampledPoint samples b := by
  funext i
  simp only [sampledPoint, Pi.inf_apply]
  rcases le_total (a i) (b i) with h | h
  · simp [min_eq_left h, min_eq_left (hs i h)]
  · simp [min_eq_right h, min_eq_right (hs i h)]

/-- Coordinatewise increasing sample arrays preserve joins. -/
theorem sampledPoint_sup {N : ℕ} (samples : ι → Fin N → ℝ)
    (hs : ∀ i, Monotone (samples i)) (a b : ι → Fin N) :
    sampledPoint samples (a ⊔ b) = sampledPoint samples a ⊔ sampledPoint samples b := by
  funext i
  simp only [sampledPoint, Pi.sup_apply]
  rcases le_total (a i) (b i) with h | h
  · simp [max_eq_right h, max_eq_right (hs i h)]
  · simp [max_eq_left h, max_eq_left (hs i h)]

/-- FKG for a sorted finite sample array, before removing the sorting. -/
theorem finite_grid_fkg_sorted {N : ℕ} (samples : ι → Fin N → ℝ)
    (hs : ∀ i, Monotone (samples i))
    (w f g : (ι → ℝ) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfm : Monotone f) (hgm : Monotone g)
    (hwl : ∀ x y, w x * w y ≤ w (x ⊓ y) * w (x ⊔ y)) :
    (∑ a, w (sampledPoint samples a) * f (sampledPoint samples a)) *
        (∑ a, w (sampledPoint samples a) * g (sampledPoint samples a)) ≤
      (∑ a, w (sampledPoint samples a)) *
        ∑ a, w (sampledPoint samples a) *
          (f (sampledPoint samples a) * g (sampledPoint samples a)) := by
  have hsm : Monotone (sampledPoint samples) := by
    intro a b hab i
    exact hs i (hab i)
  apply fkg (fun a ↦ f (sampledPoint samples a)) (fun a ↦ g (sampledPoint samples a))
    (fun a ↦ w (sampledPoint samples a))
    (fun a ↦ hw _) (fun a ↦ hf _) (fun a ↦ hg _) (hfm.comp hsm) (hgm.comp hsm)
  intro a b
  simpa only [Function.comp_apply, sampledPoint_inf samples hs,
    sampledPoint_sup samples hs] using hwl (sampledPoint samples a) (sampledPoint samples b)

/-- FKG holds on every sampled Cartesian grid, including repeated samples.
No asymptotic or probabilistic conclusion is assumed in this theorem. -/
theorem finite_grid_fkg {N : ℕ} (samples : ι → Fin N → ℝ)
    (w f g : (ι → ℝ) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfm : Monotone f) (hgm : Monotone g)
    (hwl : ∀ x y, w x * w y ≤ w (x ⊓ y) * w (x ⊔ y)) :
    (∑ a, w (sampledPoint samples a) * f (sampledPoint samples a)) *
        (∑ a, w (sampledPoint samples a) * g (sampledPoint samples a)) ≤
      (∑ a, w (sampledPoint samples a)) *
        ∑ a, w (sampledPoint samples a) *
          (f (sampledPoint samples a) * g (sampledPoint samples a)) := by
  classical
  let σ : (ι → Fin N) ≃ (ι → Fin N) := Equiv.piCongrRight fun i ↦ Tuple.sort (samples i)
  let sorted : ι → Fin N → ℝ := fun i ↦ samples i ∘ Tuple.sort (samples i)
  have hsorted : ∀ i, Monotone (sorted i) := fun i ↦ Tuple.monotone_sort (samples i)
  have hpoint : ∀ a, sampledPoint sorted a = sampledPoint samples (σ a) := by
    intro a
    rfl
  have hsum (h : (ι → ℝ) → ℝ) :
      (∑ a, h (sampledPoint sorted a)) = ∑ a, h (sampledPoint samples a) := by
    simp_rw [hpoint]
    exact Equiv.sum_comp σ (fun a ↦ h (sampledPoint samples a))
  have h := finite_grid_fkg_sorted sorted hsorted w f g hw hf hg hfm hgm hwl
  rw [hsum (fun x ↦ w x * f x), hsum (fun x ↦ w x * g x), hsum w,
    hsum (fun x ↦ w x * (f x * g x))] at h
  exact h

/-- The four-functions theorem on every sampled Cartesian grid. -/
theorem finite_grid_four_functions {N : ℕ} (samples : ι → Fin N → ℝ)
    (A B C D : (ι → ℝ) → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x)
    (hC : ∀ x, 0 ≤ C x) (hD : ∀ x, 0 ≤ D x)
    (hcross : ∀ x y, A x * B y ≤ C (x ⊓ y) * D (x ⊔ y)) :
    (∑ a, A (sampledPoint samples a)) * (∑ a, B (sampledPoint samples a)) ≤
      (∑ a, C (sampledPoint samples a)) * ∑ a, D (sampledPoint samples a) := by
  classical
  let σ : (ι → Fin N) ≃ (ι → Fin N) := Equiv.piCongrRight fun i ↦ Tuple.sort (samples i)
  let sorted : ι → Fin N → ℝ := fun i ↦ samples i ∘ Tuple.sort (samples i)
  have hs : ∀ i, Monotone (sorted i) := fun i ↦ Tuple.monotone_sort (samples i)
  have hpoint : ∀ a, sampledPoint sorted a = sampledPoint samples (σ a) := fun _ ↦ rfl
  have hsum (h : (ι → ℝ) → ℝ) :
      (∑ a, h (sampledPoint sorted a)) = ∑ a, h (sampledPoint samples a) := by
    simp_rw [hpoint]
    exact Equiv.sum_comp σ (fun a ↦ h (sampledPoint samples a))
  have h := four_functions_theorem_univ
    (fun a ↦ A (sampledPoint sorted a)) (fun a ↦ B (sampledPoint sorted a))
    (fun a ↦ C (sampledPoint sorted a)) (fun a ↦ D (sampledPoint sorted a))
    (fun a ↦ hA _) (fun a ↦ hB _) (fun a ↦ hC _) (fun a ↦ hD _)
    (fun a b ↦ by
      simpa only [sampledPoint_inf sorted hs, sampledPoint_sup sorted hs] using
        hcross (sampledPoint sorted a) (sampledPoint sorted b))
  rw [hsum A, hsum B, hsum C, hsum D] at h
  exact h

/-- FKG only needs monotonicity on the positive support of its density. -/
theorem finite_grid_fkg_on {N : ℕ} (samples : ι → Fin N → ℝ)
    (w f g : (ι → ℝ) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfm : SupportedMonotone w f) (hgm : SupportedMonotone w g)
    (hwl : ∀ x y, w x * w y ≤ w (x ⊓ y) * w (x ⊔ y)) :
    (∑ a, w (sampledPoint samples a) * f (sampledPoint samples a)) *
        (∑ a, w (sampledPoint samples a) * g (sampledPoint samples a)) ≤
      (∑ a, w (sampledPoint samples a)) *
        ∑ a, w (sampledPoint samples a) *
          (f (sampledPoint samples a) * g (sampledPoint samples a)) := by
  apply finite_grid_four_functions samples (fun x ↦ w x * f x)
    (fun x ↦ w x * g x) w (fun x ↦ w x * (f x * g x))
    (fun x ↦ mul_nonneg (hw x) (hf x)) (fun x ↦ mul_nonneg (hw x) (hg x)) hw
    (fun x ↦ mul_nonneg (hw x) (mul_nonneg (hf x) (hg x)))
  intro x y
  by_cases hx : w x = 0
  · simp only [hx, zero_mul]
    exact mul_nonneg (hw _) (mul_nonneg (hw _) (mul_nonneg (hf _) (hg _)))
  by_cases hy : w y = 0
  · simp only [hy, zero_mul, mul_zero]
    exact mul_nonneg (hw _) (mul_nonneg (hw _) (mul_nonneg (hf _) (hg _)))
  have hxpos : 0 < w x := lt_of_le_of_ne (hw x) (Ne.symm hx)
  have hypos : 0 < w y := lt_of_le_of_ne (hw y) (Ne.symm hy)
  have hsup : 0 < w (x ⊔ y) := by
    have hp : 0 < w (x ⊓ y) * w (x ⊔ y) := (mul_pos hxpos hypos).trans_le (hwl x y)
    exact pos_of_mul_pos_right hp (hw _)
  calc
    (w x * f x) * (w y * g y) = (w x * w y) * (f x * g y) := by ring
    _ ≤ (w (x ⊓ y) * w (x ⊔ y)) * (f (x ⊔ y) * g (x ⊔ y)) :=
      mul_le_mul (hwl x y)
        (mul_le_mul (hfm x _ hxpos hsup le_sup_left) (hgm y _ hypos hsup le_sup_right)
          (hg y) (hf _)) (mul_nonneg (hf x) (hg y)) (mul_nonneg (hw _) (hw _))
    _ = w (x ⊓ y) * (w (x ⊔ y) * (f (x ⊔ y) * g (x ⊔ y))) := by ring

end WishartVerification
end CanonicalSource55

section CanonicalSource56
/- Source: Wishart/RandomGridLaws.lean -/



open scoped Classical

/-!
# Distributional facts for random Cartesian grids

All coordinate samples are independent. A selected Cartesian grid point has the
original product law. Two selected points are independent whenever the sample
indices differ in every coordinate. These facts are the distributional part of
the finite-grid proof of continuous FKG.
-/

open MeasureTheory ProbabilityTheory

namespace WishartVerification

variable {ι : Type*} [Fintype ι]

/-- The law of `N` independent samples in each coordinate. -/
noncomputable def gridSampleLaw (μ : ι → Measure ℝ) (N : ℕ) :
    Measure (ι × Fin N → ℝ) := Measure.pi (fun z ↦ μ z.1)

/-- A Cartesian grid point chosen by one sample index in every coordinate. -/
def gridPoint {N : ℕ} (a : ι → Fin N) (ω : ι × Fin N → ℝ) : ι → ℝ :=
  fun i ↦ ω (i, a i)

theorem gridPoint_measurable {N : ℕ} (a : ι → Fin N) : Measurable (gridPoint a) := by
  exact Measurable.of_eval fun i ↦ measurable_pi_apply (i, a i)

instance gridSampleLaw_probability (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (N : ℕ) :
    IsProbabilityMeasure (gridSampleLaw μ N) := by
  unfold gridSampleLaw
  infer_instance

variable (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]

/-- The complete sample array has independent coordinates. -/
theorem grid_coordinates_independent (N : ℕ) :
    iIndepFun (fun z : ι × Fin N ↦ fun ω : ι × Fin N → ℝ ↦ ω z)
      (gridSampleLaw μ N) := by
  exact iIndepFun_pi (fun _ ↦ aemeasurable_id)

/-- Selecting one sample in each coordinate preserves the original product law. -/
theorem gridPoint_measurePreserving {N : ℕ} (a : ι → Fin N) :
    MeasurePreserving (gridPoint a) (gridSampleLaw μ N) (Measure.pi μ) := by
  refine ⟨gridPoint_measurable a, ?_⟩
  have hinj : Function.Injective (fun i : ι ↦ (i, a i)) := by
    intro i j h
    exact congrArg Prod.fst h
  have hind : iIndepFun (fun i : ι ↦ fun ω : ι × Fin N → ℝ ↦ ω (i, a i))
      (gridSampleLaw μ N) :=
    iIndepFun.precomp hinj (grid_coordinates_independent μ N)
  have hmap := hind.map_fun_eq_pi_map
    (fun i ↦ (measurable_pi_apply (i, a i)).aemeasurable)
  change (gridSampleLaw μ N).map (fun ω i ↦ ω (i, a i)) = Measure.pi μ
  rw [hmap]
  congr 1
  funext i
  exact (measurePreserving_eval (fun z : ι × Fin N ↦ μ z.1) (i, a i)).map_eq

/-- Integrating a measurable test of one selected point gives its original
product-law expectation. -/
theorem integral_gridPoint {N : ℕ} (a : ι → Fin N)
    (h : (ι → ℝ) → ℝ) (hh : Measurable h) :
    (∫ ω, h (gridPoint a ω) ∂gridSampleLaw μ N) = ∫ x, h x ∂Measure.pi μ := by
  rw [← (gridPoint_measurePreserving μ a).map_eq]
  exact (integral_map (gridPoint_measurable a).aemeasurable hh.aestronglyMeasurable).symm

/-- Disjoint sample-index selections produce independent random vectors. -/
theorem gridPoint_independent {N : ℕ} (a b : ι → Fin N)
    (hab : ∀ i, a i ≠ b i) :
    IndepFun (gridPoint a) (gridPoint b) (gridSampleLaw μ N) := by
  let S : Set (ι × Fin N) := Set.range fun i ↦ (i, a i)
  let T : Set (ι × Fin N) := Set.range fun i ↦ (i, b i)
  have hST : Disjoint S T := by
    rw [Set.disjoint_left]
    rintro z ⟨i, rfl⟩ ⟨j, hj⟩
    have hji : j = i := congrArg Prod.fst hj
    subst j
    exact hab i (congrArg Prod.snd hj).symm
  have hind := (grid_coordinates_independent μ N).indepFun_set S T hST
    (fun z ↦ measurable_pi_apply z)
  let fromS : (S → ℝ) → (ι → ℝ) := fun v i ↦ v ⟨(i, a i), ⟨i, rfl⟩⟩
  let fromT : (T → ℝ) → (ι → ℝ) := fun v i ↦ v ⟨(i, b i), ⟨i, rfl⟩⟩
  have hS : Measurable fromS := by
    exact Measurable.of_eval fun i ↦ measurable_pi_apply (⟨(i, a i), ⟨i, rfl⟩⟩ : S)
  have hT : Measurable fromT := by
    exact Measurable.of_eval fun i ↦ measurable_pi_apply (⟨(i, b i), ⟨i, rfl⟩⟩ : T)
  exact hind.comp hS hT

/-- The contribution of a collision-free pair of grid points factors exactly. -/
theorem integral_gridPoint_mul {N : ℕ} (a b : ι → Fin N)
    (hab : ∀ i, a i ≠ b i)
    (h k : (ι → ℝ) → ℝ) (hh : Measurable h) (hk : Measurable k) :
    (∫ ω, h (gridPoint a ω) * k (gridPoint b ω) ∂gridSampleLaw μ N) =
      (∫ x, h x ∂Measure.pi μ) * (∫ x, k x ∂Measure.pi μ) := by
  have hind := (gridPoint_independent μ a b hab).comp hh hk
  have heq := hind.integral_fun_mul_eq_mul_integral
    (hh.comp (gridPoint_measurable a)).aestronglyMeasurable
    (hk.comp (gridPoint_measurable b)).aestronglyMeasurable
  simp only [Function.comp_apply] at heq
  rw [heq]
  rw [integral_gridPoint μ a h hh, integral_gridPoint μ b k hk]

/-- Bounded measurable functions on a probability space are integrable. This
convenient specialization keeps the later finite-grid estimates explicit. -/
theorem integrable_of_nonneg_bounded {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (h : Ω → ℝ) (K : ℝ)
    (hh : Measurable h) (h0 : ∀ x, 0 ≤ h x) (hK : ∀ x, h x ≤ K) :
    Integrable h ν := by
  exact Integrable.of_bound hh.aestronglyMeasurable K
    (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs, abs_of_nonneg (h0 x)] using hK x)

end WishartVerification
end CanonicalSource56

section CanonicalSource57
/- Source: Wishart/GridCounting.lean -/



open scoped Classical

/-!
# Exact collision counts for random Cartesian grids

A pair of grid-index tuples is collision-free when its two sample indices
differ in every coordinate. The count is exact in every finite dimension.
-/

namespace WishartVerification

variable {ι : Type*} [Fintype ι]

def CollisionFree {N : ℕ} (p : (ι → Fin N) × (ι → Fin N)) : Prop :=
  ∀ i, p.1 i ≠ p.2 i

def unequalPairEquiv (N : ℕ) :
    {p : Fin N × Fin N // p.1 ≠ p.2} ≃ ((a : Fin N) × {b : Fin N // b ≠ a}) where
  toFun p := ⟨p.1.1, ⟨p.1.2, Ne.symm p.2⟩⟩
  invFun p := ⟨(p.1, p.2.1), Ne.symm p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

theorem unequalPair_card (N : ℕ) :
    Fintype.card {p : Fin N × Fin N // p.1 ≠ p.2} = N * (N - 1) := by
  classical
  rw [Fintype.card_congr (unequalPairEquiv N), Fintype.card_sigma]
  have h (a : Fin N) : Fintype.card {b : Fin N // b ≠ a} = N - 1 := by
    simpa using Fintype.card_subtype_compl (fun b : Fin N ↦ b = a)
  simp_rw [h]
  simp

def collisionFreePairEquiv (N : ℕ) :
    {p : (ι → Fin N) × (ι → Fin N) // CollisionFree p} ≃
      (ι → {p : Fin N × Fin N // p.1 ≠ p.2}) where
  toFun p i := ⟨(p.1.1 i, p.1.2 i), p.2 i⟩
  invFun p := ⟨(fun i ↦ (p i).1.1, fun i ↦ (p i).1.2), fun i ↦ (p i).2⟩
  left_inv p := by cases p; rfl
  right_inv p := by
    funext i
    exact Subtype.ext rfl

/-- Exactly `(N(N-1))^d` ordered pairs are collision-free in dimension `d`. -/
theorem collisionFree_pair_card (N : ℕ) :
    Fintype.card {p : (ι → Fin N) × (ι → Fin N) // CollisionFree p} =
      (N * (N - 1)) ^ Fintype.card ι := by
  classical
  rw [Fintype.card_congr (collisionFreePairEquiv (ι := ι) N)]
  rw [Fintype.card_fun, unequalPair_card]

/-- The complementary collision count. -/
theorem colliding_pair_card (N : ℕ) :
    Fintype.card {p : (ι → Fin N) × (ι → Fin N) // ¬CollisionFree p} =
      (N ^ Fintype.card ι) ^ 2 - (N * (N - 1)) ^ Fintype.card ι := by
  classical
  rw [Fintype.card_subtype_compl CollisionFree, collisionFree_pair_card]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, pow_two]

end WishartVerification
end CanonicalSource57

section CanonicalSource58
/- Source: Wishart/RandomGridTransfer.lean -/



open scoped Classical

/-!
# From every finite Cartesian grid to a product integral

This file implements a random-grid limit argument. It does not presume
association of the continuous law: that conclusion is to be derived from the
finite-grid inequality. The negligible error consists exactly of index pairs
which reuse a sample in at least one coordinate.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace WishartVerification

variable {ι : Type*} [Fintype ι]

noncomputable def gridSum {N : ℕ} (h : (ι → ℝ) → ℝ) (ω : ι × Fin N → ℝ) : ℝ :=
  ∑ a : ι → Fin N, h (gridPoint a ω)

theorem gridSum_mul_eq_sum {N : ℕ} (h k : (ι → ℝ) → ℝ) (ω : ι × Fin N → ℝ) :
    gridSum h ω * gridSum k ω =
      ∑ p : (ι → Fin N) × (ι → Fin N), h (gridPoint p.1 ω) * k (gridPoint p.2 ω) := by
  simpa only [gridSum, Fintype.sum_prod_type] using
    Fintype.sum_mul_sum (fun a : ι → Fin N ↦ h (gridPoint a ω))
      (fun b : ι → Fin N ↦ k (gridPoint b ω))

variable (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]

theorem integrable_gridPoint_mul_bounded {N : ℕ} (a b : ι → Fin N)
    (h k : (ι → ℝ) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hh : Measurable h) (hk : Measurable k)
    (hh0 : ∀ x, 0 ≤ h x) (hk0 : ∀ x, 0 ≤ k x)
    (hhK : ∀ x, h x ≤ K) (hkK : ∀ x, k x ≤ K) :
    Integrable (fun ω ↦ h (gridPoint a ω) * k (gridPoint b ω)) (gridSampleLaw μ N) := by
  apply integrable_of_nonneg_bounded (gridSampleLaw μ N) _ (K * K)
  · exact (hh.comp (gridPoint_measurable a)).mul (hk.comp (gridPoint_measurable b))
  · intro ω
    exact mul_nonneg (hh0 _) (hk0 _)
  · intro ω
    exact mul_le_mul (hhK _) (hkK _) (hk0 _) hK

theorem integrable_gridSum_mul {N : ℕ}
    (h k : (ι → ℝ) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hh : Measurable h) (hk : Measurable k)
    (hh0 : ∀ x, 0 ≤ h x) (hk0 : ∀ x, 0 ≤ k x)
    (hhK : ∀ x, h x ≤ K) (hkK : ∀ x, k x ≤ K) :
    Integrable (fun ω : ι × Fin N → ℝ ↦ gridSum h ω * gridSum k ω)
      (gridSampleLaw μ N) := by
  simp_rw [gridSum_mul_eq_sum]
  exact integrable_finsetSum Finset.univ fun p _ ↦
    integrable_gridPoint_mul_bounded μ p.1 p.2 h k K hK hh hk hh0 hk0 hhK hkK

theorem integral_gridSum_mul {N : ℕ}
    (h k : (ι → ℝ) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hh : Measurable h) (hk : Measurable k)
    (hh0 : ∀ x, 0 ≤ h x) (hk0 : ∀ x, 0 ≤ k x)
    (hhK : ∀ x, h x ≤ K) (hkK : ∀ x, k x ≤ K) :
    (∫ ω : ι × Fin N → ℝ, gridSum h ω * gridSum k ω ∂gridSampleLaw μ N) =
      ∑ p : (ι → Fin N) × (ι → Fin N),
        ∫ ω, h (gridPoint p.1 ω) * k (gridPoint p.2 ω) ∂gridSampleLaw μ N := by
  simp_rw [gridSum_mul_eq_sum]
  exact integral_finsetSum Finset.univ fun p _ ↦
    integrable_gridPoint_mul_bounded μ p.1 p.2 h k K hK hh hk hh0 hk0 hhK hkK

/-- The collision-free part of the integral has an exact product value. -/
theorem integral_gridSum_mul_lower {N : ℕ}
    (h k : (ι → ℝ) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hh : Measurable h) (hk : Measurable k)
    (hh0 : ∀ x, 0 ≤ h x) (hk0 : ∀ x, 0 ≤ k x)
    (hhK : ∀ x, h x ≤ K) (hkK : ∀ x, k x ≤ K) :
    (((N * (N - 1)) ^ Fintype.card ι : ℕ) : ℝ) *
        ((∫ x, h x ∂Measure.pi μ) * (∫ x, k x ∂Measure.pi μ)) ≤
      ∫ ω : ι × Fin N → ℝ, gridSum h ω * gridSum k ω ∂gridSampleLaw μ N := by
  classical
  rw [integral_gridSum_mul μ h k K hK hh hk hh0 hk0 hhK hkK]
  let J (p : (ι → Fin N) × (ι → Fin N)) : ℝ :=
    ∫ ω, h (gridPoint p.1 ω) * k (gridPoint p.2 ω) ∂gridSampleLaw μ N
  have hJ0 (p) : 0 ≤ J p := integral_nonneg fun ω ↦ mul_nonneg (hh0 _) (hk0 _)
  have hsplit := Fintype.sum_subtype_add_sum_subtype (p := CollisionFree) J
  have hgood : (∑ p : {p : (ι → Fin N) × (ι → Fin N) // CollisionFree p}, J p) =
      (((N * (N - 1)) ^ Fintype.card ι : ℕ) : ℝ) *
        ((∫ x, h x ∂Measure.pi μ) * (∫ x, k x ∂Measure.pi μ)) := by
    have heq (p : {p : (ι → Fin N) × (ι → Fin N) // CollisionFree p}) :
        J p = (∫ x, h x ∂Measure.pi μ) * (∫ x, k x ∂Measure.pi μ) :=
      integral_gridPoint_mul μ p.1.1 p.1.2 p.2 h k hh hk
    simp_rw [heq]
    simp [collisionFree_pair_card, nsmul_eq_mul]
  rw [← hsplit, hgood]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun p _ ↦ hJ0 p))

/-- Reused samples contribute at most the exact collision count times `K²`. -/
theorem integral_gridSum_mul_upper {N : ℕ}
    (h k : (ι → ℝ) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hh : Measurable h) (hk : Measurable k)
    (hh0 : ∀ x, 0 ≤ h x) (hk0 : ∀ x, 0 ≤ k x)
    (hhK : ∀ x, h x ≤ K) (hkK : ∀ x, k x ≤ K) :
    (∫ ω : ι × Fin N → ℝ, gridSum h ω * gridSum k ω ∂gridSampleLaw μ N) ≤
      (((N * (N - 1)) ^ Fintype.card ι : ℕ) : ℝ) *
        ((∫ x, h x ∂Measure.pi μ) * (∫ x, k x ∂Measure.pi μ)) +
      (((N ^ Fintype.card ι) ^ 2 - (N * (N - 1)) ^ Fintype.card ι : ℕ) : ℝ) * (K * K) := by
  classical
  rw [integral_gridSum_mul μ h k K hK hh hk hh0 hk0 hhK hkK]
  let J (p : (ι → Fin N) × (ι → Fin N)) : ℝ :=
    ∫ ω, h (gridPoint p.1 ω) * k (gridPoint p.2 ω) ∂gridSampleLaw μ N
  have hJK (p) : J p ≤ K * K := by
    calc
      J p ≤ ∫ _ω : ι × Fin N → ℝ, K * K ∂gridSampleLaw μ N := by
        apply integral_mono
          (integrable_gridPoint_mul_bounded μ p.1 p.2 h k K hK hh hk hh0 hk0 hhK hkK)
          (integrable_const _)
        intro ω
        exact mul_le_mul (hhK _) (hkK _) (hk0 _) hK
      _ = K * K := by simp
  have hsplit := Fintype.sum_subtype_add_sum_subtype (p := CollisionFree) J
  rw [← hsplit]
  apply add_le_add
  · apply le_of_eq
    have heq (p : {p : (ι → Fin N) × (ι → Fin N) // CollisionFree p}) :
        J p = (∫ x, h x ∂Measure.pi μ) * (∫ x, k x ∂Measure.pi μ) :=
      integral_gridPoint_mul μ p.1.1 p.1.2 p.2 h k hh hk
    simp_rw [heq]
    simp [collisionFree_pair_card, nsmul_eq_mul]
  · calc
      (∑ p : {p : (ι → Fin N) × (ι → Fin N) // ¬CollisionFree p}, J p) ≤
          ∑ _p : {p : (ι → Fin N) × (ι → Fin N) // ¬CollisionFree p}, K * K :=
        Finset.sum_le_sum fun p _ ↦ hJK p
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, colliding_pair_card, nsmul_eq_mul]

/-- A bounded nonnegative four-function inequality valid on every finite
Cartesian grid is also valid for every product probability measure.

This is a genuine integral theorem. The premise concerns finite sums and is
discharged by finite FKG when this theorem is applied to association. -/
theorem integral_four_functions_of_finite_grid
    (A B C D : (ι → ℝ) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hAm : Measurable A) (hBm : Measurable B) (hCm : Measurable C) (hDm : Measurable D)
    (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ x, 0 ≤ B x)
    (hC0 : ∀ x, 0 ≤ C x) (hD0 : ∀ x, 0 ≤ D x)
    (hAK : ∀ x, A x ≤ K) (hBK : ∀ x, B x ≤ K)
    (hCK : ∀ x, C x ≤ K) (hDK : ∀ x, D x ≤ K)
    (hgrid : ∀ (N : ℕ) (ω : ι × Fin N → ℝ),
      gridSum A ω * gridSum B ω ≤ gridSum C ω * gridSum D ω) :
    (∫ x, A x ∂Measure.pi μ) * (∫ x, B x ∂Measure.pi μ) ≤
      (∫ x, C x ∂Measure.pi μ) * (∫ x, D x ∂Measure.pi μ) := by
  classical
  let P : ℝ := (∫ x, A x ∂Measure.pi μ) * (∫ x, B x ∂Measure.pi μ)
  let Q : ℝ := (∫ x, C x ∂Measure.pi μ) * (∫ x, D x ∂Measure.pi μ)
  let d := Fintype.card ι
  have hcount (N : ℕ) : (N * (N - 1)) ^ d ≤ (N ^ d) ^ 2 := by
    calc
      (N * (N - 1)) ^ d =
          Fintype.card {p : (ι → Fin N) × (ι → Fin N) // CollisionFree p} :=
        (collisionFree_pair_card (ι := ι) N).symm
      _ ≤ Fintype.card ((ι → Fin N) × (ι → Fin N)) :=
        Fintype.card_subtype_le _
      _ = (N ^ d) ^ 2 := by simp [d, pow_two]
  have hbound (N : ℕ) :
      (((N * (N - 1)) ^ d : ℕ) : ℝ) * P ≤
        (((N * (N - 1)) ^ d : ℕ) : ℝ) * Q +
          (((N ^ d) ^ 2 - (N * (N - 1)) ^ d : ℕ) : ℝ) * (K * K) := by
    calc
      _ ≤ ∫ ω : ι × Fin N → ℝ, gridSum A ω * gridSum B ω ∂gridSampleLaw μ N :=
        integral_gridSum_mul_lower μ A B K hK hAm hBm hA0 hB0 hAK hBK
      _ ≤ ∫ ω : ι × Fin N → ℝ, gridSum C ω * gridSum D ω ∂gridSampleLaw μ N :=
        integral_mono
          (integrable_gridSum_mul μ A B K hK hAm hBm hA0 hB0 hAK hBK)
          (integrable_gridSum_mul μ C D K hK hCm hDm hC0 hD0 hCK hDK)
          (hgrid N)
      _ ≤ _ := integral_gridSum_mul_upper μ C D K hK hCm hDm hC0 hD0 hCK hDK
  let r (n : ℕ) : ℝ := ((n : ℝ) / ((n : ℝ) + 1)) ^ d
  have hnormalized (n : ℕ) : r n * P ≤ r n * Q + (1 - r n) * (K * K) := by
    let a : ℝ := ((n : ℝ) + 1) ^ d
    have ha : 0 < a := pow_pos (by positivity) _
    have hcoeff : a ^ 2 * r n = a * (n : ℝ) ^ d := by
      dsimp [r, a]
      rw [div_pow]
      field_simp [ne_of_gt (show 0 < (n : ℝ) + 1 by positivity)]
    have hb := hbound (n + 1)
    rw [Nat.cast_sub (hcount (n + 1))] at hb
    simp only [Nat.add_sub_cancel, Nat.cast_pow, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, mul_pow] at hb
    change (a * (n : ℝ) ^ d) * P ≤ (a * (n : ℝ) ^ d) * Q +
      (a ^ 2 - a * (n : ℝ) ^ d) * (K * K) at hb
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos ha)).mp
    calc
      a ^ 2 * (r n * P) = (a * (n : ℝ) ^ d) * P := by rw [← mul_assoc, hcoeff]
      _ ≤ (a * (n : ℝ) ^ d) * Q + (a ^ 2 - a * (n : ℝ) ^ d) * (K * K) := hb
      _ = (a ^ 2 * r n) * Q + (a ^ 2 - a ^ 2 * r n) * (K * K) := by rw [hcoeff]
      _ = a ^ 2 * (r n * Q + (1 - r n) * (K * K)) := by ring
  have hr : Tendsto r atTop (𝓝 (1 : ℝ)) := by
    simpa [r] using (tendsto_natCast_div_add_atTop (1 : ℝ)).pow d
  have hlim := le_of_tendsto_of_tendsto
    (hr.mul_const P)
    ((hr.mul_const Q).add ((tendsto_const_nhds.sub hr).mul_const (K * K)))
    (Eventually.of_forall hnormalized)
  simpa [P, Q] using hlim

end WishartVerification
end CanonicalSource58

section CanonicalSource59
/- Source: Wishart/ContinuousFKG.lean -/



open scoped Classical ENNReal

/-!
# Continuous FKG for bounded densities and tests

The finite lattice inequality is transferred to product probability measures by
independent random grids. The mathematical hypotheses are ordinary measurability,
nonnegativity, boundedness, coordinate monotonicity of the tests, and the lattice
inequality for the density. Association itself is a conclusion.
-/

open MeasureTheory
open Filter
open scoped Topology

namespace WishartVerification

theorem sampledPoint_gridPoint {ι : Type*} {N : ℕ}
    (ω : ι × Fin N → ℝ) (a : ι → Fin N) :
    sampledPoint (fun i j ↦ ω (i, j)) a = gridPoint a ω := rfl

variable {ι : Type*} [Fintype ι]

/-- Integral FKG on a product of arbitrary probability laws on the real line,
for bounded nonnegative density and bounded monotone tests. -/
theorem continuous_fkg_bounded_on
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f g : (ι → ℝ) → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hwm : Measurable w) (hfm : Measurable f) (hgm : Measurable g)
    (hw0 : ∀ x, 0 ≤ w x) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hwM : ∀ x, w x ≤ M) (hfM : ∀ x, f x ≤ M) (hgM : ∀ x, g x ≤ M)
    (hfi : SupportedMonotone w f) (hgi : SupportedMonotone w g)
    (hwl : ∀ x y, w x * w y ≤ w (x ⊓ y) * w (x ⊔ y)) :
    (∫ x, w x * f x ∂Measure.pi μ) * (∫ x, w x * g x ∂Measure.pi μ) ≤
      (∫ x, w x ∂Measure.pi μ) * (∫ x, w x * (f x * g x) ∂Measure.pi μ) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hM2 : M ≤ M * M := by nlinarith
  have hM3 : M * M ≤ M * (M * M) := by nlinarith
  apply integral_four_functions_of_finite_grid μ
    (fun x ↦ w x * f x) (fun x ↦ w x * g x) w
    (fun x ↦ w x * (f x * g x)) (M * (M * M)) (by positivity)
  · exact hwm.mul hfm
  · exact hwm.mul hgm
  · exact hwm
  · exact hwm.mul (hfm.mul hgm)
  · intro x
    exact mul_nonneg (hw0 x) (hf0 x)
  · intro x
    exact mul_nonneg (hw0 x) (hg0 x)
  · exact hw0
  · intro x
    exact mul_nonneg (hw0 x) (mul_nonneg (hf0 x) (hg0 x))
  · intro x
    exact (mul_le_mul (hwM x) (hfM x) (hf0 x) hM0).trans hM3
  · intro x
    exact (mul_le_mul (hwM x) (hgM x) (hg0 x) hM0).trans hM3
  · intro x
    exact (hwM x).trans (hM2.trans hM3)
  · intro x
    exact mul_le_mul (hwM x)
      (mul_le_mul (hfM x) (hgM x) (hg0 x) hM0)
      (mul_nonneg (hf0 x) (hg0 x)) hM0
  · intro N ω
    simpa only [gridSum, sampledPoint_gridPoint] using
      finite_grid_fkg_on (fun i j ↦ ω (i, j)) w f g hw0 hf0 hg0 hfi hgi hwl

/-- Extended nonnegative integral form of the bounded theorem. -/
theorem continuous_fkg_bounded_lintegral_on
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f g : (ι → ℝ) → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hwm : Measurable w) (hfm : Measurable f) (hgm : Measurable g)
    (hw0 : ∀ x, 0 ≤ w x) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hwM : ∀ x, w x ≤ M) (hfM : ∀ x, f x ≤ M) (hgM : ∀ x, g x ≤ M)
    (hfi : SupportedMonotone w f) (hgi : SupportedMonotone w g)
    (hwl : ∀ x y, w x * w y ≤ w (x ⊓ y) * w (x ⊔ y)) :
    (∫⁻ x, ENNReal.ofReal (w x * f x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (w x * g x) ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (w x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (w x * (f x * g x)) ∂Measure.pi μ) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hwf := integrable_of_nonneg_bounded (Measure.pi μ) (fun x ↦ w x * f x) (M * M)
    (hwm.mul hfm) (fun x ↦ mul_nonneg (hw0 x) (hf0 x))
    (fun x ↦ mul_le_mul (hwM x) (hfM x) (hf0 x) hM0)
  have hwg := integrable_of_nonneg_bounded (Measure.pi μ) (fun x ↦ w x * g x) (M * M)
    (hwm.mul hgm) (fun x ↦ mul_nonneg (hw0 x) (hg0 x))
    (fun x ↦ mul_le_mul (hwM x) (hgM x) (hg0 x) hM0)
  have hw := integrable_of_nonneg_bounded (Measure.pi μ) w M hwm hw0 hwM
  have hwfg := integrable_of_nonneg_bounded (Measure.pi μ) (fun x ↦ w x * (f x * g x))
    (M * (M * M)) (hwm.mul (hfm.mul hgm))
    (fun x ↦ mul_nonneg (hw0 x) (mul_nonneg (hf0 x) (hg0 x)))
    (fun x ↦ mul_le_mul (hwM x)
      (mul_le_mul (hfM x) (hgM x) (hg0 x) hM0)
      (mul_nonneg (hf0 x) (hg0 x)) hM0)
  rw [← ofReal_integral_eq_lintegral_ofReal hwf
      (ae_of_all _ fun x ↦ mul_nonneg (hw0 x) (hf0 x)),
    ← ofReal_integral_eq_lintegral_ofReal hwg
      (ae_of_all _ fun x ↦ mul_nonneg (hw0 x) (hg0 x)),
    ← ofReal_integral_eq_lintegral_ofReal hw (ae_of_all _ hw0),
    ← ofReal_integral_eq_lintegral_ofReal hwfg
      (ae_of_all _ fun x ↦ mul_nonneg (hw0 x) (mul_nonneg (hf0 x) (hg0 x))),
    ← ENNReal.ofReal_mul (integral_nonneg (fun x ↦ mul_nonneg (hw0 x) (hf0 x))),
    ← ENNReal.ofReal_mul (integral_nonneg hw0)]
  exact ENNReal.ofReal_le_ofReal
    (continuous_fkg_bounded_on μ w f g M hM hwm hfm hgm hw0 hf0 hg0 hwM hfM hgM hfi hgi hwl)

/-- Monotone convergence in an explicit supremum form for real approximants. -/
theorem lintegral_ofReal_eq_iSup_of_monotone
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (u : ℕ → Ω → ℝ) (U : Ω → ℝ)
    (hum : ∀ n, Measurable (u n))
    (hmono : ∀ x, Monotone fun n ↦ u n x)
    (hlim : ∀ x, Tendsto (fun n ↦ u n x) atTop (𝓝 (U x))) :
    (∫⁻ x, ENNReal.ofReal (U x) ∂ν) =
      ⨆ n, ∫⁻ x, ENNReal.ofReal (u n x) ∂ν := by
  have hpoint (x : Ω) : ENNReal.ofReal (U x) = ⨆ n, ENNReal.ofReal (u n x) := by
    exact tendsto_nhds_unique (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim x))
      (tendsto_atTop_iSup (ENNReal.ofReal_mono.comp (hmono x)))
  simp_rw [hpoint]
  apply lintegral_iSup (fun n ↦ (hum n).ennreal_ofReal)
  intro n m hnm x
  exact ENNReal.ofReal_le_ofReal (hmono x hnm)

noncomputable def testCap (n : ℕ) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  min (f x) ((n : ℝ) + 1)

theorem testCap_nonneg (n : ℕ) (f : (ι → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x) (x) :
    0 ≤ testCap n f x := le_min (hf x) (by positivity)

theorem testCap_mono_index (f : (ι → ℝ) → ℝ) (x) : Monotone fun n ↦ testCap n f x := by
  intro n m hnm
  exact min_le_min_left _ (by exact_mod_cast Nat.add_le_add_right hnm 1)

theorem testCap_mono (n : ℕ) (f : (ι → ℝ) → ℝ) (hf : Monotone f) :
    Monotone (testCap n f) := fun _ _ h ↦ min_le_min_right _ (hf h)

theorem testCap_tendsto (f : (ι → ℝ) → ℝ) (x) :
    Tendsto (fun n ↦ testCap n f x) atTop (𝓝 (f x)) := by
  have hevent : ∀ᶠ n : ℕ in atTop, f x ≤ (n : ℝ) + 1 :=
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (f x))).mono fun n hn ↦ hn.trans (by linarith)
  apply tendsto_const_nhds.congr'
  exact hevent.mono fun n hn ↦ (min_eq_left hn).symm

/-- Continuous FKG for a density obtained as an increasing limit of bounded
MTP₂ densities. Test functions are arbitrary measurable nonnegative increasing
real functions, and the conclusion allows infinite expectations.

The subsequent Vandermonde specialization constructs the approximating densities
explicitly; this theorem does not assume any association conclusion. -/
theorem continuous_fkg_of_monotone_approximation_on
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w : (ι → ℝ) → ℝ) (wn : ℕ → (ι → ℝ) → ℝ) (bound : ℕ → ℝ)
    (hwnm : ∀ n, Measurable (wn n))
    (hwn0 : ∀ n x, 0 ≤ wn n x) (hbound : ∀ n, 1 ≤ bound n)
    (hwnbound : ∀ n x, wn n x ≤ bound n)
    (hwnl : ∀ n x y, wn n x * wn n y ≤ wn n (x ⊓ y) * wn n (x ⊔ y))
    (hwnmono : ∀ x, Monotone fun n ↦ wn n x)
    (hwnlim : ∀ x, Tendsto (fun n ↦ wn n x) atTop (𝓝 (w x)))
    (f g : (ι → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : SupportedMonotone w f) (hgi : SupportedMonotone w g) :
    (∫⁻ x, ENNReal.ofReal (w x * f x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (w x * g x) ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (w x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (w x * (f x * g x)) ∂Measure.pi μ) := by
  have hwnle (n : ℕ) (x) : wn n x ≤ w x :=
    (hwnmono x).ge_of_tendsto (hwnlim x) n
  have hw0 (x) : 0 ≤ w x := (hwn0 0 x).trans (hwnle 0 x)
  let A (n : ℕ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (wn n x * testCap n f x) ∂Measure.pi μ
  let B (n : ℕ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (wn n x * testCap n g x) ∂Measure.pi μ
  have hAm (n) : Measurable (fun x ↦ wn n x * testCap n f x) :=
    (hwnm n).mul (hfm.min measurable_const)
  have hBm (n) : Measurable (fun x ↦ wn n x * testCap n g x) :=
    (hwnm n).mul (hgm.min measurable_const)
  have hAmono (x) : Monotone fun n ↦ wn n x * testCap n f x := by
    intro n m hnm
    exact mul_le_mul (hwnmono x hnm) (testCap_mono_index f x hnm)
      (testCap_nonneg n f hf0 x) (hwn0 m x)
  have hBmono (x) : Monotone fun n ↦ wn n x * testCap n g x := by
    intro n m hnm
    exact mul_le_mul (hwnmono x hnm) (testCap_mono_index g x hnm)
      (testCap_nonneg n g hg0 x) (hwn0 m x)
  have hAsup : (∫⁻ x, ENNReal.ofReal (w x * f x) ∂Measure.pi μ) = ⨆ n, A n :=
    lintegral_ofReal_eq_iSup_of_monotone (Measure.pi μ) _ _ hAm hAmono
      (fun x ↦ (hwnlim x).mul (testCap_tendsto f x))
  have hBsup : (∫⁻ x, ENNReal.ofReal (w x * g x) ∂Measure.pi μ) = ⨆ n, B n :=
    lintegral_ofReal_eq_iSup_of_monotone (Measure.pi μ) _ _ hBm hBmono
      (fun x ↦ (hwnlim x).mul (testCap_tendsto g x))
  have hAn : Monotone A := fun n m hnm ↦ lintegral_mono fun x ↦
    ENNReal.ofReal_le_ofReal (hAmono x hnm)
  have hBn : Monotone B := fun n m hnm ↦ lintegral_mono fun x ↦
    ENNReal.ofReal_le_ofReal (hBmono x hnm)
  have hfinite (n : ℕ) : A n * B n ≤
      (∫⁻ x, ENNReal.ofReal (w x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (w x * (f x * g x)) ∂Measure.pi μ) := by
    let M := max (bound n) ((n : ℝ) + 1)
    have h := continuous_fkg_bounded_lintegral_on μ (wn n) (testCap n f) (testCap n g) M
      ((hbound n).trans (le_max_left _ _)) (hwnm n)
      (hfm.min measurable_const) (hgm.min measurable_const) (hwn0 n)
      (testCap_nonneg n f hf0) (testCap_nonneg n g hg0)
      (fun x ↦ (hwnbound n x).trans (le_max_left _ _))
      (fun x ↦ (min_le_right _ _).trans (le_max_right _ _))
      (fun x ↦ (min_le_right _ _).trans (le_max_right _ _))
      (fun x y hx hy hxy ↦ min_le_min_right _
        (hfi x y (hx.trans_le (hwnle n x)) (hy.trans_le (hwnle n y)) hxy))
      (fun x y hx hy hxy ↦ min_le_min_right _
        (hgi x y (hx.trans_le (hwnle n x)) (hy.trans_le (hwnle n y)) hxy)) (hwnl n)
    apply h.trans
    apply mul_le_mul'
    · exact lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hwnle n x)
    · apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul (hwnle n x)
        (mul_le_mul (min_le_left _ _) (min_le_left _ _)
          (testCap_nonneg n g hg0 x) (hf0 x))
        (mul_nonneg (testCap_nonneg n f hf0 x) (testCap_nonneg n g hg0 x)) (hw0 x)
  rw [hAsup, hBsup, ENNReal.iSup_mul]
  simp_rw [ENNReal.mul_iSup]
  apply iSup_le
  intro n
  apply iSup_le
  intro m
  exact (mul_le_mul' (hAn (le_max_left n m)) (hBn (le_max_right n m))).trans
    (hfinite (max n m))

end WishartVerification
end CanonicalSource59

section CanonicalSource60
/- Source: Wishart/VandermondeAssociation.lean -/



open scoped Classical ENNReal

/-!
# Association of the Vandermonde density in every finite dimension

The bounded approximants are constructed explicitly from separate coordinate
weights and expanding compact boxes. Only coordinate weights are capped: the
whole density is never capped, since that operation need not preserve MTP₂.
-/

open MeasureTheory Filter
open scoped Topology

namespace WishartVerification

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

noncomputable def truncateCoordinate (n : ℕ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  if |t| ≤ (n : ℝ) + 1 then min (w t) ((n : ℝ) + 1) else 0

theorem truncateCoordinate_nonneg (n : ℕ) (w : ℝ → ℝ)
    (hw : ∀ t, 0 ≤ w t) (t : ℝ) : 0 ≤ truncateCoordinate n w t := by
  unfold truncateCoordinate
  split_ifs
  · exact le_min (hw t) (by positivity)
  · rfl

theorem truncateCoordinate_le (n : ℕ) (w : ℝ → ℝ) (t : ℝ) :
    truncateCoordinate n w t ≤ (n : ℝ) + 1 := by
  unfold truncateCoordinate
  split_ifs
  · exact min_le_right _ _
  · positivity

theorem truncateCoordinate_measurable (n : ℕ) (w : ℝ → ℝ) (hw : Measurable w) :
    Measurable (truncateCoordinate n w) := by
  exact Measurable.ite (measurableSet_le measurable_id.abs measurable_const)
    (hw.min measurable_const) measurable_const

theorem truncateCoordinate_mono (w : ℝ → ℝ) (hw : ∀ t, 0 ≤ w t) (t : ℝ) :
    Monotone fun n ↦ truncateCoordinate n w t := by
  intro n m hnm
  have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  by_cases hn : |t| ≤ (n : ℝ) + 1
  · have hm : |t| ≤ (m : ℝ) + 1 := hn.trans hnm'
    simp only [truncateCoordinate, hn, hm, ite_true]
    exact min_le_min_left _ hnm'
  · simp only [truncateCoordinate, hn, ite_false]
    exact truncateCoordinate_nonneg m w hw t

theorem truncateCoordinate_tendsto (w : ℝ → ℝ) (t : ℝ) :
    Tendsto (fun n ↦ truncateCoordinate n w t) atTop (𝓝 (w t)) := by
  have hevent : ∀ᶠ n : ℕ in atTop, max |t| (w t) ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (max |t| (w t)))
  apply tendsto_const_nhds.congr'
  filter_upwards [hevent] with n hn
  have ht : |t| ≤ (n : ℝ) + 1 := (le_max_left _ _).trans (hn.trans (by linarith))
  have hw : w t ≤ (n : ℝ) + 1 := (le_max_right _ _).trans (hn.trans (by linarith))
  simp [truncateCoordinate, ht, min_eq_left hw]

theorem orderedVandermonde_measurable (β : ℝ) : Measurable (orderedVandermonde (ι := ι) β) := by
  classical
  unfold orderedVandermonde
  apply Finset.measurable_prod
  intro i hi
  apply Finset.measurable_prod
  intro j hj
  by_cases hij : i < j
  · simpa [hij] using
      (((measurable_pi_apply j).sub (measurable_pi_apply i)).max measurable_const).pow_const β
  · simp [hij]

theorem vandermondeWeight_measurable (w : ι → ℝ → ℝ) (β : ℝ)
    (hw : ∀ i, Measurable (w i)) : Measurable (vandermondeWeight w β) := by
  unfold vandermondeWeight
  apply Measurable.mul _ (orderedVandermonde_measurable β)
  exact Finset.measurable_prod _ fun i _ ↦ (hw i).comp (measurable_pi_apply i)

noncomputable def truncatedVandermondeWeight (w : ι → ℝ → ℝ) (β : ℝ) (n : ℕ) :
    (ι → ℝ) → ℝ := vandermondeWeight (fun i ↦ truncateCoordinate n (w i)) β

noncomputable def truncatedVandermondeBound (β : ℝ) (n : ℕ) : ℝ :=
  max 1 (((n : ℝ) + 1) ^ Fintype.card ι *
    (((2 * ((n : ℝ) + 1)) ^ β) ^ Fintype.card ι) ^ Fintype.card ι)

theorem truncatedVandermonde_bound (w : ι → ℝ → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hw : ∀ i t, 0 ≤ w i t) (n : ℕ) (x : ι → ℝ) :
    truncatedVandermondeWeight w β n x ≤ truncatedVandermondeBound (ι := ι) β n := by
  classical
  let R : ℝ := (n : ℝ) + 1
  let C : ℝ := (2 * R) ^ β
  let d := Fintype.card ι
  have hR : 1 ≤ R := by
    dsimp [R]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hC : 1 ≤ C := Real.one_le_rpow (by linarith) hβ
  by_cases hbox : ∀ i, |x i| ≤ R
  · have hfactor (i j : ι) :
        (if i < j then (max (x j - x i) 0) ^ β else 1) ≤ C := by
      by_cases hij : i < j
      · simp only [hij, ite_true]
        apply Real.rpow_le_rpow (by positivity) _ hβ
        apply max_le
        · have hi := (abs_le.mp (hbox i)).1
          have hj := (abs_le.mp (hbox j)).2
          linarith
        · positivity
      · simpa [hij] using hC
    have hV : orderedVandermonde β x ≤ (C ^ d) ^ d := by
      calc
        orderedVandermonde β x ≤ ∏ _i : ι, ∏ _j : ι, C := by
          unfold orderedVandermonde
          apply Finset.prod_le_prod₀
          · intro i hi
            positivity
          · intro i hi
            apply Finset.prod_le_prod₀
            · intro j hj
              split_ifs <;> positivity
            · intro j hj
              exact hfactor i j
        _ = (C ^ d) ^ d := by simp [d]
    have hW : (∏ i, truncateCoordinate n (w i) (x i)) ≤ R ^ d := by
      calc
        (∏ i, truncateCoordinate n (w i) (x i)) ≤ ∏ _i : ι, R :=
          Finset.prod_le_prod₀ (fun i _ ↦ truncateCoordinate_nonneg n (w i) (hw i) (x i))
            (fun i _ ↦ truncateCoordinate_le n (w i) (x i))
        _ = R ^ d := by simp [d]
    calc
      truncatedVandermondeWeight w β n x ≤ R ^ d * (C ^ d) ^ d :=
        mul_le_mul hW hV (orderedVandermonde_nonneg β x) (by positivity)
      _ ≤ truncatedVandermondeBound (ι := ι) β n := le_max_right _ _
  · obtain ⟨i, hi⟩ := not_forall.mp hbox
    have hi0 : truncateCoordinate n (w i) (x i) = 0 := by
      simp [truncateCoordinate, R, hi]
    have hprod : (∏ i, truncateCoordinate n (w i) (x i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi0
    simp only [truncatedVandermondeWeight, vandermondeWeight, hprod, zero_mul]
    exact zero_le_one.trans (le_max_left _ _)

theorem truncatedVandermonde_mono (w : ι → ℝ → ℝ) (β : ℝ)
    (hw : ∀ i t, 0 ≤ w i t) (x : ι → ℝ) :
    Monotone fun n ↦ truncatedVandermondeWeight w β n x := by
  intro n m hnm
  apply mul_le_mul_of_nonneg_right _ (orderedVandermonde_nonneg β x)
  exact Finset.prod_le_prod₀
    (fun i _ ↦ truncateCoordinate_nonneg n (w i) (hw i) (x i))
    (fun i _ ↦ truncateCoordinate_mono (w i) (hw i) (x i) hnm)

theorem truncatedVandermonde_tendsto (w : ι → ℝ → ℝ) (β : ℝ) (x : ι → ℝ) :
    Tendsto (fun n ↦ truncatedVandermondeWeight w β n x) atTop
      (𝓝 (vandermondeWeight w β x)) := by
  have hp : Tendsto (fun n ↦ ∏ i, truncateCoordinate n (w i) (x i)) atTop
      (𝓝 (∏ i, w i (x i))) := by
    exact tendsto_finsetProd _ fun i _ ↦ truncateCoordinate_tendsto (w i) (x i)
  exact hp.mul_const (orderedVandermonde β x)

/-- Full extended association inequality for a Vandermonde density relative to
an arbitrary product of one-dimensional probability laws. Every dimension and
every nonnegative measurable coordinate weight is permitted. -/
theorem vandermonde_association_lintegral_on
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w : ι → ℝ → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t)
    (f g : (ι → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : SupportedMonotone (vandermondeWeight w β) f)
    (hgi : SupportedMonotone (vandermondeWeight w β) g) :
    (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * f x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * g x) ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * (f x * g x)) ∂Measure.pi μ) := by
  apply continuous_fkg_of_monotone_approximation_on μ (vandermondeWeight w β)
    (truncatedVandermondeWeight w β) (truncatedVandermondeBound (ι := ι) β)
  · intro n
    exact vandermondeWeight_measurable _ β fun i ↦ truncateCoordinate_measurable n (w i) (hwm i)
  · intro n x
    exact vandermondeWeight_nonneg _ β
      (fun i t ↦ truncateCoordinate_nonneg n (w i) (hw0 i) t) x
  · intro n
    exact le_max_left _ _
  · exact truncatedVandermonde_bound w β hβ hw0
  · intro n x y
    exact vandermondeWeight_lattice _ β
      (fun i t ↦ truncateCoordinate_nonneg n (w i) (hw0 i) t) hβ x y
  · exact truncatedVandermonde_mono w β hw0
  · exact truncatedVandermonde_tendsto w β
  · exact hfm
  · exact hgm
  · exact hf0
  · exact hg0
  · exact hfi
  · exact hgi

/-- Global monotonicity is a convenient special case of support monotonicity. -/
theorem vandermonde_association_lintegral
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w : ι → ℝ → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t)
    (f g : (ι → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : Monotone f) (hgi : Monotone g) :
    (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * f x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * g x) ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * (f x * g x)) ∂Measure.pi μ) :=
  vandermonde_association_lintegral_on μ w β hβ hwm hw0 f g hfm hgm hf0 hg0
    (supportedMonotone_of_monotone _ _ hfi) (supportedMonotone_of_monotone _ _ hgi)

end WishartVerification
end CanonicalSource60

section CanonicalSource61
/- Source: Wishart/ProductDensity.lean -/



open scoped Classical ENNReal

/-!
# Product densities and the sigma-finite reference-measure bridge

The random-grid proof uses probability reference measures. A sigma-finite
reference measure can always be replaced by an equivalent probability law;
its Radon–Nikodym derivative is absorbed into the individual coordinate weight.
This section proves that change of reference measure, rather than assuming any
integrability of the individual weights.
-/

open MeasureTheory ProbabilityTheory

namespace WishartVerification

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise densities multiply under a finite product of probability
reference measures. The target coordinate measures may be infinite. -/
theorem pi_eq_withDensity_prod
    (μ ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, SigmaFinite (ν i)]
    (ρ : ι → ℝ → ℝ≥0∞) (hρm : ∀ i, Measurable (ρ i))
    (hρν : ∀ i, (μ i).withDensity (ρ i) = ν i) :
    Measure.pi ν = (Measure.pi μ).withDensity (fun x ↦ ∏ i, ρ i (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hsPi : MeasurableSet (Set.pi Set.univ s) :=
    MeasurableSet.pi Set.countable_univ (fun i _ ↦ hs i)
  rw [withDensity_apply _ hsPi, ← lintegral_indicator hsPi]
  have hindicator :
      (Set.pi Set.univ s).indicator (fun x ↦ ∏ i, ρ i (x i)) =
        fun x ↦ ∏ i, (s i).indicator (ρ i) (x i) := by
    funext x
    by_cases hx : ∀ i, x i ∈ s i
    · have hxPi : x ∈ Set.pi Set.univ s := fun i _ ↦ hx i
      simp only [Set.indicator_of_mem hxPi]
      apply Finset.prod_congr rfl
      intro i hi
      exact (Set.indicator_of_mem (hx i) _).symm
    · obtain ⟨i, hi⟩ := not_forall.mp hx
      have hxPi : x ∉ Set.pi Set.univ s := fun h ↦ hi (h i (Set.mem_univ i))
      rw [Set.indicator_of_notMem hxPi]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
  rw [hindicator]
  calc
    (∫⁻ x, ∏ i, (s i).indicator (ρ i) (x i) ∂Measure.pi μ) =
        ∏ i, ∫⁻ x, (s i).indicator (ρ i) (x i) ∂Measure.pi μ := by
      exact lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
        (fun (i : ι) (x : ι → ℝ) ↦ (s i).indicator (ρ i) (x i))
        (iIndepFun_pi (fun i ↦ ((hρm i).indicator (hs i)).aemeasurable))
        (fun i ↦ ((hρm i).indicator (hs i)).comp (measurable_pi_apply i))
    _ = ∏ i, ν i (s i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [(measurePreserving_eval μ i).lintegral_comp ((hρm i).indicator (hs i)),
        lintegral_indicator (hs i), ← withDensity_apply _ (hs i), hρν i]

/-- The real-valued Radon–Nikodym correction of a coordinate weight. -/
noncomputable def referenceCorrectedWeight (ν : ι → Measure ℝ)
    [∀ i, SigmaFinite (ν i)] (w : ι → ℝ → ℝ) : ι → ℝ → ℝ :=
  fun i t ↦ w i t * ((ν i).rnDeriv (ν i).toFinite t).toReal

theorem referenceCorrectedWeight_measurable (ν : ι → Measure ℝ)
    [∀ i, SigmaFinite (ν i)] (w : ι → ℝ → ℝ)
    (hwm : ∀ i, Measurable (w i)) (i : ι) :
    Measurable (referenceCorrectedWeight ν w i) :=
  (hwm i).mul ((Measure.measurable_rnDeriv _ _).ennreal_toReal)

theorem referenceCorrectedWeight_nonneg (ν : ι → Measure ℝ)
    [∀ i, SigmaFinite (ν i)] (w : ι → ℝ → ℝ)
    (hw0 : ∀ i t, 0 ≤ w i t) (i : ι) (t : ℝ) :
    0 ≤ referenceCorrectedWeight ν w i t :=
  mul_nonneg (hw0 i t) ENNReal.toReal_nonneg

theorem referenceCorrectedWeight_factor [LinearOrder ι]
    (ν : ι → Measure ℝ) [∀ i, SigmaFinite (ν i)] (w : ι → ℝ → ℝ)
    (β : ℝ) (x : ι → ℝ) :
    vandermondeWeight (referenceCorrectedWeight ν w) β x =
      (∏ i, ((ν i).rnDeriv (ν i).toFinite (x i)).toReal) * vandermondeWeight w β x := by
  unfold vandermondeWeight referenceCorrectedWeight
  rw [Finset.prod_mul_distrib]
  ring

theorem referenceCorrectedWeight_support [LinearOrder ι]
    (ν : ι → Measure ℝ) [∀ i, SigmaFinite (ν i)] (w : ι → ℝ → ℝ)
    (β : ℝ) (x : ι → ℝ) (hx : 0 < vandermondeWeight (referenceCorrectedWeight ν w) β x) :
    0 < vandermondeWeight w β x := by
  rw [referenceCorrectedWeight_factor] at hx
  exact pos_of_mul_pos_right hx (Finset.prod_nonneg fun i _ ↦ ENNReal.toReal_nonneg)

/-- The density adjustment is exact for every nonnegative measurable test,
including tests with infinite integral. -/
theorem vandermonde_reference_change [LinearOrder ι]
    (ν : ι → Measure ℝ) [∀ i, SigmaFinite (ν i)] [∀ i, NeZero (ν i)]
    (w : ι → ℝ → ℝ) (β : ℝ)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t)
    (h : (ι → ℝ) → ℝ) (hhm : Measurable h) (hh0 : ∀ x, 0 ≤ h x) :
    (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * h x) ∂Measure.pi ν) =
      ∫⁻ x, ENNReal.ofReal
        (vandermondeWeight (referenceCorrectedWeight ν w) β x * h x)
        ∂Measure.pi (fun i ↦ (ν i).toFinite) := by
  classical
  let μ : ι → Measure ℝ := fun i ↦ (ν i).toFinite
  let ρ : ι → ℝ → ℝ≥0∞ := fun i ↦ (ν i).rnDeriv (μ i)
  have hρm : ∀ i, Measurable (ρ i) := fun i ↦ Measure.measurable_rnDeriv _ _
  have hρν : ∀ i, (μ i).withDensity (ρ i) = ν i := fun i ↦
    Measure.withDensity_rnDeriv_eq _ _ (absolutelyContinuous_toFinite _)
  have hpi := pi_eq_withDensity_prod μ ν ρ hρm hρν
  have hprodm : Measurable (fun x : ι → ℝ ↦ ∏ i, ρ i (x i)) :=
    Finset.measurable_prod _ fun i _ ↦ (hρm i).comp (measurable_pi_apply i)
  rw [hpi, lintegral_withDensity_eq_lintegral_mul (g := fun x ↦
    ENNReal.ofReal (vandermondeWeight w β x * h x)) _ hprodm
    ((vandermondeWeight_measurable w β hwm).mul hhm).ennreal_ofReal]
  have hfinite : ∀ᵐ x ∂Measure.pi μ, ∀ i, ρ i (x i) ≠ ∞ := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval μ i).quasiMeasurePreserving.ae
      (Measure.rnDeriv_ne_top (ν i) (μ i))
  apply lintegral_congr_ae
  filter_upwards [hfinite] with x hx
  have hprod0 : 0 ≤ ∏ i, w i (x i) := Finset.prod_nonneg fun i _ ↦ hw0 i _
  have hcprod0 : 0 ≤ ∏ i, (ρ i (x i)).toReal :=
    Finset.prod_nonneg fun i _ ↦ ENNReal.toReal_nonneg
  have hcorr : vandermondeWeight (referenceCorrectedWeight ν w) β x =
      (∏ i, (ρ i (x i)).toReal) * vandermondeWeight w β x := by
    unfold vandermondeWeight referenceCorrectedWeight
    rw [Finset.prod_mul_distrib]
    ring
  rw [hcorr, mul_assoc, ENNReal.ofReal_mul hcprod0,
    ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ ENNReal.toReal_nonneg)]
  simp only [Pi.mul_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact (ENNReal.ofReal_toReal (hx i)).symm

/-- Association for arbitrary nonzero sigma-finite coordinate reference laws.
Lebesgue measure is the principal application. No separate integrability of
the coordinate weights is required. -/
theorem vandermonde_association_sigmaFinite_on [LinearOrder ι]
    (ν : ι → Measure ℝ) [∀ i, SigmaFinite (ν i)] [∀ i, NeZero (ν i)]
    (w : ι → ℝ → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t)
    (f g : (ι → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : SupportedMonotone (vandermondeWeight w β) f)
    (hgi : SupportedMonotone (vandermondeWeight w β) g) :
    (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * f x) ∂Measure.pi ν) *
        (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * g x) ∂Measure.pi ν) ≤
      (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x) ∂Measure.pi ν) *
        (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * (f x * g x)) ∂Measure.pi ν) := by
  have h := vandermonde_association_lintegral_on (fun i ↦ (ν i).toFinite)
    (referenceCorrectedWeight ν w) β hβ
    (referenceCorrectedWeight_measurable ν w hwm)
    (referenceCorrectedWeight_nonneg ν w hw0) f g hfm hgm hf0 hg0
    (fun x y hx hy hxy ↦ hfi x y
      (referenceCorrectedWeight_support ν w β x hx)
      (referenceCorrectedWeight_support ν w β y hy) hxy)
    (fun x y hx hy hxy ↦ hgi x y
      (referenceCorrectedWeight_support ν w β x hx)
      (referenceCorrectedWeight_support ν w β y hy) hxy)
  have hone := vandermonde_reference_change ν w β hwm hw0 (fun _ ↦ 1) measurable_const
    (fun _ ↦ zero_le_one)
  simp only [mul_one] at hone
  rw [← vandermonde_reference_change ν w β hwm hw0 f hfm hf0,
    ← vandermonde_reference_change ν w β hwm hw0 g hgm hg0,
    ← hone,
    ← vandermonde_reference_change ν w β hwm hw0 (fun x ↦ f x * g x)
      (hfm.mul hgm) (fun x ↦ mul_nonneg (hf0 x) (hg0 x))] at h
  simpa only [mul_one] using h

/-- The global-monotonicity specialization. -/
theorem vandermonde_association_sigmaFinite [LinearOrder ι]
    (ν : ι → Measure ℝ) [∀ i, SigmaFinite (ν i)] [∀ i, NeZero (ν i)]
    (w : ι → ℝ → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t)
    (f g : (ι → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : Monotone f) (hgi : Monotone g) :
    (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * f x) ∂Measure.pi ν) *
        (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * g x) ∂Measure.pi ν) ≤
      (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x) ∂Measure.pi ν) *
        (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x * (f x * g x)) ∂Measure.pi ν) :=
  vandermonde_association_sigmaFinite_on ν w β hβ hwm hw0 f g hfm hgm hf0 hg0
    (supportedMonotone_of_monotone _ _ hfi) (supportedMonotone_of_monotone _ _ hgi)

end WishartVerification
end CanonicalSource61

section CanonicalSource62
/- Source: Wishart/ChamberAssociation.lean -/



open scoped Classical ENNReal

/-!
# The weak association assertion of Lemma 2.1

The ordered chamber and its density are explicit. Test functions only need to
increase on that chamber. Normalization is proved to give a probability law,
and the association inequality permits infinite nonnegative expectations.
-/

open MeasureTheory

namespace WishartVerification

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def orderedChamber (s : Set ℝ) : Set (ι → ℝ) :=
  {x | StrictMono x ∧ ∀ i, x i ∈ s}

noncomputable def chamberWeight (s : Set ℝ) (w : ι → ℝ → ℝ) (β : ℝ) :
    (ι → ℝ) → ℝ := vandermondeWeight (fun i ↦ s.indicator (w i)) β

theorem chamberWeight_nonneg (s : Set ℝ) (w : ι → ℝ → ℝ) (β : ℝ)
    (hw0 : ∀ i t, 0 ≤ w i t) (x) : 0 ≤ chamberWeight s w β x :=
  vandermondeWeight_nonneg _ β (fun i t ↦ Set.indicator_nonneg (fun t _ ↦ hw0 i t) t) x

theorem chamberWeight_measurable (s : Set ℝ) (hs : MeasurableSet s)
    (w : ι → ℝ → ℝ) (β : ℝ) (hwm : ∀ i, Measurable (w i)) :
    Measurable (chamberWeight s w β) :=
  vandermondeWeight_measurable _ β (fun i ↦ (hwm i).indicator hs)

theorem chamberWeight_eq_zero_off (s : Set ℝ) (w : ι → ℝ → ℝ)
    (β : ℝ) (hβ : 0 < β) (x : ι → ℝ) (hx : x ∉ orderedChamber (ι := ι) s) :
    chamberWeight s w β x = 0 := by
  classical
  by_cases hxmono : StrictMono x
  · have hxmem : ¬∀ i, x i ∈ s := fun h ↦ hx ⟨hxmono, h⟩
    obtain ⟨i, hi⟩ := not_forall.mp hxmem
    unfold chamberWeight vandermondeWeight
    have hp : (∏ j, s.indicator (w j) (x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
    rw [hp, zero_mul]
  · unfold chamberWeight vandermondeWeight
    rw [orderedVandermonde_eq_zero_off_chamber β hβ x hxmono, mul_zero]

/-- The formal density agrees exactly with the paper's product on the chamber
and vanishes elsewhere. -/
theorem chamberWeight_eq_density (s : Set ℝ) (w : ι → ℝ → ℝ)
    (β : ℝ) (hβ : 0 < β) (x : ι → ℝ) :
    chamberWeight s w β x =
      if x ∈ orderedChamber (ι := ι) s then
        (∏ i, w i (x i)) * (∏ i, ∏ j, if i < j then (x j - x i) ^ β else 1)
      else 0 := by
  classical
  by_cases hx : x ∈ orderedChamber (ι := ι) s
  · rw [if_pos hx]
    unfold chamberWeight vandermondeWeight
    rw [orderedVandermonde_eq_on_chamber β x hx.1]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact Set.indicator_of_mem (hx.2 i) _
  · rw [if_neg hx]
    exact chamberWeight_eq_zero_off s w β hβ x hx

theorem supportedMonotone_chamberWeight (s : Set ℝ) (w : ι → ℝ → ℝ)
    (β : ℝ) (hβ : 0 < β) (f : (ι → ℝ) → ℝ)
    (hf : MonotoneOn f (orderedChamber s)) :
    SupportedMonotone (chamberWeight s w β) f := by
  intro x y hx hy hxy
  have hxmem : x ∈ orderedChamber (ι := ι) s := by
    by_contra h
    rw [chamberWeight_eq_zero_off s w β hβ x h] at hx
    exact (lt_irrefl 0) hx
  have hymem : y ∈ orderedChamber (ι := ι) s := by
    by_contra h
    rw [chamberWeight_eq_zero_off s w β hβ y h] at hy
    exact (lt_irrefl 0) hy
  exact hf hxmem hymem hxy

section Normalization

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Normalizing a nonnegative real density by its nonnegative integral. -/
noncomputable def normalizedWeight (μ : Measure Ω) (w : Ω → ℝ) : Measure Ω :=
  (∫⁻ x, ENNReal.ofReal (w x) ∂μ)⁻¹ • μ.withDensity (fun x ↦ ENNReal.ofReal (w x))

theorem normalizedWeight_probability (μ : Measure Ω) (w : Ω → ℝ)
    (hZ0 : (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ≠ 0)
    (hZtop : (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ≠ ∞) :
    IsProbabilityMeasure (normalizedWeight μ w) := by
  constructor
  simp only [normalizedWeight, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hZ0 hZtop

theorem normalizedWeight_lintegral (μ : Measure Ω) (w f : Ω → ℝ)
    (hwm : Measurable w) (hfm : Measurable f) (hw0 : ∀ x, 0 ≤ w x) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂normalizedWeight μ w) =
      (∫⁻ x, ENNReal.ofReal (w x) ∂μ)⁻¹ *
        ∫⁻ x, ENNReal.ofReal (w x * f x) ∂μ := by
  rw [normalizedWeight, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ hwm.ennreal_ofReal hfm.ennreal_ofReal]
  simp only [smul_eq_mul, Pi.mul_apply, ENNReal.ofReal_mul (hw0 _)]

/-- Exact algebra of normalization, valid for infinite test expectations. -/
theorem normalizedWeight_association (μ : Measure Ω) (w f g : Ω → ℝ)
    (hwm : Measurable w) (hfm : Measurable f) (hgm : Measurable g)
    (hw0 : ∀ x, 0 ≤ w x) (hg0 : ∀ x, 0 ≤ g x)
    (hZ0 : (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ≠ 0)
    (hZtop : (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ≠ ∞)
    (hassoc : (∫⁻ x, ENNReal.ofReal (w x * f x) ∂μ) *
        (∫⁻ x, ENNReal.ofReal (w x * g x) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (w x) ∂μ) *
        (∫⁻ x, ENNReal.ofReal (w x * (f x * g x)) ∂μ)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂normalizedWeight μ w) *
        (∫⁻ x, ENNReal.ofReal (g x) ∂normalizedWeight μ w) ≤
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂normalizedWeight μ w := by
  rw [normalizedWeight_lintegral μ w f hwm hfm hw0,
    normalizedWeight_lintegral μ w g hwm hgm hw0,
    normalizedWeight_lintegral μ w (fun x ↦ f x * g x) hwm (hfm.mul hgm) hw0]
  let Z := ∫⁻ x, ENNReal.ofReal (w x) ∂μ
  let A := ∫⁻ x, ENNReal.ofReal (w x * f x) ∂μ
  let B := ∫⁻ x, ENNReal.ofReal (w x * g x) ∂μ
  let C := ∫⁻ x, ENNReal.ofReal (w x * (f x * g x)) ∂μ
  change (Z⁻¹ * A) * (Z⁻¹ * B) ≤ Z⁻¹ * C
  calc
    (Z⁻¹ * A) * (Z⁻¹ * B) = (Z⁻¹ * Z⁻¹) * (A * B) := by ac_rfl
    _ ≤ (Z⁻¹ * Z⁻¹) * (Z * C) := mul_le_mul_right hassoc _
    _ = Z⁻¹ * ((Z⁻¹ * Z) * C) := by ac_rfl
    _ = Z⁻¹ * C := by rw [ENNReal.inv_mul_cancel hZ0 hZtop, one_mul]

end Normalization

/-- Lemma 2.1's weak association statement, for the normalized Lebesgue density
on an ordered chamber. An arbitrary measurable set of allowed coordinate values
is permitted; in the manuscript it is the interval `(a,b)`.

Strictness is a separate assertion and is not asserted by this declaration. -/
theorem lemma_2_1_association
    (s : Set ℝ) (hs : MeasurableSet s) (w : ι → ℝ → ℝ)
    (β : ℝ) (hβ : 0 < β) (hwm : ∀ i, Measurable (w i))
    (hw0 : ∀ i t, 0 ≤ w i t)
    (hZ0 : (∫⁻ x : ι → ℝ, ENNReal.ofReal (chamberWeight s w β x)) ≠ 0)
    (hZtop : (∫⁻ x : ι → ℝ, ENNReal.ofReal (chamberWeight s w β x)) ≠ ∞)
    (f g : (ι → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : MonotoneOn f (orderedChamber s)) (hgi : MonotoneOn g (orderedChamber s)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂normalizedWeight volume (chamberWeight s w β)) *
        (∫⁻ x, ENNReal.ofReal (g x) ∂normalizedWeight volume (chamberWeight s w β)) ≤
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂normalizedWeight volume (chamberWeight s w β) := by
  apply normalizedWeight_association volume (chamberWeight s w β) f g
    (chamberWeight_measurable s hs w β hwm) hfm hgm
    (chamberWeight_nonneg s w β hw0) hg0 hZ0 hZtop
  exact vandermonde_association_sigmaFinite_on (fun _ : ι ↦ volume)
    (fun i ↦ s.indicator (w i)) β hβ.le (fun i ↦ (hwm i).indicator hs)
    (fun i t ↦ Set.indicator_nonneg (fun t _ ↦ hw0 i t) t)
    f g hfm hgm hf0 hg0
    (supportedMonotone_chamberWeight s w β hβ f hfi)
    (supportedMonotone_chamberWeight s w β hβ g hgi)

end WishartVerification
end CanonicalSource62

section CanonicalSource63
/- Source: Wishart/SpectralWindow.lean -/



noncomputable section

/-!
# An injective spectral window and its Haar frame event

A Cayley frame with positive diagonal entries has no column-sign ambiguity.
The full window in skew coordinates is enough: its sign saturation has finite,
strictly positive Haar mass, and probability normalization will control the
angular integral without a separate bounded-chart estimate.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator
open scoped Classical ENNReal

namespace Wishart.Spectral

abbrev positiveChamber (p : ℕ) : Set (Fin p → ℝ) :=
  WishartVerification.orderedChamber (Set.Ioi 0)

theorem isOpen_positiveChamber (p : ℕ) : IsOpen (positiveChamber p) := by
  have hm : IsOpen {lam : Fin p → ℝ | StrictMono lam} := by
    have heq : {lam : Fin p → ℝ | StrictMono lam} =
        ⋂ i : Fin p, ⋂ j : Fin p, ⋂ (_ : i < j), {lam : Fin p → ℝ | lam i < lam j} := by
      ext lam
      simp only [Set.mem_setOf_eq, Set.mem_iInter, StrictMono]
    rw [heq]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply i) (continuous_apply j)
  have hp : IsOpen {lam : Fin p → ℝ | ∀ i, 0 < lam i} := by
    have heq : {lam : Fin p → ℝ | ∀ i, 0 < lam i} =
        ⋂ i : Fin p, {lam : Fin p → ℝ | 0 < lam i} := by
      ext lam
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  exact hm.inter hp

def spectralWindow (p : ℕ) : Set (Sym p) :=
  (spectralSplit p) ⁻¹' (positiveChamber p ×ˢ cayleyWindow p)

theorem isOpen_spectralWindow (p : ℕ) : IsOpen (spectralWindow p) :=
  ((isOpen_positiveChamber p).prod (isOpen_cayleyWindow p)).preimage
    (spectralSplit p).continuous

/-- On the positive ascending chamber the chart has a literally unique spectrum
and, in the positive-diagonal window, a unique frame as well. -/
theorem spectralChart_injOn_window (p : ℕ) :
    Set.InjOn (@spectralChart p) (spectralWindow p) := by
  intro X hX Y hY hXY
  have hspec : (spectralSplit p X).1 = (spectralSplit p Y).1 := by
    have h := congrArg ascendingSpectrum hXY
    simpa only [spectralChart,
      ascendingSpectrum_conjugate_diagonal _ _ hX.1.1,
      ascendingSpectrum_conjugate_diagonal _ _ hY.1.1] using h
  have hframe : (spectralSplit p X).2 = (spectralSplit p Y).2 := by
    apply cayley_spectral_injective_fixed _ hX.1.1.injective hX.2 hY.2
    simpa only [spectralChart, ← hspec] using hXY
  exact (spectralSplit p).injective (Prod.ext hspec hframe)

def spectralWindowImage (p : ℕ) : Set (Sym p) :=
  spectralChart '' spectralWindow p

theorem measurableSet_spectralWindowImage (p : ℕ) :
    MeasurableSet (spectralWindowImage p) :=
  measurable_image_of_fderivWithin (isOpen_spectralWindow p).measurableSet
    (fun X _ => (hasFDerivAt_spectralChart X).hasFDerivWithinAt)
    (spectralChart_injOn_window p)

def frameWindow (p : ℕ) : Set (Orth p) :=
  {O | (1 + (O : Matrix (Fin p) (Fin p) ℝ)).det ≠ 0 ∧
    ∀ i, 0 < (O : Matrix (Fin p) (Fin p) ℝ) i i}

theorem image_cayley_window (p : ℕ) :
    cayley '' cayleyWindow p = frameWindow p := by
  ext O
  constructor
  · rintro ⟨S, hS, rfl⟩
    refine ⟨?_, hS⟩
    exact (Set.ext_iff.mp (range_cayley p) (cayley S)).mp ⟨S, rfl⟩
  · rintro ⟨hden, hdiag⟩
    obtain ⟨S, hS⟩ := (Set.ext_iff.mp (range_cayley p) O).mpr hden
    refine ⟨S, ?_, hS⟩
    change ∀ i, 0 < (cayley S : Matrix (Fin p) (Fin p) ℝ) i i
    rw [hS]
    exact hdiag

theorem isOpen_frameWindow (p : ℕ) : IsOpen (frameWindow p) := by
  have hdiag : IsOpen {O : Orth p | ∀ i, 0 < (O : Matrix (Fin p) (Fin p) ℝ) i i} := by
    have heq : {O : Orth p | ∀ i, 0 < (O : Matrix (Fin p) (Fin p) ℝ) i i} =
        ⋂ i : Fin p, {O : Orth p | 0 < (O : Matrix (Fin p) (Fin p) ℝ) i i} := by
      ext O
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_subtype_val.matrix_elem i i)
  have hden := isOpen_range_cayley p
  rw [range_cayley] at hden
  exact hden.inter hdiag

@[simp] theorem signOrthogonal_mul_self {p : ℕ} (ε : Fin p → Bool) :
    signOrthogonal ε * signOrthogonal ε = (1 : Orth p) := by
  apply Subtype.ext
  exact signDiagonal_mul_self ε

@[simp] theorem signOrthogonal_all_true (p : ℕ) :
    signOrthogonal (fun _ : Fin p => true) = (1 : Orth p) := by
  apply Subtype.ext
  simp only [signOrthogonal, signDiagonal, boolSign, Matrix.diagonal_one,
    Submonoid.coe_one]

/-- The finite column-sign saturation of the actual Cayley frame window. -/
def frameSignWindow (p : ℕ) : Set (Orth p) :=
  ⋃ ε : Fin p → Bool, (fun O : Orth p => O * signOrthogonal ε) ⁻¹' frameWindow p

theorem isOpen_frameSignWindow (p : ℕ) : IsOpen (frameSignWindow p) :=
  isOpen_iUnion fun ε => (isOpen_frameWindow p).preimage
    (continuous_id.mul continuous_const)

theorem one_mem_frameSignWindow (p : ℕ) : (1 : Orth p) ∈ frameSignWindow p := by
  apply Set.mem_iUnion.mpr
  refine ⟨fun _ => true, ?_⟩
  simp only [Set.mem_preimage, signOrthogonal_all_true, mul_one]
  rw [← image_cayley_window]
  exact ⟨0, zero_mem_cayleyWindow p, cayley_zero p⟩

noncomputable def frameWindowMass (p : ℕ) : ℝ≥0∞ :=
  TauCeti.haarProb (Orth p) (frameSignWindow p)

theorem frameWindowMass_pos (p : ℕ) : 0 < frameWindowMass p :=
  (isOpen_frameSignWindow p).measure_pos (TauCeti.haarProb (Orth p))
    ⟨1, one_mem_frameSignWindow p⟩

theorem frameWindowMass_ne_top (p : ℕ) : frameWindowMass p ≠ ∞ :=
  measure_ne_top _ _

/-- The full stabilizer of a simple real diagonal matrix consists of column
signs. This gives a frame event independent of the eigenvalues. -/
theorem exists_sign_of_conjugate_diagonal_eq {p : ℕ} (lam : Fin p → ℝ)
    (hlam : Function.Injective lam) (Q O : Orth p)
    (heq : conjugate Q (diagonalSym lam) = conjugate O (diagonalSym lam)) :
    ∃ ε : Fin p → Bool, O = Q * signOrthogonal ε := by
  let E : Orth p := Q⁻¹ * O
  have hfix : conjugate E (diagonalSym lam) = diagonalSym lam := by
    dsimp [E]
    rw [conjugate_mul, ← heq, ← conjugate_mul, inv_mul_cancel, conjugate_one]
  have hfixM : (E : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal lam *
      (E : Matrix (Fin p) (Fin p) ℝ)ᵀ = Matrix.diagonal lam := by
    simpa only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply, diagonalSym]
      using congrArg Subtype.val hfix
  have hcomm : (E : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal lam =
      Matrix.diagonal lam * (E : Matrix (Fin p) (Fin p) ℝ) := by
    have h := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ =>
      A * (E : Matrix (Fin p) (Fin p) ℝ)) hfixM
    simpa only [Matrix.mul_assoc, orth_transpose_mul, Matrix.mul_one] using h
  let e : Fin p → ℝ := fun i => (E : Matrix (Fin p) (Fin p) ℝ) i i
  have hdiag : (E : Matrix (Fin p) (Fin p) ℝ) = Matrix.diagonal e :=
    eq_diagonal_of_commute_diagonal lam hlam E hcomm
  have hsquare (i : Fin p) : e i * e i = 1 := by
    have h := orth_transpose_mul E
    rw [hdiag, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal] at h
    simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using
      congrFun (congrFun h i) i
  let ε : Fin p → Bool := fun i => if e i = 1 then true else false
  have hsign (i : Fin p) : boolSign (ε i) = e i := by
    by_cases hi : e i = 1
    · simp only [ε, hi, if_pos, boolSign]
    · have hm : e i = -1 := (mul_self_eq_one_iff.mp (hsquare i)).resolve_left hi
      have hε : ε i = false := by simp only [ε, hi, if_false]
      rw [hε]
      exact hm.symm
  have hE : E = signOrthogonal ε := by
    apply Subtype.ext
    rw [hdiag]
    exact congrArg Matrix.diagonal (funext fun i => (hsign i).symm)
  refine ⟨ε, ?_⟩
  rw [← hE]
  simp only [E, mul_inv_cancel_left]

/-- For every positive simple ascending spectrum, membership in the chart image
is the same measurable finite-sign frame event. -/
theorem conjugate_mem_spectralWindowImage_iff {p : ℕ}
    (O : Orth p) (lam : Fin p → ℝ) (hlam : lam ∈ positiveChamber p) :
    conjugate O (diagonalSym lam) ∈ spectralWindowImage p ↔ O ∈ frameSignWindow p := by
  constructor
  · rintro ⟨X, hX, hXeq⟩
    have hspec : (spectralSplit p X).1 = lam := by
      have h := congrArg ascendingSpectrum hXeq
      simpa only [spectralChart,
        ascendingSpectrum_conjugate_diagonal _ _ hX.1.1,
        ascendingSpectrum_conjugate_diagonal _ _ hlam.1] using h
    have hconj : conjugate (cayley (spectralSplit p X).2) (diagonalSym lam) =
        conjugate O (diagonalSym lam) := by
      simpa only [spectralChart, hspec] using hXeq
    obtain ⟨ε, hε⟩ := exists_sign_of_conjugate_diagonal_eq lam hlam.1.injective _ O hconj
    apply Set.mem_iUnion.mpr
    refine ⟨ε, ?_⟩
    change O * signOrthogonal ε ∈ frameWindow p
    rw [hε, mul_assoc, signOrthogonal_mul_self, mul_one, ← image_cayley_window]
    exact ⟨_, hX.2, rfl⟩
  · intro hO
    obtain ⟨ε, hε⟩ := Set.mem_iUnion.mp hO
    change O * signOrthogonal ε ∈ frameWindow p at hε
    rw [← image_cayley_window] at hε
    obtain ⟨S, hS, hSO⟩ := hε
    refine ⟨(spectralSplit p).symm (lam, S), ?_, ?_⟩
    · change (spectralSplit p ((spectralSplit p).symm (lam, S))) ∈
        positiveChamber p ×ˢ cayleyWindow p
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact ⟨hlam, hS⟩
    · simp only [spectralChart, ContinuousLinearEquiv.apply_symm_apply, hSO,
        conjugate_mul, conjugate_signOrthogonal_diagonal]

end Wishart.Spectral
end
end CanonicalSource63

section CanonicalSource64
/- Source: Wishart/SimpleSpectrum.lean -/



/-!
# Simple spectrum almost everywhere

The repeated-spectrum set is the image of a zero-Jacobian parameter set under
the global Cayley spectral map. Mathlib's fixed-dimensional Sard theorem then
gives Lebesgue nullity, and the actual Wishart density transfers this nullity to
every nonsingular real-shape Wishart law.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator

namespace Wishart.Spectral

theorem spectralDerivative_det_eq_zero_of_repeated {p : ℕ} (X : Sym p)
    (hX : ¬Function.Injective (spectralSplit p X).1) :
    (spectralDerivative (spectralSplit p X).2 (spectralSplit p X).1).det = 0 := by
  apply abs_eq_zero.mp
  rw [abs_det_spectralDerivative, gapProduct_eq_zero_of_not_injective hX, abs_zero,
    mul_zero]

/-- Repeated eigenvalues form a null set for the actual symmetric Lebesgue
measure, in every finite dimension. -/
theorem symmetricLebesgue_repeated_spectrum (p : ℕ) :
    TauCeti.symmetricLebesgue p
      {S : Sym p | ¬Function.Injective (coordinateSpectrum S)} = 0 := by
  apply measure_mono_null (repeated_spectrum_subset_spectralChart_image p)
  exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (TauCeti.symmetricLebesgue p)
    (fun X _ => (hasFDerivAt_spectralChart X).hasFDerivWithinAt)
    (fun X hX => spectralDerivative_det_eq_zero_of_repeated X hX)

/-- Absolute continuity is applied to the genuine Wishart density. The result
does not assume an eigenvalue law or restrict the shape parameter to integers. -/
theorem ae_simple_spectrum_nonsingularWishart {p : ℕ} {α : ℝ}
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef) (hα : (p : ℝ) - 1 < α) :
    ∀ᵐ S ∂TauCeti.Probability.nonsingularWishartMeasure α C,
      Function.Injective (coordinateSpectrum S) := by
  rw [MeasureTheory.ae_iff]
  rw [TauCeti.Probability.nonsingularWishartMeasure_of_posDef hC hα]
  exact withDensity_absolutelyContinuous _ _ (symmetricLebesgue_repeated_spectrum p)

end Wishart.Spectral
end CanonicalSource64

section CanonicalSource65
/- Source: Wishart/SpectralAveraging.lean -/



/-!
# Haar averaging of the actual spectral marginal

The positive ascending chamber has full mass for every real shape parameter
above the nonsingularity threshold. Independent Haar reconstruction then turns
the chart restriction into a fixed, positive finite multiple of the entire
spectral marginal. No eigenvalue density is assumed in this step.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability
open scoped Classical ENNReal

namespace Wishart.Spectral

noncomputable def identityEigenLaw (p : ℕ) (α : ℝ) : Measure (Fin p → ℝ) :=
  (nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ)).map ascendingSpectrum

theorem identityEigenLaw_isProbability {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    IsProbabilityMeasure (identityEigenLaw p α) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (Matrix.PosDef.one : (1 : Matrix (Fin p) (Fin p) ℝ).PosDef) hα
  unfold identityEigenLaw
  infer_instance

theorem ae_identityEigenLaw_mem_chamber {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ∀ᵐ lam ∂identityEigenLaw p α, lam ∈ positiveChamber p := by
  apply (ae_map_iff (continuous_ascendingSpectrum p).measurable.aemeasurable
    (isOpen_positiveChamber p).measurableSet).mpr
  filter_upwards [ae_simple_spectrum_nonsingularWishart Matrix.PosDef.one hα,
    ae_posDef_nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ)] with S hs hp
  refine ⟨strictMono_ascendingSpectrum S hs, ?_⟩
  intro i
  exact hp.eigenvalues_pos (ascendingIndexEquiv p i)

/-- The exact chart restriction is a fixed Haar mass times the whole eigenvalue
law, for every nonnegative measurable test function. -/
theorem setLIntegral_spectralWindow_wishart {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (f : (Fin p → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ S in spectralWindowImage p, f (ascendingSpectrum S)
      ∂nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ)) =
        frameWindowMass p * ∫⁻ lam, f lam ∂identityEigenLaw p α := by
  letI := identityEigenLaw_isProbability hα
  let build : Orth p × (Fin p → ℝ) → Sym p :=
    fun z => conjugate z.1 (diagonalSym z.2)
  let F : Sym p → ℝ≥0∞ :=
    (spectralWindowImage p).indicator (fun S => f (ascendingSpectrum S))
  have hbuild : Measurable build :=
    (continuous_conjugate p).measurable.comp
      (measurable_fst.prodMk ((continuous_diagonalSym p).measurable.comp measurable_snd))
  have hF : Measurable F :=
    (hf.comp (continuous_ascendingSpectrum p).measurable).indicator
      (measurableSet_spectralWindowImage p)
  have hrec : ((haarProb (Orth p)).prod (identityEigenLaw p α)).map build =
      nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ) :=
    haar_ascending_spectral_reconstruction hα
  have hinner (lam : Fin p → ℝ) (hlam : lam ∈ positiveChamber p) :
      (∫⁻ O, F (build (O, lam)) ∂haarProb (Orth p)) = frameWindowMass p * f lam := by
    have heq (O : Orth p) : F (build (O, lam)) =
        (frameSignWindow p).indicator (fun _ => f lam) O := by
      by_cases hO : O ∈ frameSignWindow p
      · have hmem := (conjugate_mem_spectralWindowImage_iff O lam hlam).mpr hO
        simp only [F, build, Set.indicator_of_mem hmem, Set.indicator_of_mem hO,
          ascendingSpectrum_conjugate_diagonal O lam hlam.1]
      · have hmem : conjugate O (diagonalSym lam) ∉ spectralWindowImage p :=
          fun h => hO ((conjugate_mem_spectralWindowImage_iff O lam hlam).mp h)
        simp only [F, build, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hO]
    rw [lintegral_congr heq,
      lintegral_indicator_const (isOpen_frameSignWindow p).measurableSet]
    exact mul_comm _ _
  calc
    (∫⁻ S in spectralWindowImage p, f (ascendingSpectrum S)
      ∂nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ)) =
        ∫⁻ S, F S ∂nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ) :=
      (lintegral_indicator (measurableSet_spectralWindowImage p)
        (fun S => f (ascendingSpectrum S))).symm
    _ = ∫⁻ lam, ∫⁻ O, F (build (O, lam)) ∂haarProb (Orth p) ∂identityEigenLaw p α := by
      rw [← hrec, lintegral_map hF hbuild]
      simpa only [Function.comp_def] using
        lintegral_prod_symm (F ∘ build) (hF.comp hbuild).aemeasurable
    _ = ∫⁻ lam, frameWindowMass p * f lam ∂identityEigenLaw p α := by
      apply lintegral_congr_ae
      exact (ae_identityEigenLaw_mem_chamber hα).mono hinner
    _ = _ := lintegral_const_mul _ hf

end Wishart.Spectral
end CanonicalSource65

section CanonicalSource66
/- Source: Wishart/SpectralMeasureCoordinates.lean -/



/-!
# Lebesgue coordinates and the angular factor

Any fixed additive Haar normalization on the skew subspace is suitable. Haar
uniqueness supplies the exact finite positive factor between the product
coordinates and the manuscript's upper-triangle Lebesgue measure. The factor is
retained explicitly and disappears only when the spectral law is normalized.
-/

open Matrix MeasureTheory TauCeti
open scoped Classical ENNReal

namespace Wishart.Spectral

instance skew_locallyCompactSpace (p : ℕ) : LocallyCompactSpace (Skew p) :=
  (skewCoordinates p).toHomeomorph.isClosedEmbedding.locallyCompactSpace

instance skew_secondCountableTopology (p : ℕ) : SecondCountableTopology (Skew p) :=
  (skewCoordinates p).toHomeomorph.secondCountableTopology

noncomputable def angularLebesgue (p : ℕ) : Measure (Skew p) := Measure.addHaar

instance angularLebesgue_isAddHaarMeasure (p : ℕ) :
    (angularLebesgue p).IsAddHaarMeasure := by
  unfold angularLebesgue
  infer_instance

instance angularLebesgue_sigmaFinite (p : ℕ) : SigmaFinite (angularLebesgue p) := by
  unfold angularLebesgue
  infer_instance

noncomputable def coordinateHaarFactor (p : ℕ) : ℝ≥0∞ :=
  Measure.addHaarScalarFactor
    ((symmetricLebesgue p).map (spectralSplit p))
    ((volume : Measure (Fin p → ℝ)).prod (angularLebesgue p))

theorem map_spectralSplit_symmetricLebesgue (p : ℕ) :
    (symmetricLebesgue p).map (spectralSplit p) =
      coordinateHaarFactor p • (volume.prod (angularLebesgue p)) := by
  letI : ((symmetricLebesgue p).map (spectralSplit p)).IsAddHaarMeasure :=
    (spectralSplit p).isAddHaarMeasure_map (symmetricLebesgue p)
  exact Measure.isAddLeftInvariant_eq_smul _ _

theorem coordinateHaarFactor_ne_zero (p : ℕ) : coordinateHaarFactor p ≠ 0 := by
  letI : ((symmetricLebesgue p).map (spectralSplit p)).IsAddHaarMeasure :=
    (spectralSplit p).isAddHaarMeasure_map (symmetricLebesgue p)
  simpa only [coordinateHaarFactor, ne_eq, ENNReal.coe_eq_zero] using
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      ((symmetricLebesgue p).map (spectralSplit p))
      ((volume : Measure (Fin p → ℝ)).prod (angularLebesgue p))).ne'

theorem coordinateHaarFactor_ne_top (p : ℕ) : coordinateHaarFactor p ≠ ∞ :=
  ENNReal.coe_ne_top

theorem setLIntegral_spectralSplit (p : ℕ)
    (f : (Fin p → ℝ) × Skew p → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ X in spectralWindow p, f (spectralSplit p X) ∂symmetricLebesgue p) =
      coordinateHaarFactor p *
        ∫⁻ z in positiveChamber p ×ˢ cayleyWindow p,
          f z ∂(volume.prod (angularLebesgue p)) := by
  calc
    (∫⁻ X in spectralWindow p, f (spectralSplit p X) ∂symmetricLebesgue p) =
        ∫⁻ z in positiveChamber p ×ˢ cayleyWindow p,
          f z ∂(symmetricLebesgue p).map (spectralSplit p) :=
      (setLIntegral_map ((isOpen_positiveChamber p).measurableSet.prod
        (isOpen_cayleyWindow p).measurableSet) hf (spectralSplit p).continuous.measurable).symm
    _ = _ := by
      rw [map_spectralSplit_symmetricLebesgue, Measure.restrict_smul,
        lintegral_smul_measure]
      rfl

theorem continuous_skew_inverse_plus (p : ℕ) :
    Continuous (fun S : Skew p => (1 + (S : Matrix (Fin p) (Fin p) ℝ))⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro S
  have hden : Continuous (fun T : Skew p => 1 + (T : Matrix (Fin p) (Fin p) ℝ)) := by
    fun_prop
  have hinv : ContinuousAt Inv.inv (1 + (S : Matrix (Fin p) (Fin p) ℝ)) := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ (det_one_add_skew_ne_zero (transpose_skew S)))
  exact hinv.comp (f := fun T : Skew p => 1 + (T : Matrix (Fin p) (Fin p) ℝ))
    hden.continuousAt

theorem continuous_skew_inverse_minus (p : ℕ) :
    Continuous (fun S : Skew p => (1 - (S : Matrix (Fin p) (Fin p) ℝ))⁻¹) := by
  simpa only [Function.comp_def, Submodule.coe_neg, ← sub_eq_add_neg] using
    (continuous_skew_inverse_plus p).comp continuous_neg

theorem continuous_cayleyAngularEquiv_apply {p : ℕ} (H : Skew p) :
    Continuous (fun S : Skew p => cayleyAngularEquiv S H) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun S : Skew p => (-2 : ℝ) •
      ((1 - (S : Matrix (Fin p) (Fin p) ℝ))⁻¹ *
        (H : Matrix (Fin p) (Fin p) ℝ) * (1 + (S : Matrix (Fin p) (Fin p) ℝ))⁻¹)) :=
    by
      simpa only [Pi.smul_def, Pi.mul_def] using
        (((continuous_skew_inverse_minus p).mul
          (continuous_const (y := (H : Matrix (Fin p) (Fin p) ℝ)))).mul
          (continuous_skew_inverse_plus p)).const_smul (-2 : ℝ)
  exact hc.congr fun S => (coe_cayleyAngularEquiv_apply S H).symm

theorem continuous_spectralAngularEquiv_apply {p : ℕ} (X : Sym p) :
    Continuous (fun S : Skew p => spectralAngularEquiv S X) := by
  have hc : Continuous (fun S : Skew p => (spectralSplit p).symm
      ((spectralSplit p X).1, cayleyAngularEquiv S (spectralSplit p X).2)) :=
    (spectralSplit p).symm.continuous.comp
      (continuous_const.prodMk (continuous_cayleyAngularEquiv_apply (spectralSplit p X).2))
  simpa only [spectralAngularEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply] using hc

theorem continuous_angularJacobian (p : ℕ) : Continuous (@angularJacobian p) := by
  have hc : Continuous (fun S : Skew p => LinearMap.toMatrix (symmetricBasis p)
      (symmetricBasis p) (spectralAngularEquiv S : Sym p →ₗ[ℝ] Sym p)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [LinearMap.toMatrix_apply, symmetricBasis_repr]
    exact (continuous_subtype_val.comp
      (continuous_spectralAngularEquiv_apply (symmetricBasis p j))).matrix_elem i.1.1 i.1.2
  apply hc.matrix_det.abs.congr
  intro S
  change |Matrix.det (LinearMap.toMatrix (symmetricBasis p) (symmetricBasis p)
      (spectralAngularEquiv S : Sym p →ₗ[ℝ] Sym p))| = angularJacobian S
  rw [LinearMap.det_toMatrix]
  rfl

/-- The complete angular multiplier is initially allowed to be infinite. Its
finiteness and nonzero value will follow from the exact probability identity. -/
noncomputable def angularMass (p : ℕ) : ℝ≥0∞ :=
  coordinateHaarFactor p *
    ∫⁻ S in cayleyWindow p, ENNReal.ofReal (angularJacobian S) ∂angularLebesgue p

end Wishart.Spectral
end CanonicalSource66

section CanonicalSource67
/- Source: Wishart/SpectralWeights.lean -/



/-!
# Exact factorization of the Wishart density in spectral coordinates

The coordinate weight is the manuscript's Laguerre weight on `(0,∞)` and has a
measurable nonnegative extension outside that interval. The Vandermonde factor
is exactly the ascending product, with exponent one and no missing multiplicity.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability
open scoped Classical ENNReal

namespace Wishart.Spectral

noncomputable def laguerreWeight (p : ℕ) (α t : ℝ) : ℝ :=
  (max t 0) ^ ((α - (p : ℝ) - 1) / 2) * Real.exp (-t / 2)

noncomputable def wishartEigenDensity (p : ℕ) (α : ℝ) : (Fin p → ℝ) → ℝ :=
  WishartVerification.chamberWeight (Set.Ioi 0) (fun _ => laguerreWeight p α) 1

theorem laguerreWeight_nonneg (p : ℕ) (α t : ℝ) : 0 ≤ laguerreWeight p α t :=
  mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (Real.exp_pos _).le

theorem measurable_laguerreWeight (p : ℕ) (α : ℝ) : Measurable (laguerreWeight p α) := by
  exact (((measurable_id.max measurable_const).pow_const _).mul
    ((measurable_id.neg.div_const 2).exp))

theorem laguerreWeight_pos {p : ℕ} (α : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < laguerreWeight p α t := by
  unfold laguerreWeight
  exact mul_pos (Real.rpow_pos_of_pos (ht.trans_le (le_max_left _ _)) _) (Real.exp_pos _)

theorem wishartEigenDensity_nonneg (p : ℕ) (α : ℝ) (lam : Fin p → ℝ) :
    0 ≤ wishartEigenDensity p α lam :=
  WishartVerification.chamberWeight_nonneg _ _ _ (fun _ => laguerreWeight_nonneg p α) lam

theorem measurable_wishartEigenDensity (p : ℕ) (α : ℝ) :
    Measurable (wishartEigenDensity p α) :=
  WishartVerification.chamberWeight_measurable _ measurableSet_Ioi _ _
    (fun _ => measurable_laguerreWeight p α)

theorem gapProduct_eq_double_product {p : ℕ} (lam : Fin p → ℝ) :
    gapProduct lam = ∏ i, ∏ j, if i < j then lam j - lam i else 1 := by
  classical
  calc
    gapProduct lam = ∏ ij ∈ (Finset.univ : Finset (Fin p × Fin p)).filter
        (fun ij => ij.1 < ij.2), (lam ij.2 - lam ij.1) := by
      symm
      exact Finset.prod_subtype _ (by simp) _
    _ = ∏ ij : Fin p × Fin p, if ij.1 < ij.2 then lam ij.2 - lam ij.1 else 1 :=
      Finset.prod_filter _ _
    _ = _ := Fintype.prod_prod_type _

theorem wishartEigenDensity_on_chamber {p : ℕ} (α : ℝ) (lam : Fin p → ℝ)
    (hlam : lam ∈ positiveChamber p) :
    wishartEigenDensity p α lam = (∏ i, laguerreWeight p α (lam i)) * gapProduct lam := by
  rw [wishartEigenDensity, WishartVerification.chamberWeight_eq_density _ _ 1 (by norm_num),
    if_pos hlam, gapProduct_eq_double_product]
  simp only [Real.rpow_one]

theorem wishartEigenDensity_off_chamber {p : ℕ} (α : ℝ) (lam : Fin p → ℝ)
    (hlam : lam ∉ positiveChamber p) : wishartEigenDensity p α lam = 0 :=
  WishartVerification.chamberWeight_eq_zero_off _ _ 1 (by norm_num) lam hlam

noncomputable def wishartSpectralConstant (p : ℕ) (α : ℝ) : ℝ :=
  (2 : ℝ) ^ (α * (p : ℝ) / 2) * multivariateGamma p (α / 2)

theorem wishartSpectralConstant_pos {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    0 < wishartSpectralConstant p α :=
  mul_pos (Real.rpow_pos_of_pos two_pos _) (multivariateGamma_pos (by linarith))

theorem det_conjugate {p : ℕ} (O : Orth p) (S : Sym p) :
    (conjugate O S : Matrix (Fin p) (Fin p) ℝ).det =
      (S : Matrix (Fin p) (Fin p) ℝ).det := by
  have hO : (O : Matrix (Fin p) (Fin p) ℝ).det *
      (O : Matrix (Fin p) (Fin p) ℝ).det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using
      congrArg Matrix.det (orth_mul_transpose O)
  rw [show (conjugate O S : Matrix (Fin p) (Fin p) ℝ) =
      (O : Matrix (Fin p) (Fin p) ℝ) * (S : Matrix (Fin p) (Fin p) ℝ) *
        (O : Matrix (Fin p) (Fin p) ℝ)ᵀ from
          Matrix.coe_symmetricCongruenceLinearMap_apply _ _]
  simp only [Matrix.det_mul, Matrix.det_transpose]
  calc
    _ = (S : Matrix (Fin p) (Fin p) ℝ).det *
        ((O : Matrix (Fin p) (Fin p) ℝ).det * (O : Matrix (Fin p) (Fin p) ℝ).det) := by ring
    _ = _ := by rw [hO, mul_one]

theorem trace_conjugate {p : ℕ} (O : Orth p) (S : Sym p) :
    (conjugate O S : Matrix (Fin p) (Fin p) ℝ).trace =
      (S : Matrix (Fin p) (Fin p) ℝ).trace := by
  rw [show (conjugate O S : Matrix (Fin p) (Fin p) ℝ) =
      (O : Matrix (Fin p) (Fin p) ℝ) * (S : Matrix (Fin p) (Fin p) ℝ) *
        (O : Matrix (Fin p) (Fin p) ℝ)ᵀ from
          Matrix.coe_symmetricCongruenceLinearMap_apply _ _,
    Matrix.trace_mul_cycle, orth_transpose_mul, Matrix.one_mul]

theorem posDef_conjugate_iff {p : ℕ} (O : Orth p) (S : Sym p) :
    (conjugate O S : Matrix (Fin p) (Fin p) ℝ).PosDef ↔
      (S : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  simpa only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (O : Matrix (Fin p) (Fin p) ℝ)))

theorem prod_laguerreWeight {p : ℕ} (α : ℝ) (lam : Fin p → ℝ)
    (hlam : ∀ i, 0 < lam i) :
    (∏ i, laguerreWeight p α (lam i)) =
      (∏ i, lam i) ^ ((α - (p : ℝ) - 1) / 2) * Real.exp (-(∑ i, lam i) / 2) := by
  have hmax (i : Fin p) : max (lam i) 0 = lam i := max_eq_left (hlam i).le
  simp only [laguerreWeight, hmax, Finset.prod_mul_distrib]
  rw [Real.finsetProd_rpow _ _ (fun i _ => (hlam i).le)
    ((α - (p : ℝ) - 1) / 2), ← Real.exp_sum]
  simp only [← Finset.sum_div, Finset.sum_neg_distrib]

/-- The actual matrix density, not a replacement definition, has the required
product form at every orthogonal spectral representative. -/
theorem nonsingularWishartPDFReal_conjugate_diagonal {p : ℕ} (α : ℝ)
    (O : Orth p) (lam : Fin p → ℝ) (hlam : ∀ i, 0 < lam i) :
    nonsingularWishartPDFReal α (1 : Matrix (Fin p) (Fin p) ℝ)
      (conjugate O (diagonalSym lam)) =
        (∏ i, laguerreWeight p α (lam i)) / wishartSpectralConstant p α := by
  have hp : (conjugate O (diagonalSym lam) : Matrix (Fin p) (Fin p) ℝ).PosDef :=
    (posDef_conjugate_iff O _).mpr (Matrix.PosDef.diagonal hlam)
  rw [nonsingularWishartPDFReal_of_posDef _ _ hp, prod_laguerreWeight α lam hlam,
    det_conjugate]
  simp only [diagonalSym, Matrix.det_diagonal, inv_one, Matrix.one_mul,
    trace_conjugate, Matrix.trace_diagonal, Matrix.det_one, Real.one_rpow, mul_one,
    wishartSpectralConstant]

/-- On the chart, matrix density times the exact Jacobian separates into the
angular part and precisely the paper's beta-one Laguerre density. -/
theorem wishart_spectral_density_factor {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (X : Sym p) (hX : X ∈ spectralWindow p) :
    ENNReal.ofReal |(spectralDerivative (spectralSplit p X).2 (spectralSplit p X).1).det| *
      nonsingularWishartPDF α (1 : Matrix (Fin p) (Fin p) ℝ) (spectralChart X) =
    ENNReal.ofReal (angularJacobian (spectralSplit p X).2) *
      (ENNReal.ofReal (wishartSpectralConstant p α))⁻¹ *
        ENNReal.ofReal (wishartEigenDensity p α (spectralSplit p X).1) := by
  rw [abs_det_spectralDerivative, abs_of_pos (gapProduct_pos hX.1.1),
    nonsingularWishartPDF_def, spectralChart,
    nonsingularWishartPDFReal_conjugate_diagonal α _ _ hX.1.2,
    wishartEigenDensity_on_chamber α _ hX.1]
  rw [ENNReal.ofReal_mul (angularJacobian_pos _).le,
    ENNReal.ofReal_div_of_pos (wishartSpectralConstant_pos hα),
    ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => laguerreWeight_nonneg p α _)]
  simp only [div_eq_mul_inv]
  ac_rfl

end Wishart.Spectral
end CanonicalSource67

section CanonicalSource68
/- Source: Wishart/DensityNormalization.lean -/



open scoped Classical ENNReal
open MeasureTheory

/-!
# Recovering normalization from a proportional probability density

Spectral change of variables first gives a density up to an angular constant.
An exact proportional-measure identity and probability mass determine the
constant, prove that the raw normalizer is positive and finite, and identify the
whole normalized law. No separate evaluation of a Selberg integral is needed.
-/

namespace WishartVerification

theorem ennreal_factors_ne_zero_top_of_mul_eq {a b c : ℝ≥0∞}
    (h : a * b = c) (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    a ≠ 0 ∧ a ≠ ∞ ∧ b ≠ 0 ∧ b ≠ ∞ := by
  have ha0 : a ≠ 0 := by
    intro ha
    apply hc0
    rw [ha, zero_mul] at h
    exact h.symm
  have hb0 : b ≠ 0 := by
    intro hb
    apply hc0
    rw [hb, mul_zero] at h
    exact h.symm
  have hatop : a ≠ ∞ := by
    intro ha
    apply hctop
    rw [ha, ENNReal.top_mul hb0] at h
    exact h.symm
  have hbtop : b ≠ ∞ := by
    intro hb
    apply hctop
    rw [hb, ENNReal.mul_top ha0] at h
    exact h.symm
  exact ⟨ha0, hatop, hb0, hbtop⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Any exact scalar-density representation of a probability measure forces a
positive finite raw normalizer and gives the usual normalized density. -/
theorem normalizedWeight_eq_of_probability_density
    (κ μ : Measure Ω) [IsProbabilityMeasure κ] (w : Ω → ℝ) (c : ℝ≥0∞)
    (hlaw : κ = c • μ.withDensity (fun x ↦ ENNReal.ofReal (w x))) :
    (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ≠ 0 ∧
    (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ≠ ∞ ∧ κ = normalizedWeight μ w := by
  let Z := ∫⁻ x, ENNReal.ofReal (w x) ∂μ
  have hmass : c * Z = 1 := by
    have h := congrArg (fun ρ : Measure Ω ↦ ρ Set.univ) hlaw
    simpa only [measure_univ, Measure.smul_apply,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul, Z] using h.symm
  obtain ⟨hc0, hctop, hZ0, hZtop⟩ :=
    ennreal_factors_ne_zero_top_of_mul_eq hmass one_ne_zero ENNReal.one_ne_top
  have hc : c = Z⁻¹ := by
    calc
      c = (c * Z) * Z⁻¹ := (ENNReal.mul_inv_cancel_right hZ0 hZtop).symm
      _ = Z⁻¹ := by rw [hmass, one_mul]
  refine ⟨hZ0, hZtop, ?_⟩
  rw [hlaw, hc]
  rfl

/-- The form naturally produced by a spectral chart: a finite positive scalar
times the probability law equals an initially unknown angular scalar times the
raw eigenvalue density. Probability mass proves both angular and eigenvalue
normalizers finite and nonzero, and identifies the complete law. -/
theorem normalizedWeight_eq_of_scaled_probability_density
    (κ μ : Measure Ω) [IsProbabilityMeasure κ] (w : Ω → ℝ)
    (c A : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hlaw : c • κ = A • μ.withDensity (fun x ↦ ENNReal.ofReal (w x))) :
    A ≠ 0 ∧ A ≠ ∞ ∧
    (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ≠ 0 ∧
    (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ≠ ∞ ∧ κ = normalizedWeight μ w := by
  let Z := ∫⁻ x, ENNReal.ofReal (w x) ∂μ
  have hmass : A * Z = c := by
    have h := congrArg (fun ρ : Measure Ω ↦ ρ Set.univ) hlaw
    simpa only [Measure.smul_apply, measure_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      smul_eq_mul, mul_one, Z] using h.symm
  obtain ⟨hA0, hAtop, hZ0, hZtop⟩ :=
    ennreal_factors_ne_zero_top_of_mul_eq hmass hc0 hctop
  have hκ : κ = (c⁻¹ * A) • μ.withDensity (fun x ↦ ENNReal.ofReal (w x)) := by
    calc
      κ = c⁻¹ • (c • κ) := by
        rw [smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]
      _ = (c⁻¹ * A) • μ.withDensity (fun x ↦ ENNReal.ofReal (w x)) := by
        rw [hlaw, smul_smul]
  exact ⟨hA0, hAtop, hZ0, hZtop,
    (normalizedWeight_eq_of_probability_density κ μ w (c⁻¹ * A) hκ).2.2⟩

end WishartVerification
end CanonicalSource68

section CanonicalSource69
/- Source: Wishart/SpectralDensity.lean -/



/-!
# The full real-shape Wishart eigenvalue law

The same chart-restricted integral is evaluated by independent Haar averaging
and by the actual spectral Jacobian. The resulting proportional-measure identity
and probability normalization identify the complete ascending eigenvalue law.
There is no integer-shape restriction, density hypothesis, or unproved Weyl
integration formula among the assumptions.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability
open scoped Matrix.Norms.Operator
open scoped Classical ENNReal

namespace Wishart.Spectral

/-- Exact change of variables for the actual Wishart density on the injective
spectral window. All angular and coordinate normalization factors are retained. -/
theorem setLIntegral_spectralWindow_density {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (f : (Fin p → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ S in spectralWindowImage p, f (ascendingSpectrum S)
      ∂nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ)) =
      (angularMass p * (ENNReal.ofReal (wishartSpectralConstant p α))⁻¹) *
        ∫⁻ lam, ENNReal.ofReal (wishartEigenDensity p α lam) * f lam := by
  let K : ℝ≥0∞ := (ENNReal.ofReal (wishartSpectralConstant p α))⁻¹
  let a : Skew p → ℝ≥0∞ := fun S => ENNReal.ofReal (angularJacobian S)
  let q : (Fin p → ℝ) → ℝ≥0∞ :=
    fun lam => ENNReal.ofReal (wishartEigenDensity p α lam) * f lam
  let F : (Fin p → ℝ) × Skew p → ℝ≥0∞ := fun z => a z.2 * K * q z.1
  have ha : Measurable a := (continuous_angularJacobian p).measurable.ennreal_ofReal
  have hq : Measurable q := (measurable_wishartEigenDensity p α).ennreal_ofReal.mul hf
  have hF : Measurable F := ((ha.comp measurable_snd).mul_const K).mul
    (hq.comp measurable_fst)
  have hq_support : Function.support q ⊆ positiveChamber p := by
    intro lam hlam
    by_contra hnot
    apply hlam
    simp only [q, wishartEigenDensity_off_chamber α lam hnot,
      ENNReal.ofReal_zero, zero_mul]
  have hq_int : (∫⁻ lam in positiveChamber p, q lam) = ∫⁻ lam, q lam :=
    setLIntegral_eq_of_support_subset hq_support
  have hsplit :
      (∫⁻ X in spectralWindow p, F (spectralSplit p X) ∂symmetricLebesgue p) =
        angularMass p * K * ∫⁻ lam, q lam := by
    rw [setLIntegral_spectralSplit p F hF,
      setLIntegral_prod F hF.aemeasurable]
    have hinner (lam : Fin p → ℝ) :
        (∫⁻ S in cayleyWindow p, F (lam, S) ∂angularLebesgue p) =
          ((∫⁻ S in cayleyWindow p, a S ∂angularLebesgue p) * K) * q lam := by
      simp only [F, mul_assoc]
      rw [lintegral_mul_const _ ha]
    simp_rw [hinner]
    rw [lintegral_const_mul _ hq, hq_int]
    change coordinateHaarFactor p *
        (((∫⁻ S in cayleyWindow p, a S ∂angularLebesgue p) * K) * ∫⁻ lam, q lam) = _
    simp only [angularMass, a, mul_assoc]
  calc
    (∫⁻ S in spectralWindowImage p, f (ascendingSpectrum S)
      ∂nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ)) =
      ∫⁻ S in spectralWindowImage p,
        nonsingularWishartPDF α (1 : Matrix (Fin p) (Fin p) ℝ) S *
          f (ascendingSpectrum S) ∂symmetricLebesgue p := by
      rw [nonsingularWishartMeasure_of_posDef Matrix.PosDef.one hα]
      simpa only [Pi.mul_apply] using
        (setLIntegral_withDensity_eq_setLIntegral_mul (symmetricLebesgue p)
          (f := nonsingularWishartPDF α (1 : Matrix (Fin p) (Fin p) ℝ))
          (g := fun S => f (ascendingSpectrum S))
          (measurable_nonsingularWishartPDF _ _)
          (by simpa only [Function.comp_def] using
            hf.comp (continuous_ascendingSpectrum p).measurable)
          (measurableSet_spectralWindowImage p))
    _ = ∫⁻ X in spectralWindow p,
        ENNReal.ofReal |(spectralDerivative (spectralSplit p X).2 (spectralSplit p X).1).det| *
          (nonsingularWishartPDF α (1 : Matrix (Fin p) (Fin p) ℝ) (spectralChart X) *
            f (ascendingSpectrum (spectralChart X))) ∂symmetricLebesgue p :=
      lintegral_image_eq_lintegral_abs_det_fderiv_mul (symmetricLebesgue p)
        (isOpen_spectralWindow p).measurableSet
        (fun X _ => (hasFDerivAt_spectralChart X).hasFDerivWithinAt)
        (spectralChart_injOn_window p) _
    _ = ∫⁻ X in spectralWindow p, F (spectralSplit p X) ∂symmetricLebesgue p := by
      apply setLIntegral_congr_fun (isOpen_spectralWindow p).measurableSet
      intro X hX
      dsimp only
      rw [← mul_assoc, wishart_spectral_density_factor hα X hX]
      have hspec : ascendingSpectrum (spectralChart X) = (spectralSplit p X).1 :=
        ascendingSpectrum_conjugate_diagonal _ _ hX.1.1
      rw [hspec]
      simp only [F, a, K, q, mul_assoc]
    _ = _ := hsplit

/-- The proportional density identity is an equality of complete measures,
not only a finite collection of moments or test functions. -/
theorem identityEigenLaw_scaled_density {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    frameWindowMass p • identityEigenLaw p α =
      (angularMass p * (ENNReal.ofReal (wishartSpectralConstant p α))⁻¹) •
        (volume : Measure (Fin p → ℝ)).withDensity
          (fun lam => ENNReal.ofReal (wishartEigenDensity p α lam)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_smul_measure, lintegral_smul_measure]
  change frameWindowMass p * (∫⁻ lam, f lam ∂identityEigenLaw p α) = _
  rw [← setLIntegral_spectralWindow_wishart hα f hf,
    setLIntegral_spectralWindow_density hα f hf,
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_wishartEigenDensity p α).ennreal_ofReal hf]
  rfl

/-- The raw beta-one Laguerre density has a positive finite integral, and its
normalization is exactly the ascending spectrum of the real-shape Wishart law. -/
theorem identityEigenLaw_normalized_density {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    (∫⁻ lam : Fin p → ℝ, ENNReal.ofReal (wishartEigenDensity p α lam)) ≠ 0 ∧
    (∫⁻ lam : Fin p → ℝ, ENNReal.ofReal (wishartEigenDensity p α lam)) ≠ ∞ ∧
    identityEigenLaw p α =
      WishartVerification.normalizedWeight volume (wishartEigenDensity p α) := by
  letI := identityEigenLaw_isProbability hα
  obtain ⟨_, _, hZ0, hZtop, hlaw⟩ :=
    WishartVerification.normalizedWeight_eq_of_scaled_probability_density
      (identityEigenLaw p α) volume (wishartEigenDensity p α)
      (frameWindowMass p)
      (angularMass p * (ENNReal.ofReal (wishartSpectralConstant p α))⁻¹)
      (frameWindowMass_pos p).ne' (frameWindowMass_ne_top p)
      (identityEigenLaw_scaled_density hα)
  exact ⟨hZ0, hZtop, hlaw⟩

/-- Exact independent spectral representation with the normalized ordered
Vandermonde density and normalized Haar frame. -/
theorem wishart_haar_laguerre_representation {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ((haarProb (Orth p)).prod
      (WishartVerification.normalizedWeight volume (wishartEigenDensity p α))).map
        (fun z => conjugate z.1 (diagonalSym z.2)) =
      nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ) := by
  rw [← (identityEigenLaw_normalized_density hα).2.2]
  exact haar_ascending_spectral_reconstruction hα

/-- The normalized Laguerre law is supported on the exact positive ascending
chamber used in Lemma 2.1. -/
theorem ae_laguerreLaw_mem_chamber {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ∀ᵐ lam ∂WishartVerification.normalizedWeight volume (wishartEigenDensity p α),
      lam ∈ positiveChamber p := by
  rw [← (identityEigenLaw_normalized_density hα).2.2]
  exact ae_identityEigenLaw_mem_chamber hα

theorem laguerreLaw_isProbability {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    IsProbabilityMeasure
      (WishartVerification.normalizedWeight volume (wishartEigenDensity p α)) := by
  rw [← (identityEigenLaw_normalized_density hα).2.2]
  exact identityEigenLaw_isProbability hα

/-- The same independent representation in eigenvalue-first order. -/
theorem wishart_laguerre_haar_representation {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ((WishartVerification.normalizedWeight volume (wishartEigenDensity p α)).prod
      (haarProb (Orth p))).map
        (fun z => conjugate z.2 (diagonalSym z.1)) =
      nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ) := by
  letI := laguerreLaw_isProbability hα
  have hb : Measurable (fun z : Orth p × (Fin p → ℝ) =>
      conjugate z.1 (diagonalSym z.2)) :=
    (continuous_conjugate p).measurable.comp
      (measurable_fst.prodMk ((continuous_diagonalSym p).measurable.comp measurable_snd))
  have h := wishart_haar_laguerre_representation hα
  rw [← Measure.prod_swap
    (μ := WishartVerification.normalizedWeight volume (wishartEigenDensity p α))
    (ν := haarProb (Orth p)), Measure.map_map hb measurable_swap] at h
  exact h

end Wishart.Spectral
end CanonicalSource69

section CanonicalSource70
/- Source: Wishart/FourFunctionsIntegral.lean -/



open scoped Classical ENNReal

/-!
# The continuous four-functions theorem

The random-grid argument is more general than association: it transfers the
pointwise four-functions lattice inequality to product integrals. This form also
compares two different conditional densities and is used for strictness.
-/

open MeasureTheory Filter
open scoped Topology

namespace WishartVerification

variable {ι : Type*} [Fintype ι]

theorem continuous_four_functions_bounded
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A B C D : (ι → ℝ) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hAm : Measurable A) (hBm : Measurable B) (hCm : Measurable C) (hDm : Measurable D)
    (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ x, 0 ≤ B x)
    (hC0 : ∀ x, 0 ≤ C x) (hD0 : ∀ x, 0 ≤ D x)
    (hAK : ∀ x, A x ≤ K) (hBK : ∀ x, B x ≤ K)
    (hCK : ∀ x, C x ≤ K) (hDK : ∀ x, D x ≤ K)
    (hcross : ∀ x y, A x * B y ≤ C (x ⊓ y) * D (x ⊔ y)) :
    (∫ x, A x ∂Measure.pi μ) * (∫ x, B x ∂Measure.pi μ) ≤
      (∫ x, C x ∂Measure.pi μ) * (∫ x, D x ∂Measure.pi μ) := by
  apply integral_four_functions_of_finite_grid μ A B C D K hK hAm hBm hCm hDm
    hA0 hB0 hC0 hD0 hAK hBK hCK hDK
  intro N ω
  simpa only [gridSum, sampledPoint_gridPoint] using
    finite_grid_four_functions (fun i j ↦ ω (i, j)) A B C D hA0 hB0 hC0 hD0 hcross

theorem continuous_four_functions_bounded_lintegral
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A B C D : (ι → ℝ) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hAm : Measurable A) (hBm : Measurable B) (hCm : Measurable C) (hDm : Measurable D)
    (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ x, 0 ≤ B x)
    (hC0 : ∀ x, 0 ≤ C x) (hD0 : ∀ x, 0 ≤ D x)
    (hAK : ∀ x, A x ≤ K) (hBK : ∀ x, B x ≤ K)
    (hCK : ∀ x, C x ≤ K) (hDK : ∀ x, D x ≤ K)
    (hcross : ∀ x y, A x * B y ≤ C (x ⊓ y) * D (x ⊔ y)) :
    (∫⁻ x, ENNReal.ofReal (A x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (B x) ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (C x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (D x) ∂Measure.pi μ) := by
  have hAi := integrable_of_nonneg_bounded (Measure.pi μ) A K hAm hA0 hAK
  have hBi := integrable_of_nonneg_bounded (Measure.pi μ) B K hBm hB0 hBK
  have hCi := integrable_of_nonneg_bounded (Measure.pi μ) C K hCm hC0 hCK
  have hDi := integrable_of_nonneg_bounded (Measure.pi μ) D K hDm hD0 hDK
  rw [← ofReal_integral_eq_lintegral_ofReal hAi (ae_of_all _ hA0),
    ← ofReal_integral_eq_lintegral_ofReal hBi (ae_of_all _ hB0),
    ← ofReal_integral_eq_lintegral_ofReal hCi (ae_of_all _ hC0),
    ← ofReal_integral_eq_lintegral_ofReal hDi (ae_of_all _ hD0),
    ← ENNReal.ofReal_mul (integral_nonneg hA0),
    ← ENNReal.ofReal_mul (integral_nonneg hC0)]
  exact ENNReal.ofReal_le_ofReal
    (continuous_four_functions_bounded μ A B C D K hK hAm hBm hCm hDm
      hA0 hB0 hC0 hD0 hAK hBK hCK hDK hcross)

/-- The continuous four-functions theorem for explicit monotone bounded
approximants. This is an analytic closure theorem; the lattice condition is
verified at every approximating level. -/
theorem continuous_four_functions_of_monotone_approximation
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A B C D : (ι → ℝ) → ℝ)
    (An Bn Cn Dn : ℕ → (ι → ℝ) → ℝ) (bound : ℕ → ℝ)
    (hAnm : ∀ n, Measurable (An n)) (hBnm : ∀ n, Measurable (Bn n))
    (hCnm : ∀ n, Measurable (Cn n)) (hDnm : ∀ n, Measurable (Dn n))
    (hAn0 : ∀ n x, 0 ≤ An n x) (hBn0 : ∀ n x, 0 ≤ Bn n x)
    (hCn0 : ∀ n x, 0 ≤ Cn n x) (hDn0 : ∀ n x, 0 ≤ Dn n x)
    (hbound : ∀ n, 0 ≤ bound n)
    (hAnbound : ∀ n x, An n x ≤ bound n) (hBnbound : ∀ n x, Bn n x ≤ bound n)
    (hCnbound : ∀ n x, Cn n x ≤ bound n) (hDnbound : ∀ n x, Dn n x ≤ bound n)
    (hcross : ∀ n x y, An n x * Bn n y ≤ Cn n (x ⊓ y) * Dn n (x ⊔ y))
    (hAnmono : ∀ x, Monotone fun n ↦ An n x) (hBnmono : ∀ x, Monotone fun n ↦ Bn n x)
    (hCnmono : ∀ x, Monotone fun n ↦ Cn n x) (hDnmono : ∀ x, Monotone fun n ↦ Dn n x)
    (hAnlim : ∀ x, Tendsto (fun n ↦ An n x) atTop (𝓝 (A x)))
    (hBnlim : ∀ x, Tendsto (fun n ↦ Bn n x) atTop (𝓝 (B x)))
    (hCnlim : ∀ x, Tendsto (fun n ↦ Cn n x) atTop (𝓝 (C x)))
    (hDnlim : ∀ x, Tendsto (fun n ↦ Dn n x) atTop (𝓝 (D x))) :
    (∫⁻ x, ENNReal.ofReal (A x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (B x) ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (C x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (D x) ∂Measure.pi μ) := by
  let a (n : ℕ) := ∫⁻ x, ENNReal.ofReal (An n x) ∂Measure.pi μ
  let b (n : ℕ) := ∫⁻ x, ENNReal.ofReal (Bn n x) ∂Measure.pi μ
  have hasup : (∫⁻ x, ENNReal.ofReal (A x) ∂Measure.pi μ) = ⨆ n, a n :=
    lintegral_ofReal_eq_iSup_of_monotone (Measure.pi μ) An A hAnm hAnmono hAnlim
  have hbsup : (∫⁻ x, ENNReal.ofReal (B x) ∂Measure.pi μ) = ⨆ n, b n :=
    lintegral_ofReal_eq_iSup_of_monotone (Measure.pi μ) Bn B hBnm hBnmono hBnlim
  have hamono : Monotone a := fun n m hnm ↦ lintegral_mono fun x ↦
    ENNReal.ofReal_le_ofReal (hAnmono x hnm)
  have hbmono : Monotone b := fun n m hnm ↦ lintegral_mono fun x ↦
    ENNReal.ofReal_le_ofReal (hBnmono x hnm)
  have hfinite (n : ℕ) : a n * b n ≤
      (∫⁻ x, ENNReal.ofReal (C x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (D x) ∂Measure.pi μ) := by
    have h := continuous_four_functions_bounded_lintegral μ (An n) (Bn n) (Cn n) (Dn n)
      (bound n) (hbound n) (hAnm n) (hBnm n) (hCnm n) (hDnm n)
      (hAn0 n) (hBn0 n) (hCn0 n) (hDn0 n)
      (hAnbound n) (hBnbound n) (hCnbound n) (hDnbound n) (hcross n)
    apply h.trans
    apply mul_le_mul'
    · exact lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal
        ((hCnmono x).ge_of_tendsto (hCnlim x) n)
    · exact lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal
        ((hDnmono x).ge_of_tendsto (hDnlim x) n)
  rw [hasup, hbsup, ENNReal.iSup_mul]
  simp_rw [ENNReal.mul_iSup]
  apply iSup_le
  intro n
  apply iSup_le
  intro m
  exact (mul_le_mul' (hamono (le_max_left n m)) (hbmono (le_max_right n m))).trans
    (hfinite (max n m))

end WishartVerification
end CanonicalSource70

section CanonicalSource71
/- Source: Wishart/SliceHolley.lean -/



open scoped Classical ENNReal

/-!
# Stochastic ordering of successive-coordinate slices

Supporting comparison for the strictness argument. The mixed Holley inequality for two slices
is a direct consequence of the full lattice inequality, so no pointwise
finiteness of all conditional normalizers is asserted here.
-/

open MeasureTheory Filter
open scoped Topology

namespace WishartVerification

variable {n : ℕ}

/-- Nondependent real specialization of `Fin.snoc`, with its target made explicit. -/
def appendLast (x : Fin n → ℝ) (t : ℝ) : Fin (n + 1) → ℝ := Fin.snoc x t

@[simp] theorem appendLast_castSucc (x : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    appendLast x t i.castSucc = x i := by
  simpa only [appendLast] using (Fin.snoc_castSucc (α := fun _ : Fin (n + 1) ↦ ℝ) t x i)

@[simp] theorem appendLast_last (x : Fin n → ℝ) (t : ℝ) :
    appendLast x t (Fin.last n) = t := by
  simpa only [appendLast] using (Fin.snoc_last (α := fun _ : Fin (n + 1) ↦ ℝ) t x)

theorem appendLast_le {x y : Fin n → ℝ} {s t : ℝ}
    (hxy : x ≤ y) (hst : s ≤ t) : appendLast x s ≤ appendLast y t := by
  intro i
  cases i using Fin.lastCases with
  | last => simpa only [appendLast_last] using hst
  | cast i => simpa only [appendLast_castSucc] using hxy i

theorem snoc_inf (x y : Fin n → ℝ) (s t : ℝ) :
    appendLast x s ⊓ appendLast y t = appendLast (x ⊓ y) (s ⊓ t) := by
  funext i
  cases i using Fin.lastCases <;> simp

theorem snoc_sup (x y : Fin n → ℝ) (s t : ℝ) :
    appendLast x s ⊔ appendLast y t = appendLast (x ⊔ y) (s ⊔ t) := by
  funext i
  cases i using Fin.lastCases <;> simp

theorem snoc_measurable (t : ℝ) : Measurable (fun x : Fin n → ℝ ↦ appendLast x t) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa using (measurable_const : Measurable (fun _ : Fin n → ℝ ↦ t))
  · simpa using (measurable_pi_apply j : Measurable (fun x : Fin n → ℝ ↦ x j))

theorem snoc_uncurry_measurable :
    Measurable (fun p : (Fin n → ℝ) × ℝ ↦ appendLast p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa using (measurable_snd : Measurable (fun p : (Fin n → ℝ) × ℝ ↦ p.2))
  · simpa only [appendLast_castSucc, Function.comp_def] using (measurable_pi_apply j).comp
      (measurable_fst : Measurable (fun p : (Fin n → ℝ) × ℝ ↦ p.1))

theorem slice_mixed_lattice
    (W : (Fin (n + 1) → ℝ) → ℝ)
    (hW : ∀ x y, W x * W y ≤ W (x ⊓ y) * W (x ⊔ y))
    (s t : ℝ) (hst : s ≤ t) (x y : Fin n → ℝ) :
    W (appendLast x s) * W (appendLast y t) ≤
      W (appendLast (x ⊓ y) s) * W (appendLast (x ⊔ y) t) := by
  simpa only [snoc_inf, snoc_sup, inf_eq_left.mpr hst, sup_eq_right.mpr hst] using
    hW (appendLast x s) (appendLast y t)

/-- Unnormalized stochastic ordering of two admissible slices. The test need
only be monotone across their actual positive supports. -/
theorem slice_holley_lintegral
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (W : (Fin (n + 1) → ℝ) → ℝ)
    (Wn : ℕ → (Fin (n + 1) → ℝ) → ℝ) (bound : ℕ → ℝ)
    (hWnm : ∀ k, Measurable (Wn k))
    (hWn0 : ∀ k x, 0 ≤ Wn k x) (hbound : ∀ k, 1 ≤ bound k)
    (hWnbound : ∀ k x, Wn k x ≤ bound k)
    (hWnl : ∀ k x y, Wn k x * Wn k y ≤ Wn k (x ⊓ y) * Wn k (x ⊔ y))
    (hWnmono : ∀ x, Monotone fun k ↦ Wn k x)
    (hWnlim : ∀ x, Tendsto (fun k ↦ Wn k x) atTop (𝓝 (W x)))
    (s t : ℝ) (hst : s ≤ t)
    (f : (Fin n → ℝ) → ℝ) (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : ∀ x y, 0 < W (appendLast x s) → 0 < W (appendLast y t) → x ≤ y → f x ≤ f y) :
    (∫⁻ x, ENNReal.ofReal (W (appendLast x s) * f x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (W (appendLast x t)) ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (W (appendLast x s)) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (W (appendLast x t) * f x) ∂Measure.pi μ) := by
  have hWnle (k : ℕ) (x) : Wn k x ≤ W x :=
    (hWnmono x).ge_of_tendsto (hWnlim x) k
  let R (k : ℕ) : ℝ := (k : ℝ) + 1
  have hR (k : ℕ) : 1 ≤ R k := by
    dsimp [R]
    exact le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hM0 (k : ℕ) : 0 ≤ bound k := zero_le_one.trans (hbound k)
  have hWnmul (k : ℕ) (u : ℝ) :
      Measurable (fun x : Fin n → ℝ ↦ Wn k (appendLast x u) * testCap k f x) :=
    ((hWnm k).comp (snoc_measurable u)).mul (hfm.min measurable_const)
  have hWnprodMono (x : Fin n → ℝ) (u : ℝ) :
      Monotone fun k ↦ Wn k (appendLast x u) * testCap k f x := by
    intro k l hkl
    exact mul_le_mul (hWnmono _ hkl) (testCap_mono_index f x hkl)
      (testCap_nonneg k f hf0 x) (hWn0 l _)
  apply continuous_four_functions_of_monotone_approximation μ
    (fun x ↦ W (appendLast x s) * f x) (fun x ↦ W (appendLast x t))
    (fun x ↦ W (appendLast x s)) (fun x ↦ W (appendLast x t) * f x)
    (fun k x ↦ Wn k (appendLast x s) * testCap k f x)
    (fun k x ↦ Wn k (appendLast x t)) (fun k x ↦ Wn k (appendLast x s))
    (fun k x ↦ Wn k (appendLast x t) * testCap k f x)
    (fun k ↦ bound k * R k)
  · exact fun k ↦ hWnmul k s
  · exact fun k ↦ (hWnm k).comp (snoc_measurable t)
  · exact fun k ↦ (hWnm k).comp (snoc_measurable s)
  · exact fun k ↦ hWnmul k t
  · exact fun k x ↦ mul_nonneg (hWn0 k _) (testCap_nonneg k f hf0 x)
  · exact fun k x ↦ hWn0 k _
  · exact fun k x ↦ hWn0 k _
  · exact fun k x ↦ mul_nonneg (hWn0 k _) (testCap_nonneg k f hf0 x)
  · exact fun k ↦ mul_nonneg (hM0 k) (zero_le_one.trans (hR k))
  · intro k x
    exact mul_le_mul (hWnbound k _) (min_le_right _ _) (testCap_nonneg k f hf0 x) (hM0 k)
  · intro k x
    exact (hWnbound k _).trans (le_mul_of_one_le_right (hM0 k) (hR k))
  · intro k x
    exact (hWnbound k _).trans (le_mul_of_one_le_right (hM0 k) (hR k))
  · intro k x
    exact mul_le_mul (hWnbound k _) (min_le_right _ _) (testCap_nonneg k f hf0 x) (hM0 k)
  · intro k x y
    have hmix := slice_mixed_lattice (Wn k) (hWnl k) s t hst x y
    by_cases hx : Wn k (appendLast x s) = 0
    · simp only [hx, zero_mul]
      exact mul_nonneg (hWn0 k _) (mul_nonneg (hWn0 k _) (testCap_nonneg k f hf0 _))
    by_cases hy : Wn k (appendLast y t) = 0
    · simp only [hy, mul_zero]
      exact mul_nonneg (hWn0 k _) (mul_nonneg (hWn0 k _) (testCap_nonneg k f hf0 _))
    have hxpos : 0 < Wn k (appendLast x s) := lt_of_le_of_ne (hWn0 k _) (Ne.symm hx)
    have hypos : 0 < Wn k (appendLast y t) := lt_of_le_of_ne (hWn0 k _) (Ne.symm hy)
    have hsup : 0 < Wn k (appendLast (x ⊔ y) t) :=
      pos_of_mul_pos_right ((mul_pos hxpos hypos).trans_le hmix) (hWn0 k _)
    have hft : testCap k f x ≤ testCap k f (x ⊔ y) := min_le_min_right _
      (hfi x _ (hxpos.trans_le (hWnle k _)) (hsup.trans_le (hWnle k _)) le_sup_left)
    calc
      (Wn k (appendLast x s) * testCap k f x) * Wn k (appendLast y t) =
          (Wn k (appendLast x s) * Wn k (appendLast y t)) * testCap k f x := by ring
      _ ≤ (Wn k (appendLast (x ⊓ y) s) * Wn k (appendLast (x ⊔ y) t)) *
          testCap k f (x ⊔ y) := mul_le_mul hmix hft (testCap_nonneg k f hf0 x)
            (mul_nonneg (hWn0 k _) (hWn0 k _))
      _ = Wn k (appendLast (x ⊓ y) s) *
          (Wn k (appendLast (x ⊔ y) t) * testCap k f (x ⊔ y)) := by ring
  · exact fun x ↦ hWnprodMono x s
  · exact fun x ↦ hWnmono _
  · exact fun x ↦ hWnmono _
  · exact fun x ↦ hWnprodMono x t
  · exact fun x ↦ (hWnlim _).mul (testCap_tendsto f x)
  · exact fun x ↦ hWnlim _
  · exact fun x ↦ hWnlim _
  · exact fun x ↦ (hWnlim _).mul (testCap_tendsto f x)

end WishartVerification
end CanonicalSource71

section CanonicalSource72
/- Source: Wishart/ConditionalDensity.lean -/



open scoped Classical ENNReal

/-!
# Explicit conditional means for a product density

Conditional normalizers need only be finite almost everywhere. This file works
with the actual fiber integrals and records the exceptional-set arguments
needed when applying strict scalar covariance to those means.
-/

open MeasureTheory

namespace WishartVerification

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integral_withDensity_ofReal (μ : Measure Ω) (w f : Ω → ℝ)
    (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) :
    (∫ x, f x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (w x))) =
      ∫ x, w x * f x ∂μ := by
  simpa only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul] using
    integral_withDensity_eq_integral_toReal_smul hwm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) f

theorem integrable_withDensity_ofReal_iff (μ : Measure Ω) (w f : Ω → ℝ)
    (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) :
    Integrable f (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))) ↔
      Integrable (fun x ↦ w x * f x) μ := by
  simpa only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' hwm.ennreal_ofReal
      (ae_of_all μ fun _ ↦ ENNReal.ofReal_lt_top) (g := f))

theorem normalizedWeight_integral (μ : Measure Ω) (w f : Ω → ℝ)
    (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hwi : Integrable w μ) :
    (∫ x, f x ∂normalizedWeight μ w) = (∫ x, w x * f x ∂μ) / (∫ x, w x ∂μ) := by
  rw [normalizedWeight, integral_smul_measure,
    integral_withDensity_ofReal μ w f hwm hw0,
    ENNReal.toReal_inv, ← ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all _ hw0),
    ENNReal.toReal_ofReal (integral_nonneg hw0)]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem integrable_normalizedWeight (μ : Measure Ω) (w f : Ω → ℝ)
    (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hZ0 : (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ≠ 0)
    (hfi : Integrable (fun x ↦ w x * f x) μ) :
    Integrable f (normalizedWeight μ w) := by
  exact ((integrable_withDensity_ofReal_iff μ w f hwm hw0).mpr hfi).smul_measure
    (ENNReal.inv_ne_top.mpr hZ0)

/-- The fiber normalizer is real-valued. On the null set of nonintegrable
fibers, the Bochner convention gives zero; no pointwise finiteness is claimed. -/
noncomputable def sliceNorm (μ : Measure Ω) (W : Ω × ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, W (x, t) ∂μ

noncomputable def sliceMoment (μ : Measure Ω) (W f : Ω × ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, W (x, t) * f (x, t) ∂μ

noncomputable def sliceMean (μ : Measure Ω) (W f : Ω × ℝ → ℝ) (t : ℝ) : ℝ :=
  sliceMoment μ W f t / sliceNorm μ W t

noncomputable def densityMarginal (μ : Measure Ω) (ν : Measure ℝ) (W : Ω × ℝ → ℝ) :
    Measure ℝ := ν.withDensity (fun t ↦ ENNReal.ofReal (sliceNorm μ W t))

theorem sliceNorm_measurable (μ : Measure Ω) [SFinite μ] (W : Ω × ℝ → ℝ)
    (hWm : Measurable W) : Measurable (sliceNorm μ W) :=
  hWm.stronglyMeasurable.integral_prod_left'.measurable

theorem sliceMoment_measurable (μ : Measure Ω) [SFinite μ] (W f : Ω × ℝ → ℝ)
    (hWm : Measurable W) (hfm : Measurable f) : Measurable (sliceMoment μ W f) :=
  (hWm.mul hfm).stronglyMeasurable.integral_prod_left'.measurable

theorem sliceMean_measurable (μ : Measure Ω) [SFinite μ] (W f : Ω × ℝ → ℝ)
    (hWm : Measurable W) (hfm : Measurable f) : Measurable (sliceMean μ W f) :=
  (sliceMoment_measurable μ W f hWm hfm).div (sliceNorm_measurable μ W hWm)

theorem sliceNorm_nonneg (μ : Measure Ω) (W : Ω × ℝ → ℝ)
    (hW0 : ∀ p, 0 ≤ W p) (t : ℝ) : 0 ≤ sliceNorm μ W t :=
  integral_nonneg fun x ↦ hW0 (x, t)

theorem sliceMean_nonneg (μ : Measure Ω) (W f : Ω × ℝ → ℝ)
    (hW0 : ∀ p, 0 ≤ W p) (hf0 : ∀ p, 0 ≤ f p) (t : ℝ) :
    0 ≤ sliceMean μ W f t :=
  div_nonneg (integral_nonneg fun x ↦ mul_nonneg (hW0 (x, t)) (hf0 (x, t)))
    (sliceNorm_nonneg μ W hW0 t)

theorem densityMarginal_absolutelyContinuous (μ : Measure Ω) (ν : Measure ℝ)
    (W : Ω × ℝ → ℝ) : densityMarginal μ ν W ≪ ν :=
  withDensity_absolutelyContinuous _ _

instance densityMarginal_nullSingleton (μ : Measure Ω) (ν : Measure ℝ)
    [NullSingletonClass ν] (W : Ω × ℝ → ℝ) :
    NullSingletonClass (densityMarginal μ ν W) := by
  unfold densityMarginal
  infer_instance

theorem densityMarginal_probability (μ : Measure Ω) [SFinite μ]
    (ν : Measure ℝ) [SFinite ν] (W : Ω × ℝ → ℝ)
    (hW0 : ∀ p, 0 ≤ W p) (hWi : Integrable W (μ.prod ν))
    (hWone : ∫ p, W p ∂μ.prod ν = 1) :
    IsProbabilityMeasure (densityMarginal μ ν W) := by
  constructor
  rw [densityMarginal, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ t, ENNReal.ofReal (∫ x, W (x, t) ∂μ) ∂ν) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal hWi.integral_prod_right
      (ae_of_all _ fun t ↦ integral_nonneg fun x ↦ hW0 (x, t)),
    ← integral_prod_symm W hWi, hWone, ENNReal.ofReal_one]

theorem densityMarginal_sliceNorm_pos_ae (μ : Measure Ω) [SFinite μ]
    (ν : Measure ℝ) (W : Ω × ℝ → ℝ) (hWm : Measurable W) :
    ∀ᵐ t ∂densityMarginal μ ν W, 0 < sliceNorm μ W t := by
  rw [densityMarginal, ae_withDensity_iff (sliceNorm_measurable μ W hWm).ennreal_ofReal]
  exact ae_of_all _ fun t ht ↦ lt_of_not_ge fun h ↦ ht (ENNReal.ofReal_eq_zero.mpr h)

theorem sliceMoment_eq_zero_of_norm_eq_zero (μ : Measure Ω) (W f : Ω × ℝ → ℝ)
    (hW0 : ∀ p, 0 ≤ W p) (t : ℝ) (hWt : Integrable (fun x ↦ W (x, t)) μ)
    (hZ : sliceNorm μ W t = 0) : sliceMoment μ W f t = 0 := by
  have hzero : (fun x ↦ W (x, t)) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x ↦ hW0 (x, t)) hWt).mp hZ
  unfold sliceMoment
  calc
    (∫ x, W (x, t) * f (x, t) ∂μ) = ∫ _x : Ω, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hzero] with x hx
      simp only [Pi.zero_apply] at hx
      rw [hx, zero_mul]
    _ = 0 := integral_zero _ _

theorem sliceNorm_mul_sliceMean (μ : Measure Ω) (W f : Ω × ℝ → ℝ)
    (hW0 : ∀ p, 0 ≤ W p) (t : ℝ) (hWt : Integrable (fun x ↦ W (x, t)) μ) :
    sliceNorm μ W t * sliceMean μ W f t = sliceMoment μ W f t := by
  by_cases hZ : sliceNorm μ W t = 0
  · rw [hZ, zero_mul, sliceMoment_eq_zero_of_norm_eq_zero μ W f hW0 t hWt hZ]
  · simpa only [sliceMean, mul_comm] using div_mul_cancel₀ (sliceMoment μ W f t) hZ

theorem sliceMean_integrable (μ : Measure Ω) [SFinite μ]
    (ν : Measure ℝ) [SFinite ν] (W f : Ω × ℝ → ℝ)
    (hWm : Measurable W) (hW0 : ∀ p, 0 ≤ W p)
    (hWi : Integrable W (μ.prod ν)) (hWfi : Integrable (fun p ↦ W p * f p) (μ.prod ν)) :
    Integrable (sliceMean μ W f) (densityMarginal μ ν W) := by
  apply (integrable_withDensity_ofReal_iff ν (sliceNorm μ W) (sliceMean μ W f)
    (sliceNorm_measurable μ W hWm) (sliceNorm_nonneg μ W hW0)).mpr
  apply hWfi.integral_prod_right.congr
  filter_upwards [hWi.prod_left_ae] with t ht
  exact (sliceNorm_mul_sliceMean μ W f hW0 t ht).symm

theorem integral_sliceMean (μ : Measure Ω) [SFinite μ]
    (ν : Measure ℝ) [SFinite ν] (W f : Ω × ℝ → ℝ)
    (hWm : Measurable W) (hW0 : ∀ p, 0 ≤ W p)
    (hWi : Integrable W (μ.prod ν)) (hWfi : Integrable (fun p ↦ W p * f p) (μ.prod ν)) :
    (∫ t, sliceMean μ W f t ∂densityMarginal μ ν W) =
      ∫ p, W p * f p ∂μ.prod ν := by
  rw [densityMarginal, integral_withDensity_ofReal ν (sliceNorm μ W) (sliceMean μ W f)
    (sliceNorm_measurable μ W hWm) (sliceNorm_nonneg μ W hW0),
    integral_prod_symm _ hWfi]
  apply integral_congr_ae
  filter_upwards [hWi.prod_left_ae] with t ht
  exact sliceNorm_mul_sliceMean μ W f hW0 t ht

/-- On every integrable positive fiber the explicit mean is the expectation
under its actual normalized density. -/
theorem sliceMean_eq_integral_normalizedWeight (μ : Measure Ω) (W f : Ω × ℝ → ℝ)
    (hWm : Measurable W) (hW0 : ∀ p, 0 ≤ W p) (t : ℝ)
    (hWt : Integrable (fun x ↦ W (x, t)) μ) :
    sliceMean μ W f t =
      ∫ x, f (x, t) ∂normalizedWeight μ (fun x ↦ W (x, t)) := by
  exact (normalizedWeight_integral μ (fun x ↦ W (x, t)) (fun x ↦ f (x, t))
    (hWm.comp measurable_prodMk_right) (fun x ↦ hW0 (x, t)) hWt).symm

/-- Conditional Jensen for the square, proved directly from the two-point
covariance identity. All fiber finiteness assumptions are explicit. -/
theorem sliceMean_sq_le (μ : Measure Ω) (W f : Ω × ℝ → ℝ)
    (hWm : Measurable W) (hW0 : ∀ p, 0 ≤ W p) (t : ℝ)
    (hWt : Integrable (fun x ↦ W (x, t)) μ)
    (hWft : Integrable (fun x ↦ W (x, t) * f (x, t)) μ)
    (hWf2t : Integrable (fun x ↦ W (x, t) * f (x, t) ^ 2) μ)
    (hZpos : 0 < sliceNorm μ W t) :
    (sliceMean μ W f t) ^ 2 ≤ sliceMean μ W (fun p ↦ f p ^ 2) t := by
  let κ := normalizedWeight μ (fun x ↦ W (x, t))
  have hZ : (∫⁻ x, ENNReal.ofReal (W (x, t)) ∂μ) =
      ENNReal.ofReal (sliceNorm μ W t) :=
    (ofReal_integral_eq_lintegral_ofReal hWt (ae_of_all _ fun x ↦ hW0 (x, t))).symm
  have hZ0 : (∫⁻ x, ENNReal.ofReal (W (x, t)) ∂μ) ≠ 0 := by
    rw [hZ]
    exact (ENNReal.ofReal_pos.mpr hZpos).ne'
  have hZtop : (∫⁻ x, ENNReal.ofReal (W (x, t)) ∂μ) ≠ ∞ := by
    rw [hZ]
    exact ENNReal.ofReal_ne_top
  letI : IsProbabilityMeasure κ := normalizedWeight_probability μ _ hZ0 hZtop
  have hfi : Integrable (fun x ↦ f (x, t)) κ :=
    integrable_normalizedWeight μ _ _ (hWm.comp measurable_prodMk_right)
      (fun x ↦ hW0 (x, t)) hZ0 hWft
  have hf2i : Integrable (fun x ↦ f (x, t) * f (x, t)) κ := by
    simpa only [κ, pow_two, Function.comp_apply] using
      integrable_normalizedWeight μ (fun x ↦ W (x, t)) (fun x ↦ f (x, t) ^ 2)
      (hWm.comp measurable_prodMk_right) (fun x ↦ hW0 (x, t)) hZ0 hWf2t
  have h := integral_mul_ge_mul_integral_of_comonotone hfi hfi hf2i
    (fun x y ↦ mul_self_nonneg (f (x, t) - f (y, t)))
  rw [sliceMean_eq_integral_normalizedWeight μ W f hWm hW0 t hWt,
    sliceMean_eq_integral_normalizedWeight μ W (fun p ↦ f p ^ 2) hWm hW0 t hWt]
  simpa only [pow_two] using h

theorem sliceMean_sq_integrable (μ : Measure Ω) [SFinite μ]
    (ν : Measure ℝ) [SFinite ν] (W f : Ω × ℝ → ℝ)
    (hWm : Measurable W) (hfm : Measurable f) (hW0 : ∀ p, 0 ≤ W p)
    (hWi : Integrable W (μ.prod ν)) (hWfi : Integrable (fun p ↦ W p * f p) (μ.prod ν))
    (hWf2i : Integrable (fun p ↦ W p * f p ^ 2) (μ.prod ν)) :
    Integrable (fun t ↦ (sliceMean μ W f t) ^ 2) (densityMarginal μ ν W) := by
  have hAC := densityMarginal_absolutelyContinuous μ ν W
  have hgood : ∀ᵐ t ∂densityMarginal μ ν W,
      (sliceMean μ W f t) ^ 2 ≤ sliceMean μ W (fun p ↦ f p ^ 2) t := by
    filter_upwards [hAC.ae_le hWi.prod_left_ae, hAC.ae_le hWfi.prod_left_ae,
      hAC.ae_le hWf2i.prod_left_ae, densityMarginal_sliceNorm_pos_ae μ ν W hWm]
      with t hWt hWft hWf2t hZt
    exact sliceMean_sq_le μ W f hWm hW0 t hWt hWft hWf2t hZt
  apply (sliceMean_integrable μ ν W (fun p ↦ f p ^ 2) hWm hW0 hWi hWf2i).mono'
    ((sliceMean_measurable μ W f hWm hfm).pow_const 2).aestronglyMeasurable
  filter_upwards [hgood] with t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (sliceMean μ W f t))] using ht

theorem sliceMean_memLp_two (μ : Measure Ω) [SFinite μ]
    (ν : Measure ℝ) [SFinite ν] (W f : Ω × ℝ → ℝ)
    (hWm : Measurable W) (hfm : Measurable f) (hW0 : ∀ p, 0 ≤ W p)
    (hWi : Integrable W (μ.prod ν)) (hWfi : Integrable (fun p ↦ W p * f p) (μ.prod ν))
    (hWf2i : Integrable (fun p ↦ W p * f p ^ 2) (μ.prod ν)) :
    MemLp (sliceMean μ W f) 2 (densityMarginal μ ν W) :=
  (memLp_two_iff_integrable_sq (sliceMean_measurable μ W f hWm hfm).aestronglyMeasurable).mpr
    (sliceMean_sq_integrable μ ν W f hWm hfm hW0 hWi hWfi hWf2i)

/-- The final total-covariance step, retaining the exceptional parameter set.
The slice comparison hypotheses are supplied by the lattice and strict-order
lemmas; this theorem proves the integration/strictness implication. -/
theorem strict_association_of_strict_sliceMeans
    (μ : Measure Ω) [SFinite μ] (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    (W f g : Ω × ℝ → ℝ)
    (hWm : Measurable W) (hfm : Measurable f) (hgm : Measurable g)
    (hW0 : ∀ p, 0 ≤ W p) (hWi : Integrable W (μ.prod ν))
    (hWone : ∫ p, W p ∂μ.prod ν = 1)
    (hWfi : Integrable (fun p ↦ W p * f p) (μ.prod ν))
    (hWgi : Integrable (fun p ↦ W p * g p) (μ.prod ν))
    (hWfgi : Integrable (fun p ↦ W p * (f p * g p)) (μ.prod ν))
    (hWf2i : Integrable (fun p ↦ W p * f p ^ 2) (μ.prod ν))
    (hWg2i : Integrable (fun p ↦ W p * g p ^ 2) (μ.prod ν))
    (s : Set ℝ) (hs : ∀ᵐ t ∂densityMarginal μ ν W, t ∈ s)
    (hfstrict : StrictMonoOn (sliceMean μ W f) s)
    (hgstrict : StrictMonoOn (sliceMean μ W g) s)
    (hweak : ∀ᵐ t ∂densityMarginal μ ν W,
      sliceMean μ W f t * sliceMean μ W g t ≤ sliceMean μ W (fun p ↦ f p * g p) t) :
    (∫ p, W p * f p ∂μ.prod ν) * (∫ p, W p * g p ∂μ.prod ν) <
      ∫ p, W p * (f p * g p) ∂μ.prod ν := by
  letI : IsProbabilityMeasure (densityMarginal μ ν W) :=
    densityMarginal_probability μ ν W hW0 hWi hWone
  have hfL2 := sliceMean_memLp_two μ ν W f hWm hfm hW0 hWi hWfi hWf2i
  have hgL2 := sliceMean_memLp_two μ ν W g hWm hgm hW0 hWi hWgi hWg2i
  have hfg := hfL2.integrable_mul hgL2
  have hstrict := integral_mul_gt_mul_integral_of_strictMonoOn_ae
    (sliceMean_integrable μ ν W f hWm hW0 hWi hWfi)
    (sliceMean_integrable μ ν W g hWm hW0 hWi hWgi) hfg s hs hfstrict hgstrict
  have hle := integral_mono_ae hfg
    (sliceMean_integrable μ ν W (fun p ↦ f p * g p) hWm hW0 hWi hWfgi) hweak
  have h := hstrict.trans_le hle
  rw [integral_sliceMean μ ν W f hWm hW0 hWi hWfi,
    integral_sliceMean μ ν W g hWm hW0 hWi hWgi,
    integral_sliceMean μ ν W (fun p ↦ f p * g p) hWm hW0 hWi hWfgi] at h
  exact h

end WishartVerification
end CanonicalSource72

section CanonicalSource73
/- Source: Wishart/NormalizedHolley.lean -/



open scoped Classical ENNReal

/-!
# Normalizing Holley comparisons and obtaining strict inequalities

The comparison is first kept in extended nonnegative integrals. This proves
integrability of the upper-parameter test under the lower-parameter law before
using a strict integral comparison; that cross-fiber integrability cannot be
assumed from Fubini alone.
-/

open MeasureTheory

namespace WishartVerification

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integral_mul_le_of_lintegral_mul_le (μ : Measure Ω) (f g : Ω → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hfgi : Integrable (fun x ↦ f x * g x) μ)
    (h : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) * (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂μ) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0),
    ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0),
    ← ofReal_integral_eq_lintegral_ofReal hfgi
      (ae_of_all _ fun x ↦ mul_nonneg (hf0 x) (hg0 x)),
    ← ENNReal.ofReal_mul (integral_nonneg hf0)] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg fun x ↦ mul_nonneg (hf0 x) (hg0 x))).mp h

theorem ennreal_normalize_holley {A B Z₁ Z₂ : ℝ≥0∞}
    (hZ₁0 : Z₁ ≠ 0) (hZ₁top : Z₁ ≠ ∞) (hZ₂0 : Z₂ ≠ 0) (hZ₂top : Z₂ ≠ ∞)
    (h : A * Z₂ ≤ Z₁ * B) : Z₁⁻¹ * A ≤ Z₂⁻¹ * B := by
  apply (ENNReal.mul_le_mul_iff_left hZ₂0 hZ₂top).mp
  calc
    (Z₁⁻¹ * A) * Z₂ = Z₁⁻¹ * (A * Z₂) := by ac_rfl
    _ ≤ Z₁⁻¹ * (Z₁ * B) := mul_le_mul_right h _
    _ = B := ENNReal.inv_mul_cancel_left hZ₁0 hZ₁top
    _ = (Z₂⁻¹ * B) * Z₂ := by
      rw [show (Z₂⁻¹ * B) * Z₂ = B * (Z₂⁻¹ * Z₂) by ac_rfl,
        ENNReal.inv_mul_cancel hZ₂0 hZ₂top, mul_one]

theorem normalizedWeight_lintegral_holley (μ : Measure Ω) (u v f : Ω → ℝ)
    (hum : Measurable u) (hvm : Measurable v) (hfm : Measurable f)
    (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x)
    (hZu0 : (∫⁻ x, ENNReal.ofReal (u x) ∂μ) ≠ 0)
    (hZutop : (∫⁻ x, ENNReal.ofReal (u x) ∂μ) ≠ ∞)
    (hZv0 : (∫⁻ x, ENNReal.ofReal (v x) ∂μ) ≠ 0)
    (hZvtop : (∫⁻ x, ENNReal.ofReal (v x) ∂μ) ≠ ∞)
    (hholley : (∫⁻ x, ENNReal.ofReal (u x * f x) ∂μ) *
        (∫⁻ x, ENNReal.ofReal (v x) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (u x) ∂μ) *
        (∫⁻ x, ENNReal.ofReal (v x * f x) ∂μ)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂normalizedWeight μ u) ≤
      ∫⁻ x, ENNReal.ofReal (f x) ∂normalizedWeight μ v := by
  rw [normalizedWeight_lintegral μ u f hum hfm hu0,
    normalizedWeight_lintegral μ v f hvm hfm hv0]
  exact ennreal_normalize_holley hZu0 hZutop hZv0 hZvtop hholley

/-- Extended stochastic domination supplies both the ordinary expectation
comparison and the integrability needed on the dominated side. -/
theorem integral_le_of_lintegral_le (μ ν : Measure Ω) (f : Ω → ℝ)
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfν : Integrable f ν)
    (hle : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν := by
  have hfiniteν : (∫⁻ x, ENNReal.ofReal (f x) ∂ν) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hfm.aestronglyMeasurable
      (ae_of_all _ hf0)).mpr hfν
  have hfμ : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hfm.aestronglyMeasurable
      (ae_of_all _ hf0)).mp (ne_top_of_le_ne_top hfiniteν hle)
  refine ⟨hfμ, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hfμ (ae_of_all _ hf0),
    ← ofReal_integral_eq_lintegral_ofReal hfν (ae_of_all _ hf0)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hf0)).mp hle

theorem normalizedWeight_pos_ae (μ : Measure Ω) (w : Ω → ℝ) (hwm : Measurable w) :
    ∀ᵐ x ∂normalizedWeight μ w, 0 < w x := by
  have hraw : ∀ᵐ x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (w x)), 0 < w x := by
    rw [ae_withDensity_iff hwm.ennreal_ofReal]
    exact ae_of_all _ fun x hx ↦ lt_of_not_ge fun h ↦ hx (ENNReal.ofReal_eq_zero.mpr h)
  exact Measure.ae_smul_measure hraw _

/-- A pointwise strict parameter increase, followed by stochastic domination,
gives a strict comparison of the two normalized expectations. -/
theorem normalizedWeight_integral_strict_of_holley
    (μ : Measure Ω) (u v f g : Ω → ℝ)
    (hum : Measurable u) (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hZu0 : (∫⁻ x, ENNReal.ofReal (u x) ∂μ) ≠ 0)
    (hZutop : (∫⁻ x, ENNReal.ofReal (u x) ∂μ) ≠ ∞)
    (hfi : Integrable f (normalizedWeight μ u))
    (hgi : Integrable g (normalizedWeight μ v))
    (hstrict : ∀ x, 0 < u x → f x < g x)
    (hholley : (∫⁻ x, ENNReal.ofReal (g x) ∂normalizedWeight μ u) ≤
      ∫⁻ x, ENNReal.ofReal (g x) ∂normalizedWeight μ v) :
    (∫ x, f x ∂normalizedWeight μ u) < ∫ x, g x ∂normalizedWeight μ v := by
  letI := normalizedWeight_probability μ u hZu0 hZutop
  obtain ⟨hgu, hgle⟩ := integral_le_of_lintegral_le
    (normalizedWeight μ u) (normalizedWeight μ v) g hgm hg0 hgi hholley
  have hpos : 0 < ∫ x, g x - f x ∂normalizedWeight μ u :=
    integral_pos_of_pos_ae (hgu.sub hfi)
      ((normalizedWeight_pos_ae μ u hum).mono fun x hx ↦ sub_pos.mpr (hstrict x hx))
  rw [integral_sub hgu hfi] at hpos
  exact (sub_pos.mp hpos).trans_le hgle

end WishartVerification
end CanonicalSource73

section CanonicalSource74
/- Source: Wishart/MTP2Approximation.lean -/



open scoped Classical ENNReal

/-!
# Explicit bounded approximations of a continuous lattice density

This structure packages proved approximation data, rather than an association
assumption. The Vandermonde constructor below supplies every field explicitly.
-/

open MeasureTheory Filter
open scoped Topology

namespace WishartVerification

variable {ι : Type*} [Fintype ι]

structure MTP2Approximation (W : (ι → ℝ) → ℝ) where
  approximant : ℕ → (ι → ℝ) → ℝ
  bound : ℕ → ℝ
  measurable : ∀ k, Measurable (approximant k)
  nonneg : ∀ k x, 0 ≤ approximant k x
  one_le_bound : ∀ k, 1 ≤ bound k
  le_bound : ∀ k x, approximant k x ≤ bound k
  lattice : ∀ k x y, approximant k x * approximant k y ≤
    approximant k (x ⊓ y) * approximant k (x ⊔ y)
  monotone : ∀ x, Monotone fun k ↦ approximant k x
  tendsto : ∀ x, Tendsto (fun k ↦ approximant k x) atTop (𝓝 (W x))

namespace MTP2Approximation

variable {W : (ι → ℝ) → ℝ} (H : MTP2Approximation W)

include H

theorem le_limit (k : ℕ) (x : ι → ℝ) : H.approximant k x ≤ W x :=
  (H.monotone x).ge_of_tendsto (H.tendsto x) k

theorem limit_nonneg (x : ι → ℝ) : 0 ≤ W x :=
  (H.nonneg 0 x).trans (H.le_limit 0 x)

noncomputable def const_mul (c : ℝ) (hc : 0 ≤ c) :
    MTP2Approximation (fun x ↦ c * W x) where
  approximant k x := c * H.approximant k x
  bound k := max 1 (c * H.bound k)
  measurable k := (H.measurable k).const_mul c
  nonneg k x := mul_nonneg hc (H.nonneg k x)
  one_le_bound k := le_max_left _ _
  le_bound k x := (mul_le_mul_of_nonneg_left (H.le_bound k x) hc).trans (le_max_right _ _)
  lattice k x y := by
    calc
      (c * H.approximant k x) * (c * H.approximant k y) =
          (c * c) * (H.approximant k x * H.approximant k y) := by ring
      _ ≤ (c * c) * (H.approximant k (x ⊓ y) * H.approximant k (x ⊔ y)) :=
        mul_le_mul_of_nonneg_left (H.lattice k x y) (mul_nonneg hc hc)
      _ = (c * H.approximant k (x ⊓ y)) * (c * H.approximant k (x ⊔ y)) := by ring
  monotone x := fun k l hkl ↦ mul_le_mul_of_nonneg_left (H.monotone x hkl) hc
  tendsto x := (H.tendsto x).const_mul c

theorem association_lintegral_on
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f g : (ι → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : SupportedMonotone W f) (hgi : SupportedMonotone W g) :
    (∫⁻ x, ENNReal.ofReal (W x * f x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (W x * g x) ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (W x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (W x * (f x * g x)) ∂Measure.pi μ) :=
  continuous_fkg_of_monotone_approximation_on μ W H.approximant H.bound
    H.measurable H.nonneg H.one_le_bound H.le_bound H.lattice H.monotone H.tendsto
    f g hfm hgm hf0 hg0 hfi hgi

end MTP2Approximation

/-- Every measurable nonnegative separate-weight Vandermonde density has an
explicit bounded MTP₂ approximation in every finite dimension. -/
noncomputable def vandermondeApproximation [LinearOrder ι]
    (w : ι → ℝ → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t) :
    MTP2Approximation (vandermondeWeight w β) where
  approximant := truncatedVandermondeWeight w β
  bound := truncatedVandermondeBound (ι := ι) β
  measurable k := vandermondeWeight_measurable _ β
    (fun i ↦ truncateCoordinate_measurable k (w i) (hwm i))
  nonneg k x := vandermondeWeight_nonneg _ β
    (fun i t ↦ truncateCoordinate_nonneg k (w i) (hw0 i) t) x
  one_le_bound k := le_max_left _ _
  le_bound := truncatedVandermonde_bound w β hβ hw0
  lattice k x y := vandermondeWeight_lattice _ β
    (fun i t ↦ truncateCoordinate_nonneg k (w i) (hw0 i) t) hβ x y
  monotone := truncatedVandermonde_mono w β hw0
  tendsto := truncatedVandermonde_tendsto w β

namespace MTP2Approximation

variable {n : ℕ} {W : (Fin (n + 1) → ℝ) → ℝ} (H : MTP2Approximation W)

include H

/-- Fixing the last coordinate preserves all the proved approximation data. -/
noncomputable def slice (t : ℝ) : MTP2Approximation (fun x ↦ W (appendLast x t)) where
  approximant k x := H.approximant k (appendLast x t)
  bound := H.bound
  measurable k := (H.measurable k).comp (snoc_measurable t)
  nonneg k x := H.nonneg k _
  one_le_bound := H.one_le_bound
  le_bound k x := H.le_bound k _
  lattice k x y := slice_mixed_lattice (H.approximant k) (H.lattice k) t t le_rfl x y
  monotone x := H.monotone _
  tendsto x := H.tendsto _

theorem slice_holley
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s t : ℝ) (hst : s ≤ t)
    (f : (Fin n → ℝ) → ℝ) (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : ∀ x y, 0 < W (appendLast x s) → 0 < W (appendLast y t) → x ≤ y → f x ≤ f y) :
    (∫⁻ x, ENNReal.ofReal (W (appendLast x s) * f x) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (W (appendLast x t)) ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (W (appendLast x s)) ∂Measure.pi μ) *
        (∫⁻ x, ENNReal.ofReal (W (appendLast x t) * f x) ∂Measure.pi μ) :=
  slice_holley_lintegral μ W H.approximant H.bound H.measurable H.nonneg H.one_le_bound
    H.le_bound H.lattice H.monotone H.tendsto s t hst f hfm hf0 hfi

end MTP2Approximation

end WishartVerification
end CanonicalSource74
