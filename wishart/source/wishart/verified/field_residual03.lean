module

public import wishart.verified.field_residual02

/- Recovered canonical proof stage; see verification/recovery-patches.json. -/

@[expose] public section


section CanonicalSource20
/- Source: Wishart/LeadingRowSubmean.lean -/



/-!
# Leading products under a scalar row update

For every orthonormal frame, the compressed determinant is logarithmically
submean. The variational maximum is attained by an actual eigenframe, so
the same inequality holds for the product of the largest j eigenvalues.
This applies to every j, with no rank or overlap restriction.
-/

noncomputable section
open Matrix
open scoped Classical Quaternion ComplexOrder BigOperators
namespace Wishart.FieldGaussian
open WishartVerification

section RowUpdate
variable (F : Type*) [NormedDivisionRing F]
  [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

def hermitianRowUpdate {k : ℕ}
    (Q : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F))
    (z v : Row F k) (u : F) : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F) :=
  ⟨(Q : Matrix (Fin k) (Fin k) F) + rowGram F (rowShift F z u v), by
    rw [rowGram_eq_matrix]
    exact (WishartVerification.hermitian_matrix_coe Q).add
      (Matrix.isHermitian_conjTranspose_mul_self _)⟩

theorem continuous_hermitianRowUpdate {k : ℕ}
    (Q : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F)) (z v : Row F k) :
    Continuous (hermitianRowUpdate F Q z v) := by
  apply Continuous.subtype_mk
  unfold rowGram rowShift
  fun_prop

end RowUpdate

theorem complex_rowUpdate_posDef {k : ℕ} (Q : FieldSpectral.Hermitian ℂ k)
    (hQ : (Q : Matrix (Fin k) (Fin k) ℂ).PosDef) (z v : Row ℂ k) (u : ℂ) :
    (hermitianRowUpdate ℂ Q z v u : Matrix (Fin k) (Fin k) ℂ).PosDef := by
  change ((Q : Matrix (Fin k) (Fin k) ℂ) + rowGram ℂ (rowShift ℂ z u v)).PosDef
  rw [rowGram_eq_matrix]
  exact hQ.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)

theorem quaternion_rowUpdate_posDef {k : ℕ} (Q : QuaternionMatrix.Hermitian k)
    (hQ : QuaternionMatrix.PosDef (Q : Matrix (Fin k) (Fin k) ℍ[ℝ]))
    (z v : Row ℍ[ℝ] k) (u : ℍ[ℝ]) :
    QuaternionMatrix.PosDef
      (hermitianRowUpdate ℍ[ℝ] Q z v u : Matrix (Fin k) (Fin k) ℍ[ℝ]) := by
  change QuaternionMatrix.PosDef ((Q : Matrix (Fin k) (Fin k) ℍ[ℝ]) +
    rowGram ℍ[ℝ] (rowShift ℍ[ℝ] z u v))
  rw [rowGram_eq_matrix]
  exact hQ.add_posSemidef (QuaternionMatrix.posSemidef_gram _)

theorem positiveLogSubmean_complex_leadingProduct {k j : ℕ} (hj : j ≤ k)
    (Q : FieldSpectral.Hermitian ℂ k)
    (hQ : (Q : Matrix (Fin k) (Fin k) ℂ).PosDef) (z v : Row ℂ k) :
    PositiveLogSubmean (fun u : ℂ => FieldSpectral.leadingEigenvalueProduct hj
      (WishartVerification.hermitian_matrix_coe (hermitianRowUpdate ℂ Q z v u))) := by
  let A := hermitianRowUpdate ℂ Q z v
  have hA (u : ℂ) : (A u : Matrix (Fin k) (Fin k) ℂ).PosDef :=
    complex_rowUpdate_posDef Q hQ z v u
  apply PositiveLogSubmean.of_attaining_family
    (fun U : FieldSpectral.OrthonormalFrame ℂ k j => fun u =>
      FieldSpectral.compressionDeterminant (A u : Matrix (Fin k) (Fin k) ℂ) U)
  · intro U
    have hcomp : (U.valᴴ * (Q : Matrix (Fin k) (Fin k) ℂ) * U.val + 0).PosDef := by
      simpa only [add_zero] using hQ.conjTranspose_mul_mul_same U.injective_mulVec
    simpa only [FieldSpectral.compressionDeterminant, ComplexMatrix.realDeterminant,
      A, hermitianRowUpdate, add_zero, RCLike.re_to_complex] using
      positiveLogSubmean_complex_compressed_row (Q : Matrix (Fin k) (Fin k) ℂ)
        U.val 0 hcomp z v
  · exact (FieldSpectral.continuous_leadingEigenvalueProduct hj).comp
      (continuous_hermitianRowUpdate ℂ Q z v)
  · intro u
    exact FieldSpectral.leadingEigenvalueProduct_pos hj (hA u)
  · intro U u
    exact (FieldSpectral.leadingEigenvalueProduct_isGreatest hj (hA u).posSemidef).2
      (Set.mem_range_self U)
  · intro u
    exact (FieldSpectral.leadingEigenvalueProduct_isGreatest hj (hA u).posSemidef).1

theorem positiveLogSubmean_quaternion_leadingProduct {k j : ℕ} (hj : j ≤ k)
    (Q : QuaternionMatrix.Hermitian k)
    (hQ : QuaternionMatrix.PosDef (Q : Matrix (Fin k) (Fin k) ℍ[ℝ]))
    (z v : Row ℍ[ℝ] k) :
    PositiveLogSubmean (fun u : ℍ[ℝ] => QuaternionMatrix.leadingEigenvalueProduct hj
      (WishartVerification.hermitian_matrix_coe (hermitianRowUpdate ℍ[ℝ] Q z v u))) := by
  let A := hermitianRowUpdate ℍ[ℝ] Q z v
  have hA (u : ℍ[ℝ]) : QuaternionMatrix.PosDef
      (A u : Matrix (Fin k) (Fin k) ℍ[ℝ]) := quaternion_rowUpdate_posDef Q hQ z v u
  apply PositiveLogSubmean.of_attaining_family
    (fun U : QuaternionMatrix.OrthonormalFrame k j => fun u =>
      QuaternionMatrix.compressionDeterminant
        (A u : Matrix (Fin k) (Fin k) ℍ[ℝ]) U)
  · intro U
    have hcomp : QuaternionMatrix.PosDef
        (U.valᴴ * (Q : Matrix (Fin k) (Fin k) ℍ[ℝ]) * U.val + 0) := by
      simpa only [add_zero] using
        QuaternionMatrix.FullColumnRank.congruence_posDef hQ
          (QuaternionMatrix.fullColumnRank_of_orthonormal U.val U.property)
    simpa only [QuaternionMatrix.compressionDeterminant, A, hermitianRowUpdate, add_zero] using
      positiveLogSubmean_quaternion_compressed_row (Q : Matrix (Fin k) (Fin k) ℍ[ℝ])
        U.val 0 hcomp z v
  · exact (QuaternionMatrix.continuous_leadingEigenvalueProduct hj).comp
      (continuous_hermitianRowUpdate ℍ[ℝ] Q z v)
  · intro u
    exact QuaternionMatrix.leadingEigenvalueProduct_pos hj (hA u)
  · intro U u
    exact (QuaternionMatrix.leadingEigenvalueProduct_isGreatest hj (hA u).posSemidef).2
      (Set.mem_range_self U)
  · intro u
    exact (QuaternionMatrix.leadingEigenvalueProduct_isGreatest hj (hA u).posSemidef).1

open Wishart.Spectral

def complexSpectralMonomial {k : ℕ} (a : Fin k → ℝ) (b : ℝ)
    (A : FieldSpectral.Hermitian ℂ k) : ℝ :=
  Real.exp b * ∏ j : Fin k,
    FieldSpectral.leadingEigenvalueProduct (Nat.succ_le_of_lt j.isLt)
      (WishartVerification.hermitian_matrix_coe A) ^ slopeDrop a j

def quaternionSpectralMonomial {k : ℕ} (a : Fin k → ℝ) (b : ℝ)
    (A : QuaternionMatrix.Hermitian k) : ℝ :=
  Real.exp b * ∏ j : Fin k,
    QuaternionMatrix.leadingEigenvalueProduct (Nat.succ_le_of_lt j.isLt)
      (WishartVerification.hermitian_matrix_coe A) ^ slopeDrop a j

theorem continuous_complexSpectralMonomial {k : ℕ} {a : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (b : ℝ) :
    Continuous (complexSpectralMonomial a b) := by
  apply continuous_const.mul
  apply continuous_finsetProd
  intro j hj
  exact (Real.continuous_rpow_const (slopeDrop_nonneg ha hmono j)).comp
    (FieldSpectral.continuous_leadingEigenvalueProduct _)

theorem continuous_quaternionSpectralMonomial {k : ℕ} {a : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (b : ℝ) :
    Continuous (quaternionSpectralMonomial a b) := by
  apply continuous_const.mul
  apply continuous_finsetProd
  intro j hj
  exact (Real.continuous_rpow_const (slopeDrop_nonneg ha hmono j)).comp
    (QuaternionMatrix.continuous_leadingEigenvalueProduct _)

theorem positiveLogSubmean_complex_monomial {k : ℕ} {a : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (b : ℝ)
    (Q : FieldSpectral.Hermitian ℂ k)
    (hQ : (Q : Matrix (Fin k) (Fin k) ℂ).PosDef) (z v : Row ℂ k) :
    PositiveLogSubmean (fun u => complexSpectralMonomial a b
      (hermitianRowUpdate ℂ Q z v u)) := by
  apply (PositiveLogSubmean.const (Real.exp_pos b)).mul
  apply PositiveLogSubmean.finset_prod
  intro j hj
  exact (positiveLogSubmean_complex_leadingProduct _ Q hQ z v).rpow
    (slopeDrop_nonneg ha hmono j)

theorem positiveLogSubmean_quaternion_monomial {k : ℕ} {a : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (b : ℝ)
    (Q : QuaternionMatrix.Hermitian k)
    (hQ : QuaternionMatrix.PosDef (Q : Matrix (Fin k) (Fin k) ℍ[ℝ]))
    (z v : Row ℍ[ℝ] k) :
    PositiveLogSubmean (fun u => quaternionSpectralMonomial a b
      (hermitianRowUpdate ℍ[ℝ] Q z v u)) := by
  apply (PositiveLogSubmean.const (Real.exp_pos b)).mul
  apply PositiveLogSubmean.finset_prod
  intro j hj
  exact (positiveLogSubmean_quaternion_leadingProduct _ Q hQ z v).rpow
    (slopeDrop_nonneg ha hmono j)

end Wishart.FieldGaussian
end
end CanonicalSource20

section CanonicalSource21
/- Source: Wishart/FiniteCoordinateMinorants.lean -/



/-! # Countable nonnegative supporting planes on any finite coordinate set -/

noncomputable section
open Set Filter Topology
open scoped Classical BigOperators
namespace Wishart.Spectral
open WishartVerification

variable {ι : Type*} [Fintype ι]

def finiteCoordinatePlane (a : ι → ℝ) (b : ℝ) (x : ι → ℝ) : ℝ :=
  (∑ i, a i * x i) + b

theorem finiteLinearForm_eq_coordinate_sum (l : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    l x = ∑ i, l (Pi.single i 1) * x i := by
  classical
  have hx : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
    ext i
    simp [Pi.single_apply, eq_comm]
  calc
    l x = l (∑ i, x i • Pi.single i (1 : ℝ)) := congrArg l hx
    _ = ∑ i, l (Pi.single i 1) * x i := by
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

theorem finiteLinearForm_single (l : (ι → ℝ) →L[ℝ] ℝ) (i : ι) (t : ℝ) :
    l (Pi.single i t) = l (Pi.single i 1) * t := by
  classical
  have heq : Pi.single i t = t • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [heq, map_smul, smul_eq_mul, mul_comm]

theorem finiteCoordinate_coeff_nonneg {h : (ι → ℝ) → ℝ} (hm : Monotone h)
    (l : (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) (hle : ∀ x, l x + b ≤ h x) (i : ι) :
    0 ≤ l (Pi.single i 1) := by
  classical
  have hmline : Monotone (fun t : ℝ => h (Pi.single i t)) := by
    intro s t hst
    apply hm
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hst
    · simp [Pi.single_apply, hji, Ne.symm hji]
  apply nonnegative_slope_of_affine_minorant hmline
  intro t
  have ht := hle (Pi.single i t)
  rw [finiteLinearForm_single] at ht
  exact ht

theorem exists_nonnegative_finiteCoordinate_minorants {h : (ι → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) :
    ∃ (a : ℕ → ι → ℝ) (b : ℕ → ℝ),
      (∀ n i, 0 ≤ a n i) ∧
      (∀ n x, finiteCoordinatePlane (a n) (b n) x ≤ h x) ∧
      (∀ x, (⨆ n, finiteCoordinatePlane (a n) (b n) x) = h x) := by
  have hcont : Continuous h := by
    simpa only [interior_univ, continuousOn_univ] using hc.continuousOn_interior
  obtain ⟨l, b, hle, hsup⟩ := hc.real_univ_sSup_of_nat_affine_eq hcont.lowerSemicontinuous
  have hl (n : ℕ) (x : ι → ℝ) : l n x + b n ≤ h x := by
    simpa only [Pi.add_apply, Function.const_apply] using hle n x
  refine ⟨fun n i => l n (Pi.single i 1), b,
    fun n i => finiteCoordinate_coeff_nonneg hm (l n) (b n) (hl n) i, ?_, ?_⟩
  · intro n x
    simpa only [finiteCoordinatePlane, ← finiteLinearForm_eq_coordinate_sum] using hl n x
  · intro x
    simpa only [iSup_apply, Pi.add_apply, Function.const_apply, finiteCoordinatePlane,
      ← finiteLinearForm_eq_coordinate_sum] using congrFun hsup x

theorem finiteCoordinate_maximum_tendsto {a : ℕ → ι → ℝ} {b : ℕ → ℝ}
    {h : (ι → ℝ) → ℝ}
    (hle : ∀ n x, finiteCoordinatePlane (a n) (b n) x ≤ h x)
    (hsup : ∀ x, (⨆ n, finiteCoordinatePlane (a n) (b n) x) = h x) (x : ι → ℝ) :
    Tendsto (fun n => finiteMaximum (fun j : Fin (n + 1) =>
      finiteCoordinatePlane (a j) (b j) x)) atTop (𝓝 (h x)) := by
  let H (n : ℕ) := finiteMaximum (fun j : Fin (n + 1) =>
    finiteCoordinatePlane (a j) (b j) x)
  have hHle (n : ℕ) : H n ≤ h x := finiteMaximum_le fun j => hle j x
  have hHmono : Monotone H := by
    intro n m hnm
    apply finiteMaximum_le
    intro j
    exact le_finiteMaximum
      (fun i : Fin (m + 1) => finiteCoordinatePlane (a i) (b i) x)
      (⟨j, lt_of_lt_of_le j.isLt (Nat.add_le_add_right hnm 1)⟩ : Fin (m + 1))
  have hb : BddAbove (Set.range H) := ⟨h x, by rintro _ ⟨n, rfl⟩; exact hHle n⟩
  have heq : (⨆ n, H n) = h x := by
    apply le_antisymm (ciSup_le hHle)
    rw [← hsup x]
    apply ciSup_le
    intro n
    exact (le_finiteMaximum
      (fun j : Fin (n + 1) => finiteCoordinatePlane (a j) (b j) x)
      (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))).trans (le_ciSup hb n)
  simpa only [heq] using tendsto_atTop_ciSup hHmono hb

def finiteCoordinateMonomial (a : ι → ℝ) (b : ℝ) (x : ι → ℝ) : ℝ :=
  Real.exp b * ∏ i, x i ^ a i

theorem finiteCoordinateMonomial_eq_exp {a x : ι → ℝ} (b : ℝ)
    (hx : ∀ i, 0 < x i) :
    finiteCoordinateMonomial a b x =
      Real.exp (finiteCoordinatePlane a b (fun i => Real.log (x i))) := by
  simp only [finiteCoordinateMonomial, finiteCoordinatePlane, Real.exp_add, Real.exp_sum]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.rpow_def_of_pos (hx i)]
  congr 1
  ring

theorem finiteCoordinateMonomial_partialMaximum_tendsto
    {a : ℕ → ι → ℝ} {b : ℕ → ℝ} {h : (ι → ℝ) → ℝ}
    (hle : ∀ n x, finiteCoordinatePlane (a n) (b n) x ≤ h x)
    (hsup : ∀ x, (⨆ n, finiteCoordinatePlane (a n) (b n) x) = h x)
    {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    Tendsto (fun n => finiteMaximum (fun j : Fin (n + 1) =>
      finiteCoordinateMonomial (a j) (b j) x)) atTop
      (𝓝 (Real.exp (h (fun i => Real.log (x i))))) := by
  have heq (n : ℕ) : finiteMaximum (fun j : Fin (n + 1) =>
      finiteCoordinateMonomial (a j) (b j) x) =
      Real.exp (finiteMaximum (fun j : Fin (n + 1) =>
        finiteCoordinatePlane (a j) (b j) (fun i => Real.log (x i)))) := by
    simp_rw [finiteCoordinateMonomial_eq_exp _ hx]
    apply le_antisymm
    · exact finiteMaximum_le fun j => Real.exp_le_exp.mpr (le_finiteMaximum
        (fun j : Fin (n + 1) => finiteCoordinatePlane (a j) (b j)
          (fun i => Real.log (x i))) j)
    · obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j : Fin (n + 1) => finiteCoordinatePlane (a j) (b j) (fun i => Real.log (x i)))
      change Real.exp (Finset.univ.sup' Finset.univ_nonempty _) ≤ _
      rw [hmax]
      exact le_finiteMaximum
        (fun j : Fin (n + 1) => Real.exp (finiteCoordinatePlane (a j) (b j)
          (fun i => Real.log (x i)))) j
  simp only [heq]
  exact Real.continuous_exp.continuousAt.tendsto.comp
    (finiteCoordinate_maximum_tendsto hle hsup (fun i => Real.log (x i)))

end Wishart.Spectral
end
end CanonicalSource21

section CanonicalSource22
/- Source: Wishart/SpectralFacePlanes.lean -/



/-!
# Supporting monomials on every spectral boundary face

There are finitely many coordinate faces. Every finite face contributes a
countable sequence of ordinary supporting planes with zero slopes on the
omitted coordinates. Finite prefix maxima across all those faces increase to
the actual regularized boundary value at every nonnegative vector. This is
the boundary-preserving approximation required in Section 7.2.
-/

noncomputable section
open Set Filter Topology
open scoped Classical BigOperators
namespace Wishart.Spectral
open WishartVerification
variable {k : ℕ}

theorem faceFinite_univ (h : (Fin k → ℝ) → ℝ) : FaceFinite h Finset.univ := by
  refine ⟨fun _ => 0, h 0, ?_⟩
  rintro _ ⟨t, rfl⟩
  have heq : faceFill (Finset.univ : Finset (Fin k)) (fun _ => 0) t = 0 := by
    funext i
    simp only [faceFill, Finset.mem_univ, dif_pos, Pi.zero_apply]
  simpa only [heq] using (le_refl (h 0))

def FiniteFace (h : (Fin k → ℝ) → ℝ) := {J : Finset (Fin k) // FaceFinite h J}

instance finiteFaceFinite (h : (Fin k → ℝ) → ℝ) : Finite (FiniteFace h) := by
  unfold FiniteFace
  infer_instance
noncomputable instance finiteFaceFintype (h : (Fin k → ℝ) → ℝ) : Fintype (FiniteFace h) :=
  Fintype.ofFinite _
instance finiteFaceNonempty (h : (Fin k → ℝ) → ℝ) : Nonempty (FiniteFace h) :=
  ⟨⟨Finset.univ, faceFinite_univ h⟩⟩

structure FaceSupportingSequence (h : (Fin k → ℝ) → ℝ) (J : Finset (Fin k)) where
  slope : ℕ → J → ℝ
  intercept : ℕ → ℝ
  nonnegative : ∀ n i, 0 ≤ slope n i
  minorant : ∀ n x, finiteCoordinatePlane (slope n) (intercept n) x ≤ faceProfile h J x
  supremum : ∀ x, (⨆ n, finiteCoordinatePlane (slope n) (intercept n) x) = faceProfile h J x

theorem nonempty_faceSupportingSequence {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (J : FiniteFace h) :
    Nonempty (FaceSupportingSequence h J.val) := by
  obtain ⟨a, b, ha, hle, hsup⟩ := exists_nonnegative_finiteCoordinate_minorants
    (convexOn_faceProfile hc hm J.property) (monotone_faceProfile hc hm J.property)
  exact ⟨⟨a, b, ha, hle, hsup⟩⟩

def chosenFaceSupportingSequence {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (J : FiniteFace h) :
    FaceSupportingSequence h J.val := Classical.choice (nonempty_faceSupportingSequence hc hm J)

def extendFaceSlopes (J : Finset (Fin k)) (a : J → ℝ) (i : Fin k) : ℝ :=
  if hi : i ∈ J then a ⟨i, hi⟩ else 0

theorem extendFaceSlopes_nonneg (J : Finset (Fin k)) {a : J → ℝ}
    (ha : ∀ i, 0 ≤ a i) (i : Fin k) : 0 ≤ extendFaceSlopes J a i := by
  by_cases hi : i ∈ J
  · simpa only [extendFaceSlopes, dif_pos hi] using ha ⟨i, hi⟩
  · simp only [extendFaceSlopes, dif_neg hi, le_refl]

theorem finiteCoordinatePlane_extendFaceSlopes (J : Finset (Fin k))
    (a : J → ℝ) (b : ℝ) (x : Fin k → ℝ) :
    finiteCoordinatePlane (extendFaceSlopes J a) b x =
      finiteCoordinatePlane a b (fun i => x i) := by
  unfold finiteCoordinatePlane
  congr 1
  calc
    (∑ i, extendFaceSlopes J a i * x i) = ∑ i ∈ J, extendFaceSlopes J a i * x i :=
      (Finset.sum_subset (Finset.subset_univ J) (fun i hi hiJ => by
        simp only [extendFaceSlopes, dif_neg hiJ, zero_mul])).symm
    _ = ∑ i : J, a i * x i := by
      rw [← Finset.sum_coe_sort J (fun i => extendFaceSlopes J a i * x i)]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [extendFaceSlopes, dif_pos i.property]

theorem finiteCoordinateMonomial_extendFaceSlopes (J : Finset (Fin k))
    (a : J → ℝ) (b : ℝ) (x : Fin k → ℝ) :
    finiteCoordinateMonomial (extendFaceSlopes J a) b x =
      finiteCoordinateMonomial a b (fun i => x i) := by
  unfold finiteCoordinateMonomial
  congr 1
  calc
    (∏ i, x i ^ extendFaceSlopes J a i) = ∏ i ∈ J, x i ^ extendFaceSlopes J a i :=
      (Finset.prod_subset (Finset.subset_univ J) (fun i hi hiJ => by
        simp only [extendFaceSlopes, dif_neg hiJ, Real.rpow_zero])).symm
    _ = ∏ i : J, x i ^ a i := by
      rw [← Finset.prod_coe_sort J (fun i => x i ^ extendFaceSlopes J a i)]
      apply Finset.prod_congr rfl
      intro i hi
      simp only [extendFaceSlopes, dif_pos i.property]

theorem face_plane_global_minorant {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (J : FiniteFace h)
    (D : FaceSupportingSequence h J.val) (n : ℕ) (x : Fin k → ℝ) :
    finiteCoordinatePlane (extendFaceSlopes J.val (D.slope n)) (D.intercept n) x ≤ h x := by
  rw [finiteCoordinatePlane_extendFaceSlopes]
  exact (D.minorant n _).trans (faceProfile_le_full hc hm J.property x)

theorem nonnegative_monomial_le_boundary_of_minorant {h : (Fin k → ℝ) → ℝ}
    {a : Fin k → ℝ} {b : ℝ} (ha : ∀ i, 0 ≤ a i)
    (hle : ∀ z, finiteCoordinatePlane a b z ≤ h z)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    finiteCoordinateMonomial a b x ≤ spectralBoundaryValue h x := by
  apply le_ciInf
  intro t
  calc
    finiteCoordinateMonomial a b x ≤
        finiteCoordinateMonomial a b (fun i => x i + Real.exp t) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Real.rpow_nonneg (hx i) _
      · intro i hi
        exact Real.rpow_le_rpow (hx i) (le_add_of_nonneg_right (Real.exp_pos t).le) (ha i)
    _ = Real.exp (finiteCoordinatePlane a b (fun i => Real.log (x i + Real.exp t))) :=
      finiteCoordinateMonomial_eq_exp b (fun i => add_pos_of_nonneg_of_pos (hx i) (Real.exp_pos t))
    _ ≤ spectralRegularization h x t := Real.exp_le_exp.mpr (hle _)

def faceMonomialApprox {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ) (x : Fin k → ℝ) : ℝ :=
  finiteMaximum (fun z : FiniteFace h × Fin (n + 1) =>
    let D := chosenFaceSupportingSequence hc hm z.1
    finiteCoordinateMonomial (extendFaceSlopes z.1.val (D.slope z.2)) (D.intercept z.2) x)

theorem faceMonomialApprox_nonneg {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ faceMonomialApprox hc hm n x := by
  apply finiteMaximum_nonneg
  intro z
  exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hx i) _)

theorem faceMonomialApprox_le_boundary {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    faceMonomialApprox hc hm n x ≤ spectralBoundaryValue h x := by
  apply finiteMaximum_le
  intro z
  let D := chosenFaceSupportingSequence hc hm z.1
  exact nonnegative_monomial_le_boundary_of_minorant
    (extendFaceSlopes_nonneg z.1.val (D.nonnegative z.2))
    (face_plane_global_minorant hc hm z.1 D z.2) hx

theorem faceMonomialApprox_monotone_index {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (x : Fin k → ℝ) :
    Monotone (fun n => faceMonomialApprox hc hm n x) := by
  intro n m hnm
  apply finiteMaximum_le
  intro z
  exact le_finiteMaximum
    (fun w : FiniteFace h × Fin (m + 1) =>
      let D := chosenFaceSupportingSequence hc hm w.1
      finiteCoordinateMonomial (extendFaceSlopes w.1.val (D.slope w.2)) (D.intercept w.2) x)
    (z.1, ⟨z.2, lt_of_lt_of_le z.2.isLt (Nat.add_le_add_right hnm 1)⟩)

/-- Every boundary value is recovered, including the identically-zero
faces. No strictly-positive-eigenvalue assumption is made. -/
theorem faceMonomialApprox_tendsto {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    Tendsto (fun n => faceMonomialApprox hc hm n x) atTop (𝓝 (spectralBoundaryValue h x)) := by
  let J := positiveCoordinateSet x
  by_cases hJ : FaceFinite h J
  · let J' : FiniteFace h := ⟨J, hJ⟩
    let D := chosenFaceSupportingSequence hc hm J'
    have hxJ (i : J) : 0 < x i := (mem_positiveCoordinateSet x i).mp i.property
    have hl := finiteCoordinateMonomial_partialMaximum_tendsto D.minorant D.supremum hxJ
    have htarget : Real.exp (faceProfile h J (fun i => Real.log (x i))) =
        spectralBoundaryValue h x := by
      rw [spectralBoundaryValue_eq_faceExponential hc hm hx,
        faceExponential_eq_exp_faceProfile hc hm hJ]
    rw [htarget] at hl
    apply hl.squeeze tendsto_const_nhds
    · intro n
      apply finiteMaximum_le
      intro j
      rw [← finiteCoordinateMonomial_extendFaceSlopes J (D.slope j) (D.intercept j) x]
      exact le_finiteMaximum
        (fun w : FiniteFace h × Fin (n + 1) =>
          let D := chosenFaceSupportingSequence hc hm w.1
          finiteCoordinateMonomial (extendFaceSlopes w.1.val (D.slope w.2)) (D.intercept w.2) x)
        (J', j)
    · exact fun n => faceMonomialApprox_le_boundary hc hm n hx
  · have hz : spectralBoundaryValue h x = 0 := by
      rw [spectralBoundaryValue_eq_faceExponential hc hm hx]
      exact faceExponential_eq_zero_of_not_finite hJ _
    have heq (n : ℕ) : faceMonomialApprox hc hm n x = 0 := by
      apply le_antisymm _ (faceMonomialApprox_nonneg hc hm n hx)
      simpa only [hz] using faceMonomialApprox_le_boundary hc hm n hx
    simp only [heq, hz]
    exact tendsto_const_nhds

end Wishart.Spectral
end
end CanonicalSource22

section CanonicalSource23
/- Source: Wishart/SortedSpectralFaces.lean -/



/-!
# Sorted supporting monomials, including zero eigenvalues

Sorting a nonnegative supporting slope is justified by symmetry and the
rearrangement inequality. The inequality at a zero coordinate is obtained by
continuity from positive coordinate vectors. Thus sorting the boundary-face
approximants retains their exact limit on the entire nonnegative chamber.
-/

noncomputable section
open Set Filter Topology
open scoped Classical BigOperators
namespace Wishart.Spectral
open WishartVerification
variable {k : ℕ}

theorem continuous_finiteCoordinateMonomial {a : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (b : ℝ) : Continuous (finiteCoordinateMonomial a b) := by
  apply continuous_const.mul
  apply continuous_finsetProd
  intro i hi
  exact (Real.continuous_rpow_const (ha i)).comp (continuous_apply i)

theorem finiteCoordinateMonomial_mono {a : Fin k → ℝ} (ha : ∀ i, 0 ≤ a i)
    (b : ℝ) {x y : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) (hxy : x ≤ y) :
    finiteCoordinateMonomial a b x ≤ finiteCoordinateMonomial a b y := by
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact Finset.prod_le_prod₀
    (fun i _ => Real.rpow_nonneg (hx i) _)
    (fun i _ => Real.rpow_le_rpow (hx i) (hxy i) (ha i))

theorem finiteCoordinateMonomial_le_sorted {a : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (b : ℝ) {x : Fin k → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hmono : Antitone x) :
    finiteCoordinateMonomial a b x ≤
      finiteCoordinateMonomial (sortedCoefficients a) b x := by
  have hlim : Tendsto (fun t : ℝ => fun i : Fin k => x i + Real.exp t)
      atBot (𝓝 x) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [add_zero] using tendsto_const_nhds.add Real.tendsto_exp_atBot
  apply le_of_tendsto_of_tendsto
    ((continuous_finiteCoordinateMonomial ha b).continuousAt.tendsto.comp hlim)
    ((continuous_finiteCoordinateMonomial (sortedCoefficients_nonneg ha) b).continuousAt.tendsto.comp hlim)
  apply Filter.Eventually.of_forall
  intro t
  have hpos (i : Fin k) : 0 < x i + Real.exp t :=
    add_pos_of_nonneg_of_pos (hx i) (Real.exp_pos t)
  simp only [Function.comp_apply]
  rw [finiteCoordinateMonomial_eq_exp b hpos,
    finiteCoordinateMonomial_eq_exp b hpos]
  apply Real.exp_le_exp.mpr
  change coordinatePlane a b (fun i => Real.log (x i + Real.exp t)) ≤
    coordinatePlane (sortedCoefficients a) b (fun i => Real.log (x i + Real.exp t))
  apply coordinatePlane_le_sorted_on_chamber
  intro i j hij
  exact Real.log_le_log (hpos j) (by
    simpa only [add_comm] using add_le_add_right (hmono hij) (Real.exp t))

theorem finiteCoordinateMonomial_eq_leadingProducts
    {a : Fin k → ℝ} (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    (b : ℝ) {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    finiteCoordinateMonomial a b x =
      Real.exp b * ∏ j, coordinateLeadingProduct x j ^ slopeDrop a j := by
  have hlim : Tendsto (fun t : ℝ => fun i : Fin k => x i + Real.exp t)
      atBot (𝓝 x) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [add_zero] using tendsto_const_nhds.add Real.tendsto_exp_atBot
  have hright : Continuous (fun y : Fin k → ℝ =>
      Real.exp b * ∏ j, coordinateLeadingProduct y j ^ slopeDrop a j) := by
    apply continuous_const.mul
    apply continuous_finsetProd
    intro j hj
    apply (Real.continuous_rpow_const (slopeDrop_nonneg ha hmono j)).comp
    unfold coordinateLeadingProduct
    fun_prop
  apply tendsto_nhds_unique
    ((continuous_finiteCoordinateMonomial ha b).continuousAt.tendsto.comp hlim)
  apply (hright.continuousAt.tendsto.comp hlim).congr
  intro t
  have hpos (i : Fin k) : 0 < x i + Real.exp t :=
    add_pos_of_nonneg_of_pos (hx i) (Real.exp_pos t)
  simp only [Function.comp_apply]
  rw [finiteCoordinateMonomial_eq_exp b hpos]
  exact (exp_coordinatePlane_log_eq_leadingProducts a b hpos).symm

def sortedFaceMonomialApprox {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ) (x : Fin k → ℝ) : ℝ :=
  finiteMaximum (fun z : FiniteFace h × Fin (n + 1) =>
    let D := chosenFaceSupportingSequence hc hm z.1
    finiteCoordinateMonomial
      (sortedCoefficients (extendFaceSlopes z.1.val (D.slope z.2))) (D.intercept z.2) x)

theorem sortedFaceMonomialApprox_nonneg {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ sortedFaceMonomialApprox hc hm n x := by
  apply finiteMaximum_nonneg
  intro z
  exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hx i) _)

theorem continuous_sortedFaceMonomialApprox {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ) :
    Continuous (sortedFaceMonomialApprox hc hm n) := by
  apply continuous_finiteMaximum
  intro z
  apply continuous_finiteCoordinateMonomial
  exact sortedCoefficients_nonneg (extendFaceSlopes_nonneg z.1.val
    ((chosenFaceSupportingSequence hc hm z.1).nonnegative z.2))

theorem sortedFaceMonomialApprox_mono {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    {x y : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) (hxy : x ≤ y) :
    sortedFaceMonomialApprox hc hm n x ≤ sortedFaceMonomialApprox hc hm n y := by
  apply finiteMaximum_mono
  intro z
  exact finiteCoordinateMonomial_mono
    (sortedCoefficients_nonneg (extendFaceSlopes_nonneg z.1.val
      ((chosenFaceSupportingSequence hc hm z.1).nonnegative z.2))) _ hx hxy

theorem sortedFaceMonomialApprox_monotone_index {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (x : Fin k → ℝ) :
    Monotone (fun n => sortedFaceMonomialApprox hc hm n x) := by
  intro n m hnm
  apply finiteMaximum_le
  intro z
  exact le_finiteMaximum
    (fun w : FiniteFace h × Fin (m + 1) =>
      let D := chosenFaceSupportingSequence hc hm w.1
      finiteCoordinateMonomial (sortedCoefficients (extendFaceSlopes w.1.val (D.slope w.2)))
        (D.intercept w.2) x)
    (z.1, ⟨z.2, lt_of_lt_of_le z.2.isLt (Nat.add_le_add_right hnm 1)⟩)

theorem sortedFaceMonomialApprox_le_boundary {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (hsym : SymmetricProfile h) (n : ℕ)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    sortedFaceMonomialApprox hc hm n x ≤ spectralBoundaryValue h x := by
  apply finiteMaximum_le
  intro z
  let D := chosenFaceSupportingSequence hc hm z.1
  apply nonnegative_monomial_le_boundary_of_minorant
    (sortedCoefficients_nonneg (extendFaceSlopes_nonneg z.1.val (D.nonnegative z.2))) _ hx
  intro y
  exact coordinatePlane_permutation_minorant hsym
    (face_plane_global_minorant hc hm z.1 D z.2)
    (Tuple.sortDesc (extendFaceSlopes z.1.val (D.slope z.2))) y

theorem faceMonomialApprox_le_sorted {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) (hmono : Antitone x) :
    faceMonomialApprox hc hm n x ≤ sortedFaceMonomialApprox hc hm n x := by
  apply finiteMaximum_mono
  intro z
  exact finiteCoordinateMonomial_le_sorted
    (extendFaceSlopes_nonneg z.1.val ((chosenFaceSupportingSequence hc hm z.1).nonnegative z.2))
    _ hx hmono

/-- The full boundary profile is recovered on the ordered chamber. Sorting
does not discard the planes responsible for nonzero singular-boundary values. -/
theorem sortedFaceMonomialApprox_tendsto {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (hsym : SymmetricProfile h)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) (hmono : Antitone x) :
    Tendsto (fun n => sortedFaceMonomialApprox hc hm n x) atTop
      (𝓝 (spectralBoundaryValue h x)) := by
  exact (faceMonomialApprox_tendsto hc hm hx).squeeze tendsto_const_nhds
    (fun n => faceMonomialApprox_le_sorted hc hm n hx hmono)
    (fun n => sortedFaceMonomialApprox_le_boundary hc hm hsym n hx)

end Wishart.Spectral
end
end CanonicalSource23

section CanonicalSource24
/- Source: Wishart/FieldSpectralShift.lean -/




/-!
# Identity shifts and the literal matrix boundary convention

Translation by εI translates every ordered eigenvalue by ε. The proof uses
an actual diagonalization, so multiplicities and zero eigenvalues require no
separate exceptional case. This identifies the spectral boundary used in the
target with the matrix regularization stated in the manuscript.
-/

noncomputable section
open Matrix Set Filter Topology
open scoped Classical Quaternion ComplexOrder

namespace Wishart.FieldSpectral
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}

def identityShift (A : Hermitian 𝕜 p) (t : ℝ) : Hermitian 𝕜 p :=
  A + t • (⟨1, Matrix.isHermitian_one⟩ : Hermitian 𝕜 p)

theorem orderedValues_identityShift (A : Hermitian 𝕜 p) (t : ℝ) :
    orderedValues (WishartVerification.hermitian_matrix_coe (identityShift A t)) =
      fun i => orderedValues (WishartVerification.hermitian_matrix_coe A) i + t := by
  obtain ⟨U, hU⟩ := exists_sorted_diagonalization (WishartVerification.hermitian_matrix_coe A)
  apply orderedValues_eq_of_sorted_diagonalization _ U
  · change (star U : Matrix (Fin p) (Fin p) 𝕜) *
      ((A : Matrix (Fin p) (Fin p) 𝕜) + t • 1) * U = _
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Unitary.coe_star_mul_self, hU]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
        Matrix.one_apply_eq, Algebra.smul_def, mul_one, map_add,
        Matrix.algebraMap_eq_diagonal, Pi.algebraMap_apply,
        RCLike.algebraMap_eq_ofReal, Matrix.diagonal_apply_eq]
    · simp [hij]
  · intro i j hij
    simpa only [add_comm] using
      add_le_add_right (antitone_orderedValues (WishartVerification.hermitian_matrix_coe A) hij) t

theorem identityShift_posDef (A : Hermitian 𝕜 p)
    (hA : (A : Matrix (Fin p) (Fin p) 𝕜).PosSemidef) {t : ℝ} (ht : 0 < t) :
    (identityShift A t : Matrix (Fin p) (Fin p) 𝕜).PosDef :=
  Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul ht)

theorem identityShift_posSemidef (A : Hermitian 𝕜 p)
    (hA : (A : Matrix (Fin p) (Fin p) 𝕜).PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    (identityShift A t : Matrix (Fin p) (Fin p) 𝕜).PosSemidef :=
  hA.add (Matrix.PosDef.one.posSemidef.smul ht)

theorem continuous_identityShift (A : Hermitian 𝕜 p) : Continuous (identityShift A) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem boundary_eq_matrix_regularization {h : (Fin p → ℝ) → ℝ}
    (hm : Monotone h) (A : Hermitian 𝕜 p)
    (hA : (A : Matrix (Fin p) (Fin p) 𝕜).PosSemidef) :
    Tendsto (fun ε : ℝ => Real.exp (h (fun i => Real.log
      (orderedValues (WishartVerification.hermitian_matrix_coe (identityShift A ε)) i))))
      (𝓝[>] 0) (𝓝 (Spectral.spectralBoundaryValue h
        (orderedValues (WishartVerification.hermitian_matrix_coe A)))) := by
  simpa only [orderedValues_identityShift] using
    Spectral.spectralBoundaryValue_tendsto_epsilon hm (orderedValues_nonneg hA)

end Wishart.FieldSpectral

namespace Wishart.QuaternionMatrix
variable {p : ℕ}

def identityShift (A : Hermitian p) (t : ℝ) : Hermitian p :=
  A + t • (⟨1, Matrix.isHermitian_one⟩ : Hermitian p)

theorem flatHermitian_identityShift (A : Hermitian p) (t : ℝ) :
    flatHermitian (identityShift A t) = Wishart.FieldSpectral.identityShift (flatHermitian A) t := by
  apply Subtype.ext
  change (complexRepresentation ((A : Matrix (Fin p) (Fin p) ℍ[ℝ]) + t • 1)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm = _
  simp only [complexRepresentation_add, complexRepresentation_smul,
    complexRepresentation_one, Matrix.submatrix_add, Matrix.submatrix_smul,
    Matrix.submatrix_one_equiv, Pi.add_apply, Pi.smul_apply]
  rfl

theorem orderedValues_identityShift (A : Hermitian p) (t : ℝ) :
    orderedValues (identityShift A t) = fun i => orderedValues A i + t := by
  funext i
  simpa only [orderedValues, flatHermitian_identityShift] using
    congrFun (Wishart.FieldSpectral.orderedValues_identityShift (flatHermitian A) t)
      (doubledIndex i)

theorem identityShift_posDef (A : Hermitian p) (hA : PosSemidef (A : Matrix (Fin p) (Fin p) ℍ[ℝ]))
    {t : ℝ} (ht : 0 < t) : PosDef (identityShift A t : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  change PosDef ((A : Matrix (Fin p) (Fin p) ℍ[ℝ]) + t • 1)
  rw [add_comm]
  exact (posDef_one.smul ht).add_posSemidef hA

theorem identityShift_posSemidef (A : Hermitian p) (hA : PosSemidef (A : Matrix (Fin p) (Fin p) ℍ[ℝ]))
    {t : ℝ} (ht : 0 ≤ t) : PosSemidef (identityShift A t : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  unfold PosSemidef
  change (complexRepresentation ((A : Matrix (Fin p) (Fin p) ℍ[ℝ]) + t • 1)).PosSemidef
  rw [complexRepresentation_add, complexRepresentation_smul, complexRepresentation_one]
  exact Matrix.PosSemidef.add hA (Matrix.PosDef.one.posSemidef.smul ht)

theorem continuous_identityShift (A : Hermitian p) : Continuous (identityShift A) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem boundary_eq_matrix_regularization {h : (Fin p → ℝ) → ℝ}
    (hm : Monotone h) (A : Hermitian p) (hA : PosSemidef (A : Matrix (Fin p) (Fin p) ℍ[ℝ])) :
    Tendsto (fun ε : ℝ => Real.exp (h (fun i => Real.log
      (orderedValues (identityShift A ε) i))))
      (𝓝[>] 0) (𝓝 (Spectral.spectralBoundaryValue h (orderedValues A))) := by
  simpa only [orderedValues_identityShift] using
    Spectral.spectralBoundaryValue_tendsto_epsilon hm (orderedValues_nonneg A hA)

end Wishart.QuaternionMatrix
end
end CanonicalSource24

section CanonicalSource25
/- Source: Wishart/FieldSpectralApproximation.lean -/




/-!
# The same finite spectral approximation on both positive cones

The functions below are defined by actual leading eigenvalue products.
Their equality with the sorted supporting monomials is proved on the entire
PSD cone, including its boundary. This gives continuity, exact boundary
convergence, and the positive-offset row inequality in one construction.
-/

noncomputable section
open Matrix Set Filter Topology
open scoped Classical Quaternion ComplexOrder BigOperators
namespace Wishart.FieldGaussian
open WishartVerification Wishart.Spectral
variable {k : ℕ}

theorem complexSpectralMonomial_eq_coordinate {a : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (b : ℝ)
    (A : FieldSpectral.Hermitian ℂ k)
    (hA : (A : Matrix (Fin k) (Fin k) ℂ).PosSemidef) :
    complexSpectralMonomial a b A = finiteCoordinateMonomial a b
      (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe A)) := by
  rw [finiteCoordinateMonomial_eq_leadingProducts ha hmono b
    (FieldSpectral.orderedValues_nonneg hA)]
  rfl

theorem quaternionSpectralMonomial_eq_coordinate {a : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (b : ℝ)
    (A : QuaternionMatrix.Hermitian k) (hA : QuaternionMatrix.PosSemidef (A : Matrix (Fin k) (Fin k) ℍ[ℝ])) :
    quaternionSpectralMonomial a b A =
      finiteCoordinateMonomial a b (QuaternionMatrix.orderedValues A) := by
  rw [finiteCoordinateMonomial_eq_leadingProducts ha hmono b
    (QuaternionMatrix.orderedValues_nonneg A hA)]
  unfold quaternionSpectralMonomial
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [QuaternionMatrix.leadingEigenvalueProduct_eq_orderedValues _ A hA]
  rfl

def complexFaceApprox {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    (A : FieldSpectral.Hermitian ℂ k) : ℝ :=
  finiteMaximum (fun z : FiniteFace h × Fin (n + 1) =>
    let D := chosenFaceSupportingSequence hc hm z.1
    complexSpectralMonomial
      (sortedCoefficients (extendFaceSlopes z.1.val (D.slope z.2))) (D.intercept z.2) A)

def quaternionFaceApprox {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    (A : QuaternionMatrix.Hermitian k) : ℝ :=
  finiteMaximum (fun z : FiniteFace h × Fin (n + 1) =>
    let D := chosenFaceSupportingSequence hc hm z.1
    quaternionSpectralMonomial
      (sortedCoefficients (extendFaceSlopes z.1.val (D.slope z.2))) (D.intercept z.2) A)

theorem continuous_complexFaceApprox {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ) :
    Continuous (complexFaceApprox hc hm n) := by
  apply continuous_finiteMaximum
  intro z
  apply continuous_complexSpectralMonomial
  · exact sortedCoefficients_nonneg (extendFaceSlopes_nonneg z.1.val
      ((chosenFaceSupportingSequence hc hm z.1).nonnegative z.2))
  · exact antitone_sortedCoefficients _

theorem continuous_quaternionFaceApprox {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ) :
    Continuous (quaternionFaceApprox hc hm n) := by
  apply continuous_finiteMaximum
  intro z
  apply continuous_quaternionSpectralMonomial
  · exact sortedCoefficients_nonneg (extendFaceSlopes_nonneg z.1.val
      ((chosenFaceSupportingSequence hc hm z.1).nonnegative z.2))
  · exact antitone_sortedCoefficients _

theorem complexFaceApprox_eq_sorted {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    (A : FieldSpectral.Hermitian ℂ k)
    (hA : (A : Matrix (Fin k) (Fin k) ℂ).PosSemidef) :
    complexFaceApprox hc hm n A = sortedFaceMonomialApprox hc hm n
      (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe A)) := by
  apply congrArg finiteMaximum
  funext z
  apply complexSpectralMonomial_eq_coordinate _ (antitone_sortedCoefficients _) _ A hA
  exact sortedCoefficients_nonneg (extendFaceSlopes_nonneg z.1.val
    ((chosenFaceSupportingSequence hc hm z.1).nonnegative z.2))

theorem quaternionFaceApprox_eq_sorted {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    (A : QuaternionMatrix.Hermitian k) (hA : QuaternionMatrix.PosSemidef (A : Matrix (Fin k) (Fin k) ℍ[ℝ])) :
    quaternionFaceApprox hc hm n A =
      sortedFaceMonomialApprox hc hm n (QuaternionMatrix.orderedValues A) := by
  apply congrArg finiteMaximum
  funext z
  apply quaternionSpectralMonomial_eq_coordinate _ (antitone_sortedCoefficients _) _ A hA
  exact sortedCoefficients_nonneg (extendFaceSlopes_nonneg z.1.val
    ((chosenFaceSupportingSequence hc hm z.1).nonnegative z.2))

theorem complexFaceApprox_nonneg {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    (A : FieldSpectral.Hermitian ℂ k)
    (hA : (A : Matrix (Fin k) (Fin k) ℂ).PosSemidef) : 0 ≤ complexFaceApprox hc hm n A := by
  rw [complexFaceApprox_eq_sorted hc hm n A hA]
  exact sortedFaceMonomialApprox_nonneg hc hm n (FieldSpectral.orderedValues_nonneg hA)

theorem quaternionFaceApprox_nonneg {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    (A : QuaternionMatrix.Hermitian k) (hA : QuaternionMatrix.PosSemidef (A : Matrix (Fin k) (Fin k) ℍ[ℝ])) :
    0 ≤ quaternionFaceApprox hc hm n A := by
  rw [quaternionFaceApprox_eq_sorted hc hm n A hA]
  exact sortedFaceMonomialApprox_nonneg hc hm n (QuaternionMatrix.orderedValues_nonneg A hA)

theorem complexFaceApprox_monotone_index {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (A : FieldSpectral.Hermitian ℂ k) :
    Monotone (fun n => complexFaceApprox hc hm n A) := by
  intro n m hnm
  change complexFaceApprox hc hm n A ≤ complexFaceApprox hc hm m A
  apply finiteMaximum_le
  intro z
  exact le_finiteMaximum
    (fun w : FiniteFace h × Fin (m + 1) =>
      let D := chosenFaceSupportingSequence hc hm w.1
      complexSpectralMonomial
        (sortedCoefficients (extendFaceSlopes w.1.val (D.slope w.2))) (D.intercept w.2) A)
    (z.1, ⟨z.2, lt_of_lt_of_le z.2.isLt (Nat.add_le_add_right hnm 1)⟩)

theorem quaternionFaceApprox_monotone_index {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (A : QuaternionMatrix.Hermitian k) :
    Monotone (fun n => quaternionFaceApprox hc hm n A) := by
  intro n m hnm
  change quaternionFaceApprox hc hm n A ≤ quaternionFaceApprox hc hm m A
  apply finiteMaximum_le
  intro z
  exact le_finiteMaximum
    (fun w : FiniteFace h × Fin (m + 1) =>
      let D := chosenFaceSupportingSequence hc hm w.1
      quaternionSpectralMonomial
        (sortedCoefficients (extendFaceSlopes w.1.val (D.slope w.2))) (D.intercept w.2) A)
    (z.1, ⟨z.2, lt_of_lt_of_le z.2.isLt (Nat.add_le_add_right hnm 1)⟩)

theorem complexFaceApprox_le_boundary {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (hsym : SymmetricProfile h) (n : ℕ)
    (A : FieldSpectral.Hermitian ℂ k)
    (hA : (A : Matrix (Fin k) (Fin k) ℂ).PosSemidef) :
    complexFaceApprox hc hm n A ≤ spectralBoundaryValue h
      (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe A)) := by
  rw [complexFaceApprox_eq_sorted hc hm n A hA]
  exact sortedFaceMonomialApprox_le_boundary hc hm hsym n (FieldSpectral.orderedValues_nonneg hA)

theorem quaternionFaceApprox_le_boundary {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (hsym : SymmetricProfile h) (n : ℕ)
    (A : QuaternionMatrix.Hermitian k) (hA : QuaternionMatrix.PosSemidef (A : Matrix (Fin k) (Fin k) ℍ[ℝ])) :
    quaternionFaceApprox hc hm n A ≤ spectralBoundaryValue h (QuaternionMatrix.orderedValues A) := by
  rw [quaternionFaceApprox_eq_sorted hc hm n A hA]
  exact sortedFaceMonomialApprox_le_boundary hc hm hsym n (QuaternionMatrix.orderedValues_nonneg A hA)

theorem complexFaceApprox_tendsto {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (hsym : SymmetricProfile h)
    (A : FieldSpectral.Hermitian ℂ k)
    (hA : (A : Matrix (Fin k) (Fin k) ℂ).PosSemidef) :
    Tendsto (fun n => complexFaceApprox hc hm n A) atTop
      (𝓝 (spectralBoundaryValue h (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe A)))) := by
  simp_rw [complexFaceApprox_eq_sorted hc hm _ A hA]
  exact sortedFaceMonomialApprox_tendsto hc hm hsym
    (FieldSpectral.orderedValues_nonneg hA) (FieldSpectral.antitone_orderedValues _)

theorem quaternionFaceApprox_tendsto {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (hsym : SymmetricProfile h)
    (A : QuaternionMatrix.Hermitian k) (hA : QuaternionMatrix.PosSemidef (A : Matrix (Fin k) (Fin k) ℍ[ℝ])) :
    Tendsto (fun n => quaternionFaceApprox hc hm n A) atTop
      (𝓝 (spectralBoundaryValue h (QuaternionMatrix.orderedValues A))) := by
  simp_rw [quaternionFaceApprox_eq_sorted hc hm _ A hA]
  exact sortedFaceMonomialApprox_tendsto hc hm hsym
    (QuaternionMatrix.orderedValues_nonneg A hA) (QuaternionMatrix.orderedValues_antitone A)

theorem positiveLogSubmean_complexFaceApprox {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    (Q : FieldSpectral.Hermitian ℂ k)
    (hQ : (Q : Matrix (Fin k) (Fin k) ℂ).PosDef) (z v : Row ℂ k) :
    PositiveLogSubmean (fun u => complexFaceApprox hc hm n (hermitianRowUpdate ℂ Q z v u)) := by
  apply PositiveLogSubmean.finiteMaximum
  intro z'
  apply positiveLogSubmean_complex_monomial _ (antitone_sortedCoefficients _) _ Q hQ z v
  exact sortedCoefficients_nonneg (extendFaceSlopes_nonneg z'.1.val
    ((chosenFaceSupportingSequence hc hm z'.1).nonnegative z'.2))

theorem positiveLogSubmean_quaternionFaceApprox {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    (Q : QuaternionMatrix.Hermitian k)
    (hQ : QuaternionMatrix.PosDef (Q : Matrix (Fin k) (Fin k) ℍ[ℝ])) (z v : Row ℍ[ℝ] k) :
    PositiveLogSubmean (fun u => quaternionFaceApprox hc hm n
      (hermitianRowUpdate ℍ[ℝ] Q z v u)) := by
  apply PositiveLogSubmean.finiteMaximum
  intro z'
  apply positiveLogSubmean_quaternion_monomial _ (antitone_sortedCoefficients _) _ Q hQ z v
  exact sortedCoefficients_nonneg (extendFaceSlopes_nonneg z'.1.val
    ((chosenFaceSupportingSequence hc hm z'.1).nonnegative z'.2))

end Wishart.FieldGaussian
end
end CanonicalSource25

section CanonicalSource26
/- Source: Wishart/FieldBoundarySubmean.lean -/



/-!
# Submean inequalities on singular offsets

All regularization hypotheses are discharged for the concrete finite spectral
approximants. The last two theorems allow a different matrix size, compression,
offset, and row direction in each factor. Only their scalar update is shared.
Zeros in one factor cause no logarithm-of-zero convention in the proof.
-/

noncomputable section
open scoped Matrix.Norms.Frobenius
open Matrix Set Filter Topology
open scoped Classical Quaternion ComplexOrder BigOperators
namespace Wishart.FieldGaussian
open WishartVerification Wishart.Spectral

section RowAlgebra
variable (F : Type*) [NormedDivisionRing F]
  [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

theorem hermitianRowUpdate_add {k : ℕ}
    (Q R : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F))
    (z v : Row F k) (u : F) :
    hermitianRowUpdate F (Q + R) z v u = hermitianRowUpdate F Q z v u + R := by
  apply Subtype.ext
  change ((Q : Matrix (Fin k) (Fin k) F) + R) + rowGram F (rowShift F z u v) =
    ((Q : Matrix (Fin k) (Fin k) F) + rowGram F (rowShift F z u v)) + R
  abel

end RowAlgebra

theorem complex_rowUpdate_posSemidef {k : ℕ} (Q : FieldSpectral.Hermitian ℂ k)
    (hQ : (Q : Matrix (Fin k) (Fin k) ℂ).PosSemidef) (z v : Row ℂ k) (u : ℂ) :
    (hermitianRowUpdate ℂ Q z v u : Matrix (Fin k) (Fin k) ℂ).PosSemidef := by
  change ((Q : Matrix (Fin k) (Fin k) ℂ) + rowGram ℂ (rowShift ℂ z u v)).PosSemidef
  rw [rowGram_eq_matrix]
  exact hQ.add (Matrix.posSemidef_conjTranspose_mul_self _)

theorem quaternion_rowUpdate_posSemidef {k : ℕ} (Q : QuaternionMatrix.Hermitian k)
    (hQ : QuaternionMatrix.PosSemidef (Q : Matrix (Fin k) (Fin k) ℍ[ℝ])) (z v : Row ℍ[ℝ] k) (u : ℍ[ℝ]) :
    QuaternionMatrix.PosSemidef
      (hermitianRowUpdate ℍ[ℝ] Q z v u : Matrix (Fin k) (Fin k) ℍ[ℝ]) := by
  change QuaternionMatrix.PosSemidef ((Q : Matrix (Fin k) (Fin k) ℍ[ℝ]) +
    rowGram ℍ[ℝ] (rowShift ℍ[ℝ] z u v))
  rw [rowGram_eq_matrix]
  exact hQ.add (QuaternionMatrix.posSemidef_gram _)

theorem complexFaceApprox_monotone_shift {k : ℕ} {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    (A : FieldSpectral.Hermitian ℂ k)
    (hA : (A : Matrix (Fin k) (Fin k) ℂ).PosSemidef) :
    MonotoneOn (fun ε : ℝ => complexFaceApprox hc hm n (FieldSpectral.identityShift A ε))
      (Ici 0) := by
  intro s hs t ht hst
  change complexFaceApprox hc hm n (FieldSpectral.identityShift A s) ≤
    complexFaceApprox hc hm n (FieldSpectral.identityShift A t)
  rw [complexFaceApprox_eq_sorted hc hm n _ (FieldSpectral.identityShift_posSemidef A hA hs),
    complexFaceApprox_eq_sorted hc hm n _ (FieldSpectral.identityShift_posSemidef A hA ht),
    FieldSpectral.orderedValues_identityShift, FieldSpectral.orderedValues_identityShift]
  exact sortedFaceMonomialApprox_mono hc hm n
    (fun i => add_nonneg (FieldSpectral.orderedValues_nonneg hA i) hs)
    (fun i => add_le_add le_rfl hst)

theorem quaternionFaceApprox_monotone_shift {k : ℕ} {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (n : ℕ)
    (A : QuaternionMatrix.Hermitian k) (hA : QuaternionMatrix.PosSemidef (A : Matrix (Fin k) (Fin k) ℍ[ℝ])) :
    MonotoneOn (fun ε : ℝ => quaternionFaceApprox hc hm n (QuaternionMatrix.identityShift A ε))
      (Ici 0) := by
  intro s hs t ht hst
  change quaternionFaceApprox hc hm n (QuaternionMatrix.identityShift A s) ≤
    quaternionFaceApprox hc hm n (QuaternionMatrix.identityShift A t)
  rw [quaternionFaceApprox_eq_sorted hc hm n _ (QuaternionMatrix.identityShift_posSemidef A hA hs),
    quaternionFaceApprox_eq_sorted hc hm n _ (QuaternionMatrix.identityShift_posSemidef A hA ht),
    QuaternionMatrix.orderedValues_identityShift, QuaternionMatrix.orderedValues_identityShift]
  exact sortedFaceMonomialApprox_mono hc hm n
    (fun i => add_nonneg (QuaternionMatrix.orderedValues_nonneg A hA i) hs)
    (fun i => add_le_add le_rfl hst)

theorem ballSubmean_complexFaceApprox_product {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (n : ι → ℕ)
    (Q : ∀ i, FieldSpectral.Hermitian ℂ (k i))
    (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (z v : ∀ i, Row ℂ (k i)) :
    BallSubmean (fun u : ℂ => ∏ i, complexFaceApprox (hc i) (hm i) (n i)
      (hermitianRowUpdate ℂ (Q i) (z i) (v i) u)) := by
  let V := ∀ i, FieldSpectral.Hermitian ℂ (k i)
  let A : ℂ → V := fun u i => hermitianRowUpdate ℂ (Q i) (z i) (v i) u
  let I : V := fun i => ⟨1, Matrix.isHermitian_one⟩
  let g : V → ℝ := fun X => ∏ i, complexFaceApprox (hc i) (hm i) (n i) (X i)
  have hA : Continuous A := continuous_pi fun i => continuous_hermitianRowUpdate ℂ _ _ _
  have hg : Continuous g := continuous_finsetProd _ fun i _ =>
    (continuous_complexFaceApprox (hc i) (hm i) (n i)).comp (continuous_apply i)
  apply BallSubmean.of_positive_scalar_regularization A hA I hg
  · intro u s hs t ht hst
    apply Finset.prod_le_prod₀
    · intro i hi
      exact complexFaceApprox_nonneg (hc i) (hm i) (n i) _
        (FieldSpectral.identityShift_posSemidef _
          (complex_rowUpdate_posSemidef (Q i) (hQ i) (z i) (v i) u) hs)
    · intro i hi
      exact complexFaceApprox_monotone_shift (hc i) (hm i) (n i) _
        (complex_rowUpdate_posSemidef (Q i) (hQ i) (z i) (v i) u) hs ht hst
  · intro ε hε
    apply PositiveLogSubmean.finset_prod
    intro i hi
    have h := positiveLogSubmean_complexFaceApprox (hc i) (hm i) (n i)
      (FieldSpectral.identityShift (Q i) ε)
      (FieldSpectral.identityShift_posDef (Q i) (hQ i) hε) (z i) (v i)
    have heq : (fun u : ℂ => complexFaceApprox (hc i) (hm i) (n i)
        (hermitianRowUpdate ℂ (FieldSpectral.identityShift (Q i) ε) (z i) (v i) u)) =
        fun u => complexFaceApprox (hc i) (hm i) (n i) ((A u + ε • I) i) := by
      funext u
      congr 1
      exact hermitianRowUpdate_add ℂ (Q i) (ε • I i) (z i) (v i) u
    rwa [heq] at h

theorem ballSubmean_quaternionFaceApprox_product {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (n : ι → ℕ)
    (Q : ∀ i, QuaternionMatrix.Hermitian (k i))
    (hQ : ∀ i, QuaternionMatrix.PosSemidef (Q i : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]))
    (z v : ∀ i, Row ℍ[ℝ] (k i)) :
    BallSubmean (fun u : ℍ[ℝ] => ∏ i, quaternionFaceApprox (hc i) (hm i) (n i)
      (hermitianRowUpdate ℍ[ℝ] (Q i) (z i) (v i) u)) := by
  let V := ∀ i, QuaternionMatrix.Hermitian (k i)
  let A : ℍ[ℝ] → V := fun u i => hermitianRowUpdate ℍ[ℝ] (Q i) (z i) (v i) u
  let I : V := fun i => ⟨1, Matrix.isHermitian_one⟩
  let g : V → ℝ := fun X => ∏ i, quaternionFaceApprox (hc i) (hm i) (n i) (X i)
  have hA : Continuous A := continuous_pi fun i => continuous_hermitianRowUpdate ℍ[ℝ] _ _ _
  have hg : Continuous g := continuous_finsetProd _ fun i _ =>
    (continuous_quaternionFaceApprox (hc i) (hm i) (n i)).comp (continuous_apply i)
  apply BallSubmean.of_positive_scalar_regularization A hA I hg
  · intro u s hs t ht hst
    apply Finset.prod_le_prod₀
    · intro i hi
      exact quaternionFaceApprox_nonneg (hc i) (hm i) (n i) _
        (QuaternionMatrix.identityShift_posSemidef _
          (quaternion_rowUpdate_posSemidef (Q i) (hQ i) (z i) (v i) u) hs)
    · intro i hi
      exact quaternionFaceApprox_monotone_shift (hc i) (hm i) (n i) _
        (quaternion_rowUpdate_posSemidef (Q i) (hQ i) (z i) (v i) u) hs ht hst
  · intro ε hε
    apply PositiveLogSubmean.finset_prod
    intro i hi
    have h := positiveLogSubmean_quaternionFaceApprox (hc i) (hm i) (n i)
      (QuaternionMatrix.identityShift (Q i) ε)
      (QuaternionMatrix.identityShift_posDef (Q i) (hQ i) hε) (z i) (v i)
    have heq : (fun u : ℍ[ℝ] => quaternionFaceApprox (hc i) (hm i) (n i)
        (hermitianRowUpdate ℍ[ℝ] (QuaternionMatrix.identityShift (Q i) ε) (z i) (v i) u)) =
        fun u => quaternionFaceApprox (hc i) (hm i) (n i) ((A u + ε • I) i) := by
      funext u
      congr 1
      exact hermitianRowUpdate_add ℍ[ℝ] (Q i) (ε • I i) (z i) (v i) u
    rwa [heq] at h

end Wishart.FieldGaussian
end
end CanonicalSource26

section CanonicalSource27
/- Source: Wishart/FieldApproximationGrowth.lean -/




/-!
# Polynomial growth of the actual boundary-preserving approximants

Every leading product is bounded by the appropriate power of the real trace.
The trace under a compressed row update is a constant plus a squared row norm.
The resulting natural-degree envelope is uniform in both the Gaussian row
and the field scalar. Products and finite maxima therefore have the explicit
growth needed for Fubini and dominated convergence in Lemma 7.2.
-/

noncomputable section
open Matrix
open scoped Classical Quaternion ComplexOrder BigOperators
namespace Wishart.FieldGaussian
open WishartVerification Wishart.Spectral

section CompressedRow
variable (F : Type*) [NormedDivisionRing F]
  [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]
variable {m k : ℕ}

theorem rowFactor_rowShift (B : Matrix (Fin m) (Fin k) F)
    (z v : Row F m) (u : F) :
    rowFactorCLM F B (rowShift F z u v) =
      rowShift F (rowFactorCLM F B z) u (rowFactorCLM F B v) := by
  ext j
  simp only [rowFactorCLM_apply, rowShift_apply, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

def compressedHermitianRowUpdate
    (Q : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F))
    (B : Matrix (Fin m) (Fin k) F) (v : Row F m) (w : Row F m × F) :
    selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F) :=
  hermitianRowUpdate F Q (rowFactorCLM F B w.1) (rowFactorCLM F B v) w.2

theorem continuous_compressedHermitianRowUpdate
    (Q : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F))
    (B : Matrix (Fin m) (Fin k) F) (v : Row F m) :
    Continuous (compressedHermitianRowUpdate F Q B v) := by
  apply Continuous.subtype_mk
  dsimp only [compressedHermitianRowUpdate, hermitianRowUpdate, rowGram, rowShift]
  fun_prop

theorem trace_compressedHermitianRowUpdate (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (Q : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F))
    (B : Matrix (Fin m) (Fin k) F) (v : Row F m) (w : Row F m × F) :
    realTrace F re (compressedHermitianRowUpdate F Q B v w : Matrix (Fin k) (Fin k) F) =
      realTrace F re (Q : Matrix (Fin k) (Fin k) F) + ‖rowFactorCLM F B (rowShift F w.1 w.2 v)‖ ^ 2 := by
  change realTrace F re ((Q : Matrix (Fin k) (Fin k) F) +
    rowGram F (rowShift F (rowFactorCLM F B w.1) w.2 (rowFactorCLM F B v))) = _
  rw [← rowFactor_rowShift, realTrace_add, realTrace_rowGram F re hstar]

theorem polynomial_trace_compressedHermitianRowUpdate (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (Q : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F))
    (B : Matrix (Fin m) (Fin k) F) (v : Row F m) :
    JointPolynomialBound (fun w => realTrace F re
      (compressedHermitianRowUpdate F Q B v w : Matrix (Fin k) (Fin k) F)) := by
  have h := (JointPolynomialBound.const (realTrace F re (Q : Matrix (Fin k) (Fin k) F))).add
    ((polynomial_compressedRow_norm F B v).rpow (show (0 : ℝ) ≤ 2 by norm_num))
  simpa only [trace_compressedHermitianRowUpdate F re hstar, Real.rpow_two] using h

end CompressedRow

theorem complex_realTrace_eq {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    realTrace ℂ Complex.reLm A = A.trace.re := by
  change (∑ i, (A i i).re) = (∑ i, A i i).re
  rw [Complex.re_sum]

theorem quaternion_realTrace_eq {k : ℕ} (A : Matrix (Fin k) (Fin k) ℍ[ℝ]) :
    realTrace ℍ[ℝ] (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) A = A.trace.re := by
  change (∑ i, (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) (A i i)) = (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) (∑ i, A i i)
  rw [map_sum]

theorem complex_re_star_mul (a : ℂ) : Complex.reLm (star a * a) = ‖a‖ ^ 2 := by
  change (star a * a).re = ‖a‖ ^ 2
  simp only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem quaternion_re_star_mul (a : ℍ[ℝ]) :
    (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) (star a * a) = ‖a‖ ^ 2 := by
  rw [Quaternion.star_mul_self]
  change Quaternion.normSq a = ‖a‖ ^ 2
  rw [Quaternion.normSq_eq_norm_mul_self, pow_two]

theorem polynomial_complex_leading_row {m k j : ℕ} (hj : j ≤ k)
    (Q : FieldSpectral.Hermitian ℂ k)
    (hQ : (Q : Matrix (Fin k) (Fin k) ℂ).PosSemidef)
    (B : Matrix (Fin m) (Fin k) ℂ) (v : Row ℂ m) :
    JointPolynomialBound (fun w => FieldSpectral.leadingEigenvalueProduct hj
      (WishartVerification.hermitian_matrix_coe (compressedHermitianRowUpdate ℂ Q B v w))) := by
  have h := (polynomial_trace_compressedHermitianRowUpdate ℂ Complex.reLm
    complex_re_star_mul Q B v).rpow (show (0 : ℝ) ≤ j by positivity)
  simp only [Real.rpow_natCast, complex_realTrace_eq] at h
  apply h.mono
  intro w
  have hA : (compressedHermitianRowUpdate ℂ Q B v w :
      Matrix (Fin k) (Fin k) ℂ).PosSemidef :=
    complex_rowUpdate_posSemidef Q hQ (rowFactorCLM ℂ B w.1)
      (rowFactorCLM ℂ B v) w.2
  rw [Real.norm_of_nonneg (FieldSpectral.leadingEigenvalueProduct_nonneg hj hA),
    Real.norm_eq_abs]
  exact (FieldSpectral.leadingEigenvalueProduct_le_trace_pow hj hA).trans (le_abs_self _)

theorem polynomial_quaternion_leading_row {m k j : ℕ} (hj : j ≤ k)
    (Q : QuaternionMatrix.Hermitian k) (hQ : QuaternionMatrix.PosSemidef (Q : Matrix (Fin k) (Fin k) ℍ[ℝ]))
    (B : Matrix (Fin m) (Fin k) ℍ[ℝ]) (v : Row ℍ[ℝ] m) :
    JointPolynomialBound (fun w => QuaternionMatrix.leadingEigenvalueProduct hj
      (WishartVerification.hermitian_matrix_coe (compressedHermitianRowUpdate ℍ[ℝ] Q B v w))) := by
  have h := (polynomial_trace_compressedHermitianRowUpdate ℍ[ℝ] (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))
    quaternion_re_star_mul Q B v).rpow (show (0 : ℝ) ≤ j by positivity)
  simp only [Real.rpow_natCast, quaternion_realTrace_eq] at h
  apply h.mono
  intro w
  have hA := quaternion_rowUpdate_posSemidef Q hQ (rowFactorCLM ℍ[ℝ] B w.1)
    (rowFactorCLM ℍ[ℝ] B v) w.2
  rw [Real.norm_of_nonneg (QuaternionMatrix.leadingEigenvalueProduct_nonneg hj _),
    Real.norm_eq_abs]
  exact (QuaternionMatrix.leadingEigenvalueProduct_le_trace_pow hj hA).trans (le_abs_self _)

theorem polynomial_complex_monomial_row {m k : ℕ} {a : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (b : ℝ)
    (Q : FieldSpectral.Hermitian ℂ k)
    (hQ : (Q : Matrix (Fin k) (Fin k) ℂ).PosSemidef)
    (B : Matrix (Fin m) (Fin k) ℂ) (v : Row ℂ m) :
    JointPolynomialBound (fun w => complexSpectralMonomial a b
      (compressedHermitianRowUpdate ℂ Q B v w)) := by
  apply (JointPolynomialBound.const (Real.exp b)).mul
  apply JointPolynomialBound.finset_prod
  intro j hj
  exact (polynomial_complex_leading_row _ Q hQ B v).rpow (slopeDrop_nonneg ha hmono j)

theorem polynomial_quaternion_monomial_row {m k : ℕ} {a : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (b : ℝ)
    (Q : QuaternionMatrix.Hermitian k) (hQ : QuaternionMatrix.PosSemidef (Q : Matrix (Fin k) (Fin k) ℍ[ℝ]))
    (B : Matrix (Fin m) (Fin k) ℍ[ℝ]) (v : Row ℍ[ℝ] m) :
    JointPolynomialBound (fun w => quaternionSpectralMonomial a b
      (compressedHermitianRowUpdate ℍ[ℝ] Q B v w)) := by
  apply (JointPolynomialBound.const (Real.exp b)).mul
  apply JointPolynomialBound.finset_prod
  intro j hj
  exact (polynomial_quaternion_leading_row _ Q hQ B v).rpow (slopeDrop_nonneg ha hmono j)

theorem polynomial_complexFaceApprox_row {m k : ℕ} {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ Set.univ h) (hm : Monotone h) (n : ℕ)
    (Q : FieldSpectral.Hermitian ℂ k)
    (hQ : (Q : Matrix (Fin k) (Fin k) ℂ).PosSemidef)
    (B : Matrix (Fin m) (Fin k) ℂ) (v : Row ℂ m) :
    JointPolynomialBound (fun w => complexFaceApprox hc hm n
      (compressedHermitianRowUpdate ℂ Q B v w)) := by
  apply JointPolynomialBound.finiteMaximum
  intro z
  apply polynomial_complex_monomial_row _ (antitone_sortedCoefficients _) _ Q hQ B v
  exact sortedCoefficients_nonneg (extendFaceSlopes_nonneg z.1.val
    ((chosenFaceSupportingSequence hc hm z.1).nonnegative z.2))

theorem polynomial_quaternionFaceApprox_row {m k : ℕ} {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ Set.univ h) (hm : Monotone h) (n : ℕ)
    (Q : QuaternionMatrix.Hermitian k) (hQ : QuaternionMatrix.PosSemidef (Q : Matrix (Fin k) (Fin k) ℍ[ℝ]))
    (B : Matrix (Fin m) (Fin k) ℍ[ℝ]) (v : Row ℍ[ℝ] m) :
    JointPolynomialBound (fun w => quaternionFaceApprox hc hm n
      (compressedHermitianRowUpdate ℍ[ℝ] Q B v w)) := by
  apply JointPolynomialBound.finiteMaximum
  intro z
  apply polynomial_quaternion_monomial_row _ (antitone_sortedCoefficients _) _ Q hQ B v
  exact sortedCoefficients_nonneg (extendFaceSlopes_nonneg z.1.val
    ((chosenFaceSupportingSequence hc hm z.1).nonnegative z.2))

end Wishart.FieldGaussian
end
end CanonicalSource27


section CanonicalSource28
/- Source: Wishart/FieldMatrixGaussianInvariance.lean -/



/-!
# Unitary invariance of the actual field laws

The normalized rectangular Gaussian density is invariant under left unitary
multiplication because its Gram matrix is unchanged. The corresponding map
is an actual real linear equivalence. The identical argument, using the
proved density congruence identity, gives unitary invariance of the literal
real-shape Wishart law. No Haar-disintegration premise is used here.
-/

noncomputable section
open scoped Matrix.Norms.Frobenius
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.FieldGaussian
open Wishart.FieldDensity WishartVerification.FieldDensity

variable (F : Type*) [NormedRing F]
  [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [StarModule ℝ F]
  [FiniteDimensional ℝ F] [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

@[reducible] local instance compatibleScalarAlgebraStage3 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le

theorem realTrace_matrixGram {p q : ℕ} (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (Z : Matrix (Fin p) (Fin q) F) :
    realTrace F re (Zᴴ * Z) = rectangularNormSquare Z := by
  simp only [realTrace, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, hstar]
  exact Finset.sum_comm

theorem rectangularNormSquare_unitary_left {p q : ℕ} (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (U : unitary (Matrix (Fin p) (Fin p) F)) (Z : Matrix (Fin p) (Fin q) F) :
    rectangularNormSquare (U.val * Z) = rectangularNormSquare Z := by
  rw [← realTrace_matrixGram F re hstar, ← realTrace_matrixGram F re hstar,
    Matrix.conjTranspose_mul]
  have hU : U.valᴴ * U.val = 1 := Unitary.coe_star_mul_self U
  have heq : Zᴴ * U.valᴴ * (U.val * Z) = Zᴴ * Z := by
    calc
      _ = Zᴴ * (U.valᴴ * U.val) * Z := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]
  rw [heq]

theorem matrixGaussian_map_unitary_left {p q : ℕ} (hF : 0 < Module.finrank ℝ F)
    (re : F →ₗ[ℝ] ℝ) (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (U : unitary (Matrix (Fin p) (Fin p) F)) :
    (matrixGaussian F p q).map (fun Z => U.val * Z) =
      matrixGaussian F p q := by
  let e := Wishart.FieldJacobian.leftActionCL (m := Fin q)
    U.val Unitary.isUnit_coe
  have h := @normalized_transport_haar
    (Matrix (Fin p) (Fin q) F) (Matrix (Fin p) (Fin q) F)
    _ _ _ _ (by exact inferInstanceAs (BorelSpace (Matrix (Fin p) (Fin q) F)))
    _ _ _ _ (by exact inferInstanceAs (BorelSpace (Matrix (Fin p) (Fin q) F))) e
    (Wishart.FieldHermitian.rectangularLebesgue F p q)
    (Wishart.FieldHermitian.rectangularLebesgue F p q)
    (by exact inferInstanceAs (Measure.IsAddHaarMeasure
      (Wishart.FieldHermitian.rectangularLebesgue F p q)))
    (by exact inferInstanceAs (Measure.IsAddHaarMeasure
      (Wishart.FieldHermitian.rectangularLebesgue F p q))) (matrixKernel F) (matrixKernel F)
    (finiteDensity_matrixKernel_and_law F p q hF).1 (fun Z => by
      change matrixKernel F (e Z) = matrixKernel F Z
      rw [show e Z = U.val * Z from
        Wishart.FieldJacobian.leftActionCL_apply _ _ Z]
      unfold matrixKernel
      rw [rectangularNormSquare_unitary_left F re hstar])
  rw [(finiteDensity_matrixKernel_and_law F p q hF).2] at h
  have hmap := h.2.symm
  change (matrixGaussian F p q).map (fun Z => U.val * Z) = matrixGaussian F p q at hmap
  exact hmap

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
open WishartVerification.FieldDensity

theorem wishartMeasure_map_unitary {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α)
    (U : unitary (Matrix (Fin p) (Fin p) ℂ)) :
    (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ)).map
      (Wishart.FieldHermitian.congruence ℂ U.val) = wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ) := by
  have he : Wishart.FieldCharts.unitaryConjugate ℂ (star U) =
      Wishart.FieldHermitian.congruence ℂ U.val := by
    funext X
    apply Subtype.ext
    simp only [Wishart.FieldCharts.unitaryConjugate, Wishart.FieldHermitian.congruence,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [← he]
  exact map_unitaryConjugate_wishart hα (star U)

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open WishartVerification.FieldDensity

theorem wishartMeasure_map_unitary {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α)
    (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) :
    (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])).map
      (Wishart.FieldHermitian.congruence ℍ[ℝ] U.val) =
        wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  have he : Wishart.FieldCharts.unitaryConjugate ℍ[ℝ] (star U) =
      Wishart.FieldHermitian.congruence ℍ[ℝ] U.val := by
    funext X
    apply Subtype.ext
    simp only [Wishart.FieldCharts.unitaryConjugate, Wishart.FieldHermitian.congruence,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [← he]
  exact map_unitaryConjugate_wishart hα (star U)

end Wishart.QuaternionMatrix
end
end CanonicalSource28

section CanonicalSource29
/- Source: Wishart/FieldSingleRowComparison.lean -/




/-!
# The concrete complex and quaternion single-row comparison

The two comparison theorems below have no analytic proof obligation in their
signatures. They use an actual centered field Gaussian row, allow its covariance
factor to be rectangular or singular, and allow arbitrary overlapping fixed
compressions and PSD offsets. Polynomial envelopes, Gaussian phase invariance,
continuity, and all submean inequalities are proved in their dependency chain.

These are the finite-approximation form of Lemma 7.2. Passing to the full profile
uses the already stated boundary-preserving limit, and the principal product
theorem additionally needs regression and association for the selected spectrum.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder BigOperators
namespace Wishart.FieldGaussian
open WishartVerification Wishart.Spectral

section CompressedGram
variable (F : Type*) [NormedDivisionRing F]
  [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]
variable {m k : ℕ}

def compressedRowGram
    (Q : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F))
    (B : Matrix (Fin m) (Fin k) F) (z : Row F m) :
    selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F) :=
  ⟨(Q : Matrix (Fin k) (Fin k) F) + rowGram F (rowFactorCLM F B z), by
    rw [rowGram_eq_matrix]
    exact (WishartVerification.hermitian_matrix_coe Q).add
      (Matrix.isHermitian_conjTranspose_mul_self _)⟩

theorem compressedHermitianRowUpdate_real
    (Q : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F))
    (B : Matrix (Fin m) (Fin k) F) (z v : Row F m) (t : ℝ) :
    compressedHermitianRowUpdate F Q B v (z, t • (1 : F)) =
      compressedRowGram F Q B (z + t • v) := by
  apply Subtype.ext
  change (Q : Matrix (Fin k) (Fin k) F) +
    rowGram F (rowShift F (rowFactorCLM F B z) (t • (1 : F)) (rowFactorCLM F B v)) = _
  rw [rowShift_real]
  simp only [compressedRowGram, map_add, map_smul]

theorem compressedHermitianRowUpdate_phase
    (Q : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F))
    (B : Matrix (Fin m) (Fin k) F) (z v : Row F m) (u : unitary F) (a : F) :
    compressedHermitianRowUpdate F Q B v (rowPhase F u z, (u : F) * a) =
      compressedHermitianRowUpdate F Q B v (z, a) := by
  apply Subtype.ext
  change (Q : Matrix (Fin k) (Fin k) F) +
    rowGram F (rowShift F (rowFactorCLM F B (rowPhase F u z))
      ((u : F) * a) (rowFactorCLM F B v)) = _
  rw [rowFactor_phase]
  exact congrArg (fun G => (Q : Matrix (Fin k) (Fin k) F) + G)
    (rowGram_phase_shift F u (rowFactorCLM F B z) (rowFactorCLM F B v) a)

end CompressedGram

theorem complex_single_row_spectral_comparison {r m : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) (Fin m) ℂ) (v : Row ℂ m)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℂ)
    (Q : ∀ i, FieldSpectral.Hermitian ℂ (k i))
    (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun t : ℝ => ∫ z,
      ∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (compressedRowGram ℂ (Q i) (B i) (z + Real.sqrt t • v))
      ∂gaussianRowWithFactor ℂ R) (Ici 0) := by
  let G : Row ℂ m × ℂ → ℝ := fun w => ∏ i,
    complexFaceApprox (hc i) (hm i) (L i)
      (compressedHermitianRowUpdate ℂ (Q i) (B i) v w)
  have hcont : Continuous G := continuous_finsetProd _ fun i _ =>
    (continuous_complexFaceApprox (hc i) (hm i) (L i)).comp
      (continuous_compressedHermitianRowUpdate ℂ (Q i) (B i) v)
  have hpoly : JointPolynomialBound G := JointPolynomialBound.finset_prod
    Finset.univ _ (fun i _ => polynomial_complexFaceApprox_row
      (hc i) (hm i) (L i) (Q i) (hQ i) (B i) v)
  have hsub : ∀ z, BallSubmean (fun u : ℂ => G (z, u)) := by
    intro z
    exact ballSubmean_complexFaceApprox_product k h hc hm L Q hQ
      (fun i => rowFactorCLM ℂ (B i) z) (fun i => rowFactorCLM ℂ (B i) v)
  have hphase : ∀ a b : ℂ, ‖a‖ = ‖b‖ → ∃ T : Row ℂ m ≃ᵐ Row ℂ m,
      MeasurePreserving T (gaussianRowWithFactor ℂ R) (gaussianRowWithFactor ℂ R) ∧
        ∀ z, G (z, a) = G (T z, b) := by
    intro a b hab
    obtain ⟨u, hu⟩ := exists_unitary_mul_of_norm_eq
      (fun _ => complex_mem_unitary_of_norm_one) a b hab
    refine ⟨(rowPhase ℂ u).toHomeomorph.toMeasurableEquiv,
      measurePreserving_rowPhase ℂ R u, ?_⟩
    intro z
    rw [← hu]
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg (complexFaceApprox (hc i) (hm i) (L i))
      (compressedHermitianRowUpdate_phase ℂ (Q i) (B i) z v u a).symm
  have hmono := monotone_integral_sqrt_smul_of_polynomial_submean
    (norm_allFiniteMoments ℂ R) hcont hpoly
    (Filter.Eventually.of_forall hsub) hphase (1 : ℂ)
  simpa only [G, compressedHermitianRowUpdate_real] using hmono

theorem quaternion_single_row_spectral_comparison {r m : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) (Fin m) ℍ[ℝ]) (v : Row ℍ[ℝ] m)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, QuaternionMatrix.Hermitian (k i))
    (hQ : ∀ i, QuaternionMatrix.PosSemidef (Q i : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]))
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun t : ℝ => ∫ z,
      ∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (compressedRowGram ℍ[ℝ] (Q i) (B i) (z + Real.sqrt t • v))
      ∂gaussianRowWithFactor ℍ[ℝ] R) (Ici 0) := by
  let G : Row ℍ[ℝ] m × ℍ[ℝ] → ℝ := fun w => ∏ i,
    quaternionFaceApprox (hc i) (hm i) (L i)
      (compressedHermitianRowUpdate ℍ[ℝ] (Q i) (B i) v w)
  have hcont : Continuous G := continuous_finsetProd _ fun i _ =>
    (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).comp
      (continuous_compressedHermitianRowUpdate ℍ[ℝ] (Q i) (B i) v)
  have hpoly : JointPolynomialBound G := JointPolynomialBound.finset_prod
    Finset.univ _ (fun i _ => polynomial_quaternionFaceApprox_row
      (hc i) (hm i) (L i) (Q i) (hQ i) (B i) v)
  have hsub : ∀ z, BallSubmean (fun u : ℍ[ℝ] => G (z, u)) := by
    intro z
    exact ballSubmean_quaternionFaceApprox_product k h hc hm L Q hQ
      (fun i => rowFactorCLM ℍ[ℝ] (B i) z) (fun i => rowFactorCLM ℍ[ℝ] (B i) v)
  have hphase : ∀ a b : ℍ[ℝ], ‖a‖ = ‖b‖ → ∃ T : Row ℍ[ℝ] m ≃ᵐ Row ℍ[ℝ] m,
      MeasurePreserving T (gaussianRowWithFactor ℍ[ℝ] R) (gaussianRowWithFactor ℍ[ℝ] R) ∧
        ∀ z, G (z, a) = G (T z, b) := by
    intro a b hab
    obtain ⟨u, hu⟩ := exists_unitary_mul_of_norm_eq
      (fun _ => quaternion_mem_unitary_of_norm_one) a b hab
    refine ⟨(rowPhase ℍ[ℝ] u).toHomeomorph.toMeasurableEquiv,
      measurePreserving_rowPhase ℍ[ℝ] R u, ?_⟩
    intro z
    rw [← hu]
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg (quaternionFaceApprox (hc i) (hm i) (L i))
      (compressedHermitianRowUpdate_phase ℍ[ℝ] (Q i) (B i) z v u a).symm
  have hmono := monotone_integral_sqrt_smul_of_polynomial_submean
    (norm_allFiniteMoments ℍ[ℝ] R) hcont hpoly
    (Filter.Eventually.of_forall hsub) hphase (1 : ℍ[ℝ])
  simpa only [G, compressedHermitianRowUpdate_real] using hmono

end Wishart.FieldGaussian
end
end CanonicalSource29
