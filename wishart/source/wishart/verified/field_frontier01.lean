module

public import wishart.verified.field_analytic_union
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/- Recovered canonical proof stage; see verification/recovery-patches.json. -/

@[expose] public section


section CanonicalSource0
/- Source: Wishart/FieldSpectralCoordinates.lean -/




/-!
# Real coordinates and Vandermonde powers for field Hermitian matrices

A Hermitian matrix has one real coordinate per diagonal entry and a full field
coordinate per strict upper-triangular entry. The commutator with a real
diagonal spectrum multiplies each off-diagonal field coordinate by the
corresponding eigenvalue difference. Its real determinant therefore contributes
the second/fourth power in the complex/quaternion cases.
-/

noncomputable section
open Matrix
open scoped Classical Quaternion Matrix BigOperators

namespace Wishart.FieldCharts

variable (F : Type*) [Ring F] [Algebra ℝ F] [StarRing F] [StarModule ℝ F]

/-- The real fixed-point coordinates of conjugation, with actual instances
below for the complex and quaternion fields. -/
structure RealPartData where
  re : F →ₗ[ℝ] ℝ
  re_ofReal : ∀ r : ℝ, re (algebraMap ℝ F r) = r
  ofReal_re : ∀ x : F, star x = x → algebraMap ℝ F (re x) = x

abbrev Hermitian (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) F)
abbrev PairIndex (p : ℕ) := {ij : Fin p × Fin p // ij.1 < ij.2}
abbrev OffDiagonal (p : ℕ) := PairIndex p → F
abbrev Coordinates (p : ℕ) := (Fin p → ℝ) × OffDiagonal F p

def hermitianEntries {p : ℕ} (x : Coordinates F p) : Matrix (Fin p) (Fin p) F :=
  Matrix.of fun i j => if hij : i = j then algebraMap ℝ F (x.1 i)
    else if hlt : i < j then x.2 ⟨(i,j),hlt⟩ else star (x.2 ⟨(j,i), by
      change j < i
      exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)⟩)

theorem hermitianEntries_isHermitian {p : ℕ} (x : Coordinates F p) :
    (hermitianEntries F x).IsHermitian := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [hermitianEntries, Algebra.algebraMap_eq_smul_one]
  · by_cases hlt : i < j
    · simp [hermitianEntries, hij, Ne.symm hij, hlt, not_lt.mpr hlt.le]
    · have hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      simp [hermitianEntries, hij, Ne.symm hij, hlt, hgt]

def hermitianFromCoordinates {p : ℕ} (x : Coordinates F p) : Hermitian F p :=
  ⟨hermitianEntries F x, hermitianEntries_isHermitian F x⟩

def hermitianCoordinates (R : RealPartData F) (p : ℕ) : Hermitian F p ≃ₗ[ℝ] Coordinates F p where
  toFun X := (fun i => R.re (X.val i i), fun ij => X.val ij.1.1 ij.1.2)
  invFun := hermitianFromCoordinates F
  left_inv X := by
    apply Subtype.ext
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [hermitianFromCoordinates, hermitianEntries, Matrix.of_apply,
        dite_true]
      exact R.ofReal_re _ (congrFun (congrFun (WishartVerification.hermitian_matrix_coe X) i) i)
    · by_cases hlt : i < j
      · simp [hermitianFromCoordinates, hermitianEntries, hij, hlt]
      · simp only [hermitianFromCoordinates, hermitianEntries, Matrix.of_apply,
          dif_neg hij, dif_neg hlt]
        exact congrFun (congrFun (WishartVerification.hermitian_matrix_coe X) i) j
  right_inv x := by
    apply Prod.ext
    · funext i
      simp [hermitianFromCoordinates, hermitianEntries, R.re_ofReal]
    · funext ij
      simp [hermitianFromCoordinates, hermitianEntries, ij.2, ne_of_lt ij.2]
  map_add' X Y := by
    apply Prod.ext <;> funext i <;> simp [map_add]
  map_smul' r X := by
    apply Prod.ext <;> funext i <;> simp [map_smul]

def skewOffEntries {p : ℕ} (z : OffDiagonal F p) : Matrix (Fin p) (Fin p) F :=
  Matrix.of fun i j => if hij : i = j then 0
    else if hlt : i < j then z ⟨(i,j),hlt⟩ else -star (z ⟨(j,i), by
      change j < i
      exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)⟩)

theorem skewOffEntries_star {p : ℕ} (z : OffDiagonal F p) :
    (skewOffEntries F z)ᴴ = -skewOffEntries F z := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [skewOffEntries]
  · by_cases hlt : i < j
    · simp [skewOffEntries, hij, Ne.symm hij, hlt, not_lt.mpr hlt.le]
    · have hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      simp [skewOffEntries, hij, Ne.symm hij, hlt, hgt]

def skewOffLinearMap (p : ℕ) : OffDiagonal F p →ₗ[ℝ] Matrix (Fin p) (Fin p) F where
  toFun := skewOffEntries F
  map_add' a b := by
    ext i j
    simp only [skewOffEntries, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp [add_comm]
  map_smul' r a := by
    ext i j
    simp only [skewOffEntries, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]
    split_ifs <;> simp

def realDiagonal {p : ℕ} (lam : Fin p → ℝ) : Matrix (Fin p) (Fin p) F :=
  Matrix.diagonal (fun i => algebraMap ℝ F (lam i))

def spectralCommutator {p : ℕ} (lam : Fin p → ℝ) (z : OffDiagonal F p) :
    Matrix (Fin p) (Fin p) F :=
  skewOffEntries F z * realDiagonal F lam - realDiagonal F lam * skewOffEntries F z

theorem spectralCommutator_isHermitian {p : ℕ} (lam : Fin p → ℝ) (z : OffDiagonal F p) :
    (spectralCommutator F lam z).IsHermitian := by
  have hd : (realDiagonal F lam)ᴴ = realDiagonal F lam := by
    simp [realDiagonal, Algebra.algebraMap_eq_smul_one]
  change (spectralCommutator F lam z)ᴴ = _
  rw [spectralCommutator, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hd, skewOffEntries_star]
  simp only [Matrix.neg_mul, Matrix.mul_neg]
  abel

def spectralCommutatorHermitian {p : ℕ} (lam : Fin p → ℝ) (z : OffDiagonal F p) :
    Hermitian F p := ⟨spectralCommutator F lam z, spectralCommutator_isHermitian F lam z⟩

def gapOperator {p : ℕ} (lam : Fin p → ℝ) : OffDiagonal F p →ₗ[ℝ] OffDiagonal F p :=
  LinearMap.pi fun ij => (lam ij.1.2 - lam ij.1.1) • LinearMap.proj ij

theorem hermitianCoordinates_spectralCommutator (R : RealPartData F)
    {p : ℕ} (lam : Fin p → ℝ) (z : OffDiagonal F p) :
    hermitianCoordinates F R p (spectralCommutatorHermitian F lam z) =
      (0, gapOperator F lam z) := by
  apply Prod.ext
  · funext i
    simp [hermitianCoordinates, spectralCommutatorHermitian, spectralCommutator,
      realDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, skewOffEntries]
  · funext ij
    change (spectralCommutator F lam z) ij.1.1 ij.1.2 = (gapOperator F lam z) ij
    simp only [spectralCommutator,
      realDiagonal, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      skewOffEntries, Matrix.of_apply, dif_neg (ne_of_lt ij.2), dif_pos ij.2,
      gapOperator, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply]
    rw [← Algebra.commutes, ← Algebra.smul_def, ← Algebra.smul_def, sub_smul]

variable [FiniteDimensional ℝ F]

theorem det_gapOperator {p : ℕ} (lam : Fin p → ℝ) :
    LinearMap.det (gapOperator F lam) =
      (∏ ij : PairIndex p, (lam ij.1.2 - lam ij.1.1)) ^ Module.finrank ℝ F := by
  have heq : gapOperator F lam =
      LinearMap.pi (fun ij : PairIndex p =>
        ((lam ij.1.2 - lam ij.1.1) • (LinearMap.id : F →ₗ[ℝ] F)).comp (LinearMap.proj ij)) := by
    ext z ij
    rfl
  rw [heq, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one]
  exact Finset.prod_pow _ _ _

end Wishart.FieldCharts

namespace Wishart.ComplexMatrix

def realPartData : Wishart.FieldCharts.RealPartData ℂ where
  re := Complex.reLm
  re_ofReal r := rfl
  ofReal_re z hz := by
    apply Complex.ext
    · rfl
    · have h := congrArg Complex.im hz
      change -z.im = z.im at h
      change 0 = z.im
      linarith

theorem det_gapOperator {p : ℕ} (lam : Fin p → ℝ) :
    LinearMap.det (Wishart.FieldCharts.gapOperator ℂ lam) =
      (∏ ij : Wishart.FieldCharts.PairIndex p, (lam ij.1.2 - lam ij.1.1)) ^ 2 := by
  simpa [Complex.finrank_real_complex] using Wishart.FieldCharts.det_gapOperator ℂ lam

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix

def realPartData : Wishart.FieldCharts.RealPartData ℍ[ℝ] where
  re := QuaternionAlgebra.reₗ (-1) 0 (-1)
  re_ofReal r := rfl
  ofReal_re z hz := by
    change (z.re : ℍ[ℝ]) = z
    exact (Quaternion.star_eq_self.mp hz).symm

theorem det_gapOperator {p : ℕ} (lam : Fin p → ℝ) :
    LinearMap.det (Wishart.FieldCharts.gapOperator ℍ[ℝ] lam) =
      (∏ ij : Wishart.FieldCharts.PairIndex p, (lam ij.1.2 - lam ij.1.1)) ^ 4 := by
  simpa [Quaternion.finrank_eq_four] using Wishart.FieldCharts.det_gapOperator ℍ[ℝ] lam

end Wishart.QuaternionMatrix
end
end CanonicalSource0

section CanonicalSource1
/- Source: Wishart/FieldCayley.lean -/



/-!
# Cayley coordinates over the complex and quaternion fields

Only the ordinary real normed-algebra inverse is used.  All assertions are
proved on the open set where the denominator is a unit; this includes a
neighborhood of zero.  Thus the construction does not require a determinant
over a noncommutative field, or a global exponential chart.
-/

noncomputable section
open Matrix Filter
open scoped Classical Ring Topology Matrix.Norms.Operator

namespace Wishart.FieldCharts

section Algebra
variable {R : Type*} [Ring R] [Algebra ℝ R] [StarRing R] [StarModule ℝ R]

def cayleyElement (A : R) : R := (1 - A) * (1 + A)⁻¹ʳ

@[simp] theorem cayleyElement_zero : cayleyElement (0 : R) = 1 := by
  simp [cayleyElement]

theorem one_add_cayleyElement {A : R} (hA : IsUnit (1 + A)) :
    1 + cayleyElement A = (2 : ℝ) • (1 + A)⁻¹ʳ := by
  calc
    1 + cayleyElement A = (1 + A) * (1 + A)⁻¹ʳ +
        (1 - A) * (1 + A)⁻¹ʳ := by rw [Ring.mul_inverse_cancel _ hA]; rfl
    _ = ((1 + A) + (1 - A)) * (1 + A)⁻¹ʳ := by noncomm_ring
    _ = (2 : ℝ) • (1 + A)⁻¹ʳ := by
      have heq : (1 + A) + (1 - A) = (2 : ℝ) • (1 : R) := by
        simp only [two_smul]
        abel
      rw [heq, smul_mul_assoc, one_mul]

theorem cayleyElement_eq_inverse {A : R} (hA : IsUnit (1 + A)) :
    cayleyElement A = (2 : ℝ) • (1 + A)⁻¹ʳ - 1 := by
  have h := one_add_cayleyElement hA
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)

theorem cayleyElement_unitary {A : R} (hstar : star A = -A)
    (hA : IsUnit (1 + A)) : cayleyElement A ∈ unitary R := by
  have hm : IsUnit (1 - A) := by
    simpa only [star_add, star_one, hstar, ← sub_eq_add_neg] using hA.star
  have hcomm : (1 + A) * (1 - A) = (1 - A) * (1 + A) := by noncomm_ring
  have hs : star (cayleyElement A) = (1 - A)⁻¹ʳ * (1 + A) := by
    simp only [cayleyElement, star_mul, ← Ring.inverse_star,
      star_add, star_sub, star_one, hstar, sub_neg_eq_add, ← sub_eq_add_neg]
  constructor
  · rw [hs, cayleyElement]
    calc
      (1 - A)⁻¹ʳ * (1 + A) * ((1 - A) * (1 + A)⁻¹ʳ) =
          (1 - A)⁻¹ʳ * ((1 + A) * (1 - A)) * (1 + A)⁻¹ʳ := by simp only [mul_assoc]
      _ = 1 := by
        rw [hcomm, Ring.inverse_mul_cancel_left _ _ hm, Ring.mul_inverse_cancel _ hA]
  · rw [hs, cayleyElement]
    calc
      ((1 - A) * (1 + A)⁻¹ʳ) * ((1 - A)⁻¹ʳ * (1 + A)) =
          (1 - A) * ((1 + A)⁻¹ʳ * (1 - A)⁻¹ʳ) * (1 + A) := by simp only [mul_assoc]
      _ = (1 - A) * ((1 - A) * (1 + A))⁻¹ʳ * (1 + A) := by
        rw [Ring.inverse_mul (Or.inl hm)]
      _ = (1 - A) * ((1 + A) * (1 - A))⁻¹ʳ * (1 + A) := by rw [hcomm]
      _ = 1 := by
        rw [Ring.inverse_mul (Or.inl hA), Ring.mul_inverse_cancel_left _ _ hm,
          Ring.inverse_mul_cancel _ hA]

end Algebra

section Calculus
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
  [StarRing R] [StarModule ℝ R]

def cayleyDerivative (A : R) : R →L[ℝ] R :=
  (-2 : ℝ) • ContinuousLinearMap.mulLeftRight ℝ R (1 + A)⁻¹ʳ (1 + A)⁻¹ʳ

@[simp] theorem cayleyDerivative_apply (A H : R) :
    cayleyDerivative A H = (-2 : ℝ) • ((1 + A)⁻¹ʳ * H * (1 + A)⁻¹ʳ) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem hasStrictFDerivAt_cayleyElement {A : R} (hA : IsUnit (1 + A)) :
    HasStrictFDerivAt cayleyElement (cayleyDerivative A) A := by
  obtain ⟨u, hu⟩ := hA
  have hinv : HasStrictFDerivAt (fun B : R => (1 + B)⁻¹ʳ)
      (-ContinuousLinearMap.mulLeftRight ℝ R (1 + A)⁻¹ʳ (1 + A)⁻¹ʳ) A := by
    have hu' : (u : R) = 1 + A := hu
    have hi := hasStrictFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hu'] at hi
    have h := hi.comp A
      ((hasStrictFDerivAt_id A).const_add 1)
    simpa only [hu, Function.comp_def, ContinuousLinearMap.comp_id,
      ← Ring.inverse_unit] using h
  have hd : HasStrictFDerivAt
      (fun B : R => (2 : ℝ) • (1 + B)⁻¹ʳ - 1) (cayleyDerivative A) A := by
    simpa only [cayleyDerivative, Pi.smul_apply, Function.comp_def,
      smul_neg, neg_smul] using (hinv.const_smul (2 : ℝ)).sub_const 1
  apply hd.congr_of_eventuallyEq
  have hevent : ∀ᶠ B : R in 𝓝 A, IsUnit (1 + B) :=
    (Units.isOpen.preimage (continuous_const.add continuous_id)).mem_nhds ⟨u, hu⟩
  filter_upwards [hevent] with B hB
  exact (cayleyElement_eq_inverse hB).symm

theorem hasFDerivAt_cayleyElement {A : R} (hA : IsUnit (1 + A)) :
    HasFDerivAt cayleyElement (cayleyDerivative A) A :=
  (hasStrictFDerivAt_cayleyElement hA).hasFDerivAt

@[simp] theorem cayleyDerivative_zero :
    cayleyDerivative (0 : R) = (-2 : ℝ) • ContinuousLinearMap.id ℝ R := by
  ext H
  simp [cayleyDerivative_apply]

end Calculus

section Matrix
variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F] [StarRing F]
  [StarModule ℝ F] [FiniteDimensional ℝ F]

def cayleyMatrix {p : ℕ} (z : OffDiagonal F p) : Matrix (Fin p) (Fin p) F :=
  cayleyElement (skewOffEntries F z)

def cayleyDomain (p : ℕ) : Set (OffDiagonal F p) :=
  {z | IsUnit (1 + skewOffEntries F z)}

theorem isOpen_cayleyDomain (p : ℕ) : IsOpen (cayleyDomain F p) :=
  Units.isOpen.preimage (continuous_const.add (skewOffLinearMap F p).continuous_of_finiteDimensional)

theorem zero_mem_cayleyDomain (p : ℕ) : (0 : OffDiagonal F p) ∈ cayleyDomain F p := by
  change IsUnit (1 + skewOffLinearMap F p 0)
  simp

def cayleyUnitary {p : ℕ} (z : OffDiagonal F p) (hz : z ∈ cayleyDomain F p) :
    unitary (Matrix (Fin p) (Fin p) F) :=
  ⟨cayleyMatrix F z, cayleyElement_unitary (skewOffEntries_star F z) hz⟩

@[simp] theorem cayleyMatrix_zero (p : ℕ) : cayleyMatrix F (0 : OffDiagonal F p) = 1 := by
  change cayleyElement (skewOffLinearMap F p 0) = 1
  simp

def spectralMap {p : ℕ} (x : Coordinates F p) : Hermitian F p :=
  ⟨cayleyMatrix F x.2 * realDiagonal F x.1 * (cayleyMatrix F x.2)ᴴ,
    Matrix.isHermitian_mul_mul_conjTranspose _ (by
      change (realDiagonal F x.1)ᴴ = _
      simp [realDiagonal, Algebra.algebraMap_eq_smul_one])⟩

@[simp] theorem spectralMap_zero {p : ℕ} (lam : Fin p → ℝ) :
    (spectralMap F (lam,0) : Matrix (Fin p) (Fin p) F) = realDiagonal F lam := by
  simp only [spectralMap, cayleyMatrix_zero, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]

end Matrix

end Wishart.FieldCharts
end
end CanonicalSource1

section CanonicalSource2
/- Source: Wishart/ProductChartWindow.lean -/



/-!
# Product neighborhoods inside an inverse-function chart

The resulting angular neighborhood can be used for all simple spectra once
the concrete matrix commutant transfers equality to one reference spectrum.
This avoids introducing a quotient-manifold integration theorem as an axiom.
-/

noncomputable section
open Set
open scoped Topology

namespace WishartVerification

variable {L A E : Type*}
  [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_product_window_of_hasStrictFDerivAt
    {f : L × A → E} {e : (L × A) ≃L[ℝ] E} {l : L} {a : A}
    (hf : HasStrictFDerivAt f (e : (L × A) →L[ℝ] E) (l,a)) :
    ∃ U : Set L, ∃ V : Set A,
      IsOpen U ∧ IsOpen V ∧ l ∈ U ∧ a ∈ V ∧
      Set.InjOn f (U ×ˢ V) ∧ IsOpen (f '' (U ×ˢ V)) := by
  let H := hf.toOpenPartialHomeomorph f
  have hmem : (l,a) ∈ H.source := hf.mem_toOpenPartialHomeomorph_source
  obtain ⟨U,V,hU,hV,hl,ha,hUV⟩ := isOpen_prod_iff.mp H.open_source l a hmem
  refine ⟨U,V,hU,hV,hl,ha,?_,?_⟩
  · exact H.injOn.mono hUV
  · exact H.isOpen_image_of_subset_source (hU.prod hV) hUV

theorem exists_product_window_within_of_hasStrictFDerivAt
    {f : L × A → E} {e : (L × A) ≃L[ℝ] E} {l : L} {a : A}
    (hf : HasStrictFDerivAt f (e : (L × A) →L[ℝ] E) (l,a))
    {D : Set L} {W : Set A} (hD : IsOpen D) (hW : IsOpen W)
    (hlD : l ∈ D) (haW : a ∈ W) :
    ∃ U : Set L, ∃ V : Set A,
      IsOpen U ∧ IsOpen V ∧ l ∈ U ∧ a ∈ V ∧ U ⊆ D ∧ V ⊆ W ∧
      Set.InjOn f (U ×ˢ V) ∧ IsOpen (f '' (U ×ˢ V)) := by
  let H := hf.toOpenPartialHomeomorph f
  have hmem : (l,a) ∈ H.source := hf.mem_toOpenPartialHomeomorph_source
  obtain ⟨U,V,hU,hV,hl,ha,hUV⟩ := isOpen_prod_iff.mp H.open_source l a hmem
  have hsub : (U ∩ D) ×ˢ (V ∩ W) ⊆ H.source :=
    fun x hx => hUV ⟨hx.1.1,hx.2.1⟩
  refine ⟨U∩D,V∩W,hU.inter hD,hV.inter hW,⟨hl,hlD⟩,⟨ha,haW⟩,
    inter_subset_right,inter_subset_right,H.injOn.mono hsub,?_⟩
  exact H.isOpen_image_of_subset_source ((hU.inter hD).prod (hV.inter hW)) hsub

/-- The sole topological transfer used to make the IFT angular window uniform.
The equality-transfer premise will be the proved field-matrix commutant lemma. -/
theorem injOn_product_of_reference_spectrum
    {f : L × A → E} {spectrum : E → L} {D U : Set L} {V : Set A} {l : L}
    (hlU : l ∈ U) (hlD : l ∈ D)
    (hlocal : Set.InjOn f (U ×ˢ V))
    (hspectrum : ∀ x ∈ D, ∀ a ∈ V, spectrum (f (x,a)) = x)
    (htransfer : ∀ x ∈ D, ∀ a ∈ V, ∀ b ∈ V,
      f (x,a) = f (x,b) → f (l,a) = f (l,b)) :
    Set.InjOn f (D ×ˢ V) := by
  rintro ⟨x,a⟩ ⟨hx,ha⟩ ⟨y,b⟩ ⟨hy,hb⟩ h
  have hxy : x = y := by
    have hs := congrArg spectrum h
    simpa only [hspectrum x hx a ha, hspectrum y hy b hb] using hs
  subst y
  have hab : (l,a) = (l,b) :=
    hlocal (x₁ := (l,a)) (x₂ := (l,b)) ⟨hlU,ha⟩ ⟨hlU,hb⟩
      (htransfer x hx a ha b hb h)
  have hab' := congrArg Prod.snd hab
  exact Prod.ext rfl hab'

end WishartVerification
end
end CanonicalSource2

section CanonicalSource3
/- Source: Wishart/FieldChartDerivative.lean -/



/-!
# The actual spectral-chart derivative at a simple diagonal matrix

The chart is differentiated as a matrix polynomial in a genuine Cayley map.
The target is expressed in the explicit real diagonal/field off-diagonal
coordinates.  Its derivative is a continuous linear equivalence precisely
when the reference spectrum is simple.
-/

noncomputable section
open Matrix Filter
open scoped Classical Topology Matrix.Norms.Operator

namespace Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F] [StarRing F]
  [StarModule ℝ F] [FiniteDimensional ℝ F] [ContinuousStar F]

def ambientCoordinates (R : RealPartData F) (p : ℕ) :
    Matrix (Fin p) (Fin p) F →ₗ[ℝ] Coordinates F p where
  toFun X := (fun i => R.re (X i i), fun ij => X ij.1.1 ij.1.2)
  map_add' A B := by apply Prod.ext <;> funext i <;> simp
  map_smul' r A := by apply Prod.ext <;> funext i <;> simp

def realDiagonalLinearMap (p : ℕ) :
    (Fin p → ℝ) →ₗ[ℝ] Matrix (Fin p) (Fin p) F where
  toFun := realDiagonal F
  map_add' a b := by
    ext i j
    by_cases h : i = j <;> simp [realDiagonal, Matrix.diagonal_apply, h]
  map_smul' r a := by
    ext i j
    by_cases h : i = j <;> simp [realDiagonal, Matrix.diagonal_apply, Algebra.smul_def, h]

def starMatrixLinearMap (p : ℕ) :
    Matrix (Fin p) (Fin p) F →ₗ[ℝ] Matrix (Fin p) (Fin p) F where
  toFun := fun A => Aᴴ
  map_add' A B := Matrix.conjTranspose_add _ _
  map_smul' r A := by simp

def chartCoordinates (R : RealPartData F) {p : ℕ} (x : Coordinates F p) :
    Coordinates F p := hermitianCoordinates F R p (spectralMap F x)

@[simp] theorem ambientCoordinates_diagonal (R : RealPartData F)
    {p : ℕ} (lam : Fin p → ℝ) :
    ambientCoordinates F R p (realDiagonal F lam) = (lam,0) := by
  apply Prod.ext
  · funext i
    simp [ambientCoordinates, realDiagonal, R.re_ofReal]
  · funext ij
    simp [ambientCoordinates, realDiagonal, ne_of_lt ij.2]

@[simp] theorem chartCoordinates_zero (R : RealPartData F)
    {p : ℕ} (lam : Fin p → ℝ) : chartCoordinates F R (lam,0) = (lam,0) := by
  change ambientCoordinates F R p (spectralMap F (lam,0)) = _
  rw [spectralMap_zero, ambientCoordinates_diagonal]

def zeroChartDerivative (R : RealPartData F) {p : ℕ} (lam : Fin p → ℝ) :
    Coordinates F p →L[ℝ] Coordinates F p :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    (((-2 : ℝ) • (gapOperator F lam).toContinuousLinearMap).comp
      (ContinuousLinearMap.snd ℝ _ _))

@[simp] theorem zeroChartDerivative_apply (R : RealPartData F)
    {p : ℕ} (lam : Fin p → ℝ) (h : Coordinates F p) :
    zeroChartDerivative F R lam h = (h.1, (-2 : ℝ) • gapOperator F lam h.2) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem hasStrictFDerivAt_chartCoordinates_zero (R : RealPartData F)
    {p : ℕ} (lam : Fin p → ℝ) :
    HasStrictFDerivAt (chartCoordinates F R) (zeroChartDerivative F R lam) (lam,0) := by
  let P : Coordinates F p →L[ℝ] Matrix (Fin p) (Fin p) F :=
    (skewOffLinearMap F p).toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ _ _)
  let D : Coordinates F p →L[ℝ] Matrix (Fin p) (Fin p) F :=
    (realDiagonalLinearMap F p).toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ _)
  let T : Matrix (Fin p) (Fin p) F →L[ℝ] Matrix (Fin p) (Fin p) F :=
    (starMatrixLinearMap F p).toContinuousLinearMap
  let Q : Coordinates F p → Matrix (Fin p) (Fin p) F := fun x => cayleyElement (P x)
  have hP : P (lam,0) = 0 := by change skewOffLinearMap F p 0 = 0; exact map_zero _
  have hQ : HasStrictFDerivAt Q ((-2 : ℝ) • P) (lam,0) := by
    have h := (hasStrictFDerivAt_cayleyElement (R := Matrix (Fin p) (Fin p) F)
      (A := P (lam,0)) (by rw [hP]; simp)).comp (lam,0) P.hasStrictFDerivAt
    simpa only [hP, cayleyDerivative_zero, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.id_comp, Function.comp_def, Q] using h
  have hQT := T.hasStrictFDerivAt.comp (lam,0) hQ
  have hraw := (hQ.mul' D.hasStrictFDerivAt).mul' hQT
  have hc := ((ambientCoordinates F R p).toContinuousLinearMap.hasStrictFDerivAt).comp
    (lam,0) hraw
  have hfun : (fun x => (ambientCoordinates F R p).toContinuousLinearMap
      ((Q * D * fun x => T (Q x)) x)) = chartCoordinates F R := by
    funext x
    rfl
  rw [hfun] at hc
  apply hc.congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  change ambientCoordinates F R p
    (Q (lam,0) * D (lam,0) * T ((-2 : ℝ) • P h) +
      (Q (lam,0) * D h + ((-2 : ℝ) • P h) * D (lam,0)) * T (Q (lam,0))) = _
  have hQ0 : Q (lam,0) = 1 := by simp only [Q, hP, cayleyElement_zero]
  rw [hQ0]
  have hT : T (P h) = -P h := skewOffEntries_star F h.2
  have hT1 : T 1 = 1 := by change (1 : Matrix (Fin p) (Fin p) F)ᴴ = 1; simp
  rw [map_smul, hT, hT1, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  have heq : D (lam,0) * ((-2 : ℝ) • -P h) +
      (D h + ((-2 : ℝ) • P h) * D (lam,0)) =
      realDiagonal F h.1 + (-2 : ℝ) • spectralCommutator F lam h.2 := by
    change realDiagonal F lam * ((-2 : ℝ) • -skewOffEntries F h.2) +
      (realDiagonal F h.1 + ((-2 : ℝ) • skewOffEntries F h.2) * realDiagonal F lam) = _
    simp only [spectralCommutator, mul_smul_comm, smul_mul_assoc,
      smul_neg, smul_sub, mul_neg]
    abel
  rw [heq, map_add, map_smul, ambientCoordinates_diagonal]
  have hcomm : ambientCoordinates F R p (spectralCommutator F lam h.2) =
      (0, gapOperator F lam h.2) := hermitianCoordinates_spectralCommutator F R lam h.2
  rw [hcomm]
  simp only [zeroChartDerivative_apply, Prod.smul_mk, smul_zero, Prod.mk_add_mk,
    add_zero, zero_add]

def gapEquiv {p : ℕ} (lam : Fin p → ℝ) (hlam : Function.Injective lam) :
    OffDiagonal F p ≃ₗ[ℝ] OffDiagonal F p where
  toFun := gapOperator F lam
  invFun z ij := (lam ij.1.2 - lam ij.1.1)⁻¹ • z ij
  left_inv z := by
    funext ij
    have hne : lam ij.1.2 - lam ij.1.1 ≠ 0 :=
      sub_ne_zero.mpr (fun h => (ne_of_lt ij.2) (hlam h).symm)
    simp [gapOperator, smul_smul, hne]
  right_inv z := by
    funext ij
    have hne : lam ij.1.2 - lam ij.1.1 ≠ 0 :=
      sub_ne_zero.mpr (fun h => (ne_of_lt ij.2) (hlam h).symm)
    simp [gapOperator, smul_smul, hne]
  map_add' := (gapOperator F lam).map_add
  map_smul' := (gapOperator F lam).map_smul

def zeroChartDerivativeEquiv {p : ℕ} (lam : Fin p → ℝ)
    (hlam : Function.Injective lam) : Coordinates F p ≃L[ℝ] Coordinates F p :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.prodCongr (LinearEquiv.refl ℝ (Fin p → ℝ))
    ((gapEquiv F lam hlam).trans
      (LinearEquiv.smulOfNeZero ℝ (OffDiagonal F p) (-2 : ℝ) (by norm_num))))

theorem zeroChartDerivativeEquiv_coe (R : RealPartData F) {p : ℕ}
    (lam : Fin p → ℝ) (hlam : Function.Injective lam) :
    (zeroChartDerivativeEquiv F lam hlam : Coordinates F p →L[ℝ] Coordinates F p) =
      zeroChartDerivative F R lam := by
  apply ContinuousLinearMap.ext
  intro h
  rfl

theorem exists_simple_spectral_product_window (R : RealPartData F)
    {p : ℕ} (lam : Fin p → ℝ) (hlam : Function.Injective lam) :
    ∃ U : Set (Fin p → ℝ), ∃ V : Set (OffDiagonal F p),
      IsOpen U ∧ IsOpen V ∧ lam ∈ U ∧ (0 : OffDiagonal F p) ∈ V ∧
      Set.InjOn (chartCoordinates F R) (U ×ˢ V) ∧
      IsOpen (chartCoordinates F R '' (U ×ˢ V)) := by
  apply WishartVerification.exists_product_window_of_hasStrictFDerivAt
    (e := zeroChartDerivativeEquiv F lam hlam)
  rw [zeroChartDerivativeEquiv_coe F R]
  exact hasStrictFDerivAt_chartCoordinates_zero F R lam

end Wishart.FieldCharts
end
end CanonicalSource3

section CanonicalSource4
/- Source: Wishart/FieldSpectralCommutant.lean -/




/-!
# The simple-spectrum stabilizer is independent of the eigenvalues

Over both fields the commutant of an injective real diagonal spectrum consists
of diagonal matrices.  Its diagonal entries may be arbitrary unit phases.
The consequence used by the spectral chart is equality of frame orbits for
every real diagonal spectrum once equality holds for one simple spectrum.
-/

noncomputable section
open Matrix
open scoped Classical Matrix

namespace Wishart.FieldCharts

variable (F : Type*) [Ring F] [Algebra ℝ F] [StarRing F] [StarModule ℝ F]

def diagonalHermitian {p : ℕ} (lam : Fin p → ℝ) : Hermitian F p :=
  ⟨realDiagonal F lam, by
    change (realDiagonal F lam)ᴴ = _
    simp [realDiagonal, Algebra.algebraMap_eq_smul_one]⟩

def unitaryConjugate {p : ℕ} (U : unitary (Matrix (Fin p) (Fin p) F))
    (X : Hermitian F p) : Hermitian F p :=
  ⟨(U : Matrix (Fin p) (Fin p) F) * (X : Matrix (Fin p) (Fin p) F) *
      (U : Matrix (Fin p) (Fin p) F)ᴴ,
    Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix (Fin p) (Fin p) F)
      (WishartVerification.hermitian_matrix_coe X)⟩

@[simp] theorem unitaryConjugate_one {p : ℕ} (X : Hermitian F p) :
    unitaryConjugate F 1 X = X := by
  apply Subtype.ext
  simp only [unitaryConjugate, Submonoid.coe_one, star_one, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]

theorem unitaryConjugate_mul {p : ℕ} (U V : unitary (Matrix (Fin p) (Fin p) F))
    (X : Hermitian F p) :
    unitaryConjugate F (U*V) X = unitaryConjugate F U (unitaryConjugate F V X) := by
  apply Subtype.ext
  simp only [unitaryConjugate, Submonoid.coe_mul, star_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

theorem eq_diagonal_of_commute_simple {p : ℕ} (lam : Fin p → ℝ)
    (hlam : Function.Injective lam) (A : Matrix (Fin p) (Fin p) F)
    (hA : A * realDiagonal F lam = realDiagonal F lam * A) :
    A = Matrix.diagonal (fun i => A i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · have hentry := congrFun (congrFun hA i) j
    simp only [realDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
    have hscalar : (lam j - lam i) • A i j = 0 := by
      rw [sub_smul, sub_eq_zero]
      rw [Algebra.smul_def, Algebra.smul_def, Algebra.commutes (lam j) (A i j)]
      exact hentry
    have hne : lam j - lam i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hlam h).symm)
    have hz : A i j = 0 := (smul_eq_zero.mp hscalar).resolve_left hne
    simpa only [Matrix.diagonal_apply_ne (fun k => A k k) hij] using hz

theorem diagonal_commutes_realDiagonal {p : ℕ} (d : Fin p → F) (lam : Fin p → ℝ) :
    Matrix.diagonal d * realDiagonal F lam = realDiagonal F lam * Matrix.diagonal d := by
  simp only [realDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact (Algebra.commutes (lam i) (d i)).symm

theorem intertwines_of_unitary_conjugates {p : ℕ}
    (U V : unitary (Matrix (Fin p) (Fin p) F))
    (D E : Matrix (Fin p) (Fin p) F)
    (h : (U : Matrix (Fin p) (Fin p) F) * D * star (U : Matrix (Fin p) (Fin p) F) =
      (V : Matrix (Fin p) (Fin p) F) * E * star (V : Matrix (Fin p) (Fin p) F)) :
    (star (V : Matrix (Fin p) (Fin p) F) * (U : Matrix (Fin p) (Fin p) F)) * D =
      E * (star (V : Matrix (Fin p) (Fin p) F) * (U : Matrix (Fin p) (Fin p) F)) := by
  let u : Matrix (Fin p) (Fin p) F := U
  let v : Matrix (Fin p) (Fin p) F := V
  have hu : star u * u = 1 := U.property.1
  have hv : star v * v = 1 := V.property.1
  change u * D * star u = v * E * star v at h
  change (star v * u) * D = E * (star v * u)
  calc
    (star v * u) * D = star v * (u * D * star u) * u := by
      simp only [Matrix.mul_assoc, hu, Matrix.mul_one]
    _ = star v * (v * E * star v) * u := by rw [h]
    _ = ((star v * v) * E) * (star v * u) := by simp only [Matrix.mul_assoc]
    _ = E * (star v * u) := by rw [hv, Matrix.one_mul]

theorem conjugate_diagonal_eq_iff {p : ℕ} (lam : Fin p → ℝ)
    (U V : unitary (Matrix (Fin p) (Fin p) F)) :
    unitaryConjugate F U (diagonalHermitian F lam) =
      unitaryConjugate F V (diagonalHermitian F lam) ↔
      ((star V * U : unitary (Matrix (Fin p) (Fin p) F)) : Matrix (Fin p) (Fin p) F) *
        realDiagonal F lam = realDiagonal F lam *
          ((star V * U : unitary (Matrix (Fin p) (Fin p) F)) : Matrix (Fin p) (Fin p) F) := by
  constructor
  · intro h
    have hM := congrArg Subtype.val h
    exact intertwines_of_unitary_conjugates F U V (realDiagonal F lam)
      (realDiagonal F lam) hM
  · intro h
    apply Subtype.ext
    let u : Matrix (Fin p) (Fin p) F := U
    let v : Matrix (Fin p) (Fin p) F := V
    have hu : u * star u = 1 := U.property.2
    have hv : v * star v = 1 := V.property.2
    change (star v * u) * realDiagonal F lam = realDiagonal F lam * (star v * u) at h
    change u * realDiagonal F lam * star u = v * realDiagonal F lam * star v
    calc
      u * realDiagonal F lam * star u =
          v * ((star v * u) * realDiagonal F lam) * star u := by
            simp only [← Matrix.mul_assoc, hv, Matrix.one_mul]
      _ = v * (realDiagonal F lam * (star v * u)) * star u := by rw [h]
      _ = v * realDiagonal F lam * star v := by
        simp only [Matrix.mul_assoc, hu, Matrix.mul_one]

/-- This is the exact replacement for the finite sign argument over the reals.
It proves the full phase ambiguity disappears simultaneously for all spectra. -/
theorem conjugate_diagonal_eq_forall_of_eq_simple {p : ℕ}
    (lam : Fin p → ℝ) (hlam : Function.Injective lam)
    (U V : unitary (Matrix (Fin p) (Fin p) F))
    (h : unitaryConjugate F U (diagonalHermitian F lam) =
      unitaryConjugate F V (diagonalHermitian F lam)) (mu : Fin p → ℝ) :
    unitaryConjugate F U (diagonalHermitian F mu) =
      unitaryConjugate F V (diagonalHermitian F mu) := by
  apply (conjugate_diagonal_eq_iff F mu U V).mpr
  have hd := eq_diagonal_of_commute_simple F lam hlam
    ((star V * U : unitary (Matrix (Fin p) (Fin p) F)) : Matrix (Fin p) (Fin p) F)
    ((conjugate_diagonal_eq_iff F lam U V).mp h)
  rw [hd]
  exact diagonal_commutes_realDiagonal F _ mu

section Nontrivial
variable [Nontrivial F]

theorem exists_ne_zero_in_unitary_row {p : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) F)) (i : Fin p) :
    ∃ j, (U : Matrix (Fin p) (Fin p) F) i j ≠ 0 := by
  by_contra h
  push_neg at h
  have hu := congrArg (fun A : Matrix (Fin p) (Fin p) F => A i i) U.property.2
  simp only [Matrix.mul_apply, h, zero_mul, Finset.sum_const_zero,
    Matrix.one_apply_eq] at hu
  exact zero_ne_one hu

theorem range_subset_of_unitary_intertwines {p : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) F)) (lam mu : Fin p → ℝ)
    (h : (U : Matrix (Fin p) (Fin p) F) * realDiagonal F lam =
      realDiagonal F mu * U) : Set.range mu ⊆ Set.range lam := by
  rintro _ ⟨i,rfl⟩
  obtain ⟨j,hij⟩ := exists_ne_zero_in_unitary_row F U i
  refine ⟨j, ?_⟩
  have he := congrFun (congrFun h i) j
  simp only [realDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  have hs : (lam j - mu i) • (U : Matrix (Fin p) (Fin p) F) i j = 0 := by
    rw [sub_smul, sub_eq_zero, Algebra.smul_def, Algebra.smul_def,
      Algebra.commutes (lam j) ((U : Matrix (Fin p) (Fin p) F) i j)]
    exact he
  exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hij)

/-- Equality of two strict ordered spectral reconstructions forces literal
coordinate equality, over either field, without a determinant over that field. -/
theorem strict_spectrum_unique {p : ℕ} (U V : unitary (Matrix (Fin p) (Fin p) F))
    {lam mu : Fin p → ℝ} (hlam : StrictMono lam) (hmu : StrictMono mu)
    (h : unitaryConjugate F U (diagonalHermitian F lam) =
      unitaryConjugate F V (diagonalHermitian F mu)) : lam = mu := by
  let E : unitary (Matrix (Fin p) (Fin p) F) := star V * U
  have hi : (E : Matrix (Fin p) (Fin p) F) * realDiagonal F lam =
      realDiagonal F mu * E := by
    have hm := congrArg Subtype.val h
    exact intertwines_of_unitary_conjugates F U V (realDiagonal F lam) (realDiagonal F mu) hm
  have hir : (star E : Matrix (Fin p) (Fin p) F) * realDiagonal F mu =
      realDiagonal F lam * star E := by
    let e : Matrix (Fin p) (Fin p) F := E
    have hleft : star e * e = 1 := E.property.1
    have hright : e * star e = 1 := E.property.2
    change star e * realDiagonal F mu = realDiagonal F lam * star e
    calc
      star e * realDiagonal F mu =
          star e * realDiagonal F mu * (e * star e) := by rw [hright, Matrix.mul_one]
      _ = (star e * (realDiagonal F mu * e)) * star e := by simp only [Matrix.mul_assoc]
      _ = (star e * (e * realDiagonal F lam)) * star e := by rw [← hi]
      _ = realDiagonal F lam * star e := by
        rw [← Matrix.mul_assoc (star e) e, hleft, Matrix.one_mul]
  have hr : Set.range lam = Set.range mu := Set.Subset.antisymm
    (range_subset_of_unitary_intertwines F (star E) mu lam hir)
    (range_subset_of_unitary_intertwines F E lam mu hi)
  exact hlam.eq_of_range_eq hmu hr

end Nontrivial

end Wishart.FieldCharts
end
end CanonicalSource4

section CanonicalSource5
/- Source: Wishart/FieldAngularDerivative.lean -/



/-!
# The horizontal part of the genuine angular differential

The full left-translated Cayley derivative is skew-adjoint. Its imaginary
diagonal has zero commutator with every real spectrum. The strict upper
entries therefore give exactly the effective angular differential.
-/

noncomputable section
open Matrix
open scoped Classical Ring Matrix.Norms.Operator

namespace Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F] [StarRing F]
  [StarModule ℝ F] [FiniteDimensional ℝ F] [ContinuousStar F]

def angularFull {p : ℕ} (z h : OffDiagonal F p) : Matrix (Fin p) (Fin p) F :=
  let B := (1 + skewOffEntries F z)⁻¹ʳ
  (-2 : ℝ) • (star B * skewOffEntries F h * B)

theorem angularFull_star {p : ℕ} (z h : OffDiagonal F p) :
    (angularFull F z h)ᴴ = -angularFull F z h := by
  simp only [angularFull, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, star_trivial,
    skewOffEntries_star, Matrix.mul_neg, Matrix.neg_mul, smul_neg, Matrix.mul_assoc]

def angularFullLinearMap {p : ℕ} (z : OffDiagonal F p) :
    OffDiagonal F p →ₗ[ℝ] Matrix (Fin p) (Fin p) F where
  toFun := angularFull F z
  map_add' h k := by
    have heq : skewOffEntries F (h+k) = skewOffEntries F h + skewOffEntries F k :=
      (skewOffLinearMap F p).map_add h k
    simp only [angularFull, heq, Matrix.mul_add,
      Matrix.add_mul, smul_add]
  map_smul' r h := by
    have heq : skewOffEntries F (r • h) = r • skewOffEntries F h :=
      (skewOffLinearMap F p).map_smul r h
    simp only [angularFull, heq, Matrix.mul_smul, Matrix.smul_mul]
    exact smul_comm (-2 : ℝ) r _

def angularOffLinearMap {p : ℕ} (z : OffDiagonal F p) :
    OffDiagonal F p →ₗ[ℝ] OffDiagonal F p :=
  LinearMap.pi fun ij =>
    ((LinearMap.proj ij.1.2).comp (LinearMap.proj ij.1.1)).comp
      (angularFullLinearMap F z)

@[simp] theorem angularOffLinearMap_apply {p : ℕ} (z h : OffDiagonal F p)
    (ij : PairIndex p) : angularOffLinearMap F z h ij = angularFull F z h ij.1.1 ij.1.2 := rfl

@[simp] theorem angularOffLinearMap_zero (p : ℕ) :
    angularOffLinearMap F (0 : OffDiagonal F p) = (-2 : ℝ) • LinearMap.id := by
  apply LinearMap.ext
  intro h
  funext ij
  change ((-2 : ℝ) • (star ((1 + skewOffLinearMap F p 0)⁻¹ʳ) *
    skewOffEntries F h * (1 + skewOffLinearMap F p 0)⁻¹ʳ)) ij.1.1 ij.1.2 = _
  simp only [map_zero, add_zero, Ring.inverse_one, star_one, Matrix.one_mul,
    Matrix.mul_one, Matrix.smul_apply, skewOffEntries, Matrix.of_apply,
    dif_neg (ne_of_lt ij.2), dif_pos ij.2, LinearMap.smul_apply, LinearMap.id_apply,
    Pi.smul_apply]

theorem cayley_left_translated_derivative {p : ℕ} (z h : OffDiagonal F p)
    (hz : z ∈ cayleyDomain F p) :
    (cayleyMatrix F z)ᴴ *
      cayleyDerivative (skewOffEntries F z) (skewOffEntries F h) = angularFull F z h := by
  let A := skewOffEntries F z
  let H := skewOffEntries F h
  have hs : star A = -A := skewOffEntries_star F z
  have hstar : star ((1 + A)⁻¹ʳ) = (1 - A)⁻¹ʳ := by
    rw [← Ring.inverse_star, star_add, star_one, hs]
    rw [sub_eq_add_neg]
  have hc : star (cayleyElement A) = (1 - A)⁻¹ʳ * (1 + A) := by
    simp only [cayleyElement, star_mul, ← Ring.inverse_star, star_add,
      star_sub, star_one, hs, sub_neg_eq_add, ← sub_eq_add_neg]
  change star (cayleyElement A) * ((-2 : ℝ) • ((1+A)⁻¹ʳ * H * (1+A)⁻¹ʳ)) =
    (-2 : ℝ) • (star ((1+A)⁻¹ʳ) * H * (1+A)⁻¹ʳ)
  rw [hc,hstar,mul_smul_comm]
  congr 1
  calc
    ((1-A)⁻¹ʳ * (1+A)) * ((1+A)⁻¹ʳ * H * (1+A)⁻¹ʳ) =
        (1-A)⁻¹ʳ * ((1+A) * (1+A)⁻¹ʳ) * H * (1+A)⁻¹ʳ := by
          simp only [mul_assoc]
    _ = _ := by rw [Ring.mul_inverse_cancel _ hz, mul_one]

theorem cayley_derivative_eq_angular {p : ℕ} (z h : OffDiagonal F p)
    (hz : z ∈ cayleyDomain F p) :
    cayleyDerivative (skewOffEntries F z) (skewOffEntries F h) =
      cayleyMatrix F z * angularFull F z h := by
  rw [← cayley_left_translated_derivative F z h hz, ← Matrix.mul_assoc]
  have hu := (cayleyUnitary F z hz).property.2
  change cayleyMatrix F z * (cayleyMatrix F z)ᴴ = 1 at hu
  rw [hu,Matrix.one_mul]

theorem ambientCoordinates_skew_commutator (R : RealPartData F) {p : ℕ}
    (lam : Fin p → ℝ) (K : Matrix (Fin p) (Fin p) F) (hK : Kᴴ = -K) :
    ambientCoordinates F R p (K * realDiagonal F lam - realDiagonal F lam * K) =
      (0, gapOperator F lam (fun ij => K ij.1.1 ij.1.2)) := by
  apply Prod.ext
  · funext i
    change R.re ((K * realDiagonal F lam - realDiagonal F lam * K) i i) = 0
    simp only [realDiagonal, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [(Algebra.commutes (lam i) (K i i)).symm, sub_self, map_zero]
  · funext ij
    change (K * realDiagonal F lam - realDiagonal F lam * K) ij.1.1 ij.1.2 = _
    simp only [realDiagonal, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      gapOperator, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      sub_smul, Algebra.smul_def]
    rw [(Algebra.commutes (lam ij.1.2) (K ij.1.1 ij.1.2)).symm, map_sub, sub_mul]

def spectralInnerLinearMap {p : ℕ} (z : OffDiagonal F p) (lam : Fin p → ℝ) :
    Coordinates F p →ₗ[ℝ] Coordinates F p :=
  (LinearMap.fst ℝ _ _).prod
    (((gapOperator F lam).comp (angularOffLinearMap F z)).comp (LinearMap.snd ℝ _ _))

@[simp] theorem spectralInnerLinearMap_apply {p : ℕ}
    (z : OffDiagonal F p) (lam : Fin p → ℝ) (h : Coordinates F p) :
    spectralInnerLinearMap F z lam h = (h.1,gapOperator F lam (angularOffLinearMap F z h.2)) := rfl

theorem det_spectralInnerLinearMap {p : ℕ} (z : OffDiagonal F p) (lam : Fin p → ℝ) :
    LinearMap.det (spectralInnerLinearMap F z lam) =
      LinearMap.det (angularOffLinearMap F z) *
        (∏ ij : PairIndex p, (lam ij.1.2 - lam ij.1.1)) ^ Module.finrank ℝ F := by
  change LinearMap.det ((LinearMap.id : (Fin p → ℝ) →ₗ[ℝ] (Fin p → ℝ)).prodMap
    ((gapOperator F lam).comp (angularOffLinearMap F z))) = _
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_comp,
    det_gapOperator]
  exact mul_comm _ _

end Wishart.FieldCharts
end
end CanonicalSource5

section CanonicalSource6
/- Source: Wishart/FieldChartWindow.lean -/



/-!
# One angular window for every simple complex or quaternion spectrum

The inverse-function theorem is applied at a fixed reference spectrum.  The
proved simple-spectrum commutant then extends its injectivity to the entire
positive chamber.  The associated event in the unitary group is open, has
positive finite Haar mass, and is independent of the chosen simple spectrum.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Topology ENNReal Matrix.Norms.Operator

namespace Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F] [StarRing F]
  [StarModule ℝ F] [FiniteDimensional ℝ F] [ContinuousStar F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]

abbrev chamber (p : ℕ) : Set (Fin p → ℝ) := Wishart.Spectral.positiveChamber p

def referenceSpectrum (p : ℕ) (i : Fin p) : ℝ := (i.val : ℝ) + 1

theorem referenceSpectrum_mem_chamber (p : ℕ) : referenceSpectrum p ∈ chamber p := by
  constructor
  · intro i j hij
    dsimp [referenceSpectrum]
    exact_mod_cast Nat.add_lt_add_right hij 1
  · intro i
    change 0 < (i.val : ℝ) + 1
    positivity

structure ProductWindow (R : RealPartData F) (p : ℕ) where
  eigenWindow : Set (Fin p → ℝ)
  angularWindow : Set (OffDiagonal F p)
  eigen_open : IsOpen eigenWindow
  angular_open : IsOpen angularWindow
  reference_mem : referenceSpectrum p ∈ eigenWindow
  zero_mem : (0 : OffDiagonal F p) ∈ angularWindow
  eigen_subset : eigenWindow ⊆ chamber p
  angular_subset : angularWindow ⊆ cayleyDomain F p
  injOn_local : Set.InjOn (chartCoordinates F R) (eigenWindow ×ˢ angularWindow)
  image_open : IsOpen (chartCoordinates F R '' (eigenWindow ×ˢ angularWindow))

theorem productWindow_exists (R : RealPartData F) (p : ℕ) :
    Nonempty (ProductWindow F R p) := by
  have hmono := (referenceSpectrum_mem_chamber p).1
  have hd : HasStrictFDerivAt (chartCoordinates F R)
      (zeroChartDerivativeEquiv F (referenceSpectrum p) hmono.injective :
        Coordinates F p →L[ℝ] Coordinates F p) (referenceSpectrum p,0) := by
    rw [zeroChartDerivativeEquiv_coe F R]
    exact hasStrictFDerivAt_chartCoordinates_zero F R _
  obtain ⟨U,V,hU,hV,hl,hz,hUD,hVD,hinj,hopen⟩ :=
    WishartVerification.exists_product_window_within_of_hasStrictFDerivAt hd
      (Wishart.Spectral.isOpen_positiveChamber p) (isOpen_cayleyDomain F p)
      (referenceSpectrum_mem_chamber p) (zero_mem_cayleyDomain F p)
  exact ⟨⟨U,V,hU,hV,hl,hz,hUD,hVD,hinj,hopen⟩⟩

def chosenWindow (R : RealPartData F) (p : ℕ) : ProductWindow F R p :=
  Classical.choice (productWindow_exists F R p)

@[simp] theorem chartCoordinates_eq_frame (R : RealPartData F) {p : ℕ}
    (lam : Fin p → ℝ) (z : OffDiagonal F p) (hz : z ∈ cayleyDomain F p) :
    chartCoordinates F R (lam,z) = hermitianCoordinates F R p
      (unitaryConjugate F (cayleyUnitary F z hz) (diagonalHermitian F lam)) := rfl

theorem ProductWindow.injOn_chamber (R : RealPartData F) {p : ℕ}
    (W : ProductWindow F R p) :
    Set.InjOn (chartCoordinates F R) (chamber p ×ˢ W.angularWindow) := by
  rintro ⟨lam,a⟩ ⟨hlam,ha⟩ ⟨mu,b⟩ ⟨hmu,hb⟩ heq
  let U := cayleyUnitary F a (W.angular_subset ha)
  let V := cayleyUnitary F b (W.angular_subset hb)
  have hm : unitaryConjugate F U (diagonalHermitian F lam) =
      unitaryConjugate F V (diagonalHermitian F mu) :=
    (hermitianCoordinates F R p).injective heq
  have hspec := strict_spectrum_unique F U V hlam.1 hmu.1 hm
  change lam = mu at hspec
  subst mu
  have href := conjugate_diagonal_eq_forall_of_eq_simple F lam hlam.1.injective U V hm
    (referenceSpectrum p)
  have hlocal : chartCoordinates F R (referenceSpectrum p,a) =
      chartCoordinates F R (referenceSpectrum p,b) :=
    congrArg (hermitianCoordinates F R p) href
  have hab := W.injOn_local (x₁ := (referenceSpectrum p,a))
    (x₂ := (referenceSpectrum p,b)) ⟨W.reference_mem,ha⟩ ⟨W.reference_mem,hb⟩ hlocal
  have hab' := congrArg Prod.snd hab
  exact Prod.ext rfl hab'

def orbitCoordinates (R : RealPartData F) {p : ℕ} (lam : Fin p → ℝ)
    (U : unitary (Matrix (Fin p) (Fin p) F)) : Coordinates F p :=
  hermitianCoordinates F R p (unitaryConjugate F U (diagonalHermitian F lam))

theorem continuous_orbitCoordinates (R : RealPartData F) {p : ℕ} (lam : Fin p → ℝ) :
    Continuous (orbitCoordinates F R lam) := by
  apply (hermitianCoordinates F R p).continuous_of_finiteDimensional.comp
  apply Continuous.subtype_mk
  change Continuous (fun U : unitary (Matrix (Fin p) (Fin p) F) =>
    (U : Matrix (Fin p) (Fin p) F) * realDiagonal F lam * star U)
  fun_prop

def ProductWindow.frameWindow (R : RealPartData F) {p : ℕ} (W : ProductWindow F R p) :
    Set (unitary (Matrix (Fin p) (Fin p) F)) :=
  (orbitCoordinates F R (referenceSpectrum p)) ⁻¹'
    (chartCoordinates F R '' (W.eigenWindow ×ˢ W.angularWindow))

theorem ProductWindow.frameWindow_open (R : RealPartData F) {p : ℕ}
    (W : ProductWindow F R p) : IsOpen (W.frameWindow F R) :=
  W.image_open.preimage (continuous_orbitCoordinates F R _)

theorem ProductWindow.one_mem_frameWindow (R : RealPartData F) {p : ℕ}
    (W : ProductWindow F R p) : (1 : unitary (Matrix (Fin p) (Fin p) F)) ∈ W.frameWindow F R := by
  refine ⟨(referenceSpectrum p,0),⟨W.reference_mem,W.zero_mem⟩,?_⟩
  simp only [orbitCoordinates, unitaryConjugate_one, chartCoordinates_zero]
  exact (ambientCoordinates_diagonal F R _).symm

theorem ProductWindow.mem_frameWindow_iff (R : RealPartData F) {p : ℕ}
    (W : ProductWindow F R p) (U : unitary (Matrix (Fin p) (Fin p) F)) :
    U ∈ W.frameWindow F R ↔ ∃ a ∈ W.angularWindow,
      orbitCoordinates F R (referenceSpectrum p) U =
        chartCoordinates F R (referenceSpectrum p,a) := by
  constructor
  · rintro ⟨⟨mu,a⟩,⟨hmu,ha⟩,heq⟩
    have hm : unitaryConjugate F (cayleyUnitary F a (W.angular_subset ha))
          (diagonalHermitian F mu) =
        unitaryConjugate F U (diagonalHermitian F (referenceSpectrum p)) :=
      (hermitianCoordinates F R p).injective heq
    have hs := strict_spectrum_unique F _ _ (W.eigen_subset hmu).1
      (referenceSpectrum_mem_chamber p).1 hm
    change mu = referenceSpectrum p at hs
    subst mu
    exact ⟨a,ha,heq.symm⟩
  · rintro ⟨a,ha,heq⟩
    exact ⟨(referenceSpectrum p,a),⟨W.reference_mem,ha⟩,heq.symm⟩

/-- The indicator appearing in Haar averaging depends only on the frame,
not on the positive simple eigenvalues. -/
theorem ProductWindow.orbit_mem_image_iff (R : RealPartData F) {p : ℕ}
    (W : ProductWindow F R p) (lam : Fin p → ℝ) (hlam : lam ∈ chamber p)
    (U : unitary (Matrix (Fin p) (Fin p) F)) :
    orbitCoordinates F R lam U ∈ chartCoordinates F R '' (chamber p ×ˢ W.angularWindow) ↔
      U ∈ W.frameWindow F R := by
  rw [W.mem_frameWindow_iff]
  constructor
  · rintro ⟨⟨mu,a⟩,⟨hmu,ha⟩,heq⟩
    let V := cayleyUnitary F a (W.angular_subset ha)
    have hm : unitaryConjugate F V (diagonalHermitian F mu) =
        unitaryConjugate F U (diagonalHermitian F lam) :=
      (hermitianCoordinates F R p).injective heq
    have hs := strict_spectrum_unique F V U hmu.1 hlam.1 hm
    change mu = lam at hs
    subst mu
    refine ⟨a,ha,?_⟩
    exact congrArg (hermitianCoordinates F R p)
      (conjugate_diagonal_eq_forall_of_eq_simple F lam hlam.1.injective U V hm.symm _)
  · rintro ⟨a,ha,heq⟩
    let V := cayleyUnitary F a (W.angular_subset ha)
    have hm : unitaryConjugate F U (diagonalHermitian F (referenceSpectrum p)) =
        unitaryConjugate F V (diagonalHermitian F (referenceSpectrum p)) :=
      (hermitianCoordinates F R p).injective heq
    refine ⟨(lam,a),⟨hlam,ha⟩,?_⟩
    exact congrArg (hermitianCoordinates F R p)
      (conjugate_diagonal_eq_forall_of_eq_simple F (referenceSpectrum p)
        (referenceSpectrum_mem_chamber p).1.injective V U hm.symm lam)

theorem ProductWindow.haar_frameWindow_pos (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))]
    (W : ProductWindow F R p) :
    0 < TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F)) (W.frameWindow F R) :=
  (W.frameWindow_open F R).measure_pos _ ⟨1,W.one_mem_frameWindow F R⟩

theorem ProductWindow.haar_frameWindow_ne_top (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))]
    (W : ProductWindow F R p) :
    TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F)) (W.frameWindow F R) ≠ ∞ :=
  measure_ne_top _ _

end Wishart.FieldCharts
end
end CanonicalSource6

section CanonicalSource7
/- Source: Wishart/CompactJacobian.lean -/



/-!
# Compact linear group actions have unit absolute Jacobian

This avoids choosing a special invariant inner product.  A continuous positive
character of a compact group is bounded on all powers, hence is identically
one.  Applying this to the absolute real determinant gives the Jacobian claim.
-/

noncomputable section
open Set

namespace WishartVerification

theorem continuous_nonnegative_character_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (f : G →* ℝ) (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) (g : G) : f g = 1 := by
  obtain ⟨C,hC⟩ := (isCompact_range hf).bddAbove
  have hle (x : G) : f x ≤ 1 := by
    by_contra hx
    obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt C (lt_of_not_ge hx)
    have hb := hC (mem_range_self (x^n))
    rw [map_pow] at hb
    exact (not_lt_of_ge hb) hn
  apply le_antisymm (hle g)
  calc
    1 = f g * f g⁻¹ := by rw [← map_mul, mul_inv_cancel, map_one]
    _ ≤ f g * 1 := mul_le_mul_of_nonneg_left (hle g⁻¹) (h0 g)
    _ = f g := mul_one _

theorem abs_det_compact_representation
    {G E : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : G →* Module.End ℝ E)
    (hc : ∀ x : E, Continuous (fun g => ρ g x)) (g : G) :
    |LinearMap.det (ρ g)| = 1 := by
  let f : G →* ℝ :=
    { toFun := fun g => |LinearMap.det (ρ g)|
      map_one' := by simp
      map_mul' := by intro a b; simp only [map_mul, abs_mul] }
  apply continuous_nonnegative_character_eq_one f ?_ (fun _ => abs_nonneg _) g
  have hρ : Continuous (fun g => LinearMap.toContinuousLinearMap (ρ g)) := by
    rw [continuous_iff_continuousAt]
    intro g
    apply continuousAt_clm_apply.mpr
    intro x
    exact (hc x).continuousAt
  exact (ContinuousLinearMap.continuous_det.comp hρ).abs

end WishartVerification
end
end CanonicalSource7

section CanonicalSource8
/- Source: Wishart/FieldUnitaryJacobian.lean -/



/-!
# Unitary conjugation has absolute real determinant one

The proof uses compactness of the actual unitary group.  It applies in either
field and to every additive Haar normalization on the Hermitian space.
-/

noncomputable section
open Matrix MeasureTheory MeasureTheory.Measure
open scoped Classical Matrix.Norms.Operator

namespace Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F] [StarRing F]
  [StarModule ℝ F] [FiniteDimensional ℝ F] [ContinuousStar F] [MeasurableSpace F] [BorelSpace F]

def conjugationLinearEquiv {p : ℕ} (U : unitary (Matrix (Fin p) (Fin p) F)) :
    Hermitian F p ≃ₗ[ℝ] Hermitian F p where
  toFun := unitaryConjugate F U
  invFun := unitaryConjugate F (star U)
  left_inv X := by
    rw [← unitaryConjugate_mul, Unitary.star_mul_self, unitaryConjugate_one]
  right_inv X := by
    rw [← unitaryConjugate_mul, Unitary.mul_star_self, unitaryConjugate_one]
  map_add' X Y := by
    apply Subtype.ext
    simp only [unitaryConjugate, Submodule.coe_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by
    apply Subtype.ext
    simp only [unitaryConjugate, Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul,
      RingHom.id_apply]

def conjugationRepresentation (p : ℕ) :
    unitary (Matrix (Fin p) (Fin p) F) →* Module.End ℝ (Hermitian F p) where
  toFun U := (conjugationLinearEquiv F U).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro X
    exact unitaryConjugate_one F X
  map_mul' U V := by
    apply LinearMap.ext
    intro X
    exact unitaryConjugate_mul F U V X

theorem continuous_conjugation_apply {p : ℕ} (X : Hermitian F p) :
    Continuous (fun U : unitary (Matrix (Fin p) (Fin p) F) => unitaryConjugate F U X) := by
  apply Continuous.subtype_mk
  change Continuous (fun U : unitary (Matrix (Fin p) (Fin p) F) =>
    (U : Matrix (Fin p) (Fin p) F) * (X : Matrix (Fin p) (Fin p) F) * star U)
  fun_prop

theorem abs_det_conjugation {p : ℕ} [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))]
    (U : unitary (Matrix (Fin p) (Fin p) F)) :
    |LinearMap.det (conjugationLinearEquiv F U).toLinearMap| = 1 :=
  WishartVerification.abs_det_compact_representation (conjugationRepresentation F p)
    (continuous_conjugation_apply F) U

def coordinateConjugation (R : RealPartData F) {p : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) F)) : Coordinates F p ≃ₗ[ℝ] Coordinates F p :=
  ((hermitianCoordinates F R p).symm.trans (conjugationLinearEquiv F U)).trans
    (hermitianCoordinates F R p)

theorem abs_det_coordinateConjugation (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))]
    (U : unitary (Matrix (Fin p) (Fin p) F)) :
    |LinearMap.det (coordinateConjugation F R U).toLinearMap| = 1 := by
  have hd : LinearMap.det (coordinateConjugation F R U).toLinearMap =
      LinearMap.det (conjugationLinearEquiv F U).toLinearMap := by
    simpa only [LinearEquiv.coe_det, coordinateConjugation] using
      congrArg (fun u : ℝˣ => (u : ℝ))
      (LinearEquiv.det_conj (conjugationLinearEquiv F U) (hermitianCoordinates F R p))
  rw [hd, abs_det_conjugation F U]

theorem map_unitaryConjugate_addHaar {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))]
    [MeasurableSpace (Hermitian F p)] [BorelSpace (Hermitian F p)]
    (μ : Measure (Hermitian F p)) [IsAddHaarMeasure μ]
    (U : unitary (Matrix (Fin p) (Fin p) F)) :
    μ.map (unitaryConjugate F U) = μ := by
  have hd := abs_det_conjugation F U
  have hn : LinearMap.det (conjugationLinearEquiv F U).toLinearMap ≠ 0 := by
    intro h
    rw [h, abs_zero] at hd
    exact zero_ne_one hd
  change μ.map ((conjugationLinearEquiv F U).toLinearMap) = μ
  have hmap := @Measure.map_linearMap_addHaar_eq_smul_addHaar (Hermitian F p)
    _ _ _ ‹BorelSpace (Hermitian F p)› _ μ ‹IsAddHaarMeasure μ›
      (conjugationLinearEquiv F U).toLinearMap hn
  simpa only [abs_inv, hd, inv_one, ENNReal.ofReal_one, one_smul] using hmap

end Wishart.FieldCharts
end
end CanonicalSource8

section CanonicalSource9
/- Source: Wishart/FieldChartJacobian.lean -/



/-!
# Exact angular–Vandermonde factorization of the field spectral Jacobian

All derivatives are derivatives of the literal Cayley spectral map. The
angular determinant is independent of the eigenvalues. Repeated spectra make
the Jacobian vanish; this will also give the null repeated-spectrum locus by
the equal-dimensional critical-image theorem.
-/

noncomputable section
open Matrix
open scoped Classical Matrix.Norms.Operator

namespace Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F] [StarRing F]
  [StarModule ℝ F] [FiniteDimensional ℝ F] [ContinuousStar F]
  [MeasurableSpace F] [BorelSpace F]

def innerHermitian {p : ℕ} (z : OffDiagonal F p) (lam : Fin p → ℝ)
    (h : Coordinates F p) : Hermitian F p :=
  ⟨realDiagonal F h.1 +
    (angularFull F z h.2 * realDiagonal F lam - realDiagonal F lam * angularFull F z h.2), by
    have hd (a : Fin p → ℝ) : (realDiagonal F a)ᴴ = realDiagonal F a := by
      simp [realDiagonal, Algebra.algebraMap_eq_smul_one]
    change (realDiagonal F h.1 + (_ - _))ᴴ = _
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, hd, angularFull_star, Matrix.neg_mul, Matrix.mul_neg]
    abel⟩

theorem innerHermitian_coordinates (R : RealPartData F) {p : ℕ}
    (z : OffDiagonal F p) (lam : Fin p → ℝ) (h : Coordinates F p) :
    hermitianCoordinates F R p (innerHermitian F z lam h) = spectralInnerLinearMap F z lam h := by
  change ambientCoordinates F R p (realDiagonal F h.1 +
    (angularFull F z h.2 * realDiagonal F lam - realDiagonal F lam * angularFull F z h.2)) = _
  rw [map_add, ambientCoordinates_diagonal,
    ambientCoordinates_skew_commutator F R lam _ (angularFull_star F z h.2)]
  simp only [Prod.mk_add_mk, add_zero, zero_add, spectralInnerLinearMap_apply,
    angularOffLinearMap_apply]
  rfl

def chartDerivative (R : RealPartData F) {p : ℕ}
    (z : OffDiagonal F p) (hz : z ∈ cayleyDomain F p) (lam : Fin p → ℝ) :
    Coordinates F p →L[ℝ] Coordinates F p :=
  (coordinateConjugation F R (cayleyUnitary F z hz)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (spectralInnerLinearMap F z lam).toContinuousLinearMap

theorem chartDerivative_apply (R : RealPartData F) {p : ℕ}
    (z : OffDiagonal F p) (hz : z ∈ cayleyDomain F p)
    (lam : Fin p → ℝ) (h : Coordinates F p) :
    chartDerivative F R z hz lam h =
      ambientCoordinates F R p (cayleyMatrix F z *
        (realDiagonal F h.1 + angularFull F z h.2 * realDiagonal F lam -
          realDiagonal F lam * angularFull F z h.2) * (cayleyMatrix F z)ᴴ) := by
  change hermitianCoordinates F R p (unitaryConjugate F (cayleyUnitary F z hz)
    ((hermitianCoordinates F R p).symm (spectralInnerLinearMap F z lam h))) = _
  rw [← innerHermitian_coordinates F R z lam h,
    LinearEquiv.symm_apply_apply]
  change ambientCoordinates F R p (cayleyMatrix F z *
    (realDiagonal F h.1 + (angularFull F z h.2 * realDiagonal F lam -
      realDiagonal F lam * angularFull F z h.2)) * (cayleyMatrix F z)ᴴ) = _
  rw [add_sub_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem hasStrictFDerivAt_chartCoordinates (R : RealPartData F) {p : ℕ}
    (x : Coordinates F p) (hx : x.2 ∈ cayleyDomain F p) :
    HasStrictFDerivAt (chartCoordinates F R) (chartDerivative F R x.2 hx x.1) x := by
  let P : Coordinates F p →L[ℝ] Matrix (Fin p) (Fin p) F :=
    (skewOffLinearMap F p).toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ _ _)
  let D : Coordinates F p →L[ℝ] Matrix (Fin p) (Fin p) F :=
    (realDiagonalLinearMap F p).toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ _)
  let T : Matrix (Fin p) (Fin p) F →L[ℝ] Matrix (Fin p) (Fin p) F :=
    (starMatrixLinearMap F p).toContinuousLinearMap
  let Q : Coordinates F p → Matrix (Fin p) (Fin p) F := fun y => cayleyElement (P y)
  let Q' : Coordinates F p →L[ℝ] Matrix (Fin p) (Fin p) F :=
    (cayleyDerivative (P x)).comp P
  have hQ : HasStrictFDerivAt Q Q' x :=
    (hasStrictFDerivAt_cayleyElement hx).comp x P.hasStrictFDerivAt
  have hraw := ((hQ.mul' D.hasStrictFDerivAt).mul'
    (T.hasStrictFDerivAt.comp x hQ))
  have hc := (ambientCoordinates F R p).toContinuousLinearMap.hasStrictFDerivAt.comp x hraw
  have hfun : (fun y => (ambientCoordinates F R p).toContinuousLinearMap
      ((Q * D * fun y => T (Q y)) y)) = chartCoordinates F R := by
    funext y
    rfl
  rw [hfun] at hc
  apply hc.congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  change ambientCoordinates F R p
    (Q x * D x * T (Q' h) + (Q x * D h + Q' h * D x) * T (Q x)) = _
  have hd : Q' h = cayleyMatrix F x.2 * angularFull F x.2 h.2 :=
    cayley_derivative_eq_angular F x.2 h.2 hx
  rw [hd, chartDerivative_apply]
  change ambientCoordinates F R p
    (cayleyMatrix F x.2 * realDiagonal F x.1 *
      (cayleyMatrix F x.2 * angularFull F x.2 h.2)ᴴ +
      (cayleyMatrix F x.2 * realDiagonal F h.1 +
        cayleyMatrix F x.2 * angularFull F x.2 h.2 * realDiagonal F x.1) *
          (cayleyMatrix F x.2)ᴴ) = _
  rw [Matrix.conjTranspose_mul, angularFull_star]
  congr 1
  noncomm_ring

theorem abs_det_chartDerivative (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))]
    (z : OffDiagonal F p) (hz : z ∈ cayleyDomain F p) (lam : Fin p → ℝ) :
    |LinearMap.det (chartDerivative F R z hz lam).toLinearMap| =
      |LinearMap.det (angularOffLinearMap F z)| *
        |∏ ij : PairIndex p, (lam ij.1.2 - lam ij.1.1)| ^ Module.finrank ℝ F := by
  change |LinearMap.det ((coordinateConjugation F R (cayleyUnitary F z hz)).toLinearMap.comp
    (spectralInnerLinearMap F z lam))| = _
  rw [LinearMap.det_comp, abs_mul, abs_det_coordinateConjugation F R,
    one_mul, det_spectralInnerLinearMap, abs_mul, abs_pow]

theorem abs_det_fderiv_chartCoordinates (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))]
    (x : Coordinates F p) (hx : x.2 ∈ cayleyDomain F p) :
    |(fderiv ℝ (chartCoordinates F R) x).det| =
      |LinearMap.det (angularOffLinearMap F x.2)| *
        |∏ ij : PairIndex p, (x.1 ij.1.2 - x.1 ij.1.1)| ^ Module.finrank ℝ F := by
  rw [(hasStrictFDerivAt_chartCoordinates F R x hx).hasFDerivAt.fderiv]
  exact abs_det_chartDerivative F R x.2 hx x.1

end Wishart.FieldCharts
end
end CanonicalSource9

section CanonicalSource10
/- Source: Wishart/FieldAngularMeasure.lean -/



/-!
# The actual angular reference measure and Jacobian

The finite positive normalization of the spectral density will be obtained
from probability mass.  No angular integral is assumed finite in this file.
-/

noncomputable section
open Matrix MeasureTheory MeasureTheory.Measure Set
open scoped Classical Ring Topology ENNReal Matrix.Norms.Operator

namespace Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F] [StarRing F]
  [StarModule ℝ F] [FiniteDimensional ℝ F] [ContinuousStar F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]

def angularLebesgue (p : ℕ) : Measure (OffDiagonal F p) :=
  (Module.finBasis ℝ (OffDiagonal F p)).addHaar

instance angularLebesgue_isAddHaarMeasure (p : ℕ) :
    IsAddHaarMeasure (angularLebesgue F p) := by unfold angularLebesgue; infer_instance

instance angularLebesgue_sigmaFinite (p : ℕ) : SigmaFinite (angularLebesgue F p) := by
  unfold angularLebesgue
  infer_instance

def coordinateLebesgue (p : ℕ) : Measure (Coordinates F p) :=
  (volume : Measure (Fin p → ℝ)).prod (angularLebesgue F p)

instance coordinateLebesgue_isAddHaarMeasure (p : ℕ) :
    IsAddHaarMeasure (coordinateLebesgue F p) := by unfold coordinateLebesgue; infer_instance

instance coordinateLebesgue_sigmaFinite (p : ℕ) : SigmaFinite (coordinateLebesgue F p) := by
  unfold coordinateLebesgue
  infer_instance

def angularJacobian {p : ℕ} (z : OffDiagonal F p) : ℝ :=
  |LinearMap.det (angularOffLinearMap F z)|

theorem continuousOn_angularFull_apply {p : ℕ} (h : OffDiagonal F p) :
    ContinuousOn (fun z => angularFull F z h) (cayleyDomain F p) := by
  intro z hz
  obtain ⟨u,hu⟩ := hz
  have hlin : Continuous (fun z : OffDiagonal F p => 1 + skewOffEntries F z) :=
    continuous_const.add (skewOffLinearMap F p).continuous_of_finiteDimensional
  have hi : ContinuousAt (fun z : OffDiagonal F p => (1 + skewOffEntries F z)⁻¹ʳ) z := by
    have hi := NormedRing.inverse_continuousAt u
    rw [hu] at hi
    have h := hi.comp (f := fun z : OffDiagonal F p => 1 + skewOffEntries F z)
      hlin.continuousAt
    convert h using 1 <;> rfl
  exact (((hi.star.mul continuousAt_const).mul hi).const_smul (-2 : ℝ)).continuousWithinAt

theorem continuousOn_angularJacobian (p : ℕ) :
    ContinuousOn (angularJacobian F (p := p)) (cayleyDomain F p) := by
  change ContinuousOn (fun z : OffDiagonal F p => |LinearMap.det (angularOffLinearMap F z)|) _
  let b := Module.finBasis ℝ (OffDiagonal F p)
  have hentry (i j : Fin (Module.finrank ℝ (OffDiagonal F p))) :
      ContinuousOn (fun z => LinearMap.toMatrix b b (angularOffLinearMap F z) i j)
        (cayleyDomain F p) := by
    have hc : ContinuousOn (fun z => angularOffLinearMap F z (b j)) (cayleyDomain F p) := by
      apply continuousOn_pi.mpr
      intro ij
      exact (continuous_apply ij.1.2).comp_continuousOn
        ((continuous_apply ij.1.1).comp_continuousOn (continuousOn_angularFull_apply F (b j)))
    simpa only [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, Function.comp_def,
      Module.Basis.equivFun_apply] using
      ((continuous_apply i).comp b.equivFun.toLinearMap.continuous_of_finiteDimensional).comp_continuousOn hc
  have hm : ContinuousOn (fun z => LinearMap.toMatrix b b (angularOffLinearMap F z))
      (cayleyDomain F p) := continuousOn_pi.mpr fun i => continuousOn_pi.mpr (hentry i)
  simpa only [angularJacobian, Function.comp_def, id_eq, LinearMap.det_toMatrix] using
    (continuous_id.matrix_det.comp_continuousOn hm).abs

def ProductWindow.angularWeight (R : RealPartData F) {p : ℕ}
    (W : ProductWindow F R p) : OffDiagonal F p → ℝ≥0∞ :=
  W.angularWindow.indicator (fun z => ENNReal.ofReal (angularJacobian F z))

theorem ProductWindow.measurable_angularWeight (R : RealPartData F) {p : ℕ}
    (W : ProductWindow F R p) : Measurable (W.angularWeight F R) := by
  have hc : ContinuousOn (fun z => ENNReal.ofReal (angularJacobian F z)) W.angularWindow :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((continuousOn_angularJacobian F p).mono W.angular_subset)
  exact hc.measurable_piecewise continuous_const.continuousOn W.angular_open.measurableSet

@[simp] theorem ProductWindow.angularWeight_of_mem (R : RealPartData F) {p : ℕ}
    (W : ProductWindow F R p) {z : OffDiagonal F p} (hz : z ∈ W.angularWindow) :
    W.angularWeight F R z = ENNReal.ofReal (angularJacobian F z) :=
  Set.indicator_of_mem hz _

def ProductWindow.angularMass (R : RealPartData F) {p : ℕ} (W : ProductWindow F R p) :
    ℝ≥0∞ := ∫⁻ z, W.angularWeight F R z ∂angularLebesgue F p

def ProductWindow.imageWindow (R : RealPartData F) {p : ℕ} (W : ProductWindow F R p) :
    Set (Coordinates F p) := chartCoordinates F R '' (chamber p ×ˢ W.angularWindow)

theorem ProductWindow.measurableSet_imageWindow (R : RealPartData F) {p : ℕ}
    (W : ProductWindow F R p) : MeasurableSet (W.imageWindow F R) := by
  apply measurable_image_of_fderivWithin
    ((Wishart.Spectral.isOpen_positiveChamber p).measurableSet.prod W.angular_open.measurableSet)
    (f' := fderiv ℝ (chartCoordinates F R)) _ (W.injOn_chamber F R)
  intro x hx
  have hd := (hasStrictFDerivAt_chartCoordinates F R x (W.angular_subset hx.2)).hasFDerivAt
  rw [hd.fderiv]
  exact hd.hasFDerivWithinAt

end Wishart.FieldCharts
end
end CanonicalSource10

section CanonicalSource11
/- Source: Wishart/HaarIsometry.lean -/



/-! A real linear isometry preserves every additive Haar normalization. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal

namespace WishartVerification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem linearIsometryEquiv_map_addHaar (L : E ≃ₗᵢ[ℝ] E)
    (μ : Measure E) [IsAddHaarMeasure μ] : μ.map L = μ := by
  letI : IsAddHaarMeasure (μ.map L) := L.toContinuousLinearEquiv.isAddHaarMeasure_map μ
  let c := Measure.addHaarScalarFactor (μ.map L) μ
  have hscale : μ.map L = c • μ :=
    Measure.isAddLeftInvariant_eq_smul (μ.map L) μ
  have hpre : L ⁻¹' ball (0 : E) 1 = ball (0 : E) 1 := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, L.norm_map]
  have hmass : (c : ℝ≥0∞) * μ (ball (0 : E) 1) = μ (ball (0 : E) 1) := by
    have h := congrArg (fun ν : Measure E => ν (ball (0 : E) 1)) hscale
    rw [Measure.map_apply L.continuous.measurable isOpen_ball.measurableSet, hpre,
      Measure.smul_apply] at h
    change μ (ball (0 : E) 1) = (c : ℝ≥0∞) * μ (ball (0 : E) 1) at h
    exact h.symm
  have h0 : μ (ball (0 : E) 1) ≠ 0 :=
    (isOpen_ball.measure_pos μ (nonempty_ball.mpr zero_lt_one)).ne'
  have htop : μ (ball (0 : E) 1) ≠ ∞ :=
    (measure_mono (ball_subset_closedBall : ball (0 : E) 1 ⊆ closedBall 0 1)).trans_lt
      (isCompact_closedBall (0 : E) 1).measure_lt_top |>.ne
  have hc : (c : ℝ≥0∞) = 1 := by
    calc
      (c : ℝ≥0∞) = ((c : ℝ≥0∞) * μ (ball (0 : E) 1)) *
          (μ (ball (0 : E) 1))⁻¹ := (ENNReal.mul_inv_cancel_right h0 htop).symm
      _ = 1 := by rw [hmass, ENNReal.mul_inv_cancel h0 htop]
  have hc' : c = 1 := ENNReal.coe_injective hc
  rw [hscale, hc', one_smul]

end WishartVerification
end
end CanonicalSource11
