module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The integral Cramer step in the Newton basis argument

Over a domain, Cramer's rule produces polynomial coefficients when the full
determinant divides every replaced-column determinant. This theorem constructs
a basis of the specified submodule and identifies every basis vector with the
literal matrix column. It supplies the algebraic last step of Proposition 2.2;
the Newton determinant factor and local divisibilities must be established
before this theorem is applied there.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open scoped BigOperators Matrix

variable {R I : Type*} [CommRing R] [IsDomain R] [Fintype I] [DecidableEq I]

/-- Factoring a prescribed divisor from every row gives the product divisor
of the determinant. -/
theorem prod_row_divisors_dvd_det (A : Matrix I I R) (d : I → R)
    (h : ∀ i j, d i ∣ A i j) : (∏ i, d i) ∣ A.det := by
  choose B hB using h
  let B' : Matrix I I R := Matrix.of B
  have hA : A = Matrix.diagonal d * B' := by
    ext i j
    simpa only [Matrix.diagonal_mul, B', Matrix.of_apply] using hB i j
  refine ⟨B'.det, ?_⟩
  rw [hA, Matrix.det_mul, Matrix.det_diagonal]

/-- A divisor common to one row divides the determinant. -/
theorem row_divisor_dvd_det (A : Matrix I I R) (i : I) (p : R)
    (h : ∀ j, p ∣ A i j) : p ∣ A.det := by
  choose r hr using h
  have hrow : A i = p • r := funext hr
  refine ⟨(A.updateRow i r).det, ?_⟩
  calc
    A.det = (A.updateRow i (A i)).det := by rw [Matrix.updateRow_eq_self]
    _ = p * (A.updateRow i r).det := by rw [hrow, Matrix.det_updateRow_smul]

/-- The positive-edge tangent condition forces one factor in every determinant. -/
theorem tangent_factor_dvd_det (A : Matrix I I R) (i j : I) (hij : i ≠ j) (p : R)
    (h : ∀ k, p ∣ A i k - A j k) : p ∣ A.det := by
  let B := A.updateRow i (A i + (-1 : R) • A j)
  have hb : p ∣ B.det := by
    apply row_divisor_dvd_det B i p
    intro k
    simpa only [B, Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      neg_one_mul, sub_eq_add_neg] using h k
  rwa [Matrix.det_updateRow_add_smul_self A hij (-1)] at hb

/-- A divisor common to all rows except one occurs to the expected power. -/
theorem all_but_one_row_divisor_dvd_det (A : Matrix I I R) (i : I) (p : R)
    (h : ∀ j, j ≠ i → ∀ k, p ∣ A j k) : p ^ (Fintype.card I - 1) ∣ A.det := by
  let d : I → R := fun j ↦ if j = i then 1 else p
  have hd : ∀ j k, d j ∣ A j k := by
    intro j k
    by_cases hj : j = i
    · simp [d, hj]
    · simpa only [d, if_neg hj] using h j hj k
  have hprod : (∏ j, d j) = p ^ (Fintype.card I - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
    have heq : (∏ j ∈ Finset.univ.erase i, d j) = ∏ j ∈ Finset.univ.erase i, p := by
      apply Finset.prod_congr rfl
      intro j hj
      exact if_neg (Finset.mem_erase.mp hj).1
    rw [heq]
    simp [d]
  rw [← hprod]
  exact prod_row_divisors_dvd_det A d hd

/-- The negative-edge normal conditions put all possible nondivisibility into
one row, forcing `p^(n-1)` in the numerator determinant. -/
theorem normal_factor_pow_dvd_det (A : Matrix I I R) (i j : I) (hij : i ≠ j)
    (p u v : R) (hv : IsUnit v)
    (hpair : ∀ k, p ∣ u * A i k + v * A j k)
    (hother : ∀ l, l ≠ i → l ≠ j → ∀ k, p ∣ A l k) :
    p ^ (Fintype.card I - 1) ∣ A.det := by
  let B := A.updateRow j (u • A i + v • A j)
  have hb : p ^ (Fintype.card I - 1) ∣ B.det := by
    apply all_but_one_row_divisor_dvd_det B i p
    intro l hli k
    by_cases hlj : l = j
    · subst l
      simpa only [B, Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        using hpair k
    · simpa only [B, Matrix.updateRow_ne hlj] using hother l hli hlj k
  have hdet : B.det = v * A.det := by
    dsimp [B]
    rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_updateRow_smul,
      Matrix.det_updateRow_eq_zero hij, mul_zero, zero_add, Matrix.updateRow_eq_self]
  rw [hdet] at hb
  exact hv.dvd_mul_left.mp hb

/-- Nonzero determinant makes multiplication by a square matrix injective
without requiring the determinant to be a unit. -/
theorem mulVec_injective_of_det_ne_zero (A : Matrix I I R) (hA : A.det ≠ 0) :
    Function.Injective (fun c ↦ A *ᵥ c) := by
  intro c d h
  have hh := congrArg (fun v ↦ A.adjugate *ᵥ v) h
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at hh
  funext i
  exact mul_left_cancel₀ hA (congrFun hh i)

/-- Divisibility of the replaced-column determinants gives an integral solution. -/
theorem exists_mulVec_eq_of_cramer_dvd (A : Matrix I I R) (hA : A.det ≠ 0)
    (v : I → R) (hdiv : ∀ i, A.det ∣ (A.updateCol i v).det) :
    ∃ c : I → R, A *ᵥ c = v := by
  have hd : ∀ i, A.det ∣ A.cramer v i := by simpa only [Matrix.cramer_apply] using hdiv
  choose c hc using hd
  have hcr : A.cramer v = A.det • c := by
    funext i
    exact hc i
  have h := Matrix.mulVec_cramer A v
  rw [hcr, Matrix.mulVec_smul] at h
  refine ⟨c, ?_⟩
  funext i
  exact mul_left_cancel₀ hA (congrFun h i)

/-- The column map has its literal specified submodule as codomain. -/
def columnMapToSubmodule (N : Submodule R (I → R)) (A : Matrix I I R)
    (hcol : ∀ j, (fun i ↦ A i j) ∈ N) : (I → R) →ₗ[R] N :=
  (Matrix.mulVecLin A).codRestrict N (by
    intro c
    have hm : A *ᵥ c = ∑ j, c j • (fun i ↦ A i j) := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        mul_comm]
    rw [Matrix.mulVecLin_apply, hm]
    exact N.sum_mem fun j _ ↦ N.smul_mem _ (hcol j))

 theorem columnMapToSubmodule_bijective (N : Submodule R (I → R)) (A : Matrix I I R)
    (hcol : ∀ j, (fun i ↦ A i j) ∈ N) (hA : A.det ≠ 0)
    (hdiv : ∀ v ∈ N, ∀ i, A.det ∣ (A.updateCol i v).det) :
    Function.Bijective (columnMapToSubmodule N A hcol) := by
  constructor
  · intro c d h
    apply mulVec_injective_of_det_ne_zero A hA
    simpa only [columnMapToSubmodule, LinearMap.codRestrict_apply,
      Matrix.mulVecLin_apply] using congrArg Subtype.val h
  · intro v
    obtain ⟨c, hc⟩ := exists_mulVec_eq_of_cramer_dvd A hA v.val (hdiv v.val v.prop)
    exact ⟨c, Subtype.ext hc⟩

/-- Cramer's rule as an actual basis constructor for the full Newton module. -/
def basisOfColumnDeterminants (N : Submodule R (I → R)) (A : Matrix I I R)
    (hcol : ∀ j, (fun i ↦ A i j) ∈ N) (hA : A.det ≠ 0)
    (hdiv : ∀ v ∈ N, ∀ i, A.det ∣ (A.updateCol i v).det) : Module.Basis I R N :=
  (Pi.basisFun R I).map
    (LinearEquiv.ofBijective (columnMapToSubmodule N A hcol)
      (columnMapToSubmodule_bijective N A hcol hA hdiv))

@[simp] theorem basisOfColumnDeterminants_apply
    (N : Submodule R (I → R)) (A : Matrix I I R)
    (hcol : ∀ j, (fun i ↦ A i j) ∈ N) (hA : A.det ≠ 0)
    (hdiv : ∀ v ∈ N, ∀ i, A.det ∣ (A.updateCol i v).det) (j : I) :
    ((basisOfColumnDeterminants N A hcol hA hdiv j : N) : I → R) = fun i ↦ A i j := by
  simp only [basisOfColumnDeterminants, Module.Basis.map_apply, Pi.basisFun_apply,
    LinearEquiv.ofBijective_apply, columnMapToSubmodule, LinearMap.codRestrict_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  rfl

end PaperVerification.Fermion.Newton
