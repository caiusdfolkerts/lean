module

public import Ellipsoid.PositiveJacobians
public import tau_ceti.analysis.convex.stiemke

@[expose] public section

noncomputable section

open Matrix Finset
open scoped BigOperators

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def DiagonallyStable (A : Matrix ι ι ℝ) : Prop :=
  ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧
    (symmetricPart (Matrix.diagonal d * A)).PosDef

theorem DiagonallyStable.exists_positive_coordinate {A : Matrix ι ι ℝ}
    (hA : DiagonallyStable A) {x : ι → ℝ} (hx : x ≠ 0) :
    ∃ i, 0 < x i * (A *ᵥ x) i := by
  obtain ⟨d, hd, hpd⟩ := hA
  have hp := quadratic_pos_of_symmetricPart_posDef hpd hx
  by_contra h
  push_neg at h
  have hsum : ∑ i, d i * (x i * (A *ᵥ x) i) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hd i).le (h i)
  have heq : x ⬝ᵥ ((Matrix.diagonal d * A) *ᵥ x) =
      ∑ i, d i * (x i * (A *ᵥ x) i) := by
    simp only [← Matrix.mulVec_mulVec, dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq] at hp
  exact (not_lt_of_ge hsum) hp

theorem DiagonallyStable.no_nonnegative_transpose_reverse {A : Matrix ι ι ℝ}
    (hA : DiagonallyStable A) {y : ι → ℝ}
    (hy : 0 ≤ y) (hAy : Aᵀ *ᵥ y ≤ 0) : y = 0 := by
  obtain ⟨d, hd, hpd⟩ := hA
  let x : ι → ℝ := fun i => y i / d i
  have hx : 0 ≤ x := fun i => div_nonneg (hy i) (hd i).le
  by_contra hy0
  have hx0 : x ≠ 0 := by
    intro hx0
    apply hy0
    funext i
    have hi := congrFun hx0 i
    exact (div_eq_zero_iff).mp hi |>.resolve_right (hd i).ne'
  have hp := quadratic_pos_of_symmetricPart_posDef hpd hx0
  have hsum : (Aᵀ *ᵥ y) ⬝ᵥ x ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (hAy i) (hx i)
  have heq : x ⬝ᵥ ((Matrix.diagonal d * A) *ᵥ x) = (Aᵀ *ᵥ y) ⬝ᵥ x := by
    simp only [dotProduct, Matrix.mulVec, Matrix.diagonal_mul,
      Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [x]
    field_simp [(hd i).ne', (hd j).ne']
  rw [heq] at hp
  exact (not_lt_of_ge hsum) hp

def alternativeGraph (A : Matrix ι ι ℝ) : (ι → ℝ) →ₗ[ℝ] (ι ⊕ ι → ℝ) where
  toFun y := Sum.elim (fun i => -(Aᵀ *ᵥ y) i) y
  map_add' x y := by
    funext i
    cases i <;> simp [Matrix.mulVec_add, add_comm]
  map_smul' r y := by
    funext i
    cases i <;> simp [Matrix.mulVec_smul, mul_neg]

/-- The positive direction used in the rectangle univalence proof is
derived from Stiemke's theorem of the alternative, not assumed. -/
theorem DiagonallyStable.exists_pos_mulVec_pos {A : Matrix ι ι ℝ}
    (hA : DiagonallyStable A) :
    ∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ ∀ i, 0 < (A *ᵥ v) i := by
  have hcone : ∀ z ∈ (alternativeGraph A).range, (0 : ι ⊕ ι → ℝ) ≤ z → z = 0 := by
    rintro z ⟨y, rfl⟩ hz
    have hy : 0 ≤ y := fun i => hz (Sum.inr i)
    have hAy : Aᵀ *ᵥ y ≤ 0 := fun i => by
      have hi := hz (Sum.inl i)
      simpa only [alternativeGraph, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl,
        Pi.zero_apply, neg_nonneg] using hi
    have hy0 := hA.no_nonnegative_transpose_reverse hy hAy
    simp [hy0]
  obtain ⟨w, hw, horth⟩ := TauCeti.exists_pos_forall_sum_mul_eq_zero_iff.mpr hcone
  refine ⟨fun i => w (Sum.inl i), fun i => hw _, fun j => ?_⟩
  have hj := horth (alternativeGraph A (Pi.single j 1)) ⟨Pi.single j 1, rfl⟩
  have heq : (A *ᵥ (fun i => w (Sum.inl i))) j = w (Sum.inr j) := by
    simp only [Fintype.sum_sum_type, alternativeGraph, LinearMap.coe_mk, AddHom.coe_mk,
      Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, mul_neg, Finset.sum_neg_distrib] at hj
    dsimp [Matrix.mulVec, dotProduct]
    have hcomm : (∑ i, w (Sum.inl i) * A j i) = ∑ i, A j i * w (Sum.inl i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hcomm] at hj
    linarith
  rw [heq]
  exact hw (Sum.inr j)

theorem DiagonallyStable.submatrix {A : Matrix ι ι ℝ} (hA : DiagonallyStable A)
    (s : Finset ι) :
    DiagonallyStable (A.submatrix (fun i : s => i.val) (fun i : s => i.val)) := by
  obtain ⟨d, hd, hpd⟩ := hA
  refine ⟨fun i => d i.val, fun i => hd i.val, ?_⟩
  have h := hpd.submatrix (e := fun i : s => i.val) (fun a b h => Subtype.ext h)
  convert h using 1
  ext i j
  simp [symmetricPart, Matrix.diagonal_mul, mul_add]

end EllipsoidVerification
