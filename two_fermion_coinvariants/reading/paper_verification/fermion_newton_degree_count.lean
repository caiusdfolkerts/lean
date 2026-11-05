module

public import PaperVerification.FermionNewtonHomogeneity

/-!
# The exact degree count in the Newton determinant

Counting each signed edge by its later endpoint identifies the sum of column
degrees with the degree of the full local determinant divisor. Together with
nonvanishing and local divisibility, this forces a nonzero scalar quotient.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators Matrix

variable {F : Type*} [Field F] {n : ℕ}

def edgeEndEquiv (σ : Fin n → ℤ) (a : ℤ) :
    (Σ i : Fin n, {j : Fin n // j < i ∧ σ j = a}) ≃ {e : Edge n // σ e.1.1 = a} where
  toFun x := ⟨⟨(x.2.val,x.1),x.2.property.1⟩,x.2.property.2⟩
  invFun e := ⟨e.val.val.2,⟨e.val.val.1,e.val.property,e.property⟩⟩
  left_inv x := by cases x; rfl
  right_inv e := by cases e; rfl

theorem sum_earlier_sign_card (σ : Fin n → ℤ) (a : ℤ) :
    (∑ i : Fin n, (Finset.univ.filter (fun j ↦ j < i ∧ σ j = a)).card) =
      (signedEdges σ a).card := by
  have h := Fintype.card_congr (edgeEndEquiv σ a)
  simpa only [Fintype.card_sigma, Fintype.card_subtype, signedEdges] using h

theorem sum_earlierPositive_card (σ : Fin n → ℤ) :
    (∑ i, (earlierPositive σ i).card) = positiveEdgeCount σ :=
  sum_earlier_sign_card σ 1

theorem sum_earlierNegative_card (σ : Fin n → ℤ) :
    (∑ i, (earlierNegative σ i).card) = negativeEdgeCount σ :=
  sum_earlier_sign_card σ (-1)

theorem earlierNegative_card_le (σ : Fin n → ℤ) (i : Fin n) :
    (earlierNegative σ i).card ≤ negativeEdgeCount σ := by
  rw [← sum_earlierNegative_card]
  exact Finset.single_le_sum (fun j hj ↦ Nat.zero_le (earlierNegative σ j).card)
    (Finset.mem_univ i)

def determinantDegree (δ : Fin n → ℕ) (σ : Fin n → ℤ) : ℕ :=
  (∑ i, δ i) + positiveEdgeCount σ + (n - 1) * negativeEdgeCount σ

theorem sum_numeratorMultiplicity (δ : Fin n → ℕ) (σ : Fin n → ℤ) :
    (∑ h : Hyperplane n, numeratorMultiplicity δ σ h) = determinantDegree δ σ := by
  rw [Fintype.sum_sum_type]
  have hterm (e : Edge n) : numeratorMultiplicity δ σ (.inr e) =
      (if σ e.1.1 = 1 then 1 else 0) + (if σ e.1.1 = -1 then n - 1 else 0) := by
    by_cases hp : σ e.1.1 = 1
    · simp only [numeratorMultiplicity, if_pos hp, if_neg (by omega : σ e.1.1 ≠ -1), add_zero]
    · by_cases hn : σ e.1.1 = -1 <;> simp [numeratorMultiplicity, hp, hn]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hp : (∑ e : Edge n, if σ e.1.1 = 1 then 1 else 0) = positiveEdgeCount σ := by
    simp only [positiveEdgeCount, signedEdges, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
  have hn : (∑ e : Edge n, if σ e.1.1 = -1 then n - 1 else 0) =
      (n - 1) * negativeEdgeCount σ := by
    simp only [negativeEdgeCount, signedEdges, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    exact mul_comm _ _
  rw [hp,hn]
  simp only [numeratorMultiplicity, determinantDegree, Nat.add_assoc]

theorem sum_columnNumeratorDegree (δ : Fin n → ℕ) (σ : Fin n → ℤ) :
    (∑ i, columnNumeratorDegree δ σ i) = determinantDegree δ σ := by
  have hi (i : Fin n) : columnNumeratorDegree δ σ i + (earlierNegative σ i).card =
      negativeEdgeCount σ + δ i + (earlierPositive σ i).card := by
    unfold columnNumeratorDegree
    apply Nat.sub_add_cancel
    exact (earlierNegative_card_le σ i).trans (by omega)
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i hi' ↦ hi i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id,
    sum_earlierNegative_card, sum_earlierPositive_card] at hsum
  by_cases hn : n = 0
  · subst n
    simp [determinantDegree, positiveEdgeCount, negativeEdgeCount, signedEdges]
  · have hmul : n * negativeEdgeCount σ = (n - 1) * negativeEdgeCount σ + negativeEdgeCount σ := by
      have he : n = (n - 1) + 1 := by omega
      calc
        n * negativeEdgeCount σ = ((n - 1) + 1) * negativeEdgeCount σ := congrArg (· * _) he
        _ = _ := by rw [Nat.add_mul, one_mul]
    rw [hmul] at hsum
    unfold determinantDegree
    omega

theorem numeratorDetFactor_homogeneous (δ : Fin n → ℕ) (σ : Fin n → ℤ) :
    (numeratorDetFactor (F := F) δ σ).IsHomogeneous (determinantDegree δ σ) := by
  rw [← sum_numeratorMultiplicity δ σ]
  apply IsHomogeneous.prod
  intro h hh
  cases h with
  | inl i => exact isHomogeneous_X_pow i (δ i)
  | inr e =>
      have he := ((isHomogeneous_X F e.1.1).sub (isHomogeneous_X F e.1.2)).pow
        (numeratorMultiplicity δ σ (.inr e))
      simpa only [hyperplaneLinear,edgeLinear,one_mul] using he

theorem commonNumeratorMatrix_det_homogeneous_degree
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ) :
    (commonNumeratorMatrix β δ σ hc).det.IsHomogeneous (determinantDegree δ σ) := by
  rw [← sum_columnNumeratorDegree δ σ]
  exact commonNumeratorMatrix_det_homogeneous β δ σ hc

/-- Local divisibility, the exact degree count, and the complete determinant
induction yield a nonzero scalar factor for the literal matrix. -/
theorem exists_commonNumerator_determinant_scalar
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    ∃ c : F, c ≠ 0 ∧ (commonNumeratorMatrix β δ σ hc).det = C c * numeratorDetFactor δ σ := by
  have hβi (i : Fin n) : β i ≠ 0 := by
    simpa only [Finset.sum_singleton] using (hβ {i} (Finset.singleton_nonempty i)).ne_zero
  obtain ⟨u,hu⟩ := numeratorDetFactor_dvd_commonNumeratorMatrix β δ σ hc hβi
  have hdet := commonNumeratorMatrix_det_ne_zero β δ σ hc hσ hβ
  have hD := numeratorDetFactor_ne_zero (F := F) δ σ
  have hu0 : u ≠ 0 := by
    intro hz
    apply hdet
    rw [hu,hz,mul_zero]
  have hdegree := congrArg MvPolynomial.totalDegree hu
  rw [(commonNumeratorMatrix_det_homogeneous_degree β δ σ hc).totalDegree hdet,
    totalDegree_mul_of_isDomain hD hu0,
    (numeratorDetFactor_homogeneous δ σ).totalDegree hD] at hdegree
  have huzero : u.totalDegree = 0 := by omega
  have huC := totalDegree_eq_zero_iff_eq_C.mp huzero
  refine ⟨u.coeff 0, ?_, ?_⟩
  · intro hzero
    apply hu0
    rw [huC,hzero,map_zero]
  · rw [hu]
    exact (congrArg (fun x => numeratorDetFactor δ σ * x) huC).trans (mul_comm _ _)

end PaperVerification.Fermion.Newton
