module
public import VolumeVerification.CircleFactorization
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
@[expose] public section
set_option autoImplicit false

/-!
# Inertia and strict perturbations of positive hollow rank-three matrices

Inertia is stated using Mathlib's maximal dimensions of positive and negative
definite subspaces.  Sylvester's law of inertia in Mathlib identifies these
dimensions with the usual signs in a diagonalization.
-/
namespace VolumeVerification.MatrixInertia
open scoped BigOperators Matrix
open QuadraticMap

section General
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem one_le_sigPos_of_pos (Q : QuadraticForm ℝ E)
    {v : E} (hv : 0 < Q v) : 1 ≤ sigPos Q := by
  have hv0 : v ≠ 0 := by
    intro h
    simpa [h] using hv
  have hline : (Q.restrict (ℝ ∙ v)).PosDef := by
    intro x hx
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp x.property
    have hr0 : r ≠ 0 := by
      intro h
      apply hx
      apply Subtype.ext
      simpa [h] using hr.symm
    change 0 < Q x.val
    rw [← hr, QuadraticMap.map_smul]
    exact mul_pos (mul_self_pos.mpr hr0) hv
  have hb := le_sigPos_of_posDef Q hline
  rwa [finrank_span_singleton hv0] at hb

theorem sigPos_eq_one_of_nonpos_kernel (Q : QuadraticForm ℝ E)
    (l : E →ₗ[ℝ] ℝ) (hnonpos : ∀ x ∈ l.ker, Q x ≤ 0)
    (hpositive : ∃ x, 0 < Q x) : sigPos Q = 1 := by
  have hu := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := Q) (V := l.ker) hnonpos
  have hr := l.finrank_range_add_finrank_ker
  have hdim : Module.finrank ℝ l.range ≤ 1 := by
    simpa using l.range.finrank_le
  obtain ⟨x,hx⟩ := hpositive
  have hl := one_le_sigPos_of_pos Q hx
  omega

theorem strict_signature_of_negative_kernel (Q : QuadraticForm ℝ E)
    (l : E →ₗ[ℝ] ℝ) (hnegative : ∀ x ∈ l.ker, x ≠ 0 → Q x < 0)
    (hpositive : ∃ x, 0 < Q x) :
    sigPos Q = 1 ∧
      sigNeg Q = Module.finrank ℝ E - 1 ∧
      Module.finrank ℝ Q.radical = 0 := by
  have hp : sigPos Q = 1 := sigPos_eq_one_of_nonpos_kernel Q l
    (by
      intro x hx
      by_cases hzero : x = 0
      · simp [hzero]
      · exact (hnegative x hx hzero).le) hpositive
  have hneg : ((-Q).restrict l.ker).PosDef := by
    intro x hx
    have hx0 : x.val ≠ 0 := by simpa using hx
    change 0 < -Q x.val
    exact neg_pos.mpr (hnegative x.val x.property hx0)
  have hn := le_sigNeg_of_negDef Q hneg
  have hd := l.finrank_range_add_finrank_ker
  have hr : Module.finrank ℝ l.range ≤ 1 := by
    simpa using l.range.finrank_le
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  omega
end General

section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def dotLinear (a : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun x => ∑ i, a i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp [Finset.mul_sum, mul_assoc, mul_left_comm]

theorem quadratic_apply (P : Matrix ι ι ℝ) (u : ι → ℝ) :
    P.toQuadraticForm' u = ∑ i, ∑ j, u i * u j * P i j := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem bilinear_symmetric (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (u v : ι → ℝ) :
    Matrix.toLinearMap₂' ℝ P u v = Matrix.toLinearMap₂' ℝ P v u := by
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hsym i j]
  ring

theorem radical_eq_kernel (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) :
    P.toQuadraticForm'.radical = P.mulVecLin.ker := by
  have ha : QuadraticMap.associated P.toQuadraticForm' =
      Matrix.toLinearMap₂' ℝ P :=
    QuadraticMap.associated_left_inverse ℝ (bilinear_symmetric P hsym)
  rw [QuadraticMap.radical_eq_ker_associated, ha]
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    ext i
    have hi := LinearMap.congr_fun hx (Pi.single i 1)
    rw [bilinear_symmetric P hsym] at hi
    simpa [Matrix.toLinearMap₂'_apply'] using hi
  · intro hx
    apply LinearMap.ext
    intro y
    change Matrix.toLinearMap₂' ℝ P x y = 0
    rw [bilinear_symmetric P hsym, Matrix.toLinearMap₂'_apply']
    change y ⬝ᵥ (P.mulVecLin x) = 0
    rw [hx]
    simp

theorem rank_add_radical (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) :
    P.rank + Module.finrank ℝ P.toQuadraticForm'.radical = Fintype.card ι := by
  rw [radical_eq_kernel P hsym]
  simpa [Matrix.rank] using P.mulVecLin.finrank_range_add_finrank_ker

private theorem double_sum_product (a b u v : ι → ℝ) :
    (∑ i, ∑ j, u i * v j * (a i*b j)) = dotLinear a u * dotLinear b v := by
  simp only [dotLinear, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_lorentz (P : Matrix ι ι ℝ) (a b c : ι → ℝ)
    (hP : ∀ i j, P i j = a i*a j - b i*b j - c i*c j) (u : ι → ℝ) :
    P.toQuadraticForm' u =
      (dotLinear a u)^2 - (dotLinear b u)^2 - (dotLinear c u)^2 := by
  rw [quadratic_apply]
  simp_rw [hP, mul_sub, Finset.sum_sub_distrib]
  rw [double_sum_product, double_sum_product, double_sum_product]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem quadratic_pair (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0) (i j : ι) :
    P.toQuadraticForm' (Pi.single i 1 + Pi.single j 1) = 2 * P i j := by
  have hsingle (k l : ι) :
      Matrix.toLinearMap₂' ℝ P (Pi.single k (1 : ℝ)) (Pi.single l (1 : ℝ)) = P k l := by
    simp only [Matrix.toLinearMap₂'_apply', single_dotProduct,
      Matrix.mulVec_single_one, Matrix.col_apply, one_mul]
  have hsum : (P i i + P j i) + (P i j + P j j) = 2 * P i j := by
    rw [hdiag i, hdiag j, hsym j i]
    ring
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    map_add, LinearMap.add_apply]
  exact (congrArg₂ (fun x y : ℝ => x + y)
    (congrArg₂ (fun x y : ℝ => x + y) (hsingle i i) (hsingle j i))
    (congrArg₂ (fun x y : ℝ => x + y) (hsingle i j) (hsingle j j))).trans hsum

/-- The inertia assertion in Lemma 2.1, without replacing matrix rank by a hypothesis
on an unverified factorization. -/
theorem positive_hollow_rank_three_signature (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) (hrank : P.rank = 3)
    (i₀ i₁ i₂ : ι) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) :
    sigPos P.toQuadraticForm' = 1 ∧ sigNeg P.toQuadraticForm' = 2 ∧
      Module.finrank ℝ P.toQuadraticForm'.radical = Fintype.card ι - 3 := by
  obtain ⟨a,b,c,ha,hnull,hP⟩ :=
    CircleFactorization.exists_lorentz_factorization P hsym hdiag hpos
      hrank.le i₀ i₁ i₂ h01 h02 h12
  have hp : sigPos P.toQuadraticForm' = 1 :=
    sigPos_eq_one_of_nonpos_kernel _ (dotLinear a)
      (by
        intro u hu
        rw [LinearMap.mem_ker] at hu
        rw [quadratic_lorentz P a b c hP, hu]
        nlinarith [sq_nonneg (dotLinear b u), sq_nonneg (dotLinear c u)])
      ⟨Pi.single i₀ 1 + Pi.single i₁ 1, by
        rw [quadratic_pair P hsym hdiag]
        exact mul_pos (by norm_num) (hpos _ _ h01)⟩
  have hs := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := P.toQuadraticForm')
  have hr := rank_add_radical P hsym
  simp only [Module.finrank_fintype_fun_eq_card] at hs
  rw [hrank] at hr
  omega

/-- A hollow perturbation preserving all positive off-diagonal entries. -/
def strictPerturb (P : Matrix ι ι ℝ) (a : ι → ℝ) (ε : ℝ) : Matrix ι ι ℝ :=
  fun i j => P i j + ε * (a i*a j - if i = j then (a i)^2 else 0)

theorem strictPerturb_symmetric (P : Matrix ι ι ℝ) (a : ι → ℝ) (ε : ℝ)
    (hsym : ∀ i j, P i j = P j i) :
    ∀ i j, strictPerturb P a ε i j = strictPerturb P a ε j i := by
  intro i j
  by_cases h : i = j
  · subst j; rfl
  · simp [strictPerturb, h, Ne.symm h, hsym i j, mul_comm]

theorem strictPerturb_hollow (P : Matrix ι ι ℝ) (a : ι → ℝ) (ε : ℝ)
    (hdiag : ∀ i, P i i = 0) :
    ∀ i, strictPerturb P a ε i i = 0 := by
  intro i
  simp [strictPerturb, hdiag, pow_two]

theorem strictPerturb_positive (P : Matrix ι ι ℝ) (a : ι → ℝ) (ε : ℝ)
    (ha : ∀ i, 0 < a i) (hε : 0 ≤ ε)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) :
    ∀ i j, i ≠ j → 0 < strictPerturb P a ε i j := by
  intro i j hij
  simp only [strictPerturb, if_neg hij, sub_zero]
  exact add_pos_of_pos_of_nonneg (hpos i j hij)
    (mul_nonneg hε (mul_pos (ha i) (ha j)).le)

theorem strictPerturb_quadratic (P : Matrix ι ι ℝ) (a b c : ι → ℝ)
    (hP : ∀ i j, P i j = a i*a j - b i*b j - c i*c j)
    (ε : ℝ) (u : ι → ℝ) :
    (strictPerturb P a ε).toQuadraticForm' u =
      (1+ε)*(dotLinear a u)^2 - (dotLinear b u)^2 - (dotLinear c u)^2 -
        ε * ∑ i, (a i)^2*(u i)^2 := by
  have hdiag :
      (∑ i, ∑ j, u i * u j * (if i = j then (a i)^2 else 0)) =
        ∑ i, (a i)^2*(u i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring
  have hsplit : (strictPerturb P a ε).toQuadraticForm' u =
      P.toQuadraticForm' u +
        ε * ((dotLinear a u)^2 - ∑ i, (a i)^2*(u i)^2) := by
    simp only [quadratic_apply, strictPerturb]
    simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have he1 :
        (∑ i, ∑ j, u i * u j * (ε * (a i*a j))) =
          ε * (∑ i, ∑ j, u i * u j * (a i*a j)) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have he2 :
        (∑ i, ∑ j, u i * u j * (ε * (if i = j then (a i)^2 else 0))) =
          ε * (∑ i, ∑ j, u i * u j * (if i = j then (a i)^2 else 0)) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he1, he2, double_sum_product, hdiag]
    ring
  rw [hsplit, quadratic_lorentz P a b c hP]
  ring

theorem strictPerturb_negative_kernel (P : Matrix ι ι ℝ) (a b c : ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (hP : ∀ i j, P i j = a i*a j - b i*b j - c i*c j)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ u ∈ (dotLinear a).ker, u ≠ 0 →
      (strictPerturb P a ε).toQuadraticForm' u < 0 := by
  intro u hu hu0
  rw [LinearMap.mem_ker] at hu
  have hsum : 0 < ∑ k, (a k)^2 * (u k)^2 := by
    apply Finset.sum_pos'
    · intro k _
      positivity
    · have hex : ∃ k, u k ≠ 0 := by
        by_contra h
        push_neg at h
        exact hu0 (funext h)
      obtain ⟨k,hk⟩ := hex
      exact ⟨k, Finset.mem_univ k,
        mul_pos (sq_pos_of_pos (ha k)) (sq_pos_of_ne_zero hk)⟩
  rw [strictPerturb_quadratic P a b c hP, hu]
  have hs1 := sq_nonneg (dotLinear b u)
  have hs2 := sq_nonneg (dotLinear c u)
  nlinarith [mul_pos hε hsum]

theorem strictPerturb_signature (P : Matrix ι ι ℝ) (a b c : ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (hP : ∀ i j, P i j = a i*a j - b i*b j - c i*c j)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (i j : ι) (hij : i ≠ j) (ε : ℝ) (hε : 0 < ε) :
    sigPos (strictPerturb P a ε).toQuadraticForm' = 1 ∧
      sigNeg (strictPerturb P a ε).toQuadraticForm' = Fintype.card ι - 1 ∧
      Module.finrank ℝ (strictPerturb P a ε).toQuadraticForm'.radical = 0 := by
  suffices h :
      sigPos (strictPerturb P a ε).toQuadraticForm' = 1 ∧
        sigNeg (strictPerturb P a ε).toQuadraticForm' =
          Module.finrank ℝ (ι → ℝ) - 1 ∧
        Module.finrank ℝ (strictPerturb P a ε).toQuadraticForm'.radical = 0 by
    simpa using h
  apply strict_signature_of_negative_kernel _ (dotLinear a)
  · intro u hu hu0
    rw [LinearMap.mem_ker] at hu
    have hsum : 0 < ∑ k, (a k)^2 * (u k)^2 := by
      apply Finset.sum_pos'
      · intro k _
        positivity
      · have hex : ∃ k, u k ≠ 0 := by
          by_contra h
          push_neg at h
          exact hu0 (funext h)
        obtain ⟨k,hk⟩ := hex
        exact ⟨k, Finset.mem_univ k, mul_pos (sq_pos_of_pos (ha k)) (sq_pos_of_ne_zero hk)⟩
    rw [strictPerturb_quadratic P a b c hP, hu]
    have hs1 := sq_nonneg (dotLinear b u)
    have hs2 := sq_nonneg (dotLinear c u)
    nlinarith [mul_pos hε hsum]
  · refine ⟨Pi.single i 1 + Pi.single j 1, ?_⟩
    rw [quadratic_pair _ (strictPerturb_symmetric P a ε hsym)
      (strictPerturb_hollow P a ε hdiag)]
    exact mul_pos (by norm_num) (strictPerturb_positive P a ε ha hε.le hpos i j hij)

theorem strictPerturb_tendsto (P : Matrix ι ι ℝ) (a : ι → ℝ) :
    Filter.Tendsto (strictPerturb P a) (nhds 0) (nhds P) := by
  have hc : Continuous (strictPerturb P a) := by
    unfold strictPerturb
    fun_prop
  have hzero : strictPerturb P a 0 = P := by
    ext i j
    simp only [strictPerturb, zero_mul, add_zero]
  simpa only [hzero] using hc.tendsto 0

end Matrix
end VolumeVerification.MatrixInertia

