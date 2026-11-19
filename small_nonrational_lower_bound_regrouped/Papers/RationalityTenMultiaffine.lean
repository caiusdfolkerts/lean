module
public import Papers.RationalityTenMultiaffineCore
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section
noncomputable section

namespace Papers.RationalityTen.MultiaffineDensity

open Set MvPolynomial
open scoped BigOperators

def evalRat {ι : Type*} (p : MvPolynomial ι ℚ) (x : ι → ℝ) : ℝ :=
  eval₂ (Rat.castHom ℝ) x p

theorem evalRat_continuous {ι : Type*} (p : MvPolynomial ι ℚ) :
    Continuous (evalRat p) := by
  change Continuous (fun x => eval₂ (Rat.castHom ℝ) x p)
  simp_rw [eval₂_eq_eval_map]
  exact MvPolynomial.continuous_eval (p := MvPolynomial.map (Rat.castHom ℝ) p)

theorem evalRat_rational {ι : Type*} (p : MvPolynomial ι ℚ)
    (x : ι → ℝ) (hx : RationalVector x) : ∃ q : ℚ, (q : ℝ)=evalRat p x := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨a,by simp [evalRat]⟩
  | add p q hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    exact ⟨a+b,by simp only [Rat.cast_add,ha,hb,evalRat,eval₂_add]⟩
  | mul_X p i hp =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hx i
    exact ⟨a*b,by simp only [Rat.cast_mul,ha,hb,evalRat,eval₂_mul,eval₂_X]⟩

theorem product_update_affine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι →₀ ℕ) (i : ι) (hi : s i≤1) (x : ι → ℝ) (t : ℝ) :
    (∏ j, Function.update x i t j ^ s j) =
      (∏ j, Function.update x i 0 j ^ s j) +
      t*((∏ j, Function.update x i 1 j ^ s j) -
         (∏ j, Function.update x i 0 j ^ s j)) := by
  have hprod (a : ℝ) :
      (∏ j, Function.update x i a j ^ s j) =
        (∏ j ∈ Finset.univ.erase i,x j ^ s j) * a ^ s i := by
    rw [←Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    congr 1
    · apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    · simp only [Function.update_self]
  have hcases : s i=0 ∨ s i=1 := by omega
  rcases hcases with hzero | hone
  · simp only [hprod,hzero,pow_zero,mul_one,sub_self,mul_zero,add_zero]
  · simp only [hprod,hone,pow_one,mul_zero,mul_one,zero_add,sub_zero]
    ring

theorem evalRat_affineIn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℚ) (i : ι) (hi : p.degreeOf i≤1) :
    AffineIn (evalRat p) i := by
  intro x t
  simp only [evalRat,axisSlope,eval₂_eq']
  rw [mul_sub,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [product_update_affine s i ((degreeOf_le_iff.mp hi) s hs)]
  ring

/-- Specialize the final coordinate z while keeping all affine coordinates. -/
def specializeParameter {n : ℕ} (p : MvPolynomial (Option (Fin n)) ℚ)
    (z : ℝ) : MvPolynomial (Fin n) ℝ :=
  eval₂ (MvPolynomial.C.comp (Rat.castHom ℝ))
    (Option.elim' (MvPolynomial.C z) MvPolynomial.X) p

theorem specializeParameter_eval {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℚ) (z : ℝ) (x : Fin n → ℝ) :
    eval x (specializeParameter p z) = evalRat p (Option.elim' z x) := by
  unfold specializeParameter
  rw [eval_eval₂]
  apply congrArg₂ (fun f g => eval₂ f g p)
  · ext a
    simp
  · funext i
    cases i <;> simp

/-- Paper Lemma 12, with every affine variable and the parameter retained.
The specialized fiber is explicitly required to be a nonzero polynomial. -/
theorem multiaffine_rational_zeros_dense {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℚ)
    (hdegree : ∀ i : Fin n, p.degreeOf (some i)≤1)
    (x : Option (Fin n) → ℝ)
    (hzero : evalRat p x=0)
    (hfiber : specializeParameter p (x none)≠0) :
    x∈closure {q | RationalVector q ∧ evalRat p q=0} := by
  exact rational_zeros_dense_of_multiaffine_fiber (evalRat p)
    (evalRat_continuous p) (evalRat_rational p)
    (fun i=>evalRat_affineIn p (some i) (hdegree i))
    x hzero (specializeParameter p (x none)) hfiber
    (specializeParameter_eval p (x none))

theorem multiaffine_rational_zeros_in_open {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℚ)
    (hdegree : ∀ i : Fin n, p.degreeOf (some i)≤1)
    (x : Option (Fin n) → ℝ) (hzero : evalRat p x=0)
    (hfiber : specializeParameter p (x none)≠0)
    (U : Set (Option (Fin n) → ℝ)) (hU : IsOpen U) (hxU : x∈U) :
    ∃ q∈U, RationalVector q ∧ evalRat p q=0 := by
  have h := multiaffine_rational_zeros_dense p hdegree x hzero hfiber
  obtain ⟨q,hq,hqU⟩ := mem_closure_iff.mp h U hU hxU
  exact ⟨q,hq,hqU⟩

end Papers.RationalityTen.MultiaffineDensity
