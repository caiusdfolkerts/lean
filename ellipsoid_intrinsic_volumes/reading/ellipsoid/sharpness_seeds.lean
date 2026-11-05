module

public import Ellipsoid.Semiaxes
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

noncomputable section

open Polynomial Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def realMonicRootPolynomial {n : ℕ} (u : Fin n → ℝ) : ℝ[X] :=
  ∏ i, (X - C (u i))

theorem realMonicRootPolynomial_isMonicOfDegree {n : ℕ} (u : Fin n → ℝ) :
    (realMonicRootPolynomial u).IsMonicOfDegree n := by
  refine ⟨?_, monic_prod_X_sub_C u Finset.univ⟩
  simp [realMonicRootPolynomial, natDegree_prod_of_monic, monic_X_sub_C]

theorem realMonicRootPolynomial_eval_root {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    (realMonicRootPolynomial u).eval (u i) = 0 := by
  simp only [realMonicRootPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

theorem integerRootPolynomial_sign_change {n : ℕ} (i : Fin n) :
    (realMonicRootPolynomial (fun j : Fin n => (j.val : ℝ))).eval ((i.val : ℝ) - 1 / 4) *
      (realMonicRootPolynomial (fun j : Fin n => (j.val : ℝ))).eval ((i.val : ℝ) + 1 / 4) < 0 := by
  classical
  simp only [realMonicRootPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, ← Finset.prod_mul_distrib]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (fun j => ((i.val : ℝ) - 1 / 4 - j.val) * (i.val + 1 / 4 - j.val))
      (Finset.mem_univ i)]
  apply mul_neg_of_neg_of_pos
  · ring_nf
    norm_num
  · apply Finset.prod_pos
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hneq : j.val ≠ i.val := fun h => hji (Fin.ext h)
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · have h : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast Nat.succ_le_of_lt hlt
      apply mul_pos <;> linarith
    · have h : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast Nat.succ_le_of_lt hgt
      apply mul_pos_of_neg_of_neg <;> linarith

theorem exists_root_between_of_eval_mul_neg {p : ℝ[X]} {a b : ℝ}
    (hab : a < b) (hp : p.eval a * p.eval b < 0) :
    ∃ x ∈ Ioo a b, p.eval x = 0 := by
  rcases mul_neg_iff.mp hp with h | h
  · exact intermediate_value_Ioo' hab.le p.continuous.continuousOn ⟨h.2, h.1⟩
  · exact intermediate_value_Ioo hab.le p.continuous.continuousOn ⟨h.1, h.2⟩

/-- In every positive degree there are two distinct, completely real-rooted
monic polynomials differing only by a nonzero constant. This establishes the
sharpness seed by explicit disjoint sign-change intervals around integer roots.
It does not assume the openness of the real-rooted locus. -/
theorem exists_constant_perturbation_real_roots {n : ℕ} (hn : 0 < n) :
    ∃ (u v : Fin n → ℝ) (c : ℝ), 0 < c ∧
      u ⟨0, hn⟩ = 0 ∧ (∀ i, v i ≠ 0) ∧
      realMonicRootPolynomial v = realMonicRootPolynomial u - C c := by
  classical
  let u : Fin n → ℝ := fun i => i.val
  let p := realMonicRootPolynomial u
  have heach (i : Fin n) :
      ∀ᶠ c : ℝ in 𝓝 0,
        (p.eval ((i.val : ℝ) - 1 / 4) - c) * (p.eval ((i.val : ℝ) + 1 / 4) - c) < 0 := by
    have hc : ContinuousAt (fun c : ℝ =>
        (p.eval ((i.val : ℝ) - 1 / 4) - c) * (p.eval ((i.val : ℝ) + 1 / 4) - c)) 0 := by fun_prop
    exact hc.eventually (gt_mem_nhds (by
      simpa [p, u] using integerRootPolynomial_sign_change i))
  have hall : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c ∧ ∀ i : Fin n,
      (p.eval ((i.val : ℝ) - 1 / 4) - c) * (p.eval ((i.val : ℝ) + 1 / 4) - c) < 0 := by
    have hpos : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c := self_mem_nhdsWithin
    exact hpos.and ((Filter.eventually_all.mpr heach).filter_mono nhdsWithin_le_nhds)
  obtain ⟨c, hc, hsign⟩ := hall.exists
  have hex (i : Fin n) : ∃ x ∈ Ioo ((i.val : ℝ) - 1 / 4) (i.val + 1 / 4),
      (p - C c).eval x = 0 := by
    apply exists_root_between_of_eval_mul_neg (by linarith)
    simpa only [Polynomial.eval_sub, Polynomial.eval_C] using hsign i
  choose v hv hroot using hex
  have hv_inj : Function.Injective v := by
    intro i j heq
    apply Fin.ext
    by_contra hneq
    rcases lt_or_gt_of_ne hneq with hij | hji
    · have h : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast Nat.succ_le_of_lt hij
      have hi := (hv i).2
      have hj := (hv j).1
      linarith
    · have h : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast Nat.succ_le_of_lt hji
      have hi := (hv i).1
      have hj := (hv j).2
      linarith
  have hq : (p - C c).IsMonicOfDegree n :=
    (realMonicRootPolynomial_isMonicOfDegree u).sub (by simpa using hn)
  have heq : realMonicRootPolynomial v = p - C c := by
    apply sub_eq_zero.mp
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hv_inj
    · intro i
      rw [Polynomial.eval_sub, realMonicRootPolynomial_eval_root, hroot, sub_self]
    · simpa only [Fintype.card_fin] using
        (realMonicRootPolynomial_isMonicOfDegree v).natDegree_sub_lt hn.ne' hq
  refine ⟨u, v, c, hc, by simp [u], ?_, heq⟩
  intro i hi
  have h := hroot i
  rw [hi, Polynomial.eval_sub, Polynomial.eval_C] at h
  have hp0 : p.eval 0 = 0 := by
    simpa only [p, u, Fin.val_mk, Nat.cast_zero] using
      realMonicRootPolynomial_eval_root u ⟨0, hn⟩
  rw [hp0, zero_sub, neg_eq_zero] at h
  exact hc.ne' h

end EllipsoidVerification
