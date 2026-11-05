module

public import PaperVerification.PowerConjugation
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Restricting original power quotients to the first variables

The restriction sets every omitted variable to zero. Positive-index original
power operators commute with this map, including at singular parameters. The
literal Artin span therefore descends from `n` variables to any first `r`
variables. No invertible diagonal conjugation is used in this argument.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K ι τ : Type*} [Field K]

theorem euler_monomial (i : ι) (a : ι →₀ ℕ) (r : K) :
    euler i (monomial a r) = (a i : K) • monomial a r := by
  rw [euler_apply, X_mul_pderiv_monomial]
  simp only [Nat.cast_smul_eq_nsmul]

theorem coeff_euler (i : ι) (a : ι →₀ ℕ) (p : MvPolynomial ι K) :
    (euler i p).coeff a = (a i : K) * p.coeff a := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial b r =>
    rw [euler_monomial]
    by_cases h : a = b
    · subst b
      simp only [coeff_smul, coeff_monomial, ite_true, smul_eq_mul]
    · simp only [coeff_smul, coeff_monomial, ite_eq_right h,
        ite_eq_right (Ne.symm h), smul_zero, mul_zero]
  | add p q hp hq => simp only [map_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem killCompl_euler (f : ι ↪ τ) (i : ι) (p : MvPolynomial τ K) :
    killCompl f.injective (euler (f i) p) =
      euler i (killCompl f.injective p) := by
  ext a
  rw [coeff_killCompl, coeff_euler, coeff_euler, coeff_killCompl,
    Finsupp.mapDomain_apply_of_injective f.injective]

@[simp] theorem killCompl_X_image (f : ι ↪ τ) (i : ι) :
    killCompl (R := K) f.injective (X (f i)) = X i := by
  simpa only [rename_X] using killCompl_rename_app f.injective (X i : MvPolynomial ι K)

theorem killCompl_X_outside (f : ι ↪ τ) (j : τ) (hj : j ∉ Set.range f) :
    killCompl (R := K) f.injective (X j) = 0 := by
  simp only [killCompl, aeval_X, dif_neg hj]

variable [Fintype ι] [Fintype τ]

/-- All positive operator indices, without a parameter restriction. -/
theorem killCompl_original (f : ι ↪ τ) (c : τ → K) (α : K)
    (k : ℕ) (hk : 0 < k) (p : MvPolynomial τ K) :
    killCompl f.injective (original c α k p) =
      original (c ∘ f) α k (killCompl f.injective p) := by
  classical
  let g : τ → MvPolynomial ι K := fun j =>
    killCompl f.injective (X j ^ k * (c j • p + α • euler j p))
  have hzero (j : τ) (hj : j ∉ Set.range f) : g j = 0 := by
    simp only [g, map_mul, map_pow, killCompl_X_outside f j hj,
      zero_pow (Nat.ne_of_gt hk), zero_mul]
  have hsum : (∑ j : τ, g j) = ∑ i : ι, g (f i) := by
    rw [← Finset.sum_map]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hn
    apply hzero j
    rintro ⟨i, rfl⟩
    exact hn (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  change killCompl f.injective ((∑ j : τ,
      (LinearMap.mulLeft K (X j ^ k)).comp
        (c j • LinearMap.id + α • euler j)) p) = _
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply, LinearMap.mulLeft_apply, map_sum]
  change (∑ j : τ, g j) = _
  rw [hsum]
  simp only [g, original, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.mulLeft_apply, map_mul, map_pow, map_add, map_smul,
    killCompl_X_image, killCompl_euler, Function.comp_apply, mul_add, mul_smul_comm]

theorem killCompl_mem_originalTailHit (f : ι ↪ τ) (c : τ → K) (α : K)
    (m : ℕ) (hm : 0 < m) {p : MvPolynomial τ K}
    (hp : p ∈ originalTailHit c α m) :
    killCompl f.injective p ∈ originalTailHit (c ∘ f) α m := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨k, hk, q, rfl⟩ := hp
    rw [killCompl_original f c α k (hm.trans_le hk)]
    exact Submodule.subset_span ⟨k, hk, _, rfl⟩
  | zero => simpa only [map_zero] using (originalTailHit (c ∘ f) α m).zero_mem
  | add p q _ _ hp hq =>
    simpa only [map_add] using (originalTailHit (c ∘ f) α m).add_mem hp hq
  | smul a p _ hp =>
    simpa only [map_smul] using (originalTailHit (c ∘ f) α m).smul_mem a hp

def firstVariables {r n : ℕ} (hrn : r ≤ n) : Fin r ↪ Fin n :=
  ⟨Fin.castLE hrn, Fin.castLE_injective hrn⟩

theorem killCompl_mem_artinSpan {r n : ℕ} (hrn : r ≤ n) (m : ℕ)
    {p : MvPolynomial (Fin n) K} (hp : p ∈ artinSpan K n m) :
    killCompl (firstVariables hrn).injective p ∈ artinSpan K r m := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a, ha, rfl⟩ := hp
    rw [killCompl_monomial]
    split_ifs with hs
    · apply monomial_mem_artinSpan
      intro i
      simp only [Finsupp.comapDomain_apply]
      exact ha (firstVariables hrn i)
    · exact (artinSpan K r m).zero_mem
  | zero => simpa only [map_zero] using (artinSpan K r m).zero_mem
  | add p q _ _ hp hq => simpa only [map_add] using (artinSpan K r m).add_mem hp hq
  | smul a p _ hp => simpa only [map_smul] using (artinSpan K r m).smul_mem a hp

/-- A spanning assertion descends to any initial set of variables. -/
theorem original_artin_span_restrict {r n : ℕ} (hrn : r ≤ n)
    (α : K) (m : ℕ) (hm : 0 < m)
    (hspan : (artinSpan K n m).map
      (originalTailHit (fun _ => (1 : K)) α m).mkQ = ⊤) :
    (artinSpan K r m).map
      (originalTailHit (fun _ => (1 : K)) α m).mkQ = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨p, rfl⟩ := (originalTailHit (fun _ : Fin r => (1 : K)) α m).mkQ_surjective z
  let f := firstVariables hrn
  have hp : (originalTailHit (fun _ : Fin n => (1 : K)) α m).mkQ (rename f p) ∈
      (artinSpan K n m).map (originalTailHit (fun _ => (1 : K)) α m).mkQ := by
    rw [hspan]
    trivial
  obtain ⟨q, hq, hqp⟩ := hp
  refine ⟨killCompl f.injective q, killCompl_mem_artinSpan hrn m hq, ?_⟩
  have hdiff : q-rename f p ∈ originalTailHit (fun _ : Fin n => (1 : K)) α m :=
    (Submodule.Quotient.eq _).mp hqp
  have hr := killCompl_mem_originalTailHit f (fun _ => (1 : K)) α m hm hdiff
  simp only [map_sub, killCompl_rename_app, Function.comp_def] at hr
  exact (Submodule.Quotient.eq _).mpr hr

end PaperVerification.PowerOperators
