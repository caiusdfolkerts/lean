module

public import VolumePolynomials.GenericVolumePolynomial
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Tactic.FieldSimp

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Normalized mixed volume of actual convex bodies

The definition extracts the squarefree coefficient of the proved volume
polynomial and divides it by the factorial of the number of arguments.
Its geometric use has exactly as many arguments as the ambient dimension.
It is not an abstract functional supplied with assumed mixed-volume laws.
-/

open Set MeasureTheory Module MvPolynomial
open scoped BigOperators Pointwise

namespace VolumePolynomials

def squarefreeExponent (d : ℕ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

@[simp] theorem squarefreeExponent_apply (d : ℕ) (i : Fin d) :
    squarefreeExponent d i = 1 := by simp [squarefreeExponent]

theorem squarefreeExponent_sum (d : ℕ) :
    (squarefreeExponent d).sum (fun _ m => m) = d := by
  first
  | rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp

theorem squarefreeExponent_multinomial (d : ℕ) :
    (squarefreeExponent d).multinomial = d.factorial := by
  first
  | rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), Nat.multinomial]
    simp

theorem squarefreeExponent_mapDomain {d : ℕ} (e : Equiv.Perm (Fin d)) :
    (squarefreeExponent d).mapDomain e = squarefreeExponent d := by
  first
  | ext i
    rw [Finsupp.mapDomain_equiv_apply]
    simp

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def mixedVolume {d : ℕ} (K : Fin d → ConvexBody E) : ℝ :=
  (volumePolynomial μ K).coeff (squarefreeExponent d) / d.factorial

theorem mixedVolume_nonnegative {d : ℕ} (K : Fin d → ConvexBody E) :
    0 ≤ mixedVolume μ K :=
  div_nonneg (volumePolynomial_nonnegative μ K _) (Nat.cast_nonneg _)

theorem continuous_mixedVolume (d : ℕ) : Continuous (mixedVolume μ (d := d)) :=
  (continuous_volumePolynomial_coeff μ (squarefreeExponent d)).div_const _

theorem mixedVolume_translate {d : ℕ} (K : Fin d → ConvexBody E) (v : Fin d → E) :
    mixedVolume μ (fun i => translateBody (v i) (K i)) = mixedVolume μ K := by
  first
  | simp only [mixedVolume, volumePolynomial_translate]

theorem volumePolynomial_reindex {n : ℕ} (K : Fin n → ConvexBody E)
    (e : Equiv.Perm (Fin n)) :
    volumePolynomial μ (fun i => K (e.symm i)) =
      MvPolynomial.rename e (volumePolynomial μ K) := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [MvPolynomial.eval_rename, volumePolynomial_eval μ K (t ∘ e)
      (fun i => ht (e i))]
    congr 2
    exact Fintype.sum_equiv e _ _ (fun i => by simp)

theorem mixedVolume_reindex {d : ℕ} (K : Fin d → ConvexBody E)
    (e : Equiv.Perm (Fin d)) : mixedVolume μ (fun i => K (e i)) = mixedVolume μ K := by
  first
  | have h := volumePolynomial_reindex μ K e.symm
    simp only [Equiv.symm_symm] at h
    change (volumePolynomial μ (fun i => K (e i))).coeff _ / _ = _
    rw [h]
    apply congrArg (fun r : ℝ => r / (d.factorial : ℝ))
    simpa only [squarefreeExponent_mapDomain] using
      MvPolynomial.coeff_rename_mapDomain e.symm e.symm.injective
        (volumePolynomial μ K) (squarefreeExponent d)

theorem sum_smul_one_body {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (r : ι → ℝ) (K : ConvexBody E) (hr : ∀ i ∈ s, 0 ≤ r i) :
    (∑ i ∈ s, r i • K) = (∑ i ∈ s, r i) • K := by
  first
  | induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, body_zero_smul]
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          ih (fun j hj => hr j (Finset.mem_insert_of_mem hj)),
          body_add_smul K (hr i (Finset.mem_insert_self i s))
            (Finset.sum_nonneg (fun j hj => hr j (Finset.mem_insert_of_mem hj)))]

theorem haar_real_smul_body (K : ConvexBody E) {r : ℝ} (hr : 0 ≤ r) :
    μ.real ((r • K : ConvexBody E) : Set E) = r ^ finrank ℝ E * μ.real (K : Set E) := by
  first
  | simp only [ConvexBody.coe_smul, measureReal_def,
      Measure.addHaar_smul_of_nonneg μ hr (K : Set E), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr _)]

theorem volumePolynomial_diagonal {n : ℕ} (K : ConvexBody E) :
    volumePolynomial μ (fun _ : Fin n => K) =
      C (μ.real (K : Set E)) * (∑ i : Fin n, X i) ^ finrank ℝ E := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [sum_smul_one_body Finset.univ t K (fun i _ => ht i),
      haar_real_smul_body μ K (Finset.sum_nonneg (fun i _ => ht i))]
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_pow,
      MvPolynomial.eval_sum, MvPolynomial.eval_X]
    exact mul_comm _ _

/-- The normalization agrees with ordinary volume on the diagonal, in the
ambient dimension, including dimension zero. -/
theorem mixedVolume_diagonal {d : ℕ} (hdim : finrank ℝ E = d) (K : ConvexBody E) :
    mixedVolume μ (fun _ : Fin d => K) = μ.real (K : Set E) := by
  first
  | rw [mixedVolume, volumePolynomial_diagonal, hdim, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_sum_X_pow_of_fintype, squarefreeExponent_sum,
      if_pos rfl, squarefreeExponent_multinomial]
    exact mul_div_cancel_right₀ _ (by exact_mod_cast (Nat.factorial_ne_zero d))

/-- Simultaneously scaling the bodies has exactly the ambient volume degree. -/
theorem volumePolynomial_common_smul {n : ℕ} (K : Fin n → ConvexBody E)
    {r : ℝ} (hr : 0 ≤ r) :
    volumePolynomial μ (fun i => r • K i) =
      C (r ^ finrank ℝ E) * volumePolynomial μ K := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, volumePolynomial_eval μ K t ht]
    have hsum : (∑ i, t i • (r • K i)) = r • (∑ i, t i • K i) := by
      first
      | rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul, smul_smul, mul_comm]
    rw [hsum, haar_real_smul_body μ _ hr]

theorem mixedVolume_common_smul {d : ℕ} (K : Fin d → ConvexBody E)
    {r : ℝ} (hr : 0 ≤ r) :
    mixedVolume μ (fun i => r • K i) = r ^ finrank ℝ E * mixedVolume μ K := by
  first
  | rw [mixedVolume, volumePolynomial_common_smul μ K hr, MvPolynomial.coeff_C_mul,
      mixedVolume]
    ring

end Generic
end VolumePolynomials
