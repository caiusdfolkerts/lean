module

public import Ellipsoid.CoefficientDefinitions
public import tau_ceti.analysis.calculus.parametric_integral
public import tau_ceti.analysis.special_functions.beta
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Constructions.UnitInterval

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

namespace EllipsoidVerification

abbrev CompactUnitInterval := {u : ℝ // u ∈ Icc (0 : ℝ) 1}

theorem integral_compactUnitInterval (f : ℝ → ℝ) :
    (∫ u : CompactUnitInterval, f u) = ∫ u in Icc (0 : ℝ) 1, f u :=
  unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe f

theorem integrable_compactUnitInterval_iff (f : ℝ → ℝ) :
    Integrable (fun u : CompactUnitInterval => f u) ↔ IntegrableOn f (Icc (0 : ℝ) 1) :=
  unitInterval.measurePreserving_coe.integrable_comp_emb unitInterval.measurableEmbedding_coe

def homogeneousCoefficientPolynomial {n : ℕ} (e : Coefficients n) (u : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), e j * u ^ (2 * j.val) * (1 - u) ^ (2 * n - 2 * j.val)

def positiveCoefficientDomain (n : ℕ) : Set (Coefficients n) :=
  {e | ∀ u ∈ Icc (0 : ℝ) 1, 0 < homogeneousCoefficientPolynomial e u}

def coefficientMellinPower {n : ℕ} (e : Coefficients n) (s r : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ (r - 1) * (coefficientPolynomial e t) ^ (-s)

def compactMellinWeight (n : ℕ) (s r u : ℝ) : ℝ :=
  u ^ (r - 1) * (1 - u) ^ (2 * n * s - r - 1)

def compactMellinPower {n : ℕ} (e : Coefficients n) (s r : ℝ) : ℝ :=
  ∫ u : CompactUnitInterval, compactMellinWeight n s r u *
    (homogeneousCoefficientPolynomial e u) ^ (-s)

@[fun_prop] theorem contDiff_homogeneousCoefficientPolynomial {n : ℕ}
    (N : WithTop ℕ∞) :
    ContDiff ℝ N (fun z : Coefficients n × ℝ => homogeneousCoefficientPolynomial z.1 z.2) := by
  unfold homogeneousCoefficientPolynomial
  fun_prop

theorem admissible_mem_positiveCoefficientDomain {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) : e ∈ positiveCoefficientDomain n := by
  intro u hu
  have hterm (j : Fin (n + 1)) :
      0 ≤ e j * u ^ (2 * j.val) * (1 - u) ^ (2 * n - 2 * j.val) := by
    have hej := he.1 j
    have hu0 := hu.1
    have hu1 := sub_nonneg.mpr hu.2
    positivity
  by_cases hu1 : u = 1
  · have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      hterm j) (Finset.mem_univ (Fin.last n))
    have hpos : 0 < e (Fin.last n) * u ^ (2 * (Fin.last n).val) *
        (1 - u) ^ (2 * n - 2 * (Fin.last n).val) := by simpa [hu1] using he.2.2
    exact hpos.trans_le h
  · have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      hterm j) (Finset.mem_univ 0)
    have h1u : 0 < 1 - u := sub_pos.mpr (lt_of_le_of_ne hu.2 hu1)
    have hpos : 0 < e 0 * u ^ (2 * (0 : Fin (n + 1)).val) *
        (1 - u) ^ (2 * n - 2 * (0 : Fin (n + 1)).val) := by
      simpa using mul_pos he.2.1 (pow_pos h1u (2 * n))
    exact hpos.trans_le h

theorem isOpen_positiveCoefficientDomain (n : ℕ) : IsOpen (positiveCoefficientDomain n) := by
  rw [isOpen_iff_forall_mem_open]
  intro e he
  let W : Set (Coefficients n × ℝ) := {z | 0 < homogeneousCoefficientPolynomial z.1 z.2}
  have hW : IsOpen W := isOpen_lt continuous_const
    (contDiff_homogeneousCoefficientPolynomial (n := n) 0).continuous
  obtain ⟨U, V, hU, hV, heU, hIV, hUV⟩ := generalized_tube_lemma
    (t := Icc (0 : ℝ) 1)
    (isCompact_singleton : IsCompact ({e} : Set (Coefficients n))) isCompact_Icc hW
    (by rintro ⟨x, u⟩ ⟨rfl, hu⟩; exact he u hu)
  refine ⟨U, ?_, hU, heU (mem_singleton e)⟩
  intro x hx u hu
  exact hUV (show (x, u) ∈ U ×ˢ V from ⟨hx, hIV hu⟩)

theorem homogeneousCoefficientPolynomial_compactification {n : ℕ}
    (e : Coefficients n) {u : ℝ} (hu : u ≠ 1) :
    homogeneousCoefficientPolynomial e u =
      (1 - u) ^ (2 * n) * coefficientPolynomial e (u / (1 - u)) := by
  unfold homogeneousCoefficientPolynomial coefficientPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hpow : 2 * j.val + (2 * n - 2 * j.val) = 2 * n := by omega
  have hne : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  calc
    _ = (1 - u) ^ (2 * j.val + (2 * n - 2 * j.val)) *
        (e j * (u / (1 - u)) ^ (2 * j.val)) := by
      rw [div_pow, pow_add]
      field_simp [hne] <;> ring
    _ = _ := by rw [hpow]

def positiveCompactification (u : ℝ) : ℝ := u / (1 - u)

theorem positiveCompactification_image : positiveCompactification '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact div_pos hu.1 (sub_pos.mpr hu.2)
  · intro ht
    change 0 < t at ht
    have hd : 0 < 1 + t := by linarith
    refine ⟨t / (1 + t), ⟨div_pos ht hd,
      (div_lt_one hd).2 (by linarith)⟩, ?_⟩
    dsimp [positiveCompactification]
    have hden : 1 - t / (1 + t) = 1 / (1 + t) := by
      field_simp [hd.ne'] <;> ring
    rw [hden]
    field_simp [hd.ne'] <;> ring

theorem positiveCompactification_injOn : Set.InjOn positiveCompactification (Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv
  dsimp [positiveCompactification] at huv
  have h := (div_eq_div_iff (sub_ne_zero.mpr hu.2.ne') (sub_ne_zero.mpr hv.2.ne')).mp huv
  nlinarith

theorem hasDerivAt_positiveCompactification {u : ℝ} (hu : u ≠ 1) :
    HasDerivAt positiveCompactification ((1 - u) ^ (-2 : ℤ)) u := by
  have hne : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  have h := (hasDerivAt_id u).div ((hasDerivAt_id u).const_sub 1) hne
  have hf : positiveCompactification = id / (fun x : ℝ => 1 - id x) := by
    funext x
    rfl
  rw [hf]
  convert h using 1 <;>
    simp only [id_eq, mul_one, one_mul, mul_neg, sub_neg_eq_add,
      sub_add_cancel, zpow_neg, zpow_ofNat, one_div]

theorem compactMellinWeight_integrable {n : ℕ} {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    Integrable (fun u : CompactUnitInterval => compactMellinWeight n s r u) volume := by
  apply (integrable_compactUnitInterval_iff _).2
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  exact TauCeti.integrableOn_rpow_mul_one_sub_rpow_iff.mpr ⟨hr, sub_pos.mpr hrn⟩

theorem contDiffOn_compactMellinPower {n : ℕ} {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    ContDiffOn ℝ ∞ (fun e : Coefficients n => compactMellinPower e s r)
      (positiveCoefficientDomain n) := by
  let W : Set (Coefficients n × ℝ) := {z | 0 < homogeneousCoefficientPolynomial z.1 z.2}
  have hW : IsOpen W := isOpen_lt continuous_const
    (contDiff_homogeneousCoefficientPolynomial (n := n) 0).continuous
  have hF : ContDiffOn ℝ ∞
      (fun z : Coefficients n × ℝ => (homogeneousCoefficientPolynomial z.1 z.2) ^ (-s)) W := by
    apply (contDiff_homogeneousCoefficientPolynomial (n := n) ∞).contDiffOn.rpow_const_of_ne
    intro z hz
    exact hz.ne'
  simpa only [compactMellinPower, smul_eq_mul] using
    TauCeti.contDiffOn_integral_smul_of_contDiffOn
      (compactMellinWeight_integrable hr hrn)
      (continuous_subtype_val : Continuous (fun u : CompactUnitInterval => (u : ℝ))) hW hF
      (isOpen_positiveCoefficientDomain n)
      (fun e he u => he u u.property)

end EllipsoidVerification
