module

public import VolumePolynomials.MainQuadraticCharacterization
public import Mathlib.Tactic.FunProp

@[expose] public section
set_option autoImplicit false

/-!
# Finite rational certificates for computable inputs

An input is supplied by rational approximations with a certified error bound.
The finite certificate predicate uses rational arithmetic only. Its soundness
is an interval bound proved for every real vector, and completeness follows
from the strict inequality furnished by the exact volume-locus criterion.
The executable enumeration never tests equality of a real coefficient sum.
-/

open Filter
open scoped BigOperators Topology

namespace VolumePolynomials.RationalCertificates

variable {ι : Type*} [Fintype ι]

def quadraticValue (M : ι → ι → ℚ) (q : ι → ℚ) : ℚ :=
  ∑ i, ∑ j, M i j * q i * q j

def realQuadratic (M : ι → ι → ℚ) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j : ℝ) * c i * c j

def quadraticError (M : ι → ι → ℚ) (q : ι → ℚ) (δ : ℚ) : ℚ :=
  ∑ i, ∑ j, |M i j| * δ * (|q i| + |q j| + δ)

theorem product_error {x y a b δ : ℝ} (hδ : 0 ≤ δ)
    (hx : |x - a| ≤ δ) (hy : |y - b| ≤ δ) :
    |x * y - a * b| ≤ δ * (|a| + |b| + δ) := by
  first
  | have hid : x * y - a * b = (x - a) * (y - b) + a * (y - b) + b * (x - a) := by ring
    rw [hid]
    calc
      _ ≤ |(x - a) * (y - b)| + |a * (y - b)| + |b * (x - a)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |x - a| * |y - b| + |a| * |y - b| + |b| * |x - a| := by simp only [abs_mul]
      _ ≤ δ * δ + |a| * δ + |b| * δ := by gcongr
      _ = δ * (|a| + |b| + δ) := by ring

theorem quadratic_interval_bound (M : ι → ι → ℚ) (c : ι → ℝ) (q : ι → ℚ)
    (δ : ℚ) (hδ : 0 ≤ δ) (hq : ∀ i, |c i - (q i : ℝ)| ≤ (δ : ℝ)) :
    |realQuadratic M c - (quadraticValue M q : ℝ)| ≤ (quadraticError M q δ : ℝ) := by
  first
  | simp only [realQuadratic, quadraticValue, quadraticError, Rat.cast_sum, Rat.cast_mul,
      Rat.cast_add, Rat.cast_abs, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [show (M i j : ℝ) * c i * c j - (M i j : ℝ) * (q i : ℝ) * (q j : ℝ) =
      (M i j : ℝ) * (c i * c j - (q i : ℝ) * (q j : ℝ)) by ring, abs_mul]
    have hp := product_error (by exact_mod_cast hδ) (hq i) (hq j)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (abs_nonneg (M i j : ℝ))

def precision (h : ℕ) : ℚ := 1 / ((h : ℚ) + 1)

theorem precision_pos (h : ℕ) : 0 < precision h := by unfold precision; positivity

def IsName (c : ι → ℝ) (a : ℕ → ι → ℚ) : Prop :=
  ∀ h i, |c i - (a h i : ℝ)| ≤ (precision h : ℝ)

theorem precision_tendsto : Tendsto (fun h => (precision h : ℝ)) atTop (𝓝 0) := by
  first
  | simpa only [precision, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem name_tendsto {c : ι → ℝ} {a : ℕ → ι → ℚ} (ha : IsName c a) :
    Tendsto (fun h i => (a h i : ℝ)) atTop (𝓝 c) := by
  first
  | apply tendsto_pi_nhds.mpr
    intro i
    apply (tendsto_iff_dist_tendsto_zero).mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ precision_tendsto
    intro h
    simpa only [Real.dist_eq, abs_sub_comm] using ha h i

theorem quadraticUpper_tendsto (M : ι → ι → ℚ)
    {c : ι → ℝ} {a : ℕ → ι → ℚ} (ha : IsName c a) :
    Tendsto (fun h => ((quadraticValue M (a h) + quadraticError M (a h) (precision h) : ℚ) : ℝ))
      atTop (𝓝 (realQuadratic M c)) := by
  first
  | have hq : Continuous (realQuadratic M) := by unfold realQuadratic; fun_prop
    have he : Continuous (fun z : (ι → ℝ) × ℝ =>
        ∑ i, ∑ j, |(M i j : ℝ)| * z.2 * (|z.1 i| + |z.1 j| + z.2)) := by fun_prop
    have hv := (hq.tendsto c).comp (name_tendsto ha)
    have he' := (he.tendsto (c, 0)).comp ((name_tendsto ha).prodMk_nhds precision_tendsto)
    have h := hv.add he'
    simpa [quadraticValue, quadraticError, realQuadratic] using h

/-- A certificate specifies a negative coordinate or a violated enumerated
quadratic, together with one finite rational input precision. -/
abbrev Certificate (ι : Type*) := (ι × ℕ) ⊕ (ℕ × ℕ)

def Valid (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ) : Certificate ι → Prop
  | .inl (i, h) => a h i + precision h < 0
  | .inr (k, h) => quadraticValue (matrices k) (a h) +
      quadraticError (matrices k) (a h) (precision h) < 0

instance validDecidable (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ)
    (cert : Certificate ι) : Decidable (Valid matrices a cert) := by
  first
  | cases cert <;> unfold Valid <;> infer_instance

theorem valid_sound (matrices : ℕ → ι → ι → ℚ) {c : ι → ℝ} {a : ℕ → ι → ℚ}
    (ha : IsName c a) (cert : Certificate ι) (hcert : Valid matrices a cert) :
    (∃ i, c i < 0) ∨ ∃ k, realQuadratic (matrices k) c < 0 := by
  first
  | cases cert with
    | inl z =>
        obtain ⟨i, h⟩ := z
        apply Or.inl
        refine ⟨i, ?_⟩
        have hq := (abs_le.mp (ha h i)).2
        have hv : (a h i : ℝ) + (precision h : ℝ) < 0 := by exact_mod_cast hcert
        linarith
    | inr z =>
        obtain ⟨k, h⟩ := z
        apply Or.inr
        refine ⟨k, ?_⟩
        have hb := (abs_le.mp (quadratic_interval_bound (matrices k) c (a h) (precision h)
          (precision_pos h).le (ha h))).2
        have hv : (quadraticValue (matrices k) (a h) : ℝ) +
            (quadraticError (matrices k) (a h) (precision h) : ℝ) < 0 := by exact_mod_cast hcert
        linarith

theorem exists_valid_of_strict (matrices : ℕ → ι → ι → ℚ)
    {c : ι → ℝ} {a : ℕ → ι → ℚ} (ha : IsName c a)
    (hbad : (∃ i, c i < 0) ∨ ∃ k, realQuadratic (matrices k) c < 0) :
    ∃ cert, Valid matrices a cert := by
  first
  | rcases hbad with ⟨i, hi⟩ | ⟨k, hk⟩
    · have hlim := ((continuous_apply i).tendsto c |>.comp (name_tendsto ha)).add precision_tendsto
      rw [add_zero] at hlim
      obtain ⟨h, hh⟩ := (hlim.eventually (gt_mem_nhds hi)).exists
      refine ⟨.inl (i, h), ?_⟩
      change a h i + precision h < 0
      change (a h i : ℝ) + (precision h : ℝ) < 0 at hh
      exact_mod_cast hh
    · obtain ⟨h, hh⟩ := ((quadraticUpper_tendsto (matrices k) ha).eventually (gt_mem_nhds hk)).exists
      refine ⟨.inr (k, h), ?_⟩
      change quadraticValue (matrices k) (a h) +
        quadraticError (matrices k) (a h) (precision h) < 0
      exact_mod_cast hh

/-- Exhaustive executable enumeration of all valid finite rational certificates. -/
def enumerate [Encodable ι] (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ)
    (j : ℕ) : Option (Certificate ι) :=
  match Encodable.decode j with
  | none => none
  | some cert => if Valid matrices a cert then some cert else none

theorem enumerate_sound [Encodable ι] (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ)
    {j : ℕ} {cert : Certificate ι} (h : enumerate matrices a j = some cert) :
    Valid matrices a cert := by
  first
  | unfold enumerate at h
    split at h
    · contradiction
    · split at h
      · cases h
        assumption
      · contradiction

theorem enumerate_complete [Encodable ι] (matrices : ℕ → ι → ι → ℚ) (a : ℕ → ι → ℚ)
    {cert : Certificate ι} (h : Valid matrices a cert) :
    enumerate matrices a (Encodable.encode cert) = some cert := by
  first
  | simp [enumerate, Encodable.encodek, h]

end RationalCertificates

namespace Main

/-- Every nonrealizable vector has a strict violated inequality, without
assuming positivity or nonzero total coefficient sum. -/
theorem nonrealizable_strict_inequality (n d : ℕ) (hd : 0 < d) (c : Coefficients n d)
    (hc : c ∉ VolumeLocus n d) :
    (∃ α, c α < 0) ∨ ∃ k, RationalCertificates.realQuadratic (volumeInequalityMatrix n d k) c < 0 := by
  first
  | have h := Iff.mp (not_congr (volumeLocus_iff_countableQuadratics n d hd c)) hc
    by_cases hn : ∀ α, 0 ≤ c α
    · right
      push_neg at h
      exact h hn
    · left
      simpa only [not_forall, not_le] using hn

/-- Rational input names permit a finite rational certificate exactly when
the actual real coefficient vector is nonrealizable. -/
theorem finite_rational_certificate (n d : ℕ) (hd : 0 < d) (c : Coefficients n d)
    (a : ℕ → MultiIndex n d → ℚ) (ha : RationalCertificates.IsName c a) :
    c ∉ VolumeLocus n d ↔
      ∃ cert, RationalCertificates.Valid (volumeInequalityMatrix n d) a cert := by
  first
  | constructor
    · intro hc
      exact RationalCertificates.exists_valid_of_strict _ ha
        (nonrealizable_strict_inequality n d hd c hc)
    · rintro ⟨cert, hcert⟩ hc
      have hgood := Iff.mp (volumeLocus_iff_countableQuadratics n d hd c) hc
      rcases RationalCertificates.valid_sound _ ha cert hcert with ⟨α, hα⟩ | ⟨k, hk⟩
      · exact (not_lt_of_ge (hgood.1 α)) hα
      · exact (not_lt_of_ge (hgood.2 k)) hk

/-- Dovetailing the finite codes rejects every nonrealizable named input at
some finite index and accepts no false certificate. -/
theorem rational_rejection_terminates (n d : ℕ) (hd : 0 < d) (c : Coefficients n d)
    (a : ℕ → MultiIndex n d → ℚ) (ha : RationalCertificates.IsName c a) :
    c ∉ VolumeLocus n d ↔ ∃ j cert,
      RationalCertificates.enumerate (volumeInequalityMatrix n d) a j = some cert := by
  first
  | rw [finite_rational_certificate n d hd c a ha]
    constructor
    · rintro ⟨cert, hc⟩
      exact ⟨Encodable.encode cert, cert, RationalCertificates.enumerate_complete _ _ hc⟩
    · rintro ⟨j, cert, hc⟩
      exact ⟨cert, RationalCertificates.enumerate_sound _ _ hc⟩

end Main
end VolumePolynomials
