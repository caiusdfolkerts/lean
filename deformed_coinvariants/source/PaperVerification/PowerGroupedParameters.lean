module

public import PaperVerification.PowerGenericParameters
public import PaperVerification.PowerStabilizerCharacteristic

/-!
# Generic coefficients compatible with every coefficient stabilizer

There is one independent variable for each actual coefficient value. Thus any
permutation preserving the original tuple preserves the entire family. A
nonempty sum of generic coefficients is nonzero in every characteristic:
evaluating the variable attached to `a` at `a + λ*m` gives exactly the
nonresonance scalar for `s = m*|I|`. No splitting-field or orbit-size hypothesis
is imposed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

abbrev CoefficientClass (c : Fin n → K) := Set.range c

instance coefficientClass_finite (c : Fin n → K) : Finite (CoefficientClass c) :=
  (Set.finite_range c).to_subtype

noncomputable instance coefficientClass_fintype (c : Fin n → K) :
    Fintype (CoefficientClass c) := Fintype.ofFinite _

def coefficientClassOf (c : Fin n → K) (i : Fin n) : CoefficientClass c :=
  ⟨c i, ⟨i, rfl⟩⟩

abbrev GroupedCoefficientRing (c : Fin n → K) := MvPolynomial (CoefficientClass c) K

abbrev GroupedCoefficientField (c : Fin n → K) := FractionRing (GroupedCoefficientRing c)

def groupedCoefficient (c : Fin n → K) (i : Fin n) : GroupedCoefficientField c :=
  algebraMap (GroupedCoefficientRing c) (GroupedCoefficientField c) (X (coefficientClassOf c i))

/-- The class-indexed family is invariant under every permutation fixing the
actual coefficient tuple, not merely a chosen smaller subgroup. -/
theorem groupedCoefficient_permutation (c : Fin n → K) (g : Equiv.Perm (Fin n))
    (hfix : ∀ i, c (g i) = c i) (i : Fin n) :
    groupedCoefficient c (g i) = groupedCoefficient c i := by
  have he : coefficientClassOf c (g i) = coefficientClassOf c i := Subtype.ext (hfix i)
  simp only [groupedCoefficient, he]

theorem groupedIndeterminate_subset_sum_ne_zero
    {c : Fin n → K} {lam : K} {m : ℕ} (hnr : Nonresonant c lam m)
    (I : Finset (Fin n)) (hI : I.Nonempty) :
    (∑ i ∈ I, (X (coefficientClassOf c i) : GroupedCoefficientRing c)) ≠ 0 := by
  intro hz
  have he : (∑ i ∈ I, (c i + lam * (m : K))) =
      (∑ i ∈ I, c i) + lam * ((m * I.card : ℕ) : K) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
    ring
  have h := congrArg (MvPolynomial.eval (fun a : CoefficientClass c =>
    a.val + lam * (m : K))) hz
  simp only [map_sum, MvPolynomial.eval_X, coefficientClassOf, map_zero] at h
  rw [he] at h
  exact hnr I hI (m * I.card) le_rfl h

theorem groupedCoefficient_subset_sum_ne_zero
    {c : Fin n → K} {lam : K} {m : ℕ} (hnr : Nonresonant c lam m)
    (I : Finset (Fin n)) (hI : I.Nonempty) :
    (∑ i ∈ I, groupedCoefficient c i) ≠ 0 := by
  change (∑ i ∈ I, algebraMap (GroupedCoefficientRing c) (GroupedCoefficientField c)
    (X (coefficientClassOf c i))) ≠ 0
  rw [← map_sum]
  exact (map_ne_zero_iff _ (IsFractionRing.injective
    (GroupedCoefficientRing c) (GroupedCoefficientField c))).mpr
      (groupedIndeterminate_subset_sum_ne_zero hnr I hI)

theorem groupedCoefficient_subset_sum_unit
    {c : Fin n → K} {lam : K} {m : ℕ} (hnr : Nonresonant c lam m)
    (I : Finset (Fin n)) (hI : I.Nonempty) :
    IsUnit (∑ i ∈ I, groupedCoefficient c i) :=
  isUnit_iff_ne_zero.mpr (groupedCoefficient_subset_sum_ne_zero hnr I hI)

theorem groupedCoefficient_nonresonant
    {c : Fin n → K} {lam : K} {m : ℕ} (hnr : Nonresonant c lam m) (r : ℕ) :
    Nonresonant (groupedCoefficient c) 0 r := by
  intro I hI s _
  simpa only [zero_mul, add_zero] using groupedCoefficient_subset_sum_ne_zero hnr I hI

/-- The invariant generic zero-slope fiber has the genuine regular weighted
power sequence. This is derived from the original NR condition in all fields. -/
theorem grouped_weighted_power_regular
    {c : Fin n → K} {lam : K} {m : ℕ} (hnr : Nonresonant c lam m)
    (r : ℕ) (hr : 0 < r) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) (GroupedCoefficientField c))
      (List.ofFn fun j : Fin n => weightedPower (groupedCoefficient c) (r+j.val)) := by
  simpa only [weightedPower_eq_powerMoment] using
    Fermion.powerMoments_isWeaklyRegular (fun _ : Fin n => 1)
      (groupedCoefficient c) r (fun _ => Nat.zero_lt_one) hr
      (groupedCoefficient_subset_sum_unit hnr)

end PaperVerification.PowerOperators
