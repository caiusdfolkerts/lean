module

public import ToricPower.PropositionSix
public import ToricPower.Effectivity
public import Mathlib.Data.Pi.Interval

@[expose] public section

open Set Matrix Module
open scoped BigOperators Pointwise

namespace ToricPower

/-- The literal integer-parameter form of Lemma 7.1. -/
theorem paper_lemma_7_1_int
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (L : AddSubgroup E) (vertices : Finset E)
    (hintegral : (vertices : Set E) ⊆ L)
    (hzero : (0 : E) ∈ convexHull ℝ (vertices : Set E))
    (P : Set E) (t : ℤ)
    (ht : (finrank ℝ (Submodule.span ℝ (vertices : Set E)) : ℤ) ≤ t) :
    let K := convexHull ℝ (vertices : Set E)
    let V := Submodule.span ℝ (vertices : Set E)
    ((P + (t : ℝ) • K) ∩ (L : Set E)).Nonempty ↔
      ((V.mkQ '' P) ∩ (V.mkQ '' (L : Set E))).Nonempty := by
  have ht0 : 0 ≤ t := by omega
  have htn : finrank ℝ (Submodule.span ℝ (vertices : Set E)) ≤ t.toNat := by omega
  have hcast : (t.toNat : ℝ) = (t : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg ht0)
  simpa only [hcast] using paper_lemma_7_1 L vertices hintegral hzero P t.toNat htn

variable {n s : ℕ}

def executableUniversalDenominator (A : Matrix (Fin s) (Fin n) ℤ) : ℕ :=
  universalDenominator A

@[simp] theorem executableUniversalDenominator_eq (A : Matrix (Fin s) (Fin n) ℤ) :
    executableUniversalDenominator A = universalDenominator A := rfl

/-- An executable stable multiple of the universal denominator. -/
def executableStableExponent (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) : ℕ :=
  universalDenominator A * periodicityBound A b

noncomputable section

theorem paper_proposition_6_2_classes_int
    (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) (k : ℤ)
    (hK : (accessibilityBound A b : ℤ) ≤ k)
    (hC : (circuitBound A b : ℤ) ≤ (universalDenominator A : ℤ) * k) :
    frobeniusClasses A b ((universalDenominator A : ℤ) * k) =
      accessibleThomsenClasses A b := by
  have hk0 : 0 ≤ k := by
    have hp := accessibilityBound_pos A b
    omega
  have hkn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
  have hK' : accessibilityBound A b ≤ k.toNat := by omega
  have hC' : circuitBound A b ≤ universalDenominator A * k.toNat := by
    exact_mod_cast (show (circuitBound A b : ℤ) ≤
      (universalDenominator A : ℤ) * (k.toNat : ℤ) by simpa only [hkn] using hC)
  simpa only [Nat.cast_mul, hkn] using
    paper_proposition_6_2_classes A b k.toNat hK' hC'

def stableMultipleExponent (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) : ℕ :=
  universalDenominator A * max (accessibilityBound A b) (circuitBound A b)

theorem classes_at_stableMultipleExponent
    (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) :
    frobeniusClasses A b (stableMultipleExponent A b : ℤ) =
      accessibleThomsenClasses A b := by
  apply paper_proposition_6_2_classes A b
    (max (accessibilityBound A b) (circuitBound A b)) (le_max_left _ _)
  have hR : 1 ≤ universalDenominator A := universalDenominator_pos A
  exact (le_max_right _ _).trans (Nat.le_mul_of_pos_left _ hR)

theorem frobeniusClasses_eq_image_raw (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) (ell : ℤ) (hell : 0 < ell) :
    frobeniusClasses A b ell = divisorClass A '' rawCoefficients A b ell := by
  ext a
  constructor
  · intro ha
    obtain ⟨u, hu, hua⟩ := (frobeniusClasses_iff_bounded A b ell hell a).mp ha
    exact ⟨powerCoefficient A b ell u, ⟨u, hu, rfl⟩, hua⟩
  · rintro ⟨c, ⟨u, _, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩

theorem frobeniusClasses_finite (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) (ell : ℤ) (hell : 0 < ell) :
    (frobeniusClasses A b ell).Finite := by
  have hf : (Set.Icc (0 : Fin n → ℤ) (fun _ => ell - 1)).Finite := Set.finite_Icc _ _
  apply (hf.image (fun u => divisorClass A (powerCoefficient A b ell u))).subset
  intro a ha
  obtain ⟨u, hu, hua⟩ := (frobeniusClasses_iff_bounded A b ell hell a).mp ha
  refine ⟨u, ⟨fun j => (hu j).1, fun j => ?_⟩, hua⟩
  change u j ≤ ell - 1
  have hj := (hu j).2
  omega

theorem thomsenClasses_finite (A : Matrix (Fin s) (Fin n) ℤ)
    (e : Fin s → ℤ) (he : IsSignPattern e) : (thomsenClasses A e).Finite := by
  rw [thomsenClasses_eq_frobenius_universal A e he]
  apply frobeniusClasses_finite
  exact_mod_cast universalDenominator_pos A

theorem accessibleThomsenClasses_finite (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) : (accessibleThomsenClasses A b).Finite := by
  rw [← classes_at_stableMultipleExponent A b]
  apply frobeniusClasses_finite
  have hR := universalDenominator_pos A
  have hK := accessibilityBound_pos A b
  have hmax : 0 < max (accessibilityBound A b) (circuitBound A b) :=
    lt_of_lt_of_le hK (le_max_left _ _)
  exact_mod_cast (Nat.mul_pos hR hmax)

theorem frobeniusClasses_periodic (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) (ell : ℤ) (hell : (periodicityBound A b : ℤ) ≤ ell) :
    frobeniusClasses A b (ell + (rayPeriod A : ℤ)) = frobeniusClasses A b ell := by
  have hN : 0 < periodicityBound A b := by
    unfold periodicityBound
    have := realStabilizationBound_pos A b
    omega
  have hellpos : 0 < ell := lt_of_lt_of_le (by exact_mod_cast hN) hell
  have hD : (0 : ℤ) < rayPeriod A := by exact_mod_cast rayPeriod_pos A
  rw [frobeniusClasses_eq_image_raw A b _ (by omega),
    frobeniusClasses_eq_image_raw A b ell hellpos,
    paper_theorem_7_2_raw_int A b ell hell]

theorem periodicityBound_pos (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) :
    0 < periodicityBound A b := by
  unfold periodicityBound
  have := realStabilizationBound_pos A b
  omega

theorem frobeniusClasses_add_period_mul (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) (ell : ℤ) (hell : (periodicityBound A b : ℤ) ≤ ell)
    (t : ℕ) :
    frobeniusClasses A b (ell + (t : ℤ) * (rayPeriod A : ℤ)) =
      frobeniusClasses A b ell := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hD : (0 : ℤ) ≤ rayPeriod A := Int.natCast_nonneg _
    have ht : (0 : ℤ) ≤ t := Int.natCast_nonneg _
    have hbase : (periodicityBound A b : ℤ) ≤
        ell + (t : ℤ) * (rayPeriod A : ℤ) := by nlinarith
    calc
      frobeniusClasses A b (ell + ((t + 1 : ℕ) : ℤ) * (rayPeriod A : ℤ)) =
          frobeniusClasses A b ((ell + (t : ℤ) * (rayPeriod A : ℤ)) +
            (rayPeriod A : ℤ)) := by congr 1; push_cast; ring
      _ = frobeniusClasses A b (ell + (t : ℤ) * (rayPeriod A : ℤ)) :=
        frobeniusClasses_periodic A b _ hbase
      _ = frobeniusClasses A b ell := ih

/-- Eventual raw periodicity removes the classical accessibility witnesses from
the numerical stable-multiple bound. -/
theorem classes_stable_at_computable_bound
    (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) (k : ℕ)
    (hk : periodicityBound A b ≤ k) :
    frobeniusClasses A b ((universalDenominator A * k : ℕ) : ℤ) =
      accessibleThomsenClasses A b := by
  let j := max k (max (accessibilityBound A b) (circuitBound A b))
  have hkj : k ≤ j := le_max_left _ _
  have hK : accessibilityBound A b ≤ j :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC : circuitBound A b ≤ j :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hR : 0 < universalDenominator A := universalDenominator_pos A
  have hC' : circuitBound A b ≤ universalDenominator A * j :=
    hC.trans (Nat.le_mul_of_pos_left j hR)
  have hNj : (periodicityBound A b : ℤ) ≤
      ((universalDenominator A * k : ℕ) : ℤ) := by
    exact_mod_cast hk.trans (Nat.le_mul_of_pos_left k hR)
  have heqN : universalDenominator A * k +
      ((j - k) * dimensionDenominator n) * rayPeriod A =
      universalDenominator A * j := by
    unfold universalDenominator
    calc
      rayPeriod A * dimensionDenominator n * k +
          ((j - k) * dimensionDenominator n) * rayPeriod A =
        rayPeriod A * dimensionDenominator n * (k + (j - k)) := by ring
      _ = rayPeriod A * dimensionDenominator n * j := by
        rw [Nat.add_sub_of_le hkj]
  have heqZ : ((universalDenominator A * k : ℕ) : ℤ) +
      (((j - k) * dimensionDenominator n : ℕ) : ℤ) * (rayPeriod A : ℤ) =
      ((universalDenominator A * j : ℕ) : ℤ) := by exact_mod_cast heqN
  have hp := frobeniusClasses_add_period_mul A b
    ((universalDenominator A * k : ℕ) : ℤ) hNj ((j - k) * dimensionDenominator n)
  rw [heqZ] at hp
  rw [← hp]
  exact paper_proposition_6_2_classes A b j hK hC'

theorem classes_at_executableStableExponent (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) :
    frobeniusClasses A b (executableStableExponent A b : ℤ) =
      accessibleThomsenClasses A b :=
  classes_stable_at_computable_bound A b (periodicityBound A b) le_rfl

end
end ToricPower

