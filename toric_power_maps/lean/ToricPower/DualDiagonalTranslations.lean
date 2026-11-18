module

public import ToricPower.DualDiagonalStrip
public import ToricPower.DiagonalChartAction
public import ToricPower.ConvexComplementTranslation

/-!
# Actual monomial translations of the open dual strip

Multiplication by a regular character on each factor raises the total
weight by their sum and translates the universal-cover cell by the
negative of the first character. Bounded integer windows map into
bounded windows with an explicit coordinate margin.
-/

@[expose] public noncomputable section

open Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S T : Set (Fin s))
  (u : Fin n → ℤ) (a : rayCharacterMonoid A S) (b : rayCharacterMonoid A T)

/-- The two literal dual Cartier inequalities are preserved by genuine
monomial multiplication on the two affine factors. -/
theorem dualDiagonalMonomialAllowed_multiply {q : ℕ} (c : NormalizedCell A q)
    (v : Fin n → ℤ) (hv : dualDiagonalMonomialAllowed A S T u (c, v)) :
    dualDiagonalMonomialAllowed A S T (u + a.val + b.val) (c, v + a.val) := by
  constructor
  · intro i hi
    have ha := a.property i hi
    have original := hv.1 i hi
    change 0 ≤ rayPairing A v i + reflectedCeiling A c.val i at original
    change 0 ≤ rayPairing A (v + a.val) i + reflectedCeiling A c.val i
    rw [rayPairing_add]
    omega
  · intro i hi
    have hb := b.property i hi
    have original := hv.2 i hi
    change 0 ≤ rayPairing A (u - v) i + c.val.val.1 (.inl i) at original
    change 0 ≤ rayPairing A (u + a.val + b.val - (v + a.val)) i +
      c.val.val.1 (.inl i)
    rw [rayPairing_sub, rayPairing_add, rayPairing_add, rayPairing_add]
    rw [rayPairing_sub] at original
    omega

/-- The actual support inclusion underlying monomial multiplication. -/
theorem dualDiagonalStrip_monomial_translation :
    translatedRegion (dualDiagonalStrip A S T u) (latticeLift (-a.val)) ⊆
      dualDiagonalStrip A S T (u + a.val + b.val) := by
  rintro _ ⟨x, hx, rfl⟩
  have row (i : Fin s) : integralRowForm A i (x + latticeLift (-a.val)) =
      integralRowForm A i x - (rayPairing A a.val i : ℝ) := by
    rw [latticeLift_neg, map_add, map_neg]
    have lift := augmentedForms_latticeLift A a.val (.inl i)
    change integralRowForm A i (latticeLift a.val) = (rayPairing A a.val i : ℝ) at lift
    rw [lift]
    rfl
  constructor
  · intro i hi
    rw [row]
    have nonnegative : (0 : ℝ) ≤ (rayPairing A a.val i : ℝ) := by
      exact_mod_cast a.property i hi
    exact sub_le_self _ nonnegative |>.trans_lt (hx.1 i hi)
  · intro i hi
    rw [row, rayPairing_add, rayPairing_add, Int.cast_add, Int.cast_add]
    have nonnegative : (0 : ℝ) ≤ (rayPairing A b.val i : ℝ) := by
      exact_mod_cast b.property i hi
    have lower := hx.2 i hi
    linarith

/-- A coordinate margin controls translation of every integer box,
independently of the strip or the number of its cells. -/
theorem integerOpenBox_translation {r C : ℕ} (z : Fin n → ℤ)
    (bound : ∀ j, |latticeLift z j| ≤ (C : ℝ)) :
    translatedRegion (integerOpenBox (n := n) r) (latticeLift z) ⊆
      integerOpenBox (r + C) := by
  rintro _ ⟨x, hx, rfl⟩ j
  have lower := (abs_le.mp (bound j)).1
  have upper := (abs_le.mp (bound j)).2
  change -((r + C : ℕ) : ℝ) < x j + latticeLift z j ∧
    x j + latticeLift z j < ((r + C : ℕ) : ℝ)
  rw [Nat.cast_add]
  constructor <;> linarith [(hx j).1, (hx j).2]

/-- Every lattice translation admits a finite integer coordinate margin. -/
theorem latticeLift_exists_coordinateMargin (z : Fin n → ℤ) :
    ∃ C : ℕ, ∀ j, |latticeLift z j| ≤ (C : ℝ) := by
  obtain ⟨C, bound⟩ := exists_nat_gt ‖latticeLift z‖
  refine ⟨C, fun j => ?_⟩
  have coordinate : |latticeLift z j| ≤ ‖latticeLift z‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (latticeLift z) j
  exact coordinate.trans bound.le

/-- Literal finite-stage support inclusion for multiplication by the
chosen regular monomial pair. -/
theorem dualDiagonalWindow_monomial_translation (r C : ℕ)
    (bound : ∀ j, |latticeLift (-a.val) j| ≤ (C : ℝ)) :
    translatedRegion (dualDiagonalWindow A S T u r) (latticeLift (-a.val)) ⊆
      dualDiagonalWindow A S T (u + a.val + b.val) (r + C) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨dualDiagonalStrip_monomial_translation A S T u a b ⟨x, hx.1, rfl⟩,
    integerOpenBox_translation (-a.val) bound ⟨x, hx.2, rfl⟩⟩

end ToricPower.IntegralArrangement
