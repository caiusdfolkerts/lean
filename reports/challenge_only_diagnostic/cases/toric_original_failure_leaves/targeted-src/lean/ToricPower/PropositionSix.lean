module

public import ToricPower.AccessibleClasses
public import ToricPower.FloorZonotope

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n s : ℕ}

/-- Closed-cube representatives determine a compatible accessible boundary
pattern whenever the representative lies on the power-map grid. -/
theorem powerCoefficient_pattern_at_cube
    (A : Matrix (Fin s) (Fin n) ℤ) (b a : Fin s → ℤ)
    (ell : ℤ) (hell : 0 < ell) (u m : Fin n → ℤ) (q : Fin n → ℝ)
    (hgrid : (fun j => (m j : ℝ)) = (ell : ℝ) • q)
    (hfloor : powerCoefficient A b ell u = a)
    (hcube : ∀ i, -1 ≤ (a i : ℝ) - realRayMap A q i ∧
      (a i : ℝ) - realRayMap A q i ≤ 0) :
    patternCoefficient (shiftSignPattern A b (u - m)) (realRayMap A q) = a := by
  apply (patternCoefficient_eq_iff _ _ _).mpr
  intro i
  have hellr : (0 : ℝ) < ell := by exact_mod_cast hell
  have hf := (powerCoefficient_eq_iff A b a ell hell u).mp hfloor i
  have hfr : (ell : ℝ) * (a i : ℝ) ≤ (b i : ℝ) + (rayMap A u i : ℝ) ∧
      (b i : ℝ) + (rayMap A u i : ℝ) ≤
        (ell : ℝ) * ((a i : ℝ) + 1) - 1 := by
    exact_mod_cast hf
  have hmi := congrFun (congrArg (realRayMap A) hgrid) i
  simp only [realRayMap_smul, Pi.smul_apply, smul_eq_mul, realRayMap_integer] at hmi
  have hshift : (b i + rayMap A (u - m) i : ℤ) =
      b i + rayMap A u i - rayMap A m i := by
    simp [map_sub]
    ring
  have hshiftr : ((b i + rayMap A (u - m) i : ℤ) : ℝ) =
      (b i : ℝ) + (rayMap A u i : ℝ) - (ell : ℝ) * realRayMap A q i := by
    rw [hshift]
    push_cast
    rw [hmi]
  have hlo := (hcube i).1
  have hup := (hcube i).2
  by_cases hi : 0 ≤ b i + rayMap A (u - m) i
  · have he : shiftSignPattern A b (u - m) i = 0 := by
      simp only [shiftSignPattern, if_pos hi]
    rw [if_pos he]
    have hsign : (0 : ℝ) ≤ (b i : ℝ) + (rayMap A u i : ℝ) -
        (ell : ℝ) * realRayMap A q i := by
      rw [← hshiftr]
      exact_mod_cast hi
    constructor
    · linarith
    · nlinarith [hfr.2]
  · have he : shiftSignPattern A b (u - m) i ≠ 0 := by
      simp only [shiftSignPattern, if_neg hi, Int.reduceNeg, ne_eq, Int.reduceEq,
        not_false_eq_true]
    rw [if_neg he]
    have hsign : (b i : ℝ) + (rayMap A u i : ℝ) -
        (ell : ℝ) * realRayMap A q i < 0 := by
      rw [← hshiftr]
      exact_mod_cast (lt_of_not_ge hi)
    constructor
    · nlinarith [hfr.1]
    · linarith

theorem frobeniusClasses_subset_accessibleThomsen
    (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) (k : ℕ)
    (hC : circuitBound A b ≤ universalDenominator A * k) :
    frobeniusClasses A b ((universalDenominator A * k : ℕ) : ℤ) ⊆
      accessibleThomsenClasses A b := by
  let ell : ℤ := ((universalDenominator A * k : ℕ) : ℤ)
  have hell : 0 < ell := by
    have hCpos := circuitBound_pos A b
    dsimp [ell]
    exact_mod_cast (lt_of_lt_of_le hCpos hC)
  rintro a ⟨u, rfl⟩
  have hzon := powerCoefficient_mem_zonotope A b ell
    (by dsimp [ell]; exact_mod_cast hC) u
  obtain ⟨a', hclass, z, hz⟩ :=
    paper_lemma_6_1_zonotope_grid A (powerCoefficient A b ell u) hzon
  have hprincipal : a' - powerCoefficient A b ell u ∈ LinearMap.range (rayMap A) :=
    (Submodule.Quotient.eq _).mp hclass
  obtain ⟨v, hv⟩ := hprincipal
  let u' : Fin n → ℤ := u + ell • v
  have hfloor : powerCoefficient A b ell u' = a' := by
    rw [powerCoefficient_translate A b ell hell.ne' u v, hv]
    abel
  let q : Fin n → ℝ :=
    (universalDenominator A : ℝ)⁻¹ • (fun j => (z j : ℝ))
  let m : Fin n → ℤ := (k : ℤ) • z
  have hR : (universalDenominator A : ℝ) ≠ 0 := by
    exact_mod_cast (universalDenominator_pos A).ne'
  have hgrid : (fun j => (m j : ℝ)) = (ell : ℝ) • q := by
    ext j
    dsimp [m, q, ell]
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    field_simp
  have hp := powerCoefficient_pattern_at_cube A b a' ell hell u' m q hgrid hfloor hz
  apply Set.mem_iUnion.mpr
  refine ⟨shiftSignPattern A b (u' - m), Set.mem_iUnion.mpr ?_⟩
  refine ⟨⟨u' - m, rfl⟩, ?_⟩
  refine ⟨q, ?_⟩
  change divisorClass A (patternCoefficient (shiftSignPattern A b (u' - m))
    (realRayMap A q)) = divisorClass A (powerCoefficient A b ell u)
  rw [hp]
  exact hclass

/-- The complete summand-class stabilization assertion of Proposition 6.2,
with its exact R, chosen-witness K_b, and primitive-circuit C_b thresholds.
The categorical generation conclusion additionally requires the geometric
splitting formula and the split-trace preservation of classical generators. -/
theorem paper_proposition_6_2_classes
    (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) (k : ℕ)
    (hK : accessibilityBound A b ≤ k)
    (hC : circuitBound A b ≤ universalDenominator A * k) :
    frobeniusClasses A b ((universalDenominator A * k : ℕ) : ℤ) =
      accessibleThomsenClasses A b := by
  exact Set.Subset.antisymm
    (frobeniusClasses_subset_accessibleThomsen A b k hC)
    (accessibleThomsenClasses_subset_power A b k hK)

end ToricPower

