module

public import ToricPower.ToricEffectiveLineBundles

/-!
# Periodicity of generation by actual toric power-map direct images

The complete arithmetic class set controls classical generation because the
actual finite residue decompositions have isomorphic summands whenever their
integral divisor classes agree. Consequently the arithmetic period also is a
period of generation in the literal bounded derived category of coherent
sheaves. The period depends only on the fan and the chosen lattice coordinates.

These results do not assume the cohomological criterion. A separate final lemma
shows how an eventual-generation theorem supplies generation at the explicit
arithmetic threshold. This is the step used in the effective conclusion of
Section 7 after the principal cohomological theorem is established.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

section Invariant

variable {κ : Type u} [Fintype κ] {s n : ℕ}

/-- Equal-period translates have exactly the same actual coherent residue
summand isomorphism classes. This assertion is independent of generation. -/
theorem toricCoherentResidueClasses_add_period_mul
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b : fan.Ray → ℤ) (ell : ℕ)
    (hell : periodicityBound
      (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)) (b ∘ rays) ≤ ell)
    (t : ℕ) :
    toricCoherentResidueClasses fan nonempty regular basis b
        (ell + t * rayPeriod
          (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))) =
      toricCoherentResidueClasses fan nonempty regular basis b ell := by
  let A := enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)
  have hclasses :
      frobeniusClasses A (b ∘ rays) ((ell + t * rayPeriod A : ℕ) : ℤ) =
        frobeniusClasses A (b ∘ rays) (ell : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      frobeniusClasses_add_period_mul A (b ∘ rays) (ell : ℤ)
        (by exact_mod_cast hell) t
  have positive : 0 < ell := (periodicityBound_pos _ _).trans_le hell
  exact toricCoherentResidueClasses_eq_of_classes_eq fan nonempty regular
    rays basis coordinates b b _ ell (Nat.add_pos_left positive _) positive hclasses

/-- Equal-period translates of an exponent have the same generation property.
All coefficients and lattice residues are retained by the actual splitting. -/
theorem toricInvariantPowerGenerates_add_period_mul
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b : fan.Ray → ℤ) (ell : ℕ)
    (hell : periodicityBound
      (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)) (b ∘ rays) ≤ ell)
    (t : ℕ) :
    toricInvariantPowerGenerates fan nonempty regular b
        (ell + t * rayPeriod
          (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)))
        (Nat.add_pos_left ((periodicityBound_pos _ _).trans_le hell) _) ↔
      toricInvariantPowerGenerates fan nonempty regular b ell
        ((periodicityBound_pos _ _).trans_le hell) := by
  let A := enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)
  have hclasses :
      frobeniusClasses A (b ∘ rays) ((ell + t * rayPeriod A : ℕ) : ℤ) =
        frobeniusClasses A (b ∘ rays) (ell : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      frobeniusClasses_add_period_mul A (b ∘ rays) (ell : ℤ)
        (by exact_mod_cast hell) t
  exact toricInvariantPowerGenerates_iff_of_classes_eq fan nonempty regular
    rays basis coordinates b b _ ell _ _ hclasses

/-- The categorical periodicity assertion for an arbitrary invariant divisor. -/
theorem toricInvariantPowerGenerates_periodic
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b : fan.Ray → ℤ) (ell : ℕ)
    (hell : periodicityBound
      (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)) (b ∘ rays) ≤ ell) :
    toricInvariantPowerGenerates fan nonempty regular b
        (ell + rayPeriod
          (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)))
        (Nat.add_pos_left ((periodicityBound_pos _ _).trans_le hell) _) ↔
      toricInvariantPowerGenerates fan nonempty regular b ell
        ((periodicityBound_pos _ _).trans_le hell) := by
  simpa only [one_mul] using toricInvariantPowerGenerates_add_period_mul
    fan nonempty regular rays basis coordinates b ell hell 1

end Invariant

/-- The ray matrix supplied by the actual fan, using finite coordinates from
its integral character lattice. No divisor enters this definition. -/
def toricPowerRayMatrix (fan : Fan i) :
    Matrix (Fin (Nat.card fan.Ray)) (Fin (Module.finrank ℤ N)) ℤ :=
  enumeratedFanRayMatrix fan (toricEffectiveRayEnumeration fan)
    ((toricEffectiveCharacterBasis fan).reindex (Equiv.ulift.{u, 0}))

/-- The positive period, independent of the chosen line bundle or divisor. -/
def toricPowerPeriod (fan : Fan i) : ℕ := rayPeriod (toricPowerRayMatrix fan)

theorem toricPowerPeriod_pos (fan : Fan i) : 0 < toricPowerPeriod fan :=
  rayPeriod_pos _

/-- The explicit arithmetic threshold of the constructed invariant
representative of an arbitrary actual line bundle. -/
def toricLineBundlePeriodicityBound (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization) : ℕ :=
  periodicityBound (toricPowerRayMatrix fan)
    (toricLineBundleInvariantCoefficients fan nonempty regular L.obj ∘
      toricEffectiveRayEnumeration fan)

theorem toricLineBundlePeriodicityBound_pos (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization) :
    0 < toricLineBundlePeriodicityBound fan nonempty regular L :=
  periodicityBound_pos _ _

/-- Periodicity of the actual coherent residue-summand class set, for any
number of periods and every original line bundle. Its family is linked to the
actual direct image by `toricCoherentLineBundleSplitting`. -/
theorem toricLineBundleResidueClasses_add_period_mul
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization)
    (ell : ℕ) (hell : toricLineBundlePeriodicityBound fan nonempty regular L ≤ ell)
    (t : ℕ) :
    toricLineBundleResidueClasses fan nonempty regular L (ell + t * toricPowerPeriod fan) =
      toricLineBundleResidueClasses fan nonempty regular L ell := by
  exact toricCoherentResidueClasses_add_period_mul fan nonempty regular
    (toricEffectiveRayEnumeration fan) (toricEffectiveCharacterBasis fan)
    (Equiv.ulift.{u, 0}).symm
    (toricLineBundleInvariantCoefficients fan nonempty regular L.obj) ell hell t

/-- **Theorem 7.2, actual summand-class periodicity.** The ray-dependent
positive period preserves precisely the isomorphism classes of the constructed
weight summands of the original line-bundle direct image, beyond the explicit
height-dependent threshold. No generation criterion is assumed. -/
theorem paper_theorem_7_2_summandClasses_periodic_lineBundle
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization)
    (ell : ℕ) (hell : toricLineBundlePeriodicityBound fan nonempty regular L ≤ ell) :
    toricLineBundleResidueClasses fan nonempty regular L (ell + toricPowerPeriod fan) =
      toricLineBundleResidueClasses fan nonempty regular L ell := by
  simpa only [one_mul] using toricLineBundleResidueClasses_add_period_mul
    fan nonempty regular L ell hell 1

/-- Actual summand-class periodicity for an arbitrary Cartier divisor. -/
theorem paper_theorem_7_2_summandClasses_periodic_cartier
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (D : letI := toricSchemeIntegral fan nonempty
      TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization)
    (ell : ℕ)
    (hell : letI := toricSchemeIntegral fan nonempty
      toricLineBundlePeriodicityBound fan nonempty regular D.toInvertibleSheaf ≤ ell) :
    letI := toricSchemeIntegral fan nonempty
    toricLineBundleResidueClasses fan nonempty regular D.toInvertibleSheaf
        (ell + toricPowerPeriod fan) =
      toricLineBundleResidueClasses fan nonempty regular D.toInvertibleSheaf ell := by
  letI := toricSchemeIntegral fan nonempty
  exact paper_theorem_7_2_summandClasses_periodic_lineBundle fan nonempty regular
    D.toInvertibleSheaf ell hell

/-- Periodicity through any nonnegative number of periods, for every actual
line bundle in the genuine coherent derived category. -/
theorem toricLineBundlePowerGenerates_add_period_mul
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization)
    (ell : ℕ) (hell : toricLineBundlePeriodicityBound fan nonempty regular L ≤ ell)
    (t : ℕ) :
    toricLineBundlePowerGenerates fan regular L (ell + t * toricPowerPeriod fan)
        (Nat.add_pos_left
          ((toricLineBundlePeriodicityBound_pos fan nonempty regular L).trans_le hell) _) ↔
      toricLineBundlePowerGenerates fan regular L ell
        ((toricLineBundlePeriodicityBound_pos fan nonempty regular L).trans_le hell) := by
  rw [toricLineBundlePowerGenerates_iff_invariant fan nonempty regular L,
    toricLineBundlePowerGenerates_iff_invariant fan nonempty regular L]
  exact toricInvariantPowerGenerates_add_period_mul fan nonempty regular
    (toricEffectiveRayEnumeration fan) (toricEffectiveCharacterBasis fan)
    (Equiv.ulift.{u, 0}).symm
    (toricLineBundleInvariantCoefficients fan nonempty regular L.obj) ell hell t

/-- **Theorem 7.2, periodicity of generation.** The exact class-set period is
also a period for generation by the actual direct image of every line bundle.
The fan need not be complete or projective. -/
theorem paper_theorem_7_2_generation_periodic_lineBundle
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization)
    (ell : ℕ) (hell : toricLineBundlePeriodicityBound fan nonempty regular L ≤ ell) :
    toricLineBundlePowerGenerates fan regular L (ell + toricPowerPeriod fan)
        (Nat.add_pos_left
          ((toricLineBundlePeriodicityBound_pos fan nonempty regular L).trans_le hell) _) ↔
      toricLineBundlePowerGenerates fan regular L ell
        ((toricLineBundlePeriodicityBound_pos fan nonempty regular L).trans_le hell) := by
  simpa only [one_mul] using toricLineBundlePowerGenerates_add_period_mul
    fan nonempty regular L ell hell 1

/-- The same periodicity statement for every actual Cartier divisor, through
the invertibility of its genuine associated sheaf. -/
theorem paper_theorem_7_2_generation_periodic_cartier
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (D : letI := toricSchemeIntegral fan nonempty
      TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization)
    (ell : ℕ)
    (hell : letI := toricSchemeIntegral fan nonempty
      toricLineBundlePeriodicityBound fan nonempty regular D.toInvertibleSheaf ≤ ell) :
    letI := toricSchemeIntegral fan nonempty
    toricLineBundlePowerGenerates fan regular D.toInvertibleSheaf
        (ell + toricPowerPeriod fan)
        (Nat.add_pos_left
          ((toricLineBundlePeriodicityBound_pos fan nonempty regular D.toInvertibleSheaf).trans_le
            hell) _) ↔
      toricLineBundlePowerGenerates fan regular D.toInvertibleSheaf ell
        ((toricLineBundlePeriodicityBound_pos fan nonempty regular D.toInvertibleSheaf).trans_le
          hell) := by
  letI := toricSchemeIntegral fan nonempty
  exact paper_theorem_7_2_generation_periodic_lineBundle fan nonempty regular
    D.toInvertibleSheaf ell hell

/-- Once eventual generation has been proved, the arithmetic threshold is
already sufficient: move forwards by whole periods to a known generator and
use equality of the actual summand class sets to return to the original power.
The eventual-generation hypothesis is explicit; this is the final numerical
reduction, not a replacement for the cohomological criterion. -/
theorem toricLineBundlePowerGenerates_at_periodicityBound_of_eventually
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization)
    (eventually : ∃ K : ℕ, ∀ (ell : ℕ) (hell : 0 < ell), K ≤ ell →
      toricLineBundlePowerGenerates fan regular L ell hell)
    (ell : ℕ) (hell : toricLineBundlePeriodicityBound fan nonempty regular L ≤ ell) :
    toricLineBundlePowerGenerates fan regular L ell
      ((toricLineBundlePeriodicityBound_pos fan nonempty regular L).trans_le hell) := by
  obtain ⟨K, hK⟩ := eventually
  have hp := toricPowerPeriod_pos fan
  have hlarge : K ≤ ell + K * toricPowerPeriod fan := by nlinarith
  have hpositive : 0 < ell + K * toricPowerPeriod fan :=
    Nat.add_pos_left
      ((toricLineBundlePeriodicityBound_pos fan nonempty regular L).trans_le hell) _
  exact (toricLineBundlePowerGenerates_add_period_mul fan nonempty regular L ell hell K).mp
    (hK _ hpositive hlarge)

end ToricPower

end
