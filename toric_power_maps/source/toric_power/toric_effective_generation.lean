module

public import ToricPower.ArithmeticEndpoints
public import ToricPower.DivisorWeightClassDictionary
public import ToricPower.SummandClasses
public import ToricPower.ToricGeneratorTransfer

/-!
# The effective generator criterion for actual toric direct images

This is the categorical conclusion of Proposition 6.2. Its inputs are the
proved arithmetic class sets, the actual global residue decomposition,
and the actual finite-power generator transfer. A class equality is used
only after constructing an isomorphism of the corresponding Cartier
sheaves. Generation means classical generation in the literal bounded
derived category of the coherent-sheaf category.

The finite ray enumeration and integral character basis are explicit, so
the exponent is literally the paper's `R * max K_b C_b`. No initial
generator is assumed: the conclusion is an equivalence with existence of
one positive generating power. In particular, this implication is
independent of the initial generation theorem (Theorem 1.1).

Development source: these proofs must pass the pinned compiler before
any declaration is reported as verified.
-/

@[expose] public noncomputable section

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

local instance effectiveToricLocallyNoetherian (fan : Fan i) :
    IsLocallyNoetherian fan.algebraicRealization := by
  letI := toricScheme_isNoetherian fan
  infer_instance

/-- The actual coherent sheaf of an invariant Cartier divisor. -/
def toricCoherentInvariantDivisor (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) : Coh fan.algebraicRealization := by
  letI := toricSchemeIntegral fan nonempty
  exact coherentInvertible (invariantCartierDivisor fan nonempty regular b).toInvertibleSheaf

/-- The assertion that the actual positive power direct image generates. -/
def toricInvariantPowerGenerates (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell) : Prop :=
  generatesDbCoh (X := fan.algebraicRealization) (coherentSingle fan.algebraicRealization
    ((toricCoherentPowerPushforward fan regular ell hell).obj
      (toricCoherentInvariantDivisor fan nonempty regular b)))

section ResidueSplitting

variable {κ : Type u} [Fintype κ]

/-- Each member of the genuine residue decomposition as an invertible
sheaf, retaining the complete lattice residue index. -/
def toricInvertibleResidueFamily (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (b : fan.Ray → ℤ) (ell : ℕ) :
    LatticeResidues κ ell → TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization :=
  fun residue =>
    letI := toricSchemeIntegral fan nonempty
    (invariantCartierDivisor fan nonempty regular
      (toricResidueCoefficients fan b ell
        (basis.equivFun.symm (latticeResidueRepresentative residue)))).toInvertibleSheaf

/-- The global module-sheaf decomposition lifts through the fully faithful
coherent inclusion, including its actual finite-biproduct comparison. -/
def toricCoherentInvariantSplitting (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell) :
    (toricCoherentPowerPushforward fan regular ell hell).obj
        (toricCoherentInvariantDivisor fan nonempty regular b) ≅
      ⨁ (fun residue => coherentInvertible
        (toricInvertibleResidueFamily fan nonempty regular basis b ell residue)) := by
  letI := toricSchemeIntegral fan nonempty
  exact coherentBiproductIsoOfUnderlying _
    (toricPowerInvariantCartierSplitting fan nonempty regular basis b ell hell)

/-- Every positive multiple of a generating invariant-divisor direct
image generates. Its needed invertible splitting is proved, not assumed. -/
theorem toricInvariantPowerGenerates_mul (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell k : ℕ) (hell : 0 < ell) (hk : 0 < k)
    (h : toricInvariantPowerGenerates fan nonempty regular b ell hell) :
    toricInvariantPowerGenerates fan nonempty regular b (ell * k) (Nat.mul_pos hell hk) := by
  letI : Nonempty (LatticeResidues κ ell) := ⟨zeroLatticeResidue ell hell⟩
  exact toricPowerPushforward_multiples_generate_of_invertibleSplitting
    fan nonempty regular ell k hell hk
    (toricInvertibleResidueFamily fan nonempty regular basis b ell)
    (toricCoherentInvariantDivisor fan nonempty regular b)
    (toricCoherentInvariantSplitting fan nonempty regular basis b ell hell) h

variable {s n : ℕ}

/-- The actual coherent residue summands are isomorphic when their
coefficient classes in the exact finite ray matrix agree. -/
def toricCoherentResidueIso_of_enumerated_class_eq
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b c : fan.Ray → ℤ) (ell k : ℕ)
    (residue : LatticeResidues κ ell) (other : LatticeResidues κ k)
    (same :
      divisorClass (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))
        ((toricResidueCoefficients fan b ell
          (basis.equivFun.symm (latticeResidueRepresentative residue))) ∘ rays) =
      divisorClass (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))
        ((toricResidueCoefficients fan c k
          (basis.equivFun.symm (latticeResidueRepresentative other))) ∘ rays)) :
    coherentInvertible (toricInvertibleResidueFamily fan nonempty regular basis b ell residue) ≅
      coherentInvertible (toricInvertibleResidueFamily fan nonempty regular basis c k other) := by
  letI := toricSchemeIntegral fan nonempty
  apply coherentIsoOfUnderlying
  change (invariantCartierDivisor fan nonempty regular
      (toricResidueCoefficients fan b ell
        (basis.equivFun.symm (latticeResidueRepresentative residue)))).sheaf ≅
    (invariantCartierDivisor fan nonempty regular
      (toricResidueCoefficients fan c k
        (basis.equivFun.symm (latticeResidueRepresentative other)))).sheaf
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using
    toricInvariantCartierSheafIso_of_enumerated_class_eq fan nonempty regular rays
      (basis.reindex coordinates.symm) _ _ same

/-- The isomorphism classes of the actual coherent weight summands. The
underlying finite family is the one appearing in the proved power-map
splitting; this records its classes without their multiplicities. -/
def toricCoherentResidueClasses (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (b : fan.Ray → ℤ) (ell : ℕ) : ObjectProperty (Coh fan.algebraicRealization) :=
  (ObjectProperty.ofObj (fun residue : LatticeResidues κ ell => coherentInvertible
    (toricInvertibleResidueFamily fan nonempty regular basis b ell residue))).isoClosure

/-- Equality of the full arithmetic class sets gives equality of the actual
coherent residue-summand isomorphism classes. Each match is witnessed by a
constructed Cartier-sheaf isomorphism. -/
theorem toricCoherentResidueClasses_eq_of_classes_eq
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b c : fan.Ray → ℤ)
    (ell k : ℕ) (hell : 0 < ell) (hk : 0 < k)
    (same :
      frobeniusClasses (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))
        (b ∘ rays) (ell : ℤ) =
      frobeniusClasses (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))
        (c ∘ rays) (k : ℤ)) :
    toricCoherentResidueClasses fan nonempty regular basis b ell =
      toricCoherentResidueClasses fan nonempty regular basis c k := by
  let q := divisorClass (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))
  let first := fun residue : LatticeResidues κ ell =>
    q ((toricResidueCoefficients fan b ell
      (basis.equivFun.symm (latticeResidueRepresentative residue))) ∘ rays)
  let second := fun residue : LatticeResidues κ k =>
    q ((toricResidueCoefficients fan c k
      (basis.equivFun.symm (latticeResidueRepresentative residue))) ∘ rays)
  have ranges : Set.range first = Set.range second :=
    (toricResidueClassRange_enumerated fan rays basis coordinates b ell hell).trans
      (same.trans (toricResidueClassRange_enumerated fan rays basis coordinates c k hk).symm)
  apply (isoClosure_ofObj_eq_iff _ _).2
  constructor
  · intro residue
    have member : first residue ∈ Set.range second := by
      rw [← ranges]
      exact ⟨residue, rfl⟩
    obtain ⟨other, equal⟩ := member
    exact ⟨other, ⟨toricCoherentResidueIso_of_enumerated_class_eq fan nonempty regular
      rays basis coordinates b c ell k residue other equal.symm⟩⟩
  · intro other
    have member : second other ∈ Set.range first := by
      rw [ranges]
      exact ⟨other, rfl⟩
    obtain ⟨residue, equal⟩ := member
    exact ⟨residue, ⟨toricCoherentResidueIso_of_enumerated_class_eq fan nonempty regular
      rays basis coordinates c b k ell other residue equal.symm⟩⟩


/-- Equality of arithmetic class sets implies simultaneous generation of
the actual direct images. This uses actual sheaf isomorphisms and finite
retract closure, so neither multiplicities nor Krull--Schmidt uniqueness
are needed. The two original divisors may be different. -/
theorem toricInvariantPowerGenerates_iff_of_classes_eq
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b c : fan.Ray → ℤ)
    (ell k : ℕ) (hell : 0 < ell) (hk : 0 < k)
    (same :
      frobeniusClasses (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))
        (b ∘ rays) (ell : ℤ) =
      frobeniusClasses (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))
        (c ∘ rays) (k : ℤ)) :
    toricInvariantPowerGenerates fan nonempty regular b ell hell ↔
      toricInvariantPowerGenerates fan nonempty regular c k hk := by
  letI : Nonempty (LatticeResidues κ ell) := ⟨zeroLatticeResidue ell hell⟩
  letI : Nonempty (LatticeResidues κ k) := ⟨zeroLatticeResidue k hk⟩
  exact coherentSameIsoClasses_generates_iff
    (fun residue => coherentInvertible
      (toricInvertibleResidueFamily fan nonempty regular basis b ell residue))
    (fun residue => coherentInvertible
      (toricInvertibleResidueFamily fan nonempty regular basis c k residue))
    (toricCoherentInvariantSplitting fan nonempty regular basis b ell hell)
    (toricCoherentInvariantSplitting fan nonempty regular basis c k hk)
    (toricCoherentResidueClasses_eq_of_classes_eq fan nonempty regular rays basis
      coordinates b c ell k hell hk same)

end ResidueSplitting

section StableMultiple

variable {s n : ℕ}

theorem stableMultipleExponent_pos (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) : 0 < stableMultipleExponent A b :=
  Nat.mul_pos (universalDenominator_pos A)
    (lt_of_lt_of_le (accessibilityBound_pos A b) (le_max_left _ _))

/-- A positive multiple of the paper's stable exponent already has the
same complete class set. This explicit common multiple avoids a further
unspecified sufficiently-large choice in the categorical argument. -/
theorem classes_at_mul_stableMultipleExponent_eq
    (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) (ell : ℕ) (hell : 0 < ell) :
    frobeniusClasses A b ((ell * stableMultipleExponent A b : ℕ) : ℤ) =
      frobeniusClasses A b (stableMultipleExponent A b : ℤ) := by
  rw [classes_at_stableMultipleExponent]
  have exponent : ell * stableMultipleExponent A b =
      universalDenominator A * (ell * max (accessibilityBound A b) (circuitBound A b)) := by
    unfold stableMultipleExponent
    ring
  rw [exponent]
  apply paper_proposition_6_2_classes
  · exact (le_max_left _ _).trans (Nat.le_mul_of_pos_left _ hell)
  · exact (le_max_right _ _).trans ((Nat.le_mul_of_pos_left _ hell).trans
      (Nat.le_mul_of_pos_left _ (universalDenominator_pos A)))

variable {κ : Type u} [Fintype κ]

/-- **Proposition 6.2, generator criterion.** For the literal exponent
`R * max K_b C_b`, the actual direct image generates the literal bounded
derived category of coherent sheaves if and only if some positive power
direct image does. Every residue, torus factor, and divisor class is
retained; no initial generation assumption appears. -/
theorem paper_proposition_6_2_generates_invariant
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b : fan.Ray → ℤ) :
    toricInvariantPowerGenerates fan nonempty regular b
      (stableMultipleExponent
        (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)) (b ∘ rays))
      (stableMultipleExponent_pos _ _) ↔
    ∃ ell : ℕ, ∃ hell : 0 < ell,
      toricInvariantPowerGenerates fan nonempty regular b ell hell := by
  let A := enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)
  let exponent := stableMultipleExponent A (b ∘ rays)
  have positive : 0 < exponent := stableMultipleExponent_pos A (b ∘ rays)
  constructor
  · intro h
    exact ⟨exponent, positive, h⟩
  · rintro ⟨ell, hell, h⟩
    have multiple := toricInvariantPowerGenerates_mul fan nonempty regular basis b
      ell exponent hell positive h
    exact (toricInvariantPowerGenerates_iff_of_classes_eq fan nonempty regular rays
      basis coordinates b b (ell * exponent) exponent (Nat.mul_pos hell positive) positive
      (classes_at_mul_stableMultipleExponent_eq A (b ∘ rays) ell hell)).mp multiple

end StableMultiple

end ToricPower

end
