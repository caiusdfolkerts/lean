module

public import ToricPower.SubfanRayRetraction
public import ToricPower.CechToricCohomology
public import ToricPower.CechWitnessReindex
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Boundary twists stabilize each original character complex

The extension coefficient is zero on new rays. Adding a times the
reduced invariant boundary gives coefficient a there. For a fixed
character, a finite explicit bound makes every new-ray inequality
nonnegative. The full Čech complex then agrees with the original fan's
complex on the old-ray face cover, including every differential.

This supplies the cohomological boundary argument directly from the
proved all-character Čech comparison, without a filtered-colimit
cohomology theorem as an additional premise.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)

def subfanRayOfOld (ρ : extension.Ray) (old : ρ.toCone.val ∈ fan.cones) : fan.Ray :=
  ⟨⟨ρ.toCone.val,old⟩,ρ.property⟩

@[simp]
theorem subfanRayEmbedding_ofOld (ρ : extension.Ray) (old : ρ.toCone.val ∈ fan.cones) :
    subfanRayEmbedding fan extension included (subfanRayOfOld fan extension ρ old) = ρ := rfl

@[simp]
theorem subfanRayOfOld_embedding (ρ : fan.Ray) :
    subfanRayOfOld fan extension (subfanRayEmbedding fan extension included ρ)
      ρ.toCone.property = ρ := rfl

/-- Coefficient one exactly on the missing invariant prime divisors. -/
def subfanBoundaryCoefficients (ρ : extension.Ray) : ℤ :=
  if ρ.toCone.val ∈ fan.cones then 0 else 1

/-- The original divisor coefficients, extended by zero on new rays. -/
def subfanZeroExtension (b : fan.Ray → ℤ) (ρ : extension.Ray) : ℤ :=
  if old : ρ.toCone.val ∈ fan.cones then b (subfanRayOfOld fan extension ρ old) else 0

/-- The actual invariant coefficients of the extended divisor plus aE. -/
def subfanBoundaryTwist (b : fan.Ray → ℤ) (a : ℕ) (ρ : extension.Ray) : ℤ :=
  if old : ρ.toCone.val ∈ fan.cones then b (subfanRayOfOld fan extension ρ old) else (a : ℤ)

theorem subfanBoundaryTwist_eq_add (b : fan.Ray → ℤ) (a : ℕ) (ρ : extension.Ray) :
    subfanBoundaryTwist fan extension b a ρ = subfanZeroExtension fan extension b ρ +
      (a : ℤ) * subfanBoundaryCoefficients fan extension ρ := by
  by_cases old : ρ.toCone.val ∈ fan.cones <;>
    simp [subfanBoundaryTwist,subfanZeroExtension,subfanBoundaryCoefficients,old]

@[simp]
theorem subfanBoundaryTwist_old (b : fan.Ray → ℤ) (a : ℕ) (ρ : fan.Ray) :
    subfanBoundaryTwist fan extension b a (subfanRayEmbedding fan extension included ρ) = b ρ := by
  unfold subfanBoundaryTwist
  change (if old : ρ.toCone.val ∈ fan.cones then b ρ else (a : ℤ)) = b ρ
  rw [dif_pos ρ.toCone.property]

theorem subfanBoundaryTwist_new (b : fan.Ray → ℤ) (a : ℕ) (ρ : extension.Ray)
    (newRay : ρ.toCone.val ∉ fan.cones) :
    subfanBoundaryTwist fan extension b a ρ = (a : ℤ) := by
  simp only [subfanBoundaryTwist,dif_neg newRay]

local instance boundaryCharacterRayFintype : Fintype extension.Ray := Fintype.ofFinite _

/-- One explicit bound controls every new ray for the specified character. -/
def subfanBoundaryThreshold (m : N →+ ℤ) : ℕ :=
  Finset.univ.sup (fun ρ : extension.Ray => (-m (fanRayPrimitiveGenerator extension ρ)).toNat)

theorem subfanBoundaryThreshold_bound (m : N →+ ℤ) (ρ : extension.Ray) :
    -m (fanRayPrimitiveGenerator extension ρ) ≤ (subfanBoundaryThreshold extension m : ℤ) :=
  (Int.self_le_toNat _).trans
    (Int.ofNat_le.mpr (Finset.le_sup (f := fun ρ : extension.Ray =>
      (-m (fanRayPrimitiveGenerator extension ρ)).toNat) (Finset.mem_univ ρ)))

theorem subfanBoundaryTwist_new_nonnegative (b : fan.Ray → ℤ) (m : N →+ ℤ)
    (a : ℕ) (large : subfanBoundaryThreshold extension m ≤ a) (ρ : extension.Ray)
    (newRay : ρ.toCone.val ∉ fan.cones) :
    ¬ toricCharacterNegative extension (subfanBoundaryTwist fan extension b a) m ρ := by
  have bound := subfanBoundaryThreshold_bound extension m ρ
  have largeInt : (subfanBoundaryThreshold extension m : ℤ) ≤ (a : ℤ) := Int.ofNat_le.mpr large
  unfold toricCharacterNegative
  rw [subfanBoundaryTwist_new fan extension b a ρ newRay]
  omega

theorem subfanBoundaryTwist_old_negative (b : fan.Ray → ℤ) (m : N →+ ℤ)
    (a : ℕ) (ρ : fan.Ray) :
    toricCharacterNegative extension (subfanBoundaryTwist fan extension b a) m
        (subfanRayEmbedding fan extension included ρ) ↔
      toricCharacterNegative fan b m ρ := by
  unfold toricCharacterNegative
  rw [subfanBoundaryTwist_old,subfanRayEmbedding_primitive]

variable (regular : extension.IsRegular) (rayFull : IsFullOnRays fan extension)

/-- A finite genuine affine cover of the original fan using the old-ray faces. -/
def subfanRetractedCechCharts : Fin (Nat.card extension.cones) → fan.cones :=
  subfanOldRayFace fan extension regular rayFull ∘ toricFiniteCechCharts extension

include included in
theorem subfanRetractedCechCharts_surjective :
    Function.Surjective (subfanRetractedCechCharts fan extension regular rayFull) :=
  (subfanOldRayFace_surjective fan extension included regular rayFull).comp
    (toricFiniteCechCharts_surjective extension)

/-- A literal isomorphism of the entire cochain complexes for every
twist beyond the fixed character's explicit bound. -/
def subfanBoundaryTwistWeightIso (b : fan.Ray → ℤ) (m : N →+ ℤ)
    (a : ℕ) (large : subfanBoundaryThreshold extension m ≤ a) :
    toricCechWeightComplex extension (toricFiniteCechCharts extension)
        (subfanBoundaryTwist fan extension b a) m ≅
      toricCechWeightComplex fan (subfanRetractedCechCharts fan extension regular rayFull) b m :=
  NegativeSupportCech.relativeComplexIsoOfForbiddenIff ℂ _ _ _ _ (by
    intro degree tuple
    constructor
    · rintro ⟨ρ,bad,incident⟩
      have old : ρ.toCone.val ∈ fan.cones := by
        by_contra newRay
        exact subfanBoundaryTwist_new_nonnegative fan extension b m a large ρ newRay bad
      let oldRay := subfanRayOfOld fan extension ρ old
      have same : subfanRayEmbedding fan extension included oldRay = ρ := rfl
      refine ⟨oldRay,?_,?_⟩
      · apply (subfanBoundaryTwist_old_negative fan extension included b m a oldRay).mp
        simpa only [same] using bad
      · intro j
        apply (subfanOldRayFace_oldRay fan extension included regular rayFull _ oldRay).mpr
        simpa only [same,toricCechRayIncidence] using incident j
    · rintro ⟨ρ,bad,incident⟩
      refine ⟨subfanRayEmbedding fan extension included ρ,
        (subfanBoundaryTwist_old_negative fan extension included b m a ρ).mpr bad,?_⟩
      intro j
      exact (subfanOldRayFace_oldRay fan extension included regular rayFull _ ρ).mp (incident j))

end ToricPower

end
