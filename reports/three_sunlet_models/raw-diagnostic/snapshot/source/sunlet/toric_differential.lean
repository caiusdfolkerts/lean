module

public import sunlet.contact_coefficient
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.FieldSimp

/-! The actual first and logarithmic second differentials of the ratio
monomial map. These identities connect the sparse linear algebra to
rational functions, rather than defining the desired geometric conclusion. -/

@[expose] public section
noncomputable section

namespace Sunlet.ToricDifferential

variable {F E ι Ω : Type*} [Field F] [Field E] [Algebra F E]

abbrev Variation (E ι Ω : Type*) := (ι → E) × (Ω → E)

def ratio (π : ι → Equiv.Perm Ω) (k : Ω → E) (a : ι) (b : Ω) : E :=
  k b / k (π a b)

def coordinate (π : ι → Equiv.Perm Ω) (U : ι → E) (k : Ω → E)
    (a : ι) (b : Ω) : E := U a * ratio π k a b

def differential (π : ι → Equiv.Perm Ω) (U : ι → E) (k : Ω → E) :
    Variation E ι Ω →ₗ[E] (ι × Ω → E) where
  toFun v ab := ratio π k ab.1 ab.2 *
    (v.1 ab.1 + U ab.1 * (v.2 ab.2 - v.2 (π ab.1 ab.2)))
  map_add' := by intros; funext ab; dsimp; ring
  map_smul' := by intros; funext ab; dsimp; ring

@[simp] theorem differential_apply (π : ι → Equiv.Perm Ω) (U : ι → E) (k : Ω → E)
    (v : Variation E ι Ω) (a : ι) (b : Ω) :
    differential π U k v (a, b) = ratio π k a b * (v.1 a + U a * (v.2 b - v.2 (π a b))) := rfl

def hessian (π : ι → Equiv.Perm Ω) (U : ι → E) (k : Ω → E)
    (v w : Variation E ι Ω) (ab : ι × Ω) : E :=
  ratio π k ab.1 ab.2 * (w.1 ab.1 * (v.2 ab.2 - v.2 (π ab.1 ab.2)) +
    v.1 ab.1 * (w.2 ab.2 - w.2 (π ab.1 ab.2)) +
    U ab.1 * (v.2 ab.2 - v.2 (π ab.1 ab.2)) * (w.2 ab.2 - w.2 (π ab.1 ab.2)))

def logarithmicVelocity (D : Derivation F E E) (U : ι → E) (k : Ω → E) :
    Variation E ι Ω := (fun a => D (U a), fun b => D (k b) / k b)

/-- The displayed first differential is obtained by applying an arbitrary
base-field derivation to the actual coordinate rational function. -/
theorem derivation_coordinate (D : Derivation F E E) (π : ι → Equiv.Perm Ω)
    (U : ι → E) (k : Ω → E) (hk : ∀ b, k b ≠ 0) (a : ι) (b : Ω) :
    D (coordinate π U k a b) = differential π U k (logarithmicVelocity D U k) (a, b) := by
  simp only [coordinate, differential_apply, ratio, logarithmicVelocity,
    D.leibniz, D.leibniz_div, smul_eq_mul]
  field_simp [hk b, hk (π a b)]
  ring

/-- Differentiating a constant coefficient/logarithmic-torus column gives
the displayed second differential. -/
theorem derivation_differential_column (D : Derivation F E E) (π : ι → Equiv.Perm Ω)
    (U : ι → E) (k : Ω → E) (hk : ∀ b, k b ≠ 0) (w : Variation E ι Ω)
    (hp : ∀ a, D (w.1 a) = 0) (hH : ∀ b, D (w.2 b) = 0) (a : ι) (b : Ω) :
    D (differential π U k w (a, b)) = hessian π U k (logarithmicVelocity D U k) w (a, b) := by
  simp only [differential_apply, hessian, ratio, logarithmicVelocity,
    D.leibniz, D.leibniz_div, map_add, map_sub, hp, hH, sub_self, mul_zero, add_zero,
    smul_eq_mul]
  field_simp [hk b, hk (π a b)]
  ring

variable [DecidableEq Ω] [DecidableEq ι]

def sparseCoefficients (A : Set ι) [DecidablePred (· ∈ A)] : ι → E :=
  fun a => if a ∈ A then 1 else 0

def sparseScale [CharZero E] (o : Ω) : Ω → E :=
  fun b => algebraMap ℚ E (TwoRatioRigidity.scale o b)

theorem sparseScale_ne_zero [CharZero E] (o b : Ω) : sparseScale (E := E) o b ≠ 0 := by
  by_cases h : b = o <;> simp [sparseScale, TwoRatioRigidity.scale, h]

theorem sparseScale_ratio [CharZero E] (π : ι → Equiv.Perm Ω) (o : Ω) (a : ι) (b : Ω) :
    ratio π (sparseScale (E := E) o) a b =
      algebraMap ℚ E (TwoRatioRigidity.ratio o (π a) b) := by
  simp [ratio, sparseScale, TwoRatioRigidity.ratio]

/-- The sparse paired differential from Section 4.2 is literally the sum of
the two differentials of the monomial map at the two displayed parameters. -/
theorem sparse_pair_differential [Fintype Ω] [CharZero E]
    (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (v w : Variation E ι Ω) :
    (fun ab => differential π (sparseCoefficients A) (fun _ => 1) v ab +
      differential π (sparseCoefficients B) (sparseScale o) w ab) =
        Contact.pairDifferential π o A B (v, w) := by
  funext ab
  rcases ab with ⟨a, b⟩
  simp only [differential_apply, sparseScale_ratio, Contact.pairDifferential_apply]
  simp only [ratio, div_self (one_ne_zero : (1 : E) ≠ 0), one_mul, sparseCoefficients]
  split_ifs <;> ring

/-- The radial velocity has its second differential in the first tangent
space, with an explicit tangent preimage. -/
theorem radial_hessian (π : ι → Equiv.Perm Ω) (U : ι → E) (k : Ω → E)
    (w : Variation E ι Ω) :
    hessian π U k (U, 0) w = differential π U k (0, w.2) := by
  funext ab
  rcases ab with ⟨a, b⟩
  simp [hessian, differential_apply]

end Sunlet.ToricDifferential
