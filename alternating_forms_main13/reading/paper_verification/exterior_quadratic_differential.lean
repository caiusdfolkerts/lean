module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Tactic.Abel

/-!
# Exterior differentials for a central two-step bracket

The operators here act on Mathlib's actual exterior algebra.  The main
calculation proves that two quadratic creation operators followed by
contraction give a square-zero odd derivation when their coefficients
are closed and even.  The hypotheses are explicit algebraic identities;
this file does not assert a Lie-cohomology comparison on their own.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ExteriorQuadraticDifferential

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

abbrev parity : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.involute (Q := (0 : QuadraticForm R M))

abbrev contraction (c : Module.Dual R M) : Module.End R (ExteriorAlgebra R M) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) c

/-- The usual odd Leibniz rule for the genuine exterior algebra. -/
def IsOddDerivation (D : Module.End R (ExteriorAlgebra R M)) : Prop :=
  D 1 = 0 ∧ ∀ x y, D (x * y) = D x * y + parity x * D y

/-- An odd derivation is uniquely determined on the original degree-one
generators.  In particular, specifying the bracket dual determines the
Chevalley--Eilenberg exterior differential uniquely. -/
theorem oddDerivation_ext {D E : Module.End R (ExteriorAlgebra R M)}
    (hD : IsOddDerivation D) (hE : IsOddDerivation E)
    (hgen : ∀ m, D (ExteriorAlgebra.ι R m) = E (ExteriorAlgebra.ι R m)) : D = E := by
  apply LinearMap.ext
  intro x
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, hD.1, hE.1]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | ι_mul m x hx => rw [hD.2, hE.2, hgen, hx]

/-- The concrete sum of quadratic multiplication followed by contraction. -/
def differential (a b : ExteriorAlgebra R M) (c₀ c₁ : Module.Dual R M) :
    Module.End R (ExteriorAlgebra R M) :=
  (LinearMap.mulLeft R a).comp (contraction c₀) +
    (LinearMap.mulLeft R b).comp (contraction c₁)

@[simp] theorem differential_apply (a b : ExteriorAlgebra R M)
    (c₀ c₁ : Module.Dual R M) (x : ExteriorAlgebra R M) :
    differential a b c₀ c₁ x = a * contraction c₀ x + b * contraction c₁ x := rfl

/-- The value on a degree-one generator retains exactly the prescribed
coefficients of the two contracting functionals. -/
theorem differential_generator (a b : ExteriorAlgebra R M)
    (c₀ c₁ : Module.Dual R M) (m : M) :
    differential a b c₀ c₁ (ExteriorAlgebra.ι R m) = c₀ m • a + c₁ m • b := by
  rw [differential_apply, contraction, CliffordAlgebra.contractLeft_ι,
    CliffordAlgebra.contractLeft_ι]
  simp only [Algebra.smul_def]
  exact congrArg₂ (· + ·) (Algebra.commutes (c₀ m) a).symm
    (Algebra.commutes (c₁ m) b).symm

/-- Central quadratic coefficients give the required odd Leibniz rule. -/
theorem differential_isOddDerivation (a b : ExteriorAlgebra R M)
    (c₀ c₁ : Module.Dual R M)
    (ha : ∀ x, Commute a x) (hb : ∀ x, Commute b x) :
    IsOddDerivation (differential a b c₀ c₁) := by
  constructor
  · simp [differential_apply, contraction]
  · intro x y
    simp only [differential_apply, contraction, CliffordAlgebra.contractLeft_mul,
      mul_add, add_mul, ← mul_assoc]
    rw [(ha (parity x)).eq, (hb (parity x)).eq]
    abel

/-- The actual exterior operator squares to zero.  Its proof uses the
anticommutation of the two genuine contraction operators. -/
theorem differential_square_zero (a b : ExteriorAlgebra R M)
    (c₀ c₁ : Module.Dual R M) (hab : Commute a b)
    (ha : parity a = a) (hb : parity b = b)
    (h₀a : contraction c₀ a = 0) (h₀b : contraction c₀ b = 0)
    (h₁a : contraction c₁ a = 0) (h₁b : contraction c₁ b = 0)
    (x : ExteriorAlgebra R M) :
    differential a b c₀ c₁ (differential a b c₀ c₁ x) = 0 := by
  simp only [differential_apply, map_add, contraction,
    CliffordAlgebra.contractLeft_mul, h₀a, h₀b, h₁a, h₁b, ha, hb,
    CliffordAlgebra.contractLeft_contractLeft, zero_mul, mul_zero,
    zero_add, add_zero]
  rw [CliffordAlgebra.contractLeft_comm c₀ c₁ x]
  simp only [mul_neg, ← mul_assoc]
  simp only [hab.eq, neg_add_cancel, add_neg_cancel]

end PaperVerification.ExteriorQuadraticDifferential
