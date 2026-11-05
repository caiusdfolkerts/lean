module

public import Recovery.Unimodular.KoszulSupport.PaperVerification.NoncommutativeBarLength

/-!
# The genuine normalized bar differential with arbitrary coefficients

The differential is obtained by evaluating the coefficients of the actual
free bar differential. Its square and its naturality therefore follow from
that checked free resolution, without a new exactness assumption.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.FlagKoszul.CoefficientModuleBar

open PaperVerification.NoncommutativeBar

variable {K A I M N : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- Evaluation of a free word vector on a module coefficient. -/
def evaluate : Words I A →ₗ[A] (M →ₗ[A] Words I M) :=
  Finsupp.linearCombination A (fun L => Finsupp.lsingle L)

@[simp] theorem evaluate_single (L : List I) (a : A) (m : M) :
    evaluate (Finsupp.single L a) m = Finsupp.single L (a • m) := by
  simp only [evaluate, Finsupp.linearCombination_single, LinearMap.smul_apply,
    Finsupp.lsingle_apply, Finsupp.smul_single]

@[simp] theorem evaluate_apply (z : Words I A) (m : M) (L : List I) :
    evaluate z m L = z L • m := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply, Finsupp.zero_apply, zero_smul]
  | add z w hz hw =>
    simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, hz, hw, add_smul]
  | single T a =>
    by_cases h : T = L
    · subst T
      simp only [evaluate_single, Finsupp.single_eq_same]
    · simp [evaluate_single, Finsupp.single_apply, h]

/-- The coefficient-module differential induced by the actual free differential. -/
def differential (B : Module.Basis (Option I) K A) : Words I M →ₗ[A] Words I M :=
  Finsupp.lsum A (fun L => evaluate (PaperVerification.NoncommutativeBar.differential B
    (Finsupp.single L 1)))

@[simp] theorem differential_single (B : Module.Basis (Option I) K A)
    (L : List I) (m : M) :
    differential B (Finsupp.single L m) =
      evaluate (PaperVerification.NoncommutativeBar.differential B (Finsupp.single L 1)) m := by
  simp only [differential, Finsupp.lsum_single]

theorem differential_evaluate (B : Module.Basis (Option I) K A)
    (z : Words I A) (m : M) :
    differential B (evaluate z m) =
      evaluate (PaperVerification.NoncommutativeBar.differential B z) m := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add z w hz hw => simp only [map_add, LinearMap.add_apply, hz, hw]
  | single L a =>
    have hs : (Finsupp.single L a : Words I A) = a • Finsupp.single L 1 := by
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [evaluate_single, differential_single, hs]
    simp only [map_smul, LinearMap.smul_apply]

variable (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none = 1) (hε : ∀ i, ε (B (some i)) = 0)

include hunit hε in
/-- Square-zero is inherited from the genuine free bar resolution. -/
theorem differential_squared (z : Words I M) : differential B (differential B z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw, add_zero]
  | single L m =>
    rw [differential_single, differential_evaluate,
      PaperVerification.NoncommutativeBar.differential_squared ε B hunit hε,
      map_zero, LinearMap.zero_apply]

/-- The actual coefficientwise map associated to a module homomorphism. -/
def map (f : M →ₗ[A] N) : Words I M →ₗ[A] Words I N := Finsupp.mapRange.linearMap f

@[simp] theorem map_single (f : M →ₗ[A] N) (L : List I) (m : M) :
    map f (Finsupp.single L m) = Finsupp.single L (f m) := by
  simp [map]

theorem map_evaluate (f : M →ₗ[A] N) (z : Words I A) (m : M) :
    map f (evaluate z m) = evaluate z (f m) := by
  ext L
  simp only [map, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    evaluate_apply, map_smul]

theorem map_differential (f : M →ₗ[A] N) (z : Words I M) :
    map f (differential B z) = differential B (map f z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | single L m => rw [map_single, differential_single, differential_single, map_evaluate]

#print axioms differential_squared
#print axioms map_differential

end Unimodular.FlagKoszul.CoefficientModuleBar
