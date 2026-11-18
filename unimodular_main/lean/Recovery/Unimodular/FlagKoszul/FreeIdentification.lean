module

public import Recovery.Unimodular.FlagKoszul.CoefficientModuleBar

/-! The coefficient-module construction recovers the actual free bar differential. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Unimodular.FlagKoszul.CoefficientModuleBar

open PaperVerification.NoncommutativeBar

variable {K A I : Type*} [CommRing K] [CommRing A] [Algebra K A]

@[simp] theorem evaluate_self (z : Words I A) (a : A) : evaluate z a = a • z := by
  ext L
  simp only [evaluate_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- No new free resolution is introduced by extending the coefficients. -/
theorem differential_self (B : Module.Basis (Option I) K A) :
    differential (M := A) B = PaperVerification.NoncommutativeBar.differential B := by
  apply Finsupp.lhom_ext
  intro L a
  rw [differential_single, evaluate_self, ← map_smul]
  congr 1
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

#print axioms differential_self

end Unimodular.FlagKoszul.CoefficientModuleBar
