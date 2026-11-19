module

public import PaperVerification.AlternatingFormsBooleanDuality
public import PaperVerification.AlternatingFormsEvenDeterminantMultiaffine

/-!
# Determinant families give lower bounds for the actual Boolean quotient

The nonzero coefficient minor proves independence of the original polynomial
vectors.  Their degree, multiaffinity, and derivative identities then place
them in the concrete polynomial dual of the quotient.  This is the required
bridge from determinant constructions to quotient dimensions.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.EvenDeterminants

open scoped BigOperators
open BooleanQuotient PolynomialMinors

variable {K τ ι : Type*} [Field K] [Fintype τ] [Fintype ι] [DecidableEq ι]

theorem determinantProduct_mem_jointDerivativeKernel (m q : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m)
    (hdegree : ∑ a, r a = q)
    (hdisjoint : Function.Injective (fun p : (a : τ) × Fin (2 * r a + 1) => I p.1 p.2))
    (b c : Fin m → K) :
    determinantProduct m r I b c ∈ jointDerivativeKernel b c q := by
  apply (mem_jointDerivativeKernel_iff b c q _).mpr
  have hhom := determinantProduct_homogeneous m r I b c
  rw [hdegree] at hhom
  exact ⟨hhom, determinantProduct_degreeOf_le_one m r I hdisjoint b c,
    determinantProduct_joint_kernel m r I b c⟩

/-- A nonzero coefficient minor of a disjoint-odd-subset determinant family
bounds the dimension of the ordinary square-zero quotient from below. -/
theorem card_le_finrank_booleanPiece_of_coefficient_det_ne_zero
    (m q : ℕ) (r : ι → τ → ℕ)
    (I : (w : ι) → (a : τ) → Fin (2 * r w a + 1) → Fin m)
    (hdegree : ∀ w, ∑ a, r w a = q)
    (hdisjoint : ∀ w, Function.Injective
      (fun p : (a : τ) × Fin (2 * r w a + 1) => I w p.1 p.2))
    (b c : Fin m → K) (e : ι → Fin m →₀ ℕ)
    (hdet : (coefficientMatrix e (fun w => determinantProduct m (r w) (I w) b c)).det ≠ 0) :
    Fintype.card ι ≤ Module.finrank K (piece b c q) := by
  apply card_le_finrank_piece_of_linearIndependent b c q
    (fun w => determinantProduct m (r w) (I w) b c)
  · intro w
    exact determinantProduct_mem_jointDerivativeKernel m q (r w) (I w)
      (hdegree w) (hdisjoint w) b c
  · exact linearIndependent_of_coefficient_det_ne_zero e _ hdet

end PaperVerification.AlternatingForms.EvenDeterminants
