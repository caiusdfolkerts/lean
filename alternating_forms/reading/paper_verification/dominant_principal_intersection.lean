module

public import PaperVerification.AlternatingFormsOrbitGenericity

/-!
# A dominant orbit meets every nonempty principal open

This supplies the precise existence step needed to combine an explicit
surjective orbit Jacobian with a generic geometric property.  It requires
neither an orbit-classification theorem nor algebraic closedness.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial

variable {K σ ι : Type*} [CommRing K] [IsDomain K] [Infinite K]
  [Fintype σ] [Finite ι]

/-- Every nonempty target principal open meets the image of a nonempty
source principal open under a polynomial parametrization with a surjective Jacobian. -/
theorem exists_dominant_principal_intersection
    (p : ι → MvPolynomial σ K) (v : σ → K)
    (hJ : (TauCeti.jacobiMatrixAt p v).mulVec.Surjective)
    (g : MvPolynomial σ K) (hg : g ≠ 0)
    (q : MvPolynomial ι K) (hq : q ≠ 0) :
    ∃ x : σ → K, eval x g ≠ 0 ∧
      eval (fun i => eval x (p i)) q ≠ 0 := by
  by_contra h
  apply hq
  apply polynomial_eq_zero_of_dominant_open_vanish hJ hg
  intro x hx
  by_contra hqx
  exact h ⟨x,hx,hqx⟩

end PaperVerification.AlternatingForms
