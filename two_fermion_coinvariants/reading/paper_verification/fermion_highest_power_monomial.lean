module

public import PaperVerification.FermionDefinitions

/-!
# Highest-power condition for a monomial

This elementary lemma is shared by the weighted homogenized family and
by the local ramification factors. Its statement and proof are unchanged
from the former location in `FermionHomogenizedFamily`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial
variable {R : Type*} [CommRing R] {n : ℕ}

theorem highestPower_X_pow (r : Fin n → ℕ) (i : Fin n) (e : ℕ) :
    HasHighestPower r (X i^e : PolynomialRing R n) i e := by
  rw [X_pow_eq_monomial]
  refine ⟨by simp,?_⟩
  intro a ha hne
  have hz : (monomial (Finsupp.single i e) (1 : R)).coeff a=0 := by
    rw [coeff_monomial,if_neg hne.symm]
  exact False.elim ((mem_support_iff.mp ha) hz)

end PaperVerification.Fermion
