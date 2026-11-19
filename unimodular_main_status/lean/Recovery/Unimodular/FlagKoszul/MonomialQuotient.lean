module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# The actual basis of a quotient by an upward closed monomial ideal

The quotient is the ordinary ideal quotient of the polynomial ring. Its
coefficient map retains exactly the exponents outside the specified upper set.
This supplies an explicit basis; no assertion about a quotient basis is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace Unimodular.FlagKoszul.MonomialQuotient

variable {E K : Type*} [CommRing K]

abbrev Exp (E : Type*) := E →₀ ℕ

abbrev Good (B : Set (Exp E)) := {u : Exp E // u ∉ B}

def ideal (B : Set (Exp E)) (hB : IsUpperSet B) : Ideal (MvPolynomial E K) :=
  MvPolynomial.restrictSupportIdeal K B hB

abbrev Quot (B : Set (Exp E)) (hB : IsUpperSet B) (K : Type*) [CommRing K] :=
  MvPolynomial E K ⧸ ideal B hB

def coefficients (B : Set (Exp E)) :
    MvPolynomial E K →ₗ[K] (Good B →₀ K) :=
  (Finsupp.lcomapDomain Subtype.val Subtype.val_injective).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

@[simp] theorem coefficients_apply (B : Set (Exp E)) (f : MvPolynomial E K)
    (u : Good B) : coefficients B f u = f.coeff u.1 := rfl

theorem coefficients_surjective (B : Set (Exp E)) :
    Function.Surjective (coefficients B (K := K)) := by
  intro f
  refine ⟨(AddMonoidAlgebra.coeffLinearEquiv K).symm (Finsupp.mapDomain Subtype.val f), ?_⟩
  change Finsupp.lcomapDomain (R := K) (M := K) Subtype.val Subtype.val_injective
    ((AddMonoidAlgebra.coeffLinearEquiv K)
      ((AddMonoidAlgebra.coeffLinearEquiv K).symm _)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.leftInverse_lcomapDomain_mapDomain (R := K) (M := K) _ Subtype.val_injective f

theorem mem_ideal_iff (B : Set (Exp E)) (hB : IsUpperSet B) (f : MvPolynomial E K) :
    f ∈ ideal B hB ↔ ∀ u ∈ f.support, u ∈ B := Iff.rfl

theorem kernel_coefficients (B : Set (Exp E)) (hB : IsUpperSet B) :
    (ideal B hB (K := K)).restrictScalars K = LinearMap.ker (coefficients B) := by
  ext f
  rw [Submodule.restrictScalars_mem, mem_ideal_iff, LinearMap.mem_ker]
  constructor
  · intro hf
    ext u
    change f.coeff u.1 = 0
    by_contra hu
    exact u.2 (hf u.1 (MvPolynomial.mem_support_iff.mpr hu))
  · intro hf u hu
    by_contra hub
    have hz := congrArg (fun z : Good B →₀ K => z ⟨u, hub⟩) hf
    exact (MvPolynomial.mem_support_iff.mp hu) hz

/-- The actual quotient is linearly equivalent to finitely supported coefficients
on the surviving monomials. -/
def repr (B : Set (Exp E)) (hB : IsUpperSet B) :
    Quot B hB K ≃ₗ[K] (Good B →₀ K) :=
  (Submodule.Quotient.restrictScalarsEquiv K (ideal B hB (K := K))).symm.trans
    ((Submodule.quotEquivOfEq
      ((ideal B hB (K := K)).restrictScalars K)
      (LinearMap.ker (coefficients B (K := K)))
      (kernel_coefficients B hB (K := K))).trans
      ((coefficients B (K := K)).quotKerEquivOfSurjective
        (coefficients_surjective B (K := K))))

@[simp] theorem repr_mk (B : Set (Exp E)) (hB : IsUpperSet B) (f : MvPolynomial E K) :
    repr B hB (Ideal.Quotient.mk (ideal B hB) f) = coefficients B f := rfl

/-- The basis consists literally of the classes of the surviving monomials. -/
def basis (B : Set (Exp E)) (hB : IsUpperSet B) :
    Module.Basis (Good B) K (Quot B hB K) where
  repr := repr B hB

theorem coefficients_monomial_good (B : Set (Exp E)) (u : Good B) (c : K) :
    coefficients B (MvPolynomial.monomial u.1 c) = Finsupp.single u c := by
  classical
  ext v
  simp only [coefficients_apply, MvPolynomial.coeff_monomial, Finsupp.single_apply]
  congr 1
  exact propext Subtype.ext_iff.symm

theorem coefficients_monomial_bad (B : Set (Exp E)) {u : Exp E} (hu : u ∈ B) (c : K) :
    coefficients B (MvPolynomial.monomial u c) = 0 := by
  classical
  ext v
  have huv : u ≠ v.1 := fun h => v.2 (h ▸ hu)
  simp [coefficients_apply, MvPolynomial.coeff_monomial, huv]

@[simp] theorem basis_apply (B : Set (Exp E)) (hB : IsUpperSet B) (u : Good B) :
    basis B hB (K := K) u = Ideal.Quotient.mk (ideal B hB) (MvPolynomial.monomial u.1 1) := by
  apply (repr B hB).injective
  change (basis B hB).repr ((basis B hB) u) = _
  rw [Module.Basis.repr_self, repr_mk, coefficients_monomial_good]

theorem monomial_eq_zero_of_bad (B : Set (Exp E)) (hB : IsUpperSet B)
    {u : Exp E} (hu : u ∈ B) (c : K) :
    Ideal.Quotient.mk (ideal B hB) (MvPolynomial.monomial u c) = 0 := by
  apply (repr B hB).injective
  rw [repr_mk, map_zero, coefficients_monomial_bad B hu]

#print axioms repr
#print axioms basis_apply
#print axioms monomial_eq_zero_of_bad

end Unimodular.FlagKoszul.MonomialQuotient

#check Unimodular.FlagKoszul.MonomialQuotient.basis_apply
