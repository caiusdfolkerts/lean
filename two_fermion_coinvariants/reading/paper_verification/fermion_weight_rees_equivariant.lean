module

public import PaperVerification.FermionWeightReesFiltration
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Automorphisms of the actual Laurent Rees subalgebra

Coefficientwise extension fixes the Laurent parameter. An automorphism
preserving the independently given filtration therefore restricts to the
actual Rees subalgebra. The group law and the coefficient formula remain
literal, so this construction supplies equivariance of the family itself.

-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators LaurentPolynomial PaperVerification.Fermion.WeightRees

namespace PaperVerification.Fermion.WeightRees

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A] [Fintype I]

def parameterLaurentEquiv (e : A ≃ₐ[K] A) :
    LaurentPolynomial A ≃ₐ[Polynomial K] LaurentPolynomial A where
  __ := (AddMonoidAlgebra.mapAlgEquiv K ℤ e).toRingEquiv
  commutes' p := by
    change AddMonoidAlgebra.mapAlgHom ℤ e.toAlgHom (parameterMap K A p)=parameterMap K A p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,hp,hq]
    | monomial r c =>
        rw [parameterMap_monomial,AddMonoidAlgebra.mapAlgHom_single]
        exact congrArg (AddMonoidAlgebra.single (r : ℤ)) (e.commutes c)

@[simp] theorem parameterLaurentEquiv_coeff (e : A ≃ₐ[K] A)
    (z : LaurentPolynomial A) (r : ℤ) :
    (parameterLaurentEquiv e z).coeff r=e (z.coeff r) :=
  AddMonoidAlgebra.coeff_mapAlgHom e.toAlgHom z r

@[simp] theorem parameterLaurentEquiv_symm_coeff (e : A ≃ₐ[K] A)
    (z : LaurentPolynomial A) (r : ℤ) :
    ((parameterLaurentEquiv e).symm z).coeff r=e.symm (z.coeff r) :=
  AddMonoidAlgebra.coeff_mapAlgHom e.symm.toAlgHom z r

variable (b : Module.Basis I K A) (weight : I → ℕ) (hmul : Multiplicative b weight)

/-- The premise concerns the original, independently defined basis filtration. -/
def filtrationEquiv (e : A ≃ₐ[K] A)
    (he : ∀ r x, e x ∈ BlockInitial.lowerSubmodule b weight r ↔
      x ∈ BlockInitial.lowerSubmodule b weight r) :
    algebra b weight hmul ≃ₐ[Polynomial K] algebra b weight hmul where
  toFun z := ⟨parameterLaurentEquiv e z,by
    have hz := z.property
    rw [mem_algebra_iff_filtration] at hz ⊢
    intro r
    rw [parameterLaurentEquiv_coeff]
    exact (he _ _).mpr (hz r)⟩
  invFun z := ⟨(parameterLaurentEquiv e).symm z,by
    have hz := z.property
    rw [mem_algebra_iff_filtration] at hz ⊢
    intro r
    rw [parameterLaurentEquiv_symm_coeff]
    apply (he _ _).mp
    rw [e.apply_symm_apply]
    exact hz r⟩
  left_inv z := by
    apply Subtype.ext
    exact (parameterLaurentEquiv e).symm_apply_apply z
  right_inv z := by
    apply Subtype.ext
    exact (parameterLaurentEquiv e).apply_symm_apply z
  map_mul' x y := Subtype.ext ((parameterLaurentEquiv e).map_mul x y)
  map_add' x y := Subtype.ext ((parameterLaurentEquiv e).map_add x y)
  commutes' p := Subtype.ext ((parameterLaurentEquiv e).commutes p)

@[simp] theorem filtrationEquiv_coeff (e : A ≃ₐ[K] A)
    (he : ∀ r x, e x ∈ BlockInitial.lowerSubmodule b weight r ↔
      x ∈ BlockInitial.lowerSubmodule b weight r)
    (z : algebra b weight hmul) (r : ℤ) :
    ((filtrationEquiv b weight hmul e he z : algebra b weight hmul) :
      LaurentPolynomial A).coeff r=e ((z : LaurentPolynomial A).coeff r) :=
  parameterLaurentEquiv_coeff e z r

variable {G : Type*} [Monoid G]

/-- Every filtration-preserving action extends to the actual Rees algebra,
with parameter fixed and original coefficient action unchanged. -/
def filtrationAction (rho : G →* (A ≃ₐ[K] A))
    (hrho : ∀ g r x, rho g x ∈ BlockInitial.lowerSubmodule b weight r ↔
      x ∈ BlockInitial.lowerSubmodule b weight r) :
    G →* (algebra b weight hmul ≃ₐ[Polynomial K] algebra b weight hmul) where
  toFun g := filtrationEquiv b weight hmul (rho g) (hrho g)
  map_one' := by
    apply AlgEquiv.ext
    intro z
    apply Subtype.ext
    apply LaurentPolynomial.ext
    intro r
    simp only [filtrationEquiv_coeff,map_one,AlgEquiv.one_apply]
  map_mul' g h := by
    apply AlgEquiv.ext
    intro z
    apply Subtype.ext
    apply LaurentPolynomial.ext
    intro r
    simp only [AlgEquiv.mul_apply,filtrationEquiv_coeff,map_mul]

end PaperVerification.Fermion.WeightRees
