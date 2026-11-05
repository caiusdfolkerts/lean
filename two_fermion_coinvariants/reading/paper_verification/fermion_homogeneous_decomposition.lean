module

public import PaperVerification.FermionQuotientDegreeBasis
public import Mathlib.LinearAlgebra.DirectSum.Basis

/-!
# The actual direct-sum decomposition of a homogeneous quotient

The pieces are images of the original homogeneous spaces. Their collected
basis is compared with the genuine full quotient basis, proving that the
canonical sum of inclusions is bijective. No dimension statement is assumed.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.BasisFiltered

open scoped DirectSum Classical

variable {R M Q I E : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]

/-- A degree attached to each basis vector does not change the basis index set. -/
def degreeIndexEquiv (degree : E → ℕ) : (Σ d : ℕ,{e : E // degree e=d}) ≃ E where
  toFun x := x.2.val
  invFun e := ⟨degree e,⟨e,rfl⟩⟩
  left_inv := by rintro ⟨d,e,he⟩; cases he; rfl
  right_inv := fun _ ↦ rfl

/-- The direct-sum basis is the inclusion of the basis in the chosen summand. -/
theorem dfinsupp_basis_apply {D : Type*} [DecidableEq D] (V : D → Type*)
    [∀ d,AddCommMonoid (V d)] [∀ d,Module R (V d)] {η : D → Type*}
    (B : ∀ d,Module.Basis (η d) R (V d)) (x : Σ d,η d) :
    DFinsupp.basis B x=DirectSum.of V x.1 (B x.1 x.2) := by
  classical
  change DFinsupp.mapRange (fun d y ↦ (B d).repr.symm y)
    (fun d ↦ (B d).repr.symm.map_zero)
    (sigmaFinsuppEquivDFinsupp (Finsupp.single x (1 : R))) = _
  rw [sigmaFinsuppEquivDFinsupp_single,DFinsupp.mapRange_single,
    Module.Basis.repr_symm_single_one]
  apply DFinsupp.ext
  intro d
  by_cases hd : d=x.1
  · subst d
    simp only [DFinsupp.single_eq_same,DirectSum.of_eq_same]
  · simp only [DFinsupp.single_eq_of_ne hd,DirectSum.of_eq_of_ne _ _ _ hd]

variable [Fintype E]
  (b : Module.Basis I R M) (w : I → ℕ)
  (q : M →ₗ[R] Q) (B : Module.Basis E R Q) (v : E → M) (degree : E → ℕ)
  (hv : ∀ e,Homogeneous b w (degree e) (v e)) (hB : ∀ e,q (v e)=B e)
  (hker : ∀ d x,x ∈ q.ker → component b w d x ∈ q.ker)

/-- An equivalence built from the actual homogeneous quotient bases. Its
underlying map is proved below to be the sum of the original inclusions. -/
def homogeneousQuotientDecomposition :
    (⨁ d : ℕ,(homogeneousPiece b w d).map q) ≃ₗ[R] Q :=
  (DFinsupp.basis (fun d ↦ quotientPieceBasis b w q B v degree hv hB hker d)).equiv
    B (degreeIndexEquiv degree)

theorem homogeneousQuotientDecomposition_toLinearMap :
    (homogeneousQuotientDecomposition b w q B v degree hv hB hker).toLinearMap =
      DirectSum.coeLinearMap (fun d ↦ (homogeneousPiece b w d).map q) := by
  classical
  apply (DFinsupp.basis (fun d ↦ quotientPieceBasis b w q B v degree hv hB hker d)).ext
  rintro ⟨d,e⟩
  change homogeneousQuotientDecomposition b w q B v degree hv hB hker
    (DFinsupp.basis (fun d ↦ quotientPieceBasis b w q B v degree hv hB hker d) ⟨d,e⟩) = _
  rw [homogeneousQuotientDecomposition,Module.Basis.equiv_apply,dfinsupp_basis_apply]
  dsimp only [Prod.fst,Prod.snd]
  simpa only [quotientPieceBasis_coe, degreeIndexEquiv, Equiv.coe_fn_mk] using
    (DirectSum.coeLinearMap_of (R := R)
      (fun d ↦ (homogeneousPiece b w d).map q) d
      (quotientPieceBasis b w q B v degree hv hB hker d e)).symm

include hv hB hker in
/-- The original quotient is the internal direct sum of its actual homogeneous
images, over an arbitrary coefficient ring. -/
theorem homogeneousQuotient_isInternal :
    DirectSum.IsInternal (fun d ↦ (homogeneousPiece b w d).map q) := by
  have h := (homogeneousQuotientDecomposition b w q B v degree hv hB hker).bijective
  rwa [← LinearEquiv.coe_toLinearMap,homogeneousQuotientDecomposition_toLinearMap] at h

end PaperVerification.Fermion.BasisFiltered
