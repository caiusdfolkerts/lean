module

public import PaperVerification.FermionTypeAMultiplicity
public import PaperVerification.FermionStrictWeightReesFibers
public import Mathlib.Algebra.DirectSum.Module

/-!
# The actual initial quotient and its multiplicity coefficient modules

The map takes literal exterior coefficients and reduces each polynomial modulo
its actual colon ideal. Its kernel is proved to be the initial relation ideal,
and surjectivity is proved by choosing polynomial representatives. Regrouping
by multiplicity therefore gives a linear equivalence of the actual quotient
with the finite direct sum of its coefficient-quotient coloring modules.

The further identification
of the coloring modules with tensor products of exterior powers, together with
equivariance of that identification, is a separate obligation.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion.TypeA

open scoped BigOperators DirectSum

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

local instance FermionMultiplicityQuotientDecomposition_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective

abbrev CoefficientQuotient (m : MultiplicityVector n) :=
  PolynomialRing F n ⧸ coefficientIdeal (F := F) m

/-- A separate, literal coefficient quotient for every exterior word. -/
def coefficientProjection : SuperRing F n →ₗ[F]
    ((T : Finset (OddIndex n)) → CoefficientQuotient (F := F) (wordMultiplicityVector T)) :=
  LinearMap.pi fun T ↦
    ((Ideal.Quotient.mkₐ F (coefficientIdeal (wordMultiplicityVector T))).toLinearMap).comp
      (((superPolynomialBasis (K := F)).coord T).restrictScalars F)

@[simp] theorem coefficientProjection_apply (z : SuperRing F n) (T : Finset (OddIndex n)) :
    coefficientProjection z T =
      Ideal.Quotient.mk (coefficientIdeal (wordMultiplicityVector T))
        ((superPolynomialBasis (K := F)).repr z T) := rfl

theorem coefficientProjection_surjective :
    Function.Surjective (coefficientProjection (F := F) (n := n)) := by
  classical
  intro y
  choose p hp using fun T ↦ Ideal.Quotient.mk_surjective (y T)
  refine ⟨(superPolynomialBasis (K := F)).equivFun.symm p,?_⟩
  funext T
  rw [coefficientProjection_apply]
  have hrepr : (superPolynomialBasis (K := F)).repr
      ((superPolynomialBasis (K := F)).equivFun.symm p) T=p T := by
    rw [←Module.Basis.equivFun_apply,LinearEquiv.apply_symm_apply]
  rw [hrepr]
  exact hp T

/-- The kernel equality uses the previously proved, literal equation (21). -/
theorem coefficientProjection_kernel (hn : 0<n) :
    (coefficientProjection (F := F) (n := n)).ker =
      (strictInitialProjection (data (F := F) hn)).toLinearMap.ker := by
  rw [strictInitialProjection,quotient_kernel_eq_twoSidedIdealSubmodule]
  ext z
  change coefficientProjection z=0 ↔ z∈initialIdeal hn
  rw [equation_21]
  constructor
  · intro hz T
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact congrFun hz T
  · intro hz
    funext T
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hz T)

/-- A canonical coefficient description of the actual initial algebra as a
vector space. No quotient dimension or desired decomposition is assumed. -/
def initialCoefficientEquiv (hn : 0<n) :
    StrictMultiplicityInitialQuotient (data (F := F) hn) ≃ₗ[F]
      ((T : Finset (OddIndex n)) → CoefficientQuotient (F := F) (wordMultiplicityVector T)) :=
  ((strictInitialProjection (data (F := F) hn)).toLinearMap.quotKerEquivOfSurjective
      ((strictMultiplicityInitialIdeal (data (F := F) hn)).ringCon.mkₐ_surjective
        (α := F))).symm |>.trans
    ((Submodule.quotEquivOfEq _ _ (coefficientProjection_kernel (F := F) hn).symm).trans
      ((coefficientProjection (F := F) (n := n)).quotKerEquivOfSurjective
        coefficientProjection_surjective))

@[simp] theorem initialCoefficientEquiv_mk (hn : 0<n) (z : SuperRing F n) :
    initialCoefficientEquiv hn (strictInitialProjection (data hn) z)=
      coefficientProjection z := by
  change initialCoefficientEquiv hn
    ((strictInitialProjection (data hn)).toLinearMap z)=coefficientProjection z
  simp only [initialCoefficientEquiv,LinearEquiv.trans_apply]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply
    (f := (strictInitialProjection (data (F := F) hn)).toLinearMap)
    ((strictMultiplicityInitialIdeal (data (F := F) hn)).ringCon.mkₐ_surjective (α := F)) z]
  simp only [Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Regrouping all exterior words retains every coloring, including zero
coefficient quotients attached to inadmissible multiplicities. -/
def regroupCoefficientEquiv :
    ((T : Finset (OddIndex n)) → CoefficientQuotient (F := F) (wordMultiplicityVector T))
      ≃ₗ[F] ((m : MultiplicityVector n) → MultiplicityColoring m → CoefficientQuotient (F := F) m) where
  toFun y m T :=
    Ideal.quotientEquivAlgOfEq F (congrArg (coefficientIdeal (F := F)) T.property) (y T.val)
  invFun y T := y (wordMultiplicityVector T) ⟨T,rfl⟩
  left_inv y := by
    funext T
    change Ideal.quotientEquivAlgOfEq F rfl (y T)=y T
    obtain ⟨p,hp⟩ := Ideal.Quotient.mk_surjective (y T)
    rw [←hp,Ideal.quotientEquivAlgOfEq_mk]
  right_inv y := by
    funext m T
    rcases T with ⟨T,hT⟩
    subst m
    change Ideal.quotientEquivAlgOfEq F rfl
      (y (wordMultiplicityVector T) ⟨T,rfl⟩)=y (wordMultiplicityVector T) ⟨T,rfl⟩
    obtain ⟨p,hp⟩ := Ideal.Quotient.mk_surjective (y (wordMultiplicityVector T) ⟨T,rfl⟩)
    rw [←hp,Ideal.quotientEquivAlgOfEq_mk]
  map_add' x y := by
    funext m T
    exact map_add (Ideal.quotientEquivAlgOfEq F
      (congrArg (coefficientIdeal (F := F)) T.property)) (x T.val) (y T.val)
  map_smul' a y := by
    funext m T
    exact map_smul (Ideal.quotientEquivAlgOfEq F
      (congrArg (coefficientIdeal (F := F)) T.property)) a (y T.val)

/-- The exact direct-sum decomposition of the actual initial quotient into
literal polynomial colon quotients, one copy per exterior coloring. -/
def initialMultiplicityDirectSumEquiv (hn : 0<n) :
    StrictMultiplicityInitialQuotient (data (F := F) hn) ≃ₗ[F]
      ⨁ m : MultiplicityVector n,
        (MultiplicityColoring m → CoefficientQuotient (F := F) m) :=
  ((initialCoefficientEquiv hn).trans (regroupCoefficientEquiv (F := F))).trans
    (DirectSum.linearEquivFunOnFintype F (MultiplicityVector n)
      (fun m ↦ MultiplicityColoring m → CoefficientQuotient (F := F) m)).symm

end PaperVerification.Fermion.TypeA
