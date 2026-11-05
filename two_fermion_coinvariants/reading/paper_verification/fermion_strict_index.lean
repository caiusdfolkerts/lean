module

public import PaperVerification.FermionStrictDescent
public import PaperVerification.FermionPairedIndex

/-!
# Exact original strict monomials over every coefficient ring

The nonnegative prefix-cardinality formulation is equivalent to the paper's
integer arrival heights. A rectangle containing an exponent automatically
has strictly positive arrival height at every step. The exterior order is
the original increasing theta order followed by increasing xi order.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators TensorProduct

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionStrictIndex_localInst_1 : DecidableEq (Fin n ⊕ Fin n) :=
  (interleavedOddOrder n).toDecidableEq

theorem wordHeight_arrival_cast (T S : Finset (Fin n))
    (h : ValidWord (T.disjSum S)) (i : Fin n) :
    (wordHeight (T.disjSum S) (i.val+1) : ℤ)=height T S i := by
  rw [height_eq_prefix_card,wordHeight,Nat.cast_sub (h (i.val+1) (Nat.succ_le_of_lt i.isLt))]
  push_cast
  rfl

theorem strictWordBoxBounds_disjSum_cast (r : Fin n → ℕ) (T S : Finset (Fin n))
    (h : ValidWord (T.disjSum S)) (i : Fin n) :
    (strictWordBoxBounds r (T.disjSum S) i : ℤ)=(r i : ℤ)*height T S i := by
  rw [strictWordBoxBounds,Nat.cast_mul,wordHeight_arrival_cast T S h i]

def strictIndexToPower (d : StrictData (K := R) (n := n)) (z : StrictIndex d) :
    StrictPowerIndex d.r := by
  let W := z.val.1.1.disjSum z.val.1.2
  have hW : ValidWord W := (validWord_disjSum_iff _ _).mpr
    (fun i ↦ le_trans (by decide : (0 : ℤ)≤1) (z.property.1 i))
  refine ⟨W,⟨⟨Finsupp.equivFunOnFinite.symm z.val.2,?_⟩,hW⟩⟩
  intro i
  have hi := z.property.2 i
  rw [←strictWordBoxBounds_disjSum_cast d.r _ _ hW i] at hi
  exact_mod_cast hi

def strictPowerToIndex (d : StrictData (K := R) (n := n)) (z : StrictPowerIndex d.r) :
    StrictIndex d := by
  have hW : ValidWord (z.1.toLeft.disjSum z.1.toRight) := by
    rw [Finset.toLeft_disjSum_toRight]
    exact z.2.property
  have hstrict := strictWord_of_polynomialIndex d.r z.1 z.2
  refine ⟨((z.1.toLeft,z.1.toRight),fun i ↦ z.2.val.val i),?_,?_⟩
  · intro i
    rw [←wordHeight_arrival_cast _ _ hW i,Finset.toLeft_disjSum_toRight]
    have hh := hstrict (i.val+1) (Nat.succ_pos _) (Nat.succ_le_of_lt i.isLt)
    have hp : 1≤wordHeight z.1 (i.val+1) := by unfold wordHeight; omega
    exact_mod_cast hp
  · intro i
    rw [←strictWordBoxBounds_disjSum_cast d.r _ _ hW i,Finset.toLeft_disjSum_toRight]
    exact_mod_cast z.2.val.property i

private theorem strictPowerIndex_ext {r : Fin n → ℕ}
    {a b : StrictPowerIndex r} (hW : a.1 = b.1)
    (he : a.2.val.val = b.2.val.val) : a = b := by
  rcases a with ⟨W, ⟨⟨e, he'⟩, hW'⟩⟩
  rcases b with ⟨U, ⟨⟨f, hf'⟩, hU'⟩⟩
  dsimp at hW he
  subst U
  subst f
  rfl

def strictIndexEquiv (d : StrictData (K := R) (n := n)) :
    StrictIndex d ≃ StrictPowerIndex d.r where
  toFun := strictIndexToPower d
  invFun := strictPowerToIndex d
  left_inv z := by
    apply Subtype.ext
    simp only [strictIndexToPower,strictPowerToIndex,Finset.toLeft_disjSum,
      Finset.toRight_disjSum,Finsupp.coe_equivFunOnFinite_symm]
  right_inv z := by
    rcases z with ⟨W,⟨⟨e,he⟩,hW⟩⟩
    apply strictPowerIndex_ext
    · exact Finset.toLeft_disjSum_toRight
    · exact Finsupp.equivFunOnFinite_symm_coe e

-- Actual basis monomials put every theta generator before every xi generator.
local instance FermionStrictIndex_localInst_2 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
local instance FermionStrictIndex_localInst_3 : PartialOrder (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toPartialOrder
local instance FermionStrictIndex_localInst_4 : Preorder (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toPreorder
local instance FermionStrictIndex_localInst_5 : LE (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toLE
local instance FermionStrictIndex_localInst_6 : LT (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toLT
local instance FermionStrictIndex_localInst_7 : DecidableEq (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toDecidableEq

@[simp] theorem strictCoupledClasses_indexEquiv (d : StrictData (K := R) (n := n))
    (z : StrictIndex d) : strictCoupledClasses d (strictIndexEquiv d z)=strictClasses d z := by
  rw [strictClasses,boxMonomial_eq_tensor]
  rfl

def strictPaperBasis (d : StrictData (K := R) (n := n)) :
    Module.Basis (StrictIndex d) R (StrictQuotient d.beta d.phi) :=
  (strictArbitraryRingBasis d).reindex (strictIndexEquiv d).symm

@[simp] theorem strictPaperBasis_apply (d : StrictData (K := R) (n := n))
    (z : StrictIndex d) : strictPaperBasis d z=strictClasses d z := by
  rw [strictPaperBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    strictArbitraryRingBasis_apply,strictCoupledClasses_indexEquiv]

/-- The exact frozen statement of the original strict basis clause, with
all coupled coefficients and every original commutative base ring. -/
theorem strict_basis_claim (d : StrictData (K := R) (n := n)) : StrictBasisClaim d := by
  have he : (strictPaperBasis d : StrictIndex d → StrictQuotient d.beta d.phi)=
      strictClasses d := funext (strictPaperBasis_apply d)
  constructor
  · rw [←he]
    exact (strictPaperBasis d).linearIndependent
  · rw [←he]
    exact (strictPaperBasis d).span_eq

end PaperVerification.Fermion
