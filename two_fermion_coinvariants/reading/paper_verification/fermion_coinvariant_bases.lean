module

public import PaperVerification.FermionCoinvariantMoments
public import PaperVerification.FermionTheoremOneOne
public import PaperVerification.FermionTheoremOneTwo

/-!
# Literal bases of the genuine invariant-theoretic quotients

The full invariant-generated ideals were
identified with the original moment ideals before these basis transports.
The comparison maps fix every original polynomial/exterior representative.
The displayed arrival bounds, all covering degrees and positive
characteristic hypotheses are retained.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion.Coinvariants

open MvPolynomial Exterior

variable {R : Type*} [CommRing R] {n r a : ℕ}

local instance coinvariantBasisOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem allowedWeights_one (hfac : IsUnit (n.factorial : R)) :
    AllowedWeights (fun _ : Fin n ↦ (1 : R)) := by
  refine ⟨hfac,?_⟩
  intro U hU
  have hpos : 0<U.card := Finset.card_pos.mpr hU
  have hle : U.card≤n := by simpa only [Fintype.card_fin] using U.card_le_univ
  have hu : IsUnit (U.card : R) :=
    isUnit_of_dvd_unit (map_dvd (Nat.castRingHom R) (Nat.dvd_factorial hpos hle)) hfac
  simpa only [Finset.sum_const,nsmul_one] using hu

def oppositePowerData (hn : 0<n) (hr : 0<r) (ha : a≤r)
    (hfac : IsUnit (n.factorial : R)) : PairedData (K := R) (n := n) where
  positive_n := hn
  s := 1
  positive_s := Nat.zero_lt_one
  r := fun _ ↦ r
  u := fun _ ↦ a
  v := fun _ ↦ r-a
  positive_r := fun _ ↦ hr
  degree_split := fun _ ↦ by simpa only [Nat.mul_one] using Nat.add_sub_of_le ha
  beta := fun _ ↦ 1
  allowed_weights := allowedWeights_one hfac
  phi := fun i ↦ X i^r
  a := fun i ↦ X i^a
  b := fun i ↦ X i^(r-a)
  highest_phi := fun i ↦ highestPower_X_pow _ i _
  highest_a := fun i ↦ highestPower_X_pow _ i _
  highest_b := fun i ↦ highestPower_X_pow _ i _

def trivialColorPowerData (hn : 0<n) (hr : 0<r)
    (hfac : IsUnit (n.factorial : R)) : StrictData (K := R) (n := n) where
  positive_n := hn
  r := fun _ ↦ r
  positive_r := fun _ ↦ hr
  beta := fun _ ↦ 1
  allowed_weights := allowedWeights_one hfac
  phi := fun i ↦ X i^r
  highest_phi := fun i ↦ highestPower_X_pow _ i _

/-- This is exactly the bound in equation(20), including both marked colors
and the arrival height after the current index. -/
theorem oppositePowerData_bound (hn : 0<n) (hr : 0<r) (ha : a≤r)
    (hfac : IsUnit (n.factorial : R)) (T S : Finset (Fin n)) (i : Fin n) :
    pairedBound (oppositePowerData hn hr ha hfac) T S i=
      (r : ℤ)*height T S i+(if i∈T then (r-a : ℕ) else 0)+
        (if i∈S then a else 0) := by
  rw [height_eq_previousHeight]
  simp only [pairedBound,oppositePowerData,marks,Nat.cast_one,Nat.cast_add]
  have hsub : ((r-a : ℕ) : ℤ)=(r : ℤ)-(a : ℤ) := Nat.cast_sub ha
  split_ifs <;> simp only [Nat.cast_zero,Nat.cast_one,hsub] <;> ring

section Field

variable {F : Type*} [Field F]

def oppositeCoinvariantBasis (hn : 0<n) (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    Module.Basis (PairedIndex (oppositePowerData hn hr har.le hfac)) F
      (CoinvariantAlgebra (R := F) (n := n) (r := r) a (r-a)) :=
  (pairedPaperBasis (oppositePowerData hn hr har.le hfac)).map
    (oppositeCoinvariantEquiv hr ha har hfac ζ hζ).symm.toLinearEquiv

theorem oppositeCoinvariantBasis_apply (hn : 0<n) (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (z : PairedIndex (oppositePowerData hn hr har.le hfac)) :
    oppositeCoinvariantBasis hn hr ha har hfac ζ hζ z=
      ((boxMonomial z.val.1.1 z.val.1.2 z.val.2 : SuperRing F n) :
        CoinvariantAlgebra (R := F) (n := n) (r := r) a (r-a)) := by
  let e := oppositeCoinvariantEquiv hr ha har hfac ζ hζ
  change e.symm (pairedPaperBasis (oppositePowerData hn hr har.le hfac) z)=_
  apply e.injective
  rw [AlgEquiv.apply_symm_apply,pairedPaperBasis_apply]
  rfl

theorem oppositeCoinvariant_finrank (hn : 0<n) (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    Module.finrank F (CoinvariantAlgebra (R := F) (n := n) (r := r) a (r-a))=
      (2*r)^n*n.factorial := by
  rw [(oppositeCoinvariantEquiv hr ha har hfac ζ hζ).toLinearEquiv.finrank_eq]
  change Module.finrank F
    (PairedQuotient (oppositePowerData hn hr har.le hfac).beta
      (oppositePowerData hn hr har.le hfac).phi
      (oppositePowerData hn hr har.le hfac).a
      (oppositePowerData hn hr har.le hfac).b)=_
  rw [paired_finrank]
  simp only [oppositePowerData,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Nat.one_ascFactorial,Nat.mul_pow]

def trivialColorCoinvariantBasis (hn : 0<n) (hr : 0<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    Module.Basis (StrictIndex (trivialColorPowerData hn hr hfac)) F
      (CoinvariantAlgebra (R := F) (n := n) (r := r) 0 0) :=
  (strictPaperBasis (trivialColorPowerData hn hr hfac)).map
    (trivialColorCoinvariantEquiv hr hfac ζ hζ).symm.toLinearEquiv

theorem trivialColorCoinvariantBasis_apply (hn : 0<n) (hr : 0<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (z : StrictIndex (trivialColorPowerData hn hr hfac)) :
    trivialColorCoinvariantBasis hn hr hfac ζ hζ z=
      ((boxMonomial z.val.1.1 z.val.1.2 z.val.2 : SuperRing F n) :
        CoinvariantAlgebra (R := F) (n := n) (r := r) 0 0) := by
  let e := trivialColorCoinvariantEquiv hr hfac ζ hζ
  change e.symm (strictPaperBasis (trivialColorPowerData hn hr hfac) z)=_
  apply e.injective
  rw [AlgEquiv.apply_symm_apply,strictPaperBasis_apply]
  rfl

theorem trivialColorCoinvariant_finrank (hn : 0<n) (hr : 0<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    Module.finrank F (CoinvariantAlgebra (R := F) (n := n) (r := r) 0 0)=
      r^n*2^(n-1)*n.factorial := by
  rw [(trivialColorCoinvariantEquiv hr hfac ζ hζ).toLinearEquiv.finrank_eq]
  change Module.finrank F
    (StrictQuotient (trivialColorPowerData hn hr hfac).beta
      (trivialColorPowerData hn hr hfac).phi)=_
  rw [strict_finrank]
  simp only [trivialColorPowerData,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

end Field

/-- The type-A basis over arbitrary coefficient rings is obtained without
passing to a field or assuming semisimplicity. -/
def typeACoinvariantBasis (hn : 0<n) (hfac : IsUnit (n.factorial : R)) :
    Module.Basis (StrictIndex (trivialColorPowerData hn (by decide : 0<1) hfac)) R
      (CoinvariantAlgebra (R := R) (n := n) (r := 1) 0 0) := by
  let e : CoinvariantAlgebra (R := R) (n := n) (r := 1) 0 0 ≃ₐ[R]
      StrictQuotient (fun _ : Fin n ↦ (1 : R)) (fun i ↦ (X i)^1) :=
    quotientEquivOfIdealEq ((positiveInvariantIdeal_eq_blockIdeal_typeA hfac).trans
      (blockIdeal_eq_strictIdeal (by decide : 0<1)))
  exact (strictPaperBasis (trivialColorPowerData hn (by decide : 0<1) hfac)).map
    e.symm.toLinearEquiv

end PaperVerification.Fermion.Coinvariants
