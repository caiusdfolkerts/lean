module

public import PaperVerification.FermionCoinvariantHilbert
public import Mathlib.Data.Nat.Factorial.NatCast

/-!
# The literal characteristic and type-A/type-B specializations

This file discharges the unit hypotheses from the characteristic assumptions
in Section 8.1 and records the values of the original invariant-theoretic
bases. Every quotient here is defined from the original wreath action.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion.Coinvariants

open MvPolynomial Exterior

variable {R : Type*} [CommRing R] {n : ℕ}

local instance coinvariantApplicationsOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- The positive invariant ideal for the literal symmetric-group action. -/
def positivePermutationInvariantIdeal : TwoSidedIdeal (SuperRing R n) :=
  TwoSidedIdeal.span {f | augmentation f=0 ∧
    ∀ σ : Equiv.Perm (Fin n),permutation σ f=f}

/-- At covering degree one the wreath-group definition is exactly the
original symmetric-group invariant ideal. This comparison uses only the
actual group actions, independently of any moment theorem. -/
theorem typeA_positiveInvariantIdeal_eq_permutation :
    positiveInvariantIdeal (R := R) (n := n) (r := 1) 0 0=
      positivePermutationInvariantIdeal := by
  unfold positiveInvariantIdeal positivePermutationInvariantIdeal
  congr 1
  ext f
  constructor
  · rintro ⟨hzero,hfixed⟩
    exact ⟨hzero,wreath_invariant_permutation hfixed⟩
  · rintro ⟨hzero,hfixed⟩
    refine ⟨hzero,?_⟩
    intro g
    change diagonal 0 0 (fun i ↦ (g.left i : Rˣ)) (permutation g.right f)=f
    rw [hfixed]
    have hc : (fun i ↦ (g.left i : Rˣ))=(1 : Fin n→Rˣ) := by
      funext i
      apply Units.ext
      simpa only [pow_one,Pi.one_apply,Units.val_one] using
        (root_pow_eq_one_of_dvd (g.left i) (dvd_refl 1))
    rw [hc,diagonal_one,AlgEquiv.one_apply]

/-- The type-A basis consists of the actual residue classes of the printed
monomials, over any commutative ring in which `n!` is a unit. -/
theorem typeACoinvariantBasis_apply (hn : 0<n) (hfac : IsUnit (n.factorial : R))
    (z : StrictIndex (trivialColorPowerData hn (by decide : 0<1) hfac)) :
    typeACoinvariantBasis hn hfac z=
      ((boxMonomial z.val.1.1 z.val.1.2 z.val.2 : SuperRing R n) :
        CoinvariantAlgebra (R := R) (n := n) (r := 1) 0 0) := by
  let e : CoinvariantAlgebra (R := R) (n := n) (r := 1) 0 0 ≃ₐ[R]
      StrictQuotient (fun _ : Fin n ↦ (1 : R)) (fun i ↦ (X i)^1) :=
    quotientEquivOfIdealEq ((positiveInvariantIdeal_eq_blockIdeal_typeA hfac).trans
      (blockIdeal_eq_strictIdeal (by decide : 0<1)))
  change e.symm (strictPaperBasis (trivialColorPowerData hn (by decide : 0<1) hfac) z)=_
  apply e.injective
  rw [AlgEquiv.apply_symm_apply,strictPaperBasis_apply]
  rfl

/-- The signed-permutation bounds in the introduction are exactly the
opposite-character bounds with covering degree two and character one. -/
theorem typeB_bound (hn : 0<n) (hfac : IsUnit (n.factorial : R))
    (T S : Finset (Fin n)) (i : Fin n) :
    pairedBound (oppositePowerData hn (by decide : 0<2) (by decide : 1≤2) hfac) T S i=
      2*height T S i+marks T S i := by
  rw [oppositePowerData_bound]
  simp only [Nat.reduceSub,Nat.cast_ofNat,marks]
  split_ifs <;> norm_num <;> ring

/-- Lentfer's type-A upper exponent is one less than the strict height. -/
def lentferTypeAUpper (T S : Finset (Fin n)) (i : Fin n) : ℤ :=
  height T S i-1

/-- Lentfer's type-B upper exponent is one less than the paired bound. -/
def lentferTypeBUpper (T S : Finset (Fin n)) (i : Fin n) : ℤ :=
  2*height T S i+marks T S i-1

theorem height_first (hn : 0<n) (T S : Finset (Fin n)) :
    height T S ⟨0,hn⟩=1-marks T S ⟨0,hn⟩ := by
  rw [height_eq_previousHeight]
  have hprefix : Finset.univ.filter (fun j : Fin n ↦ j < ⟨0,hn⟩) = ∅ := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
    exact Nat.not_lt_zero j.val
  simp [previousHeight,hprefix]

/-- The strict arrival condition gives exactly the omitted first index in
the support sets of Lentfer's type-A definition. -/
theorem typeA_first_unmarked (hn : 0<n) (T S : Finset (Fin n))
    (hadmissible : 1≤height T S ⟨0,hn⟩) :
    (⟨0,hn⟩ : Fin n)∉T ∧ (⟨0,hn⟩ : Fin n)∉S := by
  rw [height_first hn T S] at hadmissible
  by_cases hT : (⟨0,hn⟩ : Fin n)∈T <;>
    by_cases hS : (⟨0,hn⟩ : Fin n)∈S <;>
    simp_all [marks]

theorem height_next (T S : Finset (Fin n)) (i j : Fin n)
    (hnext : j.val=i.val+1) :
    height T S j=height T S i+1-marks T S j := by
  rw [height_eq_previousHeight T S j]
  have hprefix : Finset.univ.filter (fun k : Fin n ↦ k<j)=
      Finset.univ.filter (fun k : Fin n ↦ k ≤ i) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    change (k.val < j.val) ↔ (k.val ≤ i.val)
    omega
  have hj : (j.val : ℤ)=(i.val : ℤ)+1 := by exact_mod_cast hnext
  simp only [previousHeight,height,hprefix,hj]

/-- This is the initial condition in Lentfer, Definition 3.1. -/
theorem lentferTypeAUpper_first (hn : 0<n) (T S : Finset (Fin n))
    (hadmissible : 1≤height T S ⟨0,hn⟩) :
    lentferTypeAUpper T S ⟨0,hn⟩=0 := by
  unfold lentferTypeAUpper
  have hh := height_first hn T S
  have hm : (0 : ℤ)≤marks T S ⟨0,hn⟩ := by positivity
  omega

/-- This is the full recurrence in Lentfer, Definition 3.1. -/
theorem lentferTypeAUpper_next (T S : Finset (Fin n)) (i j : Fin n)
    (hnext : j.val=i.val+1) :
    lentferTypeAUpper T S j=lentferTypeAUpper T S i-1+
      (if j∉T then 1 else 0)+(if j∉S then 1 else 0) := by
  unfold lentferTypeAUpper
  rw [height_next T S i j hnext]
  simp only [marks,Nat.cast_add]
  by_cases hT : j∈T <;> by_cases hS : j∈S <;> simp [hT,hS] <;> ring

/-- This is the initial condition in Lentfer, Definition 9.5. -/
theorem lentferTypeBUpper_first (hn : 0<n) (T S : Finset (Fin n)) :
    lentferTypeBUpper T S ⟨0,hn⟩=(-1)+
      (if (⟨0,hn⟩ : Fin n)∉T then 1 else 0)+
      (if (⟨0,hn⟩ : Fin n)∉S then 1 else 0) := by
  unfold lentferTypeBUpper
  rw [height_first hn T S]
  by_cases hT : (⟨0,hn⟩ : Fin n)∈T <;>
    by_cases hS : (⟨0,hn⟩ : Fin n)∈S <;> simp [marks,hT,hS]

/-- This is the full recurrence in Lentfer, Definition 9.5, with both
adjacent indices and both colors retained. -/
theorem lentferTypeBUpper_next (T S : Finset (Fin n)) (i j : Fin n)
    (hnext : j.val=i.val+1) :
    lentferTypeBUpper T S j=lentferTypeBUpper T S i-2+
      (if j∉T then 1 else 0)+(if i∉T then 1 else 0)+
      (if j∉S then 1 else 0)+(if i∉S then 1 else 0) := by
  unfold lentferTypeBUpper
  rw [height_next T S i j hnext]
  by_cases hiT : i∈T <;> by_cases hiS : i∈S <;>
    by_cases hjT : j∈T <;> by_cases hjS : j∈S <;>
    simp [marks,hiT,hiS,hjT,hjS] <;> ring

/-- The strict box inequality is exactly the inclusive type-A bound. -/
theorem lentferTypeA_exponent_iff (T S : Finset (Fin n)) (i : Fin n) (e : ℕ) :
    (e : ℤ)<height T S i ↔ (e : ℤ)≤lentferTypeAUpper T S i := by
  unfold lentferTypeAUpper
  omega

/-- The type-B box inequality is exactly the inclusive bound in Definition 9.5. -/
theorem lentferTypeB_exponent_iff (T S : Finset (Fin n)) (i : Fin n) (e : ℕ) :
    (e : ℤ)<2*height T S i+marks T S i ↔
      (e : ℤ)≤lentferTypeBUpper T S i := by
  unfold lentferTypeBUpper
  omega

/-- The initial condition and recurrence determine the entire type-A
sequence, so they rigorously identify the recursively printed bounds. -/
theorem lentferTypeAUpper_unique (hn : 0<n) (T S : Finset (Fin n))
    (hadmissible : 1≤height T S ⟨0,hn⟩) (f : Fin n → ℤ)
    (hfirst : f ⟨0,hn⟩=0)
    (hstep : ∀ i j : Fin n,j.val=i.val+1 →
      f j=f i-1+(if j∉T then 1 else 0)+(if j∉S then 1 else 0)) :
    f=lentferTypeAUpper T S := by
  cases n with
  | zero => omega
  | succ n =>
      funext i
      induction i using Fin.induction with
      | zero => exact hfirst.trans (lentferTypeAUpper_first hn T S hadmissible).symm
      | succ i ih =>
          rw [hstep i.castSucc i.succ rfl,
            lentferTypeAUpper_next T S i.castSucc i.succ rfl,ih]

/-- The analogous uniqueness statement for the type-B recurrence. -/
theorem lentferTypeBUpper_unique (hn : 0<n) (T S : Finset (Fin n))
    (f : Fin n → ℤ)
    (hfirst : f ⟨0,hn⟩=(-1)+
      (if (⟨0,hn⟩ : Fin n)∉T then 1 else 0)+
      (if (⟨0,hn⟩ : Fin n)∉S then 1 else 0))
    (hstep : ∀ i j : Fin n,j.val=i.val+1 → f j=f i-2+
      (if j∉T then 1 else 0)+(if i∉T then 1 else 0)+
      (if j∉S then 1 else 0)+(if i∉S then 1 else 0)) :
    f=lentferTypeBUpper T S := by
  cases n with
  | zero => omega
  | succ n =>
      funext i
      induction i using Fin.induction with
      | zero => exact hfirst.trans (lentferTypeBUpper_first hn T S).symm
      | succ i ih =>
          rw [hstep i.castSucc i.succ rfl,
            lentferTypeBUpper_next T S i.castSucc i.succ rfl,ih]

/-- Using a unit as the primitive-root witness adds no hypothesis: every
positive-order primitive root in the original ring is already a unit. -/
theorem primitive_root_unit_exists_iff {r : ℕ} (hr : 0<r) :
    (∃ ζ : Rˣ,IsPrimitiveRoot (ζ : R) r) ↔
      (∃ ζ : R,IsPrimitiveRoot ζ r) := by
  constructor
  · rintro ⟨ζ,hζ⟩
    exact ⟨(ζ : R),hζ⟩
  · rintro ⟨z,hz⟩
    obtain ⟨ζ,hζ⟩ := hz.isUnit hr.ne'
    exact ⟨ζ,by simpa only [hζ] using hz⟩

/-- Over a field, the positive covering degree is already a unit whenever
the field contains a primitive root of that order. Thus the extra unit
condition printed in Section 8.1 is a consequence of its root hypothesis. -/
theorem primitive_root_order_unit {F : Type*} [Field F] {r : ℕ}
    (hr : 0<r) (ζ : F) (hζ : IsPrimitiveRoot ζ r) : IsUnit (r : F) := by
  letI : NeZero r := ⟨hr.ne'⟩
  letI : NeZero (r : F) := hζ.neZero'
  exact isUnit_iff_ne_zero.mpr (NeZero.ne (r : F))

section PositiveCharacteristic

variable {F : Type*} [Field F] {p r a : ℕ} [CharP F p]

/-- No factorial-unit hypothesis is added to the positive-characteristic
application: it follows from the paper's stated inequality. -/
theorem factorial_unit_of_characteristic_gt (hn : 0<n) (hp : n<p) :
    IsUnit (n.factorial : F) := by
  letI : Fact p.Prime := ⟨CharP.char_is_prime_of_two_le F p (by omega)⟩
  exact (IsUnit.natCast_factorial_iff_of_charP p).mpr hp

/-- The paired invariant ideal equality with precisely the characteristic
range of Section 8.1. The primitive root is an actual element of the field. -/
theorem positive_characteristic_opposite_ideal
    (hn : 0<n) (hp : n<p) (hr : 2≤r) (ha : 1≤a) (har : a≤r-1)
    (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    positiveInvariantIdeal (R := F) (n := n) (r := r) a (r-a)=
      pairedIdeal (fun _ : Fin n ↦ (1 : F))
        (fun i ↦ (MvPolynomial.X i : PolynomialRing F n)^r)
        (fun i ↦ (MvPolynomial.X i)^a) (fun i ↦ (MvPolynomial.X i)^(r-a)) :=
  positiveInvariantIdeal_eq_paired (by omega) (by omega) (by omega)
    (factorial_unit_of_characteristic_gt hn hp) ζ hζ

/-- Both exterior characters are zero; covering degree one is included. -/
theorem positive_characteristic_trivial_color_ideal
    (hn : 0<n) (hp : n<p) (hr : 0<r)
    (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    positiveInvariantIdeal (R := F) (n := n) (r := r) 0 0=
      strictIdeal (fun _ : Fin n ↦ (1 : F))
        (fun i ↦ (MvPolynomial.X i : PolynomialRing F n)^r) :=
  positiveInvariantIdeal_eq_strict hr (factorial_unit_of_characteristic_gt hn hp) ζ hζ

/-- The full rank formula in every allowed positive characteristic. -/
theorem positive_characteristic_opposite_finrank
    (hn : 0<n) (hp : n<p) (hr : 2≤r) (ha : 1≤a) (har : a≤r-1)
    (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    Module.finrank F (CoinvariantAlgebra (R := F) (n := n) (r := r) a (r-a))=
      (2*r)^n*n.factorial :=
  oppositeCoinvariant_finrank hn (by omega) (by omega) (by omega)
    (factorial_unit_of_characteristic_gt hn hp) ζ hζ

/-- The strict-character dimension formula has the same unrestricted
positive-characteristic range as the original invariant-ideal theorem. -/
theorem positive_characteristic_trivial_color_finrank
    (hn : 0<n) (hp : n<p) (hr : 0<r)
    (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    Module.finrank F (CoinvariantAlgebra (R := F) (n := n) (r := r) 0 0)=
      r^n*2^(n-1)*n.factorial :=
  trivialColorCoinvariant_finrank hn hr
    (factorial_unit_of_characteristic_gt hn hp) ζ hζ

end PositiveCharacteristic

end PaperVerification.Fermion.Coinvariants
