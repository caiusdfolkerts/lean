module

public import PaperVerification.FermionCoinvariantInvariantIdeal
public import Mathlib.RingTheory.Congruence.Hom

/-!
# The genuine invariant-generated ideal equals the original moment ideal

The arithmetic classification below exhausts
every positive one-index invariant block. The full occupied-index induction
and the actual diagonal-character argument were proved in the preceding
sources; they are not additional assumptions in these endpoints.

The type-A result is over an arbitrary commutative coefficient ring with n!
invertible. The wreath results are over any field with n! invertible and an
actual primitive rth root. No characteristic-zero hypothesis is introduced.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.Coinvariants

variable {R : Type*} [CommRing R] {n r a : ℕ}

/-- Every positive compatible exponent is one of the four printed paired
families, with no upper bound on the moment index. -/
theorem exists_oppositeExponent (hr : 0<r) (ha : 0<a) (har : a<r)
    (d : ℕ) (c : MomentKind) (hd : r∣d+oddWeight a (r-a) c)
    (hp : 0<d ∨ c≠.polynomial) : ∃ k,d=oppositeExponent r a c k := by
  cases c with
  | polynomial =>
      have hdpos : 0<d := hp.resolve_right (by simp)
      simp only [oddWeight,Nat.add_zero] at hd
      obtain ⟨k,hk⟩ := hd
      cases k with
      | zero => simp only [Nat.mul_zero] at hk; omega
      | succ k => exact ⟨k,by simpa only [oppositeExponent,Nat.succ_eq_add_one] using hk⟩
  | theta =>
      simp only [oddWeight] at hd
      obtain ⟨k,hk⟩ := hd
      cases k with
      | zero => simp only [Nat.mul_zero] at hk; omega
      | succ k =>
          refine ⟨k,?_⟩
          simp only [oppositeExponent]
          rw [Nat.mul_succ] at hk
          omega
  | xi =>
      simp only [oddWeight] at hd
      obtain ⟨k,hk⟩ := hd
      cases k with
      | zero => simp only [Nat.mul_zero] at hk; omega
      | succ k =>
          refine ⟨k,?_⟩
          simp only [oppositeExponent]
          rw [Nat.mul_succ] at hk
          omega
  | mixed =>
      simp only [oddWeight,Nat.add_sub_of_le har.le] at hd
      obtain ⟨k,hk⟩ := hd
      cases k with
      | zero => simp only [Nat.mul_zero] at hk; omega
      | succ k =>
          refine ⟨k,?_⟩
          simp only [oppositeExponent]
          rw [Nat.mul_succ] at hk
          omega

/-- With trivial exterior characters the positive polynomial family starts
at r, while each of the three odd families starts at exponent zero. -/
theorem exists_strictExponent (hr : 0<r) (d : ℕ) (c : MomentKind)
    (hd : r∣d+oddWeight 0 0 c) (hp : 0<d ∨ c≠.polynomial) :
    ∃ k,d=strictExponent r c k := by
  have hd' : r∣d := by cases c <;> simpa only [oddWeight,Nat.add_zero] using hd
  obtain ⟨k,hk⟩ := hd'
  cases c with
  | polynomial =>
      have hdpos : 0<d := hp.resolve_right (by simp)
      cases k with
      | zero => simp only [Nat.mul_zero] at hk; omega
      | succ k => exact ⟨k,by simpa only [strictExponent,Nat.succ_eq_add_one] using hk⟩
  | theta => exact ⟨k,hk⟩
  | xi => exact ⟨k,hk⟩
  | mixed => exact ⟨k,hk⟩

theorem blockIdeal_eq_pairedIdeal (hr : 0<r) (ha : 0<a) (har : a<r) :
    blockIdeal (R := R) (n := n) r a (r-a)=
      pairedIdeal (fun _ : Fin n ↦ (1 : R))
        (fun i ↦ (MvPolynomial.X i : PolynomialRing R n)^r)
        (fun i ↦ (MvPolynomial.X i)^a) (fun i ↦ (MvPolynomial.X i)^(r-a)) := by
  apply le_antisymm
  · apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨d,c,hd,hp,rfl⟩
    obtain ⟨k,rfl⟩ := exists_oppositeExponent hr ha har d c hd hp
    rw [←paired_moment_eq_opposite_blockSum r a har.le]
    exact TwoSidedIdeal.subset_span ⟨⟨c,k⟩,rfl⟩
  · apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨⟨c,k⟩,rfl⟩
    dsimp only
    rw [paired_moment_eq_opposite_blockSum r a har.le]
    exact blockSum_mem_blockIdeal _ c (oppositeExponent_weight_dvd r a har.le c k)
      (oppositeExponent_positive r a hr c k)

theorem blockIdeal_eq_strictIdeal (hr : 0<r) :
    blockIdeal (R := R) (n := n) r 0 0=
      strictIdeal (fun _ : Fin n ↦ (1 : R))
        (fun i ↦ (MvPolynomial.X i : PolynomialRing R n)^r) := by
  apply le_antisymm
  · apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨d,c,hd,hp,rfl⟩
    obtain ⟨k,rfl⟩ := exists_strictExponent hr d c hd hp
    rw [←strict_moment_eq_blockSum r]
    exact TwoSidedIdeal.subset_span ⟨⟨c,k⟩,rfl⟩
  · apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨⟨c,k⟩,rfl⟩
    dsimp only
    rw [strict_moment_eq_blockSum r]
    apply blockSum_mem_blockIdeal
    · cases c <;> simp [strictExponent,oddWeight]
    · cases c
      · exact Or.inl (Nat.mul_pos hr (Nat.succ_pos k))
      all_goals exact Or.inr (by decide)

/-- The original type-A invariant-generated ideal, over every commutative
ring in which n! is invertible, is the precise original strict ideal. -/
theorem positiveInvariantIdeal_eq_strict_typeA (hfac : IsUnit (n.factorial : R)) :
    positiveInvariantIdeal (R := R) (n := n) (r := 1) 0 0=
      strictIdeal (fun _ : Fin n ↦ (1 : R)) (fun i ↦ MvPolynomial.X i) := by
  rw [positiveInvariantIdeal_eq_blockIdeal_typeA hfac,blockIdeal_eq_strictIdeal (by decide : 0<1)]
  simp only [pow_one]

/-- Equality of actual defining ideals induces the identity on the original
polynomial/exterior representatives. -/
def quotientEquivOfIdealEq {I J : TwoSidedIdeal (SuperRing R n)} (h : I=J) :
    I.ringCon.Quotient ≃ₐ[R] J.ringCon.Quotient :=
  RingCon.congrₐ R (AlgEquiv.refl : SuperRing R n ≃ₐ[R] SuperRing R n) (by cases h; rfl)

@[simp] theorem quotientEquivOfIdealEq_mk {I J : TwoSidedIdeal (SuperRing R n)}
    (h : I=J) (x : SuperRing R n) :
    quotientEquivOfIdealEq h (x : I.ringCon.Quotient)=(x : J.ringCon.Quotient) := rfl

/-- This is the genuine invariant-theoretic type-A quotient, not a new name
for the moment quotient. The preceding ideal equality proves the comparison. -/
def typeACoinvariantEquiv (hfac : IsUnit (n.factorial : R)) :
    CoinvariantAlgebra (R := R) (n := n) (r := 1) 0 0 ≃ₐ[R]
      StrictQuotient (fun _ : Fin n ↦ (1 : R)) (fun i ↦ MvPolynomial.X i) :=
  quotientEquivOfIdealEq (positiveInvariantIdeal_eq_strict_typeA hfac)

section Field

variable {F : Type*} [Field F]

/-- The opposite-character statement of Section8.1 for every field with
the stated unit and actual primitive-root hypotheses. -/
theorem positiveInvariantIdeal_eq_paired (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    positiveInvariantIdeal (R := F) (n := n) (r := r) a (r-a)=
      pairedIdeal (fun _ : Fin n ↦ (1 : F))
        (fun i ↦ (MvPolynomial.X i : PolynomialRing F n)^r)
        (fun i ↦ (MvPolynomial.X i)^a) (fun i ↦ (MvPolynomial.X i)^(r-a)) := by
  rw [positiveInvariantIdeal_eq_blockIdeal hfac ζ hζ,blockIdeal_eq_pairedIdeal hr ha har]

theorem positiveInvariantIdeal_eq_strict (hr : 0<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    positiveInvariantIdeal (R := F) (n := n) (r := r) 0 0=
      strictIdeal (fun _ : Fin n ↦ (1 : F))
        (fun i ↦ (MvPolynomial.X i : PolynomialRing F n)^r) := by
  rw [positiveInvariantIdeal_eq_blockIdeal hfac ζ hζ,blockIdeal_eq_strictIdeal hr]

def oppositeCoinvariantEquiv (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    CoinvariantAlgebra (R := F) (n := n) (r := r) a (r-a) ≃ₐ[F]
      PairedQuotient (fun _ : Fin n ↦ (1 : F))
        (fun i ↦ (MvPolynomial.X i : PolynomialRing F n)^r)
        (fun i ↦ (MvPolynomial.X i)^a) (fun i ↦ (MvPolynomial.X i)^(r-a)) :=
  quotientEquivOfIdealEq (positiveInvariantIdeal_eq_paired hr ha har hfac ζ hζ)

def trivialColorCoinvariantEquiv (hr : 0<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    CoinvariantAlgebra (R := F) (n := n) (r := r) 0 0 ≃ₐ[F]
      StrictQuotient (fun _ : Fin n ↦ (1 : F))
        (fun i ↦ (MvPolynomial.X i : PolynomialRing F n)^r) :=
  quotientEquivOfIdealEq (positiveInvariantIdeal_eq_strict hr hfac ζ hζ)

end Field
end PaperVerification.Fermion.Coinvariants
