module

public import PaperVerification.FermionPhysicalHilbert
public import PaperVerification.FermionCoinvariantApplications
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The printed rectangle products in all three Hilbert variables

The finite sums are over the entire original
paper index. The proof regroups those sums by the original two supports,
retaining the exact integer arrival inequalities and every exponent bound.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion.PhysicalHilbert

open Exterior Newton
variable {R A : Type*} [CommRing R] [CommSemiring A] {n : ℕ}

local instance paperBoxHilbertDecidableEq : DecidableEq (OddIndex n) :=
  (interleavedOddOrder n).toDecidableEq

def geometricSum (q : A) (d : ℕ) : A := ∑ j : Fin d,q^j.val

theorem rectangle_generating (q : A) (bounds : Fin n→ℕ) :
    (∑ e : RectangleIndex bounds,q^(∑ i,e.val i))=
      ∏ i,geometricSum q (bounds i) := by
  calc
    _ = ∑ e : ∀ i,Fin (bounds i),∏ i,q^(e i).val := by
      rw [←Equiv.sum_comp (rectangleIndexEquiv bounds).symm]
      apply Finset.sum_congr rfl
      intro e he
      change q^(∑ i,(e i).val)=∏ i,q^(e i).val
      exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ (e i).val) q).symm
    _ = _ := (Fintype.prod_sum (fun i (e : Fin (bounds i)) ↦ q^e.val)).symm

theorem paired_word_generating (r u v : Fin n→ℕ) (s : ℕ)
    (q : A) (W : Finset (OddIndex n)) :
    (∑ e : PairedWordPolynomialIndex r u v s W,q^(∑ i,e.val.val i))=
      if ValidWord W then ∏ i,geometricSum q (wordBoxBounds r u v s W i) else 0 := by
  by_cases hW : ValidWord W
  · rw [if_pos hW]
    let e : PairedWordPolynomialIndex r u v s W ≃
        RectangleIndex (wordBoxBounds r u v s W) :=
      ⟨Subtype.val,fun a ↦ ⟨a,hW⟩,fun _ ↦ rfl,fun _ ↦ rfl⟩
    calc
      _ = ∑ a : RectangleIndex (wordBoxBounds r u v s W),q^(∑ i,a.val i) :=
        e.sum_comp (fun a ↦ q^(∑ i,a.val i))
      _ = _ := rectangle_generating q _
  · haveI : IsEmpty (PairedWordPolynomialIndex r u v s W) := ⟨fun e ↦ hW e.property⟩
    simp only [Finset.univ_eq_empty,Finset.sum_empty,if_neg hW]

theorem strict_word_generating (r : Fin n→ℕ) (q : A) (W : Finset (OddIndex n)) :
    (∑ e : StrictWordPolynomialIndex r W,q^(∑ i,e.val.val i))=
      if StrictWord W then ∏ i,geometricSum q (strictWordBoxBounds r W i) else 0 := by
  by_cases hW : StrictWord W
  · rw [if_pos hW]
    let e : StrictWordPolynomialIndex r W ≃ RectangleIndex (strictWordBoxBounds r W) :=
      ⟨Subtype.val,fun a ↦ ⟨a,hW.valid⟩,fun _ ↦ rfl,fun _ ↦ rfl⟩
    calc
      _ = ∑ a : RectangleIndex (strictWordBoxBounds r W),q^(∑ i,a.val i) :=
        e.sum_comp (fun a ↦ q^(∑ i,a.val i))
      _ = _ := rectangle_generating q _
  · haveI : IsEmpty (StrictWordPolynomialIndex r W) :=
      ⟨fun e ↦ hW (strictWord_of_polynomialIndex r W e)⟩
    simp only [Finset.univ_eq_empty,Finset.sum_empty,if_neg hW]

theorem strictWord_disjSum_iff (T S : Finset (Fin n)) :
    StrictWord (T.disjSum S) ↔ ∀ i,1≤height T S i := by
  constructor
  · intro h i
    have hp := h (i.val+1) (Nat.succ_pos _) (Nat.succ_le_of_lt i.isLt)
    rw [height_eq_prefix_card]
    omega
  · intro h j hj hjn
    let i : Fin n := ⟨j-1,by omega⟩
    have hi : i.val+1=j := by dsimp only [i]; omega
    have hp := h i
    rw [height_eq_prefix_card,hi] at hp
    omega

/-- Full three-variable sum for the exact paired index, with the original
nonnegative integer arrival condition and literal printed exponent lengths. -/
theorem paired_paper_generating (d : PairedData (K := R) (n := n)) (q u v : A) :
    (∑ z : PairedIndex d,q^(∑ i,z.val.2 i)*u^z.val.1.1.card*v^z.val.1.2.card)=
      ∑ T : Finset (Fin n),∑ S : Finset (Fin n),
        if (∀ i,0≤height T S i) then
          (∏ i,geometricSum q (pairedBound d T S i).toNat)*u^T.card*v^S.card else 0 := by
  rw [←Equiv.sum_comp (pairedIndexEquiv d).symm]
  change (∑ z : PairedPowerIndex d.r d.u d.v d.s,
    q^(∑ i,z.2.val.val i)*u^z.1.toLeft.card*v^z.1.toRight.card)=_
  rw [Fintype.sum_sigma]
  simp only [←Finset.sum_mul,paired_word_generating]
  rw [←Equiv.sum_comp (Finset.sumEquiv.toEquiv :
    Finset (OddIndex n) ≃ Finset (Fin n)×Finset (Fin n)).symm,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro S hS
  change (if ValidWord (T.disjSum S) then
      ∏ i,geometricSum q (wordBoxBounds d.r d.u d.v d.s (T.disjSum S) i) else 0)*
        u^(T.disjSum S).toLeft.card*v^(T.disjSum S).toRight.card=_
  rw [Finset.toLeft_disjSum,Finset.toRight_disjSum]
  by_cases h : ValidWord (T.disjSum S)
  · rw [if_pos h,if_pos ((validWord_disjSum_iff T S).mp h)]
    congr 2
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    have he := wordBoxBounds_disjSum_cast d T S h i
    simpa only [Int.toNat_natCast] using congrArg Int.toNat he
  · rw [if_neg h,if_neg (fun hp ↦ h ((validWord_disjSum_iff T S).mpr hp)),zero_mul,zero_mul]

/-- Full strict three-variable sum with the original strictly positive
arrival heights. Empty boxes are handled by the actual finite index. -/
theorem strict_paper_generating (d : StrictData (K := R) (n := n)) (q u v : A) :
    (∑ z : StrictIndex d,q^(∑ i,z.val.2 i)*u^z.val.1.1.card*v^z.val.1.2.card)=
      ∑ T : Finset (Fin n),∑ S : Finset (Fin n),
        if (∀ i,1≤height T S i) then
          (∏ i,geometricSum q ((d.r i : ℤ)*height T S i).toNat)*
            u^T.card*v^S.card else 0 := by
  rw [←Equiv.sum_comp (strictIndexEquiv d).symm]
  change (∑ z : StrictPowerIndex d.r,
    q^(∑ i,z.2.val.val i)*u^z.1.toLeft.card*v^z.1.toRight.card)=_
  rw [Fintype.sum_sigma]
  simp only [←Finset.sum_mul,strict_word_generating]
  rw [←Equiv.sum_comp (Finset.sumEquiv.toEquiv :
    Finset (OddIndex n) ≃ Finset (Fin n)×Finset (Fin n)).symm,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro S hS
  change (if StrictWord (T.disjSum S) then
      ∏ i,geometricSum q (strictWordBoxBounds d.r (T.disjSum S) i) else 0)*
        u^(T.disjSum S).toLeft.card*v^(T.disjSum S).toRight.card=_
  rw [Finset.toLeft_disjSum,Finset.toRight_disjSum]
  by_cases h : StrictWord (T.disjSum S)
  · rw [if_pos h,if_pos ((strictWord_disjSum_iff T S).mp h)]
    congr 2
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    have he := strictWordBoxBounds_disjSum_cast d.r T S h.valid i
    simpa only [Int.toNat_natCast] using congrArg Int.toNat he
  · rw [if_neg h,if_neg (fun hp ↦ h ((strictWord_disjSum_iff T S).mpr hp)),zero_mul,zero_mul]

end PaperVerification.Fermion.PhysicalHilbert

namespace PaperVerification.Fermion.Coinvariants

open MvPolynomial
variable {F : Type*} [Field F] {n r a : ℕ}

/-- The printed full Hilbert polynomial for opposite nontrivial characters. -/
def oppositeHilbertPolynomial (n r a : ℕ) : MvPolynomial (Fin 3) ℕ :=
  ∑ T : Finset (Fin n),∑ S : Finset (Fin n),
    if (∀ i,0≤height T S i) then
      (∏ i,PhysicalHilbert.geometricSum (X 0 : MvPolynomial (Fin 3) ℕ)
        ((r : ℤ)*height T S i+(if i∈T then (r-a : ℕ) else 0)+
          (if i∈S then a else 0)).toNat)*X 1^T.card*X 2^S.card else 0

/-- The printed strict three-variable Hilbert polynomial. -/
def trivialColorHilbertPolynomial (n r : ℕ) : MvPolynomial (Fin 3) ℕ :=
  ∑ T : Finset (Fin n),∑ S : Finset (Fin n),
    if (∀ i,1≤height T S i) then
      (∏ i,PhysicalHilbert.geometricSum (X 0 : MvPolynomial (Fin 3) ℕ)
        ((r : ℤ)*height T S i).toNat)*X 1^T.card*X 2^S.card else 0

theorem opposite_index_polynomial_eq_printed
    (hn : 0<n) (hr : 0<r) (har : a≤r) (hfac : IsUnit (n.factorial : F)) :
    PhysicalHilbert.polynomial
      (fun z : PairedIndex (oppositePowerData hn hr har hfac) ↦ paperBoxDegree z.val)=
      oppositeHilbertPolynomial n r a := by
  rw [PhysicalHilbert.polynomial_eq]
  change (∑ z : PairedIndex (oppositePowerData hn hr har hfac),
    (X 0 : MvPolynomial (Fin 3) ℕ)^(∑ i,z.val.2 i)*X 1^z.val.1.1.card*X 2^z.val.1.2.card)=_
  rw [PhysicalHilbert.paired_paper_generating]
  simp only [oppositeHilbertPolynomial,oppositePowerData_bound]

theorem trivial_index_polynomial_eq_printed
    (hn : 0<n) (hr : 0<r) (hfac : IsUnit (n.factorial : F)) :
    PhysicalHilbert.polynomial
      (fun z : StrictIndex (trivialColorPowerData hn hr hfac) ↦ paperBoxDegree z.val)=
      trivialColorHilbertPolynomial n r := by
  rw [PhysicalHilbert.polynomial_eq]
  change (∑ z : StrictIndex (trivialColorPowerData hn hr hfac),
    (X 0 : MvPolynomial (Fin 3) ℕ)^(∑ i,z.val.2 i)*X 1^z.val.1.1.card*X 2^z.val.1.2.card)=_
  rw [PhysicalHilbert.strict_paper_generating]
  rfl

/-- Every printed coefficient is the dimension of the original physical
piece, uniformly in all three degrees and all parameters. -/
theorem oppositeCoinvariant_full_hilbert_coefficient
    (hn : 0<n) (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (g : ℕ×(ℕ×ℕ)) :
    Module.finrank F
      (coinvariantPhysicalPiece (R := F) (n := n) (r := r) a (r-a) g)=
      (oppositeHilbertPolynomial n r a).coeff (PhysicalHilbert.exponent g) := by
  rw [oppositeCoinvariant_physical_hilbert_coefficient hn hr ha har hfac ζ hζ,
    opposite_index_polynomial_eq_printed]

theorem trivialColorCoinvariant_full_hilbert_coefficient
    (hn : 0<n) (hr : 0<r) (hfac : IsUnit (n.factorial : F))
    (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) (g : ℕ×(ℕ×ℕ)) :
    Module.finrank F (coinvariantPhysicalPiece (R := F) (n := n) (r := r) 0 0 g)=
      (trivialColorHilbertPolynomial n r).coeff (PhysicalHilbert.exponent g) := by
  rw [trivialColorCoinvariant_physical_hilbert_coefficient hn hr hfac ζ hζ,
    trivial_index_polynomial_eq_printed]

/-- All parameters in the complex opposite-character specialization are
exactly the printed integer ranges. -/
theorem complex_opposite_full_hilbert_coefficient
    (hn : 0<n) (hr : 2≤r) (ha : 1≤a) (har : a≤r-1) (g : ℕ×(ℕ×ℕ)) :
    Module.finrank ℂ
      (coinvariantPhysicalPiece (R := ℂ) (n := n) (r := r) a (r-a) g)=
      (oppositeHilbertPolynomial n r a).coeff (PhysicalHilbert.exponent g) := by
  have hr' : 0<r := by omega
  obtain ⟨ζ,hζ⟩ := complex_primitive_unit hr'
  exact oppositeCoinvariant_full_hilbert_coefficient hn hr' (by omega) (by omega)
    (complex_factorial_unit n) ζ hζ g

theorem complex_trivialColor_full_hilbert_coefficient
    (hn : 0<n) (hr : 0<r) (g : ℕ×(ℕ×ℕ)) :
    Module.finrank ℂ (coinvariantPhysicalPiece (R := ℂ) (n := n) (r := r) 0 0 g)=
      (trivialColorHilbertPolynomial n r).coeff (PhysicalHilbert.exponent g) := by
  obtain ⟨ζ,hζ⟩ := complex_primitive_unit hr
  exact trivialColorCoinvariant_full_hilbert_coefficient hn hr
    (complex_factorial_unit n) ζ hζ g

section PositiveCharacteristic

variable {p : ℕ} [CharP F p]

/-- The complete printed Hilbert polynomial in every permitted positive
characteristic; the factorial-unit condition is derived, not assumed. -/
theorem positive_characteristic_opposite_full_hilbert_coefficient
    (hn : 0<n) (hp : n<p) (hr : 2≤r) (ha : 1≤a) (har : a≤r-1)
    (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) (g : ℕ×(ℕ×ℕ)) :
    Module.finrank F
      (coinvariantPhysicalPiece (R := F) (n := n) (r := r) a (r-a) g)=
      (oppositeHilbertPolynomial n r a).coeff (PhysicalHilbert.exponent g) :=
  oppositeCoinvariant_full_hilbert_coefficient hn (by omega) (by omega) (by omega)
    (factorial_unit_of_characteristic_gt hn hp) ζ hζ g

/-- The complete strict Hilbert polynomial, including covering degree one,
in every permitted positive characteristic. -/
theorem positive_characteristic_trivial_color_full_hilbert_coefficient
    (hn : 0<n) (hp : n<p) (hr : 0<r)
    (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) (g : ℕ×(ℕ×ℕ)) :
    Module.finrank F (coinvariantPhysicalPiece (R := F) (n := n) (r := r) 0 0 g)=
      (trivialColorHilbertPolynomial n r).coeff (PhysicalHilbert.exponent g) :=
  trivialColorCoinvariant_full_hilbert_coefficient hn hr
    (factorial_unit_of_characteristic_gt hn hp) ζ hζ g

end PositiveCharacteristic

section ArbitraryTypeA
variable {R : Type*} [CommRing R]

/-- The full polynomial's coefficients are explicit basis cardinalities over
every type-A base ring, including the zero ring. -/
theorem typeACoinvariant_physical_basis_card
    (hn : 0<n) (hfac : IsUnit (n.factorial : R)) (g : ℕ×(ℕ×ℕ)) :
    Fintype.card {z : StrictIndex (trivialColorPowerData hn (by decide : 0<1) hfac) //
      paperBoxDegree z.val=g}=
      (trivialColorHilbertPolynomial n 1).coeff (PhysicalHilbert.exponent g) := by
  rw [←PhysicalHilbert.coefficient]
  apply congrArg (fun p : MvPolynomial (Fin 3) ℕ ↦ p.coeff (PhysicalHilbert.exponent g))
  rw [PhysicalHilbert.polynomial_eq]
  change (∑ z : StrictIndex (trivialColorPowerData hn (by decide : 0<1) hfac),
    (X 0 : MvPolynomial (Fin 3) ℕ)^(∑ i,z.val.2 i)*X 1^z.val.1.1.card*X 2^z.val.1.2.card)=_
  rw [PhysicalHilbert.strict_paper_generating]
  rfl

theorem typeACoinvariant_full_hilbert_coefficient [Nontrivial R]
    (hn : 0<n) (hfac : IsUnit (n.factorial : R)) (g : ℕ×(ℕ×ℕ)) :
    Module.finrank R (coinvariantPhysicalPiece (R := R) (n := n) (r := 1) 0 0 g)=
      (trivialColorHilbertPolynomial n 1).coeff (PhysicalHilbert.exponent g) := by
  rw [Module.finrank_eq_card_basis (typeAPhysicalPieceBasis hn hfac g)]
  exact typeACoinvariant_physical_basis_card hn hfac g

end ArbitraryTypeA
end PaperVerification.Fermion.Coinvariants
