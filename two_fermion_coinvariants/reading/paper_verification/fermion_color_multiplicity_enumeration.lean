module

public import PaperVerification.FermionColorBasisEnumeration
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact multiplicity regrouping of the full strict basis polynomial

This is the finite combinatorial identity in equation (22), retaining every
polynomial exponent and both color supports. The input is the actual strict
basis index. The natural arrival bounds are proved equal to the paper's
integer heights. No Hilbert or character formula is used as a hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators

namespace PaperVerification.Fermion.ColorPaths

open Exterior Endpoint Paths Newton

variable {R : Type*} [CommSemiring R] {n : ℕ}

local instance colorMultiplicityEnumerationDecidableEq (n : ℕ) : DecidableEq (OddIndex n) :=
  (interleavedOddOrder n).toDecidableEq

abbrev LocalColorFiber (m : Fin 3) := {a : Mark // markDegree a=m.val}

theorem markDegree_wordMark (T : Finset (OddIndex n)) (i : Fin n) :
    markDegree (wordMark T i)=wordMultiplicity T i := by
  by_cases hθ : Sum.inl i∈T <;> by_cases hξ : Sum.inr i∈T <;>
    simp only [wordMark,wordMultiplicity,hθ,hξ,if_true,if_false,markDegree] <;> rfl

/-- Each multiplicity-one position has exactly its two original colors. -/
def coloringLocalEquiv (m : MultiplicityVector n) :
    MultiplicityColoring m ≃ (∀ i,LocalColorFiber (m i)) where
  toFun T i := ⟨wordMark T.val i,by
    rw [markDegree_wordMark]
    exact congrArg (fun f : MultiplicityVector n ↦ (f i).val) T.property⟩
  invFun a := ⟨wordOfMarks (fun i ↦ (a i).val),by
    funext i
    apply Fin.ext
    change wordMultiplicity (wordOfMarks (fun i ↦ (a i).val)) i=(m i).val
    rw [wordMultiplicity_wordOfMarks]
    exact (a i).property⟩
  left_inv T := by
    apply Subtype.ext
    exact (marksWordEquiv n).right_inv T.val
  right_inv a := by
    funext i
    apply Subtype.ext
    exact wordMark_wordOfMarks (fun i ↦ (a i).val) i

theorem localColorFiber_sum (u v : R) (m : Fin 3) :
    (∑ a : LocalColorFiber m,markColor u v a.val)=
      (if m.val=1 then u+v else 1)*(if m.val=2 then u*v else 1) := by
  rw [←Finset.sum_subtype (Finset.univ.filter (fun a : Mark ↦ markDegree a=m.val))
    (by intro a; simp) (markColor u v),Finset.sum_filter,Paths.sum_mark]
  fin_cases m <;> simp [markDegree,markColor]

def singleCount (m : MultiplicityVector n) : ℕ :=
  (Finset.univ.filter (fun i ↦ (m i).val=1)).card

def doubleCount (m : MultiplicityVector n) : ℕ :=
  (Finset.univ.filter (fun i ↦ (m i).val=2)).card

theorem coloring_color_sum (u v : R) (m : MultiplicityVector n) :
    (∑ T : MultiplicityColoring m,wordColor u v T.val)=
      (u+v)^singleCount m*(u*v)^doubleCount m := by
  rw [←Equiv.sum_comp (coloringLocalEquiv m).symm]
  change (∑ a : ∀ i,LocalColorFiber (m i),
    wordColor u v (wordOfMarks (fun i ↦ (a i).val)))=_
  simp only [wordColor_wordOfMarks]
  rw [←Fintype.prod_sum (fun i (a : LocalColorFiber (m i)) ↦ markColor u v a.val)]
  simp only [localColorFiber_sum,Finset.prod_mul_distrib]
  simp [singleCount,doubleCount,Finset.prod_ite]

/-- The finite geometric polynomial evaluated at q, including length zero. -/
def qNumber (q : R) (d : ℕ) : R := ∑ k : Fin d,q^k.val

def arrivalBound (m : MultiplicityVector n) (i : Fin n) : ℕ :=
  (TypeA.arrival m i).toNat

def multiplicityBoxPolynomial (q : R) (m : MultiplicityVector n) : R :=
  ∏ i,qNumber q (arrivalBound m i)

theorem word_bounds_eq_arrival (W : Finset (OddIndex n)) :
    strictWordBoxBounds (fun _ ↦ 1) W=arrivalBound (wordMultiplicityVector W) := by
  funext i
  rw [strictWordBoxBounds,one_mul,wordHeight,TypeA.prefix_card_eq_multiplicity_Iic]
  unfold arrivalBound TypeA.arrival
  omega

theorem rectangle_q_sum (q : R) (h : Fin n → ℕ) :
    (∑ a : RectangleIndex h,q^(∑ i,a.val i))=∏ i,qNumber q (h i) := by
  calc
    _ = ∑ a : ∀ i,Fin (h i), ∏ i,q^(a i).val := by
      rw [←Equiv.sum_comp (rectangleIndexEquiv h).symm]
      apply Finset.sum_congr rfl
      intro a ha
      change q^(∑ i,(a i).val)=∏ i,q^(a i).val
      exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ (a i).val) q).symm
    _ = _ := (Fintype.prod_sum (fun i (a : Fin (h i)) ↦ q^a.val)).symm

theorem strictWord_q_sum (q : R) (W : Finset (OddIndex n)) :
    (∑ a : StrictWordPolynomialIndex (fun _ ↦ 1) W,q^(∑ i,a.val.val i))=
      if StrictWord W then ∏ i,qNumber q (strictWordBoxBounds (fun _ ↦ 1) W i) else 0 := by
  by_cases hW : StrictWord W
  · rw [if_pos hW]
    let e : StrictWordPolynomialIndex (fun _ ↦ 1) W ≃
        RectangleIndex (strictWordBoxBounds (fun _ ↦ 1) W) :=
      ⟨Subtype.val,fun a ↦ ⟨a,hW.valid⟩,fun _ ↦ rfl,fun _ ↦ rfl⟩
    calc
      _ = ∑ a : RectangleIndex (strictWordBoxBounds (fun _ ↦ 1) W),
          q^(∑ i,a.val i) := e.sum_comp (fun a ↦ q^(∑ i,a.val i))
      _ = _ := rectangle_q_sum q _
  · haveI : IsEmpty (StrictWordPolynomialIndex (fun _ : Fin n ↦ 1) W) :=
      ⟨fun a ↦ hW (strictWord_of_polynomialIndex _ W a)⟩
    simp only [Finset.univ_eq_empty,Finset.sum_empty,if_neg hW]

/-- The full polynomial-degree/two-color basis sum, regrouped by the paper's
multiplicity vectors with no change to the admissibility condition. -/
theorem strictPower_q_color_sum (q u v : R) :
    (∑ z : StrictPowerIndex (fun _ : Fin n ↦ 1),
      q^(∑ i,z.2.val.val i)*wordColor u v z.1)=
      ∑ m : MultiplicityVector n,if TypeA.Admissible m then
        multiplicityBoxPolynomial q m*(u+v)^singleCount m*(u*v)^doubleCount m else 0 := by
  rw [Fintype.sum_sigma]
  simp only [←Finset.sum_mul,strictWord_q_sum,TypeA.strictWord_iff_admissible,
    word_bounds_eq_arrival]
  rw [←Equiv.sum_comp (multiplicityColoringEquiv (n := n)).symm,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro m hm
  change (∑ T : MultiplicityColoring m,
    (if TypeA.Admissible (wordMultiplicityVector T.val) then
      ∏ i,qNumber q (arrivalBound (wordMultiplicityVector T.val) i) else 0)*
        wordColor u v T.val)=_
  have he (T : MultiplicityColoring m) : wordMultiplicityVector T.val=m := T.property
  simp only [he]
  rw [←Finset.mul_sum,coloring_color_sum]
  by_cases h : TypeA.Admissible m <;>
    simp only [h,if_true,if_false,zero_mul,multiplicityBoxPolynomial,mul_assoc]

end PaperVerification.Fermion.ColorPaths

namespace PaperVerification.Fermion.TypeA

variable {F R : Type*} [Field F] [CharZero F] [CommSemiring R] {n : ℕ}

/-- The exact original paper index has the same complete polynomial/two-color
sum, including its original exponent function and the two ordered supports. -/
theorem strict_paper_q_color_sum (hn : 0<n) (q u v : R) :
    (∑ z : StrictIndex (data (F := F) hn),
      q^(∑ i,z.val.2 i)*u^z.val.1.1.card*v^z.val.1.2.card)=
      ∑ m : MultiplicityVector n,if Admissible m then
        ColorPaths.multiplicityBoxPolynomial q m*(u+v)^ColorPaths.singleCount m*
          (u*v)^ColorPaths.doubleCount m else 0 := by
  rw [←Equiv.sum_comp (strictIndexEquiv (data (F := F) hn)).symm]
  change (∑ z : StrictPowerIndex (fun _ : Fin n ↦ 1),
    q^(∑ i,z.2.val.val i)*u^z.1.toLeft.card*v^z.1.toRight.card)=_
  simpa only [ColorPaths.wordColor_eq_left_right,mul_assoc] using
    (ColorPaths.strictPower_q_color_sum (n := n) q u v)

end PaperVerification.Fermion.TypeA
