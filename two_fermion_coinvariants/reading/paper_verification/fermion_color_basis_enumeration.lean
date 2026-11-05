module

public import PaperVerification.FermionColorDiagonalTrace
public import PaperVerification.FermionColorPathEnumeration
public import PaperVerification.FermionStrictIndexRecursion

/-!
# The strict quotient basis and the genuine permutation color polynomial

Every polynomial exponent in every strict rectangle is counted. The exact
strict-to-paired-tail bijection removes only the compulsory unmarked first
position and its unique exponent. The remaining four marks carry precisely
the weights in ColorPathEnumeration.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators

namespace PaperVerification.Fermion.ColorPaths

open Exterior Endpoint Paths

variable {R : Type*} [CommSemiring R] {n : ℕ}

local instance colorBasisEnumerationDecidableEq (n : ℕ) : DecidableEq (OddIndex n) :=
  (interleavedOddOrder n).toDecidableEq

def markColor (u v : R) : Mark → R
  | .unmarked => 1
  | .theta => u
  | .xi => v
  | .double => u*v

def wordColor (u v : R) (W : Finset (OddIndex n)) : R :=
  ∏ a∈W, Sum.elim (fun _ ↦ u) (fun _ ↦ v) a

theorem wordColor_eq_left_right (u v : R) (W : Finset (OddIndex n)) :
    wordColor u v W=u^W.toLeft.card*v^W.toRight.card := by
  rw [wordColor,Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  simp only [Sum.elim_inl,Sum.elim_inr,Finset.prod_const]

@[simp] theorem wordColor_disjSum (u v : R) (T S : Finset (Fin n)) :
    wordColor u v (T.disjSum S)=u^T.card*v^S.card := by
  rw [wordColor_eq_left_right,Finset.toLeft_disjSum,Finset.toRight_disjSum]

@[simp] theorem wordColor_wordCons (u v : R) (W : Finset (OddIndex n)) :
    wordColor u v (wordCons W)=wordColor u v W := by
  rw [wordColor,wordCons,Finset.prod_map,wordColor]
  apply Finset.prod_congr rfl
  intro a ha
  cases a <;> rfl

theorem wordColor_wordOfMarks (u v : R) (m : Fin n → Mark) :
    wordColor u v (wordOfMarks m)=∏ i,markColor u v (m i) := by
  have hfull : wordColor u v (wordOfMarks m)=
      ∏ a : OddIndex n,if a∈wordOfMarks m then Sum.elim (fun _ ↦ u) (fun _ ↦ v) a else 1 := by
    simp only [wordColor,Finset.prod_ite_mem,Finset.univ_inter]
  rw [hfull,Fintype.prod_sum_type,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases hm : m i <;> simp [markColor,hm]

theorem wordColor_wordOfMarks_snoc (u v : R) (m : Fin n → Mark) (a : Mark) :
    wordColor u v (wordOfMarks (Fin.snoc m a))=
      wordColor u v (wordOfMarks m)*markColor u v a := by
  simp only [wordColor_wordOfMarks,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]

theorem stepWeight_eq_box_color (u v : R) (h : ℕ) (a : Mark) :
    stepWeight u v h a=(pairedBoxBound 1 1 1 2 h a : R)*markColor u v a := by
  cases a <;> simp only [stepWeight,pairedBoxBound,markColor,one_mul,Nat.cast_add,
    Nat.cast_one,Nat.cast_ofNat,mul_one] <;> ring

theorem coefficient_eq_actual_boxes (u v : R) (m : Fin n → Mark) :
    coefficient u v m=
      if ValidWord (wordOfMarks m) then
        boxProduct (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1) 2 m *
          wordColor u v (wordOfMarks m) else 0 := by
  induction n with
  | zero =>
      have hw : wordOfMarks m=(∅ : Finset (OddIndex 0)) := by
        ext a
        exact isEmptyElim a
      have h : ValidWord (wordOfMarks m) := by
        intro j hj
        have : j=0 := by omega
        subst j
        simp only [hw,Finset.empty_inter,Finset.card_empty,Nat.le_refl]
      rw [if_pos h]
      simp [coefficient,boxProduct,wordColor,hw]
  | succ n ih =>
      obtain ⟨⟨a,m⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (n+1) ↦ Mark)).surjective m
      simp only [Fin.snocEquiv_apply]
      rw [coefficient,Fin.init_snoc,Fin.snoc_last,ih m,stepWeight_eq_box_color]
      by_cases hm : ValidWord (wordOfMarks m)
      · rw [if_pos hm,pathHeight_eq_card m hm]
        by_cases ha : (wordOfMarks m).card+markDegree a≤n+1
        · rw [if_pos ((validWord_snoc_iff m a).mpr ⟨hm,ha⟩),boxProduct_snoc,
            wordColor_wordOfMarks_snoc]
          ring
        · have hn : ¬ValidWord (wordOfMarks (Fin.snoc m a)) :=
            fun h ↦ ha ((validWord_snoc_iff m a).mp h).2
          rw [if_neg hn]
          have hc := hm n le_rfl
          rw [pairedPrefix_full,Finset.inter_univ] at hc
          cases a <;> simp only [markDegree] at ha
          · omega
          · omega
          · omega
          · have hz : n-(wordOfMarks m).card=0 := by omega
            simp only [pairedBoxBound,hz,mul_zero,Nat.cast_zero,zero_mul]
      · have hn : ¬ValidWord (wordOfMarks (Fin.snoc m a)) :=
          fun h ↦ hm ((validWord_snoc_iff m a).mp h).1
        simp only [if_neg hm,if_neg hn,zero_mul]

theorem paired_tail_color_sum (u v : R) :
    (∑ z : PairedPowerIndex (fun _ : Fin n ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1) 2,
      wordColor u v z.1)=Eulerian.permutationPolynomial (n+1) (1+u) (1+v) := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_pairedWordPolynomialIndex]
  rw [←Equiv.sum_comp (marksWordEquiv n)]
  rw [←sum_coefficient_eq_eulerian n u v]
  apply Finset.sum_congr rfl
  intro m hm
  rw [coefficient_eq_actual_boxes]
  simp only [marksWordEquiv,Equiv.coe_fn_mk,pairedWordBoxCard,boxProduct,wordMark_wordOfMarks,
    Nat.cast_ite,Nat.cast_zero,Nat.cast_prod,ite_mul,zero_mul]

theorem strict_tail_color_sum (u v : R) :
    (∑ z : StrictPowerIndex (fun _ : Fin (n+1) ↦ 1),wordColor u v z.1)=
      Eulerian.permutationPolynomial (n+1) (1+u) (1+v) := by
  rw [←Equiv.sum_comp (strictIndexTailEquiv (fun _ : Fin (n+1) ↦ 1)).symm,
    Fintype.sum_prod_type]
  have hw (a : Fin 1)
      (z : PairedPowerIndex (fun _ : Fin n ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1) 2) :
      wordColor u v ((strictIndexTailEquiv (fun _ : Fin (n+1) ↦ 1)).symm (a,z)).1=
        wordColor u v z.1 := by
    change wordColor u v (wordCons z.1)=wordColor u v z.1
    exact wordColor_wordCons u v z.1
  simp only [hw,Finset.sum_const,Finset.card_univ,Fintype.card_fin,one_nsmul]
  exact paired_tail_color_sum (n := n) u v

end PaperVerification.Fermion.ColorPaths

namespace PaperVerification.Fermion.TypeA

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

theorem strict_paper_color_sum (hn : 0<n) (u v : F) :
    (∑ z : StrictIndex (data (F := F) hn),diagonalMonomialWeight u v hn z)=
      Eulerian.permutationPolynomial n (1+u) (1+v) := by
  cases n with
  | zero => omega
  | succ n =>
      rw [←Equiv.sum_comp (strictIndexEquiv (data (F := F) hn)).symm]
      have hw (z : StrictPowerIndex (fun _ : Fin (n+1) ↦ 1)) :
          diagonalMonomialWeight u v hn ((strictIndexEquiv (data hn)).symm z)=
            ColorPaths.wordColor u v z.1 := by
        rw [ColorPaths.wordColor_eq_left_right]
        rfl
      calc
        _ = ∑ z : StrictPowerIndex (fun _ : Fin (n+1) ↦ 1),
            ColorPaths.wordColor u v z.1 := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hw z
        _ = _ := ColorPaths.strict_tail_color_sum (n := n) u v

/-- Equation (23) at the actual diagonal action: the trace on the original
strict quotient is the genuine permutation ascent/descent sum. -/
theorem diagonal_trace_eq_eulerian (hn : 0<n)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
    LinearMap.trace F (StrictQuotient (fun _ ↦ (1 : F)) (fun i : Fin n ↦ MvPolynomial.X i))
      (ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)).toLinearMap =
        Eulerian.permutationPolynomial n (1+g.val 0 0) (1+g.val 1 1) := by
  rw [diagonal_trace_eq_box_sum hn g h01 h10,strict_paper_color_sum]

end PaperVerification.Fermion.TypeA
