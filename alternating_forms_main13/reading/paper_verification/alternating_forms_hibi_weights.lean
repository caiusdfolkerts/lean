module

public import PaperVerification.AlternatingFormsHibiPresentation
public import PaperVerification.WeightedInitialFiber
import Mathlib.Tactic.Linarith

/-!
# The positive rank-square weight for the literal Hibi relations

The interval rank is the sum of the coordinate increments above its lower
endpoint. Meet and join preserve the sum of the two ranks, and an incomparable
pair strictly increases their separation. Complementing their squares by a
uniform positive constant gives the paper's strictly decreasing sorting
weight, with no order or termination hypothesis supplied.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open scoped BigOperators

variable {s n : ℕ} (α β : Fin s → Fin n)

def intervalRank (I : IntervalIndex α β) : ℕ := ∑ i, ((I.val.val i).val-(α i).val)
def rankBound : ℕ := ∑ i, ((β i).val-(α i).val)

theorem intervalRank_le_bound (I : IntervalIndex α β) : intervalRank α β I ≤ rankBound α β := by
  unfold intervalRank rankBound
  apply Finset.sum_le_sum
  intro i hi
  have h := (I.property i).2
  exact Nat.sub_le_sub_right h _

theorem intervalRank_strict (I J : IntervalIndex α β) (hle : I ≤ J) (hne : I≠J) :
    intervalRank α β I < intervalRank α β J := by
  have hex : ∃ i,I.val.val i≠J.val.val i := by
    by_contra h
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact Classical.not_not.mp (fun hi => h ⟨i,hi⟩)
  obtain ⟨j,hj⟩ := hex
  unfold intervalRank
  apply Finset.sum_lt_sum
  · intro i hi
    exact Nat.sub_le_sub_right (hle i) _
  · refine ⟨j,Finset.mem_univ _,?_⟩
    have h1 : (I.val.val j).val ≤ (J.val.val j).val := hle j
    have h2 : (α j).val ≤ (I.val.val j).val := (I.property j).1
    have h3 : (I.val.val j).val≠(J.val.val j).val := fun h => hj (Fin.ext h)
    omega

theorem intervalRank_meet_join (I J : IntervalIndex α β) :
    intervalRank α β (meet α β I J)+intervalRank α β (join α β I J)=
      intervalRank α β I+intervalRank α β J := by
  unfold intervalRank
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : I.val.val i ≤ J.val.val i
  · simp only [meet,join,min_eq_left h,max_eq_right h]
  · have h' : J.val.val i ≤ I.val.val i := le_of_not_ge h
    simp only [meet,join,min_eq_right h',max_eq_left h',add_comm]

theorem intervalRank_meet_lt_left (I J : IntervalIndex α β)
    (h : incomparable α β I J) :
    intervalRank α β (meet α β I J) < intervalRank α β I := by
  apply intervalRank_strict α β _ _ (meet_le_left α β I J)
  intro he
  exact h.1 (he ▸ meet_le_right α β I J)

theorem intervalRank_meet_lt_right (I J : IntervalIndex α β)
    (h : incomparable α β I J) :
    intervalRank α β (meet α β I J) < intervalRank α β J := by
  apply intervalRank_strict α β _ _ (meet_le_right α β I J)
  intro he
  exact h.2 (he ▸ meet_le_left α β I J)

def sortingWeight (I : IntervalIndex α β) : ℕ :=
  (rankBound α β)^2+1-(intervalRank α β I)^2

theorem sortingWeight_positive (I : IntervalIndex α β) : 0 < sortingWeight α β I := by
  have h := intervalRank_le_bound α β I
  have hsq : (intervalRank α β I)^2 ≤ (rankBound α β)^2 := pow_le_pow_left' h 2
  unfold sortingWeight
  omega

theorem sortingWeight_decreases (I J : IntervalIndex α β)
    (h : incomparable α β I J) :
    sortingWeight α β (meet α β I J)+sortingWeight α β (join α β I J) < 
      sortingWeight α β I+sortingWeight α β J := by
  let a := intervalRank α β (meet α β I J)
  let b := intervalRank α β I
  let c := intervalRank α β J
  let d := intervalRank α β (join α β I J)
  have hab : a < b := intervalRank_meet_lt_left α β I J h
  have hac : a < c := intervalRank_meet_lt_right α β I J h
  have hsum : a+d=b+c := intervalRank_meet_join α β I J
  have habZ : (a : ℤ) < b := by exact_mod_cast hab
  have hacZ : (a : ℤ) < c := by exact_mod_cast hac
  have hp : (0 : ℤ) < ((b : ℤ)-a)*((c : ℤ)-a) :=
    mul_pos (sub_pos.mpr habZ) (sub_pos.mpr hacZ)
  have hsumZ : (a : ℤ)+d=b+c := by exact_mod_cast hsum
  have hsquareZ : (b : ℤ)^2+c^2 < a^2+d^2 := by nlinarith
  have hsquare : b^2+c^2 < a^2+d^2 := by exact_mod_cast hsquareZ
  have ha := pow_le_pow_left' (intervalRank_le_bound α β (meet α β I J)) 2
  have hb := pow_le_pow_left' (intervalRank_le_bound α β I) 2
  have hc := pow_le_pow_left' (intervalRank_le_bound α β J) 2
  have hd := pow_le_pow_left' (intervalRank_le_bound α β (join α β I J)) 2
  change (rankBound α β)^2+1-a^2+((rankBound α β)^2+1-d^2) < 
    (rankBound α β)^2+1-b^2+((rankBound α β)^2+1-c^2)
  dsimp only [a,b,c,d] at hsquare ⊢
  omega

variable {K : Type*} [Field K]

/-- The proposed quadratic monomial initial ideal, with exactly the
incomparable pairs as generators. -/
def incomparableIdeal : Ideal (MvPolynomial (IntervalIndex α β) K) :=
  Ideal.span {p | ∃ I J,incomparable α β I J ∧ p=MvPolynomial.X I*MvPolynomial.X J}

theorem relation_top (I J : IntervalIndex α β) (h : incomparable α β I J) :
    MvPolynomial.weightedHomogeneousComponent (sortingWeight α β)
      (sortingWeight α β I+sortingWeight α β J) (relation (K := K) α β I J)=
        MvPolynomial.X I*MvPolynomial.X J := by
  have hleft := (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) I).mul
    (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) J)
  have hright :=
    (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) (meet α β I J)).mul
      (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) (join α β I J))
  have hne := (sortingWeight_decreases α β I J h).ne'
  rw [relation,map_sub,MvPolynomial.weightedHomogeneousComponent_of_mem hleft,
    MvPolynomial.weightedHomogeneousComponent_of_mem hright]
  simp only [ite_true,if_neg hne,sub_zero]

theorem relation_weightBound (I J : IntervalIndex α β) (h : incomparable α β I J) :
    WeightedInitialFiber.WeightBound (sortingWeight α β)
      (sortingWeight α β I+sortingWeight α β J) (relation (K := K) α β I J) := by
  have hleft := (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) I).mul
    (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) J)
  have hright :=
    (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) (meet α β I J)).mul
      (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) (join α β I J))
  intro a ha
  by_cases hl : (MvPolynomial.X I*MvPolynomial.X J :
      MvPolynomial (IntervalIndex α β) K).coeff a=0
  · have hr : (MvPolynomial.X (meet α β I J)*MvPolynomial.X (join α β I J) :
        MvPolynomial (IntervalIndex α β) K).coeff a≠0 := by
      intro hr
      exact ha (by simp only [relation,MvPolynomial.coeff_sub,hl,hr,sub_zero])
    exact (hright hr).le.trans (sortingWeight_decreases α β I J h).le
  · exact (hleft hl).le

theorem incomparableIdeal_le_initial :
    incomparableIdeal (K := K) α β ≤ 
      WeightedInitialFiber.initialIdeal (relationIdeal α β) (sortingWeight α β) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨I,J,h,rfl⟩
  rw [←relation_top α β I J h]
  exact WeightedInitialFiber.component_mem_initialIdeal _ _ _
    (relation_mem α β I J) _ (relation_weightBound α β I J h)

end PaperVerification.AlternatingForms.Hibi
