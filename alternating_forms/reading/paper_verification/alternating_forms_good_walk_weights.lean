module

public import PaperVerification.AlternatingFormsGoodWalkEquiv
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The bijection preserves the original two exterior degrees

The odd original positions are exactly the first positions in the paired
steps; the fixed initial position contributes zero.  An explicit bijection
between selected odd letters and selected first slots proves equality of the
`a` degrees.  The endpoint conservation law then gives the `b` degree.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace PaperVerification.AlternatingForms.GoodPaths

open BigradedTransfer

def indexADegree {s n : ℕ} (I : Fin s → Fin n) : ℕ :=
  ∑ i,if (I i).val%2=1 then 1 else 0

theorem indexADegree_le {s n : ℕ} (I : Fin s → Fin n) : indexADegree I≤s := by
  calc
    indexADegree I≤∑ i : Fin s,(1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs <;> omega
    _ = s := by simp

theorem selectedAt_eq_one_iff {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) :
    selectedAt I q=1 ↔ ∃ i,(I i).val+1=q := by simp [selectedAt]

/-- Every selected original odd position is the first slot of exactly one
pair, and every selected first slot comes from one such original position. -/
def selectedOddSlotEquiv {k s : ℕ} (I : Fin s → Fin (2*k+1)) (hI : StrictMono I) :
    {i : Fin s // (I i).val%2=1} ≃
      {r : Fin (k+1) // selectedAt I (2*r.val)=1} := by
  let f : {i : Fin s // (I i).val%2=1} →
      {r : Fin (k+1) // selectedAt I (2*r.val)=1} := fun i =>
    ⟨⟨((I i.val).val+1)/2,by have := (I i.val).isLt; omega⟩,by
      change selectedAt I (2*(((I i.val).val+1)/2))=1
      rw [selectedAt_eq_one_iff]
      refine ⟨i.val,?_⟩
      change (I i.val).val+1=2*(((I i.val).val+1)/2)
      have hi := i.property
      omega⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro i j he
    apply Subtype.ext
    apply hI.injective
    apply Fin.ext
    have hv := congrArg (fun r : {r : Fin (k+1) // selectedAt I (2*r.val)=1} => r.val.val) he
    have hi := i.property
    have hj := j.property
    change ((I i.val).val+1)/2=((I j.val).val+1)/2 at hv
    omega
  · intro r
    obtain ⟨i,hi⟩ := (selectedAt_eq_one_iff I (2*r.val.val)).mp r.property
    have hip : (I i).val%2=1 := by omega
    refine ⟨⟨i,hip⟩,?_⟩
    apply Subtype.ext
    apply Fin.ext
    change ((I i).val+1)/2=r.val.val
    omega

theorem indexADegree_eq_pair_slots {k s : ℕ}
    (I : Fin s → Fin (2*k+1)) (hI : StrictMono I) :
    indexADegree I=∑ r : Fin (k+1),selectedAt I (2*r.val) := by
  have he := Fintype.card_congr (selectedOddSlotEquiv I hI)
  rw [Fintype.card_subtype,Fintype.card_subtype] at he
  rw [indexADegree,Finset.sum_boole]
  rw [he]
  symm
  calc
    (∑ r : Fin (k+1),selectedAt I (2*r.val))=
        ∑ r : Fin (k+1),if selectedAt I (2*r.val)=1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      have hle := selectedAt_le_one I (2*r.val)
      split_ifs <;> omega
    _ = _ := Finset.sum_boole _ _

theorem goodIndexToWalk_aDegree {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s) :
    walkADegree (k+1-s) (goodIndexToWalk hs I)=indexADegree I.val.val := by
  rw [walkADegree_eq_sum_marks,goodIndexToWalk_marks]
  simp only [pairedMark_a]
  exact (indexADegree_eq_pair_slots I.val.val I.val.property).symm

theorem goodIndexToWalk_bDegree {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s) :
    walkBDegree (k+1-s) (goodIndexToWalk hs I)=s-indexADegree I.val.val := by
  have he := walk_degree_balance (k+1-s) (k+1) 0 (Fin.last (k+1-s))
    (goodIndexToWalk hs I)
  rw [goodIndexToWalk_aDegree] at he
  change indexADegree I.val.val+walkBDegree (k+1-s) (goodIndexToWalk hs I)+(k+1-s)=0+(k+1) at he
  omega

/-- Exact preservation of the literal original exterior monomial weight. -/
theorem goodIndexToWalk_weight {R : Type*} [CommRing R] {k s : ℕ}
    (hs : s≤k+1) (I : GoodPathIndex k s) (u v : R) :
    walkWeight (k+1-s) u v (goodIndexToWalk hs I)=
      u^indexADegree I.val.val*v^(s-indexADegree I.val.val) := by
  rw [walkWeight_eq_degrees,goodIndexToWalk_aDegree,goodIndexToWalk_bDegree]

/-- The weighted sum over every good exterior word is the actual transfer
matrix corner, for every `k` and every printed degree `0≤s≤k+1`. -/
theorem good_index_weight_sum {R : Type*} [CommRing R] (k s : ℕ)
    (hs : s≤k+1) (u v : R) :
    (∑ I : GoodPathIndex k s,u^indexADegree I.val.val*v^(s-indexADegree I.val.val))=
      (transferMatrix (k+1-s) u v ^ (k+1)) 0 (Fin.last (k+1-s)) := by
  calc
    _ = ∑ I : GoodPathIndex k s,walkWeight (k+1-s) u v (goodIndexWalkEquiv k s hs I) := by
      apply Finset.sum_congr rfl
      intro I hI
      exact (goodIndexToWalk_weight hs I u v).symm
    _ = ∑ p : ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s)),
        walkWeight (k+1-s) u v p := Equiv.sum_comp (goodIndexWalkEquiv k s hs) _
    _ = _ := coloredWalk_weight_sum (k+1-s) (k+1) u v 0 (Fin.last (k+1-s))

end PaperVerification.AlternatingForms.GoodPaths
