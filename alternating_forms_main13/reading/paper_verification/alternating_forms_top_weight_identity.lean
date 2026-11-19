module

public import PaperVerification.AlternatingFormsSymmetricPencilWeights
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The complete torus-weight identity, with its determinant twist

The exterior quotient and the plethysm have different central characters
as representations of `GL₂`.  The explicit integer `determinantTwist`
corrects this difference.  Its disappearance on `SL₂` is used only in the
final representation theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.TopInterlacing

open SymmetricPencil

def finIndexSum (n : ℕ) : ℤ := ∑ i : Fin n, (i.val : ℤ)

theorem finIndexSum_succ (n : ℕ) : finIndexSum (n+1)=finIndexSum n+n := by
  rw [finIndexSum, Fin.sum_univ_castSucc]
  rfl

theorem twice_finIndexSum_succ (n : ℕ) :
    2*finIndexSum (n+1)=(n : ℤ)*(n+1) := by
  induction n with
  | zero => simp [finIndexSum]
  | succ n ih =>
      rw [finIndexSum_succ (n+1)]
      push_cast
      nlinarith

theorem finIndexSum_pair (p : ℕ) : finIndexSum p+finIndexSum (p+1)=(p : ℤ)^2 := by
  have h := twice_finIndexSum_succ p
  rw [finIndexSum_succ] at h ⊢
  nlinarith

def weakSum {p q : ℕ} (I : Interlacing p q) : ℤ :=
  ∑ j : Fin (2*p+1), ((toWeakWord I).val j).val

def aSum {p q : ℕ} (I : Interlacing p q) : ℤ := ∑ i : Fin p, (I.val.1 i).val
def cSum {p q : ℕ} (I : Interlacing p q) : ℤ := ∑ i : Fin (p+1), (I.val.2 i).val

theorem weakSum_add_square {p q : ℕ} (I : Interlacing p q) :
    weakSum I+(p : ℤ)^2=aSum I+cSum I := by
  have he : weakSum I =
      (∑ i : Fin p, (((I.val.1 i).val : ℤ)-i.val)) +
        (∑ i : Fin (p+1), (((I.val.2 i).val : ℤ)-i.val)) := by
    rw [weakSum, ← Equiv.sum_comp (abIndex p), Fintype.sum_sum_type]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      change (weakValue I (abIndex p (.inl i)) : ℤ)=_
      rw [weakValue_a, Nat.cast_sub (strictMonoFin_lower _ I.property.1 i)]
    · apply Finset.sum_congr rfl
      intro i hi
      change (weakValue I (abIndex p (.inr i)) : ℤ)=_
      rw [weakValue_c, Nat.cast_sub (strictMonoFin_lower _ I.property.2.1 i)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at he
  change weakSum I=aSum I-finIndexSum p+(cSum I-finIndexSum (p+1)) at he
  have h := finIndexSum_pair p
  omega

/-- The integral determinant power required before restricting to `SL₂`. -/
def determinantTwist (p q : ℕ) : ℤ :=
  (p : ℤ)^2-finIndexSum (p+q+1)+((p : ℤ)+q)*q-(p : ℤ)*(p+q-1 : ℤ)

theorem determinantTwist_central (p q : ℕ) :
    2*determinantTwist p q =
      -(p : ℤ)*(p+q-1 : ℤ)+(q : ℤ)*(p+q)-q*(2*p+1) := by
  have hs := twice_finIndexSum_succ (p+q)
  unfold determinantTwist
  push_cast at hs ⊢
  nlinarith

theorem prod_zpow_sum {G ι : Type*} [CommGroup G] (S : Finset ι) (f : ι → ℤ) (a : G) :
    ∏ i ∈ S, a^(f i) = a^(∑ i ∈ S, f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi, ih, zpow_add]

def symmetricWeight {K : Type*} [Field K] (q r : ℕ) (u : Fin 2 → Kˣ)
    (S : Sym (Fin (q+1)) r) : Kˣ :=
  ((S : Multiset (Fin (q+1))).map
    (fun i => u 0^(i.val : ℤ)*u 1^((q : ℤ)-i.val))).prod

theorem symmetricWeight_interlacing {K : Type*} [Field K] {p q : ℕ}
    (u : Fin 2 → Kˣ) (I : Interlacing p q) :
    symmetricWeight q (2*p+1) u (interlacingSymEquiv p q I) =
      u 0^(weakSum I)*u 1^((q : ℤ)*(2*p+1)-weakSum I) := by
  change ((TauCeti.Sym.ofFn (toWeakWord I).val : Multiset (Fin (q+1))).map _).prod=_
  rw [TauCeti.Sym.coe_ofFn, Multiset.map_coe, Multiset.prod_coe,
    List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply]
  rw [Finset.prod_mul_distrib,
    prod_zpow_sum, prod_zpow_sum]
  congr 1
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  change ((2*p+1 : ℕ) : ℤ)*q-weakSum I=(q : ℤ)*(2*p+1)-weakSum I
  push_cast
  ring

theorem wordWeight_of_selectedAB {K : Type} [Field K] {k s : ℕ}
    (u : Fin 2 → Kˣ) (I : Fin s → Fin (2*k+1)) (hI : StrictMono I)
    (A : Finset (Fin k)) (B : Finset (Fin (k+1)))
    (hS : GoodPaths.selectedSet I=selectedAB A B) :
    wordWeight K u I = (∏ i ∈ A, aWeight K k u i)*(∏ i ∈ B, bWeight K k u i) := by
  have he : wordWeight K u I = ∏ j ∈ GoodPaths.selectedSet I, indexWeight K k u j := by
    rw [GoodPaths.selectedSet, Finset.prod_image]
    · rfl
    · intro a ha b hb hab
      exact hI.injective hab
  rw [he, hS, selectedAB, Finset.prod_map, Finset.prod_disjSum]
  change (∏ i ∈ A, indexWeight K k u (abIndex k (.inl i))) *
      (∏ i ∈ B, indexWeight K k u (abIndex k (.inr i))) = _
  simp only [indexWeight_a, indexWeight_b]

theorem pairWeight_formula {K : Type} [Field K] {k : ℕ} (u : Fin 2 → Kˣ)
    (A : Finset (Fin k)) (B : Finset (Fin (k+1))) :
    (∏ i ∈ A, aWeight K k u i)*(∏ i ∈ B, bWeight K k u i) =
      u 0^((∑ i ∈ A, (i.val : ℤ))-(A.card : ℤ)*(k-1)+(B.card : ℤ)*k-
        ∑ i ∈ B, (i.val : ℤ)) *
      u 1^((∑ i ∈ B, (i.val : ℤ))-∑ i ∈ A, (i.val : ℤ)) := by
  simp only [aWeight, bWeight, Finset.prod_mul_distrib, prod_zpow_sum]
  rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]
  congr 1
  · congr 1
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul]
    ring
  · congr 1
    rw [Finset.sum_neg_distrib]
    ring

theorem interlacing_wordWeight {K : Type} [Field K] {p q : ℕ}
    (u : Fin 2 → Kˣ) (I : Interlacing p q) :
    wordWeight K u (goodPairToTopWord (interlacingToGoodPair I)).val.val.val =
      (u 0*u 1)^(determinantTwist p q) *
        symmetricWeight q (2*p+1) u (interlacingSymEquiv p q I) := by
  let P := interlacingToGoodPair I
  let A := P.val.1
  let C := P.val.2
  let B := Cᶜ
  have ha : A.card=p := P.property.1
  have hc : C.card=p+1 := P.property.2.1
  have hb : B.card=q := by
    dsimp only [B]
    rw [Finset.card_compl, Fintype.card_fin, hc]
    omega
  have hsa : (∑ i ∈ A, (i.val : ℤ))=aSum I := by
    change (∑ i ∈ GoodPaths.selectedSet I.val.1, (i.val : ℤ))=aSum I
    rw [GoodPaths.selectedSet, Finset.sum_image]
    · rfl
    · intro i hi j hj hij
      exact I.property.1.injective hij
  have hsc : (∑ i ∈ C, (i.val : ℤ))=cSum I := by
    change (∑ i ∈ GoodPaths.selectedSet I.val.2, (i.val : ℤ))=cSum I
    rw [GoodPaths.selectedSet, Finset.sum_image]
    · rfl
    · intro i hi j hj hij
      exact I.property.2.1.injective hij
  have hsb : (∑ i ∈ B, (i.val : ℤ))=finIndexSum (p+q+1)-cSum I := by
    have h := C.sum_add_sum_compl (fun i => (i.val : ℤ))
    rw [hsc] at h
    change cSum I+(∑ i ∈ B, (i.val : ℤ))=finIndexSum (p+q+1) at h
    omega
  have hz := weakSum_add_square I
  have hs := twice_finIndexSum_succ (p+q)
  rw [wordWeight_of_selectedAB u _ (goodPairToTopWord P).val.val.property A B
      (goodPairToTopWord_selected P), pairWeight_formula, ha, hb, hsa, hsb,
    symmetricWeight_interlacing, mul_zpow, mul_mul_mul_comm, ← zpow_add, ← zpow_add]
  congr 1
  · congr 1
    unfold determinantTwist
    push_cast at *
    nlinarith
  · congr 1
    unfold determinantTwist
    push_cast at *
    nlinarith

/-- The full torus character identity on the exact actual good-word index
set, with the indispensable determinant factor retained. -/
theorem topWord_weight_sum {K : Type} [Field K] (p q : ℕ) (u : Fin 2 → Kˣ) :
    (∑ W : TopWord p q, (wordWeight K u W.val.val.val : K)) =
      (((u 0*u 1)^(determinantTwist p q) : Kˣ) : K) *
        ∑ S : Sym (Fin (q+1)) (2*p+1), (symmetricWeight q (2*p+1) u S : K) := by
  rw [← Equiv.sum_comp (topWordInterlacingEquiv p q).symm]
  have hw (I : Interlacing p q) :
      (topWordInterlacingEquiv p q).symm I=goodPairToTopWord (interlacingToGoodPair I) := rfl
  simp_rw [hw, interlacing_wordWeight, Units.val_mul]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (interlacingSymEquiv p q)
    (fun S : Sym (Fin (q+1)) (2*p+1) => (symmetricWeight q (2*p+1) u S : K))

end PaperVerification.AlternatingForms.TopInterlacing
