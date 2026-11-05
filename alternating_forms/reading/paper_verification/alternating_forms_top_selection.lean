module

public import PaperVerification.AlternatingFormsTopInterlacing
public import PaperVerification.AlternatingFormsBigradedPieces
public import PaperVerification.AlternatingFormsGoodPathBounds
public import PaperVerification.AlternatingFormsBooleanGoodSubsets
import Lean.Elab.Tactic.Omega

/-!
# The original good words are exactly the interlacing selections

The `a`-set is selected and the `c`-set is the complement of the selected
`b`-set.  The strip inequalities are equivalent to the two prefix-count
inequalities below.  Sorting then recovers the interlacing inequalities.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.TopInterlacing

open BooleanWalks

theorem prefix_compl_add {n : ℕ} (C : Finset (Fin n)) (r : ℕ) (hr : r≤n) :
    prefixCount C r + prefixCount Cᶜ r = r := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i : Fin n => i.val<r)) (fun i => i∈C)
  have h₁ : (Finset.univ.filter (fun i : Fin n => i.val<r)).filter (fun i => i∈C) =
      C.filter (fun i => i.val<r) := by
    ext i
    simp [and_comm]
  have h₂ : (Finset.univ.filter (fun i : Fin n => i.val<r)).filter (fun i => ¬i∈C) =
      Cᶜ.filter (fun i => i.val<r) := by
    ext i
    simp [and_comm]
  rw [h₁, h₂, Fin.card_filter_val_lt, Nat.min_eq_right hr] at h
  exact h

theorem prefixCount_mono {n : ℕ} (C : Finset (Fin n)) : Monotone (prefixCount C) := by
  intro a b hab
  apply Finset.card_le_card
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨hi,hia⟩
  exact Finset.mem_filter.mpr ⟨hi, hia.trans_le hab⟩

theorem index_lt_prefix_iff {m n : ℕ} (S : Finset (Fin n)) (hS : S.card=m)
    (i : Fin m) (r : ℕ) :
    i.val < prefixCount S r ↔ (S.orderEmbOfFin hS i).val < r := by
  have he : prefixCount S r =
      (Finset.univ.filter (fun j : Fin m => (S.orderEmbOfFin hS j).val<r)).card := by
    conv_lhs => rw [← Finset.image_orderEmbOfFin_univ S hS]
    rw [prefixCount, Finset.filter_image,
      Finset.card_image_of_injective _ (S.orderEmbOfFin hS).injective]
  rw [he]
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro a b hba ha
  have hb : (S.orderEmbOfFin hS b).val ≤ (S.orderEmbOfFin hS a).val :=
    (S.orderEmbOfFin hS).monotone hba
  omega

theorem prefix_at_index {m n : ℕ} (S : Finset (Fin n)) (hS : S.card=m) (i : Fin m) :
    prefixCount S (S.orderEmbOfFin hS i).val=i.val := by
  have he' (r : ℕ) : prefixCount S r =
      (Finset.univ.filter (fun j : Fin m => (S.orderEmbOfFin hS j).val < r)).card := by
    conv_lhs => rw [← Finset.image_orderEmbOfFin_univ S hS]
    rw [prefixCount, Finset.filter_image,
      Finset.card_image_of_injective _ (S.orderEmbOfFin hS).injective]
  have he : prefixCount S (S.orderEmbOfFin hS i).val =
      (Finset.univ.filter (fun j : Fin m => j < i)).card := by
    rw [he']
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (S.orderEmbOfFin hS).lt_iff_lt
  rw [he]
  have hf : (Finset.univ.filter (fun j : Fin m => j < i))=Finset.Iio i := by
    ext j
    simp
  rw [hf, Fin.card_Iio]

theorem prefix_after_index {m n : ℕ} (S : Finset (Fin n)) (hS : S.card=m) (i : Fin m) :
    prefixCount S ((S.orderEmbOfFin hS i).val+1)=i.val+1 := by
  rw [prefixCount_succ, prefix_at_index, selectedAt_position,
    if_pos (S.orderEmbOfFin_mem hS i)]

def GoodPair (p q : ℕ) :=
  {AC : Finset (Fin (p+q)) × Finset (Fin (p+q+1)) //
    AC.1.card=p ∧ AC.2.card=p+1 ∧ ∀ r, r≤p+q →
      prefixCount AC.1 r ≤ prefixCount AC.2 r ∧
        prefixCount AC.2 (r+1) ≤ prefixCount AC.1 r+1}

instance (p q : ℕ) : Fintype (GoodPair p q) := by
  unfold GoodPair
  infer_instance

def goodPairToInterlacing {p q : ℕ} (P : GoodPair p q) : Interlacing p q :=
  ⟨(P.val.1.orderEmbOfFin P.property.1, P.val.2.orderEmbOfFin P.property.2.1),
    (P.val.1.orderEmbOfFin P.property.1).strictMono,
    (P.val.2.orderEmbOfFin P.property.2.1).strictMono, by
      intro i
      change (P.val.2.orderEmbOfFin P.property.2.1 i.castSucc).val ≤
          (P.val.1.orderEmbOfFin P.property.1 i).val ∧
        (P.val.1.orderEmbOfFin P.property.1 i).val <
          (P.val.2.orderEmbOfFin P.property.2.1 i.succ).val
      constructor
      · have hi := (P.val.1.orderEmbOfFin P.property.1 i).isLt
        have hp := (P.property.2.2 ((P.val.1.orderEmbOfFin P.property.1 i).val+1)
          (by omega)).1
        rw [prefix_after_index] at hp
        have hc := (index_lt_prefix_iff P.val.2 P.property.2.1 i.castSucc
          ((P.val.1.orderEmbOfFin P.property.1 i).val+1)).mp (by simpa using hp)
        omega
      · have hi := (P.val.2.orderEmbOfFin P.property.2.1 i.succ).isLt
        have hp := (P.property.2.2 (P.val.2.orderEmbOfFin P.property.2.1 i.succ).val
          (by omega)).2
        rw [prefix_after_index] at hp
        have ha := (index_lt_prefix_iff P.val.1 P.property.1 i
          (P.val.2.orderEmbOfFin P.property.2.1 i.succ).val).mp (by
            simp only [Fin.val_succ] at hp
            omega)
        exact ha⟩

def interlacingToGoodPair {p q : ℕ} (I : Interlacing p q) : GoodPair p q := by
  let A := GoodPaths.selectedSet I.val.1
  let C := GoodPaths.selectedSet I.val.2
  have ha : A.card=p := GoodPaths.selectedSet_card I.property.1
  have hc : C.card=p+1 := GoodPaths.selectedSet_card I.property.2.1
  have hea : A.orderEmbOfFin ha=I.val.1 :=
    (Finset.orderEmbOfFin_unique ha
      (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) I.property.1).symm
  have hec : C.orderEmbOfFin hc=I.val.2 :=
    (Finset.orderEmbOfFin_unique hc
      (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) I.property.2.1).symm
  refine ⟨(A,C), ha, hc, ?_⟩
  intro r hr
  change prefixCount A r ≤ prefixCount C r ∧
    prefixCount C (r+1) ≤ prefixCount A r+1
  constructor
  · by_contra h
    have hA := (prefixCount_le A r).trans_eq ha
    let i : Fin p := ⟨prefixCount C r, by omega⟩
    have hai := (index_lt_prefix_iff A ha i r).mp (by dsimp [i]; omega)
    have hci := (index_lt_prefix_iff C hc i.castSucc r).not.mp (by dsimp [i]; omega)
    rw [hea] at hai
    rw [hec] at hci
    have hb := (I.property.2.2 i).1
    omega
  · by_contra h
    have hC := (prefixCount_le C (r+1)).trans_eq hc
    let i : Fin p := ⟨prefixCount A r, by omega⟩
    have hci := (index_lt_prefix_iff C hc i.succ (r+1)).mp (by dsimp [i]; omega)
    have hai := (index_lt_prefix_iff A ha i r).not.mp (by dsimp [i]; omega)
    rw [hea] at hai
    rw [hec] at hci
    have hb := (I.property.2.2 i).2
    omega

def goodPairInterlacingEquiv (p q : ℕ) : GoodPair p q ≃ Interlacing p q where
  toFun := goodPairToInterlacing
  invFun := interlacingToGoodPair
  left_inv P := by
    apply Subtype.ext
    apply Prod.ext
    · exact Finset.image_orderEmbOfFin_univ P.val.1 P.property.1
    · exact Finset.image_orderEmbOfFin_univ P.val.2 P.property.2.1
  right_inv I := by
    apply Subtype.ext
    apply Prod.ext
    · exact (Finset.orderEmbOfFin_unique (GoodPaths.selectedSet_card I.property.1)
        (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) I.property.1).symm
    · exact (Finset.orderEmbOfFin_unique (GoodPaths.selectedSet_card I.property.2.1)
        (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) I.property.2.1).symm

def selectedAB {k : ℕ} (A : Finset (Fin k)) (B : Finset (Fin (k+1))) :
    Finset (Fin (2*k+1)) := (A.disjSum B).map (abIndex k).toEmbedding

def originalPrefix {k : ℕ} (S : Finset (Fin (2*k+1))) (r : ℕ) : ℕ :=
  (S.filter (fun i => i.val+1<r)).card

theorem originalPrefix_selectedAB {k : ℕ} (A : Finset (Fin k))
    (B : Finset (Fin (k+1))) (r : ℕ) :
    originalPrefix (selectedAB A B) r =
      (A.filter (fun i => 2*i.val+2<r)).card +
        (B.filter (fun i => 2*i.val+1<r)).card := by
  rw [originalPrefix, selectedAB, Finset.filter_map, Finset.card_map]
  have he : (A.disjSum B).filter (fun x => (abIndex k x).val+1<r) =
      (A.filter (fun i => 2*i.val+2<r)).disjSum
        (B.filter (fun i => 2*i.val+1<r)) := by
    ext x
    cases x with
    | inl i =>
        simp only [Finset.mem_filter, Finset.inl_mem_disjSum]
        change (i∈A ∧ (2*i.val+1)+1<r) ↔ (i∈A ∧ 2*i.val+2<r)
        exact and_congr_right (fun _ => by omega)
    | inr i =>
        simp only [Finset.mem_filter, Finset.inr_mem_disjSum]
        rfl
  change ((A.disjSum B).filter (fun x => (abIndex k x).val+1<r)).card = _
  rw [he, Finset.card_disjSum]

theorem originalPrefix_odd {k : ℕ} (A : Finset (Fin k))
    (B : Finset (Fin (k+1))) (r : ℕ) :
    originalPrefix (selectedAB A B) (2*r+1) = prefixCount A r+prefixCount B r := by
  rw [originalPrefix_selectedAB]
  have ha : A.filter (fun i => 2*i.val+2<2*r+1)=A.filter (fun i => i.val<r) := by
    ext i
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => by omega)
  have hb : B.filter (fun i => 2*i.val+1<2*r+1)=B.filter (fun i => i.val<r) := by
    ext i
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => by omega)
  rw [ha,hb]
  rfl

theorem originalPrefix_even {k : ℕ} (A : Finset (Fin k))
    (B : Finset (Fin (k+1))) (r : ℕ) :
    originalPrefix (selectedAB A B) (2*r+2) = prefixCount A r+prefixCount B (r+1) := by
  rw [originalPrefix_selectedAB]
  have ha : A.filter (fun i => 2*i.val+2<2*r+2)=A.filter (fun i => i.val<r) := by
    ext i
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => by omega)
  have hb : B.filter (fun i => 2*i.val+1<2*r+2)=B.filter (fun i => i.val<r+1) := by
    ext i
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => by omega)
  rw [ha,hb]
  rfl

theorem selectedAB_strip_iff {p q : ℕ} (A : Finset (Fin (p+q)))
    (C : Finset (Fin (p+q+1))) (hA : A.card=p) (hC : C.card=p+1) :
    (∀ r, r≤2*(p+q)+3 →
      2*originalPrefix (selectedAB A Cᶜ) r≤r ∧
        r+2*(p+q)≤2*(p+q)+3+2*originalPrefix (selectedAB A Cᶜ) r) ↔
    (∀ r, r≤p+q → prefixCount A r≤prefixCount C r ∧
      prefixCount C (r+1)≤prefixCount A r+1) := by
  constructor
  · intro h r hr
    have ho := h (2*r+1) (by omega)
    have he := h (2*r+2) (by omega)
    rw [originalPrefix_odd] at ho
    rw [originalPrefix_even] at he
    have hc₁ := prefix_compl_add C r (by omega)
    have hc₂ := prefix_compl_add C (r+1) (by omega)
    constructor <;> omega
  · intro h r hr
    by_cases hz : r=0
    · subst r
      simp [originalPrefix]
    · by_cases hpar : r%2=1
      · let j := r/2
        have he : r=2*j+1 := by dsimp [j]; omega
        rw [he, originalPrefix_odd]
        by_cases hj : j≤p+q
        · have hp := h j hj
          have hc := prefix_compl_add C j (by omega)
          have hm : prefixCount C j ≤ prefixCount C (j+1) :=
            prefixCount_mono C (Nat.le_succ j)
          constructor <;> omega
        · have hj' : j=p+q+1 := by omega
          rw [hj', prefixCount_all A _ (by omega), prefixCount_all Cᶜ _ le_rfl,
            hA, Finset.card_compl, Fintype.card_fin, hC]
          constructor <;> omega
      · let j := r/2-1
        have he : r=2*j+2 := by dsimp [j]; omega
        have hj : j≤p+q := by omega
        rw [he, originalPrefix_even]
        have hp := h j hj
        have hc := prefix_compl_add C (j+1) (by omega)
        have hm : prefixCount C j ≤ prefixCount C (j+1) :=
          prefixCount_mono C (Nat.le_succ j)
        constructor <;> omega

end PaperVerification.AlternatingForms.TopInterlacing
