import Characterizations.TripleCount

/-! # A minimum family of universal variable-order tests -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Except (j : V) := {v : V // v ≠ j}

theorem card_except (j : V) : Fintype.card (Except j) = Fintype.card V - 1 := by
  simpa using Fintype.card_subtype_compl (fun v : V => v = j)

theorem exists_finalTriple_and_pair (i q j : V) (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) :
    ∃ o : VariableOrder V, FinalTriple o i q j ∧ FinalPair o q j := by
  let f : V → ℕ := fun x => if x = j then 3 else if x = q then 2 else if x = i then 1 else 0
  obtain ⟨o, ho⟩ := exists_order_refining f
  have hijO : o i < o j := ho i j (by simp [f, hij, hiq])
  have hqjO : o q < o j := ho q j (by simp [f, hqj])
  refine ⟨o, ⟨hijO, hqjO, ?_⟩, ⟨hqjO, ?_⟩⟩
  · intro t hti htq htj
    exact ⟨ho t i (by simp [f, hti, htq, htj, hiq, hij]),
      ho t q (by simp [f, hti, htq, htj, hqj])⟩
  · intro t htq htj
    apply ho
    simp only [f, if_neg htj, if_neg htq, if_neg hqj, ite_true]
    split_ifs <;> omega

theorem FinalTriple.swap {o : VariableOrder V} {i q j : V} (h : FinalTriple o i q j) :
    FinalTriple o q i j := ⟨h.2.1, h.1, fun x hxq hxi hxj => (h.2.2 x hxi hxq hxj).symm⟩

theorem FinalTriple.of_pair_eq {o : VariableOrder V} {i q a b j : V}
    (h : FinalTriple o a b j) (hiq : i ≠ q) (hab : a ≠ b)
    (he : ({i,q} : Finset V) = {a,b}) : FinalTriple o i q j := by
  have hi : i = a ∨ i = b := by
    have hh : i ∈ ({i,q} : Finset V) := by simp
    rw [he] at hh
    simpa using hh
  have hq : q = a ∨ q = b := by
    have hh : q ∈ ({i,q} : Finset V) := by simp
    rw [he] at hh
    simpa using hh
  rcases hi with rfl | rfl
  · have hqb : q = b := hq.resolve_left hiq.symm
    simpa [hqb] using h
  · have hqa : q = a := hq.resolve_right hiq.symm
    simpa [hqa] using h.swap

structure OrderedPoint (R : ∀ j : V, Except j → Except j → Prop) (P : PointedTriple V) where
  left : Except P.1
  right : Except P.1
  edge : R P.1 left right
  pair_eq : P.2.val = {left.val, right.val}
  order : VariableOrder V
  triple : FinalTriple order left.val right.val P.1
  finalPair : FinalPair order right.val P.1

theorem exists_orderedPoint (R : ∀ j : V, Except j → Except j → Prop)
    (hR : ∀ j a b, a ≠ b → R j a b ∨ R j b a) (P : PointedTriple V) :
    Nonempty (OrderedPoint R P) := by
  obtain ⟨i, q, hiq, hA⟩ := card_eq_two.mp P.2.property.2
  have hij : i ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  have hqj : q ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  let I : Except P.1 := ⟨i,hij⟩
  let Q : Except P.1 := ⟨q,hqj⟩
  rcases hR P.1 I Q (fun h => hiq (congrArg Subtype.val h)) with h | h
  · obtain ⟨o, ht, hp⟩ := exists_finalTriple_and_pair i q P.1 hiq hij hqj
    exact ⟨⟨I,Q,h,hA,o,ht,hp⟩⟩
  · obtain ⟨o, ht, hp⟩ := exists_finalTriple_and_pair q i P.1 hiq.symm hqj hij
    exact ⟨⟨Q,I,h,by simpa [pair_comm] using hA,o,ht,hp⟩⟩

/-- Exactly one order for every pointed final triple suffices, with the
orientations chosen so that every final pair is also covered. -/
theorem exists_optimal_order_family (hcard : 4 ≤ Fintype.card V) :
    ∃ F : Finset (VariableOrder V), CoversFinalPairs (F : Set (VariableOrder V)) ∧
      CoversFinalTriples (F : Set (VariableOrder V)) ∧
      F.card = Fintype.card V * (Fintype.card V - 1).choose 2 := by
  have hT (j : V) : ∃ R : Except j → Except j → Prop,
      (∀ a b, R a b → ¬ R b a) ∧
      (∀ a b, a ≠ b → R a b ∨ R b a) ∧ (∀ b, ∃ a, R a b) :=
    exists_incoming_tournament (Except j) (by rw [card_except]; omega)
  choose R hRasym hRtotal hRincoming using hT
  let chosen (P : PointedTriple V) : OrderedPoint R P := (exists_orderedPoint R hRtotal P).some
  let F : Finset (VariableOrder V) := univ.image (fun P : PointedTriple V => (chosen P).order)
  have hmem (P : PointedTriple V) : (chosen P).order ∈ F := mem_image.mpr ⟨P, mem_univ _, rfl⟩
  have hchosen_ne (P : PointedTriple V) : (chosen P).left ≠ (chosen P).right := by
    intro he
    have hh := (chosen P).edge
    have hh' : R P.1 (chosen P).right (chosen P).left := he ▸ hh
    exact hRasym P.1 _ _ hh hh'
  have htriples : CoversFinalTriples (F : Set (VariableOrder V)) := by
    intro i q j hiq hij hqj
    let P : PointedTriple V := ⟨j, ⟨{i,q}, by simp [insert_subset_iff, hij, hqj], by simp [hiq]⟩⟩
    refine ⟨(chosen P).order, hmem P, ?_⟩
    exact (chosen P).triple.of_pair_eq hiq
      (fun he => hchosen_ne P (Subtype.ext he)) (chosen P).pair_eq
  have hpairs : CoversFinalPairs (F : Set (VariableOrder V)) := by
    intro b j hbj
    let B : Except j := ⟨b,hbj⟩
    obtain ⟨A, hAB⟩ := hRincoming j B
    have hABne : A ≠ B := by
      intro he
      exact hRasym j _ _ hAB (he ▸ hAB)
    have hab : A.val ≠ b := fun he => hABne (Subtype.ext he)
    let P : PointedTriple V := ⟨j, ⟨{A.val,b},
      by simp [insert_subset_iff, A.property, hbj], by simp [hab]⟩⟩
    have hright : (chosen P).right.val = b := by
      have hrmem : (chosen P).right.val ∈ ({A.val,b} : Finset V) := by
        change (chosen P).right.val ∈ P.2.val
        rw [(chosen P).pair_eq]
        simp
      rcases (by simpa using hrmem : (chosen P).right.val = A.val ∨ (chosen P).right.val = b) with hr | hr
      · have hlmem : (chosen P).left.val ∈ ({A.val,b} : Finset V) := by
          change (chosen P).left.val ∈ P.2.val
          rw [(chosen P).pair_eq]
          simp
        have hlb : (chosen P).left.val = b := by
          rcases (by simpa using hlmem : (chosen P).left.val = A.val ∨ (chosen P).left.val = b) with hl | hl
          · exact (hchosen_ne P (Subtype.ext (hl.trans hr.symm))).elim
          · exact hl
        have hlB : (chosen P).left = B := Subtype.ext hlb
        have hrA : (chosen P).right = A := Subtype.ext hr
        have hBA : R j B A := by simpa only [hlB, hrA] using (chosen P).edge
        exact (hRasym j A B hAB hBA).elim
      · exact hr
    exact ⟨(chosen P).order, hmem P, by simpa only [hright] using (chosen P).finalPair⟩
  refine ⟨F, hpairs, htriples, le_antisymm ?_ (triple_coverage_card_lower_bound F htriples)⟩
  have hh := card_image_le (s := (univ : Finset (PointedTriple V))) (f := fun P => (chosen P).order)
  simpa [F, card_pointedTriple] using hh

/-- The minimum number in Theorem 5.3, expressed as an attained bound. -/
theorem exact_universal_test_number {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : 4 ≤ Fintype.card V) :
    (∃ F : Finset (VariableOrder V), UniversalOrderTests k (F : Set (VariableOrder V)) ∧
      F.card = Fintype.card V * (Fintype.card V - 1).choose 2) ∧
    (∀ F : Finset (VariableOrder V), UniversalOrderTests k (F : Set (VariableOrder V)) →
      Fintype.card V * (Fintype.card V - 1).choose 2 ≤ F.card) := by
  constructor
  · obtain ⟨F, hp, ht, hc⟩ := exists_optimal_order_family (V := V) hcard
    exact ⟨F, (universalOrderTests_iff_coverage hcard _).mpr ⟨hp, ht⟩, hc⟩
  · exact fun F hF => universalOrderTests_card_lower_bound hcard F hF

end Characterizations
