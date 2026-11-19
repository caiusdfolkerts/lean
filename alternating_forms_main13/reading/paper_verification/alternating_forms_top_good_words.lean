module

public import PaperVerification.AlternatingFormsTopSelection

/-!
# The actual top bidegree basis and its interlacing indexing equivalence

All three index sets below are independently defined.  The source consists
of the original good exterior words of total degree `p+q` and `a`-degree
`p`; the intermediate set records the selected `a` indices and omitted
`b` indices; the target is the symmetric-power monomial indexing set.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.TopInterlacing

open BooleanWalks

def TopWord (p q : ℕ) :=
  {I : GoodOddIndex (p+q) (p+q) // Bidegree.goodADegree I=p}

instance (p q : ℕ) : Fintype (TopWord p q) := by
  unfold TopWord
  infer_instance

theorem selectedAB_injective {k : ℕ} {A A' : Finset (Fin k)}
    {B B' : Finset (Fin (k+1))} (h : selectedAB A B=selectedAB A' B') :
    A=A' ∧ B=B' :=
  Finset.disjSum_inj.mp (Finset.map_injective (abIndex k).toEmbedding h)

theorem aDegree_of_selectedAB {k s : ℕ} (I : Fin s → Fin (2*k+1))
    (hI : StrictMono I) (A : Finset (Fin k)) (B : Finset (Fin (k+1)))
    (hS : GoodPaths.selectedSet I=selectedAB A B) :
    Bidegree.aWordDegree I=A.card := by
  have hsum : Bidegree.aWordDegree I =
      ∑ j ∈ GoodPaths.selectedSet I, Bidegree.aIndexDegree j := by
    rw [GoodPaths.selectedSet, Finset.sum_image]
    · rfl
    · intro a ha b hb hab
      exact hI.injective hab
  rw [hsum, hS, selectedAB, Finset.sum_map, Finset.sum_disjSum]
  have ha (i : Fin k) : Bidegree.aIndexDegree ((abIndex k) (.inl i))=1 := by
    have h : (2*i.val+1)%2=1 := by omega
    simp [Bidegree.aIndexDegree, abIndex, h]
  have hb (i : Fin (k+1)) : Bidegree.aIndexDegree ((abIndex k) (.inr i))=0 := by
    have h : (2*i.val)%2≠1 := by omega
    simp [Bidegree.aIndexDegree, abIndex, h]
  change (∑ i∈A, Bidegree.aIndexDegree (abIndex k (.inl i))) +
    (∑ j∈B, Bidegree.aIndexDegree (abIndex k (.inr j))) = A.card
  simp only [ha, hb, Finset.sum_const, Finset.sum_const_zero, Nat.nsmul_eq_mul,
    Nat.mul_one, Nat.mul_zero, Nat.add_zero]

theorem goodPair_selected_card {p q : ℕ} (P : GoodPair p q) :
    (selectedAB P.val.1 P.val.2ᶜ).card=p+q := by
  rw [selectedAB, Finset.card_map, Finset.card_disjSum, P.property.1,
    Finset.card_compl, Fintype.card_fin, P.property.2.1]
  omega

def goodPairToTopWord {p q : ℕ} (P : GoodPair p q) : TopWord p q := by
  let S := selectedAB P.val.1 P.val.2ᶜ
  have hS : S.card=p+q := goodPair_selected_card P
  let I := S.orderEmbOfFin hS
  have hi : GoodPaths.selectedSet I=S := Finset.image_orderEmbOfFin_univ S hS
  have hg : ∀ j, 2*j.val≤(I j).val ∧ (I j).val+2*(p+q)≤2*(p+q)+2+2*j.val := by
    apply (GoodPaths.good_bounds_iff_prefix_strip (p+q) (p+q) I I.strictMono).mpr
    intro r hr
    rw [GoodPaths.selectedBefore_eq_filter_card I.strictMono, hi]
    exact (selectedAB_strip_iff P.val.1 P.val.2 P.property.1 P.property.2.1).mpr
      P.property.2.2 r hr
  refine ⟨⟨⟨I,I.strictMono⟩,hg⟩, ?_⟩
  change Bidegree.aWordDegree I=p
  exact (aDegree_of_selectedAB I I.strictMono P.val.1 P.val.2ᶜ hi).trans P.property.1

theorem goodPairToTopWord_selected {p q : ℕ} (P : GoodPair p q) :
    GoodPaths.selectedSet (goodPairToTopWord P).val.val.val = selectedAB P.val.1 P.val.2ᶜ :=
  Finset.image_orderEmbOfFin_univ _ (goodPair_selected_card P)

theorem goodPairToTopWord_injective (p q : ℕ) :
    Function.Injective (goodPairToTopWord (p := p) (q := q)) := by
  intro P Q h
  have hs := congrArg (fun I : TopWord p q => GoodPaths.selectedSet I.val.val.val) h
  rw [goodPairToTopWord_selected, goodPairToTopWord_selected] at hs
  obtain ⟨ha,hb⟩ := selectedAB_injective hs
  apply Subtype.ext
  exact Prod.ext ha (by simpa only [compl_compl] using congrArg (fun C => Cᶜ) hb)

theorem goodPairToTopWord_surjective (p q : ℕ) :
    Function.Surjective (goodPairToTopWord (p := p) (q := q)) := by
  intro I
  let S := GoodPaths.selectedSet I.val.val.val
  let T := S.map (abIndex (p+q)).symm.toEmbedding
  let A := T.toLeft
  let B := T.toRight
  let C := Bᶜ
  have hs : selectedAB A B=S := by
    rw [selectedAB]
    change (T.toLeft.disjSum T.toRight).map _=S
    rw [Finset.toLeft_disjSum_toRight]
    simp [T, Finset.map_map]
  have ha : A.card=p := by
    have h := aDegree_of_selectedAB I.val.val.val I.val.val.property A B hs.symm
    exact h.symm.trans I.property
  have hc : C.card=p+1 := by
    have htotal : A.card+B.card=p+q := by
      have hcard := congrArg Finset.card hs
      rw [selectedAB, Finset.card_map, Finset.card_disjSum] at hcard
      exact hcard.trans (GoodPaths.selectedSet_card I.val.val.property)
    change (Bᶜ).card=p+1
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hgood : ∀ r, r≤p+q → prefixCount A r≤prefixCount C r ∧
      prefixCount C (r+1)≤prefixCount A r+1 := by
    apply (selectedAB_strip_iff A C ha hc).mp
    intro r hr
    have hp := (GoodPaths.good_bounds_iff_prefix_strip (p+q) (p+q)
      I.val.val.val I.val.val.property).mp I.val.property r hr
    rw [GoodPaths.selectedBefore_eq_filter_card I.val.val.property] at hp
    simpa only [C, compl_compl, hs, S, originalPrefix] using hp
  let P : GoodPair p q := ⟨(A,C),ha,hc,hgood⟩
  refine ⟨P, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply (GoodPaths.increasingSelectionEquiv (p+q) (2*(p+q)+1)).injective
  apply Subtype.ext
  change GoodPaths.selectedSet (goodPairToTopWord P).val.val.val=S
  rw [goodPairToTopWord_selected]
  simpa only [P, C, compl_compl] using hs

def topWordGoodPairEquiv (p q : ℕ) : TopWord p q ≃ GoodPair p q :=
  (Equiv.ofBijective goodPairToTopWord
    ⟨goodPairToTopWord_injective p q, goodPairToTopWord_surjective p q⟩).symm

def topWordInterlacingEquiv (p q : ℕ) : TopWord p q ≃ Interlacing p q :=
  (topWordGoodPairEquiv p q).trans (goodPairInterlacingEquiv p q)

/-- Every actual good word in the original top bidegree corresponds to
exactly one symmetric monomial, in the full parameter range. -/
def topWordSymEquiv (p q : ℕ) : TopWord p q ≃ Sym (Fin (q+1)) (2*p+1) :=
  (topWordInterlacingEquiv p q).trans (interlacingSymEquiv p q)

theorem topWord_card (p q : ℕ) : Fintype.card (TopWord p q)=(2*p+q+1).choose q := by
  rw [Fintype.card_congr (topWordInterlacingEquiv p q), interlacing_card]

/-- The dimension clause of Corollary 5.2 for the actual exterior quotient. -/
theorem actual_top_bigraded_dimension {K : Type*} [Field K] [CharZero K] (p q : ℕ) :
    Module.finrank K (Bidegree.actualBigradedPiece (K := K) (p+q) p q) =
      (2*p+q+1).choose q := by
  rw [Bidegree.finrank_actualBigradedPiece]
  change Nat.card (TopWord p q)=_
  rw [Nat.card_eq_fintype_card]
  exact topWord_card p q

end PaperVerification.AlternatingForms.TopInterlacing
