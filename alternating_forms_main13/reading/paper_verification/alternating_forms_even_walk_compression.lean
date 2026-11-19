module

public import PaperVerification.AlternatingFormsEvenAvailableRenaming
public import Mathlib.Data.Fintype.Fin

/-!
# Removing the two colors of singleton loops

The positions not occupied by singletons are enumerated increasingly.
Deleting the singleton positions preserves the two strip inequalities:
the prefix length decreases by exactly the number of deleted positions,
and every singleton contributes exactly one original down step.  The
equivalence proved here keeps the actual subsets and both singleton colors.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.EvenSingletons

open BooleanWalks

theorem prefixCount_univ {k : ℕ} (j : ℕ) (hj : j ≤ k) :
    prefixCount (Finset.univ : Finset (Fin k)) j = j := by
  simpa only [prefixCount, Fin.card_filter_val_lt, min_eq_right hj]

theorem prefixCount_union {k : ℕ} (A B : Finset (Fin k)) (h : Disjoint A B) (j : ℕ) :
    prefixCount (A ∪ B) j = prefixCount A j + prefixCount B j := by
  simp only [prefixCount, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))

def embeddingRank {m k : ℕ} (e : Fin m ↪ Fin k) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (e i).val < j).card

theorem embeddingRank_le {m k : ℕ} (e : Fin m ↪ Fin k) (j : ℕ) : embeddingRank e j ≤ m := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin m)

theorem lt_embeddingRank_iff {m k : ℕ} {e : Fin m ↪ Fin k}
    (he : StrictMono e) (j : ℕ) (i : Fin m) :
    i.val < embeddingRank e j ↔ (e i).val < j := by
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro a b hba ha
  have hab : (e b).val ≤ (e a).val := he.monotone hba
  omega

theorem prefixCount_map {m k : ℕ} {e : Fin m ↪ Fin k}
    (he : StrictMono e) (P : Finset (Fin m)) (j : ℕ) :
    prefixCount (P.map e) j = prefixCount P (embeddingRank e j) := by
  rw [prefixCount, Finset.filter_map, Finset.card_map, prefixCount]
  congr 1
  apply Finset.filter_congr
  intro i hi
  exact (lt_embeddingRank_iff he j i).symm

theorem embeddingRank_at {m k : ℕ} {e : Fin m ↪ Fin k}
    (he : StrictMono e) (i : Fin m) : embeddingRank e (e i).val = i.val := by
  unfold embeddingRank
  have h : (Finset.univ.filter fun j => (e j).val < (e i).val) = Finset.Iio i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact he.lt_iff_lt
  rw [h, Fin.card_Iio]

theorem embeddingRank_last {m k : ℕ} (e : Fin m ↪ Fin k) : embeddingRank e k = m := by
  have h : (Finset.univ.filter fun i => (e i).val < k) = Finset.univ := by
    exact Finset.filter_true_of_mem (fun i hi => (e i).isLt)
  rw [embeddingRank, h, Finset.card_univ, Fintype.card_fin]

theorem embeddingRank_surjective {m k : ℕ} {e : Fin m ↪ Fin k}
    (he : StrictMono e) (r : ℕ) (hr : r ≤ m) :
    ∃ j, j ≤ k ∧ embeddingRank e j = r := by
  by_cases hlt : r < m
  · exact ⟨(e ⟨r, hlt⟩).val, Nat.le_of_lt (e ⟨r, hlt⟩).isLt,
      embeddingRank_at he ⟨r, hlt⟩⟩
  · have h : r = m := by omega
    subst r
    exact ⟨k, le_rfl, embeddingRank_last e⟩

def occupied {k : ℕ} (S : SingletonState (Fin k)) : Finset (Fin k) := S.val.1 ∪ S.val.2

theorem available_univ_map {k : ℕ} (S : SingletonState (Fin k)) :
    Finset.univ.map (availableEmbedding S) = (occupied S)ᶜ := by
  ext i
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_compl]
  constructor
  · rintro ⟨r, rfl⟩
    exact (availableOrderEquiv S r).property
  · intro hi
    refine ⟨(availableOrderEquiv S).symm ⟨i, hi⟩, ?_⟩
    change ((availableOrderEquiv S) ((availableOrderEquiv S).symm ⟨i, hi⟩)).val = i
    exact congrArg Subtype.val ((availableOrderEquiv S).apply_symm_apply ⟨i, hi⟩)

theorem available_rank_balance {k : ℕ} (S : SingletonState (Fin k))
    (j : ℕ) (hj : j ≤ k) :
    embeddingRank (availableEmbedding S) j + prefixCount (occupied S) j = j := by
  have he : embeddingRank (availableEmbedding S) j = prefixCount (occupied S)ᶜ j := by
    rw [← available_univ_map S, prefixCount, Finset.filter_map, Finset.card_map]
    rfl
  have hd : Disjoint (occupied S)ᶜ (occupied S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hc
    exact Finset.mem_compl.mp hi hc
  have hu : (occupied S)ᶜ ∪ occupied S = Finset.univ := by
    ext i
    by_cases hi : i ∈ occupied S <;> simp [hi]
  rw [he, ← prefixCount_union _ _ hd, hu]
  exact prefixCount_univ j hj

def compressPairs {k : ℕ} (S : SingletonState (Fin k)) (P : Finset (Available S)) :
    Finset (Fin (Fintype.card (Available S))) :=
  P.map (availableOrderEquiv S).symm.toEquiv.toEmbedding

@[simp] theorem compressPairs_card {k : ℕ} (S : SingletonState (Fin k))
    (P : Finset (Available S)) : (compressPairs S P).card = P.card := Finset.card_map _

theorem compressPairs_map {k : ℕ} (S : SingletonState (Fin k))
    (P : Finset (Available S)) :
    (compressPairs S P).map (availableEmbedding S) = pairSupport S P := by
  rw [compressPairs, Finset.map_map]
  have h : (availableOrderEquiv S).symm.toEquiv.toEmbedding.trans (availableEmbedding S) =
      Function.Embedding.subtype (fun i => i ∉ occupied S) := by
    ext i
    change ((availableOrderEquiv S) ((availableOrderEquiv S).symm i)).val.val = i.val.val
    exact congrArg (fun x : Available S => x.val.val)
      ((availableOrderEquiv S).apply_symm_apply i)
  rw [h]
  rfl

theorem pairSupport_prefix {k : ℕ} (S : SingletonState (Fin k))
    (P : Finset (Available S)) (j : ℕ) :
    prefixCount (pairSupport S P) j =
      prefixCount (compressPairs S P) (embeddingRank (availableEmbedding S) j) := by
  rw [← compressPairs_map]
  exact prefixCount_map (availableEmbedding_strictMono S) _ _

def selectionPrefix {k : ℕ} (T : PairedState (Fin k)) (j : ℕ) : ℕ :=
  prefixCount (selection T).1 j + prefixCount (selection T).2 j

theorem selectionPrefix_decompose {k : ℕ} (T : PairedState (Fin k)) (j : ℕ) :
    selectionPrefix T j = prefixCount (occupied T.1) j +
      2 * prefixCount (compressPairs T.1 T.2) (embeddingRank (availableEmbedding T.1) j) := by
  rw [selectionPrefix]
  change prefixCount (T.1.val.1 ∪ pairSupport T.1 T.2) j +
    prefixCount (T.1.val.2 ∪ pairSupport T.1 T.2) j = _
  rw [prefixCount_union _ _ (pairSupport_disjoint_left T.1 T.2),
    prefixCount_union _ _ (pairSupport_disjoint_right T.1 T.2),
    pairSupport_prefix]
  rw [occupied, prefixCount_union _ _ T.1.property]
  omega

/-- These are the strip bounds at the odd heights between complete pairs.
Both singleton colors satisfy the same bounds at both walls. -/
def PairedGood {k : ℕ} (T : PairedState (Fin k)) : Prop :=
  ∀ j, j ≤ k → selectionPrefix T j ≤ j ∧ j + degree T ≤ k + selectionPrefix T j

def compressedFixed {k : ℕ} (T : PairedState (Fin k)) :
    FixedSubsets (Fin (Fintype.card (Available T.1))) T.2.card :=
  ⟨compressPairs T.1 T.2, compressPairs_card T.1 T.2⟩

theorem compressed_good_iff {k : ℕ} (T : PairedState (Fin k)) :
    Good (compressedFixed T) ↔ PairedGood T := by
  have hcard := card_available_add_singletonDegree T.1
  rw [Fintype.card_fin] at hcard
  constructor
  · intro h j hj
    have hg := h (embeddingRank (availableEmbedding T.1) j) (embeddingRank_le _ _)
    have hb := available_rank_balance T.1 j hj
    have hp := selectionPrefix_decompose T j
    change 2 * prefixCount (compressPairs T.1 T.2) _ ≤ _ ∧
      _ + 2 * T.2.card ≤ _ + 2 * prefixCount (compressPairs T.1 T.2) _ at hg
    change selectionPrefix T j ≤ j ∧
      j + (singletonDegree T.1 + 2 * T.2.card) ≤ k + selectionPrefix T j
    omega
  · intro h r hr
    obtain ⟨j, hj, he⟩ := embeddingRank_surjective (availableEmbedding_strictMono T.1) r hr
    have hg := h j hj
    have hb := available_rank_balance T.1 j hj
    have hp := selectionPrefix_decompose T j
    rw [he] at hb hp
    change selectionPrefix T j ≤ j ∧
      j + (singletonDegree T.1 + 2 * T.2.card) ≤ k + selectionPrefix T j at hg
    change 2 * prefixCount (compressPairs T.1 T.2) r ≤ r ∧
      r + 2 * T.2.card ≤ Fintype.card (Available T.1) + 2 * prefixCount (compressPairs T.1 T.2) r
    omega

abbrev GoodDegreeState (k s : ℕ) := {T : DegreeState (Fin k) s // PairedGood T.val}

instance (k s : ℕ) : Fintype (GoodDegreeState k s) := Fintype.ofFinite _

def blockGoodToPaired {k s : ℕ}
    (x : (J : DegreeBlock (Fin k) s) × BlockGoodSubsets J) : GoodDegreeState k s := by
  let P := x.2.val.val.map (availableOrderEquiv x.1.val.1).toEquiv.toEmbedding
  have hP : P.card = x.1.val.2.val := by simp only [P, Finset.card_map, x.2.val.property]
  have hc : compressPairs x.1.val.1 P = x.2.val.val := by
    exact ((availableOrderEquiv x.1.val.1).toEquiv.finsetCongr).symm_apply_apply x.2.val.val
  refine ⟨⟨⟨x.1.val.1, P⟩, ?_⟩, ?_⟩
  · change singletonDegree x.1.val.1 + 2 * P.card = s
    rw [hP]
    exact x.1.property
  · apply (compressed_good_iff _).mp
    intro r hr
    have h := x.2.property r hr
    simpa only [compressedFixed, hc, hP] using h

theorem blockGoodToPaired_injective (k s : ℕ) :
    Function.Injective (blockGoodToPaired (k := k) (s := s)) := by
  rintro ⟨⟨⟨S, q⟩, hS⟩, P⟩ ⟨⟨⟨T, r⟩, hT⟩, Q⟩ he
  have hstate := congrArg (fun z : GoodDegreeState k s => z.val.val) he
  have hST : S = T := congrArg Sigma.fst hstate
  subst T
  have hqr : q = r := by
    apply Fin.ext
    dsimp only at hS hT
    omega
  subst r
  have hP : P.val.val = Q.val.val := by
    apply Finset.map_injective (availableOrderEquiv S).toEquiv.toEmbedding
    exact eq_of_heq ((Sigma.mk.inj_iff.mp hstate).2)
  have heq : P = Q := Subtype.ext (Subtype.ext hP)
  subst Q
  rfl

theorem blockGoodToPaired_surjective (k s : ℕ) :
    Function.Surjective (blockGoodToPaired (k := k) (s := s)) := by
  rintro ⟨⟨⟨S, P⟩, hdeg⟩, hgood⟩
  let J : DegreeBlock (Fin k) s :=
    ⟨(S, ⟨P.card, by change singletonDegree S + 2 * P.card = s at hdeg; omega⟩), hdeg⟩
  let Q : BlockGoodSubsets J := ⟨compressedFixed ⟨S, P⟩, (compressed_good_iff _).mpr hgood⟩
  refine ⟨⟨J, Q⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (⟨S, (compressPairs S P).map (availableOrderEquiv S).toEquiv.toEmbedding⟩ :
    PairedState (Fin k)) = ⟨S, P⟩
  congr 1
  exact ((availableOrderEquiv S).toEquiv.finsetCongr).apply_symm_apply P

/-- The exact deletion and insertion bijection, retaining both singleton colors. -/
def blockGoodPairedEquiv (k s : ℕ) :
    ((J : DegreeBlock (Fin k) s) × BlockGoodSubsets J) ≃ GoodDegreeState k s :=
  Equiv.ofBijective blockGoodToPaired
    ⟨blockGoodToPaired_injective k s, blockGoodToPaired_surjective k s⟩

end PaperVerification.AlternatingForms.EvenSingletons
