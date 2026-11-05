module

public import PaperVerification.AlternatingFormsBarCutSigns
public import Mathlib.Data.List.FinRange

/-!
# Merging adjacent bar factors deletes the corresponding literal cut

The list operation joins exactly factors i and i+1. Its concatenation and
positivity proofs make it an actual factorization of the original word.
The scan of block lengths proves that its boundary set is obtained by
erasing boundary i+1, including all endpoint and cardinality information.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.BarCompositions

variable {α β : Type*}

def mergeAdjacent (op : α → α → α) : ℕ → List α → List α
  | 0,a::b::L => op a b::L
  | 0,L => L
  | i+1,a::L => a::mergeAdjacent op i L
  | _+1,[] => []

theorem map_mergeAdjacent (op : α → α → α) (op' : β → β → β)
    (f : α → β) (hf : ∀ a b,f (op a b)=op' (f a) (f b))
    (i : ℕ) (L : List α) :
    (mergeAdjacent op i L).map f=mergeAdjacent op' i (L.map f) := by
  induction i generalizing L with
  | zero => cases L with
    | nil => rfl
    | cons a L => cases L <;> simp only [mergeAdjacent,List.map_cons,List.map_nil,hf]
  | succ i ih => cases L with
    | nil => rfl
    | cons a L => simp only [mergeAdjacent,List.map_cons,ih]

theorem mergeAdjacent_length (op : α → α → α) (i : ℕ) (L : List α)
    (hi : i+1<L.length) : (mergeAdjacent op i L).length+1=L.length := by
  induction i generalizing L with
  | zero => cases L with
    | nil => simp at hi
    | cons a L => cases L with
      | nil => simp at hi
      | cons b L => simp only [mergeAdjacent,List.length_cons]
  | succ i ih => cases L with
    | nil => simp at hi
    | cons a L =>
      have hi' : i+1<L.length := by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hi
      simpa only [mergeAdjacent,List.length_cons,Nat.add_assoc] using congrArg (·+1) (ih L hi')

theorem mergeAdjacent_positive (L : List (List α))
    (hL : ∀ T∈L,0<T.length) (i : ℕ) :
    ∀ T∈mergeAdjacent (·++·) i L,0<T.length := by
  induction i generalizing L with
  | zero =>
    cases L with
    | nil => simp [mergeAdjacent]
    | cons a L =>
      cases L with
      | nil => simpa only [mergeAdjacent] using hL
      | cons b L =>
        intro T hT
        rcases List.mem_cons.mp hT with rfl | hT
        · have ha := hL a (by simp)
          rw [List.length_append]
          omega
        · exact hL T (by simp only [List.mem_cons]; exact Or.inr (Or.inr hT))
  | succ i ih =>
    cases L with
    | nil => simp [mergeAdjacent]
    | cons a L =>
      intro T hT
      rcases List.mem_cons.mp hT with rfl | hT
      · exact hL _ List.mem_cons_self
      · exact ih L (fun S hS ↦ hL S (List.mem_cons_of_mem _ hS)) T hT

theorem flatten_mergeAdjacent (i : ℕ) (L : List (List α)) :
    (mergeAdjacent (·++·) i L).flatten=L.flatten := by
  induction i generalizing L with
  | zero =>
    cases L with
    | nil => rfl
    | cons a L => cases L <;> simp only [mergeAdjacent,List.flatten_cons,List.append_assoc]
  | succ i ih =>
    cases L with
    | nil => rfl
    | cons a L => simp only [mergeAdjacent,List.flatten_cons,ih]

def mergeFactorization (W : List α) (L : Factorization W)
    (i : ℕ) : Factorization W :=
  ⟨mergeAdjacent (·++·) i L.val,
    (flatten_mergeAdjacent i L.val).trans L.property.1,
    mergeAdjacent_positive L.val L.property.2 i⟩

/-- Scanning actual block lengths makes the deleted cut completely explicit. -/
theorem scanl_mergeAdjacent (i : ℕ) (L : List ℕ) (hi : i+1<L.length) (a : ℕ) :
    (mergeAdjacent (·+·) i L).scanl (·+·) a=
      (L.scanl (·+·) a).eraseIdx (i+1) := by
  induction i generalizing L a with
  | zero =>
    cases L with
    | nil => simp at hi
    | cons b L =>
      cases L with
      | nil => simp at hi
      | cons c L =>
        simp only [mergeAdjacent,List.scanl_cons,List.eraseIdx_cons_succ,
          List.eraseIdx_cons_zero,Nat.add_assoc]
  | succ i ih =>
    cases L with
    | nil => simp at hi
    | cons b L =>
      have hi' : i+1<L.length := by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hi
      simp only [mergeAdjacent,List.scanl_cons,List.eraseIdx_cons_succ,ih L hi']

def boundaryList {n : ℕ} (c : Composition n) : List ℕ :=
  c.blocks.scanl (·+·) 0

theorem boundaryList_eq_ofFn {n : ℕ} (c : Composition n) :
    boundaryList c=List.ofFn (fun j : Fin (c.length+1) ↦ (c.boundary j).val) := by
  apply List.ext_getElem
  · simp only [boundaryList,List.length_scanl,List.length_ofFn,Composition.length]
  · intro i hi hj
    simp only [boundaryList,List.getElem_scanl,List.getElem_ofFn,←List.sum_eq_foldl]
    rfl

/-- Evaluate the boundary list before substituting any factorization-specific
length proof.  This avoids rewriting a list underneath a dependent index. -/
theorem boundaryList_getElem {n : ℕ} (c : Composition n)
    (j : Fin (c.length+1)) :
    (boundaryList c)[j.val]'(by
      simpa only [boundaryList,List.length_scanl,Composition.length] using j.isLt) =
        (c.boundary j).val := by
  simp only [boundaryList,List.getElem_scanl,←List.sum_eq_foldl]
  rfl

theorem boundaryList_nodup {n : ℕ} (c : Composition n) : (boundaryList c).Nodup := by
  rw [boundaryList_eq_ofFn,List.nodup_ofFn]
  exact Fin.val_injective.comp c.boundary.injective

theorem image_boundaries_eq_boundaryList {n : ℕ} (c : Composition n) :
    c.boundaries.image Fin.val=(boundaryList c).toFinset := by
  classical
  rw [boundaryList_eq_ofFn]
  ext x
  simp only [Composition.boundaries,Finset.mem_image,Finset.mem_map,
    Finset.mem_univ,true_and,List.mem_toFinset,List.mem_ofFn]
  constructor
  · rintro ⟨y,⟨j,rfl⟩,rfl⟩
    exact ⟨j,rfl⟩
  · rintro ⟨j,rfl⟩
    exact ⟨c.boundary j,⟨j,rfl⟩,rfl⟩

theorem toFinset_eraseIdx [DecidableEq α] (L : List α) (hL : L.Nodup) (i : ℕ) (hi : i<L.length) :
    (L.eraseIdx i).toFinset=L.toFinset.erase L[i] := by
  ext x
  simp only [List.mem_toFinset,Finset.mem_erase,List.mem_eraseIdx_iff_getElem]
  constructor
  · rintro ⟨j,hj,hji,hx⟩
    refine ⟨?_,hx ▸ List.getElem_mem hj⟩
    intro he
    exact hji (hL.getElem_inj.mp (hx.trans he))
  · rintro ⟨hxi,hx⟩
    obtain ⟨j,hj,hjx⟩ := List.mem_iff_getElem.mp hx
    refine ⟨j,hj,?_,hjx⟩
    intro hji
    subst j
    exact hxi hjx.symm

/-- The actual merge deletes exactly the boundary between the two factors. -/
theorem boundaries_mergeFactorization (W : List α) (L : Factorization W)
    (i : ℕ) (hi : i+1<L.val.length) :
    boundaries W (mergeFactorization W L i)=
      (boundaries W L).erase
        ((factorizationComposition W L).boundary
          ⟨i+1,by simpa only [Composition.length,factorizationComposition,List.length_map] using
            Nat.lt_succ_of_lt hi⟩) := by
  classical
  let c := factorizationComposition W L
  let j : Fin (c.length+1) := ⟨i+1,by
    simpa only [c,Composition.length,factorizationComposition,List.length_map] using
      Nat.lt_succ_of_lt hi⟩
  apply Finset.image_injective (f := Fin.val) Fin.val_injective
  simp only [boundaries]
  rw [Finset.image_erase Fin.val_injective,
    image_boundaries_eq_boundaryList,image_boundaries_eq_boundaryList]
  have he : boundaryList (factorizationComposition W (mergeFactorization W L i))=
      (boundaryList c).eraseIdx (i+1) := by
    change ((mergeAdjacent (·++·) i L.val).map List.length).scanl (·+·) 0=
      ((L.val.map List.length).scanl (·+·) 0).eraseIdx (i+1)
    rw [map_mergeAdjacent (·++·) (·+·) List.length (fun a b => List.length_append),
      scanl_mergeAdjacent i _ (by simpa only [List.length_map] using hi)]
  rw [he,toFinset_eraseIdx _ (boundaryList_nodup c) (i+1) (by
    simpa only [boundaryList,List.length_scanl,c,Composition.length,
      factorizationComposition,List.length_map] using Nat.lt_succ_of_lt hi)]
  congr 1
  exact boundaryList_getElem c j

/-- For an admissible bar word, the merged tensor remains admissible
exactly when the deleted cut is optional. -/
theorem merge_admissible_iff_optional (R : α → α → Prop) (W : List α)
    (L : AdmissibleFactorization R W) (i : ℕ) (hi : i+1<L.val.val.length) :
    (∀ T∈(mergeFactorization W L.val i).val,T.IsChain R) ↔
      (factorizationComposition W L.val).boundary
        ⟨i+1,by simpa only [Composition.length,factorizationComposition,List.length_map] using
          Nat.lt_succ_of_lt hi⟩∉mandatoryCuts R W := by
  rw [factorization_admissible_iff,boundaries_mergeFactorization W L.val i hi,
    Finset.subset_erase]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨(factorization_admissible_iff R W L.val).mp L.property,h⟩

end PaperVerification.AlternatingForms.BarCompositions

