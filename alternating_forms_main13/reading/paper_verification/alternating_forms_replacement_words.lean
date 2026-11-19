module

public import PaperVerification.AlternatingFormsWordCoordinates

/-!
# Every actual canonical replacement word has lower Plücker weight

The singleton word and the entire suffix are retained.  Both exterior
length and vertex weight are computed from the actual lists, so the result
applies to every support state of the prefix inverse, including words that
vanish because a vertex is repeated.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators
open PaperVerification.WeightedInitialFiber

variable {ι α : Type*} [DecidableEq ι]

def matchingIndexWord (u v : ι → α) (T : Finset ι) : List α :=
  T.toList.flatMap (fun i => [u i,v i])

theorem matchingIndexWord_length (u v : ι → α) (T : Finset ι) :
    (matchingIndexWord u v T).length=2*T.card := by
  have h (L : List ι) : (L.flatMap (fun i => [u i,v i])).length=2*L.length := by
    induction L with
    | nil => simp
    | cons i L ih => simp only [List.flatMap_cons,List.length_append,List.length_cons,
        List.length_nil,ih]; omega
  simpa only [matchingIndexWord,Finset.length_toList] using h T.toList

theorem matchingIndexWord_weight {A : Type*} [AddCommMonoid A]
    (u v : ι → α) (w : α → A) (T : Finset ι) :
    ((matchingIndexWord u v T).map w).sum=∑ i ∈ T,(w (u i)+w (v i)) := by
  have h (L : List ι) :
      ((L.flatMap (fun i => [u i,v i])).map w).sum=
        (L.map (fun i => w (u i)+w (v i))).sum := by
    induction L with
    | nil => simp
    | cons i L ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,ih]
  rw [matchingIndexWord,h,Finset.sum_map_toList]

theorem replacementWord_length (u v : ι → α) (P T : Finset ι) (j : ι)
    (hc : P.card=T.card+1) (S L : List α) :
    ([u j,v j]++S++matchingIndexWord u v T++L).length =
      (S++matchingIndexWord u v P++L).length := by
  simp only [List.length_append,List.length_cons,List.length_nil,matchingIndexWord_length,hc]
  omega

theorem replacementWord_weight_strict (u v : ι → α) (w : α → ℤ)
    (P T : Finset ι) (j : ι) (S L : List α)
    (hcost : (∑ i ∈ T,(w (u i)+w (v i)))+(w (u j)+w (v j)) <
      ∑ i ∈ P,(w (u i)+w (v i))) :
    (([u j,v j]++S++matchingIndexWord u v T++L).map w).sum <
      ((S++matchingIndexWord u v P++L).map w).sum := by
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,matchingIndexWord_weight]
  omega

theorem wordWeight_nat_cast {k : ℕ} (L : List (Fin (2*k+1))) :
    (((L.map (oddNatVertexWeight k)).sum : ℕ) : ℤ) =
      (L.map (oddPathVertexWeight k)).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp only [List.map_cons,List.sum_cons,Nat.cast_add,
      oddNatVertexWeight_cast,ih]

variable {K : Type*} [Field K] {k s : ℕ}

/-- Every first-prefix correction word, with its fixed singleton word and
arbitrary suffix, belongs to the literal lower-weight polynomial submodule. -/
theorem oddFirst_replacement_coordinate_lower
    (P T : Finset (Fin k)) (h : ℕ) (j : Fin k)
    (hP : ∀ i ∈ P,i.val<h) (hj : h≤j.val) (hc : P.card=T.card+1)
    (S L : List (Fin (2*k+1)))
    (hs : (S++matchingIndexWord oddPathFirstLeft oddPathMiddle P++L).length=s) :
    totalExteriorPluckerCoordinates (K := K) s (2*k+1)
      (indexExteriorWord
        ([oddPathFirstLeft j,oddPathMiddle j]++S++
          matchingIndexWord oddPathFirstLeft oddPathMiddle T++L)) ∈
      lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
        (((S++matchingIndexWord oddPathFirstLeft oddPathMiddle P++L).map (oddNatVertexWeight k)).sum) := by
  have hlen := (replacementWord_length oddPathFirstLeft oddPathMiddle P T j hc S L).trans hs
  apply totalExteriorPluckerCoordinates_word_lower (oddNatVertexWeight k) _ hlen
  have hz := replacementWord_weight_strict oddPathFirstLeft oddPathMiddle
    (oddPathVertexWeight k) P T j S L
    (oddFirst_replacement_weight_strict P T h j hP hj hc)
  have hcst :
      (((([oddPathFirstLeft j,oddPathMiddle j]++S++
        matchingIndexWord oddPathFirstLeft oddPathMiddle T++L).map (oddNatVertexWeight k)).sum : ℕ) : ℤ) <
      ((((S++matchingIndexWord oddPathFirstLeft oddPathMiddle P++L).map (oddNatVertexWeight k)).sum : ℕ) : ℤ) := by
    simpa only [wordWeight_nat_cast] using hz
  exact_mod_cast hcst

/-- The reflected second-prefix correction uses the same original vertex
weight vector and the same complete suffix calculation. -/
theorem oddSecond_replacement_coordinate_lower
    (P T : Finset (Fin k)) (h : ℕ) (j : Fin k)
    (hP : ∀ i ∈ P,i.val<h) (hj : h≤j.val) (hc : P.card=T.card+1)
    (S L : List (Fin (2*k+1)))
    (hs : (S++matchingIndexWord (fun i => oddPathMiddle i.rev)
      (fun i => oddPathSecondRight i.rev) P++L).length=s) :
    totalExteriorPluckerCoordinates (K := K) s (2*k+1)
      (indexExteriorWord
        ([oddPathMiddle j.rev,oddPathSecondRight j.rev]++S++
          matchingIndexWord (fun i => oddPathMiddle i.rev)
            (fun i => oddPathSecondRight i.rev) T++L)) ∈
      lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
        (((S++matchingIndexWord (fun i => oddPathMiddle i.rev)
          (fun i => oddPathSecondRight i.rev) P++L).map (oddNatVertexWeight k)).sum) := by
  have hlen := (replacementWord_length (fun i : Fin k => oddPathMiddle i.rev)
    (fun i : Fin k => oddPathSecondRight i.rev) P T j hc S L).trans hs
  apply totalExteriorPluckerCoordinates_word_lower (oddNatVertexWeight k) _ hlen
  have hcost := oddSecond_replacement_weight_strict P T h j hP hj hc
  have hz := replacementWord_weight_strict (fun i : Fin k => oddPathMiddle i.rev)
    (fun i : Fin k => oddPathSecondRight i.rev) (oddPathVertexWeight k) P T j S L hcost
  have hcst :
      (((([oddPathMiddle j.rev,oddPathSecondRight j.rev]++S++
        matchingIndexWord (fun i => oddPathMiddle i.rev)
          (fun i => oddPathSecondRight i.rev) T++L).map (oddNatVertexWeight k)).sum : ℕ) : ℤ) <
      ((((S++matchingIndexWord (fun i => oddPathMiddle i.rev)
        (fun i => oddPathSecondRight i.rev) P++L).map (oddNatVertexWeight k)).sum : ℕ) : ℤ) := by
    simpa only [wordWeight_nat_cast] using hz
  exact_mod_cast hcst

end PaperVerification.AlternatingForms
