module

public import PaperVerification.AlternatingFormsBarWordFibers
public import PaperVerification.AlternatingFormsBarCoefficientFormula

/-!
# Normal adjacent multiplication and admissible cut deletion

Normal merging is defined on the literal positive words. Its output,
when present, is exactly the factorization obtained by deleting the
corresponding interior cut. Thus optional cuts are precisely the nonzero
normal adjacent products.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.BarCompositions

open BarCoefficientFormula PaperVerification.ReducedBarBasis

variable {C J : Type*} [Preorder J] (e : C ≃ PositiveNormalWord J)

def concatenateNormal (a b : C)
    (h : ((e a).val++(e b).val).IsChain (·≤·)) : C :=
  e.symm ⟨(e a).val++(e b).val,
    by rw [List.length_append]; exact Nat.add_pos_left (e a).property.1 _,h⟩

@[simp] theorem concatenateNormal_word (a b : C)
    (h : ((e a).val++(e b).val).IsChain (·≤·)) :
    (e (concatenateNormal e a b h)).val=(e a).val++(e b).val := by
  exact congrArg (fun W : PositiveNormalWord J => W.val)
    (e.apply_symm_apply _)

def normalMerge : ℕ → List C → Option (List C)
  | 0,a::b::L => if h : ((e a).val++(e b).val).IsChain (·≤·)
      then some (concatenateNormal e a b h::L) else none
  | 0,_ => none
  | i+1,a::L => (normalMerge i L).map (a::·)
  | _+1,[] => none

theorem normalMerge_map (i : ℕ) (L M : List C)
    (h : normalMerge e i L=some M) :
    M.map (fun a ↦ (e a).val)=mergeAdjacent (·++·) i (L.map (fun a ↦ (e a).val)) := by
  induction i generalizing L M with
  | zero =>
    cases L with
    | nil => simp only [normalMerge] at h; cases h
    | cons a L =>
      cases L with
      | nil => simp only [normalMerge] at h; cases h
      | cons b L =>
        by_cases hab : ((e a).val++(e b).val).IsChain (· ≤ ·)
        · rw [normalMerge,dif_pos hab] at h
          cases h
          simp only [List.map_cons,mergeAdjacent,concatenateNormal_word]
        · rw [normalMerge,dif_neg hab] at h
          cases h
  | succ i ih =>
    cases L with
    | nil => simp only [normalMerge] at h; cases h
    | cons a L =>
      cases he : normalMerge e i L with
      | none => simp only [normalMerge,he,Option.map_none] at h; cases h
      | some T =>
        simp only [normalMerge,he,Option.map_some,Option.some.injEq] at h
        subst M
        simp only [List.map_cons,mergeAdjacent,ih L T he]

theorem normalMerge_length (i : ℕ) (L M : List C)
    (h : normalMerge e i L=some M) (hi : i+1<L.length) :
    M.length+1=L.length := by
  have hm := normalMerge_map e i L M h
  have hlen := congrArg List.length hm
  have hj : i+1<(L.map (fun a ↦ (e a).val)).length := by
    simpa only [List.length_map] using hi
  have he := mergeAdjacent_length (·++·) i (L.map (fun a ↦ (e a).val)) hj
  simpa only [List.length_map,←hlen] using he

theorem normalMerge_exists_iff (i : ℕ) (L : List C) (hi : i+1<L.length) :
    (∃ M,normalMerge e i L=some M) ↔
      ∀ T∈mergeAdjacent (·++·) i (L.map (fun a ↦ (e a).val)),T.IsChain (·≤·) := by
  constructor
  · rintro ⟨M,hM⟩ T hT
    rw [←normalMerge_map e i L M hM] at hT
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hT
    exact (e a).property.2
  · intro h
    induction i generalizing L with
    | zero =>
      cases L with
      | nil => simp only [List.length_nil] at hi; omega
      | cons a L =>
        cases L with
        | nil => simp only [List.length_cons,List.length_nil] at hi; omega
        | cons b L =>
          have hab : ((e a).val++(e b).val).IsChain (·≤·) :=
            h _ (by simp only [List.map_cons,mergeAdjacent]; exact List.mem_cons_self)
          exact ⟨concatenateNormal e a b hab::L,by rw [normalMerge,dif_pos hab]⟩
    | succ i ih =>
      cases L with
      | nil => simp only [List.length_nil] at hi; omega
      | cons a L =>
        have hi' : i+1<L.length := by simp only [List.length_cons] at hi; omega
        have h' : ∀ T∈mergeAdjacent (·++·) i (L.map (fun a ↦ (e a).val)),T.IsChain (·≤·) := by
          intro T hT
          apply h T
          exact List.mem_cons_of_mem _ hT
        obtain ⟨M,hM⟩ := ih L hi' h'
        exact ⟨a::M,by simp only [normalMerge,hM,Option.map_some]⟩

theorem normalMerge_optional (W : List J) (r : ℕ) (L : ActualBarIndex e W r)
    (i : ℕ) (hi : i+1<L.val.length) :
    (∃ M,normalMerge e i L.val=some M) ↔
      (factorizationComposition W (actualFactorization e W r L).val.val).boundary
        ⟨i+1,by
          simpa only [factorizationComposition,Composition.length,actualFactorization,
            List.length_map] using Nat.lt_succ_of_lt hi⟩∉mandatoryCuts (·≤·) W := by
  rw [normalMerge_exists_iff e i L.val hi]
  exact merge_admissible_iff_optional (·≤·) W (actualFactorization e W r L).val i
    (by simpa only [actualFactorization,List.length_map] using hi)

variable {K : Type*} [CommRing K]

def normalProduct (a b : C) : C →₀ K :=
  if h : ((e a).val++(e b).val).IsChain (·≤·)
    then Finsupp.single (concatenateNormal e a b h) 1 else 0

def optionalSingle (M : Option (List C)) : List C →₀ K :=
  M.elim 0 (fun L ↦ Finsupp.single L 1)

theorem adjacent_normalProduct (i : ℕ) (L : List C) :
    adjacent (normalProduct (K := K) e) i L=optionalSingle (normalMerge e i L) := by
  induction i generalizing L with
  | zero =>
    cases L with
    | nil => rfl
    | cons a L =>
      cases L with
      | nil => rfl
      | cons b L =>
        by_cases h : ((e a).val++(e b).val).IsChain (·≤·)
        · simp only [adjacent,normalProduct,normalMerge,dif_pos h,appendTail_single,
            optionalSingle,Option.elim_some]
        · simp only [adjacent,normalProduct,normalMerge,dif_neg h,map_zero,
            optionalSingle,Option.elim_none]
  | succ i ih =>
    cases L with
    | nil => rfl
    | cons a L =>
      rw [adjacent,normalMerge,ih]
      cases normalMerge e i L <;> simp only [optionalSingle,Option.map_none,
        Option.map_some,Option.elim_none,Option.elim_some,map_zero,prefix_single]

def barWordMap (W : List J) (r : ℕ) :
    (BarIndex (·≤·) W r →₀ K) →ₗ[K] (List C →₀ K) :=
  Finsupp.lmapDomain K K (fun L ↦ factorizationBarWord e W L.val)

@[simp] theorem barWordMap_single (W : List J) (r : ℕ)
    (L : BarIndex (·≤·) W r) (c : K) :
    barWordMap e W r (Finsupp.single L c)=
      Finsupp.single (factorizationBarWord e W L.val) c := by
  simp only [barWordMap,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

theorem barWordMap_injective (W : List J) (r : ℕ) :
    Function.Injective (barWordMap (K := K) e W r) := by
  apply Finsupp.mapDomain_injective
  intro L M h
  apply (actualBarIndexEquiv e W r).symm.injective
  apply Subtype.ext
  change factorizationBarWord e W L.val = factorizationBarWord e W M.val
  exact h

end PaperVerification.AlternatingForms.BarCompositions
