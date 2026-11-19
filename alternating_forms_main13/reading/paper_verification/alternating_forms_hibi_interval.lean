module

public import PaperVerification.AlternatingFormsIntervalBasis
public import Mathlib.Data.List.Pairwise
public import Mathlib.Order.MinMax

/-!
# The actual interval lattice and finite meet-join sorting

The elements are increasing coordinate tuples in the displayed interval.
Meet and join are literal coordinatewise minimum and maximum. Insertion
sorting replaces each adjacent comparison by meet and join, preserves the
length, and produces a genuine componentwise chain.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

variable {s n : ℕ} (α β : Fin s → Fin n)

def IntervalIndex := {I : PluckerIndex s n // ∀ i,α i≤I.val i ∧ I.val i≤β i}

instance : Fintype (IntervalIndex α β) := by
  classical
  unfold IntervalIndex PluckerIndex
  infer_instance
instance : PartialOrder (IntervalIndex α β) := by
  unfold IntervalIndex PluckerIndex
  infer_instance

def meet (I J : IntervalIndex α β) : IntervalIndex α β :=
  ⟨⟨fun i => min (I.val.val i) (J.val.val i),by
    intro i j hij
    exact lt_min ((min_le_left _ _).trans_lt (I.val.property hij))
      ((min_le_right _ _).trans_lt (J.val.property hij))⟩,by
    intro i
    exact ⟨le_min (I.property i).1 (J.property i).1,
      (min_le_left _ _).trans (I.property i).2⟩⟩

def join (I J : IntervalIndex α β) : IntervalIndex α β :=
  ⟨⟨fun i => max (I.val.val i) (J.val.val i),by
    intro i j hij
    exact max_lt ((I.val.property hij).trans_le (le_max_left _ _))
      ((J.val.property hij).trans_le (le_max_right _ _))⟩,by
    intro i
    exact ⟨(I.property i).1.trans (le_max_left _ _),
      max_le (I.property i).2 (J.property i).2⟩⟩

theorem meet_le_left (I J : IntervalIndex α β) : meet α β I J≤I :=
  fun i => min_le_left _ _

theorem meet_le_right (I J : IntervalIndex α β) : meet α β I J≤J :=
  fun i => min_le_right _ _

theorem left_le_join (I J : IntervalIndex α β) : I≤join α β I J :=
  fun i => le_max_left _ _

theorem right_le_join (I J : IntervalIndex α β) : J≤join α β I J :=
  fun i => le_max_right _ _

theorem le_meet (A I J : IntervalIndex α β) (hI : A≤I) (hJ : A≤J) : A≤meet α β I J :=
  fun i => le_min (hI i) (hJ i)

theorem meet_eq_left (I J : IntervalIndex α β) (h : I≤J) : meet α β I J=I := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact min_eq_left (h i)

theorem meet_eq_right (I J : IntervalIndex α β) (h : J≤I) : meet α β I J=J := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact min_eq_right (h i)

theorem join_eq_right (I J : IntervalIndex α β) (h : I≤J) : join α β I J=J := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact max_eq_right (h i)

theorem join_eq_left (I J : IntervalIndex α β) (h : J≤I) : join α β I J=I := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact max_eq_left (h i)

def insert (I : IntervalIndex α β) : List (IntervalIndex α β) → List (IntervalIndex α β)
  | [] => [I]
  | J::L => meet α β I J :: insert (join α β I J) L

@[simp] theorem length_insert (I : IntervalIndex α β) (L : List (IntervalIndex α β)) :
    (insert α β I L).length=L.length+1 := by
  induction L generalizing I with
  | nil => rfl
  | cons J L ih => simp only [insert,List.length_cons,ih]

theorem insert_lower_bound (A I : IntervalIndex α β) (L : List (IntervalIndex α β))
    (hI : A≤I) (hL : ∀ J∈L,A≤J) : ∀ J∈insert α β I L,A≤J := by
  induction L generalizing I with
  | nil =>
      intro J hJ
      have he : J=I := List.mem_singleton.mp hJ
      exact he.symm ▸ hI
  | cons J L ih =>
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact le_meet α β A I J hI (hL J List.mem_cons_self)
      · exact ih (join α β I J) (hI.trans (left_le_join α β I J))
          (fun T hT => hL T (List.mem_cons_of_mem _ hT)) Z hZ

theorem insert_sorted (I : IntervalIndex α β) (L : List (IntervalIndex α β))
    (hL : L.Pairwise (·≤·)) : (insert α β I L).Pairwise (·≤·) := by
  induction L generalizing I with
  | nil => simp only [insert,List.pairwise_singleton]
  | cons J L ih =>
      have h := List.pairwise_cons.mp hL
      apply List.pairwise_cons.mpr
      refine ⟨?_,ih (join α β I J) h.2⟩
      exact insert_lower_bound α β (meet α β I J) (join α β I J) L
        ((meet_le_left α β I J).trans (left_le_join α β I J))
        (fun T hT => (meet_le_right α β I J).trans (h.1 T hT))

def sort (L : List (IntervalIndex α β)) : List (IntervalIndex α β) :=
  L.foldr (insert α β) []

@[simp] theorem length_sort (L : List (IntervalIndex α β)) :
    (sort α β L).length=L.length := by
  induction L with
  | nil => rfl
  | cons I L ih =>
      change (insert α β I (sort α β L)).length=(I::L).length
      rw [length_insert,ih,List.length_cons]

theorem sort_sorted (L : List (IntervalIndex α β)) :
    (sort α β L).Pairwise (·≤·) := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons I L ih => exact insert_sorted α β I (sort α β L) ih

def chainOfList (L : List (IntervalIndex α β)) (hL : L.Pairwise (·≤·)) :
    BandChain α β L.length :=
  ⟨fun j => (L.get j).val.val,fun j => (L.get j).val.property,
    (fun j i => (L.get j).property i),fun a b hab => hL.rel_get_of_le hab⟩

def intervalIndexOfChain {r : ℕ} (C : BandChain α β r) (j : Fin r) :
    IntervalIndex α β := ⟨⟨C.val j,C.property.1 j⟩,C.property.2.1 j⟩

theorem intervalIndexOfChain_injective {r : ℕ} :
    Function.Injective (fun C : BandChain α β r => intervalIndexOfChain α β C) := by
  intro C D h
  apply Subtype.ext
  funext j i
  exact congrArg (fun I : IntervalIndex α β => I.val.val i) (congrFun h j)

end PaperVerification.AlternatingForms.Hibi
