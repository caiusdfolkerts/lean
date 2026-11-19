module

public import PaperVerification.AlternatingFormsPBWInversions
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fintype.Pi

/-!
# A finite natural-number filtration on words

The primary comparison is the actual commutative monomial order. A
secondary comparison counts out-of-order letter pairs. On words of each
fixed internal degree, the cardinality of the strict lower set converts
this comparison to a natural-number weight. Thus every replacement needed
by the PBW bar argument strictly decreases a literal finite filtration,
including commutative reorderings with unchanged monomial exponent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators MonomialOrder

namespace PaperVerification.AlternatingForms.PBWWords

variable {α : Type*}

def exponent : List α → α →₀ ℕ
  | [] => 0
  | a::L => Finsupp.single a 1+exponent L

@[simp] theorem exponent_append (L M : List α) :
    exponent (L++M)=exponent L+exponent M := by
  induction L with
  | nil => simp only [List.nil_append,exponent,zero_add]
  | cons a L ih => simp only [List.cons_append,exponent,ih,add_assoc]

@[simp] theorem exponent_apply (L : List α) (a : α) :
    exponent L a=L.count a := by
  induction L with
  | nil => simp only [exponent,Finsupp.zero_apply,List.count_nil]
  | cons b L ih =>
    by_cases h : b=a
    · subst b
      simp only [exponent,Finsupp.add_apply,Finsupp.single_eq_same,
        List.count_cons_self,ih,Nat.add_comm]
    · simp only [exponent,Finsupp.add_apply,Finsupp.single_eq_of_ne (Ne.symm h),
        List.count_cons_of_ne h,zero_add,ih]

theorem exponent_eq_iff_perm (L M : List α) :
    exponent L=exponent M ↔ L.Perm M := by
  rw [List.perm_iff_count]
  constructor
  · intro h a
    simpa only [exponent_apply] using congrArg (fun e : α →₀ ℕ ↦ e a) h
  · intro h
    ext a
    simpa only [exponent_apply] using h a

def Before (m : MonomialOrder α) (R : α → α → Prop) (L M : List α) : Prop :=
  exponent L ≺[m] exponent M ∨
    (exponent L=exponent M ∧ badPairs R L<badPairs R M)

theorem before_irrefl (m : MonomialOrder α) (R : α → α → Prop) (L : List α) :
    ¬Before m R L L := by
  rintro (h | ⟨_,h⟩) <;> exact lt_irrefl _ h

theorem before_trans (m : MonomialOrder α) (R : α → α → Prop)
    {L M N : List α} (hLM : Before m R L M) (hMN : Before m R M N) :
    Before m R L N := by
  rcases hLM with hLM | ⟨hLM,hLM'⟩
  · rcases hMN with hMN | ⟨hMN,hMN'⟩
    · exact Or.inl (hLM.trans hMN)
    · exact Or.inl (hMN ▸ hLM)
  · rcases hMN with hMN | ⟨hMN,hMN'⟩
    · exact Or.inl (hLM.symm ▸ hMN)
    · exact Or.inr ⟨hLM.trans hMN,hLM'.trans hMN'⟩

/-- The full strict word comparison is retained by an identical context.
Equal exponents imply equal multiplicities, so all inversions involving
the context cancel in the secondary comparison. -/
theorem before_context_of_before (m : MonomialOrder α) (R : α → α → Prop)
    (P Q L M : List α) (h : Before m R L M) :
    Before m R (P++L++Q) (P++M++Q) := by
  rcases h with h | ⟨he,h⟩
  · apply Or.inl
    simpa only [exponent_append,map_add,add_assoc,add_comm,add_left_comm] using
      add_lt_add_right (add_lt_add_left h (m.toSyn (exponent P))) (m.toSyn (exponent Q))
  · refine Or.inr ⟨by simp only [exponent_append,he],?_⟩
    have hp := (exponent_eq_iff_perm L M).mp he
    have hb := badPairs_context_balance R P Q L M hp
    omega

/-- A nonnormal product decreases in every context, either in its actual
monomial exponent or in the number of out-of-order pairs. -/
theorem before_context (m : MonomialOrder α) (R : α → α → Prop)
    (P Q L M : List α) (hmon : exponent M ≼[m] exponent L)
    (hL : ¬L.Pairwise R) (hM : M.Pairwise R) :
    Before m R (P++M++Q) (P++L++Q) := by
  rcases hmon.lt_or_eq with hlt | heq
  · apply Or.inl
    simpa only [exponent_append,map_add,add_assoc,add_comm,add_left_comm] using
      add_lt_add_right (add_lt_add_left hlt (m.toSyn (exponent P))) (m.toSyn (exponent Q))
  · have he : exponent M=exponent L := m.toSyn.injective heq
    refine Or.inr ⟨by simp only [exponent_append,he],?_⟩
    exact badPairs_context_decrease R P Q L M
      ((exponent_eq_iff_perm L M).mp he.symm) hL hM

def wordUniverse [Fintype α] (N : ℕ) : Finset (List α) :=
  (Finset.univ : Finset (Fin N → α)).image List.ofFn

theorem mem_wordUniverse [Fintype α] (N : ℕ) (L : List α) (hL : L.length=N) :
    L∈wordUniverse (α := α) N := by
  subst N
  apply Finset.mem_image.mpr
  exact ⟨L.get,Finset.mem_univ _,List.ofFn_get L⟩

def weight [Fintype α] (m : MonomialOrder α) (R : α → α → Prop) (N : ℕ)
    (L : List α) : ℕ :=
  ((wordUniverse (α := α) N).filter (fun M ↦ Before m R M L)).card

/-- Strict comparison is converted to strict natural-number decrease on
the finite set of words of the given internal degree. -/
theorem weight_lt [Fintype α] (m : MonomialOrder α) (R : α → α → Prop)
    (N : ℕ) (L M : List α) (hL : L.length=N) (h : Before m R L M) :
    weight m R N L<weight m R N M := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro T hT
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨hT.1,before_trans m R hT.2 h⟩
  · intro he
    have hmem : L∈(wordUniverse (α := α) N).filter (fun T ↦ Before m R T M) :=
      Finset.mem_filter.mpr ⟨mem_wordUniverse N L hL,h⟩
    rw [←he] at hmem
    exact before_irrefl m R L (Finset.mem_filter.mp hmem).2

theorem weight_context_lt [Fintype α] (m : MonomialOrder α) (R : α → α → Prop)
    (N : ℕ) (P Q L M : List α) (hlen : (P++M++Q).length=N)
    (hmon : exponent M ≼[m] exponent L)
    (hL : ¬L.Pairwise R) (hM : M.Pairwise R) :
    weight m R N (P++M++Q)<weight m R N (P++L++Q) :=
  weight_lt m R N _ _ hlen (before_context m R P Q L M hmon hL hM)

end PaperVerification.AlternatingForms.PBWWords

