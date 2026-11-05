module

public import Papers.GraphicalZonotopes.GraphModels
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Finset.Powerset
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

/-- Bounded integral sums attain every value between zero and their total
capacity. This supplies every intermediate branch count, uniformly. -/
theorem bounded_sum_composition {E : Type*} [DecidableEq E] (S : Finset E)
    (d : E → ℕ) {n : ℕ} (hn : n≤∑ i∈S,d i) :
    ∃ f : E → ℕ,(∀ i∈S,f i≤d i) ∧ (∑ i∈S,f i)=n := by
  classical
  induction S using Finset.induction_on generalizing n with
  | empty =>
    have hn0 : n=0 := by simpa using hn
    exact ⟨fun _ => 0,by simp,by simp [hn0]⟩
  | @insert a S ha ih =>
    rw [sum_insert ha] at hn
    have hr : n-min (d a) n≤∑ i∈S,d i := by
      by_cases h : d a≤n
      · rw [min_eq_left h]
        omega
      · rw [min_eq_right (by omega)]
        omega
    obtain ⟨f,hf,hfs⟩ := ih hr
    let g := fun i => if i=a then min (d a) n else f i
    refine ⟨g,?_,?_⟩
    · intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · simp only [g,ite_true]
        exact min_le_left _ _
      · have hia : i≠a := fun h => ha (h ▸ hi)
        simpa only [g,ite_eq_right hia] using hf i hi
    · rw [sum_insert ha]
      have hg : (∑ i∈S,g i)=∑ i∈S,f i := by
        apply sum_congr rfl
        intro i hi
        change (if i=a then min (d a) n else f i)=f i
        exact ite_eq_right (fun (h : i=a) => ha (h ▸ hi))
      rw [hg,hfs]
      simp only [g,ite_true]
      omega

theorem positive_sum_composition {B : Type*} [Fintype B] [DecidableEq B]
    (d : B → ℕ) (hd : ∀ b,1≤d b) {n : ℕ}
    (hnlo : Fintype.card B≤n) (hnhi : n≤∑ b,d b) :
    ∃ k : B → ℕ,(∀ b,1≤k b ∧ k b≤d b) ∧ (∑ b,k b)=n := by
  classical
  have hsum : (∑ b,(d b-1))+Fintype.card B=∑ b,d b := by
    calc
      _ = ∑ b,((d b-1)+1) := by simp [sum_add_distrib]
      _ = _ := sum_congr rfl (fun b _ => Nat.sub_add_cancel (hd b))
  obtain ⟨f,hf,hfs⟩ := bounded_sum_composition (univ : Finset B) (fun b => d b-1)
    (n:=n-Fintype.card B) (by omega)
  refine ⟨fun b => f b+1,?_,?_⟩
  · intro b
    have h := hf b (mem_univ b)
    have hdb := hd b
    change 1≤f b+1 ∧ f b+1≤d b
    constructor <;> omega
  · rw [sum_add_distrib,hfs]
    simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,Nat.cast_id]
    omega

section Powersets
variable {H : Type*} [DecidableEq H]

def blockDimensionSum (S : Finset H) : ℕ :=
  ∑ C∈S.powerset,(C.card.choose 2-1)

def nontrivialSubsets (S : Finset H) : Finset (Finset H) :=
  S.powerset.filter (fun C => 2≤C.card)

theorem small_subsets_card (S : Finset H) :
    (S.powerset.filter (fun C => ¬2≤C.card)).card=S.card+1 := by
  have he : S.powerset.filter (fun C => ¬2≤C.card)=insert ∅ (S.image singleton) := by
    ext C
    simp only [mem_filter,mem_powerset,mem_insert,mem_image]
    constructor
    · rintro ⟨hCS,hC⟩
      have hc : C.card=0 ∨ C.card=1 := by omega
      rcases hc with hc | hc
      · exact Or.inl (card_eq_zero.mp hc)
      · obtain ⟨a,rfl⟩ := card_eq_one.mp hc
        exact Or.inr ⟨a,hCS (mem_singleton_self a),rfl⟩
    · rintro (rfl | ⟨a,ha,rfl⟩)
      · simp
      · simp [singleton_subset_iff,ha]
  rw [he,card_insert_of_notMem]
  · rw [card_image_of_injective _ singleton_injective]
  · simp

theorem nontrivialSubsets_card (S : Finset H) :
    (nontrivialSubsets S).card=2^S.card-S.card-1 := by
  have h := card_filter_add_card_filter_not (s:=S.powerset) (p:=fun C => 2≤C.card)
  rw [small_subsets_card,card_powerset] at h
  change (S.powerset.filter (fun C => 2≤C.card)).card=_
  omega

theorem sum_powerset_card (S : Finset H) :
    (∑ C∈S.powerset,C.card)=S.card*2^(S.card-1) := by
  rw [sum_powerset_apply_card (fun n : ℕ => n)]
  simpa only [nsmul_eq_mul,Nat.mul_comm,Nat.cast_id] using Nat.sum_range_mul_choose S.card

theorem sum_powerset_choose_two (S : Finset H) :
    (∑ C∈S.powerset,C.card.choose 2)=S.card.choose 2*2^(S.card-2) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [sum_powerset_insert ha]
    have ht : ∀ T∈S.powerset,(insert a T).card.choose 2=T.card+T.card.choose 2 := by
      intro T hT
      have haT : a∉T := fun h => ha ((mem_powerset.mp hT) h)
      rw [card_insert_of_notMem haT]
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ T.card 1
    have ht' : (∑ T∈S.powerset,(insert a T).card.choose 2)=
        ∑ T∈S.powerset,(T.card+T.card.choose 2) := sum_congr rfl ht
    rw [ht']
    rw [sum_add_distrib,ih,sum_powerset_card,card_insert_of_notMem ha]
    by_cases h0 : S.card=0
    · norm_num [h0]
    by_cases h1 : S.card=1
    · norm_num [h1]
    have hn : 2≤S.card := by omega
    have he : S.card+1-2=S.card-1 := by omega
    have he' : S.card-2+1=S.card-1 := by omega
    have hp : 2^(S.card-1)=2^(S.card-2)*2 := by rw [← he',pow_succ]
    have hc : (S.card+1).choose 2=S.card+S.card.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ S.card 1
    rw [hc,he,hp]
    ring

theorem blockDimensionSum_add_cliques (S : Finset H) :
    blockDimensionSum S+(nontrivialSubsets S).card=∑ C∈S.powerset,C.card.choose 2 := by
  have hd : blockDimensionSum S=∑ C∈nontrivialSubsets S,(C.card.choose 2-1) := by
    symm
    unfold blockDimensionSum nontrivialSubsets
    apply sum_subset (filter_subset _ _)
    intro C hC hn
    have hc : ¬2≤C.card := fun h => hn (mem_filter.mpr ⟨hC,h⟩)
    have hchoose : C.card.choose 2=0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [hchoose,Nat.zero_sub]
  have hc : (∑ C∈nontrivialSubsets S,C.card.choose 2)=∑ C∈S.powerset,C.card.choose 2 := by
    apply sum_subset (filter_subset _ _)
    intro C hC hn
    exact Nat.choose_eq_zero_of_lt (by
      have h : ¬2≤C.card := fun h => hn (mem_filter.mpr ⟨hC,h⟩)
      omega)
  rw [hd,← hc]
  calc
    _ = ∑ C∈nontrivialSubsets S,((C.card.choose 2-1)+1) := by simp [sum_add_distrib]
    _ = _ := by
      apply sum_congr rfl
      intro C hC
      exact Nat.sub_add_cancel (Nat.choose_pos (mem_filter.mp hC).2)

theorem blockDimensionSum_eq (S : Finset H) :
    blockDimensionSum S=S.card.choose 2*2^(S.card-2)-(2^S.card-S.card-1) := by
  have h := blockDimensionSum_add_cliques S
  rw [nontrivialSubsets_card,sum_powerset_choose_two] at h
  omega

theorem cliqueCapacity_eq_dimension_sum (S : Finset H) :
    cliqueCapacity S.card=blockDimensionSum S+1 := by
  rw [blockDimensionSum_eq]
  rfl

end Powersets
end BooleanModule
end GraphicalZonotopes
