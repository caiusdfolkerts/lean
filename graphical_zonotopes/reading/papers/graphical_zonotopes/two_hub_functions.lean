module

public import Papers.GraphicalZonotopes.GeneralBranchAssembly

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

theorem assembled_context (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (X : Finset H) (Y : Finset J) :
    assembled z F w (context X Y)=z X+∑ j∈Y,w j*F j X := by
  simp only [assembled,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    boundaryLift,hubs_context,branchLift,mem_context_outer]
  simp only [mul_ite,mul_zero]
  rw [← sum_filter]
  have hY : (univ.filter (fun j => j∈Y))=Y := by ext j; simp
  rw [hY]

theorem privateSlice_context (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (X : Finset H) (Y : Finset J) (j : J) (hj : j∉Y) :
    assembled z F w (context X (insert j Y))-assembled z F w (context X Y)=
      w j*F j X := by
  rw [assembled_context,assembled_context,sum_insert hj]
  ring

end BooleanModule

namespace TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Hub (I : Type*) := Bool⊕I
def a : Hub I := .inl false
def b : Hub I := .inl true
def u (i : I) : Hub I := .inr i

/-- The four corner values are (1,1,0,1) when e=false and (0,1,1,1)
when e=true, in the order 00,10,01,11. -/
def corner (e : Bool) : SetFunction Bool := fun S =>
  if false∈S then 1 else if true∈S then (if e then 1 else 0) else (if e then 0 else 1)

def pair (A B C : ℝ) : SetFunction Bool := fun S =>
  (if false∈S then A else 0)+(if true∈S then B else 0)+
    (if false∈S ∧ true∈S then C else 0)

@[simp] theorem pair_empty (A B C : ℝ) : pair A B C ∅=0 := by simp [pair]
@[simp] theorem pair_false (A B C : ℝ) : pair A B C {false}=A := by simp [pair]
@[simp] theorem pair_true (A B C : ℝ) : pair A B C {true}=B := by simp [pair]
@[simp] theorem pair_full (A B C : ℝ) : pair A B C univ=A+B+C := by simp [pair]

theorem bool_set_ext {f g : SetFunction Bool}
    (h0 : f ∅=g ∅) (ha : f {false}=g {false}) (hb : f {true}=g {true})
    (h1 : f univ=g univ) : f=g := by
  funext X
  have hx : X∈(univ : Finset Bool).powerset := mem_powerset.mpr (subset_univ X)
  fin_cases hx <;> simpa using (by first | exact h0 | exact ha | exact hb | exact h1)

theorem eq_pair (f : SetFunction Bool) (h0 : f ∅=0) :
    f=pair (f {false}) (f {true}) (f univ-f {false}-f {true}) := by
  apply bool_set_ext
  · simp [h0]
  · simp
  · simp
  · simp only [pair_full]
    ring

@[simp] theorem corner_empty (e : Bool) : corner e ∅=if e then 0 else 1 := by simp [corner]
@[simp] theorem corner_false (e : Bool) : corner e {false}=1 := by simp [corner]
@[simp] theorem corner_true (e : Bool) : corner e {true}=if e then 1 else 0 := by simp [corner]
@[simp] theorem corner_full (e : Bool) : corner e univ=1 := by simp [corner]

theorem corner_values (e : Bool) (X : Finset Bool) : corner e X=0 ∨ corner e X=1 := by
  unfold corner
  split_ifs <;> simp

theorem corner_nonneg (e : Bool) (X : Finset Bool) : 0≤corner e X := by
  rcases corner_values e X with h | h <;> rw [h] <;> norm_num

theorem corner_private_line (e : Bool) (f : SetFunction Bool)
    (hzero : f (if e then ∅ else {true})=0)
    (ha : f (if e then univ else {false})=f (if e then {true} else ∅))
    (hb : f univ=f {false}) : ∃ c : ℝ,f=c • corner e := by
  cases e with
  | false =>
    refine ⟨f ∅,?_⟩
    apply bool_set_ext <;> simp only [Pi.smul_apply,smul_eq_mul,corner_empty,
      corner_false,corner_true,corner_full,Bool.false_eq_true,ite_false,mul_zero,mul_one]
    · exact ha
    · exact hzero
    · exact hb.trans ha
  | true =>
    refine ⟨f {true},?_⟩
    apply bool_set_ext <;> simp only [Pi.smul_apply,smul_eq_mul,corner_empty,
      corner_false,corner_true,corner_full,ite_true,mul_zero,mul_one]
    · exact hzero
    · exact hb.symm.trans ha
    · exact ha

def eta (ε : Finset I) : ℝ := if ε=∅ then 1 else 0

def central (ε : Finset I) : SetFunction Bool :=
  pair (eta ε) ((Fintype.card I : ℝ)-(ε.card : ℝ)) ((ε.card : ℝ)-1)

def moduleFunction (ε : Finset I) : SetFunction (Hub I) :=
  assembled (central ε) (fun i => corner (decide (i∈ε))) (fun _ => 1)

@[simp] theorem module_empty (ε : Finset I) : moduleFunction ε ∅=0 := by
  simp [moduleFunction,assembled,boundaryLift,branchLift,central]

theorem module_context (ε : Finset I) (X : Finset Bool) (Y : Finset I) :
    moduleFunction ε (context X Y)=central ε X+∑ i∈Y,corner (decide (i∈ε)) X := by
  simp only [moduleFunction,assembled_context,one_mul]

theorem module_outer_zero (ε : Finset I) : OuterZero (moduleFunction ε) := by
  intro i j hij X hi hj
  exact delta_assembled_outer _ _ _ i j hij X hi hj

theorem module_spoke (ε : Finset I) (i : I) (X : Finset Bool) :
    moduleFunction ε (insert (u i) (hubSet X))-moduleFunction ε (hubSet X)=
      corner (decide (i∈ε)) X := by
  simpa only [moduleFunction,u,one_mul,privateSlice] using
    privateSlice_assembled (central ε) (fun i => corner (decide (i∈ε))) (fun _ => 1) i X

theorem module_hub_spoke (ε : Finset I) (i : I) (v : Bool) (X : Finset Bool) :
    delta (moduleFunction ε) (Sum.inl v) (u i) (hubSet X)=
      corner (decide (i∈ε)) (insert v X)-corner (decide (i∈ε)) X := by
  simp only [moduleFunction,u,delta_assembled_spoke _ _ _ _ _ _ (notMem_hubSet_outer X i),
    hubs_hubSet,one_mul]

theorem delta_pair (A B C : ℝ) : delta (pair A B C) false true ∅=C := by
  simp [delta,pair]
  ring

theorem delta_corner (e : Bool) : delta (corner e) false true ∅=if e then -1 else 1 := by
  cases e <;> norm_num [delta,corner]

theorem module_ab (ε Y : Finset I) :
    delta (moduleFunction ε) a b (outerSet Y)=
      ((ε.card : ℝ)-1)+∑ i∈Y,if i∈ε then (-1 : ℝ) else 1 := by
  change delta (assembled (central ε) _ _) (.inl false) (.inl true) (outerSet Y)=_
  rw [delta_assembled_hubs]
  have hh : hubs (outerSet (H:=Bool) Y)=∅ := by ext v; simp
  rw [hh]
  simp only [central,delta_pair,one_mul,mem_outerSet_outer,delta_corner,ite_mul]
  simp only [Bool.decide_iff]
  rw [← sum_filter]
  have hY : (univ.filter (fun i => i∈Y))=Y := by ext i; simp
  rw [hY]

def neighbor (ε : Finset I) (i : I) : Finset I :=
  if i∈ε then ε.erase i else insert i ε

theorem signed_sum_epsilon (ε : Finset I) (γ : I → ℝ) :
    (∑ i∈ε,if i∈ε then -γ i else γ i)= -∑ i∈ε,γ i := by
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  rw [if_pos hi]

theorem signed_sum_neighbor (ε : Finset I) (γ : I → ℝ) (j : I) :
    (∑ i∈neighbor ε j,if i∈ε then -γ i else γ i)= -(∑ i∈ε,γ i)+γ j := by
  unfold neighbor
  by_cases hj : j∈ε
  · rw [if_pos hj]
    have he := sum_erase_add (s:=ε) (f:=fun i => if i∈ε then -γ i else γ i) hj
    rw [signed_sum_epsilon,if_pos hj] at he
    linarith
  · rw [if_neg hj,sum_insert hj,if_neg hj,signed_sum_epsilon]
    ring

theorem module_ab_neighbor (ε : Finset I) (j : I) :
    delta (moduleFunction ε) a b (outerSet (neighbor ε j))=0 := by
  rw [module_ab]
  have hs:=signed_sum_neighbor ε (fun _ => (1 : ℝ)) j
  rw [hs]
  simp

end TwoHub
end GraphicalZonotopes
