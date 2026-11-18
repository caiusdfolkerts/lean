module

public import Papers.GraphicalZonotopes.PathJoinSlacks

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

def transitionSet {n : ℕ} (S : Finset (Vertex n)) : Finset (Fin (n+1)) :=
  univ.filter (fun i => vertex i.castSucc∉S ∧ vertex i.succ∈S)

theorem transition_endpoints_disjoint {n : ℕ} (S : Finset (Vertex n)) :
    Disjoint ((transitionSet S).image Fin.castSucc) ((transitionSet S).image Fin.succ) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
  obtain ⟨j,hj,hji⟩ := mem_image.mp hy
  have hzero := (mem_filter.mp hi).2.1
  have hone := (mem_filter.mp hj).2.2
  apply hzero
  simpa only [hji] using hone

theorem transition_card_le {n : ℕ} (S : Finset (Vertex n)) :
    (transitionSet S).card≤(n+2)/2 := by
  have hl : ((transitionSet S).image Fin.castSucc).card=(transitionSet S).card :=
    card_image_of_injective _ (Fin.castSucc_injective (n+1))
  have hr : ((transitionSet S).image Fin.succ).card=(transitionSet S).card :=
    card_image_of_injective _ (Fin.succ_injective (n+1))
  have hc := card_le_card (subset_univ
    (((transitionSet S).image Fin.castSucc)∪((transitionSet S).image Fin.succ)))
  rw [card_union_of_disjoint (transition_endpoints_disjoint S),hl,hr,
    card_univ,Fintype.card_fin] at hc
  omega

theorem transition_sum_eq_card {n : ℕ} (S : Finset (Vertex n)) :
    (∑ i : Fin (n+1),(1-bit (vertex i.castSucc) S)*bit (vertex i.succ) S) =
      ((transitionSet S).card : ℝ) := by
  have he (i : Fin (n+1)) :
      (1-bit (vertex i.castSucc) S)*bit (vertex i.succ) S =
      if vertex i.castSucc∉S ∧ vertex i.succ∈S then (1 : ℝ) else 0 := by
    by_cases hl : vertex i.castSucc∈S <;> by_cases hr : vertex i.succ∈S <;>
      simp [bit,hl,hr]
  simp_rw [he]
  simp [transitionSet]

theorem delta_hub_bounds {n : ℕ} (S : Finset (Vertex n))
    (ha : hubA n∉S) (hb : hubB n∉S) :
    0≤delta (setFunction n) (hubA n) (hubB n) S ∧
      delta (setFunction n) (hubA n) (hubB n) S≤((n+2)/2 : ℕ) := by
  rw [delta_hub S ha hb,transition_sum_eq_card]
  have hc : ((transitionSet S).card : ℝ)≤((n+2)/2 : ℕ) := by
    exact_mod_cast transition_card_le S
  have hn : (0 : ℝ)≤((transitionSet S).card : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

def alternatingSet (n : ℕ) : Finset (Vertex n) :=
  univ.filter (fun v => 2≤v.val ∧ v.val%2=1)

@[simp] theorem hubA_notMem_alternatingSet (n : ℕ) : hubA n∉alternatingSet n := by
  simp [alternatingSet,hubA]
@[simp] theorem hubB_notMem_alternatingSet (n : ℕ) : hubB n∉alternatingSet n := by
  simp [alternatingSet,hubB]
@[simp] theorem vertex_mem_alternatingSet {n : ℕ} (i : Fin (n+2)) :
    vertex i∈alternatingSet n ↔ i.val%2=1 := by
  simp [alternatingSet,vertex,Nat.add_mod]

def evenEdgeEquiv (n : ℕ) : {i : Fin (n+1) // i.val%2=0} ≃ Fin ((n+2)/2) where
  toFun i := ⟨i.1.val/2,by have := i.1.isLt; have := i.2; omega⟩
  invFun j := ⟨⟨2*j.val,by have := j.isLt; omega⟩,by change (2*j.val)%2=0; omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change 2*(i.1.val/2)=i.1.val
    have := i.2
    omega
  right_inv j := by
    apply Fin.ext
    change (2*j.val)/2=j.val
    omega

theorem alternating_transitions (n : ℕ) :
    transitionSet (alternatingSet n)=univ.filter (fun i : Fin (n+1) => i.val%2=0) := by
  ext i
  simp only [transitionSet,mem_filter,mem_univ,true_and,vertex_mem_alternatingSet,
    Fin.val_castSucc,Fin.val_succ]
  omega

theorem alternating_transition_card (n : ℕ) :
    (transitionSet (alternatingSet n)).card=(n+2)/2 := by
  rw [alternating_transitions,← Fintype.card_subtype]
  exact (Fintype.card_congr (evenEdgeEquiv n)).trans (Fintype.card_fin _)

theorem delta_hub_alternating (n : ℕ) :
    delta (setFunction n) (hubA n) (hubB n) (alternatingSet n)=0 := by
  rw [delta_hub _ (hubA_notMem_alternatingSet n) (hubB_notMem_alternatingSet n),
    transition_sum_eq_card,alternating_transition_card,sub_self]

end GraphicalZonotopes.PathJoin
