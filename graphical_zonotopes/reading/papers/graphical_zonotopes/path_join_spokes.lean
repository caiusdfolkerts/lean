module

public import Papers.GraphicalZonotopes.PathJoinTransitions

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

def neighborBit {n : ℕ} (i : Fin (n+2)) (j : Fin (n+1))
    (S : Finset (Vertex n)) : ℝ :=
  if i=j.castSucc then bit (vertex j.succ) S
  else if i=j.succ then bit (vertex j.castSucc) S else 0

@[simp] theorem edge_castSucc_ne_succ {n : ℕ} (j : Fin (n+1)) :
    j.castSucc ≠ j.succ := by
  intro h
  have := congrArg Fin.val h
  simp at this

@[simp] theorem edge_succ_ne_castSucc {n : ℕ} (j : Fin (n+1)) :
    j.succ ≠ j.castSucc := (edge_castSucc_ne_succ j).symm

theorem delta_clique_a {n : ℕ} (s : Slot n) (i : Fin (n+2))
    (S : Finset (Vertex n)) (ha : hubA n∉S) (hi : vertex i∉S) :
    delta (setMonomial (clique s)) (hubA n) (vertex i) S =
      match s with
      | .inl _ => 0
      | .inr (.inl (r,j)) =>
        if j=i then if r=0 then 1 else if r=2 then bit (hubB n) S else 0 else 0
      | .inr (.inr (r,j)) =>
        if r=1 then neighborBit i j S
        else if r=3 then neighborBit i j S*bit (hubB n) S else 0 := by
  rw [delta_setMonomial (vertex_ne_hubA i).symm ha hi]
  rcases s with u | ⟨r,j⟩ | ⟨r,j⟩
  · simp [clique]
  · by_cases hj : j=i
    · subst j
      fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    · fin_cases r <;> simp [clique,hj,Ne.symm hj]
  · by_cases hl : i=j.castSucc
    · subst i
      fin_cases r <;> simp [clique,neighborBit,bit,Finset.insert_subset_iff,
        Finset.singleton_subset_iff]
      by_cases hb : hubB n∈S <;> by_cases hr : vertex j.succ∈S <;> simp [hb,hr]
    · by_cases hr : i=j.succ
      · subst i
        fin_cases r <;> simp [clique,neighborBit,hl,bit,Finset.insert_subset_iff,
          Finset.singleton_subset_iff]
        by_cases hb : hubB n∈S <;> by_cases he : vertex j.castSucc∈S <;> simp [hb,he]
      · fin_cases r <;> simp [clique,neighborBit,hl,hr]

theorem delta_clique_b {n : ℕ} (s : Slot n) (i : Fin (n+2))
    (S : Finset (Vertex n)) (hb : hubB n∉S) (hi : vertex i∉S) :
    delta (setMonomial (clique s)) (hubB n) (vertex i) S =
      match s with
      | .inl _ => 0
      | .inr (.inl (r,j)) =>
        if j=i then if r=1 then 1 else if r=2 then bit (hubA n) S else 0 else 0
      | .inr (.inr (r,j)) =>
        if r=2 then neighborBit i j S
        else if r=3 then neighborBit i j S*bit (hubA n) S else 0 := by
  rw [delta_setMonomial (vertex_ne_hubB i).symm hb hi]
  rcases s with u | ⟨r,j⟩ | ⟨r,j⟩
  · simp [clique]
  · by_cases hj : j=i
    · subst j
      fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    · fin_cases r <;> simp [clique,hj,Ne.symm hj]
  · by_cases hl : i=j.castSucc
    · subst i
      fin_cases r <;> simp [clique,neighborBit,bit,Finset.insert_subset_iff,
        Finset.singleton_subset_iff]
      by_cases ha : hubA n∈S <;> by_cases hr : vertex j.succ∈S <;> simp [ha,hr]
    · by_cases hr : i=j.succ
      · subst i
        fin_cases r <;> simp [clique,neighborBit,hl,bit,Finset.insert_subset_iff,
          Finset.singleton_subset_iff]
        by_cases ha : hubA n∈S <;> by_cases he : vertex j.castSucc∈S <;> simp [ha,he]
      · fin_cases r <;> simp [clique,neighborBit,hl,hr]

theorem delta_polynomial_a {n : ℕ} (x : Slot n → ℝ) (i : Fin (n+2))
    (S : Finset (Vertex n)) (ha : hubA n∉S) (hi : vertex i∉S) :
    delta (FiniteMonomial.polynomial clique x) (hubA n) (vertex i) S =
      x (.inr (.inl (0,i))) + x (.inr (.inl (2,i)))*bit (hubB n) S +
      ∑ j : Fin (n+1), neighborBit i j S *
        (x (.inr (.inr (1,j)))+x (.inr (.inr (3,j)))*bit (hubB n) S) := by
  rw [FiniteMonomial.polynomial,delta_sum]
  simp only [delta_smul]
  simp_rw [delta_clique_a _ _ _ ha hi]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_three,
    Fin.sum_univ_four,Fin.isValue,Fin.reduceEq,ite_true,ite_false,mul_zero,
    Finset.sum_const_zero,add_zero,zero_add,Fintype.sum_unique,mul_ite,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_one]
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem delta_polynomial_b {n : ℕ} (x : Slot n → ℝ) (i : Fin (n+2))
    (S : Finset (Vertex n)) (hb : hubB n∉S) (hi : vertex i∉S) :
    delta (FiniteMonomial.polynomial clique x) (hubB n) (vertex i) S =
      x (.inr (.inl (1,i))) + x (.inr (.inl (2,i)))*bit (hubA n) S +
      ∑ j : Fin (n+1), neighborBit i j S *
        (x (.inr (.inr (2,j)))+x (.inr (.inr (3,j)))*bit (hubA n) S) := by
  rw [FiniteMonomial.polynomial,delta_sum]
  simp only [delta_smul]
  simp_rw [delta_clique_b _ _ _ hb hi]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_three,
    Fin.sum_univ_four,Fin.isValue,Fin.reduceEq,ite_true,ite_false,mul_zero,
    Finset.sum_const_zero,add_zero,zero_add,Fintype.sum_unique,mul_ite,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_one]
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

end GraphicalZonotopes.PathJoin
