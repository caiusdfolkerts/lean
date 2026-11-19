module

public import Papers.GraphicalZonotopes.PathJoinCliques

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

def bit {n : ℕ} (v : Vertex n) (S : Finset (Vertex n)) : ℝ := if v∈S then 1 else 0

theorem bit_cases {n : ℕ} (v : Vertex n) (S : Finset (Vertex n)) :
    bit v S=0 ∨ bit v S=1 := by
  by_cases h : v∈S <;> simp [bit,h]

theorem bit_nonneg {n : ℕ} (v : Vertex n) (S : Finset (Vertex n)) : 0≤bit v S := by
  rcases bit_cases v S with h | h <;> rw [h] <;> norm_num

theorem bit_le_one {n : ℕ} (v : Vertex n) (S : Finset (Vertex n)) : bit v S≤1 := by
  rcases bit_cases v S with h | h <;> rw [h] <;> norm_num

theorem delta_clique_hub {n : ℕ} (s : Slot n) (S : Finset (Vertex n))
    (ha : hubA n∉S) (hb : hubB n∉S) :
    delta (setMonomial (clique s)) (hubA n) (hubB n) S =
      match s with
      | .inl _ => 1
      | .inr (.inl (r,i)) => if r=2 then bit (vertex i) S else 0
      | .inr (.inr (r,i)) =>
        if r=3 then bit (vertex i.castSucc) S*bit (vertex i.succ) S else 0 := by
  rw [delta_setMonomial (hubA_ne_hubB n) ha hb]
  rcases s with u | ⟨r,i⟩ | ⟨r,i⟩
  · simp [clique]
  · fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
  · fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    by_cases hl : vertex i.castSucc∈S <;> by_cases hr : vertex i.succ∈S <;>
      simp [hl,hr]

theorem delta_polynomial_hub {n : ℕ} (x : Slot n → ℝ) (S : Finset (Vertex n))
    (ha : hubA n∉S) (hb : hubB n∉S) :
    delta (FiniteMonomial.polynomial clique x) (hubA n) (hubB n) S =
      x (.inl ()) +
        ∑ i : Fin (n+2),x (.inr (.inl (2,i)))*bit (vertex i) S +
        ∑ i : Fin (n+1),x (.inr (.inr (3,i)))*
          bit (vertex i.castSucc) S*bit (vertex i.succ) S := by
  rw [FiniteMonomial.polynomial,delta_sum]
  simp only [delta_smul]
  simp_rw [delta_clique_hub _ _ ha hb]
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_three,
    Fin.sum_univ_four,mul_assoc,add_assoc]

theorem delta_hub {n : ℕ} (S : Finset (Vertex n))
    (ha : hubA n∉S) (hb : hubB n∉S) :
    delta (setFunction n) (hubA n) (hubB n) S = ((n+2)/2 : ℕ) -
      ∑ i : Fin (n+1),(1-bit (vertex i.castSucc) S)*bit (vertex i.succ) S := by
  rw [setFunction,delta_polynomial_hub _ _ ha hb]
  have hsum : (∑ i : Fin (n+2),
      coefficient n (.inr (.inl (2,i)))*bit (vertex i) S) =
      -∑ i : Fin (n+1),bit (vertex i.succ) S := by
    rw [Fin.sum_univ_succ]
    simp [coefficient,Fin.succ_ne_zero,Finset.sum_neg_distrib]
  rw [hsum]
  simp only [coefficient,Fin.isValue,Fin.reduceEq,ite_false,one_mul]
  simp only [sub_mul,one_mul,Finset.sum_sub_distrib]
  ring

theorem path_vertices_mem_pair_iff {n : ℕ} (r : Fin 4) (j : Fin (n+1))
    (i : Fin (n+2)) :
    vertex i∈clique (.inr (.inr (r,j)) : Slot n) ↔ i=j.castSucc ∨ i=j.succ := by
  fin_cases r <;> simp [clique]

theorem delta_clique_path {n : ℕ} (s : Slot n) (i : Fin (n+1))
    (S : Finset (Vertex n)) (hl : vertex i.castSucc∉S) (hr : vertex i.succ∉S) :
    delta (setMonomial (clique s)) (vertex i.castSucc) (vertex i.succ) S =
      match s with
      | .inl _ => 0
      | .inr (.inl _) => 0
      | .inr (.inr (r,j)) =>
        if j=i then
          if r=0 then 1 else if r=1 then bit (hubA n) S
          else if r=2 then bit (hubB n) S else bit (hubA n) S*bit (hubB n) S
        else 0 := by
  rw [delta_setMonomial (vertex_left_ne_right i) hl hr]
  rcases s with u | ⟨r,j⟩ | ⟨r,j⟩
  · simp [clique]
  · have hne : i.castSucc≠i.succ := by intro h; have := congrArg Fin.val h; simp at this
    fin_cases r <;> simp [clique,vertex_inj]
    all_goals intro h0 h1; exact (hne (h0.trans h1.symm)).elim
  · by_cases he : j=i
    · subst j
      fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
      by_cases ha : hubA n∈S <;> by_cases hb : hubB n∈S <;> simp [ha,hb]
    · have hnot : ¬(vertex i.castSucc∈clique (.inr (.inr (r,j)) : Slot n) ∧
          vertex i.succ∈clique (.inr (.inr (r,j)) : Slot n)) := by
        intro h
        have h0 := (path_vertices_mem_pair_iff r j i.castSucc).mp h.1
        have h1 := (path_vertices_mem_pair_iff r j i.succ).mp h.2
        simp only [Fin.ext_iff,Fin.val_castSucc,Fin.val_succ] at h0 h1
        apply he
        apply Fin.ext
        omega
      simp only [he,ite_false]
      apply if_neg
      intro h
      exact hnot ⟨h.1,h.2.1⟩

theorem delta_polynomial_path {n : ℕ} (x : Slot n → ℝ) (i : Fin (n+1))
    (S : Finset (Vertex n)) (hl : vertex i.castSucc∉S) (hr : vertex i.succ∉S) :
    delta (FiniteMonomial.polynomial clique x) (vertex i.castSucc) (vertex i.succ) S =
      x (.inr (.inr (0,i))) + x (.inr (.inr (1,i)))*bit (hubA n) S +
      x (.inr (.inr (2,i)))*bit (hubB n) S +
      x (.inr (.inr (3,i)))*bit (hubA n) S*bit (hubB n) S := by
  rw [FiniteMonomial.polynomial,delta_sum]
  simp only [delta_smul]
  simp_rw [delta_clique_path _ _ _ hl hr]
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_three,
    Fin.sum_univ_four,mul_ite,mul_assoc,add_assoc]

theorem delta_path {n : ℕ} (i : Fin (n+1)) (S : Finset (Vertex n))
    (hl : vertex i.castSucc∉S) (hr : vertex i.succ∉S) :
    delta (setFunction n) (vertex i.castSucc) (vertex i.succ) S =
      1 - (if i.val%2=0 then bit (hubA n) S else bit (hubB n) S) +
        bit (hubA n) S*bit (hubB n) S := by
  rw [setFunction,delta_polynomial_path _ _ _ hl hr]
  by_cases he : i.val%2=0 <;> simp [coefficient,he] <;> ring

theorem delta_path_boolean {n : ℕ} (i : Fin (n+1)) (S : Finset (Vertex n))
    (hl : vertex i.castSucc∉S) (hr : vertex i.succ∉S) :
    delta (setFunction n) (vertex i.castSucc) (vertex i.succ) S=0 ∨
      delta (setFunction n) (vertex i.castSucc) (vertex i.succ) S=1 := by
  rw [delta_path i S hl hr]
  rcases bit_cases (hubA n) S with ha | ha <;>
    rcases bit_cases (hubB n) S with hb | hb <;>
      by_cases he : i.val%2=0 <;> simp [ha,hb,he]

end GraphicalZonotopes.PathJoin
