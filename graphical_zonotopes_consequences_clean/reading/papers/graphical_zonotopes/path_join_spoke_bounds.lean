module

public import Papers.GraphicalZonotopes.PathJoinSpokes

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

def incidentParity {n : ℕ} (p : ℕ) (i : Fin (n+2)) : Finset (Fin (n+1)) :=
  univ.filter (fun j => j.val%2=p ∧ (i=j.castSucc ∨ i=j.succ))

def coloredNeighbor {n : ℕ} (p : ℕ) (i : Fin (n+2)) (S : Finset (Vertex n)) : ℝ :=
  ∑ j∈incidentParity p i, neighborBit i j S

theorem incidentParity_card_le_one {n : ℕ} (p : ℕ) (i : Fin (n+2)) :
    (incidentParity p i).card≤1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [incidentParity,mem_filter,mem_univ,true_and,Fin.ext_iff,
    Fin.val_castSucc,Fin.val_succ] at ha hb
  apply Fin.ext
  omega

theorem neighborBit_cases {n : ℕ} (i : Fin (n+2)) (j : Fin (n+1))
    (S : Finset (Vertex n)) : neighborBit i j S=0 ∨ neighborBit i j S=1 := by
  by_cases hl : i=j.castSucc
  · simpa [neighborBit,hl] using bit_cases (vertex j.succ) S
  · by_cases hr : i=j.succ
    · simpa [neighborBit,hl,hr] using bit_cases (vertex j.castSucc) S
    · simp [neighborBit,hl,hr]

theorem coloredNeighbor_bounds {n : ℕ} (p : ℕ) (i : Fin (n+2))
    (S : Finset (Vertex n)) : 0≤coloredNeighbor p i S ∧ coloredNeighbor p i S≤1 := by
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    rcases neighborBit_cases i j S with h | h <;> rw [h] <;> norm_num
  · calc
      coloredNeighbor p i S ≤ ∑ _j∈incidentParity p i,(1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rcases neighborBit_cases i j S with h | h <;> rw [h] <;> norm_num
      _ = ((incidentParity p i).card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast incidentParity_card_le_one p i

theorem coloredNeighbor_eq_sum {n : ℕ} (p : ℕ) (i : Fin (n+2))
    (S : Finset (Vertex n)) :
    coloredNeighbor p i S = ∑ j : Fin (n+1),if j.val%2=p then neighborBit i j S else 0 := by
  rw [coloredNeighbor,incidentParity,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hp : j.val%2=p <;> by_cases hl : i=j.castSucc <;>
    by_cases hr : i=j.succ <;> simp [hp,hl,hr,neighborBit]

theorem coloredNeighbor_first_odd {n : ℕ} (S : Finset (Vertex n)) :
    coloredNeighbor 1 (0 : Fin (n+2)) S=0 := by
  have h : incidentParity 1 (0 : Fin (n+2))=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    simp only [incidentParity,mem_filter,mem_univ,true_and,Fin.ext_iff,
      Fin.val_zero,Fin.val_castSucc,Fin.val_succ] at hj
    omega
  simp [coloredNeighbor,h]

theorem delta_a_colored {n : ℕ} (i : Fin (n+2)) (S : Finset (Vertex n))
    (ha : hubA n∉S) (hi : vertex i∉S) :
    delta (setFunction n) (hubA n) (vertex i) S =
      1-(if i=0 then 0 else 1)*bit (hubB n) S-coloredNeighbor 0 i S+
        bit (hubB n) S*(coloredNeighbor 0 i S+coloredNeighbor 1 i S) := by
  rw [setFunction,delta_polynomial_a _ _ _ ha hi]
  simp only [coefficient,Fin.isValue,Fin.reduceEq,ite_true,ite_false]
  rw [coloredNeighbor_eq_sum,coloredNeighbor_eq_sum]
  have hs : (∑ j : Fin (n+1), neighborBit i j S *
      ((if j.val%2=0 then -1 else 0)+1*bit (hubB n) S)) =
      -(∑ j : Fin (n+1),if j.val%2=0 then neighborBit i j S else 0)+
      bit (hubB n) S*((∑ j : Fin (n+1),if j.val%2=0 then neighborBit i j S else 0)+
        ∑ j : Fin (n+1),if j.val%2=1 then neighborBit i j S else 0) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_neg_distrib]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases he : j.val%2=0
    · have ho : j.val%2≠1 := by omega
      simp [he,ho]; ring
    · have ho : j.val%2=1 := by omega
      simp [he,ho]; ring
  rw [hs]
  by_cases hi0 : i=0 <;> simp [hi0] <;> ring

theorem delta_b_colored {n : ℕ} (i : Fin (n+2)) (S : Finset (Vertex n))
    (hb : hubB n∉S) (hi : vertex i∉S) :
    delta (setFunction n) (hubB n) (vertex i) S =
      (if i=0 then 0 else 1)-(if i=0 then 0 else 1)*bit (hubA n) S-
        coloredNeighbor 1 i S+
        bit (hubA n) S*(coloredNeighbor 0 i S+coloredNeighbor 1 i S) := by
  rw [setFunction,delta_polynomial_b _ _ _ hb hi]
  simp only [coefficient,Fin.isValue,Fin.reduceEq,ite_true,ite_false]
  rw [coloredNeighbor_eq_sum,coloredNeighbor_eq_sum]
  have hs : (∑ j : Fin (n+1), neighborBit i j S *
      ((if j.val%2=0 then 0 else -1)+1*bit (hubA n) S)) =
      -(∑ j : Fin (n+1),if j.val%2=1 then neighborBit i j S else 0)+
      bit (hubA n) S*((∑ j : Fin (n+1),if j.val%2=0 then neighborBit i j S else 0)+
        ∑ j : Fin (n+1),if j.val%2=1 then neighborBit i j S else 0) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_neg_distrib]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases he : j.val%2=0
    · have ho : j.val%2≠1 := by omega
      simp [he,ho]; ring
    · have ho : j.val%2=1 := by omega
      simp [he,ho]; ring
  rw [hs]
  by_cases hi0 : i=0 <;> simp [hi0] <;> ring

theorem delta_a_bounds {n : ℕ} (i : Fin (n+2)) (S : Finset (Vertex n))
    (ha : hubA n∉S) (hi : vertex i∉S) :
    0≤delta (setFunction n) (hubA n) (vertex i) S ∧
      delta (setFunction n) (hubA n) (vertex i) S≤1 := by
  rw [delta_a_colored i S ha hi]
  have he := coloredNeighbor_bounds 0 i S
  have ho := coloredNeighbor_bounds 1 i S
  by_cases hi0 : i=0
  · subst i
    rw [coloredNeighbor_first_odd]
    rcases bit_cases (hubB n) S with h | h <;> simp only [h,ite_true] <;>
      constructor <;> nlinarith
  · rcases bit_cases (hubB n) S with h | h <;> simp only [h,hi0,ite_false] <;>
      constructor <;> nlinarith

theorem delta_b_bounds {n : ℕ} (i : Fin (n+2)) (S : Finset (Vertex n))
    (hb : hubB n∉S) (hi : vertex i∉S) :
    0≤delta (setFunction n) (hubB n) (vertex i) S ∧
      delta (setFunction n) (hubB n) (vertex i) S≤1 := by
  rw [delta_b_colored i S hb hi]
  have he := coloredNeighbor_bounds 0 i S
  have ho := coloredNeighbor_bounds 1 i S
  by_cases hi0 : i=0
  · subst i
    rw [coloredNeighbor_first_odd]
    rcases bit_cases (hubA n) S with h | h <;> simp only [h,ite_true] <;>
      constructor <;> nlinarith
  · rcases bit_cases (hubA n) S with h | h <;> simp only [h,hi0,ite_false] <;>
      constructor <;> nlinarith

end GraphicalZonotopes.PathJoin
