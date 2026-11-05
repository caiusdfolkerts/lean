module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.FinCases
public meta import Lean.Elab.Tactic.Omega

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace GraphicalZonotopes.FourColorResource
open Finset Function

def total (a : Fin 4 → ℕ) : ℕ := ∑ i,a i

def Balanced (a : Fin 4 → ℕ) : Prop :=
  (∀ i,0<a i) ∧ ∀ i,3*a i+3≤2*total a

theorem total_ge_four {a : Fin 4 → ℕ} (ha : ∀ i,0<a i) : 4≤total a := by
  calc
    4=∑ i : Fin 4,(1 : ℕ) := by simp
    _≤total a := sum_le_sum (fun i _ => ha i)

theorem total_update (a : Fin 4 → ℕ) (i : Fin 4) (k : ℕ) :
    total (update a i k)+a i=total a+k := by
  fin_cases i <;> simp [total,Fin.sum_univ_succ] <;> omega

theorem pair_bound {a : Fin 4 → ℕ} (ha : ∀ i,0<a i)
    (i j : Fin 4) (hij : i≠j) : a i+a j+2≤total a := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  fin_cases i <;> fin_cases j <;> simp [total,Fin.sum_univ_succ] at hij ⊢ <;> omega

theorem eq_one_of_total_four {a : Fin 4 → ℕ} (ha : ∀ i,0<a i)
    (hN : total a=4) : a=(fun _ => 1) := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have hs : a 0+(a 1+(a 2+a 3))=4 := by
    simpa [total,Fin.sum_univ_succ] using hN
  have hall : a 0=1 ∧ a 1=1 ∧ a 2=1 ∧ a 3=1 :=
    ⟨by omega,by omega,by omega,by omega⟩
  funext i
  fin_cases i
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2.1
  · exact hall.2.2.2

/-- Removing one vertex from a largest part preserves the exact balance
inequalities. Reversing this removal gives strictly positive capacity in the
part to which the vertex is subsequently added. -/
theorem remove_largest {a : Fin 4 → ℕ} (ha : Balanced a) (hN : 4<total a) :
    ∃ i : Fin 4,1<a i ∧
      Balanced (update a i (a i-1)) ∧
      total (update a i (a i-1))+1=total a ∧
      3*(update a i (a i-1) i)+3<2*total (update a i (a i-1)) := by
  obtain ⟨i,_,hmax⟩ := exists_max_image (univ : Finset (Fin 4)) a (by simp)
  have hm : ∀ j,a j≤a i := fun j => hmax j (mem_univ _)
  have hi : 1<a i := by
    by_contra hni
    have hs : total a≤4 := by
      calc
        total a≤∑ j : Fin 4,(1 : ℕ) := sum_le_sum (fun j _ => by have h := hm j;omega)
        _=4 := by simp
    omega
  let b := update a i (a i-1)
  have htotal : total b+1=total a := by
    have h := total_update a i (a i-1)
    dsimp only [b]
    omega
  have hbi : b i=a i-1 := by simp [b]
  have hb : Balanced b := by
    constructor
    · intro j
      by_cases hji : j=i
      · subst j;rw [hbi];omega
      · simpa [b,update_of_ne hji] using ha.1 j
    · intro j
      by_cases hji : j=i
      · subst j
        have h := ha.2 i
        rw [hbi]
        omega
      · have hp := pair_bound ha.1 i j (Ne.symm hji)
        have hmi := hm j
        have hjpos := ha.1 j
        have hbjeq : b j=a j := by simp [b,update_of_ne hji]
        rw [hbjeq]
        omega
  refine ⟨i,hi,hb,htotal,?_⟩
  have h := ha.2 i
  change 3*b i+3<2*total b
  rw [hbi]
  omega

/-- A finite sequence of color additions, starting with one vertex of each
color and using a color only when its triangle capacity is positive. -/
inductive Schedule : (Fin 4 → ℕ) → Prop
  | initial : Schedule (fun _ => 1)
  | add {a : Fin 4 → ℕ} (h : Schedule a) (i : Fin 4)
      (hcapacity : 3*a i+3<2*total a) : Schedule (update a i (a i+1))

/-- Every positive, balanced four-part size vector has a valid unbounded
attachment schedule. No bound on any part size is imposed. -/
theorem schedule_of_balanced {a : Fin 4 → ℕ} (ha : Balanced a) : Schedule a := by
  suffices ∀ N : ℕ,∀ a : Fin 4 → ℕ,total a=N → Balanced a → Schedule a from
    this (total a) a rfl ha
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a hN ha
    by_cases hfour : total a=4
    · rw [eq_one_of_total_four ha.1 hfour]
      exact Schedule.initial
    · have hgt : 4<total a := by have h := total_ge_four ha.1;omega
      obtain ⟨i,hi,hb,hbN,hcap⟩ := remove_largest ha hgt
      let b := update a i (a i-1)
      have hs : Schedule b := ih (total b) (by dsimp only [b];omega) b rfl hb
      have hstep := Schedule.add hs i hcap
      have he : update b i (b i+1)=a := by
        funext j
        by_cases hji : j=i
        · subst j
          simp only [b,update_self]
          omega
        · simp [b,update_of_ne hji]
      rwa [he] at hstep

end GraphicalZonotopes.FourColorResource
