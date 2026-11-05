module

public import Papers.GraphicalZonotopes.RootedResponseAlgebra
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalZonotopes
namespace RootedResponse
open Finset
open scoped BigOperators

def unitBit (i : Fin 3) (x : Fin 3) : Bool := decide (x=i)

def exceptionalCoordinate (v : Row) : Fin 3 :=
  if v 0=v 1 then 2 else if v 0=v 2 then 1 else 0

/-- Each nonconstant three-bit vector is a unit vector or a complementary
unit vector. The exceptional coordinate is selected by a fixed formula. -/
theorem exceptionalCoordinate_spec : ∀ v,Nonconstant v →
    ∀ x,v x=if v (exceptionalCoordinate v) then
      unitBit (exceptionalCoordinate v) x else !(unitBit (exceptionalCoordinate v) x) := by
  decide

def threeRows (complement : Bool) (p : Equiv.Perm (Fin 3)) (j : Fin 3) : Row :=
  fun x => if complement then !(unitBit (p j) x) else unitBit (p j) x

theorem threeRows_nonconstant (complement : Bool) (p : Equiv.Perm (Fin 3))
    (j : Fin 3) : Nonconstant (threeRows complement p j) := by
  have h : ∀ (complement : Bool) (i : Fin 3),Nonconstant
      (fun x => if complement then !(unitBit i x) else unitBit i x) := by decide
  exact h complement (p j)

/-- Any prescribed nonconstant incoming row can occupy any of the three
branch positions. The other rows have the same unit/complement type. -/
theorem threeRows_extend (j : Fin 3) (v : Row) (hv : Nonconstant v) :
    ∃ complement p,threeRows complement p j=v := by
  let i := exceptionalCoordinate v
  refine ⟨!(v i),Equiv.swap j i,?_⟩
  funext x
  rw [exceptionalCoordinate_spec v hv x]
  simp only [threeRows,Equiv.swap_apply_left]
  change (if !(v i) then !(unitBit i x) else unitBit i x)=
    (if v i then unitBit i x else !(unitBit i x))
  cases v i <;> rfl

theorem weighted_unit_row (p : Equiv.Perm (Fin 3)) (lam : Fin 3 → ℝ) (j : Fin 3) :
    (∑ i,lam i*realBit (unitBit (p i) (p j)))=lam j := by
  rw [sum_eq_single j]
  · simp [unitBit,realBit]
  · intro i hi hij
    have he : p j≠p i := fun he => hij (p.injective he.symm)
    simp [unitBit,realBit,he]
  · intro hj
    exact False.elim (hj (mem_univ j))

theorem realBit_not (b : Bool) : realBit (!b)=1-realBit b := by
  cases b <;> norm_num [realBit]

theorem weighted_threeRows_at (complement : Bool) (p : Equiv.Perm (Fin 3))
    (lam : Fin 3 → ℝ) (j : Fin 3) :
    (∑ i,lam i*realBit (threeRows complement p i (p j)))=
      if complement then (∑ i,lam i)-lam j else lam j := by
  cases complement
  · simpa only [threeRows,Bool.false_eq_true,ite_false] using weighted_unit_row p lam j
  · simp only [threeRows,ite_true,realBit_not,mul_sub,mul_one]
    rw [sum_sub_distrib,weighted_unit_row]

/-- The quotient response relation is exactly one-dimensional. No
positivity or prior common-scale hypothesis is used to recover the scales. -/
theorem threeRows_relation_kernel (complement : Bool) (p : Equiv.Perm (Fin 3))
    (lam : Fin 3 → ℝ) (d : ℝ)
    (h : ∀ x,(∑ i,lam i*realBit (threeRows complement p i x))=d) :
    (∀ i,lam i=lam 0) ∧ d=(if complement then 2 else 1)*lam 0 := by
  have he : ∀ j,(if complement then (∑ i,lam i)-lam j else lam j)=d := by
    intro j
    rw [← weighted_threeRows_at]
    exact h (p j)
  have hs : ∀ j,lam j=lam 0 := by
    intro j
    have h0 := he 0
    have hj := he j
    cases complement <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h0 hj <;>
      linarith
  refine ⟨hs,?_⟩
  have h0 := he 0
  have hsum : (∑ i,lam i)=3*lam 0 := by
    simp only [hs,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    norm_num
  rw [hsum] at h0
  cases complement <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h0 ⊢ <;>
    linarith

theorem threeRows_sum (complement : Bool) (p : Equiv.Perm (Fin 3)) (x : Fin 3) :
    (∑ i,realBit (threeRows complement p i x))=if complement then 2 else 1 := by
  have h := weighted_threeRows_at complement p (fun _ => 1) (p.symm x)
  have hsum : (∑ _ : Fin 3,(1:ℝ))=3 := by norm_num
  rw [hsum] at h
  simpa only [Equiv.apply_symm_apply,one_mul,show (3:ℝ)-1=2 by norm_num] using h

def twoRows (v : Row) : Fin 2 → Row := ![v,fun x => !(v x)]

theorem twoRows_nonconstant : ∀ v,Nonconstant v → ∀ j,Nonconstant (twoRows v j) := by
  decide

theorem twoRows_sum (v : Row) (x : Fin 3) :
    (∑ i,realBit (twoRows v i x))=1 := by
  rw [Fin.sum_univ_two]
  change realBit (v x) + realBit (!(v x)) = 1
  cases v x <;> norm_num [realBit]

theorem twoRows_relation_kernel (v : Row) (hv : Nonconstant v)
    (lam : Fin 2 → ℝ) (d : ℝ)
    (h : ∀ x,(∑ i,lam i*realBit (twoRows v i x))=d) :
    lam 0=lam 1 ∧ d=lam 0 := by
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := hv
  have h0 := h i
  have h1 := h j
  simp [twoRows,Fin.sum_univ_two,hi,hj,realBit] at h0 h1
  exact ⟨by linarith,by linarith⟩

end RootedResponse
end GraphicalZonotopes
