module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Tauto

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace QuadraticSign
open Finset
open scoped symmDiff

/-- The real sign of a parity, written over the natural numbers so that no
representative of an element of `𝔽₂` is chosen implicitly. -/
def parity (n : ℕ) : ℝ := (-1 : ℝ)^n

def triangle (n : ℕ) : ℝ := parity (n.choose 2)

@[simp] theorem parity_zero : parity 0=1 := by simp [parity]
@[simp] theorem parity_one : parity 1=-1 := by simp [parity]
@[simp] theorem parity_add (m n : ℕ) : parity (m+n)=parity m*parity n := by
  simp only [parity,pow_add]
@[simp] theorem parity_square (n : ℕ) : parity n*parity n=1 := by
  simp [parity,← mul_pow]
theorem parity_ne_zero (n : ℕ) : parity n≠0 := pow_ne_zero _ (by norm_num)

theorem parity_mod_two (n : ℕ) : parity n=parity (n%2) :=
  neg_one_pow_eq_pow_mod_two n

theorem parity_mul (m n : ℕ) :
    parity (m*n)=if Even m then 1 else parity n := by
  rw [parity,pow_mul,neg_one_pow_eq_ite]
  split_ifs <;> simp [parity]

@[simp] theorem triangle_zero : triangle 0=1 := by simp [triangle]
@[simp] theorem triangle_one : triangle 1=1 := by simp [triangle]
@[simp] theorem triangle_square (n : ℕ) : triangle n*triangle n=1 := by
  exact parity_square _
theorem triangle_ne_zero (n : ℕ) : triangle n≠0 := parity_ne_zero _

theorem triangle_succ (n : ℕ) : triangle (n+1)=triangle n*parity n := by
  change parity ((n+1).choose (1+1))=triangle n*parity n
  rw [Nat.choose_succ_succ',Nat.choose_one_right,parity_add]
  exact mul_comm _ _

theorem triangle_add (m n : ℕ) :
    triangle (m+n)=triangle m*triangle n*parity (m*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m+(n+1)=(m+n)+1 by omega,triangle_succ,ih,
      triangle_succ,parity_add,show m*(n+1)=m*n+m by ring,parity_add]
    ring

theorem triangle_add_two (n : ℕ) : triangle (n+2)= -triangle n := by
  rw [show n+2=(n+1)+1 by omega,triangle_succ,triangle_succ,parity_add]
  simp only [parity_one]
  calc
    triangle n*parity n*(parity n*(-1)) =
        -(triangle n*(parity n*parity n)) := by ring
    _ = -triangle n := by rw [parity_square,mul_one]

theorem triangle_add_twice (n k : ℕ) :
    triangle (n+2*k)=triangle n*parity k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show n+2*(k+1)=(n+2*k)+2 by omega,triangle_add_two,ih,parity_add]
    simp

variable {I : Type*} [DecidableEq I]

theorem card_symmDiff_add_twice_inter (A B : Finset I) :
    (A∆B).card+2*(A∩B).card=A.card+B.card := by
  have hd : Disjoint (A\B) (B\A) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
  rw [Finset.symmDiff_def,card_union_of_disjoint hd]
  have ha := card_sdiff_add_card_inter A B
  have hb := card_sdiff_add_card_inter B A
  rw [inter_comm B A] at hb
  omega

/-- The complete quadratic form on subsets. Its exponent is precisely the
number of unordered pairs of chosen coordinates. -/
def complete (A : Finset I) : ℝ := triangle A.card

/-- The ordinary Boolean character pairing. -/
def pairing (A B : Finset I) : ℝ := parity (A∩B).card

@[simp] theorem complete_empty : complete (∅ : Finset I)=1 := by simp [complete]
@[simp] theorem complete_square (A : Finset I) : complete A*complete A=1 :=
  triangle_square _
theorem complete_ne_zero (A : Finset I) : complete A≠0 := triangle_ne_zero _
@[simp] theorem pairing_empty_left (A : Finset I) : pairing ∅ A=1 := by simp [pairing]
@[simp] theorem pairing_empty_right (A : Finset I) : pairing A ∅=1 := by simp [pairing]
@[simp] theorem pairing_square (A B : Finset I) : pairing A B*pairing A B=1 :=
  parity_square _
theorem pairing_comm (A B : Finset I) : pairing A B=pairing B A := by
  simp only [pairing,inter_comm]

/-- Polarization of the complete Boolean quadratic form, with every sign
identity proved over the real numbers. -/
theorem complete_symmDiff (A B : Finset I) :
    complete (A∆B)=complete A*complete B*parity (A.card*B.card)*pairing A B := by
  have h := congrArg triangle (card_symmDiff_add_twice_inter A B)
  rw [triangle_add_twice,triangle_add] at h
  calc
    complete (A∆B) =
        (triangle (A∆B).card*parity (A∩B).card)*parity (A∩B).card := by
      rw [mul_assoc,parity_square,mul_one]
      rfl
    _ = (triangle A.card*triangle B.card*parity (A.card*B.card))*
        parity (A∩B).card := by rw [h]
    _ = _ := rfl

/-- The parity of symmetric-difference cardinality is the product of the two
parities; the intersection contributes twice and therefore cancels. -/
theorem parity_card_symmDiff (A B : Finset I) :
    parity (A∆B).card=parity A.card*parity B.card := by
  have h := congrArg parity (card_symmDiff_add_twice_inter A B)
  rw [parity_add,parity_add] at h
  have htwo : parity (2*(A∩B).card)=1 := by
    rw [parity_mul]
    simp
  simpa only [htwo,mul_one] using h

theorem pairing_symmDiff_right (A B C : Finset I) :
    pairing A (B∆C)=pairing A B*pairing A C := by
  have hset : A∩(B∆C)=(A∩B)∆(A∩C) := by
    ext i
    simp only [mem_inter,mem_symmDiff]
    tauto
  change parity (A∩(B∆C)).card=_
  rw [hset,parity_card_symmDiff]
  rfl

theorem pairing_symmDiff_left (A B C : Finset I) :
    pairing (A∆B) C=pairing A C*pairing B C := by
  rw [pairing_comm,pairing_symmDiff_right,pairing_comm C A,pairing_comm C B]

variable [Fintype I]

/-- The bilinear map `I+J` on Boolean subsets. -/
def polar (A : Finset I) : Finset I := if Even A.card then A else Aᶜ

theorem pairing_compl_left (A B : Finset I) :
    pairing Aᶜ B=parity B.card*pairing A B := by
  have hcard : (Aᶜ∩B).card+(A∩B).card=B.card := by
    have hs : Aᶜ∩B=B\A := by ext i; simp [and_comm]
    rw [hs,inter_comm A B]
    exact card_sdiff_add_card_inter B A
  have h := congrArg parity hcard
  rw [parity_add] at h
  calc
    pairing Aᶜ B=(pairing Aᶜ B*pairing A B)*pairing A B := by
      rw [mul_assoc,pairing_square,mul_one]
    _ = parity B.card*pairing A B := by change _ = _; rw [show pairing Aᶜ B * pairing A B = parity B.card from h]

theorem pairing_polar (A B : Finset I) :
    pairing (polar A) B=parity (A.card*B.card)*pairing A B := by
  rw [polar,parity_mul]
  split_ifs with h
  · simp
  · exact pairing_compl_left A B

theorem complete_polarization (A B : Finset I) :
    complete (A∆B)=complete A*complete B*pairing (polar A) B := by
  rw [complete_symmDiff,pairing_polar]
  ring

theorem even_card_compl_iff (hI : Even (Fintype.card I)) (A : Finset I) :
    Even Aᶜ.card ↔ Even A.card := by
  rw [card_compl,Nat.even_iff,Nat.even_iff] 
  have hle := card_le_univ A
  have he := Nat.even_iff.mp hI
  omega

theorem polar_involutive (hI : Even (Fintype.card I)) :
    Function.Involutive (polar (I := I)) := by
  intro A
  by_cases h : Even A.card
  · simp [polar,h]
  · have hc : ¬Even Aᶜ.card := by simpa only [even_card_compl_iff hI A] using h
    simp [polar,h,hc]

theorem polar_eq_empty_iff (hI : Even (Fintype.card I)) (A : Finset I) :
    polar A=∅ ↔ A=∅ := by
  constructor
  · intro h
    have he := congrArg polar h
    rw [polar_involutive hI A] at he
    simpa [polar] using he
  · rintro rfl
    simp [polar]

end QuadraticSign
end GraphicalZonotopes
