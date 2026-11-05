module

public import PaperVerification.AlternatingFormsPluckerDimension
public import PaperVerification.AlternatingFormsOddPencilRelations
public import PaperVerification.AlternatingFormsColoredEdges

/-!
# The odd pencil has the expected Plücker-cone dimension lower bound

The forms below are the two literal path matchings. Their identification with
the existing exterior quadratic forms is proved coefficient by coefficient.
The coordinate plane on the first s odd vertices is common isotropic, giving
the lower dimension bound required by the paper's odd degeneration argument.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Matrix
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {k t : ℕ}

def oddPluckerEdge (k : ℕ) (l : Fin 2) (i : Fin k) : StrictPairs (2*k+1) :=
  ⟨(⟨2*i.val+l.val,by have := i.isLt; have := l.isLt; omega⟩,
    ⟨2*i.val+l.val+1,by have := i.isLt; have := l.isLt; omega⟩),by
      change 2*i.val+l.val < 2*i.val+l.val+1
      omega⟩

def oddPluckerForms (k : ℕ) (l : Fin 2) (a : StrictPairs (2*k+1)) : K :=
  ∑ i : Fin k, if a=oddPluckerEdge k l i then 1 else 0

def twoFormOfCoefficients {M : Type*} [AddCommGroup M] [Module K M]
    {n : ℕ} (f : StrictPairs n → K) (z : Fin n → M) : ⋀[K]^2 M :=
  ∑ a : StrictPairs n, f a • exteriorPair (z a.val.1) (z a.val.2)

theorem oddPluckerForms_twoForm {M : Type*} [AddCommGroup M] [Module K M]
    (k : ℕ) (l : Fin 2) (z : Fin (2*k+1) → M) :
    twoFormOfCoefficients (oddPluckerForms (K := K) k l) z =
      ∑ i : Fin k, exteriorPair (z (oddPluckerEdge k l i).val.1)
        (z (oddPluckerEdge k l i).val.2) := by
  classical
  simp only [twoFormOfCoefficients,oddPluckerForms,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem oddPluckerForms_first
    {M : Type*} [AddCommGroup M] [Module K M] (k : ℕ) (z : Fin (2*k+1) → M) :
    twoFormOfCoefficients (oddPluckerForms (K := K) k 0) z = oddPathFirstQuadratic z := by
  rw [oddPluckerForms_twoForm]
  rfl

theorem oddPluckerForms_second
    {M : Type*} [AddCommGroup M] [Module K M] (k : ℕ) (z : Fin (2*k+1) → M) :
    twoFormOfCoefficients (oddPluckerForms (K := K) k 1) z = oddPathSecondQuadratic z := by
  rw [oddPluckerForms_twoForm]
  rfl

def oddCoordinatePivot (k t : ℕ) (h : t+2≤k+1) : PluckerIndex (t+2) (2*k+1) :=
  ⟨fun i => ⟨2*i.val,by have := i.isLt; omega⟩,by
    intro i j hij
    change 2*i.val<2*j.val
    exact Nat.mul_lt_mul_of_pos_left hij (by decide)⟩

theorem oddCoordinatePlane_isotropic (k t : ℕ) (h : t+2≤k+1)
    (l : Fin 2) (i j : Fin (t+2)) :
    alternatingRowPair (oddPluckerForms (K := K) k l)
      (pluckerCoordinatePlane (K := K) (oddCoordinatePivot k t h)) i j=0 := by
  classical
  simp only [alternatingRowPair,oddPluckerForms,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e he
  simp only [ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have h₁ : ¬ ((oddPluckerEdge k l e).val.1 = (oddCoordinatePivot k t h).val i ∧
      (oddPluckerEdge k l e).val.2 = (oddCoordinatePivot k t h).val j) := by
    rintro ⟨ha,hb⟩
    have ha' := congrArg Fin.val ha
    have hb' := congrArg Fin.val hb
    dsimp [oddPluckerEdge,oddCoordinatePivot] at ha' hb'
    omega
  have h₂ : ¬ ((oddPluckerEdge k l e).val.2 = (oddCoordinatePivot k t h).val i ∧
      (oddPluckerEdge k l e).val.1 = (oddCoordinatePivot k t h).val j) := by
    rintro ⟨ha,hb⟩
    have ha' := congrArg Fin.val ha
    have hb' := congrArg Fin.val hb
    dsimp [oddPluckerEdge,oddCoordinatePivot] at ha' hb'
    omega
  simp only [pluckerCoordinatePlane]
  split_ifs <;> simp_all

/-- The complete expected cone lower bound, with the actual canonical pair,
all odd dimensions, and the entire nonempty isotropic-plane range. -/
theorem odd_isotropic_Plucker_cone_dimension_ge
    (k t : ℕ) (h : t+2≤k+1) :
    ((((t+2)*(2*k+2-2*(t+2))+1) : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) := by
  have hd := isotropic_cone_dimension_bound (oddCoordinatePivot k t h)
    (oddPluckerForms (K := K) k) (oddCoordinatePlane_isotropic k t h)
  have hchoose := two_mul_choose_two_add (t+2)
  have h₁ : (2*k+1-(t+2))+(t+2)=2*k+1 := by omega
  have h₂ : (2*k+2-2*(t+2))+2*(t+2)=2*k+2 := by omega
  have hnum : (t+2)*(2*k+1-(t+2))+1 =
      ((t+2)*(2*k+2-2*(t+2))+1)+2*(t+2).choose 2 := by nlinarith
  rw [hnum,Nat.cast_add] at hd
  exact ENat.WithBot.add_le_add_natCast_right_iff.mp hd

end PaperVerification.AlternatingForms
