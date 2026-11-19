module

public import PaperVerification.AlternatingFormsOrbitSlotBasis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Exact four-dimensional Pfaffian factorization

Six coordinates are an actual exterior basis. Vanishing of the displayed
Pfaffian, with a nonzero 01 coefficient, gives explicit decomposable
factors. The mixed Pfaffian is exactly the determinant of the four factors,
so its nonvanishing constructs a genuine basis of the vector space.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix

namespace PaperVerification.AlternatingForms.FourPfaffian

variable {R : Type*} [CommRing R]

def pfaffian (c : Fin 6 → R) : R := c 0*c 5-c 1*c 4+c 2*c 3

def polar (c d : Fin 6 → R) : R :=
  c 0*d 5+d 0*c 5-c 1*d 4-d 1*c 4+c 2*d 3+d 2*c 3

def pencil (c d : Fin 6 → R) (t : R) : Fin 6 → R := fun i => c i-t*d i

def discriminant (c d : Fin 6 → R) : R :=
  (polar c d)^2-4*pfaffian d*pfaffian c

def pivotResultant (c d : Fin 6 → R) : R :=
  pfaffian d*(c 0)^2-polar c d*c 0*d 0+pfaffian c*(d 0)^2

theorem pfaffian_pencil (c d : Fin 6 → R) (t : R) :
    pfaffian (pencil c d t)=pfaffian d*t^2-polar c d*t+pfaffian c := by
  dsimp [pfaffian,polar,pencil]
  ring

theorem pencil_polar_identity (c d : Fin 6 → R) (r s : R) :
    polar (pencil c d r) (pencil c d s)+pfaffian d*(r-s)^2=
      pfaffian (pencil c d r)+pfaffian (pencil c d s) := by
  dsimp [pfaffian,polar,pencil]
  ring

variable {K : Type*} [Field K]

def slotRow : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def slotCol : Fin 6 → Fin 4 := ![1,2,3,2,3,3]

theorem slots : OrbitPairSlots slotRow slotCol := by
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [slotRow,slotCol]
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [slotRow,slotCol,Fin.exists_fin_succ]

def formEquiv : (Fin 6 → K) ≃ₗ[K] (⋀[K]^2 (Fin 4 → K)) := orbitSlotLinearEquiv slots

def formBasis : Module.Basis (Fin 6) K (⋀[K]^2 (Fin 4 → K)) := orbitSlotBasis slots

def leftFactor (c : Fin 6 → K) : Fin 4 → K := ![1,0,-c 3/c 0,-c 4/c 0]
def rightFactor (c : Fin 6 → K) : Fin 4 → K := ![0,c 0,c 1,c 2]

/-- A literal factorization in the genuine second exterior power. -/
theorem decomposable_of_pfaffian_zero (c : Fin 6 → K)
    (hc : c 0≠0) (hp : pfaffian c=0) :
    formEquiv c=exteriorPower.ιMulti K 2 ![leftFactor c,rightFactor c] := by
  apply (formEquiv (K := K)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext i
  dsimp only [pfaffian] at hp
  fin_cases i <;>
    simp [formEquiv,orbitSlotLinearEquiv_symm_apply,orbitExteriorCoefficientMatrix,
      orbitExteriorCoefficient_word,slotRow,slotCol,leftFactor,rightFactor]
  all_goals field_simp [hc]
  all_goals linear_combination hp

def factorMatrix (c d : Fin 6 → K) : Matrix (Fin 4) (Fin 4) K :=
  ![leftFactor c,rightFactor c,leftFactor d,rightFactor d]

/-- The determinant records genuine independence of all four factor vectors. -/
theorem factorMatrix_det (c d : Fin 6 → K) (hc : c 0≠0) (hd : d 0≠0)
    (hpc : pfaffian c=0) (hpd : pfaffian d=0) :
    (factorMatrix c d).det=polar c d := by
  have hc5 : c 5=(c 1*c 4-c 2*c 3)/c 0 := by
    apply (eq_div_iff hc).mpr
    dsimp only [pfaffian] at hpc
    linear_combination hpc
  have hd5 : d 5=(d 1*d 4-d 2*d 3)/d 0 := by
    apply (eq_div_iff hd).mpr
    dsimp only [pfaffian] at hpd
    linear_combination hpd
  dsimp only [polar]
  rw [hc5,hd5,Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ]
  norm_num [Matrix.det_fin_three,Matrix.submatrix,Fin.succAbove,factorMatrix,leftFactor,rightFactor]
  field_simp [hc,hd]
  ring

def factorBasis (c d : Fin 6 → K) (h : (factorMatrix c d).det≠0) :
    Module.Basis (Fin 4) K (Fin 4 → K) :=
  basisOfLinearIndependentOfCardEqFinrank' (factorMatrix c d)
    (Matrix.linearIndependent_rows_of_det_ne_zero h) (by simp)

theorem factorBasis_apply (c d : Fin 6 → K) (h : (factorMatrix c d).det≠0) (i : Fin 4) :
    factorBasis c d h i=factorMatrix c d i := by
  exact congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank' (K := K) (factorMatrix c d)
      (Matrix.linearIndependent_rows_of_det_ne_zero h) (by simp)) i

/-- Every simple Pfaffian root lies in the explicit decomposability chart. -/
theorem pencil_pivot_ne_zero (c d : Fin 6 → K) (hR : pivotResultant c d≠0)
    (t : K) (ht : pfaffian (pencil c d t)=0) : pencil c d t 0≠0 := by
  intro hz
  have hc : c 0=t*d 0 := sub_eq_zero.mp hz
  rw [pfaffian_pencil] at ht
  apply hR
  dsimp only [pivotResultant]
  rw [hc]
  linear_combination (d 0)^2*ht

theorem distinct_root_polar_ne_zero (c d : Fin 6 → K) (hd : pfaffian d≠0)
    (r s : K) (hrs : r≠s)
    (hr : pfaffian (pencil c d r)=0) (hs : pfaffian (pencil c d s)=0) :
    polar (pencil c d r) (pencil c d s)≠0 := by
  intro hz
  have h := pencil_polar_identity c d r s
  rw [hz,hr,hs,zero_add,add_zero] at h
  exact (mul_ne_zero hd (pow_ne_zero 2 (sub_ne_zero.mpr hrs))) h

/-- Distinct quadratic roots are constructed in the algebraically closed
coefficient field; no root-existence hypothesis is added to the normal form. -/
theorem quadratic_distinct_roots [CharZero K] [IsAlgClosed K]
    (a b c : K) (ha : a≠0) (hD : b^2-4*a*c≠0) :
    ∃ r s : K,r≠s ∧ a*r^2+b*r+c=0 ∧ a*s^2+b*s+c=0 := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (b^2-4*a*c) (n := 2) (by decide)
  have hz0 : z≠0 := by intro h; rw [h,zero_pow (by decide)] at hz; exact hD hz.symm
  let r := (-b+z)/(2*a)
  let s := (-b-z)/(2*a)
  have hrs : r-s=z/a := by dsimp [r,s]; field_simp [ha]; ring
  refine ⟨r,s,?_,?_,?_⟩
  · intro he
    have hq : z/a=0 := by rw [←hrs,he,sub_self]
    exact (div_ne_zero hz0 ha) hq
  · dsimp [r]
    field_simp [ha]
    linear_combination hz
  · dsimp [s]
    field_simp [ha]
    linear_combination hz

end PaperVerification.AlternatingForms.FourPfaffian
