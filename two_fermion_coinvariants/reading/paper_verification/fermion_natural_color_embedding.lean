module

public import PaperVerification.FermionNaturalExteriorTensor
public import PaperVerification.FermionDefinitions
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# The literal local color embeddings

Each copy of the two-dimensional color space maps to the original theta and
xi generators at its own index. Independent color changes commute with these
embeddings before any quotient or representation comparison is constructed.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
open scoped BigOperators TensorProduct

namespace PaperVerification.Fermion.NaturalColor

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The local two-color space at index i, embedded in the original odd module. -/
def embedding (i : Fin n) : (Fin 2 → R) →ₗ[R] OddModule R n where
  toFun v := Sum.elim (fun j ↦ if j=i then v 0 else 0)
    (fun j ↦ if j=i then v 1 else 0)
  map_add' v w := by
    funext j
    cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.add_apply] <;>
      split_ifs <;> simp
  map_smul' c v := by
    funext j
    cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.smul_apply,
      smul_eq_mul,RingHom.id_apply] <;> split_ifs <;> simp

@[simp] theorem embedding_theta (i : Fin n) :
    embedding (R := R) i (Pi.single 0 1)=Pi.single (Sum.inl i) 1 := by
  classical
  funext j
  cases j <;> simp [embedding,Pi.single_apply,eq_comm]

@[simp] theorem embedding_xi (i : Fin n) :
    embedding (R := R) i (Pi.single 1 1)=Pi.single (Sum.inr i) 1 := by
  classical
  funext j
  cases j <;> simp [embedding,Pi.single_apply,eq_comm]

/-- The usual matrix action, explicitly on the original two coordinates. -/
def colorLinear (A : Matrix (Fin 2) (Fin 2) R) : (Fin 2 → R) →ₗ[R] (Fin 2 → R) where
  toFun v c := A c 0*v 0+A c 1*v 1
  map_add' v w := by funext c; simp only [Pi.add_apply]; ring
  map_smul' r v := by
    funext c
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

@[simp] theorem colorLinear_one :
    colorLinear (1 : Matrix (Fin 2) (Fin 2) R)=LinearMap.id := by
  ext v c
  fin_cases c <;> simp [colorLinear,Matrix.one_apply]

theorem colorLinear_mul (A B : Matrix (Fin 2) (Fin 2) R) :
    colorLinear (A*B)=(colorLinear A).comp (colorLinear B) := by
  ext v c
  simp only [colorLinear,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.comp_apply,
    Matrix.mul_apply,Fin.sum_univ_two]
  ring

/-- Independent matrix changes on the original theta/xi coordinates.
This is definitionally the existing ColorAction.indexLinear map. -/
def independentLinear (A : Fin n → Matrix (Fin 2) (Fin 2) R) :
    OddModule R n →ₗ[R] OddModule R n where
  toFun v := Sum.elim
    (fun i ↦ A i 0 0*v (.inl i)+A i 0 1*v (.inr i))
    (fun i ↦ A i 1 0*v (.inl i)+A i 1 1*v (.inr i))
  map_add' v w := by
    funext j
    cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.add_apply] <;> ring
  map_smul' c v := by
    funext j
    cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.smul_apply,
      smul_eq_mul,RingHom.id_apply] <;> ring

/-- The local/global commuting square for every matrix at every index. -/
theorem embedding_natural (A : Fin n → Matrix (Fin 2) (Fin 2) R) (i : Fin n) :
    (independentLinear A).comp (embedding i)=
      (embedding i).comp (colorLinear (A i)) := by
  classical
  ext v j
  cases j with
  | inl j =>
      by_cases h : j=i
      · subst j; simp [independentLinear,embedding,colorLinear]
      · simp [independentLinear,embedding,colorLinear,h]
  | inr j =>
      by_cases h : j=i
      · subst j; simp [independentLinear,embedding,colorLinear]
      · simp [independentLinear,embedding,colorLinear,h]

/-- Actual exterior multiplication of arbitrary prescribed local degrees. -/
def assemble (d : Fin n → ℕ) :
    (⨂[R] i : Fin n, (⋀[R]^(d i) (Fin 2 → R))) →ₗ[R]
      ExteriorAlgebra R (OddModule R n) :=
  NaturalExteriorTensor.assemble (R := R) (V := Fin 2 → R) (W := OddModule R n)
    d (embedding (R := R))

@[simp] theorem assemble_tprod (d : Fin n → ℕ)
    (x : ∀ i,⋀[R]^(d i) (Fin 2 → R)) :
    assemble d (PiTensorProduct.tprod R x)=
      (List.ofFn (fun i ↦ ExteriorAlgebra.map (embedding i) (x i))).prod :=
  NaturalExteriorTensor.assemble_tprod (R := R) (V := Fin 2 → R) (W := OddModule R n)
    d (embedding (R := R)) x

/-- The independently defined actions commute with the natural multiplication. -/
theorem assemble_natural (d : Fin n → ℕ)
    (A : Fin n → Matrix (Fin 2) (Fin 2) R)
    (x : ⨂[R] i : Fin n, (⋀[R]^(d i) (Fin 2 → R))) :
    ExteriorAlgebra.map (independentLinear A) (assemble d x)=
      assemble d (PiTensorProduct.map
        (fun i ↦ exteriorPower.map (d i) (colorLinear (A i))) x) :=
  NaturalExteriorTensor.assemble_natural_apply (R := R) (V := Fin 2 → R) (W := OddModule R n)
    d (embedding (R := R))
    (fun i ↦ colorLinear (A i)) (independentLinear A) (embedding_natural A) x

end PaperVerification.Fermion.NaturalColor
