module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-! # The genuine degreewise scalar change in a polynomial algebra

Multiplying the degree-d coefficient by q^d is an actual algebra automorphism
for every unit q. This is the algebra map induced by replacing T with qT and
will realize a principal Cartier translation on the actual section ring.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.GraphicSectionRing.GradedScalarChange

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]

 def degreeCharacter (q : F) : Multiplicative ℕ →* AddMonoidAlgebra F ℕ where
  toFun d := AddMonoidAlgebra.single d.toAdd (q ^ d.toAdd)
  map_one' := by simp [AddMonoidAlgebra.one_def]
  map_mul' d e := by
    change AddMonoidAlgebra.single (d.toAdd + e.toAdd) (q ^ (d.toAdd + e.toAdd)) = _
    rw [AddMonoidAlgebra.single_mul_single, pow_add]

 def scaleHom (q : F) : AddMonoidAlgebra F ℕ →ₐ[F] AddMonoidAlgebra F ℕ :=
  AddMonoidAlgebra.lift F (AddMonoidAlgebra F ℕ) ℕ (degreeCharacter q)

@[simp] theorem scaleHom_single (q : F) (d : ℕ) (c : F) :
    scaleHom q (AddMonoidAlgebra.single d c) = AddMonoidAlgebra.single d (c * q ^ d) := by
  rw [scaleHom, AddMonoidAlgebra.lift_single]
  change c • AddMonoidAlgebra.single d (q ^ d) = _
  rw [AddMonoidAlgebra.smul_single, smul_eq_mul]

/-- Exact coefficient formula, valid in every degree. -/
 theorem scaleHom_coefficient (q : F) (p : AddMonoidAlgebra F ℕ) (d : ℕ) :
    (scaleHom q p).coeff d = q ^ d * p.coeff d := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p t hp ht => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, ht, mul_add]
  | single m c =>
    rw [scaleHom_single]
    by_cases h : m = d
    · subst m
      simp [mul_comm]
    · simp [AddMonoidAlgebra.coeff_single_apply, h]

 theorem scaleHom_inverse (q : Fˣ) (p : AddMonoidAlgebra F ℕ) :
    scaleHom ((q⁻¹ : Fˣ) : F) (scaleHom (q : F) p) = p := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro d
  rw [scaleHom_coefficient, scaleHom_coefficient, ← mul_assoc]
  have h : (((q⁻¹ : Fˣ) : F) ^ d) * ((q : F) ^ d) = 1 := by
    rw [← mul_pow]
    simp
  rw [h, one_mul]

/-- The principal rescaling is a true algebra automorphism over the base. -/
def equivalence (q : Fˣ) : AddMonoidAlgebra F ℕ ≃ₐ[K] AddMonoidAlgebra F ℕ where
  __ := (scaleHom (q : F)).restrictScalars K
  invFun := scaleHom ((q⁻¹ : Fˣ) : F)
  left_inv := scaleHom_inverse q
  right_inv p := by
    change scaleHom (q : F) (scaleHom ((q⁻¹ : Fˣ) : F) p) = p
    simpa only [inv_inv] using scaleHom_inverse q⁻¹ p

@[simp] theorem equivalence_coefficient (q : Fˣ) (p : AddMonoidAlgebra F ℕ) (d : ℕ) :
    (equivalence (K := K) q p).coeff d = (q : F) ^ d * p.coeff d :=
  scaleHom_coefficient (q : F) p d

#print axioms scaleHom_coefficient
#print axioms equivalence

end Unimodular.GraphicSectionRing.GradedScalarChange

#check Unimodular.GraphicSectionRing.GradedScalarChange.equivalence
