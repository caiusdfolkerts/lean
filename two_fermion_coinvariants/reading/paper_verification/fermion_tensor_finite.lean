module

public import Mathlib.RingTheory.TwoSidedIdeal.Basic
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finiteness after imposing scalar relations in a tensor-product algebra

The exterior factor is noncommutative. This lemma therefore works with a
two-sided ideal of the actual tensor-product algebra, and descends the scalar
factor through a commutative ideal quotient.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped TensorProduct

variable {K A B : Type*} [CommRing K] [CommRing A] [Ring B]
variable [Algebra K A] [Algebra K B]

/-- Apply the augmentation on the second tensor factor. -/
def tensorScalarProjection (ε : B →ₐ[K] K) : A ⊗[K] B →ₐ[K] A :=
  Algebra.TensorProduct.productMap (AlgHom.id K A) ((Algebra.ofId K A).comp ε)

@[simp]
theorem tensorScalarProjection_includeLeft (ε : B →ₐ[K] K) (a : A) :
    tensorScalarProjection ε ((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B) a) = a := by
  simp [tensorScalarProjection]

theorem tensorScalarProjection_smul (ε : B →ₐ[K] K) (a : A) (z : A ⊗[K] B) :
    tensorScalarProjection ε (a • z) = a * tensorScalarProjection ε z := by
  rw [Algebra.smul_def, map_mul]
  change tensorScalarProjection ε ((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B) a) * _ = _
  rw [tensorScalarProjection_includeLeft]

/-- A quotient of `A ⊗ B` is finite over `K` if its scalar factor factors through
a finite quotient of `A` and `B` is finite over `K`. -/
theorem finite_tensor_quotient_of_scalar_relations
    (I : TwoSidedIdeal (A ⊗[K] B)) (J : Ideal A)
    [Module.Finite K (A ⧸ J)] [Module.Finite K B]
    (hJ : ∀ a : A, a ∈ J →
      (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B) a ∈ I) :
    Module.Finite K I.ringCon.Quotient := by
  let q : A ⊗[K] B →ₐ[K] I.ringCon.Quotient := I.ringCon.mkₐ K
  let f : A →ₐ[K] I.ringCon.Quotient := q.comp Algebra.TensorProduct.includeLeft
  let g : B →ₐ[K] I.ringCon.Quotient := q.comp Algebra.TensorProduct.includeRight
  have hfJ : ∀ a : A, a ∈ J → f a = 0 := by
    intro a ha
    exact I.ringCon.eq.mpr (hJ a ha)
  let f' : A ⧸ J →ₐ[K] I.ringCon.Quotient := Ideal.Quotient.liftₐ J f hfJ
  have hcomm : ∀ a : A ⧸ J, ∀ b : B, Commute (f' a) (g b) := by
    intro a b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change q (a ⊗ₜ[K] (1 : B)) * q ((1 : A) ⊗ₜ[K] b) =
      q ((1 : A) ⊗ₜ[K] b) * q (a ⊗ₜ[K] (1 : B))
    rw [← map_mul, ← map_mul]
    simp
  let L : (A ⧸ J) ⊗[K] B →ₐ[K] I.ringCon.Quotient :=
    Algebra.TensorProduct.lift f' g hcomm
  let π : A ⊗[K] B →ₐ[K] (A ⧸ J) ⊗[K] B :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K J) (AlgHom.id K B)
  have hcomp : L.comp π = q := by
    apply Algebra.TensorProduct.ext'
    intro a b
    change q (a ⊗ₜ[K] (1 : B)) * q ((1 : A) ⊗ₜ[K] b) = q (a ⊗ₜ[K] b)
    rw [← map_mul]
    simp
  have hsurj : Function.Surjective L := by
    intro z
    obtain ⟨w, rfl⟩ := I.ringCon.mkₐ_surjective (α := K) z
    exact ⟨π w, AlgHom.congr_fun hcomp w⟩
  exact Module.Finite.of_surjective L.toLinearMap hsurj

/-- An augmentation-compatible scalar quotient is a quotient of the full tensor quotient. -/
theorem finite_scalar_quotient_of_tensor_relations
    (ε : B →ₐ[K] K) (I : TwoSidedIdeal (A ⊗[K] B)) (J : Ideal A)
    [Module.Finite K I.ringCon.Quotient]
    (hI : ∀ z : A ⊗[K] B, z ∈ I → tensorScalarProjection ε z ∈ J) :
    Module.Finite K (A ⧸ J) := by
  let f : A ⊗[K] B →ₐ[K] A ⧸ J :=
    (Ideal.Quotient.mkₐ K J).comp (tensorScalarProjection ε)
  have hcon : I.ringCon ≤ RingCon.ker f.toRingHom := by
    intro x y hxy
    change f x = f y
    rw [← sub_eq_zero, ← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hI (x - y) ((I.rel_iff x y).mp hxy)
  let L : I.ringCon.Quotient →ₐ[K] A ⧸ J := I.ringCon.liftₐ f hcon
  have hsurj : Function.Surjective L := by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨I.ringCon.mkₐ K ((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B) a), ?_⟩
    change (I.ringCon.liftₐ f hcon)
      (↑((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B) a) : I.ringCon.Quotient) = _
    rw [RingCon.liftₐ_mk]
    change Ideal.Quotient.mk J
      (tensorScalarProjection ε ((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B) a)) = Ideal.Quotient.mk J a
    rw [tensorScalarProjection_includeLeft]
  exact Module.Finite.of_surjective L.toLinearMap hsurj

/-- With an augmentation on the finite second factor, finiteness is equivalent to
finiteness of the exact scalar quotient. -/
theorem finite_tensor_quotient_iff_scalar_quotient
    (ε : B →ₐ[K] K) (I : TwoSidedIdeal (A ⊗[K] B)) (J : Ideal A)
    [Module.Finite K B]
    (hJ : ∀ a : A, a ∈ J →
      (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B) a ∈ I)
    (hI : ∀ z : A ⊗[K] B, z ∈ I → tensorScalarProjection ε z ∈ J) :
    Module.Finite K I.ringCon.Quotient ↔ Module.Finite K (A ⧸ J) := by
  constructor
  · intro h
    letI := h
    exact finite_scalar_quotient_of_tensor_relations ε I J hI
  · intro h
    letI := h
    exact finite_tensor_quotient_of_scalar_relations I J hJ

end PaperVerification.Fermion
