module

public import PaperVerification.ExteriorQuadraticDifferential
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Transport of actual exterior differentials

A linear equivalence induces an algebra equivalence of the actual exterior
algebras. Conjugation by this equivalence preserves the odd Leibniz rule,
square-zero identity, and each genuine exterior degree.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ExteriorDerivationTransport

open ExteriorQuadraticDifferential

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Functoriality of the actual exterior algebra, as an algebra equivalence. -/
def mapEquiv (e : M ≃ₗ[R] N) : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R N :=
  { ExteriorAlgebra.map e.toLinearMap with
    invFun := ExteriorAlgebra.map e.symm.toLinearMap
    left_inv := ExteriorAlgebra.leftInverse_map_iff.mpr e.left_inv
    right_inv := ExteriorAlgebra.leftInverse_map_iff.mpr e.right_inv }

@[simp] theorem mapEquiv_apply (e : M ≃ₗ[R] N) (x : ExteriorAlgebra R M) :
    mapEquiv e x = ExteriorAlgebra.map e.toLinearMap x := rfl

@[simp] theorem mapEquiv_symm_apply (e : M ≃ₗ[R] N) (x : ExteriorAlgebra R N) :
    (mapEquiv e).symm x = ExteriorAlgebra.map e.symm.toLinearMap x := rfl

@[simp] theorem mapEquiv_ι (e : M ≃ₗ[R] N) (m : M) :
    mapEquiv e (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι R (e m) :=
  ExteriorAlgebra.map_apply_ι _ _

@[simp] theorem mapEquiv_symm_ι (e : M ≃ₗ[R] N) (n : N) :
    (mapEquiv e).symm (ExteriorAlgebra.ι R n) = ExteriorAlgebra.ι R (e.symm n) :=
  ExteriorAlgebra.map_apply_ι _ _

/-- The exterior grading involution is natural under every linear map. -/
theorem parity_map (e : M ≃ₗ[R] N) (x : ExteriorAlgebra R M) :
    parity (mapEquiv e x) = mapEquiv e (parity x) := by
  have h : parity.comp (mapEquiv e).toAlgHom =
      (mapEquiv e).toAlgHom.comp parity := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro m
    simp [parity, CliffordAlgebra.involute_ι]
  exact DFunLike.congr_fun h x

/-- Conjugation of the genuine linear differential. -/
def conjugate (e : M ≃ₗ[R] N) (D : Module.End R (ExteriorAlgebra R M)) :
    Module.End R (ExteriorAlgebra R N) :=
  (mapEquiv e).toLinearMap.comp (D.comp (mapEquiv e).symm.toLinearMap)

@[simp] theorem conjugate_apply (e : M ≃ₗ[R] N)
    (D : Module.End R (ExteriorAlgebra R M)) (x : ExteriorAlgebra R N) :
    conjugate e D x = mapEquiv e (D ((mapEquiv e).symm x)) := rfl

/-- Odd derivations remain odd derivations under the actual algebra map. -/
theorem conjugate_isOddDerivation (e : M ≃ₗ[R] N)
    (D : Module.End R (ExteriorAlgebra R M)) (hD : IsOddDerivation D) :
    IsOddDerivation (conjugate e D) := by
  constructor
  · simp [conjugate_apply, hD.1]
  · intro x y
    change mapEquiv e (D ((mapEquiv e).symm (x*y))) = _
    rw [map_mul, hD.2, map_add, map_mul, map_mul]
    rw [← parity_map]
    simp only [AlgEquiv.apply_symm_apply, conjugate_apply]

/-- No square-zero assumption is lost when changing cochain coordinates. -/
theorem conjugate_square_zero (e : M ≃ₗ[R] N)
    (D : Module.End R (ExteriorAlgebra R M)) (hD : ∀ x, D (D x) = 0)
    (x : ExteriorAlgebra R N) : conjugate e D (conjugate e D x) = 0 := by
  simp only [conjugate_apply, AlgEquiv.symm_apply_apply, hD, map_zero]

/-- Exterior algebra maps preserve the actual homogeneous submodules. -/
theorem map_mem_exteriorPower (f : M →ₗ[R] N) {q : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^q M) :
    ExteriorAlgebra.map f x ∈ ⋀[R]^q N := by
  simpa only [exteriorPower.coe_map] using (exteriorPower.map q f ⟨x,hx⟩).property

/-- Conjugation also preserves the precise degree-one shift. -/
theorem conjugate_degree (e : M ≃ₗ[R] N)
    (D : Module.End R (ExteriorAlgebra R M))
    (hD : ∀ q x, x ∈ ⋀[R]^q M → D x ∈ ⋀[R]^(q+1) M)
    (q : ℕ) (x : ExteriorAlgebra R N) (hx : x ∈ ⋀[R]^q N) :
    conjugate e D x ∈ ⋀[R]^(q+1) N :=
  map_mem_exteriorPower e.toLinearMap
    (hD q _ (map_mem_exteriorPower e.symm.toLinearMap hx))

end PaperVerification.ExteriorDerivationTransport
