module

public import Recovery.Unimodular.GraphicSectionRing.Polytope
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The actual real extension of arbitrary integral coordinate changes

An integral linear equivalence of the original lattices extends to a real
linear equivalence by its values on the standard basis. The extension commutes
with the literal integer-to-real embeddings and therefore with every dilation
of the actual real polytope. No real extension is assumed as extra input.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Pointwise BigOperators

namespace Unimodular.GraphicSectionRing.RealCoordinates

variable {n d : ℕ}

def castLinear (n : ℕ) : Lattice n →ₗ[ℤ] RealLattice n where
  toFun := latticeCast
  map_add' x y := by ext i; exact Int.cast_add _ _
  map_smul' a x := by
    ext i
    change (((a * x i : ℤ) : ℝ)) = a • (x i : ℝ)
    simp only [Int.cast_mul, zsmul_eq_mul]

@[simp] theorem castLinear_apply (x : Lattice n) : castLinear n x = latticeCast x := rfl

@[simp] theorem cast_basis (i : Fin n) :
    latticeCast (Pi.basisFun ℤ (Fin n) i) = Pi.basisFun ℝ (Fin n) i := by
  ext j
  simp [latticeCast, Pi.basisFun_apply, Pi.single_apply]

/-- The real linear map defined by the actual integral matrix columns. -/
def extension (f : Lattice n →ₗ[ℤ] Lattice d) : RealLattice n →ₗ[ℝ] RealLattice d :=
  (Pi.basisFun ℝ (Fin n)).constr ℝ (fun i => latticeCast (f (Pi.basisFun ℤ (Fin n) i)))

@[simp] theorem extension_basis (f : Lattice n →ₗ[ℤ] Lattice d) (i : Fin n) :
    extension f (Pi.basisFun ℝ (Fin n) i) = latticeCast (f (Pi.basisFun ℤ (Fin n) i)) :=
  Module.Basis.constr_basis _ _ _ _

/-- The real extension agrees on every original lattice vector. -/
theorem extension_cast (f : Lattice n →ₗ[ℤ] Lattice d) (x : Lattice n) :
    extension f (latticeCast x) = latticeCast (f x) := by
  have h : ((extension f).restrictScalars ℤ).comp (castLinear n) =
      (castLinear d).comp f := by
    apply (Pi.basisFun ℤ (Fin n)).ext
    intro i
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      castLinear_apply, cast_basis, extension_basis]
  exact LinearMap.congr_fun h x

theorem extension_inverse (e : Lattice n ≃ₗ[ℤ] Lattice d) :
    (extension e.symm.toLinearMap).comp (extension e.toLinearMap) = LinearMap.id := by
  apply (Pi.basisFun ℝ (Fin n)).ext
  intro i
  simp only [LinearMap.comp_apply, extension_basis, extension_cast,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.id_apply, cast_basis]

/-- The uniquely specified real coordinate equivalence, derived from the
integral equivalence and its inverse. -/
def equivalence (e : Lattice n ≃ₗ[ℤ] Lattice d) : RealLattice n ≃ₗ[ℝ] RealLattice d where
  toLinearMap := extension e.toLinearMap
  invFun := extension e.symm.toLinearMap
  left_inv x := LinearMap.congr_fun (extension_inverse e) x
  right_inv x := LinearMap.congr_fun (extension_inverse e.symm) x

@[simp] theorem equivalence_cast (e : Lattice n ≃ₗ[ℤ] Lattice d) (x : Lattice n) :
    equivalence e (latticeCast x) = latticeCast (e x) := extension_cast e.toLinearMap x

/-- The actual polytope in the original real lattice coordinates. -/
def coordinateBody (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d)) :
    Set (RealLattice n) := (equivalence e) ⁻¹' body C

@[simp] theorem cast_mem_coordinateBody (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (x : Lattice n) :
    latticeCast x ∈ coordinateBody e C ↔ Satisfies C (e x) := by
  change equivalence e (latticeCast x) ∈ body C ↔ _
  rw [equivalence_cast, latticeCast_mem_body]

/-- Positive dilation in the original real vector space is carried exactly
to positive dilation in the difference coordinates. -/
theorem cast_mem_coordinate_dilate (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (k : ℕ) (x : Lattice n) :
    latticeCast x ∈ (k : ℝ) • coordinateBody e C ↔
      latticeCast (e x) ∈ (k : ℝ) • body C := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨equivalence e y, hy, ?_⟩
    have h := congrArg (equivalence e) hyx
    simpa only [map_smul, equivalence_cast] using h
  · rintro ⟨y, hy, hyx⟩
    refine ⟨(equivalence e).symm y, ?_, ?_⟩
    · change equivalence e ((equivalence e).symm y) ∈ body C
      simpa only [LinearEquiv.apply_symm_apply] using hy
    · apply (equivalence e).injective
      simpa only [map_smul, LinearEquiv.apply_symm_apply, equivalence_cast] using hyx

#print axioms extension_cast
#print axioms equivalence
#print axioms cast_mem_coordinate_dilate

end Unimodular.GraphicSectionRing.RealCoordinates

#check Unimodular.GraphicSectionRing.RealCoordinates.cast_mem_coordinate_dilate
