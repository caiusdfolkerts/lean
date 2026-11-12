module

public import ToricPower.SimplicialPrimitiveBasis
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.Group.Int.Units

/-!
# The actual integer multiplicity of a full-dimensional simplicial cone

Multiplicity is the absolute determinant of the primitive ray vectors
in the original integral lattice. A fixed lattice basis and a finite
enumeration make this a literal natural-number function on cones.
The determinant is proved independent of both choices, so subsequent
column-replacement calculations can use any convenient integral basis
and primitive-ray indexing.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

def latticeBasis (lattice : IsIntegralLattice i) : Module.Basis (Fin (Module.finrank ℤ N)) ℤ N := by
  letI := lattice.free
  letI := lattice.finite
  exact Module.finBasis ℤ N

def coneRayEnumeration (lattice : IsIntegralLattice i) {C : PointedCone ℝ V}
    (toric : IsToricCone i C) (count : Nat.card (ToricRay C) = Module.finrank ℤ N) :
    ToricRay C ≃ Fin (Module.finrank ℤ N) := by
  letI := ToricRay.finite_of_fg toric.fg
  letI := Fintype.ofFinite (ToricRay C)
  exact Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using count)

/-- The determinant multiplicity is used only on full-dimensional
simplicial cones. The value on other cones is a harmless total extension
of the function, not a regularity assertion. -/
def coneMultiplicity (lattice : IsIntegralLattice i) (C : PointedCone ℝ V) : ℕ :=
  if toric : IsToricCone i C then
    if count : Nat.card (ToricRay C) = Module.finrank ℤ N then
      ((latticeBasis lattice).det
        (fun j => primitiveGenerator lattice toric ((coneRayEnumeration lattice toric count).symm j))).natAbs
    else 0
  else 0

theorem coneMultiplicity_eq (lattice : IsIntegralLattice i) {C : PointedCone ℝ V}
    (toric : IsToricCone i C) (count : Nat.card (ToricRay C) = Module.finrank ℤ N) :
    coneMultiplicity lattice C =
      ((latticeBasis lattice).det
        (fun j => primitiveGenerator lattice toric ((coneRayEnumeration lattice toric count).symm j))).natAbs := by
  simp only [coneMultiplicity, dif_pos toric, dif_pos count]

theorem integralBasis_det_natAbs_permute {κ : Type*} [Fintype κ] [DecidableEq κ]
    (basis : Module.Basis κ ℤ N) (vectors : κ → N) (permutation : Equiv.Perm κ) :
    (basis.det (vectors ∘ permutation)).natAbs = (basis.det vectors).natAbs := by
  have matrixEquality : basis.toMatrix (vectors ∘ permutation) =
      (basis.toMatrix vectors).submatrix (Equiv.refl κ) permutation := by
    ext a b
    rfl
  have absolute := Matrix.abs_det_submatrix_equiv_equiv (Equiv.refl κ) permutation (basis.toMatrix vectors)
  rw [Module.Basis.det_apply, Module.Basis.det_apply, matrixEquality]
  have castEquality : (((basis.toMatrix vectors).submatrix (Equiv.refl κ) permutation).det.natAbs : ℤ) =
      ((basis.toMatrix vectors).det.natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs] using absolute
  exact_mod_cast castEquality

theorem integralBasis_det_natAbs_basis_independent {κ : Type*} [Fintype κ] [DecidableEq κ]
    (first second : Module.Basis κ ℤ N) (vectors : κ → N) :
    (first.det vectors).natAbs = (second.det vectors).natAbs := by
  have formula := congrArg (fun f : N [⋀^κ]→ₗ[ℤ] ℤ => f vectors)
    (AlternatingMap.eq_smul_basis_det second first.det)
  change first.det vectors = first.det second * second.det vectors at formula
  rw [formula, Int.natAbs_mul, Int.natAbs_of_isUnit (first.isUnit_det second), one_mul]

/-- Any enumeration of the actual primitive rays computes the same
multiplicity. -/
theorem coneMultiplicity_eq_of_enumeration (lattice : IsIntegralLattice i)
    {C : PointedCone ℝ V} (toric : IsToricCone i C)
    (enumeration : ToricRay C ≃ Fin (Module.finrank ℤ N)) :
    coneMultiplicity lattice C =
      ((latticeBasis lattice).det (fun j => primitiveGenerator lattice toric (enumeration.symm j))).natAbs := by
  have count : Nat.card (ToricRay C) = Module.finrank ℤ N := by
    simpa only [Nat.card_fin] using Nat.card_congr enumeration
  rw [coneMultiplicity_eq lattice toric count]
  let canonical := coneRayEnumeration lattice toric count
  let vectors := fun j => primitiveGenerator lattice toric (enumeration.symm j)
  let permutation : Equiv.Perm (Fin (Module.finrank ℤ N)) := canonical.symm.trans enumeration
  have family : (fun j => primitiveGenerator lattice toric (canonical.symm j)) = vectors ∘ permutation := by
    funext j
    simp only [vectors, permutation, Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [family]
  exact integralBasis_det_natAbs_permute _ _ _

/-- A primitive independent generating family computes multiplicity in
any actual integral basis, regardless of its finite indexing type. -/
theorem coneMultiplicity_eq_det_of_primitive_family (lattice : IsIntegralLattice i)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (basis : Module.Basis κ ℤ N) (vectors : κ → N)
    (primitive : ∀ j, TauCeti.IsPrimitive (vectors j))
    (independent : LinearIndependent ℝ (fun j => i (vectors j)))
    {C : PointedCone ℝ V} (toric : IsToricCone i C)
    (spans : C = PointedCone.hull ℝ (Set.range (fun j => i (vectors j)))) :
    coneMultiplicity lattice C = (basis.det vectors).natAbs := by
  let rays := toricRayEquivOfLinearIndependent (fun j => i (vectors j)) independent spans
  have generator (ρ : ToricRay C) : primitiveGenerator lattice toric ρ = vectors (rays ρ) := by
    apply Eq.symm
    apply IsPrimitiveGenerator.eq_primitiveGenerator _ lattice toric
    apply isPrimitiveGenerator_iff.mpr
    refine ⟨?_, primitive (rays ρ)⟩
    exact (apply_mem_iff_toricRayEquivOfLinearIndependent
      (fun j => i (vectors j)) independent spans ρ (rays ρ)).mpr rfl
  let index := basis.indexEquiv (latticeBasis lattice)
  let enumeration := rays.trans index
  rw [coneMultiplicity_eq_of_enumeration lattice toric enumeration]
  have family : (fun j => primitiveGenerator lattice toric (enumeration.symm j)) = vectors ∘ index.symm := by
    funext j
    rw [generator]
    simp only [enumeration, Equiv.symm_trans_apply, Equiv.apply_symm_apply, Function.comp_apply]
  rw [family, ← Module.Basis.det_reindex (latticeBasis lattice) vectors index.symm]
  exact integralBasis_det_natAbs_basis_independent _ _ _

end ToricPower.FanSubdivision
end
