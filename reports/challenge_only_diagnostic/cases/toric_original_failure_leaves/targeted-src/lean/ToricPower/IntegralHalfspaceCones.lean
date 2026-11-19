module

public import ToricPower.IntegerPolyhedralCones
public import TauCeti.Geometry.Toric.Algebraic.Lattice

/-!
# Integral halfspace cones in an arbitrary integral lattice

The finite-generation theorem is transported through an actual integral
basis and its scalar-extension basis. The integral generators remain
vectors of the original lattice; no rationality hypothesis is assumed
for the cone being constructed.
-/

@[expose] public noncomputable section
open TauCeti.Toric Set
open scoped BigOperators

namespace ToricPower.FanSubdivision

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} [Fintype ι] [DecidableEq ι]

theorem integral_inequalityCone_isLatticeRational (lattice : IsIntegralLattice i)
    (σ : PointedCone ℝ V) (forms : ι → N →+ ℤ)
    (membership : ∀ x, x ∈ σ ↔ ∀ r, lattice.realCharacter (forms r) x ≤ 0) :
    IsLatticeRational i σ := by
  letI := lattice.free
  letI := lattice.finite
  let basis := Module.finBasis ℤ N
  let realBasis := lattice.isBaseChange.basis basis
  let integralEquiv := basis.equivFun.symm
  let realEquiv := realBasis.equivFun.symm
  have baseValue (j : Fin (Module.finrank ℤ N)) : realBasis j = i (basis j) := by
    exact lattice.isBaseChange.basis_apply basis j
  have compatibility (z : Fin (Module.finrank ℤ N) → ℤ) :
      realEquiv (integerCoordinateMap _ z) = i (integralEquiv z) := by
    change realBasis.equivFun.symm (fun j => (z j : ℝ)) = i (basis.equivFun.symm z)
    rw [Module.Basis.equivFun_symm_apply,Module.Basis.equivFun_symm_apply,map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [baseValue,map_zsmul,Int.cast_smul_eq_zsmul]
  let C : Matrix ι (Fin (Module.finrank ℤ N)) ℤ := fun r j => forms r (basis j)
  have formValue (r : ι) (x : Fin (Module.finrank ℤ N) → ℝ) :
      matrixRows (C.map (Int.castRingHom ℝ)) r x =
        lattice.realCharacter (forms r) (realEquiv x) := by
    change _ = lattice.realCharacter (forms r) (realBasis.equivFun.symm x)
    rw [Module.Basis.equivFun_symm_apply,map_sum]
    simp only [map_smul,smul_eq_mul,baseValue,lattice.realCharacter_apply,
      matrixRows_apply,Matrix.mulVec,dotProduct,Matrix.map_apply,C]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  let coordinateCone := PointedCone.comap realEquiv.toLinearMap σ
  have coordinateRational : IsLatticeRational (integerCoordinateMap (Module.finrank ℤ N))
      coordinateCone := by
    apply integer_inequalityCone_isLatticeRational coordinateCone C
    intro x
    change realEquiv x ∈ σ ↔ _
    rw [membership]
    simp only [formValue]
  have mapped := coordinateRational.map
    (f := integralEquiv.toAddMonoidHom) (g := realEquiv.toLinearMap) compatibility
  have equality : PointedCone.map realEquiv.toLinearMap coordinateCone = σ := by
    ext x
    constructor
    · rintro ⟨y,member,rfl⟩
      exact member
    · intro member
      refine ⟨realEquiv.symm x,?_,realEquiv.apply_symm_apply x⟩
      change realEquiv (realEquiv.symm x) ∈ σ
      rwa [realEquiv.apply_symm_apply]
  rwa [equality] at mapped

end ToricPower.FanSubdivision
end
