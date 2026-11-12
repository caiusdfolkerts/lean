module

public import ToricPower.BasisQuotientByVector
public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import TauCeti.Algebra.Module.Primitive
public import Mathlib.Data.Fintype.Card

/-!
# The actual quotient lattice by a primitive ray

Both the integral lattice and its real vector space are literal module
quotients. Deleting the primitive vector from an extending integral
basis proves the full scalar-extension property of the quotient map.
The integral rank strictly decreases, supplying the well-founded
dimension parameter in the relative fan-completion construction.
-/

@[expose] public noncomputable section

open TauCeti TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  (i : N →+ V) (ray : N)

abbrev RayQuotientLattice := N ⧸ Submodule.span ℤ {ray}
abbrev RayQuotientSpace := V ⧸ Submodule.span ℝ {i ray}

/-- The real quotient of the original lattice map descends along the
literal integral cyclic submodule. -/
def rayQuotientLatticeMap : RayQuotientLattice ray →+ RayQuotientSpace i ray :=
  (Submodule.liftQSpanSingleton ray
    (((Submodule.span ℝ {i ray}).mkQ.restrictScalars ℤ).comp i.toIntLinearMap)
    (by
      change (Submodule.span ℝ {i ray}).mkQ (i ray) = 0
      exact LinearMap.mem_ker.mp (by
        rw [Submodule.ker_mkQ]
        exact Submodule.mem_span_singleton_self _))).toAddMonoidHom

@[simp]
theorem rayQuotientLatticeMap_apply (n : N) :
    rayQuotientLatticeMap i ray ((Submodule.span ℤ {ray}).mkQ n) =
      (Submodule.span ℝ {i ray}).mkQ (i n) := rfl

/-- The compatible maps used by the actual quotient-star constructor. -/
theorem rayQuotient_maps_compatible (n : N) :
    (Submodule.span ℝ {i ray}).mkQ (i n) =
      rayQuotientLatticeMap i ray ((Submodule.span ℤ {ray}).mkQ.toAddMonoidHom n) := rfl

theorem rayQuotient_real_kernel :
    LinearMap.ker (Submodule.span ℝ {i ray}).mkQ = Submodule.span ℝ {i ray} :=
  Submodule.ker_mkQ _

/-- A primitive quotient is again an integral lattice, in the full
base-change sense used by the toric scheme realization. -/
theorem rayQuotient_isIntegralLattice (lattice : IsIntegralLattice i)
    (primitive : IsPrimitive ray) : IsIntegralLattice (rayQuotientLatticeMap i ray) := by
  classical
  letI := lattice.free
  letI := lattice.finite
  obtain ⟨m,basis,pivot,pivotValue⟩ := primitive.exists_basis
  let realBasis := lattice.isBaseChange.basis basis
  have realValue : realBasis pivot = i ray := by
    change lattice.isBaseChange.basis basis pivot = i ray
    rw [lattice.isBaseChange.basis_apply, pivotValue]
    rfl
  have integralKernel : LinearMap.ker (Submodule.span ℤ {ray}).mkQ =
      Submodule.span ℤ {basis pivot} := by rw [Submodule.ker_mkQ,pivotValue]
  have realKernel : LinearMap.ker (Submodule.span ℝ {i ray}).mkQ =
      Submodule.span ℝ {realBasis pivot} := by rw [Submodule.ker_mkQ,realValue]
  let quotientBasis := projectedBasis basis pivot (Submodule.span ℤ {ray}).mkQ
    integralKernel (Submodule.mkQ_surjective _)
  let quotientRealBasis := projectedBasis realBasis pivot (Submodule.span ℝ {i ray}).mkQ
    realKernel (Submodule.mkQ_surjective _)
  apply isIntegralLattice_of_basis quotientBasis quotientRealBasis
  intro k
  simp only [quotientBasis,quotientRealBasis,projectedBasis_apply,rayQuotientLatticeMap_apply]
  apply congrArg (Submodule.span ℝ {i ray}).mkQ
  exact (lattice.isBaseChange.basis_apply basis k.val).symm

/-- Quotienting a primitive ray strictly lowers the integral rank;
the zero-rank case is excluded by the actual primitive vector. -/
theorem rayQuotient_finrank_lt (lattice : IsIntegralLattice i)
    (primitive : IsPrimitive ray) :
    Module.finrank ℤ (RayQuotientLattice ray) < Module.finrank ℤ N := by
  classical
  letI := lattice.free
  letI := lattice.finite
  obtain ⟨m,basis,pivot,pivotValue⟩ := primitive.exists_basis
  have integralKernel : LinearMap.ker (Submodule.span ℤ {ray}).mkQ =
      Submodule.span ℤ {basis pivot} := by rw [Submodule.ker_mkQ,pivotValue]
  let quotientBasis := projectedBasis basis pivot (Submodule.span ℤ {ray}).mkQ
    integralKernel (Submodule.mkQ_surjective _)
  rw [Module.finrank_eq_card_basis quotientBasis,Module.finrank_eq_card_basis basis]
  exact Fintype.card_subtype_lt (x := pivot) (fun h => h rfl)

end ToricPower.FanSubdivision
end
