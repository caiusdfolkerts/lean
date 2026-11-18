module

public import ToricPower.IntegralHyperplaneFan
public import TauCeti.Geometry.Toric.Algebraic.Regular
public import TauCeti.Geometry.Toric.Algebraic.Ray.Generation
public import TauCeti.Geometry.Convex.Cone.Face.Simplicial

/-!
# Finite integral inequalities for a regular cone

An extending integral basis gives a literal finite halfspace description:
active coordinates are nonnegative and the complementary coordinates vanish.
The same integral forms separate the ambient real vector space. This supplies
the defining hyperplanes used to adapt the exterior completion to the given fan.
-/

@[expose] public noncomputable section
open TauCeti.Toric Set

namespace ToricPower.FanSubdivision

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem mem_basisCone_iff {κ : Type*} (basis : Module.Basis κ ℝ V)
    (active : Set κ) (x : V) :
    x ∈ PointedCone.hull ℝ (basis '' active) ↔
      (∀ k, 0 ≤ basis.repr x k) ∧ (∀ k ∉ active, basis.repr x k = 0) := by
  classical
  rw [PointedCone.mem_hull_image_iff_linearCombination]
  constructor
  · rintro ⟨c,supported,positive,value⟩
    have same : c = basis.repr x := by
      simpa only [basis.repr_linearCombination] using congrArg basis.repr value
    subst c
    refine ⟨positive,?_⟩
    intro k outside
    apply Finsupp.notMem_support_iff.mp
    intro member
    exact outside ((Finsupp.mem_supported _ _).mp supported member)
  · rintro ⟨positive,zero⟩
    refine ⟨basis.repr x,?_,positive,basis.linearCombination_repr x⟩
    apply (Finsupp.mem_supported _ _).mpr
    intro k member
    by_contra outside
    exact (Finsupp.mem_support_iff.mp member) (zero k outside)

variable {N : Type*} [AddCommGroup N] {i : N →+ V}

theorem integralBasis_real_coord {κ : Type*} (lattice : IsIntegralLattice i)
    (basis : Module.Basis κ ℤ N) (k : κ) :
    (lattice.isBaseChange.basis basis).coord k =
      lattice.realCharacter (basis.coord k).toAddMonoidHom := by
  classical
  let realBasis := lattice.isBaseChange.basis basis
  apply realBasis.ext
  intro j
  calc
    realBasis.coord k (realBasis j) = ((basis.coord k (basis j) : ℤ) : ℝ) := by
      simp only [Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply]
      split_ifs <;> norm_num
    _ = lattice.realCharacter (basis.coord k).toAddMonoidHom (realBasis j) := by
      rw [lattice.isBaseChange.basis_apply]
      exact (lattice.realCharacter_apply (basis.coord k).toAddMonoidHom (basis j)).symm

/-- A regular cone has a separating integral halfspace description, with
exactly twice the lattice rank as a fixed finite indexing type. -/
theorem regularCone_exists_integral_inequalities (lattice : IsIntegralLattice i)
    {σ : PointedCone ℝ V} (regular : IsRegularCone i σ) :
    ∃ forms : (Fin (Module.finrank ℤ N) × Bool) → N →+ ℤ,
      (∀ x, x ∈ σ ↔ ∀ p, lattice.realCharacter (forms p) x ≤ 0) ∧
      (∀ x, (∀ p, lattice.realCharacter (forms p) x = 0) → x = 0) := by
  classical
  obtain ⟨basis,rayIndex,basisExtends⟩ := regular.exists_basis_finrank
  let realBasis := lattice.isBaseChange.basis basis
  let active : Set (Fin (Module.finrank ℤ N)) := Set.range rayIndex
  have primitive (ρ : ToricRay σ) :
      basis (rayIndex ρ) = primitiveGenerator lattice regular.toIsToricCone ρ :=
    (basisExtends.isPrimitiveGenerator_apply ρ).eq_primitiveGenerator lattice regular.toIsToricCone
  have generators : realBasis '' active =
      i '' Set.range (primitiveGenerator lattice regular.toIsToricCone) := by
    ext x
    constructor
    · rintro ⟨_,⟨ρ,rfl⟩,rfl⟩
      refine ⟨primitiveGenerator lattice regular.toIsToricCone ρ,⟨ρ,rfl⟩,?_⟩
      rw [← primitive,lattice.isBaseChange.basis_apply]
      rfl
    · rintro ⟨_,⟨ρ,rfl⟩,rfl⟩
      refine ⟨rayIndex ρ,⟨ρ,rfl⟩,?_⟩
      rw [lattice.isBaseChange.basis_apply,primitive]
      rfl
  have cone : PointedCone.hull ℝ (realBasis '' active) = σ := by
    rw [generators]
    exact regular.toIsToricCone.hull_primitiveGenerator lattice
  let forms : (Fin (Module.finrank ℤ N) × Bool) → N →+ ℤ := fun p =>
    if p.2 then (if p.1 ∈ active then 0 else (basis.coord p.1).toAddMonoidHom)
    else -(basis.coord p.1).toAddMonoidHom
  have negativeValue (k : Fin (Module.finrank ℤ N)) (x : V) :
      lattice.realCharacter (forms (k,false)) x = -(realBasis.repr x k) := by
    simp only [forms,Bool.false_eq_true,if_false,map_neg,LinearMap.neg_apply]
    rw [← integralBasis_real_coord]
    rfl
  have positiveValue (k : Fin (Module.finrank ℤ N)) (outside : k ∉ active) (x : V) :
      lattice.realCharacter (forms (k,true)) x = realBasis.repr x k := by
    simp only [forms,if_true,if_neg outside]
    rw [← integralBasis_real_coord]
    rfl
  refine ⟨forms,?_,?_⟩
  · intro x
    rw [← cone,mem_basisCone_iff]
    constructor
    · rintro ⟨positive,zero⟩ ⟨k,b⟩
      cases b
      · rw [negativeValue]
        exact neg_nonpos.mpr (positive k)
      · by_cases member : k ∈ active
        · simp [forms,member]
        · rw [positiveValue k member,zero k member]
    · intro inequalities
      refine ⟨?_,?_⟩
      · intro k
        apply neg_nonpos.mp
        simpa only [negativeValue] using inequalities (k,false)
      · intro k outside
        have lower := inequalities (k,false)
        have upper := inequalities (k,true)
        rw [negativeValue] at lower
        rw [positiveValue k outside] at upper
        linarith
  · intro x zero
    apply realBasis.repr.injective
    ext k
    have value := zero (k,false)
    rw [negativeValue] at value
    simpa only [map_zero,Finsupp.zero_apply,neg_eq_zero] using value

end ToricPower.FanSubdivision
end
