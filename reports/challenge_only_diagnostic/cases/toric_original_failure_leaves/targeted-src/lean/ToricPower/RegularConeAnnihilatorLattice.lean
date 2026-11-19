module

public import ToricPower.RegularConeIntegralSlice
public import ToricPower.IntegralDualLattice
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The integral lattice spans the annihilator of a regular cone

The primitive rays extend to an integral basis. The dual coordinates
of the complementary basis vectors are integral characters annihilating
the cone, and they span its entire real annihilator. This supplies the
lattice approximation hypothesis used in the shrinking argument.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Module TauCeti.Toric
open scoped BigOperators

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- Vanishing on the actual primitive rays is exactly vanishing on
the entire real span of the cone. -/
theorem mem_coneSpan_annihilator_iff (lattice : IsIntegralLattice i)
    (toric : IsToricCone i σ) (x : Module.Dual ℝ V) :
    x ∈ (Submodule.span ℝ (σ : Set V)).dualAnnihilator ↔
      ∀ ρ : ToricRay σ, x (i (primitiveGenerator lattice toric ρ)) = 0 := by
  constructor
  · intro hx ρ
    exact ((Submodule.mem_dualAnnihilator x).mp hx) _
      (Submodule.subset_span
        (ρ.val.isFaceOf.le (primitiveGenerator_mem lattice toric ρ)))
  · intro rays
    have generators : i '' Set.range (primitiveGenerator lattice toric) ⊆
        (LinearMap.ker x : Set V) := by
      rintro _ ⟨_,⟨ρ,rfl⟩,rfl⟩
      exact rays ρ
    have cone : σ ≤ PointedCone.ofSubmodule (LinearMap.ker x) := by
      rw [← toric.hull_primitiveGenerator lattice]
      exact Submodule.span_le.mpr generators
    have span : Submodule.span ℝ (σ : Set V) ≤ LinearMap.ker x :=
      Submodule.span_le.mpr cone
    exact (Submodule.mem_dualAnnihilator x).mpr (fun v hv => span hv)

/-- Every real vector in the annihilator is in the real span of the
actual integral characters that belong to that annihilator. -/
theorem regularCone_annihilator_integral_span
    (lattice : IsIntegralLattice i) (regular : IsRegularCone i σ) :
    Submodule.span ℝ
      ((Set.range lattice.realCharacter) ∩
        ((Submodule.span ℝ (σ : Set V)).dualAnnihilator : Set (Module.Dual ℝ V))) =
      (Submodule.span ℝ (σ : Set V)).dualAnnihilator := by
  classical
  letI := lattice.finite
  obtain ⟨l,basis,primitive⟩ := regular.exists_basis_sum
  letI : Finite (ToricRay σ ⊕ Fin l) := Module.Finite.finite_basis basis
  letI : Fintype (ToricRay σ ⊕ Fin l) := Fintype.ofFinite _
  let B := lattice.isBaseChange.basis basis
  have extended (a : ToricRay σ ⊕ Fin l) : B a = i (basis a) :=
    lattice.isBaseChange.basis_apply basis a
  have coordinate (a : ToricRay σ ⊕ Fin l) :
      B.coord a = lattice.realCharacter (basis.coord a).toAddMonoidHom := by
    apply B.ext
    intro b
    calc
      B.coord a (B b) = ((basis.coord a (basis b) : ℤ) : ℝ) := by
        simp only [Basis.coord_apply,Basis.repr_self,Finsupp.single_apply]
        split_ifs <;> norm_num
      _ = lattice.realCharacter (basis.coord a).toAddMonoidHom (B b) := by
        rw [extended,lattice.realCharacter_apply]
        rfl
  have complementary (a : Fin l) :
      B.coord (Sum.inr a) ∈ (Submodule.span ℝ (σ : Set V)).dualAnnihilator := by
    rw [mem_coneSpan_annihilator_iff lattice regular.toIsToricCone]
    intro ρ
    rw [← (primitive ρ).eq_primitiveGenerator lattice regular.toIsToricCone,
      ← extended]
    simp only [Basis.coord_apply,Basis.repr_self,Finsupp.single_apply,
      Sum.inl_ne_inr,if_false]
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun x hx => hx.2)
  · intro x hx
    rw [← B.sum_dual_apply_smul_coord x]
    apply Submodule.sum_mem
    intro a _
    cases a with
    | inl ρ =>
        have value : x (B (Sum.inl ρ)) = 0 := by
          rw [extended,(primitive ρ).eq_primitiveGenerator lattice regular.toIsToricCone]
          exact (mem_coneSpan_annihilator_iff lattice regular.toIsToricCone x).mp hx ρ
        rw [value,zero_smul]
        exact Submodule.zero_mem _
    | inr a =>
        apply Submodule.smul_mem
        apply Submodule.subset_span
        exact ⟨⟨(basis.coord (Sum.inr a)).toAddMonoidHom,(coordinate _).symm⟩,
          complementary a⟩

end ToricPower

end
