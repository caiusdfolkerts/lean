module

public import ToricPower.RegularConeIntegralSlice
public import TauCeti.Geometry.Convex.Cone.Face.Simplicial

/-! # Active ray subfamilies and integral affine slices

A subset of the primitive rays of a regular cone spans a genuine face.
Integral values only on those rays already extend to a full integral
character. No values are required on the inactive rays.
-/

@[expose] public noncomputable section

open Set TauCeti.Toric

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}
  (lattice : IsIntegralLattice i) (regular : IsRegularCone i σ)
  (T : Set (ToricRay σ))

def regularRaySubcone : PointedCone ℝ V :=
  PointedCone.hull ℝ
    ((fun ρ : ToricRay σ => i (primitiveGenerator lattice regular.toIsToricCone ρ)) '' T)

theorem regularRaySubcone_isFaceOf : (regularRaySubcone lattice regular T).IsFaceOf σ := by
  apply PointedCone.isFaceOf_hull_image
    (regular.linearIndependent_primitiveGenerator lattice)
  have ranges : (Set.range fun ρ : ToricRay σ =>
      i (primitiveGenerator lattice regular.toIsToricCone ρ)) =
      i '' Set.range (primitiveGenerator lattice regular.toIsToricCone) :=
    Set.range_comp _ _
  rw [ranges]
  exact (regular.toIsToricCone.hull_primitiveGenerator lattice).symm

theorem regularRaySubcone_le_submodule (W : Submodule ℝ V)
    (contained : ∀ ρ ∈ T, i (primitiveGenerator lattice regular.toIsToricCone ρ) ∈ W) :
    regularRaySubcone lattice regular T ≤ (W : PointedCone ℝ V) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨ρ,hρ,rfl⟩
  exact contained ρ hρ

/-- Integral data on precisely the chosen primitive rays extends to an
ambient lattice character and agrees on the whole real span of their cone. -/
theorem regularRaySubcone_realCharacter_agrees
    (x : Module.Dual ℝ V)
    (integral : ∀ ρ ∈ T,
      ∃ z : ℤ, x (i (primitiveGenerator lattice regular.toIsToricCone ρ)) = (z : ℝ)) :
    ∃ m : N →+ ℤ, ∀ v ∈ Submodule.span ℝ (regularRaySubcone lattice regular T : Set V),
      lattice.realCharacter m v = x v := by
  classical
  let z : ToricRay σ → ℤ := fun ρ =>
    if h : ρ ∈ T then Classical.choose (integral ρ h) else 0
  obtain ⟨l,basis,hbasis⟩ := regular.exists_basis_sum
  let m : N →+ ℤ :=
    (basis.constr ℤ (Sum.elim z (fun _ : Fin l => 0))).toAddMonoidHom
  have values (ρ : ToricRay σ) :
      m (primitiveGenerator lattice regular.toIsToricCone ρ) = z ρ := by
    rw [← (hbasis ρ).eq_primitiveGenerator lattice regular.toIsToricCone]
    simp [m]
  have generators :
      ((fun ρ : ToricRay σ => i (primitiveGenerator lattice regular.toIsToricCone ρ)) '' T) ⊆
        (LinearMap.ker (lattice.realCharacter m-x) : Set V) := by
    rintro _ ⟨ρ,hρ,rfl⟩
    change lattice.realCharacter m (i (primitiveGenerator lattice regular.toIsToricCone ρ)) -
      x (i (primitiveGenerator lattice regular.toIsToricCone ρ)) = 0
    rw [lattice.realCharacter_apply,values]
    have same : x (i (primitiveGenerator lattice regular.toIsToricCone ρ)) = (z ρ : ℝ) := by
      simpa only [z,dif_pos hρ] using Classical.choose_spec (integral ρ hρ)
    rw [same,sub_self]
  have cone : regularRaySubcone lattice regular T ≤
      PointedCone.ofSubmodule (LinearMap.ker (lattice.realCharacter m-x)) :=
    Submodule.span_le.mpr generators
  have span : Submodule.span ℝ (regularRaySubcone lattice regular T : Set V) ≤
      LinearMap.ker (lattice.realCharacter m-x) := Submodule.span_le.mpr cone
  exact ⟨m,fun v hv => sub_eq_zero.mp (span hv)⟩

/-- The entire affine annihilator slice is an integral translate when
the active subfamily spans its normal space. -/
theorem regularRaySubcone_integralAffineSlice
    (W : Submodule ℝ V)
    (spans : Submodule.span ℝ (regularRaySubcone lattice regular T : Set V) = W)
    (x : Module.Dual ℝ V)
    (integral : ∀ ρ ∈ T,
      ∃ z : ℤ, x (i (primitiveGenerator lattice regular.toIsToricCone ρ)) = (z : ℝ)) :
    ∃ m : N →+ ℤ, ∀ y : Module.Dual ℝ V,
      y-x ∈ W.dualAnnihilator ↔ y-lattice.realCharacter m ∈ W.dualAnnihilator := by
  obtain ⟨m,agrees⟩ := regularRaySubcone_realCharacter_agrees lattice regular T x integral
  have shift : lattice.realCharacter m-x ∈ W.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    change lattice.realCharacter m v-x v = 0
    exact sub_eq_zero.mpr (agrees v (spans.symm ▸ hv))
  refine ⟨m,fun y => ⟨?_,?_⟩⟩
  · intro h
    convert W.dualAnnihilator.sub_mem h shift using 1 <;> abel
  · intro h
    convert W.dualAnnihilator.add_mem h shift using 1 <;> abel

end ToricPower

end
