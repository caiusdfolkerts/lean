module

public import ToricPower.DivisorWeightMonomialFrames

/-!
# An actual monomial incidence with zero chart valuations is invertible

Both the normalized character and its negative belong to the affine
semigroup. The original morphism in the original Cartier frames is
therefore multiplication by an actual global unit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric MonoidAlgebra

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

theorem toricCartierMonomialMap_restrict_isIso (fan : Fan i) (regular : fan.IsRegular)
    (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ : fan.Ray,
      0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (cone : fan.cones)
    (equal : ∀ ρ : fan.Ray, ρ.toCone ≤ cone →
      c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ) = 0)
    (nonempty : Nonempty fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    IsIso ((Scheme.Modules.restrictFunctor (fan.affineToricChartι cone)).map
      (toricCartierMonomialMap fan nonempty regular b c character nonnegative)) := by
  letI := toricSchemeIntegral fan nonempty
  let m := normalizedToricMonomialCharacter fan regular b c character cone
  have vanish : ∀ ρ : ToricRay cone.val,
      m (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ) = 0 := by
    intro ρ
    have h := equal (Fan.Ray.ofToricRay fan cone ρ) (Fan.Ray.toCone_ofToricRay_le fan cone ρ)
    rw [fanRayPrimitiveGenerator_ofToricRay] at h
    simpa only [m, normalizedToricMonomialCharacter, AddMonoidHom.sub_apply,
      AddMonoidHom.add_apply, AddMonoidHom.neg_apply, coneDivisorCharacter_ray, coneDivisorCoefficients,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have negative : -m ∈ dualSemigroup fan.lattice cone.val := by
    rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice (fan.isToricCone cone.property)]
    intro ρ
    rw [AddMonoidHom.neg_apply, vanish ρ]
    simp
  let positiveCharacter : dualSemigroup fan.lattice cone.val :=
    ⟨m, normalizedToricMonomialCharacter_mem fan regular b c character nonnegative cone⟩
  let negativeCharacter : dualSemigroup fan.lattice cone.val := ⟨-m, negative⟩
  have sum : positiveCharacter + negativeCharacter = 0 := by
    apply Subtype.ext
    exact add_neg_cancel m
  have product : Multiplicative.ofAdd positiveCharacter * Multiplicative.ofAdd negativeCharacter = 1 :=
    congrArg Multiplicative.ofAdd sum
  have unit : IsUnit (normalizedToricMonomial fan regular b c character nonnegative cone) := by
    refine ⟨⟨_, single (Multiplicative.ofAdd negativeCharacter) 1, ?_, ?_⟩, rfl⟩
    · change single (Multiplicative.ofAdd positiveCharacter) (1 : ℂ) *
        single (Multiplicative.ofAdd negativeCharacter) 1 = 1
      rw [single_mul_single, product, one_mul]
      rfl
    · change single (Multiplicative.ofAdd negativeCharacter) (1 : ℂ) *
        single (Multiplicative.ofAdd positiveCharacter) 1 = 1
      rw [single_mul_single, mul_comm, product, one_mul]
      rfl
  obtain ⟨u, hu⟩ := unit.map (affineGlobalSectionsEquiv
    (affineCoordinateRing fan.lattice cone.val)).toMonoidHom
  haveI scalarIso : IsIso (Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (fan.affineToricChart cone).ringCatSheaf)
      (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)
        (normalizedToricMonomial fan regular b c character nonnegative cone))) := by
    change (u : Γ(Spec (.of (affineCoordinateRing fan.lattice cone.val)), ⊤)) =
      affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)
        (normalizedToricMonomial fan regular b c character nonnegative cone) at hu
    erw [← hu]
    infer_instance
  haveI frameIso : IsIso ((toricCartierAffineFrame fan nonempty regular b cone).hom ≫
      (Scheme.Modules.restrictFunctor (fan.affineToricChartι cone)).map
        (toricCartierMonomialMap fan nonempty regular b c character nonnegative)) := by
    rw [toricCartierMonomialMap_affine_frame]
    infer_instance
  exact IsIso.of_isIso_comp_left (toricCartierAffineFrame fan nonempty regular b cone).hom _

end ToricPower

end
