module

public import ToricPower.LinearSubspaceSupportCharacter
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersions on the actual affine linear-test charts

The actual nonnegative-character restriction is surjective, so the induced
complex semigroup-algebra map is surjective. Taking spectra gives a closed
immersion from the chart of `σ ∩ W` in the saturated trace lattice to the chart
of `σ` in the original lattice.

This module proves the affine statement. Global closedness of the glued
linear inclusion additionally requires identification of the preimage of
each ambient chart with this restricted chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

universe u

section CoordinateRings

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'}

/-- Surjectivity on the genuine semigroup generators implies surjectivity
of the actual complex coordinate-ring homomorphism. -/
theorem affineCoordinateRingMap_surjective_of_dualSemigroupMap
    (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ)
    (surjective : Function.Surjective (dualSemigroupMap hi hi' f g hfg hστ)) :
    Function.Surjective (affineCoordinateRingMap hi hi' f g hfg hστ) := by
  intro p
  induction p using MonoidAlgebra.induction_on with
  | of m =>
      obtain ⟨a, ha⟩ := surjective m.toAdd
      refine ⟨MonoidAlgebra.single (Multiplicative.ofAdd a) 1, ?_⟩
      rw [affineCoordinateRingMap_single, ha]
      rfl
  | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  | smul c p hp =>
      obtain ⟨a, ha⟩ := hp
      exact ⟨c • a, by rw [map_smul, ha]⟩

end CoordinateRings

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The literal coordinate-ring map of each linear-test chart is surjective,
including characters in torus-factor directions. -/
theorem linearSubspace_affineCoordinateRingMap_surjective
    (fan : Fan i) (W : LinearSubspace fan) (σ : fan.cones) :
    Function.Surjective
      (affineCoordinateRingMap (restrictedFan fan W.space W.rational).lattice fan.lattice
        (latticeTrace i W.space).subtype.toAddMonoidHom W.space.subtype (fun _ => rfl)
        (σ := σ.val.comap W.space.subtype) (τ := σ.val) (fun _ hx => hx)) :=
  affineCoordinateRingMap_surjective_of_dualSemigroupMap
    (restrictedFan fan W.space W.rational).lattice fan.lattice
    (latticeTrace i W.space).subtype.toAddMonoidHom W.space.subtype (fun _ => rfl)
    (fun _ hx => hx) (linearSubspace_dualSemigroupRestriction_surjective fan W σ)

/-- The actual spectrum map from the chart of `σ ∩ W` is a closed immersion
into the chart of `σ`. No closedness hypothesis is supplied. -/
theorem linearSubspace_affineChart_isClosedImmersion
    (fan : Fan i) (W : LinearSubspace fan) (σ : fan.cones) :
    IsClosedImmersion
      (affineToricSchemeMap (restrictedFan fan W.space W.rational).lattice fan.lattice
        (latticeTrace i W.space).subtype.toAddMonoidHom W.space.subtype (fun _ => rfl)
        (σ := σ.val.comap W.space.subtype) (τ := σ.val) (fun _ hx => hx)) := by
  erw [affineToricSchemeMap_def]
  exact IsClosedImmersion.spec_of_surjective _
    (linearSubspace_affineCoordinateRingMap_surjective fan W σ)

end ToricPower

end
