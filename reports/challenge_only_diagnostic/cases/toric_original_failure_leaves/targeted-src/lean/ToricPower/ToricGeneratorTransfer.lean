module

public import ToricPower.GeometricCore
public import ToricPower.CoherentFoundations
public import ToricPower.DivisorWeightStructureRetract
public import ToricPower.ToricCoherentPower

/-!
# Actual finite-power transfer of a toric coherent generator

The geometric inputs here are the actual toric scheme, its Noetherian
property, finiteness of the positive power map, and the actual global
structure-sheaf retract constructed from the residue splitting. The
categorical conclusion is classical generation in the literal bounded
derived category of coherent sheaves.

An existing generator and its genuine finite invertible decomposition are
explicit inputs. This theorem is the power-multiple step in the paper;
it does not assert the existence of the initial generator.
-/

@[expose] public noncomputable section

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.Toric

namespace ToricPower

universe u v w

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

local instance toricTransferLocallyNoetherian (fan : Fan i) :
    IsLocallyNoetherian fan.algebraicRealization := by
  letI := toricScheme_isNoetherian fan
  infer_instance

/-- A positive toric power sends a coherent generator that has a genuine
finite decomposition into invertible sheaves to another coherent generator.
The conclusion uses the actual bounded derived category and actual direct
image, with no completeness, projectivity, or extra flatness hypothesis. -/
theorem toricPowerPushforward_generates_of_invertibleSplitting
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (ell : ℕ) (hell : 0 < ell)
    {I : Type w} [Finite I] [Nonempty I]
    (L : I → TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization)
    (M : Coh fan.algebraicRealization)
    (eM : M ≅ ⨁ (fun j => coherentInvertible (L j)))
    (hM : generatesDbCoh (X := fan.algebraicRealization) (coherentSingle fan.algebraicRealization M)) :
    generatesDbCoh (X := fan.algebraicRealization) (coherentSingle fan.algebraicRealization
      ((toricCoherentPowerPushforward fan regular ell hell).obj M)) := by
  letI := toricPowerMap_finite fan regular ell hell
  exact coherentPushforward_generates_of_invertibleSplitting
    (X := fan.algebraicRealization)
    (toricPowerMap fan ell)
    (toricPowerGlobalStructureRetract fan nonempty regular ell hell) L M eM hM

/-- Actual coherent power pushforwards compose according to multiplication
of the positive degrees. The isomorphism is induced by the ordinary
scheme-module pushforward comparison and the actual power-map equality. -/
def toricCoherentPowerPushforwardCompIso
    (fan : Fan i) (regular : fan.IsRegular)
    (ell k : ℕ) (hell : 0 < ell) (hk : 0 < k)
    (M : Coh fan.algebraicRealization) :
    (toricCoherentPowerPushforward fan regular k hk).obj
        ((toricCoherentPowerPushforward fan regular ell hell).obj M) ≅
      (toricCoherentPowerPushforward fan regular (ell * k) (Nat.mul_pos hell hk)).obj M :=
  (SheafOfModules.isFinitePresentation fan.algebraicRealization.ringCatSheaf).fullyFaithfulι.preimageIso
      ((Scheme.Modules.pushforwardComp (toricPowerMap fan ell)
          (toricPowerMap fan k)).app M.obj ≪≫
        eqToIso (congrArg (fun f => (Scheme.Modules.pushforward f).obj M.obj)
          (toricPowerMap_comp fan ell k)))

/-- Once one positive power pushforward is a generator and has an actual
finite invertible splitting, every positive multiple is a generator.
This is the geometric categorical implication in Proposition 6.2. -/
theorem toricPowerPushforward_multiples_generate_of_invertibleSplitting
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (ell k : ℕ) (hell : 0 < ell) (hk : 0 < k)
    {I : Type w} [Finite I] [Nonempty I]
    (L : I → TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization)
    (M : Coh fan.algebraicRealization)
    (eM : (toricCoherentPowerPushforward fan regular ell hell).obj M ≅
      ⨁ (fun j => coherentInvertible (L j)))
    (hM : generatesDbCoh (X := fan.algebraicRealization) (coherentSingle fan.algebraicRealization
      ((toricCoherentPowerPushforward fan regular ell hell).obj M))) :
    generatesDbCoh (X := fan.algebraicRealization) (coherentSingle fan.algebraicRealization
      ((toricCoherentPowerPushforward fan regular (ell * k) (Nat.mul_pos hell hk)).obj M)) := by
  have h := toricPowerPushforward_generates_of_invertibleSplitting
    fan nonempty regular k hk L
      ((toricCoherentPowerPushforward fan regular ell hell).obj M) eM hM
  exact (coherentSingle_generates_iff_of_iso (X := fan.algebraicRealization)
    (toricCoherentPowerPushforwardCompIso fan regular ell k hell hk M)).mp h

end ToricPower

end
