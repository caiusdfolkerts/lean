module

public import ToricPower.ToricEffectiveGeneration
public import ToricPower.DivisorWeightClassification

/-!
# The effective criterion for every actual line bundle and Cartier divisor

The invariant representative used below is constructed from actual local
rational frames. Its comparison with the original line bundle is an
isomorphism of module sheaves. Consequently the effective generator
criterion applies to every line bundle, and in particular every Cartier
divisor, without assuming an invariant presentation as an extra hypothesis.

The final endpoint chooses finite coordinates from the lattice and fan,
so no coordinate-existence hypothesis remains. Its explicit mathematical
exponent is still `R * max K_b C_b` for the constructed invariant
representative. This representative uses classical choices of actual
frames; no algorithm extracting it from an abstract line bundle is claimed.

Development source: compilation of this complete dependency chain is
required before any theorem is reported as verified.
-/

@[expose] public noncomputable section

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

local instance effectiveLineBundleLocallyNoetherian (fan : Fan i) :
    IsLocallyNoetherian fan.algebraicRealization := by
  letI := toricScheme_isNoetherian fan
  infer_instance

/-- The actual positive direct image of a line bundle, placed in degree
zero in the literal bounded derived category of coherent sheaves, is a
classical generator. -/
def toricLineBundlePowerGenerates (fan : Fan i) (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization)
    (ell : ℕ) (hell : 0 < ell) : Prop :=
  generatesDbCoh (X := fan.algebraicRealization) (coherentSingle fan.algebraicRealization
    ((toricCoherentPowerPushforward fan regular ell hell).obj (coherentInvertible L)))

/-- The explicit actual sheaf isomorphism to an invariant representative
lifts to the coherent category. -/
def toricCoherentLineBundleInvariantIso (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization) :
    coherentInvertible L ≅ toricCoherentInvariantDivisor fan nonempty regular
      (toricLineBundleInvariantCoefficients fan nonempty regular L.obj) := by
  letI := toricSchemeIntegral fan nonempty
  exact coherentIsoOfUnderlying (toricLineBundleInvariantIso fan nonempty regular L.obj)

theorem toricLineBundlePowerGenerates_iff_invariant (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization)
    (ell : ℕ) (hell : 0 < ell) :
    toricLineBundlePowerGenerates fan regular L ell hell ↔
      toricInvariantPowerGenerates fan nonempty regular
        (toricLineBundleInvariantCoefficients fan nonempty regular L.obj) ell hell :=
  coherentSingle_generates_iff_of_iso
    ((toricCoherentPowerPushforward fan regular ell hell).mapIso
      (toricCoherentLineBundleInvariantIso fan nonempty regular L))

section ExplicitCoordinates

variable {κ : Type u} [Fintype κ] {s n : ℕ}

/-- **Proposition 6.2 for every actual line bundle**, with the exact ray
matrix and invariant representative exposed in the exponent. -/
theorem paper_proposition_6_2_generates_lineBundle_of_coordinates
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization) :
    toricLineBundlePowerGenerates fan regular L
      (stableMultipleExponent
        (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))
        (toricLineBundleInvariantCoefficients fan nonempty regular L.obj ∘ rays))
      (stableMultipleExponent_pos _ _) ↔
    ∃ ell : ℕ, ∃ hell : 0 < ell, toricLineBundlePowerGenerates fan regular L ell hell := by
  rw [toricLineBundlePowerGenerates_iff_invariant fan nonempty regular L]
  rw [paper_proposition_6_2_generates_invariant fan nonempty regular rays basis coordinates]
  exact exists_congr fun ell => exists_congr fun hell =>
    (toricLineBundlePowerGenerates_iff_invariant fan nonempty regular L ell hell).symm

end ExplicitCoordinates

/-- A finite ray enumeration is supplied by finiteness of the actual fan. -/
def toricEffectiveRayEnumeration (fan : Fan i) : Fin (Nat.card fan.Ray) ≃ fan.Ray := by
  letI : Fintype fan.Ray := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using (Fintype.equivFin fan.Ray).symm

/-- The actual character lattice has a finite basis. The lift preserves
arbitrary ambient universes while allowing the full geometric residue
family, whose index lives in the lattice universe. -/
def toricEffectiveCharacterBasis (fan : Fan i) :
    Module.Basis (ULift.{u, 0} (Fin (Module.finrank ℤ N))) ℤ (N →+ ℤ) :=
  (latticeCharacterBasis fan.lattice).reindex (Equiv.ulift.{u, 0}).symm

/-- The actual invertible residue summands of an arbitrary line bundle,
using its constructed invariant representative and the full character lattice. -/
def toricLineBundleResidueFamily (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization) (ell : ℕ) :=
  toricInvertibleResidueFamily fan nonempty regular (toricEffectiveCharacterBasis fan)
    (toricLineBundleInvariantCoefficients fan nonempty regular L.obj) ell

/-- The constructed residue family really splits the finite direct image of
the original line bundle in the coherent category. -/
def toricCoherentLineBundleSplitting (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization)
    (ell : ℕ) (hell : 0 < ell) :
    (toricCoherentPowerPushforward fan regular ell hell).obj (coherentInvertible L) ≅
      ⨁ (fun residue => coherentInvertible
        (toricLineBundleResidueFamily fan nonempty regular L ell residue)) :=
  (toricCoherentPowerPushforward fan regular ell hell).mapIso
      (toricCoherentLineBundleInvariantIso fan nonempty regular L) ≪≫
    toricCoherentInvariantSplitting fan nonempty regular (toricEffectiveCharacterBasis fan)
      (toricLineBundleInvariantCoefficients fan nonempty regular L.obj) ell hell

/-- Isomorphism classes of the genuine coherent residue summands of the
original line-bundle direct image, with multiplicities forgotten. -/
def toricLineBundleResidueClasses (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization) (ell : ℕ) :
    ObjectProperty (Coh fan.algebraicRealization) :=
  toricCoherentResidueClasses fan nonempty regular (toricEffectiveCharacterBasis fan)
    (toricLineBundleInvariantCoefficients fan nonempty regular L.obj) ell

/-- The exact mathematical stable exponent from Proposition 6.2, with all
finite coordinate choices supplied by the actual fan and character lattice.
The invariant representative uses chosen rational frames, so this is not
an executable extraction algorithm on abstract line bundles. -/
def toricLineBundleStableExponent (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization) : ℕ :=
  stableMultipleExponent
    (enumeratedFanRayMatrix fan (toricEffectiveRayEnumeration fan)
      ((toricEffectiveCharacterBasis fan).reindex (Equiv.ulift.{u, 0})))
    (toricLineBundleInvariantCoefficients fan nonempty regular L.obj ∘
      toricEffectiveRayEnumeration fan)

theorem toricLineBundleStableExponent_pos (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization) :
    0 < toricLineBundleStableExponent fan nonempty regular L :=
  stableMultipleExponent_pos _ _

/-- **Proposition 6.2, full line-bundle endpoint.** The actual direct image
at the explicit positive exponent generates exactly when some positive
power direct image generates. No basis, enumeration, invariant-presentation,
initial-generator, completeness, or projectivity hypothesis is added. -/
theorem paper_proposition_6_2_generates_lineBundle
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf fan.algebraicRealization) :
    toricLineBundlePowerGenerates fan regular L
      (toricLineBundleStableExponent fan nonempty regular L)
      (toricLineBundleStableExponent_pos fan nonempty regular L) ↔
    ∃ ell : ℕ, ∃ hell : 0 < ell, toricLineBundlePowerGenerates fan regular L ell hell := by
  exact paper_proposition_6_2_generates_lineBundle_of_coordinates fan nonempty regular
    (toricEffectiveRayEnumeration fan) (toricEffectiveCharacterBasis fan)
    (Equiv.ulift.{u, 0}).symm L

/-- The paper's Cartier-divisor formulation, for every actual Cartier
divisor. Its sheaf is proved invertible by the actual Cartier theory. -/
theorem paper_proposition_6_2_generates_cartier
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (D : letI := toricSchemeIntegral fan nonempty
      TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization) :
    letI := toricSchemeIntegral fan nonempty
    toricLineBundlePowerGenerates fan regular D.toInvertibleSheaf
      (toricLineBundleStableExponent fan nonempty regular D.toInvertibleSheaf)
      (toricLineBundleStableExponent_pos fan nonempty regular D.toInvertibleSheaf) ↔
    ∃ ell : ℕ, ∃ hell : 0 < ell,
      toricLineBundlePowerGenerates fan regular D.toInvertibleSheaf ell hell := by
  letI := toricSchemeIntegral fan nonempty
  exact paper_proposition_6_2_generates_lineBundle fan nonempty regular D.toInvertibleSheaf

end ToricPower

end
