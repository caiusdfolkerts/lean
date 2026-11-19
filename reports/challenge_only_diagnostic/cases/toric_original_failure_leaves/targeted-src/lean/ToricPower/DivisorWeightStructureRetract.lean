module

public import ToricPower.DivisorWeightGlobalSplitting

/-!
# The actual structure sheaf as a global power-map summand

The zero coefficient vector gives the zero Cartier divisor, even though
its independently chosen cone characters need only be regular units.
The zero lattice residue in the full decomposition therefore supplies an
actual global structure-sheaf retract.

Development source: verification requires a successful check of its current
source together with the complete imported proof chain.
-/

@[expose] public noncomputable section

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti.Toric

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Zero ray coefficients give the actual zero Cartier divisor. The proof
uses regular-unit local equations, not a choice-dependent character identity. -/
theorem invariantCartierDivisor_zero (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) :
    letI := toricSchemeIntegral fan nonempty
    invariantCartierDivisor fan nonempty regular (0 : fan.Ray → ℤ) = 0 := by
  letI := toricSchemeIntegral fan nonempty
  let atlas := (invariantDivisorCharacterAtlas fan regular (0 : fan.Ray → ℤ)).cartierEquationAtlas nonempty
  change atlas.cartierDivisor = 0
  apply atlas.existsUnique_cartierDivisor.unique
  · exact atlas.cartierDivisor_restrict
  · intro cone
    letI := chartOpen_nonempty fan cone
    let q := coneDivisorCharacter fan regular (0 : fan.Ray → ℤ) cone
    have positive : q ∈ dualSemigroup fan.lattice cone.val := by
      rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice
        (fan.isToricCone cone.property)]
      intro ρ
      simp only [q, coneDivisorCharacter_ray, coneDivisorCoefficients,
        Pi.zero_apply, le_refl]
    have negative : -q ∈ dualSemigroup fan.lattice cone.val := by
      rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice
        (fan.isToricCone cone.property)]
      intro ρ
      simp only [AddMonoidHom.neg_apply, q, coneDivisorCharacter_ray,
        coneDivisorCoefficients, Pi.zero_apply, neg_zero, le_refl]
    let unit := Units.map (chartCoordinateSectionsEquiv fan cone).toMonoidHom
      (toricMonomialUnit fan.lattice cone.val q positive negative)
    have unit_germ : Units.map
        (fan.algebraicRealization.germToFunctionField (fan.affineToricChartι cone).opensRange).hom unit =
      rationalCharacterUnit fan nonempty q :=
        (chartCoordinateGerm_regularUnit fan nonempty cone
          (toricMonomialUnit fan.lattice cone.val q positive negative)).trans
            (chartCoordinateGerm_monomialUnit fan nonempty cone q positive negative)
    have zero_class := TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_germToFunctionField_eq_zero
      fan.algebraicRealization (fan.affineToricChartι cone).opensRange unit
    rw [unit_germ] at zero_class
    change (0 : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization) |_
      (fan.affineToricChartι cone).opensRange =
        TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization
          (fan.affineToricChartι cone).opensRange (Additive.ofMul (rationalCharacterUnit fan nonempty q))
    simpa only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_zero] using zero_class.symm

/-- The actual zero-coefficient divisor sheaf is the structure sheaf. -/
def invariantCartierZeroSheafIso (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) :
    letI := toricSchemeIntegral fan nonempty
    SheafOfModules.unit fan.algebraicRealization.ringCatSheaf ≅
      (invariantCartierDivisor fan nonempty regular (0 : fan.Ray → ℤ)).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitIsoSheafPrincipalCartierDivisor
      fan.algebraicRealization 1 ≪≫
    eqToIso (congrArg TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheaf
      ((TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor_one fan.algebraicRealization).trans
        (invariantCartierDivisor_zero fan nonempty regular).symm))

variable {κ : Type u} [Fintype κ]

/-- The zero residue is defined for every positive degree. -/
def zeroLatticeResidue (ell : ℕ) (hell : 0 < ell) : LatticeResidues κ ell :=
  fun _ => ⟨0, hell⟩

@[simp] theorem zeroLatticeResidue_representative (ell : ℕ) (hell : 0 < ell) :
    latticeResidueRepresentative (zeroLatticeResidue (κ := κ) ell hell) = 0 := by
  funext j
  rfl

/-- The zero residue has the zero floor divisor in the zero-coefficient case. -/
theorem toricResidueCoefficients_zero_residue (fan : Fan i)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (ell : ℕ) (hell : 0 < ell) :
    toricResidueCoefficients fan (0 : fan.Ray → ℤ) ell
      (basis.equivFun.symm (latticeResidueRepresentative
        (zeroLatticeResidue (κ := κ) ell hell))) = 0 := by
  funext ρ
  simp [toricResidueCoefficients, zeroLatticeResidue_representative]

/-- The zero-residue summand is canonically identified with the structure
sheaf through the actual zero Cartier divisor. -/
def toricZeroResidueSheafIso (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (ell : ℕ) (hell : 0 < ell) :
    SheafOfModules.unit fan.algebraicRealization.ringCatSheaf ≅
      toricResidueSheafFamily fan nonempty regular basis (0 : fan.Ray → ℤ) ell
        (zeroLatticeResidue (κ := κ) ell hell) := by
  letI := toricSchemeIntegral fan nonempty
  exact invariantCartierZeroSheafIso fan nonempty regular ≪≫ eqToIso (by
    simp only [toricResidueSheafFamily, toricResidueCoefficients_zero_residue])

/-- The actual global structure-sheaf direct image contains the structure
sheaf as a retract. Both arrows are morphisms of genuine module sheaves. -/
def toricPowerGlobalStructureRetractOfBasis (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (ell : ℕ) (hell : 0 < ell) :
    Retract (SheafOfModules.unit fan.algebraicRealization.ringCatSheaf)
      ((Scheme.Modules.pushforward (toricPowerMap fan ell)).obj
        (SheafOfModules.unit fan.algebraicRealization.ringCatSheaf)) := by
  letI := toricSchemeIntegral fan nonempty
  let family := toricResidueSheafFamily fan nonempty regular basis (0 : fan.Ray → ℤ) ell
  let zero := zeroLatticeResidue (κ := κ) ell hell
  let summand : Retract (family zero) (⨁ family) := (biproduct.bicone family).retract zero
  let targetIso := (toricPowerInvariantCartierSplitting fan nonempty regular basis
      (0 : fan.Ray → ℤ) ell hell).symm ≪≫
    (Scheme.Modules.pushforward (toricPowerMap fan ell)).mapIso
      (invariantCartierZeroSheafIso fan nonempty regular).symm
  exact ((Retract.ofIso (toricZeroResidueSheafIso fan nonempty regular basis ell hell)).trans
    summand).trans (Retract.ofIso targetIso)

/-- No additional basis assumption is needed: the integral lattice supplies
its own finite character basis. -/
def toricPowerGlobalStructureRetract (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (ell : ℕ) (hell : 0 < ell) :
    Retract (SheafOfModules.unit fan.algebraicRealization.ringCatSheaf)
      ((Scheme.Modules.pushforward (toricPowerMap fan ell)).obj
        (SheafOfModules.unit fan.algebraicRealization.ringCatSheaf)) :=
  toricPowerGlobalStructureRetractOfBasis fan nonempty regular
    ((latticeCharacterBasis fan.lattice).reindex (Equiv.ulift.{u, 0}).symm) ell hell

end ToricPower
