module

public import ToricPower.DivisorWeightSplitting
public import ToricPower.AffineSplitting
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Actual affine sheaf direct image of a divisor module

The tagged Laurent scalar action is identified with Mathlib's restriction of
scalars along the chart power endomorphism.  Affine sheafification then turns
the module decomposition into an isomorphism of genuine sheaf direct images.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

namespace ToricPower

open MonoidAlgebra CategoryTheory CategoryTheory.Limits AlgebraicGeometry


universe ringUniverse moduleUniverse indexUniverse

/-- The standard finite-biproduct comparison, allowing the finite index in
any universe. This is the same universal-property proof as Mathlib's
`ModuleCat.biproductIsoPi`, using its universe-polymorphic product cone. -/
def moduleFiniteBiproductIsoPi {R : Type ringUniverse} [Ring R]
    {J : Type indexUniverse} [Finite J]
    (family : J → ModuleCat.{max indexUniverse moduleUniverse} R) :
    (⨁ family) ≅ ModuleCat.of R (∀ j, family j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit family)
    (ModuleCat.HasLimit.productLimitCone family).isLimit

@[simp] theorem moduleFiniteBiproductIsoPi_inv_comp_π {R : Type ringUniverse} [Ring R]
    {J : Type indexUniverse} [Finite J]
    (family : J → ModuleCat.{max indexUniverse moduleUniverse} R) (j : J) :
    (moduleFiniteBiproductIsoPi family).inv ≫ biproduct.π family j =
      ModuleCat.ofHom (LinearMap.proj j : (∀ j, family j) →ₗ[R] family j) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

variable {ι κ : Type*} [Fintype κ]

def rayChartPowerEndomorphism (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) : RayChartRing R A →+* RayChartRing R A :=
  mapDomainRingHom R (ell • AddMonoidHom.id (rayWeightMonoid A)).toMultiplicative

theorem rayChartPowerEndomorphism_ambient (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) (a : RayChartRing R A) :
    mapDomain (rayChartPowerMonoidHom A 1) (rayChartPowerEndomorphism R A ell a) =
      mapDomain (rayChartPowerMonoidHom A ell) a := by
  have hp : (rayChartPowerMonoidHom A 1).comp
      (ell • AddMonoidHom.id (rayWeightMonoid A)).toMultiplicative =
        rayChartPowerMonoidHom A ell := by
    apply MonoidHom.ext
    intro s
    apply Multiplicative.toAdd.injective
    change 1 • (ell • (Multiplicative.toAdd s).1) = ell • (Multiplicative.toAdd s).1
    rw [one_smul]
  have h := congrArg (fun f : RayChartRing R A →+*
      MonoidAlgebra R (Multiplicative (κ → ℤ)) => f a)
    (mapDomainRingHom_comp (R := R) (rayChartPowerMonoidHom A 1)
      (ell • AddMonoidHom.id (rayWeightMonoid A)).toMultiplicative)
  simpa only [hp, RingHom.comp_apply, mapDomainRingHom_apply,
    rayChartPowerEndomorphism] using h.symm

/-- The power-tagged divisor module is precisely the ordinary divisor module
with scalars restricted through the chart power endomorphism. -/
def divisorRestrictScalarsLinearEquiv (R : Type*) [CommRing R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) :
    ((ModuleCat.restrictScalars (rayChartPowerEndomorphism R A ell)).obj
      (ModuleCat.of (RayChartRing R A) (DivisorSectionModule R A b 1))) ≃ₗ[RayChartRing R A]
      DivisorSectionModule R A b ell where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A ell
    change mapDomain (rayChartPowerMonoidHom A 1) (rayChartPowerEndomorphism R A ell a) *
        rayPowerLaurentValue R A 1 x.1 =
      mapDomain (rayChartPowerMonoidHom A ell) a * rayPowerLaurentValue R A 1 x.1
    rw [rayChartPowerEndomorphism_ambient]

/-- The full splitting as an isomorphism in the actual category of modules over
the affine coordinate ring. -/
def divisorPowerModuleIso (R : Type*) [CommRing R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell) :
    (ModuleCat.restrictScalars (rayChartPowerEndomorphism R A ell)).obj
      (ModuleCat.of (RayChartRing R A) (DivisorSectionModule R A b 1)) ≅
      ModuleCat.of (RayChartRing R A)
        (∀ u : LatticeResidues κ ell, DivisorSectionModule R A
          (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1) :=
  (divisorRestrictScalarsLinearEquiv R A b ell).toModuleIso ≪≫
    (divisorSectionResidueLinearEquiv R A b ell hell).symm.toModuleIso

/-- The affine power-map direct image of the associated divisor sheaf is the
associated sheaf of the finite direct sum of the literal floor-divisor modules.
The left side uses Mathlib's actual scheme-module direct image functor. -/
def affineDivisorPowerPushforwardIso (R : Type*) [CommRing R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell) :
    (Scheme.Modules.pushforward (Spec.map
      (CommRingCat.ofHom (rayChartPowerEndomorphism R A ell)))).obj
        (tilde (ModuleCat.of (RayChartRing R A) (DivisorSectionModule R A b 1))) ≅
      tilde (ModuleCat.of (RayChartRing R A)
        (∀ u : LatticeResidues κ ell, DivisorSectionModule R A
          (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1)) :=
  affinePushforwardTildeIso (CommRingCat.ofHom (rayChartPowerEndomorphism R A ell))
      (ModuleCat.of (RayChartRing R A) (DivisorSectionModule R A b 1)) ≪≫
    (tilde.functor (CommRingCat.of (RayChartRing R A))).mapIso
      (divisorPowerModuleIso R A b ell hell)

/-- The same actual affine sheaf isomorphism, with its target displayed as the
categorical finite direct sum of the associated floor-divisor sheaves. -/
def affineDivisorPowerBiproductIso (R : Type*) [CommRing R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell) :
    (Scheme.Modules.pushforward (Spec.map
      (CommRingCat.ofHom (rayChartPowerEndomorphism R A ell)))).obj
        (tilde (ModuleCat.of (RayChartRing R A) (DivisorSectionModule R A b 1))) ≅
      ⨁ (fun u : LatticeResidues κ ell =>
        tilde (ModuleCat.of (RayChartRing R A) (DivisorSectionModule R A
          (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1))) := by
  let family : LatticeResidues κ ell → ModuleCat (RayChartRing R A) := fun u =>
    ModuleCat.of (RayChartRing R A) (DivisorSectionModule R A
      (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1)
  letI : (tilde.functor (CommRingCat.of (RayChartRing R A))).PreservesZeroMorphisms :=
    ⟨fun _ _ => tilde.map_zero⟩
  letI : (tilde.functor (CommRingCat.of (RayChartRing R A))).IsLeftAdjoint :=
    tilde.adjunction.isLeftAdjoint
  letI : PreservesBiproduct family (tilde.functor (CommRingCat.of (RayChartRing R A))) :=
    preservesBiproduct_of_preservesCoproduct _
  exact affineDivisorPowerPushforwardIso R A b ell hell ≪≫
    (tilde.functor (CommRingCat.of (RayChartRing R A))).mapIso
      (moduleFiniteBiproductIsoPi family).symm ≪≫
    (tilde.functor (CommRingCat.of (RayChartRing R A))).mapBiproduct family

end ToricPower
