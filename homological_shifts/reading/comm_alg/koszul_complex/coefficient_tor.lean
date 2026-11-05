import CommAlg.KoszulComplex.FiniteVariables
import CommAlg.Polymatroid.Exponents
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Genuine Tor over the coefficient ring

The coordinate Koszul complex is transported along exact restriction of
scalars. Its differential remains the actual tensor Koszul differential.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open CategoryTheory MvPolynomial CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

abbrev underlyingDifferential (B : Family V) (i : ℕ) :
    (Set.powersetCard V (i + 1) →₀ (monomialIdeal k B)) →ₗ[k]
      (Set.powersetCard V i →₀ (monomialIdeal k B)) :=
  (coordinateDifferential (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i).restrictScalars k

theorem underlyingDifferential_comp (B : Family V) (i : ℕ) :
    underlyingDifferential (k := k) B i ∘ₗ underlyingDifferential B (i + 1) = 0 := by
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun
    (coordinateDifferential_comp (X : V → MvPolynomial V k)
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i) z

/-- The genuine coordinate Koszul complex, regarded as a complex over the
coefficient ring by its canonical scalar structure. -/
def underlyingComplex (B : Family V) : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of
    (fun i => ModuleCat.of k (Set.powersetCard V i →₀ (monomialIdeal k B)))
    (fun i => ModuleCat.ofHom (underlyingDifferential B i))
    (fun i => ModuleCat.hom_ext (underlyingDifferential_comp B i))

@[simp] theorem underlyingComplex_d (B : Family V) (i : ℕ) :
    (underlyingComplex (k := k) B).d (i + 1) i =
      ModuleCat.ofHom
        ((coordinateDifferential (X : V → MvPolynomial V k)
          (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i).restrictScalars k) := by
  simp [underlyingComplex]

/-- The restriction-of-scalars module structure agrees with the canonical
coefficient-ring module structure. The equivalence is the identity on values. -/
def coefficientRestrictionEquiv (B : Family V) (i : ℕ) :
    ((ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (ModuleCat.of (MvPolynomial V k)
        (Set.powersetCard V i →₀ (monomialIdeal k B)))) ≃ₗ[k]
      (Set.powersetCard V i →₀ (monomialIdeal k B)) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun r z => by
    change (algebraMap k (MvPolynomial V k) r) •
      (show Set.powersetCard V i →₀ (monomialIdeal k B) from z) =
        r • (show Set.powersetCard V i →₀ (monomialIdeal k B) from z)
    exact algebraMap_smul (MvPolynomial V k) r
      (show Set.powersetCard V i →₀ (monomialIdeal k B) from z)

/-- Exact scalar restriction of the polynomial coordinate complex is
isomorphic to the same complex in canonical coefficient-ring modules. -/
def restrictionCoordinateComplexIso (B : Family V) :
    ((ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      (coordinateComplex (X : V → MvPolynomial V k)
        (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ≅
      underlyingComplex (k := k) B :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (coefficientRestrictionEquiv B i).toModuleIso)
    (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      simp only [Functor.mapHomologicalComplex_obj_d, coordinateComplex_d,
        underlyingComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      rfl)

/-- Actual derived Tor, restricted to the coefficient ring, is the homology
of the original standard coordinate Koszul complex. -/
def coefficientTorIso [Nontrivial k] (B : Family V) (i : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i
        (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ≅
      (underlyingComplex (k := k) B).homology i :=
  let F := ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))
  let M := ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)
  let C := coordinateComplex (X : V → MvPolynomial V k) M
  F.mapIso (finitePolynomialTorIso i M ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat (MvPolynomial V k))
      (ComplexShape.down ℕ) i).mapIso (coordinateComplexIso (X : V → MvPolynomial V k) M)) ≪≫
    ((C.sc i).mapHomologyIso F).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso
      (restrictionCoordinateComplexIso B)

end CommAlg.Koszul
