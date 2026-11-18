module

public import ToricPower.DualDiagonalMonomialMaps

/-!
# Monomial naturality of the full dual-diagonal comparison

The original cellular coefficient map and the genuine compact-support
map agree on every finite-stage generator, and therefore on their full
complexes. The resulting top-class map is exactly multiplication of the
corresponding Laurent monomials. No infinite algebraic dual is taken.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S T : Set (Fin s))
  (u : Fin n → ℤ) (a : rayCharacterMonoid A S) (b : rayCharacterMonoid A T)
  (k : Type) [Field k] (C : ℕ)
  (bound : ∀ j, |latticeLift (-a.val) j| ≤ (C : ℝ))

local notation "v" => u + a.val + b.val

/-- Actual compact-support multiplication on every finite-stage term,
in its complete universal-cover cell coordinates. -/
theorem dualDiagonalCompactMonomialMap_window_coordinates (r₀ r q : ℕ)
    (φ : (openSupportCochainComplex A k
      (dualDiagonalWindowSupport A S T u (r₀ + r))).X q) :
    dualDiagonalCompactCoordinates A S T v k (r₀ + C) q
        ((dualDiagonalCompactMonomialMap A k S T u a b C bound r₀).f q
          ((colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r).f q φ)) =
      Finsupp.mapDomain (dualDiagonalStripCellMonomialMap A S T u a b q)
        (dualDiagonalCompactCoordinates A S T u k r₀ q
          ((colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r).f q φ)) := by
  have square := congrArg (fun f => HomologicalComplex.Hom.f f q)
    (colimit.ι_map (dualDiagonalWindowMonomialMap A k S T u a b C bound r₀) r)
  have value := ConcreteCategory.congr_hom square φ
  change (dualDiagonalCompactMonomialMap A k S T u a b C bound r₀).f q
      ((colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r).f q φ) =
    (colimit.ι (dualDiagonalWindowCochainSystem A k S T v (r₀ + C)) r).f q
      ((openSupportCochainTranslation A (-a.val)
        (dualDiagonalWindowSystem_translation A S T u a b C bound r₀ r) k).f q φ) at value
  rw [value, dualDiagonalCompactCoordinates_inclusion,
    openSupportCochainTranslation_coordinates, dualDiagonalCompactCoordinates_inclusion,
    ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1

/-- The actual colimit map is literal translated extension on the full
finite-support Laurent basis, without any finite-strip assumption. -/
theorem dualDiagonalCompactMonomialMap_coordinates (r₀ q : ℕ)
    (w : (dualDiagonalCompactCochainComplex A k S T u r₀).X q) :
    dualDiagonalCompactCoordinates A S T v k (r₀ + C) q
        ((dualDiagonalCompactMonomialMap A k S T u a b C bound r₀).f q w) =
      Finsupp.mapDomain (dualDiagonalStripCellMonomialMap A S T u a b q)
        (dualDiagonalCompactCoordinates A S T u k r₀ q w) := by
  let f := (dualDiagonalCompactMonomialMap A k S T u a b C bound r₀).f q ≫
    (dualDiagonalCompactCoordinates A S T v k (r₀ + C) q).toModuleIso.hom
  let g := (dualDiagonalCompactCoordinates A S T u k r₀ q).toModuleIso.hom ≫
    ModuleCat.ofHom (Finsupp.lmapDomain k k (dualDiagonalStripCellMonomialMap A S T u a b q))
  have equality : f = g := by
    apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat k) (.up ℕ) q)
      (colimit.isColimit (dualDiagonalWindowCochainSystem A k S T u r₀))).hom_ext
    intro r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    exact dualDiagonalCompactMonomialMap_window_coordinates A S T u a b k C bound r₀ r q φ
  exact ConcreteCategory.congr_hom equality w

/-- The comparison of the two actual complexes commutes with literal
monomial multiplication on both affine factors. -/
@[reassoc]
theorem dualDiagonalWeightCompactIso_monomial (r₀ : ℕ) :
    dualDiagonalWeightMonomialMap A S T u a b k ≫
        (dualDiagonalWeightCompactIso A S T v k (r₀ + C)).hom =
      (dualDiagonalWeightCompactIso A S T u k r₀).hom ≫
        dualDiagonalCompactMonomialMap A k S T u a b C bound r₀ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  apply (dualDiagonalCompactCoordinates A S T v k (r₀ + C) q).injective
  change dualDiagonalCompactCoordinates A S T v k (r₀ + C) q
      ((dualDiagonalCompactCoordinates A S T v k (r₀ + C) q).symm
        (dualDiagonalWeightCoordinates A S T v k q
          ((dualDiagonalWeightMonomialMap A S T u a b k).f q w))) =
    dualDiagonalCompactCoordinates A S T v k (r₀ + C) q
      ((dualDiagonalCompactMonomialMap A k S T u a b C bound r₀).f q
        ((dualDiagonalCompactCoordinates A S T u k r₀ q).symm
          (dualDiagonalWeightCoordinates A S T u k q w)))
  rw [LinearEquiv.apply_symm_apply, dualDiagonalCompactMonomialMap_coordinates,
    LinearEquiv.apply_symm_apply]
  exact dualDiagonalWeightMonomialMap_coordinates A S T u a b k q w

/-- The coherent top coefficient of the original, independently defined
cellular monomial map is exactly one. -/
theorem dualDiagonalWeightMonomialMap_topClass_atWindow (r₀ : ℕ)
    (h₀ : (dualDiagonalWindow A S T u r₀).Nonempty) :
    HomologicalComplex.homologyMap (dualDiagonalWeightMonomialMap A S T u a b k) n ≫
        HomologicalComplex.homologyMap
          (dualDiagonalWeightCompactIso A S T v k (r₀ + C)).hom n ≫
        (dualDiagonalCompactTopClassIso A k S T v (r₀ + C)
          (dualDiagonalWindowMonomial_nonempty A S T u a b C bound h₀)).hom =
      HomologicalComplex.homologyMap (dualDiagonalWeightCompactIso A S T u k r₀).hom n ≫
        (dualDiagonalCompactTopClassIso A k S T u r₀ h₀).hom := by
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    dualDiagonalWeightCompactIso_monomial A S T u a b k C bound,
    HomologicalComplex.homologyMap_comp, Category.assoc,
    dualDiagonalCompactMonomialMap_topClass]

end ToricPower.IntegralArrangement
