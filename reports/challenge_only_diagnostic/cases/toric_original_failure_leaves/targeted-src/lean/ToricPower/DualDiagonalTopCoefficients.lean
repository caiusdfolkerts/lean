module

public import ToricPower.DualDiagonalFramedAction
public import ToricPower.DualDiagonalTopClassNaturality
public import ToricPower.DualDiagonalBoundaryModule
public import ToricPower.ModuleSupportedDirectSum
public import ToricPower.ModuleDirectSumHomologyMaps

/-!
# The coherent top classes of the complete affine dual diagonal

The unrestricted homology sum is identified with exactly the permitted
boundary weights. The chosen ambient classes commute with every actual
monomial multiplication map. This is the coefficient-linear comparison
from which the genuine product-chart module comparison is obtained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [Field k] (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s))

/-- The complete top homology, in its genuine boundary-character basis. -/
def dualDiagonalAllWeightTopIso :
    (dualDiagonalAllWeightComplex k A S T).homology n ≅
      ModuleCat.of k (DualDiagonalBoundaryCoefficients A S T k) :=
  ModuleDirectSum.homologySumIso k (fun u => dualDiagonalWeightComplex A S T u k) n ≪≫
    SupportedDirectSum.iso k (fun u => (dualDiagonalWeightComplex A S T u k).homology n)
      (fun u => (dualDiagonalStrip A S T u).Nonempty)
      (fun u h => dualDiagonalWeightTopClassIso A S T u k h)
      (fun u h => dualDiagonalWeightComplex_isZero_homology_of_empty A S T u k
        (Set.not_nonempty_iff_eq_empty.mp h) n)

/-- The comparison sends each genuine weight inclusion to its chosen
ambient top class followed by the literal boundary basis inclusion. -/
@[reassoc]
theorem dualDiagonalAllWeightTopIso_inclusion (u : Fin n → ℤ)
    (h : (dualDiagonalStrip A S T u).Nonempty) :
    HomologicalComplex.homologyMap
        (ModuleDirectSum.complexInclusion k (fun v => dualDiagonalWeightComplex A S T v k) u) n ≫
        (dualDiagonalAllWeightTopIso k A S T).hom =
      (dualDiagonalWeightTopClassIso A S T u k h).hom ≫
        ModuleCat.ofHom (Finsupp.lsingle (R := k) (M := k)
          (⟨u,h⟩ : DualDiagonalBoundaryWeight A S T)) := by
  unfold dualDiagonalAllWeightTopIso
  rw [Iso.trans_hom, ← Category.assoc, ModuleDirectSum.homologySumIso_inclusion]
  exact SupportedDirectSum.iso_inclusion k
    (fun u => (dualDiagonalWeightComplex A S T u k).homology n)
    (fun u => (dualDiagonalStrip A S T u).Nonempty)
    (fun u h => dualDiagonalWeightTopClassIso A S T u k h)
    (fun u h => dualDiagonalWeightComplex_isZero_homology_of_empty A S T u k
      (Set.not_nonempty_iff_eq_empty.mp h) n) u h

variable (a : rayCharacterMonoid A S) (b : rayCharacterMonoid A T)

/-- Literal multiplication on the supported boundary coefficients. -/
def dualDiagonalBoundaryMonomialMap :
    ModuleCat.of k (DualDiagonalBoundaryCoefficients A S T k) ⟶
      ModuleCat.of k (DualDiagonalBoundaryCoefficients A S T k) :=
  ModuleCat.ofHom (Finsupp.lmapDomain k k (dualDiagonalBoundaryTranslate A S T (a,b)))

@[reassoc]
theorem dualDiagonalBoundaryMonomialMap_inclusion (u : DualDiagonalBoundaryWeight A S T) :
    ModuleCat.ofHom (Finsupp.lsingle (R := k) (M := k) u) ≫
        dualDiagonalBoundaryMonomialMap k A S T a b =
      ModuleCat.ofHom (Finsupp.lsingle (R := k) (M := k)
        (dualDiagonalBoundaryTranslate A S T (a,b) u)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact Finsupp.mapDomain_single

/-- The actual full homology map acts on the chosen top coefficients by
the literal monomial translation. This retains the original chain maps. -/
theorem dualDiagonalAllWeightTopIso_monomial :
    HomologicalComplex.homologyMap (dualDiagonalAllWeightMonomialMap k A S T a b) n ≫
        (dualDiagonalAllWeightTopIso k A S T).hom =
      (dualDiagonalAllWeightTopIso k A S T).hom ≫
        dualDiagonalBoundaryMonomialMap k A S T a b := by
  apply (isColimitOfPreserves (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) n)
    (ModuleDirectSum.complexCoconeIsColimit k
      (fun u => dualDiagonalWeightComplex A S T u k))).hom_ext
  intro u
  change HomologicalComplex.homologyMap
      (ModuleDirectSum.complexInclusion k (fun v => dualDiagonalWeightComplex A S T v k) u.as) n ≫
        HomologicalComplex.homologyMap (dualDiagonalAllWeightMonomialMap k A S T a b) n ≫
          (dualDiagonalAllWeightTopIso k A S T).hom =
    HomologicalComplex.homologyMap
      (ModuleDirectSum.complexInclusion k (fun v => dualDiagonalWeightComplex A S T v k) u.as) n ≫
        (dualDiagonalAllWeightTopIso k A S T).hom ≫
          dualDiagonalBoundaryMonomialMap k A S T a b
  by_cases h : (dualDiagonalStrip A S T u.as).Nonempty
  · have target := dualDiagonalStrip_monomial_nonempty A S T u.as a b h
    rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
      dualDiagonalAllWeightMonomialMap_inclusion, HomologicalComplex.homologyMap_comp,
      Category.assoc, dualDiagonalAllWeightTopIso_inclusion k A S T _ target,
      ← Category.assoc, dualDiagonalWeightMonomialMap_topClass A S T u.as k a b h target,
      dualDiagonalAllWeightTopIso_inclusion_assoc k A S T u.as h,
      dualDiagonalBoundaryMonomialMap_inclusion]
    rfl
  · exact (dualDiagonalWeightComplex_isZero_homology_of_empty A S T u.as k
      (Set.not_nonempty_iff_eq_empty.mp h) n).eq_of_src _ _

variable (frames : ∀ q, DiagonalCellFrames A S T q)

/-- The actual top homology of the actual ring-linear dual, with its
underlying coefficient-field structure retained. -/
def diagonalFramedDualTopScalarIso :
    (ModuleCat.restrictScalars (algebraMap k (DiagonalChartRing k A S T))).obj
      ((diagonalFramedDualComplex k A S T frames).homology n) ≅
        ModuleCat.of k (DualDiagonalBoundaryCoefficients A S T k) :=
  (((diagonalFramedDualComplex k A S T frames).sc n).mapHomologyIso
    (ModuleCat.restrictScalars (algebraMap k (DiagonalChartRing k A S T)))).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (diagonalFramedDualAllWeightIso k A S T frames) ≪≫
        dualDiagonalAllWeightTopIso k A S T

end ToricPower.IntegralArrangement
