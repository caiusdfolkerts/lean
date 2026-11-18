module

public import ToricPower.DiagonalGlobalComplex
public import ToricPower.DiagonalCartierFrames
public import ToricPower.DiagonalFramedResolution
public import ToricPower.AffineFreeFrameComparison

/-!
# Restriction of the actual global diagonal complex to an affine chart

The isomorphisms in this file use the actual Cartier frames and actual
finite biproducts. Each global character entry becomes the exact normalized
monomial of the separately constructed cellular matrix. This identifies
the entire restricted global complex with the independently constructed
finite free local complex, including every incidence coefficient.

Candidate source pending compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical BigOperators

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace ToricPower

/-- Morphisms from the tilde of a finite free module are determined by
the actual module generators, expressed in the unit sheaf's frame. -/
theorem tildeFiniteFree_hom_ext (R : CommRingCat.{0}) (I : Type) [Finite I]
    {P : (Spec R).Modules}
    {f g : tilde (ModuleCat.of R (I →₀ R)) ⟶ P}
    (h : ∀ j : I,
      (tildeSelf (R := R)).inv ≫
        tilde.map (ModuleCat.ofHom (Finsupp.lsingle j : R →ₗ[R] I →₀ R)) ≫ f =
      (tildeSelf (R := R)).inv ≫
        tilde.map (ModuleCat.ofHom (Finsupp.lsingle j : R →ₗ[R] I →₀ R)) ≫ g) : f = g := by
  apply (cancel_epi (tildeFiniteFreeBiproductIso R I).inv).mp
  apply biproduct.hom_ext'
  intro j
  rw [← tildeFiniteFreeBiproductIso_single R I j]
  simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h j

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "R" => DiagonalChartRing ℂ A S T
local notation "U" => Spec (CommRingCat.of R)
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "P" => Scheme.Modules.pullback chart
local notation "L" => diagonalProductSheaf fan nonempty regular basis rays
local notation "G" => diagonalGlobalSheafTerm fan nonempty regular basis rays
local notation "F" => toricDiagonalCellFrames fan regular basis rays σ τ
local notation "col" => diagonalGlobalColumn ℂ A

local instance diagonalAffineModuleLinear :
    Linear ℂ (SheafOfModules (U).ringCatSheaf) :=
  Scheme.Modules.baseLinear ℂ U

local instance diagonalRestrictedCellsFintype (d : ℕ) : Fintype (NormalizedCell A d) := Fintype.ofFinite _
local instance diagonalRestrictedTermsFintype (d : ℕ) (j : NormalizedCell A (d+1)) :
    Fintype (DiagonalGlobalColumnTerm ℂ A d j) := Fintype.ofFinite _

/-- The actual generator of a finite free affine sheaf, with domain the
unit sheaf. -/
def diagonalFreeSheafGenerator (d : ℕ) (j : NormalizedCell A d) :
    SheafOfModules.unit (U).ringCatSheaf ⟶
      tilde (ModuleCat.of R (NormalizedCell A d →₀ R)) :=
  (tildeSelf («R» := CommRingCat.of R)).inv ≫
    tilde.map (ModuleCat.ofHom (Finsupp.lsingle j : R →ₗ[R] NormalizedCell A d →₀ R))

/-- The actual restriction of each global finite sum is the actual tilde
of its finite free Cartier-frame module. -/
def diagonalGlobalTermChartIso (d : ℕ) :
    tilde (ModuleCat.of R (NormalizedCell A d →₀ R)) ≅ (P).obj (G d) :=
  affineFreeFrameComparison (CommRingCat.of R) (NormalizedCell A d) P
    (fun j : NormalizedCell A d => L j)
    (fun j => diagonalProductCartierFrame fan nonempty regular basis rays σ τ j)

/-- The displayed term isomorphism uses precisely the specified Cartier
frame on each actual summand. -/
@[reassoc]
theorem diagonalGlobalTermChartIso_generator (d : ℕ) (j : NormalizedCell A d) :
    diagonalFreeSheafGenerator fan basis rays σ τ d j ≫
        (diagonalGlobalTermChartIso fan nonempty regular basis rays σ τ d).hom =
      (diagonalProductCartierFrame fan nonempty regular basis rays σ τ j).hom ≫
        (P).map (biproduct.ι (fun i : NormalizedCell A d => L i) j) := by
  simpa only [diagonalFreeSheafGenerator, diagonalGlobalTermChartIso,
    Category.assoc] using affineFreeFrameComparison_generator
      (CommRingCat.of R) (NormalizedCell A d) P
      (fun i : NormalizedCell A d => L i)
      (fun i => diagonalProductCartierFrame fan nonempty regular basis rays σ τ i) j

/-- The monomial obtained from the actual Cartier sheaf frames is the
literal exponent independently obtained from the cellular frame data. -/
theorem diagonalEntryChartCharacter_eq_framed (d : ℕ)
    (j : NormalizedCell A (d+1)) (p : DiagonalGlobalColumnTerm ℂ A d j) :
    diagonalEntryChartCharacter fan regular basis rays σ τ j p.val.1 p.val.2
      (diagonalEntryRegular_of_globalColumn_ne_zero fan basis rays d j p.val.1 p.val.2
        (Finsupp.mem_support_iff.mp p.property)) =
      diagonalFramedMonomial ℂ A (F d) (F (d+1)) j p := by
  apply Prod.ext
  · apply Subtype.ext
    exact diagonalEntryChartCharacter_left fan regular basis rays σ τ j p.val.1 p.val.2 _
  · apply Subtype.ext
    exact diagonalEntryChartCharacter_right fan regular basis rays σ τ j p.val.1 p.val.2 _

/-- The framed free-module differential has the exact finite polynomial
column, as an equality of genuine module-category morphisms. -/
theorem diagonalFramedBoundary_module_column (d : ℕ) (j : NormalizedCell A (d+1)) :
    ModuleCat.ofHom (Finsupp.lsingle j : R →ₗ[R] NormalizedCell A (d+1) →₀ R) ≫
        ModuleCat.ofHom (diagonalFramedBoundary ℂ A (F d) (F (d+1))) =
      ∑ p : DiagonalGlobalColumnTerm ℂ A d j,
        (AddMonoidAlgebra.single (diagonalFramedMonomial ℂ A (F d) (F (d+1)) j p)
          (col d j p.val) : R) •
          ModuleCat.ofHom (Finsupp.lsingle p.val.1 : R →ₗ[R] NormalizedCell A d →₀ R) := by
  apply ModuleCat.hom_ext
  ext r i
  simp [diagonalFramedBoundary,diagonalFramedGlobalColumn,
    Finsupp.linearCombination_single,Finsupp.smul_single,smul_eq_mul,mul_comm]

private theorem diagonalAffine_baseScalar (r : ℂ) :
    Scheme.Modules.baseRingToGlobalSections ℂ U r =
      affineGlobalSectionsEquiv R (algebraMap ℂ R r) := by
  rw [Scheme.Modules.baseRingToGlobalSections_apply, specOverSpec_over]
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap ℂ R))) r).symm

/-- Base-field scalar multiplication on an actual affine sheaf
endomorphism is multiplication of the literal affine coefficient. -/
theorem diagonalAffineScalar_smul (r : ℂ) (v : R) :
    r • Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (U).ringCatSheaf)
        (affineGlobalSectionsEquiv R v) =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (U).ringCatSheaf)
        (affineGlobalSectionsEquiv R (r • v)) := by
  rw [Scheme.Modules.base_smul_eq,
    diagonalAffine_baseScalar,
    ← Scheme.Modules.globalSectionsSmul_mul]
  change Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (U).ringCatSheaf)
      (affineGlobalSectionsEquiv R (algebraMap ℂ R r) * affineGlobalSectionsEquiv R v) = _
  rw [← map_mul,Algebra.smul_def]

/-- Every actually supported global entry, including its actual incidence
coefficient, becomes the corresponding literal polynomial coefficient. -/
@[reassoc]
theorem diagonalProductCartierFrame_supported_smul (d : ℕ)
    (j : NormalizedCell A (d+1)) (p : DiagonalGlobalColumnTerm ℂ A d j) (r : ℂ) :
    (diagonalProductCartierFrame fan nonempty regular basis rays σ τ j).hom ≫
      (P).map (r • diagonalProductMonomialEntry fan nonempty regular basis rays d j p) =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (U).ringCatSheaf)
        (affineGlobalSectionsEquiv R
          (AddMonoidAlgebra.single
            (diagonalFramedMonomial ℂ A (F d) (F (d+1)) j p) r)) ≫
        (diagonalProductCartierFrame fan nonempty regular basis rays σ τ p.val.1).hom := by
  have h := diagonalEntryRegular_of_globalColumn_ne_zero fan basis rays d j
    p.val.1 p.val.2 (Finsupp.mem_support_iff.mp p.property)
  rw [Functor.map_smul,Linear.comp_smul,
    diagonalProductMonomialEntry_eq_characterHom,diagonalProductCharacterHom,dif_pos h,
    diagonalProductCartierFrame_map,diagonalEntryChartCharacter_eq_framed,
    ← Linear.smul_comp,diagonalAffineScalar_smul]
  simp only [AddMonoidAlgebra.smul_single,smul_eq_mul,mul_one]

/-- The original global column is exactly the finite sum of scalar-weighted
actual character entries, with the same supported-term indexing. -/
theorem diagonalGlobalSheafColumn_eq_supported_sum (d : ℕ)
    (j : NormalizedCell A (d+1)) :
    diagonalGlobalSheafColumn fan nonempty regular basis rays d j =
      ∑ p : DiagonalGlobalColumnTerm ℂ A d j,
        (col d j p.val •
          diagonalProductMonomialEntry fan nonempty regular basis rays d j p) ≫
          biproduct.ι (fun i : NormalizedCell A d => L i) p.val.1 := by
  simp only [diagonalGlobalSheafColumn,Scheme.Modules.base_smul_eq,Category.assoc]

/-- Pullback of the actual finite global column is the literal finite
polynomial column in the actual target Cartier frames. -/
theorem diagonalGlobalColumn_chart_frame (d : ℕ) (j : NormalizedCell A (d+1)) :
    (diagonalProductCartierFrame fan nonempty regular basis rays σ τ j).hom ≫
        (P).map (diagonalGlobalSheafColumn fan nonempty regular basis rays d j) =
      ∑ p : DiagonalGlobalColumnTerm ℂ A d j,
        Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (U).ringCatSheaf)
          (affineGlobalSectionsEquiv R
            (AddMonoidAlgebra.single
              (diagonalFramedMonomial ℂ A (F d) (F (d+1)) j p) (col d j p.val))) ≫
          (diagonalProductCartierFrame fan nonempty regular basis rays σ τ p.val.1).hom ≫
          (P).map (biproduct.ι (fun i : NormalizedCell A d => L i) p.val.1) := by
  rw [diagonalGlobalSheafColumn_eq_supported_sum]
  simp only [Functor.map_sum,Preadditive.comp_sum,Functor.map_comp,Category.assoc]
  apply Finset.sum_congr rfl
  intro p hp
  rw [diagonalProductCartierFrame_supported_smul_assoc]

/-- An arbitrary polynomial multiple of one free generator has the same
coefficient in the corresponding actual Cartier frame. -/
theorem diagonalGlobalTermChartIso_scalar_generator (d : ℕ)
    (j : NormalizedCell A d) (r : R) :
    (tildeSelf («R» := CommRingCat.of R)).inv ≫
      tilde.map (r • ModuleCat.ofHom
        (Finsupp.lsingle j : R →ₗ[R] NormalizedCell A d →₀ R)) ≫
      (diagonalGlobalTermChartIso fan nonempty regular basis rays σ τ d).hom =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (U).ringCatSheaf)
          (affineGlobalSectionsEquiv R r) ≫
        (diagonalProductCartierFrame fan nonempty regular basis rays σ τ j).hom ≫
        (P).map (biproduct.ι (fun i : NormalizedCell A d => L i) j) := by
  have hs : r • ModuleCat.ofHom
        (Finsupp.lsingle j : R →ₗ[R] NormalizedCell A d →₀ R) =
      (r • 𝟙 (ModuleCat.of R R)) ≫ ModuleCat.ofHom
        (Finsupp.lsingle j : R →ₗ[R] NormalizedCell A d →₀ R) := by
    simp only [Linear.smul_comp,Category.id_comp]
  rw [hs]
  rw [tilde.map_comp]
  calc
    _ = ((tildeSelf («R» := CommRingCat.of R)).inv ≫
          tilde.map (r • 𝟙 (ModuleCat.of R R)) ≫ (tildeSelf («R» := CommRingCat.of R)).hom) ≫
        (diagonalFreeSheafGenerator fan basis rays σ τ d j ≫
          (diagonalGlobalTermChartIso fan nonempty regular basis rays σ τ d).hom) := by
      simp only [diagonalFreeSheafGenerator,Category.assoc,Iso.hom_inv_id_assoc]
    _ = _ := by
      rw [tildeScalarSelf_unit_frame,diagonalGlobalTermChartIso_generator]
      rfl

/-- The genuine sheafification of the local free matrix has precisely the
same column in the actual Cartier frame as the restricted global matrix. -/
theorem diagonalFramedSheafBoundary_generator (d : ℕ)
    (j : NormalizedCell A (d+1)) :
    diagonalFreeSheafGenerator fan basis rays σ τ (d+1) j ≫
        tilde.map (ModuleCat.ofHom (diagonalFramedBoundary ℂ A (F d) (F (d+1)))) ≫
        (diagonalGlobalTermChartIso fan nonempty regular basis rays σ τ d).hom =
      (diagonalProductCartierFrame fan nonempty regular basis rays σ τ j).hom ≫
        (P).map (diagonalGlobalSheafColumn fan nonempty regular basis rays d j) := by
  rw [diagonalGlobalColumn_chart_frame]
  unfold diagonalFreeSheafGenerator
  erw [Category.assoc,← tilde.map_comp_assoc,diagonalFramedBoundary_module_column,
    affineTilde_map_sum,
    Preadditive.sum_comp,Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact diagonalGlobalTermChartIso_scalar_generator
    fan nonempty regular basis rays σ τ d p.val.1 _

/-- Equality of the entire actual local and restricted global boundary
matrices, proved by their genuine free generators. -/
@[reassoc]
theorem diagonalGlobalTermChartIso_boundary (d : ℕ) :
    tilde.map (ModuleCat.ofHom (diagonalFramedBoundary ℂ A (F d) (F (d+1)))) ≫
        (diagonalGlobalTermChartIso fan nonempty regular basis rays σ τ d).hom =
      (diagonalGlobalTermChartIso fan nonempty regular basis rays σ τ (d+1)).hom ≫
        (P).map (diagonalGlobalSheafBoundary fan nonempty regular basis rays d) := by
  apply tildeFiniteFree_hom_ext (.of R) (NormalizedCell A (d+1))
  intro j
  have localColumn := diagonalFramedSheafBoundary_generator
    fan nonempty regular basis rays σ τ d j
  have globalColumn := diagonalGlobalTermChartIso_generator_assoc
    fan nonempty regular basis rays σ τ (d+1) j
    ((P).map (diagonalGlobalSheafBoundary fan nonempty regular basis rays d))
  erw [← Functor.map_comp, diagonalGlobalSheafBoundary_column] at globalColumn
  simpa only [diagonalFreeSheafGenerator, Category.assoc] using
    localColumn.trans globalColumn.symm

/-- Restriction of the genuine global sheaf complex is isomorphic to the
independently constructed local cellular matrix complex. -/
def diagonalGlobalComplexChartIso :
    toricDiagonalFramedSheafComplex fan regular basis rays σ τ ≅
      ((P).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (diagonalGlobalSheafComplex fan nonempty regular basis rays) :=
  HomologicalComplex.Hom.isoOfComponents
    (diagonalGlobalTermChartIso fan nonempty regular basis rays σ τ)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      change (diagonalGlobalTermChartIso fan nonempty regular basis rays σ τ (j+1)).hom ≫
          (P).map ((diagonalGlobalSheafComplex fan nonempty regular basis rays).d (j+1) j) =
        tilde.map ((toricDiagonalFramedComplex fan regular basis rays σ τ).d (j+1) j) ≫
          (diagonalGlobalTermChartIso fan nonempty regular basis rays σ τ j).hom
      have globalBoundary :
          (diagonalGlobalSheafComplex fan nonempty regular basis rays).d (j+1) j =
            diagonalGlobalSheafBoundary fan nonempty regular basis rays j :=
        ChainComplex.of_d _ _ j
      have localBoundary :
          (toricDiagonalFramedComplex fan regular basis rays σ τ).d (j+1) j =
            ModuleCat.ofHom (diagonalFramedBoundary ℂ A (F j) (F (j+1))) :=
        diagonalFramedComplex_d ℂ A S T F j
      erw [globalBoundary, localBoundary]
      exact (diagonalGlobalTermChartIso_boundary
        fan nonempty regular basis rays σ τ j).symm)

end ToricPower
