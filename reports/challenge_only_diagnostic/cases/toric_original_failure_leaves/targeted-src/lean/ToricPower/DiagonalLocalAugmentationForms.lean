module

public import ToricPower.DiagonalVertexAugmentation
public import ToricPower.DiagonalGlobalRestriction
public import ToricPower.AffineCoefficientAdjunction

/-!
# The exact sheaf-level vertex formula of the local diagonal resolution

The canonical cellular vertex augmentation, already normalized by the
actual disk orientation, is transported through the actual finite-free
frame and affine direct-image comparisons. The resulting morphism is the
actual scheme-adjunction transpose of multiplication by
`χ^(-q_left-q_right)`. This is an equality of actual sheaf maps.

Candidate source pending compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "R" => DiagonalChartRing ℂ A S T
local notation "B" => affineCoordinateRing fan.lattice (σ.val ⊓ τ.val)
local notation "φ" => CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ)
local notation "g" => Spec.map φ

private theorem affineTildeAugmentation_f_zero {R' : CommRingCat}
    {K : ChainComplex (ModuleCat.{0} R') ℕ} {M : ModuleCat.{0} R'}
    {P : (Spec R').Modules} (f : K ⟶ (ChainComplex.single₀ _).obj M)
    (e : tilde M ≅ P) :
    ((affineTildeChainFunctor R').map f ≫ (affineTildeSingleZeroIso R' M).hom ≫
      (ChainComplex.single₀ (Spec R').Modules).map e.hom).f 0 =
      tilde.map (f.f 0) ≫ e.hom := by
  simp only [HomologicalComplex.comp_f, affineTildeSingleZeroIso, Iso.app_hom,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
    CategoryTheory.Functor.map_id, ChainComplex.single₀_map_f_zero, Category.id_comp]
  rfl

/-- The literal regular monomial of the actual overlap coordinate ring
determined by the two chosen Cartier frames of a vertex. -/
def diagonalVertexCoefficient (j : NormalizedCell A 0) : B :=
  MonoidAlgebra.single
    (Multiplicative.ofAdd (diagonalVertexOverlapCharacter fan regular basis rays σ τ j)) 1

/-- The exact degree-zero column of the actual local module augmentation
is the scalar-restricted coefficient map `r ↦ φ(r)χ^(-q_left-q_right)`. -/
theorem diagonalFramedAugmentation_module_column (j : NormalizedCell A 0) :
    ModuleCat.ofHom (Finsupp.lsingle j : R →ₗ[R] NormalizedCell A 0 →₀ R) ≫
        (toricDiagonalFramedAugmentation fan regular basis rays σ τ).f 0 =
      affineCoefficientHom φ (diagonalVertexCoefficient fan regular basis rays σ τ j) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  have hs : (Finsupp.single j r : NormalizedCell A 0 →₀ R) =
      r • Finsupp.single j 1 := by simp
  change (toricDiagonalFramedAugmentation fan regular basis rays σ τ).f 0
      (Finsupp.single j r) = _
  rw [hs,map_smul,toricDiagonalFramedAugmentation_vertex]
  rfl

/-- The degree-zero map of the actual sheafified augmentation is the
actual sheafification of the module map followed by the specified target
isomorphism. -/
theorem toricDiagonalFramedSheafAugmentation_f_zero :
    (toricDiagonalFramedSheafAugmentation fan regular basis rays σ τ).f 0 =
      tilde.map ((toricDiagonalFramedAugmentation fan regular basis rays σ τ).f 0) ≫
        (toricDiagonalChartTargetIso fan basis rays σ τ).hom :=
  affineTildeAugmentation_f_zero
    (R' := CommRingCat.of R)
    (K := toricDiagonalFramedComplex fan regular basis rays σ τ)
    (M := diagonalIntersectionModule fan basis rays σ τ)
    (P := toricDiagonalChartDirectImage fan basis rays σ τ)
    (toricDiagonalFramedAugmentation fan regular basis rays σ τ)
    (toricDiagonalChartTargetIso fan basis rays σ τ)

/-- The actual local sheaf augmentation on a genuine free vertex
generator is the actual affine coefficient sheaf morphism. -/
theorem diagonalFramedSheafAugmentation_generator (j : NormalizedCell A 0) :
    diagonalFreeSheafGenerator fan basis rays σ τ 0 j ≫
        (toricDiagonalFramedSheafAugmentation fan regular basis rays σ τ).f 0 =
      affineCoefficientSheafMap φ
        (diagonalVertexCoefficient fan regular basis rays σ τ j) := by
  rw [toricDiagonalFramedSheafAugmentation_f_zero]
  unfold diagonalFreeSheafGenerator
  rw [Category.assoc,← tilde.map_comp_assoc,diagonalFramedAugmentation_module_column]
  rfl

/-- The local cellular resolution uses exactly the actual adjunction
transpose of multiplication by the expected overlap monomial. -/
theorem diagonalFramedSheafAugmentation_generator_adjunct
    (j : NormalizedCell A 0) :
    diagonalFreeSheafGenerator fan basis rays σ τ 0 j ≫
        (toricDiagonalFramedSheafAugmentation fan regular basis rays σ τ).f 0 =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((Scheme.Modules.pullbackObjUnitIso g).hom ≫
          Scheme.Modules.globalSectionsSmul
            (SheafOfModules.unit (Spec (.of B)).ringCatSheaf)
            ((Scheme.ΓSpecIso (.of B)).inv
              (diagonalVertexCoefficient fan regular basis rays σ τ j))) := by
  rw [diagonalFramedSheafAugmentation_generator,affineCoefficientSheafMap_eq_adjunct]

end ToricPower
