module

public import ToricPower.CellularVertexAugmentation
public import ToricPower.DiagonalFramedResolution

/-!
# The exact degree-zero coefficient of the diagonal augmentation

Every genuine cellular vertex has canonical augmentation one. In the
actual Cartier frame its total character is `-q_left-q_right`, so the
augmentation to the actual intersection ring is the literal corresponding
monomial. This is the normalization needed for the global diagonal
augmentation, not just an abstract isomorphism on zeroth homology.

Candidate source pending compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s))

/-- The canonical homology construction recovers the independently
defined coefficient augmentation as its actual degree-zero map. -/
theorem diagonalChartAugmentation_f_zero :
    (diagonalChartAugmentation k A S T).f 0 =
      ModuleCat.ofHom (diagonalChartAugmentationLinear k A S T) := by
  let K := diagonalChartComplex k A S T
  let ε := ModuleCat.ofHom (diagonalChartAugmentationLinear k A S T)
  change K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫
    (K.isoHomologyι₀.hom ≫ K.descOpcycles ε 1 (by simp)
      (diagonalChartBoundary_augmentation k A S T)) = ε
  rw [Iso.inv_hom_id_assoc]
  exact HomologicalComplex.p_descOpcycles K ε 1 (by simp)
    (diagonalChartBoundary_augmentation k A S T)

theorem diagonalChartAugmentationMap_vertex (u : Fin n → ℤ)
    (c : {c : Cell (augmentedForms A) 0 // stripCellAllowed A S T u c})
    (hne : (diagonalStrip A S T u).Nonempty) (r : k) :
    diagonalChartAugmentationMap k A S T (Finsupp.single ⟨u,c⟩ r) =
      Finsupp.single ⟨u,hne⟩ r := by
  exact diagonalChartAugmentationMap_single_value k A S T u c hne r

end ToricPower.IntegralArrangement

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
local notation "F" => toricDiagonalCellFrames fan regular basis rays σ τ

theorem diagonalToricChartAugmentation_vertex (u : Fin n → ℤ)
    (c : {c : Cell (augmentedForms A) 0 // stripCellAllowed A S T u c})
    (hne : (diagonalStrip A S T u).Nonempty) (r : ℂ) :
    (diagonalToricChartAugmentation fan basis rays σ τ).f 0
        (Finsupp.single ⟨u,c⟩ r) =
      MonoidAlgebra.single
        (Multiplicative.ofAdd (diagonalSupportedWeightEquiv fan basis rays σ τ ⟨u,hne⟩)) r := by
  simp only [diagonalToricChartAugmentation,HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_zero,diagonalChartAugmentation_f_zero,
    ConcreteCategory.comp_apply]
  change diagonalIntersectionCoefficientEquiv fan basis rays σ τ
      (diagonalChartAugmentationMap ℂ A S T (Finsupp.single ⟨u,c⟩ r)) = _
  rw [diagonalChartAugmentationMap_vertex ℂ A S T u c hne r,
    diagonalIntersectionCoefficientEquiv_single]
  rfl

theorem diagonalVertexWeight_nonempty (j : NormalizedCell A 0) :
    (diagonalStrip A S T ((F 0).weight j 0)).Nonempty := by
  obtain ⟨x,hx⟩ := ((F 0).cell j 0).2.val.property.1
  exact ⟨x,(stripCellAllowed_iff_point A S T _ _ hx).mp ((F 0).cell j 0).2.property⟩

/-- The actual regular overlap character of a degree-zero Cartier frame. -/
def diagonalVertexOverlapCharacter (j : NormalizedCell A 0) :
    dualSemigroup fan.lattice (σ.val ⊓ τ.val) :=
  diagonalSupportedWeightEquiv fan basis rays σ τ
    ⟨(F 0).weight j 0,diagonalVertexWeight_nonempty fan regular basis rays σ τ j⟩

theorem diagonalVertexOverlapCharacter_val (j : NormalizedCell A 0) :
    (diagonalVertexOverlapCharacter fan regular basis rays σ τ j : N →+ ℤ) =
      -coneDivisorCharacter fan regular (diagonalLeftCoefficients fan basis rays j) σ -
        coneDivisorCharacter fan regular (diagonalRightCoefficients fan basis rays j) τ := by
  change basis.equivFun.symm ((0-diagonalLeftFrameCharacter fan regular basis rays σ j)+
      (0-diagonalRightFrameCharacter fan regular basis rays τ j)) = _
  simp only [zero_sub, map_add, map_neg, diagonalLeftFrameCharacter,
    diagonalRightFrameCharacter, LinearEquiv.symm_apply_apply, sub_eq_add_neg,
    map_zero, zero_add]

/-- The genuine local finite-matrix augmentation has precisely the
coefficient of the canonical global multiplication map to the diagonal. -/
theorem toricDiagonalFramedAugmentation_vertex (j : NormalizedCell A 0) :
    (toricDiagonalFramedAugmentation fan regular basis rays σ τ).f 0
        (Finsupp.single j (1 : R)) =
      MonoidAlgebra.single
        (Multiplicative.ofAdd (diagonalVertexOverlapCharacter fan regular basis rays σ τ j)) 1 := by
  change (diagonalToricChartAugmentation fan basis rays σ τ).f 0
    ((F 0).linearEquiv ℂ (Finsupp.single j (1 : R))) = _
  have hone : (1 : R) = AddMonoidAlgebra.single 0 1 := rfl
  rw [hone,DiagonalCellFrames.linearEquiv_single]
  exact diagonalToricChartAugmentation_vertex fan basis rays σ τ
    ((F 0).weight j 0) ((F 0).cell j 0).2
      (diagonalVertexWeight_nonempty fan regular basis rays σ τ j) 1

end ToricPower
