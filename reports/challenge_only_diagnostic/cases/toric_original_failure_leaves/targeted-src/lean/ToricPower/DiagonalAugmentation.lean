module

public import ToricPower.DiagonalCellular
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# The actual augmentation of each diagonal monomial-weight complex

For a nonempty strip, the cellular complex maps to the coefficient module
in degree zero through its canonical homology quotient and the ordinary
singular augmentation.  The map is proved to be a quasi-isomorphism.

The construction does not replace a complex by its homology as a definition:
the source is the actual cellular complex, the augmentation is an actual
chain map, and its homology is computed explicitly.

Candidate until the complete cellular dependency closure compiles.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

section Augmentation

variable {C : Type*} [Category* C] [Abelian C]

/-- The actual chain map induced by a map out of zeroth homology. -/
def augmentationOfHomologyZero (K : ChainComplex C ℕ) {M : C}
    (η : K.homology 0 ⟶ M) : K ⟶ (ChainComplex.single₀ C).obj M :=
  HomologicalComplex.mkHomToSingle
    (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ η)
    (fun j _ => by
      rw [← Category.assoc, HomologicalComplex.d_pOpcycles, zero_comp])

/-- Naturality is an equality of actual chain maps, including their
degree-zero components, and follows from the natural quotient to
opcycles. -/
theorem augmentationOfHomologyZero_naturality {K L : ChainComplex C ℕ}
    (φ : K ⟶ L) {M : C} (η : L.homology 0 ⟶ M) :
    φ ≫ augmentationOfHomologyZero L η =
      augmentationOfHomologyZero K (HomologicalComplex.homologyMap φ 0 ≫ η) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, augmentationOfHomologyZero,
    HomologicalComplex.mkHomToSingle_f, Category.assoc,
    ChainComplex.isoHomologyι₀_inv_naturality_assoc,
    HomologicalComplex.p_opcyclesMap_assoc]

/-- The augmentation induces exactly the prescribed map on homology. -/
theorem augmentationOfHomologyZero_homology (K : ChainComplex C ℕ) {M : C}
    (η : K.homology 0 ⟶ M) :
    HomologicalComplex.homologyMap (augmentationOfHomologyZero K η) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 M).hom = η := by
  let α := augmentationOfHomologyZero K η
  let S := (ChainComplex.single₀ C).obj M
  have hα : α.f 0 =
      (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ η) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 M).inv := by
    simp only [α, augmentationOfHomologyZero, HomologicalComplex.mkHomToSingle_f]
  apply (cancel_epi (K.homologyπ 0)).mp
  change K.homologyπ 0 ≫ (HomologicalComplex.homologyMap α 0 ≫
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 M).hom) =
      K.homologyπ 0 ≫ η
  calc
    _ = HomologicalComplex.cyclesMap α 0 ≫ S.homologyπ 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 M).hom := by
      rw [HomologicalComplex.homologyπ_naturality_assoc]
    _ = HomologicalComplex.cyclesMap α 0 ≫ S.iCycles 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 M).hom := by
      rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
        HomologicalComplex.singleObjCyclesSelfIso_hom]
    _ = K.iCycles 0 ≫ α.f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 M).hom := by
      rw [HomologicalComplex.cyclesMap_i_assoc]
    _ = K.iCycles 0 ≫ K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ η := by
      rw [hα]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = K.homologyπ 0 ≫ η := by
      rw [← HomologicalComplex.homology_π_ι_assoc]
      simp only [Category.assoc, HomologicalComplex.isoHomologyι_hom_inv_id_assoc]

/-- Positive-degree exactness together with the computed zeroth homology
proves that this actual augmentation is a quasi-isomorphism. -/
theorem augmentationOfHomologyZero_quasiIso (K : ChainComplex C ℕ) {M : C}
    (e : K.homology 0 ≅ M) (hexact : ∀ q : ℕ, q ≠ 0 → K.ExactAt q) :
    QuasiIso (augmentationOfHomologyZero K e.hom) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hq : q = 0
  · subst q
    have hcomp : IsIso (HomologicalComplex.homologyMap
        (augmentationOfHomologyZero K e.hom) 0 ≫
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 M).hom) := by
      rw [augmentationOfHomologyZero_homology]
      infer_instance
    letI := hcomp
    exact IsIso.of_isIso_comp_right _
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 M).hom
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology K q).mp (hexact q hq)).isIso
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 M q hq) _

/-- The component at degree zero is the canonical quotient from zero
chains, followed by the chosen map from homology. -/
theorem augmentationOfHomologyZero_f_zero (K : ChainComplex C ℕ) {M : C}
    (η : K.homology 0 ⟶ M) :
    (augmentationOfHomologyZero K η).f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 M).hom =
        K.cycles₀Iso.inv ≫ K.homologyπ 0 ≫ η := by
  have hquot : K.pOpcycles 0 ≫ K.isoHomologyι₀.inv =
      K.cycles₀Iso.inv ≫ K.homologyπ 0 := by
    rw [← cancel_mono (K.homologyι 0), Category.assoc,
      HomologicalComplex.isoHomologyι_inv_hom_id, Category.comp_id,
      Category.assoc, HomologicalComplex.homology_π_ι,
      HomologicalComplex.iCyclesIso_inv_hom_id_assoc]
  simp only [augmentationOfHomologyZero, HomologicalComplex.mkHomToSingle_f,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hquot, Category.assoc]

end Augmentation

namespace IntegralArrangement

open Set

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  {k : Type} [Ring k] (M : ModuleCat k)

/-- The actual chain augmentation of a nonempty diagonal strip. -/
def diagonalWeightAugmentation (S T : Set (Fin s)) (u : Fin n → ℤ)
    (hne : (diagonalStrip A S T u).Nonempty) :
    diagonalWeightCellComplex A M S T u ⟶ (ChainComplex.single₀ (ModuleCat k)).obj M :=
  augmentationOfHomologyZero (diagonalWeightCellComplex A M S T u)
    (diagonalWeightCellHomologyZeroIso A M S T u hne).hom

/-- The genuine weight complex resolves exactly one copy of its coefficient
module, via the genuine augmentation. -/
theorem diagonalWeightAugmentation_quasiIso (S T : Set (Fin s)) (u : Fin n → ℤ)
    (hne : (diagonalStrip A S T u).Nonempty) :
    QuasiIso (diagonalWeightAugmentation A M S T u hne) :=
  augmentationOfHomologyZero_quasiIso (diagonalWeightCellComplex A M S T u)
    (diagonalWeightCellHomologyZeroIso A M S T u hne)
    (fun q hq => diagonalWeightCellComplex_exactAt A M S T u hne hq)

/-- This augmentation is the ordinary singular augmentation after the
actual cellular comparison.  In particular it is not a freely chosen
rank-one identification. -/
theorem diagonalWeightAugmentation_f_zero (S T : Set (Fin s)) (u : Fin n → ℤ)
    (hne : (diagonalStrip A S T u).Nonempty) :
    (diagonalWeightAugmentation A M S T u hne).f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 M).hom =
        (diagonalWeightCellComplex A M S T u).cycles₀Iso.inv ≫
          (diagonalWeightCellComplex A M S T u).homologyπ 0 ≫
            (diagonalWeightCellularSingularIso A M S T u 0).hom ≫
              (TopCat.of (diagonalStripCarrier A S T u)).singularHomology₀ε M := by
  rw [diagonalWeightAugmentation, augmentationOfHomologyZero_f_zero,
    diagonalWeightCellHomologyZeroIso_hom]

end IntegralArrangement

end ToricPower
