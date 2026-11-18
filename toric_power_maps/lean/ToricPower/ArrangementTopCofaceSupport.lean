module

public import ToricPower.ArrangementTopCellClass
public import ToricPower.ArrangementCostalkSupportCoordinates

/-!
# The actual top-cell inclusion in a represented costalk

A top-dimensional cell contained in a bounded convex open support
computes that support by its original cochain extension. The map is a
quasi-isomorphism because it preserves the fixed ambient top class.
The final coordinate formula retains the literal incidence generator.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]

/-- The specified support extension preserves all cohomology, including
its original ambient top class. -/
theorem openSupportCochainExtension_quasiIso {U V : OpenCellSupport A}
    (h : U ≤ V)
    (convexU : Convex ℝ (U.val : Set (Fin n → ℝ)))
    (convexV : Convex ℝ (V.val : Set (Fin n → ℝ)))
    (nonemptyU : (U.val : Set (Fin n → ℝ)).Nonempty)
    (nonemptyV : (V.val : Set (Fin n → ℝ)).Nonempty)
    (boundedU : Bornology.IsBounded (U.val : Set (Fin n → ℝ)))
    (boundedV : Bornology.IsBounded (V.val : Set (Fin n → ℝ))) :
    QuasiIso (openSupportCochainExtension A k h) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases equal : q = n
  · subst q
    haveI : IsIso (HomologicalComplex.homologyMap
        (openSupportCochainExtension A k h) n ≫
        (openSupportCochainTopClassIso A k V convexV nonemptyV boundedV).hom) := by
      rw [openSupportCochainTopClassIso_natural A k h convexU convexV
        nonemptyU nonemptyV boundedU boundedV]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (openSupportCochainTopClassIso A k V convexV nonemptyV boundedV).hom
  · exact (openSupportCochainComplex_isZero_homology A k U convexU
      nonemptyU boundedU q equal).isIso
        (openSupportCochainComplex_isZero_homology A k V convexV
          nonemptyV boundedV q equal) _

variable (d : Cell (augmentedForms A) n)

/-- The original single characteristic-cell cochain, as a chain map. -/
def topCellCochainSingleMap :
    (HomologicalComplex.single (ModuleCat k) (.up ℕ) n).obj (ModuleCat.of k k) ⟶
      openSupportCochainComplex A k (topCellSupport A d) :=
  HomologicalComplex.mkHomFromSingle (topCellCochainTermIso A d k).inv
    (fun q relation => by
      have different : q ≠ n := by
        have successor : q = n + 1 := relation.symm
        omega
      exact (topCellCochain_isZero_X A d k q different).eq_of_tgt _ _)

instance topCellCochainSingleMap_isIso : IsIso (topCellCochainSingleMap A k d) := by
  haveI components (q : ℕ) : IsIso ((topCellCochainSingleMap A k d).f q) := by
    by_cases equal : q = n
    · subst q
      dsimp only [topCellCochainSingleMap]
      rw [HomologicalComplex.mkHomFromSingle_f]
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) n
        (ModuleCat.of k k) q equal).isIso
          (topCellCochain_isZero_X A d k q equal) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The original one-cell support is literally a single complex. -/
def topCellCochainSingleIso :
    (HomologicalComplex.single (ModuleCat k) (.up ℕ) n).obj (ModuleCat.of k k) ≅
      openSupportCochainComplex A k (topCellSupport A d) :=
  asIso (topCellCochainSingleMap A k d)

/-- The specified generator retains its original characteristic-cell
coefficient, without choosing a new orientation. -/
theorem topCellCochainSingleMap_coordinates (a : k) :
    openSupportCochainCoordinates A k (topCellSupport A d) n
      ((topCellCochainSingleMap A k d).f n
        ((HomologicalComplex.singleObjXSelf (.up ℕ) n (ModuleCat.of k k)).inv a)) =
      Finsupp.single (topCellSupport_index A d) a := by
  simp only [topCellCochainSingleMap, HomologicalComplex.mkHomFromSingle_f,
    ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  change openSupportCochainCoordinates A k (topCellSupport A d) n
      ((openSupportCochainCoordinates A k (topCellSupport A d) n).symm
        ((Finsupp.uniqueLinearEquiv k k (topCellSupport_index A d)).symm a)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable {U : OpenCellSupport A}

/-- Membership of the center includes the whole original open cell,
because the support is an actual union of arrangement cells. -/
theorem topCellSupport_le_of_center
    (member : cellCenter (augmentedForms A) d ∈ U.val) : topCellSupport A d ≤ U := by
  intro x hx
  exact (U.property d.val.1 d.val.2
    (cellCenter_mem (augmentedForms A) d) hx).mp member

variable (S : Set (Fin s)) (c : IncidenceObject A) (m : Fin n → ℤ)

/-- A genuine supported top coface supplies its entire original open cell. -/
def representedTopCofaceCell (p : RepresentableCostalkIndex A c S m n) :
    OpenSupportCell A (representedCostalkSupport A S c m) n :=
  (representedCostalkSupportIndexEquiv A S c m n).symm p

/-- The original characteristic-cell generator enters the represented
complex by the literal support map and the original coordinate comparisons. -/
def representedTopCofaceMap (p : RepresentableCostalkIndex A c S m n) :
    (HomologicalComplex.single (ModuleCat k) (.up ℕ) n).obj (ModuleCat.of k k) ⟶
      representedWeightCellularComplex A S c m k :=
  topCellCochainSingleMap A k (representedTopCofaceCell A S c m p).val ≫
    openSupportCochainExtension A k
      (topCellSupport_le_of_center A (representedTopCofaceCell A S c m p).val
        (representedTopCofaceCell A S c m p).property) ≫
      (representedCostalkOpenSupportIso A S c m k).inv ≫
        (representableCostalkCochainIso k A c S m).inv ≫
          (representedWeightCostalkComplexIso A S c m k).inv

/-- This particular top-cell inclusion, with all original incidence
signs retained, computes the complete represented character fiber. -/
theorem representedTopCofaceMap_quasiIso
    (p : RepresentableCostalkIndex A c S m n) :
    QuasiIso (representedTopCofaceMap A k S c m p) := by
  let d := representedTopCofaceCell A S c m p
  have inside := topCellSupport_le_of_center A d.val d.property
  haveI := openSupportCochainExtension_quasiIso A k inside
    (topCellSupport_convex A d.val) (costalkRegion_convex _ _ _ _)
    (topCellSupport_nonempty A d.val)
    ⟨cellCenter (augmentedForms A) d.val, d.property⟩
    (topCellSupport_bounded A d.val) (representedCostalkSupport_bounded A S c m)
  unfold representedTopCofaceMap
  infer_instance

end ToricPower.IntegralArrangement

end
