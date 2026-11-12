module

public import ToricPower.ClosedDualLaurentLabels
public import ToricPower.ClosedSliceComponentIndex
public import ToricPower.ClosedSliceComponentCohomology
public import ToricPower.CWSubcomplexBoundary

/-! # All closed convex components of the dual slice

Each component is the actual affine integral level set, intersected
with the original closed monomial halfspaces. Its CW structure is the
restriction of the original periodic characteristic disks. The
augmentation sends every actual vertex to one and retains empty
components as zero coefficient modules.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (selected : Set (Fin s ⊕ Fin n))

def closedIntegralLevelSlice (value : selected → ℤ) : Set (Fin n → ℝ) :=
  {x | ∀ j : selected, augmentedForms A j.val x = (value j : ℝ)}

theorem closedIntegralLevelSlice_cell_iff (value : selected → ℤ)
    {q : ℕ} (c : Cell (augmentedForms A) q) {x : Fin n → ℝ}
    (inside : x ∈ cell (augmentedForms A) c.val.1 c.val.2) :
    x ∈ closedIntegralLevelSlice A selected value ↔
      selected ⊆ c.val.2 ∧ ∀ j : selected, c.val.1 j.val = value j := by
  constructor
  · intro point
    constructor
    · intro j member
      rw [← integralIndices_eq_of_mem_cell (augmentedForms A) _ _ inside]
      change augmentedForms A j x = (⌈augmentedForms A j x⌉ : ℝ)
      rw [point ⟨j,member⟩,Int.ceil_intCast]
    · intro j
      rw [← ceil_eq_of_mem_cell (augmentedForms A) _ _ inside j.val,
        point j,Int.ceil_intCast]
  · rintro ⟨active,level⟩ j
    have point := inside j.val
    rwa [if_pos (active j.property),level j] at point

theorem closedIntegralLevelSlice_cellwise (value : selected → ℤ) :
    Cellwise (augmentedForms A) (closedIntegralLevelSlice A selected value) := by
  intro e active x y hx hy
  let c : Cell (augmentedForms A) (Module.finrank ℝ (cellDirection (augmentedForms A) active)) :=
    ⟨⟨e,active⟩,⟨x,hx⟩,rfl⟩
  exact (closedIntegralLevelSlice_cell_iff A selected value c hx).trans
    (closedIntegralLevelSlice_cell_iff A selected value c hy).symm

theorem closedIntegralLevelSlice_isClosed (value : selected → ℤ) :
    IsClosed (closedIntegralLevelSlice A selected value) := by
  change IsClosed {x | ∀ j : selected, augmentedForms A j.val x = (value j : ℝ)}
  simp only [setOf_forall]
  exact isClosed_iInter fun j => isClosed_eq
    (augmentedForms A j.val).continuous_of_finiteDimensional continuous_const

theorem closedIntegralLevelSlice_convex (value : selected → ℤ) :
    Convex ℝ (closedIntegralLevelSlice A selected value) := by
  intro x hx y hy a b ha hb hab j
  change augmentedForms A j.val (a • x+b • y) = (value j : ℝ)
  rw [map_add,map_smul,map_smul,hx j,hy j]
  change a*(value j : ℝ)+b*(value j : ℝ)=(value j : ℝ)
  rw [← add_mul,hab,one_mul]

variable (S : Set (Fin s)) (b : Fin s → ℤ) (value : IntegralSliceValue A selected)

def closedDualComponentRegion : Set (Fin n → ℝ) :=
  closedIntegralLevelSlice A selected value.val ∩
    closedLowerWeightRegion A S (fun r => -b r)

theorem closedDualComponentRegion_convex :
    Convex ℝ (closedDualComponentRegion A selected S b value) :=
  (closedIntegralLevelSlice_convex A selected value.val).inter
    (closedLowerWeightRegion_convex A S (fun r => -b r))

local instance dualComponentAmbientCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

def closedDualComponentSubcomplex : CWComplex.Subcomplex (arrangementCarrier A) :=
  periodicCellwiseSubcomplex A (closedDualComponentRegion A selected S b value)
    ((closedIntegralLevelSlice_isClosed A selected value.val).inter
      (closedLowerWeightRegion_isClosed A S (fun r => -b r)))
    ((closedIntegralLevelSlice_cellwise A selected value.val).inter
      (closedLowerWeightRegion_cellwise A S (fun r => -b r)))

local instance dualComponentCW : CWComplex (closedDualComponentRegion A selected S b value) :=
  inferInstanceAs (CWComplex (closedDualComponentSubcomplex A selected S b value : Set (Fin n → ℝ)))

def ClosedDualComponentCell (q : ℕ) :=
  {c : Cell (augmentedForms A) q //
    (selected ⊆ c.val.2 ∧ ∀ j : selected, c.val.1 j.val=value.val j) ∧
      cellCenter (augmentedForms A) c ∈ closedLowerWeightRegion A S (fun r => -b r)}

def closedDualComponentCellEquiv (q : ℕ) :
    RelCWComplex.cell (closedDualComponentRegion A selected S b value) q ≃
      ClosedDualComponentCell A selected S b value q :=
  Equiv.subtypeEquivRight fun c => and_congr
    (closedIntegralLevelSlice_cell_iff A selected value.val c (cellCenter_mem _ c)) Iff.rfl

variable (k : Type) [CommRing k]

def closedDualComponentComplex : ChainComplex (ModuleCat.{0} k) ℕ :=
  TauCeti.cellularChainComplex (closedDualComponentRegion A selected S b value) (ModuleCat.of k k)

def closedDualComponentBasis (q : ℕ) :
    Module.Basis (ClosedDualComponentCell A selected S b value q) k
      (TauCeti.cellularChainGroup (closedDualComponentRegion A selected S b value)
        (ModuleCat.of k k) q : ModuleCat k) :=
  (TauCeti.cellularChainBasis (closedDualComponentRegion A selected S b value) k q).reindex
    (closedDualComponentCellEquiv A selected S b value q)

def closedDualComponentCoordinates (q : ℕ) :
    (closedDualComponentComplex A selected S b value k).X q ≃ₗ[k]
      (ClosedDualComponentCell A selected S b value q →₀ k) :=
  (eqToIso (TauCeti.cellularChainComplex_X (closedDualComponentRegion A selected S b value)
    (ModuleCat.of k k) q)).toLinearEquiv.trans
      (closedDualComponentBasis A selected S b value k q).repr

theorem closedDualComponent_isZero_X_of_empty
    (empty : ¬ (closedDualComponentRegion A selected S b value).Nonempty) (q : ℕ) :
    IsZero ((closedDualComponentComplex A selected S b value k).X q) := by
  letI : IsEmpty (ClosedDualComponentCell A selected S b value q) :=
    ⟨fun c => empty ⟨cellCenter (augmentedForms A) c.val,
      (closedIntegralLevelSlice_cell_iff A selected value.val c.val
        (cellCenter_mem _ c.val)).mpr c.property.1,c.property.2⟩⟩
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of k (ClosedDualComponentCell A selected S b value q →₀ k))).of_iso
      (closedDualComponentCoordinates A selected S b value k q).toModuleIso

def closedDualComponentZeroIso :
    (closedDualComponentComplex A selected S b value k).homology 0 ≅
      ModuleCat.of k (MorseCoefficients.openScalar k
        (¬ (closedDualComponentRegion A selected S b value).Nonempty)) := by
  by_cases present : (closedDualComponentRegion A selected S b value).Nonempty
  · letI := (closedDualComponentRegion_convex A selected S b value).contractibleSpace present
    exact contractibleCellularHomologyZeroIso (ModuleCat.of k k)
      (closedDualComponentRegion A selected S b value) ⟨present.choose,present.choose_spec⟩ ≪≫
        (MorseCoefficients.openScalarPresentIso k present).symm
  · exact IsZero.iso (ShortComplex.isZero_homology_of_isZero_X₂ _
      (closedDualComponent_isZero_X_of_empty A selected S b value k present 0))
        (MorseCoefficients.openScalarAbsent_isZero k present)

theorem closedDualComponent_exactAt (q : ℕ) (positive : q ≠ 0) :
    (closedDualComponentComplex A selected S b value k).ExactAt q := by
  by_cases present : (closedDualComponentRegion A selected S b value).Nonempty
  · letI := (closedDualComponentRegion_convex A selected S b value).contractibleSpace present
    exact contractibleCellular_exactAt (ModuleCat.of k k)
      (closedDualComponentRegion A selected S b value) q positive
  · exact HomologicalComplex.ExactAt.of_isZero
      (closedDualComponent_isZero_X_of_empty A selected S b value k present q)

/-- Every component has its original augmentation, including the
empty component with its literal zero coefficient module. -/
def closedDualComponentAugmentation :
    closedDualComponentComplex A selected S b value k ⟶
      (ChainComplex.single₀ (ModuleCat k)).obj
        (ModuleCat.of k (MorseCoefficients.openScalar k
          (¬ (closedDualComponentRegion A selected S b value).Nonempty))) :=
  augmentationOfHomologyZero _ (closedDualComponentZeroIso A selected S b value k).hom

theorem closedDualComponentAugmentation_quasiIso :
    QuasiIso (closedDualComponentAugmentation A selected S b value k) :=
  augmentationOfHomologyZero_quasiIso _ (closedDualComponentZeroIso A selected S b value k)
    (closedDualComponent_exactAt A selected S b value k)

end ToricPower.IntegralArrangement

end
