module

public import ToricPower.ClosedDualSliceComponents
public import ToricPower.ClosedSliceComponentIncidence

/-! # Original cell and boundary coordinates in every closed dual component

The component index is its actual integral row level. Nonzero cellular
incidence cannot change that level. Within each component its inherited
boundary has exactly the original ambient characteristic-disk signs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (selected : Set (Fin s ⊕ Fin n))
  (S : Set (Fin s)) (b : Fin s → ℤ)

local instance dualCoordinatesAmbientCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A
local instance dualCoordinatesCW (value : IntegralSliceValue A selected) :
    CWComplex (closedDualComponentRegion A selected S b value) :=
  inferInstanceAs (CWComplex (closedDualComponentSubcomplex A selected S b value : Set (Fin n → ℝ)))

variable
  (covered : ∀ {q : ℕ} (c : Cell (augmentedForms A) q), selected ⊆ c.val.2 →
    ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c-latticeLift a ∈
      arrangementZeroSlice (augmentedForms A) selected)

def closedDualCellValue {q : ℕ} (c : ClosedDualSupportCell A selected S b q) :
    IntegralSliceValue A selected :=
  ⟨fun j => c.val.val.1 j.val,
    cellLevel_mem_integralSliceValues A selected c.val c.property.1
      (covered c.val c.property.1)⟩

def closedDualCellValueFiberEquiv (value : IntegralSliceValue A selected) (q : ℕ) :
    {c : ClosedDualSupportCell A selected S b q // closedDualCellValue A selected S b covered c=value} ≃
      ClosedDualComponentCell A selected S b value q where
  toFun c := ⟨c.val.val,⟨c.val.property.1,fun j =>
    congrArg (fun v : IntegralSliceValue A selected => v.val j) c.property⟩,c.val.property.2⟩
  invFun c := ⟨⟨c.val,c.property.1.1,c.property.2⟩,by
    apply Subtype.ext
    funext j
    exact c.property.1.2 j⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

def closedDualCellComponentsEquiv (q : ℕ) :
    ClosedDualSupportCell A selected S b q ≃
      Σ value : IntegralSliceValue A selected, ClosedDualComponentCell A selected S b value q :=
  (Equiv.sigmaFiberEquiv (closedDualCellValue A selected S b covered)).symm.trans
    (Equiv.sigmaCongrRight fun value => closedDualCellValueFiberEquiv A selected S b covered value q)

@[simp]
theorem closedDualCellComponentsEquiv_symm_val (q : ℕ)
    (value : IntegralSliceValue A selected) (c : ClosedDualComponentCell A selected S b value q) :
    ((closedDualCellComponentsEquiv A selected S b covered q).symm ⟨value,c⟩).val=c.val := rfl

variable (k : Type) [CommRing k]

omit covered in
theorem closedDualComponent_incidence_of_ne (q : ℕ)
    (value other : IntegralSliceValue A selected) (different : value ≠ other)
    (c : ClosedDualComponentCell A selected S b value q)
    (d : ClosedDualComponentCell A selected S b other (q+1)) :
    TauCeti.cellularIncidence (arrangementCarrier A) k q c.val d.val=0 := by
  by_contra nonzero
  apply different
  apply Subtype.ext
  funext j
  have source := cellCenter_mem (augmentedForms A) c.val j.val
  have target := point_mem_closedCell_of_incidence_ne_zero A k c.val d.val nonzero
    (cellCenter_mem (augmentedForms A) c.val) j.val
  rw [if_pos (c.property.1.1 j.property),c.property.1.2 j] at source
  rw [if_pos (d.property.1.1 j.property),d.property.1.2 j] at target
  exact_mod_cast source.symm.trans target

omit covered in
theorem closedDualComponentBasis_differential (value : IntegralSliceValue A selected)
    (q : ℕ) (c : ClosedDualComponentCell A selected S b value q)
    (d : ClosedDualComponentCell A selected S b value (q+1)) :
    (closedDualComponentBasis A selected S b value k q).repr
      (TauCeti.cellularDifferential (closedDualComponentRegion A selected S b value)
        (ModuleCat.of k k) q (closedDualComponentBasis A selected S b value k (q+1) d)) c =
      TauCeti.cellularIncidence (arrangementCarrier A) k q c.val d.val := by
  simp only [closedDualComponentBasis,Module.Basis.repr_reindex_apply,Module.Basis.reindex_apply]
  exact (TauCeti.cellularIncidence_def _ k q _ _).symm.trans
    (subcomplexCellularIncidence (closedDualComponentSubcomplex A selected S b value) k q _ _)

omit covered in
theorem closedDualComponentCoordinates_d_single (value : IntegralSliceValue A selected)
    (q : ℕ) (c : ClosedDualComponentCell A selected S b value q)
    (d : ClosedDualComponentCell A selected S b value (q+1)) :
    closedDualComponentCoordinates A selected S b value k q
      ((closedDualComponentComplex A selected S b value k).d (q+1) q
        ((closedDualComponentCoordinates A selected S b value k (q+1)).symm
          (Finsupp.single d 1))) c =
      TauCeti.cellularIncidence (arrangementCarrier A) k q c.val d.val := by
  let C := closedDualComponentRegion A selected S b value
  let e₁ := eqToIso (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) (q+1))
  let e₀ := eqToIso (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) q)
  have square : (closedDualComponentComplex A selected S b value k).d (q+1) q ≫ e₀.hom =
      e₁.hom ≫ TauCeti.cellularDifferential C (ModuleCat.of k k) q := by
    change (TauCeti.cellularChainComplex C (ModuleCat.of k k)).d (q+1) q ≫ _ = _
    rw [TauCeti.cellularChainComplex_d]
    simp [e₀,e₁]
  have eval := ConcreteCategory.congr_hom square
    ((closedDualComponentCoordinates A selected S b value k (q+1)).symm (Finsupp.single d 1))
  have generator : e₁.hom
      ((closedDualComponentCoordinates A selected S b value k (q+1)).symm (Finsupp.single d 1)) =
        closedDualComponentBasis A selected S b value k (q+1) d := by
    change e₁.hom (e₁.inv ((closedDualComponentBasis A selected S b value k (q+1)).repr.symm
      (Finsupp.single d 1))) = _
    rw [← ConcreteCategory.comp_apply,Iso.inv_hom_id,ConcreteCategory.id_apply,
      Module.Basis.repr_symm_apply,Finsupp.linearCombination_single,one_smul]
  simp only [ConcreteCategory.comp_apply] at eval
  change (closedDualComponentBasis A selected S b value k q).repr
    (e₀.hom ((closedDualComponentComplex A selected S b value k).d (q+1) q
      ((closedDualComponentCoordinates A selected S b value k (q+1)).symm
        (Finsupp.single d 1)))) c = _
  refine (congrArg (fun z => (closedDualComponentBasis A selected S b value k q).repr z c) eval).trans ?_
  exact (congrArg (fun z => (closedDualComponentBasis A selected S b value k q).repr
    (TauCeti.cellularDifferential C (ModuleCat.of k k) q z) c) generator).trans
      (closedDualComponentBasis_differential A selected S b k value q c d)

omit covered in
theorem closedDualComponentCoordinates_d_generator (value : IntegralSliceValue A selected)
    (q : ℕ) (c : ClosedDualComponentCell A selected S b value q)
    (d : ClosedDualComponentCell A selected S b value (q+1)) (r : k) :
    closedDualComponentCoordinates A selected S b value k q
      ((closedDualComponentComplex A selected S b value k).d (q+1) q
        ((closedDualComponentCoordinates A selected S b value k (q+1)).symm
          (Finsupp.single d r))) c =
      TauCeti.cellularIncidence (arrangementCarrier A) k q c.val d.val * r := by
  have single : Finsupp.single d r=r • (Finsupp.single d 1 : _ →₀ k) := by
    rw [Finsupp.smul_single,smul_eq_mul,mul_one]
  rw [single,map_smul,map_smul,map_smul,Finsupp.smul_apply,
    closedDualComponentCoordinates_d_single,smul_eq_mul,mul_comm]

end ToricPower.IntegralArrangement

end
