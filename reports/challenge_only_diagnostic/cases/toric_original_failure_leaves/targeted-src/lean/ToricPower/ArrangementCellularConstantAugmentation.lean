module

public import ToricPower.ArrangementCellularComplex
public import ToricPower.DiagonalAugmentationScalars
public import Mathlib.Algebra.Homology.Single

/-! # The original cellular augmentation from compatible coefficient maps

Every vertex is sent by its specified coefficient morphism. The actual
degree-one cellular columns sum to zero, so this is a map of the genuine
cellular chain complex, including all translated incidences.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical BigOperators

namespace ToricPower.IntegralArrangement

universe u v

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [CommRing k]
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear k B] [HasFiniteBiproducts B]
  (P : (IncidenceObject A)ᵒᵖ ⥤ B) (T : B)
  (α : P ⟶ (Functor.const (IncidenceObject A)ᵒᵖ).obj T)

local instance constantAugmentationCellFintype (q : ℕ) : Fintype (NormalizedCell A q) :=
  Fintype.ofFinite _

def cellularConstantAugmentationZero : arrangementCellularTerm A P 0 ⟶ T :=
  biproduct.desc (fun c : NormalizedCell A 0 => α.app (op ⟨0,c⟩))

@[reassoc]
theorem cellularConstantAugmentationZero_inclusion (c : NormalizedCell A 0) :
    biproduct.ι (fun c : NormalizedCell A 0 => P.obj (op ⟨0,c⟩)) c ≫
      cellularConstantAugmentationZero A P T α = α.app (op ⟨0,c⟩) :=
  biproduct.ι_desc _ _

theorem cellularConstantAugmentationZero_boundary :
    (arrangementCellularChainComplex A k P).d 1 0 ≫
      cellularConstantAugmentationZero A P T α = 0 := by
  rw [arrangementCellularChainComplex_d]
  apply biproduct.hom_ext'
  intro j
  rw [← Category.assoc, arrangementCellularBoundary_column, comp_zero]
  change (Linear.rightComp k (P.obj (op ⟨1,j⟩))
    (cellularConstantAugmentationZero A P T α))
      (Finsupp.linearCombination k _ (diagonalGlobalColumn k A 0 j)) = 0
  rw [Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
  calc
    _ = (diagonalGlobalColumn k A 0 j).sum
        (fun _ r => r • α.app (op ⟨1,j⟩)) := by
      apply Finsupp.sum_congr
      intro p hp
      congr 1
      change (cellularCoefficientHom A P j p.1 p.2 ≫
        biproduct.ι (fun i : NormalizedCell A 0 => P.obj (op ⟨0,i⟩)) p.1) ≫
        cellularConstantAugmentationZero A P T α = α.app (op ⟨1,j⟩)
      rw [Category.assoc, cellularConstantAugmentationZero_inclusion]
      have incidence := incidenceTranslation_of_column_ne_zero A k 0 j p.1 p.2
        (Finsupp.mem_support_iff.mp hp)
      simp only [cellularCoefficientHom, dif_pos incidence]
      rw [α.naturality]
      exact Category.comp_id _
    _ = ((diagonalGlobalColumn k A 0 j).sum (fun _ r => r)) • α.app (op ⟨1,j⟩) := by
      simp only [Finsupp.sum, Finset.sum_smul]
    _ = 0 := by rw [diagonalGlobalColumn_zero_sum, zero_smul]

/-- The actual chain augmentation determined by the compatible maps. -/
def cellularConstantAugmentation :
    arrangementCellularChainComplex A k P ⟶ (ChainComplex.single₀ B).obj T :=
  (ChainComplex.toSingle₀Equiv (arrangementCellularChainComplex A k P) T).symm
    ⟨cellularConstantAugmentationZero A P T α,
      cellularConstantAugmentationZero_boundary A k P T α⟩

@[simp]
theorem cellularConstantAugmentation_f_zero :
    (cellularConstantAugmentation A k P T α).f 0 =
      cellularConstantAugmentationZero A P T α :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

end ToricPower.IntegralArrangement

end
