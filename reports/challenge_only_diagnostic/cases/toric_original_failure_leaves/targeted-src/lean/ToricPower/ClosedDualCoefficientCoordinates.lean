module

public import ToricPower.DualLaurentDiagram
public import ToricPower.ClosedContravariantLabels
public import ToricPower.ArrangementChainFreeCoordinates

/-! # Full free coordinates of the supported inverse Laurent labels

The finite support-proof biproduct is identified with its genuine free
module on all allowed characters. Every contravariant incidence is the
original positive translation of the character.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s)) (b : Fin s → ℤ)
  (k : Type) [CommRing k]

local instance closedDualProofCoordinatesFinite (c : IncidenceObject A) :
    Fintype (PLift (closedIntegralRowsSupport A selected c)) := Fintype.ofFinite _

def closedDualCoefficientCoordinates (c : IncidenceObject A) :
    (Cellular.closedContravariantLabels (closedIntegralRowsSupport A selected)
      (closedIntegralRowsSupport_incidence A selected) (dualLaurentDiagram A S b k)).obj (op c) ≃ₗ[k]
        (ClosedDualLaurentCellIndex A selected S b c →₀ k) :=
  (ModuleCat.biproductIsoPi (fun _ : PLift (closedIntegralRowsSupport A selected c) =>
    (dualLaurentDiagram A S b k).obj (op c))).toLinearEquiv.trans
      (Finsupp.sigmaFinsuppLEquivPiFinsupp k).symm

theorem closedDualCoefficientCoordinates_inclusion_single (c : IncidenceObject A)
    (h : PLift (closedIntegralRowsSupport A selected c))
    (m : DualLaurentWeight A S b c) (r : k) :
    closedDualCoefficientCoordinates A selected S b k c
      (biproduct.ι (fun _ : PLift (closedIntegralRowsSupport A selected c) =>
        (dualLaurentDiagram A S b k).obj (op c)) h (Finsupp.single m r)) =
      Finsupp.single ⟨h,m⟩ r := by
  ext p
  rcases p with ⟨t,u⟩
  change (((ModuleCat.biproductIsoPi
    (fun _ : PLift (closedIntegralRowsSupport A selected c) =>
      ModuleCat.of k (DualLaurentWeight A S b c →₀ k))).hom
      (biproduct.ι (fun _ : PLift (closedIntegralRowsSupport A selected c) =>
        ModuleCat.of k (DualLaurentWeight A S b c →₀ k)) h (Finsupp.single m r))) t :
          DualLaurentWeight A S b c →₀ k) u = _
  erw [moduleBiproductIsoPi_hom_apply,← ModuleCat.comp_apply]
  have equal : h=t := Subsingleton.elim _ _
  subst t
  rw [biproduct.ι_π_self,ModuleCat.id_apply]
  have same : m = u ↔ (⟨h,m⟩ : ClosedDualLaurentCellIndex A selected S b c) = ⟨h,u⟩ :=
    ⟨fun e => congrArg (fun z => (⟨h,z⟩ : ClosedDualLaurentCellIndex A selected S b c)) e,
      fun e => congrArg (fun z : ClosedDualLaurentCellIndex A selected S b c => z.2) e⟩
  simp only [Finsupp.single_apply,same]
  split_ifs <;> rfl

/-- The whole supported coefficient diagram, including every arrow. -/
def closedDualCoefficientDiagramIso :
    Cellular.closedContravariantLabels (closedIntegralRowsSupport A selected)
      (closedIntegralRowsSupport_incidence A selected) (dualLaurentDiagram A S b k) ≅
        closedDualLaurentDiagram A selected S b k :=
  NatIso.ofComponents
    (fun c => (closedDualCoefficientCoordinates A selected S b k c.unop).toModuleIso)
    (by
      intro c d f
      apply biproduct.hom_ext'
      intro h
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext
      intro m r
      change closedDualCoefficientCoordinates A selected S b k d.unop
          (((Cellular.closedContravariantLabels (closedIntegralRowsSupport A selected)
            (closedIntegralRowsSupport_incidence A selected) (dualLaurentDiagram A S b k)).map f)
              (biproduct.ι (fun _ : PLift (closedIntegralRowsSupport A selected c.unop) =>
                (dualLaurentDiagram A S b k).obj c) h (Finsupp.single m r))) =
        (closedDualLaurentDiagram A selected S b k).map f
          (closedDualCoefficientCoordinates A selected S b k c.unop
            (biproduct.ι (fun _ : PLift (closedIntegralRowsSupport A selected c.unop) =>
              (dualLaurentDiagram A S b k).obj c) h (Finsupp.single m r)))
      erw [← ModuleCat.comp_apply,Cellular.closedContravariantLabels_map_inclusion,
        ModuleCat.comp_apply]
      change closedDualCoefficientCoordinates A selected S b k d.unop
          (biproduct.ι (fun _ : PLift (closedIntegralRowsSupport A selected d.unop) =>
            (dualLaurentDiagram A S b k).obj d) _
            (Finsupp.mapDomain (dualLaurentWeightMap A S b f.unop)
            (Finsupp.single m r))) = _
      rw [Finsupp.mapDomain_single,closedDualCoefficientCoordinates_inclusion_single,
        closedDualCoefficientCoordinates_inclusion_single]
      exact (closedDualLaurentDiagram_map_single A selected S b k f.unop ⟨h,m⟩ r).symm)

end ToricPower.IntegralArrangement

end
