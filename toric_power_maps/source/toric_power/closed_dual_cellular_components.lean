module

public import ToricPower.ClosedDualCellularDifferential
public import ToricPower.ClosedDualComponentCoordinates
public import ToricPower.ModuleChainDirectSum

/-! # Every closed affine component of the actual dual cellular complex

The original Laurent coefficient chains are isomorphic to the full
direct sum of the ordinary cellular chains of their closed convex
components. The comparison retains each original characteristic disk
and its boundary sign. Empty components remain in the indexing family.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s)) (b : Fin s → ℤ)
  (covered : ∀ {q : ℕ} (c : Cell (augmentedForms A) q), selected ⊆ c.val.2 →
    ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c-latticeLift a ∈
      arrangementZeroSlice (augmentedForms A) selected)
  (k : Type) [CommRing k]

local instance dualComponentsAmbientCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

abbrev ClosedDualComponentIndex (q : ℕ) :=
  Σ value : IntegralSliceValue A selected, ClosedDualComponentCell A selected S b value q

def closedDualLaurentComponentsEquiv (q : ℕ) :
    ClosedDualCellularIndex A selected S b q ≃ ClosedDualComponentIndex A selected S b q :=
  (closedDualLaurentCellEquiv A selected S b q).trans
    (closedDualCellComponentsEquiv A selected S b covered q)

def closedDualComponentsCoordinates (q : ℕ) :
    (closedDualCellularComplex A selected S b k).X q ≃ₗ[k]
      (ClosedDualComponentIndex A selected S b q →₀ k) :=
  (closedDualCellularCoordinates A selected S b k q).trans
    (Finsupp.mapDomain.linearEquiv k k (closedDualLaurentComponentsEquiv A selected S b covered q))

theorem closedDualComponentsCoordinates_apply (q : ℕ)
    (x : (closedDualCellularComplex A selected S b k).X q)
    (p : ClosedDualComponentIndex A selected S b q) :
    closedDualComponentsCoordinates A selected S b covered k q x p =
      closedDualCellularCoordinates A selected S b k q x
        ((closedDualLaurentComponentsEquiv A selected S b covered q).symm p) := by
  let e := closedDualLaurentComponentsEquiv A selected S b covered q
  change Finsupp.mapDomain e (closedDualCellularCoordinates A selected S b k q x) p = _
  have h := Finsupp.mapDomain_apply_of_injective e.injective
    (closedDualCellularCoordinates A selected S b k q x) (e.symm p)
  simpa only [Equiv.apply_symm_apply] using h

theorem closedDualComponentsCoordinates_symm_single (q : ℕ)
    (p : ClosedDualComponentIndex A selected S b q) (r : k) :
    (closedDualComponentsCoordinates A selected S b covered k q).symm (Finsupp.single p r) =
      (closedDualCellularCoordinates A selected S b k q).symm
        (Finsupp.single ((closedDualLaurentComponentsEquiv A selected S b covered q).symm p) r) := by
  apply (closedDualComponentsCoordinates A selected S b covered k q).injective
  rw [LinearEquiv.apply_symm_apply]
  symm
  change Finsupp.mapDomain (closedDualLaurentComponentsEquiv A selected S b covered q)
    ((closedDualCellularCoordinates A selected S b k q)
      ((closedDualCellularCoordinates A selected S b k q).symm _)) = _
  rw [LinearEquiv.apply_symm_apply,Finsupp.mapDomain_single,Equiv.apply_symm_apply]

theorem closedDualLaurentComponentsEquiv_symm_cell (q : ℕ)
    (p : ClosedDualComponentIndex A selected S b q) :
    closedDualLaurentCellEquiv A selected S b q
      ((closedDualLaurentComponentsEquiv A selected S b covered q).symm p) =
        (closedDualCellComponentsEquiv A selected S b covered q).symm p :=
  (closedDualLaurentCellEquiv A selected S b q).apply_symm_apply _

theorem closedDualComponentsCoordinates_d (q : ℕ)
    (p : ClosedDualComponentIndex A selected S b (q+1))
    (t : ClosedDualComponentIndex A selected S b q) (r : k) :
    closedDualComponentsCoordinates A selected S b covered k q
      ((closedDualCellularComplex A selected S b k).d (q+1) q
        ((closedDualComponentsCoordinates A selected S b covered k (q+1)).symm
          (Finsupp.single p r))) t =
      TauCeti.cellularIncidence (arrangementCarrier A) k q t.2.val p.2.val*r := by
  rw [closedDualComponentsCoordinates_symm_single,closedDualComponentsCoordinates_apply,
    closedDualCellularCoordinates_d_geometric,closedDualLaurentComponentsEquiv_symm_cell,
    closedDualLaurentComponentsEquiv_symm_cell]
  rfl

def closedDualComponentSum : ChainComplex (ModuleCat.{0} k) ℕ :=
  ModuleChainDirectSum.complex k (fun value => closedDualComponentComplex A selected S b value k)

def closedDualComponentSumCoordinates (q : ℕ) :
    (closedDualComponentSum A selected S b k).X q ≃ₗ[k]
      (ClosedDualComponentIndex A selected S b q →₀ k) :=
  ModuleChainDirectSum.coordinates k
    (fun value => closedDualComponentComplex A selected S b value k)
    (ClosedDualComponentCell A selected S b)
    (fun value => closedDualComponentCoordinates A selected S b value k) q

/-- The complete original dual coefficient chain complex, with all
integral components and no finiteness restriction on the character set. -/
def closedDualCellularComponentIso :
    closedDualCellularComplex A selected S b k ≅ closedDualComponentSum A selected S b k :=
  chainIsoOfFreeCoordinates k _ _ (ClosedDualComponentIndex A selected S b)
    (closedDualComponentsCoordinates A selected S b covered k)
    (closedDualComponentSumCoordinates A selected S b k) (by
      intro q p r
      rcases p with ⟨value,d⟩
      ext t
      rcases t with ⟨other,c⟩
      rw [closedDualComponentsCoordinates_d]
      by_cases same : other=value
      · subst other
        exact ((ModuleChainDirectSum.coordinates_d_single_self k
          (fun value => closedDualComponentComplex A selected S b value k)
          (ClosedDualComponentCell A selected S b)
          (fun value => closedDualComponentCoordinates A selected S b value k)
          (q+1) q value d c r).trans
            (closedDualComponentCoordinates_d_generator A selected S b k value q c d r)).symm
      · rw [closedDualComponent_incidence_of_ne A selected S b k q other value same,
          zero_mul]
        exact (ModuleChainDirectSum.coordinates_d_single_ne k
          (fun value => closedDualComponentComplex A selected S b value k)
          (ClosedDualComponentCell A selected S b)
          (fun value => closedDualComponentCoordinates A selected S b value k)
          (q+1) q value other same d c r).symm)

end ToricPower.IntegralArrangement

end
