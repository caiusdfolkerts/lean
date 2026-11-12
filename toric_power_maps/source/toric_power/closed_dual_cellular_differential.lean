module

public import ToricPower.ClosedDualLaurentLabels
public import ToricPower.ArrangementChainFreeCoordinates

/-! # The original dual closed-slice differential in every character

The contravariant Cartier map adds the incidence character. Thus the
unique surviving translation is the low-cell character minus the
high-cell character. The resulting scalar is precisely the original
oriented boundary between their positively translated universal cells.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s)) (b : Fin s → ℤ)
  (k : Type) [CommRing k]

local instance dualDifferentialCellsFintype (q : ℕ) : Fintype (NormalizedCell A q) :=
  Fintype.ofFinite _
local instance dualDifferentialAmbientCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

abbrev ClosedDualCellularIndex (q : ℕ) :=
  Σ c : NormalizedCell A q, ClosedDualLaurentCellIndex A selected S b ⟨q,c⟩

def closedDualCellularComplex : ChainComplex (ModuleCat.{0} k) ℕ :=
  arrangementCellularChainComplex A k (closedDualLaurentDiagram A selected S b k)

def closedDualCellularCoordinates (q : ℕ) :
    (closedDualCellularComplex A selected S b k).X q ≃ₗ[k]
      (ClosedDualCellularIndex A selected S b q →₀ k) :=
  cellularChainFreeCoordinates A k (closedDualLaurentDiagram A selected S b k)
    (ClosedDualLaurentCellIndex A selected S b) (fun _ => LinearEquiv.refl k _) q

def closedDualColumnSummand (q : ℕ)
    (j : ClosedDualCellularIndex A selected S b (q+1))
    (i : ClosedDualCellularIndex A selected S b q) (r : k)
    (p : NormalizedCell A q × (Fin n → ℤ)) : k :=
  (show ClosedDualLaurentCellIndex A selected S b ⟨q,i.1⟩ →₀ k from
    (biproduct.π (fun t : NormalizedCell A q =>
    (closedDualLaurentDiagram A selected S b k).obj (op ⟨q,t⟩)) i.1
      (biproduct.ι (fun t : NormalizedCell A q =>
        (closedDualLaurentDiagram A selected S b k).obj (op ⟨q,t⟩)) p.1
          (cellularCoefficientHom A (closedDualLaurentDiagram A selected S b k)
            j.1 p.1 p.2 (Finsupp.single j.2 r))))) i.2

theorem closedDualColumnSummand_generator (q : ℕ)
    (j : ClosedDualCellularIndex A selected S b (q+1))
    (i : ClosedDualCellularIndex A selected S b q) (r : k)
    (p : NormalizedCell A q × (Fin n → ℤ))
    (supported : p ∈ (diagonalGlobalColumn k A q j.1).support) :
    closedDualColumnSummand A selected S b k q j i r p =
      (Pi.single (i.1,i.2.2.val-j.2.2.val) r :
        (NormalizedCell A q × (Fin n → ℤ)) → k) p := by
  rcases p with ⟨e,a⟩
  have incidence := incidenceTranslation_of_column_ne_zero A k q j.1 e a
    (Finsupp.mem_support_iff.mp supported)
  unfold closedDualColumnSummand
  by_cases sameCell : e=i.1
  · subst e
    rw [← ModuleCat.comp_apply,biproduct.ι_π_self,ModuleCat.id_apply,
      cellularCoefficientHom,dif_pos incidence,closedDualLaurentDiagram_map_single]
    let f : (⟨q,i.1⟩ : IncidenceObject A) ⟶ ⟨q+1,j.1⟩ := ⟨a,incidence⟩
    change Finsupp.single (closedDualLaurentIndexMap A selected S b f j.2) r i.2 = _
    by_cases sameTranslation : a=i.2.2.val-j.2.2.val
    · have index : closedDualLaurentIndexMap A selected S b f j.2=i.2 := by
        apply Sigma.ext (Subsingleton.elim _ _)
        apply heq_of_eq
        apply Subtype.ext
        change j.2.2.val+a=i.2.2.val
        rw [sameTranslation]
        abel
      rw [index,Finsupp.single_eq_same,sameTranslation,Pi.single_eq_same]
    · have differentIndex : i.2 ≠ closedDualLaurentIndexMap A selected S b f j.2 := by
        intro equal
        have value := congrArg
          (fun t : ClosedDualLaurentCellIndex A selected S b ⟨q,i.1⟩ => t.2.val) equal
        change i.2.2.val=j.2.2.val+a at value
        apply sameTranslation
        rw [value]
        abel
      have differentPair : (i.1,a) ≠ (i.1,i.2.2.val-j.2.2.val) :=
        fun equal => sameTranslation (congrArg Prod.snd equal)
      exact (Finsupp.single_eq_of_ne differentIndex).trans
        (Pi.single_eq_of_ne (M := fun _ : NormalizedCell A q × (Fin n → ℤ) => k)
          differentPair r).symm
  · rw [← ModuleCat.comp_apply,biproduct.ι_π_ne _ sameCell]
    change (0 : ClosedDualLaurentCellIndex A selected S b ⟨q,i.1⟩ →₀ k) i.2 = _
    rw [Finsupp.zero_apply,Pi.single_eq_of_ne (fun equal => sameCell (congrArg Prod.fst equal))]

theorem closedDualCellularCoordinates_d_generator (q : ℕ)
    (j : ClosedDualCellularIndex A selected S b (q+1))
    (i : ClosedDualCellularIndex A selected S b q) (r : k) :
    closedDualCellularCoordinates A selected S b k q
      ((closedDualCellularComplex A selected S b k).d (q+1) q
        ((closedDualCellularCoordinates A selected S b k (q+1)).symm
          (Finsupp.single j r))) i =
      diagonalGlobalColumn k A q j.1 (i.1,i.2.2.val-j.2.2.val)*r := by
  change cellularChainFreeCoordinates A k (closedDualLaurentDiagram A selected S b k)
    (ClosedDualLaurentCellIndex A selected S b) (fun _ => LinearEquiv.refl k _) q
      ((arrangementCellularChainComplex A k (closedDualLaurentDiagram A selected S b k)).d
        (q+1) q
        ((cellularChainFreeCoordinates A k (closedDualLaurentDiagram A selected S b k)
          (ClosedDualLaurentCellIndex A selected S b) (fun _ => LinearEquiv.refl k _) (q+1)).symm
            (Finsupp.single j r))) i = _
  rw [cellularChainFreeCoordinates_d_generator]
  change Finsupp.linearCombination k (closedDualColumnSummand A selected S b k q j i r)
    (diagonalGlobalColumn k A q j.1) = _
  calc
    _ = Finsupp.linearCombination k (Pi.single (i.1,i.2.2.val-j.2.2.val) r)
        (diagonalGlobalColumn k A q j.1) := by
      simp only [Finsupp.linearCombination_apply]
      apply Finsupp.sum_congr
      intro p hp
      rw [closedDualColumnSummand_generator A selected S b k q j i r p hp]
    _ = _ := Finsupp.linearCombination_single_index _ _ _ r
      (i.1,i.2.2.val-j.2.2.val) (diagonalGlobalColumn k A q j.1)

theorem closedDualCellularCoordinates_d_geometric (q : ℕ)
    (j : ClosedDualCellularIndex A selected S b (q+1))
    (i : ClosedDualCellularIndex A selected S b q) (r : k) :
    closedDualCellularCoordinates A selected S b k q
      ((closedDualCellularComplex A selected S b k).d (q+1) q
        ((closedDualCellularCoordinates A selected S b k (q+1)).symm
          (Finsupp.single j r))) i =
      TauCeti.cellularIncidence (arrangementCarrier A) k q
        (closedDualLaurentCellEquiv A selected S b q i).val
        (closedDualLaurentCellEquiv A selected S b (q+1) j).val*r := by
  rw [closedDualCellularCoordinates_d_generator,diagonalGlobalColumn_apply]
  have translated := arrangement_cellularIncidence_translate A k (-j.2.2.val) q
    (translateCell A i.2.2.val i.1.val) (translateCell A j.2.2.val j.1.val)
  simp only [translateCell_add,add_neg_cancel,translateCell_zero] at translated
  have difference : i.2.2.val+ -j.2.2.val=i.2.2.val-j.2.2.val := by abel
  rw [difference] at translated
  exact congrArg (fun z : k => z*r) translated

end ToricPower.IntegralArrangement

end
