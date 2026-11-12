module

public import ToricPower.ClosedSliceCellularCoordinates

/-! # Every original closed-slice cellular differential coefficient

The actual copower map shifts a Laurent character by the recorded
incidence translation. Thus a matrix coefficient can survive only at
the difference of the two characters. Translation invariance identifies
that coefficient with the original incidence of the two actual
universal-cover cells, preserving its orientation and sign.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s))
  (k : Type) [Field k]

local notation "D" => Cellular.covariantCopowerDiagram k (reflectedLaurentDiagram A S k)
  (closedIntegralRowsDiagram A selected k)
local notation "K" => closedSliceCellularComplex A selected S k
local notation "I" => ClosedSliceLaurentIndex A selected S

local instance closedSliceDifferentialCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

def closedSliceCellularSummand (q : ℕ) (j : I (q+1)) (v : (K).X q)
    (p : NormalizedCell A q × (Fin n → ℤ)) : k :=
  closedSliceLaurentCellCoordinates A selected S k ⟨q+1,j.1.val⟩
    ((cellularCoefficientHom A (D).op j.1.val p.1 p.2).unop
      (arrangementCellularCochainProjection A k D q p.1 v))
    ⟨⟨j.1.property⟩,j.2⟩

theorem closedSliceCellularCoordinates_differential (q : ℕ)
    (v : (K).X q) (j : I (q+1)) :
    closedSliceCellularCoordinates A selected S k (q+1) ((K).d q (q+1) v) j =
      Finsupp.linearCombination k (closedSliceCellularSummand A selected S k q j v)
        (diagonalGlobalColumn k A q j.1.val) := by
  rw [closedSliceCellularCoordinates_apply]
  exact (cellularCochainFreeCoordinates_apply A k D
    (ClosedSliceCellLaurentIndex A selected S)
    (closedSliceLaurentCellCoordinates A selected S k) (q+1) ((K).d q (q+1) v)
    j.1.val ⟨⟨j.1.property⟩,j.2⟩).symm.trans
      (cellularCochainFreeCoordinates_differential A k D
        (ClosedSliceCellLaurentIndex A selected S)
        (closedSliceLaurentCellCoordinates A selected S k) q v
        j.1.val ⟨⟨j.1.property⟩,j.2⟩)

/-- On the genuine incidence-column support, exactly one translation
can carry the source Laurent monomial to the target monomial. -/
theorem closedSliceCellularSummand_generator (q : ℕ)
    (i : I q) (j : I (q+1)) (r : k)
    (p : NormalizedCell A q × (Fin n → ℤ))
    (supported : p ∈ (diagonalGlobalColumn k A q j.1.val).support) :
    closedSliceCellularSummand A selected S k q j
      (arrangementCellularCochainInclusion A k D q i.1.val
        ((closedSliceLaurentCellCoordinates A selected S k ⟨q,i.1.val⟩).symm
          (Finsupp.single ⟨⟨i.1.property⟩,i.2⟩ r))) p =
      (Pi.single (i.1.val,j.2.val-i.2.val) r :
        (NormalizedCell A q × (Fin n → ℤ)) → k) p := by
  rcases p with ⟨e,a⟩
  have incidence := incidenceTranslation_of_column_ne_zero A k q j.1.val e a
    (Finsupp.mem_support_iff.mp supported)
  let v := (closedSliceLaurentCellCoordinates A selected S k ⟨q,i.1.val⟩).symm
    (Finsupp.single ⟨⟨i.1.property⟩,i.2⟩ r)
  unfold closedSliceCellularSummand
  by_cases sameCell : e = i.1.val
  · subst e
    have projection := ConcreteCategory.congr_hom
      (arrangementCellularCochainInclusion_projection_self A k D q i.1.val) v
    change arrangementCellularCochainProjection A k D q i.1.val
      (arrangementCellularCochainInclusion A k D q i.1.val v) = v at projection
    change closedSliceLaurentCellCoordinates A selected S k ⟨q+1,j.1.val⟩
      ((cellularCoefficientHom A (D).op j.1.val i.1.val a).unop
        (arrangementCellularCochainProjection A k D q i.1.val
          (arrangementCellularCochainInclusion A k D q i.1.val v))) _ = _
    rw [projection,cellularCoefficientHom_op_unop A D j.1.val i.1.val a incidence]
    let h : (⟨q,i.1.val⟩ : IncidenceObject A) ⟶ ⟨q+1,j.1.val⟩ := ⟨a,incidence⟩
    refine (congrArg (fun z : ClosedSliceCellLaurentIndex A selected S ⟨q+1,j.1.val⟩ →₀ k =>
      z ⟨⟨j.1.property⟩,j.2⟩)
      (closedSliceLaurentCellMap_generator A selected S k h
        i.1.property j.1.property i.2 r)).trans ?_
    by_cases sameTranslation : a = j.2.val-i.2.val
    · have weight : reflectedLaurentWeightMap A S h i.2 = j.2 := by
        apply Subtype.ext
        change i.2.val+a = j.2.val
        rw [sameTranslation]
        abel
      rw [weight,Finsupp.single_eq_same,sameTranslation,Pi.single_eq_same]
    · have differentIndex :
          (⟨⟨j.1.property⟩,j.2⟩ : ClosedSliceCellLaurentIndex A selected S ⟨q+1,j.1.val⟩) ≠
            ⟨⟨j.1.property⟩,reflectedLaurentWeightMap A S h i.2⟩ := by
        intro equal
        have translated := congrArg
          (fun p : ClosedSliceCellLaurentIndex A selected S ⟨q+1,j.1.val⟩ => p.2.val) equal
        change j.2.val = i.2.val+a at translated
        apply sameTranslation
        rw [translated]
        abel
      have differentPair : (i.1.val,a) ≠ (i.1.val,j.2.val-i.2.val) :=
        fun equal => sameTranslation (congrArg Prod.snd equal)
      exact (Finsupp.single_eq_of_ne differentIndex).trans
        (Pi.single_eq_of_ne (M := fun _ : NormalizedCell A q × (Fin n → ℤ) => k)
          differentPair r).symm
  · have projection := ConcreteCategory.congr_hom
      (arrangementCellularCochainInclusion_projection_ne A k D q i.1.val e (Ne.symm sameCell)) v
    change arrangementCellularCochainProjection A k D q e
      (arrangementCellularCochainInclusion A k D q i.1.val v) = 0 at projection
    change closedSliceLaurentCellCoordinates A selected S k ⟨q+1,j.1.val⟩
      ((cellularCoefficientHom A (D).op j.1.val e a).unop
        (arrangementCellularCochainProjection A k D q e
          (arrangementCellularCochainInclusion A k D q i.1.val v))) _ = _
    rw [projection,map_zero,map_zero,Finsupp.zero_apply]
    rw [Pi.single_eq_of_ne (fun equal => sameCell (congrArg Prod.fst equal))]

theorem closedSliceCellularCoordinates_d_generator (q : ℕ)
    (i : I q) (j : I (q+1)) (r : k) :
    closedSliceCellularCoordinates A selected S k (q+1)
      ((K).d q (q+1)
        ((closedSliceCellularCoordinates A selected S k q).symm (Finsupp.single i r))) j =
      diagonalGlobalColumn k A q j.1.val (i.1.val,j.2.val-i.2.val) * r := by
  rw [closedSliceCellularCoordinates_symm_single,closedSliceCellularCoordinates_differential]
  calc
    Finsupp.linearCombination k _ (diagonalGlobalColumn k A q j.1.val) =
        Finsupp.linearCombination k (Pi.single (i.1.val,j.2.val-i.2.val) r)
          (diagonalGlobalColumn k A q j.1.val) := by
      simp only [Finsupp.linearCombination_apply]
      apply Finsupp.sum_congr
      intro p hp
      rw [closedSliceCellularSummand_generator A selected S k q i j r p hp]
    _ = diagonalGlobalColumn k A q j.1.val (i.1.val,j.2.val-i.2.val) • r :=
      by apply Finsupp.linearCombination_single_index
    _ = _ := rfl

/-- Translation identifies the complete actual matrix with the
original oriented incidence of the genuine universal cells. -/
theorem closedSliceCellularCoordinates_d_geometric (q : ℕ)
    (i : I q) (j : I (q+1)) (r : k) :
    closedSliceCellularCoordinates A selected S k (q+1)
      ((K).d q (q+1)
        ((closedSliceCellularCoordinates A selected S k q).symm (Finsupp.single i r))) j =
      TauCeti.cellularIncidence (arrangementCarrier A) k q
        (closedSliceLaurentCellEquiv A selected S q i).val
        (closedSliceLaurentCellEquiv A selected S (q+1) j).val * r := by
  rw [closedSliceCellularCoordinates_d_generator,diagonalGlobalColumn_apply]
  have translated := arrangement_cellularIncidence_translate A k j.2.val q
    (translateCell A (-i.2.val) i.1.val.val)
    (translateCell A (-j.2.val) j.1.val.val)
  simp only [translateCell_add,neg_add_cancel,translateCell_zero] at translated
  have difference : -i.2.val+j.2.val = j.2.val-i.2.val := by abel
  rw [difference] at translated
  exact congrArg (fun a : k => a*r) translated

end ToricPower.IntegralArrangement

end
