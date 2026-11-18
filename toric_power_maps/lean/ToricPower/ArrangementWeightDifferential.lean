module

public import ToricPower.ArrangementWeightDiagram
public import ToricPower.ArrangementCostalkCochainRepresentation

/-!
# The actual cellular differential in a character fiber

The matrix is derived from the original cellular cochain functor. A
nonzero incidence with translation `a` postcomposes the recorded source
incidence. Thus its coefficient between two given basis vectors can be
nonzero only when `a` is their translation difference. The resulting
matrix is exactly the independently constructed geometric costalk matrix.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A) (m : Fin n → ℤ) (k : Type) [Field k]

local notation "F" => representedWeightDiagram A S c m k
local notation "K" => representedWeightCellularComplex A S c m k
local notation "indices" => RepresentableCostalkIndex A c S m

/-- An actual summand of the cellular differential, evaluated in the
literal target incidence coordinate. -/
def representedWeightCellularSummand (q : ℕ) (j : indices (q + 1))
    (v : (K).X q) (p : NormalizedCell A q × (Fin n → ℤ)) : k :=
  Finsupp.lapply (R := k) (M := k)
    (⟨j.val.2, j.property⟩ : RepresentedWeightIndex A S c m ⟨q + 1, j.val.1⟩)
    ((cellularCoefficientHom A (F).op j.val.1 p.1 p.2).unop
      (arrangementCellularCochainProjection A k F q p.1 v))

theorem representedWeightCellularCoordinates_differential (q : ℕ)
    (v : (K).X q) (j : indices (q + 1)) :
    representedWeightCellularCoordinates A S c m k (q + 1)
      ((K).d q (q + 1) v) j =
      Finsupp.linearCombination k
        (representedWeightCellularSummand A S c m k q j v)
        (diagonalGlobalColumn k A q j.val.1) := by
  rw [representedWeightCellularCoordinates_apply]
  exact (cellularCochainFreeCoordinates_apply A k F
    (RepresentedWeightIndex A S c m) (fun _ => LinearEquiv.refl k _) (q + 1)
    ((K).d q (q + 1) v) j.val.1 ⟨j.val.2, j.property⟩).symm.trans
      (cellularCochainFreeCoordinates_differential A k F
        (RepresentedWeightIndex A S c m) (fun _ => LinearEquiv.refl k _) q v
        j.val.1 ⟨j.val.2, j.property⟩)

/-- On the support of the genuine geometric incidence column, the
actual coefficient map picks exactly the required translation difference. -/
theorem representedWeightCellularSummand_generator (q : ℕ)
    (i : indices q) (j : indices (q + 1)) (r : k)
    (p : NormalizedCell A q × (Fin n → ℤ))
    (supported : p ∈ (diagonalGlobalColumn k A q j.val.1).support) :
    representedWeightCellularSummand A S c m k q j
      (arrangementCellularCochainInclusion A k F q i.val.1
        (Finsupp.single ⟨i.val.2, i.property⟩ r)) p =
      (Pi.single (i.val.1, j.val.2.val - i.val.2.val) r :
        (NormalizedCell A q × (Fin n → ℤ)) → k) p := by
  rcases p with ⟨e, a⟩
  have incidence := incidenceTranslation_of_column_ne_zero A k q j.val.1 e a
    (Finsupp.mem_support_iff.mp supported)
  unfold representedWeightCellularSummand
  by_cases sameCell : e = i.val.1
  · subst e
    have projection := ConcreteCategory.congr_hom
      (arrangementCellularCochainInclusion_projection_self A k F q i.val.1)
      (Finsupp.single (⟨i.val.2, i.property⟩ :
        RepresentedWeightIndex A S c m ⟨q, i.val.1⟩) r)
    change arrangementCellularCochainProjection A k F q i.val.1
        (arrangementCellularCochainInclusion A k F q i.val.1
          (Finsupp.single ⟨i.val.2, i.property⟩ r)) = Finsupp.single ⟨i.val.2, i.property⟩ r
      at projection
    rw [projection, cellularCoefficientHom_op_unop A F j.val.1 i.val.1 a incidence]
    let h : (⟨q, i.val.1⟩ : IncidenceObject A) ⟶ ⟨q + 1, j.val.1⟩ := ⟨a, incidence⟩
    refine (congrArg (Finsupp.lapply (R := k) (M := k)
      (⟨j.val.2, j.property⟩ : RepresentedWeightIndex A S c m ⟨q + 1, j.val.1⟩))
        (representedWeightDiagram_map_single A S c m k h ⟨i.val.2, i.property⟩ r)).trans ?_
    change (Finsupp.single
      (representedWeightIndexMap A S c m h ⟨i.val.2, i.property⟩) r)
        (⟨j.val.2, j.property⟩ : RepresentedWeightIndex A S c m ⟨q + 1, j.val.1⟩) = _
    by_cases sameTranslation : a = j.val.2.val - i.val.2.val
    · have sameIndex : representedWeightIndexMap A S c m h ⟨i.val.2, i.property⟩ =
          (⟨j.val.2, j.property⟩ : RepresentedWeightIndex A S c m ⟨q + 1, j.val.1⟩) := by
        apply Subtype.ext
        apply Subtype.ext
        change i.val.2.val + a = j.val.2.val
        rw [sameTranslation]
        abel
      rw [sameIndex, Finsupp.single_eq_same, sameTranslation, Pi.single_eq_same]
    · have differentIndex :
          (⟨j.val.2, j.property⟩ : RepresentedWeightIndex A S c m ⟨q + 1, j.val.1⟩) ≠
            representedWeightIndexMap A S c m h ⟨i.val.2, i.property⟩ := by
        intro equal
        have translated := congrArg (fun f : RepresentedWeightIndex A S c m
          ⟨q + 1, j.val.1⟩ => f.val.val) equal
        change j.val.2.val = i.val.2.val + a at translated
        apply sameTranslation
        rw [translated]
        abel
      have differentPair : (i.val.1, a) ≠ (i.val.1, j.val.2.val - i.val.2.val) :=
        fun equal => sameTranslation (congrArg Prod.snd equal)
      exact (Finsupp.single_eq_of_ne differentIndex).trans
        (Pi.single_eq_of_ne (M := fun _ : NormalizedCell A q × (Fin n → ℤ) => k)
          differentPair r).symm
  · have projection := ConcreteCategory.congr_hom
      (arrangementCellularCochainInclusion_projection_ne A k F q i.val.1 e (Ne.symm sameCell))
      (Finsupp.single (⟨i.val.2, i.property⟩ :
        RepresentedWeightIndex A S c m ⟨q, i.val.1⟩) r)
    change arrangementCellularCochainProjection A k F q e
        (arrangementCellularCochainInclusion A k F q i.val.1
          (Finsupp.single ⟨i.val.2, i.property⟩ r)) = 0 at projection
    rw [projection, map_zero]
    change (0 : k) = _
    rw [Pi.single_eq_of_ne (fun equal => sameCell (congrArg Prod.fst equal))]

/-- Every actual differential matrix coefficient agrees with the
geometric costalk incidence, with its original orientation and sign. -/
theorem representedWeightCellularCoordinates_d_generator (q : ℕ)
    (i : indices q) (j : indices (q + 1)) (r : k) :
    representedWeightCellularCoordinates A S c m k (q + 1)
      ((K).d q (q + 1)
        ((representedWeightCellularCoordinates A S c m k q).symm
          (Finsupp.single i r))) j =
      representableCostalkIncidence A c S m k q i j * r := by
  rw [representedWeightCellularCoordinates_symm_single,
    representedWeightCellularCoordinates_differential]
  calc
    Finsupp.linearCombination k
        (representedWeightCellularSummand A S c m k q j
          (arrangementCellularCochainInclusion A k F q i.val.1
            (Finsupp.single ⟨i.val.2, i.property⟩ r)))
        (diagonalGlobalColumn k A q j.val.1) =
      Finsupp.linearCombination k
        (Pi.single (i.val.1, j.val.2.val - i.val.2.val) r)
        (diagonalGlobalColumn k A q j.val.1) := by
      simp only [Finsupp.linearCombination_apply]
      apply Finsupp.sum_congr
      intro p hp
      rw [representedWeightCellularSummand_generator A S c m k q i j r p hp]
    _ = diagonalGlobalColumn k A q j.val.1
        (i.val.1, j.val.2.val - i.val.2.val) • r :=
      by apply Finsupp.linearCombination_single_index
    _ = representableCostalkIncidence A c S m k q i j * r := by
      rw [diagonalGlobalColumn_apply]
      rfl

end ToricPower.IntegralArrangement
