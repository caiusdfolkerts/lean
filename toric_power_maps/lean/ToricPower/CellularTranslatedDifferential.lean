module

public import ToricPower.CellularTranslatedWeights

/-!
# The actual differential on translating character bases

For two basis vectors, a differential contribution can occur only at
their exact character difference. The resulting coefficient is the
original periodic cellular incidence column at that displacement.
This is proved from the actual coefficient functor and cochain complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (allowed : IncidenceObject A → (Fin n → ℤ) → Prop)
  (stable : ∀ {c d : IncidenceObject A} (f : c ⟶ d) {a : Fin n → ℤ},
    allowed c a → allowed d (a + f.val))
  (k : Type) [CommRing k]

local notation "F" => translatedWeightDiagram A allowed stable k
local notation "K" => translatedWeightCellularComplex A allowed stable k
local notation "indices" => TranslatedCellIndex A allowed

def translatedWeightCellularSummand (q : ℕ) (j : indices (q + 1))
    (v : (K).X q) (p : NormalizedCell A q × (Fin n → ℤ)) : k :=
  Finsupp.lapply (R := k) (M := k) j.2
    ((cellularCoefficientHom A (F).op j.1 p.1 p.2).unop
      (arrangementCellularCochainProjection A k F q p.1 v))

theorem translatedWeightCellularCoordinates_differential (q : ℕ)
    (v : (K).X q) (j : indices (q + 1)) :
    translatedWeightCellularCoordinates A allowed stable k (q + 1)
      ((K).d q (q + 1) v) j =
      Finsupp.linearCombination k
        (translatedWeightCellularSummand A allowed stable k q j v)
        (diagonalGlobalColumn k A q j.1) :=
  cellularCochainFreeCoordinates_differential A k F (TranslatedWeightIndex A allowed)
    (fun _ => LinearEquiv.refl k _) q v j.1 j.2

/-- On a genuine supported incidence, the actual coefficient map
selects exactly the difference of the two character labels. -/
theorem translatedWeightCellularSummand_generator (q : ℕ)
    (i : indices q) (j : indices (q + 1)) (r : k)
    (p : NormalizedCell A q × (Fin n → ℤ))
    (supported : p ∈ (diagonalGlobalColumn k A q j.1).support) :
    translatedWeightCellularSummand A allowed stable k q j
      (arrangementCellularCochainInclusion A k F q i.1 (Finsupp.single i.2 r)) p =
      (Pi.single (i.1, j.2.val - i.2.val) r :
        (NormalizedCell A q × (Fin n → ℤ)) → k) p := by
  rcases p with ⟨e, a⟩
  have incidence := incidenceTranslation_of_column_ne_zero A k q j.1 e a
    (Finsupp.mem_support_iff.mp supported)
  unfold translatedWeightCellularSummand
  by_cases sameCell : e = i.1
  · subst e
    have projection := ConcreteCategory.congr_hom
      (arrangementCellularCochainInclusion_projection_self A k F q i.1)
      (Finsupp.single i.2 r)
    change arrangementCellularCochainProjection A k F q i.1
        (arrangementCellularCochainInclusion A k F q i.1
          (Finsupp.single i.2 r)) = Finsupp.single i.2 r at projection
    rw [projection, cellularCoefficientHom_op_unop A F j.1 i.1 a incidence]
    let h : (⟨q, i.1⟩ : IncidenceObject A) ⟶ ⟨q + 1, j.1⟩ := ⟨a, incidence⟩
    refine (congrArg (Finsupp.lapply (R := k) (M := k) j.2)
      (translatedWeightDiagram_map_single A allowed stable k h i.2 r)).trans ?_
    change (Finsupp.single (translatedWeightMap A allowed stable h i.2) r) j.2 = _
    by_cases sameTranslation : a = j.2.val - i.2.val
    · have sameIndex : translatedWeightMap A allowed stable h i.2 = j.2 := by
        apply Subtype.ext
        change i.2.val + a = j.2.val
        rw [sameTranslation]
        abel
      rw [sameIndex, Finsupp.single_eq_same, sameTranslation, Pi.single_eq_same]
    · have differentIndex : j.2 ≠ translatedWeightMap A allowed stable h i.2 := by
        intro equal
        have translated := congrArg Subtype.val equal
        change j.2.val = i.2.val + a at translated
        apply sameTranslation
        rw [translated]
        abel
      have differentPair : (i.1, a) ≠ (i.1, j.2.val - i.2.val) :=
        fun equal => sameTranslation (congrArg Prod.snd equal)
      exact (Finsupp.single_eq_of_ne differentIndex).trans
        (Pi.single_eq_of_ne (M := fun _ : NormalizedCell A q × (Fin n → ℤ) => k)
          differentPair r).symm
  · have projection := ConcreteCategory.congr_hom
      (arrangementCellularCochainInclusion_projection_ne A k F q i.1 e (Ne.symm sameCell))
      (Finsupp.single i.2 r)
    change arrangementCellularCochainProjection A k F q e
        (arrangementCellularCochainInclusion A k F q i.1
          (Finsupp.single i.2 r)) = 0 at projection
    rw [projection, map_zero]
    change (0 : k) = _
    rw [Pi.single_eq_of_ne (fun equal => sameCell (congrArg Prod.fst equal))]

/-- Every coefficient of the actual differential is the original
incidence at the exact translated character difference. -/
theorem translatedWeightCellularCoordinates_d_generator (q : ℕ)
    (i : indices q) (j : indices (q + 1)) (r : k) :
    translatedWeightCellularCoordinates A allowed stable k (q + 1)
      ((K).d q (q + 1)
        ((translatedWeightCellularCoordinates A allowed stable k q).symm
          (Finsupp.single i r))) j =
      diagonalGlobalColumn k A q j.1 (i.1, j.2.val - i.2.val) * r := by
  rw [translatedWeightCellularCoordinates_symm_single,
    translatedWeightCellularCoordinates_differential]
  calc
    Finsupp.linearCombination k
        (translatedWeightCellularSummand A allowed stable k q j
          (arrangementCellularCochainInclusion A k F q i.1 (Finsupp.single i.2 r)))
        (diagonalGlobalColumn k A q j.1) =
      Finsupp.linearCombination k
        (Pi.single (i.1, j.2.val - i.2.val) r)
        (diagonalGlobalColumn k A q j.1) := by
      simp only [Finsupp.linearCombination_apply]
      apply Finsupp.sum_congr
      intro p hp
      rw [translatedWeightCellularSummand_generator A allowed stable k q i j r p hp]
    _ = diagonalGlobalColumn k A q j.1 (i.1, j.2.val - i.2.val) * r := by
      apply Finsupp.linearCombination_single_index

end ToricPower.IntegralArrangement
