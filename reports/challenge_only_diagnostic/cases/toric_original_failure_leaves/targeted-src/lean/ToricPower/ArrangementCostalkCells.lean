module

public import ToricPower.ArrangementWeightedIncidence
public import ToricPower.ArrangementUniversalCells
public import ToricPower.DiagonalCellWeights

/-!
# The literal cells in a representable costalk

The cells in an open star are precisely its actual cofaces in the
universal cover. After normalizing a coface, its lattice displacement is
the negative of the recorded incidence translation. Its monomial
inequality is exactly the section inequality of the reflected dual
Cartier label, with weight shifted by that incidence.

These statements retain equality walls and the extra coordinate
hyperplanes: only the selected original rows impose section conditions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)

/-- Membership in the actual open star is exactly containment of the
whole closed face, not merely a relation between chosen centers. -/
theorem cellCenter_mem_localStar_iff {p q : ℕ}
    (c : Cell (augmentedForms matrix) p) (d : Cell (augmentedForms matrix) q) :
    cellCenter (augmentedForms matrix) d ∈
        localStar (augmentedForms matrix) (cellCenter (augmentedForms matrix) c) ↔
      closedCell (augmentedForms matrix) c.val.1 c.val.2 ⊆
        closedCell (augmentedForms matrix) d.val.1 d.val.2 := by
  rw [mem_localStar_iff_point_mem_closedCell, cellCenter_ceilingVector,
    cellCenter_integralIndices]
  constructor
  · intro contained
    simpa only [cellCenter_ceilingVector, cellCenter_integralIndices] using
      closedCell_of_point_subset (augmentedForms matrix) d.val.1 d.val.2 contained
  · intro contained
    exact contained (cell_subset_closedCell _ _ _ (cellCenter_mem _ c))

@[simp]
theorem latticeLift_neg (a : Fin n → ℤ) : latticeLift (-a) = -latticeLift a := by
  funext j
  simp only [latticeLift, Pi.neg_apply, Int.cast_neg]

/-- An ambient point lies in a translated closed cell exactly when its
literal inverse translate lies in the original closed cell. -/
theorem mem_translatedClosedCell_iff {q : ℕ} (d : Cell (augmentedForms matrix) q)
    (a : Fin n → ℤ) (x : Fin n → ℝ) :
    x ∈ closedCell (augmentedForms matrix) (translateCell matrix a d).val.1
        (translateCell matrix a d).val.2 ↔
      x - latticeLift a ∈ closedCell (augmentedForms matrix) d.val.1 d.val.2 := by
  simpa only [translateCell, sub_add_cancel] using
    add_mem_closedCell_iff (augmentedForms matrix) d.val.1
      (augmentedLatticePairing matrix a) d.val.2 (latticeLift a)
      (augmentedForms_latticeLift matrix a) (x - latticeLift a)

/-- A normalized translated coface gives precisely the recorded
incidence in the finite quotient category. -/
theorem translatedCell_star_iff_incidence (c : IncidenceObject matrix)
    {q : ℕ} (d : NormalizedCell matrix q) (a : Fin n → ℤ) :
    cellCenter (augmentedForms matrix) (translateCell matrix (-a) d.val) ∈
        localStar (augmentedForms matrix) (incidenceCellCenter matrix c) ↔
      ∀ x ∈ incidenceClosedCell matrix c,
        x + latticeLift a ∈ incidenceClosedCell matrix ⟨q, d⟩ := by
  change cellCenter (augmentedForms matrix) (translateCell matrix (-a) d.val) ∈
      localStar (augmentedForms matrix) (cellCenter (augmentedForms matrix) c.2.val) ↔ _
  rw [cellCenter_mem_localStar_iff]
  constructor <;> intro h x hx
  · have shifted := (mem_translatedClosedCell_iff matrix d.val (-a) x).mp (h hx)
    simpa only [latticeLift_neg, sub_neg_eq_add, incidenceClosedCell] using shifted
  · apply (mem_translatedClosedCell_iff matrix d.val (-a) x).mpr
    simpa only [latticeLift_neg, sub_neg_eq_add, incidenceClosedCell] using h x hx

/-- The strict support inequality has the exact reflected ceiling
coefficient, including points on an integral wall. -/
theorem cellCenter_openWeight_iff (S : Set (Fin s)) (m : Fin n → ℤ)
    {q : ℕ} (d : Cell (augmentedForms matrix) q) :
    cellCenter (augmentedForms matrix) d ∈
        openWeightRegion (augmentedForms matrix) (Sum.inl '' S)
          (augmentedLatticePairing matrix m) ↔
      ∀ i ∈ S, 0 ≤ rayPairing matrix m i + reflectedCeiling matrix d i := by
  constructor
  · intro h i hi
    have bound := h (.inl i) ⟨i, hi, rfl⟩
    change integralRowForm matrix i (cellCenter (augmentedForms matrix) d) <
      (rayPairing matrix m i : ℝ) + 1 at bound
    rw [reflectedCeiling_eq_ceil matrix d (cellCenter_mem _ d) i]
    have lower : -rayPairing matrix m i ≤
        ⌈-integralRowForm matrix i (cellCenter (augmentedForms matrix) d)⌉ := by
      rw [Int.le_ceil_iff, Int.cast_neg]
      linarith
    omega
  · intro h j hj
    obtain ⟨i, hi, rfl⟩ := hj
    have bound := h i hi
    rw [reflectedCeiling_eq_ceil matrix d (cellCenter_mem _ d) i] at bound
    have lower : -rayPairing matrix m i ≤
        ⌈-integralRowForm matrix i (cellCenter (augmentedForms matrix) d)⌉ := by omega
    rw [Int.le_ceil_iff, Int.cast_neg] at lower
    change integralRowForm matrix i (cellCenter (augmentedForms matrix) d) <
      (rayPairing matrix m i : ℝ) + 1
    linarith

/-- The actual cells in each costalk are the actual normalized cofaces
and the actual monomial sections of `Q(d)`, with weight `m+a`. -/
theorem translatedCell_costalk_iff (c : IncidenceObject matrix)
    (S : Set (Fin s)) (m : Fin n → ℤ) {q : ℕ}
    (d : NormalizedCell matrix q) (a : Fin n → ℤ) :
    cellCenter (augmentedForms matrix) (translateCell matrix (-a) d.val) ∈
        costalkRegion (augmentedForms matrix) (Sum.inl '' S)
          (augmentedLatticePairing matrix m) (incidenceCellCenter matrix c) ↔
      (∀ x ∈ incidenceClosedCell matrix c,
        x + latticeLift a ∈ incidenceClosedCell matrix ⟨q, d⟩) ∧
      ∀ i ∈ S, 0 ≤ rayPairing matrix (m + a) i + reflectedCeiling matrix d.val i := by
  change (_ ∧ _) ↔ _
  rw [translatedCell_star_iff_incidence, cellCenter_openWeight_iff]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  have pairingAdd : rayPairing matrix (m + a) i =
      rayPairing matrix m i + rayPairing matrix a i := by
    simp [rayPairing, mul_add, Finset.sum_add_distrib]
  rw [reflectedCeiling_translate, pairingAdd]
  have negative : rayPairing matrix (-a) i = -rayPairing matrix a i := by
    simp [rayPairing, mul_neg, Finset.sum_neg_distrib]
  rw [negative]
  omega

/-- The signed orbit coordinates use the actual incidence translation:
the lifted coface is the normalized cell translated by its negative. -/
def signedCellOrbitEquiv (q : ℕ) :
    Cell (augmentedForms matrix) q ≃ NormalizedCell matrix q × (Fin n → ℤ) :=
  (cellOrbitEquiv matrix q).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.neg (Fin n → ℤ)))

@[simp]
theorem signedCellOrbitEquiv_symm_apply (q : ℕ)
    (d : NormalizedCell matrix q) (a : Fin n → ℤ) :
    (signedCellOrbitEquiv matrix q).symm (d, a) = translateCell matrix (-a) d.val := rfl

/-- The exact section condition for a normalized coface and its actual
incidence. The full character is `m+a`, with no chosen bounded range. -/
def RepresentableCostalkIndex (c : IncidenceObject matrix)
    (S : Set (Fin s)) (m : Fin n → ℤ) (q : ℕ) :=
  {p : Σ d : NormalizedCell matrix q, c ⟶ (⟨q, d⟩ : IncidenceObject matrix) //
    ∀ i ∈ S, 0 ≤ rayPairing matrix (m + p.2.val) i + reflectedCeiling matrix p.1.val i}

/-- The geometric costalk cell set is exactly the actual representable
incidence basis with its actual Cartier monomial conditions. -/
def costalkCellIndexEquiv (c : IncidenceObject matrix)
    (S : Set (Fin s)) (m : Fin n → ℤ) (q : ℕ) :
    {d : Cell (augmentedForms matrix) q //
      cellCenter (augmentedForms matrix) d ∈
        costalkRegion (augmentedForms matrix) (Sum.inl '' S)
          (augmentedLatticePairing matrix m) (incidenceCellCenter matrix c)} ≃
      RepresentableCostalkIndex matrix c S m q := by
  let e : {p : NormalizedCell matrix q × (Fin n → ℤ) //
      (∀ x ∈ incidenceClosedCell matrix c,
        x + latticeLift p.2 ∈ incidenceClosedCell matrix ⟨q, p.1⟩) ∧
      ∀ i ∈ S, 0 ≤ rayPairing matrix (m + p.2) i + reflectedCeiling matrix p.1.val i} ≃
      {d : Cell (augmentedForms matrix) q //
        cellCenter (augmentedForms matrix) d ∈
          costalkRegion (augmentedForms matrix) (Sum.inl '' S)
            (augmentedLatticePairing matrix m) (incidenceCellCenter matrix c)} :=
    (signedCellOrbitEquiv matrix q).symm.subtypeEquiv (fun p =>
      (translatedCell_costalk_iff matrix c S m p.1 p.2).symm)
  refine e.symm.trans
    { toFun := fun p => ⟨⟨p.val.1, ⟨p.val.2, p.property.1⟩⟩, p.property.2⟩
      invFun := fun p => ⟨(p.val.1, p.val.2.val), p.val.2.property, p.property⟩
      left_inv := fun p => by cases p; rfl
      right_inv := fun p => by cases p with | mk p hp => cases p; rfl }

local instance costalkCellsPeriodicCW : CWComplex (arrangementCarrier matrix) :=
  periodicArrangementCWComplex matrix

/-- The cells of the genuine relative CW pair retain exactly the cells
whose centers lie in the actual open support. -/
def periodicCostalkCellSupportEquiv (selected : Set (Fin s ⊕ Fin n))
    (weight : Fin s ⊕ Fin n → ℤ) (x : Fin n → ℝ) (q : ℕ) :
    Topology.RelCWComplex.cell
        (relativeCWCarrier (periodicCostalkComplementSubcomplex matrix selected weight x)) q ≃
      {d : Cell (augmentedForms matrix) q //
        cellCenter (augmentedForms matrix) d ∈
          costalkRegion (augmentedForms matrix) selected weight x} where
  toFun d := ⟨d.val, by
    have h := d.property
    change ¬¬cellCenter (augmentedForms matrix) d.val ∈
      costalkRegion (augmentedForms matrix) selected weight x at h
    exact not_not.mp h⟩
  invFun d := ⟨d.val, by
    change ¬¬cellCenter (augmentedForms matrix) d.val ∈
      costalkRegion (augmentedForms matrix) selected weight x
    exact not_not.mpr d.property⟩
  left_inv d := Subtype.ext rfl
  right_inv d := Subtype.ext rfl

/-- The actual relative cellular basis is exactly the representable
coface basis on the quotient, with the correct monomial weight shift. -/
def periodicCostalkRepresentableCellEquiv (c : IncidenceObject matrix)
    (S : Set (Fin s)) (m : Fin n → ℤ) (q : ℕ) :
    Topology.RelCWComplex.cell
        (relativeCWCarrier (periodicCostalkComplementSubcomplex matrix (Sum.inl '' S)
          (augmentedLatticePairing matrix m) (incidenceCellCenter matrix c))) q ≃
      RepresentableCostalkIndex matrix c S m q :=
  (periodicCostalkCellSupportEquiv matrix _ _ _ q).trans
    (costalkCellIndexEquiv matrix c S m q)

instance representableCostalkIndex_finite (c : IncidenceObject matrix)
    (S : Set (Fin s)) (m : Fin n → ℤ) (q : ℕ) :
    Finite (RepresentableCostalkIndex matrix c S m q) := by
  unfold RepresentableCostalkIndex
  infer_instance

/-- Each actual costalk has only finitely many cells in each degree,
although the character and universal-cover categories are unbounded. -/
theorem periodicCostalkCells_finite (c : IncidenceObject matrix)
    (S : Set (Fin s)) (m : Fin n → ℤ) (q : ℕ) :
    Finite (Topology.RelCWComplex.cell
      (relativeCWCarrier (periodicCostalkComplementSubcomplex matrix (Sum.inl '' S)
        (augmentedLatticePairing matrix m) (incidenceCellCenter matrix c))) q) :=
  Finite.of_equiv _ (periodicCostalkRepresentableCellEquiv matrix c S m q).symm

end ToricPower.IntegralArrangement
