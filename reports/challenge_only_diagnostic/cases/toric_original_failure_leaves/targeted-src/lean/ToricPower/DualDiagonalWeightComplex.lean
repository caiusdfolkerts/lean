module

public import ToricPower.CellularTranslatedDifferential
public import ToricPower.DualDiagonalCompactDifferential
public import ToricPower.ArrangementIncidenceCeilings
public import ToricPower.DiagonalChartAction

/-!
# The actual dual-diagonal weight complex

The coefficient functor retains both literal Cartier monomial
inequalities in one total character. Its incidence maps multiply the
two factors by the actual characters `(a,-a)`. The original cellular
cochain construction is then compared with compactly supported cochains
of the unrestricted open dual strip, through a proved equality of all
matrix coefficients.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s)) (u : Fin n → ℤ)

local instance dualWeightPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

/-- Both actual dual Cartier factors, with total character fixed. -/
def dualDiagonalWeightAllowed (c : IncidenceObject A) (a : Fin n → ℤ) : Prop :=
  dualDiagonalMonomialAllowed A S T u (c.2, a)

/-- Every genuine incidence preserves the two monomial section
conditions. No cohomological assumption enters this coefficient map. -/
theorem dualDiagonalWeightAllowed_map {c d : IncidenceObject A} (f : c ⟶ d)
    {a : Fin n → ℤ} (h : dualDiagonalWeightAllowed A S T u c a) :
    dualDiagonalWeightAllowed A S T u d (a + f.val) := by
  constructor
  · intro i hi
    have original := h.1 i hi
    have incidence := (incidence_ceiling_bounds A f i).1
    change 0 ≤ rayPairing A a i + reflectedCeiling A c.2.val i at original
    change 0 ≤ rayPairing A (a + f.val) i + reflectedCeiling A d.2.val i
    rw [rayPairing_add]
    omega
  · intro i hi
    have original := h.2 i hi
    have incidence := (incidence_ceiling_bounds A f i).2
    change 0 ≤ rayPairing A (u - a) i + c.2.val.val.1 (.inl i) at original
    change 0 ≤ rayPairing A (u - (a + f.val)) i + d.2.val.val.1 (.inl i)
    rw [rayPairing_sub, rayPairing_add]
    rw [rayPairing_sub] at original
    omega

abbrev DualDiagonalWeightIndex (q : ℕ) :=
  TranslatedCellIndex A (dualDiagonalWeightAllowed A S T u) q

/-- The normalized-cell/character indexing of the original Laurent
coefficient functor is precisely the earlier pair indexing. -/
def dualDiagonalWeightPairEquiv (q : ℕ) :
    DualDiagonalWeightIndex A S T u q ≃
      {p : NormalizedCell A q × (Fin n → ℤ) // dualDiagonalMonomialAllowed A S T u p} where
  toFun p := ⟨(p.1, p.2.val), p.2.property⟩
  invFun p := ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
  left_inv p := by rcases p with ⟨c, a, h⟩; rfl
  right_inv p := by rcases p with ⟨⟨c, a⟩, h⟩; rfl

def dualDiagonalAllowedCellEquiv (q : ℕ) :
    {c : Cell (augmentedForms A) q // dualStripCellAllowed A S T u c} ≃
      DualDiagonalStripCell A S T u q where
  toFun c := ⟨c.val, (dualStripCellAllowed_iff_point A S T u c.val
    (cellCenter_mem _ c.val)).mp c.property⟩
  invFun c := ⟨c.val, (dualStripCellAllowed_iff_point A S T u c.val
    (cellCenter_mem _ c.val)).mpr c.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The actual sign is `-a`: incidence multiplication by `a` translates
the corresponding universal-cover cell by its negative. -/
def dualDiagonalWeightCellEquiv (q : ℕ) :
    DualDiagonalWeightIndex A S T u q ≃ DualDiagonalStripCell A S T u q :=
  (dualDiagonalWeightPairEquiv A S T u q).trans
    ((dualDiagonalMonomialCellEquiv A S T u q).trans
      (dualDiagonalAllowedCellEquiv A S T u q))

@[simp]
theorem dualDiagonalWeightCellEquiv_val (q : ℕ) (i : DualDiagonalWeightIndex A S T u q) :
    (dualDiagonalWeightCellEquiv A S T u q i).val =
      translateCell A (-i.2.val) i.1.val := rfl

variable (k : Type) [Field k]

/-- The actual fixed-weight coefficient diagram and original cellular
differential, defined independently of a compact-support replacement. -/
def dualDiagonalWeightComplex : CochainComplex (ModuleCat.{0} k) ℕ :=
  translatedWeightCellularComplex A (dualDiagonalWeightAllowed A S T u)
    (dualDiagonalWeightAllowed_map A S T u) k

def dualDiagonalWeightCoordinates (q : ℕ) :
    (dualDiagonalWeightComplex A S T u k).X q ≃ₗ[k]
      (DualDiagonalStripCell A S T u q →₀ k) :=
  (translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
    (dualDiagonalWeightAllowed_map A S T u) k q).trans
      (Finsupp.mapDomain.linearEquiv k k (dualDiagonalWeightCellEquiv A S T u q))

theorem dualDiagonalWeightCoordinates_apply (q : ℕ)
    (v : (dualDiagonalWeightComplex A S T u k).X q)
    (i : DualDiagonalWeightIndex A S T u q) :
    dualDiagonalWeightCoordinates A S T u k q v (dualDiagonalWeightCellEquiv A S T u q i) =
      translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
        (dualDiagonalWeightAllowed_map A S T u) k q v i :=
  Finsupp.mapDomain_apply_of_injective (dualDiagonalWeightCellEquiv A S T u q).injective _ i

theorem dualDiagonalWeightCoordinates_symm_single (q : ℕ)
    (i : DualDiagonalWeightIndex A S T u q) (r : k) :
    (dualDiagonalWeightCoordinates A S T u k q).symm
        (Finsupp.single (dualDiagonalWeightCellEquiv A S T u q i) r) =
      (translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
        (dualDiagonalWeightAllowed_map A S T u) k q).symm (Finsupp.single i r) := by
  apply (dualDiagonalWeightCoordinates A S T u k q).injective
  rw [LinearEquiv.apply_symm_apply]
  change _ = Finsupp.mapDomain (dualDiagonalWeightCellEquiv A S T u q)
    (translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
      (dualDiagonalWeightAllowed_map A S T u) k q
      ((translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
        (dualDiagonalWeightAllowed_map A S T u) k q).symm (Finsupp.single i r)))
  rw [LinearEquiv.apply_symm_apply, Finsupp.mapDomain_single]

/-- Translation preserves the original characteristic-disk incidence,
so both independently computed differential coefficients are identical. -/
theorem dualDiagonalWeightCellEquiv_incidence (q : ℕ)
    (i : DualDiagonalWeightIndex A S T u q)
    (j : DualDiagonalWeightIndex A S T u (q + 1)) :
    TauCeti.cellularIncidence (arrangementCarrier A) k q
        (dualDiagonalWeightCellEquiv A S T u q i).val
        (dualDiagonalWeightCellEquiv A S T u (q + 1) j).val =
      diagonalGlobalColumn k A q j.1 (i.1, j.2.val - i.2.val) := by
  rw [dualDiagonalWeightCellEquiv_val, dualDiagonalWeightCellEquiv_val,
    diagonalGlobalColumn_apply]
  have translated := arrangement_cellularIncidence_translate A k j.2.val q
    (translateCell A (-i.2.val) i.1.val) (translateCell A (-j.2.val) j.1.val)
  simp only [translateCell_add, neg_add_cancel, translateCell_zero] at translated
  have difference : -i.2.val + j.2.val = j.2.val - i.2.val := by abel
  rw [difference] at translated
  exact translated.symm

/-- The actual original cellular coefficient complex has the literal
ambient strip matrix, including every character and every incidence. -/
theorem dualDiagonalWeightCoordinates_d_generator (q : ℕ)
    (i : DualDiagonalWeightIndex A S T u q)
    (j : DualDiagonalWeightIndex A S T u (q + 1)) (r : k) :
    dualDiagonalWeightCoordinates A S T u k (q + 1)
        ((dualDiagonalWeightComplex A S T u k).d q (q + 1)
          ((dualDiagonalWeightCoordinates A S T u k q).symm
            (Finsupp.single (dualDiagonalWeightCellEquiv A S T u q i) r)))
        (dualDiagonalWeightCellEquiv A S T u (q + 1) j) =
      TauCeti.cellularIncidence (arrangementCarrier A) k q
        (dualDiagonalWeightCellEquiv A S T u q i).val
        (dualDiagonalWeightCellEquiv A S T u (q + 1) j).val * r := by
  rw [dualDiagonalWeightCoordinates_symm_single, dualDiagonalWeightCoordinates_apply]
  exact (translatedWeightCellularCoordinates_d_generator A
    (dualDiagonalWeightAllowed A S T u) (dualDiagonalWeightAllowed_map A S T u)
    k q i j r).trans (congrArg (fun z => z * r)
      (dualDiagonalWeightCellEquiv_incidence A S T u k q i j).symm)

end ToricPower.IntegralArrangement
