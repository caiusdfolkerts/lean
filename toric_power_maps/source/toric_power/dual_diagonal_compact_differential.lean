module

public import ToricPower.DualDiagonalCompactCoordinates

/-!
# The literal incidence matrix of compactly supported dual-strip cochains

The coordinates here belong to the actual filtered colimit of bounded
relative CW cochains. Its differential is proved, coefficient by
coefficient, to be the original ambient cellular incidence matrix.
Every comparison uses a common finite window containing the two cells;
no finite support condition on the entire strip is imposed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s)) (u : Fin n → ℤ) (k : Type) [Field k]

local instance compactDifferentialPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

/-- Inclusion of the actual cells of one window into the full strip. -/
def dualDiagonalWindowCellInclusion (r₀ r q : ℕ) :
    OpenSupportCell A (dualDiagonalWindowSupport A S T u (r₀ + r)) q →
      DualDiagonalStripCell A S T u q :=
  fun c => ⟨c.val, c.property.1⟩

theorem dualDiagonalWindowCellInclusion_injective (r₀ r q : ℕ) :
    Function.Injective (dualDiagonalWindowCellInclusion A S T u r₀ r q) := by
  intro c d h
  exact Subtype.ext (congrArg (fun x : DualDiagonalStripCell A S T u q => x.val) h)

/-- The actual unrestricted colimit term in its original cell basis. -/
def dualDiagonalCompactCoordinates (r₀ q : ℕ) :
    (dualDiagonalCompactCochainComplex A k S T u r₀).X q ≃ₗ[k]
      (DualDiagonalStripCell A S T u q →₀ k) :=
  (dualDiagonalCompactTermIso A S T u k r₀ q).toLinearEquiv

/-- The actual colimit leg is extension by zero in these coordinates. -/
theorem dualDiagonalCompactCoordinates_inclusion (r₀ r q : ℕ)
    (φ : (openSupportCochainComplex A k
      (dualDiagonalWindowSupport A S T u (r₀ + r))).X q) :
    dualDiagonalCompactCoordinates A S T u k r₀ q
        ((colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r).f q φ) =
      Finsupp.mapDomain (dualDiagonalWindowCellInclusion A S T u r₀ r q)
        (openSupportCochainCoordinates A k
          (dualDiagonalWindowSupport A S T u (r₀ + r)) q φ) := by
  have actual := ConcreteCategory.congr_hom
    (dualDiagonalCompactTermIso_inclusion A S T u k r₀ r q) φ
  refine actual.trans ?_
  change Finsupp.mapDomain Subtype.val
      (Finsupp.domLCongr (R := k) (M := k)
        (dualDiagonalWindowCellEquiv A S T u r₀ r q)
        (openSupportCochainCoordinates A k
          (dualDiagonalWindowSupport A S T u (r₀ + r)) q φ)) = _
  simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  rfl

/-- A basis cochain in a window represents the identical basis cochain
of the unrestricted, finitely supported full strip. -/
theorem dualDiagonalCompactCoordinates_symm_single (r₀ r q : ℕ)
    (c : OpenSupportCell A (dualDiagonalWindowSupport A S T u (r₀ + r)) q)
    (a : k) :
    (dualDiagonalCompactCoordinates A S T u k r₀ q).symm
        (Finsupp.single (dualDiagonalWindowCellInclusion A S T u r₀ r q c) a) =
      (colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r).f q
        ((openSupportCochainCoordinates A k
          (dualDiagonalWindowSupport A S T u (r₀ + r)) q).symm
          (Finsupp.single c a)) := by
  apply (dualDiagonalCompactCoordinates A S T u k r₀ q).injective
  rw [LinearEquiv.apply_symm_apply, dualDiagonalCompactCoordinates_inclusion,
    LinearEquiv.apply_symm_apply, Finsupp.mapDomain_single]

/-- The actual colimit differential agrees with ambient incidence for
two cells lying in a common finite window. -/
theorem dualDiagonalCompactCoordinates_differential_window (r₀ r q : ℕ)
    (i : OpenSupportCell A (dualDiagonalWindowSupport A S T u (r₀ + r)) q)
    (j : OpenSupportCell A (dualDiagonalWindowSupport A S T u (r₀ + r)) (q + 1)) :
    dualDiagonalCompactCoordinates A S T u k r₀ (q + 1)
        ((dualDiagonalCompactCochainComplex A k S T u r₀).d q (q + 1)
          ((dualDiagonalCompactCoordinates A S T u k r₀ q).symm
            (Finsupp.single (dualDiagonalWindowCellInclusion A S T u r₀ r q i) 1)))
        (dualDiagonalWindowCellInclusion A S T u r₀ r (q + 1) j) =
      TauCeti.cellularIncidence (arrangementCarrier A) k q i.val j.val := by
  rw [dualDiagonalCompactCoordinates_symm_single]
  let φ := (openSupportCochainCoordinates A k
    (dualDiagonalWindowSupport A S T u (r₀ + r)) q).symm (Finsupp.single i 1)
  have commutation := ConcreteCategory.congr_hom
    ((colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r).comm q (q + 1)) φ
  refine (congrArg (fun v => dualDiagonalCompactCoordinates A S T u k r₀ (q + 1) v
    (dualDiagonalWindowCellInclusion A S T u r₀ r (q + 1) j)) commutation).trans ?_
  refine (congrArg (fun v => v
      (dualDiagonalWindowCellInclusion A S T u r₀ r (q + 1) j))
    (dualDiagonalCompactCoordinates_inclusion A S T u k r₀ r (q + 1)
      ((openSupportCochainComplex A k
        (dualDiagonalWindowSupport A S T u (r₀ + r))).d q (q + 1) φ))).trans ?_
  rw [Finsupp.mapDomain_apply_of_injective
    (dualDiagonalWindowCellInclusion_injective A S T u r₀ r (q + 1))]
  exact openSupportCochainCoordinates_differential_single A
    (dualDiagonalWindowSupport A S T u (r₀ + r)) k q i j

/-- Every coefficient of the actual unrestricted compact-support
differential is the original ambient periodic incidence, in all degrees. -/
theorem dualDiagonalCompactCoordinates_differential_single (r₀ q : ℕ)
    (i : DualDiagonalStripCell A S T u q)
    (j : DualDiagonalStripCell A S T u (q + 1)) :
    dualDiagonalCompactCoordinates A S T u k r₀ (q + 1)
        ((dualDiagonalCompactCochainComplex A k S T u r₀).d q (q + 1)
          ((dualDiagonalCompactCoordinates A S T u k r₀ q).symm (Finsupp.single i 1))) j =
      TauCeti.cellularIncidence (arrangementCarrier A) k q i.val j.val := by
  obtain ⟨r, hr⟩ := dualDiagonalWindowCellSet_exhaustive A S T u r₀ q i
  obtain ⟨t, ht⟩ := dualDiagonalWindowCellSet_exhaustive A S T u r₀ (q + 1) j
  let p := max r t
  let i' : OpenSupportCell A (dualDiagonalWindowSupport A S T u (r₀ + p)) q :=
    ⟨i.val, dualDiagonalWindowCellSet_mono A S T u r₀ q (le_max_left r t) hr⟩
  let j' : OpenSupportCell A (dualDiagonalWindowSupport A S T u (r₀ + p)) (q + 1) :=
    ⟨j.val, dualDiagonalWindowCellSet_mono A S T u r₀ (q + 1) (le_max_right r t) ht⟩
  exact dualDiagonalCompactCoordinates_differential_window A S T u k r₀ p q i' j'

end ToricPower.IntegralArrangement
