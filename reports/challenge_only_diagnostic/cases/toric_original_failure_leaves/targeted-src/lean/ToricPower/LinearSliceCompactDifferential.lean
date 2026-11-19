module

public import ToricPower.LinearSliceCompactCoordinates

/-!
# The literal incidence matrix of compactly supported closed-slice cochains

The coordinates here belong to the actual filtered colimit of bounded
relative CW cochains. Its differential is proved, coefficient by
coefficient, to be the original ambient cellular incidence matrix.
Every comparison uses a common finite window containing the two cells;
no finite support condition on the entire slice support is imposed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (zeroRows : Set (Fin s ⊕ Fin n)) (U : OpenCellSupport A) (k : Type) [Field k]

local instance sliceCompactDifferentialPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

/-- Inclusion of the actual cells of one window into the full slice support. -/
def sliceWindowCellInclusion (r₀ r q : ℕ) :
    SliceSupportCell A zeroRows (openCellWindow A U (r₀ + r)) q →
      SliceSupportCell A zeroRows U q :=
  fun c => ⟨c.val, c.property.1⟩

theorem sliceWindowCellInclusion_injective (r₀ r q : ℕ) :
    Function.Injective (sliceWindowCellInclusion A zeroRows U r₀ r q) := by
  intro c d h
  exact Subtype.ext (congrArg (fun x : SliceSupportCell A zeroRows U q => x.val) h)

/-- The actual unrestricted colimit term in its original cell basis. -/
def sliceCompactCoordinates (r₀ q : ℕ) :
    (sliceCompactCochainComplex A zeroRows k U r₀).X q ≃ₗ[k]
      (SliceSupportCell A zeroRows U q →₀ k) :=
  (sliceCompactTermIso A zeroRows U k r₀ q).toLinearEquiv

/-- The actual colimit leg is extension by zero in these coordinates. -/
theorem sliceCompactCoordinates_inclusion (r₀ r q : ℕ)
    (φ : (sliceSupportCochainComplex A zeroRows k
      (openCellWindow A U (r₀ + r))).X q) :
    sliceCompactCoordinates A zeroRows U k r₀ q
        ((colimit.ι (sliceWindowCochainSystem A zeroRows k U r₀) r).f q φ) =
      Finsupp.mapDomain (sliceWindowCellInclusion A zeroRows U r₀ r q)
        (sliceSupportCochainCoordinates A zeroRows k
          (openCellWindow A U (r₀ + r)) q φ) := by
  have actual := ConcreteCategory.congr_hom
    (sliceCompactTermIso_inclusion A zeroRows U k r₀ r q) φ
  refine actual.trans ?_
  change Finsupp.mapDomain Subtype.val
      (Finsupp.domLCongr (R := k) (M := k)
        (sliceWindowCellEquiv A zeroRows U r₀ r q)
        (sliceSupportCochainCoordinates A zeroRows k
          (openCellWindow A U (r₀ + r)) q φ)) = _
  simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  rfl

/-- A basis cochain in a window represents the identical basis cochain
of the unrestricted, finitely supported full slice support. -/
theorem sliceCompactCoordinates_symm_single (r₀ r q : ℕ)
    (c : SliceSupportCell A zeroRows (openCellWindow A U (r₀ + r)) q)
    (a : k) :
    (sliceCompactCoordinates A zeroRows U k r₀ q).symm
        (Finsupp.single (sliceWindowCellInclusion A zeroRows U r₀ r q c) a) =
      (colimit.ι (sliceWindowCochainSystem A zeroRows k U r₀) r).f q
        ((sliceSupportCochainCoordinates A zeroRows k
          (openCellWindow A U (r₀ + r)) q).symm
          (Finsupp.single c a)) := by
  apply (sliceCompactCoordinates A zeroRows U k r₀ q).injective
  rw [LinearEquiv.apply_symm_apply, sliceCompactCoordinates_inclusion,
    LinearEquiv.apply_symm_apply, Finsupp.mapDomain_single]

/-- The actual colimit differential agrees with ambient incidence for
two cells lying in a common finite window. -/
theorem sliceCompactCoordinates_differential_window (r₀ r q : ℕ)
    (i : SliceSupportCell A zeroRows (openCellWindow A U (r₀ + r)) q)
    (j : SliceSupportCell A zeroRows (openCellWindow A U (r₀ + r)) (q + 1)) :
    sliceCompactCoordinates A zeroRows U k r₀ (q + 1)
        ((sliceCompactCochainComplex A zeroRows k U r₀).d q (q + 1)
          ((sliceCompactCoordinates A zeroRows U k r₀ q).symm
            (Finsupp.single (sliceWindowCellInclusion A zeroRows U r₀ r q i) 1)))
        (sliceWindowCellInclusion A zeroRows U r₀ r (q + 1) j) =
      TauCeti.cellularIncidence (arrangementCarrier A) k q i.val.val j.val.val := by
  rw [sliceCompactCoordinates_symm_single]
  let φ := (sliceSupportCochainCoordinates A zeroRows k
    (openCellWindow A U (r₀ + r)) q).symm (Finsupp.single i 1)
  have commutation := ConcreteCategory.congr_hom
    ((colimit.ι (sliceWindowCochainSystem A zeroRows k U r₀) r).comm q (q + 1)) φ
  refine (congrArg (fun v => sliceCompactCoordinates A zeroRows U k r₀ (q + 1) v
    (sliceWindowCellInclusion A zeroRows U r₀ r (q + 1) j)) commutation).trans ?_
  refine (congrArg (fun v => v
      (sliceWindowCellInclusion A zeroRows U r₀ r (q + 1) j))
    (sliceCompactCoordinates_inclusion A zeroRows U k r₀ r (q + 1)
      ((sliceSupportCochainComplex A zeroRows k
        (openCellWindow A U (r₀ + r))).d q (q + 1) φ))).trans ?_
  rw [Finsupp.mapDomain_apply_of_injective
    (sliceWindowCellInclusion_injective A zeroRows U r₀ r (q + 1))]
  exact sliceSupportCochainCoordinates_differential_single A zeroRows
    (openCellWindow A U (r₀ + r)) k q i j

/-- Every coefficient of the actual unrestricted compact-support
differential is the original ambient periodic incidence, in all degrees. -/
theorem sliceCompactCoordinates_differential_single (r₀ q : ℕ)
    (i : SliceSupportCell A zeroRows U q)
    (j : SliceSupportCell A zeroRows U (q + 1)) :
    sliceCompactCoordinates A zeroRows U k r₀ (q + 1)
        ((sliceCompactCochainComplex A zeroRows k U r₀).d q (q + 1)
          ((sliceCompactCoordinates A zeroRows U k r₀ q).symm (Finsupp.single i 1))) j =
      TauCeti.cellularIncidence (arrangementCarrier A) k q i.val.val j.val.val := by
  obtain ⟨r, hr⟩ := sliceWindowCellSet_exhaustive A zeroRows U r₀ q i
  obtain ⟨t, ht⟩ := sliceWindowCellSet_exhaustive A zeroRows U r₀ (q + 1) j
  let p := max r t
  let i' : SliceSupportCell A zeroRows (openCellWindow A U (r₀ + p)) q :=
    ⟨i.val, sliceWindowCellSet_mono A zeroRows U r₀ q (le_max_left r t) hr⟩
  let j' : SliceSupportCell A zeroRows (openCellWindow A U (r₀ + p)) (q + 1) :=
    ⟨j.val, sliceWindowCellSet_mono A zeroRows U r₀ (q + 1) (le_max_right r t) ht⟩
  exact sliceCompactCoordinates_differential_window A zeroRows U k r₀ p q i' j'

end ToricPower.IntegralArrangement
