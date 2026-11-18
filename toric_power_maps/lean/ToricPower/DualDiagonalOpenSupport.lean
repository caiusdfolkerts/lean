module

public import ToricPower.DualDiagonalTopClassNaturality
public import ToricPower.ArrangementBoundedCells

/-!
# Actual bounded-support extension into a full dual strip

Any bounded open union of arrangement cells contained in the full strip
lies in a genuine integer window. Its original support-extension map
therefore enters the actual filtered colimit and then the original
dual-diagonal weight complex. For a nonempty convex source this specified
map is a quasi-isomorphism: it preserves the fixed ambient top class.

This includes the bounded translated costalk supports of representables;
no bound is imposed on the target strip or on the complete character family.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S T : Set (Fin s))
  (u : Fin n → ℤ) (U : OpenCellSupport A)

/-- Every actual bounded subregion of the unrestricted strip is
contained in one of the original integer windows. -/
theorem boundedSupport_exists_dualDiagonalWindow
    (bounded : Bornology.IsBounded (U.val : Set (Fin n → ℝ)))
    (inside : (U.val : Set (Fin n → ℝ)) ⊆ dualDiagonalStrip A S T u) :
    ∃ r : ℕ, U ≤ dualDiagonalWindowSupport A S T u r := by
  obtain ⟨C, bound⟩ := bounded.exists_norm_le
  obtain ⟨r, larger⟩ := exists_nat_gt C
  refine ⟨r, fun x hx => ⟨inside hx, fun j => ?_⟩⟩
  apply abs_lt.mp
  have coordinate := (norm_le_pi_norm x j).trans (bound x hx)
  have coordinate' : |x j| ≤ C := by
    simpa only [Real.norm_eq_abs] using coordinate
  exact coordinate'.trans_lt larger

variable (k : Type) [Field k] (r : ℕ)
  (inside : U ≤ dualDiagonalWindowSupport A S T u r)

/-- The original extension, original colimit inclusion, and original
full-weight complex comparison give the specified map. -/
def dualDiagonalOpenSupportMap :
    openSupportCochainComplex A k U ⟶ dualDiagonalWeightComplex A S T u k :=
  openSupportCochainExtension A k inside ≫
    colimit.ι (dualDiagonalWindowCochainSystem A k S T u r) 0 ≫
      (dualDiagonalWeightCompactIso A S T u k r).inv

variable (convex : Convex ℝ (U.val : Set (Fin n → ℝ)))
  (nonempty : (U.val : Set (Fin n → ℝ)).Nonempty)
  (bounded : Bornology.IsBounded (U.val : Set (Fin n → ℝ)))

/-- This is equality for the actual homology map and fixed ambient
orientation, rather than an arbitrary isomorphism of one-dimensional spaces. -/
@[reassoc]
theorem dualDiagonalOpenSupportMap_topClass
    (stripNonempty : (dualDiagonalStrip A S T u).Nonempty) :
    HomologicalComplex.homologyMap
        (dualDiagonalOpenSupportMap A S T u U k r inside) n ≫
      (dualDiagonalWeightTopClassIso A S T u k stripNonempty).hom =
    (openSupportCochainTopClassIso A k U convex nonempty bounded).hom := by
  have windowNonempty : (dualDiagonalWindow A S T u r).Nonempty := nonempty.mono inside
  rw [dualDiagonalWeightTopClassIso_eq_window A S T u k stripNonempty r windowNonempty]
  simp only [dualDiagonalOpenSupportMap, HomologicalComplex.homologyMap_comp, Category.assoc]
  rw [← Category.assoc (HomologicalComplex.homologyMap
      (dualDiagonalWeightCompactIso A S T u k r).inv n),
    ← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id,
    HomologicalComplex.homologyMap_id, Category.id_comp,
    dualDiagonalCompactTopClassIso_inclusion]
  exact openSupportCochainTopClassIso_natural A k inside
    convex (dualDiagonalWindow_convex A S T u r)
    nonempty windowNonempty bounded (dualDiagonalWindow_bounded A S T u r)

include convex nonempty bounded in
/-- Every such actual bounded convex support computes the entire
unrestricted weight complex by its genuine support-extension map. -/
theorem dualDiagonalOpenSupportMap_quasiIso :
    QuasiIso (dualDiagonalOpenSupportMap A S T u U k r inside) := by
  have stripNonempty : (dualDiagonalStrip A S T u).Nonempty :=
    nonempty.mono (fun x hx => (inside hx).1)
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases equal : q = n
  · subst q
    haveI : IsIso (HomologicalComplex.homologyMap
        (dualDiagonalOpenSupportMap A S T u U k r inside) n ≫
      (dualDiagonalWeightTopClassIso A S T u k stripNonempty).hom) := by
      rw [dualDiagonalOpenSupportMap_topClass A S T u U k r inside
        convex nonempty bounded stripNonempty]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (dualDiagonalWeightTopClassIso A S T u k stripNonempty).hom
  · exact (openSupportCochainComplex_isZero_homology A k U convex nonempty bounded q equal).isIso
      (dualDiagonalWeightComplex_isZero_homology A S T u k stripNonempty q equal) _

end ToricPower.IntegralArrangement

end
