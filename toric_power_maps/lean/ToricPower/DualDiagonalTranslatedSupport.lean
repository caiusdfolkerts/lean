module

public import ToricPower.DualDiagonalOpenSupport
public import ToricPower.ArrangementOpenSupportTranslationCoordinates

/-!
# The specified translated-support map into the unrestricted dual strip

The map uses inverse translation of the genuine relative CW pairs,
scalar duality, a genuine window inclusion, and the full filtered
colimit. Its top class is the fixed ambient one. This is the precise
geometric comparison required by the represented cellular evaluation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S T : Set (Fin s))
  (u : Fin n → ℤ) (U : OpenCellSupport A) (z : Fin n → ℤ)

/-- A bounded translated source lies in an actual finite window, while
the full target strip remains unrestricted. -/
theorem translatedSupport_exists_dualDiagonalWindow
    (bounded : Bornology.IsBounded (U.val : Set (Fin n → ℝ)))
    (inside : translatedRegion (U.val : Set (Fin n → ℝ)) (latticeLift z) ⊆
      dualDiagonalStrip A S T u) :
    ∃ r : ℕ, translatedRegion (U.val : Set (Fin n → ℝ)) (latticeLift z) ⊆
      dualDiagonalWindow A S T u r := by
  obtain ⟨C, bound⟩ := bounded.exists_norm_le
  obtain ⟨r, larger⟩ := exists_nat_gt (C + ‖latticeLift z‖)
  refine ⟨r, fun x hx => ⟨inside hx, fun j => ?_⟩⟩
  obtain ⟨y, hy, rfl⟩ := hx
  apply abs_lt.mp
  have coordinate := (norm_le_pi_norm (y + latticeLift z) j).trans
    ((norm_add_le y (latticeLift z)).trans (add_le_add (bound y hy) le_rfl))
  have coordinate' : |(y + latticeLift z) j| ≤ C + ‖latticeLift z‖ := by
    simpa only [Real.norm_eq_abs] using coordinate
  exact coordinate'.trans_lt larger

variable (k : Type) [Field k] (r : ℕ)
  (inside : translatedRegion (U.val : Set (Fin n → ℝ)) (latticeLift z) ⊆
    dualDiagonalWindow A S T u r)

/-- The original translated relative-cellular map into a window,
followed by the actual unrestricted compact-support comparison. -/
def dualDiagonalTranslatedSupportMap :
    openSupportCochainComplex A k U ⟶ dualDiagonalWeightComplex A S T u k :=
  openSupportCochainTranslation A z
      (U := U) (V := dualDiagonalWindowSupport A S T u r) inside k ≫
    colimit.ι (dualDiagonalWindowCochainSystem A k S T u r) 0 ≫
      (dualDiagonalWeightCompactIso A S T u k r).inv

/-- The literal translated cell in the full strip, with no quotient
or finite replacement of its actual index. -/
def dualDiagonalTranslatedSupportCell (q : ℕ) :
    OpenSupportCell A U q → DualDiagonalStripCell A S T u q :=
  dualDiagonalWindowCellInclusion A S T u r 0 q ∘
    openSupportCellTranslation A z
      (U := U) (V := dualDiagonalWindowSupport A S T u r) inside q

@[simp]
theorem dualDiagonalTranslatedSupportCell_val (q : ℕ) (c : OpenSupportCell A U q) :
    (dualDiagonalTranslatedSupportCell A S T u U z r inside q c).val =
      translateCell A z c.val := rfl

/-- Every original coefficient is transported to its actual translated
cell, with coefficient unchanged, in the unrestricted full weight. -/
theorem dualDiagonalTranslatedSupportMap_coordinates (q : ℕ)
    [Finite (OpenSupportCell A U q)] (v : (openSupportCochainComplex A k U).X q) :
    dualDiagonalWeightCoordinates A S T u k q
        ((dualDiagonalTranslatedSupportMap A S T u U z k r inside).f q v) =
      Finsupp.mapDomain (dualDiagonalTranslatedSupportCell A S T u U z r inside q)
        (openSupportCochainCoordinates A k U q v) := by
  change dualDiagonalWeightCoordinates A S T u k q
      ((dualDiagonalWeightCoordinates A S T u k q).symm
        (dualDiagonalCompactCoordinates A S T u k r q
          ((colimit.ι (dualDiagonalWindowCochainSystem A k S T u r) 0).f q
            ((openSupportCochainTranslation A z
              (U := U) (V := dualDiagonalWindowSupport A S T u r) inside k).f q v)))) = _
  rw [LinearEquiv.apply_symm_apply, dualDiagonalCompactCoordinates_inclusion]
  simp only [Nat.add_zero]
  rw [openSupportCochainTranslation_coordinates, ← Finsupp.mapDomain_comp]
  rfl

/-- In particular, a characteristic-cell generator has its literal
translated characteristic-cell image. -/
theorem dualDiagonalTranslatedSupportMap_single (q : ℕ)
    [Finite (OpenSupportCell A U q)] (c : OpenSupportCell A U q) (a : k) :
    (dualDiagonalTranslatedSupportMap A S T u U z k r inside).f q
        ((openSupportCochainCoordinates A k U q).symm (Finsupp.single c a)) =
      (dualDiagonalWeightCoordinates A S T u k q).symm
        (Finsupp.single (dualDiagonalTranslatedSupportCell A S T u U z r inside q c) a) := by
  apply (dualDiagonalWeightCoordinates A S T u k q).injective
  rw [dualDiagonalTranslatedSupportMap_coordinates, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, Finsupp.mapDomain_single]

variable (convex : Convex ℝ (U.val : Set (Fin n → ℝ)))
  (nonempty : (U.val : Set (Fin n → ℝ)).Nonempty)
  (bounded : Bornology.IsBounded (U.val : Set (Fin n → ℝ)))

/-- The actual translated support map preserves the chosen ambient
top class, including its original orientation. -/
@[reassoc]
theorem dualDiagonalTranslatedSupportMap_topClass
    (stripNonempty : (dualDiagonalStrip A S T u).Nonempty) :
    HomologicalComplex.homologyMap
        (dualDiagonalTranslatedSupportMap A S T u U z k r inside) n ≫
      (dualDiagonalWeightTopClassIso A S T u k stripNonempty).hom =
    (openSupportCochainTopClassIso A k U convex nonempty bounded).hom := by
  have windowNonempty : (dualDiagonalWindow A S T u r).Nonempty := by
    obtain ⟨x, hx⟩ := nonempty
    exact ⟨x + latticeLift z, inside ⟨x, hx, rfl⟩⟩
  rw [dualDiagonalWeightTopClassIso_eq_window A S T u k stripNonempty r windowNonempty]
  simp only [dualDiagonalTranslatedSupportMap, HomologicalComplex.homologyMap_comp,
    Category.assoc]
  rw [← Category.assoc (HomologicalComplex.homologyMap
      (dualDiagonalWeightCompactIso A S T u k r).inv n),
    ← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id,
    HomologicalComplex.homologyMap_id, Category.id_comp,
    dualDiagonalCompactTopClassIso_inclusion]
  exact openSupportCochainTopClassIso_translation A z
    (U := U) (V := dualDiagonalWindowSupport A S T u r) inside k
    convex (dualDiagonalWindow_convex A S T u r)
    nonempty windowNonempty bounded (dualDiagonalWindow_bounded A S T u r)

include convex nonempty bounded in
/-- The specified map computes every homological degree of the full
weight complex, without a boundedness assumption on that weight's strip. -/
theorem dualDiagonalTranslatedSupportMap_quasiIso :
    QuasiIso (dualDiagonalTranslatedSupportMap A S T u U z k r inside) := by
  have stripNonempty : (dualDiagonalStrip A S T u).Nonempty := by
    obtain ⟨x, hx⟩ := nonempty
    exact ⟨x + latticeLift z, (inside ⟨x, hx, rfl⟩).1⟩
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases equal : q = n
  · subst q
    haveI : IsIso (HomologicalComplex.homologyMap
        (dualDiagonalTranslatedSupportMap A S T u U z k r inside) n ≫
      (dualDiagonalWeightTopClassIso A S T u k stripNonempty).hom) := by
      rw [dualDiagonalTranslatedSupportMap_topClass A S T u U z k r inside
        convex nonempty bounded stripNonempty]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (dualDiagonalWeightTopClassIso A S T u k stripNonempty).hom
  · exact (openSupportCochainComplex_isZero_homology A k U convex nonempty bounded q equal).isIso
      (dualDiagonalWeightComplex_isZero_homology A S T u k stripNonempty q equal) _

end ToricPower.IntegralArrangement

end
