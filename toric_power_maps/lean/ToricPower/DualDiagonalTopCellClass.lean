module

public import ToricPower.ArrangementTopCellClass
public import ToricPower.DualDiagonalTopClassNaturality

/-!
# Every genuine top cell has a nonzero dual-strip class

A top cell of the full strip lies in a finite integer window. Its actual
one-cell relative cochains extend into that window, then into the genuine
filtered colimit, and finally into the independent Laurent weight
complex. The existing coordinate and orientation comparisons show that
this is the original single-cell generator and that its top class is
nonzero. No arbitrary choice of a cohomology basis is used to force this.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S T : Set (Fin s))
  (u : Fin n → ℤ) (k : Type) [Field k]

local notation "K" => dualDiagonalWeightComplex A S T u k

theorem dualDiagonalWeightComplex_isZero_X_above (q : ℕ) (above : n < q) :
    IsZero ((K).X q) := by
  letI : IsEmpty (DualDiagonalStripCell A S T u q) :=
    ⟨fun c => (not_lt_of_ge (cell_dimension_le A c.val) above).elim⟩
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of k (DualDiagonalStripCell A S T u q →₀ k))).of_iso
      (dualDiagonalWeightCoordinates A S T u k q).toModuleIso

theorem dualDiagonalWeightComplex_outgoing : (K).d n (n+1) = 0 :=
  (dualDiagonalWeightComplex_isZero_X_above A S T u k (n+1) (Nat.lt_succ_self n)).eq_of_tgt _ _

variable (i : DualDiagonalStripCell A S T u n) (r : ℕ)
  (inside : cellCenter (augmentedForms A) i.val ∈ dualDiagonalWindow A S T u r)

include inside in
/-- Since the window is an actual union of open cells, membership of
the center puts the entire cell inside it. -/
theorem dualDiagonalTopCell_window_le :
    topCellSupport A i.val ≤ dualDiagonalWindowSupport A S T u r := by
  intro x hx
  exact ((dualDiagonalWindow_cellwise A S T u r) i.val.val.1 i.val.val.2
    (cellCenter_mem (augmentedForms A) i.val) hx).mp inside

/-- The literal support extension through one finite window into the
independently defined full-character complex. -/
def dualDiagonalTopCellMap :
    openSupportCochainComplex A k (topCellSupport A i.val) ⟶ K :=
  openSupportCochainExtension A k (dualDiagonalTopCell_window_le A S T u i r inside) ≫
    colimit.ι (dualDiagonalWindowCochainSystem A k S T u r) 0 ≫
      (dualDiagonalWeightCompactIso A S T u k r).inv

/-- The map preserves the actual single-cell coordinate. -/
theorem dualDiagonalTopCellMap_generator :
    (dualDiagonalTopCellMap A S T u k i r inside).f n
        (topCellCochainGenerator A i.val k) =
      (dualDiagonalWeightCoordinates A S T u k n).symm (Finsupp.single i 1) := by
  apply (dualDiagonalWeightCoordinates A S T u k n).injective
  change dualDiagonalWeightCoordinates A S T u k n
      ((dualDiagonalWeightCoordinates A S T u k n).symm
        (dualDiagonalCompactCoordinates A S T u k r n
          ((colimit.ι (dualDiagonalWindowCochainSystem A k S T u r) 0).f n
            ((openSupportCochainExtension A k
              (dualDiagonalTopCell_window_le A S T u i r inside)).f n
                (topCellCochainGenerator A i.val k))))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    dualDiagonalCompactCoordinates_inclusion]
  simp only [Nat.add_zero]
  rw [openSupportCochainExtension_coordinates, topCellCochainGenerator_coordinates,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  all_goals congr 1

/-- Its induced top homology map preserves the fixed ambient class. -/
theorem dualDiagonalTopCellMap_topClass
    (nonempty : (dualDiagonalStrip A S T u).Nonempty) :
    HomologicalComplex.homologyMap (dualDiagonalTopCellMap A S T u k i r inside) n ≫
        (dualDiagonalWeightTopClassIso A S T u k nonempty).hom =
      (openSupportCochainTopClassIso A k (topCellSupport A i.val)
        (topCellSupport_convex A i.val) (topCellSupport_nonempty A i.val)
        (topCellSupport_bounded A i.val)).hom := by
  have windowNonempty : (dualDiagonalWindow A S T u r).Nonempty := ⟨_, inside⟩
  rw [dualDiagonalWeightTopClassIso_eq_window A S T u k nonempty r windowNonempty]
  simp only [dualDiagonalTopCellMap, HomologicalComplex.homologyMap_comp, Category.assoc]
  rw [← Category.assoc (HomologicalComplex.homologyMap
      (dualDiagonalWeightCompactIso A S T u k r).inv n),
    ← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id,
    HomologicalComplex.homologyMap_id, Category.id_comp,
    dualDiagonalCompactTopClassIso_inclusion]
  exact openSupportCochainTopClassIso_natural A k
    (dualDiagonalTopCell_window_le A S T u i r inside)
    (topCellSupport_convex A i.val) (dualDiagonalWindow_convex A S T u r)
    (topCellSupport_nonempty A i.val) windowNonempty
    (topCellSupport_bounded A i.val) (dualDiagonalWindow_bounded A S T u r)

/-- The genuine quotient in top degree, with the chosen ambient class. -/
def dualDiagonalWeightTopFunctional (nonempty : (dualDiagonalStrip A S T u).Nonempty) :
    (K).X n ⟶ ModuleCat.of k k :=
  (K).pOpcycles n ≫
    ((K).isoHomologyι n (n+1) (by simp) (dualDiagonalWeightComplex_outgoing A S T u k)).inv ≫
      (dualDiagonalWeightTopClassIso A S T u k nonempty).hom

/-- Every original top-cell basis vector represents a nonzero ambient
top class in the full unrestricted dual strip. -/
theorem dualDiagonalWeightTopFunctional_single_ne_zero
    (nonempty : (dualDiagonalStrip A S T u).Nonempty) :
    dualDiagonalWeightTopFunctional A S T u k nonempty
      ((dualDiagonalWeightCoordinates A S T u k n).symm (Finsupp.single i 1)) ≠ 0 := by
  have point := i.property
  change cellCenter (augmentedForms A) i.val ∈ dualDiagonalStrip A S T u at point
  rw [← dualDiagonalWindow_exhausts A S T u] at point
  obtain ⟨r, hr⟩ := mem_iUnion.mp point
  let φ := dualDiagonalTopCellMap A S T u k i r hr
  have quotient := topHomologyQuotient_natural
    (openSupportCochainComplex A k (topCellSupport A i.val)) n
    (topCellCochain_outgoing A i.val k)
    (dualDiagonalWeightComplex_outgoing A S T u k) φ
  have maps : φ.f n ≫ dualDiagonalWeightTopFunctional A S T u k nonempty =
      topCellCochainTopFunctional A i.val k := by
    have transported := congrArg
      (fun f => f ≫ (dualDiagonalWeightTopClassIso A S T u k nonempty).hom) quotient
    simp only [Category.assoc] at transported
    dsimp only [φ] at transported
    rw [dualDiagonalTopCellMap_topClass A S T u k i r hr nonempty] at transported
    exact transported
  have value := ConcreteCategory.congr_hom maps (topCellCochainGenerator A i.val k)
  change dualDiagonalWeightTopFunctional A S T u k nonempty
      ((dualDiagonalTopCellMap A S T u k i r hr).f n (topCellCochainGenerator A i.val k)) = _ at value
  rw [dualDiagonalTopCellMap_generator] at value
  intro zero
  exact topCellCochainTopFunctional_generator_ne_zero A i.val k (value.symm.trans zero)

end ToricPower.IntegralArrangement
