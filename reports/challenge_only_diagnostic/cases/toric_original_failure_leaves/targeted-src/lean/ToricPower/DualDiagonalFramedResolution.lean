module

public import ToricPower.DualDiagonalTopModule
public import ToricPower.TopHomologyAugmentation

/-!
# A genuine quasi-isomorphism for the ring-linear dual diagonal

The finite actual dual complex maps canonically to the boundary-weight
module in ambient degree. Its quasi-isomorphism follows from the complete
ring-linear top-class calculation and the vanishing of every other
homology group. The map is not an unspecified derived isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [Field k] (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s)) (frames : ∀ q, DiagonalCellFrames A S T q)

/-- The genuine dual free complex has no terms above ambient rank. -/
theorem diagonalFramedDualComplex_isZero_X_above (q : ℕ) (above : n < q) :
    IsZero ((diagonalFramedDualComplex k A S T frames).X q) := by
  letI : IsEmpty (NormalizedCell A q) :=
    ⟨fun c => (not_lt_of_ge (cell_dimension_le A c.val) above).elim⟩
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of (DiagonalChartRing k A S T)
      (NormalizedCell A q →₀ DiagonalChartRing k A S T))).of_iso
        (diagonalFramedDualCoordinates k A S T frames q).toModuleIso

theorem diagonalFramedDualComplex_top_differential :
    (diagonalFramedDualComplex k A S T frames).d n (n+1) = 0 :=
  (diagonalFramedDualComplex_isZero_X_above k A S T frames (n+1) (Nat.lt_succ_self n)).eq_of_tgt _ _

/-- The canonical actual module cochain map to the boundary coefficient
module placed in the intended ambient degree. -/
def diagonalFramedDualAugmentation :
    diagonalFramedDualComplex k A S T frames ⟶
      (HomologicalComplex.single (ModuleCat (DiagonalChartRing k A S T)) (.up ℕ) n).obj
        (dualDiagonalBoundaryModule A S T k) :=
  augmentationOfTopHomology (diagonalFramedDualComplex k A S T frames) n
    (diagonalFramedDualComplex_top_differential k A S T frames)
    (diagonalFramedDualTopModuleIso k A S T frames).hom

/-- All weights, all ring scalars, and the full finite cochain complex
are retained in this actual quasi-isomorphism. -/
theorem diagonalFramedDualAugmentation_quasiIso :
    QuasiIso (diagonalFramedDualAugmentation k A S T frames) :=
  augmentationOfTopHomology_quasiIso (diagonalFramedDualComplex k A S T frames) n
    (diagonalFramedDualComplex_top_differential k A S T frames)
    (diagonalFramedDualTopModuleIso k A S T frames)
    (diagonalFramedDualComplex_isZero_homology k A S T frames)

end ToricPower.IntegralArrangement
