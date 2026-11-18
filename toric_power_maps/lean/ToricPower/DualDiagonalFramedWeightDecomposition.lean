module

public import ToricPower.DualDiagonalFramedWeightMatrix
public import ToricPower.ModuleDirectSumCoordinates
public import ToricPower.DualDiagonalWeightComparison

/-!
# Every character of the actual affine dual diagonal complex

The actual dual over the product-chart coordinate ring, after restriction
of scalars, is isomorphic as a complete complex to the unrestricted sum
of the original cellular weight complexes. Equality of every differential
entry proves the comparison. The resulting vanishing is consequently a
theorem about the original ring-linear complex itself.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [Field k] (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s))

/-- The full sum retains all integral total characters. -/
def dualDiagonalAllWeightComplex : CochainComplex (ModuleCat.{0} k) ℕ :=
  ModuleDirectSum.complex k (fun u => dualDiagonalWeightComplex A S T u k)

/-- Literal normalized-cell/Laurent coordinates of that full sum. -/
def dualDiagonalAllWeightCoordinates (q : ℕ) :
    (dualDiagonalAllWeightComplex k A S T).X q ≃ₗ[k]
      (DualDiagonalAllWeightIndex A S T q →₀ k) :=
  ModuleDirectSum.complexCoordinates k (fun u => dualDiagonalWeightComplex A S T u k)
    (fun u q => DualDiagonalWeightIndex A S T u q)
    (fun u q => translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
      (dualDiagonalWeightAllowed_map A S T u) k q) q

/-- The direct sum uses the original cellular matrix in each exact
character, and has zero coefficients between distinct characters. -/
theorem dualDiagonalAllWeightCoordinates_d_generator (q : ℕ)
    (x : DualDiagonalAllWeightIndex A S T q)
    (y : DualDiagonalAllWeightIndex A S T (q+1)) (r : k) :
    dualDiagonalAllWeightCoordinates k A S T (q+1)
      ((dualDiagonalAllWeightComplex k A S T).d q (q+1)
        ((dualDiagonalAllWeightCoordinates k A S T q).symm
          (Finsupp.single x r))) y =
      if x.1 = y.1 then
        diagonalGlobalColumn k A q y.2.1 (x.2.1, y.2.2.val - x.2.2.val) * r
      else 0 := by
  rcases x with ⟨u, i⟩
  rcases y with ⟨v, j⟩
  by_cases same : u = v
  · subst v
    rw [if_pos rfl]
    exact (ModuleDirectSum.complexCoordinates_d_generator_same k
      (fun u => dualDiagonalWeightComplex A S T u k)
      (fun u q => DualDiagonalWeightIndex A S T u q)
      (fun u q => translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
        (dualDiagonalWeightAllowed_map A S T u) k q) q (q+1) u i j r).trans
      (translatedWeightCellularCoordinates_d_generator A (dualDiagonalWeightAllowed A S T u)
        (dualDiagonalWeightAllowed_map A S T u) k q i j r)
  · rw [if_neg same]
    exact ModuleDirectSum.complexCoordinates_d_generator_ne k
      (fun u => dualDiagonalWeightComplex A S T u k)
      (fun u q => DualDiagonalWeightIndex A S T u q)
      (fun u q => translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
        (dualDiagonalWeightAllowed_map A S T u) k q) q (q+1) u v same i j r

variable (frames : ∀ q, DiagonalCellFrames A S T q)

/-- The two complete differentials agree on arbitrary finite sums,
proved from their independently computed actual basis coefficients. -/
theorem diagonalFramedDual_allWeight_differential (q : ℕ)
    (v : DualDiagonalAllWeightIndex A S T q →₀ k) :
    diagonalFramedDualScalarCoordinates k A S T frames (q+1)
      ((diagonalFramedDualScalarComplex k A S T frames).d q (q+1)
        ((diagonalFramedDualScalarCoordinates k A S T frames q).symm v)) =
    dualDiagonalAllWeightCoordinates k A S T (q+1)
      ((dualDiagonalAllWeightComplex k A S T).d q (q+1)
        ((dualDiagonalAllWeightCoordinates k A S T q).symm v)) := by
  let actual := (diagonalFramedDualScalarCoordinates k A S T frames (q+1)).toLinearMap.comp
    (((diagonalFramedDualScalarComplex k A S T frames).d q (q+1)).hom.comp
      (diagonalFramedDualScalarCoordinates k A S T frames q).symm.toLinearMap)
  let weighted := (dualDiagonalAllWeightCoordinates k A S T (q+1)).toLinearMap.comp
    (((dualDiagonalAllWeightComplex k A S T).d q (q+1)).hom.comp
      (dualDiagonalAllWeightCoordinates k A S T q).symm.toLinearMap)
  have equal : actual = weighted := by
    apply Finsupp.lhom_ext
    intro i r
    ext j
    exact (diagonalFramedDualScalarCoordinates_d_generator k A S T frames q i j r).trans
      (dualDiagonalAllWeightCoordinates_d_generator k A S T q i j r).symm
  exact DFunLike.congr_fun equal v

/-- The literal ring-linear dual, after scalar restriction, is the
complete unrestricted Laurent sum as an actual complex. -/
def diagonalFramedDualAllWeightIso :
    diagonalFramedDualScalarComplex k A S T frames ≅
      dualDiagonalAllWeightComplex k A S T :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => ((diagonalFramedDualScalarCoordinates k A S T frames q).trans
      (dualDiagonalAllWeightCoordinates k A S T q).symm).toModuleIso)
    (fun q t relation => by
      obtain rfl : t = q+1 := relation.symm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      apply (dualDiagonalAllWeightCoordinates k A S T (q+1)).injective
      change dualDiagonalAllWeightCoordinates k A S T (q+1)
          ((dualDiagonalAllWeightComplex k A S T).d q (q+1)
            ((dualDiagonalAllWeightCoordinates k A S T q).symm
              (diagonalFramedDualScalarCoordinates k A S T frames q v))) =
        dualDiagonalAllWeightCoordinates k A S T (q+1)
          ((dualDiagonalAllWeightCoordinates k A S T (q+1)).symm
            (diagonalFramedDualScalarCoordinates k A S T frames (q+1)
              ((diagonalFramedDualScalarComplex k A S T frames).d q (q+1) v)))
      rw [LinearEquiv.apply_symm_apply]
      have equal := diagonalFramedDual_allWeight_differential k A S T frames q
        (diagonalFramedDualScalarCoordinates k A S T frames q v)
      rw [LinearEquiv.symm_apply_apply] at equal
      exact equal.symm)

/-- Off the ambient degree, every full scalar weight vanishes. -/
theorem dualDiagonalAllWeightComplex_isZero_homology (q : ℕ) (different : q ≠ n) :
    IsZero ((dualDiagonalAllWeightComplex k A S T).homology q) := by
  have zero (u : Fin n → ℤ) : IsZero ((dualDiagonalWeightComplex A S T u k).homology q) := by
    by_cases nonempty : (dualDiagonalStrip A S T u).Nonempty
    · exact dualDiagonalWeightComplex_isZero_homology A S T u k nonempty q different
    · exact dualDiagonalWeightComplex_isZero_homology_of_empty A S T u k
        (Set.not_nonempty_iff_eq_empty.mp nonempty) q
  letI (u : Fin n → ℤ) : Subsingleton ((dualDiagonalWeightComplex A S T u k).homology q) :=
    ModuleCat.subsingleton_of_isZero (zero u)
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of k (Π₀ u : Fin n → ℤ, (dualDiagonalWeightComplex A S T u k).homology q))).of_iso
      (ModuleDirectSum.homologyIso k (fun u => dualDiagonalWeightComplex A S T u k) q)

/-- This is vanishing for the actual dual complex over the actual
product-chart coordinate ring, not merely for chosen scalar models. -/
theorem diagonalFramedDualComplex_isZero_homology (q : ℕ) (different : q ≠ n) :
    IsZero ((diagonalFramedDualComplex k A S T frames).homology q) := by
  let restrict := ModuleCat.restrictScalars (algebraMap k (DiagonalChartRing k A S T))
  have scalarZero : IsZero ((diagonalFramedDualScalarComplex k A S T frames).homology q) :=
    (dualDiagonalAllWeightComplex_isZero_homology k A S T q different).of_iso
      ((HomologicalComplex.homologyFunctor _ _ q).mapIso
        (diagonalFramedDualAllWeightIso k A S T frames))
  have actualZero : IsZero (restrict.obj ((diagonalFramedDualComplex k A S T frames).homology q)) :=
    scalarZero.of_iso (((diagonalFramedDualComplex k A S T frames).sc q).mapHomologyIso
      restrict).symm
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (ModuleCat.subsingleton_of_isZero (R := k) actualZero)

end ToricPower.IntegralArrangement
