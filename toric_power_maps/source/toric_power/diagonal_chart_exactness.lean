module

public import ToricPower.DiagonalChartComplex
public import ToricPower.GradedExactness
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Positive exactness of the actual product-chart cellular complex

The local complex is split into all of its genuine character weights.
For a nonempty strip, convexity and the cellular–singular comparison
prove exactness.  An empty strip has no cells.  Direct-sum exactness then
proves positive exactness of the displayed module complex over the
product-chart ring, without restricting its character support.

Candidate until its complete dependency closure is checked by Lean.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)

local instance diagonalChartExactnessPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

private local instance diagonalChartExactnessStripCW (S T : Set (Fin s)) (u : Fin n → ℤ) :
    CWComplex (diagonalStripCarrier A S T u) :=
  inferInstanceAs (CWComplex (diagonalStripSubcomplex A S T u : Set (Fin n → ℝ)))

/-- The actual cellular differential in its monomial coefficient basis. -/
def diagonalWeightBoundaryCoordinates (S T : Set (Fin s))
    (u : Fin n → ℤ) (d : ℕ) :
    (Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) (d+1) →₀ k) →ₗ[k]
      (Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) d →₀ k) :=
  Finsupp.linearCombination k
    (TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T u) k d)

/-- This coordinate differential is conjugate to the actual cellular
differential by the actual cellular basis. -/
theorem diagonalWeightBoundaryCoordinates_basis (S T : Set (Fin s))
    (u : Fin n → ℤ) (d : ℕ) :
    (diagonalWeightBoundaryCoordinates k A S T u d).comp
      (TauCeti.cellularChainBasis (diagonalStripCarrier A S T u) k (d+1)).repr.toLinearMap =
    (TauCeti.cellularChainBasis (diagonalStripCarrier A S T u) k d).repr.toLinearMap.comp
      (TauCeti.cellularDifferential (diagonalStripCarrier A S T u) (ModuleCat.of k k) d).hom := by
  apply LinearMap.ext
  intro v
  exact (TauCeti.cellularChainBasis_repr_differential
    (diagonalStripCarrier A S T u) k d v).symm

/-- Every actual weight complex is exact in every positive degree,
including the weights whose strips are empty. -/
theorem diagonalWeightBoundaryCoordinates_exact (S T : Set (Fin s))
    (u : Fin n → ℤ) (d : ℕ) :
    Function.Exact (diagonalWeightBoundaryCoordinates k A S T u (d+1))
      (diagonalWeightBoundaryCoordinates k A S T u d) := by
  let C := diagonalStripCarrier A S T u
  let K := diagonalWeightCellComplex A (ModuleCat.of k k) S T u
  have hexact : K.ExactAt (d+1) := by
    by_cases hne : (diagonalStrip A S T u).Nonempty
    · exact diagonalWeightCellComplex_exactAt A (ModuleCat.of k k) S T u hne
        (Nat.succ_ne_zero d)
    · letI : IsEmpty (Topology.RelCWComplex.cell C (d+1)) := by
        refine ⟨fun c => ?_⟩
        obtain ⟨x, hx⟩ := c.val.property.1
        exact hne ⟨x, (stripCellAllowed_iff_point A S T u c.val hx).mp c.property⟩
      apply HomologicalComplex.ExactAt.of_isZero
      change IsZero ((TauCeti.cellularChainComplex C (ModuleCat.of k k)).X (d+1))
      rw [TauCeti.cellularChainComplex_X]
      exact TauCeti.isZero_cellularChainGroup C (d+1) (ModuleCat.of k k)
  have hshort := (HomologicalComplex.exactAt_iff' K (d+2) (d+1) d
    (by simp) (by simp)).mp hexact
  let S₀ := ShortComplex.mk
    (TauCeti.cellularDifferential C (ModuleCat.of k k) (d+1))
    (TauCeti.cellularDifferential C (ModuleCat.of k k) d)
    (TauCeti.cellularDifferential_comp_cellularDifferential C (ModuleCat.of k k) d)
  let e : K.sc' (d+2) (d+1) d ≅ S₀ := ShortComplex.isoMk
    (eqToIso (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) (d+2)))
    (eqToIso (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) (d+1)))
    (eqToIso (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) d))
    (by
      change eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) (d+2)) ≫
          TauCeti.cellularDifferential C (ModuleCat.of k k) (d+1) =
        (TauCeti.cellularChainComplex C (ModuleCat.of k k)).d (d+2) (d+1) ≫
          eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) (d+1))
      rw [TauCeti.cellularChainComplex_d]
      simp)
    (by
      change eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) (d+1)) ≫
          TauCeti.cellularDifferential C (ModuleCat.of k k) d =
        (TauCeti.cellularChainComplex C (ModuleCat.of k k)).d (d+1) d ≫
          eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) d)
      rw [TauCeti.cellularChainComplex_d]
      simp)
  have hfun := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₀).mp
    ((ShortComplex.exact_iff_of_iso e).mp hshort)
  exact Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := (TauCeti.cellularChainBasis C k (d+2)).repr)
    (e₂ := (TauCeti.cellularChainBasis C k (d+1)).repr)
    (e₃ := (TauCeti.cellularChainBasis C k d).repr)
    (diagonalWeightBoundaryCoordinates_basis k A S T u (d+1))
    (diagonalWeightBoundaryCoordinates_basis k A S T u d) hfun

/-- The displayed product-chart matrix is exactly the direct sum of
the actual weight matrices, as an equality of coefficient-linear maps. -/
theorem diagonalChartBoundary_eq_sigmaWeightMap (S T : Set (Fin s)) (d : ℕ) :
    diagonalChartBoundary k A S T d =
      sigmaWeightMap (fun u => diagonalWeightBoundaryCoordinates k A S T u d) := by
  apply Finsupp.lhom_ext
  rintro ⟨u,c⟩ r
  refine (diagonalChartBoundary_single k A S T d ⟨u,c⟩ r).trans ?_
  apply Eq.trans ?_ (sigmaWeightMap_single
    (fun u => diagonalWeightBoundaryCoordinates k A S T u d) u c r).symm
  change r • diagonalWeightInjection k A S T u d
      (TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T u) k d c) =
    diagonalWeightInjection k A S T u d
      (Finsupp.linearCombination k
        (TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T u) k d)
        (Finsupp.single c r))
  rw [Finsupp.linearCombination_single, map_smul]

/-- Exactness of the actual combined monomial matrices follows from
the checked direct-sum kernel/range calculation. -/
theorem diagonalChartBoundary_exact (S T : Set (Fin s)) (d : ℕ) :
    Function.Exact (diagonalChartBoundary k A S T (d+1))
      (diagonalChartBoundary k A S T d) := by
  rw [diagonalChartBoundary_eq_sigmaWeightMap, diagonalChartBoundary_eq_sigmaWeightMap]
  exact exact_sigmaWeightMap _ _
    (fun u => diagonalWeightBoundaryCoordinates_exact k A S T u d)

@[simp]
theorem diagonalChartComplex_d (S T : Set (Fin s)) (d : ℕ) :
    (diagonalChartComplex k A S T).d (d+1) d =
      ModuleCat.ofHom (diagonalChartBoundaryLinear k A S T d) := by
  unfold diagonalChartComplex
  simp only [ChainComplex.of_d]

/-- The actual complex over the affine product-chart ring is exact in
all strictly positive degrees. -/
theorem diagonalChartComplex_exactAt (S T : Set (Fin s)) (d : ℕ) :
    (diagonalChartComplex k A S T).ExactAt (d+1) := by
  apply (HomologicalComplex.exactAt_iff' _ (d+2) (d+1) d (by simp) (by simp)).mpr
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact
    ((diagonalChartComplex k A S T).d (d+2) (d+1))
    ((diagonalChartComplex k A S T).d (d+1) d)
  rw [diagonalChartComplex_d, diagonalChartComplex_d]
  exact diagonalChartBoundary_exact k A S T d

end ToricPower.IntegralArrangement
