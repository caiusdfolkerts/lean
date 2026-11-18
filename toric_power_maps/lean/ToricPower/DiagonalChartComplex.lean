module

public import ToricPower.DiagonalChartModules
public import ToricPower.DiagonalCellularAction
public import ToricPower.CellularMatrixNaturality

/-!
# The actual cellular chain complex over a product-chart ring

The differential is the finite-support boundary column of the genuine
cellular complex of each weight strip.  Naturality under literal chart
monomial translations proves that this differential is linear over the
whole product-chart coordinate ring.  Its square is zero by the actual
cellular boundary identity.

This constructs the module complex itself.  Exactness and its comparison
with line-bundle sections are separate propositions, not fields assumed
in the construction.

Candidate until the pinned compiler checks its complete dependency closure.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)

local instance diagonalChartComplexPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

private local instance diagonalChartComplexStripCW (S T : Set (Fin s)) (u : Fin n → ℤ) :
    CWComplex (diagonalStripCarrier A S T u) :=
  inferInstanceAs (CWComplex (diagonalStripSubcomplex A S T u : Set (Fin n → ℝ)))

/-- Each column is the actual cellular boundary of that cell, inserted
into the same total-character weight of the product-chart module. -/
def diagonalChartBoundaryColumn (S T : Set (Fin s)) (d : ℕ)
    (x : DiagonalChartCell A S T (d+1)) : DiagonalChartChains k A S T d :=
  diagonalWeightInjection k A S T x.1 d
    (TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T x.1) k d x.2)

/-- The actual coefficient-linear differential obtained from those
finite-support columns. -/
def diagonalChartBoundary (S T : Set (Fin s)) (d : ℕ) :
    DiagonalChartChains k A S T (d+1) →ₗ[k] DiagonalChartChains k A S T d :=
  Finsupp.linearCombination k (diagonalChartBoundaryColumn k A S T d)

@[simp]
theorem diagonalChartBoundary_single (S T : Set (Fin s)) (d : ℕ)
    (x : DiagonalChartCell A S T (d+1)) (r : k) :
    diagonalChartBoundary k A S T d (Finsupp.single x r) =
      r • diagonalChartBoundaryColumn k A S T d x :=
  Finsupp.linearCombination_single k r x

/-- The displayed differential really restricts to the cellular
differential in every actual character weight. -/
theorem diagonalChartBoundary_weight (S T : Set (Fin s))
    (u : Fin n → ℤ) (d : ℕ)
    (v : Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) (d+1) →₀ k) :
    diagonalChartBoundary k A S T d
        (diagonalWeightInjection k A S T u (d+1) v) =
      diagonalWeightInjection k A S T u d
        (Finsupp.linearCombination k
          (TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T u) k d) v) := by
  have h :
      (diagonalChartBoundary k A S T d).comp
        (diagonalWeightInjection k A S T u (d+1)) =
      (diagonalWeightInjection k A S T u d).comp
        (Finsupp.linearCombination k
          (TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T u) k d)) := by
    apply Finsupp.lhom_ext
    intro c r
    change diagonalChartBoundary k A S T d
        (diagonalWeightInjection k A S T u (d+1) (Finsupp.single c r)) =
      diagonalWeightInjection k A S T u d
        (Finsupp.linearCombination k
          (TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T u) k d)
          (Finsupp.single c r))
    rw [diagonalWeightInjection_single, diagonalChartBoundary_single]
    change r • diagonalWeightInjection k A S T u d
        (TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T u) k d c) = _
    rw [Finsupp.linearCombination_single, map_smul]
  exact DFunLike.congr_fun h v

/-- The square-zero identity is inherited from the genuine cellular
boundary identity separately in every total character. -/
theorem diagonalChartBoundary_comp (S T : Set (Fin s)) (d : ℕ) :
    (diagonalChartBoundary k A S T d).comp
      (diagonalChartBoundary k A S T (d+1)) = 0 := by
  apply Finsupp.lhom_ext
  rintro ⟨u,c⟩ r
  change diagonalChartBoundary k A S T d
      (diagonalChartBoundary k A S T (d+1) (Finsupp.single ⟨u,c⟩ r)) = 0
  rw [diagonalChartBoundary_single, map_smul]
  change r • diagonalChartBoundary k A S T d
      (diagonalWeightInjection k A S T u (d+1)
        (TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T u) k (d+1) c)) = 0
  rw [diagonalChartBoundary_weight, Finsupp.linearCombination_apply,
    TauCeti.cellularBoundaryColumn_sum_smul, map_zero, smul_zero]

/-- The boundary column of a translated cell is precisely the
translated entire column, including all coefficients outside the image. -/
theorem diagonalChartBoundaryColumn_translate (S T : Set (Fin s)) (d : ℕ)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (x : DiagonalChartCell A S T (d+1)) :
    diagonalChartBoundaryColumn k A S T d (diagonalChartTranslate A S T p x) =
      Finsupp.mapDomain (diagonalChartTranslate A S T p)
        (diagonalChartBoundaryColumn k A S T d x) := by
  rcases x with ⟨u,c⟩
  have hcol := cellularBoundaryColumn_naturality _ _
    (diagonalStripMultiplication_cellular A S T p u) k
    (fun q => diagonalStripCellTranslate A S T p u)
    (diagonalStripMultiplication_characteristic A S T p u) d c
  change Finsupp.mapDomain (Sigma.mk (u+p.1.val+p.2.val))
      (TauCeti.cellularBoundaryColumn
        (diagonalStripCarrier A S T (u+p.1.val+p.2.val)) k d
        (diagonalStripCellTranslate A S T p u c)) =
    Finsupp.mapDomain (diagonalChartTranslate A S T p)
      (Finsupp.mapDomain (Sigma.mk u)
        (TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T u) k d c))
  rw [hcol, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

/-- The coefficient-linear differential intertwines the actual monoid
actions, by its proved action on every basis vector. -/
theorem diagonalChartBoundary_monomial (S T : Set (Fin s)) (d : ℕ)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (v : DiagonalChartChains k A S T (d+1)) :
    diagonalChartBoundary k A S T d
      (Finsupp.mapDomain (diagonalChartTranslate A S T p) v) =
    Finsupp.mapDomain (diagonalChartTranslate A S T p)
      (diagonalChartBoundary k A S T d v) := by
  have h :
      (diagonalChartBoundary k A S T d).comp
        (Finsupp.lmapDomain k k (diagonalChartTranslate A S T p)) =
      (Finsupp.lmapDomain k k (diagonalChartTranslate A S T p)).comp
        (diagonalChartBoundary k A S T d) := by
    apply Finsupp.lhom_ext
    intro x r
    change diagonalChartBoundary k A S T d
        (Finsupp.mapDomain (diagonalChartTranslate A S T p) (Finsupp.single x r)) =
      Finsupp.mapDomain (diagonalChartTranslate A S T p)
        (diagonalChartBoundary k A S T d (Finsupp.single x r))
    rw [Finsupp.mapDomain_single, diagonalChartBoundary_single,
      diagonalChartBoundary_single, diagonalChartBoundaryColumn_translate]
    exact (Finsupp.mapDomain_smul (f := diagonalChartTranslate A S T p) r
      (diagonalChartBoundaryColumn k A S T d x)).symm
  exact DFunLike.congr_fun h v

/-- Finite linear combination of the monomial compatibility proves
linearity over the entire actual product-chart ring. -/
theorem diagonalChartBoundary_smul (S T : Set (Fin s)) (d : ℕ)
    (r : DiagonalChartRing k A S T) (v : DiagonalChartChains k A S T (d+1)) :
    diagonalChartBoundary k A S T d (r • v) =
      r • diagonalChartBoundary k A S T d v := by
  induction r using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add p a r _ _ ih =>
      rw [add_smul, map_add, ih, add_smul]
      congr 1
      rw [diagonalChartChains_single_smul, diagonalChartChains_single_smul,
        map_smul, diagonalChartBoundary_monomial]

/-- The genuine differential as a morphism over the product-chart
coordinate ring. -/
def diagonalChartBoundaryLinear (S T : Set (Fin s)) (d : ℕ) :
    DiagonalChartChains k A S T (d+1) →ₗ[DiagonalChartRing k A S T]
      DiagonalChartChains k A S T d where
  toFun := diagonalChartBoundary k A S T d
  map_add' := (diagonalChartBoundary k A S T d).map_add
  map_smul' := diagonalChartBoundary_smul k A S T d

/-- The actual module complex which will glue to the cellular diagonal
complex of line bundles. -/
def diagonalChartComplex (S T : Set (Fin s)) :
    ChainComplex (ModuleCat.{0} (DiagonalChartRing k A S T)) ℕ :=
  ChainComplex.of
    (fun d => ModuleCat.of (DiagonalChartRing k A S T) (DiagonalChartChains k A S T d))
    (fun d => ModuleCat.ofHom (diagonalChartBoundaryLinear k A S T d))
    (fun d => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      exact DFunLike.congr_fun (diagonalChartBoundary_comp k A S T d) v)

end ToricPower.IntegralArrangement
