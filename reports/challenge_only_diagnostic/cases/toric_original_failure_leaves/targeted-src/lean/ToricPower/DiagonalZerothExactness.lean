module

public import ToricPower.DiagonalChartExactness

/-!
# Zeroth exactness and surjectivity of the actual diagonal augmentation

The augmentation of a nonempty weight is the canonical quotient to its
zeroth cellular homology, followed by the actual singular augmentation.
Its kernel and surjectivity are proved using the genuine cokernel API.
An empty weight contributes a zero module, represented by the free module
on the empty type of proofs of nonemptiness.

Taking the algebraic direct sum over every lattice weight preserves this
kernel calculation and surjectivity.  This supplies the missing degree-zero
part of the local cellular resolution without bounding the weights.

Candidate source until the pinned compiler checks the full closure.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex
open scoped Classical

namespace ToricPower

section GeneralQuotient

variable {k : Type} [Ring k]

/-- The actual quotient map from zero chains to a specified genuine
zeroth homology isomorphism. -/
def zeroHomologyQuotient (K : ChainComplex (ModuleCat k) ℕ)
    {M : ModuleCat k} (e : K.homology 0 ≅ M) : (K.X 0) →ₗ[k] M :=
  (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ e.hom).hom

theorem zeroHomologyQuotient_exact (K : ChainComplex (ModuleCat k) ℕ)
    {M : ModuleCat k} (e : K.homology 0 ≅ M) :
    Function.Exact (K.d 1 0).hom (zeroHomologyQuotient K e) := by
  let S := ShortComplex.mk (K.d 1 0) (K.pOpcycles 0) (K.d_pOpcycles 1 0)
  have hS : S.Exact := S.exact_of_g_is_cokernel (K.opcyclesIsCokernel 1 0 (by simp))
  have hbase := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS
  let γ := K.isoHomologyι₀.symm ≪≫ e
  exact hbase.comp_injective γ.toLinearEquiv γ.toLinearEquiv.injective
    (map_zero γ.toLinearEquiv)

theorem zeroHomologyQuotient_surjective (K : ChainComplex (ModuleCat k) ℕ)
    {M : ModuleCat k} (e : K.homology 0 ≅ M) :
    Function.Surjective (zeroHomologyQuotient K e) := by
  let γ := K.isoHomologyι₀.symm ≪≫ e
  exact γ.toLinearEquiv.surjective.comp
    ((ModuleCat.epi_iff_surjective (K.pOpcycles 0)).mp inferInstance)

end GeneralQuotient

namespace IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)

local instance diagonalZerothExactnessPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

private local instance diagonalZerothExactnessStripCW (S T : Set (Fin s)) (u : Fin n → ℤ) :
    CWComplex (diagonalStripCarrier A S T u) :=
  inferInstanceAs (CWComplex (diagonalStripSubcomplex A S T u : Set (Fin n → ℝ)))

/-- The cellular basis, including the canonical identification of the
complex term with its skeletal relative-homology presentation. -/
def diagonalWeightChainCoordinates (S T : Set (Fin s)) (u : Fin n → ℤ) (d : ℕ) :
    (diagonalWeightCellComplex A (ModuleCat.of k k) S T u).X d ≃ₗ[k]
      (Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) d →₀ k) :=
  (eqToIso (TauCeti.cellularChainComplex_X
    (diagonalStripCarrier A S T u) (ModuleCat.of k k) d)).toLinearEquiv.trans
      (TauCeti.cellularChainBasis (diagonalStripCarrier A S T u) k d).repr

/-- The coordinate map commutes with the genuine complex differential,
retaining its canonical source and target transports. -/
theorem diagonalWeightChainCoordinates_boundary (S T : Set (Fin s))
    (u : Fin n → ℤ) (d : ℕ) :
    (diagonalWeightBoundaryCoordinates k A S T u d).comp
        (diagonalWeightChainCoordinates k A S T u (d+1)).toLinearMap =
      (diagonalWeightChainCoordinates k A S T u d).toLinearMap.comp
        ((diagonalWeightCellComplex A (ModuleCat.of k k) S T u).d (d+1) d).hom := by
  let C := diagonalStripCarrier A S T u
  let K := diagonalWeightCellComplex A (ModuleCat.of k k) S T u
  let e₁ := eqToIso (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) (d+1))
  let e₀ := eqToIso (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) d)
  have square : e₁.hom ≫ TauCeti.cellularDifferential C (ModuleCat.of k k) d =
      K.d (d+1) d ≫ e₀.hom := by
    change eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) (d+1)) ≫
        TauCeti.cellularDifferential C (ModuleCat.of k k) d =
      (TauCeti.cellularChainComplex C (ModuleCat.of k k)).d (d+1) d ≫
        eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) d)
    rw [TauCeti.cellularChainComplex_d]
    simp
  apply LinearMap.ext
  intro v
  exact (DFunLike.congr_fun (diagonalWeightBoundaryCoordinates_basis k A S T u d)
    (e₁.hom v)).trans
      (congrArg (TauCeti.cellularChainBasis C k d).repr
        (ConcreteCategory.congr_hom square v))

/-- The actual weight augmentation in its genuine cellular coefficient
basis. -/
def diagonalWeightAugmentationCoordinates (S T : Set (Fin s))
    (u : Fin n → ℤ) (hne : (diagonalStrip A S T u).Nonempty) :
    (Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) 0 →₀ k) →ₗ[k] k :=
  (zeroHomologyQuotient (diagonalWeightCellComplex A (ModuleCat.of k k) S T u)
    (diagonalWeightCellHomologyZeroIso A (ModuleCat.of k k) S T u hne)).comp
      (diagonalWeightChainCoordinates k A S T u 0).symm.toLinearMap

theorem diagonalWeightAugmentationCoordinates_exact (S T : Set (Fin s))
    (u : Fin n → ℤ) (hne : (diagonalStrip A S T u).Nonempty) :
    Function.Exact (diagonalWeightBoundaryCoordinates k A S T u 0)
      (diagonalWeightAugmentationCoordinates k A S T u hne) := by
  let C := diagonalStripCarrier A S T u
  let K := diagonalWeightCellComplex A (ModuleCat.of k k) S T u
  let e := diagonalWeightCellHomologyZeroIso A (ModuleCat.of k k) S T u hne
  have hbase := zeroHomologyQuotient_exact K e
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := diagonalWeightChainCoordinates k A S T u 1)
    (e₂ := diagonalWeightChainCoordinates k A S T u 0)
    (e₃ := LinearEquiv.refl k k)
    (diagonalWeightChainCoordinates_boundary k A S T u 0) ?_ hbase
  apply LinearMap.ext
  intro v
  simp only [diagonalWeightAugmentationCoordinates, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearEquiv.refl_apply]
  rfl

theorem diagonalWeightAugmentationCoordinates_surjective (S T : Set (Fin s))
    (u : Fin n → ℤ) (hne : (diagonalStrip A S T u).Nonempty) :
    Function.Surjective (diagonalWeightAugmentationCoordinates k A S T u hne) :=
  (zeroHomologyQuotient_surjective
    (diagonalWeightCellComplex A (ModuleCat.of k k) S T u)
    (diagonalWeightCellHomologyZeroIso A (ModuleCat.of k k) S T u hne)).comp
    (diagonalWeightChainCoordinates k A S T u 0).symm.surjective

/-- There is one target basis vector exactly when the literal strip is
nonempty, and no target basis vector otherwise. -/
abbrev DiagonalWeightAugmentationIndex (S T : Set (Fin s)) (u : Fin n → ℤ) :=
  PLift ((diagonalStrip A S T u).Nonempty)

def diagonalWeightSupportedAugmentation (S T : Set (Fin s)) (u : Fin n → ℤ) :
    (Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) 0 →₀ k) →ₗ[k]
      (DiagonalWeightAugmentationIndex A S T u →₀ k) :=
  if hne : (diagonalStrip A S T u).Nonempty then
    (Finsupp.lsingle ⟨hne⟩).comp
      (diagonalWeightAugmentationCoordinates k A S T u hne)
  else 0

theorem diagonalStrip_cells_isEmpty_of_empty (S T : Set (Fin s))
    (u : Fin n → ℤ) (hempty : ¬ (diagonalStrip A S T u).Nonempty) (d : ℕ) :
    IsEmpty (Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) d) := by
  refine ⟨fun c => ?_⟩
  obtain ⟨x,hx⟩ := c.val.property.1
  exact hempty ⟨x,(stripCellAllowed_iff_point A S T u c.val hx).mp c.property⟩

theorem diagonalWeightSupportedAugmentation_exact (S T : Set (Fin s))
    (u : Fin n → ℤ) :
    Function.Exact (diagonalWeightBoundaryCoordinates k A S T u 0)
      (diagonalWeightSupportedAugmentation k A S T u) := by
  by_cases hne : (diagonalStrip A S T u).Nonempty
  · rw [diagonalWeightSupportedAugmentation, dif_pos hne]
    exact (diagonalWeightAugmentationCoordinates_exact k A S T u hne).comp_injective
      (Finsupp.single (⟨hne⟩ : DiagonalWeightAugmentationIndex A S T u))
      (Finsupp.single_injective (⟨hne⟩ : DiagonalWeightAugmentationIndex A S T u))
      (Finsupp.single_zero _)
  · letI := diagonalStrip_cells_isEmpty_of_empty A S T u hne 0
    rw [diagonalWeightSupportedAugmentation, dif_neg hne]
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    simp only [LinearMap.zero_apply, Set.mem_range, map_zero, true_iff]
    exact ⟨0,map_zero _⟩

theorem diagonalWeightSupportedAugmentation_surjective (S T : Set (Fin s))
    (u : Fin n → ℤ) :
    Function.Surjective (diagonalWeightSupportedAugmentation k A S T u) := by
  intro v
  by_cases hne : (diagonalStrip A S T u).Nonempty
  · let point : DiagonalWeightAugmentationIndex A S T u := ⟨hne⟩
    obtain ⟨w,hw⟩ := diagonalWeightAugmentationCoordinates_surjective k A S T u hne
      (v point)
    refine ⟨w,?_⟩
    rw [diagonalWeightSupportedAugmentation, dif_pos hne]
    change Finsupp.single point
      (diagonalWeightAugmentationCoordinates k A S T u hne w) = v
    rw [hw]
    ext q
    have hq : q = point := Subsingleton.elim _ _
    subst q
    simp
  · letI : IsEmpty (DiagonalWeightAugmentationIndex A S T u) :=
      ⟨fun p => hne p.down⟩
    exact ⟨0,Subsingleton.elim _ _⟩

/-- The combined augmentation is the actual algebraic direct sum over
all integral weights. -/
def diagonalChartAugmentationCoordinates (S T : Set (Fin s)) :
    DiagonalChartChains k A S T 0 →ₗ[k]
      ((Σ u : Fin n → ℤ, DiagonalWeightAugmentationIndex A S T u) →₀ k) :=
  sigmaWeightMap (diagonalWeightSupportedAugmentation k A S T)

/-- Exactness at zero of the actual combined cellular matrix. -/
theorem diagonalChartAugmentationCoordinates_exact (S T : Set (Fin s)) :
    Function.Exact (diagonalChartBoundary k A S T 0)
      (diagonalChartAugmentationCoordinates k A S T) := by
  rw [diagonalChartBoundary_eq_sigmaWeightMap]
  exact exact_sigmaWeightMap _ _
    (fun u => diagonalWeightSupportedAugmentation_exact k A S T u)

/-- The combined augmentation is onto the full algebraic sum of its
genuine weight targets, with arbitrary finite support. -/
theorem diagonalChartAugmentationCoordinates_surjective (S T : Set (Fin s)) :
    Function.Surjective (diagonalChartAugmentationCoordinates k A S T) := by
  have hmap : Function.Surjective
      (DFinsupp.mapRange.linearMap (diagonalWeightSupportedAugmentation k A S T)) :=
    (DFinsupp.mapRange_surjective _ (fun u => map_zero _)).mpr
      (fun u => diagonalWeightSupportedAugmentation_surjective k A S T u)
  exact (sigmaFinsuppLequivDFinsupp k).symm.surjective.comp
    (hmap.comp (sigmaFinsuppLequivDFinsupp k).surjective)

end IntegralArrangement

end ToricPower
