module

public import ToricPower.ArrangementCostalkCellular
public import ToricPower.LinearDualHomology

/-!
# Scalar cochains of the actual arrangement costalk pair

These cochains are the scalar dual of the genuine periodic relative
cellular complex. Their cohomology is one copy of the coefficient field
in the ambient degree when the literal costalk region is nonempty, and
zero otherwise. The complex itself vanishes above the ambient dimension.
The comparison keeps scalar multiplication throughout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Set Opposite

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (weight : Fin s ⊕ Fin n → ℤ) (x : Fin n → ℝ)
  {k : Type} [Ring k] (M : ModuleCat.{0} k)

/-- No relative cells occur above the dimension of the actual ambient
vector space; this is independent of the costalk inequalities. -/
theorem periodicCostalkCellComplex_isZero_X_above (q : ℕ) (above : n < q) :
    IsZero ((periodicCostalkCellComplex matrix selected weight x M).X q) := by
  letI : RelCWComplex (univ : Set (Fin n → ℝ))
      (costalkRegion (augmentedForms matrix) selected weight x)ᶜ :=
    periodicCostalkRelativeCWComplex matrix selected weight x
  letI : IsEmpty (Topology.RelCWComplex.cell (univ : Set (Fin n → ℝ)) q) := by
    refine ⟨fun c => ?_⟩
    change { c : Cell (augmentedForms matrix) q //
      cellCenter (augmentedForms matrix) c ∉
        (costalkRegion (augmentedForms matrix) selected weight x)ᶜ } at c
    exact (not_lt_of_ge (cell_dimension_le matrix c.val) above).elim
  change IsZero ((TauCeti.cellularChainComplex (univ : Set (Fin n → ℝ)) M).X q)
  rw [TauCeti.cellularChainComplex_X]
  exact TauCeti.isZero_cellularChainGroup (univ : Set (Fin n → ℝ)) q M

/-- An empty literal region has the entire ambient space as its base,
so every term of its relative cellular chain complex is zero. -/
theorem periodicCostalkCellComplex_isZero_X_of_empty
    (empty : costalkRegion (augmentedForms matrix) selected weight x = ∅) (q : ℕ) :
    IsZero ((periodicCostalkCellComplex matrix selected weight x M).X q) := by
  letI : RelCWComplex (univ : Set (Fin n → ℝ))
      (costalkRegion (augmentedForms matrix) selected weight x)ᶜ :=
    periodicCostalkRelativeCWComplex matrix selected weight x
  letI : IsEmpty (Topology.RelCWComplex.cell (univ : Set (Fin n → ℝ)) q) := by
    refine ⟨fun c => ?_⟩
    change { c : Cell (augmentedForms matrix) q //
      cellCenter (augmentedForms matrix) c ∉
        (costalkRegion (augmentedForms matrix) selected weight x)ᶜ } at c
    apply c.property
    change cellCenter (augmentedForms matrix) c.val ∈
      (costalkRegion (augmentedForms matrix) selected weight x)ᶜ
    simp only [empty, compl_empty, mem_univ]
  change IsZero ((TauCeti.cellularChainComplex (univ : Set (Fin n → ℝ)) M).X q)
  rw [TauCeti.cellularChainComplex_X]
  exact TauCeti.isZero_cellularChainGroup (univ : Set (Fin n → ℝ)) q M

theorem periodicCostalkCellComplex_isZero_homology_of_empty
    (empty : costalkRegion (augmentedForms matrix) selected weight x = ∅) (q : ℕ) :
    IsZero ((periodicCostalkCellComplex matrix selected weight x M).homology q) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    (periodicCostalkCellComplex_isZero_X_of_empty matrix selected weight x M empty q)

section Field

variable (𝕜 : Type) [Field 𝕜]

/-- Actual scalar cochains on the periodic relative CW costalk pair. -/
def periodicCostalkCochainComplex : CochainComplex (ModuleCat.{0} 𝕜) ℕ :=
  scalarDualComplex 𝕜
    (periodicCostalkCellComplex matrix selected weight x (ModuleCat.of 𝕜 𝕜))

/-- The top cohomology uses the actual scalar dual of the coherent
ambient top class, followed by evaluation at one. -/
def periodicCostalkCochainHomologyIso
    (nonempty : (costalkRegion (augmentedForms matrix) selected weight x).Nonempty) :
    (periodicCostalkCochainComplex matrix selected weight x 𝕜).homology n ≅
      ModuleCat.of 𝕜 𝕜 :=
  scalarDualHomologyIso 𝕜 _ n ≪≫
    (scalarDual 𝕜).mapIso
      (periodicCostalkCellHomologyIso matrix selected weight x
        (ModuleCat.of 𝕜 𝕜) nonempty).symm.op ≪≫ scalarDualUnitIso 𝕜

/-- The nonempty costalk complex has cohomology only in ambient degree. -/
theorem periodicCostalkCochainComplex_isZero_homology
    (nonempty : (costalkRegion (augmentedForms matrix) selected weight x).Nonempty)
    (q : ℕ) (different : q ≠ n) :
    IsZero ((periodicCostalkCochainComplex matrix selected weight x 𝕜).homology q) :=
  scalarDualComplex_isZero_homology 𝕜 _ q
    (periodicCostalkCellComplex_isZero_homology matrix selected weight x
      (ModuleCat.of 𝕜 𝕜) nonempty q different)

/-- Empty costalk regions give zero cohomology in every degree. -/
theorem periodicCostalkCochainComplex_isZero_homology_of_empty
    (empty : costalkRegion (augmentedForms matrix) selected weight x = ∅) (q : ℕ) :
    IsZero ((periodicCostalkCochainComplex matrix selected weight x 𝕜).homology q) :=
  scalarDualComplex_isZero_homology 𝕜 _ q
    (periodicCostalkCellComplex_isZero_homology_of_empty matrix selected weight x
      (ModuleCat.of 𝕜 𝕜) empty q)

/-- The cochain model has finite length before passing to cohomology. -/
theorem periodicCostalkCochainComplex_isZero_X_above (q : ℕ) (above : n < q) :
    IsZero ((periodicCostalkCochainComplex matrix selected weight x 𝕜).X q) :=
  (scalarDual 𝕜).map_isZero
    (periodicCostalkCellComplex_isZero_X_above matrix selected weight x
      (ModuleCat.of 𝕜 𝕜) q above).op

end Field
end ToricPower.IntegralArrangement
