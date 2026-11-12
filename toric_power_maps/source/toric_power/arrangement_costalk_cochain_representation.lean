module

public import ToricPower.ArrangementCostalkRepresentation
public import ToricPower.ArrangementCostalkDuality

/-!
# The actual finite cochain matrix for a representable costalk

The scalar dual of the independently displayed representable incidence
matrix is identified with the genuine relative cellular cochain complex.
Every term has the finite basis of normalized cofaces, actual incidences,
and permitted monomial weights proved in `ArrangementCostalkCells`.
The displayed differential is the transpose of the original periodic
incidence matrix, including its translation `a_target - a_source`.

The top cohomology and its vanishing outside the ambient degree are
transported from actual relative singular homology. Nothing in this file
assumes a cellular realization theorem or a coherent--constructible
equivalence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite Set
open scoped Classical

namespace ToricPower

variable (𝕜 : Type) [Field 𝕜]

/-- Actual scalar duality on a finite free module, in its literal basis.
Finiteness is used only to identify functions with finitely supported
functions; the index set itself comes from the proved finite costalk. -/
def finiteFreeScalarDualEquiv (I : Type) [Finite I] :
    (ModuleCat.of 𝕜 (I →₀ 𝕜) ⟶ ModuleCat.of 𝕜 𝕜) ≃ₗ[𝕜] (I →₀ 𝕜) :=
  ModuleCat.homLinearEquiv.trans
    ((Finsupp.llift 𝕜 𝕜 𝕜 I).symm.trans
      (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 I).symm)

@[simp]
theorem finiteFreeScalarDualEquiv_apply (I : Type) [Finite I]
    (f : ModuleCat.of 𝕜 (I →₀ 𝕜) ⟶ ModuleCat.of 𝕜 𝕜) (i : I) :
    finiteFreeScalarDualEquiv 𝕜 I f i = f (Finsupp.single i 1) := rfl

/-- Evaluation of a linear functional is the literal finite coefficient
sum in the chosen free basis. -/
theorem finiteFreeScalarDualEquiv_evaluate (I : Type) [Finite I]
    (f : ModuleCat.of 𝕜 (I →₀ 𝕜) ⟶ ModuleCat.of 𝕜 𝕜) (v : I →₀ 𝕜) :
    f v = v.sum (fun i a => a * finiteFreeScalarDualEquiv 𝕜 I f i) := by
  have inverse := (finiteFreeScalarDualEquiv 𝕜 I).symm_apply_apply f
  apply Eq.trans (congrArg (fun g : ModuleCat.of 𝕜 (I →₀ 𝕜) ⟶
    ModuleCat.of 𝕜 𝕜 => g v) inverse.symm) ?_
  rfl

namespace IntegralArrangement

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)
  (c : IncidenceObject matrix) (S : Set (Fin s)) (m : Fin n → ℤ)

local notation "indices" => RepresentableCostalkIndex matrix c S m

/-- The scalar dual of the independent normalized incidence matrix.
Its differential is the actual transposed matrix, not an assumed
exact complex. -/
def representableCostalkCochainComplex : CochainComplex (ModuleCat.{0} 𝕜) ℕ :=
  scalarDualComplex 𝕜 (representableCostalkChainComplex matrix c S m 𝕜)

/-- Every cochain term, in the finite basis of genuine cofaces and
allowed monomials. -/
def representableCostalkCochainCoordinates (q : ℕ) :
    (representableCostalkCochainComplex 𝕜 matrix c S m).X q ≃ₗ[𝕜]
      (indices q →₀ 𝕜) :=
  finiteFreeScalarDualEquiv 𝕜 (indices q)

/-- The whole displayed cochain differential is the transpose of the
original periodic incidence matrix in actual monomial coordinates. -/
theorem representableCostalkCochainCoordinates_differential (q : ℕ)
    (f : (representableCostalkCochainComplex 𝕜 matrix c S m).X q)
    (j : indices (q + 1)) :
    representableCostalkCochainCoordinates 𝕜 matrix c S m (q + 1)
        ((representableCostalkCochainComplex 𝕜 matrix c S m).d q (q + 1) f) j =
      (representableCostalkColumn matrix c S m 𝕜 q j).sum
        (fun i a => a * representableCostalkCochainCoordinates 𝕜 matrix c S m q f i) := by
  change (ModuleCat.of 𝕜 (indices q →₀ 𝕜) ⟶ ModuleCat.of 𝕜 𝕜) at f
  change f ((representableCostalkChainComplex matrix c S m 𝕜).d (q + 1) q
    (Finsupp.single j 1)) = _
  rw [representableCostalkChainComplex_d]
  change f (representableCostalkBoundary matrix c S m 𝕜 q (Finsupp.single j 1)) = _
  rw [representableCostalkBoundary, Finsupp.linearCombination_single, one_smul]
  exact finiteFreeScalarDualEquiv_evaluate 𝕜 (indices q) f _

/-- The independent finite representable matrix is the genuine relative
cellular cochain complex. This is an isomorphism of actual complexes. -/
def representableCostalkCochainIso :
    representableCostalkCochainComplex 𝕜 matrix c S m ≅
      periodicCostalkCochainComplex matrix (Sum.inl '' S)
        (augmentedLatticePairing matrix m) (incidenceCellCenter matrix c) 𝕜 :=
  ((scalarDual 𝕜).mapHomologicalComplex _).mapIso
    ((HomologicalComplex.opFunctor _ _).mapIso
      (representableCostalkChainIso matrix c S m 𝕜).op)

/-- The actual ambient orientation supplies the unique top coefficient
whenever the literal costalk region is nonempty. -/
def representableCostalkCochainHomologyIso
    (nonempty : (costalkRegion (augmentedForms matrix) (Sum.inl '' S)
      (augmentedLatticePairing matrix m) (incidenceCellCenter matrix c)).Nonempty) :
    (representableCostalkCochainComplex 𝕜 matrix c S m).homology n ≅
      ModuleCat.of 𝕜 𝕜 :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (representableCostalkCochainIso 𝕜 matrix c S m) ≪≫
    periodicCostalkCochainHomologyIso matrix _ _ _ 𝕜 nonempty

/-- The finite matrix has zero cohomology outside the ambient degree. -/
theorem representableCostalkCochainComplex_isZero_homology
    (nonempty : (costalkRegion (augmentedForms matrix) (Sum.inl '' S)
      (augmentedLatticePairing matrix m) (incidenceCellCenter matrix c)).Nonempty)
    (q : ℕ) (different : q ≠ n) :
    IsZero ((representableCostalkCochainComplex 𝕜 matrix c S m).homology q) :=
  (periodicCostalkCochainComplex_isZero_homology matrix _ _ _ 𝕜 nonempty q different).of_iso
    ((HomologicalComplex.homologyFunctor _ _ q).mapIso
      (representableCostalkCochainIso 𝕜 matrix c S m))

/-- A forbidden weight makes the actual representable cochain matrix
acyclic in every degree, including degree zero. -/
theorem representableCostalkCochainComplex_isZero_homology_of_empty
    (empty : costalkRegion (augmentedForms matrix) (Sum.inl '' S)
      (augmentedLatticePairing matrix m) (incidenceCellCenter matrix c) = ∅) (q : ℕ) :
    IsZero ((representableCostalkCochainComplex 𝕜 matrix c S m).homology q) :=
  (periodicCostalkCochainComplex_isZero_homology_of_empty matrix _ _ _ 𝕜 empty q).of_iso
    ((HomologicalComplex.homologyFunctor _ _ q).mapIso
      (representableCostalkCochainIso 𝕜 matrix c S m))

end IntegralArrangement
end ToricPower
