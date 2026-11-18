module

public import ToricPower.ArrangementCostalkCells
public import ToricPower.CWRelativeCellularBoundary

/-!
# The actual representable costalk matrix

The geometric relative CW basis is reindexed by normalized cofaces and
their genuine incidences from the source cell. In these coordinates the
boundary coefficient is the original periodic incidence with translation
`a_target - a_source`. This is exactly the translation imposed by
composition of incidences. No new boundary signs or matrix entries are
postulated.

The resulting finite matrix is compared with the actual cellular
differential in characteristic-disk coordinates. All character weights
remain unrestricted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)
  (c : IncidenceObject matrix) (S : Set (Fin s)) (m : Fin n → ℤ)

local instance costalkRepresentationPeriodicCW : CWComplex (arrangementCarrier matrix) :=
  periodicArrangementCWComplex matrix

local notation "base" => periodicCostalkComplementSubcomplex matrix (Sum.inl '' S)
  (augmentedLatticePairing matrix m) (incidenceCellCenter matrix c)
local notation "carrier" => relativeCWCarrier base
local notation "indices" => RepresentableCostalkIndex matrix c S m

/-- The inverse indexing equivalence retains the literal universal-cover
cell, translated by the negative of its incidence vector. -/
@[simp]
theorem periodicCostalkRepresentableCellEquiv_symm_val (q : ℕ) (p : indices q) :
    ((periodicCostalkRepresentableCellEquiv matrix c S m q).symm p).val =
      translateCell matrix (-p.val.2.val) p.val.1.val := rfl

variable (R : Type) [Ring R]

/-- The actual periodic incidence required by composition of the two
recorded incidences from the source cell. -/
def representableCostalkIncidence (q : ℕ) (i : indices q) (j : indices (q + 1)) : R :=
  TauCeti.cellularIncidence (arrangementCarrier matrix) R q
    (translateCell matrix (j.val.2.val - i.val.2.val) i.val.1.val) j.val.1.val

/-- The genuine relative differential has exactly the displayed
normalized coefficient, with the original periodic orientations. -/
theorem representableCostalkIncidence_eq_relative (q : ℕ)
    (i : indices q) (j : indices (q + 1)) :
    TauCeti.cellularIncidence carrier R q
        ((periodicCostalkRepresentableCellEquiv matrix c S m q).symm i)
        ((periodicCostalkRepresentableCellEquiv matrix c S m (q + 1)).symm j) =
      representableCostalkIncidence matrix c S m R q i j := by
  apply Eq.trans (relativeCellularIncidence (arrangementCarrier matrix) base R q _ _) ?_
  change TauCeti.cellularIncidence (arrangementCarrier matrix) R q
      (translateCell matrix (-i.val.2.val) i.val.1.val)
      (translateCell matrix (-j.val.2.val) j.val.1.val) = _
  have translated := arrangement_cellularIncidence_translate matrix R j.val.2.val q
    (translateCell matrix (-i.val.2.val) i.val.1.val)
    (translateCell matrix (-j.val.2.val) j.val.1.val)
  simp only [translateCell_add, neg_add_cancel, translateCell_zero] at translated
  have difference : -i.val.2.val + j.val.2.val = j.val.2.val - i.val.2.val := by abel
  rw [difference] at translated
  exact translated.symm

/-- The actual characteristic-disk basis with its independent
representable and monomial indexing. -/
def representableCostalkBasis (q : ℕ) :
    Module.Basis (indices q) R
      (TauCeti.cellularChainGroup carrier (ModuleCat.of R R) q : ModuleCat R) :=
  (TauCeti.cellularChainBasis carrier R q).reindex
    (periodicCostalkRepresentableCellEquiv matrix c S m q)

/-- The complete matrix coefficient formula, on genuine cellular chain
groups and their actual singular-homology differential. -/
theorem representableCostalkBasis_differential (q : ℕ)
    (i : indices q) (j : indices (q + 1)) :
    (representableCostalkBasis matrix c S m R q).repr
        (TauCeti.cellularDifferential carrier (ModuleCat.of R R) q
          (representableCostalkBasis matrix c S m R (q + 1) j)) i =
      representableCostalkIncidence matrix c S m R q i j := by
  simp only [representableCostalkBasis, Module.Basis.repr_reindex_apply,
    Module.Basis.reindex_apply]
  exact (TauCeti.cellularIncidence_def carrier R q _ _).symm.trans
    (representableCostalkIncidence_eq_relative matrix c S m R q i j)

/-- The finite column is defined by the literal normalized periodic
incidences, independently of the relative cellular differential. -/
def representableCostalkColumn (q : ℕ) (j : indices (q + 1)) : indices q →₀ R :=
  Finsupp.equivFunOnFinite.symm (fun i => representableCostalkIncidence matrix c S m R q i j)

@[simp]
theorem representableCostalkColumn_apply (q : ℕ) (i : indices q) (j : indices (q + 1)) :
    representableCostalkColumn matrix c S m R q j i =
      representableCostalkIncidence matrix c S m R q i j := by
  rfl

/-- The actual finite representable matrix in coefficient coordinates. -/
def representableCostalkBoundary (q : ℕ) :
    (indices (q + 1) →₀ R) →ₗ[R] (indices q →₀ R) :=
  Finsupp.linearCombination R (representableCostalkColumn matrix c S m R q)

/-- The displayed matrix is conjugate to the actual cellular
differential by the actual basis. This is a full linear-map equality. -/
theorem representableCostalkBoundary_basis (q : ℕ) :
    (representableCostalkBoundary matrix c S m R q).comp
        (representableCostalkBasis matrix c S m R (q + 1)).repr.toLinearMap =
      (representableCostalkBasis matrix c S m R q).repr.toLinearMap.comp
        (TauCeti.cellularDifferential carrier (ModuleCat.of R R) q).hom := by
  apply (representableCostalkBasis matrix c S m R (q + 1)).ext
  intro j
  change representableCostalkBoundary matrix c S m R q
      ((representableCostalkBasis matrix c S m R (q + 1)).repr
        (representableCostalkBasis matrix c S m R (q + 1) j)) =
    (representableCostalkBasis matrix c S m R q).repr
      (TauCeti.cellularDifferential carrier (ModuleCat.of R R) q
        (representableCostalkBasis matrix c S m R (q + 1) j))
  rw [Module.Basis.repr_self, representableCostalkBoundary,
    Finsupp.linearCombination_single, one_smul]
  ext i
  exact (representableCostalkBasis_differential matrix c S m R q i j).symm

/-- The actual complex term, including its canonical transport from
the skeletal homology definition, in representable monomial coordinates. -/
def representableCostalkChainCoordinates (q : ℕ) :
    (periodicCostalkCellComplex matrix (Sum.inl '' S) (augmentedLatticePairing matrix m)
      (incidenceCellCenter matrix c) (ModuleCat.of R R)).X q ≃ₗ[R]
        (indices q →₀ R) :=
  (eqToIso (TauCeti.cellularChainComplex_X carrier (ModuleCat.of R R) q)).toLinearEquiv.trans
    (representableCostalkBasis matrix c S m R q).repr

/-- The independently displayed finite matrix intertwines the genuine
chain-complex differential, including its canonical endpoint transports. -/
theorem representableCostalkChainCoordinates_boundary (q : ℕ) :
    (representableCostalkBoundary matrix c S m R q).comp
        (representableCostalkChainCoordinates matrix c S m R (q + 1)).toLinearMap =
      (representableCostalkChainCoordinates matrix c S m R q).toLinearMap.comp
        ((periodicCostalkCellComplex matrix (Sum.inl '' S) (augmentedLatticePairing matrix m)
          (incidenceCellCenter matrix c) (ModuleCat.of R R)).d (q + 1) q).hom := by
  let K := periodicCostalkCellComplex matrix (Sum.inl '' S) (augmentedLatticePairing matrix m)
    (incidenceCellCenter matrix c) (ModuleCat.of R R)
  let e₁ := eqToIso (TauCeti.cellularChainComplex_X carrier (ModuleCat.of R R) (q + 1))
  let e₀ := eqToIso (TauCeti.cellularChainComplex_X carrier (ModuleCat.of R R) q)
  have square : e₁.hom ≫ TauCeti.cellularDifferential carrier (ModuleCat.of R R) q =
      K.d (q + 1) q ≫ e₀.hom := by
    change eqToHom (TauCeti.cellularChainComplex_X carrier (ModuleCat.of R R) (q + 1)) ≫
        TauCeti.cellularDifferential carrier (ModuleCat.of R R) q =
      (TauCeti.cellularChainComplex carrier (ModuleCat.of R R)).d (q + 1) q ≫
        eqToHom (TauCeti.cellularChainComplex_X carrier (ModuleCat.of R R) q)
    rw [TauCeti.cellularChainComplex_d]
    simp
  apply LinearMap.ext
  intro v
  exact (DFunLike.congr_fun (representableCostalkBoundary_basis matrix c S m R q)
    (e₁.hom v)).trans
      (congrArg (representableCostalkBasis matrix c S m R q).repr
        (ConcreteCategory.congr_hom square v))

/-- The displayed representable matrices square to zero because they
are the proved coordinates of the genuine cellular differential. -/
theorem representableCostalkBoundary_comp (q : ℕ) :
    (representableCostalkBoundary matrix c S m R q).comp
      (representableCostalkBoundary matrix c S m R (q + 1)) = 0 := by
  let K := periodicCostalkCellComplex matrix (Sum.inl '' S) (augmentedLatticePairing matrix m)
    (incidenceCellCenter matrix c) (ModuleCat.of R R)
  let coordinates := representableCostalkChainCoordinates matrix c S m R
  apply LinearMap.ext
  intro v
  let w := (coordinates (q + 2)).symm v
  have first := DFunLike.congr_fun
    (representableCostalkChainCoordinates_boundary matrix c S m R (q + 1)) w
  have second := DFunLike.congr_fun
    (representableCostalkChainCoordinates_boundary matrix c S m R q)
    (K.d (q + 2) (q + 1) w)
  have zero := ConcreteCategory.congr_hom (K.d_comp_d (q + 2) (q + 1) q) w
  change K.d (q + 1) q (K.d (q + 2) (q + 1) w) = 0 at zero
  change representableCostalkBoundary matrix c S m R (q + 1)
      (coordinates (q + 2) w) = coordinates (q + 1) (K.d (q + 2) (q + 1) w) at first
  have inverse : coordinates (q + 2) w = v := (coordinates (q + 2)).apply_symm_apply v
  rw [inverse] at first
  change representableCostalkBoundary matrix c S m R q
      (coordinates (q + 1) (K.d (q + 2) (q + 1) w)) =
    coordinates q (K.d (q + 1) q (K.d (q + 2) (q + 1) w)) at second
  change representableCostalkBoundary matrix c S m R q
      (representableCostalkBoundary matrix c S m R (q + 1) v) = 0
  rw [first]
  exact second.trans (by rw [zero]; exact map_zero _)

/-- The actual finite matrix complex on representable cofaces and
their true monomial weights. -/
def representableCostalkChainComplex : ChainComplex (ModuleCat.{0} R) ℕ :=
  ChainComplex.of (fun q => ModuleCat.of R (indices q →₀ R))
    (fun q => ModuleCat.ofHom (representableCostalkBoundary matrix c S m R q))
    (fun q => by
      apply ModuleCat.hom_ext
      exact representableCostalkBoundary_comp matrix c S m R q)

@[simp]
theorem representableCostalkChainComplex_d (q : ℕ) :
    (representableCostalkChainComplex matrix c S m R).d (q + 1) q =
      ModuleCat.ofHom (representableCostalkBoundary matrix c S m R q) := by
  change ChainComplex.of.d (fun r => ModuleCat.of R (indices r →₀ R))
    (fun r => ModuleCat.ofHom (representableCostalkBoundary matrix c S m R r))
    (q + 1) q = _
  exact ChainComplex.of_d _ _ q

/-- The displayed finite representable complex is isomorphic to the
genuine relative cellular complex, by its actual characteristic bases. -/
def representableCostalkChainIso :
    periodicCostalkCellComplex matrix (Sum.inl '' S) (augmentedLatticePairing matrix m)
        (incidenceCellCenter matrix c) (ModuleCat.of R R) ≅
      representableCostalkChainComplex matrix c S m R :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (representableCostalkChainCoordinates matrix c S m R q).toModuleIso)
    (fun i j relation => by
      obtain rfl : i = j + 1 := relation.symm
      rw [representableCostalkChainComplex_d]
      apply ModuleCat.hom_ext
      exact representableCostalkChainCoordinates_boundary matrix c S m R j)

end ToricPower.IntegralArrangement
