module

public import ToricPower.ArrangementCore
public import ToricPower.CellularDependency07
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Cellular exactness of the actual convex monomial-weight regions

The chain complex below is the cellular chain complex of the CW subcomplex
constructed from the literal integer hyperplanes. Its positive homology
vanishes because its carrier is a convex polyhedron. Its zeroth homology is
the coefficient module through the actual cellular–singular comparison.
There is no acyclicity predicate in the definition of a weight complex.

This is a candidate source until all imported proof bodies and this module
have passed the pinned ordinary compiler.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set Topology
open Topology.RelCWComplex

namespace ToricPower.IntegralArrangement

universe u

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]
  (f : ι → E →ₗ[ℝ] ℝ) (hc : ∀ e I, IsCompact (closedCell f e I))
  (J : Set ι) (l : ι → ℤ)

abbrev weightCarrier : Set E := weightSubcomplex f hc J l

local instance weightCW : CWComplex (weightCarrier f hc J l) := by
  letI : CWComplex (univ : Set E) := arrangementCWComplex f hc
  exact inferInstanceAs (CWComplex (weightSubcomplex f hc J l : Set E))

variable {k : Type u} [Ring k] (M : ModuleCat.{u} k)

/-- The literal cellular chain complex of a monomial weight region. -/
def weightCellComplex : ChainComplex (ModuleCat.{u} k) ℕ :=
  TauCeti.cellularChainComplex (weightCarrier f hc J l) M

/-- Cellular homology is the ordinary singular homology of this actual
weight polyhedron, with the empty-relative-base comparison made explicit. -/
def weightCellularSingularIso (n : ℕ) :
    (weightCellComplex f hc J l M).homology n ≅
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).obj
        (TopCat.of (weightCarrier f hc J l)) := by
  let C := weightCarrier f hc J l
  let P := TauCeti.complexBasePair C
  letI : IsEmpty P.snd := TauCeti.isEmpty_complexBasePair_snd C
  letI : IsIso (P.singularHomologyπ M n) := inferInstance
  exact TauCeti.cellularSingularHomologyIso C M n ≪≫ (asIso (P.singularHomologyπ M n)).symm

/-- Every positive cellular homology group of a nonempty monomial-weight
polyhedron vanishes, over an arbitrary coefficient ring and module. -/
theorem weightCellComplex_isZero_homology
    (hne : (weightRegionOn f J l).Nonempty) {n : ℕ} (hn : n ≠ 0) :
    IsZero ((weightCellComplex f hc J l M).homology n) := by
  letI : ContractibleSpace (weightCarrier f hc J l) :=
    weightSubcomplex_contractible f hc J l hne
  exact (TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace M
    (TopCat.of (weightCarrier f hc J l)) hn).of_iso
      (weightCellularSingularIso f hc J l M n)

/-- Positive-degree exactness of the actual cellular complex. -/
theorem weightCellComplex_exactAt
    (hne : (weightRegionOn f J l).Nonempty) {n : ℕ} (hn : n ≠ 0) :
    (weightCellComplex f hc J l M).ExactAt n :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (weightCellComplex_isZero_homology f hc J l M hne hn)

/-- Zeroth cellular homology is one copy of the coefficient module.
The identification is obtained by the usual augmentation of singular
homology after the actual cellular comparison. -/
def weightCellHomologyZeroIso
    (hne : (weightRegionOn f J l).Nonempty) :
    (weightCellComplex f hc J l M).homology 0 ≅ M := by
  letI : ContractibleSpace (weightCarrier f hc J l) :=
    weightSubcomplex_contractible f hc J l hne
  let x : TopCat.of (weightCarrier f hc J l) := ⟨hne.choose, hne.choose_spec⟩
  exact weightCellularSingularIso f hc J l M 0 ≪≫
    TauCeti.singularHomology₀SplitIso M x ≪≫
      (isoZeroBiprod (TauCeti.isZero_reducedSingularHomologyFunctor_of_contractibleSpace
        M (TopCat.of (weightCarrier f hc J l)) 0)).symm

/-- The abstractly constructed zeroth-homology isomorphism is the canonical
augmentation, rather than an arbitrary choice of a rank-one isomorphism. -/
theorem weightCellHomologyZeroIso_hom
    (hne : (weightRegionOn f J l).Nonempty) :
    (weightCellHomologyZeroIso f hc J l M hne).hom =
      (weightCellularSingularIso f hc J l M 0).hom ≫
        (TopCat.of (weightCarrier f hc J l)).singularHomology₀ε M := by
  simp only [weightCellHomologyZeroIso, Iso.trans_hom, Iso.symm_hom,
    isoZeroBiprod_inv, Category.assoc, TauCeti.singularHomology₀SplitIso_hom_snd]

section AugmentedCoordinates

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (b : Fin s → ℤ)

/-- The actual weight complex for arbitrary integer ray rows. Coordinate
hyperplanes only subdivide the cells and impose no extra monomial constraint. -/
def integralWeightComplex : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  weightCellComplex (augmentedForms A) (closedCell_isCompact A)
    (range (Sum.inl : Fin s → Fin s ⊕ Fin n)) (Sum.elim b (fun _ => 0))
    (ModuleCat.of ℤ ℤ)

/-- The positive-degree exactness statement used in the monomial-weight
proof of the affine diagonal resolution. All dimensions and integer row
matrices are allowed, including a zero-dimensional ambient space. -/
theorem integralWeightComplex_exactAt
    (hne : (weightRegion (integralRowForm A) b).Nonempty)
    {q : ℕ} (hq : q ≠ 0) : (integralWeightComplex A b).ExactAt q := by
  apply weightCellComplex_exactAt
  · simpa only [augmented_weightRegionOn] using hne
  · exact hq

end AugmentedCoordinates

end ToricPower.IntegralArrangement
