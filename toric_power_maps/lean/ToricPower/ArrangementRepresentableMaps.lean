module

public import ToricPower.ArrangementCostalkRepresentation
public import ToricPower.CWRelativeCellularBasisMap

/-!
# Actual incidence composition on the representable costalk bases

A weighted incidence acts on a coface basis by literal composition of
incidences. The geometric chain map is the corresponding partial
restriction of coefficients: it sends a translated characteristic cell
to the same target cell when it survives, and kills it otherwise. This
is the chain-level map whose scalar dual gives the representable map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ) (S : Set (Fin s))
  {c d : WeightedIncidenceObject matrix} (f : c ⟶ d)

local instance representableMapsPeriodicCW : CWComplex (arrangementCarrier matrix) :=
  periodicArrangementCWComplex matrix

/-- The genuine representable map composes the recorded incidence.
The coefficient monomial is unchanged because its full character is
`m + a`, with both summands transformed by the actual weighted map. -/
def representableCostalkPrecompose (q : ℕ)
    (p : RepresentableCostalkIndex matrix d.1 S d.2 q) :
    RepresentableCostalkIndex matrix c.1 S c.2 q :=
  ⟨⟨p.val.1, f.val ≫ p.val.2⟩, by
    intro i hi
    have shift : c.2 + (f.val ≫ p.val.2).val = d.2 + p.val.2.val := by
      rw [incidence_comp_val, ← add_assoc, ← f.property]
    rw [shift]
    exact p.property i hi⟩

/-- The actual translated source cell for a composed incidence is the
actual target cell, with no change in characteristic-disk orientation. -/
theorem representableCostalkPrecompose_cell (q : ℕ)
    (p : RepresentableCostalkIndex matrix d.1 S d.2 q) :
    translateCell matrix f.val.val
        (((periodicCostalkRepresentableCellEquiv matrix c.1 S c.2 q).symm
          (representableCostalkPrecompose matrix S f q p)).val) =
      ((periodicCostalkRepresentableCellEquiv matrix d.1 S d.2 q).symm p).val := by
  change translateCell matrix f.val.val
      (translateCell matrix (-(f.val.val + p.val.2.val)) p.val.1.val) =
    translateCell matrix (-p.val.2.val) p.val.1.val
  rw [translateCell_add]
  congr 1
  abel

/-- Equality of the actual translated cells is exactly equality with
the true composite representable index. -/
theorem representableCostalkPrecompose_cell_iff (q : ℕ)
    (i : RepresentableCostalkIndex matrix c.1 S c.2 q)
    (j : RepresentableCostalkIndex matrix d.1 S d.2 q) :
    translateCell matrix f.val.val
        (((periodicCostalkRepresentableCellEquiv matrix c.1 S c.2 q).symm i).val) =
      ((periodicCostalkRepresentableCellEquiv matrix d.1 S d.2 q).symm j).val ↔
      i = representableCostalkPrecompose matrix S f q j := by
  rw [← representableCostalkPrecompose_cell matrix S f q j]
  constructor
  · intro equal
    apply (periodicCostalkRepresentableCellEquiv matrix c.1 S c.2 q).symm.injective
    apply Subtype.ext
    exact (translationCellEquiv matrix f.val.val q).injective equal
  · rintro rfl
    rfl

/-- Composition is injective on the actual coface-and-monomial basis.
This is a proved property of lattice translations, not an assumed
cancellativity axiom for the incidence category. -/
theorem representableCostalkPrecompose_injective (q : ℕ) :
    Function.Injective (representableCostalkPrecompose matrix S f q) := by
  intro i j equal
  apply (periodicCostalkRepresentableCellEquiv matrix d.1 S d.2 q).symm.injective
  apply Subtype.ext
  rw [← representableCostalkPrecompose_cell matrix S f q i,
    ← representableCostalkPrecompose_cell matrix S f q j, equal]

variable (R : Type) [Ring R]

/-- Every coefficient of the actual weighted cellular map is the
Kronecker coefficient of genuine incidence composition. Absorbed cells
are automatically zero in this equality. -/
theorem weightedCostalkChainGroupMap_representable_coefficient (q : ℕ)
    (i : RepresentableCostalkIndex matrix c.1 S c.2 q)
    (j : RepresentableCostalkIndex matrix d.1 S d.2 q) :
    (representableCostalkBasis matrix d.1 S d.2 R q).repr
        (TauCeti.cellularChainGroupMap
          (relativeCWCarrier (weightedCostalkComplement matrix (Sum.inl '' S) c))
          (relativeCWCarrier (weightedCostalkComplement matrix (Sum.inl '' S) d))
          (relativeCWMap_cellular
            (weightedCostalkComplement matrix (Sum.inl '' S) c)
            (weightedCostalkComplement matrix (Sum.inl '' S) d)
            (arrangementTranslation matrix f.val.val)
            (arrangementTranslation_cellular matrix f.val.val)
            (weightedCostalk_base matrix (Sum.inl '' S) f))
          (ModuleCat.of R R) q
          (representableCostalkBasis matrix c.1 S c.2 R q i)) j =
      if i = representableCostalkPrecompose matrix S f q j then 1 else 0 := by
  simp only [representableCostalkBasis, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply]
  refine (relativeCWChainGroupMap_basis_coefficient
    (arrangementCarrier matrix) (arrangementCarrier matrix)
    (weightedCostalkComplement matrix (Sum.inl '' S) c)
    (weightedCostalkComplement matrix (Sum.inl '' S) d)
    (arrangementTranslation matrix f.val.val)
    (arrangementTranslation_cellular matrix f.val.val)
    (weightedCostalk_base matrix (Sum.inl '' S) f) R q
    ((periodicCostalkRepresentableCellEquiv matrix c.1 S c.2 q).symm i)
    ((periodicCostalkRepresentableCellEquiv matrix d.1 S d.2 q).symm j)
    (translateCell matrix f.val.val
      (((periodicCostalkRepresentableCellEquiv matrix c.1 S c.2 q).symm i).val))
    (arrangementTranslation_characteristic matrix f.val.val q _)).trans ?_
  have same := representableCostalkPrecompose_cell_iff matrix S f q i j
  by_cases equal : i = representableCostalkPrecompose matrix S f q j
  · rw [if_pos (same.mpr equal), if_pos equal]
  · rw [if_neg (fun h => equal (same.mp h)), if_neg equal]

end ToricPower.IntegralArrangement
