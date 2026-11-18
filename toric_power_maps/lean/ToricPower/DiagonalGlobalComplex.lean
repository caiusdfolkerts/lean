module

public import ToricPower.DiagonalSheafComposition

/-!
# The actual finite global sheaf complex on the toric product

The boundary matrices are genuine morphisms between finite sums of actual
Cartier line bundles. Their square-zero law is deduced from the genuine
finite convolution identity of cellular incidence coefficients and the
proved composition law for actual character maps.

This constructs a chain complex in the ordinary category of module
sheaves on `X × Spec(ℂ) X`. Local exactness and its augmentation to the
diagonal are separate statements, not part of its definition.

Candidate until the pinned compiler checks the complete source closure.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical BigOperators

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones)
  (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ))
  (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "L" => diagonalProductSheaf fan nonempty regular basis rays
local notation "H" => diagonalProductCharacterHom fan nonempty regular basis rays
local notation "G" => diagonalGlobalSheafTerm fan nonempty regular basis rays
local notation "col" => diagonalGlobalColumn ℂ A

local instance : HasFiniteBiproducts (toricDiagonalProduct fan).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance cellsFintype (d : ℕ) : Fintype (NormalizedCell A d) := Fintype.ofFinite _
local instance termsFintype (d : ℕ) (j : NormalizedCell A (d+1)) :
    Fintype (DiagonalGlobalColumnTerm ℂ A d j) := Fintype.ofFinite _

/-- The same genuine global column, written as a linear combination
of actual character morphisms, so linear functoriality can be applied. -/
def diagonalGlobalLinearColumn (d : ℕ) (j : NormalizedCell A (d+1)) : L j ⟶ G d :=
  Finsupp.linearCombination ℂ
    (fun p : NormalizedCell A d × (Fin n → ℤ) =>
      H j p.1 p.2 ≫ biproduct.ι (fun c : NormalizedCell A d => L c) p.1)
    (col d j)

def diagonalGlobalLinearBoundary (d : ℕ) : G (d+1) ⟶ G d :=
  biproduct.desc (diagonalGlobalLinearColumn fan nonempty regular basis rays d)

@[reassoc]
theorem diagonalGlobalLinearBoundary_column (d : ℕ) (j : NormalizedCell A (d+1)) :
    biproduct.ι (fun c : NormalizedCell A (d+1) => L c) j ≫
      diagonalGlobalLinearBoundary fan nonempty regular basis rays d =
        diagonalGlobalLinearColumn fan nonempty regular basis rays d j := by
  simp only [diagonalGlobalLinearBoundary, biproduct.ι_desc]

/-- The linear-combination expression is the already defined global
matrix column, including its actual base-field scalar action. -/
theorem diagonalGlobalSheafColumn_eq_linear (d : ℕ) (j : NormalizedCell A (d+1)) :
    diagonalGlobalSheafColumn fan nonempty regular basis rays d j =
      diagonalGlobalLinearColumn fan nonempty regular basis rays d j := by
  unfold diagonalGlobalSheafColumn diagonalGlobalLinearColumn
  rw [Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_subtype (col d j).support (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [diagonalProductMonomialEntry_eq_characterHom, ← Linear.smul_comp,
    Scheme.Modules.base_smul_eq, Category.assoc]

theorem diagonalGlobalSheafBoundary_eq_linear (d : ℕ) :
    diagonalGlobalSheafBoundary fan nonempty regular basis rays d =
      diagonalGlobalLinearBoundary fan nonempty regular basis rays d := by
  apply biproduct.hom_ext'
  intro j
  rw [diagonalGlobalSheafBoundary_column, diagonalGlobalLinearBoundary_column,
    diagonalGlobalSheafColumn_eq_linear]

/-- Every genuine global boundary squares to zero. The proof evaluates
the actual zero convolution column in the actual sheaf Hom module. -/
theorem diagonalGlobalLinearBoundary_square (d : ℕ) :
    diagonalGlobalLinearBoundary fan nonempty regular basis rays (d+1) ≫
      diagonalGlobalLinearBoundary fan nonempty regular basis rays d = 0 := by
  apply biproduct.hom_ext'
  intro j
  rw [← Category.assoc, diagonalGlobalLinearBoundary_column, comp_zero]
  let w : (NormalizedCell A d × (Fin n → ℤ)) → (L j ⟶ G d) :=
    fun q => H j q.1 q.2 ≫ biproduct.ι (fun c : NormalizedCell A d => L c) q.1
  let evaluate := Finsupp.linearCombination ℂ w
  have hpath (p : NormalizedCell A (d+1) × (Fin n → ℤ))
      (hp : p ∈ (col (d+1) j).support) :
      (H j p.1 p.2 ≫
        biproduct.ι (fun c : NormalizedCell A (d+1) => L c) p.1) ≫
          diagonalGlobalLinearBoundary fan nonempty regular basis rays d =
        evaluate (Finsupp.mapDomain (fun q => (q.1,p.2+q.2)) (col d p.1)) := by
    rw [Category.assoc, diagonalGlobalLinearBoundary_column]
    change (Linear.leftComp ℂ (G d) (H j p.1 p.2))
        (Finsupp.linearCombination ℂ
          (fun q : NormalizedCell A d × (Fin n → ℤ) =>
            H p.1 q.1 q.2 ≫ biproduct.ι (fun c : NormalizedCell A d => L c) q.1)
          (col d p.1)) = _
    erw [Finsupp.apply_linearCombination]
    change Finsupp.linearCombination ℂ
        (fun q : NormalizedCell A d × (Fin n → ℤ) =>
          H j p.1 p.2 ≫ H p.1 q.1 q.2 ≫
            biproduct.ι (fun c : NormalizedCell A d => L c) q.1) (col d p.1) =
      Finsupp.linearCombination ℂ w
        (Finsupp.mapDomain (fun q => (q.1,p.2+q.2)) (col d p.1))
    rw [Finsupp.linearCombination_mapDomain]
    simp only [Finsupp.linearCombination_apply]
    apply Finsupp.sum_congr
    intro q hq
    congr 1
    have ha := diagonalEntryRegular_of_globalColumn_ne_zero fan basis rays (d+1)
      j p.1 p.2 (Finsupp.mem_support_iff.mp hp)
    have hb := diagonalEntryRegular_of_globalColumn_ne_zero fan basis rays d
      p.1 q.1 q.2 (Finsupp.mem_support_iff.mp hq)
    rw [← Category.assoc, diagonalProductCharacterHom_comp fan nonempty regular
      basis rays j p.1 q.1 p.2 q.2 ha hb]
    rfl
  calc
    diagonalGlobalLinearColumn fan nonempty regular basis rays (d+1) j ≫
        diagonalGlobalLinearBoundary fan nonempty regular basis rays d =
      (col (d+1) j).sum (fun p r => r •
        ((H j p.1 p.2 ≫ biproduct.ι
          (fun c : NormalizedCell A (d+1) => L c) p.1) ≫
            diagonalGlobalLinearBoundary fan nonempty regular basis rays d)) := by
      change (Linear.rightComp ℂ (L j)
        (diagonalGlobalLinearBoundary fan nonempty regular basis rays d))
          (Finsupp.linearCombination ℂ _ (col (d+1) j)) = _
      rw [Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
      rfl
    _ = (col (d+1) j).sum (fun p r =>
        r • evaluate (Finsupp.mapDomain (fun q => (q.1,p.2+q.2)) (col d p.1))) := by
      apply Finsupp.sum_congr
      intro p hp
      rw [hpath p hp]
    _ = evaluate (diagonalGlobalComposedColumn ℂ A d j) := by
      simp only [diagonalGlobalComposedColumn, map_finsuppSum, map_smul]
    _ = 0 := by rw [diagonalGlobalComposedColumn_eq_zero, map_zero]

/-- The originally displayed actual sheaf boundary has the same
square-zero law, by the proved expression comparison. -/
theorem diagonalGlobalSheafBoundary_square (d : ℕ) :
    diagonalGlobalSheafBoundary fan nonempty regular basis rays (d+1) ≫
      diagonalGlobalSheafBoundary fan nonempty regular basis rays d = 0 := by
  rw [diagonalGlobalSheafBoundary_eq_linear, diagonalGlobalSheafBoundary_eq_linear]
  exact diagonalGlobalLinearBoundary_square fan nonempty regular basis rays d

/-- The actual global cellular complex of labelled line bundles. -/
def diagonalGlobalSheafComplex : ChainComplex (toricDiagonalProduct fan).Modules ℕ :=
  ChainComplex.of G
    (diagonalGlobalSheafBoundary fan nonempty regular basis rays)
    (diagonalGlobalSheafBoundary_square fan nonempty regular basis rays)

/-- The finite-length bound is the actual ambient lattice rank, proved
from the dimensions of the geometric cells. -/
theorem diagonalGlobalSheafTerm_isZero_of_dim_lt (d : ℕ) (hd : n < d) : IsZero (G d) := by
  rw [IsZero.iff_id_eq_zero]
  apply biproduct.hom_ext
  intro j
  exact (not_lt_of_ge (cell_dimension_le A j.val) hd).elim

end ToricPower
