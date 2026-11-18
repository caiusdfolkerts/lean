module

public import ToricPower.ArrangementEquivariant
public import ToricPower.DiagonalCellWeights
public import ToricPower.WeightCellular

/-! # Actual cellular exactness of a diagonal monomial weight

This is the ordinary cellular chain complex of the literal convex strip,
with the translation-compatible characteristic maps. The comparison to
singular homology proves its positive-degree exactness and canonical
degree-zero augmentation. It does not postulate acyclicity of a displayed
matrix or rename a diagonal resolution as an exact complex.

Candidate until ordinary kernel checking succeeds for the entire closure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set Topology Metric
open Topology.RelCWComplex
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

theorem diagonalStrip_convex (S T : Set (Fin s)) (u : Fin n → ℤ) :
    Convex ℝ (diagonalStrip A S T u) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i hi
    change 0 ≤ integralRowForm A i (a • x + b • y)
    rw [map_add, map_smul, map_smul]
    exact add_nonneg (mul_nonneg ha (hx.1 i hi)) (mul_nonneg hb (hy.1 i hi))
  · intro i hi
    change integralRowForm A i (a • x + b • y) ≤ _
    rw [map_add, map_smul, map_smul]
    calc
      a * integralRowForm A i x + b * integralRowForm A i y ≤
          a * (rayPairing A u i : ℝ) + b * (rayPairing A u i : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left (hx.2 i hi) ha)
          (mul_le_mul_of_nonneg_left (hy.2 i hi) hb)
      _ = (rayPairing A u i : ℝ) := by rw [← add_mul, hab, one_mul]

local instance periodicAmbientCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

/-- The actual strip is a subcomplex, using precisely the cells indexing
the diagonal monomial basis equivalence. -/
def diagonalStripSubcomplex (S T : Set (Fin s)) (u : Fin n → ℤ) :
    CWComplex.Subcomplex (arrangementCarrier A) :=
  CWComplex.Subcomplex.mk' (arrangementCarrier A) (diagonalStrip A S T u)
    (fun _ => {c | stripCellAllowed A S T u c})
    (by
      intro d c
      change periodicCellMap A c.val '' closedBall 0 1 ⊆ _
      rw [periodicCellMap_image_closedBall]
      exact (stripCellAllowed_iff_closedCell_subset A S T u c.val).mp c.property)
    (by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨d, hd⟩ := mem_iUnion.mp hx
        obtain ⟨c, hc⟩ := mem_iUnion.mp hd
        change x ∈ periodicCellMap A c.val '' ball 0 1 at hc
        rw [periodicCellMap_image_ball] at hc
        exact (stripCellAllowed_iff_point A S T u c.val hc).mp c.property
      · intro x hx
        let d := Module.finrank ℝ (cellDirection (augmentedForms A)
          (integralIndices (augmentedForms A) x))
        let c : Cell (augmentedForms A) d :=
          ⟨(ceilingVector (augmentedForms A) x, integralIndices (augmentedForms A) x),
            ⟨x, mem_cell_self (augmentedForms A) x⟩, rfl⟩
        have hc : stripCellAllowed A S T u c :=
          (stripCellAllowed_iff_point A S T u c (mem_cell_self (augmentedForms A) x)).mpr hx
        refine mem_iUnion.mpr ⟨d, mem_iUnion.mpr ⟨⟨c, hc⟩, ?_⟩⟩
        change x ∈ periodicCellMap A c '' ball 0 1
        rw [periodicCellMap_image_ball]
        exact mem_cell_self (augmentedForms A) x)

@[simp]
theorem diagonalStripSubcomplex_coe (S T : Set (Fin s)) (u : Fin n → ℤ) :
    (diagonalStripSubcomplex A S T u : Set (Fin n → ℝ)) = diagonalStrip A S T u := rfl

abbrev diagonalStripCarrier (S T : Set (Fin s)) (u : Fin n → ℤ) : Set (Fin n → ℝ) :=
  diagonalStripSubcomplex A S T u

local instance diagonalStripCW (S T : Set (Fin s)) (u : Fin n → ℤ) :
    CWComplex (diagonalStripCarrier A S T u) :=
  inferInstanceAs (CWComplex (diagonalStripSubcomplex A S T u : Set (Fin n → ℝ)))

theorem diagonalStripCarrier_contractible (S T : Set (Fin s)) (u : Fin n → ℤ)
    (hne : (diagonalStrip A S T u).Nonempty) :
    ContractibleSpace (diagonalStripCarrier A S T u) :=
  (diagonalStrip_convex A S T u).contractibleSpace hne

variable {k : Type} [Ring k] (M : ModuleCat.{0} k)

def diagonalWeightCellComplex (S T : Set (Fin s)) (u : Fin n → ℤ) :
    ChainComplex (ModuleCat.{0} k) ℕ :=
  TauCeti.cellularChainComplex (diagonalStripCarrier A S T u) M

def diagonalWeightCellularSingularIso (S T : Set (Fin s)) (u : Fin n → ℤ) (q : ℕ) :
    (diagonalWeightCellComplex A M S T u).homology q ≅
      ((singularHomologyFunctor (ModuleCat.{0} k) q).obj M).obj
        (TopCat.of (diagonalStripCarrier A S T u)) := by
  let C := diagonalStripCarrier A S T u
  let P := TauCeti.complexBasePair C
  letI : IsEmpty P.snd := TauCeti.isEmpty_complexBasePair_snd C
  letI : IsIso (P.singularHomologyπ M q) := inferInstance
  exact TauCeti.cellularSingularHomologyIso C M q ≪≫
    (asIso (P.singularHomologyπ M q)).symm

theorem diagonalWeightCellComplex_exactAt (S T : Set (Fin s)) (u : Fin n → ℤ)
    (hne : (diagonalStrip A S T u).Nonempty) {q : ℕ} (hq : q ≠ 0) :
    (diagonalWeightCellComplex A M S T u).ExactAt q := by
  letI := diagonalStripCarrier_contractible A S T u hne
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  exact (TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace M
    (TopCat.of (diagonalStripCarrier A S T u)) hq).of_iso
      (diagonalWeightCellularSingularIso A M S T u q)

def diagonalWeightCellHomologyZeroIso (S T : Set (Fin s)) (u : Fin n → ℤ)
    (hne : (diagonalStrip A S T u).Nonempty) :
    (diagonalWeightCellComplex A M S T u).homology 0 ≅ M := by
  letI := diagonalStripCarrier_contractible A S T u hne
  let x : TopCat.of (diagonalStripCarrier A S T u) := ⟨hne.choose, hne.choose_spec⟩
  exact diagonalWeightCellularSingularIso A M S T u 0 ≪≫
    TauCeti.singularHomology₀SplitIso M x ≪≫
      (isoZeroBiprod (TauCeti.isZero_reducedSingularHomologyFunctor_of_contractibleSpace
        M (TopCat.of (diagonalStripCarrier A S T u)) 0)).symm

theorem diagonalWeightCellHomologyZeroIso_hom (S T : Set (Fin s)) (u : Fin n → ℤ)
    (hne : (diagonalStrip A S T u).Nonempty) :
    (diagonalWeightCellHomologyZeroIso A M S T u hne).hom =
      (diagonalWeightCellularSingularIso A M S T u 0).hom ≫
        (TopCat.of (diagonalStripCarrier A S T u)).singularHomology₀ε M := by
  simp only [diagonalWeightCellHomologyZeroIso, Iso.trans_hom, Iso.symm_hom,
    isoZeroBiprod_inv, Category.assoc, TauCeti.singularHomology₀SplitIso_hom_snd]

end ToricPower.IntegralArrangement
