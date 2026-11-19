module

public import ToricPower.DiagonalCellular
public import ToricPower.DiagonalChartAction
public import ToricPower.CellularIncidenceNaturality

/-!
# Actual monomial maps of the diagonal weight complexes

Multiplication by a chart monomial acts on the literal convex strips by
translation.  This translation is proved cellular for the periodic
characteristic maps, and therefore induces an actual chain map through
relative singular homology.  Its effect on a cellular basis vector is
proved from equality of characteristic maps.  Thus the monomial action
commutes with the differential for geometric reasons; no matrix
commutation relation or incidence invariance is supplied as a hypothesis.

This source remains a candidate until its full dependency closure has
passed the pinned compiler.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local instance diagonalCellularActionPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

local instance stripCW (S T : Set (Fin s)) (u : Fin n → ℤ) :
    CWComplex (diagonalStripCarrier A S T u) :=
  inferInstanceAs (CWComplex (diagonalStripSubcomplex A S T u : Set (Fin n → ℝ)))

@[simp]
theorem integralRowForm_latticeLift (a : Fin n → ℤ) (i : Fin s) :
    integralRowForm A i (latticeLift a) = (rayPairing A a i : ℝ) :=
  augmentedForms_latticeLift A a (.inl i)

/-- The chart-semigroup conditions are exactly what makes translation
send the actual source strip into the actual target strip. -/
theorem diagonalStrip_monomial_translate (S T : Set (Fin s))
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (u : Fin n → ℤ) {x : Fin n → ℝ} (hx : x ∈ diagonalStrip A S T u) :
    x + latticeLift p.1.val ∈ diagonalStrip A S T (u+p.1.val+p.2.val) := by
  constructor
  · intro i hi
    change 0 ≤ integralRowForm A i (x + latticeLift p.1.val)
    rw [map_add, integralRowForm_latticeLift]
    have ha : (0 : ℝ) ≤ rayPairing A p.1.val i := by
      exact_mod_cast p.1.property i hi
    exact add_nonneg (hx.1 i hi) ha
  · intro i hi
    change integralRowForm A i (x + latticeLift p.1.val) ≤ _
    rw [map_add, integralRowForm_latticeLift, rayPairing_add, rayPairing_add]
    simp only [Int.cast_add]
    have hb : (0 : ℝ) ≤ rayPairing A p.2.val i := by
      exact_mod_cast p.2.property i hi
    linarith [hx.2 i hi]

/-- The literal continuous map underlying multiplication by a monomial
on an affine product chart. -/
def diagonalStripMultiplication (S T : Set (Fin s))
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (u : Fin n → ℤ) :
    TopCat.of (diagonalStripCarrier A S T u) ⟶
      TopCat.of (diagonalStripCarrier A S T (u+p.1.val+p.2.val)) :=
  TopCat.ofHom ⟨fun x => ⟨x.val + latticeLift p.1.val,
    diagonalStrip_monomial_translate A S T p u x.property⟩,
    (continuous_subtype_val.add continuous_const).subtype_mk _⟩

/-- The induced map of the actual geometric cell indices. -/
def diagonalStripCellTranslate (S T : Set (Fin s))
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (u : Fin n → ℤ)
    {d : ℕ} (c : Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) d) :
    Topology.RelCWComplex.cell (diagonalStripCarrier A S T (u+p.1.val+p.2.val)) d :=
  ⟨translateCell A p.1.val c.val,
    stripCellAllowed_monomial_translate A S T p.1 p.2 u c.val c.property⟩

theorem diagonalStripMultiplication_cellular (S T : Set (Fin s))
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (u : Fin n → ℤ) :
    TauCeti.IsCellular (diagonalStripCarrier A S T u)
      (diagonalStripCarrier A S T (u+p.1.val+p.2.val))
      (diagonalStripMultiplication A S T p u) := by
  intro m x hx
  obtain ⟨d, hd, c, hc⟩ := CWComplex.mem_skeletonLT_iff.mp hx
  apply CWComplex.mem_skeletonLT_iff.mpr
  refine ⟨d, hd, diagonalStripCellTranslate A S T p u c, ?_⟩
  change x.val ∈ periodicCellMap A c.val '' Metric.ball 0 1 at hc
  obtain ⟨z, hz, he⟩ := hc
  change x.val + latticeLift p.1.val ∈
    periodicCellMap A (translateCell A p.1.val c.val) '' Metric.ball 0 1
  exact ⟨z, hz, by rw [periodicCellMap_translate, he]⟩

set_option backward.isDefEq.respectTransparency false in
/-- Equality of characteristic maps keeps the actual disk parameter,
including its orientation, under the chart monomial map. -/
theorem diagonalStripMultiplication_characteristic (S T : Set (Fin s))
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (u : Fin n → ℤ)
    (d : ℕ) (c : Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) d) :
    TauCeti.characteristicCellPairMap (diagonalStripCarrier A S T u) c ≫
      TauCeti.skeletonPairMap _ _ (diagonalStripMultiplication_cellular A S T p u) d =
    TauCeti.characteristicCellPairMap (diagonalStripCarrier A S T (u+p.1.val+p.2.val))
      (diagonalStripCellTranslate A S T p u c) := by
  apply TopPair.hom_ext_of_fst
  rw [TopPair.Hom.fst_comp, TauCeti.skeletonPairMap_fst]
  ext x
  erw [ConcreteCategory.comp_apply]
  apply Subtype.ext
  let y : TauCeti.skeletonObj (diagonalStripCarrier A S T u) (d + 1) :=
    TopPair.Hom.fst (TauCeti.characteristicCellPairMap (diagonalStripCarrier A S T u) c) x
  let v := (EuclideanSpace.equiv (Fin d) ℝ).unitBallHomeomorph (x : TopCat.disk d).down
  have sourceValue : (y : Fin n → ℝ) = periodicCellMap A c.val v :=
    TauCeti.coe_characteristicCellPairMap_fst_apply (diagonalStripCarrier A S T u) c x
  have targetValue :
      ((TopPair.Hom.fst (TauCeti.characteristicCellPairMap
        (diagonalStripCarrier A S T (u+p.1.val+p.2.val))
        (diagonalStripCellTranslate A S T p u c))) x).val =
      periodicCellMap A (translateCell A p.1.val c.val) v :=
    TauCeti.coe_characteristicCellPairMap_fst_apply
      (diagonalStripCarrier A S T (u+p.1.val+p.2.val))
      (diagonalStripCellTranslate A S T p u c) x
  have translatedValue := congrArg Subtype.val
    (TauCeti.skeletonMap_apply (diagonalStripCarrier A S T u)
      (diagonalStripCarrier A S T (u+p.1.val+p.2.val))
      (diagonalStripMultiplication_cellular A S T p u) (d + 1) y)
  change _ = (y : Fin n → ℝ) + latticeLift p.1.val at translatedValue
  exact translatedValue.trans
    ((congrArg (fun w => w + latticeLift p.1.val) sourceValue).trans
      ((periodicCellMap_translate A p.1.val c.val v).symm.trans targetValue.symm))

variable {R : Type} [Ring R]

/-- The actual monomial chain map, obtained from the actual cellular
translation and its induced maps of relative singular homology. -/
def diagonalStripMultiplicationChainMap (M : ModuleCat.{0} R) (S T : Set (Fin s))
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (u : Fin n → ℤ) :
    diagonalWeightCellComplex A M S T u ⟶
      diagonalWeightCellComplex A M S T (u+p.1.val+p.2.val) :=
  TauCeti.cellularChainComplexMap _ _ (diagonalStripMultiplication_cellular A S T p u) M

/-- Monomial multiplication sends each geometric cellular basis vector
to the translated basis vector, with coefficient exactly one. -/
theorem diagonalStripMultiplication_cellularBasis (S T : Set (Fin s))
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (u : Fin n → ℤ)
    (d : ℕ) (c : Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) d) :
    TauCeti.cellularChainGroupMap _ _ (diagonalStripMultiplication_cellular A S T p u)
      (ModuleCat.of R R) d
      (TauCeti.cellularChainBasis (diagonalStripCarrier A S T u) R d c) =
    TauCeti.cellularChainBasis (diagonalStripCarrier A S T (u+p.1.val+p.2.val)) R d
      (diagonalStripCellTranslate A S T p u c) :=
  ToricPower.cellularChainGroupMap_basis_of_characteristic _ _
    (diagonalStripMultiplication_cellular A S T p u) R c
    (diagonalStripCellTranslate A S T p u c)
    (diagonalStripMultiplication_characteristic A S T p u d c)

end ToricPower.IntegralArrangement
