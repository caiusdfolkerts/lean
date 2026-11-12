module

public import ToricPower.ArrangementWeightDifferential

/-!
# An actual complex isomorphism from cellular realization to a costalk

The independently defined cellular coefficient functor and the geometric
relative CW complex have the same literal matrix, in their proved free
bases. This gives a genuine isomorphism of complexes in every integral
character. In particular, the top-class and vanishing results apply to
the original cellular realization, with no exactness premise added.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A) (m : Fin n → ℤ) (k : Type) [Field k]

local notation "K" => representedWeightCellularComplex A S c m k
local notation "L" => representableCostalkCochainComplex k A c S m
local notation "indices" => RepresentableCostalkIndex A c S m

/-- The geometric costalk differential evaluated on one actual basis
cochain. Its coefficient is the previously proved periodic incidence. -/
theorem representableCostalkCochainCoordinates_d_generator (q : ℕ)
    (i : indices q) (j : indices (q + 1)) (r : k) :
    representableCostalkCochainCoordinates k A c S m (q + 1)
      ((L).d q (q + 1)
        ((representableCostalkCochainCoordinates k A c S m q).symm
          (Finsupp.single i r))) j =
      representableCostalkIncidence A c S m k q i j * r := by
  rw [representableCostalkCochainCoordinates_differential, LinearEquiv.apply_symm_apply]
  rw [Finsupp.sum_eq_single i]
  · rw [Finsupp.single_eq_same, representableCostalkColumn_apply]
  · intro b _ different
    rw [Finsupp.single_eq_of_ne different, mul_zero]
  · intro _
    exact zero_mul _

/-- The complete actual differentials agree in their independent
coordinate systems, on arbitrary finite sums of basis cochains. -/
theorem representedWeightCostalkCoordinates_differential (q : ℕ)
    (v : indices q →₀ k) :
    representedWeightCellularCoordinates A S c m k (q + 1)
      ((K).d q (q + 1)
        ((representedWeightCellularCoordinates A S c m k q).symm v)) =
      representableCostalkCochainCoordinates k A c S m (q + 1)
        ((L).d q (q + 1)
          ((representableCostalkCochainCoordinates k A c S m q).symm v)) := by
  let actual : (indices q →₀ k) →ₗ[k] (indices (q + 1) →₀ k) :=
    (representedWeightCellularCoordinates A S c m k (q + 1)).toLinearMap.comp
      (((K).d q (q + 1)).hom.comp
        (representedWeightCellularCoordinates A S c m k q).symm.toLinearMap)
  let geometric : (indices q →₀ k) →ₗ[k] (indices (q + 1) →₀ k) :=
    (representableCostalkCochainCoordinates k A c S m (q + 1)).toLinearMap.comp
      (((L).d q (q + 1)).hom.comp
        (representableCostalkCochainCoordinates k A c S m q).symm.toLinearMap)
  have equal : actual = geometric := by
    apply Finsupp.lhom_ext
    intro i r
    ext j
    exact (representedWeightCellularCoordinates_d_generator A S c m k q i j r).trans
      (representableCostalkCochainCoordinates_d_generator A S c m k q i j r).symm
  exact DFunLike.congr_fun equal v

/-- The literal term comparison uses the actual cellular coordinates
and the independently obtained geometric costalk coordinates. -/
def representedWeightCostalkTermIso (q : ℕ) : (K).X q ≅ (L).X q :=
  ((representedWeightCellularCoordinates A S c m k q).trans
    (representableCostalkCochainCoordinates k A c S m q).symm).toModuleIso

/-- The genuine character-fiber cellular realization is the genuine
relative costalk cochain complex, including every differential. -/
def representedWeightCostalkComplexIso : K ≅ L :=
  HomologicalComplex.Hom.isoOfComponents
    (representedWeightCostalkTermIso A S c m k)
    (fun q r relation => by
      obtain rfl : r = q + 1 := relation.symm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      apply (representableCostalkCochainCoordinates k A c S m (q + 1)).injective
      change representableCostalkCochainCoordinates k A c S m (q + 1)
          ((L).d q (q + 1)
            ((representableCostalkCochainCoordinates k A c S m q).symm
              (representedWeightCellularCoordinates A S c m k q v))) =
        representableCostalkCochainCoordinates k A c S m (q + 1)
          ((representableCostalkCochainCoordinates k A c S m (q + 1)).symm
            (representedWeightCellularCoordinates A S c m k (q + 1)
              ((K).d q (q + 1) v)))
      rw [LinearEquiv.apply_symm_apply]
      have equal := representedWeightCostalkCoordinates_differential A S c m k q
        (representedWeightCellularCoordinates A S c m k q v)
      rw [LinearEquiv.symm_apply_apply] at equal
      exact equal.symm)

/-- Top cohomology of the original cellular realization is the actual
ambient orientation coefficient whenever its geometric support is nonempty. -/
def representedWeightCellularHomologyIso
    (nonempty : (costalkRegion (augmentedForms A) (Sum.inl '' S)
      (augmentedLatticePairing A m) (incidenceCellCenter A c)).Nonempty) :
    (K).homology n ≅ ModuleCat.of k k :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (representedWeightCostalkComplexIso A S c m k) ≪≫
    representableCostalkCochainHomologyIso k A c S m nonempty

theorem representedWeightCellularComplex_isZero_homology
    (nonempty : (costalkRegion (augmentedForms A) (Sum.inl '' S)
      (augmentedLatticePairing A m) (incidenceCellCenter A c)).Nonempty)
    (q : ℕ) (different : q ≠ n) : IsZero ((K).homology q) :=
  (representableCostalkCochainComplex_isZero_homology k A c S m nonempty q different).of_iso
    ((HomologicalComplex.homologyFunctor _ _ q).mapIso
      (representedWeightCostalkComplexIso A S c m k))

theorem representedWeightCellularComplex_isZero_homology_of_empty
    (empty : costalkRegion (augmentedForms A) (Sum.inl '' S)
      (augmentedLatticePairing A m) (incidenceCellCenter A c) = ∅) (q : ℕ) :
    IsZero ((K).homology q) :=
  (representableCostalkCochainComplex_isZero_homology_of_empty k A c S m empty q).of_iso
    ((HomologicalComplex.homologyFunctor _ _ q).mapIso
      (representedWeightCostalkComplexIso A S c m k))

end ToricPower.IntegralArrangement
