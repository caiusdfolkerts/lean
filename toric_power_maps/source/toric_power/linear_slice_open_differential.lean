module

public import ToricPower.LinearSliceOpenCoordinates
public import ToricPower.CWSubcomplexBoundary

/-!
# The original incidence matrix on finite open parts of the closed slice

The scalar cochain differential is computed in the actual characteristic
cell coordinates. Each coefficient is the original ambient cellular
incidence, with no independent choice of sign or boundary operator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (zeroRows : Set (Fin s ⊕ Fin n))

local notation "E" => Fin n → ℝ
local notation "L" => arrangementZeroSlice (augmentedForms A) zeroRows

local instance sliceDifferentialPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

local instance sliceDifferentialInheritedCW : CWComplex (L : Set E) :=
  inferInstanceAs (CWComplex (periodicLinearSliceSubcomplex A zeroRows : Set E))

variable (R : Type) [Ring R] (U : OpenCellSupport A)

theorem sliceSupportBasis_differential (q : ℕ)
    (i : SliceSupportCell A zeroRows U q) (j : SliceSupportCell A zeroRows U (q + 1)) :
    (sliceSupportBasis A zeroRows R U q).repr
        (TauCeti.cellularDifferential (relativeCWCarrier (sliceSupportComplement A zeroRows U))
          (ModuleCat.of R R) q (sliceSupportBasis A zeroRows R U (q + 1) j)) i =
      TauCeti.cellularIncidence (arrangementCarrier A) R q i.val.val j.val.val := by
  simp only [sliceSupportBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  exact (TauCeti.cellularIncidence_def _ R q _ _).symm.trans
    ((relativeCellularIncidence (L : Set E) (sliceSupportComplement A zeroRows U) R q _ _).trans
      (subcomplexCellularIncidence (periodicLinearSliceSubcomplex A zeroRows) R q i.val j.val))

/-- The actual chain-term transports keep every original incidence. -/
theorem sliceSupportChainCoordinates_differential_single (q : ℕ)
    (i : SliceSupportCell A zeroRows U q) (j : SliceSupportCell A zeroRows U (q + 1)) :
    sliceSupportChainCoordinates A zeroRows R U q
        ((sliceSupportChainComplex A zeroRows (ModuleCat.of R R) U).d (q + 1) q
          ((sliceSupportChainCoordinates A zeroRows R U (q + 1)).symm (Finsupp.single j 1))) i =
      TauCeti.cellularIncidence (arrangementCarrier A) R q i.val.val j.val.val := by
  let C := relativeCWCarrier (sliceSupportComplement A zeroRows U)
  let e₁ := eqToIso (TauCeti.cellularChainComplex_X C (ModuleCat.of R R) (q + 1))
  let e₀ := eqToIso (TauCeti.cellularChainComplex_X C (ModuleCat.of R R) q)
  have square :
      (sliceSupportChainComplex A zeroRows (ModuleCat.of R R) U).d (q + 1) q ≫ e₀.hom =
        e₁.hom ≫ TauCeti.cellularDifferential C (ModuleCat.of R R) q := by
    change (TauCeti.cellularChainComplex C (ModuleCat.of R R)).d (q + 1) q ≫ _ = _
    rw [TauCeti.cellularChainComplex_d]
    simp [e₀, e₁]
  have eval := ConcreteCategory.congr_hom square
    ((sliceSupportChainCoordinates A zeroRows R U (q + 1)).symm (Finsupp.single j 1))
  have basis : e₁.hom
      ((sliceSupportChainCoordinates A zeroRows R U (q + 1)).symm (Finsupp.single j 1)) =
        sliceSupportBasis A zeroRows R U (q + 1) j := by
    change e₁.hom (e₁.inv ((sliceSupportBasis A zeroRows R U (q + 1)).repr.symm
      (Finsupp.single j 1))) = _
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply,
      Module.Basis.repr_symm_apply, Finsupp.linearCombination_single, one_smul]
  simp only [ConcreteCategory.comp_apply] at eval
  change (sliceSupportBasis A zeroRows R U q).repr
    (e₀.hom ((sliceSupportChainComplex A zeroRows (ModuleCat.of R R) U).d (q + 1) q
      ((sliceSupportChainCoordinates A zeroRows R U (q + 1)).symm (Finsupp.single j 1)))) i = _
  refine (congrArg (fun w => (sliceSupportBasis A zeroRows R U q).repr w i) eval).trans ?_
  exact (congrArg (fun w => (sliceSupportBasis A zeroRows R U q).repr
    (TauCeti.cellularDifferential C (ModuleCat.of R R) q w) i) basis).trans
      (sliceSupportBasis_differential A zeroRows R U q i j)

section Field

variable (k : Type) [Field k]

/-- Read a scalar cochain as the actual linear functional on chains. -/
def sliceSupportCochainEvaluation (q : ℕ) (φ : (sliceSupportCochainComplex A zeroRows k U).X q) :
    (sliceSupportChainComplex A zeroRows (ModuleCat.of k k) U).X q →ₗ[k] k :=
  ModuleCat.Hom.hom (A := (sliceSupportChainComplex A zeroRows (ModuleCat.of k k) U).X q)
    (B := ModuleCat.of k k) φ

@[simp]
theorem sliceSupportCochainCoordinates_apply (q : ℕ) [Finite (SliceSupportCell A zeroRows U q)]
    (φ : (sliceSupportChainComplex A zeroRows (ModuleCat.of k k) U).X q ⟶ ModuleCat.of k k)
    (i : SliceSupportCell A zeroRows U q) :
    sliceSupportCochainCoordinates A zeroRows k U q φ i =
      φ ((sliceSupportChainCoordinates A zeroRows k U q).symm (Finsupp.single i 1)) := rfl

/-- The basis cochain is literal extraction of its chain coordinate. -/
theorem sliceSupportCochainCoordinates_symm_single_apply (q : ℕ)
    [Finite (SliceSupportCell A zeroRows U q)] (i : SliceSupportCell A zeroRows U q)
    (x : (sliceSupportChainComplex A zeroRows (ModuleCat.of k k) U).X q) :
    sliceSupportCochainEvaluation A zeroRows U k q
      ((sliceSupportCochainCoordinates A zeroRows k U q).symm (Finsupp.single i 1)) x =
      sliceSupportChainCoordinates A zeroRows k U q x i := by
  let φ : (sliceSupportChainComplex A zeroRows (ModuleCat.of k k) U).X q ⟶ ModuleCat.of k k :=
    ModuleCat.ofHom ((Finsupp.lapply i).comp (sliceSupportChainCoordinates A zeroRows k U q).toLinearMap)
  have coordinates : sliceSupportCochainCoordinates A zeroRows k U q φ = Finsupp.single i 1 := by
    ext j
    rw [sliceSupportCochainCoordinates_apply]
    change sliceSupportChainCoordinates A zeroRows k U q
      ((sliceSupportChainCoordinates A zeroRows k U q).symm (Finsupp.single j 1)) i = _
    rw [LinearEquiv.apply_symm_apply]
    simp only [Finsupp.single_apply, eq_comm]
  have inverse : (sliceSupportCochainCoordinates A zeroRows k U q).symm (Finsupp.single i 1) = φ :=
    (sliceSupportCochainCoordinates A zeroRows k U q).symm_apply_eq.mpr coordinates.symm
  rw [inverse]
  rfl

/-- Each coefficient of the actual scalar differential is precisely
the ambient periodic incidence of the same two cells. -/
theorem sliceSupportCochainCoordinates_differential_single (q : ℕ)
    [Finite (SliceSupportCell A zeroRows U q)] [Finite (SliceSupportCell A zeroRows U (q + 1))]
    (i : SliceSupportCell A zeroRows U q) (j : SliceSupportCell A zeroRows U (q + 1)) :
    sliceSupportCochainCoordinates A zeroRows k U (q + 1)
        ((sliceSupportCochainComplex A zeroRows k U).d q (q + 1)
          ((sliceSupportCochainCoordinates A zeroRows k U q).symm (Finsupp.single i 1))) j =
      TauCeti.cellularIncidence (arrangementCarrier A) k q i.val.val j.val.val := by
  rw [sliceSupportCochainCoordinates_apply]
  change sliceSupportCochainEvaluation A zeroRows U k q
      ((sliceSupportCochainCoordinates A zeroRows k U q).symm (Finsupp.single i 1))
      ((sliceSupportChainComplex A zeroRows (ModuleCat.of k k) U).d (q + 1) q
        ((sliceSupportChainCoordinates A zeroRows k U (q + 1)).symm (Finsupp.single j 1))) = _
  rw [sliceSupportCochainCoordinates_symm_single_apply]
  exact sliceSupportChainCoordinates_differential_single A zeroRows k U q i j

end Field
end ToricPower.IntegralArrangement
