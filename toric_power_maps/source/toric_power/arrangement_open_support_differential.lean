module

public import ToricPower.ArrangementOpenSupportCoordinates

/-!
# The original incidence matrix on finite open supports

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

local instance openDifferentialPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

variable (R : Type) [Ring R] (U : OpenCellSupport A)

theorem openSupportBasis_differential (q : ℕ)
    (i : OpenSupportCell A U q) (j : OpenSupportCell A U (q + 1)) :
    (openSupportBasis A R U q).repr
        (TauCeti.cellularDifferential (relativeCWCarrier (openSupportComplement A U))
          (ModuleCat.of R R) q (openSupportBasis A R U (q + 1) j)) i =
      TauCeti.cellularIncidence (arrangementCarrier A) R q i.val j.val := by
  simp only [openSupportBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  exact (TauCeti.cellularIncidence_def _ R q _ _).symm.trans
    (relativeCellularIncidence (arrangementCarrier A) (openSupportComplement A U) R q _ _)

/-- The actual chain-term transports keep every original incidence. -/
theorem openSupportChainCoordinates_differential_single (q : ℕ)
    (i : OpenSupportCell A U q) (j : OpenSupportCell A U (q + 1)) :
    openSupportChainCoordinates A R U q
        ((openSupportChainComplex A (ModuleCat.of R R) U).d (q + 1) q
          ((openSupportChainCoordinates A R U (q + 1)).symm (Finsupp.single j 1))) i =
      TauCeti.cellularIncidence (arrangementCarrier A) R q i.val j.val := by
  let C := relativeCWCarrier (openSupportComplement A U)
  let e₁ := eqToIso (TauCeti.cellularChainComplex_X C (ModuleCat.of R R) (q + 1))
  let e₀ := eqToIso (TauCeti.cellularChainComplex_X C (ModuleCat.of R R) q)
  have square :
      (openSupportChainComplex A (ModuleCat.of R R) U).d (q + 1) q ≫ e₀.hom =
        e₁.hom ≫ TauCeti.cellularDifferential C (ModuleCat.of R R) q := by
    change (TauCeti.cellularChainComplex C (ModuleCat.of R R)).d (q + 1) q ≫ _ = _
    rw [TauCeti.cellularChainComplex_d]
    simp [e₀, e₁]
  have eval := ConcreteCategory.congr_hom square
    ((openSupportChainCoordinates A R U (q + 1)).symm (Finsupp.single j 1))
  have basis : e₁.hom
      ((openSupportChainCoordinates A R U (q + 1)).symm (Finsupp.single j 1)) =
        openSupportBasis A R U (q + 1) j := by
    change e₁.hom (e₁.inv ((openSupportBasis A R U (q + 1)).repr.symm
      (Finsupp.single j 1))) = _
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply,
      Module.Basis.repr_symm_apply, Finsupp.linearCombination_single, one_smul]
  simp only [ConcreteCategory.comp_apply] at eval
  change (openSupportBasis A R U q).repr
    (e₀.hom ((openSupportChainComplex A (ModuleCat.of R R) U).d (q + 1) q
      ((openSupportChainCoordinates A R U (q + 1)).symm (Finsupp.single j 1)))) i = _
  refine (congrArg (fun w => (openSupportBasis A R U q).repr w i) eval).trans ?_
  exact (congrArg (fun w => (openSupportBasis A R U q).repr
    (TauCeti.cellularDifferential C (ModuleCat.of R R) q w) i) basis).trans
      (openSupportBasis_differential A R U q i j)

section Field

variable (k : Type) [Field k]

/-- Read a scalar cochain as the actual linear functional on chains. -/
def openSupportCochainEvaluation (q : ℕ) (φ : (openSupportCochainComplex A k U).X q) :
    (openSupportChainComplex A (ModuleCat.of k k) U).X q →ₗ[k] k :=
  ModuleCat.Hom.hom (A := (openSupportChainComplex A (ModuleCat.of k k) U).X q)
    (B := ModuleCat.of k k) φ

@[simp]
theorem openSupportCochainCoordinates_apply (q : ℕ) [Finite (OpenSupportCell A U q)]
    (φ : (openSupportChainComplex A (ModuleCat.of k k) U).X q ⟶ ModuleCat.of k k)
    (i : OpenSupportCell A U q) :
    openSupportCochainCoordinates A k U q φ i =
      φ ((openSupportChainCoordinates A k U q).symm (Finsupp.single i 1)) := rfl

/-- The basis cochain is literal extraction of its chain coordinate. -/
theorem openSupportCochainCoordinates_symm_single_apply (q : ℕ)
    [Finite (OpenSupportCell A U q)] (i : OpenSupportCell A U q)
    (x : (openSupportChainComplex A (ModuleCat.of k k) U).X q) :
    openSupportCochainEvaluation A U k q
      ((openSupportCochainCoordinates A k U q).symm (Finsupp.single i 1)) x =
      openSupportChainCoordinates A k U q x i := by
  let φ : (openSupportChainComplex A (ModuleCat.of k k) U).X q ⟶ ModuleCat.of k k :=
    ModuleCat.ofHom ((Finsupp.lapply i).comp (openSupportChainCoordinates A k U q).toLinearMap)
  have coordinates : openSupportCochainCoordinates A k U q φ = Finsupp.single i 1 := by
    ext j
    rw [openSupportCochainCoordinates_apply]
    change openSupportChainCoordinates A k U q
      ((openSupportChainCoordinates A k U q).symm (Finsupp.single j 1)) i = _
    rw [LinearEquiv.apply_symm_apply]
    simp only [Finsupp.single_apply, eq_comm]
  have inverse : (openSupportCochainCoordinates A k U q).symm (Finsupp.single i 1) = φ :=
    (openSupportCochainCoordinates A k U q).symm_apply_eq.mpr coordinates.symm
  rw [inverse]
  rfl

/-- Each coefficient of the actual scalar differential is precisely
the ambient periodic incidence of the same two cells. -/
theorem openSupportCochainCoordinates_differential_single (q : ℕ)
    [Finite (OpenSupportCell A U q)] [Finite (OpenSupportCell A U (q + 1))]
    (i : OpenSupportCell A U q) (j : OpenSupportCell A U (q + 1)) :
    openSupportCochainCoordinates A k U (q + 1)
        ((openSupportCochainComplex A k U).d q (q + 1)
          ((openSupportCochainCoordinates A k U q).symm (Finsupp.single i 1))) j =
      TauCeti.cellularIncidence (arrangementCarrier A) k q i.val j.val := by
  rw [openSupportCochainCoordinates_apply]
  change openSupportCochainEvaluation A U k q
      ((openSupportCochainCoordinates A k U q).symm (Finsupp.single i 1))
      ((openSupportChainComplex A (ModuleCat.of k k) U).d (q + 1) q
        ((openSupportChainCoordinates A k U (q + 1)).symm (Finsupp.single j 1))) = _
  rw [openSupportCochainCoordinates_symm_single_apply]
  exact openSupportChainCoordinates_differential_single A k U q i j

end Field
end ToricPower.IntegralArrangement
