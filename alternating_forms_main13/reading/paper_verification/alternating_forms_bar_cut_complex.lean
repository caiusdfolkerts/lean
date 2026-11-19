module

public import PaperVerification.AlternatingFormsBarMerging
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# The coefficient complex of admissible cuts

The coefficient modules have exactly the actual normal-block bar words
of fixed concatenation and length as basis. Their equivalence with the
exterior valid-cut submodules is explicit on every basis vector. This
transports the previously proved contraction to a cycle-boundary theorem.
The comparison with the algebra's leading adjacent-product differential
is a separate required step, not an assumption in this construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarCompositions

open PaperVerification.MonomialBarCuts

variable {K α : Type*} [CommRing K]
  (R : α → α → Prop) (W : List α)

def BarIndex (r : ℕ) :=
  {L : AdmissibleFactorization R W // L.val.val.length=r}

def CutIndex (n : ℕ) (mandatory : Finset (Fin n)) (r : ℕ) :=
  {S : Finset (Fin n) // mandatory⊆S ∧ S.card=r}

def barCutDegreeEquiv (r : ℕ) :
    BarIndex R W r ≃ CutIndex (W.length+1) (mandatoryCuts R W) (r+1) where
  toFun L := ⟨(admissibleCutEquiv R W L.val).val,
    (admissibleCutEquiv R W L.val).property,by
      rw [admissibleCutEquiv_card,L.property]⟩
  invFun S := ⟨(admissibleCutEquiv R W).symm ⟨S.val,S.property.1⟩,by
    have h := admissibleCutEquiv_card R W
      ((admissibleCutEquiv R W).symm ⟨S.val,S.property.1⟩)
    have he : (admissibleCutEquiv R W
        ((admissibleCutEquiv R W).symm ⟨S.val,S.property.1⟩)).val.card=S.val.card :=
      congrArg (fun T : AdmissibleCutSet R W ↦ T.val.card)
        ((admissibleCutEquiv R W).apply_symm_apply ⟨S.val,S.property.1⟩)
    have hc := S.property.2
    omega⟩
  left_inv L := by
    apply Subtype.ext
    exact (admissibleCutEquiv R W).symm_apply_apply L.val
  right_inv S := by
    apply Subtype.ext
    change (admissibleCutEquiv R W
      ((admissibleCutEquiv R W).symm ⟨S.val,S.property.1⟩)).val=S.val
    exact congrArg (fun T : AdmissibleCutSet R W ↦ T.val)
      ((admissibleCutEquiv R W).apply_symm_apply ⟨S.val,S.property.1⟩)

def cutBasis (n : ℕ) (mandatory : Finset (Fin n)) (r : ℕ) :
    Module.Basis (CutIndex n mandatory r) K (cutPiece (K := K) n mandatory r) := by
  let b := (coordinateBasis (K := K) n).ExteriorAlgebra
  let v : CutIndex n mandatory r → ExteriorAlgebra K (Fin n → K) := fun S ↦ b S.val
  have hli : LinearIndependent K v :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  have hs : Submodule.span K (Set.range v)=cutPiece (K := K) n mandatory r := by
    congr 1
    ext x
    constructor
    · rintro ⟨S,rfl⟩
      exact ⟨S.val,S.property.1,S.property.2,rfl⟩
    · rintro ⟨S,hS,hcard,hx⟩
      exact ⟨⟨S,hS,hcard⟩,hx.symm⟩
  exact (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hs)

@[simp] theorem cutBasis_apply (n : ℕ) (mandatory : Finset (Fin n)) (r : ℕ)
    (S : CutIndex n mandatory r) :
    (cutBasis (K := K) n mandatory r S).val=
      (coordinateBasis (K := K) n).ExteriorAlgebra S.val := by
  simp only [cutBasis,Module.Basis.map_apply]
  exact (LinearEquiv.coe_ofEq_apply _ _).trans (Module.Basis.coe_span_apply _ S)

def barCutLinearEquiv (r : ℕ) :
    (BarIndex R W r →₀ K) ≃ₗ[K]
      cutPiece (K := K) (W.length+1) (mandatoryCuts R W) (r+1) :=
  (Finsupp.domLCongr (barCutDegreeEquiv R W r)).trans
    (cutBasis (K := K) (W.length+1) (mandatoryCuts R W) (r+1)).repr.symm

@[simp] theorem barCutLinearEquiv_single (r : ℕ) (L : BarIndex R W r) :
    (barCutLinearEquiv (K := K) R W r (Finsupp.single L 1)).val=
      (coordinateBasis (K := K) (W.length+1)).ExteriorAlgebra
        (boundaries W L.val.val) := by
  simp only [barCutLinearEquiv,LinearEquiv.trans_apply,
    Finsupp.domLCongr_single,Module.Basis.repr_symm_single_one,cutBasis_apply]
  change (coordinateBasis (K := K) (W.length+1)).ExteriorAlgebra
      (admissibleCutMap R W L.val).val=_
  rfl

def cutDegreeDifferential (n : ℕ) (mandatory : Finset (Fin n)) (r : ℕ) :
    cutPiece (K := K) n mandatory (r+1) →ₗ[K] cutPiece (K := K) n mandatory r :=
  LinearMap.codRestrict _
    ((differential n mandatory).comp (cutPiece n mandatory (r+1)).subtype)
    (fun x ↦ differential_mem_cutPiece n mandatory r x.val x.property)

def cutModelDifferential (r : ℕ) :
    (BarIndex R W (r+1) →₀ K) →ₗ[K] (BarIndex R W r →₀ K) :=
  (barCutLinearEquiv R W r).symm.toLinearMap.comp
    ((cutDegreeDifferential (W.length+1) (mandatoryCuts R W) (r+1)).comp
      (barCutLinearEquiv R W (r+1)).toLinearMap)

theorem cutModelDifferential_comm (r : ℕ) (z : BarIndex R W (r+1) →₀ K) :
    (barCutLinearEquiv R W r (cutModelDifferential (K := K) R W r z)).val=
      differential (W.length+1) (mandatoryCuts R W)
        (barCutLinearEquiv R W (r+1) z).val := by
  simp only [cutModelDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rfl

theorem cutModelDifferential_squared (r : ℕ) (z : BarIndex R W (r+2) →₀ K) :
    cutModelDifferential R W r (cutModelDifferential (K := K) R W (r+1) z)=0 := by
  apply (barCutLinearEquiv R W r).injective
  apply Subtype.ext
  rw [cutModelDifferential_comm,cutModelDifferential_comm,map_zero]
  exact differential_squared (W.length+1) (mandatoryCuts R W) _

/-- Every off-diagonal cycle in this explicit coefficient complex is an
actual boundary; the excluded degree is the literal word length. -/
theorem cutModel_cycle_is_boundary (r : ℕ) (hr : r≠W.length)
    (z : BarIndex R W r →₀ K)
    (hz : differential (W.length+1) (mandatoryCuts R W)
      (barCutLinearEquiv (K := K) R W r z).val=0) :
    ∃ y : BarIndex R W (r+1) →₀ K,cutModelDifferential R W r y=z := by
  obtain ⟨y,hy,hdy⟩ := off_diagonal_cycle_is_boundary (W.length+1)
    (mandatoryCuts R W) (r+1) (by omega)
      (barCutLinearEquiv (K := K) R W r z).val
      (barCutLinearEquiv (K := K) R W r z).property hz
  refine ⟨(barCutLinearEquiv R W (r+1)).symm ⟨y,hy⟩,?_⟩
  apply (barCutLinearEquiv R W r).injective
  apply Subtype.ext
  rw [cutModelDifferential_comm,LinearEquiv.apply_symm_apply]
  exact hdy

end PaperVerification.AlternatingForms.BarCompositions

