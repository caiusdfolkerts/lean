module

public import PaperVerification.AlternatingFormsEvenSingletonAction
public import Mathlib.LinearAlgebra.Pi

/-!
# All homogeneous exterior components as singleton blocks

The block indices carry the exact equation `number of singletons + 2q = s`.
Consequently this decomposition includes all parities, zero-degree blocks,
and degrees beyond the ambient dimension without truncated-subtraction
conventions.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.EvenSingletons

open scoped BigOperators

section Indices

variable {ι : Type*} [DecidableEq ι]

abbrev DegreeBlock (ι : Type*) [DecidableEq ι] (s : ℕ) :=
  {Sq : SingletonState ι × Fin (s + 1) // singletonDegree Sq.1 + 2 * Sq.2.val = s}

instance [Fintype ι] (s : ℕ) : Fintype (DegreeBlock ι s) := Fintype.ofFinite _

abbrev BlockSubsets {s : ℕ} (J : DegreeBlock ι s) :=
  FixedSubsets (Available J.val.1) J.val.2.val

def blockStateEquiv (s : ℕ) : ((J : DegreeBlock ι s) × BlockSubsets J) ≃ DegreeState ι s where
  toFun x := ⟨⟨x.1.val.1, x.2.val⟩, by
    change singletonDegree x.1.val.1 + 2 * x.2.val.card = s
    rw [x.2.property]
    exact x.1.property⟩
  invFun T :=
    ⟨⟨(T.val.1, ⟨T.val.2.card, by
        have h := T.property
        change singletonDegree T.val.1 + 2 * T.val.2.card = s at h
        omega⟩), T.property⟩, ⟨T.val.2, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨⟨S, ⟨q, hq⟩⟩, hdeg⟩, ⟨P, hP⟩⟩
    dsimp only at P hP hdeg
    subst q
    rfl
  right_inv := by
    rintro ⟨⟨S, P⟩, hP⟩
    rfl

end Indices

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [LinearOrder ι] [Fintype ι]
local notation "E" => ExteriorAlgebra K M

def groupedDegreeBasis (b : Module.Basis (ι ⊕ ι) K M) (s : ℕ) :
    Module.Basis ((J : DegreeBlock ι s) × BlockSubsets J) K (⋀[K]^s M) :=
  (stateDegreeBasis b s).reindex (blockStateEquiv s).symm

@[simp] theorem groupedDegreeBasis_coe (b : Module.Basis (ι ⊕ ι) K M) (s : ℕ)
    (J : DegreeBlock ι s) (P : BlockSubsets J) :
    (groupedDegreeBasis b s ⟨J, P⟩ : E) = stateMonomial b ⟨J.val.1, P.val⟩ := by
  simp only [groupedDegreeBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    stateDegreeBasis_coe, blockStateEquiv]
  rfl

def blockIntoDegree (b : Module.Basis (ι ⊕ ι) K M) (s : ℕ) (J : DegreeBlock ι s) :
    (BlockSubsets J → K) →ₗ[K] (⋀[K]^s M) :=
  (blockEvaluation b J.val.1 J.val.2.val).codRestrict _ (fun v => by
    have h := blockEvaluation_homogeneous b J.val.1 J.val.2.val v
    rwa [J.property] at h)

theorem blockIntoDegree_eq_sum (b : Module.Basis (ι ⊕ ι) K M) (s : ℕ)
    (J : DegreeBlock ι s) (v : BlockSubsets J → K) :
    blockIntoDegree b s J v =
      ∑ P : BlockSubsets J, v P • groupedDegreeBasis b s ⟨J, P⟩ := by
  apply Subtype.ext
  change blockEvaluation b J.val.1 J.val.2.val v = _
  rw [blockEvaluation_apply]
  simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, groupedDegreeBasis_coe]

/-- The explicit finite product decomposition of the genuine s-th exterior power. -/
def degreeCoordinates (b : Module.Basis (ι ⊕ ι) K M) (s : ℕ) :
    (⋀[K]^s M) ≃ₗ[K] ((J : DegreeBlock ι s) → BlockSubsets J → K) :=
  (groupedDegreeBasis b s).equivFun.trans
    (LinearEquiv.piCurry K (fun (J : DegreeBlock ι s) (_ : BlockSubsets J) => K))

theorem degreeCoordinates_symm (b : Module.Basis (ι ⊕ ι) K M) (s : ℕ)
    (v : (J : DegreeBlock ι s) → BlockSubsets J → K) :
    (degreeCoordinates b s).symm v = ∑ J, blockIntoDegree b s J (v J) := by
  change (groupedDegreeBasis b s).equivFun.symm (fun x => v x.1 x.2) = _
  rw [Module.Basis.equivFun_symm_apply, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro J hJ
  exact (blockIntoDegree_eq_sum b s J (v J)).symm

theorem degreeCoordinates_symm_single (b : Module.Basis (ι ⊕ ι) K M) (s : ℕ)
    (J : DegreeBlock ι s) (v : BlockSubsets J → K) :
    (degreeCoordinates b s).symm (Pi.single J v) = blockIntoDegree b s J v := by
  rw [degreeCoordinates_symm]
  rw [Finset.sum_eq_single J]
  · simp only [Pi.single_eq_same]
  · intro L hL hne
    simp [hne, Ne.symm hne]
  · simp

@[simp] theorem degreeCoordinates_block (b : Module.Basis (ι ⊕ ι) K M) (s : ℕ)
    (J : DegreeBlock ι s) (v : BlockSubsets J → K) :
    degreeCoordinates b s (blockIntoDegree b s J v) = Pi.single J v := by
  apply (degreeCoordinates b s).symm.injective
  rw [LinearEquiv.symm_apply_apply, degreeCoordinates_symm_single]

theorem blockEvaluation_single (b : Module.Basis (ι ⊕ ι) K M) (S : SingletonState ι)
    (q : ℕ) (P : FixedSubsets (Available S) q) :
    blockEvaluation b S q (Pi.single P 1) = stateMonomial b ⟨S, P.val⟩ := by
  rw [blockEvaluation_apply]
  simp [Pi.single_apply]

end PaperVerification.AlternatingForms.EvenSingletons
