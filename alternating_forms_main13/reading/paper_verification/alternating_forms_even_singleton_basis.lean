module

public import PaperVerification.AlternatingFormsEvenSingletonIndex
public import PaperVerification.AlternatingFormsFrobenius
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.Order.Sum.Order

/-!
# A genuine singleton/pair basis of the exterior algebra

The basis vectors are literal singleton words multiplied by products of the
central pair variables.  They are compared with Mathlib's exterior basis by
proved nonzero permutation scalars.  This constructs the full basis and every
homogeneous component without assuming the desired Boolean decomposition.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.EvenSingletons

open scoped BigOperators

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [LinearOrder ι] [Fintype ι]

local instance : LinearOrder (ι ⊕ ι) := Sum.Lex.linearOrder

def selectionWord (A B : Finset ι) : List (ι ⊕ ι) :=
  A.toList.map Sum.inl ++ B.toList.map Sum.inr

theorem selectionWord_nodup (A B : Finset ι) : (selectionWord A B).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨A.nodup_toList.map Sum.inl_injective, B.nodup_toList.map Sum.inr_injective, ?_⟩
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
  exact Sum.inl_ne_inr hxy

theorem selectionWord_toFinset (A B : Finset ι) :
    (selectionWord A B).toFinset = A.disjSum B := by
  ext i
  cases i <;> simp [selectionWord]

def singletonWord (S : SingletonState ι) : List (ι ⊕ ι) :=
  selectionWord S.val.1 S.val.2

def singletonMonomial (b : Module.Basis (ι ⊕ ι) K M) (S : SingletonState ι) :
    ExteriorAlgebra K M :=
  (((singletonWord S).map b).map (ExteriorAlgebra.ι K)).prod

def stateMonomial (b : Module.Basis (ι ⊕ ι) K M) (T : PairedState ι) :
    ExteriorAlgebra K M :=
  singletonMonomial b T.1 *
    pairedMonomial (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i)) (pairSupport T.1 T.2)

/-- Every displayed state is a nonzero scalar multiple of its exact canonical
exterior basis vector.  The scalar accounts for all word-order signs. -/
theorem stateMonomial_unit (b : Module.Basis (ι ⊕ ι) K M) (T : PairedState ι) :
    ∃ ε : K, ε ≠ 0 ∧ stateMonomial b T = ε • b.ExteriorAlgebra (supportEquiv T) := by
  let u : ι → M := fun i => b (Sum.inl i)
  let v : ι → M := fun i => b (Sum.inr i)
  obtain ⟨a, ha, hfactor⟩ := exterior_monomial_singleton_pair_factorization
    (K := K) u v (selection T).1 (selection T).2
  rw [selection_sdiff_left, selection_sdiff_right, selection_inter] at hfactor
  obtain ⟨d, hd, hword⟩ := exterior_basis_word_unit b
    (selectionWord (selection T).1 (selection T).2)
    (selectionWord_nodup (selection T).1 (selection T).2)
  rw [selectionWord_toFinset, ← supportEquiv_apply] at hword
  have he : a • stateMonomial b T = d • b.ExteriorAlgebra (supportEquiv T) := by
    have hf : (((selectionWord (selection T).1 (selection T).2).map b).map
        (ExteriorAlgebra.ι K)).prod = a • stateMonomial b T := by
      simpa only [selectionWord, singletonMonomial, singletonWord, stateMonomial,
        List.map_append, List.map_map, Function.comp_def, u, v] using hfactor
    exact hf.symm.trans hword
  refine ⟨a⁻¹ * d, mul_ne_zero (inv_ne_zero ha) hd, ?_⟩
  have hh := congrArg (fun x : ExteriorAlgebra K M => a⁻¹ • x) he
  simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hh

def stateScalar (b : Module.Basis (ι ⊕ ι) K M) (T : PairedState ι) : K :=
  (stateMonomial_unit b T).choose

theorem stateScalar_ne_zero (b : Module.Basis (ι ⊕ ι) K M) (T : PairedState ι) :
    stateScalar b T ≠ 0 := (stateMonomial_unit b T).choose_spec.1

theorem stateScalar_spec (b : Module.Basis (ι ⊕ ι) K M) (T : PairedState ι) :
    stateMonomial b T = stateScalar b T • b.ExteriorAlgebra (supportEquiv T) :=
  (stateMonomial_unit b T).choose_spec.2

def stateBasis (b : Module.Basis (ι ⊕ ι) K M) :
    Module.Basis (PairedState ι) K (ExteriorAlgebra K M) :=
  (b.ExteriorAlgebra.reindex supportEquiv.symm).isUnitSMul
    (fun T => isUnit_iff_ne_zero.mpr (stateScalar_ne_zero b T))

@[simp] theorem stateBasis_apply (b : Module.Basis (ι ⊕ ι) K M) (T : PairedState ι) :
    stateBasis b T = stateMonomial b T := by
  rw [stateBasis, Module.Basis.isUnitSMul_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm]
  exact (stateScalar_spec b T).symm

/-- The homogeneous basis contains precisely the states of the original exterior degree. -/
def stateDegreeBasis (b : Module.Basis (ι ⊕ ι) K M) (s : ℕ) :
    Module.Basis (DegreeState ι s) K (⋀[K]^s M) :=
  ((b.exteriorPower s).reindex (degreeSupportEquiv s).symm).isUnitSMul
    (fun T => isUnit_iff_ne_zero.mpr (stateScalar_ne_zero b T.val))

@[simp] theorem stateDegreeBasis_coe (b : Module.Basis (ι ⊕ ι) K M) (s : ℕ)
    (T : DegreeState ι s) :
    (stateDegreeBasis b s T : ExteriorAlgebra K M) = stateMonomial b T.val := by
  simp only [stateDegreeBasis, Module.Basis.isUnitSMul_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm, Submodule.coe_smul]
  rw [← ExteriorAlgebra.basis_eq_coe_basis]
  exact (stateScalar_spec b T.val).symm

theorem stateMonomial_homogeneous (b : Module.Basis (ι ⊕ ι) K M) (T : PairedState ι) :
    stateMonomial b T ∈ ⋀[K]^(degree T) M := by
  rw [← stateDegreeBasis_coe b (degree T) (⟨T, rfl⟩ : DegreeState ι (degree T))]
  exact (stateDegreeBasis b (degree T) ⟨T, rfl⟩).property

theorem stateMonomial_ne_zero (b : Module.Basis (ι ⊕ ι) K M) (T : PairedState ι) :
    stateMonomial b T ≠ 0 := by
  rw [← stateBasis_apply]
  exact (stateBasis b).ne_zero T

end PaperVerification.AlternatingForms.EvenSingletons
