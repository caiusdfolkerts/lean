module

public import PaperVerification.FermionPairedDescent
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Finset.Sort

/-!
# Exact correspondence with the paper's paired monomials

The valid exterior words are precisely the pairs of supports with nonnegative
arrival heights.  The natural rectangle lengths equal the printed integer
bounds, and theta-then-xi sorting gives exactly the paper's ordered exterior
product.  Thus the alternative index used in the construction loses no
parameters, words, or exponent choices.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators TensorProduct

variable {R : Type*} [CommRing R] {n : ℕ}

-- Prefix cardinalities use the same equality decision as `ValidWord` and `wordHeight`.
local instance FermionPairedIndex_localInst_1 : DecidableEq (Fin n ⊕ Fin n) :=
  (interleavedOddOrder n).toDecidableEq

@[simp] theorem wordMultiplicity_disjSum (T S : Finset (Fin n)) (i : Fin n) :
    wordMultiplicity (T.disjSum S) i = marks T S i := by
  simp only [wordMultiplicity,marks,Finset.inl_mem_disjSum,Finset.inr_mem_disjSum]

theorem height_eq_prefix_card (T S : Finset (Fin n)) (i : Fin n) :
    height T S i = (i.val : ℤ)+1-((T.disjSum S ∩ pairedPrefix n (i.val+1)).card : ℤ) := by
  have hc := prefix_card_eq_multiplicity_sum (T.disjSum S) (i.val+1)
  have hf : Finset.univ.filter (fun j : Fin n ↦ j.val < i.val+1) =
      Finset.univ.filter (fun j : Fin n ↦ j ≤ i) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    change j.val < i.val+1 ↔ j.val ≤ i.val
    omega
  rw [hf] at hc
  simp only [wordMultiplicity_disjSum] at hc
  have hs : (∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j ≤ i), (marks T S j : ℤ)) =
      ((T.disjSum S ∩ pairedPrefix n (i.val+1)).card : ℤ) := by
    exact_mod_cast hc.symm
  rw [height,hs]

theorem validWord_disjSum_iff (T S : Finset (Fin n)) :
    ValidWord (T.disjSum S) ↔ ∀ i, 0 ≤ height T S i := by
  constructor
  · intro h i
    rw [height_eq_prefix_card]
    have hi := h (i.val+1) (Nat.succ_le_of_lt i.isLt)
    omega
  · intro h j hj
    cases j with
    | zero => simp [pairedPrefix]
    | succ j =>
      let i : Fin n := ⟨j,by omega⟩
      have hi := h i
      rw [height_eq_prefix_card] at hi
      change 0 ≤ (j : ℤ)+1-((T.disjSum S ∩ pairedPrefix n (j+1)).card : ℤ) at hi
      omega

theorem previousHeight_eq_wordHeight (T S : Finset (Fin n))
    (h : ValidWord (T.disjSum S)) (i : Fin n) :
    previousHeight T S i = (wordHeight (T.disjSum S) i.val : ℤ) := by
  have hc := prefix_card_eq_multiplicity_sum (T.disjSum S) i.val
  simp only [wordMultiplicity_disjSum] at hc
  have hs : (∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j < i), (marks T S j : ℤ)) =
      ((T.disjSum S ∩ pairedPrefix n i.val).card : ℤ) := by
    exact_mod_cast hc.symm
  rw [previousHeight,hs,wordHeight,Nat.cast_sub (h i.val i.isLt.le)]

theorem wordBoxBounds_disjSum_cast (d : PairedData (K := R) (n := n))
    (T S : Finset (Fin n)) (h : ValidWord (T.disjSum S)) (i : Fin n) :
    (wordBoxBounds d.r d.u d.v d.s (T.disjSum S) i : ℤ) = pairedBound d T S i := by
  have he := wordBoxBounds_add_shift d.r d.u d.v d.s d.degree_split (T.disjSum S) h i
  rw [heightDegree_wordSign (T.disjSum S) h d.s i,wordShift_apply] at he
  simp only [Finset.inl_mem_disjSum,Finset.inr_mem_disjSum] at he
  have he' := congrArg (fun k : ℕ ↦ (k : ℤ)) he
  push_cast at he'
  rw [← previousHeight_eq_wordHeight T S h i] at he'
  unfold pairedBound
  omega

def pairedIndexToPower (d : PairedData (K := R) (n := n)) (z : PairedIndex d) :
    PairedPowerIndex d.r d.u d.v d.s := by
  let W := z.val.1.1.disjSum z.val.1.2
  have hW : ValidWord W := (validWord_disjSum_iff _ _).mpr z.property.1
  refine ⟨W,⟨⟨Finsupp.equivFunOnFinite.symm z.val.2,?_⟩,hW⟩⟩
  intro i
  have hi := z.property.2 i
  rw [← wordBoxBounds_disjSum_cast d _ _ hW i] at hi
  exact_mod_cast hi

def pairedPowerToIndex (d : PairedData (K := R) (n := n))
    (z : PairedPowerIndex d.r d.u d.v d.s) : PairedIndex d := by
  have hW : ValidWord (z.1.toLeft.disjSum z.1.toRight) := by
    rw [Finset.toLeft_disjSum_toRight]
    exact z.2.property
  refine ⟨((z.1.toLeft,z.1.toRight),fun i ↦ z.2.val.val i),
    (validWord_disjSum_iff _ _).mp hW,?_⟩
  intro i
  rw [← wordBoxBounds_disjSum_cast d _ _ hW i,Finset.toLeft_disjSum_toRight]
  exact_mod_cast z.2.val.property i

private theorem pairedPowerIndex_ext {r u v : Fin n → ℕ} {s : ℕ}
    {a b : PairedPowerIndex r u v s} (hW : a.1 = b.1)
    (he : a.2.val.val = b.2.val.val) : a = b := by
  rcases a with ⟨W, ⟨⟨e, he'⟩, hW'⟩⟩
  rcases b with ⟨U, ⟨⟨f, hf'⟩, hU'⟩⟩
  dsimp at hW he
  subst U
  subst f
  rfl

/-- An exact equivalence, including all words and every integer exponent
bound in the statement of Theorem 1.1. -/
def pairedIndexEquiv (d : PairedData (K := R) (n := n)) :
    PairedIndex d ≃ PairedPowerIndex d.r d.u d.v d.s where
  toFun := pairedIndexToPower d
  invFun := pairedPowerToIndex d
  left_inv z := by
    apply Subtype.ext
    simp only [pairedIndexToPower,pairedPowerToIndex,Finset.toLeft_disjSum,
      Finset.toRight_disjSum,Finsupp.coe_equivFunOnFinite_symm]
  right_inv z := by
    rcases z with ⟨W,⟨⟨e,he⟩,hW⟩⟩
    apply pairedPowerIndex_ext
    · exact Finset.toLeft_disjSum_toRight
    · exact Finsupp.equivFunOnFinite_symm_coe e

-- The paper orders every theta generator before every xi generator.
local instance FermionPairedIndex_localInst_2 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
local instance FermionPairedIndex_localInst_3 : PartialOrder (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toPartialOrder
local instance FermionPairedIndex_localInst_4 : Preorder (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toPreorder
local instance FermionPairedIndex_localInst_5 : LE (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toLE
local instance FermionPairedIndex_localInst_6 : LT (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toLT
local instance FermionPairedIndex_localInst_7 : DecidableEq (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toDecidableEq

theorem sort_disjSum_theta_xi (T S : Finset (Fin n)) :
    (T.disjSum S).sort = T.sort.map Sum.inl ++ S.sort.map Sum.inr := by
  have hl : (T.sort.map (Sum.inl : Fin n → OddIndex n)).SortedLT := by
    rw [List.sortedLT_iff_pairwise,List.pairwise_map]
    exact T.sortedLT_sort.pairwise.imp (fun {_ _} h ↦ h)
  have hr : (S.sort.map (Sum.inr : Fin n → OddIndex n)).SortedLT := by
    rw [List.sortedLT_iff_pairwise,List.pairwise_map]
    apply S.sortedLT_sort.pairwise.imp
    intro i j hij
    change n+i.val < n+j.val
    exact Nat.add_lt_add_left hij n
  have hs : (T.sort.map (Sum.inl : Fin n → OddIndex n) ++ S.sort.map Sum.inr).SortedLT := by
    apply List.sortedLT_append.mpr
    refine ⟨hl,hr,?_⟩
    intro a ha b hb
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
    change i.val < n+j.val
    omega
  apply (T.disjSum S).sortedLT_sort.eq_of_mem_iff hs
  intro a
  cases a <;> simp

theorem includeRight_basis_disjSum (T S : Finset (Fin n)) :
    (Algebra.TensorProduct.includeRight :
      ExteriorAlgebra R (OddModule R n) →ₐ[R] SuperRing R n)
      ((Pi.basisFun R (OddIndex n)).ExteriorAlgebra (T.disjSum S)) =
        (T.sort.map (theta R n)).prod * (S.sort.map (xi R n)).prod := by
  rw [Module.Basis.exteriorAlgebra_eq_prod_map_sort,sort_disjSum_theta_xi,
    List.map_append,List.map_append,List.prod_append,map_mul,map_list_prod,map_list_prod]
  simp only [List.map_map,Function.comp_def,Pi.basisFun_apply]
  have hθ : (fun i : Fin n =>
      (Algebra.TensorProduct.includeRight :
        ExteriorAlgebra R (OddModule R n) →ₐ[R] SuperRing R n)
        (ExteriorAlgebra.ι R (Pi.single (Sum.inl i) 1))) =
      PaperVerification.Fermion.theta R n := by
    funext i
    unfold PaperVerification.Fermion.theta
    apply congrArg (Algebra.TensorProduct.includeRight :
      ExteriorAlgebra R (OddModule R n) →ₐ[R] SuperRing R n)
    apply congrArg (ExteriorAlgebra.ι R)
    funext j
    by_cases h : j = Sum.inl i <;> simp [Pi.single_apply, h]
  have hξ : (fun i : Fin n =>
      (Algebra.TensorProduct.includeRight :
        ExteriorAlgebra R (OddModule R n) →ₐ[R] SuperRing R n)
        (ExteriorAlgebra.ι R (Pi.single (Sum.inr i) 1))) =
      PaperVerification.Fermion.xi R n := by
    funext i
    unfold PaperVerification.Fermion.xi
    apply congrArg (Algebra.TensorProduct.includeRight :
      ExteriorAlgebra R (OddModule R n) →ₐ[R] SuperRing R n)
    apply congrArg (ExteriorAlgebra.ι R)
    funext j
    by_cases h : j = Sum.inr i <;> simp [Pi.single_apply, h]
  rw [hθ, hξ]

theorem boxMonomial_eq_tensor (T S : Finset (Fin n)) (e : Fin n → ℕ) :
    boxMonomial (K := R) T S e =
      monomial (Finsupp.equivFunOnFinite.symm e) 1 ⊗ₜ[R]
        (Pi.basisFun R (OddIndex n)).ExteriorAlgebra (T.disjSum S) := by
  rw [boxMonomial,← includeRight_basis_disjSum]
  simp only [Algebra.TensorProduct.includeRight_apply,TensorProduct.smul_tmul',
    smul_eq_mul,mul_one]

@[simp] theorem pairedCoupledClasses_indexEquiv (d : PairedData (K := R) (n := n))
    (z : PairedIndex d) :
    pairedCoupledClasses d (pairedIndexEquiv d z) = pairedClasses d z := by
  rw [pairedClasses,boxMonomial_eq_tensor]
  rfl

/-- The exact paper-facing basis statement for all original coefficients.
This source candidate retains the literal integer heights and monomials. -/
def pairedPaperBasis (d : PairedData (K := R) (n := n)) :
    Module.Basis (PairedIndex d) R (PairedQuotient d.beta d.phi d.a d.b) :=
  (pairedArbitraryRingBasis d).reindex (pairedIndexEquiv d).symm

@[simp] theorem pairedPaperBasis_apply (d : PairedData (K := R) (n := n))
    (z : PairedIndex d) : pairedPaperBasis d z = pairedClasses d z := by
  rw [pairedPaperBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    pairedArbitraryRingBasis_apply,pairedCoupledClasses_indexEquiv]

theorem paired_basis_claim (d : PairedData (K := R) (n := n)) : PairedBasisClaim d := by
  have he : (pairedPaperBasis d : PairedIndex d → PairedQuotient d.beta d.phi d.a d.b) =
      pairedClasses d := funext (pairedPaperBasis_apply d)
  constructor
  · rw [← he]
    exact (pairedPaperBasis d).linearIndependent
  · rw [← he]
    exact (pairedPaperBasis d).span_eq

end PaperVerification.Fermion
