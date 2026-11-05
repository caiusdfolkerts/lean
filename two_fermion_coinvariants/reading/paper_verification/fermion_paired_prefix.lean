module

public import PaperVerification.FermionPrefixTransport
public import PaperVerification.FermionGaussGrading
public import Mathlib.Data.Fin.Embedding

/-!
# Harmonics on every smaller paired prefix

The prefix coordinate module is reindexed by the actual two copies of `Fin i`.
The full odd and mixed equations restrict to the corresponding equations with
restricted moment data. This is the algebraic transport needed before applying
the primitive and Gauss bounds at each prefix size.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n i : ℕ}

/-- The exact reindexing of the first `i` pairs. -/
def pairedPrefixEquiv (hi : i ≤ n) : (Fin i ⊕ Fin i) ≃ pairedPrefix n i where
  toFun
    | .inl j => ⟨.inl (j.castLE hi), (mem_pairedPrefix_inl _).mpr j.isLt⟩
    | .inr j => ⟨.inr (j.castLE hi), (mem_pairedPrefix_inr _).mpr j.isLt⟩
  invFun j := match j with
    | ⟨.inl k, hk⟩ => .inl ⟨k.val, (mem_pairedPrefix_inl k).mp hk⟩
    | ⟨.inr k, hk⟩ => .inr ⟨k.val, (mem_pairedPrefix_inr k).mp hk⟩
  left_inv j := by cases j <;> rfl
  right_inv j := by rcases j with ⟨j, hj⟩; cases j <;> rfl

/-- The literal paired coordinate basis of the smaller prefix module. -/
def pairedPrefixBasis (R : Type*) [CommRing R] (hi : i ≤ n) :
    Module.Basis (Fin i ⊕ Fin i) R (pairedPrefix n i → R) :=
  (Pi.basisFun R (pairedPrefix n i)).reindex (pairedPrefixEquiv hi).symm

theorem pairedPrefixBasis_apply (hi : i ≤ n) (j : Fin i ⊕ Fin i) :
    pairedPrefixBasis R hi j = Pi.basisFun R (pairedPrefix n i) (pairedPrefixEquiv hi j) := by
  simp only [pairedPrefixBasis, Module.Basis.reindex_apply, Equiv.symm_symm]

variable [LinearOrder (Fin n ⊕ Fin n)]
variable (b : Module.Basis (Fin n ⊕ Fin n) R V)

@[simp] theorem prefixInclusion_pairedBasis_inl (hi : i ≤ n) (j : Fin i) :
    prefixInclusion b (pairedPrefix n i) (pairedPrefixBasis R hi (.inl j)) =
      b (.inl (j.castLE hi)) := by
  rw [pairedPrefixBasis_apply, prefixInclusion_basis]
  rfl

@[simp] theorem prefixInclusion_pairedBasis_inr (hi : i ≤ n) (j : Fin i) :
    prefixInclusion b (pairedPrefix n i) (pairedPrefixBasis R hi (.inr j)) =
      b (.inr (j.castLE hi)) := by
  rw [pairedPrefixBasis_apply, prefixInclusion_basis]
  rfl

 theorem prefix_coord_inl (hi : i ≤ n) (j : Fin i) :
    (b.coord (.inl (j.castLE hi))).comp (prefixInclusion b (pairedPrefix n i)) =
      (pairedPrefixBasis R hi).coord (.inl j) := by
  apply (pairedPrefixBasis R hi).ext
  intro k
  cases k with
  | inl k =>
    simp [LinearMap.comp_apply, Module.Basis.coord_apply, Finsupp.single_apply,
      Fin.castLE_inj]
  | inr k => simp [LinearMap.comp_apply, Module.Basis.coord_apply, Finsupp.single_apply]

 theorem prefix_coord_inr (hi : i ≤ n) (j : Fin i) :
    (b.coord (.inr (j.castLE hi))).comp (prefixInclusion b (pairedPrefix n i)) =
      (pairedPrefixBasis R hi).coord (.inr j) := by
  apply (pairedPrefixBasis R hi).ext
  intro k
  cases k with
  | inl k => simp [LinearMap.comp_apply, Module.Basis.coord_apply, Finsupp.single_apply]
  | inr k =>
    simp [LinearMap.comp_apply, Module.Basis.coord_apply, Finsupp.single_apply,
      Fin.castLE_inj]

 theorem prefix_coord_inl_outside (hi : i ≤ n) (j : Fin n) (hj : i ≤ j.val) :
    (b.coord (.inl j)).comp (prefixInclusion b (pairedPrefix n i)) = 0 := by
  apply (pairedPrefixBasis R hi).ext
  intro k
  cases k with
  | inl k =>
    have hkj : k.castLE hi ≠ j := by intro h; have := congrArg Fin.val h; simp at this; omega
    simp [LinearMap.comp_apply, Module.Basis.coord_apply, Finsupp.single_apply, hkj, (Ne.symm hkj)]
  | inr k => simp [LinearMap.comp_apply, Module.Basis.coord_apply, Finsupp.single_apply]

 theorem prefix_thetaFunctional (hi : i ≤ n) (φ c : Fin n → R) (p : Polynomial R) :
    (thetaFunctional b φ c p).comp (prefixInclusion b (pairedPrefix n i)) =
      thetaFunctional (pairedPrefixBasis R hi) (φ ∘ Fin.castLE hi) (c ∘ Fin.castLE hi) p := by
  apply (pairedPrefixBasis R hi).ext
  intro k
  cases k with
  | inl k =>
    simp [LinearMap.comp_apply, thetaFunctional, Module.Basis.coord_apply,
      Finsupp.single_apply, Function.comp_apply]
  | inr k =>
    simp [LinearMap.comp_apply, thetaFunctional, Module.Basis.coord_apply,
      Finsupp.single_apply, Function.comp_apply]

 theorem prefix_xiFunctional (hi : i ≤ n) (φ β a : Fin n → R) (p : Polynomial R) :
    (xiFunctional b φ β a p).comp (prefixInclusion b (pairedPrefix n i)) =
      xiFunctional (pairedPrefixBasis R hi) (φ ∘ Fin.castLE hi)
        (β ∘ Fin.castLE hi) (a ∘ Fin.castLE hi) p := by
  apply (pairedPrefixBasis R hi).ext
  intro k
  cases k with
  | inl k =>
    simp [LinearMap.comp_apply, xiFunctional, Module.Basis.coord_apply,
      Finsupp.single_apply, Function.comp_apply]
  | inr k =>
    simp [LinearMap.comp_apply, xiFunctional, Module.Basis.coord_apply,
      Finsupp.single_apply, Function.comp_apply]

/-- The global-index mixed current becomes exactly the smaller prefix current:
outside coordinates vanish, and the surviving coordinates are reindexed bijectively. -/
theorem prefix_mixed_sum (hi : i ≤ n) (φ : Fin n → R) (p : Polynomial R)
    (w : ExteriorAlgebra R (pairedPrefix n i → R)) :
    (∑ j : Fin n, p.eval (φ j) •
      annihilation ((b.coord (.inr j)).comp (prefixInclusion b (pairedPrefix n i)))
        (annihilation ((b.coord (.inl j)).comp (prefixInclusion b (pairedPrefix n i))) w)) =
      mixedCurrent (pairedPrefixBasis R hi) (φ ∘ Fin.castLE hi) p w := by
  let f : Fin n → ExteriorAlgebra R (pairedPrefix n i → R) := fun j ↦
    p.eval (φ j) •
      annihilation ((b.coord (.inr j)).comp (prefixInclusion b (pairedPrefix n i)))
        (annihilation ((b.coord (.inl j)).comp (prefixInclusion b (pairedPrefix n i))) w)
  let S : Finset (Fin n) := Finset.univ.image (Fin.castLE hi)
  have hS : ∑ j ∈ S, f j = ∑ j : Fin n, f j := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j hj hjS
    have hji : i ≤ j.val := by
      by_contra h
      have hlt : j.val < i := by omega
      apply hjS
      refine Finset.mem_image.mpr ⟨⟨j.val, hlt⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext rfl
    simp only [f, prefix_coord_inl_outside b hi j hji, annihilation,
      map_zero, LinearMap.zero_apply, smul_zero]
  change (∑ j : Fin n, f j) = _
  rw [← hS, Finset.sum_image]
  · simp only [f, prefix_coord_inl, prefix_coord_inr, mixedCurrent,
      LinearMap.sum_apply, LinearMap.smul_apply, Function.comp_apply,
      pairLower, Module.End.mul_apply]
  · intro a ha c hc h
    exact Fin.castLE_injective hi h

/-- All polynomial odd and mixed equations hold in every actual smaller prefix
algebra after exact suffix extraction. -/
theorem IsHarmonic.restrict_prefix (hi : i ≤ n) (φ β a c : Fin n → R)
    (w : ExteriorAlgebra R V) (hw : IsHarmonic b φ β a c w)
    (hprefix : w ∈ prefixExteriorSpan b (pairedPrefix n i)) :
    IsHarmonic (pairedPrefixBasis R hi) (φ ∘ Fin.castLE hi)
      (β ∘ Fin.castLE hi) (a ∘ Fin.castLE hi) (c ∘ Fin.castLE hi)
      (ExteriorAlgebra.map (prefixRestriction b (pairedPrefix n i)) w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    have h := prefix_annihilation_zero b (pairedPrefix n i)
      (thetaFunctional b φ c p) hprefix (hw.1 p)
    rw [prefix_thetaFunctional b hi φ c p] at h
    exact h
  · intro p
    have h := prefix_annihilation_zero b (pairedPrefix n i)
      (xiFunctional b φ β a p) hprefix (hw.2.1 p)
    rw [prefix_xiFunctional b hi φ β a p] at h
    exact h
  · intro p
    have hcurrent : (∑ j : Fin n, p.eval (φ j) •
        Exterior.annihilation (b.coord (.inr j)) (Exterior.annihilation (b.coord (.inl j)) w)) = 0 := by
      simpa only [mixedCurrent, LinearMap.sum_apply, LinearMap.smul_apply, pairLower,
        Module.End.mul_apply] using hw.2.2 p
    have h := prefix_mixed_current_zero b (pairedPrefix n i)
      (fun j ↦ p.eval (φ j)) (fun j ↦ b.coord (.inr j)) (fun j ↦ b.coord (.inl j))
      hprefix hcurrent
    rwa [prefix_mixed_sum b hi φ p] at h

end PaperVerification.Fermion.Exterior

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators
open Colex

section Degree

variable {R V J : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [LinearOrder J] [Fintype J]
variable (b : Module.Basis J R V)

local notation "E" => ExteriorAlgebra R V

 theorem exterior_basis_mem (T : Finset J) : b.ExteriorAlgebra T ∈ ⋀[R]^T.card V := by
  have h := (b.exteriorPower T.card (⟨T, rfl⟩ : Set.powersetCard J T.card)).property
  simpa only [← ExteriorAlgebra.basis_eq_coe_basis] using h

/-- The coordinate of a homogeneous vector can occur only in its actual
exterior degree. This uses the graded decomposition, including in finite characteristic. -/
theorem exterior_coefficient_eq_zero_of_card_ne (T : Finset J) {k : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^k V) (hTk : T.card ≠ k) : b.ExteriorAlgebra.repr w T = 0 := by
  have hcoord : (b.ExteriorAlgebra.coord T).comp (exteriorDegreeProjection T.card) =
      b.ExteriorAlgebra.coord T := by
    apply b.ExteriorAlgebra.ext
    intro U
    simp only [LinearMap.comp_apply]
    by_cases hU : U.card = T.card
    · rw [exteriorDegreeProjection_self (hU ▸ exterior_basis_mem b U)]
    · rw [exteriorDegreeProjection_zero (exterior_basis_mem b U) hU, map_zero]
      have hUT : U ≠ T := fun h ↦ hU (congrArg Finset.card h)
      simp [Module.Basis.coord_apply, Finsupp.single_apply, hUT, (Ne.symm hUT)]
  have h := LinearMap.congr_fun hcoord w
  rw [LinearMap.comp_apply, exteriorDegreeProjection_zero hw (Ne.symm hTk), map_zero] at h
  exact h.symm

 theorem exterior_coefficient_card (T : Finset J) {k : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^k V) (hT : b.ExteriorAlgebra.repr w T ≠ 0) : T.card = k := by
  by_contra h
  exact hT (exterior_coefficient_eq_zero_of_card_ne b T hw h)

 theorem annihilation_mem_sub_one (l : Module.Dual R V) {k : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^k V) : annihilation l w ∈ ⋀[R]^(k - 1) V := by
  cases k with
  | zero =>
    rw [show annihilation l w = 0 from
      TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero l hw]
    exact zero_mem _
  | succ k => exact TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower l hw

 theorem contractList_mem_sub_length (l : List J) {k : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^k V) : contractList b l w ∈ ⋀[R]^(k - l.length) V := by
  induction l generalizing k w with
  | nil => simpa [contractList] using hw
  | cons i l ih =>
    change contractList b l (annihilation (b.coord i) w) ∈ _
    have h := ih (annihilation_mem_sub_one (b.coord i) hw)
    convert h using 1 <;> congr 1 <;> simp only [List.length_cons] <;> omega

end Degree

section PrefixBound

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

local instance FermionPairedPrefix_localInst_1 : LinearOrder (Fin n ⊕ Fin n) := interleavedOddOrder n
local instance FermionPairedPrefix_localInst_2 : PartialOrder (Fin n ⊕ Fin n) := (interleavedOddOrder n).toPartialOrder
local instance FermionPairedPrefix_localInst_3 : Preorder (Fin n ⊕ Fin n) := (interleavedOddOrder n).toPreorder
local instance FermionPairedPrefix_localInst_4 : LE (Fin n ⊕ Fin n) := (interleavedOddOrder n).toLE
local instance FermionPairedPrefix_localInst_5 : LT (Fin n ⊕ Fin n) := (interleavedOddOrder n).toLT
local instance FermionPairedPrefix_localInst_6 : DecidableEq (Fin n ⊕ Fin n) := (interleavedOddOrder n).toDecidableEq

variable (b : Module.Basis (Fin n ⊕ Fin n) R V)

/-- The complete primitive-height constraint on every prefix of a largest
nonzero homogeneous harmonic term. This is the exact nonnegative-height
condition used in Section 4.3, for every prefix and every allowed characteristic. -/
theorem largest_harmonic_term_prefix_card_le
    (φ β a c : Fin n → R) (hfac : IsUnit (n.factorial : R))
    (k : ℕ) (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^k V)
    (hw : IsHarmonic b φ β a c w)
    (T : Finset (Fin n ⊕ Fin n)) (hT : b.ExteriorAlgebra.repr w T ≠ 0)
    (hmax : ∀ U : Finset (Fin n ⊕ Fin n), b.ExteriorAlgebra.repr w U ≠ 0 →
      toColex U ≤ toColex T) (i : ℕ) (hi : i ≤ n) :
    (T ∩ pairedPrefix n i).card ≤ i := by
  let P := pairedPrefix n i
  let S := T \ P
  let v := contractList b S.toList w
  have hvprefix : v ∈ prefixExteriorSpan b P :=
    contract_suffix_mem_prefix b P T (pairedPrefix_isOrdered n i) w hmax
  have hvne : v ≠ 0 := by
    apply contractList_ne_zero_of_coefficient b S.toList S.nodup_toList T _ w hT
    simpa only [Finset.toList_toFinset] using (show T \ P ⊆ T from Finset.sdiff_subset)
  have hvharm : IsHarmonic b φ β a c v :=
    IsHarmonic.contractList b φ β a c S.toList w hw
  have hTcard : T.card = k := exterior_coefficient_card b T hwdegree hT
  have hvdegree : v ∈ ⋀[R]^((T ∩ P).card) V := by
    have h := contractList_mem_sub_length b S.toList hwdegree
    have hcard : k - S.toList.length = (T ∩ P).card := by
      have h' := Finset.card_sdiff_add_card_inter T P
      simp only [Finset.length_toList] at ⊢
      dsimp [S]
      omega
    simpa only [hcard] using h
  let x := ExteriorAlgebra.map (prefixRestriction b P) v
  have hxne : x ≠ 0 := exterior_prefixRestriction_ne_zero b P hvprefix hvne
  have hxdegree : x ∈ ⋀[R]^((T ∩ P).card) (P → R) :=
    exterior_prefixRestriction_mem b P hvdegree
  have hxharm := IsHarmonic.restrict_prefix b hi φ β a c v hvharm hvprefix
  have hlow : lowering (pairedPrefixBasis R hi) x = 0 := by
    simpa only [mixedCurrent, Polynomial.eval_one, one_smul, lowering] using hxharm.2.2 1
  by_contra h
  apply hxne
  apply primitive_degree_bound (pairedPrefixBasis R hi)
    (by simpa only [Fintype.card_fin] using unit_factorialCast_of_le hfac hi)
    (T ∩ P).card x hxdegree hlow
  simpa only [Fintype.card_fin] using Nat.lt_of_not_ge h

end PrefixBound

end PaperVerification.Fermion.Exterior
