module

public import PaperVerification.FermionCreators
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Fintype.Fin

/-!
# Exact suffix extraction from a largest exterior term

An iterated coordinate contraction extracts a prescribed suffix. If the suffix
comes from the largest nonzero exterior term in colex order, no extra suffix
variable survives: such a source would be larger. The extraction below acts on
the genuine exterior algebra, retaining its contraction signs.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators
open Colex

variable {R V J : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [LinearOrder J] [Fintype J]

local notation "E" => ExteriorAlgebra R V

variable (b : Module.Basis J R V)

/-- Contract the listed coordinates in their listed order. -/
def contractList : List J → Module.End R E
  | [] => 1
  | i :: l => contractList l * annihilation (b.coord i)

/-- The exact unit sign accumulated by ordered coordinate deletions. -/
def contractionSign : List J → Finset J → ℤˣ
  | [], _ => 1
  | i :: l, s => TauCeti.ExteriorAlgebra.basisEraseSign i s * contractionSign l (s.erase i)

/-- An actual iterated contraction deletes exactly the listed coordinates,
with a unit sign, and vanishes if any required coordinate is absent. -/
theorem contractList_basis (l : List J) (hl : l.Nodup) (s : Finset J) :
    contractList b l (b.ExteriorAlgebra s) =
      if l.toFinset ⊆ s then contractionSign l s • b.ExteriorAlgebra (s \ l.toFinset) else 0 := by
  induction l generalizing s with
  | nil => simp [contractList, contractionSign]
  | cons i l ih =>
    have hnodup := List.nodup_cons.mp hl
    change contractList b l
      (annihilation (b.coord i) (b.ExteriorAlgebra s)) = _
    rw [show annihilation (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then TauCeti.ExteriorAlgebra.basisEraseSign i s • b.ExteriorAlgebra (s.erase i) else 0
      from TauCeti.ExteriorAlgebra.contractLeft_coord_basis b i s]
    by_cases hi : i ∈ s
    · rw [if_pos hi, map_zsmul_unit, ih hnodup.2]
      have hsub : (i :: l).toFinset ⊆ s ↔ l.toFinset ⊆ s.erase i := by
        constructor
        · intro h j hj
          refine Finset.mem_erase.mpr ⟨?_, h ?_⟩
          · intro hji
            apply hnodup.1
            exact hji ▸ List.mem_toFinset.mp hj
          · simpa only [List.toFinset_cons, Finset.mem_insert] using Or.inr hj
        · intro h j hj
          simp only [List.toFinset_cons, Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact hi
          · exact (Finset.mem_erase.mp (h hj)).2
      have hset : s.erase i \ l.toFinset = s \ (i :: l).toFinset := by
        ext j
        simp only [Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons,
          Finset.mem_insert, not_or]
        constructor
        · rintro ⟨⟨hji, hjs⟩, hjl⟩
          exact ⟨hjs, hji, hjl⟩
        · rintro ⟨hjs, hji, hjl⟩
          exact ⟨⟨hji, hjs⟩, hjl⟩
      simp only [hsub]
      split_ifs with h
      · rw [contractionSign, hset, mul_smul]
      · rw [smul_zero]
    · rw [if_neg hi, map_zero, if_neg]
      intro h
      exact hi (h (by simp))

/-- No two distinct source words containing the fixed suffix can contribute to
the same residual word. This is the exact coefficient formula, with its unit sign. -/
theorem contractList_coefficient (l : List J) (hl : l.Nodup)
    (T : Finset J) (hdisjoint : Disjoint T l.toFinset) (w : E) :
    b.ExteriorAlgebra.repr (contractList b l w) T =
      contractionSign l (T ∪ l.toFinset) • b.ExteriorAlgebra.repr w (T ∪ l.toFinset) := by
  have hmap : (b.ExteriorAlgebra.coord T).comp (contractList b l) =
      contractionSign l (T ∪ l.toFinset) • b.ExteriorAlgebra.coord (T ∪ l.toFinset) := by
    apply b.ExteriorAlgebra.ext
    intro U
    simp only [LinearMap.comp_apply, contractList_basis b l hl]
    by_cases hsub : l.toFinset ⊆ U
    · rw [if_pos hsub]
      by_cases heq : U \ l.toFinset = T
      · have hU : U = T ∪ l.toFinset := by
          rw [← heq, Finset.sdiff_union_of_subset hsub]
        subst U
        simp only [Finset.union_sdiff_cancel_right hdisjoint, map_zsmul_unit,
          Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
          LinearMap.smul_apply]
      · have hU : U ≠ T ∪ l.toFinset := by
          intro h
          apply heq
          rw [h, Finset.union_sdiff_cancel_right hdisjoint]
        simp only [map_zsmul_unit, Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_eq_of_ne heq, Finsupp.single_eq_of_ne (Ne.symm heq),
          Finsupp.single_eq_of_ne hU, Finsupp.single_eq_of_ne (Ne.symm hU),
          LinearMap.smul_apply, smul_zero]
    · rw [if_neg hsub, map_zero]
      have hU : U ≠ T ∪ l.toFinset := by
        intro h
        apply hsub
        rw [h]
        exact Finset.subset_union_right
      simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_of_ne hU, Finsupp.single_eq_of_ne (Ne.symm hU), smul_zero]
  exact LinearMap.congr_fun hmap w

/-- A selected nonzero coefficient survives exact suffix extraction, so the
extracted prefix vector is nonzero. -/
theorem contractList_ne_zero_of_coefficient (l : List J) (hl : l.Nodup)
    (T : Finset J) (hsub : l.toFinset ⊆ T) (w : E)
    (hT : b.ExteriorAlgebra.repr w T ≠ 0) : contractList b l w ≠ 0 := by
  intro hz
  have h := contractList_coefficient b l hl (T \ l.toFinset)
    Finset.sdiff_disjoint w
  rw [Finset.sdiff_union_of_subset hsub, hz, map_zero, Finsupp.zero_apply] at h
  have h' := congrArg (fun r : R ↦ (contractionSign l T)⁻¹ • r) h
  have hc : b.ExteriorAlgebra.repr w T = 0 := by
    simpa only [smul_zero, smul_smul, inv_mul_cancel, one_smul] using h'.symm
  exact hT hc

/-- The actual submodule spanned by exterior words entirely inside a prefix. -/
def prefixExteriorSpan (P : Finset J) : Submodule R E :=
  Submodule.span R (b.ExteriorAlgebra '' {s : Finset J | s ⊆ P})

/-- A prefix is lower than its complement in the chosen exterior order. -/
def IsOrderedPrefix (P : Finset J) : Prop :=
  ∀ i ∈ P, ∀ j ∉ P, i < j

/-- Colex maximality gives the exact no-extra-suffix implication, for every
ordered prefix and every source containing the selected suffix. -/
theorem suffix_source_subset_prefix (P T U : Finset J) (hP : IsOrderedPrefix P)
    (hUT : toColex U ≤ toColex T) (hSU : T \ P ⊆ U) : U \ (T \ P) ⊆ P := by
  intro a ha
  by_contra haP
  have haU := (Finset.mem_sdiff.mp ha).1
  have haT : a ∉ T := by
    intro haT
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mpr ⟨haT, haP⟩)
  obtain ⟨c, hcT, hcU, hac⟩ :=
    (Finset.Colex.toColex_le_toColex.mp hUT) haU haT
  have hcP : c ∈ P := by
    by_contra hcP
    exact hcU (hSU (Finset.mem_sdiff.mpr ⟨hcT, hcP⟩))
  exact (not_lt_of_ge hac) (hP c hcP a haP)

/-- Every nonzero exterior element has a genuinely largest nonzero basis term. -/
theorem exists_largest_exterior_term (w : E) (hw : w ≠ 0) :
    ∃ T : Finset J, b.ExteriorAlgebra.repr w T ≠ 0 ∧
      ∀ U : Finset J, b.ExteriorAlgebra.repr w U ≠ 0 → toColex U ≤ toColex T := by
  have hrepr : b.ExteriorAlgebra.repr w ≠ 0 := by
    intro h
    apply hw
    apply b.ExteriorAlgebra.repr.injective
    simpa only [map_zero] using h
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image
    (b.ExteriorAlgebra.repr w).support toColex (Finsupp.support_nonempty_iff.mpr hrepr)
  refine ⟨T, Finsupp.mem_support_iff.mp hT, ?_⟩
  intro U hU
  exact hmax U (Finsupp.mem_support_iff.mpr hU)

/-- Exact suffix extraction has no remaining exterior variable outside the
prefix. All source coefficients that could violate this are excluded by the
literal colex maximality hypothesis. -/
theorem contract_suffix_mem_prefix (P T : Finset J) (hP : IsOrderedPrefix P)
    (w : E)
    (hmax : ∀ U : Finset J, b.ExteriorAlgebra.repr w U ≠ 0 → toColex U ≤ toColex T) :
    contractList b (T \ P).toList w ∈ prefixExteriorSpan b P := by
  rw [← b.ExteriorAlgebra.sum_repr w, map_sum]
  apply Submodule.sum_mem
  intro U hU
  rw [map_smul]
  by_cases hc : b.ExteriorAlgebra.repr w U = 0
  · rw [hc, zero_smul]
    exact zero_mem _
  rw [contractList_basis b _ (T \ P).nodup_toList, Finset.toList_toFinset]
  by_cases hsub : T \ P ⊆ U
  · rw [if_pos hsub]
    apply Submodule.smul_mem
    have hword : b.ExteriorAlgebra (U \ (T \ P)) ∈ prefixExteriorSpan b P := by
      apply Submodule.subset_span
      exact ⟨U \ (T \ P), suffix_source_subset_prefix P T U hP (hmax U hc) hsub, rfl⟩
    exact (prefixExteriorSpan b P).toAddSubgroup.zsmul_mem hword _
  · rw [if_neg hsub, smul_zero]
    exact zero_mem _

end PaperVerification.Fermion.Exterior

namespace PaperVerification.Fermion.Exterior

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    [LinearOrder (Fin n ⊕ Fin n)]
variable (b : Module.Basis (Fin n ⊕ Fin n) R V)
variable (φ β a c : Fin n → R)

/-- Every ordered suffix contraction remains in the actual harmonic space. -/
theorem IsHarmonic.contractList (l : List (Fin n ⊕ Fin n))
    (w : ExteriorAlgebra R V) (hw : IsHarmonic b φ β a c w) :
    IsHarmonic b φ β a c (Exterior.contractList b l w) := by
  induction l generalizing w with
  | nil => simpa [Exterior.contractList] using hw
  | cons i l ih =>
    change IsHarmonic b φ β a c
      (Exterior.contractList b l (Exterior.annihilation (b.coord i) w))
    exact ih _ (IsHarmonic.annihilation b φ β a c hw (b.coord i))

end PaperVerification.Fermion.Exterior

namespace PaperVerification.Fermion.Exterior

/-- The numerical order of the paper's interleaved bits: theta is compared
before xi at a fixed index, and later indices are compared before earlier ones. -/
def interleavedOddRank {n : ℕ} : Fin n ⊕ Fin n → ℕ
  | .inl i => 2 * i.val + 1
  | .inr i => 2 * i.val

 theorem interleavedOddRank_injective (n : ℕ) :
    Function.Injective (@interleavedOddRank n) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hij : i.val = j.val := by simp only [interleavedOddRank] at h; omega
      exact congrArg Sum.inl (Fin.ext hij)
    | inr j => simp only [interleavedOddRank] at h; omega
  | inr i =>
    cases j with
    | inl j => simp only [interleavedOddRank] at h; omega
    | inr j =>
      have hij : i.val = j.val := by simp only [interleavedOddRank] at h; omega
      exact congrArg Sum.inr (Fin.ext hij)

/-- The actual linear order used for exact-suffix leading terms. -/
def interleavedOddOrder (n : ℕ) : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' interleavedOddRank (interleavedOddRank_injective n)

/-- The first `i` pairs, viewed as a finite set of actual odd coordinates. -/
def pairedPrefix (n i : ℕ) : Finset (Fin n ⊕ Fin n) :=
  (Finset.univ.filter (fun j : Fin n ↦ j.val < i)).disjSum
    (Finset.univ.filter (fun j : Fin n ↦ j.val < i))

@[simp] theorem mem_pairedPrefix_inl {n i : ℕ} (j : Fin n) :
    Sum.inl j ∈ pairedPrefix n i ↔ j.val < i := by simp [pairedPrefix]

@[simp] theorem mem_pairedPrefix_inr {n i : ℕ} (j : Fin n) :
    Sum.inr j ∈ pairedPrefix n i ↔ j.val < i := by simp [pairedPrefix]

 theorem card_pairedPrefix (n i : ℕ) (hi : i ≤ n) :
    (pairedPrefix n i).card = 2 * i := by
  simp only [pairedPrefix, Finset.card_disjSum, Fin.card_filter_val_lt, min_eq_right hi]
  omega

section Interleaved

local instance FermionPrefix_localInst_1 (n : ℕ) : LinearOrder (Fin n ⊕ Fin n) := interleavedOddOrder n
local instance FermionPrefix_localInst_2 (n : ℕ) : PartialOrder (Fin n ⊕ Fin n) := (interleavedOddOrder n).toPartialOrder
local instance FermionPrefix_localInst_3 (n : ℕ) : Preorder (Fin n ⊕ Fin n) := (interleavedOddOrder n).toPreorder
local instance FermionPrefix_localInst_4 (n : ℕ) : LE (Fin n ⊕ Fin n) := (interleavedOddOrder n).toLE
local instance FermionPrefix_localInst_5 (n : ℕ) : LT (Fin n ⊕ Fin n) := (interleavedOddOrder n).toLT

/-- Every paired prefix is an ordered prefix in the exact interleaved order.
No property of the ordinary `Sum` order is used. -/
theorem pairedPrefix_isOrdered (n i : ℕ) : IsOrderedPrefix (pairedPrefix n i) := by
  intro a ha b hb
  cases a with
  | inl a =>
    have ha' := (mem_pairedPrefix_inl a).mp ha
    cases b with
    | inl b =>
      have hb' : ¬ b.val < i := by simpa only [mem_pairedPrefix_inl] using hb
      change 2 * a.val + 1 < 2 * b.val + 1
      omega
    | inr b =>
      have hb' : ¬ b.val < i := by simpa only [mem_pairedPrefix_inr] using hb
      change 2 * a.val + 1 < 2 * b.val
      omega
  | inr a =>
    have ha' := (mem_pairedPrefix_inr a).mp ha
    cases b with
    | inl b =>
      have hb' : ¬ b.val < i := by simpa only [mem_pairedPrefix_inl] using hb
      change 2 * a.val < 2 * b.val + 1
      omega
    | inr b =>
      have hb' : ¬ b.val < i := by simpa only [mem_pairedPrefix_inr] using hb
      change 2 * a.val < 2 * b.val
      omega

end Interleaved

end PaperVerification.Fermion.Exterior
