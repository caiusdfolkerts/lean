module

public import PaperVerification.FermionPairedPrefix
public import PaperVerification.FermionPrefixCompletion
public import Mathlib.Data.Finset.Sort

/-!
# Exact coordinates after suffix extraction and prefix reindexing

The smaller exterior basis uses the same interleaved order as the global one.
The selected coefficient therefore changes only by the genuine unit sign of
the suffix contractions. Colex maximality is transported as well, which is
needed when the missing colour of a single mark is created.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators
open Colex

section OrderEmbedding

variable {R V W I J : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [LinearOrder I] [LinearOrder J]

theorem exterior_map_basis_orderEmbedding
    (b : Module.Basis I R V) (c : Module.Basis J R W)
    (e : I ↪o J) (f : V →ₗ[R] W) (hf : ∀ i, f (b i) = c (e i)) (T : Finset I) :
    ExteriorAlgebra.map f (b.ExteriorAlgebra T) =
      c.ExteriorAlgebra (T.map e.toEmbedding) := by
  have hs : (T.sort).map e = (T.map e.toEmbedding).sort :=
    Finset.map_sort e.toEmbedding T (· ≤ ·) (· ≤ ·)
      (fun a ha d hd ↦ e.le_iff_le.symm)
  rw [Module.Basis.exteriorAlgebra_eq_prod_map_sort,
    Module.Basis.exteriorAlgebra_eq_prod_map_sort, ← hs]
  simp only [map_list_prod, List.map_map, Function.comp_apply,
    ExteriorAlgebra.map_apply_ι, hf]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, ExteriorAlgebra.map_apply_ι, hf]

theorem exterior_map_coordinate_orderEmbedding
    (b : Module.Basis I R V) (c : Module.Basis J R W)
    (e : I ↪o J) (f : V →ₗ[R] W) (hf : ∀ i, f (b i) = c (e i))
    (T : Finset I) (w : ExteriorAlgebra R V) :
    c.ExteriorAlgebra.repr (ExteriorAlgebra.map f w) (T.map e.toEmbedding) =
      b.ExteriorAlgebra.repr w T := by
  have hh : (c.ExteriorAlgebra.coord (T.map e.toEmbedding)).comp
      (ExteriorAlgebra.map f).toLinearMap = b.ExteriorAlgebra.coord T := by
    apply b.ExteriorAlgebra.ext
    intro U
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      exterior_map_basis_orderEmbedding b c e f hf U, Module.Basis.coord_apply,
      Module.Basis.repr_self]
    by_cases hUT : U = T
    · subst U
      simp only [Finsupp.single_eq_same]
    · have hmap : U.map e.toEmbedding ≠ T.map e.toEmbedding :=
        fun h ↦ hUT ((Finset.map_injective e.toEmbedding) h)
      simp only [Finsupp.single_eq_of_ne (Ne.symm hUT), Finsupp.single_eq_of_ne (Ne.symm hmap)]
  exact LinearMap.congr_fun hh w

end OrderEmbedding

section ExactPrefix

variable {R V J : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [LinearOrder J] [Fintype J]
variable (b : Module.Basis J R V)

/-- Removing the fixed suffix also removes exactly that suffix from the
largest word. No new larger prefix coefficient can appear. -/
theorem contract_suffix_largest (P T : Finset J) (hP : IsOrderedPrefix P)
    (w : ExteriorAlgebra R V)
    (hmax : ∀ U : Finset J, b.ExteriorAlgebra.repr w U ≠ 0 → toColex U ≤ toColex T) :
    ∀ U : Finset J, b.ExteriorAlgebra.repr (contractList b (T \ P).toList w) U ≠ 0 →
      toColex U ≤ toColex (T ∩ P) := by
  intro U hU
  have hprefix := contract_suffix_mem_prefix b P T hP w hmax
  have hUP : U ⊆ P :=
    b.ExteriorAlgebra.repr_support_subset_of_mem_span {s : Finset J | s ⊆ P}
      hprefix (Finsupp.mem_support_iff.mpr hU)
  have hdisjoint : Disjoint U (T \ P) := by
    apply Finset.disjoint_left.mpr
    intro j hjU hjS
    exact (Finset.mem_sdiff.mp hjS).2 (hUP hjU)
  have hc := contractList_coefficient b (T \ P).toList (T \ P).nodup_toList U
    (by simpa only [Finset.toList_toFinset] using hdisjoint) w
  simp only [Finset.toList_toFinset] at hc
  have hsource : b.ExteriorAlgebra.repr w (U ∪ (T \ P)) ≠ 0 := by
    intro hz
    apply hU
    rw [hc, hz, smul_zero]
  have hle := hmax _ hsource
  have hh := (Finset.Colex.toColex_sdiff_le_toColex_sdiff
    (Finset.subset_union_right : T \ P ⊆ U ∪ (T \ P)) Finset.sdiff_subset).mpr hle
  simpa only [Finset.union_sdiff_cancel_right hdisjoint,
    Finset.sdiff_sdiff_self_left] using hh

end ExactPrefix

section PairedCoordinates

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n i : ℕ}

local instance FermionPrefixCoordinates_localInst_1 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m
local instance FermionPrefixCoordinates_localInst_2 (m : ℕ) : PartialOrder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPartialOrder
local instance FermionPrefixCoordinates_localInst_3 (m : ℕ) : Preorder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPreorder
local instance FermionPrefixCoordinates_localInst_4 (m : ℕ) : LE (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLE
local instance FermionPrefixCoordinates_localInst_5 (m : ℕ) : LT (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLT
local instance FermionPrefixCoordinates_localInst_6 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq

/-- The inclusion of paired prefixes preserves the actual interleaved order. -/
def pairedPrefixOrderEmbedding (hi : i ≤ n) : (Fin i ⊕ Fin i) ↪o (Fin n ⊕ Fin n) where
  toFun := Sum.map (Fin.castLE hi) (Fin.castLE hi)
  inj' := by
    intro a d h
    cases a <;> cases d <;> simp only [Sum.map_inl, Sum.map_inr, Sum.inl.injEq,
      Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at h
    · exact congrArg Sum.inl (Fin.castLE_injective hi h)
    · exact congrArg Sum.inr (Fin.castLE_injective hi h)
  map_rel_iff' := by
    intro a d
    cases a <;> cases d <;> rfl

def prefixWord (hi : i ≤ n) (T : Finset (Fin n ⊕ Fin n)) : Finset (Fin i ⊕ Fin i) :=
  Finset.univ.filter fun j ↦ pairedPrefixOrderEmbedding hi j ∈ T

@[simp] theorem mem_prefixWord (hi : i ≤ n) (T : Finset (Fin n ⊕ Fin n))
    (j : Fin i ⊕ Fin i) : j ∈ prefixWord hi T ↔ pairedPrefixOrderEmbedding hi j ∈ T := by
  simp only [prefixWord, Finset.mem_filter, Finset.mem_univ, true_and]

theorem map_prefixWord (hi : i ≤ n) (T : Finset (Fin n ⊕ Fin n)) :
    (prefixWord hi T).map (pairedPrefixOrderEmbedding hi).toEmbedding = T ∩ pairedPrefix n i := by
  ext a
  constructor
  · intro ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ha
    refine Finset.mem_inter.mpr ⟨(mem_prefixWord hi T j).mp hj, ?_⟩
    cases j with
    | inl j => exact (mem_pairedPrefix_inl _).mpr j.isLt
    | inr j => exact (mem_pairedPrefix_inr _).mpr j.isLt
  · intro ha
    obtain ⟨haT, haP⟩ := Finset.mem_inter.mp ha
    cases a with
    | inl a =>
      let j : Fin i := ⟨a.val, (mem_pairedPrefix_inl a).mp haP⟩
      have he : pairedPrefixOrderEmbedding hi (.inl j) = .inl a := by
        exact congrArg Sum.inl (Fin.ext rfl)
      exact Finset.mem_map.mpr ⟨.inl j, (mem_prefixWord hi T _).mpr (by simpa only [he] using haT), he⟩
    | inr a =>
      let j : Fin i := ⟨a.val, (mem_pairedPrefix_inr a).mp haP⟩
      have he : pairedPrefixOrderEmbedding hi (.inr j) = .inr a := by
        exact congrArg Sum.inr (Fin.ext rfl)
      exact Finset.mem_map.mpr ⟨.inr j, (mem_prefixWord hi T _).mpr (by simpa only [he] using haT), he⟩

theorem card_prefixWord (hi : i ≤ n) (T : Finset (Fin n ⊕ Fin n)) :
    (prefixWord hi T).card = (T ∩ pairedPrefix n i).card := by
  rw [← map_prefixWord hi T, Finset.card_map]

variable (b : Module.Basis (Fin n ⊕ Fin n) R V)

theorem prefixInclusion_orderEmbedding (hi : i ≤ n) (j : Fin i ⊕ Fin i) :
    prefixInclusion b (pairedPrefix n i) (pairedPrefixBasis R hi j) =
      b (pairedPrefixOrderEmbedding hi j) := by
  cases j with
  | inl j => exact prefixInclusion_pairedBasis_inl b hi j
  | inr j => exact prefixInclusion_pairedBasis_inr b hi j

/-- Exact suffix contraction followed by the split prefix restriction. -/
def extractedPrefix (hi : i ≤ n) (T : Finset (Fin n ⊕ Fin n))
    (w : ExteriorAlgebra R V) : ExteriorAlgebra R (pairedPrefix n i → R) :=
  ExteriorAlgebra.map (prefixRestriction b (pairedPrefix n i))
    (contractList b (T \ pairedPrefix n i).toList w)

theorem extractedPrefix_coefficient (hi : i ≤ n) (T : Finset (Fin n ⊕ Fin n))
    (w : ExteriorAlgebra R V)
    (hmax : ∀ U : Finset (Fin n ⊕ Fin n), b.ExteriorAlgebra.repr w U ≠ 0 →
      toColex U ≤ toColex T) :
    (pairedPrefixBasis R hi).ExteriorAlgebra.repr (extractedPrefix b hi T w) (prefixWord hi T) =
      contractionSign (T \ pairedPrefix n i).toList T • b.ExteriorAlgebra.repr w T := by
  have hcoord := exterior_map_coordinate_orderEmbedding (pairedPrefixBasis R hi) b
    (pairedPrefixOrderEmbedding hi) (prefixInclusion b (pairedPrefix n i))
    (prefixInclusion_orderEmbedding b hi) (prefixWord hi T) (extractedPrefix b hi T w)
  have hprefix := contract_suffix_mem_prefix b (pairedPrefix n i) T
    (pairedPrefix_isOrdered n i) w hmax
  rw [map_prefixWord, extractedPrefix, exterior_prefixInclusion_restriction b _ hprefix] at hcoord
  rw [extractedPrefix, ← hcoord]
  have hdisj : Disjoint (T ∩ pairedPrefix n i) (T \ pairedPrefix n i) := by
    apply Finset.disjoint_left.mpr
    intro j hj1 hj2
    exact (Finset.mem_sdiff.mp hj2).2 (Finset.mem_inter.mp hj1).2
  have hc := contractList_coefficient b (T \ pairedPrefix n i).toList
    (T \ pairedPrefix n i).nodup_toList (T ∩ pairedPrefix n i)
    (by simpa only [Finset.toList_toFinset] using hdisj) w
  have hcover : T ∩ pairedPrefix n i ∪ (T \ pairedPrefix n i) = T := by
    ext j
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  simpa only [Finset.toList_toFinset, hcover] using hc

theorem extractedPrefix_largest (hi : i ≤ n) (T : Finset (Fin n ⊕ Fin n))
    (w : ExteriorAlgebra R V)
    (hmax : ∀ U : Finset (Fin n ⊕ Fin n), b.ExteriorAlgebra.repr w U ≠ 0 →
      toColex U ≤ toColex T) :
    ∀ U : Finset (Fin i ⊕ Fin i),
      (pairedPrefixBasis R hi).ExteriorAlgebra.repr (extractedPrefix b hi T w) U ≠ 0 →
        toColex U ≤ toColex (prefixWord hi T) := by
  intro U hU
  have hcoord := exterior_map_coordinate_orderEmbedding (pairedPrefixBasis R hi) b
    (pairedPrefixOrderEmbedding hi) (prefixInclusion b (pairedPrefix n i))
    (prefixInclusion_orderEmbedding b hi) U (extractedPrefix b hi T w)
  have hprefix := contract_suffix_mem_prefix b (pairedPrefix n i) T
    (pairedPrefix_isOrdered n i) w hmax
  rw [extractedPrefix, exterior_prefixInclusion_restriction b _ hprefix] at hcoord
  have hne : b.ExteriorAlgebra.repr (contractList b (T \ pairedPrefix n i).toList w)
      (U.map (pairedPrefixOrderEmbedding hi).toEmbedding) ≠ 0 := by rwa [hcoord]
  have hh := contract_suffix_largest b (pairedPrefix n i) T
    (pairedPrefix_isOrdered n i) w hmax _ hne
  rw [← map_prefixWord hi T] at hh
  have hh' : toColex (U.image (pairedPrefixOrderEmbedding hi)) ≤
      toColex ((prefixWord hi T).image (pairedPrefixOrderEmbedding hi)) := by
    have he : ((pairedPrefixOrderEmbedding hi).toEmbedding :
        (Fin i ⊕ Fin i) → (Fin n ⊕ Fin n)) =
        (pairedPrefixOrderEmbedding hi : (Fin i ⊕ Fin i) → (Fin n ⊕ Fin n)) := rfl
    simpa only [Finset.map_eq_image, he] using hh
  exact (Finset.Colex.toColex_image_le_toColex_image
    (pairedPrefixOrderEmbedding hi).strictMono).mp hh'

theorem extractedPrefix_harmonic (hi : i ≤ n) (T : Finset (Fin n ⊕ Fin n))
    (φ β a c : Fin n → R) (w : ExteriorAlgebra R V)
    (hw : IsHarmonic b φ β a c w)
    (hmax : ∀ U : Finset (Fin n ⊕ Fin n), b.ExteriorAlgebra.repr w U ≠ 0 →
      toColex U ≤ toColex T) :
    IsHarmonic (pairedPrefixBasis R hi) (φ ∘ Fin.castLE hi) (β ∘ Fin.castLE hi)
      (a ∘ Fin.castLE hi) (c ∘ Fin.castLE hi) (extractedPrefix b hi T w) := by
  exact IsHarmonic.restrict_prefix b hi φ β a c _
    (IsHarmonic.contractList b φ β a c _ w hw)
    (contract_suffix_mem_prefix b _ T (pairedPrefix_isOrdered n i) w hmax)

theorem extractedPrefix_degree (hi : i ≤ n) (T : Finset (Fin n ⊕ Fin n))
    (k : ℕ) (w : ExteriorAlgebra R V) (hw : w ∈ ⋀[R]^k V)
    (hT : b.ExteriorAlgebra.repr w T ≠ 0) :
    extractedPrefix b hi T w ∈ ⋀[R]^(prefixWord hi T).card (pairedPrefix n i → R) := by
  have hTcard : T.card = k := exterior_coefficient_card b T hw hT
  have h := contractList_mem_sub_length b (T \ pairedPrefix n i).toList hw
  have hcard : k - (T \ pairedPrefix n i).toList.length = (prefixWord hi T).card := by
    rw [Finset.length_toList, card_prefixWord]
    have hh := Finset.card_sdiff_add_card_inter T (pairedPrefix n i)
    omega
  apply exterior_prefixRestriction_mem b (pairedPrefix n i)
  simpa only [hcard] using h

end PairedCoordinates

end PaperVerification.Fermion.Exterior
