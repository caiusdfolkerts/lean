module

public import PaperVerification.FermionHarmonicCompletion

/-!
# The actual largest harmonic coefficient is killed by the endpoint ideal

The path is read from the literal exterior word. Primitive bounds prove its
validity; diagonal and rank-one Gauss equations, including missing-colour
completion, give the actual endpoint ideal annihilator. All polynomial
identities used here were proved with a literal indeterminate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators
open Polynomial
open Colex
open Endpoint

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

local instance FermionHarmonicEndpoint_localInst_1 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m
local instance FermionHarmonicEndpoint_localInst_2 (m : ℕ) : PartialOrder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPartialOrder
local instance FermionHarmonicEndpoint_localInst_3 (m : ℕ) : Preorder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPreorder
local instance FermionHarmonicEndpoint_localInst_4 (m : ℕ) : LE (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLE
local instance FermionHarmonicEndpoint_localInst_5 (m : ℕ) : LT (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLT
local instance FermionHarmonicEndpoint_localInst_6 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) := (interleavedOddOrder m).toDecidableEq

/-- The actual nonnegative height of a word prefix. The primitive theorem
will prove that the subtraction has its intended integer meaning. -/
def wordHeight (T : Finset (Fin n ⊕ Fin n)) (i : ℕ) : ℕ :=
  i - (T ∩ pairedPrefix n i).card

@[simp] theorem wordHeight_zero (T : Finset (Fin n ⊕ Fin n)) : wordHeight T 0 = 0 :=
  Nat.zero_sub _

theorem pairedPrefix_succ (i : ℕ) (hi : i < n) :
    pairedPrefix n (i + 1) = insert (Sum.inl (⟨i, hi⟩ : Fin n))
      (insert (Sum.inr (⟨i, hi⟩ : Fin n)) (pairedPrefix n i)) := by
  ext a
  cases a with
  | inl a =>
    simp only [mem_pairedPrefix_inl, Finset.mem_insert, Sum.inl.injEq,
      Sum.inl_ne_inr, false_or, Fin.ext_iff]
    omega
  | inr a =>
    simp only [mem_pairedPrefix_inr, Finset.mem_insert, Sum.inr.injEq,
      Sum.inr_ne_inl, false_or, Fin.ext_iff]
    omega

theorem prefix_word_card_succ (T : Finset (Fin n ⊕ Fin n)) (i : ℕ) (hi : i < n) :
    (T ∩ pairedPrefix n (i + 1)).card = (T ∩ pairedPrefix n i).card +
      (if Sum.inl (⟨i, hi⟩ : Fin n) ∈ T then 1 else 0) +
      (if Sum.inr (⟨i, hi⟩ : Fin n) ∈ T then 1 else 0) := by
  rw [pairedPrefix_succ i hi]
  have hθP : Sum.inl (⟨i, hi⟩ : Fin n) ∉ T ∩ pairedPrefix n i := by
    simp only [Finset.mem_inter, mem_pairedPrefix_inl, lt_self_iff_false, and_false, not_false_eq_true]
  have hξP : Sum.inr (⟨i, hi⟩ : Fin n) ∉ T ∩ pairedPrefix n i := by
    simp only [Finset.mem_inter, mem_pairedPrefix_inr, lt_self_iff_false, and_false, not_false_eq_true]
  have hθinsert : Sum.inl (⟨i, hi⟩ : Fin n) ∉ insert (Sum.inr (⟨i, hi⟩ : Fin n))
      (T ∩ pairedPrefix n i) := by simp only [Finset.mem_insert, Sum.inl_ne_inr, false_or, hθP, not_false_eq_true]
  by_cases hθ : Sum.inl (⟨i, hi⟩ : Fin n) ∈ T
  · by_cases hξ : Sum.inr (⟨i, hi⟩ : Fin n) ∈ T
    · rw [Finset.inter_insert_of_mem hθ,Finset.inter_insert_of_mem hξ,
        Finset.card_insert_of_notMem hθinsert,Finset.card_insert_of_notMem hξP]
      simp only [if_pos hθ,if_pos hξ]
    · rw [Finset.inter_insert_of_mem hθ,Finset.inter_insert_of_notMem hξ,
        Finset.card_insert_of_notMem hθP]
      simp only [if_pos hθ,if_neg hξ,add_zero]
  · by_cases hξ : Sum.inr (⟨i, hi⟩ : Fin n) ∈ T
    · rw [Finset.inter_insert_of_notMem hθ,Finset.inter_insert_of_mem hξ,
        Finset.card_insert_of_notMem hξP]
      simp only [if_neg hθ,if_pos hξ,add_zero]
    · rw [Finset.inter_insert_of_notMem hθ,Finset.inter_insert_of_notMem hξ]
      simp only [if_neg hθ,if_neg hξ,add_zero]

/-- Once the actual prefix cardinality bound holds, the word's four marks
have exactly the up, flat, and down height updates used by the recursion. -/
theorem wordHeight_steps (T : Finset (Fin n ⊕ Fin n))
    (hbound : ∀ i ≤ n, (T ∩ pairedPrefix n i).card ≤ i)
    (i : ℕ) (hi : i < n) :
    HeightStep (wordMark T (⟨i, hi⟩ : Fin n)) (wordHeight T i) (wordHeight T (i + 1)) := by
  have hc := prefix_word_card_succ T i hi
  have hb := hbound i hi.le
  have hb' := hbound (i + 1) (by omega)
  by_cases hθ : Sum.inl (⟨i, hi⟩ : Fin n) ∈ T <;>
    by_cases hξ : Sum.inr (⟨i, hi⟩ : Fin n) ∈ T <;>
    simp only [wordMark, hθ, hξ, ite_true, ite_false, HeightStep, wordHeight] <;>
    simp only [hθ, hξ, ite_true, ite_false] at hc <;> omega

variable (b : Module.Basis (Fin n ⊕ Fin n) R V)

/-- The full literal endpoint-annihilation conclusion of Section 4.3.

The coefficient ring may have nilpotents and zero divisors. The ordinary
moment equations and node nilpotence are exactly what the homogeneous
ordinary quotient supplies, while all remaining equations follow from the
actual largest homogeneous harmonic term.
-/
theorem largest_harmonic_coefficient_endpoint_annihilates
    (φ β a c : Fin n → R) (N : ℕ) (hφ : ∀ j, φ j ^ N = 0)
    (hfac : IsUnit (n.factorial : R)) (hβ : ∀ j, IsUnit (β j))
    (hmom : ∀ r : ℕ, moment φ (fun j ↦ β j * a j * c j) r = 0)
    (k : ℕ) (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^k V)
    (hw : IsHarmonic b φ β a c w)
    (T : Finset (Fin n ⊕ Fin n)) (hT : b.ExteriorAlgebra.repr w T ≠ 0)
    (hmax : ∀ U, b.ExteriorAlgebra.repr w U ≠ 0 → toColex U ≤ toColex T) :
    ∀ p ∈ endpointIdeal (harmonicData φ β a c T) n (wordHeight T n),
      p * b.ExteriorAlgebra.repr w T = 0 := by
  have hbound : ∀ i ≤ n, (T ∩ pairedPrefix n i).card ≤ i :=
    largest_harmonic_term_prefix_card_le b φ β a c hfac k w hwdegree hw T hT hmax
  apply endpointIdeal_annihilates_of_occupation_cutoffs
    (harmonicData φ β a c T) N n (b.ExteriorAlgebra.repr w T) (wordHeight T) (wordHeight_zero T)
  · intro i hi
    simpa only [harmonicData, dataFromFin, dif_pos hi, harmonicDatum] using hφ ⟨i, hi⟩
  · intro i hi
    simpa only [harmonicData, dataFromFin, dif_pos hi, harmonicDatum] using
      wordHeight_steps T hbound i hi
  · intro i hi
    exact largest_coefficient_scalar_occupation_bound b φ β a c N hφ hfac
      k w hwdegree hw T hT hmax i hi
  · intro i hi
    exact largest_coefficient_rankOne_occupation_bound b φ β a c N hφ hfac
      k w hwdegree hw T hT hmax i hi
  · intro i hi d hd
    exact largest_coefficient_completion_occupation_bound b φ β a c N hφ hfac hβ
      k w hwdegree hw T hT hmax i hi d hd
  · simpa only [harmonicData, dataFromFin_fin, harmonicDatum, Datum.weight] using hmom

end PaperVerification.Fermion.Exterior
