module

public import Recovery.Unimodular.FlagKoszul.TorCriterion
public import Mathlib.Logic.Equiv.List

/-!
# Renaming positive basis indices in the genuine reduced bar complex

The basis, multiplication coefficients, adjacent-product differential and
homogeneous pieces are transported along an arbitrary equivalence. The index
universes are independent. This permits honest universe lifts of finite
geometric index types without changing the algebra or its grading.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace Unimodular.FlagKoszul.BarReindex

open PaperVerification.AugmentedAlgebraBasis PaperVerification.ReducedBarBasis

variable {K A I J : Type*} [CommRing K] [Ring A] [Algebra K A]

abbrev basis (e : I ≃ J) (B : Module.Basis (Option I) K A) :
    Module.Basis (Option J) K A := B.reindex (Equiv.optionCongr e)

def coefficientEquiv (e : I ≃ J) : (I →₀ K) ≃ₗ[K] (J →₀ K) := Finsupp.domLCongr e

def wordEquiv (e : I ≃ J) : (List I →₀ K) ≃ₗ[K] (List J →₀ K) :=
  Finsupp.domLCongr (Equiv.listEquivOfEquiv e)

@[simp] theorem coefficientEquiv_apply (e : I ≃ J) (z : I →₀ K) (j : J) :
    coefficientEquiv e z j = z (e.symm j) := rfl

@[simp] theorem wordEquiv_apply (e : I ≃ J) (z : List I →₀ K) (L : List J) :
    wordEquiv e z L = z (L.map e.symm) := rfl

@[simp] theorem coefficientEquiv_single (e : I ≃ J) (i : I) (c : K) :
    coefficientEquiv e (Finsupp.single i c) = Finsupp.single (e i) c :=
  Finsupp.domLCongr_single e i c

@[simp] theorem wordEquiv_single (e : I ≃ J) (L : List I) (c : K) :
    wordEquiv e (Finsupp.single L c) = Finsupp.single (L.map e) c :=
  Finsupp.domLCongr_single (Equiv.listEquivOfEquiv e) L c

@[simp] theorem basis_none (e : I ≃ J) (B : Module.Basis (Option I) K A) :
    basis e B none = B none := by simp [basis, Module.Basis.reindex_apply, Equiv.optionCongr]

@[simp] theorem basis_some (e : I ≃ J) (B : Module.Basis (Option I) K A) (j : J) :
    basis e B (some j) = B (some (e.symm j)) := by
  simp [basis, Module.Basis.reindex_apply, Equiv.optionCongr]

theorem productCoefficients_transport (e : I ≃ J) (B : Module.Basis (Option I) K A)
    (i j : I) : coefficientEquiv e (productCoefficients B i j) =
      productCoefficients (basis e B) (e i) (e j) := by
  ext k
  simp [productCoefficients, positiveCoordinates_apply, positiveVector, basis,
    Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, Equiv.optionCongr]

theorem prepend_transport (e : I ≃ J) (i : I) (z : List I →₀ K) :
    wordEquiv e (prepend i z) = prepend (e i) (wordEquiv e z) := by
  have h : (wordEquiv e (K := K)).toLinearMap.comp (prepend i) =
      (prepend (e i)).comp (wordEquiv e).toLinearMap := by
    apply Finsupp.lhom_ext
    intro L c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, prefix_single,
      wordEquiv_single, List.map_cons]
  exact LinearMap.congr_fun h z

theorem appendTail_transport (e : I ≃ J) (L : List I) (z : I →₀ K) :
    wordEquiv e (appendTail L z) = appendTail (L.map e) (coefficientEquiv e z) := by
  have h : (wordEquiv e (K := K)).toLinearMap.comp (appendTail L) =
      (appendTail (L.map e)).comp (coefficientEquiv e).toLinearMap := by
    apply Finsupp.lhom_ext
    intro i c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, appendTail_single,
      wordEquiv_single, coefficientEquiv_single, List.map_cons]
  exact LinearMap.congr_fun h z

theorem mergeBasis_transport (e : I ≃ J) (B : Module.Basis (Option I) K A)
    (i : I) (L : List I) :
    wordEquiv e (mergeBasis B i L) = mergeBasis (basis e B) (e i) (L.map e) := by
  cases L with
  | nil => simp only [mergeBasis, map_zero, List.map_nil]
  | cons j L =>
    simp only [mergeBasis, List.map_cons, appendTail_transport, productCoefficients_transport]

theorem merge_transport (e : I ≃ J) (B : Module.Basis (Option I) K A)
    (i : I) (z : List I →₀ K) :
    wordEquiv e (merge B i z) = merge (basis e B) (e i) (wordEquiv e z) := by
  have h : (wordEquiv e (K := K)).toLinearMap.comp (merge B i) =
      (merge (basis e B) (e i)).comp (wordEquiv e).toLinearMap := by
    apply Finsupp.lhom_ext
    intro L c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, merge_single, map_smul,
      wordEquiv_single, mergeBasis_transport]
  exact LinearMap.congr_fun h z

theorem differentialBasis_transport (e : I ≃ J) (B : Module.Basis (Option I) K A)
    (L : List I) : wordEquiv e (differentialBasis B L) =
      differentialBasis (basis e B) (L.map e) := by
  induction L with
  | nil => simp only [differentialBasis, map_zero, List.map_nil]
  | cons i L ih =>
    simp only [differentialBasis, map_sub, merge_transport, prepend_transport,
      wordEquiv_single, ih, List.map_cons]

/-- The literal adjacent-product differential commutes with renaming, with
no augmentation, exactness or vanishing assumption. -/
theorem differential_transport (e : I ≃ J) (B : Module.Basis (Option I) K A)
    (z : List I →₀ K) : wordEquiv e (differential B z) =
      differential (basis e B) (wordEquiv e z) := by
  have h : (wordEquiv e (K := K)).toLinearMap.comp (differential B) =
      (differential (basis e B)).comp (wordEquiv e).toLinearMap := by
    apply Finsupp.lhom_ext
    intro L c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, differential_single,
      map_smul, wordEquiv_single, differentialBasis_transport]
  exact LinearMap.congr_fun h z

def homogeneousPiece (δ : I → ℕ) (r N : ℕ) : Submodule K (List I →₀ K) :=
  Finsupp.supported K K {L | L.length = r ∧ PaperVerification.WeightedBar.totalDegree δ L = N}

theorem totalDegree_transport (e : I ≃ J) (δ : I → ℕ) (L : List I) :
    PaperVerification.WeightedBar.totalDegree (δ ∘ e.symm) (L.map e) =
      PaperVerification.WeightedBar.totalDegree δ L := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [List.map_cons, PaperVerification.WeightedBar.totalDegree_cons,
      Function.comp_apply, Equiv.symm_apply_apply, ih]

/-- Internal degree and homological word length are both retained exactly. -/
theorem homogeneousPiece_transport (e : I ≃ J) (δ : I → ℕ) (r N : ℕ)
    (z : List I →₀ K) :
    wordEquiv e z ∈ homogeneousPiece (δ ∘ e.symm) r N ↔
      z ∈ homogeneousPiece δ r N := by
  constructor
  · intro h L hL
    change L.length = r ∧ PaperVerification.WeightedBar.totalDegree δ L = N
    have hn : wordEquiv e z (L.map e) ≠ 0 := by
      simpa only [wordEquiv_apply, List.map_map, Equiv.symm_comp_self, List.map_id] using
        Finsupp.mem_support_iff.mp hL
    have hh := h (Finsupp.mem_support_iff.mpr hn)
    change (L.map e).length = r ∧
      PaperVerification.WeightedBar.totalDegree (δ ∘ e.symm) (L.map e) = N at hh
    simpa only [List.length_map, totalDegree_transport] using hh
  · intro h L hL
    change L.length = r ∧ PaperVerification.WeightedBar.totalDegree (δ ∘ e.symm) L = N
    have hn : wordEquiv e z L ≠ 0 := Finsupp.mem_support_iff.mp hL
    rw [wordEquiv_apply] at hn
    have hh := h (Finsupp.mem_support_iff.mpr hn)
    change (L.map e.symm).length = r ∧
      PaperVerification.WeightedBar.totalDegree δ (L.map e.symm) = N at hh
    refine ⟨?_, ?_⟩
    · simpa only [List.length_map] using hh.1
    · simpa only [PaperVerification.WeightedBar.totalDegree, List.map_map,
        Function.comp_def] using hh.2

#print axioms productCoefficients_transport
#print axioms differential_transport
#print axioms homogeneousPiece_transport

end Unimodular.FlagKoszul.BarReindex

#check Unimodular.FlagKoszul.BarReindex.differential_transport
