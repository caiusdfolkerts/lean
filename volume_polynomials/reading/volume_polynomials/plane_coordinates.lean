module

public import VolumePolynomials.Definitions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Coordinates for three planes in general position

A nonzero vector on each pairwise intersection gives a basis. The vanishing
of the corresponding coordinate characterizes each original plane exactly.
The construction applies to every real three-dimensional normed space and
does not assume preselected normals or an orthogonal configuration.
-/

open Set Module
open scoped BigOperators

namespace VolumePolynomials.PlaneCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem pair_intersection_nonzero (hdim : finrank ℝ E = 3)
    (P Q : Submodule ℝ E) (hP : finrank ℝ P = 2) (hQ : finrank ℝ Q = 2) :
    P ⊓ Q ≠ ⊥ := by
  first
  | intro hzero
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
    have hle := (P ⊔ Q).finrank_le
    rw [hzero, finrank_bot, hP, hQ, add_zero] at h
    rw [hdim] at hle
    omega

theorem exists_coordinate_vectors (hdim : finrank ℝ E = 3)
    (P : Fin 3 → Submodule ℝ E) (hP : ∀ i, finrank ℝ (P i) = 2)
    (htriple : P 0 ⊓ P 1 ⊓ P 2 = ⊥) :
    ∃ v : Fin 3 → E, (∀ i, v i ∉ P i) ∧ ∀ i j, i ≠ j → v i ∈ P j := by
  first
  | obtain ⟨v0, hv0, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (pair_intersection_nonzero hdim (P 1) (P 2) (hP 1) (hP 2))
    obtain ⟨v1, hv1, hn1⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (pair_intersection_nonzero hdim (P 0) (P 2) (hP 0) (hP 2))
    obtain ⟨v2, hv2, hn2⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (pair_intersection_nonzero hdim (P 0) (P 1) (hP 0) (hP 1))
    have hnP0 : v0 ∉ P 0 := by
      first
      | intro h0
        have hmem : v0 ∈ P 0 ⊓ P 1 ⊓ P 2 := ⟨⟨h0, hv0.1⟩, hv0.2⟩
        rw [htriple, Submodule.mem_bot] at hmem
        exact hn0 hmem
    have hnP1 : v1 ∉ P 1 := by
      first
      | intro h1
        have hmem : v1 ∈ P 0 ⊓ P 1 ⊓ P 2 := ⟨⟨hv1.1, h1⟩, hv1.2⟩
        rw [htriple, Submodule.mem_bot] at hmem
        exact hn1 hmem
    have hnP2 : v2 ∉ P 2 := by
      first
      | intro h2
        have hmem : v2 ∈ P 0 ⊓ P 1 ⊓ P 2 := ⟨hv2, h2⟩
        rw [htriple, Submodule.mem_bot] at hmem
        exact hn2 hmem
    refine ⟨![v0, v1, v2], ?_, ?_⟩
    · intro i
      fin_cases i <;> assumption
    · intro i j hij
      fin_cases i
      · fin_cases j
        · exact (hij rfl).elim
        · exact hv0.1
        · exact hv0.2
      · fin_cases j
        · exact hv1.1
        · exact (hij rfl).elim
        · exact hv1.2
      · fin_cases j
        · exact hv2.1
        · exact hv2.2
        · exact (hij rfl).elim

theorem independent_coordinate_vectors (P : Fin 3 → Submodule ℝ E)
    (v : Fin 3 → E) (hnot : ∀ i, v i ∉ P i)
    (hmem : ∀ i j, i ≠ j → v i ∈ P j) : LinearIndependent ℝ v := by
  first
  | classical
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hrest : (∑ j ∈ Finset.univ.erase i, a j • v j) ∈ P i := by
      first
      | apply Submodule.sum_mem
        intro j hj
        exact (P i).smul_mem (a j) (hmem j i (Finset.ne_of_mem_erase hj))
    have hsplit : a i • v i + ∑ j ∈ Finset.univ.erase i, a j • v j = 0 := by
      first
      | rw [Finset.add_sum_erase Finset.univ (fun j => a j • v j) (Finset.mem_univ i)]
        exact ha
    have hai : a i • v i ∈ P i := by
      first
      | have heq : a i • v i = -(∑ j ∈ Finset.univ.erase i, a j • v j) := by
          exact eq_neg_of_add_eq_zero_left hsplit
        rw [heq]
        exact (P i).neg_mem hrest
    by_contra hne
    exact hnot i ((P i).smul_mem_iff hne |>.mp hai)

theorem coordinate_zero_iff_mem (P : Fin 3 → Submodule ℝ E)
    (b : Basis (Fin 3) ℝ E) (hnot : ∀ i, b i ∉ P i)
    (hmem : ∀ i j, i ≠ j → b i ∈ P j) (i : Fin 3) (x : E) :
    b.equivFun x i = 0 ↔ x ∈ P i := by
  first
  | classical
    constructor
    · intro hz
      rw [← b.sum_equivFun x]
      apply Submodule.sum_mem
      intro j _
      by_cases hji : j = i
      · subst j
        rw [hz, zero_smul]
        exact (P i).zero_mem
      · exact (P i).smul_mem _ (hmem j i hji)
    · intro hx
      have hrest : (∑ j ∈ Finset.univ.erase i, b.equivFun x j • b j) ∈ P i := by
        first
        | apply Submodule.sum_mem
          intro j hj
          exact (P i).smul_mem _ (hmem j i (Finset.ne_of_mem_erase hj))
      have hsplit : b.equivFun x i • b i +
          ∑ j ∈ Finset.univ.erase i, b.equivFun x j • b j = x := by
        first
        | rw [Finset.add_sum_erase Finset.univ
            (fun j => b.equivFun x j • b j) (Finset.mem_univ i)]
          exact b.sum_equivFun x
      have hi : b.equivFun x i • b i ∈ P i := by
        first
        | have heq : b.equivFun x i • b i = x -
              ∑ j ∈ Finset.univ.erase i, b.equivFun x j • b j := by
            exact eq_sub_iff_add_eq.mpr hsplit
          rw [heq]
          exact (P i).sub_mem hx hrest
      by_contra hne
      exact hnot i ((P i).smul_mem_iff hne |>.mp hi)

/-- The geometric planes become the three coordinate planes, with both
directions of the membership equivalence retained. -/
theorem exists_plane_coordinates (hdim : finrank ℝ E = 3)
    (P : Fin 3 → Submodule ℝ E) (hP : ∀ i, finrank ℝ (P i) = 2)
    (htriple : P 0 ⊓ P 1 ⊓ P 2 = ⊥) :
    ∃ T : E ≃L[ℝ] Space 3, ∀ i : Fin 3, ∀ x : E, x ∈ P i ↔ T x i = 0 := by
  first
  | obtain ⟨v, hnot, hmem⟩ := exists_coordinate_vectors hdim P hP htriple
    have hli := independent_coordinate_vectors P v hnot hmem
    let b : Basis (Fin 3) ℝ E := basisOfLinearIndependentOfCardEqFinrank hli (by simpa using hdim.symm)
    have hb : ∀ i, b i = v i := by
      first
      | intro i
        exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli
          (by simpa using hdim.symm)) i
    refine ⟨b.equivFun.toContinuousLinearEquiv, ?_⟩
    intro i x
    exact (coordinate_zero_iff_mem P b (by simpa only [hb] using hnot)
      (by simpa only [hb] using hmem) i x).symm

end VolumePolynomials.PlaneCoordinates
