module

public import Papers.GraphicalZonotopes.Directions
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

def totalLinear : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := subsetSum x univ
  map_add' x y := subsetSum_add x y univ
  map_smul' a x := subsetSum_smul a x univ

theorem vectorSpan_basePolytope_le_total_ker {z : SetFunction V}
    (hne : (basePolytope z).Nonempty) :
    vectorSpan ℝ (basePolytope z) ≤ (totalLinear (V := V)).ker := by
  obtain ⟨q,hq⟩ := hne
  rw [vectorSpan_eq_span_vsub_set_right ℝ hq]
  apply Submodule.span_le.mpr
  rintro x ⟨p,hp,rfl⟩
  change subsetSum (p-q) univ = 0
  rw [subsetSum_sub, hp.1, hq.1, sub_self]

theorem finrank_total_ker {n : ℕ} (hn : 0 < n) :
    Module.finrank ℝ (totalLinear (V := Fin n)).ker = n-1 := by
  let e : Fin n := ⟨0, hn⟩
  have hsurj : Function.Surjective (totalLinear (V := Fin n)) := by
    intro a
    refine ⟨a • basisVector e, ?_⟩
    change subsetSum (a • basisVector e) univ = a
    simp
  have hrange : (totalLinear (V := Fin n)).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have h := (totalLinear (V := Fin n)).ker.finrank_quotient_add_finrank
  rw [(totalLinear (V := Fin n)).quotKerEquivRange.finrank_eq, hrange] at h
  simp only [finrank_top, Module.finrank_self, Module.finrank_pi, Fintype.card_fin] at h
  omega

def zeroRoot {n : ℕ} (hn : 0 < n) (i : Fin (n-1)) : Fin n → ℝ :=
  basisVector ⟨i.val+1, by omega⟩ - basisVector ⟨0, hn⟩

theorem zeroRoot_evaluation {n : ℕ} (hn : 0 < n) (i j : Fin (n-1)) :
    zeroRoot hn i ⟨j.val+1, by omega⟩ = if i = j then 1 else 0 := by
  simp [zeroRoot, basisVector, Pi.single_apply, Fin.ext_iff, eq_comm]

theorem zeroRoot_linearIndependent {n : ℕ} (hn : 0 < n) :
    LinearIndependent ℝ (zeroRoot hn) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrFun hc (⟨j.val+1, by omega⟩ : Fin n)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zeroRoot_evaluation] at h
  simpa using h

theorem all_zeroRoots_mem_of_consecutive {n : ℕ} (hn : 0 < n)
    (W : Submodule ℝ (Fin n → ℝ))
    (hW : ∀ i : Fin (n-1),
      basisVector (⟨i.val, by omega⟩ : Fin n) - basisVector ⟨i.val+1, by omega⟩ ∈ W) :
    ∀ i : Fin (n-1), zeroRoot hn i ∈ W := by
  have hroot : ∀ k : ℕ, ∀ hk : k<n,
      basisVector (⟨k,hk⟩ : Fin n) - basisVector ⟨0,hn⟩ ∈ W := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hstep := hW ⟨k,by omega⟩
      have hh := W.sub_mem hprev hstep
      convert hh using 1 <;> module
  intro i
  exact hroot (i.val+1) (by omega)

theorem finrank_vectorSpan_eq_of_consecutive_roots {n : ℕ} {z : SetFunction (Fin n)}
    (hn : 0 < n) (hne : (basePolytope z).Nonempty)
    (hroots : ∀ i : Fin (n-1),
      basisVector (⟨i.val, by omega⟩ : Fin n) - basisVector ⟨i.val+1, by omega⟩ ∈
        vectorSpan ℝ (basePolytope z)) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) = n-1 := by
  have hupper := Submodule.finrank_mono (vectorSpan_basePolytope_le_total_ker hne)
  rw [finrank_total_ker hn] at hupper
  have hspan : Submodule.span ℝ (Set.range (zeroRoot hn)) ≤ vectorSpan ℝ (basePolytope z) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact all_zeroRoots_mem_of_consecutive hn _ hroots i
  have hlower := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card (zeroRoot_linearIndependent hn), Fintype.card_fin] at hlower
  exact le_antisymm hupper hlower

end GraphicalZonotopes
