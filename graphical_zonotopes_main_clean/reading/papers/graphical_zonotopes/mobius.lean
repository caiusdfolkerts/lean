module

public import Papers.GraphicalZonotopes.Elemental
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def zeta (y : SetFunction V) (S : Finset V) : ℝ := ∑ C ∈ S.powerset, y C

def zetaLinear : SetFunction V →ₗ[ℝ] SetFunction V where
  toFun := zeta
  map_add' y z := by funext S; simp [zeta, sum_add_distrib]
  map_smul' a y := by funext S; simp [zeta, mul_sum]

theorem zeta_eq_zero_iff (y : SetFunction V) : zeta y = 0 ↔ y = 0 := by
  constructor
  · intro h
    funext S
    refine Finset.strongInductionOn S ?_
    intro S ih
    have he := congrFun h S
    change ∑ C ∈ S.powerset, y C = 0 at he
    rw [Finset.sum_eq_single S] at he
    · exact he
    · intro C hC hCS
      exact ih C (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hC, hCS⟩)
    · simp
  · rintro rfl
    funext S
    simp [zeta]

theorem zeta_injective : Function.Injective (zeta : SetFunction V → SetFunction V) := by
  intro y z he
  have h : zeta (y - z) = 0 := by
    change zetaLinear (y - z) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr he
  exact sub_eq_zero.mp ((zeta_eq_zero_iff _).mp h)

def zetaEquiv : SetFunction V ≃ₗ[ℝ] SetFunction V :=
  LinearEquiv.ofInjectiveEndo zetaLinear zeta_injective

def mobius (z : SetFunction V) : SetFunction V := zetaEquiv.symm z

@[simp] theorem zeta_mobius (z : SetFunction V) : zeta (mobius z) = z :=
  zetaEquiv.apply_symm_apply z

@[simp] theorem mobius_zeta (y : SetFunction V) : mobius (zeta y) = y :=
  zetaEquiv.symm_apply_apply y

def setMonomial (C : Finset V) (S : Finset V) : ℝ := if C ⊆ S then 1 else 0

theorem zeta_eq_sum_monomials (y : SetFunction V) :
    zeta y = ∑ C : Finset V, y C • setMonomial C := by
  funext S
  unfold zeta
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, setMonomial]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext C
  simp

theorem delta_setMonomial {u v : V} (huv : u ≠ v) {S : Finset V}
    (hu : u ∉ S) (hv : v ∉ S) (C : Finset V) :
    delta (setMonomial C) u v S =
      if u ∈ C ∧ v ∈ C ∧ C ⊆ insert u (insert v S) then 1 else 0 := by
  have h1 : C ⊆ insert u S ↔ C ⊆ insert u (insert v S) ∧ v ∉ C := by
    constructor
    · intro h
      refine ⟨h.trans (insert_subset_insert _ (subset_insert _ _)), ?_⟩
      intro hvC
      have hm := h hvC
      simp [Ne.symm huv, hv] at hm
    · rintro ⟨h, hn⟩ x hx
      have hm := h hx
      simp only [mem_insert] at hm ⊢
      rcases hm with hxu | hxv | hxS
      · exact Or.inl hxu
      · exact False.elim (hn (hxv ▸ hx))
      · exact Or.inr hxS
  have h2 : C ⊆ insert v S ↔ C ⊆ insert u (insert v S) ∧ u ∉ C := by
    constructor
    · intro h
      refine ⟨h.trans (subset_insert _ _), ?_⟩
      intro huC
      have hm := h huC
      simp [huv, hu] at hm
    · rintro ⟨h, hn⟩ x hx
      have hm := h hx
      rcases mem_insert.mp hm with hxu | hm
      · exact False.elim (hn (hxu ▸ hx))
      · exact hm
  have h3 : C ⊆ S ↔ C ⊆ insert u (insert v S) ∧ u ∉ C ∧ v ∉ C := by
    constructor
    · intro h
      refine ⟨h.trans ((subset_insert _ _).trans (subset_insert _ _)), ?_, ?_⟩
      · exact fun hm => hu (h hm)
      · exact fun hm => hv (h hm)
    · rintro ⟨h, hnu, hnv⟩ x hx
      have hm := h hx
      simp only [mem_insert] at hm
      rcases hm with hxu | hxv | hxS
      · exact False.elim (hnu (hxu ▸ hx))
      · exact False.elim (hnv (hxv ▸ hx))
      · exact hxS
  simp only [delta, setMonomial, h1, h2, h3]
  by_cases hC : C ⊆ insert u (insert v S) <;>
    by_cases huC : u ∈ C <;> by_cases hvC : v ∈ C <;> simp [hC, huC, hvC]

theorem delta_zeta {u v : V} (huv : u ≠ v) {S : Finset V}
    (hu : u ∉ S) (hv : v ∉ S) (y : SetFunction V) :
    delta (zeta y) u v S =
      ∑ C ∈ (insert u (insert v S)).powerset.filter (fun C => u ∈ C ∧ v ∈ C), y C := by
  rw [zeta_eq_sum_monomials, delta_sum]
  simp_rw [delta_smul, delta_setMonomial huv hu hv]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext C
  simp only [mem_filter, mem_univ, true_and, mem_powerset]
  tauto

@[simp] theorem zeta_empty (y : SetFunction V) : zeta y ∅ = y ∅ := by simp [zeta]

theorem zeta_singleton (y : SetFunction V) (v : V) : zeta y {v} = y ∅ + y {v} := by
  have hp : ({v} : Finset V).powerset = {∅,{v}} := by
    ext C
    simp only [mem_powerset,mem_insert,mem_singleton,subset_singleton_iff]
  simp [zeta,hp]

theorem zeta_normalized_iff (y : SetFunction V) :
    TranslationNormalized (zeta y) ↔ y ∅ = 0 ∧ ∀ v, y {v} = 0 := by
  simp only [TranslationNormalized, Normalized, zeta_empty, zeta_singleton]
  constructor
  · rintro ⟨h, hv⟩
    exact ⟨h, fun v => by simpa [h] using hv v⟩
  · rintro ⟨h, hv⟩
    exact ⟨h, fun v => by simp [h, hv v]⟩

theorem nonedge_coefficients_zero_iff (y : SetFunction V) {u v : V} (huv : u ≠ v) :
    (∀ S, u ∉ S → v ∉ S → delta (zeta y) u v S = 0) ↔
      ∀ C, u ∈ C → v ∈ C → y C = 0 := by
  constructor
  · intro hz C
    refine Finset.strongInductionOn C ?_
    intro C ih huC hvC
    let S := (C.erase u).erase v
    have huS : u ∉ S := by simp [S]
    have hvS : v ∉ S := by simp [S]
    have he : insert u (insert v S) = C := by
      ext w
      by_cases hwu : w = u
      · subst w
        simp [S,huC]
      · by_cases hwv : w = v
        · subst w
          simp [S,hvC]
        · simp [S,hwu,hwv]
    have h := hz S huS hvS
    rw [delta_zeta huv huS hvS, he] at h
    rw [sum_eq_single C] at h
    · exact h
    · intro D hD hDC
      rcases mem_filter.mp hD with ⟨hsub, huD, hvD⟩
      exact ih D (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hsub, hDC⟩) huD hvD
    · simp [huC, hvC]
  · intro hz S hu hv
    rw [delta_zeta huv hu hv]
    apply sum_eq_zero
    intro C hC
    exact hz C (mem_filter.mp hC).2.1 (mem_filter.mp hC).2.2

end GraphicalZonotopes
