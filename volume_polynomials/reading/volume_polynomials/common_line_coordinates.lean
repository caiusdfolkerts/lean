module

public import VolumePolynomials.PlaneCoordinates
public import VolumePolynomials.ProjectionCoordinates
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Compatible coordinates for planes sharing a line

One nonzero vector on the common line is used in all three planar
parameterizations. Each plane has one fixed transverse vector. Every pair
of planes then has an actual three-dimensional coordinate equivalence,
so its positive Haar factor multiplies both repeated mixed coefficients.
No angular factor or determinant normalization is assumed.
-/

open Set Module
open scoped BigOperators

namespace VolumePolynomials.CommonLineCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

structure Data (P : Fin 3 → Submodule ℝ E) where
  z : E
  z_ne_zero : z ≠ 0
  z_mem : ∀ i, z ∈ P i
  u : Fin 3 → E
  u_mem : ∀ i, u i ∈ P i
  u_not_line : ∀ i, u i ∉ ℝ ∙ z
  plane_span : ∀ i, P i = Submodule.span ℝ ({z, u i} : Set E)

theorem transverse_pair_independent {z u : E} (hz : z ≠ 0) (hu : u ∉ ℝ ∙ z) :
    LinearIndependent ℝ (![u, z] : Fin 2 → E) := by
  first
  | apply linearIndependent_fin2.mpr
    refine ⟨hz, ?_⟩
    intro a ha
    apply hu
    exact Submodule.mem_span_singleton.mpr ⟨a, ha⟩

theorem exists_data (P : Fin 3 → Submodule ℝ E)
    (hP : ∀ i, finrank ℝ (P i) = 2) (hcommon : P 0 ⊓ P 1 ⊓ P 2 ≠ ⊥) :
    Nonempty (Data P) := by
  first
  | classical
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcommon
    have hzP (i : Fin 3) : z ∈ P i := by
      first
      | fin_cases i
        · exact hz.1.1
        · exact hz.1.2
        · exact hz.2
    have hex (i : Fin 3) : ∃ u : E, u ∈ P i ∧ u ∉ ℝ ∙ z := by
      first
      | by_contra! h
        have hle : P i ≤ ℝ ∙ z := h
        have hd := Submodule.finrank_mono hle
        rw [hP i, finrank_span_singleton hz0] at hd
        omega
    choose u hu hnot using hex
    refine ⟨⟨z, hz0, hzP, u, hu, hnot, ?_⟩⟩
    intro i
    have hli := transverse_pair_independent hz0 (hnot i)
    have hrange : Set.range (![u i, z] : Fin 2 → E) = ({z, u i} : Set E) := by
      first
      | ext x
        constructor
        · rintro ⟨j, rfl⟩
          fin_cases j <;> simp
        · rintro (rfl | rfl)
          · exact ⟨1, rfl⟩
          · exact ⟨0, rfl⟩
    have hdim : finrank ℝ (Submodule.span ℝ ({z, u i} : Set E)) = 2 := by
      first
      | rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin]
    have hle : Submodule.span ℝ ({z, u i} : Set E) ≤ P i := by
      first
      | apply Submodule.span_le.mpr
        rintro x (rfl | rfl)
        · exact hzP i
        · exact hu i
    exact (Submodule.eq_of_le_of_finrank_eq hle (hdim.trans (hP i).symm)).symm

def Data.planeMap {P : Fin 3 → Submodule ℝ E} (D : Data P) (i : Fin 3) :
    (ℝ × ℝ) →L[ℝ] E where
  toFun p := p.1 • D.z + p.2 • D.u i
  map_add' p q := by
    first
    | change (p.1 + q.1) • D.z + (p.2 + q.2) • D.u i =
        (p.1 • D.z + p.2 • D.u i) + (q.1 • D.z + q.2 • D.u i)
      simp only [add_smul]
      abel
  map_smul' r p := by
    first
    | change (r * p.1) • D.z + (r * p.2) • D.u i = r • (p.1 • D.z + p.2 • D.u i)
      simp only [smul_add, smul_smul]
  cont := by fun_prop

@[simp] theorem Data.planeMap_apply {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (i : Fin 3) (p : ℝ × ℝ) :
    D.planeMap i p = p.1 • D.z + p.2 • D.u i := rfl

theorem Data.planeMap_injective {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (i : Fin 3) : Function.Injective (D.planeMap i) := by
  first
  | intro p q hpq
    have hli := transverse_pair_independent D.z_ne_zero (D.u_not_line i)
    have hsum : (∑ j : Fin 2,
        (![p.2 - q.2, p.1 - q.1] : Fin 2 → ℝ) j • (![D.u i, D.z] : Fin 2 → E) j) = 0 := by
      first
      | simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_smul]
        change p.1 • D.z + p.2 • D.u i = q.1 • D.z + q.2 • D.u i at hpq
        linear_combination (norm := module) hpq
    have heq := Fintype.linearIndependent_iff.mp hli _ hsum
    exact Prod.ext (sub_eq_zero.mp (heq 1)) (sub_eq_zero.mp (heq 0))

theorem Data.range_planeMap {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (i : Fin 3) : Set.range (D.planeMap i) = (P i : Set E) := by
  first
  | ext x
    rw [D.plane_span i]
    change (∃ p, D.planeMap i p = x) ↔ x ∈ Submodule.span ℝ {D.z, D.u i}
    rw [Submodule.mem_span_pair]
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p.1, p.2, hp⟩
    · rintro ⟨a, b, hab⟩
      exact ⟨(a, b), hab⟩

theorem Data.transverse_not_mem_other {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) : D.u j ∉ P i := by
  first
  | intro hj
    have hji : P j ≤ P i := by
      first
      | rw [D.plane_span j]
        apply Submodule.span_le.mpr
        rintro x (rfl | rfl)
        · exact D.z_mem i
        · exact hj
    have htop : P i = ⊤ := by
      first
      | have h := hpair i j hij
        rwa [sup_eq_left.mpr hji] at h
    have he := hP i
    rw [htop, finrank_top, hdim] at he
    omega

theorem Data.pair_independent {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) :
    LinearIndependent ℝ (![D.z, D.u i, D.u j] : Fin 3 → E) := by
  first
  | rw [Fintype.linearIndependent_iff]
    intro a ha r
    have hsum : a 0 • D.z + a 1 • D.u i + a 2 • D.u j = 0 := by
      first
      | simpa only [Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using ha
    have hterm : a 2 • D.u j ∈ P i := by
      first
      | have he : a 2 • D.u j = -(a 0 • D.z + a 1 • D.u i) := by
          linear_combination (norm := module) hsum
        rw [he]
        exact (P i).neg_mem ((P i).add_mem ((P i).smul_mem _ (D.z_mem i))
          ((P i).smul_mem _ (D.u_mem i)))
    have ha2 : a 2 = 0 := by
      first
      | by_contra hne
        exact D.transverse_not_mem_other hdim hP hpair i j hij ((P i).smul_mem_iff hne |>.mp hterm)
    rw [ha2, zero_smul, add_zero] at hsum
    have hterm1 : a 1 • D.u i ∈ ℝ ∙ D.z := by
      first
      | have he : a 1 • D.u i = -(a 0 • D.z) := eq_neg_of_add_eq_zero_right hsum
        rw [he]
        exact (ℝ ∙ D.z).neg_mem ((ℝ ∙ D.z).smul_mem _ (Submodule.mem_span_singleton_self D.z))
    have ha1 : a 1 = 0 := by
      first
      | by_contra hne
        exact D.u_not_line i ((ℝ ∙ D.z).smul_mem_iff hne |>.mp hterm1)
    rw [ha1, zero_smul, add_zero] at hsum
    have ha0 : a 0 = 0 := (smul_eq_zero.mp hsum).resolve_right D.z_ne_zero
    fin_cases r <;> assumption

def Data.pairBasis {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) : Basis (Fin 3) ℝ E :=
  basisOfLinearIndependentOfCardEqFinrank (D.pair_independent hdim hP hpair i j hij)
    (by simpa only [Fintype.card_fin] using hdim.symm)

theorem Data.pairBasis_apply {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) (r : Fin 3) :
    D.pairBasis hdim hP hpair i j hij r = (![D.z, D.u i, D.u j] : Fin 3 → E) r :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank
    (D.pair_independent hdim hP hpair i j hij)
    (by simpa only [Fintype.card_fin] using hdim.symm)) r

def Data.pairFrame {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) : E ≃L[ℝ] (ℝ × (ℝ × ℝ)) :=
  (D.pairBasis hdim hP hpair i j hij).equivFun.toContinuousLinearEquiv.trans
    (Holonomy.coordinateExtract 0).toContinuousLinearEquiv

theorem Data.pairFrame_basis {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) (r : Fin 3) :
    D.pairFrame hdim hP hpair i j hij (D.pairBasis hdim hP hpair i j hij r) =
      (![(1, (0, 0)), (0, (1, 0)), (0, (0, 1))] : Fin 3 → ℝ × (ℝ × ℝ)) r := by
  first
  | change ((D.pairBasis hdim hP hpair i j hij).equivFun
        (D.pairBasis hdim hP hpair i j hij r) 0,
      ((D.pairBasis hdim hP hpair i j hij).equivFun
        (D.pairBasis hdim hP hpair i j hij r) 1,
       (D.pairBasis hdim hP hpair i j hij).equivFun
        (D.pairBasis hdim hP hpair i j hij r) 2)) = _
    simp only [Basis.equivFun_self]
    fin_cases r <;> norm_num

theorem Data.pairFrame_left {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) (p : ℝ × ℝ) :
    D.pairFrame hdim hP hpair i j hij (D.planeMap i p) = (p.1, (p.2, 0)) := by
  first
  | have hz := D.pairFrame_basis hdim hP hpair i j hij 0
    have hi := D.pairFrame_basis hdim hP hpair i j hij 1
    simp only [D.pairBasis_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hz hi
    rw [D.planeMap_apply, map_add, map_smul, map_smul, hz, hi]
    ext <;> simp

theorem Data.pairFrame_right {P : Fin 3 → Submodule ℝ E}
    (D : Data P) (hdim : finrank ℝ E = 3) (hP : ∀ i, finrank ℝ (P i) = 2)
    (hpair : ∀ i j, i ≠ j → P i ⊔ P j = ⊤)
    (i j : Fin 3) (hij : i ≠ j) (p : ℝ × ℝ) :
    D.pairFrame hdim hP hpair i j hij (D.planeMap j p) = (p.1, (0, p.2)) := by
  first
  | have hz := D.pairFrame_basis hdim hP hpair i j hij 0
    have hj := D.pairFrame_basis hdim hP hpair i j hij 2
    simp only [D.pairBasis_apply, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hz hj
    rw [D.planeMap_apply, map_add, map_smul, map_smul, hz, hj]
    ext <;> simp

end VolumePolynomials.CommonLineCoordinates
