module

public import PaperVerification.FermionNewtonAllOneMatrix
public import PaperVerification.FermionNewtonSchurMatrix
public import PaperVerification.FermionNewtonSchurSpecialization

/-!
# Nonvanishing in the negative first-sign step

The exact first-height suffix expansion determines a nonempty prefix sum
as the top coefficient of the cleared Schur numerator. An injective
polynomial specialization therefore proves that the literal Newton matrix
at the next size is nonsingular.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators Matrix

variable {L E : Type*} [Field L] [Field E] {n : ℕ}

theorem allOne_negative_step_det_ne_zero
    (φ : L[X] →+* E) (hφ : Function.Injective φ)
    (σ : Fin n → ℤ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (y β : Fin n → L) (β₀ : L)
    (hβ : ∀ U : Finset (Fin (n + 1)), U.Nonempty →
      IsUnit (∑ i ∈ U, (Fin.cases β₀ β i : L)))
    (hS : (allOneNewtonMatrix σ y β).det ≠ 0)
    (hpattern : PowerExpansionPattern (allOneHeight σ)
      (matrixPowerExpansion (allOneNewtonMatrix σ y β) y)) :
    (allOneNewtonMatrix (Fin.cases (-1) σ)
      (Fin.cases (φ X) (fun i ↦ φ (C (y i))))
      (Fin.cases (φ (C β₀)) (fun i ↦ φ (C (β i))))).det ≠ 0 := by
  have hZ : φ X ≠ 0 := by
    intro h
    apply Polynomial.X_ne_zero (R := L)
    apply hφ
    simpa only [map_zero] using h
  cases n with
  | zero =>
      rw [Matrix.det_fin_one]
      simpa only [allOneNewtonMatrix_first_column,
        Fin.cases_zero] using hZ
  | succ n =>
      let c : L →+* E := φ.comp Polynomial.C
      let A := matrixPowerExpansion (allOneNewtonMatrix σ y β) y 2
      let positive := earlierPositive σ
      let poles := earlierNegative σ
      let active := @activeTail (n + 1)
      have hdisj (i : Fin (n + 1)) : Disjoint (active i) (poles i) := by
        apply Finset.disjoint_left.mpr
        intro k hk hn
        exact (not_lt_of_ge (Finset.mem_filter.mp hk).2)
          ((mem_earlierNegative σ i k).mp hn).1
      have hhigh (i : Fin (n + 1)) : (poles i).card + 1 < (positive i).card → A i = 0 := by
        intro hh
        apply hpattern.1 2 (by omega) i
        rw [allOneHeight_eq_card_difference σ hσ i]
        dsimp only [poles, positive] at hh
        omega
      have hclear : C β₀ * Lagrange.nodal Finset.univ y -
          ∑ i, C (A i) * clearedResidueRow y β (positive i) (poles i) (active i) +
          X * clearedResidueRow y β ∅ ∅ Finset.univ ≠ 0 := by
        let critical := Finset.univ.filter (fun i ↦ allOneHeight σ i = 2)
        by_cases hc : critical.Nonempty
        · let j := critical.min' hc
          have hj : allOneHeight σ j = 2 := (Finset.mem_filter.mp (Finset.min'_mem critical hc)).2
          have hjcard : (positive j).card = (poles j).card + 1 := by
            rw [allOneHeight_eq_card_difference σ hσ j] at hj
            dsimp only [positive, poles]
            omega
          have hcrit (i : Fin (n + 1)) (hi : (positive i).card = (poles i).card + 1) :
              A i = if i = j then 1 else 0 := by
            have hiheight : allOneHeight σ i = 2 := by
              rw [allOneHeight_eq_card_difference σ hσ i]
              dsimp only [positive, poles] at hi
              omega
            rw [show A i = if ∀ k, k < i → allOneHeight σ k ≠ (2 : ℤ) then 1 else 0 from
              hpattern.2 2 (by omega) i hiheight]
            by_cases hij : i = j
            · subst i
              have hfirst : ∀ k, k < j → allOneHeight σ k ≠ (2 : ℤ) := by
                intro k hkj hk
                have hkm : k ∈ critical := by simp [critical, hk]
                exact (not_le_of_gt hkj) (Finset.min'_le critical k hkm)
              rw [if_pos rfl, if_pos hfirst]
            · have hji : j < i := lt_of_le_of_ne
                (Finset.min'_le critical i (by simp [critical, hiheight])) (Ne.symm hij)
              have hn : ¬ ∀ k, k < i → allOneHeight σ k ≠ (2 : ℤ) := by
                intro h
                exact h j hji hj
              rw [if_neg hn, if_neg hij]
          have hweight : β₀ + ∑ k ∈ Finset.univ \ active j, β k ≠ 0 := by
            let U := insert (0 : Fin (n + 2)) ((Finset.univ \ active j).map (Fin.succEmb (n + 1)))
            have hu := (hβ U (Finset.insert_nonempty _ _)).ne_zero
            have hsum : (∑ i ∈ U, Fin.cases β₀ β i) =
                β₀ + ∑ k ∈ Finset.univ \ active j, β k := by
              have hnot : (0 : Fin (n + 2)) ∉
                  (Finset.univ \ active j).map (Fin.succEmb (n + 1)) := by
                intro hh
                obtain ⟨k, hk, hk0⟩ := Finset.mem_map.mp hh
                exact Fin.succ_ne_zero k hk0
              simp only [U, Finset.sum_insert hnot, Finset.sum_map,
                Fin.cases_zero, Fin.coe_succEmb, Fin.cases_succ]
            rwa [hsum] at hu
          exact clearedSchur_ne_zero_of_first_critical y β β₀ positive poles active A j
            hdisj hhigh hjcard hcrit hweight
        · have hnone (i : Fin (n + 1)) : (positive i).card ≠ (poles i).card + 1 := by
            intro hi
            apply hc
            refine ⟨i, ?_⟩
            have hh : allOneHeight σ i = 2 := by
              rw [allOneHeight_eq_card_difference σ hσ i]
              dsimp only [positive, poles] at hi
              omega
            simp [critical, hh]
          have hweight : β₀ + ∑ k, β k ≠ 0 := by
            have h := (hβ Finset.univ Finset.univ_nonempty).ne_zero
            simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ] using h
          exact clearedSchur_ne_zero_of_no_critical y β β₀ positive poles active A
            hdisj hhigh hnone hweight
      have hlinear (i : Fin (n + 1)) : φ X - φ (C (y i)) ≠ 0 := by
        intro h
        exact Polynomial.X_ne_C (y i) (hφ (sub_eq_zero.mp h))
      have hβ₀L : β₀ ≠ 0 := by
        simpa only [Finset.sum_singleton, Fin.cases_zero] using
          (hβ {0} (Finset.singleton_nonempty 0)).ne_zero
      have hβ₀E : φ (C β₀) ≠ 0 := by
        intro h
        apply hβ₀L
        apply Polynomial.C_injective
        apply hφ
        simpa only [map_zero] using h
      have hschur := specializedSchur_ne_zero_of_cleared φ hφ y β β₀
        positive poles active A Finset.univ hdisj hlinear hβ₀E hclear
      let S := allOneNewtonMatrix σ (c ∘ y) (c ∘ β)
      have hSmap : S = (allOneNewtonMatrix σ y β).map c := (allOneNewtonMatrix_map c σ y β).symm
      have hSE : S.det ≠ 0 := by
        rw [hSmap, matrix_map_det]
        exact (map_ne_zero c).mpr hS
      let z := φ X
      let r : Fin (n + 1) → E := fun i ↦
        specializedResidueRow φ y β (positive i) (poles i) (active i) / φ (C β₀)
      have hzy (i : Fin (n + 1)) : c (y i) ≠ z := by
        intro h
        apply hlinear i
        exact sub_eq_zero.mpr h.symm
      let M := allOneNewtonMatrix (Fin.cases (-1) σ)
        (Fin.cases z (c ∘ y)) (Fin.cases (c β₀) (c ∘ β))
      have hmatrix : M = adjoinPowerColumn z (c ∘ y) (fun i ↦ z * r i)
          (fun k ↦ (c (y k) - z)⁻¹) S := by
        dsimp only [M]
        rw [allOneNewtonMatrix_eq_adjoin (Fin.cases (-1) σ)
          (Fin.cases z (c ∘ y)) (Fin.cases (c β₀) (c ∘ β))
          (fun k ↦ (c (y k) - z)⁻¹)
          (fun k i ↦ by
            rw [allOneNewtonMatrix_suffix_down _ _ _ rfl, div_eq_mul_inv, mul_comm]
            simp only [Fin.cases_succ, Fin.cases_zero, Function.comp_apply])]
        congr 1
        funext i
        rw [allOneNewtonMatrix_first_row_down _ _ _ rfl i]
        change z * ((Lagrange.nodal (positive i) (fun k ↦ φ (C (y k)))).eval z /
          ((Lagrange.nodal (poles i) (fun k ↦ φ (C (y k)))).eval z * φ (C β₀)) *
            ∑ k ∈ active i, φ (C (β k)) / (z - φ (C (y k)))) = z * r i
        rw [← map_nodal_eq_eval φ y (positive i), ← map_nodal_eq_eval φ y (poles i)]
        simp only [r, specializedResidueRow, z, div_eq_mul_inv, mul_inv_rev]
        ring
      have hB₁ : S *ᵥ Pi.single 0 1 = c ∘ y := by
        rw [Matrix.mulVec_single_one]
        funext k
        exact allOneNewtonMatrix_first_column σ (c ∘ y) (c ∘ β) k
      have hB₂ : S *ᵥ (c ∘ A) = fun k ↦ (c (y k)) ^ 2 := by
        rw [hSmap]
        funext k
        rw [← RingHom.map_mulVec, matrixPowerExpansion_solves _ hS y 2]
        exact map_pow c (y k) 2
      have hschur_eq : 1 - r ⬝ᵥ (c ∘ A) + z * (r ⬝ᵥ Pi.single 0 1) =
          specializedSchur φ y β β₀ positive poles active A Finset.univ := by
        rw [dotProduct_single_one]
        simp only [specializedSchur, r, c, z, RingHom.comp_apply, dotProduct,
          Function.comp_apply, positive, poles, active, earlierPositive_zero, earlierNegative_zero,
          activeTail_zero]
      change M.det ≠ 0
      have hdet := adjoinPowerColumn_negative_det z (c ∘ y) r (Pi.single 0 1) (c ∘ A)
        hzy S hB₁ hB₂
      simp only [Function.comp_apply] at hdet
      rw [hmatrix, hdet, hschur_eq]
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero hZ hschur)
          (Finset.prod_ne_zero_iff.mpr (fun k hk ↦ inv_ne_zero (sub_ne_zero.mpr (hzy k))))) hSE

end PaperVerification.Fermion.Newton
