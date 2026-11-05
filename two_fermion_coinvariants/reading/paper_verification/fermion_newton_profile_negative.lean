module

public import PaperVerification.FermionNewtonProfileSchur

/-!
# The negative deletion step for a nonconstant multiplicity profile

The supported initial block expands both lower-left vectors. Its support
removes every higher-multiplicity term from the Schur numerator. The leading
coefficient is the literal prefix sum, so an injective polynomial evaluation
proves nonvanishing without assuming polynomial inverse coefficients.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators Matrix

variable {L E : Type*} [Field L] [Field E] {n m : ℕ}

theorem profile_negative_step_det_ne_zero
    (φ : L[X] →+* E) (hφ : Function.Injective φ)
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ) (d : ℕ)
    (y β : Fin (n + 1) → L) (β₀ : L)
    (hm : m < n + 1)
    (hmin : ∀ i, d ≤ δ i)
    (hδ : ∀ i, i.val < m → δ i = d) (hjump : d < δ ⟨m, hm⟩)
    (hpositive : ∀ i, i.val < m → σ i ≠ 1)
    (hβ : ∀ U : Finset (Fin (n + 2)), U.Nonempty →
      IsUnit (∑ i ∈ U, (Fin.cases β₀ β i : L)))
    (hS : (profileNewtonMatrix δ σ y β).det ≠ 0)
    (hblock : ((profileNewtonMatrix δ σ y β).submatrix
      (prefixEmbedding hm.le) (prefixEmbedding hm.le)).det ≠ 0) :
    (profileNewtonMatrix (Fin.cases d δ) (Fin.cases (-1) σ)
      (Fin.cases (φ X) (fun i ↦ φ (C (y i))))
      (Fin.cases (φ (C β₀)) (fun i ↦ φ (C (β i))))).det ≠ 0 := by
  let c : L →+* E := φ.comp Polynomial.C
  let z := φ X
  let U : Finset (Fin (n + 1)) := Finset.univ.filter (fun i ↦ i.val < m)
  let η : Fin (n + 1) → L := fun k ↦ if k.val < m then y k ^ d else 0
  let S := profileNewtonMatrix δ σ y β
  let S' := profileNewtonMatrix δ σ (c ∘ y) (c ∘ β)
  let r : Fin (n + 1) → E := fun i ↦ z ^ (δ i - d) *
    (specializedResidueRow φ y β (earlierPositive σ i) (earlierNegative σ i)
      (activeInterval δ i) / φ (C β₀))
  let M := profileNewtonMatrix (Fin.cases d δ) (Fin.cases (-1) σ)
    (Fin.cases z (c ∘ y)) (Fin.cases (c β₀) (c ∘ β))
  have hZ : z ≠ 0 := by
    intro hz
    apply Polynomial.X_ne_zero (R := L)
    apply hφ
    simpa only [map_zero] using hz
  have hlinear (i : Fin (n + 1)) : φ X - φ (C (y i)) ≠ 0 := by
    intro h
    exact Polynomial.X_ne_C (y i) (hφ (sub_eq_zero.mp h))
  have hyz (i : Fin (n + 1)) : c (y i) ≠ z := by
    intro h
    exact hlinear i (sub_eq_zero.mpr h.symm)
  have hSmap : S' = S.map c := (profileNewtonMatrix_map c δ σ y β).symm
  have hSE : S'.det ≠ 0 := by
    rw [hSmap, matrix_map_det]
    exact (map_ne_zero c).mpr hS
  have hfirst (k : Fin (n + 1)) : M k.succ 0 = c (η k) := by
    dsimp only [M]
    rw [profileNewtonMatrix_first_column]
    simp only [activeInterval_first_of_prefix hm δ d hδ hjump]
    by_cases hk : k.val < m
    · simp only [Fin.cases_succ, Fin.cases_zero, η, if_pos hk,
        Function.comp_apply, map_pow]
    · simp only [Fin.cases_succ, Fin.cases_zero, η, if_neg hk,
        Function.comp_apply, map_zero]
  have hrow (i : Fin (n + 1)) : M 0 i.succ = z ^ d * r i := by
    dsimp only [M]
    rw [profileNewtonMatrix_first_row_down _ _ _ _ rfl i]
    change z ^ δ i *
      ((Lagrange.nodal (earlierPositive σ i) (fun k ↦ φ (C (y k)))).eval z /
        ((Lagrange.nodal (earlierNegative σ i) (fun k ↦ φ (C (y k)))).eval z * φ (C β₀)) *
          ∑ k ∈ activeInterval δ i, φ (C (β k)) / (z - φ (C (y k)))) = _
    rw [← map_nodal_eq_eval φ y (earlierPositive σ i),
      ← map_nodal_eq_eval φ y (earlierNegative σ i)]
    have hdegree : δ i = d + (δ i - d) := by have h := hmin i; omega
    rw [hdegree, pow_add]
    simp only [r, specializedResidueRow, z, div_eq_mul_inv, mul_inv_rev]
    ring
  have hmatrix : M = adjoinPowerColumn (z ^ d) (c ∘ η) (fun i ↦ z ^ d * r i)
      (fun k ↦ (c (y k) - z)⁻¹) S' := by
    ext k i
    refine Fin.cases ?_ (fun k ↦ ?_) k <;> refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact profileNewtonMatrix_zero_zero _ _ _ _
    · exact hrow i
    · exact hfirst k
    · dsimp only [M]
      rw [profileNewtonMatrix_suffix_down _ _ _ _ rfl k i]
      change S' k i / (c (y k) - z) = (c (y k) - z)⁻¹ * S' k i
      rw [div_eq_mul_inv, mul_comm]
  have hprod : (∏ k, (c (y k) - z)⁻¹) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k hk ↦ inv_ne_zero (sub_ne_zero.mpr (hyz k)))
  change M.det ≠ 0
  by_cases hmzero : m = 0
  · have hη : c ∘ η = 0 := by
      funext k
      simp [η, hmzero]
    have hsolve (k : Fin (n + 1)) :
        (c (y k) - z)⁻¹ * (S' *ᵥ (0 : Fin (n + 1) → E)) k = (c ∘ η) k := by
      rw [hη, Matrix.mulVec_zero]
      simp only [Pi.zero_apply, mul_zero]
    rw [hmatrix, adjoinPowerColumn_det (z ^ d) (c ∘ η) _ _ 0 S' hsolve,
      dotProduct_zero, sub_zero]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero d hZ) hprod) hSE
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
    obtain ⟨A, hA, hAsupport⟩ := exists_supported_expansion (prefixEmbedding hm.le) S hblock
      (fun k hk i ↦ profileNewtonMatrix_prefix_support hm δ d σ y β hδ hjump k hk i)
      (fun k ↦ y k * η k) (by
        intro k hk
        have hk' : ¬ k.val < m := fun h ↦ hk ((mem_range_prefixEmbedding hm.le k).mpr h)
        simp only [η, if_neg hk', mul_zero])
    have hAzero (i : Fin (n + 1)) (hi : i ∉ U) : A i = 0 := by
      apply hAsupport i
      simpa only [mem_range_prefixEmbedding, U, Finset.mem_filter,
        Finset.mem_univ, true_and] using hi
    have hdisj (i : Fin (n + 1)) : Disjoint (activeInterval δ i) (earlierNegative σ i) :=
      activeInterval_disjoint_earlierNegative δ σ i
    have hpos (i : Fin (n + 1)) (hi : i ∈ U) : earlierPositive σ i = ∅ :=
      earlierPositive_eq_empty_in_initial_block σ m hpositive i (Finset.mem_filter.mp hi).2
    have hweight : β₀ + ∑ k ∈ U, β k ≠ 0 := by
      let V := insert (0 : Fin (n + 2)) (U.map (Fin.succEmb (n + 1)))
      have h := (hβ V (Finset.insert_nonempty _ _)).ne_zero
      have hsum : (∑ i ∈ V, Fin.cases β₀ β i) = β₀ + ∑ k ∈ U, β k := by
        have hzero : (0 : Fin (n+2)) ∉ U.map (Fin.succEmb (n+1)) := by
          simp only [Finset.mem_map]
          rintro ⟨i,_,hi⟩
          exact Fin.succ_ne_zero i hi
        change (∑ i ∈ insert (0 : Fin (n+2)) (U.map (Fin.succEmb (n+1))),
          (Fin.cases β₀ β i : L)) = β₀ + ∑ k ∈ U, β k
        rw [Finset.sum_insert hzero,Fin.cases_zero,Finset.sum_map]
        rfl
      rwa [hsum] at h
    have hclear := clearedSchur_ne_zero_of_supported_no_positive y β β₀
      (earlierPositive σ) (earlierNegative σ) (activeInterval δ) A U hdisj hpos hAzero hweight
    have hβ₀L : β₀ ≠ 0 := by
      simpa only [Finset.sum_singleton, Fin.cases_zero] using
        (hβ {0} (Finset.singleton_nonempty 0)).ne_zero
    have hβ₀E : φ (C β₀) ≠ 0 := (map_ne_zero c).mpr hβ₀L
    have hschur := specializedSchur_ne_zero_of_cleared φ hφ y β β₀
      (earlierPositive σ) (earlierNegative σ) (activeInterval δ) A U
      hdisj hlinear hβ₀E hclear
    have hA' : S' *ᵥ (c ∘ A) = fun k ↦ c (y k) * c (η k) := by
      rw [hSmap]
      funext k
      rw [← RingHom.map_mulVec, hA]
      exact map_mul c _ _
    have hB' : S' *ᵥ Pi.single 0 1 = c ∘ η := by
      rw [Matrix.mulVec_single_one]
      funext k
      rw [hSmap]
      change c (profileNewtonMatrix δ σ y β k 0) = c (η k)
      rw [profile_first_column_of_prefix hm hmpos δ d σ y β hδ hjump]
    have hAsum : r ⬝ᵥ (c ∘ A) =
        ∑ i, (specializedResidueRow φ y β (earlierPositive σ i) (earlierNegative σ i)
          (activeInterval δ i) / φ (C β₀)) * φ (C (A i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hiU : i ∈ U
      · have hdi := hδ i (Finset.mem_filter.mp hiU).2
        simp only [r, hdi, Nat.sub_self, pow_zero, one_mul, Function.comp_apply,
          c, RingHom.comp_apply]
      · simp only [Function.comp_apply,hAzero i hiU,map_zero,mul_zero,Polynomial.C_0]
    have hactive : activeInterval δ 0 = U := by
      ext k
      exact (mem_activeInterval_zero_of_prefix hm hmpos δ d hδ hjump k).trans
        (by simp only [U, Finset.mem_filter, Finset.mem_univ, true_and])
    have hrzero : r 0 = specializedResidueRow φ y β ∅ ∅ U / φ (C β₀) := by
      simp only [r, hδ 0 hmpos, Nat.sub_self, pow_zero, one_mul,
        earlierPositive_zero, earlierNegative_zero, hactive]
    have hschur_eq : 1 - r ⬝ᵥ (c ∘ A) + z * (r ⬝ᵥ Pi.single 0 1) =
        specializedSchur φ y β β₀ (earlierPositive σ) (earlierNegative σ)
          (activeInterval δ) A U := by
      rw [hAsum, dotProduct_single_one, hrzero]
      rfl
    have hdet := adjoinPowerColumn_weighted_negative_det z d (c ∘ y) (c ∘ η)
      r (c ∘ A) (Pi.single 0 1) hyz S' hA' hB'
    simp only [Function.comp_apply] at hdet
    rw [hmatrix,hdet,hschur_eq]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero d hZ) hschur) hprod) hSE

end PaperVerification.Fermion.Newton
