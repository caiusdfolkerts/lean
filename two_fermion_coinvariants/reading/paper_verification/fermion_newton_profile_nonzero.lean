module

public import PaperVerification.FermionNewtonProfileNegative

/-!
# Nonvanishing of the full compatible-profile Newton determinant

Constant profiles follow from the simultaneous all-one induction. For a
nonconstant profile, the suffix determinant is supplied by induction and the
initial block by the constant-profile result on its independent subset of
variables. This proves nonvanishing of the actual columns for all compatible
profiles; no bounded configuration or extra positivity hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators Matrix

variable (F : Type*) [Field F]

theorem profileGeneric_det_ne_zero (n : ℕ)
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (β : Fin n → F)
    (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    (profileNewtonMatrix δ σ (successiveNode F n) (successiveBaseMap F n ∘ β)).det ≠ 0 := by
  induction n with
  | zero => simp only [Matrix.det_isEmpty, ne_eq, one_ne_zero, not_false_eq_true]
  | succ n ih =>
      by_cases hconstant : ∀ i, δ i = δ 0
      · have hδ : δ = fun _ ↦ δ 0 := funext hconstant
        rw [hδ]
        exact constantProfileGeneric_det_ne_zero F (n + 1) (δ 0) σ β hσ hβ
      let δs : Fin n → ℕ := δ ∘ Fin.succ
      let σs : Fin n → ℤ := σ ∘ Fin.succ
      let βs : Fin n → F := β ∘ Fin.succ
      let y := successiveNode F n
      let γ : Fin n → SuccessiveField F n := successiveBaseMap F n ∘ βs
      let c := suffixCoefficientMap F n
      let φ := newVariablePolynomialMap F n
      let x := successiveNode F (n + 1)
      let γfull : Fin (n + 1) → SuccessiveField F (n + 1) := successiveBaseMap F (n + 1) ∘ β
      have hcs : Compatible δs σs := by
        constructor
        · intro i j hij hi
          exact hc.1 i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij) hi
        · intro i j hij hi
          exact hc.2 i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij) hi
      have hσs : ∀ i, σs i = -1 ∨ σs i = 0 ∨ σs i = 1 := fun i ↦ hσ i.succ
      have hβs : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, βs i) := by
        intro U hU
        have h := hβ (U.map (Fin.succEmb n)) (hU.map)
        simpa only [Finset.sum_map, Fin.coe_succEmb, βs, Function.comp_apply] using h
      have hdet := ih δs σs βs hcs hσs hβs
      change (profileNewtonMatrix δs σs y γ).det ≠ 0 at hdet
      have hxsucc : x ∘ Fin.succ = c ∘ y := by
        funext i
        exact successiveNode_succ F n i
      have hγsucc : γfull ∘ Fin.succ = c ∘ γ := by
        funext i
        exact successiveBaseMap_succ F n (β i.succ)
      have hSmap : profileNewtonMatrix δs σs (x ∘ Fin.succ) (γfull ∘ Fin.succ) =
          (profileNewtonMatrix δs σs y γ).map c := by
        rw [hxsucc, hγsucc, profileNewtonMatrix_map]
      have hS : (profileNewtonMatrix δs σs (x ∘ Fin.succ) (γfull ∘ Fin.succ)).det ≠ 0 := by
        rw [hSmap, matrix_map_det]
        exact (map_ne_zero c).mpr hdet
      change (profileNewtonMatrix δ σ x γfull).det ≠ 0
      rcases hσ 0 with hminus | hnonnegative
      · have hmin : ∀ i, δ 0 ≤ δs i := fun i ↦ hc.2 0 i.succ (Fin.succ_pos _) hminus
        have hstrict : ∃ i, δ 0 < δs i := by
          by_contra hn
          apply hconstant
          intro i
          refine Fin.cases rfl (fun j ↦ ?_) i
          exact le_antisymm (Nat.le_of_not_gt (fun hj ↦ hn ⟨j, hj⟩)) (hmin j)
        obtain ⟨m, hm, hδ, hjump⟩ := exists_initial_constant_block δs (δ 0) hmin hstrict
        cases n with
        | zero => omega
        | succ n =>
            let e := prefixEmbedding hm.le
            let ρ : MvPolynomial (Fin m) F →+* SuccessiveField F (n + 1) :=
              (successiveCoordinateMap F (n + 1)).comp (MvPolynomial.rename e).toRingHom
            have hρ : Function.Injective ρ :=
              (successiveCoordinateMap_injective F (n + 1)).comp
                (MvPolynomial.rename_injective e e.injective)
            have hβp : ∀ U : Finset (Fin m), U.Nonempty →
                IsUnit (∑ i ∈ U, βs (e i)) := by
              intro U hU
              have h := hβs (U.map e) (hU.map)
              simpa only [Finset.sum_map] using h
            have hblock : ((profileNewtonMatrix δs σs y γ).submatrix e e).det ≠ 0 := by
              rw [profileNewtonMatrix_prefix_block hm δs (δ 0) σs y γ hδ hjump]
              have h := constantProfile_det_of_injective_polynomial_map ρ hρ (δ 0)
                (σs ∘ e) (βs ∘ e) (fun i ↦ hσs (e i)) hβp
              have hρX (i : Fin m) : ρ (MvPolynomial.X i) = y (e i) := by
                change successiveCoordinateMap F (n + 1)
                  (MvPolynomial.rename e (MvPolynomial.X i)) = _
                rw [MvPolynomial.rename_X]
                rfl
              have hρC (i : Fin m) : ρ (MvPolynomial.C (βs (e i))) = γ (e i) := by
                change successiveCoordinateMap F (n + 1)
                  (MvPolynomial.rename e (MvPolynomial.C (βs (e i)))) = _
                rw [MvPolynomial.rename_C]
                rfl
              simpa only [hρX, hρC, Function.comp_def,e] using h
            have hweights : ∀ U : Finset (Fin (n + 2)), U.Nonempty →
                IsUnit (∑ i ∈ U, (Fin.cases (successiveBaseMap F (n + 1) (β 0)) γ i : SuccessiveField F (n + 1))) := by
              intro U hU
              have he : Fin.cases (successiveBaseMap F (n + 1) (β 0)) γ =
                  successiveBaseMap F (n + 1) ∘ β := by
                funext i
                exact Fin.cases rfl (fun j ↦ rfl) i
              rw [he]
              simp only [Function.comp_apply]
              rw [← map_sum]
              exact (hβ U hU).map (successiveBaseMap F (n + 1))
            have hmnew := profile_negative_step_det_ne_zero φ
              (newVariablePolynomialMap_injective F (n + 1)) δs σs (δ 0) y γ
              (successiveBaseMap F (n + 1) (β 0)) hm hmin hδ hjump
              (compatible_prefix_no_positive hm δs (δ 0) σs hcs hδ hjump)
              hweights hdet hblock
            have hδcase : δ = Fin.cases (δ 0) δs := by
              funext i
              exact Fin.cases rfl (fun j ↦ rfl) i
            have hσcase : σ = Fin.cases (-1) σs := by
              funext i
              exact Fin.cases hminus (fun j ↦ rfl) i
            have hxcase : x = Fin.cases (φ X) (fun i ↦ φ (C (y i))) := by
              funext i
              exact Fin.cases (successiveNode_zero F (n + 1))
                (fun j ↦ successiveNode_succ F (n + 1) j) i
            have hγcase : γfull =
                Fin.cases (φ (C (successiveBaseMap F (n + 1) (β 0))))
                  (fun i ↦ φ (C (γ i))) := by
              funext i
              exact Fin.cases (successiveBaseMap_succ F (n + 1) (β 0))
                (fun j ↦ successiveBaseMap_succ F (n + 1) (β j.succ)) i
            rw [hδcase, hσcase, hxcase, hγcase]
            exact hmnew
      · exact profileNewtonMatrix_nonnegative_det_ne_zero δ σ x γfull hnonnegative
          (successiveNode_injective F (n + 1)) (successiveNode_ne_zero F (n + 1) 0) hS

/-- Nonzero determinant of the paper's literal columns, for every compatible
nonnegative multiplicity profile and every allowed sign word. -/
theorem newtonColumn_det_ne_zero (n : ℕ)
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (β : Fin n → F)
    (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Matrix.det (fun k i : Fin n ↦ newtonColumn β δ σ i k) ≠ 0 := by
  have h := profileGeneric_det_ne_zero F n δ σ β hc hσ hβ
  simp_rw [newtonColumn_eq_profileNewtonMatrix F]
  change (profileNewtonMatrix δ σ (rationalNode (F := F))
    (fun i ↦ algebraMap F (RationalFunctions (F := F)) (β i))).det ≠ 0
  intro hz
  apply h
  have he := congrArg (successiveFractionMap F n) hz
  rw [map_zero, ← matrix_map_det, profileNewtonMatrix_map] at he
  simpa only [Function.comp_def, successiveFractionMap_node, successiveFractionMap_scalar] using he

end PaperVerification.Fermion.Newton
