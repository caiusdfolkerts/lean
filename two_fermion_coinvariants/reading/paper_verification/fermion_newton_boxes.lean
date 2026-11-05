module

public import PaperVerification.FermionNewtonBoxSpanning

/-!
# The full Newton rectangular basis

Deletion lowers one positive height; restriction removes that height and
preserves every other one.  These operations give a terminating induction
on the number of variables and then the sum of the multiplicities.  The
independent complete-intersection length calculation turns its spanning
rectangle into a basis of the actual contraction quotient.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

theorem profileHeight_deleted (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (q : Fin n) (hq : 0 < δ q) (i : Fin n) :
    profileHeight (deletedMultiplicity δ q) σ i =
      profileHeight δ σ i - if i = q then 1 else 0 := by
  by_cases hi : i = q
  · subst i
    simp only [profileHeight,deletedMultiplicity_self,if_pos rfl]
    rw [Int.natCast_sub (by omega : 1 ≤ δ q)]
    simp only [Nat.cast_one, if_true]
    ring
  · simp only [profileHeight,deletedMultiplicity_ne δ q i hi,if_neg hi,sub_zero]

theorem heightDegree_pos
    (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (i : Fin n) (hi : 0 < profileHeight δ σ i) :
    0 < heightDegree δ σ i := by
  have h := heightDegree_cast δ σ hσ i (le_of_lt hi)
  omega

theorem heightDegree_deleted
    (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hheight : ∀ i, 0 < profileHeight δ σ i) (q : Fin n) (hq : 0 < δ q) :
    heightDegree (deletedMultiplicity δ q) σ =
      Function.update (heightDegree δ σ) q (heightDegree δ σ q - 1) := by
  classical
  funext i
  by_cases hi : i = q
  · subst i
    have h0 := hheight q
    have he := profileHeight_deleted δ σ q hq q
    simp only [if_pos rfl,if_true] at he
    have hp : 0 ≤ profileHeight (deletedMultiplicity δ q) σ q := by omega
    have hd := heightDegree_cast (deletedMultiplicity δ q) σ hσ q hp
    have hs := heightDegree_cast δ σ hσ q (le_of_lt h0)
    rw [Function.update_self]
    apply Int.ofNat_inj.mp
    rw [hd, Int.natCast_sub (Nat.succ_le_iff.mpr (heightDegree_pos δ σ hσ q h0)), hs]
    simpa only [Nat.cast_one,if_true] using he
  · simp only [Function.update_of_ne hi,heightDegree,deletedMultiplicity_ne δ q i hi]

theorem heightDegree_restricted
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1) (hc : Compatible δ σ)
    (hheight : ∀ i, 0 < profileHeight δ σ i)
    (q : Fin (n + 1)) (hq : DeletionVertex δ σ q) :
    heightDegree (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove) =
      heightDegree δ σ ∘ q.succAbove := by
  funext i
  have he := profileHeight_restricted δ σ hσ hc q hq i
  have hh := hheight (q.succAbove i)
  have hr : 0 ≤ profileHeight (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove) i := by
    rw [he]
    exact le_of_lt hh
  have hd := heightDegree_cast (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove)
    (fun j ↦ hσ (q.succAbove j)) i hr
  have hs := heightDegree_cast δ σ hσ (q.succAbove i) (le_of_lt hh)
  dsimp only [Function.comp_apply]
  omega

theorem sum_deletedMultiplicity_lt (δ : Fin n → ℕ) (q : Fin n) (hq : 0 < δ q) :
    ∑ i, deletedMultiplicity δ q i < ∑ i, δ i := by
  classical
  apply Finset.sum_lt_sum
  · intro i hi
    by_cases he : i = q
    · subst i
      rw [deletedMultiplicity_self]
      omega
    · rw [deletedMultiplicity_ne δ q i he]
  · refine ⟨q,Finset.mem_univ q,?_⟩
    rw [deletedMultiplicity_self]
    omega

/-- Proposition 2.3's entire rectangle spans, for every compatible
multiplicity profile and every permitted sign word with positive heights. -/
theorem contraction_box_spans
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight δ σ i) :
    BoxSpans (contractionIdeal β δ σ) (heightDegree δ σ) := by
  classical
  induction n with
  | zero => exact boxSpans_zero_variables _ _
  | succ n ihn =>
      have hrec : ∀ d : ℕ, ∀ δ : Fin (n + 1) → ℕ, (∑ i, δ i) = d →
          Compatible δ σ → (∀ i, 0 < profileHeight δ σ i) →
          BoxSpans (contractionIdeal β δ σ) (heightDegree δ σ) := by
        intro d
        induction d using Nat.strong_induction_on with
        | _ d ih =>
            intro δ hsum hc hheight
            have hδ : ∃ i, 0 < δ i := by
              refine ⟨0,?_⟩
              have hh := hheight 0
              simp only [profileHeight,Fin.not_lt_zero,Finset.filter_false,
                Finset.sum_empty,add_zero] at hh
              exact_mod_cast hh
            obtain ⟨q,hq⟩ := exists_deletionVertex δ σ hδ
            have hc' := Compatible.restricted δ σ hσ hc q hq
            have hh' (i : Fin n) :
                0 < profileHeight (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove) i := by
              rw [profileHeight_restricted δ σ hσ hc q hq]
              exact hheight (q.succAbove i)
            have hL := ihn (β ∘ q.succAbove) (restrictedMultiplicity δ σ q)
              (σ ∘ q.succAbove) hc' (fun i ↦ hσ (q.succAbove i))
              (subset_weights_restricted β hβ q) hh'
            rw [heightDegree_restricted δ σ hσ hc hheight q hq] at hL
            apply boxSpans_of_deletion (contractionIdeal β δ σ)
              (contractionIdeal β (deletedMultiplicity δ q) σ)
              (contractionIdeal (β ∘ q.succAbove) (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove))
              (heightDegree δ σ) q (heightDegree_pos δ σ hσ q (hheight q))
              (map_contractionIdeal_removeCoordinate β δ σ hc hσ hβ q hq)
              (fun p hp ↦ mul_deleted_contraction_mem β δ σ q hq.1 hp) hL
            have hcd := Compatible.deleted δ σ hc q hq
            by_cases hz : profileHeight δ σ q = 1
            · left
              have hd := profileHeight_deleted δ σ q hq.1 q
              rw [hz,if_pos rfl,sub_self] at hd
              have he := profileHeight_eq_card_difference (deletedMultiplicity δ q) σ hσ q
              apply contractionIdeal_eq_top_of_zero_height β (deletedMultiplicity δ q) σ hcd hβ q
              omega
            · right
              have hhd (i : Fin (n + 1)) : 0 < profileHeight (deletedMultiplicity δ q) σ i := by
                rw [profileHeight_deleted δ σ q hq.1]
                by_cases hi : i = q
                · subst i
                  simp only [if_pos rfl]
                  have hh := hheight q
                  omega
                · simp only [if_neg hi,sub_zero]
                  exact hheight i
              have hlt : ∑ i, deletedMultiplicity δ q i < d := by
                rw [← hsum]
                exact sum_deletedMultiplicity_lt δ q hq.1
              have hspan := ih (∑ i, deletedMultiplicity δ q i) hlt
                (deletedMultiplicity δ q) rfl hcd hhd
              simpa only [heightDegree_deleted δ σ hσ hheight q hq.1] using hspan
      exact hrec _ δ rfl hc hheight

/-- The actual quotient basis of Proposition 2.3.  All bounds are the
signed heights of the paper and every basis vector is its monomial class. -/
def contractionRectangleBasis
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight δ σ i) :
    Module.Basis (RectangleIndex (heightDegree δ σ)) F (P (F := F) (n := n) ⧸ contractionIdeal β δ σ) := by
  letI := contraction_quotient_finite β δ σ hβ
  exact rectangleQuotientBasis (contractionIdeal β δ σ) (heightDegree δ σ)
    (contraction_box_spans β δ σ hc hσ hβ hheight)
    (contraction_quotient_finrank β δ σ hc hσ hβ hheight)

@[simp] theorem contractionRectangleBasis_apply
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight δ σ i) (a : RectangleIndex (heightDegree δ σ)) :
    contractionRectangleBasis β δ σ hc hσ hβ hheight a =
      Ideal.Quotient.mk (contractionIdeal β δ σ) (monomial a.val 1) := by
  letI := contraction_quotient_finite β δ σ hβ
  exact rectangleQuotientBasis_apply (contractionIdeal β δ σ) (heightDegree δ σ)
    (contraction_box_spans β δ σ hc hσ hβ hheight)
    (contraction_quotient_finrank β δ σ hc hσ hβ hheight) a

end PaperVerification.Fermion.Newton
