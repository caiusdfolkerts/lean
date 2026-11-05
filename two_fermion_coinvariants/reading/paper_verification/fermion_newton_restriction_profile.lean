module

public import PaperVerification.FermionNewtonRegular
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Fin.Basic

/-!
# Removing the selected Newton coordinate

The smaller ring, its substitution map, and its multiplicities are literal.
The surviving heights and compatibility conditions are proved from the
paper's chosen deletion vertex, before restriction surjectivity is used.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

def removeCoordinate (q : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) F →ₐ[F] MvPolynomial (Fin n) F :=
  aeval (q.insertNth 0 X)

@[simp] theorem removeCoordinate_X_self (q : Fin (n + 1)) :
    removeCoordinate (F := F) q (X q) = 0 := by
  simp [removeCoordinate]

@[simp] theorem removeCoordinate_X_succAbove (q : Fin (n + 1)) (i : Fin n) :
    removeCoordinate (F := F) q (X (q.succAbove i)) = X i := by
  simp [removeCoordinate]

@[simp] theorem removeCoordinate_C (q : Fin (n + 1)) (a : F) :
    removeCoordinate q (C a) = C a := by simp [removeCoordinate]

theorem removeCoordinate_rename (q : Fin (n + 1)) (p : MvPolynomial (Fin n) F) :
    removeCoordinate q (rename q.succAbove p) = p := by
  have h : (removeCoordinate (F := F) q).comp (rename q.succAbove) = AlgHom.id F _ := by
    ext i
    simp
  exact AlgHom.congr_fun h p

theorem rename_removeCoordinate (q : Fin (n + 1)) (p : MvPolynomial (Fin (n + 1)) F) :
    rename q.succAbove (removeCoordinate q p) = coordinateRestriction q p := by
  have h : (rename (R := F) q.succAbove).comp (removeCoordinate q) =
      coordinateRestriction q := by
    ext i
    by_cases hi : i = q
    · subst i
      simp
    · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
      simp [coordinateRestriction, Fin.succAbove_ne]
  exact AlgHom.congr_fun h p

theorem removeCoordinate_eq_zero_iff (q : Fin (n + 1)) (p : MvPolynomial (Fin (n + 1)) F) :
    removeCoordinate q p = 0 ↔ X q ∣ p := by
  rw [← coordinateRestriction_eq_zero_iff]
  constructor
  · intro hp
    rw [← rename_removeCoordinate, hp, map_zero]
  · intro hp
    apply (rename_injective (R := F) q.succAbove Fin.succAbove_right_injective)
    simpa only [rename_removeCoordinate, map_zero] using hp

theorem removeCoordinate_homogeneous (q : Fin (n + 1))
    {p : MvPolynomial (Fin (n + 1)) F} {d : ℕ} (hp : p.IsHomogeneous d) :
    (removeCoordinate q p).IsHomogeneous d := by
  have hvar (i : Fin (n + 1)) : ((q.insertNth 0 X : Fin (n + 1) → MvPolynomial (Fin n) F) i).IsHomogeneous 1 := by
    by_cases hi : i = q
    · subst i
      simpa only [Fin.insertNth_apply_same] using isHomogeneous_zero (Fin n) F 1
    · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
      simpa only [Fin.insertNth_apply_succAbove] using isHomogeneous_X F j
  simpa only [removeCoordinate, one_mul] using hp.aeval (q.insertNth 0 X) hvar

def incidentSign (σ : Fin (n + 1) → ℤ) (q : Fin (n + 1)) (i : Fin n) : ℤ :=
  if q.succAbove i < q then σ (q.succAbove i) else σ q

def restrictedMultiplicity (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (q : Fin (n + 1)) (i : Fin n) : ℕ :=
  restrictAcrossSign (δ (q.succAbove i)) (incidentSign σ q i)

theorem restrictedMultiplicity_cast (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1) (hc : Compatible δ σ)
    (q : Fin (n + 1)) (hq : DeletionVertex δ σ q) (i : Fin n) :
    (restrictedMultiplicity δ σ q i : ℤ) = (δ (q.succAbove i) : ℤ) +
      if q < q.succAbove i then σ q else 0 := by
  rcases lt_or_gt_of_ne (Fin.succAbove_ne q i) with hi | hi
  · simp only [restrictedMultiplicity, incidentSign, if_pos hi,
      if_neg (not_lt_of_gt hi), add_zero]
    exact congrArg Nat.cast (restrictAcrossSign_before δ σ hc q hq _ hi)
  · simp only [restrictedMultiplicity, incidentSign, if_neg (not_lt_of_gt hi), if_pos hi]
    exact restrictAcrossSign_after δ σ hσ hc q hq _ hi

theorem profileHeight_restricted (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1) (hc : Compatible δ σ)
    (q : Fin (n + 1)) (hq : DeletionVertex δ σ q) (i : Fin n) :
    profileHeight (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove) i =
      profileHeight δ σ (q.succAbove i) := by
  have hsum : (∑ j ∈ Finset.univ.filter (fun j ↦ j < q.succAbove i), σ j) =
      (if q < q.succAbove i then σ q else 0) +
        ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j < i), σ (q.succAbove j) := by
    simp only [Finset.sum_filter]
    rw [Fin.sum_univ_succAbove _ q]
    simp only [Fin.succAbove_lt_succAbove_iff]
  simp only [profileHeight, Function.comp_apply,
    restrictedMultiplicity_cast δ σ hσ hc q hq i, hsum]
  ring

theorem Compatible.restricted (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1) (hc : Compatible δ σ)
    (q : Fin (n + 1)) (hq : DeletionVertex δ σ q) :
    Compatible (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove) := by
  have heq (i : Fin n) := restrictedMultiplicity_cast δ σ hσ hc q hq i
  constructor
  · intro i j hij hip
    have hij' := (Fin.strictMono_succAbove q) hij
    have hd := hc.1 _ _ hij' hip
    have hi := heq i
    have hj := heq j
    by_cases hqi : q < q.succAbove i
    · have hqj := hqi.trans hij'
      simp only [if_pos hqi, if_pos hqj] at hi hj
      omega
    · have hiq : q.succAbove i < q :=
        lt_of_le_of_ne (le_of_not_gt hqi) (Fin.succAbove_ne q i)
      simp only [if_neg hqi] at hi
      by_cases hqj : q < q.succAbove j
      · simp only [if_pos hqj] at hj
        have hdi := hc.1 _ _ hiq hip
        rcases hσ q with hn | hz | hp
        · omega
        · omega
        · have hdj := hq.2.2 (by omega) _ hqj
          have hpos := hq.1
          omega
      · simp only [if_neg hqj] at hj
        omega
  · intro i j hij hin
    have hij' := (Fin.strictMono_succAbove q) hij
    have hd := hc.2 _ _ hij' hin
    have hi := heq i
    have hj := heq j
    by_cases hqi : q < q.succAbove i
    · have hqj := hqi.trans hij'
      simp only [if_pos hqi, if_pos hqj] at hi hj
      omega
    · have hiq : q.succAbove i < q :=
        lt_of_le_of_ne (le_of_not_gt hqi) (Fin.succAbove_ne q i)
      have hdi := hq.2.1 _ hiq hin
      simp only [if_neg hqi, hdi, Nat.cast_zero, zero_add] at hi
      omega

theorem subset_weights_restricted (β : Fin (n + 1) → F)
    (hβ : ∀ U : Finset (Fin (n + 1)), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (q : Fin (n + 1)) :
    ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, (β ∘ q.succAbove) i) := by
  intro U hU
  have h := hβ (U.map q.succAboveEmb) (hU.map)
  simpa only [Finset.sum_map, Fin.coe_succAboveEmb, Function.comp_apply] using h

/-- The actual smaller-ring restriction has the already proved deletion
kernel; no surjectivity onto the smaller module is asserted here. -/
theorem removed_restriction_kernel (β : Fin (n + 1) → F)
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : Fin (n + 1) → MvPolynomial (Fin (n + 1)) F)
    (ha : a ∈ numeratorModule β δ σ) :
    (∀ i : Fin n, removeCoordinate q (a (q.succAbove i)) = 0) ↔
      ∃ b ∈ numeratorModule β (deletedMultiplicity δ q) σ, a = (X q : MvPolynomial (Fin (n + 1)) F) • b := by
  rw [← tangential_restriction_kernel_eq_deleted_multiples β δ σ q hq a ha]
  constructor
  · intro h i hi
    obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
    rw [← rename_removeCoordinate, h j, map_zero]
  · intro h i
    rw [removeCoordinate_eq_zero_iff, ← coordinateRestriction_eq_zero_iff]
    exact h _ (Fin.succAbove_ne q i)

end PaperVerification.Fermion.Newton
