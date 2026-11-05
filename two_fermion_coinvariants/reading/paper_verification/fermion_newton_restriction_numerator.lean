module

public import PaperVerification.FermionNewtonRestrictionProfile

/-!
# The actual numerator restriction map

Negative edges incident to the deleted vertex contribute one common
coordinate factor to every surviving numerator. Removing exactly that
factor gives the numerator conditions of the smaller Newton module.
The map and its kernel are constructed without assuming surjectivity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

def coordinateProduct (T : Finset (Fin n)) : MvPolynomial (Fin n) F := ∏ i ∈ T, X i

theorem coordinateProduct_ne_zero (T : Finset (Fin n)) : coordinateProduct (F := F) T ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact X_ne_zero i

theorem coordinate_pairwise_relPrime :
    Pairwise (fun i j : Fin n ↦ IsRelPrime (X i : MvPolynomial (Fin n) F) (X j)) := by
  intro i j hij
  apply (prime_X (R := F) (i := i)).irreducible.isRelPrime_iff_not_dvd.mpr
  simpa only [X_dvd_X] using hij

theorem coordinate_relPrime_product (T : Finset (Fin n)) (i : Fin n) (hi : i ∉ T) :
    IsRelPrime (X i : MvPolynomial (Fin n) F) (coordinateProduct T) := by
  apply IsRelPrime.prod_right
  intro j hj
  have hij : i ≠ j := fun h ↦ hi (h.symm ▸ hj)
  exact coordinate_pairwise_relPrime hij

theorem edge_relPrime_coordinateProduct (e : Edge n) (T : Finset (Fin n)) :
    IsRelPrime (edgeLinear (F := F) e) (coordinateProduct T) :=
  IsRelPrime.prod_right (fun i hi ↦ edgeLinear_relPrime_X e i)

def negativeNeighbours (σ : Fin (n + 1) → ℤ) (q : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ incidentSign σ q i = -1

@[simp] theorem mem_negativeNeighbours (σ : Fin (n + 1) → ℤ) (q : Fin (n + 1)) (i : Fin n) :
    i ∈ negativeNeighbours σ q ↔ incidentSign σ q i = -1 := by simp [negativeNeighbours]

theorem removeCoordinate_normal_zero
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : Fin (n + 1) → MvPolynomial (Fin (n + 1)) F)
    (ha : a ∈ numeratorModule β δ σ) : removeCoordinate q (a q) = 0 := by
  rw [removeCoordinate_eq_zero_iff]
  exact (dvd_pow_self (X q) hq.ne').trans (ha.1 q)

/-- Each incident negative coordinate divides every surviving restricted
numerator. The endpoint case uses the actual weighted normal relation. -/
theorem negativeNeighbour_dvd_removed_numerator
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : Fin (n + 1) → MvPolynomial (Fin (n + 1)) F)
    (ha : a ∈ numeratorModule β δ σ)
    (i : Fin n) (hi : i ∈ negativeNeighbours σ q) (k : Fin n) :
    X i ∣ removeCoordinate q (a (q.succAbove k)) := by
  have hnormal := removeCoordinate_normal_zero β δ σ q hq a ha
  have hunit : IsUnit (C (β (q.succAbove i)) : MvPolynomial (Fin n) F) :=
    (isUnit_iff_ne_zero.mpr (hβ _)).map MvPolynomial.C
  have hin : incidentSign σ q i = -1 := (mem_negativeNeighbours σ q i).mp hi
  by_cases heq : k = i
  · subst k
    apply hunit.isRelPrime_right.dvd_of_dvd_mul_left
    rcases lt_or_gt_of_ne (Fin.succAbove_ne q i) with hlt | hgt
    · let e : Edge (n + 1) := ⟨(q.succAbove i,q),hlt⟩
      have hsig : σ e.1.1 = -1 := by simpa only [incidentSign, if_pos hlt] using hin
      have h := map_dvd (removeCoordinate (F := F) q) (ha.2.2 e hsig).1
      simpa only [edgeLinear, e, map_sub, removeCoordinate_X_succAbove,
        removeCoordinate_X_self, sub_zero, map_add, map_mul, removeCoordinate_C,
        hnormal, mul_zero, add_zero] using h
    · let e : Edge (n + 1) := ⟨(q,q.succAbove i),hgt⟩
      have hsig : σ q = -1 := by
        simpa only [incidentSign, if_neg (not_lt_of_gt hgt)] using hin
      have h := map_dvd (removeCoordinate (F := F) q) (ha.2.2 e hsig).1
      simpa only [edgeLinear, e, map_sub, removeCoordinate_X_succAbove,
        removeCoordinate_X_self, zero_sub, map_add, map_mul, removeCoordinate_C,
        hnormal, mul_zero, zero_add, neg_dvd] using h
  · have hki : q.succAbove k ≠ q.succAbove i :=
      (Fin.strictMono_succAbove q).injective.ne heq
    rcases lt_or_gt_of_ne (Fin.succAbove_ne q i) with hlt | hgt
    · let e : Edge (n + 1) := ⟨(q.succAbove i,q),hlt⟩
      have hsig : σ e.1.1 = -1 := by simpa only [incidentSign, if_pos hlt] using hin
      have h := map_dvd (removeCoordinate (F := F) q)
        ((ha.2.2 e hsig).2 _ hki (Fin.succAbove_ne q k))
      simpa only [edgeLinear, e, map_sub, removeCoordinate_X_succAbove,
        removeCoordinate_X_self, sub_zero] using h
    · let e : Edge (n + 1) := ⟨(q,q.succAbove i),hgt⟩
      have hsig : σ q = -1 := by
        simpa only [incidentSign, if_neg (not_lt_of_gt hgt)] using hin
      have h := map_dvd (removeCoordinate (F := F) q)
        ((ha.2.2 e hsig).2 _ (Fin.succAbove_ne q k) hki)
      simpa only [edgeLinear, e, map_sub, removeCoordinate_X_succAbove,
        removeCoordinate_X_self, zero_sub, neg_dvd] using h

theorem negativeNeighbourProduct_dvd_removed_numerator
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : Fin (n + 1) → MvPolynomial (Fin (n + 1)) F)
    (ha : a ∈ numeratorModule β δ σ) (k : Fin n) :
    coordinateProduct (negativeNeighbours σ q) ∣ removeCoordinate q (a (q.succAbove k)) := by
  apply Finset.prod_dvd_of_isRelPrime (coordinate_pairwise_relPrime.set_pairwise _)
  intro i hi
  exact negativeNeighbour_dvd_removed_numerator β δ σ hβ q hq a ha i hi k

def restrictedNumerator
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : numeratorModule β δ σ) (k : Fin n) : MvPolynomial (Fin n) F :=
  Classical.choose (negativeNeighbourProduct_dvd_removed_numerator β δ σ hβ q hq a.val a.property k)

theorem restrictedNumerator_relation
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : numeratorModule β δ σ) (k : Fin n) :
    coordinateProduct (negativeNeighbours σ q) * restrictedNumerator β δ σ hβ q hq a k =
      removeCoordinate q (a.val (q.succAbove k)) :=
  (Classical.choose_spec
    (negativeNeighbourProduct_dvd_removed_numerator β δ σ hβ q hq a.val a.property k)).symm

/-- Cancelling the actual squarefree coordinate product reduces exactly
one exponent at its members and leaves all other exponents unchanged. -/
theorem coordinatePower_dvd_after_product (T : Finset (Fin n)) (i : Fin n) (d : ℕ)
    (a : MvPolynomial (Fin n) F) (ha : X i ^ d ∣ coordinateProduct T * a) :
    X i ^ (if i ∈ T then d - 1 else d) ∣ a := by
  classical
  by_cases hi : i ∈ T
  · rw [if_pos hi]
    cases d with
    | zero => simp
    | succ d =>
      have hT : coordinateProduct (F := F) T = X i * coordinateProduct (T.erase i) :=
        (Finset.mul_prod_erase T X hi).symm
      rw [hT, pow_succ', mul_assoc, mul_dvd_mul_iff_left (X_ne_zero i)] at ha
      simpa only [Nat.succ_sub_one] using
        ((coordinate_relPrime_product (F := F) (T.erase i) i (Finset.notMem_erase i T)).pow_left (m := d)).dvd_of_dvd_mul_left ha
  · rw [if_neg hi]
    exact ((coordinate_relPrime_product (F := F) T i hi).pow_left (m := d)).dvd_of_dvd_mul_left ha

theorem positiveNeighbour_dvd_removed_self
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (q : Fin (n + 1)) (hq : 0 < δ q) (a : numeratorModule β δ σ)
    (i : Fin n) (hi : incidentSign σ q i = 1) :
    X i ∣ removeCoordinate q (a.val (q.succAbove i)) := by
  have hnormal := removeCoordinate_normal_zero β δ σ q hq a.val a.property
  rcases lt_or_gt_of_ne (Fin.succAbove_ne q i) with hlt | hgt
  · let e : Edge (n + 1) := ⟨(q.succAbove i,q),hlt⟩
    have hsig : σ e.1.1 = 1 := by simpa only [incidentSign, if_pos hlt] using hi
    have h := map_dvd (removeCoordinate (F := F) q) (a.property.2.1 e hsig)
    simpa only [edgeLinear, e, map_sub, removeCoordinate_X_succAbove,
      removeCoordinate_X_self, sub_zero, hnormal] using h
  · let e : Edge (n + 1) := ⟨(q,q.succAbove i),hgt⟩
    have hsig : σ q = 1 := by simpa only [incidentSign, if_neg (not_lt_of_gt hgt)] using hi
    have h := map_dvd (removeCoordinate (F := F) q) (a.property.2.1 e hsig)
    simpa only [edgeLinear, e, map_sub, removeCoordinate_X_succAbove,
      removeCoordinate_X_self, zero_sub, hnormal, neg_dvd, dvd_neg] using h

theorem restrictedNumerator_coordinate_dvd
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : numeratorModule β δ σ) (i : Fin n) :
    X i ^ restrictedMultiplicity δ σ q i ∣ restrictedNumerator β δ σ hβ q hq a i := by
  have hi : X i ^ δ (q.succAbove i) ∣
      coordinateProduct (negativeNeighbours σ q) * restrictedNumerator β δ σ hβ q hq a i := by
    rw [restrictedNumerator_relation]
    simpa only [map_pow, removeCoordinate_X_succAbove] using
      map_dvd (removeCoordinate (F := F) q) (a.property.1 (q.succAbove i))
  by_cases hn : incidentSign σ q i = -1
  · have h := coordinatePower_dvd_after_product (negativeNeighbours σ q) i
      (δ (q.succAbove i)) _ hi
    simpa only [restrictedMultiplicity, restrictAcrossSign, if_pos hn,
      mem_negativeNeighbours, if_pos hn] using h
  · by_cases hp : incidentSign σ q i = 1
    · have hmax : X i ^ max (δ (q.succAbove i)) 1 ∣
          coordinateProduct (negativeNeighbours σ q) * restrictedNumerator β δ σ hβ q hq a i := by
        rcases le_total 1 (δ (q.succAbove i)) with hd | hd
        · simpa only [max_eq_left hd] using hi
        · rw [max_eq_right hd, pow_one, restrictedNumerator_relation]
          exact positiveNeighbour_dvd_removed_self β δ σ q hq a i hp
      have h := coordinatePower_dvd_after_product (negativeNeighbours σ q) i
        (max (δ (q.succAbove i)) 1) _ hmax
      simpa only [restrictedMultiplicity, restrictAcrossSign, if_neg hn, if_pos hp,
        mem_negativeNeighbours, if_neg hn] using h
    · have h := coordinatePower_dvd_after_product (negativeNeighbours σ q) i
        (δ (q.succAbove i)) _ hi
      simpa only [restrictedMultiplicity, restrictAcrossSign, if_neg hn, if_neg hp,
        mem_negativeNeighbours, if_neg hn] using h

theorem restrictedNumerator_mem
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : numeratorModule β δ σ) :
    restrictedNumerator β δ σ hβ q hq a ∈
      numeratorModule (β ∘ q.succAbove) (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove) := by
  refine ⟨restrictedNumerator_coordinate_dvd β δ σ hβ q hq a, ?_, ?_⟩
  · intro e he
    let E : Edge (n + 1) :=
      ⟨(q.succAbove e.1.1,q.succAbove e.1.2),(Fin.strictMono_succAbove q) e.2⟩
    have h := map_dvd (removeCoordinate (F := F) q) (a.property.2.1 E he)
    have hr : removeCoordinate q (edgeLinear (F := F) E) = edgeLinear e := by
      simp only [edgeLinear, E, map_sub, removeCoordinate_X_succAbove]
    rw [hr, map_sub, ← restrictedNumerator_relation β δ σ hβ q hq a, ← restrictedNumerator_relation β δ σ hβ q hq a,
      ← mul_sub] at h
    exact (edge_relPrime_coordinateProduct e (negativeNeighbours σ q)).dvd_of_dvd_mul_left h
  · intro e he
    let E : Edge (n + 1) :=
      ⟨(q.succAbove e.1.1,q.succAbove e.1.2),(Fin.strictMono_succAbove q) e.2⟩
    have hr : removeCoordinate q (edgeLinear (F := F) E) = edgeLinear e := by
      simp only [edgeLinear, E, map_sub, removeCoordinate_X_succAbove]
    refine ⟨?_, ?_⟩
    · have h := map_dvd (removeCoordinate (F := F) q) (a.property.2.2 E he).1
      rw [hr, map_add, map_mul, map_mul, removeCoordinate_C, removeCoordinate_C,
        ← restrictedNumerator_relation β δ σ hβ q hq a, ← restrictedNumerator_relation β δ σ hβ q hq a] at h
      apply (edge_relPrime_coordinateProduct e (negativeNeighbours σ q)).dvd_of_dvd_mul_left
      convert h using 1 <;> dsimp only [Function.comp_apply, E] <;> ring
    · intro k hki hkj
      have h := map_dvd (removeCoordinate (F := F) q) ((a.property.2.2 E he).2
        (q.succAbove k) ((Fin.strictMono_succAbove q).injective.ne hki)
        ((Fin.strictMono_succAbove q).injective.ne hkj))
      rw [hr, ← restrictedNumerator_relation β δ σ hβ q hq a] at h
      exact (edge_relPrime_coordinateProduct e (negativeNeighbours σ q)).dvd_of_dvd_mul_left h

end PaperVerification.Fermion.Newton
