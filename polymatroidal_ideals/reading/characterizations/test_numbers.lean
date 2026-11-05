import Characterizations.CountingBounds

/-! # The literal minimum numbers N(n) and N(n,d) -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid

variable (k : Type*) [CommSemiring k] [Nontrivial k]

theorem exists_degree_test_size (n d : ℕ) :
    ∃ m, ∃ F : Finset (VariableOrder (Fin n)),
      DegreeOrderTests k d (F : Set (VariableOrder (Fin n))) ∧ F.card = m := by
  refine ⟨Fintype.card (VariableOrder (Fin n)),univ,?_,card_univ⟩
  intro B hB hL
  exact (polymatroidal_iff_universal_revlex hB).mpr (fun o => hL o (mem_univ _))

def orderTestNumber (n d : ℕ) : ℕ := Nat.find (exists_degree_test_size k n d)

theorem orderTestNumber_attained (n d : ℕ) :
    ∃ F : Finset (VariableOrder (Fin n)),
      DegreeOrderTests k d (F : Set (VariableOrder (Fin n))) ∧ F.card = orderTestNumber k n d :=
  Nat.find_spec (exists_degree_test_size k n d)

theorem orderTestNumber_le_card {n d : ℕ} (F : Finset (VariableOrder (Fin n)))
    (hF : DegreeOrderTests k d (F : Set (VariableOrder (Fin n)))) : orderTestNumber k n d ≤ F.card :=
  Nat.find_min' (exists_degree_test_size k n d) ⟨F,hF,rfl⟩

theorem exists_universal_test_size (n : ℕ) :
    ∃ m, ∃ F : Finset (VariableOrder (Fin n)),
      UniversalOrderTests k (F : Set (VariableOrder (Fin n))) ∧ F.card = m := by
  refine ⟨Fintype.card (VariableOrder (Fin n)),univ,?_,card_univ⟩
  intro B d hB hL
  exact (polymatroidal_iff_universal_revlex hB).mpr (fun o => hL o (mem_univ _))

def universalTestNumber (n : ℕ) : ℕ := Nat.find (exists_universal_test_size k n)

theorem universalTestNumber_attained (n : ℕ) :
    ∃ F : Finset (VariableOrder (Fin n)), UniversalOrderTests k (F : Set (VariableOrder (Fin n))) ∧
      F.card = universalTestNumber k n := Nat.find_spec (exists_universal_test_size k n)

theorem universalTestNumber_le_card {n : ℕ} (F : Finset (VariableOrder (Fin n)))
    (hF : UniversalOrderTests k (F : Set (VariableOrder (Fin n)))) : universalTestNumber k n ≤ F.card :=
  Nat.find_min' (exists_universal_test_size k n) ⟨F,hF,rfl⟩

theorem universalTestNumber_ge_four {n : ℕ} (hn : 4 ≤ n) :
    universalTestNumber k n = 3*n.choose 3 := by
  obtain ⟨F,hF,hc⟩ := universalTestNumber_attained k n
  have hlo := universalOrderTests_card_lower_bound (V := Fin n) (by simpa) F hF
  obtain ⟨G,hG,hGc⟩ := (exact_universal_test_number (k := k) (V := Fin n) (by simpa using hn)).1
  have hhi := universalTestNumber_le_card k G hG
  have hformula := pointedTriple_count_formula n (by omega)
  simp only [Fintype.card_fin] at hlo hGc
  omega

theorem universalTestNumber_one : universalTestNumber k 1 = 0 := by
  have h := universalTestNumber_le_card k (∅ : Finset (VariableOrder (Fin 1)))
    (by simpa using (empty_tests_of_small_dimension (k := k) (V := Fin 1) (by simp)))
  simpa using h

theorem universalTestNumber_two : universalTestNumber k 2 = 1 := by
  let o : VariableOrder (Fin 2) := Fintype.equivFin _
  have hhi := universalTestNumber_le_card k ({o} : Finset (VariableOrder (Fin 2)))
    (nonempty_order_family_card_two (by simp) _ ⟨o,by simp⟩)
  obtain ⟨F,hF,hc⟩ := universalTestNumber_attained k 2
  have hne := (degree_tests_card_two_iff_nonempty (k := k) (V := Fin 2) (by simp) 2 (by omega) _).mp
    (fun B hB hL => hF B 2 hB hL)
  have hpos : 0 < F.card := card_pos.mpr hne
  simp only [card_singleton] at hhi
  omega

theorem universalTestNumber_three : universalTestNumber k 3 = 6 := by
  obtain ⟨F,hF,hc⟩ := universalTestNumber_attained k 3
  have hh := degree_test_number_three (k := k) (V := Fin 3) (by simp) 2 (by omega) F
    (fun B hB hL => hF B 2 hB hL)
  omega

theorem orderTestNumber_small_degree {n d : ℕ} (hd : d ≤ 1) : orderTestNumber k n d = 0 := by
  have hh := orderTestNumber_le_card k (d := d) (∅ : Finset (VariableOrder (Fin n)))
    (by simpa using (empty_tests_of_small_degree (k := k) (V := Fin n) d hd))
  simpa using hh

theorem orderTestNumber_small_dimension {n d : ℕ} (hn : n ≤ 1) : orderTestNumber k n d = 0 := by
  have hh := orderTestNumber_le_card k (d := d) (∅ : Finset (VariableOrder (Fin n)))
    (fun B hB _ => equigenerated_polymatroidal_of_card_le_one hB (by simpa using hn))
  simpa using hh

theorem orderTestNumber_two {d : ℕ} (hd : 2 ≤ d) : orderTestNumber k 2 d = 1 := by
  let o : VariableOrder (Fin 2) := Fintype.equivFin _
  have htest : DegreeOrderTests k d (({o} : Finset (VariableOrder (Fin 2))) : Set _) :=
    (degree_tests_card_two_iff_nonempty (by simp) d hd _).mpr ⟨o,by simp⟩
  have hhi := orderTestNumber_le_card k ({o} : Finset (VariableOrder (Fin 2))) htest
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k 2 d
  have hne := (degree_tests_card_two_iff_nonempty (by simp) d hd _).mp hF
  have hpos : 0 < F.card := card_pos.mpr hne
  simp only [card_singleton] at hhi
  omega

theorem orderTestNumber_three {d : ℕ} (hd : 2 ≤ d) : orderTestNumber k 3 d = 6 := by
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k 3 d
  have hh := degree_test_number_three (k := k) (V := Fin 3) (by simp) d hd F hF
  omega

theorem orderTestNumber_high_degree {n d : ℕ} (hn : 4 ≤ n) (hd : n-2 ≤ d) :
    orderTestNumber k n d = 3*n.choose 3 := by
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k n d
  have hlo := (exact_high_degree_test_number (k := k) (V := Fin n) (by simpa using hn) d (by simpa using hd)).2 F hF
  obtain ⟨G,hG,hGc⟩ := (exact_high_degree_test_number (k := k) (V := Fin n) (by simpa using hn) d (by simpa using hd)).1
  have hhi := orderTestNumber_le_card k G hG
  have hformula := pointedTriple_count_formula n (by omega)
  simp only [Fintype.card_fin] at hlo hGc
  omega

theorem orderTestNumber_logarithmic_upper {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) (hdn : d ≤ n-2) :
    orderTestNumber k n d ≤ ⌈(testProbability d)⁻¹ *
      (Real.log (n * (n-1).choose 2 * (n-3).choose (d-1)) + 1)⌉₊ := by
  obtain ⟨F,hF,hc⟩ := exists_degree_test_family_logarithmic (k := k) (V := Fin n) d hd
    (by simpa using hn) (by simpa using hdn)
  exact (orderTestNumber_le_card k F hF).trans (by simpa using hc)

theorem orderTestNumber_counting_lower {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) (hdn : d ≤ n-2) :
    3*(d+2).choose 3 ≤ orderTestNumber k n d := by
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k n d
  rw [←hc]
  exact degree_test_number_lower_bound d hd (by simpa using hn) (by simpa using hdn) F hF

theorem orderTestNumber_signature_bound {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) :
    n-1 ≤ (orderTestNumber k n d).choose (orderTestNumber k n d / 2) := by
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k n d
  simpa [hc] using degree_test_signature_bound d hd (V := Fin n) (by simpa using hn) F hF

end Characterizations
