import CommAlg.Polymatroid.RankIdeal

/-! # Integral submodular / supermodular sandwich

An elementary coordinate-elimination proof, including integrality, supplies
the integer decomposition theorem needed for products of polymatroid ideals.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [DecidableEq V]

theorem integer_sandwich_on (E : Finset V) :
    ∀ (p q : Finset V → ℤ), p ∅ = 0 → q ∅ = 0 →
      (∀ A, A ⊆ E → ∀ B, B ⊆ E → p A + p B ≤ p (A ∪ B) + p (A ∩ B)) →
      (∀ A, A ⊆ E → ∀ B, B ⊆ E → q (A ∪ B) + q (A ∩ B) ≤ q A + q B) →
      (∀ A, A ⊆ E → p A ≤ q A) →
      ∃ b : V → ℤ, (∀ i, i ∉ E → b i = 0) ∧
        ∀ A, A ⊆ E → p A ≤ ∑ i ∈ A, b i ∧ (∑ i ∈ A, b i) ≤ q A := by
  induction E using Finset.induction_on with
  | empty =>
    intro p q hp0 hq0 hp hq hpq
    refine ⟨fun _ => 0, by simp, ?_⟩
    intro A hA
    have he : A = ∅ := Finset.subset_empty.mp hA
    simp [he, hp0, hq0]
  | @insert i E hi ih =>
    intro p q hp0 hq0 hp hq hpq
    have hpow : E.powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
    let t : ℤ := E.powerset.sup' hpow (fun A => p (insert i A) - q A)
    have htL : ∀ A, A ⊆ E → p (insert i A) - q A ≤ t := by
      intro A hA
      exact Finset.le_sup' (fun A => p (insert i A) - q A) (Finset.mem_powerset.mpr hA)
    have htR : ∀ B, B ⊆ E → t ≤ q (insert i B) - p B := by
      intro B hB
      apply Finset.sup'_le hpow _
      intro A hA
      have hA := Finset.mem_powerset.mp hA
      have hiA : i ∉ A := fun h => hi (hA h)
      have hiB : i ∉ B := fun h => hi (hB h)
      have hps := hp (insert i A) (Finset.insert_subset_insert i hA) B
        (hB.trans (Finset.subset_insert _ _))
      have hqs := hq A (hA.trans (Finset.subset_insert _ _)) (insert i B)
        (Finset.insert_subset_insert i hB)
      have hu := hpq (insert i (A ∪ B)) (Finset.insert_subset_insert i (Finset.union_subset hA hB))
      have hin := hpq (A ∩ B) ((Finset.inter_subset_left.trans hA).trans (Finset.subset_insert _ _))
      simp only [Finset.insert_union, Finset.union_insert,
        Finset.insert_inter_of_notMem hiB, Finset.inter_insert_of_notMem hiA] at hps hqs
      omega
    have htiL := htL ∅ (Finset.empty_subset E)
    have htiR := htR ∅ (Finset.empty_subset E)
    simp only [hp0, hq0, sub_zero] at htiL htiR
    let p' : Finset V → ℤ := fun A => max (p A) (p (insert i A) - t)
    let q' : Finset V → ℤ := fun A => min (q A) (q (insert i A) - t)
    have hp0' : p' ∅ = 0 := by
      change max (p ∅) (p (insert i ∅) - t) = 0
      rw [hp0]
      exact max_eq_left (by omega)
    have hq0' : q' ∅ = 0 := by
      change min (q ∅) (q (insert i ∅) - t) = 0
      rw [hq0]
      exact min_eq_left (by omega)
    have hp' : ∀ A, A ⊆ E → ∀ B, B ⊆ E →
        p' A + p' B ≤ p' (A ∪ B) + p' (A ∩ B) := by
      intro A hA B hB
      have hiA : i ∉ A := fun h => hi (hA h)
      have hiB : i ∉ B := fun h => hi (hB h)
      have hAE : A ⊆ insert i E := hA.trans (Finset.subset_insert _ _)
      have hBE : B ⊆ insert i E := hB.trans (Finset.subset_insert _ _)
      have hAiE := Finset.insert_subset_insert (a := i) hA
      have hBiE := Finset.insert_subset_insert (a := i) hB
      have h00 := hp A hAE B hBE
      have h10 := hp (insert i A) hAiE B hBE
      have h01 := hp A hAE (insert i B) hBiE
      have h11 := hp (insert i A) hAiE (insert i B) hBiE
      have hii : insert i A ∩ insert i B = insert i (A ∩ B) := by ext x; simp; tauto
      simp only [Finset.insert_union, Finset.union_insert, Finset.insert_idem, hii,
        Finset.insert_inter_of_notMem hiB, Finset.inter_insert_of_notMem hiA] at h10 h01 h11
      dsimp [p']
      omega
    have hq' : ∀ A, A ⊆ E → ∀ B, B ⊆ E →
        q' (A ∪ B) + q' (A ∩ B) ≤ q' A + q' B := by
      intro A hA B hB
      have hiA : i ∉ A := fun h => hi (hA h)
      have hiB : i ∉ B := fun h => hi (hB h)
      have hAE : A ⊆ insert i E := hA.trans (Finset.subset_insert _ _)
      have hBE : B ⊆ insert i E := hB.trans (Finset.subset_insert _ _)
      have hAiE := Finset.insert_subset_insert (a := i) hA
      have hBiE := Finset.insert_subset_insert (a := i) hB
      have h00 := hq A hAE B hBE
      have h10 := hq (insert i A) hAiE B hBE
      have h01 := hq A hAE (insert i B) hBiE
      have h11 := hq (insert i A) hAiE (insert i B) hBiE
      have hii : insert i A ∩ insert i B = insert i (A ∩ B) := by ext x; simp; tauto
      simp only [Finset.insert_union, Finset.union_insert, Finset.insert_idem, hii,
        Finset.insert_inter_of_notMem hiB, Finset.inter_insert_of_notMem hiA] at h10 h01 h11
      dsimp [q']
      omega
    have hpq' : ∀ A, A ⊆ E → p' A ≤ q' A := by
      intro A hA
      have h0 := hpq A (hA.trans (Finset.subset_insert _ _))
      have h1 := hpq (insert i A) (Finset.insert_subset_insert i hA)
      have hL := htL A hA
      have hR := htR A hA
      dsimp [p', q']
      omega
    obtain ⟨b, hb0, hb⟩ := ih p' q' hp0' hq0' hp' hq' hpq'
    let b' := Function.update b i t
    have hsum : ∀ A, i ∉ A → (∑ j ∈ A, b' j) = ∑ j ∈ A, b j := by
      intro A hiA
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := fun he => hiA (he ▸ hj)
      simp [b', Function.update_of_ne hji]
    refine ⟨b', ?_, ?_⟩
    · intro j hj
      have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
      have hjE : j ∉ E := fun h => hj (Finset.mem_insert_of_mem h)
      simp [b', Function.update_of_ne hji, hb0 j hjE]
    · intro A hA
      by_cases hiA : i ∈ A
      · let A' := A.erase i
        have hA'E : A' ⊆ E := by
          intro j hj
          obtain ⟨hji, hjA⟩ := Finset.mem_erase.mp hj
          exact (Finset.mem_insert.mp (hA hjA)).resolve_left hji
        have hAi : insert i A' = A := Finset.insert_erase hiA
        have hbA := hb A' hA'E
        have hsumA : (∑ j ∈ A, b' j) = t + ∑ j ∈ A', b j := by
          rw [← hAi, Finset.sum_insert (Finset.notMem_erase _ _), hsum A' (Finset.notMem_erase _ _)]
          simp [b']
        have hpl : p (insert i A') - t ≤ p' A' := le_max_right _ _
        have hqu : q' A' ≤ q (insert i A') - t := min_le_right _ _
        rw [hAi] at hpl hqu
        rw [hsumA]
        omega
      · have hAE : A ⊆ E := by
          intro j hj
          exact (Finset.mem_insert.mp (hA hj)).resolve_left (fun h => hiA (h ▸ hj))
        have hbA := hb A hAE
        have hpl : p A ≤ p' A := le_max_left _ _
        have hqu : q' A ≤ q A := min_le_left _ _
        rw [hsum A hiA]
        omega

theorem integer_sandwich [Fintype V] (p q : Finset V → ℤ) (hp0 : p ∅ = 0) (hq0 : q ∅ = 0)
    (hp : ∀ A B, p A + p B ≤ p (A ∪ B) + p (A ∩ B))
    (hq : ∀ A B, q (A ∪ B) + q (A ∩ B) ≤ q A + q B)
    (hpq : ∀ A, p A ≤ q A) :
    ∃ b : V → ℤ, ∀ A, p A ≤ ∑ i ∈ A, b i ∧ (∑ i ∈ A, b i) ≤ q A := by
  obtain ⟨b, _, hb⟩ := integer_sandwich_on Finset.univ p q hp0 hq0
    (fun A _ B _ => hp A B) (fun A _ B _ => hq A B) (fun A _ => hpq A)
  exact ⟨b, fun A => hb A (Finset.subset_univ _)⟩

end CommAlg.Polymatroid
