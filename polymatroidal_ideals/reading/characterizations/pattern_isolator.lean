import Characterizations.Transport

/-! # Exact degree-padded isolators on arbitrary active variable sets -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def patternActive (C : Finset V) (i q j : V) : Finset V := insert i (insert q (insert j C))

theorem patternActive_card {C : Finset V} {i q j : V}
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) (hC : C ⊆ tripleCap i q j) :
    (patternActive C i q j).card = C.card + 3 := by
  have hiC : i ∉ C := fun hi => by simpa using hC hi
  have hqC : q ∉ C := fun hq => by simpa using hC hq
  have hjC : j ∉ C := fun hj => by simpa using hC hj
  simp [patternActive, hiC, hqC, hjC, hiq, hij, hqj]

theorem exists_pattern_isolator {k : Type*} [CommSemiring k] [Nontrivial k]
    (C : Finset V) (i q j : V) (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j)
    (hC : C ⊆ tripleCap i q j) (hCne : C.Nonempty) (d : ℕ) (hd : C.card + 1 ≤ d) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧
      ∀ o : VariableOrder V, HasLinearQuotients k B (variableRevlex o) ↔ ¬ OrderPattern o C i q j := by
  let T := patternActive C i q j
  let e : T ↪ V := Function.Embedding.subtype _
  let I : T := ⟨i, by simp [T, patternActive]⟩
  let Q : T := ⟨q, by simp [T, patternActive]⟩
  let J : T := ⟨j, by simp [T, patternActive]⟩
  have hIQ : I ≠ Q := fun h => hiq (congrArg Subtype.val h)
  have hIJ : I ≠ J := fun h => hij (congrArg Subtype.val h)
  have hQJ : Q ≠ J := fun h => hqj (congrArg Subtype.val h)
  have hTcard : Fintype.card T = C.card + 3 := by
    rw [Fintype.card_coe]
    exact patternActive_card hiq hij hqj hC
  have hfour : 4 ≤ Fintype.card T := by have hh := card_pos.mpr hCne; omega
  have hdegree : Fintype.card T - 2 = C.card + 1 := by omega
  let B₀ := tripleFamily I Q J
  let B₁ := embeddedFamily e B₀
  let c : Exponent V := Finsupp.single i (d - (C.card + 1))
  let B := translatedFamily c B₁
  have hB₀ : Equigenerated B₀ (C.card + 1) := hdegree ▸ tripleFamily_equigenerated I Q J
  have hB₁ : Equigenerated B₁ (C.card + 1) := embeddedFamily_equigenerated hB₀ e
  have hcdegree : c.degree = d - (C.card + 1) := by simp only [c, Finsupp.degree_single]
  refine ⟨B, ?_, ?_, ?_⟩
  · have hh := translatedFamily_equigenerated hB₁ c
    have he : C.card + 1 + c.degree = d := by omega
    exact he ▸ hh
  · intro hp
    have hp₁ : IsPolymatroidal B₁ := (translatedFamily_polymatroidal_iff hB₁ c).mp hp
    have hp₀ : IsPolymatroidal B₀ := embeddedFamily_polymatroidal_implies hB₀ e hp₁
    exact tripleFamily_not_polymatroidal hIQ hIJ hQJ hfour hp₀
  · intro o
    rw [translatedFamily_linearQuotients_iff hB₁ c o,
      embeddedFamily_linearQuotients_iff hB₀ e o,
      tripleFamily_linearQuotients_iff hIQ hIJ hQJ hfour]
    apply not_congr
    simp only [FinalTriple, OrderPattern, restrictedOrder_lt_iff]
    change (o i < o j ∧ o q < o j ∧
      ∀ x : T, x ≠ I → x ≠ Q → x ≠ J → o x.val < o i ∧ o x.val < o q) ↔ _
    constructor
    · rintro ⟨hijO, hqjO, hrest⟩
      refine ⟨hijO, hqjO, ?_⟩
      intro x hx
      have hxT : x ∈ T := by simp [T, patternActive, hx]
      have hxneq := (mem_tripleCap _ _ _ _).mp (hC hx)
      exact hrest ⟨x, hxT⟩ (fun he => hxneq.1 (congrArg Subtype.val he))
        (fun he => hxneq.2.1 (congrArg Subtype.val he))
        (fun he => hxneq.2.2 (congrArg Subtype.val he))
    · rintro ⟨hijO, hqjO, hrest⟩
      refine ⟨hijO, hqjO, ?_⟩
      intro x hxi hxq hxj
      have hxi' : x.val ≠ i := fun he => hxi (Subtype.ext he)
      have hxq' : x.val ≠ q := fun he => hxq (Subtype.ext he)
      have hxj' : x.val ≠ j := fun he => hxj (Subtype.ext he)
      have hxC : x.val ∈ C := by
        have hxT := x.property
        simpa [T, patternActive, hxi', hxq', hxj'] using hxT
      exact hrest x.val hxC

def DegreeOrderTests (k : Type*) [CommSemiring k] (d : ℕ) (F : Set (VariableOrder V)) : Prop :=
  ∀ B : Family V, Equigenerated B d →
    (∀ o ∈ F, HasLinearQuotients k B (variableRevlex o)) → IsPolymatroidal B

/-- Theorem 5.4, the full necessary-and-sufficient pattern characterization. -/
theorem degreeOrderTests_iff_coverage {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) (F : Set (VariableOrder V)) :
    DegreeOrderTests k d F ↔
      CoversPatterns (min (d - 1) (Fintype.card V - 3)) F ∧
      (Fintype.card V - 1 ≤ d → CoversFinalPairs F) := by
  constructor
  · intro htest
    constructor
    · intro i q j hiq hij hqj C hC hc
      by_contra hn
      have hCne : C.Nonempty := card_pos.mp (by omega)
      obtain ⟨B, hB, hnot, hfail⟩ := exists_pattern_isolator (k := k) C i q j hiq hij hqj hC hCne d (by omega)
      apply hnot
      apply htest B hB
      intro o ho
      exact (hfail o).mpr (fun hp => hn ⟨o, ho, hp⟩)
    · intro hdlarge i j hij
      by_contra hn
      let c : Exponent V := Finsupp.single i (d - (Fintype.card V - 1))
      let B := translatedFamily c (pairFamily i j)
      have hB : Equigenerated B d := by
        have hh := translatedFamily_equigenerated (pairFamily_equigenerated i j) c
        have he : (Fintype.card V - 1) + c.degree = d := by simp only [c, Finsupp.degree_single]; omega
        exact he ▸ hh
      have hp := htest B hB (fun o ho =>
        (translatedFamily_linearQuotients_iff (pairFamily_equigenerated i j) c o).mpr
          (pairFamily_linearQuotients_of_not_final hij o (fun hf => hn ⟨o, ho, hf⟩)))
      exact pairFamily_not_polymatroidal hij (by omega)
        ((translatedFamily_polymatroidal_iff (pairFamily_equigenerated i j) c).mp hp)
  · rintro ⟨hpatterns, hpairs⟩ B hB hL
    exact ⟨⟨d, hB⟩, exchange_of_degree_coverage (k := k) hB hcard F hpatterns hpairs hL⟩

end Characterizations
