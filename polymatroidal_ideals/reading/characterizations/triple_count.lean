import Characterizations.Tournament
import Mathlib.Data.Fintype.Powerset

/-! # Exact counting of pointed final triples -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def PointedTriple (V : Type*) [Fintype V] [DecidableEq V] :=
  Σ j : V, {A : Finset V // A ⊆ univ.erase j ∧ A.card = 2}

instance : Fintype (PointedTriple V) := inferInstanceAs
  (Fintype (Σ j : V, {A : Finset V // A ⊆ univ.erase j ∧ A.card = 2}))

theorem card_pointedTriple : Fintype.card (PointedTriple V) =
    Fintype.card V * (Fintype.card V - 1).choose 2 := by
  change Fintype.card (Σ j : V, {A : Finset V // A ⊆ univ.erase j ∧ A.card = 2}) = _
  rw [Fintype.card_sigma]
  have hj (j : V) : Fintype.card {A : Finset V // A ⊆ univ.erase j ∧ A.card = 2} =
      (Fintype.card V - 1).choose 2 := by
    let e : {A : Finset V // A ⊆ univ.erase j ∧ A.card = 2} ≃
        ↥((univ.erase j).powersetCard 2) := Equiv.subtypeEquivRight (fun A => by simp)
    rw [Fintype.card_congr e, Fintype.card_coe, card_powersetCard]
    simp
  simp_rw [hj]
  simp

def CoversPoint (o : VariableOrder V) (P : PointedTriple V) : Prop :=
  ∃ i q : V, i ≠ q ∧ P.2.val = {i,q} ∧ FinalTriple o i q P.1

theorem coversPoint_of_triples {F : Set (VariableOrder V)} (hF : CoversFinalTriples F)
    (P : PointedTriple V) : ∃ o ∈ F, CoversPoint o P := by
  obtain ⟨i, q, hiq, hA⟩ := card_eq_two.mp P.2.property.2
  have hiP : i ∈ P.2.val := by simp [hA]
  have hqP : q ∈ P.2.val := by simp [hA]
  have hij : i ≠ P.1 := (mem_erase.mp (P.2.property.1 hiP)).1
  have hqj : q ≠ P.1 := (mem_erase.mp (P.2.property.1 hqP)).1
  obtain ⟨o, ho, hf⟩ := hF i q P.1 hiq hij hqj
  exact ⟨o, ho, i, q, hiq, hA, hf⟩

theorem finalTriple_pair_unique {o : VariableOrder V} {i q a b j : V}
    (hiq : i ≠ q) (hab : a ≠ b) (hij : i ≠ j) (hqj : q ≠ j)
    (haj : a ≠ j) (hbj : b ≠ j) (h₁ : FinalTriple o i q j) (h₂ : FinalTriple o a b j) :
    ({i,q} : Finset V) = {a,b} := by
  have hi : i ∈ ({a,b} : Finset V) := by
    by_contra hn
    have hia : i ≠ a := by simpa using (not_or.mp (by simpa using hn)).1
    have hib : i ≠ b := by simpa using (not_or.mp (by simpa using hn)).2
    have hlow := h₂.2.2 i hia hib hij
    by_cases haq : a = q
    · have hbq : b ≠ q := by intro he; exact hab (haq.trans he.symm)
      exact (lt_irrefl _ (hlow.2.trans (h₁.2.2 b hib.symm hbq hbj).1))
    · exact (lt_irrefl _ (hlow.1.trans (h₁.2.2 a hia.symm haq haj).1))
  have hq : q ∈ ({a,b} : Finset V) := by
    by_contra hn
    have hqa : q ≠ a := by simpa using (not_or.mp (by simpa using hn)).1
    have hqb : q ≠ b := by simpa using (not_or.mp (by simpa using hn)).2
    have hlow := h₂.2.2 q hqa hqb hqj
    by_cases hai : a = i
    · have hbi : b ≠ i := by intro he; exact hab (hai.trans he.symm)
      exact (lt_irrefl _ (hlow.2.trans (h₁.2.2 b hbi hqb.symm hbj).2))
    · exact (lt_irrefl _ (hlow.1.trans (h₁.2.2 a hai hqa.symm haj).2))
  exact eq_of_subset_of_card_le (by simp [insert_subset_iff, hi, hq]) (by simp [hiq, hab])

theorem coversPoint_unique {o : VariableOrder V} {P Q : PointedTriple V}
    (hP : CoversPoint o P) (hQ : CoversPoint o Q) : P = Q := by
  obtain ⟨i, q, hiq, hA, h₁⟩ := hP
  obtain ⟨a, b, hab, hB, h₂⟩ := hQ
  have hj : P.1 = Q.1 := by
    apply o.injective
    apply le_antisymm
    · exact le_of_not_gt (h₂.no_after P.1)
    · exact le_of_not_gt (h₁.no_after Q.1)
  have hij : i ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  have hqj : q ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  have haj : a ≠ Q.1 := (mem_erase.mp (Q.2.property.1 (by simp [hB]))).1
  have hbj : b ≠ Q.1 := (mem_erase.mp (Q.2.property.1 (by simp [hB]))).1
  have hsets : P.2.val = Q.2.val := by
    rw [hA, hB]
    exact finalTriple_pair_unique hiq hab hij hqj (hj ▸ haj) (hj ▸ hbj) h₁ (hj ▸ h₂)
  cases P with | mk p A =>
    cases Q with | mk q B =>
      dsimp at hj hsets
      subst q
      congr
      exact Subtype.ext hsets

/-- Every order realizes exactly one pointed final triple; hence coverage
requires at least `n * choose (n-1) 2` orders. -/
theorem triple_coverage_card_lower_bound (F : Finset (VariableOrder V))
    (hF : CoversFinalTriples (F : Set (VariableOrder V))) :
    Fintype.card V * (Fintype.card V - 1).choose 2 ≤ F.card := by
  choose f hf hcover using coversPoint_of_triples hF
  let g : PointedTriple V → F := fun P => ⟨f P, hf P⟩
  have hginj : Function.Injective g := by
    intro P Q h
    have he : f P = f Q := congrArg Subtype.val h
    exact coversPoint_unique (he ▸ hcover P) (hcover Q)
  have hh := Fintype.card_le_of_injective g hginj
  simpa [card_pointedTriple] using hh

theorem universalOrderTests_card_lower_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : 4 ≤ Fintype.card V) (F : Finset (VariableOrder V))
    (hF : UniversalOrderTests k (F : Set (VariableOrder V))) :
    Fintype.card V * (Fintype.card V - 1).choose 2 ≤ F.card :=
  triple_coverage_card_lower_bound F ((universalOrderTests_iff_coverage hcard _).mp hF).2

end Characterizations
