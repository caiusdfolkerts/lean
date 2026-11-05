import Characterizations.PatternIsolator

/-! # A tournament with a predecessor at every vertex -/

noncomputable section
namespace Characterizations
open Classical Finset

def cyclicTournament {n : ℕ} (a b : Fin n) : Prop :=
  (a.val = n - 1 ∧ b.val = 0) ∨ (a.val < b.val ∧ ¬ (a.val = 0 ∧ b.val = n - 1))

theorem cyclicTournament_asymm {n : ℕ} (hn : 3 ≤ n) (a b : Fin n)
    (hab : cyclicTournament a b) : ¬ cyclicTournament b a := by
  simp only [cyclicTournament] at *
  omega

theorem cyclicTournament_total {n : ℕ} (hn : 3 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    cyclicTournament a b ∨ cyclicTournament b a := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  simp only [cyclicTournament]
  omega

theorem cyclicTournament_incoming {n : ℕ} (hn : 3 ≤ n) (b : Fin n) :
    ∃ a, cyclicTournament a b := by
  by_cases hb : b.val = 0
  · refine ⟨⟨n-1, by omega⟩, Or.inl ⟨rfl, hb⟩⟩
  by_cases hlast : b.val = n-1
  · refine ⟨⟨1, by omega⟩, Or.inr ?_⟩
    simp only
    omega
  · refine ⟨⟨0, by omega⟩, Or.inr ?_⟩
    simp only
    omega

theorem exists_incoming_tournament (W : Type*) [Fintype W] (hcard : 3 ≤ Fintype.card W) :
    ∃ R : W → W → Prop,
      (∀ a b, R a b → ¬ R b a) ∧
      (∀ a b, a ≠ b → R a b ∨ R b a) ∧ (∀ b, ∃ a, R a b) := by
  let e := Fintype.equivFin W
  refine ⟨fun a b => cyclicTournament (e a) (e b), ?_, ?_, ?_⟩
  · exact fun a b => cyclicTournament_asymm hcard (e a) (e b)
  · exact fun a b h => cyclicTournament_total hcard (e a) (e b) (fun he => h (e.injective he))
  · intro b
    obtain ⟨a, ha⟩ := cyclicTournament_incoming hcard (e b)
    exact ⟨e.symm a, by simpa using ha⟩

end Characterizations
