module

public import sunlet.two_ratio_rigidity
public import Lean.Elab.Tactic.Omega

/-! Permutations with both edges at a distinguished vertex omitted.
Deleting the vertex and splicing its cycle reduces the ordinary-edge equations
to the checked one-hole theorem. -/

@[expose] public section
noncomputable section

namespace Sunlet.PuncturedBothEndpoints

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def spliced (o : Ω) (π : Equiv.Perm Ω) : Equiv.Perm {x : Ω // x ≠ o} :=
  (Equiv.swap o (π o) * π).subtypeEquiv (by
    intro x
    have ho : (Equiv.swap o (π o) * π) o = o := by simp
    constructor
    · intro hx he
      apply hx
      exact (Equiv.swap o (π o) * π).injective (he.trans ho.symm)
    · intro hx he
      exact hx (he ▸ ho))

lemma spliced_apply (o : Ω) (π : Equiv.Perm Ω) (x : {x : Ω // x ≠ o}) :
    (spliced o π x : Ω) = Equiv.swap o (π o) (π x) := rfl

lemma spliced_ordinary (o : Ω) (π : Equiv.Perm Ω)
    (x : {x : Ω // x ≠ o}) (hx : π x ≠ o) : (spliced o π x : Ω) = π x := by
  rw [spliced_apply]
  exact Equiv.swap_apply_of_ne_of_ne hx (fun he => x.property (π.injective he))

lemma inverse_moves {o : Ω} {π : Equiv.Perm Ω} (h : π o ≠ o) : π.symm o ≠ o := by
  intro he
  apply h
  simpa using (congrArg π he).symm

def hole (o : Ω) (π : Equiv.Perm Ω) (h : π o ≠ o) : {x : Ω // x ≠ o} :=
  ⟨π.symm o, inverse_moves h⟩

lemma spliced_hole {o : Ω} {π : Equiv.Perm Ω} (h : π o ≠ o) :
    (spliced o π (hole o π h) : Ω) = π o := by
  simp [spliced_apply, hole]

def Ordinary (o : Ω) (π : Equiv.Perm Ω) (F : {x : Ω // x ≠ o} → ℚ) (c : ℚ) : Prop :=
  ∀ (x : Ω) (hx : x ≠ o) (hy : π x ≠ o), F ⟨π x, hy⟩ - F ⟨x, hx⟩ = c

lemma outgoing_of_ordinary {o : Ω} {π : Equiv.Perm Ω}
    {F : {x : Ω // x ≠ o} → ℚ} {c : ℚ}
    (ho : π o ≠ o) (h : Ordinary o π F c) :
    PuncturedDifferences.Outgoing (hole o π ho) (spliced o π) F c := by
  intro x hx
  have hπx : π x ≠ o := by
    intro he
    apply hx
    apply Subtype.ext
    exact π.injective (he.trans (π.apply_symm_apply o).symm)
  have he : spliced o π x = ⟨π x, hπx⟩ :=
    Subtype.ext (spliced_ordinary o π x hπx)
  rw [he]
  exact h x x.property hπx

/-- A permutation is recovered from its deleted-cycle permutation and the
incoming vertex of the deleted edge. -/
lemma eq_of_spliced_eq_and_hole_eq {o : Ω} {π σ : Equiv.Perm Ω}
    (hπ : π o ≠ o) (hσ : σ o ≠ o)
    (hs : spliced o π = spliced o σ) (hh : hole o π hπ = hole o σ hσ) : π = σ := by
  have ho : π o = σ o := by
    rw [← spliced_hole hπ, hs, hh, spliced_hole hσ]
  ext x
  by_cases hx : x = o
  · subst x
    exact ho
  have hpre : π.symm o = σ.symm o := congrArg Subtype.val hh
  by_cases hp : π x = o
  · have he : x = π.symm o := π.injective (hp.trans (π.apply_symm_apply o).symm)
    rw [hp, he, hpre, σ.apply_symm_apply]
  · have hq : σ x ≠ o := by
      intro he
      have hx' : x = σ.symm o := σ.injective (he.trans (σ.apply_symm_apply o).symm)
      apply hp
      rw [hx', ← hpre, π.apply_symm_apply]
    have he := congrArg (fun f => (f ⟨x, hx⟩ : Ω)) hs
    simpa only [spliced_ordinary o π ⟨x, hx⟩ hp, spliced_ordinary o σ ⟨x, hx⟩ hq] using he

/-- Positive nonzero steps determine the entire permutation. -/
theorem eq_of_positive_steps {o : Ω} {π σ : Equiv.Perm Ω}
    {F : {x : Ω // x ≠ o} → ℚ} {c d : ℚ}
    [Nontrivial {x : Ω // x ≠ o}]
    (hπo : π o ≠ o) (hσo : σ o ≠ o)
    (hπ : Ordinary o π F c) (hσ : Ordinary o σ F d)
    (hc : 0 < c) (hd : 0 < d) : π = σ := by
  have hp := outgoing_of_ordinary hπo hπ
  have hq := outgoing_of_ordinary hσo hσ
  have hh : hole o π hπo = hole o σ hσo := by
    by_contra he
    have hmax := PuncturedDifferences.strict_max_of_positive hp hc _ (Ne.symm he)
    have hmax' := PuncturedDifferences.strict_max_of_positive hq hd _ he
    linarith
  have hq' : PuncturedDifferences.Outgoing (hole o π hπo) (spliced o σ) F d := by
    rw [hh]
    exact hq
  have hcd := PuncturedDifferences.nonzero_constant_unique hp hq' hc.ne' hd.ne'
  have hinj := PuncturedDifferences.injective_of_positive hp hc
  have hs : spliced o π = spliced o σ := by
    apply Equiv.ext
    intro x
    apply hinj
    rw [PuncturedDifferences.full_formula hp x, PuncturedDifferences.full_formula hq' x, hcd]
  exact eq_of_spliced_eq_and_hole_eq hπo hσo hs hh

end Sunlet.PuncturedBothEndpoints
