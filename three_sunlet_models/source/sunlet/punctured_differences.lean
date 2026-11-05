module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! A proof of the one-omitted-edge lemma using extrema and two moments.
The auxiliary equations are over ℚ, independently of the model's ground field.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Finset

namespace Sunlet.PuncturedDifferences

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def Outgoing (o : Ω) (π : Equiv.Perm Ω) (F : Ω → ℚ) (c : ℚ) : Prop :=
  ∀ x, x ≠ o → F (π x) - F x = c

lemma exceptional_difference {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ} {c : ℚ}
    (h : Outgoing o π F c) :
    F (π o) - F o = (1 - (Fintype.card Ω : ℚ)) * c := by
  have hsum : (∑ x, (F (π x) - F x)) = 0 := by
    rw [sum_sub_distrib, Equiv.sum_comp]
    ring
  have hsum' : (∑ x, (F (π x) - F x)) =
      (Fintype.card Ω : ℚ) * c + (F (π o) - F o - c) := by
    calc
      _ = ∑ x, (c + if x = o then F (π o) - F o - c else 0) := by
        apply sum_congr rfl
        intro x hx
        by_cases he : x = o
        · subst x; simp
        · simp [he, h x he]
      _ = _ := by simp [sum_add_distrib]
  rw [hsum] at hsum'
  linarith

lemma full_formula {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ} {c : ℚ}
    (h : Outgoing o π F c) (x : Ω) :
    F (π x) = F x + c - if x = o then (Fintype.card Ω : ℚ) * c else 0 := by
  by_cases hx : x = o
  · subst x
    have he := exceptional_difference h
    simp only [ite_true]
    linarith
  · simp only [hx, ite_false, sub_zero]
    linarith [h x hx]

lemma strict_max_of_positive {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ} {c : ℚ}
    (h : Outgoing o π F c) (hc : 0 < c) : ∀ x, x ≠ o → F x < F o := by
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image (univ : Finset Ω) F ⟨o, mem_univ o⟩
  have hzo : z = o := by
    by_contra hn
    have hstep := h z hn
    have hle := hmax (π z) (mem_univ _)
    linarith
  subst z
  intro x hx
  have hstep := h x hx
  have hle := hmax (π x) (mem_univ _)
  linarith

lemma injective_of_positive {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ} {c : ℚ}
    (h : Outgoing o π F c) (hc : 0 < c) : Function.Injective F := by
  classical
  let D : Finset Ω := univ.filter fun x => ∃ y, y ≠ x ∧ F y = F x
  by_contra hn
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hn
  have hD : D.Nonempty := ⟨x, by simp [D]; exact ⟨y, Ne.symm hne, hxy.symm⟩⟩
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image D F hD
  obtain ⟨w, hwz, hFw⟩ : ∃ w, w ≠ z ∧ F w = F z := by simpa [D] using hz
  have hzo : z ≠ o := by
    intro he
    subst z
    have hs := strict_max_of_positive h hc w hwz
    linarith
  have hwo : w ≠ o := by
    intro he
    subst w
    have hs := strict_max_of_positive h hc z hzo
    linarith
  have hπwz : π w ≠ π z := fun he => hwz (π.injective he)
  have hπF : F (π w) = F (π z) := by linarith [h w hwo, h z hzo]
  have hπz : π z ∈ D := by simp [D]; exact ⟨π w, hπwz, hπF⟩
  have hm := hmax (π z) hπz
  linarith [h z hzo]

lemma injective_of_nonzero {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ} {c : ℚ}
    (h : Outgoing o π F c) (hc : c ≠ 0) : Function.Injective F := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hn : Outgoing o π (fun x => -F x) (-c) := by
      intro x hx
      linarith [h x hx]
    have hinj := injective_of_positive hn (neg_pos.mpr hneg)
    intro x y hxy
    apply hinj
    simp [hxy]
  · exact injective_of_positive h hpos

lemma second_moment {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ} {c : ℚ}
    (h : Outgoing o π F c) :
    c * (2 * ((∑ x, F x) - (Fintype.card Ω : ℚ) * F o) +
      (Fintype.card Ω : ℚ) * ((Fintype.card Ω : ℚ) - 1) * c) = 0 := by
  let n : ℚ := Fintype.card Ω
  have hs : (∑ x, ((F (π x)) ^ 2 - (F x) ^ 2)) = 0 := by
    rw [sum_sub_distrib, Equiv.sum_comp π (fun x => (F x) ^ 2)]
    ring
  have hi : (∑ x, ((F (π x)) ^ 2 - (F x) ^ 2)) =
      2 * c * (∑ x, F x) + n * c ^ 2 - 2 * n * c * F o + (n ^ 2 - 2 * n) * c ^ 2 := by
    calc
      _ = ∑ x, (2 * c * F x + c ^ 2 +
          if x = o then -2 * n * c * F o + (n ^ 2 - 2 * n) * c ^ 2 else 0) := by
        apply sum_congr rfl
        intro x hx
        rw [full_formula h x]
        by_cases he : x = o
        · subst x; simp only [ite_true]; dsimp [n]; ring
        · simp only [he, ite_false]; ring
      _ = _ := by simp [sum_add_distrib, mul_sum, n]; ring
  rw [hs] at hi
  dsimp [n] at hi
  nlinarith

lemma invariant_of_zero {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ}
    (h : Outgoing o π F 0) : ∀ x, F (π x) = F x := by
  intro x
  simpa using full_formula h x

lemma nonzero_constant_unique [Nontrivial Ω]
    {o : Ω} {π σ : Equiv.Perm Ω} {F : Ω → ℚ} {c d : ℚ}
    (hπ : Outgoing o π F c) (hσ : Outgoing o σ F d)
    (hc : c ≠ 0) (hd : d ≠ 0) : c = d := by
  have hp := (mul_eq_zero.mp (second_moment hπ)).resolve_left hc
  have hq := (mul_eq_zero.mp (second_moment hσ)).resolve_left hd
  have hn : (2 : ℚ) ≤ Fintype.card Ω := by
    exact_mod_cast Fintype.one_lt_card
  have hnn : (0 : ℚ) < (Fintype.card Ω : ℚ) * ((Fintype.card Ω : ℚ) - 1) :=
    mul_pos (by linarith) (by linarith)
  have he : (Fintype.card Ω : ℚ) * ((Fintype.card Ω : ℚ) - 1) * (c - d) = 0 := by
    nlinarith
  have hz := (mul_eq_zero.mp he).resolve_left (ne_of_gt hnn)
  linarith

/-- Two distinct nonidentity permutations recover every omitted outgoing equation. -/
theorem two_permutations_outgoing
    {o : Ω} {π σ : Equiv.Perm Ω} {F : Ω → ℚ} {c d : ℚ}
    (hπ : Outgoing o π F c) (hσ : Outgoing o σ F d)
    (hπne : π ≠ 1) (hσne : σ ≠ 1) (hneq : π ≠ σ) :
    c = 0 ∧ d = 0 ∧ (∀ x, F (π x) = F x) ∧ (∀ x, F (σ x) = F x) := by
  classical
  have hn : ¬Subsingleton Ω := by
    intro hs
    letI := hs
    exact hπne (Subsingleton.elim _ _)
  letI : Nontrivial Ω := not_subsingleton_iff_nontrivial.mp hn
  have hc : c = 0 := by
    by_contra hc
    have hinj := injective_of_nonzero hπ hc
    have hd : d ≠ 0 := by
      intro hd
      subst d
      apply hσne
      ext x
      exact hinj (invariant_of_zero hσ x)
    have hcd := nonzero_constant_unique hπ hσ hc hd
    apply hneq
    ext x
    apply hinj
    rw [full_formula hπ x, full_formula hσ x, hcd]
  have hd : d = 0 := by
    by_contra hd
    have hinj := injective_of_nonzero hσ hd
    subst c
    apply hπne
    ext x
    exact hinj (invariant_of_zero hπ x)
  refine ⟨hc, hd, ?_, ?_⟩
  · exact invariant_of_zero (hc ▸ hπ)
  · exact invariant_of_zero (hd ▸ hσ)

/-- The incoming-hole form used in the paper follows by inverting both permutations. -/
theorem two_permutations_incoming
    {o : Ω} {π σ : Equiv.Perm Ω} {F : Ω → ℚ} {c d : ℚ}
    (hπ : ∀ x, x ≠ π.symm o → F (π x) - F x = c)
    (hσ : ∀ x, x ≠ σ.symm o → F (σ x) - F x = d)
    (hπne : π ≠ 1) (hσne : σ ≠ 1) (hneq : π ≠ σ) :
    c = 0 ∧ d = 0 ∧ (∀ x, F (π x) = F x) ∧ (∀ x, F (σ x) = F x) := by
  have hp : Outgoing o π.symm F (-c) := by
    intro x hx
    have hh := hπ (π.symm x) (fun he => hx (π.symm.injective he))
    simp only [Equiv.apply_symm_apply] at hh
    linarith
  have hq : Outgoing o σ.symm F (-d) := by
    intro x hx
    have hh := hσ (σ.symm x) (fun he => hx (σ.symm.injective he))
    simp only [Equiv.apply_symm_apply] at hh
    linarith
  have hpn : π.symm ≠ 1 := by
    change π⁻¹ ≠ 1
    exact inv_ne_one.mpr hπne
  have hqn : σ.symm ≠ 1 := by
    change σ⁻¹ ≠ 1
    exact inv_ne_one.mpr hσne
  have hpq : π.symm ≠ σ.symm := by
    intro he
    exact hneq (congrArg Equiv.symm he)
  obtain ⟨hc, hd, hi, hj⟩ := two_permutations_outgoing hp hq hpn hqn hpq
  refine ⟨neg_eq_zero.mp hc, neg_eq_zero.mp hd, ?_, ?_⟩
  · intro x
    simpa using (hi (π x)).symm
  · intro x
    simpa using (hj (σ x)).symm

end Sunlet.PuncturedDifferences
