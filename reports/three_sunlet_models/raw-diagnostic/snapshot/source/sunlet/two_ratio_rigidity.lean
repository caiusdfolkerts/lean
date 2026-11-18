module

public import sunlet.permutation_families
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.FieldSimp

/-! The two-ratio rigidity lemma (Lemma 4.3), proved by finite moments.
The rational proof is transported through separating linear functionals, so it
applies to complex-valued functions without imposing an order on the target.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Finset

namespace Sunlet.TwoRatioRigidity

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def scale (o : Ω) (x : Ω) : ℚ := if x = o then 1 else 2

def ratio (o : Ω) (π : Equiv.Perm Ω) (x : Ω) : ℚ := scale o x / scale o (π x)

def Equation (o : Ω) (π : Equiv.Perm Ω) (F : Ω → ℚ) (c d : ℚ) : Prop :=
  ∀ x, F x - F (π x) = c + d * ratio o π x

def shifted (o : Ω) (F : Ω → ℚ) (d : ℚ) (x : Ω) : ℚ :=
  F x - d * if x = o then 0 else 1

lemma shifted_outgoing {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ} {c d : ℚ}
    (h : Equation o π F c d) :
    PuncturedDifferences.Outgoing o π (shifted o F d) (-(c + d)) := by
  intro x hx
  have he := h x
  by_cases hp : π x = o
  · simp [ratio, scale, hx, hp, shifted] at he ⊢
    linarith
  · simp [ratio, scale, hx, hp, shifted] at he ⊢
    linarith

lemma coefficient_relation {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ} {c d : ℚ}
    (ho : π o ≠ o) (h : Equation o π F c d) :
    d = 2 * (Fintype.card Ω : ℚ) * (-(c + d)) := by
  have he := PuncturedDifferences.exceptional_difference (shifted_outgoing h)
  have hbase := h o
  simp [ratio, scale, shifted, ho] at he hbase
  nlinarith

lemma shifted_sum (o : Ω) (F : Ω → ℚ) (d : ℚ) :
    (∑ x, shifted o F d x) = (∑ x, F x) - d * ((Fintype.card Ω : ℚ) - 1) := by
  simp only [shifted, sum_sub_distrib, ← mul_sum]
  have hi : (∑ x : Ω, (if x = o then (0 : ℚ) else 1)) =
      (Fintype.card Ω : ℚ) - 1 := by
    calc
      _ = ∑ x : Ω, (1 - if x = o then (1 : ℚ) else 0) := by
        apply sum_congr rfl
        intro x hx
        split_ifs <;> norm_num
      _ = _ := by simp [sum_sub_distrib]
  rw [hi]

lemma moment_identity {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ} {c d : ℚ}
    (ho : π o ≠ o) (h : Equation o π F c d) :
    (-(c + d)) * (2 * ((∑ x, F x) - (Fintype.card Ω : ℚ) * F o) -
      3 * (Fintype.card Ω : ℚ) * ((Fintype.card Ω : ℚ) - 1) * (-(c + d))) = 0 := by
  have hs := PuncturedDifferences.second_moment (shifted_outgoing h)
  rw [shifted_sum] at hs
  simp only [shifted, ite_true, mul_zero, sub_zero] at hs
  have hd := coefficient_relation ho h
  generalize hq : -(c + d) = q at hs hd ⊢
  rw [hd] at hs
  convert hs using 1 <;> ring

lemma outgoing_lower_bound {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ} {q : ℚ}
    (h : PuncturedDifferences.Outgoing o π F q) (hq : 0 < q) (x : Ω) :
    F (π o) ≤ F x := by
  have hi : PuncturedDifferences.Outgoing (π o) π.symm (fun x => -F x) q := by
    intro y hy
    have hn : π.symm y ≠ o := by
      intro he
      apply hy
      rw [← π.apply_symm_apply y, he]
    have hh := h (π.symm y) hn
    simp only [Equiv.apply_symm_apply] at hh
    linarith
  by_cases hx : x = π o
  · subst x; exact le_rfl
  · have hh := PuncturedDifferences.strict_max_of_positive hi hq x hx
    linarith

lemma base_strict_min_of_positive {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ} {c d : ℚ}
    (ho : π o ≠ o) (h : Equation o π F c d) (hq : 0 < -(c + d)) :
    ∀ x, x ≠ o → F o < F x := by
  intro x hx
  have hl := outgoing_lower_bound (shifted_outgoing h) hq x
  have he := PuncturedDifferences.exceptional_difference (shifted_outgoing h)
  have hd := coefficient_relation ho h
  simp [shifted, ho] at he
  simp [shifted, ho, hx] at hl
  have hn : 0 ≤ (Fintype.card Ω : ℚ) := Nat.cast_nonneg _
  have hm := mul_nonneg hn hq.le
  nlinarith

lemma injective_of_nonzero {o : Ω} {π : Equiv.Perm Ω} {F : Ω → ℚ} {c d : ℚ}
    (ho : π o ≠ o) (h : Equation o π F c d) (hq : -(c + d) ≠ 0) :
    Function.Injective F := by
  have hshift := PuncturedDifferences.injective_of_nonzero (shifted_outgoing h) hq
  have hbase : ∀ x, x ≠ o → F x ≠ F o := by
    rcases lt_or_gt_of_ne hq with hn | hp
    · have hneg : Equation o π (fun x => -F x) (-c) (-d) := by
        intro x
        have hh := h x
        dsimp
        linarith
      have hpos : 0 < -(-c + -d) := by linarith
      intro x hx he
      have hh := base_strict_min_of_positive ho hneg hpos x hx
      rw [he] at hh
      exact lt_irrefl _ hh
    · intro x hx
      exact ne_of_gt (base_strict_min_of_positive ho h hp x hx)
  intro x y hxy
  by_cases hx : x = o
  · subst x
    by_contra hy
    exact hbase y (Ne.symm hy) hxy.symm
  by_cases hy : y = o
  · subst y
    exact False.elim (hbase x hx hxy)
  apply hshift
  simp [shifted, hx, hy, hxy]

/-- The rational two-permutation form of Lemma 4.3. Only movement of the
distinguished vertex is needed; the paper assumes derangements. -/
theorem two_permutations
    {o : Ω} {π σ : Equiv.Perm Ω} {F : Ω → ℚ} {c d c' d' : ℚ}
    (hπo : π o ≠ o) (hσo : σ o ≠ o) (hneq : π ≠ σ)
    (hπ : Equation o π F c d) (hσ : Equation o σ F c' d') :
    c = 0 ∧ d = 0 ∧ c' = 0 ∧ d' = 0 ∧
      (∀ x, F (π x) = F x) ∧ (∀ x, F (σ x) = F x) := by
  have hπne : π ≠ 1 := by intro he; apply hπo; simp [he]
  have hσne : σ ≠ 1 := by intro he; apply hσo; simp [he]
  have hntr : ¬Subsingleton Ω := by
    intro hs
    letI := hs
    exact hπo (Subsingleton.elim _ _)
  letI : Nontrivial Ω := not_subsingleton_iff_nontrivial.mp hntr
  have hn : (2 : ℚ) ≤ Fintype.card Ω := by exact_mod_cast Fintype.one_lt_card
  have hq : -(c + d) = 0 := by
    by_contra hq
    have hinj := injective_of_nonzero hπo hπ hq
    have hq' : -(c' + d') ≠ 0 := by
      intro hz
      have hd' := coefficient_relation hσo hσ
      rw [hz, mul_zero] at hd'
      have hc' : c' = 0 := by linarith
      apply hσne
      ext x
      apply hinj
      change F (σ x) = F x
      have hh := hσ x
      simp only [hc', hd', zero_mul, zero_add] at hh
      linarith
    have hp := (mul_eq_zero.mp (moment_identity hπo hπ)).resolve_left hq
    have hs := (mul_eq_zero.mp (moment_identity hσo hσ)).resolve_left hq'
    have hcoef : 0 < 3 * (Fintype.card Ω : ℚ) * ((Fintype.card Ω : ℚ) - 1) := by
      exact mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
    have heq : -(c + d) = -(c' + d') := by nlinarith
    have hdd : d = d' := by
      rw [coefficient_relation hπo hπ, coefficient_relation hσo hσ, heq]
    have hshiftσ : PuncturedDifferences.Outgoing o σ (shifted o F d) (-(c' + d')) := by
      rw [hdd]
      exact shifted_outgoing hσ
    have hh := PuncturedDifferences.two_permutations_outgoing
      (shifted_outgoing hπ) hshiftσ hπne hσne hneq
    exact hq hh.1
  have hd : d = 0 := by simpa [hq] using coefficient_relation hπo hπ
  have hc : c = 0 := by linarith
  have hq' : -(c' + d') = 0 := by
    by_contra hq'
    have hinj := injective_of_nonzero hσo hσ hq'
    apply hπne
    ext x
    apply hinj
    change F (π x) = F x
    have hh := hπ x
    simp only [hc, hd, zero_mul, zero_add] at hh
    linarith
  have hd' : d' = 0 := by simpa [hq'] using coefficient_relation hσo hσ
  have hc' : c' = 0 := by linarith
  refine ⟨hc, hd, hc', hd', ?_, ?_⟩
  · intro x
    have hh := hπ x
    simp only [hc, hd, zero_mul, zero_add] at hh
    linarith
  · intro x
    have hh := hσ x
    simp only [hc', hd', zero_mul, zero_add] at hh
    linarith

section VectorSpace

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Two-ratio rigidity over any rational vector space, in particular over ℂ.
The target is not ordered: separating rational linear functionals reduce the
claim to the already proved rational identity. -/
theorem two_permutations_module
    {o : Ω} {π σ : Equiv.Perm Ω} {F : Ω → V} {c d c' d' : V}
    (hπo : π o ≠ o) (hσo : σ o ≠ o) (hneq : π ≠ σ)
    (hπ : ∀ x, F x - F (π x) = c + ratio o π x • d)
    (hσ : ∀ x, F x - F (σ x) = c' + ratio o σ x • d') :
    c = 0 ∧ d = 0 ∧ c' = 0 ∧ d' = 0 ∧
      (∀ x, F (π x) = F x) ∧ (∀ x, F (σ x) = F x) := by
  have hf (φ : Module.Dual ℚ V) := two_permutations hπo hσo hneq
    (F := fun x => φ (F x)) (c := φ c) (d := φ d) (c' := φ c') (d' := φ d')
    (by
      intro x
      have hh := congrArg φ (hπ x)
      simpa only [map_sub, map_add, map_smul, smul_eq_mul, mul_comm] using hh)
    (by
      intro x
      have hh := congrArg φ (hσ x)
      simpa only [map_sub, map_add, map_smul, smul_eq_mul, mul_comm] using hh)
  have hc : c = 0 := (Module.forall_dual_apply_eq_zero_iff ℚ c).mp (fun φ => (hf φ).1)
  have hd : d = 0 := (Module.forall_dual_apply_eq_zero_iff ℚ d).mp (fun φ => (hf φ).2.1)
  have hc' : c' = 0 := (Module.forall_dual_apply_eq_zero_iff ℚ c').mp (fun φ => (hf φ).2.2.1)
  have hd' : d' = 0 := (Module.forall_dual_apply_eq_zero_iff ℚ d').mp (fun φ => (hf φ).2.2.2.1)
  refine ⟨hc, hd, hc', hd', ?_, ?_⟩
  · intro x
    have hh := hπ x
    simp only [hc, hd, smul_zero, zero_add] at hh
    exact (sub_eq_zero.mp hh).symm
  · intro x
    have hh := hσ x
    simp only [hc', hd', smul_zero, zero_add] at hh
    exact (sub_eq_zero.mp hh).symm

/-- Lemma 4.3 for λ=2, with arbitrary (possibly infinite) color index. -/
theorem family {ι : Type*} {o : Ω} {π : ι → Equiv.Perm Ω} {P : Set ι}
    {F : Ω → V} {c d : ι → V}
    (hmoves : ∀ a ∈ P, π a o ≠ o)
    (htwo : ∃ a ∈ P, ∃ b ∈ P, π a ≠ π b)
    (h : ∀ a ∈ P, ∀ x, F x - F (π a x) = c a + ratio o (π a) x • d a) :
    ∀ a ∈ P, c a = 0 ∧ d a = 0 ∧ ∀ x, F (π a x) = F x := by
  obtain ⟨a, ha, b, hb, hab⟩ := htwo
  intro j hj
  by_cases hja : π j = π a
  · have hjb : π j ≠ π b := by simpa [hja] using hab
    obtain ⟨hc, hd, _, _, hi, _⟩ := two_permutations_module
      (hmoves j hj) (hmoves b hb) hjb (h j hj) (h b hb)
    exact ⟨hc, hd, hi⟩
  · obtain ⟨hc, hd, _, _, hi, _⟩ := two_permutations_module
      (hmoves j hj) (hmoves a ha) hja (h j hj) (h a ha)
    exact ⟨hc, hd, hi⟩

/-- Lemma 4.3 for λ=1/2 follows by reversing every permutation edge. -/
theorem family_inverse {ι : Type*} {o : Ω} {π : ι → Equiv.Perm Ω} {P : Set ι}
    {F : Ω → V} {c d : ι → V}
    (hmoves : ∀ a ∈ P, π a o ≠ o)
    (htwo : ∃ a ∈ P, ∃ b ∈ P, π a ≠ π b)
    (h : ∀ a ∈ P, ∀ x, F x - F (π a x) = c a + (ratio o (π a) x)⁻¹ • d a) :
    ∀ a ∈ P, c a = 0 ∧ d a = 0 ∧ ∀ x, F (π a x) = F x := by
  have hmoves' : ∀ a ∈ P, (π a).symm o ≠ o := by
    intro a ha he
    apply hmoves a ha
    simpa using (congrArg (π a) he).symm
  have htwo' : ∃ a ∈ P, ∃ b ∈ P, (π a).symm ≠ (π b).symm := by
    obtain ⟨a, ha, b, hb, hab⟩ := htwo
    exact ⟨a, ha, b, hb, fun he => hab (congrArg Equiv.symm he)⟩
  have h' : ∀ a ∈ P, ∀ x, F x - F ((π a).symm x) =
      -c a + ratio o (π a).symm x • (-d a) := by
    intro a ha x
    have hh := h a ha ((π a).symm x)
    simp only [Equiv.apply_symm_apply] at hh
    calc
      _ = -(F ((π a).symm x) - F x) := (neg_sub _ _).symm
      _ = -(c a + (ratio o (π a) ((π a).symm x))⁻¹ • d a) := by rw [hh]
      _ = _ := by simp [ratio, inv_div, add_comm]
  have hf := family hmoves' htwo' h'
  intro a ha
  obtain ⟨hc, hd, hi⟩ := hf a ha
  refine ⟨neg_eq_zero.mp hc, neg_eq_zero.mp hd, ?_⟩
  intro x
  simpa using (hi (π a x)).symm

end VectorSpace

end Sunlet.TwoRatioRigidity
