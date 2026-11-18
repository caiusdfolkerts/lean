module

public import sunlet.sparse_tangent_pair
public import sunlet.one_hole_field
public import Mathlib.Tactic.Choose

/-! The coefficient half of the sparse tangential-contact computation.
All tangent spaces are ranges of the displayed linear differential; membership
does not package an assumed geometric conclusion. -/

@[expose] public section
noncomputable section

namespace Sunlet.Contact

open TwoRatioRigidity

variable {ι Ω K : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
  [Field K] [CharZero K]

abbrev Variation (K ι Ω : Type*) := (ι → K) × (Ω → K)

def pairDifferential (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    (Variation K ι Ω × Variation K ι Ω) →ₗ[K] (ι × Ω → K) where
  toFun v ab := v.1.1 ab.1 +
    (if ab.1 ∈ A then v.1.2 ab.2 - v.1.2 (π ab.1 ab.2) else 0) +
    algebraMap ℚ K (ratio o (π ab.1) ab.2) *
      (v.2.1 ab.1 + if ab.1 ∈ B then v.2.2 ab.2 - v.2.2 (π ab.1 ab.2) else 0)
  map_add' := by
    intro v w
    funext ab
    dsimp
    split_ifs <;> ring
  map_smul' := by
    intro r v
    funext ab
    dsimp
    split_ifs <;> ring

def tangentSpan (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] : Submodule K (ι × Ω → K) :=
  (pairDifferential (K := K) π o A B).range

@[simp] theorem pairDifferential_apply (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (v : Variation K ι Ω × Variation K ι Ω) (ab : ι × Ω) :
    pairDifferential π o A B v ab = v.1.1 ab.1 +
      (if ab.1 ∈ A then v.1.2 ab.2 - v.1.2 (π ab.1 ab.2) else 0) +
      algebraMap ℚ K (ratio o (π ab.1) ab.2) *
        (v.2.1 ab.1 + if ab.1 ∈ B then v.2.2 ab.2 - v.2.2 (π ab.1 ab.2) else 0) := rfl

theorem mem_tangentSpan_iff (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (t : ι × Ω → K) :
    t ∈ tangentSpan π o A B ↔ ∃ (p : ι → K) (J : Ω → K) (q : ι → K) (M : Ω → K), ∀ a x,
      t (a, x) = p a + (if a ∈ A then J x - J (π a x) else 0) +
        ratio o (π a) x • (q a + if a ∈ B then M x - M (π a x) else 0) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v.1.1, v.1.2, v.2.1, v.2.2, ?_⟩
    intro a x
    simpa only [pairDifferential_apply, Algebra.smul_def] using congrArg (fun f => f (a, x)) hv.symm
  · rintro ⟨p, J, q, M, ht⟩
    refine ⟨((p, J), (q, M)), ?_⟩
    funext ab
    simpa only [pairDifferential_apply, Algebra.smul_def] using (ht ab.1 ab.2).symm

def colorVector (a : ι) (F : Ω → K) (bx : ι × Ω) : K := if bx.1 = a then F bx.2 else 0

lemma inverse_equation_of_sum_zero {p q z : K} {r : ℚ} (hr : r ≠ 0)
    (h : p + r • (q + z) = 0) : z = -q + r⁻¹ • (-p) := by
  have hh := congrArg (fun w : K => r⁻¹ • w) h
  simp only [smul_add, smul_smul, smul_zero, inv_mul_cancel₀ hr, one_smul] at hh
  have he : z + (q + r⁻¹ • p) = 0 := by
    simpa only [add_assoc, add_comm, add_left_comm] using hh
  have he' := eq_neg_iff_add_eq_zero.mpr he
  simpa only [neg_add, smul_neg, add_comm] using he'

/-- The coefficient contact condition forces the logarithmic torus velocity
to vanish. This is the first paragraph of Proposition 4.5. -/
theorem torus_velocity_zero
    (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hdis : Disjoint A B) (hmoves : ∀ a, π a o ≠ o)
    (hBtwo : ∃ a ∈ B, ∃ b ∈ B, π a ≠ π b)
    (hBtrans : TransitiveFamily π B)
    (hredtwo : ∀ b ∈ B, ∃ a ∈ B \ {b}, ∃ c ∈ B \ {b}, π a ≠ π c)
    (hredtrans : ∀ b ∈ B, TransitiveFamily π (B \ {b}))
    (K₀ : Ω → K) (hbase : K₀ o = 0)
    (hcontact : ∀ a, colorVector a (fun x => K₀ x - K₀ (π a x)) ∈ tangentSpan π o A B) :
    ∀ x, K₀ x = 0 := by
  classical
  have hE : ∀ b ∈ B, ∃ c d : K, ∀ x,
      K₀ x - K₀ (π b x) = c + ratio o (π b) x • d := by
    intro b hb
    obtain ⟨p, J, q, M, ht⟩ := (mem_tangentSpan_iff π o A B _).mp (hcontact b)
    have hM : ∀ a ∈ B \ {b}, ∀ x,
        M x - M (π a x) = -q a + (ratio o (π a) x)⁻¹ • (-p a) := by
      intro a ha x
      obtain ⟨haB, hab⟩ := ha
      have hne : a ≠ b := by simpa only [Set.mem_singleton_iff] using hab
      have haA : a ∉ A := fun hA => Set.disjoint_left.mp hdis hA haB
      have hh := ht a x
      simp only [colorVector, hne, if_false, if_neg haA, if_pos haB, add_zero] at hh
      exact inverse_equation_of_sum_zero (SparseTangentPair.ratio_ne_zero o (π a) x) hh.symm
    have hMinv := TwoRatioRigidity.family_inverse (fun a _ => hmoves a) (hredtwo b hb) hM
    have hMc : ∀ x, M x = M o :=
      invariant_constant_of_transitive (hredtrans b hb) (fun a ha => (hMinv a ha).2.2) o
    refine ⟨p b, q b, ?_⟩
    intro x
    have hbA : b ∉ A := fun hA => Set.disjoint_left.mp hdis hA hb
    simpa only [colorVector, if_true, if_neg hbA, if_pos hb, hMc, sub_self, add_zero] using ht b x
  have hex : ∀ a, ∃ c d : K, a ∈ B → ∀ x,
      K₀ x - K₀ (π a x) = c + ratio o (π a) x • d := by
    intro a
    by_cases ha : a ∈ B
    · obtain ⟨c, d, he⟩ := hE a ha
      exact ⟨c, d, fun _ => he⟩
    · exact ⟨0, 0, fun h => False.elim (ha h)⟩
  choose c d hc using hex
  have hKinv := TwoRatioRigidity.family (fun a _ => hmoves a) hBtwo hc
  intro x
  rw [invariant_constant_of_transitive hBtrans (fun a ha => (hKinv a ha).2.2) o x, hbase]

end Sunlet.Contact
