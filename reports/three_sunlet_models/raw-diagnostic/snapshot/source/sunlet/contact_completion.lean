module

public import sunlet.contact_torus

/-! Completion of the sparse contact linear algebra: unused colors vanish,
and the common coefficient on the second support vanishes. -/

@[expose] public section
noncomputable section

namespace Sunlet.Contact

open RatioSolutionSpaces

variable {ι Ω K : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
  [Field K] [CharZero K]

theorem coefficient_zero_off_supports
    (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hm : 5 ≤ Fintype.card Ω) (hder : ∀ a, ∀ x, π a x ≠ x)
    (p : ι → K) (hp : TorusContact π o A B p) :
    ∀ a, a ∉ A → a ∉ B → p a = 0 := by
  intro a haA haB
  by_contra hpa
  obtain ⟨H, hHo, hH⟩ := ContactLinear.exists_outside_sum o
    (solutionSpace (K := K) o (π a)) (solutionSpace o (π a))
    (sum_finrank_lt o (π a) (π a) hm (hder a) (hder a))
  obtain ⟨c, J, d, M, _, _, ht⟩ := (mem_tangentSpan_iff_field π o A B _).mp (hp H)
  have hF : (fun x => (0 : K) - p a * H x) ∈ solutionSpace (K := K) o (π a) := by
    apply forward_solution_of_equation o (π a) H 0 hHo rfl (p a) (c a) (d a)
    intro x
    simpa only [if_neg haA, if_neg haB, add_zero, Pi.zero_apply, sub_self] using ht a x
  have hs : (-p a) • H ∈ solutionSpace (K := K) o (π a) := by
    simpa only [Pi.smul_def, smul_eq_mul, zero_sub, neg_mul] using hF
  exact hH (Submodule.mem_sup.mpr ⟨H,
    scalar_mem_of_nonzero_smul _ _ (neg_ne_zero.mpr hpa) H hs,
    0, Submodule.zero_mem _, by simp⟩)

/-- Three colors and injectivity of both endpoint maps supply a color
avoiding a prescribed outgoing neighbor at both endpoints. -/
theorem exists_endpoint_avoiding
    (π : ι → Equiv.Perm Ω) (o : Ω) (B : Set ι)
    (hout : Function.Injective (fun a => π a o))
    (hin : Function.Injective (fun a => (π a).symm o))
    (hthree : ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B,
      π a ≠ π b ∧ π a ≠ π c ∧ π b ≠ π c) (x : Ω) :
    ∃ b ∈ B, π b o ≠ x ∧ (π b).symm o ≠ x := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := hthree
  by_contra hh
  push_neg at hh
  have hcases : ∀ j ∈ B, π j o = x ∨ (π j).symm o = x := by
    intro j hj
    by_cases h : π j o = x
    · exact Or.inl h
    · exact Or.inr (hh j hj h)
  rcases hcases a ha with h₁ | h₁ <;>
    rcases hcases b hb with h₂ | h₂ <;>
    rcases hcases c hc with h₃ | h₃
  all_goals first
    | exact hab (congrArg π (hout (h₁.trans h₂.symm)))
    | exact hab (congrArg π (hin (h₁.trans h₂.symm)))
    | exact hac (congrArg π (hout (h₁.trans h₃.symm)))
    | exact hac (congrArg π (hin (h₁.trans h₃.symm)))
    | exact hbc (congrArg π (hout (h₂.trans h₃.symm)))
    | exact hbc (congrArg π (hin (h₂.trans h₃.symm)))

lemma endpoint_identity
    (o : Ω) (π : Equiv.Perm Ω) (ho : π o ≠ o)
    (H M : Ω → K) (hHo : H o = 0) (hMo : M o = 0) (r c d t : K)
    (hcd : c + d = 0)
    (hout : M (π o) - r * H (π o) = t)
    (hin : M (π.symm o) - r * H (π.symm o) = t)
    (h : ∀ x, r * (H x - H (π x)) =
      c + ratioValue o π x * (d + M x - M (π x))) :
    t + r * (H (π o) + H (π.symm o)) = 0 := by
  have h₀ := h o
  have h₁ := h (π.symm o)
  norm_num [ratioValue, TwoRatioRigidity.ratio, TwoRatioRigidity.scale,
    ho, inverse_moves ho, hHo, hMo] at h₀ h₁
  linear_combination -2 * h₀ - h₁ - 3 * hcd + hout - 2 * hin

/-- The ordinary-edge argument and two endpoint equations kill the common
coefficient on the second support. -/
theorem common_second_coefficient_zero
    (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hdis : Disjoint A B) (hm : 5 ≤ Fintype.card Ω)
    (hder : ∀ a, ∀ x, π a x ≠ x)
    (hthree : ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B,
      π a ≠ π b ∧ π a ≠ π c ∧ π b ≠ π c)
    (hconn : ∀ x y, Relation.EqvGen (PuncturedBothEndpoints.OrdinaryEdge o π B) x y)
    (hout : Function.Injective (fun a => π a o))
    (hin : Function.Injective (fun a => (π a).symm o))
    (p : ι → K) (hp : TorusContact π o A B p)
    (r : K) (hpr : ∀ a ∈ B, p a = r) : r = 0 := by
  classical
  have hcard : Fintype.card {x : Ω // x ≠ o} = Fintype.card Ω - 1 := by
    simpa only [Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun x : Ω => x = o)
  letI : Nontrivial {x : Ω // x ≠ o} := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hthreeCopy := hthree
  obtain ⟨a, ha, _, _, _, _, _, _, _⟩ := hthreeCopy
  let H : Ω → K := fun x => if x = π a o then 1 else 0
  have hHo : H o = 0 := by simp [H, Ne.symm (hder a o)]
  obtain ⟨c, J, d, M, _, hMo, ht⟩ := (mem_tangentSpan_iff_field π o A B _).mp (hp H)
  have hE : ∀ b ∈ B, ∀ x, r * (H x - H (π b x)) =
      c b + ratioValue o (π b) x * (d b + M x - M (π b x)) := by
    intro b hb x
    have hbA : b ∉ A := fun h => Set.disjoint_left.mp hdis h hb
    simpa only [hpr b hb, if_neg hbA, if_pos hb, add_zero, add_sub_assoc] using ht b x
  let F : {x : Ω // x ≠ o} → K := fun x => M x - r * H x
  have hOrd : ∀ b ∈ B, ∀ (x : Ω) (hx : x ≠ o) (hy : π b x ≠ o),
      F ⟨π b x, hy⟩ - F ⟨x, hx⟩ = c b + d b := by
    intro b hb x hx hy
    have hh := hE b hb x
    simp only [ratioValue, TwoRatioRigidity.ratio, TwoRatioRigidity.scale,
      if_neg hx, if_neg hy, div_self (by norm_num : (2 : ℚ) ≠ 0), map_one, one_mul] at hh
    dsimp [F]
    linear_combination hh
  have hcd := PuncturedBothEndpoints.family (fun b _ => hder b) hthree hOrd
  have hF := PuncturedBothEndpoints.constant_of_connected
    (fun b _ => hder b) hthree hOrd hconn
  let t := F ⟨π a o, hder a o⟩
  have htE : ∀ b ∈ B, t + r * (H (π b o) + H ((π b).symm o)) = 0 := by
    intro b hb
    apply endpoint_identity o (π b) (hder b o) H M hHo hMo r (c b) (d b) t (hcd b hb)
    · exact hF ⟨π b o, hder b o⟩ ⟨π a o, hder a o⟩
    · exact hF ⟨(π b).symm o, inverse_moves (hder b o)⟩ ⟨π a o, hder a o⟩
    · exact hE b hb
  obtain ⟨b, hb, hbo, hbi⟩ := exists_endpoint_avoiding π o B hout hin hthree (π a o)
  have ht : t = 0 := by simpa [H, hbo, hbi] using htE b hb
  have hh := htE a ha
  rw [ht] at hh
  by_cases hia : (π a).symm o = π a o
  · have he : 2 * r = 0 := by simpa [H, hia, mul_two, two_mul] using hh
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  · simpa [H, hia] using hh

end Sunlet.Contact
