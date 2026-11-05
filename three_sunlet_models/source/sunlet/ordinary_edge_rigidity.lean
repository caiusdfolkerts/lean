module

public import sunlet.punctured_both_endpoints

/-! Lemma 4.4: three distinct derangements force the constants on ordinary
edges to vanish. The argument uses the spliced one-hole permutations. -/

@[expose] public section
noncomputable section

namespace Sunlet.PuncturedBothEndpoints

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem eq_of_negative_steps {o : Ω} {π σ : Equiv.Perm Ω}
    {F : {x : Ω // x ≠ o} → ℚ} {c d : ℚ}
    [Nontrivial {x : Ω // x ≠ o}]
    (hπo : π o ≠ o) (hσo : σ o ≠ o)
    (hπ : Ordinary o π F c) (hσ : Ordinary o σ F d)
    (hc : c < 0) (hd : d < 0) : π = σ := by
  have hπ' : Ordinary o π (fun x => -F x) (-c) := by
    intro x hx hy
    have hh := hπ x hx hy
    dsimp
    linarith
  have hσ' : Ordinary o σ (fun x => -F x) (-d) := by
    intro x hx hy
    have hh := hσ x hx hy
    dsimp
    linarith
  exact eq_of_positive_steps hπo hσo hπ' hσ' (neg_pos.mpr hc) (neg_pos.mpr hd)

lemma constant_ne_zero_of_injective {o : Ω} {π : Equiv.Perm Ω}
    {F : {x : Ω // x ≠ o} → ℚ} {c : ℚ}
    [Nontrivial {x : Ω // x ≠ o}]
    (hder : ∀ x, π x ≠ x) (hF : Function.Injective F) (h : Ordinary o π F c) : c ≠ 0 := by
  intro hc
  obtain ⟨x, hx⟩ := exists_ne (hole o π (hder o))
  have hp : π x ≠ o := by
    intro he
    apply hx
    apply Subtype.ext
    exact π.injective (he.trans (π.apply_symm_apply o).symm)
  have hh := h x x.property hp
  rw [hc] at hh
  have he := congrArg Subtype.val (hF (sub_eq_zero.mp hh))
  exact hder x he

lemma not_three_nonzero_steps {o : Ω} {π σ τ : Equiv.Perm Ω}
    {F : {x : Ω // x ≠ o} → ℚ} {c d e : ℚ}
    [Nontrivial {x : Ω // x ≠ o}]
    (hπo : π o ≠ o) (hσo : σ o ≠ o) (hτo : τ o ≠ o)
    (hπσ : π ≠ σ) (hπτ : π ≠ τ) (hστ : σ ≠ τ)
    (hπ : Ordinary o π F c) (hσ : Ordinary o σ F d) (hτ : Ordinary o τ F e)
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) : False := by
  rcases lt_or_gt_of_ne hc with hc | hc <;>
    rcases lt_or_gt_of_ne hd with hd | hd <;>
    rcases lt_or_gt_of_ne he with he | he
  all_goals first
    | exact hπσ (eq_of_negative_steps hπo hσo hπ hσ hc hd)
    | exact hπσ (eq_of_positive_steps hπo hσo hπ hσ hc hd)
    | exact hπτ (eq_of_negative_steps hπo hτo hπ hτ hc he)
    | exact hπτ (eq_of_positive_steps hπo hτo hπ hτ hc he)
    | exact hστ (eq_of_negative_steps hσo hτo hσ hτ hd he)
    | exact hστ (eq_of_positive_steps hσo hτo hσ hτ hd he)

/-- The rational form of the both-endpoints-omitted lemma. -/
theorem family_rational {ι : Type*} {o : Ω} {π : ι → Equiv.Perm Ω} {P : Set ι}
    [Nontrivial {x : Ω // x ≠ o}]
    {F : {x : Ω // x ≠ o} → ℚ} {c : ι → ℚ}
    (hder : ∀ a ∈ P, ∀ x, π a x ≠ x)
    (hthree : ∃ a ∈ P, ∃ b ∈ P, ∃ d ∈ P,
      π a ≠ π b ∧ π a ≠ π d ∧ π b ≠ π d)
    (h : ∀ a ∈ P, Ordinary o (π a) F (c a)) : ∀ a ∈ P, c a = 0 := by
  obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := hthree
  intro j hj
  by_contra hcj
  have hF := PuncturedDifferences.injective_of_nonzero
    (outgoing_of_ordinary (hder j hj o) (h j hj)) hcj
  exact not_three_nonzero_steps (hder a ha o) (hder b hb o) (hder d hd o)
    hab had hbd (h a ha) (h b hb) (h d hd)
    (constant_ne_zero_of_injective (hder a ha) hF (h a ha))
    (constant_ne_zero_of_injective (hder b hb) hF (h b hb))
    (constant_ne_zero_of_injective (hder d hd) hF (h d hd))

/-- Lemma 4.4 over every rational vector space, including the paper's complex
functions. Nontriviality of the punctured vertex set holds whenever m≥3. -/
theorem family {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    {o : Ω} {π : ι → Equiv.Perm Ω} {P : Set ι}
    [Nontrivial {x : Ω // x ≠ o}]
    {F : {x : Ω // x ≠ o} → V} {c : ι → V}
    (hder : ∀ a ∈ P, ∀ x, π a x ≠ x)
    (hthree : ∃ a ∈ P, ∃ b ∈ P, ∃ d ∈ P,
      π a ≠ π b ∧ π a ≠ π d ∧ π b ≠ π d)
    (h : ∀ a ∈ P, ∀ (x : Ω) (hx : x ≠ o) (hy : π a x ≠ o),
      F ⟨π a x, hy⟩ - F ⟨x, hx⟩ = c a) : ∀ a ∈ P, c a = 0 := by
  intro a ha
  apply (Module.forall_dual_apply_eq_zero_iff ℚ (c a)).mp
  intro φ
  exact family_rational hder hthree (F := fun x => φ (F x)) (c := fun a => φ (c a))
    (fun j hj x hx hy => by simpa only [map_sub] using congrArg φ (h j hj x hx hy)) a ha

def OrdinaryEdge {ι : Type*} (o : Ω) (π : ι → Equiv.Perm Ω) (P : Set ι)
    (x y : {x : Ω // x ≠ o}) : Prop := ∃ a ∈ P, π a x = y

/-- Once the constants vanish, connectedness of the ordinary-edge graph gives
the last assertion of Lemma 4.4. -/
theorem constant_of_connected {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    {o : Ω} {π : ι → Equiv.Perm Ω} {P : Set ι}
    [Nontrivial {x : Ω // x ≠ o}]
    {F : {x : Ω // x ≠ o} → V} {c : ι → V}
    (hder : ∀ a ∈ P, ∀ x, π a x ≠ x)
    (hthree : ∃ a ∈ P, ∃ b ∈ P, ∃ d ∈ P,
      π a ≠ π b ∧ π a ≠ π d ∧ π b ≠ π d)
    (h : ∀ a ∈ P, ∀ (x : Ω) (hx : x ≠ o) (hy : π a x ≠ o),
      F ⟨π a x, hy⟩ - F ⟨x, hx⟩ = c a)
    (hconn : ∀ x y, Relation.EqvGen (OrdinaryEdge o π P) x y) : ∀ x y, F x = F y := by
  have hc := family hder hthree h
  intro x y
  induction hconn x y with
  | rel x y he =>
    obtain ⟨a, ha, he⟩ := he
    have hp : π a x ≠ o := by rw [he]; exact y.property
    have hh := h a ha x x.property hp
    rw [hc a ha] at hh
    have hxy : (⟨π a x, hp⟩ : {x : Ω // x ≠ o}) = y := Subtype.ext he
    rw [hxy] at hh
    exact (sub_eq_zero.mp hh).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Sunlet.PuncturedBothEndpoints
