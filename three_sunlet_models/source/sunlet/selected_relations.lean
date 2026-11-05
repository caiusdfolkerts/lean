module

public import sunlet.basic
public import sunlet.permutation_families

/-! The exact kernel of the selected monomial exponent matrix. -/

@[expose] public section
noncomputable section

namespace Sunlet.SelectedRelations

variable {ι Ω : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]

/-- This is precisely the table of least-weight terms in Theorem 2.3. -/
def selectsU (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] (a : ι) (b : Ω) : Prop :=
  if a ∈ P then b ≠ (π a).symm o else a ≠ e ∧ b = o

instance {π : ι → Equiv.Perm Ω} {e : ι} {o : Ω} {P : Set ι}
    [DecidablePred (· ∈ P)] (a : ι) (b : Ω) :
    Decidable (selectsU π e o P a b) := by unfold selectsU; infer_instance

def RelationEquation (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] (w : ParamVar ι Ω → ℚ) (a : ι) (b : Ω) : Prop :=
  w (.s b) + w (.t (π a b)) +
    (if selectsU π e o P a b then w (.u a) + w (.h (π a b))
     else w (.v a) + w (.h b)) = 0

def IsRelation (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] (w : ParamVar ι Ω → ℚ) : Prop :=
  ∀ a b, RelationEquation π e o P w a b

/-- The four scaling and identity-row directions, with no extra free parameters. -/
def canonical (e : ι) (s k v u : ℚ) : ParamVar ι Ω → ℚ
  | .s _ => s
  | .t _ => -k - v
  | .h _ => k - s
  | .u a => if a = e then u else v
  | .v _ => v

theorem selectsU_base {π : ι → Equiv.Perm Ω} {e : ι} {o : Ω} {P : Set ι}
    [DecidablePred (· ∈ P)] (heP : e ∉ P) (b : Ω) :
    ¬selectsU π e o P e b := by simp [selectsU, heP]

theorem selectsU_at_base {π : ι → Equiv.Perm Ω} {e a : ι} {o : Ω} {P : Set ι}
    [DecidablePred (· ∈ P)] (ha : a ≠ e) (hfix : π a o ≠ o) :
    selectsU π e o P a o := by
  have hne : o ≠ (π a).symm o := by
    intro h
    apply hfix
    calc
      π a o = π a ((π a).symm o) := congrArg (π a) h
      _ = o := Equiv.apply_symm_apply _ _
  by_cases haP : a ∈ P <;> simp [selectsU, haP, ha, hne]

theorem selectsV_at_preimage {π : ι → Equiv.Perm Ω} {e a : ι} {o : Ω} {P : Set ι}
    [DecidablePred (· ∈ P)] (hfix : π a o ≠ o) :
    ¬selectsU π e o P a ((π a).symm o) := by
  have hne : (π a).symm o ≠ o := by
    intro h
    have hh := congrArg (π a) h
    simp only [Equiv.apply_symm_apply] at hh
    exact hfix hh.symm
  by_cases haP : a ∈ P <;> simp [selectsU, haP, hne]

theorem canonical_isRelation (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω)
    (P : Set ι) [DecidablePred (· ∈ P)] (heP : e ∉ P) (s k v u : ℚ) :
    IsRelation π e o P (canonical e s k v u) := by
  intro a b
  unfold RelationEquation
  by_cases hs : selectsU π e o P a b
  · have ha : a ≠ e := by
      intro he
      subst a
      exact selectsU_base heP b hs
    simp only [if_pos hs, canonical, if_neg ha]
    ring
  · simp only [if_neg hs, canonical]
    ring

/-- The exponent relations have exactly the four degrees of freedom in equation (2).
All the equations here are literal dot products with selected monomial exponents. -/
theorem relation_canonical
    (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P N : Set ι)
    [DecidablePred (· ∈ P)]
    (he : π e = Equiv.refl Ω) (heP : e ∉ P)
    (hPN : Disjoint P N)
    (hder : ∀ a, a ≠ e → ∀ b, π a b ≠ b)
    (hPne : ∀ a ∈ P, a ≠ e) (hNne : ∀ a ∈ N, a ≠ e)
    (hPtwo : ∃ a ∈ P, ∃ b ∈ P, π a ≠ π b)
    (hNtwo : ∃ a ∈ N, ∃ b ∈ N, π a ≠ π b)
    (hPtr : TransitiveFamily π P) (hNtr : TransitiveFamily π N)
    (w : ParamVar ι Ω → ℚ) (hw : IsRelation π e o P w) :
    w = canonical e (w (.s o)) (w (.s o) + w (.h o)) (w (.v e)) (w (.u e)) := by
  let S : Ω → ℚ := fun b => w (.s b)
  let K : Ω → ℚ := fun b => w (.s b) + w (.h b)
  let v : ℚ := w (.v e)
  have ht (b : Ω) : w (.t b) = -w (.s b) - w (.h b) - v := by
    have hh := hw e b
    simp only [RelationEquation, if_neg (selectsU_base heP b), he,
      Equiv.refl_apply] at hh
    dsimp [v]
    linarith
  have hpne : ∀ a ∈ P, π a ≠ 1 := by
    intro a ha hh
    have h := hder a (hPne a ha) o
    exact h (by rw [hh]; rfl)
  have hnne : ∀ a ∈ N, π a ≠ 1 := by
    intro a ha hh
    have h := hder a (hNne a ha) o
    exact h (by rw [hh]; rfl)
  have hp : ∀ a ∈ P, ∀ b, b ≠ (π a).symm o →
      S (π a b) - S b = w (.u a) - v := by
    intro a ha b hb
    have hs : selectsU π e o P a b := by simp [selectsU, ha, hb]
    have hh := hw a b
    simp only [RelationEquation, if_pos hs] at hh
    dsimp [S]
    linarith [ht (π a b)]
  have hn : ∀ a ∈ N, PuncturedDifferences.Outgoing o (π a) K (w (.v a) - v) := by
    intro a ha b hb
    have haP : a ∉ P := fun h => Set.disjoint_left.mp hPN h ha
    have hs : ¬selectsU π e o P a b := by simp [selectsU, haP, hb]
    have hh := hw a b
    simp only [RelationEquation, if_neg hs] at hh
    dsimp [K]
    linarith [ht (π a b)]
  have hS := PuncturedDifferences.constant_of_incoming_transitive hpne hPtwo hPtr hp
  have hK := PuncturedDifferences.constant_of_outgoing_transitive hnne hNtwo hNtr hn
  have hs (b : Ω) : w (.s b) = w (.s o) := hS b
  have hh (b : Ω) : w (.h b) = w (.h o) := by
    have hk := hK b
    dsimp [K] at hk
    linarith [hs b]
  have hu (a : ι) (ha : a ≠ e) : w (.u a) = v := by
    have hsel := selectsU_at_base (π := π) (o := o) (P := P) ha (hder a ha o)
    have hr := hw a o
    simp only [RelationEquation, if_pos hsel] at hr
    linarith [ht (π a o), hs (π a o)]
  have hv (a : ι) : w (.v a) = v := by
    by_cases ha : a = e
    · subst a; rfl
    · have hsel := selectsV_at_preimage (π := π) (e := e) (P := P) (hder a ha o)
      have hr := hw a ((π a).symm o)
      simp only [RelationEquation, if_neg hsel, Equiv.apply_symm_apply] at hr
      linarith [ht o, hs ((π a).symm o), hh ((π a).symm o)]
  funext i
  cases i with
  | s b => exact hs b
  | t b => dsimp [canonical]; linarith [ht b, hs b, hh b]
  | h b => dsimp [canonical]; linarith [hh b]
  | u a =>
      dsimp [canonical]
      by_cases ha : a = e
      · simp [ha]
      · simpa [ha, v] using hu a ha
  | v a => exact hv a

end Sunlet.SelectedRelations
