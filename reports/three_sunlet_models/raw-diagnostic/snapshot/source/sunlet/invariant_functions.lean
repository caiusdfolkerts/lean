module

public import sunlet.permutation_families
public import Mathlib.Data.Fintype.Quotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Lean.Elab.Tactic.Omega

/-! Dimension bounds for normalized invariant functions of a derangement. -/

@[expose] public section
noncomputable section

namespace Sunlet.InvariantFunctions

variable {Ω K : Type*} [Fintype Ω] [DecidableEq Ω] [Field K]

def orbitSetoid (π : Equiv.Perm Ω) : Setoid Ω :=
  Relation.EqvGen.setoid (fun x y => π x = y)

abbrev Orbit (π : Equiv.Perm Ω) := Quotient (orbitSetoid π)

instance orbitFintype (π : Equiv.Perm Ω) : Fintype (Orbit π) := Fintype.ofFinite _

def orbitClass (π : Equiv.Perm Ω) (x : Ω) : Orbit π := Quotient.mk _ x

@[simp] theorem orbitClass_out (π : Equiv.Perm Ω) (q : Orbit π) :
    orbitClass π q.out = q := Quotient.out_eq q

theorem orbitClass_step (π : Equiv.Perm Ω) (x : Ω) :
    orbitClass π (π x) = orbitClass π x := by
  apply Quotient.sound
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ rfl)

/-- Choosing a representative and its distinct image embeds two points per
orbit. This proves the orbit bound without a cycle decomposition. -/
theorem twice_card_orbit_le (π : Equiv.Perm Ω) (hder : ∀ x, π x ≠ x) :
    2 * Fintype.card (Orbit π) ≤ Fintype.card Ω := by
  classical
  let f : Orbit π × Bool → Ω := fun z => if z.2 then π z.1.out else z.1.out
  have hclass (z : Orbit π × Bool) : orbitClass π (f z) = z.1 := by
    rcases z with ⟨q, b⟩
    cases b <;> simp [f, orbitClass_step]
  have hinj : Function.Injective f := by
    rintro ⟨q, b⟩ ⟨q', b'⟩ he
    have hq : q = q' := by
      exact (hclass (q, b)).symm.trans ((congrArg (orbitClass π) he).trans (hclass (q', b')))
    subst q'
    have hb : b = b' := by
      cases b <;> cases b' <;> simp_all [f, hder, Ne.symm (hder q.out)]
    exact congrArg (fun b => (q, b)) hb
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using hc

def normalized (o : Ω) (π : Equiv.Perm Ω) : Submodule K (Ω → K) where
  carrier := {F | F o = 0 ∧ ∀ x, F (π x) = F x}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG
    exact ⟨by simp [hF.1, hG.1], fun x => by simp [hF.2 x, hG.2 x]⟩
  smul_mem' := by
    intro a F hF
    exact ⟨by simp [hF.1], fun x => by simp [hF.2 x]⟩

lemma invariant_of_equivalent {π : Equiv.Perm Ω} {F : Ω → K}
    (hF : ∀ x, F (π x) = F x) {x y : Ω}
    (h : orbitSetoid π x y) : F x = F y := by
  induction h with
  | rel x y he => rw [← he]; exact (hF x).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def descend (o : Ω) (π : Equiv.Perm Ω) :
    normalized (K := K) o π →ₗ[K] ({q : Orbit π // q ≠ orbitClass π o} → K) where
  toFun F q := F.1 q.1.out
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem descend_injective (o : Ω) (π : Equiv.Perm Ω) :
    Function.Injective (descend (K := K) o π) := by
  intro F G hFG
  apply Subtype.ext
  funext x
  have hFout : F.1 (orbitClass π x).out = F.1 x :=
    invariant_of_equivalent F.2.2 (Quotient.exact (Quotient.out_eq (orbitClass π x)))
  have hGout : G.1 (orbitClass π x).out = G.1 x :=
    invariant_of_equivalent G.2.2 (Quotient.exact (Quotient.out_eq (orbitClass π x)))
  by_cases hx : orbitClass π x = orbitClass π o
  · have he : orbitSetoid π x o := Quotient.exact hx
    rw [invariant_of_equivalent F.2.2 he, invariant_of_equivalent G.2.2 he, F.2.1, G.2.1]
  · have he := congrArg (fun f => f ⟨orbitClass π x, hx⟩) hFG
    exact hFout.symm.trans (he.trans hGout)

theorem finrank_le_card_orbit_sub_one (o : Ω) (π : Equiv.Perm Ω) :
    Module.finrank K (normalized (K := K) o π) ≤ Fintype.card (Orbit π) - 1 := by
  classical
  have h := LinearMap.finrank_le_finrank_of_injective (descend_injective (K := K) o π)
  have hc : Fintype.card {q : Orbit π // q ≠ orbitClass π o} = Fintype.card (Orbit π) - 1 := by
    simpa only [Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun q : Orbit π => q = orbitClass π o)
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, smul_eq_mul,
    mul_one, Finset.card_univ, hc] using h

theorem normalized_rank_bound (o : Ω) (π : Equiv.Perm Ω) (hder : ∀ x, π x ≠ x) :
    2 * (Module.finrank K (normalized (K := K) o π) + 1) ≤ Fintype.card Ω := by
  have hdim := finrank_le_card_orbit_sub_one (K := K) o π
  have hcard := twice_card_orbit_le π hder
  have hpos : 0 < Fintype.card (Orbit π) := Fintype.card_pos_iff.mpr ⟨orbitClass π o⟩
  omega

end Sunlet.InvariantFunctions
