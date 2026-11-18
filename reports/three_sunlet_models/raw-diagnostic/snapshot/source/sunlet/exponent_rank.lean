module

public import sunlet.selected_relations
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic.FinCases
public import Lean.Elab.Tactic.Omega

/-! Exact rank of the actual selected monomial exponent matrix. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Sunlet.SelectedRelations

namespace Sunlet.ExponentRank

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]

def paramVarEquiv : ParamVar ι Ω ≃ (Ω ⊕ (Ω ⊕ (Ω ⊕ (ι ⊕ ι)))) where
  toFun
    | .s b => .inl b
    | .t b => .inr (.inl b)
    | .h b => .inr (.inr (.inl b))
    | .u a => .inr (.inr (.inr (.inl a)))
    | .v a => .inr (.inr (.inr (.inr a)))
  invFun
    | .inl b => .s b
    | .inr (.inl b) => .t b
    | .inr (.inr (.inl b)) => .h b
    | .inr (.inr (.inr (.inl a))) => .u a
    | .inr (.inr (.inr (.inr a))) => .v a
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with b | b | b | a | a <;> rfl

theorem card_paramVar : Fintype.card (ParamVar ι Ω) = 3 * Fintype.card Ω + 2 * Fintype.card ι := by
  have h := Fintype.card_congr (paramVarEquiv (ι := ι) (Ω := Ω))
  simp only [Fintype.card_sum] at h
  omega

def relationMap (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] : (ParamVar ι Ω → ℚ) →ₗ[ℚ] (ι × Ω → ℚ) where
  toFun w ab := w (.s ab.2) + w (.t (π ab.1 ab.2)) +
    if selectsU π e o P ab.1 ab.2 then w (.u ab.1) + w (.h (π ab.1 ab.2))
    else w (.v ab.1) + w (.h ab.2)
  map_add' w z := by
    funext ab
    dsimp
    split_ifs <;> ring
  map_smul' r w := by
    funext ab
    dsimp
    split_ifs <;> ring

theorem mem_ker_iff (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] (w : ParamVar ι Ω → ℚ) :
    w ∈ (relationMap π e o P).ker ↔ IsRelation π e o P w := by
  simp only [LinearMap.mem_ker, funext_iff, Prod.forall, relationMap, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.zero_apply, IsRelation, RelationEquation]

def canonicalLinear (e : ι) : (Fin 4 → ℚ) →ₗ[ℚ] (ParamVar ι Ω → ℚ) where
  toFun q := canonical e (q 0) (q 1) (q 2) (q 3)
  map_add' q r := by
    funext i
    cases i <;> simp only [canonical, Pi.add_apply] <;> (try split_ifs) <;> ring
  map_smul' r q := by
    funext i
    cases i <;> simp only [canonical, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;>
      (try split_ifs) <;> ring

def decodeLinear (e : ι) (o : Ω) : (ParamVar ι Ω → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) where
  toFun w := ![w (.s o), w (.s o) + w (.h o), w (.v e), w (.u e)]
  map_add' w z := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r w := by ext i; fin_cases i <;> simp <;> ring

theorem decode_canonical (e : ι) (o : Ω) (q : Fin 4 → ℚ) :
    decodeLinear e o (canonicalLinear e q) = q := by
  ext i
  fin_cases i <;> simp [decodeLinear, canonicalLinear, canonical]

theorem canonical_injective (e : ι) (o : Ω) :
    Function.Injective (canonicalLinear (Ω := Ω) e) := by
  intro q r h
  have hh := congrArg (decodeLinear e o) h
  simpa [decode_canonical] using hh

def canonicalKer (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] (heP : e ∉ P) :
    (Fin 4 → ℚ) →ₗ[ℚ] (relationMap π e o P).ker :=
  (canonicalLinear e).codRestrict _ fun q =>
    (mem_ker_iff π e o P _).mpr (canonical_isRelation π e o P heP (q 0) (q 1) (q 2) (q 3))

theorem canonicalKer_injective (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] (heP : e ∉ P) :
    Function.Injective (canonicalKer π e o P heP) := by
  intro q r h
  apply canonical_injective e o
  exact congrArg Subtype.val h

theorem finrank_ker
    (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P N : Set ι)
    [DecidablePred (· ∈ P)]
    (he : π e = Equiv.refl Ω) (heP : e ∉ P)
    (hPN : Disjoint P N)
    (hder : ∀ a, a ≠ e → ∀ b, π a b ≠ b)
    (hPne : ∀ a ∈ P, a ≠ e) (hNne : ∀ a ∈ N, a ≠ e)
    (hPtwo : ∃ a ∈ P, ∃ b ∈ P, π a ≠ π b)
    (hNtwo : ∃ a ∈ N, ∃ b ∈ N, π a ≠ π b)
    (hPtr : TransitiveFamily π P) (hNtr : TransitiveFamily π N) :
    Module.finrank ℚ (relationMap π e o P).ker = 4 := by
  have hsurj : Function.Surjective (canonicalKer π e o P heP) := by
    intro w
    refine ⟨decodeLinear e o w, ?_⟩
    apply Subtype.ext
    have hh := relation_canonical π e o P N he heP hPN hder hPne hNne hPtwo hNtwo hPtr hNtr
      w ((mem_ker_iff π e o P w).mp w.property)
    exact hh.symm
  let E := LinearEquiv.ofBijective (canonicalKer π e o P heP)
    ⟨canonicalKer_injective π e o P heP, hsurj⟩
  have h := E.finrank_eq
  simpa using h.symm

theorem finrank_range_add_four
    (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P N : Set ι)
    [DecidablePred (· ∈ P)]
    (he : π e = Equiv.refl Ω) (heP : e ∉ P)
    (hPN : Disjoint P N)
    (hder : ∀ a, a ≠ e → ∀ b, π a b ≠ b)
    (hPne : ∀ a ∈ P, a ≠ e) (hNne : ∀ a ∈ N, a ≠ e)
    (hPtwo : ∃ a ∈ P, ∃ b ∈ P, π a ≠ π b)
    (hNtwo : ∃ a ∈ N, ∃ b ∈ N, π a ≠ π b)
    (hPtr : TransitiveFamily π P) (hNtr : TransitiveFamily π N) :
    Module.finrank ℚ (relationMap π e o P).range + 4 =
      3 * Fintype.card Ω + 2 * Fintype.card ι := by
  have h := (relationMap π e o P).finrank_range_add_finrank_ker
  rw [finrank_ker π e o P N he heP hPN hder hPne hNne hPtwo hNtwo hPtr hNtr] at h
  simpa [Module.finrank_pi, card_paramVar] using h

end Sunlet.ExponentRank
