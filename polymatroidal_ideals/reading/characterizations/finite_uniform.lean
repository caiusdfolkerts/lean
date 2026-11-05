import Characterizations.OptimalOrders
import Mathlib.Algebra.Group.End

/-! # Exact finite uniform probabilities and equally sized fibers -/

noncomputable section
namespace Characterizations
open Classical Finset

variable {X Y : Type*} [Fintype X] [Fintype Y]

def finiteFraction (P : X → Prop) : ℝ := (Nat.card {x // P x} : ℝ) / Nat.card X

def preimageSigmaEquiv (f : X → Y) (P : Y → Prop) :
    {x // P (f x)} ≃ Σ y : {y // P y}, {x // f x = y.val} where
  toFun x := ⟨⟨f x.val,x.property⟩,⟨x.val,rfl⟩⟩
  invFun y := ⟨y.2.val, by rw [y.2.property]; exact y.1.property⟩
  left_inv _ := rfl
  right_inv y := by rcases y with ⟨⟨y,hy⟩,⟨x,hx⟩⟩; dsimp at hx; subst y; rfl

theorem card_preimage_of_constant_fiber (f : X → Y) (P : Y → Prop) (c : ℕ)
    (hc : ∀ y, Nat.card {x // f x = y} = c) :
    Nat.card {x // P (f x)} = Nat.card {y // P y} * c := by
  rw [Nat.card_congr (preimageSigmaEquiv f P), Nat.card_sigma]
  simp_rw [hc]
  simp [Nat.card_eq_fintype_card]

theorem fraction_preimage_of_constant_fiber [Nonempty X] (f : X → Y) (P : Y → Prop)
    (c : ℕ) (hc : ∀ y, Nat.card {x // f x = y} = c) :
    finiteFraction (fun x => P (f x)) = finiteFraction P := by
  have hX : Nat.card X = Nat.card Y * c := by
    simpa using card_preimage_of_constant_fiber f (fun _ => True) c hc
  have hcpos : 0 < c := by
    have hh : 0 < Nat.card X := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos
    nlinarith
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcpos)
  unfold finiteFraction
  rw [card_preimage_of_constant_fiber f P c hc, hX]
  push_cast
  rw [mul_div_mul_right _ _ hcR]

theorem variableOrder_eq_of_lt_iff {V : Type*} [Fintype V]
    (o₁ o₂ : VariableOrder V)
    (h : ∀ a b, o₁ a < o₁ b ↔ o₂ a < o₂ b) : o₁ = o₂ := by
  have hs : StrictMono (fun x => o₂ (o₁.symm x)) := by
    intro a b hab
    exact (h _ _).mp (by simpa using hab)
  apply Equiv.ext
  intro x
  have hh := hs.apply_eq (x := o₁ x)
  simpa using hh.symm

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem restrictedOrder_comp_subtype (T : Finset V) (o : VariableOrder V)
    (π : Equiv.Perm T) :
    restrictedOrder ((Equiv.Perm.ofSubtype π).trans o) (Function.Embedding.subtype (· ∈ T)) =
      π.trans (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) := by
  apply variableOrder_eq_of_lt_iff
  intro a b
  rw [restrictedOrder_lt_iff]
  simp only [Equiv.trans_apply, Function.Embedding.subtype_apply, Equiv.Perm.ofSubtype_apply_coe]
  exact (restrictedOrder_lt_iff o (Function.Embedding.subtype (· ∈ T)) (π a) (π b)).symm

def restrictionFiberEquiv (T : Finset V) (r₁ r₂ : VariableOrder T) :
    {o : VariableOrder V // restrictedOrder o (Function.Embedding.subtype (· ∈ T)) = r₁} ≃
    {o : VariableOrder V // restrictedOrder o (Function.Embedding.subtype (· ∈ T)) = r₂} := by
  let π := r₂.trans r₁.symm
  let σ : Equiv.Perm V := Equiv.Perm.ofSubtype π
  refine {
    toFun := fun o => ⟨σ.trans o.val, ?_⟩
    invFun := fun o => ⟨σ.symm.trans o.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [restrictedOrder_comp_subtype, o.property]
    ext a
    simp [π]
  · have hσ : σ.symm = Equiv.Perm.ofSubtype π.symm :=
      (map_inv (Equiv.Perm.ofSubtype) π).symm
    rw [hσ, restrictedOrder_comp_subtype, o.property]
    ext a
    simp [π]
  · intro o
    apply Subtype.ext
    ext a
    simp
  · intro o
    apply Subtype.ext
    ext a
    simp

theorem restriction_uniform (T : Finset V) (P : VariableOrder T → Prop) :
    finiteFraction (fun o : VariableOrder V => P (restrictedOrder o (Function.Embedding.subtype (· ∈ T)))) =
      finiteFraction P := by
  classical
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  let r₀ : VariableOrder T := Fintype.equivFin T
  let c := Nat.card {o : VariableOrder V //
    restrictedOrder o (Function.Embedding.subtype (· ∈ T)) = r₀}
  apply fraction_preimage_of_constant_fiber _ P c
  intro r
  exact Nat.card_congr (restrictionFiberEquiv T r r₀)

end Characterizations
