module

public import ToricPower.PointClosedPullback

/-! # Literal closed coefficient functors for equivalent supports -/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower.Cellular

variable (R : Type) [Ring R] {B : Type} [Preorder B]
  (P Q : B → Prop) (downP : Antitone P) (downQ : Antitone Q)
  (same : ∀ b, P b ↔ Q b)

/-- Replacing a support by an equivalent predicate preserves every
coefficient and every original face map. -/
def closedConstantCongrIso :
    closedConstantFunctor R P downP ≅ closedConstantFunctor R Q downQ :=
  NatIso.ofComponents (fun M => NatIso.ofComponents (fun b =>
    ({ toFun := fun x h => x ⟨(same b).mpr h.down⟩
       invFun := fun x h => x ⟨(same b).mp h.down⟩
       left_inv := by intro x; rfl
       right_inv := by intro x; rfl
       map_add' := by intros; rfl
       map_smul' := by intros; rfl } :
      (PLift (P b) → M) ≃ₗ[R] (PLift (Q b) → M)).toModuleIso)
      (by intros; rfl)) (by intros; rfl)

end ToricPower.Cellular

end
