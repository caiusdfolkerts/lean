module

public import Papers.GraphicalZonotopes.WeightedPureBlocks

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

/-- Finite reindexing of pure module data preserves the exact weighted
relation and all positive integral scale bounds. -/
def weightedPureBlock_of_data (C : Finset H) (M : ℤ) (v : ResponseQuotient H)
    (x : J → PairIn C → ℝ) (hx : ∀ j,PureRealizable C (x j))
    (w : J → ℤ) (hw : ∀ j,0<w j) (hM : ∀ j,w j≤M)
    (hind : LinearIndependent ℝ (fun j => blockClass C (x j)))
    (hsum : (∑ j,(w j : ℝ) • blockClass C (x j))=v)
    {r : ℕ} (hr : Fintype.card J=r) : WeightedPureBlock C M v r := by
  classical
  let e : Fin r ≃ J := (finCongr hr.symm).trans (Fintype.equivFin J).symm
  exact {
    column := fun j => x (e j)
    realizable := fun j => hx (e j)
    weight := fun j => w (e j)
    positive := fun j => hw (e j)
    bounded := fun j => hM (e j)
    independent := hind.comp e e.injective
    weighted_sum := (e.sum_comp (fun j => (w j : ℝ) • blockClass C (x j))).trans hsum
  }

theorem reference_pair_expansion (C : Finset H) (e₀ : PairIn C)
    (x : PairIn C → ℝ) (hx : x e₀=0) :
    (∑ p : ↥((univ : Finset (PairIn C)).erase e₀),x p.1 • pairIndicator {p.1})=x := by
  classical
  funext e
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pairIndicator,mem_singleton,mul_ite,mul_one,mul_zero]
  by_cases he : e=e₀
  · subst e
    have hn : ∀ p : ↥((univ : Finset (PairIn C)).erase e₀),e₀≠p.1 :=
      fun p => Ne.symm (mem_erase.mp p.2).1
    simp only [hn,ite_false,sum_const_zero,hx]
  · let p₀ : ↥((univ : Finset (PairIn C)).erase e₀) := ⟨e,mem_erase.mpr ⟨he,mem_univ _⟩⟩
    have hp : ∀ p : ↥((univ : Finset (PairIn C)).erase e₀),e=p.1 ↔ p=p₀ := by
      intro p
      exact ⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩
    simp only [hp,sum_ite_eq',mem_univ,ite_true]
    rfl

/-- The complete signed pair basis excluding one reference coordinate,
realized by genuine positive or negative pure Boolean pair modules. -/
def signed_pair_basis (C : Finset H) (hC : 3≤C.card) (e₀ : PairIn C)
    (ε : ℝ) (hε : ε=1 ∨ ε= -1) (w : PairIn C → ℤ)
    (hw₀ : w e₀=0) (hw : ∀ e,e≠e₀ → 0<w e) (M : ℤ)
    (hM : ∀ e,e≠e₀ → w e≤M) :
    WeightedPureBlock C M (blockClass C (ε • (fun e => (w e : ℝ)))) (C.card.choose 2-1) := by
  classical
  let J := ↥((univ : Finset (PairIn C)).erase e₀)
  let x : J → PairIn C → ℝ := fun p => ε • pairIndicator {p.1}
  have hx : ∀ p,PureRealizable C (x p) := by
    intro p
    rcases hε with h | h
    · simpa only [x,h,one_smul] using pureRealizable_pair C p.1
    · simpa only [x,h,neg_one_smul] using pureRealizable_negative_pair C hC p.1
  have hε₀ : ε≠0 := by rcases hε with rfl | rfl <;> norm_num
  have hind : LinearIndependent ℝ (fun p : J => blockClass C (x p)) := by
    have hi := reference_pair_columns_independent C e₀
    rw [Fintype.linearIndependent_iff]
    intro t ht p
    have hz : (∑ q : J,(t q*ε) • blockClass C (pairIndicator {q.1}))=0 := by
      simpa only [x,map_smul,mul_smul] using ht
    exact (mul_eq_zero.mp ((Fintype.linearIndependent_iff.mp hi) _ hz p)).resolve_right hε₀
  have hsum : (∑ p : J,(w p.1 : ℝ) • blockClass C (x p))=
      blockClass C (ε • (fun e => (w e : ℝ))) := by
    have he : (∑ p : J,(w p.1 : ℝ) • x p)=ε • (fun e => (w e : ℝ)) := by
      calc
        _ = ε • (∑ p : J,(w p.1 : ℝ) • pairIndicator {p.1}) := by
          simp only [x,smul_sum]
          exact sum_congr rfl (fun p _ => smul_comm _ _ _)
        _ = _ := congrArg (fun y : PairIn C → ℝ => ε • y)
          (reference_pair_expansion C e₀ (fun e => (w e : ℝ)) (by simp [hw₀]))
    simpa only [map_sum,map_smul] using congrArg (blockClass C) he
  apply weightedPureBlock_of_data C M _ x hx (fun p : J => w p.1)
    (fun p => hw p.1 (mem_erase.mp p.2).1)
    (fun p => hM p.1 (mem_erase.mp p.2).1) hind hsum
  simp only [J,Fintype.card_coe,card_erase_of_mem (mem_univ _),card_univ,pairIn_card]

end BooleanModule
end GraphicalZonotopes
