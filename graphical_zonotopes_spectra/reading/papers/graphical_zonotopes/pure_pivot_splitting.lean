module

public import Papers.GraphicalZonotopes.PureEdgePartitions

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

section Pivot
variable {E I : Type*} [DecidableEq E] [Fintype I] [DecidableEq I]

def pivotPositive (seed : I → E) (D : Finset E) (owner : D → I) (i : I) : E → ℝ :=
  fun e => (if e=seed i then 1 else 0) +
    if h : e∈D then if owner ⟨e,h⟩=i then 1 else 0 else 0

def pivotColumns (seed : I → E) (D : Finset E) (owner : D → I) : I ⊕ D → E → ℝ
  | Sum.inl i => pivotPositive seed D owner i
  | Sum.inr d => fun e => if e=d.1 then -1 else 0

theorem pivotPositive_at_seed (seed : I → E) (hseed : Function.Injective seed)
    (D : Finset E) (owner : D → I) (hD : ∀ i,seed i∉D) (i j : I) :
    pivotPositive seed D owner i (seed j)=if j=i then 1 else 0 := by
  simp only [pivotPositive,dite_eq_right (hD j),add_zero,hseed.eq_iff]

theorem pivotPositive_at_extra (seed : I → E) (D : Finset E) (owner : D → I)
    (hD : ∀ i,seed i∉D) (i : I) (d : D) :
    pivotPositive seed D owner i d.1=if owner d=i then 1 else 0 := by
  have hne : d.1≠seed i := fun h => hD i (h ▸ d.2)
  simp only [pivotPositive,ite_eq_right hne,dite_eq_left d.2,zero_add]

theorem pivotColumns_linearIndependent (seed : I → E) (hseed : Function.Injective seed)
    (D : Finset E) (owner : D → I) (hD : ∀ i,seed i∉D) :
    LinearIndependent ℝ (pivotColumns seed D owner) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hbase : ∀ i,c (Sum.inl i)=0 := by
    intro i
    have hv := congrFun hc (seed i)
    rw [Fintype.sum_sum_type] at hv
    simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      pivotColumns,pivotPositive_at_seed seed hseed D owner hD,Pi.zero_apply] at hv
    have hn : ∀ d : D,seed i≠d.1 := fun d h => hD i (h.symm ▸ d.2)
    simp only [hn,ite_false,mul_zero,sum_const_zero,add_zero] at hv
    simpa using hv
  cases j with
  | inl i => exact hbase i
  | inr d =>
    have hv := congrFun hc d.1
    rw [Fintype.sum_sum_type] at hv
    simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      hbase,zero_mul,sum_const_zero,zero_add,pivotColumns,Pi.zero_apply] at hv
    have he : ∀ e : D,d.1=e.1 ↔ e=d := fun e =>
      ⟨fun h => Subtype.ext h.symm,fun h => congrArg Subtype.val h.symm⟩
    simp_rw [he] at hv
    simpa using hv

theorem pivotColumns_sum (seed : I → E) (D : Finset E) (owner : D → I) :
    (∑ j : I ⊕ D,pivotColumns seed D owner j)=
      fun e => ∑ i : I,if e=seed i then (1 : ℝ) else 0 := by
  classical
  funext e
  rw [Fintype.sum_sum_type]
  simp only [Pi.add_apply,Finset.sum_apply,pivotColumns,pivotPositive]
  rw [sum_add_distrib]
  by_cases h : e∈D
  · simp only [dite_eq_left h]
    have he : ∀ d : D,e=d.1 ↔ d=⟨e,h⟩ := fun d =>
      ⟨fun he => Subtype.ext he.symm,fun he => congrArg Subtype.val he.symm⟩
    simp_rw [he]
    simp
  · have he : ∀ d : D,e≠d.1 := fun d he => h (he.symm ▸ d.2)
    simp only [dite_eq_right h,he,ite_false,sum_const_zero,add_zero]

theorem pivotColumns_zero_at (seed : I → E) (D : Finset E) (owner : D → I)
    (e : E) (heD : e∉D) (hseed : ∀ i,e≠seed i) (j : I ⊕ D) :
    pivotColumns seed D owner j e=0 := by
  cases j with
  | inl i => simp [pivotColumns,pivotPositive,hseed i,heD]
  | inr d =>
    have he : e≠d.1 := fun h => heD (h.symm ▸ d.2)
    simp [pivotColumns,he]

end Pivot
end BooleanModule
end GraphicalZonotopes
