module

public import Papers.GraphicalZonotopes.ForestSigns
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ForestSigns
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeProduct (x : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => x u*x v,fun _ _ => mul_comm _ _⟩

@[simp] theorem edgeProduct_pair (x : V → ℝ) (u v : V) :
    edgeProduct x s(u,v)=x u*x v := rfl

def spinToBit (σ : V → ℝ) (v : V) : ℝ := (1+σ v)/2

theorem spinToBit_boolean {σ : V → ℝ} (hσ : ∀ v,IsSign (σ v)) :
    ∀ v,spinToBit σ v=0 ∨ spinToBit σ v=1 := by
  intro v
  rcases hσ v with h | h <;> simp [spinToBit,h]

theorem neg_signs {σ : V → ℝ} (hσ : ∀ v,IsSign (σ v)) :
    ∀ v,IsSign ((-σ) v) := by
  intro v
  rcases hσ v with h | h <;> simp [IsSign,h]

theorem edgeProduct_spin_complement (σ : V → ℝ) (e : Sym2 V) :
    edgeProduct (spinToBit σ) e+edgeProduct (spinToBit (-σ)) e=
      (1+edgeProduct σ e)/2 := by
  obtain ⟨u,v⟩ := e
  simp only [edgeProduct_pair,spinToBit,Pi.neg_apply]
  ring

def quadratic (G : SimpleGraph V) (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ)
    (x : V → ℝ) : ℝ :=
  c+(∑ v,l v*x v)+∑ e ∈ G.edgeFinset,w e*edgeProduct x e

theorem quadratic_spin_complement (G : SimpleGraph V) (c : ℝ)
    (l : V → ℝ) (w : Sym2 V → ℝ) (σ : V → ℝ) :
    quadratic G c l w (spinToBit σ)+quadratic G c l w (spinToBit (-σ))=
      2*c+(∑ v,l v)+(1/2 : ℝ)*(∑ e ∈ G.edgeFinset,w e)+
      (1/2 : ℝ)*(∑ e ∈ G.edgeFinset,w e*edgeProduct σ e) := by
  have hlin : (∑ v,l v*spinToBit σ v)+(∑ v,l v*spinToBit (-σ) v)=∑ v,l v := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    simp only [spinToBit,Pi.neg_apply]
    ring
  have hquad : (∑ e ∈ G.edgeFinset,w e*edgeProduct (spinToBit σ) e)+
      (∑ e ∈ G.edgeFinset,w e*edgeProduct (spinToBit (-σ)) e)=
      (1/2 : ℝ)*(∑ e ∈ G.edgeFinset,w e)+
      (1/2 : ℝ)*(∑ e ∈ G.edgeFinset,w e*edgeProduct σ e) := by
    rw [← sum_add_distrib,mul_sum,mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro e he
    rw [← mul_add,edgeProduct_spin_complement]
    ring
  unfold quadratic
  linarith

def coefficientSign (w : Sym2 V → ℝ) (u v : V) : ℝ :=
  if 0 ≤ w s(u,v) then 1 else -1

theorem coefficientSign_isSign (w : Sym2 V → ℝ) (u v : V) :
    IsSign (coefficientSign w u v) := by
  unfold coefficientSign
  split <;> simp [IsSign]

theorem coefficientSign_symm (w : Sym2 V → ℝ) (u v : V) :
    coefficientSign w u v=coefficientSign w v u := by
  simp only [coefficientSign,Sym2.eq_swap]

theorem weight_mul_coefficientSign (w : Sym2 V → ℝ) (u v : V) :
    w s(u,v)*coefficientSign w u v=|w s(u,v)| := by
  by_cases h : 0 ≤ w s(u,v)
  · simp [coefficientSign,h,abs_of_nonneg h]
  · simp [coefficientSign,h,abs_of_neg (lt_of_not_ge h)]

theorem exists_energy_extrema (G : SimpleGraph V) (hG : G.IsAcyclic)
    (w : Sym2 V → ℝ) :
    ∃ σ τ : V → ℝ,(∀ v,IsSign (σ v)) ∧ (∀ v,IsSign (τ v)) ∧
      (∑ e ∈ G.edgeFinset,w e*edgeProduct σ e)=∑ e ∈ G.edgeFinset,|w e| ∧
      (∑ e ∈ G.edgeFinset,w e*edgeProduct τ e)=-(∑ e ∈ G.edgeFinset,|w e|) := by
  obtain ⟨σ,hσ,hσe⟩ := exists_vertex_signs G hG (coefficientSign w)
    (fun u v _ => coefficientSign_isSign w u v)
    (fun u v _ => coefficientSign_symm w u v)
  obtain ⟨τ,hτ,hτe⟩ := exists_vertex_signs G hG (fun u v => -coefficientSign w u v)
    (fun u v _ => by
      rcases coefficientSign_isSign w u v with h | h <;> simp [IsSign,h])
    (fun u v _ => by rw [coefficientSign_symm w u v])
  refine ⟨σ,τ,hσ,hτ,?_,?_⟩
  · apply sum_congr rfl
    intro e he
    obtain ⟨u,v⟩ := e
    rw [edgeProduct_pair,hσe u v (G.mem_edgeFinset.mp he),weight_mul_coefficientSign]
  · rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro e he
    obtain ⟨u,v⟩ := e
    rw [edgeProduct_pair,hτe u v (G.mem_edgeFinset.mp he),mul_neg,
      weight_mul_coefficientSign]

/-- Lemma9.3 in its full real-coefficient form: a quadratic Boolean
polynomial whose interaction graph is a forest has oscillation at least half
the total absolute interaction weight. Arbitrary linear and constant terms
are retained. -/
theorem quadratic_oscillation_lower (G : SimpleGraph V) (hG : G.IsAcyclic)
    (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) (lo hi : ℝ)
    (hbound : ∀ x : V → ℝ,(∀ v,x v=0 ∨ x v=1) →
      lo ≤ quadratic G c l w x ∧ quadratic G c l w x ≤ hi) :
    (1/2 : ℝ)*(∑ e ∈ G.edgeFinset,|w e|) ≤ hi-lo := by
  obtain ⟨σ,τ,hσ,hτ,hmax,hmin⟩ := exists_energy_extrema G hG w
  have hσplus := hbound (spinToBit σ) (spinToBit_boolean hσ)
  have hσminus := hbound (spinToBit (-σ)) (spinToBit_boolean (neg_signs hσ))
  have hτplus := hbound (spinToBit τ) (spinToBit_boolean hτ)
  have hτminus := hbound (spinToBit (-τ)) (spinToBit_boolean (neg_signs hτ))
  have hfirst := quadratic_spin_complement G c l w σ
  have hsecond := quadratic_spin_complement G c l w τ
  rw [hmax] at hfirst
  rw [hmin] at hsecond
  linarith

end ForestSigns
end GraphicalZonotopes
