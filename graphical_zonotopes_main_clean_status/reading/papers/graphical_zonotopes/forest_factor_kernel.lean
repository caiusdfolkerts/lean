module

public import Papers.GraphicalZonotopes.ForestZeroKernel
public import Papers.GraphicalZonotopes.ForestOscillation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ForestZeros
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each edge has quadratic coefficient one. Its lower coefficients are
fixed by its bit: `xy` for zero, `(1-x)(1-y)` for one. -/
def edgeFactor (b : Sym2 V → Bool) (x : V → Bool) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v =>
    if b s(u,v) then
      (1-RootedResponse.realBit (x u))*(1-RootedResponse.realBit (x v))
    else RootedResponse.realBit (x u)*RootedResponse.realBit (x v),by
      intro u v
      simp only [Sym2.eq_swap,mul_comm]⟩

@[simp] theorem edgeFactor_pair (b : Sym2 V → Bool) (x : V → Bool) (u v : V) :
    edgeFactor b x s(u,v)=
      if b s(u,v) then
        (1-RootedResponse.realBit (x u))*(1-RootedResponse.realBit (x v))
      else RootedResponse.realBit (x u)*RootedResponse.realBit (x v) := rfl

theorem edgeFactor_zero_or_one (b : Sym2 V → Bool) (x : V → Bool) (e : Sym2 V) :
    edgeFactor b x e=0 ∨ edgeFactor b x e=1 := by
  obtain ⟨u,v⟩ := e
  rw [edgeFactor_pair]
  cases b s(u,v) <;> cases x u <;> cases x v <;>
    norm_num [RootedResponse.realBit]

theorem edgeFactor_nonneg (b : Sym2 V → Bool) (x : V → Bool) (e : Sym2 V) :
    0≤edgeFactor b x e := by
  rcases edgeFactor_zero_or_one b x e with h | h <;> simp [h]

theorem edgeFactor_le_one (b : Sym2 V → Bool) (x : V → Bool) (e : Sym2 V) :
    edgeFactor b x e≤1 := by
  rcases edgeFactor_zero_or_one b x e with h | h <;> simp [h]

theorem edgeFactor_pair_eq_zero (b : Sym2 V → Bool) (x : V → Bool) (u v : V) :
    edgeFactor b x s(u,v)=0 ↔ x u=b s(u,v) ∨ x v=b s(u,v) := by
  rw [edgeFactor_pair]
  cases b s(u,v) <;> cases x u <;> cases x v <;>
    norm_num [RootedResponse.realBit]

def totalFactor (G : SimpleGraph V) (b : Sym2 V → Bool) (x : V → Bool) : ℝ :=
  ∑ e∈G.edgeFinset,edgeFactor b x e

theorem totalFactor_nonneg (G : SimpleGraph V) (b : Sym2 V → Bool) (x : V → Bool) :
    0≤totalFactor G b x := by
  exact sum_nonneg (fun e he => edgeFactor_nonneg b x e)

theorem totalFactor_le_card (G : SimpleGraph V) (b : Sym2 V → Bool) (x : V → Bool) :
    totalFactor G b x≤(G.edgeFinset.card : ℝ) := by
  calc
    totalFactor G b x≤∑ e∈G.edgeFinset,(1:ℝ) :=
      sum_le_sum (fun e he => edgeFactor_le_one b x e)
    _=(G.edgeFinset.card : ℝ) := by simp

theorem totalFactor_eq_zero_iff (G : SimpleGraph V) (b : Sym2 V → Bool)
    (x : V → Bool) : totalFactor G b x=0 ↔ CoversLabels G b x := by
  rw [totalFactor,sum_eq_zero_iff_of_nonneg (fun e he => edgeFactor_nonneg b x e)]
  constructor
  · intro h u v huv
    exact (edgeFactor_pair_eq_zero b x u v).mp (h _ (G.mem_edgeFinset.mpr huv))
  · intro h e he
    obtain ⟨u,v⟩ := e
    exact (edgeFactor_pair_eq_zero b x u v).mpr (h u v (G.mem_edgeFinset.mp he))

theorem totalFactor_has_zero (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) : ∃ x,totalFactor G b x=0 := by
  obtain ⟨x,hx⟩ := exists_cover G hG b
  exact ⟨x,(totalFactor_eq_zero_iff G b x).mpr hx⟩

/-- An actual nonempty interaction graph has a strictly positive slack.
There is no cancellation argument here: one selected factor is one and all
other factors are nonnegative. -/
theorem totalFactor_has_positive (G : SimpleGraph V) (hG : G≠⊥)
    (b : Sym2 V → Bool) : ∃ x,0<totalFactor G b x := by
  obtain ⟨e,he⟩ := G.edgeFinset_nonempty.mpr hG
  let x : V → Bool := fun _ => !(b e)
  have hone : edgeFactor b x e=1 := by
    obtain ⟨u,v⟩ := e
    rw [edgeFactor_pair]
    dsimp [x]
    cases b s(u,v) <;> norm_num [RootedResponse.realBit]
  have hle : edgeFactor b x e≤totalFactor G b x :=
    single_le_sum (fun f hf => edgeFactor_nonneg b x f) he
  refine ⟨x,?_⟩
  rw [hone] at hle
  linarith

/-- These are unrestricted real quadratic variations written in the
edge-factor basis plus their affine remainder. The coefficients on distinct
edges remain completely independent. -/
def factorCoordinates (G : SimpleGraph V) (b : Sym2 V → Bool)
    (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) (x : V → Bool) : ℝ :=
  affineValue c l x+∑ e∈G.edgeFinset,w e*edgeFactor b x e

theorem weightedFactors_zero (G : SimpleGraph V) (b : Sym2 V → Bool)
    (w : Sym2 V → ℝ) (x : V → Bool) (hx : CoversLabels G b x) :
    (∑ e∈G.edgeFinset,w e*edgeFactor b x e)=0 := by
  apply sum_eq_zero
  intro e he
  obtain ⟨u,v⟩ := e
  rw [(edgeFactor_pair_eq_zero b x u v).mpr (hx u v (G.mem_edgeFinset.mp he)),mul_zero]

/-- The entire tight kernel of the positive unit-weight forest polynomial:
the arbitrary quadratic edge coefficients survive, and every affine
remainder vanishes. The equivalence uses every zero row of the actual
polynomial and has no rank or private-kernel assumption. -/
theorem factor_tight_kernel (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) :
    (∀ x,totalFactor G b x=0 → factorCoordinates G b c l w x=0) ↔
      c=0 ∧ ∀ v,l v=0 := by
  rw [← affine_vanishing_iff G hG b c l]
  constructor
  · intro h x hx
    have hz := h x ((totalFactor_eq_zero_iff G b x).mpr hx)
    simpa only [factorCoordinates,weightedFactors_zero G b w x hx,add_zero] using hz
  · intro h x hx
    have hx' := (totalFactor_eq_zero_iff G b x).mp hx
    simp only [factorCoordinates,h x hx',weightedFactors_zero G b w x hx',add_zero]

def endpointSum (x : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => x u+x v,fun _ _ => add_comm _ _⟩

@[simp] theorem endpointSum_pair (x : V → ℝ) (u v : V) :
    endpointSum x s(u,v)=x u+x v := rfl

def constantWeight (G : SimpleGraph V) (b : Sym2 V → Bool) (w : Sym2 V → ℝ) : ℝ :=
  ∑ e∈G.edgeFinset,if b e then w e else 0

def incidentWeight (G : SimpleGraph V) (b : Sym2 V → Bool)
    (w : Sym2 V → ℝ) (v : V) : ℝ :=
  ∑ e∈G.edgeFinset,if b e ∧ v∈e.toFinset then w e else 0

theorem incidentWeight_sum (G : SimpleGraph V) (b : Sym2 V → Bool)
    (w : Sym2 V → ℝ) (x : V → ℝ) :
    (∑ v,incidentWeight G b w v*x v)=
      ∑ e∈G.edgeFinset,if b e then w e*endpointSum x e else 0 := by
  simp_rw [incidentWeight,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  obtain ⟨u,v⟩ := e
  have huv : u≠v := (G.mem_edgeFinset.mp he).ne
  cases hb : b s(u,v)
  · simp [hb]
  · simp only [hb,Bool.coe_true,true_and,ite_true,ite_mul,zero_mul]
    rw [sum_ite_mem_eq]
    simp [Sym2.toFinset_mk_eq, huv, endpointSum_pair, mul_add]

theorem weightedFactors_expansion (G : SimpleGraph V) (b : Sym2 V → Bool)
    (w : Sym2 V → ℝ) (x : V → Bool) :
    (∑ e∈G.edgeFinset,w e*edgeFactor b x e)=
      (∑ e∈G.edgeFinset,w e*ForestSigns.edgeProduct
        (fun v => RootedResponse.realBit (x v)) e)+constantWeight G b w-
        ∑ v,incidentWeight G b w v*RootedResponse.realBit (x v) := by
  rw [incidentWeight_sum]
  unfold constantWeight
  rw [← sum_add_distrib,← sum_sub_distrib]
  apply sum_congr rfl
  intro e he
  obtain ⟨u,v⟩ := e
  rw [edgeFactor_pair,ForestSigns.edgeProduct_pair,endpointSum_pair]
  cases b s(u,v) <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring

/-- Every ordinary quadratic polynomial on this graph has an exact
factor-coordinate representation. Thus the preceding kernel theorem loses
no constant, linear, or quadratic variations. -/
theorem quadratic_eq_factorCoordinates (G : SimpleGraph V) (b : Sym2 V → Bool)
    (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) (x : V → Bool) :
    ForestSigns.quadratic G c l w (fun v => RootedResponse.realBit (x v))=
      factorCoordinates G b (c-constantWeight G b w)
        (fun v => l v+incidentWeight G b w v) w x := by
  unfold factorCoordinates affineValue ForestSigns.quadratic
  rw [weightedFactors_expansion]
  simp_rw [add_mul]
  rw [sum_add_distrib]
  ring

/-- Full ordinary-coefficient form of the forest tight-kernel theorem.
All coefficients are arbitrary real numbers, and all Boolean zero rows of
the actual unit-weight polynomial are retained. -/
theorem ordinary_quadratic_tight_kernel (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) :
    (∀ x,totalFactor G b x=0 →
      ForestSigns.quadratic G c l w (fun v => RootedResponse.realBit (x v))=0) ↔
      c=constantWeight G b w ∧ ∀ v,l v= -incidentWeight G b w v := by
  simp_rw [quadratic_eq_factorCoordinates G b c l w]
  rw [factor_tight_kernel G hG b]
  constructor
  · rintro ⟨hc,hl⟩
    exact ⟨by linarith,fun v => by have hv := hl v; linarith⟩
  · rintro ⟨hc,hl⟩
    exact ⟨by linarith,fun v => by rw [hl v]; ring⟩

end ForestZeros
end GraphicalZonotopes
