module

public import Papers.GraphicalZonotopes.BooleanFace

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

def vertexOfSet (S : Finset I) : Cube I := fun i => decide (i∈S)
def trueSet (v : Cube I) : Finset I := univ.filter (fun i => v i=true)

@[simp] theorem trueSet_vertexOfSet (S : Finset I) : trueSet (vertexOfSet S)=S := by
  ext i
  simp [trueSet,vertexOfSet]

@[simp] theorem character_vertex_empty (A : Finset I) : character A (vertexOfSet ∅)=1 := by
  simp [character,vertexOfSet,spin]

theorem character_vertex_singleton (A : Finset I) (i : I) :
    character A (vertexOfSet {i})=if i∈A then -1 else 1 := by
  unfold character
  rw [prod_eq_single i]
  · simp [vertexOfSet,spin]
  · intro j hj hji
    simp [vertexOfSet,spin,hji]
  · simp

theorem character_vertex_pair (A : Finset I) {i j : I} (hij : i≠j) :
    character A (vertexOfSet {i,j})=
      character A (vertexOfSet {i})*character A (vertexOfSet {j}) := by
  simp only [character,← prod_mul_distrib]
  apply prod_congr rfl
  intro k hk
  by_cases hA : k∈A
  · by_cases hi : k=i
    · subst k
      simp [vertexOfSet,spin,hA,hij]
    · by_cases hj : k=j
      · subst k
        simp [vertexOfSet,spin,hA,Ne.symm hij]
      · simp [vertexOfSet,spin,hA,hi,hj]
  · simp [hA]

/-- A quadratic Boolean phase with every mixed pair present, arbitrary linear
part `L`, and an arbitrary nonzero constant multiplier. The exponent is the
number of pairs of true bits, so this is precisely the complete quadratic form. -/
def completePhase (c : ℝ) (L : Finset I) (v : Cube I) : ℝ :=
  c*(-1 : ℝ)^((trueSet v).card.choose 2)*character L v

@[simp] theorem completePhase_empty (c : ℝ) (L : Finset I) :
    completePhase c L (vertexOfSet ∅)=c := by
  simp [completePhase]

theorem completePhase_singleton (c : ℝ) (L : Finset I) (i : I) :
    completePhase c L (vertexOfSet {i})=c*character L (vertexOfSet {i}) := by
  simp [completePhase]

theorem completePhase_pair (c : ℝ) (L : Finset I) {i j : I} (hij : i≠j) :
    completePhase c L (vertexOfSet {i,j})=
      -c*character L (vertexOfSet {i})*character L (vertexOfSet {j}) := by
  rw [completePhase,trueSet_vertexOfSet,card_pair hij]
  norm_num
  rw [character_vertex_pair L hij]
  ring

theorem completePhase_ne_zero {c : ℝ} (hc : c≠0) (L : Finset I) (v : Cube I) :
    completePhase c L v≠0 := by
  exact mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ (by norm_num)))
    (character_ne_zero L v)

theorem completePhase_isSign {c : ℝ} (hc : c=1 ∨ c=-1) (L : Finset I) (v : Cube I) :
    completePhase c L v=1 ∨ completePhase c L v=-1 := by
  have hp : ∀ n : ℕ,(-1 : ℝ)^n=1 ∨ (-1 : ℝ)^n=-1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rcases ih with h | h <;> simp [pow_succ,h]
  have hchar : character L v=1 ∨ character L v=-1 := by
    have hsq := character_square L v
    have hprod : (character L v-1)*(character L v+1)=0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith
  rcases hc with hc | hc <;> rcases hp ((trueSet v).card.choose 2) with hp | hp <;>
    rcases hchar with hchar | hchar <;> simp [completePhase,hc,hp,hchar]

/-- The four-corner identity of a genuine separated function. Only the
defining coordinate dependence of the two factors is used. -/
theorem separated_four_corner {G H K : Cube I → ℝ} {A : Finset I}
    (hH : DependsOn A H) (hK : DependsOn Aᶜ K)
    (hfactor : ∀ v,G v=H v*K v) {i j : I} (hi : i∈A) (hj : j∉A) :
    G (vertexOfSet ∅)*G (vertexOfSet {i,j})=
      G (vertexOfSet {i})*G (vertexOfSet {j}) := by
  have hij : i≠j := by intro h; exact hj (h ▸ hi)
  have hH₀ : H (vertexOfSet {j})=H (vertexOfSet ∅) := by
    apply hH
    intro k hk
    have hkj : k≠j := by intro h; exact hj (h ▸ hk)
    simp [vertexOfSet,hkj]
  have hH₁ : H (vertexOfSet {i,j})=H (vertexOfSet {i}) := by
    apply hH
    intro k hk
    have hkj : k≠j := by intro h; exact hj (h ▸ hk)
    simp [vertexOfSet,hkj]
  have hK₀ : K (vertexOfSet {i})=K (vertexOfSet ∅) := by
    apply hK
    intro k hk
    have hki : k≠i := by
      intro h
      have hn : k∉A := mem_compl.mp hk
      exact hn (h.symm ▸ hi)
    simp [vertexOfSet,hki]
  have hK₁ : K (vertexOfSet {i,j})=K (vertexOfSet {j}) := by
    apply hK
    intro k hk
    have hki : k≠i := by
      intro h
      have hn : k∉A := mem_compl.mp hk
      exact hn (h.symm ▸ hi)
    simp [vertexOfSet,hki]
  rw [hfactor,hfactor,hfactor,hfactor,hH₀,hH₁,hK₀,hK₁]
  ring

/-- Every complete quadratic phase is nonseparable across every nonempty
proper partition, in every finite number of variables. This is the exact
nonfactorization property used by Theorem9.8 after the Walsh calculation. -/
theorem completePhase_nonseparable {c : ℝ} (hc : c≠0) (L : Finset I) :
    Nonseparable (completePhase c L) := by
  intro A hA htop hfactor
  obtain ⟨i,hi⟩ := hA
  obtain ⟨j,hj⟩ : ∃ j : I,j∉A := by
    by_contra! hall
    apply htop
    ext j
    simp [hall j]
  obtain ⟨H,K,hH,hK,hsep⟩ := hfactor
  have hij : i≠j := by intro h; exact hj (h ▸ hi)
  have hs := separated_four_corner hH hK hsep hi hj
  have hm : completePhase c L (vertexOfSet ∅)*completePhase c L (vertexOfSet {i,j})=
      -(completePhase c L (vertexOfSet {i})*completePhase c L (vertexOfSet {j})) := by
    rw [completePhase_empty,completePhase_pair c L hij,
      completePhase_singleton,completePhase_singleton]
    ring
  have hzero : completePhase c L (vertexOfSet {i})*completePhase c L (vertexOfSet {j})=0 := by
    linarith [hs,hm]
  exact (mul_ne_zero (completePhase_ne_zero hc L _) (completePhase_ne_zero hc L _)) hzero

end BooleanFourier
end GraphicalZonotopes
