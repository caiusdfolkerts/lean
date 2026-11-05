module

public import Papers.GraphicalZonotopes.ForestSigns
public import Papers.GraphicalZonotopes.RootedResponseAlgebra
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace ForestZeros
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A zero of the sum of the nonnegative factors `xy` and
`(1-x)(1-y)`: every edge has an endpoint equal to its specified bit. -/
def CoversLabels (G : SimpleGraph V) (b : Sym2 V → Bool) (x : V → Bool) : Prop :=
  ∀ u v,G.Adj u v → x u=b s(u,v) ∨ x v=b s(u,v)

def bitSign (b : Bool) : ℝ := if b then 1 else -1

def signBit (s : ℝ) : Bool := decide (s=1)

theorem bitSign_isSign (b : Bool) : ForestSigns.IsSign (bitSign b) := by
  cases b <;> simp [bitSign,ForestSigns.IsSign]

@[simp] theorem signBit_bitSign (b : Bool) : signBit (bitSign b)=b := by
  cases b <;> norm_num [signBit,bitSign]

theorem signBit_covers_of_neg_product {s t : ℝ}
    (hs : ForestSigns.IsSign s) (ht : ForestSigns.IsSign t)
    (hst : s*t=-1) (b : Bool) : signBit s=b ∨ signBit t=b := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    cases b
  all_goals try (norm_num [signBit] at hst)
  all_goals norm_num [signBit]

/-- Opposite signs on every forest edge give a zero independently of the
choice of edge labels. Empty and disconnected forests are included. -/
theorem exists_cover (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) : ∃ x,CoversLabels G b x := by
  obtain ⟨σ,hσ,hσe⟩ := ForestSigns.exists_vertex_signs G hG (fun _ _ => -1)
    (by intro u v huv; exact Or.inr rfl) (by intro u v huv; rfl)
  refine ⟨fun v => signBit (σ v),?_⟩
  intro u v huv
  exact signBit_covers_of_neg_product (hσ u) (hσ v) (hσe u v huv) _

/-- For every vertex of a forest, the common zero locus contains two
points differing at that vertex alone. In particular the zero locus spans
the full affine Boolean coordinate space; this does not follow merely from
the existence of a single zero. -/
theorem exists_flippable_cover (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) (r : V) :
    ∃ x : V → Bool,∀ a : Bool,CoversLabels G b (Function.update x r a) := by
  let ρ : V → V → ℝ := fun u v =>
    if u=r ∨ v=r then bitSign (b s(u,v)) else -1
  have hρ : ∀ u v,G.Adj u v → ForestSigns.IsSign (ρ u v) := by
    intro u v huv
    dsimp [ρ]
    split
    · exact bitSign_isSign _
    · exact Or.inr rfl
  have hρsym : ∀ u v,G.Adj u v → ρ u v=ρ v u := by
    intro u v huv
    simp only [ρ,or_comm,Sym2.eq_swap]
  obtain ⟨σ,hσ,hσe⟩ := ForestSigns.exists_vertex_signs G hG ρ hρ hρsym
  let τ : V → ℝ := fun v => σ r*σ v
  have hτ : ∀ v,ForestSigns.IsSign (τ v) := fun v => (hσ r).mul (hσ v)
  have hneighbor : ∀ v,G.Adj r v → signBit (τ v)=b s(r,v) := by
    intro v hrv
    have he := hσe r v hrv
    have he' : τ v=bitSign (b s(r,v)) := by
      dsimp only [ρ] at he
      rw [if_pos (Or.inl rfl)] at he
      simpa only [τ] using he
    rw [he',signBit_bitSign]
  have hoff : ∀ u v,G.Adj u v → u≠r → v≠r →
      signBit (τ u)=b s(u,v) ∨ signBit (τ v)=b s(u,v) := by
    intro u v huv hur hvr
    have hprod : τ u*τ v=-1 := by
      calc
        τ u*τ v=(σ r)^2*(σ u*σ v) := by dsimp [τ]; ring
        _=-1 := by rw [(hσ r).sq,hσe u v huv]; simp [ρ,hur,hvr]
    exact signBit_covers_of_neg_product (hτ u) (hτ v) hprod _
  refine ⟨fun v => signBit (τ v),?_⟩
  intro a u v huv
  by_cases hur : u=r
  · subst u
    have hvr : v≠r := huv.ne.symm
    exact Or.inr (by simpa only [Function.update_of_ne hvr] using hneighbor v huv)
  · by_cases hvr : v=r
    · subst v
      exact Or.inl (by
        simpa only [Function.update_of_ne hur,Sym2.eq_swap] using hneighbor u huv.symm)
    · simpa only [Function.update_of_ne hur,Function.update_of_ne hvr] using
        hoff u v huv hur hvr

def affineValue (c : ℝ) (l : V → ℝ) (x : V → Bool) : ℝ :=
  c+∑ v,l v*RootedResponse.realBit (x v)

theorem affineValue_update_difference (c : ℝ) (l : V → ℝ)
    (x : V → Bool) (r : V) :
    affineValue c l (Function.update x r true)-
      affineValue c l (Function.update x r false)=l r := by
  calc
    affineValue c l (Function.update x r true)-
        affineValue c l (Function.update x r false)=
        ∑ v,(l v*RootedResponse.realBit ((Function.update x r true) v)-
          l v*RootedResponse.realBit ((Function.update x r false) v)) := by
      rw [sum_sub_distrib]
      unfold affineValue
      ring
    _=l r := by
      rw [sum_eq_single r]
      · simp [RootedResponse.realBit]
      · intro v hv hvr
        simp only [Function.update_of_ne hvr,sub_self]
      · intro hr
        exact False.elim (hr (mem_univ r))

/-- No nonzero affine functional vanishes on the entire zero locus of a
sum of labelled-edge factors on a finite forest. Together with subtraction
of the known quadratic coefficients, this identifies the full quadratic
tight kernel, rather than only a selected set of zero rows. -/
theorem affine_vanishing_iff (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) (c : ℝ) (l : V → ℝ) :
    (∀ x,CoversLabels G b x → affineValue c l x=0) ↔
      c=0 ∧ ∀ v,l v=0 := by
  constructor
  · intro hzero
    have hl : ∀ r,l r=0 := by
      intro r
      obtain ⟨x,hx⟩ := exists_flippable_cover G hG b r
      have hfalse := hzero _ (hx false)
      have htrue := hzero _ (hx true)
      have hd := affineValue_update_difference c l x r
      rw [hfalse,htrue] at hd
      linarith
    obtain ⟨x,hx⟩ := exists_cover G hG b
    have hc := hzero x hx
    simp only [affineValue,hl,zero_mul,sum_const_zero,add_zero] at hc
    exact ⟨hc,hl⟩
  · rintro ⟨rfl,hl⟩ x hx
    simp only [affineValue,hl,zero_mul,sum_const_zero,add_zero]

end ForestZeros
end GraphicalZonotopes
