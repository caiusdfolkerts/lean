module

public import Papers.GraphicalZonotopes.CompleteBooleanPhase

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem faceFunction_injective : Function.Injective (faceFunction (I := I)) := by
  intro G H he
  funext v
  have hv : (1+G v)/2=(1+H v)/2 := by
    simpa [faceFunction,phase,character,spin] using
      congrFun he ((fun _ => false),v)
  linarith

/-- Two distinct Boolean functions cannot span the same nonzero real ray
or line. This elementary fact is applied to literal elemental-row slices. -/
theorem eq_zero_of_two_boolean_lines {X : Type*} {f g p : X → ℝ}
    (hf : ∀ x,f x=0 ∨ f x=1) (hg : ∀ x,g x=0 ∨ g x=1)
    (hfg : f≠g) (hp : ∃ c : ℝ,p=c • f) (hq : ∃ d : ℝ,p=d • g) : p=0 := by
  obtain ⟨c,hc⟩ := hp
  obtain ⟨d,hd⟩ := hq
  by_cases hp0 : p=0
  · exact hp0
  have hc0 : c≠0 := by
    intro h
    apply hp0
    simpa [h] using hc
  have hf0 : f≠0 := by
    intro h
    apply hp0
    simpa [h] using hc
  obtain ⟨x,hx⟩ : ∃ x,f x=1 := by
    by_contra! hn
    apply hf0
    funext x
    exact (hf x).resolve_right (hn x)
  have he : c • f=d • g := hc.symm.trans hd
  have hx' := congrFun he x
  simp only [Pi.smul_apply,smul_eq_mul,hx,mul_one] at hx'
  have hcd : c=d := by
    rcases hg x with hgx | hgx
    · rw [hgx,mul_zero] at hx'
      exact False.elim (hc0 hx')
    · simpa only [hgx,mul_one] using hx'
  apply False.elim
  apply hfg
  funext y
  have hy := congrFun he y
  simp only [Pi.smul_apply,smul_eq_mul,← hcd] at hy
  exact mul_left_cancel₀ hc0 hy

/-- The two-slice elimination used in Corollaries9.10 and9.11: the same
tensor polynomial satisfying both complete zero sets must vanish. -/
theorem boolean_slice_intersection [Nonempty I] {G H : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v= -1) (hH : ∀ v,H v=1 ∨ H v= -1)
    (hsepG : Nonseparable G) (hsepH : Nonseparable H) (hGH : G≠H)
    (p : (Cube I × Cube I) → ℝ) (hp : p∈tensorSpace)
    (hzeroG : ∀ uv,faceFunction G uv=0 → p uv=0)
    (hzeroH : ∀ uv,faceFunction H uv=0 → p uv=0) : p=0 := by
  exact eq_zero_of_two_boolean_lines (faceFunction_boolean hG) (faceFunction_boolean hH)
    (fun h => hGH (faceFunction_injective h))
    ((boolean_face_line hG hsepG p hp).mp hzeroG)
    ((boolean_face_line hH hsepH p hp).mp hzeroH)

/-- Multiplication by the parity character is nonconstant in every positive
number of variables, even when accompanied by an arbitrary constant sign. -/
theorem ne_parity_multiple [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v≠0) (c : ℝ) : G≠fun v => c*character univ v*G v := by
  intro he
  have h0 := congrFun he (vertexOfSet ∅)
  rw [character_vertex_empty,mul_one] at h0
  have hc : c=1 := by
    apply (mul_right_cancel₀ (hG (vertexOfSet ∅)))
    simpa only [one_mul] using h0.symm
  obtain ⟨i⟩ := ‹Nonempty I›
  have h1 := congrFun he (vertexOfSet {i})
  rw [hc,one_mul,character_vertex_singleton,if_pos (mem_univ i)] at h1
  have hz : G (vertexOfSet {i})=0 := by linarith
  exact hG _ hz

end BooleanFourier
end GraphicalZonotopes
