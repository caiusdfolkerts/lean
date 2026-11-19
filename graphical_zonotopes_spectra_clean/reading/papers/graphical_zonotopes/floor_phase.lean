module

public import Papers.GraphicalZonotopes.FloorHalf
public import Papers.GraphicalZonotopes.QuadraticSignAlgebra

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalZonotopes
namespace FloorHalf

/-- Exact remainder characterization, including negative integers. -/
theorem even_iff_mod_two (m : ℤ) : Even m ↔ m%2=0 := by
  constructor
  · rintro ⟨k,hk⟩
    omega
  · intro hm
    exact ⟨m/2,by omega⟩

theorem sign_zpow_mod_two (m : ℤ) :
    (-1 : ℝ)^m=if m%2=0 then 1 else -1 := by
  simp only [neg_one_zpow_eq_ite,even_iff_mod_two]

/-- Floor division as its linear part plus the exact parity correction. -/
theorem floor_half_phase (m : ℤ) :
    ((m/2 : ℤ) : ℝ)=(m : ℝ)/2+((-1 : ℝ)^m-1)/4 := by
  rw [sign_zpow_mod_two]
  by_cases hm : m%2=0
  · rw [if_pos hm]
    have he : m=2*(m/2) := by omega
    have hc : (m : ℝ)=2*((m/2 : ℤ) : ℝ) := by exact_mod_cast he
    linarith
  · rw [if_neg hm]
    have he : m=2*(m/2)+1 := by omega
    have hc : (m : ℝ)=2*((m/2 : ℤ) : ℝ)+1 := by exact_mod_cast he
    linarith

def edgePhaseInteger (m t a b : ℤ) : ℤ :=
  if a=b then
    if a=1 then (if (m+t)%2=0 then 1 else -1)
    else -(if (m+t)%2=0 then 1 else -1)
  else if m%2=0 then 1 else -1

theorem rounded_edge_phase_integer (m t a b : ℤ)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) :
    2*((m+2*t+a+b+1)/2+m/2-(m+t+a)/2-(m+t+b)/2)=
      1+edgePhaseInteger m t a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp only [edgePhaseInteger] <;> split_ifs <;> omega

/-- The exact original row profile, with all four endpoint-side choices.
Only the two endpoint bits are split; `m` and the context size are arbitrary. -/
theorem rounded_edge_phase (m t a b : ℤ)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) :
    (((m+2*t+a+b+1)/2 : ℤ) : ℝ)+((m/2 : ℤ) : ℝ)-
        (((m+t+a)/2 : ℤ) : ℝ)-(((m+t+b)/2 : ℤ) : ℝ)=
      (1+(if a=b then if a=1 then (-1 : ℝ)^(m+t) else -(-1 : ℝ)^(m+t)
        else (-1 : ℝ)^m))/2 := by
  have h := rounded_edge_phase_integer m t a b ha hb
  have hc : 2*((((m+2*t+a+b+1)/2 : ℤ) : ℝ)+((m/2 : ℤ) : ℝ)-
      (((m+t+a)/2 : ℤ) : ℝ)-(((m+t+b)/2 : ℤ) : ℝ))=
      1+(edgePhaseInteger m t a b : ℝ) := by exact_mod_cast h
  have hp : (edgePhaseInteger m t a b : ℝ)=
      if a=b then if a=1 then (-1 : ℝ)^(m+t) else -(-1 : ℝ)^(m+t)
      else (-1 : ℝ)^m := by
    rw [sign_zpow_mod_two,sign_zpow_mod_two]
    unfold edgePhaseInteger
    split_ifs <;> norm_num
  rw [hp] at hc
  linarith

end FloorHalf
end GraphicalZonotopes
