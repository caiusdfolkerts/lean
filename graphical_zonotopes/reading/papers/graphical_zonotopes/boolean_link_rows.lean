module

public import Papers.GraphicalZonotopes.ConditionalQuadratic
public import Papers.GraphicalZonotopes.MobiusFour
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace GraphicalZonotopes.BooleanLinkRows

def IsBit (x : ℝ) : Prop := x = 0 ∨ x = 1

theorem bit_square {x : ℝ} (hx : IsBit x) : x ^ 2 = x := by
  rcases hx with rfl | rfl <;> norm_num

/-- A Boolean affine function cannot vary independently in two directions. -/
theorem affine_two_mul_eq_zero (c a b : ℝ)
    (h00 : IsBit c) (h10 : IsBit (c+a)) (h01 : IsBit (c+b))
    (h11 : IsBit (c+a+b)) : a*b=0 := by
  have h0 := bit_square h00
  have h1 := bit_square h10
  have h2 := bit_square h01
  have h3 := bit_square h11
  nlinarith

/-- The difference of two vectors supported on at most one coordinate
cannot have three nonzero coordinates. -/
theorem three_differences_zero (a b c a' b' c' : ℝ)
    (hab : a*b=0) (hac : a*c=0) (hbc : b*c=0)
    (hab' : a'*b'=0) (hac' : a'*c'=0) (hbc' : b'*c'=0) :
    a'-a=0 ∨ b'-b=0 ∨ c'-c=0 := by
  by_cases ha : a=0
  · by_cases ha' : a'=0
    · exact Or.inl (by simp [ha,ha'])
    · have hb' : b'=0 := (mul_eq_zero.mp hab').resolve_left ha'
      have hc' : c'=0 := (mul_eq_zero.mp hac').resolve_left ha'
      rcases mul_eq_zero.mp hbc with hb | hc
      · exact Or.inr (Or.inl (by simp [hb,hb']))
      · exact Or.inr (Or.inr (by simp [hc,hc']))
  · have hb : b=0 := (mul_eq_zero.mp hab).resolve_left ha
    have hc : c=0 := (mul_eq_zero.mp hac).resolve_left ha
    rcases mul_eq_zero.mp hbc' with hb' | hc'
    · exact Or.inr (Or.inl (by simp [hb,hb']))
    · exact Or.inr (Or.inr (by simp [hc,hc']))

def bit (s : Bool) : ℝ := if s then 1 else 0

def quadratic4 (k a b c d ab ac ad bc bd cd : ℝ) (s t u v : Bool) : ℝ :=
  k + a*bit s + b*bit t + c*bit u + d*bit v +
    ab*bit s*bit t + ac*bit s*bit u + ad*bit s*bit v +
    bc*bit t*bit u + bd*bit t*bit v + cd*bit u*bit v

/-- An induced four-vertex path cannot be the interaction graph of a
Boolean quadratic. The middle edge coefficient is arbitrary. -/
theorem path_end_product_zero (k a b c d ab bc cd : ℝ)
    (h : ∀ s t u v : Bool, IsBit (quadratic4 k a b c d ab 0 0 bc 0 cd s t u v)) :
    ab*cd=0 := by
  have hp (s t : Bool) : (a+ab*bit s)*(d+cd*bit t)=0 := by
    apply affine_two_mul_eq_zero (k+b*bit s+c*bit t+bc*bit s*bit t)
      (a+ab*bit s) (d+cd*bit t)
    · convert h false s t false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h true s t false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h false s t true using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h true s t true using 1 <;> simp [quadratic4,bit] <;> ring
  have h00 := hp false false
  have h10 := hp true false
  have h01 := hp false true
  have h11 := hp true true
  simp only [bit, Bool.false_eq_true, if_false, if_true, mul_zero, mul_one, add_zero] at *
  nlinarith

/-- A Boolean quadratic on a three-leaf star has a zero interaction edge. -/
theorem star_three_zero (k a b c d ab ac ad : ℝ)
    (h : ∀ s t u v : Bool, IsBit (quadratic4 k a b c d ab ac ad 0 0 0 s t u v)) :
    ab=0 ∨ ac=0 ∨ ad=0 := by
  have hbc (s : Bool) : (b+ab*bit s)*(c+ac*bit s)=0 := by
    apply affine_two_mul_eq_zero (k+a*bit s) (b+ab*bit s) (c+ac*bit s)
    · convert h s false false false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s true false false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s false true false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s true true false using 1 <;> simp [quadratic4,bit] <;> ring
  have hbd (s : Bool) : (b+ab*bit s)*(d+ad*bit s)=0 := by
    apply affine_two_mul_eq_zero (k+a*bit s) (b+ab*bit s) (d+ad*bit s)
    · convert h s false false false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s true false false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s false false true using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s true false true using 1 <;> simp [quadratic4,bit] <;> ring
  have hcd (s : Bool) : (c+ac*bit s)*(d+ad*bit s)=0 := by
    apply affine_two_mul_eq_zero (k+a*bit s) (c+ac*bit s) (d+ad*bit s)
    · convert h s false false false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s false true false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s false false true using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s false true true using 1 <;> simp [quadratic4,bit] <;> ring
  have hbc0 := hbc false
  have hbd0 := hbd false
  have hcd0 := hcd false
  have hbc1 := hbc true
  have hbd1 := hbd true
  have hcd1 := hcd true
  simp only [bit, Bool.false_eq_true, if_false, if_true, mul_zero, mul_one, add_zero] at *
  rcases three_differences_zero b c d (b+ab) (c+ac) (d+ad)
    hbc0 hbd0 hcd0 hbc1 hbd1 hcd1 with hz | hz | hz
  · left; linarith
  · right; left; linarith
  · right; right; linarith

open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def pick (s : Bool) (a : V) (S : Finset V) : Finset V := if s then insert a S else S

def select4 (a b c d : V) (s t u v : Bool) : Finset V :=
  pick s a (pick t b (pick u c (pick v d ∅)))

/-- Restricting a quadratic set function to any four distinct vertices is
exactly the displayed four-variable polynomial, with its actual coefficients. -/
theorem zeta_select4 (g : SetFunction V)
    (hdegree : ∀ C : Finset V, 2<C.card → g C=0)
    {a b c d : V} (hab : a≠b) (hac : a≠c) (had : a≠d)
    (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) (s t u v : Bool) :
    zeta g (select4 a b c d s t u v) =
      quadratic4 (g ∅) (g {a}) (g {b}) (g {c}) (g {d})
        (g {a,b}) (g {a,c}) (g {a,d}) (g {b,c}) (g {b,d}) (g {c,d}) s t u v := by
  have hABC : g {a,b,c}=0 := hdegree _ (by simp [hab,hac,hbc])
  have hABD : g {a,b,d}=0 := hdegree _ (by simp [hab,had,hbd])
  have hACD : g {a,c,d}=0 := hdegree _ (by simp [hac,had,hcd])
  have hBCD : g {b,c,d}=0 := hdegree _ (by simp [hbc,hbd,hcd])
  have hABCD : g {a,b,c,d}=0 := hdegree _ (by simp [hab,hac,had,hbc,hbd,hcd])
  cases s <;> cases t <;> cases u <;> cases v <;>
    simp [select4,pick,quadratic4,bit,zeta_insert,zeta_empty,zeta_singleton,
      hab,hac,had,hbc,hbd,hcd,hABC,hABD,hACD,hBCD,hABCD] <;> ring

theorem no_induced_path (g : SetFunction V)
    (hdegree : ∀ C : Finset V, 2<C.card → g C=0)
    (hbit : ∀ S, IsBit (zeta g S))
    {a b c d : V} (hab : a≠b) (hac : a≠c) (had : a≠d)
    (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (hac0 : g {a,c}=0) (had0 : g {a,d}=0) (hbd0 : g {b,d}=0) :
    g {a,b} * g {c,d}=0 := by
  apply path_end_product_zero (g ∅) (g {a}) (g {b}) (g {c}) (g {d})
    (g {a,b}) (g {b,c}) (g {c,d})
  intro s t u v
  have hb := hbit (select4 a b c d s t u v)
  rw [zeta_select4 g hdegree hab hac had hbc hbd hcd, hac0,had0,hbd0] at hb
  exact hb

theorem no_three_leaf_star (g : SetFunction V)
    (hdegree : ∀ C : Finset V, 2<C.card → g C=0)
    (hbit : ∀ S, IsBit (zeta g S))
    {a b c d : V} (hab : a≠b) (hac : a≠c) (had : a≠d)
    (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (hbc0 : g {b,c}=0) (hbd0 : g {b,d}=0) (hcd0 : g {c,d}=0) :
    g {a,b}=0 ∨ g {a,c}=0 ∨ g {a,d}=0 := by
  apply star_three_zero (g ∅) (g {a}) (g {b}) (g {c}) (g {d})
    (g {a,b}) (g {a,c}) (g {a,d})
  intro s t u v
  have hb := hbit (select4 a b c d s t u v)
  rw [zeta_select4 g hdegree hab hac had hbc hbd hcd, hbc0,hbd0,hcd0] at hb
  exact hb

end GraphicalZonotopes.BooleanLinkRows
