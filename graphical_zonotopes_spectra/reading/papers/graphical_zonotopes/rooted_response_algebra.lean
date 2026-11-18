module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalZonotopes
namespace RootedResponse

/-! The local construction in Lemma 6.2. These finite identities concern
the first tetrahedron of an arbitrary branch. The subsequent branch induction
must establish their application to the actual private-kernel equations. -/

abbrev Row := Fin 3 → Bool

abbrev Nonconstant (v : Row) : Prop :=
  (∃ i,v i=false) ∧ (∃ i,v i=true)

def third : Fin 3 → Fin 3 → Fin 3 :=
  ![![0,2,1],![2,1,0],![1,0,2]]

theorem third_distinct : ∀ i j : Fin 3,i≠j → third i j≠i ∧ third i j≠j := by
  decide

/-- The diagonal is the boundary-edge coordinate. An off-diagonal entry
represents the common edge of two nonboundary faces. -/
def compatibleRows (occupied : Finset (Fin 3)) (v : Row) (i j : Fin 3) : Bool :=
  if i=j then v i
  else if i∈occupied then
    if j∈occupied then
      if occupied=Finset.univ then v (third i j) else !(v (third i j))
    else v j
  else v i

theorem compatibleRows_diagonal : ∀ occupied v i,
    compatibleRows occupied v i i=v i := by
  decide

theorem unoccupied_row_constant : ∀ occupied v i,i∉occupied →
    ∀ j,compatibleRows occupied v i j=v i := by
  decide

/-- This is exactly the simultaneous row choice in equation (6.1), for all
eight occupation patterns and all six permitted boundary response states. -/
theorem occupied_rows_nonconstant : ∀ occupied v,Nonconstant v →
    ∀ i,i∈occupied → Nonconstant (compatibleRows occupied v i) := by
  decide

theorem occupied_intersections_agree : ∀ occupied v i j,i≠j →
    (i∈occupied ∨ j∈occupied) →
      compatibleRows occupied v i j=compatibleRows occupied v j i := by
  decide

def integerBit (b : Bool) : ℤ := if b then 1 else 0

/-- Equation (6.4), before embedding its integer values into the reals. -/
def coreSlack (a b x y : Bool) : ℤ :=
  max (integerBit a) (integerBit b)-integerBit a*integerBit y-
    integerBit b*integerBit x+integerBit x*integerBit y

theorem coreSlack_nonnegative : ∀ a b x y,0≤coreSlack a b x y := by decide

theorem coreSlack_has_zero : ∀ a b,∃ x y,coreSlack a b x y=0 := by decide

theorem coreSlack_has_positive : ∀ a b,∃ x y,0<coreSlack a b x y := by decide

/-- Both values of either third-vertex bit remain visible at a reduced
zero when the two rows agree. -/
theorem coreSlack_equal_bits_zero : ∀ a x,coreSlack a a x a=0 := by decide

def boundarySlack (v x p : Bool) : ℤ :=
  -integerBit v*integerBit p+integerBit x*integerBit p

def boundaryMinimum (v x : Bool) : ℤ := integerBit v*(integerBit x-1)

theorem boundaryMinimum_le : ∀ v x p,boundaryMinimum v x≤boundarySlack v x p := by
  decide

theorem boundaryMinimum_attained : ∀ v x,∃ p,boundarySlack v x p=boundaryMinimum v x := by
  decide

theorem boundaryStrictExcess : ∀ v,∃ x p,boundaryMinimum v x<boundarySlack v x p := by
  decide

theorem boundary_tie : ∀ v p,boundarySlack v v p=boundaryMinimum v v := by decide

/-- Recovering the effective coefficients from the three reduced zero
rows in the zero-bit case. All variation coefficients remain arbitrary real
numbers. -/
theorem recover_zero_effective_row (c A B h : ℝ)
    (h00 : c=0) (h10 : c-B=0) (h01 : c-A=0) :
    c=0 ∧ A=0 ∧ B=0 := by
  exact ⟨h00,by linarith,by linarith⟩

/-- The corresponding three-row recovery for the one-bit case. -/
theorem recover_one_effective_row (c A B h : ℝ)
    (h10 : c-B=0) (h01 : c-A=0) (h11 : c-A-B+h=0) :
    c=h ∧ A=h ∧ B=h := by
  exact ⟨by linarith,by linarith,by linarith⟩

def realBit (b : Bool) : ℝ := if b then 1 else 0

/-- The one-child completion `r=1-b` determines the child scale, rather
than merely asserting that the resulting boundary response vanishes. -/
theorem recover_one_child (b : Row) (hb : Nonconstant b) (d lam h : ℝ)
    (he : ∀ i,d-lam*(1-realBit (b i))=h*realBit (b i)) :
    d=h ∧ lam=h := by
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := hb
  have h0 := he i
  have h1 := he j
  simp only [hi,hj,realBit,Bool.false_eq_true,ite_false,ite_true] at h0 h1
  constructor <;> nlinarith

def unitResponse (i : Fin 3) (x : Fin 3) : ℝ := if x=i then 1 else 0

/-- Two other unit responses complete a unit row, and equation (6.6)
then fixes both child scales and the triangle coefficient. -/
theorem recover_two_unit_children (i j k : Fin 3)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) (d lam mu h : ℝ)
    (he : ∀ x,d-lam*unitResponse i x-mu*unitResponse j x=h*unitResponse k x) :
    d=h ∧ lam=h ∧ mu=h := by
  have hi := he i
  have hj := he j
  have hk := he k
  simp only [unitResponse,ite_true,ite_false,hij,hik,hjk,
    Ne.symm hij,Ne.symm hik,Ne.symm hjk,mul_one,mul_zero,sub_zero] at hi hj hk
  exact ⟨by linarith,by linarith,by linarith⟩

/-- The complementary-unit completion gives triangle coefficient `2h`
and fixes the same common scale on both children. -/
theorem recover_two_complement_children (i j k : Fin 3)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) (d lam mu h : ℝ)
    (he : ∀ x,d-lam*(1-unitResponse i x)-mu*(1-unitResponse j x)=
      h*(1-unitResponse k x)) :
    d=2*h ∧ lam=h ∧ mu=h := by
  have hi := he i
  have hj := he j
  have hk := he k
  simp only [unitResponse,ite_true,ite_false,hij,hik,hjk,
    Ne.symm hij,Ne.symm hik,Ne.symm hjk,mul_one,mul_zero,sub_zero,sub_self] at hi hj hk
  exact ⟨by linarith,by linarith,by linarith⟩

end RootedResponse
end GraphicalZonotopes
