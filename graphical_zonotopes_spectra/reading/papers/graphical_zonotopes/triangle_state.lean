module

public import Papers.GraphicalZonotopes.TriangleRows
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace RootedResponse
open Finset
open scoped BigOperators
variable {J T J' T' : Type*} [Fintype J] [Fintype T] [Fintype J'] [Fintype T']

abbrev NonconstantBits (v : T → Bool) : Prop := (∃ x,v x=false) ∧ (∃ x,v x=true)

theorem nonconstantBits_comp (e : T' ≃ T) (v : T → Bool) :
    NonconstantBits (fun x => v (e x)) ↔ NonconstantBits v := by
  constructor
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    exact ⟨⟨e x,hx⟩,⟨e y,hy⟩⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    exact ⟨⟨e.symm x,by simpa using hx⟩,⟨e.symm y,by simpa using hy⟩⟩

/-- Complete local data at an internal triangle: nonconstant incident
rows, constant column sum one or two, and the full real response-kernel
condition forcing all incident clique scales to agree. -/
structure TriangleState (J T : Type*) [Fintype J] where
  row : J → T → Bool
  degree : ℕ
  degree_mem : degree=1 ∨ degree=2
  nonconstant : ∀ j,NonconstantBits (row j)
  sum_row : ∀ x,(∑ j,realBit (row j x))=(degree : ℝ)
  kernel : ∀ (lam : J → ℝ) (d : ℝ),
    (∀ x,(∑ j,lam j*realBit (row j x))=d) → ∀ i j,lam i=lam j

def TriangleState.relabel (s : TriangleState J T) (e : J' ≃ J) (f : T' ≃ T) :
    TriangleState J' T' where
  row j x := s.row (e j) (f x)
  degree := s.degree
  degree_mem := s.degree_mem
  nonconstant j := (nonconstantBits_comp f _).mpr (s.nonconstant (e j))
  sum_row x := by
    rw [Equiv.sum_comp e (fun j => realBit (s.row j (f x)))]
    exact s.sum_row (f x)
  kernel lam d h i j := by
    let μ : J → ℝ := fun k => lam (e.symm k)
    have hμ : ∀ x,(∑ k,μ k*realBit (s.row k x))=d := by
      intro x
      have hx := h (f.symm x)
      simp only [Equiv.apply_symm_apply] at hx
      rw [← Equiv.sum_comp e (fun k => μ k*realBit (s.row k x))]
      simpa only [μ,Equiv.symm_apply_apply] using hx
    simpa only [μ,Equiv.symm_apply_apply] using s.kernel μ d hμ (e i) (e j)

def threeState (complement : Bool) (p : Equiv.Perm (Fin 3)) :
    TriangleState (Fin 3) (Fin 3) where
  row := threeRows complement p
  degree := if complement then 2 else 1
  degree_mem := by cases complement <;> simp
  nonconstant := threeRows_nonconstant complement p
  sum_row x := by
    cases complement
    · simpa only [Bool.false_eq_true, ite_false, Nat.cast_one] using threeRows_sum false p x
    · simpa only [ite_true, Nat.cast_ofNat] using threeRows_sum true p x
  kernel lam d h i j :=
    (threeRows_relation_kernel complement p lam d h).1 i |>.trans
      ((threeRows_relation_kernel complement p lam d h).1 j).symm

def twoState (v : Row) (hv : Nonconstant v) : TriangleState (Fin 2) (Fin 3) where
  row := twoRows v
  degree := 1
  degree_mem := Or.inl rfl
  nonconstant := twoRows_nonconstant v hv
  sum_row x := by simpa only [Nat.cast_one] using twoRows_sum v x
  kernel lam d h i j := by
    have he := (twoRows_relation_kernel v hv lam d h).1
    fin_cases i <;> fin_cases j
    · rfl
    · exact he
    · exact he.symm
    · rfl

def twoInput (j : Fin 2) (v : Row) : Row := if j=0 then v else fun x => !(v x)

theorem twoInput_nonconstant : ∀ j v,Nonconstant v → Nonconstant (twoInput j v) := by
  decide

theorem twoInput_port : ∀ j v,twoRows (twoInput j v) j=v := by decide

theorem triangleState_extend (hT : Fintype.card T=3)
    (hJ : Fintype.card J=2 ∨ Fintype.card J=3) (j : J)
    (v : T → Bool) (hv : NonconstantBits v) :
    ∃ s : TriangleState J T,s.row j=v := by
  classical
  let f := Fintype.equivFinOfCardEq hT
  let input : Row := fun x => v (f.symm x)
  have hin : Nonconstant input := (nonconstantBits_comp f.symm v).mpr hv
  rcases hJ with hJ | hJ
  · let e := Fintype.equivFinOfCardEq hJ
    let s := twoState (twoInput (e j) input) (twoInput_nonconstant _ _ hin)
    refine ⟨s.relabel e f,?_⟩
    funext x
    change twoRows (twoInput (e j) input) (e j) (f x)=v x
    rw [twoInput_port]
    exact congrArg v (f.symm_apply_apply x)
  · let e := Fintype.equivFinOfCardEq hJ
    obtain ⟨complement,p,hport⟩ := threeRows_extend (e j) input hin
    refine ⟨(threeState complement p).relabel e f,?_⟩
    funext x
    change threeRows complement p (e j) (f x)=v x
    rw [hport]
    exact congrArg v (f.symm_apply_apply x)

theorem triangleState_nonempty (hT : Fintype.card T=3)
    (hJ : Fintype.card J=2 ∨ Fintype.card J=3) :
    Nonempty (TriangleState J T) := by
  classical
  have hpos : 0<Fintype.card J := by rcases hJ with hJ | hJ <;> omega
  letI : Nonempty J := Fintype.card_pos_iff.mp hpos
  let f := Fintype.equivFinOfCardEq hT
  let input : T → Bool := fun x => unitBit 0 (f x)
  have hv : NonconstantBits input := (nonconstantBits_comp f (unitBit 0)).mpr ⟨⟨1, rfl⟩, ⟨0, rfl⟩⟩
  obtain ⟨s,hs⟩ := triangleState_extend hT hJ (Classical.arbitrary J) input hv
  exact ⟨s⟩

end RootedResponse
end GraphicalZonotopes
