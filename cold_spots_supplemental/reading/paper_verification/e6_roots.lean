module

public import PaperVerification.E6Euclidean
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def l6SimpleRoot : Fin 6 → TriTriple :=
  ![(fun _ ↦ -triC),![(1,0),0,0],![(-1,-1),0,0],
    ![0,(1,0),0],![0,(-1,-1),0],![0,0,(1,0)]]

def e6SimpleRoot (j : Fin 6) : Fin 6 → ℝ := e6PhysicalPoint (l6SimpleRoot j)

def l6RootSum (t : Fin 6 → ℝ) : TriTriple := ∑ j,t j•l6SimpleRoot j

def l6RootCoordinates (z : TriTriple) : Fin 6 → ℝ :=
  ![3*(z 2).2,(z 0).1+2*(z 2).2-(z 0).2,(z 2).2-(z 0).2,
    (z 1).1+2*(z 2).2-(z 1).2,(z 2).2-(z 1).2,(z 2).1+(z 2).2]

theorem l6RootCoordinates_sum (t : Fin 6 → ℝ) : l6RootCoordinates (l6RootSum t)=t := by
  ext i
  fin_cases i <;> simp [l6RootCoordinates,l6RootSum,l6SimpleRoot,triC,Fin.sum_univ_succ] <;> ring

theorem l6RootSum_coordinates (z : TriTriple) : l6RootSum (l6RootCoordinates z)=z := by
  ext i <;> fin_cases i <;>
    simp [l6RootCoordinates,l6RootSum,l6SimpleRoot,triC,Fin.sum_univ_succ] <;> ring

theorem l6RootSum_injective : Function.Injective l6RootSum :=
  Function.LeftInverse.injective l6RootCoordinates_sum

def triDot (z w : TriPoint) : ℝ := z.1*w.1-(z.1*w.2+z.2*w.1)/2+z.2*w.2

theorem triTripleFlatten_dot (z w : TriTriple) :
    (∑ i, triTripleFlatten z i*triTripleFlatten w i)=∑ i, triDot (z i) (w i) := by
  rw [Fin.sum_univ_add (a:=3) (b:=3),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [triTripleFlatten,Fin.addCases_left,Fin.addCases_right]
  have h3 : Real.sqrt 3^2=(3:ℝ) := Real.sq_sqrt (by norm_num)
  dsimp [triDot]
  nlinarith only [congrArg (fun t : ℝ ↦ t*(z i).2*(w i).2) h3]

theorem e6PhysicalPoint_dot (z w : TriTriple) :
    (∑ i, e6PhysicalPoint z i*e6PhysicalPoint w i)=2*∑ i, triDot (z i) (w i) := by
  have hs : Real.sqrt 2^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
  unfold e6PhysicalPoint scaleVec
  have he (i : Fin 6) : Real.sqrt 2*triTripleFlatten z i*(Real.sqrt 2*triTripleFlatten w i)=
      2*(triTripleFlatten z i*triTripleFlatten w i) := by
    have h := congrArg (fun t : ℝ ↦ t*(triTripleFlatten z i*triTripleFlatten w i)) hs
    nlinarith only [h]
  simp_rw [he]
  rw [← Finset.mul_sum,triTripleFlatten_dot]

def e6Cartan : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2,-1,0,-1,0,-1;
     -1,2,-1,0,0,0;
     0,-1,2,0,0,0;
     -1,0,0,2,-1,0;
     0,0,0,-1,2,0;
     -1,0,0,0,0,2]

/-- The displayed simple roots have exactly the E₆ Cartan Gram matrix,
with arms of lengths two, two, and one and root norm squared two. -/
theorem e6SimpleRoot_gram (i j : Fin 6) :
    (∑ k, e6SimpleRoot i k*e6SimpleRoot j k)=(e6Cartan i j : ℝ) := by
  rw [show e6SimpleRoot i=e6PhysicalPoint (l6SimpleRoot i) from rfl,
    show e6SimpleRoot j=e6PhysicalPoint (l6SimpleRoot j) from rfl,e6PhysicalPoint_dot]
  fin_cases i <;> fin_cases j <;>
    norm_num [l6SimpleRoot,e6Cartan,triDot,triC,Fin.sum_univ_succ]

theorem l6Set_simpleRoot_span (z : TriTriple) : z ∈ l6Set ↔
    ∃ t : Fin 6 → ℤ, z=∑ j, (t j : ℝ)•l6SimpleRoot j := by
  rw [l6Set_iff_integer_glue]
  constructor
  · rintro ⟨m,k,hm⟩
    let t : Fin 6 → ℤ := ![3*(m 2).2-k,
      (m 0).1+2*(m 2).2-(m 0).2,(m 2).2-(m 0).2,
      (m 1).1+2*(m 2).2-(m 1).2,(m 2).2-(m 1).2,(m 2).1+(m 2).2]
    refine ⟨t,?_⟩
    ext i <;> rw [hm i] <;> fin_cases i <;>
      simp [t,l6SimpleRoot,Fin.sum_univ_succ,triC,eisEmbed] <;> ring
  · rintro ⟨t,rfl⟩
    let m : Fin 3 → EisInt := ![(t 1-t 2,-t 2),(t 3-t 4,-t 4),(t 5,0)]
    refine ⟨m,-t 0,?_⟩
    intro i
    fin_cases i <;> ext <;> simp [m,l6SimpleRoot,Fin.sum_univ_succ,triC,eisEmbed] <;> ring

lemma e6PhysicalPoint_sum_smul (t : Fin 6 → ℤ) (v : Fin 6 → TriTriple) :
    e6PhysicalPoint (∑ j, (t j : ℝ)•v j)=∑ j, (t j : ℝ)•e6PhysicalPoint (v j) := by
  funext i
  refine Fin.addCases (m:=3) (n:=3) (fun k ↦ ?_) (fun k ↦ ?_) i
  · simp only [e6PhysicalPoint,scaleVec,triTripleFlatten,Finset.sum_apply,
      Pi.smul_apply,Fin.addCases_left,Prod.fst_sum,Prod.snd_sum,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    rw [Finset.sum_div,← Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · simp only [e6PhysicalPoint,scaleVec,triTripleFlatten,Finset.sum_apply,
      Pi.smul_apply,Fin.addCases_right,Prod.snd_sum,Prod.smul_snd,smul_eq_mul]
    rw [Finset.mul_sum,Finset.sum_div,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- This identifies the coordinate lattice with the integer lattice generated
by the actual E₆ simple roots, not merely an isospectral construction. -/
theorem e6Set_simpleRoot_span (x : Fin 6 → ℝ) : x ∈ e6Set ↔
    ∃ t : Fin 6 → ℤ, x=∑ j, (t j : ℝ)•e6SimpleRoot j := by
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    obtain ⟨t,rfl⟩ := (l6Set_simpleRoot_span z).mp hz
    exact ⟨t,e6PhysicalPoint_sum_smul t l6SimpleRoot⟩
  · rintro ⟨t,rfl⟩
    refine ⟨triTripleFlatten (∑ j, (t j : ℝ)•l6SimpleRoot j),
      ⟨_,(l6Set_simpleRoot_span _).mpr ⟨t,rfl⟩,rfl⟩,?_⟩
    exact e6PhysicalPoint_sum_smul t l6SimpleRoot

end PaperVerification.ColdSpots
