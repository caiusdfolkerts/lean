module

public import PaperVerification.LatticeTranslations
public import Mathlib.Tactic.Module


@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def e8SimpleRoot : Fin 8 → (Fin 8 → ℝ) :=
  ![![1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,1/2],
    ![1,1,0,0,0,0,0,0],![-1,1,0,0,0,0,0,0],
    ![0,-1,1,0,0,0,0,0],![0,0,-1,1,0,0,0,0],
    ![0,0,0,-1,1,0,0,0],![0,0,0,0,-1,1,0,0],![0,0,0,0,0,-1,1,0]]

def e8RootSum (t : Fin 8 → ℝ) : Fin 8 → ℝ := ∑ i, t i • e8SimpleRoot i

def e8RootCoordinates (x : Fin 8 → ℝ) : Fin 8 → ℝ :=
  ![2*x 7,(∑ i, x i)/2+2*x 7,(∑ i, x i)/2+3*x 7-x 0,
    x 2+x 3+x 4+x 5+x 6+5*x 7,x 3+x 4+x 5+x 6+4*x 7,
    x 4+x 5+x 6+3*x 7,x 5+x 6+2*x 7,x 6+x 7]

theorem e8RootCoordinates_sum (t : Fin 8 → ℝ) : e8RootCoordinates (e8RootSum t)=t := by
  ext i
  fin_cases i <;> simp [e8RootCoordinates,e8RootSum,e8SimpleRoot,Fin.sum_univ_succ] <;> ring

theorem e8RootSum_coordinates (x : Fin 8 → ℝ) : e8RootSum (e8RootCoordinates x)=x := by
  ext i
  fin_cases i <;> simp [e8RootCoordinates,e8RootSum,e8SimpleRoot,Fin.sum_univ_succ] <;> ring

theorem e8RootSum_injective : Function.Injective e8RootSum :=
  Function.LeftInverse.injective e8RootCoordinates_sum

theorem e8SimpleRoot_mem (i : Fin 8) : e8SimpleRoot i ∈ dPlusSet 8 := by
  fin_cases i
  · refine ⟨![0,-1,-1,-1,-1,-1,-1,0],by decide,Or.inr ?_⟩
    ext j
    fin_cases j <;> norm_num [e8SimpleRoot]
  all_goals solve
    | refine ⟨![1,1,0,0,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]
    | refine ⟨![-1,1,0,0,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]
    | refine ⟨![0,-1,1,0,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]
    | refine ⟨![0,0,-1,1,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]
    | refine ⟨![0,0,0,-1,1,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]
    | refine ⟨![0,0,0,0,-1,1,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]
    | refine ⟨![0,0,0,0,0,-1,1,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
      ext j; fin_cases j <;> norm_num [e8SimpleRoot,intVec]

theorem e8RootSum_int_mem (t : Fin 8 → ℤ) : e8RootSum (fun i ↦ (t i:ℝ)) ∈ dPlusSet 8 := by
  let L := dPlusAddSubgroup 8 (by decide)
  have h : (∑ i, t i • e8SimpleRoot i) ∈ L :=
    L.sum_mem (fun i hi ↦ L.zsmul_mem (e8SimpleRoot_mem i) (t i))
  change (∑ i, t i • e8SimpleRoot i) ∈ dPlusSet 8 at h
  simpa only [e8RootSum, Int.cast_smul_eq_zsmul] using h

def e8IntCoordinates (m : Fin 8 → ℤ) (k : ℤ) : Fin 8 → ℤ :=
  ![2*m 7,k+2*m 7,k+3*m 7-m 0,
    m 2+m 3+m 4+m 5+m 6+5*m 7,m 3+m 4+m 5+m 6+4*m 7,
    m 4+m 5+m 6+3*m 7,m 5+m 6+2*m 7,m 6+m 7]

def e8HalfCoordinates : Fin 8 → ℤ := ![1,3,3,5,4,3,2,1]

theorem e8RootCoordinates_int (m : Fin 8 → ℤ) (k : ℤ) (hk : ∑ i,m i=k+k) :
    e8RootCoordinates (intVec m)=fun i ↦ (e8IntCoordinates m k i:ℝ) := by
  have hsum : (∑ i,(m i:ℝ))=(k:ℝ)+k := by exact_mod_cast hk
  ext i
  fin_cases i <;> simp [e8RootCoordinates,e8IntCoordinates,intVec,hsum] <;> ring

theorem e8RootCoordinates_half (m : Fin 8 → ℤ) (k : ℤ) (hk : ∑ i,m i=k+k) :
    e8RootCoordinates (fun i ↦ (m i:ℝ)+1/2)=
      fun i ↦ ((e8IntCoordinates m k i+e8HalfCoordinates i:ℤ):ℝ) := by
  have hsum : (∑ i,(m i:ℝ))=(k:ℝ)+k := by exact_mod_cast hk
  ext i
  fin_cases i <;> simp [e8RootCoordinates,e8IntCoordinates,e8HalfCoordinates,
    Finset.sum_add_distrib,hsum] <;> ring

/-- An explicit integral basis for the actual coordinate E₈ lattice. -/
theorem e8_mem_iff_integer_root_coordinates (x : Fin 8 → ℝ) :
    x ∈ dPlusSet 8 ↔ ∃ t : Fin 8 → ℤ, x=e8RootSum (fun i ↦ (t i:ℝ)) := by
  constructor
  · rintro ⟨m,⟨k,hk⟩,rfl|rfl⟩
    · refine ⟨e8IntCoordinates m k,?_⟩
      rw [← e8RootCoordinates_int m k hk,e8RootSum_coordinates]
    · refine ⟨fun i ↦ e8IntCoordinates m k i+e8HalfCoordinates i,?_⟩
      rw [← e8RootCoordinates_half m k hk,e8RootSum_coordinates]
  · rintro ⟨t,rfl⟩
    exact e8RootSum_int_mem t

def e8IntegralQ (t : Fin 8 → ℤ) : ℤ :=
  (∑ i,t i^2)-t 0*t 2-t 2*t 3-t 1*t 3-t 3*t 4-t 4*t 5-t 5*t 6-t 6*t 7

theorem e8RootSum_norm (t : Fin 8 → ℤ) :
    sqDist (e8RootSum (fun i ↦ (t i:ℝ))) 0=2*(e8IntegralQ t:ℝ) := by
  simp [sqDist,e8RootSum,e8SimpleRoot,e8IntegralQ,Fin.sum_univ_succ]
  ring

theorem e8RootSum_add (a b : Fin 8 → ℝ) : e8RootSum (a+b)=e8RootSum a+e8RootSum b := by
  simp [e8RootSum,add_smul,Finset.sum_add_distrib]

theorem e8RootSum_sub (a b : Fin 8 → ℝ) : e8RootSum (a-b)=e8RootSum a-e8RootSum b := by
  simp [e8RootSum,sub_smul,Finset.sum_sub_distrib]

theorem e8RootSum_smul (c : ℝ) (a : Fin 8 → ℝ) : e8RootSum (c•a)=c•e8RootSum a := by
  simp [e8RootSum,smul_smul,Finset.smul_sum]

end PaperVerification.ColdSpots
