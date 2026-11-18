module

public import Papers.GraphicalZonotopes.PairCounting
public import Papers.GraphicalZonotopes.Reflection
public import Papers.GraphicalZonotopes.GraphDefinitions

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem two_choose_two_int (n : ℕ) :
    2*(n.choose 2 : ℤ)=(n : ℤ)*((n : ℤ)-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hc : (n+1).choose 2=n.choose 2+n := by
      simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' n 1
    rw [hc]
    push_cast
    nlinarith

@[simp] theorem firstSet_compl (S : Finset (I×Fin 2)) : firstSet Sᶜ=(firstSet S)ᶜ := by
  ext i
  simp
@[simp] theorem secondSet_compl (S : Finset (I×Fin 2)) : secondSet Sᶜ=(secondSet S)ᶜ := by
  ext i
  simp
@[simp] theorem firstSet_univ : firstSet (univ : Finset (I×Fin 2))=univ := by
  ext i
  simp
@[simp] theorem secondSet_univ : secondSet (univ : Finset (I×Fin 2))=univ := by
  ext i
  simp

theorem double_count_compl (S : Finset (I×Fin 2)) :
    ((firstSet Sᶜ∩secondSet Sᶜ).card : ℤ)=
      (Fintype.card I : ℤ)-(S.card : ℤ)+((firstSet S∩secondSet S).card : ℤ) := by
  have hU : firstSet Sᶜ∩secondSet Sᶜ=(firstSet S∪secondSet S)ᶜ := by
    ext i
    simp
  have hcard := card_union_add_card_inter (firstSet S) (secondSet S)
  have hbound := card_le_univ (firstSet S∪secondSet S)
  rw [hU,card_compl,Nat.cast_sub hbound]
  have hc : ((firstSet S∪secondSet S).card : ℤ)+
      ((firstSet S∩secondSet S).card : ℤ)=((firstSet S).card : ℤ)+((secondSet S).card : ℤ) :=
    by exact_mod_cast hcard
  rw [card_eq_first_add_second]
  push_cast
  omega

theorem integerData_univ :
    integerData (univ : Finset (I×Fin 2))=
      2*(Fintype.card I : ℤ)*((Fintype.card I : ℤ)-1)+(Fintype.card I : ℤ) := by
  have h := integerData_count_identity (univ : Finset (I×Fin 2))
  simp only [firstSet_univ,secondSet_univ,inter_self,card_univ,Fintype.card_prod,
    Fintype.card_fin] at h
  have hc := two_choose_two_int (Fintype.card I*2)
  push_cast at h hc
  nlinarith

theorem integerData_compl (S : Finset (I×Fin 2)) :
    integerData Sᶜ=integerData S+integerData (univ : Finset (I×Fin 2))-
      2*(((Fintype.card I : ℤ)-1)*(S.card : ℤ)+((firstSet S).card : ℤ)) := by
  have hS := integerData_count_identity S
  have hC := integerData_count_identity Sᶜ
  have hcard : (Sᶜ.card : ℤ)=2*(Fintype.card I : ℤ)-(S.card : ℤ) := by
    rw [card_compl,Nat.cast_sub (card_le_univ S)]
    simp [Fintype.card_prod,mul_comm]
  have hfirst : ((firstSet Sᶜ).card : ℤ)=
      (Fintype.card I : ℤ)-((firstSet S).card : ℤ) := by
    rw [firstSet_compl,card_compl,Nat.cast_sub (card_le_univ (firstSet S))]
  rw [double_count_compl,hfirst] at hC
  have h2S := two_choose_two_int S.card
  have h2C := two_choose_two_int Sᶜ.card
  rw [hcard] at h2C
  rw [integerData_univ]
  nlinarith

theorem graphFunction_compl (S : Finset (I×Fin 2)) :
    graphFunction (graph I) Sᶜ-graphFunction (graph I) univ=
      graphFunction (graph I) S-2*((Fintype.card I : ℝ)-1)*(S.card : ℝ) := by
  have h := congrArg (fun m : ℤ => (m : ℝ)) (integerData_compl S)
  push_cast at h
  simp only [cast_integerData,modular,subsetSum] at h
  have hs : (∑ v∈S,(firstWeight v : ℝ))=((firstSet S).card : ℝ) := by
    exact_mod_cast firstWeight_sum S
  have hc : (∑ v∈Sᶜ,(firstWeight v : ℝ))=
      (Fintype.card I : ℝ)-((firstSet S).card : ℝ) := by
    have hh := firstWeight_sum Sᶜ
    rw [firstSet_compl,card_compl,Nat.cast_sub (card_le_univ (firstSet S))] at hh
    exact_mod_cast hh
  have hu : (∑ v : I×Fin 2,(firstWeight v : ℝ))=(Fintype.card I : ℝ) := by
    have hh := firstWeight_sum (univ : Finset (I×Fin 2))
    simp only [firstSet_univ,card_univ] at hh
    exact_mod_cast hh
  rw [hs,hc,hu] at h
  linarith

theorem floor_reflection_even (m M d : ℤ) (hM : Even M) :
    (m+M-2*d)/2-M/2=m/2-d := by
  rcases hM with ⟨k,hk⟩
  omega

theorem floor_reflection_odd (m M d : ℤ) (hM : Odd M) :
    (m+M-2*d)/2-M/2=m-m/2-d := by
  rcases hM with ⟨k,hk⟩
  omega

theorem integerData_univ_even (hI : Even (Fintype.card I)) :
    Even (integerData (univ : Finset (I×Fin 2))) := by
  obtain ⟨k,hk⟩ := hI
  have hc : (Fintype.card I : ℤ)=(k : ℤ)+(k : ℤ) := by exact_mod_cast hk
  rw [integerData_univ]
  refine ⟨(Fintype.card I : ℤ)*((Fintype.card I : ℤ)-1)+(k : ℤ),?_⟩
  nlinarith

theorem integerData_univ_odd (hI : Odd (Fintype.card I)) :
    Odd (integerData (univ : Finset (I×Fin 2))) := by
  obtain ⟨k,hk⟩ := hI
  have hc : (Fintype.card I : ℤ)=2*(k : ℤ)+1 := by exact_mod_cast hk
  rw [integerData_univ]
  refine ⟨(Fintype.card I : ℤ)*((Fintype.card I : ℤ)-1)+(k : ℤ),?_⟩
  nlinarith

def firstReflectionVector (v : I×Fin 2) : ℝ :=
  (Fintype.card I : ℝ)-1+(firstWeight v : ℝ)
def secondReflectionVector (v : I×Fin 2) : ℝ :=
  (Fintype.card I : ℝ)-1-(firstWeight v : ℝ)
def differenceReflectionVector (_ : I×Fin 2) : ℝ := (Fintype.card I : ℝ)-1

theorem modular_firstReflectionVector (S : Finset (I×Fin 2)) :
    modular firstReflectionVector S=
      ((Fintype.card I : ℝ)-1)*(S.card : ℝ)+((firstSet S).card : ℝ) := by
  have h := congrArg (fun m : ℤ => (m : ℝ)) (firstWeight_sum S)
  push_cast at h
  simp only [modular,subsetSum,firstReflectionVector,sum_add_distrib,sum_const,
    nsmul_eq_mul,h]
  ring

theorem modular_secondReflectionVector (S : Finset (I×Fin 2)) :
    modular secondReflectionVector S=
      ((Fintype.card I : ℝ)-1)*(S.card : ℝ)-((firstSet S).card : ℝ) := by
  have h := congrArg (fun m : ℤ => (m : ℝ)) (firstWeight_sum S)
  push_cast at h
  simp only [modular,subsetSum,secondReflectionVector,sum_sub_distrib,sum_const,
    nsmul_eq_mul,h]
  ring

theorem modular_differenceReflectionVector (S : Finset (I×Fin 2)) :
    modular differenceReflectionVector S=((Fintype.card I : ℝ)-1)*(S.card : ℝ) := by
  simp [modular,subsetSum,differenceReflectionVector,mul_comm] <;> ring

theorem reflected_setFunction_even (hI : Even (Fintype.card I)) :
    reflectedFunction (setFunction (I := I))=setFunction-modular firstReflectionVector := by
  funext S
  have h := floor_reflection_even (integerData S) (integerData (univ : Finset (I×Fin 2)))
    (((Fintype.card I : ℤ)-1)*(S.card : ℤ)+((firstSet S).card : ℤ))
    (integerData_univ_even hI)
  rw [← integerData_compl S] at h
  have hc := congrArg (fun m : ℤ => (m : ℝ)) h
  push_cast at hc
  simpa only [reflectedFunction,setFunction,Pi.sub_apply,modular_firstReflectionVector] using hc

theorem reflected_complementFunction_even (hI : Even (Fintype.card I)) :
    reflectedFunction (complementFunction (I := I))=
      complementFunction-modular secondReflectionVector := by
  funext S
  have hz := congrFun (reflected_setFunction_even hI) S
  change setFunction Sᶜ-setFunction univ=setFunction S-modular firstReflectionVector S at hz
  have hg := graphFunction_compl S
  simp only [reflectedFunction,complementFunction,Pi.sub_apply]
  rw [modular_firstReflectionVector] at hz
  rw [modular_secondReflectionVector]
  linarith

theorem reflected_setFunction_odd (hI : Odd (Fintype.card I)) :
    reflectedFunction (setFunction (I := I))=
      complementFunction-modular differenceReflectionVector := by
  funext S
  have h := floor_reflection_odd (integerData S) (integerData (univ : Finset (I×Fin 2)))
    (((Fintype.card I : ℤ)-1)*(S.card : ℤ)+((firstSet S).card : ℤ))
    (integerData_univ_odd hI)
  rw [← integerData_compl S] at h
  have hc := congrArg (fun m : ℤ => (m : ℝ)) h
  push_cast at hc
  rw [cast_integerData] at hc
  have hw : modular (fun v : I×Fin 2 => (firstWeight v : ℝ)) S=((firstSet S).card : ℝ) := by
    change (∑ v∈S,(firstWeight v : ℝ))=_
    exact_mod_cast firstWeight_sum S
  rw [hw] at hc
  change setFunction Sᶜ-setFunction univ=
    (graphFunction (graph I) S-setFunction S)-modular differenceReflectionVector S
  rw [modular_differenceReflectionVector]
  change (((integerData Sᶜ/2 : ℤ) : ℝ)-((integerData univ/2 : ℤ) : ℝ))=_
  dsimp only [setFunction]
  linarith

theorem polytope_centrallySymmetric (hI : Even (Fintype.card I)) :
    CentrallySymmetricUpToTranslation (polytope (I := I)) := by
  exact ⟨firstReflectionVector,basePolytope_eq_translate_reflection
    setFunction_translationNormalized.1 firstReflectionVector (reflected_setFunction_even hI)⟩

theorem complementPolytope_centrallySymmetric (hI : Even (Fintype.card I)) :
    CentrallySymmetricUpToTranslation (complementPolytope (I := I)) := by
  exact ⟨secondReflectionVector,basePolytope_eq_translate_reflection
    complementFunction_translationNormalized.1 secondReflectionVector
    (reflected_complementFunction_even hI)⟩

theorem complementPolytope_reflection (hI : Odd (Fintype.card I)) :
    complementPolytope (I := I)=
      ({differenceReflectionVector} : Set ((I×Fin 2) → ℝ))+(-1 : ℝ) • polytope :=
  basePolytope_eq_translate_reflection setFunction_translationNormalized.1
    differenceReflectionVector (reflected_setFunction_odd hI)

end DoubledParts
end GraphicalZonotopes
