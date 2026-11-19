module

public import Papers.GraphicalZonotopes.DoubledPartsBoolean
public import Papers.GraphicalZonotopes.QuadraticSignAlgebra

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators symmDiff
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary marginal of the induced-edge count. -/
theorem graphFunction_insert (G : SimpleGraph V) (u : V) (S : Finset V) (hu : u∉S) :
    graphFunction G (insert u S)=graphFunction G S+
      ∑ w∈S,if G.Adj u w then (1 : ℝ) else 0 := by
  revert hu
  induction S using Finset.induction_on with
  | empty =>
    intro hu
    simp only [insert_empty_eq, sum_empty, add_zero, (graphFunction_translationNormalized G).2]
    exact (graphFunction_translationNormalized G).1.symm
  | @insert w S hw ih =>
    intro hu
    have huS : u∉S := fun h => hu (mem_insert_of_mem h)
    have huw : u≠w := fun h => hu (by simp [h])
    have hd := graphFunction_delta G huw huS hw
    have hm := ih huS
    rw [sum_insert hw]
    unfold delta at hd
    linarith

namespace DoubledParts
variable {I : Type*} [Fintype I] [DecidableEq I]

def firstSet (S : Finset (I×Fin 2)) : Finset I := univ.filter fun i => (i,0)∈S
def secondSet (S : Finset (I×Fin 2)) : Finset I := univ.filter fun i => (i,1)∈S

@[simp] theorem mem_firstSet (S : Finset (I×Fin 2)) (i : I) : i∈firstSet S ↔ (i,0)∈S := by
  simp [firstSet]
@[simp] theorem mem_secondSet (S : Finset (I×Fin 2)) (i : I) : i∈secondSet S ↔ (i,1)∈S := by
  simp [secondSet]

theorem subset_eq_two_images (S : Finset (I×Fin 2)) :
    S=(firstSet S).image (fun i => (i,0)) ∪ (secondSet S).image (fun i => (i,1)) := by
  ext v
  rcases v with ⟨i,b⟩
  fin_cases b <;> simp

theorem card_eq_first_add_second (S : Finset (I×Fin 2)) :
    S.card=(firstSet S).card+(secondSet S).card := by
  have hd : Disjoint ((firstSet S).image (fun i => (i,(0 : Fin 2))))
      ((secondSet S).image (fun i => (i,(1 : Fin 2)))) := by
    apply disjoint_left.mpr
    rintro w hw₀ hw₁
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hw₀
    obtain ⟨j,hj,he⟩ := mem_image.mp hw₁
    have hh := congrArg Prod.snd he
    norm_num at hh
  conv_lhs => rw [subset_eq_two_images S]
  rw [card_union_of_disjoint hd,
    card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h),
    card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]

/-- Pairs internal to one doubled part. -/
def internalPairFunction : SetFunction (I×Fin 2) :=
  ∑ i : I,setMonomial {(i,0),(i,1)}

theorem internalPairFunction_eq (S : Finset (I×Fin 2)) :
    internalPairFunction S=((firstSet S∩secondSet S).card : ℝ) := by
  simp only [internalPairFunction,Finset.sum_apply,setMonomial,Finset.insert_subset_iff,Finset.singleton_subset_iff]
  rw [← sum_filter]
  simp only [sum_const,nsmul_eq_mul,mul_one]
  congr 1
  apply congrArg Finset.card
  ext i
  simp

def allPairFunction (S : Finset (I×Fin 2)) : ℝ := (S.card.choose 2 : ℝ)

theorem allPairFunction_delta {u v : I×Fin 2} (huv : u≠v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    delta allPairFunction u v S=1 := by
  have huvS : u∉insert v S := by simp [huv,hu]
  simp only [delta,allPairFunction,card_insert_of_notMem hu,card_insert_of_notMem hv,
    card_insert_of_notMem huvS]
  have h1 : (S.card+1).choose 2=S.card.choose 2+S.card := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' S.card 1
  have h2 : (S.card+1+1).choose 2=(S.card+1).choose 2+(S.card+1) := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' (S.card+1) 1
  rw [h2,h1]
  push_cast
  ring

theorem internalPairFunction_delta {u v : I×Fin 2} (huv : u≠v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    delta internalPairFunction u v S=if u.1=v.1 then 1 else 0 := by
  rw [internalPairFunction,delta_sum]
  simp_rw [delta_setMonomial huv hu hv]
  by_cases hp : u.1=v.1
  · rw [if_pos hp,sum_eq_single u.1]
    · rcases u with ⟨i,a⟩
      rcases v with ⟨j,b⟩
      dsimp at hp
      subst j
      fin_cases a <;> fin_cases b <;> simp_all [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    · intro i hi hne
      have hn : u∉({(i,0),(i,1)} : Finset (I×Fin 2)) := by
        intro hm
        simp only [mem_insert,mem_singleton] at hm
        rcases hm with he | he <;> exact hne (congrArg Prod.fst he).symm
      simp [hn]
    · simp
  · rw [if_neg hp]
    apply sum_eq_zero
    intro i hi
    have hn : ¬(u∈({(i,0),(i,1)} : Finset (I×Fin 2)) ∧
        v∈({(i,0),(i,1)} : Finset (I×Fin 2))) := by
      rintro ⟨hu',hv'⟩
      simp only [mem_insert,mem_singleton] at hu' hv'
      rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;>
        exact hp ((congrArg Prod.fst hu').trans (congrArg Prod.fst hv').symm)
    simp only [ite_eq_right_iff,one_ne_zero,imp_false,not_and]
    intro hu' hv'
    exact False.elim (hn ⟨hu',hv'⟩)

/-- The exact induced-edge formula in all dimensions. Both sides are
identified by their complete elemental rows and normalization. -/
theorem graphFunction_eq_allPairs_sub_internal :
    graphFunction (graph I)=allPairFunction-internalPairFunction := by
  have hnorm : TranslationNormalized
      (graphFunction (graph I)-(allPairFunction-internalPairFunction)) := by
    constructor
    · change graphFunction (graph I) ∅ - (allPairFunction ∅ - internalPairFunction ∅) = 0
      rw [(graphFunction_translationNormalized (graph I)).1]
      simp [allPairFunction,internalPairFunction,setMonomial]
    · intro v
      have hp : ∀ i : I,¬({(i,0),(i,1)} : Finset (I×Fin 2))⊆{v} := by
        intro i h
        have h0 := h (by simp : (i,0)∈({(i,0),(i,1)} : Finset (I×Fin 2)))
        have h1 := h (by simp : (i,1)∈({(i,0),(i,1)} : Finset (I×Fin 2)))
        simp only [mem_singleton] at h0 h1
        have h01 := congrArg Prod.snd (h0.trans h1.symm)
        norm_num at h01
      simp [allPairFunction,internalPairFunction,setMonomial,hp,
        (graphFunction_translationNormalized _).2]
  apply sub_eq_zero.mp
  apply normalized_zero_elemental_eq_zero hnorm
  intro u v huv S hu hv
  rw [delta_sub,delta_sub,graphFunction_delta _ huv hu hv,
    allPairFunction_delta huv hu hv,internalPairFunction_delta huv hu hv]
  by_cases hp : u.1=v.1 <;> simp [graph,hp]

theorem firstWeight_sum (S : Finset (I×Fin 2)) :
    (∑ v∈S,firstWeight v : ℤ)=((firstSet S).card : ℤ) := by
  rw [show (∑ v∈S,firstWeight v : ℤ)=
      ∑ v∈S.filter (fun v => v.2=0),(1 : ℤ) by simp [firstWeight,sum_filter]]
  simp only [sum_const,nsmul_eq_mul,mul_one]
  congr 1
  apply card_bij (fun v _ => v.1)
  · intro v hv
    rcases mem_filter.mp hv with ⟨hv,hv0⟩
    apply (mem_firstSet S v.1).mpr
    have he : (v.1, (0 : Fin 2)) = v := Prod.ext rfl hv0.symm
    rwa [he]
  · intro v hv w hw h
    apply Prod.ext h
    exact (mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm
  · intro i hi
    exact ⟨(i,0),by simpa using hi,rfl⟩

theorem integerData_count_identity (S : Finset (I×Fin 2)) :
    integerData S+((firstSet S∩secondSet S).card : ℤ)=
      (S.card.choose 2 : ℤ)+((firstSet S).card : ℤ) := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [cast_integerData,graphFunction_eq_allPairs_sub_internal]
  simp only [modular,subsetSum,← Int.cast_sum]
  change (allPairFunction S-internalPairFunction S)+
    ((∑ v∈S,firstWeight v : ℤ) : ℝ)+((firstSet S∩secondSet S).card : ℝ)=_
  rw [internalPairFunction_eq,firstWeight_sum]
  change (S.card.choose 2 : ℝ)-_+_+_= _
  push_cast
  ring

/-- Exact parity of the defining integer quadratic form: its quadratic part
is the complete form on the symmetric difference of the two selected sets. -/
theorem integerData_phase (S : Finset (I×Fin 2)) :
    (-1 : ℝ)^(integerData S)=
      QuadraticSign.parity (firstSet S).card *
        QuadraticSign.complete (firstSet S ∆ secondSet S) := by
  have hc : S.card=(firstSet S∆secondSet S).card+2*(firstSet S∩secondSet S).card := by
    rw [card_eq_first_add_second]
    exact (QuadraticSign.card_symmDiff_add_twice_inter _ _).symm
  have hi := congrArg (fun n : ℤ => (-1 : ℝ)^n) (integerData_count_identity S)
  rw [zpow_add₀ (by norm_num),zpow_add₀ (by norm_num)] at hi
  simp only [zpow_natCast] at hi
  change (-1 : ℝ)^integerData S*QuadraticSign.parity (firstSet S∩secondSet S).card=
    QuadraticSign.triangle S.card*QuadraticSign.parity (firstSet S).card at hi
  rw [hc,QuadraticSign.triangle_add_twice] at hi
  apply mul_right_cancel₀ (QuadraticSign.parity_ne_zero (firstSet S∩secondSet S).card)
  calc
    (-1 : ℝ)^integerData S*QuadraticSign.parity (firstSet S∩secondSet S).card =
        (QuadraticSign.triangle (firstSet S∆secondSet S).card*
          QuadraticSign.parity (firstSet S∩secondSet S).card)*
          QuadraticSign.parity (firstSet S).card := hi
    _ = _ := by unfold QuadraticSign.complete; ring

end DoubledParts
end GraphicalZonotopes
