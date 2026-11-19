module

public import Papers.GraphicalZonotopes.GraphFunctionTwins
public import Papers.GraphicalZonotopes.FloorHalf
public import Papers.GraphicalZonotopes.Lattice
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The ordinary complete multipartite graph with a pair in each part. -/
def graph (I : Type*) : SimpleGraph (I×Fin 2) where
  Adj u v := u.1≠v.1
  symm := ⟨fun _ _ => Ne.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

def integerGraphCount (S : Finset (I×Fin 2)) : ℤ :=
  ∑ C∈edgeFamily (graph I),if C⊆S then 1 else 0

def firstWeight (v : I×Fin 2) : ℤ := if v.2=0 then 1 else 0

def integerData (S : Finset (I×Fin 2)) : ℤ :=
  integerGraphCount S+∑ v∈S,firstWeight v

/-- An explicit uniform integral function for all even and odd numbers of
parts: the floor of half the induced-edge count plus first-vertex count. -/
def setFunction (S : Finset (I×Fin 2)) : ℝ := ((integerData S/2 : ℤ) : ℝ)

theorem delta_setFunction (u v : I×Fin 2) (S : Finset (I×Fin 2)) :
    delta setFunction u v S=
      ((integerData (insert u (insert v S))/2+integerData S/2-
        integerData (insert u S)/2-integerData (insert v S)/2 : ℤ) : ℝ) := by
  simp only [delta,setFunction,Int.cast_sub,Int.cast_add]
  ring

theorem cast_integerGraphCount (S : Finset (I×Fin 2)) :
    (integerGraphCount S : ℝ)=graphFunction (graph I) S := by
  simp [integerGraphCount,graphFunction,setMonomial,Finset.sum_apply]

theorem cast_integerData (S : Finset (I×Fin 2)) :
    (integerData S : ℝ)=graphFunction (graph I) S+
      modular (fun v : I×Fin 2 => (firstWeight v : ℝ)) S := by
  simp only [integerData,Int.cast_add,Int.cast_sum,cast_integerGraphCount,modular,subsetSum]

@[simp] theorem integerGraphCount_empty : integerGraphCount (I := I) ∅=0 := by
  apply Int.cast_injective (α := ℝ)
  rw [cast_integerGraphCount,(graphFunction_translationNormalized (graph I)).1]
  norm_num

@[simp] theorem integerGraphCount_singleton (v : I×Fin 2) : integerGraphCount {v}=0 := by
  apply Int.cast_injective (α := ℝ)
  rw [cast_integerGraphCount,(graphFunction_translationNormalized (graph I)).2]
  norm_num

theorem setFunction_translationNormalized : TranslationNormalized (setFunction (I := I)) := by
  constructor
  · change setFunction ∅ = 0
    simp [setFunction, integerData]
  · intro v
    simp only [setFunction, integerData, integerGraphCount_singleton, sum_singleton, zero_add]
    by_cases h : v.2=0 <;> norm_num [firstWeight,h]

theorem integerData_mixed {u v : I×Fin 2} (huv : u≠v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    integerData (insert u (insert v S))+integerData S-
      integerData (insert u S)-integerData (insert v S)=
      if (graph I).Adj u v then 1 else 0 := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  simp only [cast_integerData]
  have hg := graphFunction_delta (graph I) huv hu hv
  have hm := delta_modular (fun v : I×Fin 2 => (firstWeight v : ℝ)) huv hu hv
  unfold delta at hg hm
  split_ifs with h
  · rw [if_pos h] at hg
    linarith
  · rw [if_neg h] at hg
    linarith

theorem integerData_twins_consecutive {u v : I×Fin 2} (huv : u≠v)
    (hnon : ¬(graph I).Adj u v) {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    integerData (insert u S)+1=integerData (insert v S) ∨
    integerData (insert v S)+1=integerData (insert u S) := by
  have hp : u.1=v.1 := Classical.not_not.mp hnon
  have ht : ∀ w,(graph I).Adj u w↔(graph I).Adj v w := by
    intro w
    change u.1≠w.1 ↔ v.1≠w.1
    rw [hp]
  have hg : integerGraphCount (insert u S)=integerGraphCount (insert v S) := by
    apply Int.cast_injective (α := ℝ)
    rw [cast_integerGraphCount,cast_integerGraphCount]
    exact graphFunction_insert_twins (graph I) ht S hu hv
  have hside : u.2≠v.2 := fun he => huv (Prod.ext hp he)
  have hw : firstWeight u+1=firstWeight v ∨ firstWeight v+1=firstWeight u := by
    rcases u with ⟨i,a⟩
    rcases v with ⟨j,b⟩
    fin_cases a <;> fin_cases b <;> simp_all [firstWeight]
  simp only [integerData,sum_insert hu,sum_insert hv]
  rcases hw with hw | hw
  · left
    linarith
  · right
    linarith

theorem setFunction_graphical : Graphical (graph I) (setFunction (I := I)) := by
  intro u v huv hnon S hu hv
  have hm := integerData_mixed huv hu hv
  rw [if_neg hnon] at hm
  have ht := integerData_twins_consecutive huv hnon hu hv
  have hh := FloorHalf.twins_zero _ _ _ _ hm ht
  rw [delta_setFunction]
  exact_mod_cast hh

/-- Every original elemental slack is Boolean, uniformly in the number of
parts and in every conditioning subset. -/
theorem setFunction_boolean {u v : I×Fin 2} (huv : u≠v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    delta (setFunction (I := I)) u v S=0 ∨ delta (setFunction (I := I)) u v S=1 := by
  by_cases hadj : (graph I).Adj u v
  · have hm := integerData_mixed huv hu hv
    rw [if_pos hadj] at hm
    have hh := FloorHalf.edge_boolean_of_mixed _ _ _ _ hm
    rcases hh with hh | hh
    · left
      rw [delta_setFunction]
      exact_mod_cast hh
    · right
      rw [delta_setFunction]
      exact_mod_cast hh
  · exact Or.inl (setFunction_graphical u v huv hadj S hu hv)

theorem setFunction_supermodular : Supermodular (setFunction (I := I)) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rcases setFunction_boolean huv hu hv with he | he <;> rw [he] <;> norm_num

theorem setFunction_integerValued : IntegerValued (setFunction (I := I)) :=
  fun S => ⟨integerData S/2,rfl⟩

def complementFunction : SetFunction (I×Fin 2) := graphFunction (graph I)-setFunction

theorem complementFunction_translationNormalized :
    TranslationNormalized (complementFunction (I := I)) := by
  constructor
  · change graphFunction (graph I) ∅-setFunction ∅=0
    rw [(graphFunction_translationNormalized _).1,setFunction_translationNormalized.1,sub_self]
  · intro v
    change graphFunction (graph I) {v}-setFunction {v}=0
    rw [(graphFunction_translationNormalized _).2 v,setFunction_translationNormalized.2 v,sub_self]

theorem complementFunction_supermodular : Supermodular (complementFunction (I := I)) := by
  have h := graphical_complement_supermodular (G := graph I) (z := setFunction) setFunction_graphical (show (0 : ℝ)≤1 by norm_num)
    (fun u v huv _ S hu hv => by
      rcases setFunction_boolean huv hu hv with he | he <;> rw [he] <;> norm_num)
  simpa only [complementFunction,one_smul] using h

theorem complementFunction_integerValued : IntegerValued (complementFunction (I := I)) :=
  (graphFunction_integerValued _).sub setFunction_integerValued

def polytope : Set ((I×Fin 2) → ℝ) := basePolytope setFunction
def complementPolytope : Set ((I×Fin 2) → ℝ) := basePolytope complementFunction

theorem polytope_lattice : LatticePolytope (polytope (I := I)) :=
  setFunction_integerValued.basePolytope setFunction_translationNormalized.1 setFunction_supermodular

theorem complementPolytope_lattice : LatticePolytope (complementPolytope (I := I)) :=
  complementFunction_integerValued.basePolytope complementFunction_translationNormalized.1
    complementFunction_supermodular

theorem polytope_add_complement :
    polytope (I := I)+complementPolytope=graphicalZonotope (graph I) := by
  rw [polytope,complementPolytope,←basePolytope_add setFunction_translationNormalized.1
    complementFunction_translationNormalized.1 setFunction_supermodular complementFunction_supermodular]
  rw [show (setFunction (I := I)+complementFunction)=graphFunction (graph I) by
    unfold complementFunction
    abel,baseGraphFunction_eq_graphicalZonotope]

end DoubledParts
end GraphicalZonotopes
