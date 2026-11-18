module

public import Papers.GraphicalZonotopes.TensorIndicators
public import Papers.GraphicalZonotopes.DoubledPartsBoolean
public import Papers.GraphicalZonotopes.BoundaryContexts

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The usual Boolean coordinates of an arbitrary subset of paired vertices. -/
def subsetOfBits (s : Cube I × Cube I) : Finset (I×Fin 2) :=
  univ.filter fun v => if v.2=0 then s.1 v.1=true else s.2 v.1=true

@[simp] theorem mem_subsetOfBits_zero (s : Cube I × Cube I) (i : I) :
    (i,0)∈subsetOfBits s ↔ s.1 i=true := by simp [subsetOfBits]

@[simp] theorem mem_subsetOfBits_one (s : Cube I × Cube I) (i : I) :
    (i,1)∈subsetOfBits s ↔ s.2 i=true := by simp [subsetOfBits]

def bitsOfSubset (S : Finset (I×Fin 2)) : Cube I × Cube I :=
  (fun i => decide ((i,0)∈S),fun i => decide ((i,1)∈S))

@[simp] theorem subsetOfBits_bitsOfSubset (S : Finset (I×Fin 2)) :
    subsetOfBits (bitsOfSubset S)=S := by
  ext v
  rcases v with ⟨i,b⟩
  fin_cases b <;> simp [bitsOfSubset]

@[simp] theorem bitsOfSubset_subsetOfBits (s : Cube I × Cube I) :
    bitsOfSubset (subsetOfBits s)=s := by
  apply Prod.ext
  · funext i
    simp [bitsOfSubset]
  · funext i
    simp [bitsOfSubset]

def selector (C : Finset (I×Fin 2)) (i : I) : Option Bool :=
  if (i,0)∈C then some false else if (i,1)∈C then some true else none

def IsPartialTransversal (C : Finset (I×Fin 2)) : Prop :=
  ∀ i,¬((i,0)∈C ∧ (i,1)∈C)

theorem clique_partialTransversal {C : Finset (I×Fin 2)}
    (hC : (graph I).IsClique C) : IsPartialTransversal C := by
  intro i hi
  exact hC hi.1 hi.2 (by simp) rfl

theorem selector_zero_iff (C : Finset (I×Fin 2)) (i : I) :
    selector C i=some false ↔ (i,0)∈C := by
  by_cases h0 : (i,0)∈C <;> by_cases h1 : (i,1)∈C <;> simp [selector,h0,h1]

theorem selector_one_iff {C : Finset (I×Fin 2)} (hC : IsPartialTransversal C) (i : I) :
    selector C i=some true ↔ (i,1)∈C := by
  by_cases h0 : (i,0)∈C
  · have h1 : (i,1)∉C := fun h => hC i ⟨h0,h⟩
    simp [selector,h0,h1]
  · simp [selector,h0]

theorem subset_subsetOfBits_iff (C : Finset (I×Fin 2)) (s : Cube I × Cube I) :
    C⊆subsetOfBits s ↔
      (∀ i,(i,0)∈C → s.1 i=true) ∧ (∀ i,(i,1)∈C → s.2 i=true) := by
  constructor
  · intro h
    exact ⟨fun i hi => (mem_subsetOfBits_zero s i).mp (h hi),
      fun i hi => (mem_subsetOfBits_one s i).mp (h hi)⟩
  · rintro ⟨h0,h1⟩ ⟨i,b⟩ hi
    fin_cases b
    · exact (mem_subsetOfBits_zero s i).mpr (h0 i hi)
    · exact (mem_subsetOfBits_one s i).mpr (h1 i hi)

theorem setMonomial_subsetOfBits {C : Finset (I×Fin 2)}
    (hC : IsPartialTransversal C) (s : Cube I × Cube I) :
    setMonomial C (subsetOfBits s)=indicatorMonomial (selector C) s := by
  rw [indicatorMonomial_eq]
  simp only [setMonomial,selector_zero_iff,selector_one_iff hC,subset_subsetOfBits_iff]

theorem setMonomial_mem_tensorSpace {C : Finset (I×Fin 2)}
    (hC : IsPartialTransversal C) :
    (fun uv => setMonomial C (subsetOfBits (coordinateChange.symm uv)))∈tensorSpace := by
  simpa only [setMonomial_subsetOfBits hC] using
    indicatorMonomial_mem_tensorSpace (selector C)

abbrev Remaining (u v : I×Fin 2) := {i : I // i≠u.1 ∧ i≠v.1}

def remainingEmbedding (u v : I×Fin 2) : Remaining u v × Fin 2 ↪ I×Fin 2 where
  toFun w := (w.1.1,w.2)
  inj' := by
    rintro ⟨i,a⟩ ⟨j,b⟩ h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact congrArg (fun z : I × Fin 2 => z.2) h

def edgeContext (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) : Finset (I×Fin 2) :=
  (subsetOfBits s).map (remainingEmbedding u v)

@[simp] theorem left_not_mem_edgeContext (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) : u∉edgeContext u v s := by
  rintro h
  obtain ⟨w,hw,he⟩ := mem_map.mp h
  exact w.1.2.1 (congrArg Prod.fst he)

@[simp] theorem right_not_mem_edgeContext (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) : v∉edgeContext u v s := by
  rintro h
  obtain ⟨w,hw,he⟩ := mem_map.mp h
  exact w.1.2.2 (congrArg Prod.fst he)

def remainingPart (u v : I×Fin 2) (C : Finset (I×Fin 2)) :
    Finset (Remaining u v × Fin 2) :=
  univ.filter fun w => remainingEmbedding u v w∈C

@[simp] theorem mem_remainingPart (u v : I×Fin 2) (C : Finset (I×Fin 2))
    (w : Remaining u v × Fin 2) : w∈remainingPart u v C ↔ remainingEmbedding u v w∈C :=
  by simp [remainingPart]

theorem remainingPart_partialTransversal {u v : I×Fin 2} {C : Finset (I×Fin 2)}
    (hC : IsPartialTransversal C) : IsPartialTransversal (remainingPart u v C) := by
  intro i hi
  exact hC i.1 ⟨(mem_remainingPart _ _ _ _).mp hi.1,(mem_remainingPart _ _ _ _).mp hi.2⟩

theorem clique_edge_subset_iff {u v : I×Fin 2} {C : Finset (I×Fin 2)}
    (hC : (graph I).IsClique C) (hu : u∈C) (hv : v∈C)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    C⊆insert u (insert v (edgeContext u v s)) ↔
      remainingPart u v C⊆subsetOfBits s := by
  constructor
  · intro h w hw
    have he := h ((mem_remainingPart _ _ _ _).mp hw)
    rcases mem_insert.mp he with he | he
    · exact False.elim (w.1.2.1 (congrArg Prod.fst he))
    · rcases mem_insert.mp he with he | he
      · exact False.elim (w.1.2.2 (congrArg Prod.fst he))
      · obtain ⟨w',hw',he⟩ := mem_map.mp he
        have hw'e : w'=w := (remainingEmbedding u v).injective he
        simpa only [hw'e] using hw'
  · intro h w hw
    by_cases hwu : w=u
    · simp [hwu]
    by_cases hwv : w=v
    · simp [hwv]
    have hpu : w.1≠u.1 := hC hw hu hwu
    have hpv : w.1≠v.1 := hC hw hv hwv
    let w' : Remaining u v × Fin 2 := (⟨w.1,hpu,hpv⟩,w.2)
    have hw' : w'∈remainingPart u v C := (mem_remainingPart _ _ _ _).mpr hw
    exact mem_insert_of_mem (mem_insert_of_mem (mem_map.mpr ⟨w',h hw',rfl⟩))

theorem delta_setMonomial_tensor {u v : I×Fin 2} (huv : u≠v)
    {C : Finset (I×Fin 2)} (hC : (graph I).IsClique C) :
    (fun uv => delta (setMonomial C) u v
      (edgeContext u v (coordinateChange.symm uv)))∈tensorSpace := by
  by_cases hu : u∈C
  · by_cases hv : v∈C
    · have h := setMonomial_mem_tensorSpace
        (remainingPart_partialTransversal (u := u) (v := v) (clique_partialTransversal hC))
      convert h using 1
      funext uv
      rw [delta_setMonomial huv (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)]
      simp only [hu,hv,true_and,clique_edge_subset_iff hC hu hv,setMonomial]
    · convert (tensorSpace (I := Remaining u v)).zero_mem using 1
      funext uv
      rw [delta_setMonomial huv (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)]
      simp [hv]
  · convert (tensorSpace (I := Remaining u v)).zero_mem using 1
    funext uv
    rw [delta_setMonomial huv (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)]
    simp [hu]

/-- Every actual elemental row of a normalized graphical function belongs to
the precise tensor space used by the Boolean face argument. No row-space
hypothesis is assumed: it follows from the original clique coefficients. -/
theorem graphical_edgeProfile_mem_tensorSpace {f : SetFunction (I×Fin 2)}
    (hn : TranslationNormalized f) (hG : Graphical (graph I) f)
    {u v : I×Fin 2} (huv : u≠v) :
    (fun uv => delta f u v (edgeContext u v (coordinateChange.symm uv)))∈tensorSpace := by
  have hsupport := (mobius_cliqueSupported_iff (graph I) f).mpr ⟨hn,hG⟩
  have hsum : (∑ C : Finset (I×Fin 2),mobius f C •
      (fun uv => delta (setMonomial C) u v
        (edgeContext u v (coordinateChange.symm uv))))∈tensorSpace := by
    apply (tensorSpace (I := Remaining u v)).sum_mem
    intro C hC
    by_cases hc : mobius f C=0
    · simp only [hc,zero_smul]
      exact (tensorSpace (I := Remaining u v)).zero_mem
    · have hcl : (graph I).IsClique C := by
        by_contra hnC
        exact hc (coefficient_zero_of_not_clique hsupport C (by
          rintro ⟨_,h⟩
          exact hnC h))
      exact (tensorSpace (I := Remaining u v)).smul_mem _ (delta_setMonomial_tensor huv hcl)
  convert hsum using 1
  funext uv
  conv_lhs => rw [← zeta_mobius f,zeta_eq_sum_monomials]
  simp only [delta_sum,delta_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

end DoubledParts
end GraphicalZonotopes
