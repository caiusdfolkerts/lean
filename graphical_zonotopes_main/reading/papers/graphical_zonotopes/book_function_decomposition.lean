module

public import Papers.GraphicalZonotopes.BookBooleanFunctions

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

def outers (A : Finset (H⊕J)) : Finset J:=univ.filter (fun j => Sum.inr j∈A)

@[simp] theorem mem_outers (A : Finset (H⊕J)) (j : J) :
    j∈outers A ↔ Sum.inr j∈A := by simp [outers]

def outerSet (Y : Finset J) : Finset (H⊕J):=Y.map ⟨Sum.inr,Sum.inr_injective⟩

@[simp] theorem mem_outerSet_outer (Y : Finset J) (j : J) :
    Sum.inr j∈outerSet (H:=H) Y ↔ j∈Y := by simp [outerSet]

@[simp] theorem notMem_outerSet_hub (Y : Finset J) (u : H) :
    Sum.inl u∉outerSet Y := by simp [outerSet]

@[simp] theorem outerSet_empty : outerSet (H:=H) (∅ : Finset J)=∅ := by simp [outerSet]

@[simp] theorem outerSet_insert (Y : Finset J) (j : J) :
    outerSet (H:=H) (insert j Y)=insert (Sum.inr j) (outerSet Y) := by simp [outerSet]

def context (X : Finset H) (Y : Finset J) : Finset (H⊕J):=hubSet X∪outerSet Y

@[simp] theorem mem_context_hub (X : Finset H) (Y : Finset J) (u : H) :
    Sum.inl u∈context X Y ↔ u∈X := by simp [context]

@[simp] theorem mem_context_outer (X : Finset H) (Y : Finset J) (j : J) :
    Sum.inr j∈context X Y ↔ j∈Y := by simp [context]

@[simp] theorem context_empty (X : Finset H) : context (J:=J) X ∅=hubSet X := by
  simp [context]

@[simp] theorem context_insert (X : Finset H) (Y : Finset J) (j : J) :
    context X (insert j Y)=insert (Sum.inr j) (context X Y) := by
  simp only [context,outerSet_insert,union_insert]

@[simp] theorem hubs_context (X : Finset H) (Y : Finset J) : hubs (context X Y)=X := by
  ext u
  simp

@[simp] theorem outers_context (X : Finset H) (Y : Finset J) : outers (context X Y)=Y := by
  ext j
  simp

theorem context_parts (A : Finset (H⊕J)) : context (hubs A) (outers A)=A := by
  ext v
  cases v <;> simp

def OuterZero (f : SetFunction (H⊕J)) : Prop :=
  ∀ i j,i≠j → ∀ A,Sum.inr i∉A → Sum.inr j∉A →
    delta f (Sum.inr i) (Sum.inr j) A=0

def boundarySlice (f : SetFunction (H⊕J)) : SetFunction H:=fun X => f (hubSet X)

def privateSlice (f : SetFunction (H⊕J)) (j : J) : SetFunction H:=
  fun X => f (insert (Sum.inr j) (hubSet X))-f (hubSet X)

theorem outer_marginal_constant {f : SetFunction (H⊕J)} (hf : OuterZero f)
    (j : J) (X : Finset H) (Y : Finset J) (hj : j∉Y) :
    f (insert (Sum.inr j) (context X Y))-f (context X Y)=privateSlice f j X := by
  induction Y using Finset.induction_on with
  | empty => simp only [context_empty,privateSlice]
  | @insert i Y hi ih =>
    have hji : j≠i:=fun he => hj (mem_insert.mpr (Or.inl he))
    have hjY : j∉Y:=fun hm => hj (mem_insert_of_mem hm)
    have hz:=hf j i hji (context X Y) (by simpa using hjY) (by simpa using hi)
    have hh:=ih hjY
    rw [context_insert]
    dsimp only [delta] at hz
    linarith

/-- Vanishing on all outer nonedges is exactly the required additive
decomposition into one actual hub function and one actual private slice per
outer vertex. This retains arbitrary real variations, not merely the chosen
Boolean functions. -/
theorem function_context_decomposition {f : SetFunction (H⊕J)} (hf : OuterZero f)
    (X : Finset H) (Y : Finset J) :
    f (context X Y)=boundarySlice f X+∑ j∈Y,privateSlice f j X := by
  induction Y using Finset.induction_on with
  | empty => simp [boundarySlice]
  | @insert j Y hj ih =>
    have hm:=outer_marginal_constant hf j X Y hj
    rw [context_insert,sum_insert hj]
    linarith

theorem function_decomposition {f : SetFunction (H⊕J)} (hf : OuterZero f)
    (A : Finset (H⊕J)) :
    f A=boundarySlice f (hubs A)+∑ j∈outers A,privateSlice f j (hubs A) := by
  simpa only [context_parts] using function_context_decomposition hf (hubs A) (outers A)

theorem boundarySlice_normalized {f : SetFunction (H⊕J)} (hf : TranslationNormalized f) :
    TranslationNormalized (boundarySlice f) := by
  constructor
  · simpa only [Normalized,boundarySlice,hubSet_empty] using hf.1
  · intro a
    simpa [boundarySlice,hubSet] using hf.2 (Sum.inl a)

theorem privateSlice_empty {f : SetFunction (H⊕J)} (hf : TranslationNormalized f) (j : J) :
    privateSlice f j ∅=0 := by
  have h0 : f ∅=0 := hf.1
  simp only [privateSlice,hubSet_empty,insert_empty_eq,h0,hf.2,sub_self]

theorem privateSlice_cover (f : SetFunction (H⊕J)) (j : J) (a : H) (X : Finset H) :
    privateSlice f j (insert a X)-privateSlice f j X=
      delta f (Sum.inl a) (Sum.inr j) (hubSet X) := by
  simp only [privateSlice,hubSet_insert,delta]
  rw [insert_comm (Sum.inr j) (Sum.inl a)]
  ring

theorem graphical_outerZero {s k : ℕ} {f : SetFunction (Fin s⊕Fin k)}
    (hf : Graphical (cliqueBook s k) f) : OuterZero f := by
  intro i j hij A hi hj
  exact hf (Sum.inr i) (Sum.inr j) (fun he => hij (Sum.inr_injective he))
    (by simp [cliqueBook]) A hi hj

/-- Once the actual private slices have specified scales, the original
function itself has that assembled form. -/
theorem eq_assembled_of_privateSlices {f : SetFunction (H⊕J)} (hf : OuterZero f)
    (F : J → SetFunction H) (w : J → ℝ)
    (hparts : ∀ j,privateSlice f j=w j • F j) :
    f=assembled (boundarySlice f) F w := by
  funext A
  rw [function_decomposition hf A]
  change boundarySlice f (hubs A)+(∑ j∈outers A,privateSlice f j (hubs A))=
    boundarySlice f (hubs A)+(∑ j : J,w j • branchLift j (F j)) A
  congr 1
  rw [Finset.sum_apply]
  unfold outers
  rw [sum_filter]
  apply sum_congr rfl
  intro j hj
  rw [hparts j]
  by_cases hja : Sum.inr j∈A <;> simp [branchLift,hja]

/-- Every private spoke kernel in Lemma7.3 is the full line promised by the
paper. The variation is any normalized set function with the actual spoke
zero equations; it is not assumed to have a particular coefficient support. -/
theorem privateSlice_scalar_of_spokeZeros {z : SetFunction H}
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j)) {w : J → ℝ}
    {f : SetFunction (H⊕J)} (hf : TranslationNormalized f)
    (ht : ∀ u v,u≠v → ∀ A,u∉A → v∉A →
      delta (assembled z F w) u v A=0 → delta f u v A=0) (j : J) :
    privateSlice f j=(privateSlice f j univ) • F j := by
  apply zero_cover_kernel_line (hF j)
  refine ⟨privateSlice_empty hf j,?_⟩
  intro a X ha hzero
  rw [privateSlice_cover]
  apply ht (Sum.inl a) (Sum.inr j) (by simp) (hubSet X)
    (by simpa using ha) (notMem_hubSet_outer X j)
  rw [delta_assembled_spoke _ _ _ _ _ _ (notMem_hubSet_outer X j),hubs_hubSet,hzero,mul_zero]

end BooleanModule
end GraphicalZonotopes
