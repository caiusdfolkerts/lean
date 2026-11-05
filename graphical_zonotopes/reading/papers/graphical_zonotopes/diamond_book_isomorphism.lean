module

public import Papers.GraphicalZonotopes.DiamondBookGraph
public import Papers.GraphicalZonotopes.GraphIsomorphismDimension
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open scoped BigOperators

abbrev MultipartiteVertex (k : ℕ) := Σ i : Fin 4,Fin (![1,1,2,k] i)

/-- The literal coordinate numbering: singleton parts at0,1; the two-element
part at2,3; and the last part at4 throughk+3. -/
def sigmaToVertex (k : ℕ) (x : MultipartiteVertex k) : Vertex k :=
  ⟨if x.1.val=0 then 0 else if x.1.val=1 then 1 else
    if x.1.val=2 then x.2.val+2 else x.2.val+4,by
    rcases x with ⟨i,j⟩
    have hj := j.isLt
    fin_cases i <;> norm_num at hj ⊢ <;> omega⟩

@[simp] theorem part_sigmaToVertex (k : ℕ) (x : MultipartiteVertex k) :
    part k (sigmaToVertex k x)=x.1 := by
  rcases x with ⟨i,j⟩
  have hj := j.isLt
  fin_cases i
  · rfl
  · rfl
  · have hj' : j.val<2 := by simpa using hj
    have h0 : j.val+2≠0 := by omega
    have h1 : j.val+2≠1 := by omega
    have h4 : j.val+2<4 := by omega
    simp [part,sigmaToVertex,h0,h1,h4]
  · have h0 : j.val+4≠0 := by omega
    have h1 : j.val+4≠1 := by omega
    have h4 : ¬j.val+4<4 := by omega
    simp [part,sigmaToVertex,h0,h1,h4]

theorem sigmaToVertex_injective (k : ℕ) : Function.Injective (sigmaToVertex k) := by
  intro x y he
  have hi := congrArg (part k) he
  rw [part_sigmaToVertex,part_sigmaToVertex] at hi
  rcases x with ⟨i,j⟩
  rcases y with ⟨l,m⟩
  change i=l at hi
  subst l
  apply congrArg (Sigma.mk i)
  apply Fin.ext
  have hj := j.isLt
  have hm := m.isLt
  have hv := congrArg Fin.val he
  fin_cases i <;> norm_num [sigmaToVertex] at hj hm hv ⊢ <;> omega

def sigmaEquiv (k : ℕ) : MultipartiteVertex k ≃ Vertex k :=
  Equiv.ofBijective (sigmaToVertex k)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨sigmaToVertex_injective k,by
        simp [MultipartiteVertex,Vertex,Fintype.card_sigma,Fin.sum_univ_succ,
          Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]⟩)

def sigmaGraphIso (k : ℕ) : twoSingletonGraph 2 k ≃g graph k where
  toEquiv := sigmaEquiv k
  map_rel_iff' := by
    intro x y
    change (part k (sigmaToVertex k x)≠part k (sigmaToVertex k y)) ↔ x.1≠y.1
    rw [part_sigmaToVertex,part_sigmaToVertex]

/-- The model used for the explicit certificate is exactly the paper's
graph, under an actual bijection of all coordinates for everyk. -/
def graphIso (k : ℕ) : graph k ≃g twoSingletonGraph 2 k := (sigmaGraphIso k).symm

theorem maximum_dimension_model_eq (k : ℕ) :
    maximumIndecomposableDimension (graph k)=
      maximumIndecomposableDimension (twoSingletonGraph 2 k) :=
  maximumIndecomposableDimension_iso (graphIso k)

end GraphicalZonotopes.DiamondBook
