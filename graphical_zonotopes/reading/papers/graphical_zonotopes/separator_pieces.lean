module

public import Papers.GraphicalZonotopes.SeparatorCoordinates
public import Papers.GraphicalZonotopes.CoefficientSupport
public import Mathlib.LinearAlgebra.Pi

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

abbrev Coordinates (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) :=
  (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)

def boundaryEmbed : (boundaryIndex G B → ℝ) →ₗ[ℝ] Coordinates G B A where
  toFun z := (z,0)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def privateEmbed (j : J) : (privateIndex G B A j → ℝ) →ₗ[ℝ] Coordinates G B A where
  toFun g := (0,LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j g)
  map_add' f g := by
    apply Prod.ext
    · simp
    · exact map_add (LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j) f g
  map_smul' a f := by
    apply Prod.ext
    · simp
    · exact map_smul (LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j) a f

def globalFunctionMap (h : Partition G B A) : Coordinates G B A →ₗ[ℝ] SetFunction V :=
  (graphicalFunctionSpace G).subtype.comp (functionEquiv h).toLinearMap

def boundaryFunctionMap (h : Partition G B A) :
    (boundaryIndex G B → ℝ) →ₗ[ℝ] SetFunction V :=
  (globalFunctionMap h).comp boundaryEmbed

def privateFunctionMap (h : Partition G B A) (j : J) :
    (privateIndex G B A j → ℝ) →ₗ[ℝ] SetFunction V :=
  (globalFunctionMap h).comp (privateEmbed j)

theorem coordinates_decompose (x : Coordinates G B A) :
    x=boundaryEmbed x.1+∑ j : J,privateEmbed j (x.2 j) := by
  classical
  apply Prod.ext
  · simp [boundaryEmbed,privateEmbed, Prod.fst_sum, Prod.snd_sum]
  · funext j C
    simp [boundaryEmbed,privateEmbed,LinearMap.single_apply,Finset.sum_apply, Prod.fst_sum, Prod.snd_sum]

/-- The full original function is the sum of its boundary function and every
private branch function, with no discarded Möbius coordinates. -/
theorem function_decompose (h : Partition G B A) (x : Coordinates G B A) :
    globalFunctionMap h x=boundaryFunctionMap h x.1+
      ∑ j : J,privateFunctionMap h j (x.2 j) := by
  have he := congrArg (globalFunctionMap h) (coordinates_decompose x)
  simpa only [map_add,map_sum,boundaryFunctionMap,privateFunctionMap,
    LinearMap.comp_apply] using he

@[simp] theorem mobius_globalFunctionMap (h : Partition G B A) (x : Coordinates G B A) :
    mobius (globalFunctionMap h x)=coefficientsFromCoordinates G (joinCoordinates h x) := by
  change mobius (zeta (coefficientsFromCoordinates G (joinCoordinates h x)))=_
  exact mobius_zeta _

theorem boundaryFunction_supported (h : Partition G B A) (z : boundaryIndex G B → ℝ) :
    CoefficientSupportedOn B (mobius (boundaryFunctionMap h z)) := by
  classical
  intro C hCB
  change mobius (globalFunctionMap h (z,0)) C=0
  rw [mobius_globalFunctionMap]
  by_cases hcl : IsCliqueCoordinate G C
  · simp [coefficientsFromCoordinates,hcl,joinCoordinates,classify,hCB]
  · simp [coefficientsFromCoordinates,hcl]

theorem privateFunction_supported (h : Partition G B A) (j : J)
    (g : privateIndex G B A j → ℝ) :
    CoefficientSupportedOn (B∪A j) (mobius (privateFunctionMap h j g)) := by
  classical
  intro C hCA
  change mobius (globalFunctionMap h
    (0,LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j g)) C=0
  rw [mobius_globalFunctionMap]
  by_cases hcl : IsCliqueCoordinate G C
  · have hCB : ¬C⊆B := fun hc => hCA (hc.trans subset_union_left)
    have hbranch : branchOf h ⟨C,hcl⟩ hCB≠j := by
      intro he
      have hc := branchOf_spec h ⟨C,hcl⟩ hCB
      rw [he] at hc
      exact hCA hc
    simp [coefficientsFromCoordinates,hcl,joinCoordinates,classify,hCB,
      LinearMap.single_apply,Pi.single_eq_of_ne hbranch]
  · simp [coefficientsFromCoordinates,hcl]

theorem privateFunction_boundary_coefficients_zero (h : Partition G B A) (j : J)
    (g : privateIndex G B A j → ℝ) {C : Finset V} (hCB : C⊆B) :
    mobius (privateFunctionMap h j g) C=0 := by
  classical
  change mobius (globalFunctionMap h
    (0,LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j g)) C=0
  rw [mobius_globalFunctionMap]
  by_cases hcl : IsCliqueCoordinate G C <;>
    simp [coefficientsFromCoordinates,hcl,joinCoordinates,classify,hCB]

/-- On a private edge, the boundary contribution and every other branch
contribution vanish for all conditioning sets. -/
theorem delta_private_edge_decompose (h : Partition G B A) (x : Coordinates G B A)
    (j : J) {u v : V} (huA : u∈A j) (huv : u≠v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (globalFunctionMap h x) u v S=
      delta (privateFunctionMap h j (x.2 j)) u v S := by
  classical
  have huB : u∉B := fun hB => Finset.disjoint_left.mp (h.boundary_disjoint j) hB huA
  rw [function_decompose,delta_add,delta_sum]
  rw [delta_zero_of_outside_mobius_support (boundaryFunction_supported h x.1) huv huB hu hv,
    zero_add]
  apply sum_eq_single j
  · intro k hk hkj
    have huBA : u∉B∪A k := by
      intro hm
      rcases mem_union.mp hm with hB | hkA
      · exact huB hB
      · exact Finset.disjoint_left.mp (h.private_disjoint hkj) hkA huA
    exact delta_zero_of_outside_mobius_support (privateFunction_supported h k (x.2 k))
      huv huBA hu hv
  · simp

/-- Every private response depends only on its actual branch conditioning
bits, as required by the separator row model. -/
theorem delta_private_inter (h : Partition G B A) (j : J)
    (g : privateIndex G B A j → ℝ) {u v : V} (huv : u≠v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (privateFunctionMap h j g) u v S=
      delta (privateFunctionMap h j g) u v (S∩(B∪A j)) :=
  delta_inter_mobius_support (privateFunction_supported h j g) huv hu hv

end Separator
end GraphicalZonotopes
