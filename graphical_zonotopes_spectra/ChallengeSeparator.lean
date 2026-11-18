module
public import Mathlib
/-!
# Full positive-response gluing and exact separator capacities

Every boundary/private coordinate, original elemental difference, conditional
minimum, private kernel, positive closing relation, and active-branch count is
literal. No constructor or data definition is a hole. Named supporting theorem
obligations are selected for comparison. The Solution proves them and all four
principal conclusions from the preserved development via a fieldwise separator
partition bridge. The coordinate dictionaries below give the actual values
directly, so no opaque equivalence is supplied as an assumption.
-/
@[expose] public section
noncomputable section
open Set Finset
open scoped BigOperators Pointwise Classical
namespace PalomarGraphicalSeparator
variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev SetFunction (V : Type*) := Finset V → ℝ
def Supermodular (z : SetFunction V) : Prop :=
  ∀ A B, z A + z B ≤ z (A ∪ B) + z (A ∩ B)
def Normalized (z : SetFunction V) : Prop := z ∅ = 0
def TranslationNormalized (z : SetFunction V) : Prop :=
  Normalized z ∧ ∀ v, z {v} = 0
def delta (z : SetFunction V) (u v : V) (S : Finset V) : ℝ :=
  z (insert u (insert v S)) - z (insert u S) - z (insert v S) + z S
def ExtremeSupermodular (z : SetFunction V) : Prop :=
  TranslationNormalized z ∧ Supermodular z ∧ z ≠ 0 ∧
    ∀ f g : SetFunction V,
      TranslationNormalized f → TranslationNormalized g →
      Supermodular f → Supermodular g → f + g = z →
      ∃ a : ℝ, 0 ≤ a ∧ f = a • z
def zeta (y : SetFunction V) (S : Finset V) : ℝ := ∑ C ∈ S.powerset, y C
theorem zeta_add (y z : SetFunction V) : zeta (y+z) = zeta y+zeta z := by
  funext S
  simp [zeta, sum_add_distrib]
theorem zeta_smul (a : ℝ) (y : SetFunction V) : zeta (a • y) = a • zeta y := by
  funext S
  simp [zeta, mul_sum]
def zetaLinear : SetFunction V →ₗ[ℝ] SetFunction V where
  toFun := zeta
  map_add' := zeta_add
  map_smul' := zeta_smul
theorem zeta_injective : Function.Injective (zeta : SetFunction V → SetFunction V) := by sorry
def zetaEquiv : SetFunction V ≃ₗ[ℝ] SetFunction V :=
  LinearEquiv.ofInjectiveEndo zetaLinear zeta_injective
def mobius (z : SetFunction V) : SetFunction V := zetaEquiv.symm z
def cliqueCapacity (s : ℕ) : ℕ := s.choose 2 * 2^(s-2) - (2^s-s-1) + 1
/-- Nonedge elemental differences vanish on the entire subset lattice. -/
def Graphical (G : SimpleGraph V) (z : SetFunction V) : Prop :=
  ∀ u v, u ≠ v → ¬G.Adj u v → ∀ S, u ∉ S → v ∉ S → delta z u v S = 0
/-- Normalized Mobius coefficients supported exactly on graph cliques. -/
def CliqueSupported (G : SimpleGraph V) (y : SetFunction V) : Prop :=
  y ∅ = 0 ∧ (∀ v, y {v} = 0) ∧
    ∀ C u v, u ∈ C → v ∈ C → u ≠ v → ¬G.Adj u v → y C = 0
/-- Every clique coordinate of cardinality at least two, including zero-valued slots. -/
def IsCliqueCoordinate (G : SimpleGraph V) (C : Finset V) : Prop := 2 ≤ C.card ∧ G.IsClique C
abbrev CliqueIndex (G : SimpleGraph V) := {C : Finset V // IsCliqueCoordinate G C}
noncomputable instance cliqueIndexFintype (G : SimpleGraph V) : Fintype (CliqueIndex G) := by
  classical
  exact Subtype.fintype (IsCliqueCoordinate G)
/-- Fill every nonclique coefficient by zero, retaining every zero slot. -/
def coefficientsFromCoordinates (G : SimpleGraph V) (c : CliqueIndex G → ℝ) : SetFunction V := by
  classical
  exact fun C => if h : IsCliqueCoordinate G C then c ⟨C,h⟩ else 0
theorem coefficientFill_add (G : SimpleGraph V) (c d : CliqueIndex G → ℝ) : coefficientsFromCoordinates G (c+d) = coefficientsFromCoordinates G c + coefficientsFromCoordinates G d := by
  funext C
  by_cases hC : IsCliqueCoordinate G C <;> simp [coefficientsFromCoordinates, hC]

theorem coefficientFill_smul (G : SimpleGraph V) (a : ℝ) (c : CliqueIndex G → ℝ) : coefficientsFromCoordinates G (a • c) = a • coefficientsFromCoordinates G c := by
  funext C
  by_cases hC : IsCliqueCoordinate G C <;> simp [coefficientsFromCoordinates, hC]
def coefficientFillLinear (G : SimpleGraph V) :
    (CliqueIndex G → ℝ) →ₗ[ℝ] SetFunction V where
  toFun := coefficientsFromCoordinates G
  map_add' := coefficientFill_add G
  map_smul' := coefficientFill_smul G

/-- The actual normalized graphical function space, before imposing nonnegativity. -/
theorem graphicalSpace_zero (G : SimpleGraph V) : TranslationNormalized (0 : SetFunction V) ∧ Graphical G 0 := by
  refine ⟨⟨rfl, fun _ => rfl⟩, ?_⟩
  intro u v huv hnon S hu hv
  simp [delta]

theorem graphicalSpace_add (G : SimpleGraph V) : ∀ {f g : SetFunction V}, (TranslationNormalized f ∧ Graphical G f) → (TranslationNormalized g ∧ Graphical G g) → TranslationNormalized (f+g) ∧ Graphical G (f+g) := by
  intro f g hf hg
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change f ∅ + g ∅ = 0
    rw [hf.1.1, hg.1.1, add_zero]
  · intro v
    change f {v} + g {v} = 0
    rw [hf.1.2 v, hg.1.2 v, add_zero]
  · intro u v huv hnon S hu hv
    have h : delta (f+g) u v S = delta f u v S + delta g u v S := by
      simp only [delta, Pi.add_apply]; ring
    rw [h, hf.2 u v huv hnon S hu hv, hg.2 u v huv hnon S hu hv, add_zero]

theorem graphicalSpace_smul (G : SimpleGraph V) : ∀ (a : ℝ) {f : SetFunction V}, (TranslationNormalized f ∧ Graphical G f) → TranslationNormalized (a • f) ∧ Graphical G (a • f) := by
  intro a f hf
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change a*f ∅ = 0
    rw [hf.1.1, mul_zero]
  · intro v
    change a*f {v} = 0
    rw [hf.1.2 v, mul_zero]
  · intro u v huv hnon S hu hv
    have h : delta (a • f) u v S = a * delta f u v S := by
      simp only [delta, Pi.smul_apply, smul_eq_mul]; ring
    rw [h, hf.2 u v huv hnon S hu hv, mul_zero]
def graphicalFunctionSpace (G : SimpleGraph V) : Submodule ℝ (SetFunction V) where
  carrier := {z | TranslationNormalized z ∧ Graphical G z}
  zero_mem' := graphicalSpace_zero G
  add_mem' := graphicalSpace_add G
  smul_mem' := graphicalSpace_smul G

/-- The elemental difference as its actual linear functional. -/
theorem delta_add (u v : V) (S : Finset V) (z w : SetFunction V) : delta (z+w) u v S = delta z u v S + delta w u v S := by simp only [delta, Pi.add_apply]; ring

theorem delta_smul (u v : V) (S : Finset V) (a : ℝ) (z : SetFunction V) : delta (a • z) u v S = a * delta z u v S := by simp only [delta, Pi.smul_apply, smul_eq_mul]; ring
def deltaLinear (u v : V) (S : Finset V) : SetFunction V →ₗ[ℝ] ℝ where
  toFun z := delta z u v S
  map_add' := delta_add u v S
  map_smul' := delta_smul u v S

/-- Actual common graph neighbors. -/
def commonNeighbors (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact univ.filter (fun w => G.Adj u w ∧ G.Adj v w)
end PalomarGraphicalSeparator

namespace PalomarGraphicalSeparator.Gluing
variable {B J D : Type*} {K I X : J → Type*}
variable [Fintype B] [Fintype J] [Fintype D]
variable [∀ j, Fintype (K j)] [∀ j, Fintype (I j)] [∀ j, Fintype (X j)]
variable [DecidableEq J]
/-- Boundary coordinates and every private branch coordinate. -/
abbrev Global (J : Type*) (K : J → Type*) (D : Type*) := (D → ℝ) × (∀ j, K j → ℝ)
/-- A literal finite family of boundary, internal, and conditional response rows. -/
structure Data (B J : Type*) (K : J → Type*) (D : Type*) (I X : J → Type*) where
  boundary : (D → ℝ) →ₗ[ℝ] (B → ℝ)
  internal : (j : J) → I j → (K j → ℝ) →ₗ[ℝ] ℝ
  response : (j : J) → B → X j → (K j → ℝ) →ₗ[ℝ] ℝ
/-- Every internal zero equation and every conditional-minimizer difference equation. -/
def Data.PrivateKernel (M : Data B J K D I X) (f : ∀ j, K j → ℝ) (m : J → B → ℝ)
    (j : J) (g : K j → ℝ) : Prop :=
  (∀ i, M.internal j i (f j) = 0 → M.internal j i g = 0) ∧
    ∀ b x y, M.response j b x (f j) = m j b → M.response j b y (f j) = m j b →
      M.response j b x g = M.response j b y g
/-- Literal closing-function cancellation of the sum of branch responses. -/
def Data.Closure (M : Data B J K D I X) (m : J → B → ℝ)
    (z : D → ℝ) (c : J → ℝ) : Prop :=
  ∀ b, M.boundary z b + ∑ j, c j * m j b = 0
/-- Assemble the boundary coordinates with scaled private branch coordinates. -/
def assemble (z : D → ℝ) (c : J → ℝ) (f : ∀ j, K j → ℝ) : Global J K D :=
  (z, fun j => c j • f j)
/-- The real linear response map. -/
theorem response_add (m : J → B → ℝ) (c d : J → ℝ) : (fun b => ∑ j, (c+d) j * m j b) = (fun b => ∑ j, c j * m j b) + (fun b => ∑ j, d j * m j b) := by ext b; simp [add_mul, sum_add_distrib]

theorem response_smul (m : J → B → ℝ) (a : ℝ) (c : J → ℝ) : (fun b => ∑ j, (a • c) j * m j b) = a • (fun b => ∑ j, c j * m j b) := by ext b; simp [mul_assoc, mul_sum]
def responseLinear (m : J → B → ℝ) : (J → ℝ) →ₗ[ℝ] (B → ℝ) where
  toFun c := fun b => ∑ j, c j * m j b
  map_add' := response_add m
  map_smul' := response_smul m

/-- Responses modulo exactly the image of the actual boundary map. -/
def Data.relationLinear (M : Data B J K D I X) (m : J → B → ℝ) :
    (J → ℝ) →ₗ[ℝ] ((B → ℝ) ⧸ LinearMap.range M.boundary) :=
  (LinearMap.range M.boundary).mkQ ∘ₗ responseLinear m
/-- Complete private common kernel as an actual real linear subspace. -/
theorem privateKernel_zero (M : Data B J K D I X) (f : ∀ j, K j → ℝ) (m : J → B → ℝ) (j : J) : M.PrivateKernel f m j 0 := by
  constructor
  · intro i hi
    simp
  · intro b x y hx hy
    simp

theorem privateKernel_add (M : Data B J K D I X) (f : ∀ j, K j → ℝ) (m : J → B → ℝ) (j : J) : ∀ {g h : K j → ℝ}, M.PrivateKernel f m j g → M.PrivateKernel f m j h → M.PrivateKernel f m j (g+h) := by
  intro g h hg hh
  constructor
  · intro i hi
    rw [map_add,hg.1 i hi,hh.1 i hi,add_zero]
  · intro b x y hx hy
    rw [map_add,map_add,hg.2 b x y hx hy,hh.2 b x y hx hy]

theorem privateKernel_smul (M : Data B J K D I X) (f : ∀ j, K j → ℝ) (m : J → B → ℝ) (j : J) : ∀ (a : ℝ) {g : K j → ℝ}, M.PrivateKernel f m j g → M.PrivateKernel f m j (a • g) := by
  intro a g hg
  constructor
  · intro i hi
    rw [map_smul,hg.1 i hi,smul_zero]
  · intro b x y hx hy
    rw [map_smul,map_smul,hg.2 b x y hx hy]
def Data.privateKernelSpace (M : Data B J K D I X)
    (f : ∀ j, K j → ℝ) (m : J → B → ℝ) (j : J) :
    Submodule ℝ (K j → ℝ) where
  carrier := {g | M.PrivateKernel f m j g}
  zero_mem' := privateKernel_zero M f m j
  add_mem' := privateKernel_add M f m j
  smul_mem' := privateKernel_smul M f m j

/-- Genuinely nonzero private branches. -/
abbrev ActiveBranch (f : ∀ j,K j → ℝ) := {j : J // f j≠0}
/-- Canonical finite subtype enumeration, fixed independently of source instances. -/
noncomputable instance activeBranchFintype (f : ∀ j,K j → ℝ) : Fintype (ActiveBranch f) := by
  classical
  exact Subtype.fintype (fun j => f j ≠ 0)
end PalomarGraphicalSeparator.Gluing

namespace PalomarGraphicalSeparator.Polyhedral
variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]
/-- Full common zero space of every inequality that is tight at the specified point. -/
theorem tightKernel_zero (A : I → E →ₗ[ℝ] ℝ) (y : E) : ∀ i, A i y = 0 → A i 0 = 0 := by simp

theorem tightKernel_add (A : I → E →ₗ[ℝ] ℝ) (y : E) : ∀ {u v : E}, (∀ i, A i y = 0 → A i u = 0) → (∀ i, A i y = 0 → A i v = 0) → ∀ i, A i y = 0 → A i (u+v) = 0 := by intro u v hu hv i hi; simp [hu i hi, hv i hi]

theorem tightKernel_smul (A : I → E →ₗ[ℝ] ℝ) (y : E) : ∀ (a : ℝ) {v : E}, (∀ i, A i y = 0 → A i v = 0) → ∀ i, A i y = 0 → A i (a • v) = 0 := by intro a v hv i hi; simp [hv i hi]
def tightKernel (A : I → E →ₗ[ℝ] ℝ) (y : E) : Submodule ℝ E where
  carrier := {v | ∀ i, A i y = 0 → A i v = 0}
  zero_mem' := tightKernel_zero A y
  add_mem' := tightKernel_add A y
  smul_mem' := tightKernel_smul A y

end PalomarGraphicalSeparator.Polyhedral

namespace PalomarGraphicalSeparator.Separator
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
/-- Disjoint coverage of private vertices with no cross-branch edges. -/
structure Partition (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) : Prop where
  boundary_disjoint : ∀ j,Disjoint B (A j)
  private_disjoint : Pairwise (fun j k => Disjoint (A j) (A k))
  cover : ∀ v : V,v∈B ∨ ∃ j,v∈A j
  no_cross_edge : ∀ j k u v,u∈A j → v∈A k → G.Adj u v → j=k
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}
/-- Every clique outside the boundary lies in exactly one private branch. -/
theorem Partition.clique_unique_branch (h : Partition G B A)
    (C : CliqueIndex G) (hC : ¬C.1⊆B) : ∃! j : J,C.1⊆B∪A j := by sorry
abbrev boundaryIndex (G : SimpleGraph V) (B : Finset V) := {C : CliqueIndex G // C.1⊆B}
abbrev privateIndex (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) (j : J) :=
  {C : CliqueIndex G // ¬C.1⊆B ∧ C.1⊆B∪A j}
noncomputable instance boundaryIndexFintype : Fintype (boundaryIndex G B) := by
  classical
  exact Subtype.fintype (fun C : CliqueIndex G => C.1 ⊆ B)
noncomputable instance privateIndexFintype (j : J) : Fintype (privateIndex G B A j) := by
  classical
  exact Subtype.fintype (fun C : CliqueIndex G => ¬C.1 ⊆ B ∧ C.1 ⊆ B ∪ A j)
/-- The unique private branch of an outside-boundary clique. -/
def branchOf (h : Partition G B A) (C : CliqueIndex G) (hC : ¬C.1⊆B) : J :=
  Classical.choose (h.clique_unique_branch C hC)
theorem branchOf_spec (h : Partition G B A) (C : CliqueIndex G) (hC : ¬C.1⊆B) :
    C.1⊆B∪A (branchOf h C hC) := by
  exact (Classical.choose_spec (h.clique_unique_branch C hC)).1
/-- Classify all original coordinates, including all zero slots. -/
def classify (h : Partition G B A) (C : CliqueIndex G) :
    boundaryIndex G B ⊕ (Σ j : J,privateIndex G B A j) := by
  classical
  exact if hC : C.1⊆B then Sum.inl ⟨C,hC⟩ else
    Sum.inr ⟨branchOf h C hC,⟨C,hC,branchOf_spec h C hC⟩⟩
/-- Reassemble coordinates in the exact full clique-index dictionary. -/
def joinCoordinates (h : Partition G B A)
    (x : (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)) :
    CliqueIndex G → ℝ := fun C =>
  match classify h C with
  | Sum.inl D => x.1 D
  | Sum.inr ⟨j,D⟩ => x.2 j D
abbrev Coordinates (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) :=
  (boundaryIndex G B → ℝ) × (∀ j : J, privateIndex G B A j → ℝ)
/-- Literal full coordinate reconstruction, including every zero slot. -/
theorem joinCoordinates_add (h : Partition G B A) (x y : Coordinates G B A) : joinCoordinates h (x+y) = joinCoordinates h x + joinCoordinates h y := by
  funext C
  cases hc : classify h C <;> simp [joinCoordinates, hc]

theorem joinCoordinates_smul (h : Partition G B A) (a : ℝ) (x : Coordinates G B A) : joinCoordinates h (a • x) = a • joinCoordinates h x := by
  funext C
  cases hc : classify h C <;> simp [joinCoordinates, hc]
def joinCoordinatesLinear (h : Partition G B A) :
    Coordinates G B A →ₗ[ℝ] (CliqueIndex G → ℝ) where
  toFun := joinCoordinates h
  map_add' := joinCoordinates_add h
  map_smul' := joinCoordinates_smul h

/-- The original actual set function, computed as the finite subset zeta sum. -/
def globalFunctionMap (h : Partition G B A) : Coordinates G B A →ₗ[ℝ] SetFunction V :=
  zetaLinear.comp ((coefficientFillLinear G).comp (joinCoordinatesLinear h))
/-- Exact membership in the normalized graphical function space. -/
theorem globalFunction_mem (h : Partition G B A) (x : Coordinates G B A) :
    TranslationNormalized (globalFunctionMap h x) ∧ Graphical G (globalFunctionMap h x) := by sorry
/-- The genuine graphical function value; no equivalence is supplied opaquely. -/
def functionValue (h : Partition G B A) (x : Coordinates G B A) : graphicalFunctionSpace G :=
  ⟨globalFunctionMap h x, globalFunction_mem h x⟩
/-- The full inverse dictionary computed by ordinary finite Mobius inversion. -/
def splitCoordinates (z : graphicalFunctionSpace G) : Coordinates G B A :=
  (fun C => mobius z.1 C.1.1, fun _ C => mobius z.1 C.1.1)
/-- Addition preserves the exact zero private blocks. -/
theorem boundaryEmbed_add (z w : boundaryIndex G B → ℝ) :
    ((z+w,0) : Coordinates G B A) = (z,0)+(w,0) := by
  ext <;> simp
/-- Scalar multiplication preserves the exact zero private blocks. -/
theorem boundaryEmbed_smul (a : ℝ) (z : boundaryIndex G B → ℝ) :
    ((a • z,0) : Coordinates G B A) = a • (z,0) := by
  ext <;> simp
/-- Embed the closing function in the boundary block. -/
def boundaryEmbed : (boundaryIndex G B → ℝ) →ₗ[ℝ] Coordinates G B A where
  toFun z := (z,0)
  map_add' := boundaryEmbed_add
  map_smul' := boundaryEmbed_smul
/-- Embed one private branch, retaining all the other zero blocks. -/
theorem privateEmbed_add (j : J) (g k : privateIndex G B A j → ℝ) : ((0, LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j (g+k)) : Coordinates G B A) = (0, LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j g) + (0, LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j k) := by
  apply Prod.ext
  · simp
  · exact (LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j).map_add g k

theorem privateEmbed_smul (j : J) (a : ℝ) (g : privateIndex G B A j → ℝ) : ((0, LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j (a • g)) : Coordinates G B A) = a • (0, LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j g) := by
  ext <;> simp
def privateEmbed (j : J) : (privateIndex G B A j → ℝ) →ₗ[ℝ] Coordinates G B A where
  toFun g := (0,LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j g)
  map_add' := privateEmbed_add j
  map_smul' := privateEmbed_smul j

/-- Original set function for a pure boundary coordinate vector. -/
def boundaryFunctionMap (h : Partition G B A) :
    (boundaryIndex G B → ℝ) →ₗ[ℝ] SetFunction V := (globalFunctionMap h).comp boundaryEmbed
/-- Original set function for a single private branch vector. -/
def privateFunctionMap (h : Partition G B A) (j : J) :
    (privateIndex G B A j → ℝ) →ₗ[ℝ] SetFunction V := (globalFunctionMap h).comp (privateEmbed j)
/-- The graph obtained by deleting exactly the boundary vertices. -/
def outsideGraph (G : SimpleGraph V) (B : Finset V) : SimpleGraph {v : V // v∉B} :=
  G.induce {v : V | v∉B}
/-- The actual vertices of a connected component after boundary deletion. -/
def componentPart (G : SimpleGraph V) (B : Finset V)
    (c : (outsideGraph G B).ConnectedComponent) : Finset V := by
  classical
  exact univ.filter (fun v => ∃ hv : v∉B,
    (outsideGraph G B).connectedComponentMk ⟨v,hv⟩=c)
noncomputable instance componentFintype (G : SimpleGraph V) (B : Finset V) :
    Fintype ((outsideGraph G B).ConnectedComponent) := @Fintype.ofFinite _ (Quot.finite _)
/-- The actual induced components give the canonical separator partition. -/
theorem componentPartition (G : SimpleGraph V) (B : Finset V) :
    Partition G B (componentPart G B) := by sorry
end PalomarGraphicalSeparator.Separator

namespace PalomarGraphicalSeparator
section Ordered
variable {V J : Type*} [Fintype V] [LinearOrder V]
local instance vertexDecidableEq : DecidableEq V := LinearOrder.toDecidableEq
variable [Fintype J] [DecidableEq J]
abbrev OrientedEdge (G : SimpleGraph V) := {e : V × V // e.1< e.2 ∧ G.Adj e.1 e.2}
noncomputable instance orientedEdgeFintype (G : SimpleGraph V) : Fintype (OrientedEdge G) := by
  classical
  exact Subtype.fintype (fun e : V × V => e.1 < e.2 ∧ G.Adj e.1 e.2)
abbrev BoundaryContext (G : SimpleGraph V) :=
  Σ e : OrientedEdge G, ↥(commonNeighbors G e.1.1 e.1.2).powerset
noncomputable instance boundaryContextFintype (G : SimpleGraph V) : Fintype (BoundaryContext G) := by
  classical
  exact Sigma.instFintype
/-- Every actual edge/common-neighbor elemental row, exactly once. -/
theorem boundarySlack_add (G : SimpleGraph V) (z w : graphicalFunctionSpace G) : (fun r : BoundaryContext G => delta (z+w).1 r.1.1.1 r.1.1.2 r.2.1) = (fun r : BoundaryContext G => delta z.1 r.1.1.1 r.1.1.2 r.2.1) + (fun r : BoundaryContext G => delta w.1 r.1.1.1 r.1.1.2 r.2.1) := by
  funext r
  exact (deltaLinear r.1.1.1 r.1.1.2 r.2.1).map_add z.1 w.1

theorem boundarySlack_smul (G : SimpleGraph V) (a : ℝ) (z : graphicalFunctionSpace G) : (fun r : BoundaryContext G => delta (a • z).1 r.1.1.1 r.1.1.2 r.2.1) = a • (fun r : BoundaryContext G => delta z.1 r.1.1.1 r.1.1.2 r.2.1) := by
  funext r
  exact (deltaLinear r.1.1.1 r.1.1.2 r.2.1).map_smul a z.1
def boundarySlackMap (G : SimpleGraph V) :
    graphicalFunctionSpace G →ₗ[ℝ] (BoundaryContext G → ℝ) where
  toFun z r := delta z.1 r.1.1.1 r.1.1.2 r.2.1
  map_add' := boundarySlack_add G
  map_smul' := boundarySlack_smul G

/-- The literal linear inequality row on the normalized graphical space. -/
def contextRow (G : SimpleGraph V) (r : BoundaryContext G) : graphicalFunctionSpace G →ₗ[ℝ] ℝ where
  toFun z := boundarySlackMap G z r
  map_add' z w := congrFun ((boundarySlackMap G).map_add z w) r
  map_smul' a z := congrFun ((boundarySlackMap G).map_smul a z) r
namespace Separator
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}
abbrev BoundaryRow (G : SimpleGraph V) (B : Finset V) :=
  {r : BoundaryContext G // r.1.1.1∈B ∧ r.1.1.2∈B ∧ r.2.1⊆B}
abbrev InternalRow (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) (j : J) :=
  {r : BoundaryContext G // (r.1.1.1∈A j ∨ r.1.1.2∈A j) ∧ r.2.1⊆B∪A j}
abbrev BranchChoice (A : J → Finset V) (j : J) := {S : Finset V // S⊆A j}
noncomputable instance boundaryRowFintype : Fintype (BoundaryRow G B) := by
  classical
  exact Subtype.fintype (fun r : BoundaryContext G => r.1.1.1 ∈ B ∧ r.1.1.2 ∈ B ∧ r.2.1 ⊆ B)
noncomputable instance internalRowFintype (j : J) : Fintype (InternalRow G B A j) := by
  classical
  exact Subtype.fintype (fun r : BoundaryContext G => (r.1.1.1 ∈ A j ∨ r.1.1.2 ∈ A j) ∧ r.2.1 ⊆ B ∪ A j)
noncomputable instance branchChoiceFintype (j : J) : Fintype (BranchChoice A j) := by
  classical
  exact Subtype.fintype (fun S : Finset V => S ⊆ A j)
noncomputable instance branchChoiceInhabited (j : J) : Inhabited (BranchChoice A j) := ⟨⟨∅,empty_subset _⟩⟩
/-- The exact row model obtained from all original set-function differences. -/
def rowData (h : Partition G B A) :
    Gluing.Data (BoundaryRow G B) J (privateIndex G B A) (boundaryIndex G B)
      (InternalRow G B A) (BranchChoice A) where
  boundary := LinearMap.pi (fun b =>
    (deltaLinear b.1.1.1.1 b.1.1.1.2 b.1.2.1).comp (boundaryFunctionMap h))
  internal j r := (deltaLinear r.1.1.1.1 r.1.1.1.2 r.1.2.1).comp (privateFunctionMap h j)
  response j b X := (deltaLinear b.1.1.1.1 b.1.1.1.2 (b.1.2.1∪X.1)).comp (privateFunctionMap h j)
/-- Actual conditional minimum over every private subset, including all zero slots. -/
def conditionalMin (h : Partition G B A) (f : ∀ j,privateIndex G B A j → ℝ)
    (j : J) (b : BoundaryRow G B) : ℝ :=
  univ.inf' univ_nonempty (fun X : BranchChoice A j => (rowData h).response j b X (f j))
abbrev BoundaryEdge (G : SimpleGraph V) (B : Finset V) :=
  {e : OrientedEdge G // e.1.1∈B ∧ e.1.2∈B}
noncomputable instance boundaryEdgeFintype : Fintype (BoundaryEdge G B) := by
  classical
  exact Subtype.fintype (fun e : OrientedEdge G => e.1.1 ∈ B ∧ e.1.2 ∈ B)
/-- All original boundary clique coordinates, without dropping zero slots. -/
def boundaryCliques (G : SimpleGraph V) (B : Finset V) : Finset (Finset V) := by
  classical
  exact B.powerset.filter (IsCliqueCoordinate G)
/-- Assembly of the closing function and all scaled private coordinates. -/
def gluedCoordinates (f : ∀ j,privateIndex G B A j → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) : Coordinates G B A := Gluing.assemble z lam f
/-- A private branch with an arbitrary actual boundary lift. -/
def branchWithLift (h : Partition G B A) (j : J)
    (f : privateIndex G B A j → ℝ) (l : boundaryIndex G B → ℝ) : SetFunction V :=
  boundaryFunctionMap h l+privateFunctionMap h j f
def PositiveResponseGluingConclusion (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) : Prop :=
  let p := globalFunctionMap h (gluedCoordinates f z lam)
  let R := LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))
  TranslationNormalized p ∧ Graphical G p ∧ Supermodular p ∧
    Module.finrank ℝ
      (Polyhedral.tightKernel (contextRow G)
        (functionValue h (gluedCoordinates f z lam))) = Module.finrank ℝ R ∧
    (ExtremeSupermodular p ↔ Module.finrank ℝ R = 1) ∧
    (ExtremeSupermodular p →
      R = Submodule.span ℝ {lam} ∧
      Fintype.card J ≤
        (∑ e : BoundaryEdge G B,
          2^(commonNeighbors G e.1.1.1 e.1.1.2 ∩ B).card) -
          (boundaryCliques G B).card + 1)


/-- The literal corresponding assertion of Theorem 5.4. -/
theorem assembled_boundary_lift_transfer (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (l : J → boundaryIndex G B → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) :
    boundaryFunctionMap h (z - ∑ j, lam j • l j) +
      ∑ j, lam j • branchWithLift h j (f j) (l j) =
      globalFunctionMap h (Gluing.assemble z lam f) := by sorry

/-- The literal corresponding assertion of Theorem 5.4. -/
theorem positive_response_gluing (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ)
    (hlam : ∀ j, 0 < lam j) (hf : ∀ j, f j ≠ 0)
    (hi : ∀ j r, 0 ≤ (rowData h).internal j r (f j))
    (hprivate : ∀ j, (rowData h).privateKernelSpace f (conditionalMin h f) j =
      Submodule.span ℝ {f j})
    (hclose : (rowData h).Closure (conditionalMin h f) z lam) :
    PositiveResponseGluingConclusion h f z lam := by sorry

end Separator
end Ordered
namespace Separator
/-- An internal coordinate order on every finite vertex type. -/
def finiteVertexOrder (V : Type*) [Fintype V] : LinearOrder V :=
  LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective

/-- The complete corresponding finite-graph assertion with every original hypothesis. -/
theorem induced_separator_capacity_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := finiteVertexOrder V;
    ∀ (G : SimpleGraph V) (B : Finset V) (z : graphicalFunctionSpace G),
      ExtremeSupermodular z.1 →
      Fintype.card (Gluing.ActiveBranch
        ((splitCoordinates (G := G) (B := B) (A := componentPart G B) z).2)) ≤
        (∑ e : BoundaryEdge G B,
          2^(commonNeighbors G e.1.1.1 e.1.1.2 ∩ B).card) -
          (boundaryCliques G B).card + 1 := by sorry

/-- The complete corresponding finite-graph assertion with every original hypothesis. -/
theorem clique_separator_capacity_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := finiteVertexOrder V;
    ∀ (G : SimpleGraph V) (B : Finset V),G.IsClique B → 2≤ B.card →
      ∀ z : graphicalFunctionSpace G,ExtremeSupermodular z.1 →
        Fintype.card (Gluing.ActiveBranch
          ((splitCoordinates (G := G) (B := B) (A := componentPart G B) z).2))≤ cliqueCapacity B.card := by sorry

/-- The complete corresponding finite-graph assertion with every original hypothesis. -/
theorem positive_response_gluing_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := finiteVertexOrder V;
    ∀ {J : Type*} [Fintype J] [DecidableEq J]
      {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}
      (h : Partition G B A)
      (f : ∀ j, privateIndex G B A j → ℝ)
      (z : boundaryIndex G B → ℝ) (lam : J → ℝ),
      (∀ j, 0 < lam j) → (∀ j, f j ≠ 0) →
      (∀ j r, 0 ≤ (rowData h).internal j r (f j)) →
      (∀ j, (rowData h).privateKernelSpace f (conditionalMin h f) j =
        Submodule.span ℝ {f j}) →
      (rowData h).Closure (conditionalMin h f) z lam →
      PositiveResponseGluingConclusion h f z lam := by sorry

end Separator
variable {V : Type*} [Fintype V] [DecidableEq V]

end PalomarGraphicalSeparator
