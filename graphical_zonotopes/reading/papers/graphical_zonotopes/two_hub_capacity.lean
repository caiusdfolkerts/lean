module

public import Papers.GraphicalZonotopes.TwoHubGraph
public import Papers.GraphicalZonotopes.SeparatorPaperStatements
public import Papers.GraphicalZonotopes.WeakSummandReduction
public import Mathlib.Order.Sum.Order

/-! # The separator upper bound for the two-singleton family

The boundary is the two distinguished vertices together with the first
independent part.  We count its rows exactly and exhibit all the boundary
cliques needed for the sharp capacity estimate.  No assumption is made that
the private coefficients of an extreme summand are nonzero.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
noncomputable section
namespace GraphicalZonotopes.TwoHub.Capacity
open Finset
open scoped BigOperators Classical

abbrev Vertex (p b : ℕ) := (Bool ⊕ Fin p) ⊕ Fin b

local instance vertexOrder (p b : ℕ) : LinearOrder (Vertex p b) :=
  inferInstanceAs (LinearOrder ((Bool ⊕ₗ Fin p) ⊕ₗ Fin b))

local instance vertexLT (p b : ℕ) : LT (Vertex p b) :=
  (vertexOrder p b).toLT

local instance vertexDecidableEq (p b : ℕ) : DecidableEq (Vertex p b) :=
  (vertexOrder p b).toDecidableEq

abbrev G (p b : ℕ) := TwoHub.graph (I := Fin p) (J := Fin b)
def anchor (p b : ℕ) (t : Bool) : Vertex p b := .inl (.inl t)
def a (p b : ℕ) : Vertex p b := anchor p b false
def z (p b : ℕ) : Vertex p b := anchor p b true
def u (p b : ℕ) (i : Fin p) : Vertex p b := .inl (.inr i)
def boundary (p b : ℕ) : Finset (Vertex p b) :=
  univ.image (Sum.inl : Bool ⊕ Fin p → Vertex p b)
def privatePart (p b : ℕ) (j : Fin b) : Finset (Vertex p b) := {Sum.inr j}

@[simp] theorem boundary_card (p b : ℕ) : (boundary p b).card = p+2 := by
  rw [boundary,card_image_of_injective _ Sum.inl_injective]
  simp [Nat.add_comm]

@[simp] theorem mem_boundary_inl (p b : ℕ) (x : Bool ⊕ Fin p) :
    Sum.inl x ∈ boundary p b := by simp [boundary]

@[simp] theorem not_mem_boundary_inr (p b : ℕ) (j : Fin b) :
    Sum.inr j ∉ boundary p b := by simp [boundary]

theorem boundary_order (p b : ℕ) (x y : Bool ⊕ Fin p) :
    (Sum.inl x : Vertex p b) < Sum.inl y ↔
      (toLex x : Bool ⊕ₗ Fin p) < toLex y := Sum.lex_inl_inl

theorem partition (p b : ℕ) :
    Separator.Partition (G p b) (boundary p b) (privatePart p b) where
  boundary_disjoint j := by
    apply disjoint_left.mpr
    intro x hx hp
    have he : x=Sum.inr j := mem_singleton.mp hp
    subst x
    exact not_mem_boundary_inr p b j hx
  private_disjoint := by
    intro i j hij
    exact disjoint_singleton.mpr (fun he => hij (Sum.inr_injective he))
  cover x := by
    cases x with
    | inl x => exact Or.inl (mem_boundary_inl p b x)
    | inr j => exact Or.inr ⟨j,mem_singleton_self _⟩
  no_cross_edge := by
    intro i j x y hx hy hxy
    have hx' : x=Sum.inr i := mem_singleton.mp hx
    have hy' : y=Sum.inr j := mem_singleton.mp hy
    subst x
    subst y
    exact False.elim (hxy rfl)

abbrev EdgeCode (p : ℕ) := Unit ⊕ (Bool × Fin p)

def edgePair (p b : ℕ) : EdgeCode p → Vertex p b × Vertex p b
  | .inl _ => (a p b,z p b)
  | .inr (t,i) => (anchor p b t,u p b i)

theorem edgePair_valid (p b : ℕ) (c : EdgeCode p) :
    (edgePair p b c).1 < (edgePair p b c).2 ∧
      (G p b).Adj (edgePair p b c).1 (edgePair p b c).2 ∧
      (edgePair p b c).1 ∈ boundary p b ∧
      (edgePair p b c).2 ∈ boundary p b := by
  rcases c with c | ⟨t,i⟩
  · simp [edgePair,a,z,anchor,boundary_order,Sum.Lex.toLex_lt_toLex,
      G,TwoHub.graph,TwoHub.color]
  · cases t <;> simp [edgePair,anchor,u,boundary_order,
      Sum.Lex.toLex_lt_toLex,G,TwoHub.graph,TwoHub.color]

def boundaryEdgeOfCode (p b : ℕ) (c : EdgeCode p) :
    Separator.BoundaryEdge (G p b) (boundary p b) :=
  ⟨⟨edgePair p b c,(edgePair_valid p b c).1,(edgePair_valid p b c).2.1⟩,
    (edgePair_valid p b c).2.2⟩

theorem edgePair_injective (p b : ℕ) : Function.Injective (edgePair p b) := by
  intro c d h
  rcases c with c | ⟨t,i⟩ <;> rcases d with d | ⟨s,j⟩
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · simp [edgePair,a,z,anchor,u] at h
  · simp [edgePair,a,z,anchor,u] at h
  · simpa [edgePair,anchor,u] using h

theorem boundaryEdgeOfCode_bijective (p b : ℕ) :
    Function.Bijective (boundaryEdgeOfCode p b) := by
  constructor
  · intro c d h
    apply edgePair_injective p b
    exact congrArg (fun e : Separator.BoundaryEdge (G p b) (boundary p b) => e.1.1) h
  · rintro ⟨⟨⟨x,y⟩,hlt,hadj⟩,hx,hy⟩
    obtain ⟨x,_,rfl⟩ := mem_image.mp hx
    obtain ⟨y,_,rfl⟩ := mem_image.mp hy
    rw [boundary_order] at hlt
    rcases x with t | i <;> rcases y with s | j
    · cases t <;> cases s
      all_goals try simp [Sum.Lex.toLex_lt_toLex,Bool.lt_iff] at hlt
      refine ⟨.inl (),?_⟩
      rfl
    · refine ⟨.inr (t,j),?_⟩
      rfl
    · simp [Sum.Lex.toLex_lt_toLex] at hlt
    · exact False.elim (hadj rfl)

def boundaryEdgeEquiv (p b : ℕ) :
    EdgeCode p ≃ Separator.BoundaryEdge (G p b) (boundary p b) :=
  Equiv.ofBijective (boundaryEdgeOfCode p b) (boundaryEdgeOfCode_bijective p b)

theorem common_boundary_az (p b : ℕ) :
    commonNeighbors (G p b) (a p b) (z p b) ∩ boundary p b =
      univ.image (u p b) := by
  ext x
  rcases x with (t | i) | j
  · cases t <;> simp [mem_commonNeighbors,G,TwoHub.graph,TwoHub.color,a,z,anchor,u]
  · simp [mem_commonNeighbors,G,TwoHub.graph,TwoHub.color,a,z,anchor,u]
  · simp [u]

theorem common_boundary_anchor (p b : ℕ) (t : Bool) (i : Fin p) :
    commonNeighbors (G p b) (anchor p b t) (u p b i) ∩ boundary p b =
      {anchor p b (!t)} := by
  ext x
  rcases x with (s | j) | j
  · cases t <;> cases s <;>
      simp [mem_commonNeighbors,G,TwoHub.graph,TwoHub.color,anchor,u]
  · cases t <;> simp [mem_commonNeighbors,G,TwoHub.graph,TwoHub.color,anchor,u]
  · simp [anchor]

theorem u_injective (p b : ℕ) : Function.Injective (u p b) := by
  intro i j h
  exact Sum.inr_injective (Sum.inl_injective h)

/-- The boundary has exactly `2^p + 4*p` elementary rows. -/
theorem boundary_rows_count (p b : ℕ) :
    (∑ e : Separator.BoundaryEdge (G p b) (boundary p b),
      2^(commonNeighbors (G p b) e.1.1.1 e.1.1.2 ∩ boundary p b).card) =
        2^p+4*p := by
  have he := Fintype.sum_equiv (boundaryEdgeEquiv p b)
    (fun c : EdgeCode p =>
      (2 : ℕ)^(commonNeighbors (G p b) (edgePair p b c).1
        (edgePair p b c).2 ∩ boundary p b).card)
    (fun e : Separator.BoundaryEdge (G p b) (boundary p b) =>
      (2 : ℕ)^(commonNeighbors (G p b) e.1.1.1 e.1.1.2 ∩ boundary p b).card)
    (fun _ => rfl)
  rw [←he]
  simp [EdgeCode,Fintype.sum_sum_type,edgePair,common_boundary_az,
    common_boundary_anchor,card_image_of_injective _ (u_injective p b),
    Fintype.sum_prod_type,Fintype.sum_bool,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] <;> omega

abbrev CliqueCode (p : ℕ) := Unit ⊕ (Fin 3 × Fin p)

def cliqueSet (p b : ℕ) : CliqueCode p → Finset (Vertex p b)
  | .inl _ => {a p b,z p b}
  | .inr (t,i) => if t=0 then {a p b,u p b i}
      else if t=1 then {z p b,u p b i} else {a p b,z p b,u p b i}

theorem u_mem_cliqueSet (p b : ℕ) (t : Fin 3) (i : Fin p) :
    u p b i ∈ cliqueSet p b (.inr (t,i)) := by
  fin_cases t <;> simp [cliqueSet]

theorem u_mem_cliqueSet_iff (p b : ℕ) (t : Fin 3) (i j : Fin p) :
    u p b i ∈ cliqueSet p b (.inr (t,j)) ↔ i=j := by
  fin_cases t <;> simp [cliqueSet,a,z,anchor,u]

theorem cliqueSet_injective (p b : ℕ) : Function.Injective (cliqueSet p b) := by
  intro c d h
  rcases c with c | ⟨t,i⟩ <;> rcases d with d | ⟨s,j⟩
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · have hj := u_mem_cliqueSet p b s j
    rw [←h] at hj
    simp [cliqueSet,a,z,anchor,u] at hj
  · have hi := u_mem_cliqueSet p b t i
    rw [h] at hi
    simp [cliqueSet,a,z,anchor,u] at hi
  · have hi := u_mem_cliqueSet p b t i
    rw [h,u_mem_cliqueSet_iff] at hi
    subst j
    have ha := congrArg (fun C : Finset (Vertex p b) => a p b ∈ C) h
    have hz := congrArg (fun C : Finset (Vertex p b) => z p b ∈ C) h
    fin_cases t <;> fin_cases s <;> try rfl
    all_goals simp [cliqueSet,a,z,anchor,u] at ha hz

theorem cliqueSet_mem (p b : ℕ) (c : CliqueCode p) :
    cliqueSet p b c ∈ Separator.boundaryCliques (G p b) (boundary p b) := by
  rcases c with c | ⟨t,i⟩
  · simp [Separator.boundaryCliques,cliqueSet,IsCliqueCoordinate,
      SimpleGraph.IsClique,Set.Pairwise,Finset.subset_iff,a,z,anchor,
      G,TwoHub.graph,TwoHub.color]
  · fin_cases t <;>
      simp [Separator.boundaryCliques,cliqueSet,IsCliqueCoordinate,
        SimpleGraph.IsClique,Set.Pairwise,Finset.subset_iff,a,z,anchor,u,
        G,TwoHub.graph,TwoHub.color]

theorem boundary_cliques_lower (p b : ℕ) :
    1+3*p ≤ (Separator.boundaryCliques (G p b) (boundary p b)).card := by
  have h := Fintype.card_le_of_injective
    (fun c : CliqueCode p =>
      (⟨cliqueSet p b c,cliqueSet_mem p b c⟩ :
        ↥(Separator.boundaryCliques (G p b) (boundary p b))))
    (fun c d h => cliqueSet_injective p b (congrArg Subtype.val h))
  simpa only [CliqueCode,Fintype.card_sum,Fintype.card_unit,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_coe] using h

/-- The exact upper capacity bound, without nonzero-branch hypotheses. -/
theorem active_capacity (p b : ℕ) (f : graphicalFunctionSpace (G p b))
    (hf : ExtremeSupermodular f.1) :
    Fintype.card (Gluing.ActiveBranch
      (((Separator.functionEquiv (partition p b)).symm f).2)) ≤ 2^p+p := by
  have h := Separator.separator_capacity_for_function (partition p b) f hf
  rw [boundary_rows_count] at h
  have hc := boundary_cliques_lower p b
  have hp : 0 < (2 : ℕ)^p := pow_pos (by decide) _
  omega

theorem extreme_dimension_bound (p b : ℕ) (f : graphicalFunctionSpace (G p b))
    (hf : ExtremeSupermodular f.1) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope f.1)) ≤ 2^p+2*p+1 := by
  have h := Separator.finrank_le_boundary_add_active (partition p b)
    (fun j => by simp [privatePart]) f hf.2.1
  rw [boundary_card] at h
  have hc := active_capacity p b f hf
  omega

theorem actual_summand_dimension_bound (p b : ℕ)
    {Q : Set (Vertex p b → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (G p b))) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ min (p+b+1) (2^p+2*p+1) := by
  apply le_min
  · have h := weak_summand_dimension_le hQ hi hw
    simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] at h
    omega
  · obtain ⟨f,hf,hzero|hext,hd⟩ := weak_summand_extreme_or_zero hQ hi hw
    · rw [hd,hzero,basePolytope_zero,vectorSpan_singleton,finrank_bot]
      exact Nat.zero_le _
    · rw [hd]
      exact extreme_dimension_bound p b f hext

theorem maximum_dimension_upper (p b : ℕ) :
    maximumIndecomposableDimension (G p b) ≤ min (p+b+1) (2^p+2*p+1) := by
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  rw [←hd]
  exact actual_summand_dimension_bound p b hQ hi hw

end GraphicalZonotopes.TwoHub.Capacity
