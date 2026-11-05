import cubical.rigidity_linear
import cubical.generic_rigidity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Prod

/-!
# Edge counts from genuine infinitesimal rigidity

The edge derivative map has one coordinate per unoriented graph edge.
The space of infinitesimal rotations injects into the strictly upper
triangular coefficients of an orthonormal basis. Rank-nullity therefore
gives the usual rigidity lower bound on edges, with the correct constant.
-/

namespace Cubical.Rigidity

open Module
open scoped InnerProductSpace

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strictly ordered pairs of basis indices parametrize the independent
coefficients of a skew-adjoint operator. -/
abbrev UpperPair (k : ℕ) := {ij : Fin k × Fin k // ij.1 < ij.2}

/-- Read the upper triangular coefficients of a skew-adjoint operator. -/
noncomputable def skewCoordinates [FiniteDimensional ℝ E] :
    skewSubmodule (E := E) →ₗ[ℝ] (UpperPair (finrank ℝ E) → ℝ) where
  toFun A ij := ⟪stdOrthonormalBasis ℝ E ij.val.1,
    A.val (stdOrthonormalBasis ℝ E ij.val.2)⟫_ℝ
  map_add' A B := by funext ij; simp [inner_add_right]
  map_smul' c A := by funext ij; simp [real_inner_smul_right]

/-- Skew-adjointness determines every matrix coefficient from those
strictly above the diagonal. -/
theorem skewCoordinates_injective [FiniteDimensional ℝ E] :
    Function.Injective (skewCoordinates (E := E)) := by
  intro A B h
  apply Subtype.ext
  let b := stdOrthonormalBasis ℝ E
  apply b.toBasis.ext
  intro j
  apply b.repr.injective
  ext i
  simp only [b.repr_apply_apply]
  change ⟪b i, A.val (b j)⟫_ℝ = ⟪b i, B.val (b j)⟫_ℝ
  rcases lt_trichotomy i j with hij | hij | hji
  · exact congrFun h ⟨(i, j), hij⟩
  · subst j
    rw [A.property.inner_self, B.property.inner_self]
  · have hji' : ⟪b j, A.val (b i)⟫_ℝ = ⟪b j, B.val (b i)⟫_ℝ :=
      congrFun h ⟨(j, i), hji⟩
    have hA := A.property (b j) (b i)
    have hB := B.property (b j) (b i)
    have hcA := real_inner_comm (A.val (b j)) (b i)
    have hcB := real_inner_comm (B.val (b j)) (b i)
    linarith

/-- The dimension of the infinitesimal rotations is at most `k choose 2`. -/
theorem finrank_skewSubmodule_le [FiniteDimensional ℝ E] :
    finrank ℝ (skewSubmodule (E := E)) ≤ (finrank ℝ E).choose 2 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := skewCoordinates (E := E)) skewCoordinates_injective
  rw [Module.finrank_pi] at h
  have hc : Fintype.card (UpperPair (finrank ℝ E)) = (finrank ℝ E).choose 2 := by
    simpa only [UpperPair, Fintype.card_subtype, Fintype.card_fin] using
      (Fintype.card_product_filter_lt (α := Fin (finrank ℝ E)))
  rwa [hc] at h

/-- Translation and rotation parameters have dimension at most
`(k+1) choose 2`. -/
theorem finrank_euclideanMotionParameters_le [FiniteDimensional ℝ E] :
    finrank ℝ (EuclideanMotionParameters E) ≤ (finrank ℝ E + 1).choose 2 := by
  rw [Module.finrank_prod]
  have h := finrank_skewSubmodule_le (E := E)
  have hc := Nat.choose_succ_succ (finrank ℝ E) 1
  norm_num only [Nat.choose_one_right, Nat.succ_eq_add_one, Nat.reduceAdd] at hc
  omega

/-- The derivative of an unoriented edge's squared length, up to its
irrelevant common factor two. -/
noncomputable def unorientedEdgeEquation (p u : V → E) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun a b => ⟪p a - p b, u a - u b⟫_ℝ, by
    intro a b
    have hp : p b - p a = -(p a - p b) := by abel
    have hu : u b - u a = -(u a - u b) := by abel
    dsimp only
    rw [hp, hu, inner_neg_neg]⟩

@[simp]
theorem unorientedEdgeEquation_mk (p u : V → E) (a b : V) :
    unorientedEdgeEquation p u s(a, b) = ⟪p a - p b, u a - u b⟫_ℝ := rfl

/-- One derivative constraint for each graph edge, with no duplicated
orientation coordinates. -/
noncomputable def unorientedMotionMap (G : SimpleGraph V) (p : V → E) :
    (V → E) →ₗ[ℝ] (G.edgeSet → ℝ) where
  toFun u e := unorientedEdgeEquation p u e.val
  map_add' u v := by
    funext e
    have h : ∀ x : Sym2 V,
        unorientedEdgeEquation p (u + v) x =
          unorientedEdgeEquation p u x + unorientedEdgeEquation p v x := by
      intro x
      induction x using Sym2.inductionOn with
      | hf a b =>
        simp only [unorientedEdgeEquation_mk, Pi.add_apply]
        have hs : u a + v a - (u b + v b) = (u a - u b) + (v a - v b) := by abel
        rw [hs, inner_add_right]
    exact h e.val
  map_smul' c u := by
    funext e
    have h : ∀ x : Sym2 V, unorientedEdgeEquation p (c • u) x =
        c • unorientedEdgeEquation p u x := by
      intro x
      induction x using Sym2.inductionOn with
      | hf a b => simp [← smul_sub, real_inner_smul_right]
    exact h e.val

@[simp]
theorem mem_ker_unorientedMotionMap (G : SimpleGraph V) (p u : V → E) :
    u ∈ LinearMap.ker (unorientedMotionMap G p) ↔ IsMotion G p u := by
  constructor
  · intro hu a b hab
    have h := congrFun (LinearMap.mem_ker.mp hu) ⟨s(a, b), hab⟩
    exact h
  · intro hu
    apply LinearMap.mem_ker.mpr
    funext e
    have h : ∀ x : Sym2 V, x ∈ G.edgeSet → unorientedEdgeEquation p u x = 0 := by
      intro x
      induction x using Sym2.inductionOn with
      | hf a b => exact hu a b
    exact h e.val e.property

/-- Rigidity identifies the kernel of the unoriented edge map with
translations and infinitesimal rotations. -/
theorem IsRigid.ker_unorientedMotionMap {G : SimpleGraph V} {p : V → E}
    (hp : IsRigid G p) :
    LinearMap.ker (unorientedMotionMap G p) = LinearMap.range (trivialMotionMap p) := by
  ext u
  rw [mem_ker_unorientedMotionMap, mem_range_trivialMotionMap]
  exact ⟨hp u, fun h => h.isMotion⟩

/-- The edge-count lower bound forced by infinitesimal rigidity. -/
theorem IsRigid.edge_count [Fintype V] [FiniteDimensional ℝ E]
    {G : SimpleGraph V} [Fintype G.edgeSet] {p : V → E} (hp : IsRigid G p) :
    finrank ℝ E * Fintype.card V ≤ Fintype.card G.edgeSet +
      (finrank ℝ E + 1).choose 2 := by
  have hrange : finrank ℝ (LinearMap.range (unorientedMotionMap G p)) ≤
      Fintype.card G.edgeSet := by
    simpa only [Module.finrank_pi] using
      Submodule.finrank_le (LinearMap.range (unorientedMotionMap G p))
  have hker : finrank ℝ (LinearMap.ker (unorientedMotionMap G p)) ≤
      (finrank ℝ E + 1).choose 2 := by
    rw [hp.ker_unorientedMotionMap]
    exact (trivialMotionMap p).finrank_range_le.trans finrank_euclideanMotionParameters_le
  have hdim := (unorientedMotionMap G p).finrank_range_add_finrank_ker
  have hpi : finrank ℝ (V → E) = Fintype.card V * finrank ℝ E := by
    simp [Module.finrank_pi_fintype]
  rw [hpi] at hdim
  rw [Nat.mul_comm (finrank ℝ E) (Fintype.card V)]
  omega

/-- Generic rigidity has the same unoriented edge-count consequence. -/
theorem GenericallyRigid.edge_count [Fintype V] [FiniteDimensional ℝ E]
    {G : SimpleGraph V} [Fintype G.edgeSet] (hG : GenericallyRigid G E) :
    finrank ℝ E * Fintype.card V ≤ Fintype.card G.edgeSet +
      (finrank ℝ E + 1).choose 2 := by
  obtain ⟨p, hp⟩ := hG
  exact hp.edge_count

end Cubical.Rigidity
