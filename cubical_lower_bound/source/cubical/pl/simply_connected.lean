import differential_geometry.topology.piecewise_linear.cocycle_walk_lift
import differential_geometry.topology.simplex.normed_ball
import differential_geometry.topology.sphere.sphere_simply_connected

/-!
# Simple connectedness and exact Boolean cocycles on PL spheres

The sphere condition here is the genuine piecewise affine homeomorphism
condition, not a hypothesis about homology or graph colorability.
-/

noncomputable section

open Classical Set

namespace Cubical.PL

open DifferentialGeometry.Topology.PiecewiseLinear
open DifferentialGeometry.Topology

def simplexBoundaryComparison (n : ℕ) :
    stdSimplexBoundary n ≃ₜ DifferentialGeometry.Simplex.boundary (Fin (n + 1)) where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem sphere_simplyConnectedSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} {P : Set E}
    (hn : 2 ≤ n) (hP : IsPLSphere n P) : SimplyConnectedSpace P := by
  obtain ⟨f, hf⟩ := hP
  let e : stdSimplexBoundary (n + 1) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    (simplexBoundaryComparison (n + 1)).trans
      (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm)
  letI : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    DifferentialGeometry.Topology.simplyConnectedSpace_sphere_of_two_le hn
  letI : SimplyConnectedSpace (stdSimplexBoundary (n + 1)) :=
    e.toHomotopyEquiv.simplyConnectedSpace
  exact hf.homeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Geometry.SimplicialComplex ℝ E}

/-- Vanishing monodromy makes a cocycle exact on every graph component;
no connectedness hypothesis on the graph is needed. -/
theorem cocycle_exact_of_zero_loops (ε : SimplicialBoolCocycle K)
    (hzero : ∀ (u : K.vertices) (p : (SimplicialComplex.edgeGraph K).Walk u u),
      ε.walkMonodromy p = 0) : ε.IsCoboundary := by
  let G := SimplicialComplex.edgeGraph K
  let base (c : G.ConnectedComponent) : K.vertices := c.exists_rep.choose
  have hbase (c : G.ConnectedComponent) : G.connectedComponentMk (base c) = c :=
    c.exists_rep.choose_spec
  have reach (c : G.ConnectedComponent) (u : K.vertices)
      (hu : G.connectedComponentMk u = c) : G.Reachable (base c) u :=
    SimpleGraph.ConnectedComponent.exact ((hbase c).trans hu.symm)
  let m (u : K.vertices) : ZMod 2 :=
    ε.walkMonodromy (reach (G.connectedComponentMk u) u rfl).some
  have hedge (u v : K.vertices) (huv : G.Adj u v) :
      boolZMod2 (ε.parity u.val v.val) = m u + m v := by
    let c := G.connectedComponentMk u
    have hvc : G.connectedComponentMk v = c :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv).symm
    let pu := (reach c u rfl).some
    let pv := (reach c v hvc).some
    have hmu : ε.walkMonodromy pu = m u := rfl
    have hmv : ε.walkMonodromy pv = m v := by
      have ht (a b : G.ConnectedComponent) (hab : a = b)
          (ha : G.connectedComponentMk v = a) (hb : G.connectedComponentMk v = b) :
          ε.walkMonodromy (reach a v ha).some = ε.walkMonodromy (reach b v hb).some := by
        subst b
        rfl
      exact ht c (G.connectedComponentMk v) hvc.symm hvc rfl
    have hloop := hzero (base c)
      ((pu.append (SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil)).append pv.reverse)
    rw [ε.walkMonodromy_append, ε.walkMonodromy_append, ε.walkMonodromy_cons,
      ε.walkMonodromy_nil, add_zero, ε.walkMonodromy_reverse, hmu, hmv] at hloop
    have hj : boolZMod2 (ε.parity u.val v.val) = -m u - m v := by
      linear_combination hloop
    simpa only [sub_eq_add_neg, CharTwo.neg_eq] using hj
  refine ⟨fun a => if ha : a ∈ K.vertices then zmod2Bool (m ⟨a, ha⟩) else false, ?_⟩
  intro a b hab
  have ha : a ∈ K.vertices := K.down_closed hab (by simp) (Finset.singleton_nonempty a)
  have hb : b ∈ K.vertices := K.down_closed hab (by simp) (Finset.singleton_nonempty b)
  apply boolZMod2_injective
  rw [boolZMod2_xor]
  dsimp only
  rw [dif_pos ha, dif_pos hb, boolZMod2_zmod2Bool, boolZMod2_zmod2Bool]
  by_cases hne : a = b
  · subst b
    rw [ε.self a ha]
    exact (CharTwo.add_self_eq_zero (m ⟨a, ha⟩)).symm
  · exact hedge ⟨a, ha⟩ ⟨b, hb⟩ ⟨fun h => hne (congrArg Subtype.val h), hab⟩

theorem cocycle_exact_of_simplyConnected [FiniteDimensional ℝ E] [Finite K.faces]
    [SimplyConnectedSpace K.space] (ε : SimplicialBoolCocycle K) : ε.IsCoboundary := by
  apply cocycle_exact_of_zero_loops ε
  intro u p
  exact ε.walkMonodromy_eq_zero_of_homotopic_refl p
    (SimplyConnectedSpace.paths_homotopic _ _)

theorem cocycle_exact_of_sphere [FiniteDimensional ℝ E] [Finite K.faces]
    {n : ℕ} (hn : 2 ≤ n) (hK : IsPLSphere n K.space)
    (ε : SimplicialBoolCocycle K) : ε.IsCoboundary := by
  letI : SimplyConnectedSpace K.space := sphere_simplyConnectedSpace hn hK
  exact cocycle_exact_of_simplyConnected ε

end Cubical.PL
