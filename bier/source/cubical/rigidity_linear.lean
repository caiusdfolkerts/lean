import cubical.rigidity
import cubical.exactness

/-!
# Rigidity as exactness of a linear complex

The map from translations and skew-adjoint operators to velocity fields has
range exactly the trivial motions. The edge derivative map has kernel
exactly the infinitesimal motions. Thus genuine infinitesimal rigidity is
the exactness of this complex; in particular it is open in the placement.
-/

namespace Cubical.Rigidity

open Module Filter
open scoped InnerProductSpace Topology

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The vector space of infinitesimal rotations. -/
def skewSubmodule : Submodule ℝ (E →ₗ[ℝ] E) where
  carrier := IsSkew
  zero_mem' := by intro x y; simp
  add_mem' hA hB := by
    intro x y
    simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hA x y, hB x y]
    ring
  smul_mem' c A hA := by
    intro x y
    simp only [LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right,
      hA x y]
    ring

/-- Translation and rotation parameters. -/
abbrev EuclideanMotionParameters (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] := E × (skewSubmodule (E := E))

/-- Evaluation of a Euclidean infinitesimal motion at a placement. -/
noncomputable def trivialMotionMap (p : V → E) :
    EuclideanMotionParameters E →ₗ[ℝ] (V → E) where
  toFun a v := a.1 + a.2.val (p v)
  map_add' a b := by
    funext v
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, LinearMap.add_apply,
      Pi.add_apply]
    abel
  map_smul' c a := by
    funext v
    simp [smul_add]

/-- Directed edges are convenient linear coordinates; opposite orientations
give the same equation, which does not change its kernel. -/
abbrev DirectedEdge (G : SimpleGraph V) := {e : V × V // G.Adj e.1 e.2}

/-- The edge-length derivative map. -/
noncomputable def motionMap (G : SimpleGraph V) (p : V → E) :
    (V → E) →ₗ[ℝ] (DirectedEdge G → ℝ) where
  toFun u e := ⟪p e.val.1 - p e.val.2, u e.val.1 - u e.val.2⟫_ℝ
  map_add' u v := by
    funext e
    simp only [Pi.add_apply]
    have h : (u e.val.1 + v e.val.1) - (u e.val.2 + v e.val.2) =
      (u e.val.1 - u e.val.2) + (v e.val.1 - v e.val.2) := by abel
    rw [h, inner_add_right]
  map_smul' c u := by
    funext e
    simp [← smul_sub, real_inner_smul_right]

@[simp]
theorem mem_ker_motionMap (G : SimpleGraph V) (p u : V → E) :
    u ∈ LinearMap.ker (motionMap G p) ↔ IsMotion G p u := by
  constructor
  · intro hu a b hab
    exact congrFun (LinearMap.mem_ker.mp hu) ⟨(a, b), hab⟩
  · intro hu
    apply LinearMap.mem_ker.mpr
    funext e
    exact hu e.val.1 e.val.2 e.property

@[simp]
theorem mem_range_trivialMotionMap (p u : V → E) :
    u ∈ LinearMap.range (trivialMotionMap p) ↔ IsTrivialMotion p u := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, a.2.val, a.2.property, fun _ => rfl⟩
  · rintro ⟨t, A, hA, hu⟩
    refine ⟨(t, ⟨A, hA⟩), ?_⟩
    funext v
    exact (hu v).symm

theorem range_trivialMotionMap_le_ker (G : SimpleGraph V) (p : V → E) :
    LinearMap.range (trivialMotionMap p) ≤ LinearMap.ker (motionMap G p) := by
  intro u hu
  exact (mem_ker_motionMap G p u).mpr ((mem_range_trivialMotionMap p u).mp hu).isMotion

theorem motionMap_comp_trivialMotionMap (G : SimpleGraph V) (p : V → E) :
    (motionMap G p).comp (trivialMotionMap p) = 0 := by
  apply LinearMap.ext
  intro a
  funext e
  have hu := range_trivialMotionMap_le_ker G p (LinearMap.mem_range_self (trivialMotionMap p) a)
  exact congrFun (LinearMap.mem_ker.mp hu) e

theorem isRigid_iff_range_eq_ker (G : SimpleGraph V) (p : V → E) :
    IsRigid G p ↔ LinearMap.range (trivialMotionMap p) = LinearMap.ker (motionMap G p) := by
  constructor
  · intro h
    apply le_antisymm (range_trivialMotionMap_le_ker G p)
    intro u hu
    exact (mem_range_trivialMotionMap p u).mpr (h u ((mem_ker_motionMap G p u).mp hu))
  · intro h u hu
    apply (mem_range_trivialMotionMap p u).mp
    rw [h]
    exact (mem_ker_motionMap G p u).mpr hu

section Continuity

variable [Fintype V] [FiniteDimensional ℝ E]
  {α : Type*} [TopologicalSpace α]

omit [Fintype V] in
/-- Continuity of each trivial-motion velocity field with respect to the placement. -/
theorem continuousAt_trivialMotionMap (p : α → V → E) (a₀ : α)
    (hp : ∀ v, ContinuousAt (fun a => p a v) a₀)
    (u : EuclideanMotionParameters E) :
    ContinuousAt (fun a => trivialMotionMap (p a) u) a₀ := by
  apply continuousAt_pi.mpr
  intro v
  exact continuousAt_const.add (u.2.val.continuous_of_finiteDimensional.continuousAt.comp (hp v))

omit [Fintype V] [FiniteDimensional ℝ E] in
/-- Continuity of each edge-derivative vector with respect to the placement. -/
theorem continuousAt_motionMap (G : SimpleGraph V) (p : α → V → E) (a₀ : α)
    (hp : ∀ v, ContinuousAt (fun a => p a v) a₀) (u : V → E) :
    ContinuousAt (fun a => motionMap G (p a) u) a₀ := by
  apply continuousAt_pi.mpr
  intro e
  exact ((hp e.val.1).sub (hp e.val.2)).inner continuousAt_const

/-- Actual infinitesimal rigidity persists under sufficiently small perturbations. -/
theorem IsRigid.eventually {G : SimpleGraph V} (p : α → V → E) (a₀ : α)
    (hp : ∀ v, ContinuousAt (fun a => p a v) a₀)
    (hrigid : IsRigid G (p a₀)) :
    ∀ᶠ a in 𝓝 a₀, IsRigid G (p a) := by
  classical
  have h := Exactness.eventually_range_eq_ker
    (fun a => trivialMotionMap (p a)) (fun a => motionMap G (p a)) a₀
    (continuousAt_trivialMotionMap p a₀ hp)
    (continuousAt_motionMap G p a₀ hp)
    (fun a => motionMap_comp_trivialMotionMap G (p a))
    ((isRigid_iff_range_eq_ker G (p a₀)).mp hrigid)
  exact h.mono fun a ha => (isRigid_iff_range_eq_ker G (p a)).mpr ha

end Continuity

end Cubical.Rigidity
