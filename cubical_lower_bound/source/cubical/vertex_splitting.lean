import cubical.rigidity_linear
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Vertex splitting

A new vertex is placed at `p root + t • r`. The derivative equation for
the edge from the root to its split copy is divided by `t`; at zero the
resulting linear system remains meaningful. Exactness of this system at
zero forces exactness nearby and therefore rigidity at a nonzero split.
-/

namespace Cubical.Rigidity

open Module Filter
open scoped InnerProductSpace Topology
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Collapse the new vertex onto the designated old vertex. -/
def collapseVertex (root : V) : Option V → V
  | none => root
  | some v => v

/-- The two orientations of the edge between the split vertices. -/
def IsSplitEdge (root : V) (a b : Option V) : Prop :=
  (a = none ∧ b = some root) ∨ (a = some root ∧ b = none)

/-- Split along a one-parameter line, leaving every old point fixed. -/
def splitPlacement (p : V → E) (root : V) (r : E) (t : ℝ) : Option V → E
  | none => p root + t • r
  | some v => p v

@[simp] theorem splitPlacement_zero (p : V → E) (root : V) (r : E) (v : Option V) :
    splitPlacement p root r 0 v = p (collapseVertex root v) := by
  cases v <;> simp [splitPlacement, collapseVertex]

/-- A system of edge constraints with specified normal vectors. -/
noncomputable def edgeConstraintMap (G : SimpleGraph V) (n : DirectedEdge G → E) :
    (V → E) →ₗ[ℝ] (DirectedEdge G → ℝ) where
  toFun u e := ⟪n e, u e.val.1 - u e.val.2⟫_ℝ
  map_add' u v := by
    funext e
    simp only [Pi.add_apply]
    have h : (u e.val.1 + v e.val.1) - (u e.val.2 + v e.val.2) =
      (u e.val.1 - u e.val.2) + (v e.val.1 - v e.val.2) := by abel
    rw [h, inner_add_right]
  map_smul' c u := by
    funext e
    simp [← smul_sub, real_inner_smul_right]

/-- The split edge uses the normal `r`, including when `t = 0`; every
other edge uses the ordinary edge vector. -/
noncomputable def splitConstraintMap (H : SimpleGraph (Option V))
    (p : V → E) (root : V) (r : E) (t : ℝ) :
    (Option V → E) →ₗ[ℝ] (DirectedEdge H → ℝ) := by
  classical
  exact edgeConstraintMap H fun e =>
    if IsSplitEdge root e.val.1 e.val.2 then r else
      splitPlacement p root r t e.val.1 - splitPlacement p root r t e.val.2

@[simp]
theorem splitConstraintMap_apply (H : SimpleGraph (Option V))
    (p : V → E) (root : V) (r : E) (t : ℝ) (u : Option V → E)
    (e : DirectedEdge H) :
    splitConstraintMap H p root r t u e =
      if IsSplitEdge root e.val.1 e.val.2 then ⟪r, u e.val.1 - u e.val.2⟫_ℝ
      else ⟪splitPlacement p root r t e.val.1 - splitPlacement p root r t e.val.2,
        u e.val.1 - u e.val.2⟫_ℝ := by
  classical
  simp only [splitConstraintMap, edgeConstraintMap, LinearMap.coe_mk, AddHom.coe_mk]
  split <;> rfl

/-- Trivial motions solve the normalized split system at every parameter,
including its coincident-vertex limit. -/
theorem splitConstraintMap_comp_trivialMotionMap
    (H : SimpleGraph (Option V)) (p : V → E) (root : V) (r : E) (t : ℝ) :
    (splitConstraintMap H p root r t).comp
      (trivialMotionMap (splitPlacement p root r t)) = 0 := by
  classical
  apply LinearMap.ext
  intro a
  funext e
  change splitConstraintMap H p root r t
    (trivialMotionMap (splitPlacement p root r t) a) e = 0
  rw [splitConstraintMap_apply]
  split_ifs with he
  · rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp only [ha, hb, trivialMotionMap, LinearMap.coe_mk, AddHom.coe_mk,
        splitPlacement, map_add, map_smul]
      have hsub : a.1 + (a.2.val (p root) + t • a.2.val r) -
          (a.1 + a.2.val (p root)) = t • a.2.val r := by abel
      rw [hsub, real_inner_smul_right, a.2.property.inner_self, mul_zero]
    · simp only [ha, hb, trivialMotionMap, LinearMap.coe_mk, AddHom.coe_mk,
        splitPlacement, map_add, map_smul]
      have hsub : a.1 + a.2.val (p root) -
          (a.1 + (a.2.val (p root) + t • a.2.val r)) = -(t • a.2.val r) := by abel
      rw [hsub, inner_neg_right, real_inner_smul_right, a.2.property.inner_self,
        mul_zero, neg_zero]
  · exact ((mem_range_trivialMotionMap _ _).mp
      (LinearMap.mem_range_self (trivialMotionMap _) a)).isMotion
      e.val.1 e.val.2 e.property

/-- At a nonzero parameter the normalized system and the ordinary
rigidity system have the same kernel. -/
theorem splitConstraintMap_ker_eq (H : SimpleGraph (Option V))
    (p : V → E) (root : V) (r : E) {t : ℝ} (ht : t ≠ 0) :
    LinearMap.ker (splitConstraintMap H p root r t) =
      LinearMap.ker (motionMap H (splitPlacement p root r t)) := by
  classical
  ext u
  simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply]
  constructor <;> intro hu e
  · have h := hu e
    rw [splitConstraintMap_apply] at h
    change ⟪splitPlacement p root r t e.val.1 - splitPlacement p root r t e.val.2,
      u e.val.1 - u e.val.2⟫_ℝ = 0
    split_ifs at h with he
    · rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · simp only [ha, hb] at h
        simp only [ha, hb, splitPlacement, add_sub_cancel_left,
          real_inner_smul_left, h, mul_zero]
      · have hs : p root - (p root + t • r) = -(t • r) := by abel
        simp only [ha, hb] at h
        simp only [ha, hb, splitPlacement, hs, inner_neg_left,
          real_inner_smul_left, h, mul_zero, neg_zero]
    · exact h
  · rw [splitConstraintMap_apply]
    have h := hu e
    change ⟪splitPlacement p root r t e.val.1 - splitPlacement p root r t e.val.2,
      u e.val.1 - u e.val.2⟫_ℝ = 0 at h
    split_ifs with he
    · rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · simp only [ha, hb, splitPlacement, add_sub_cancel_left, real_inner_smul_left] at h
        simpa only [ha, hb] using (mul_eq_zero.mp h).resolve_left ht
      · have hs : p root - (p root + t • r) = -(t • r) := by abel
        simp only [ha, hb, splitPlacement, hs, inner_neg_left, real_inner_smul_left,
          neg_eq_zero] at h
        simpa only [ha, hb] using (mul_eq_zero.mp h).resolve_left ht
    · exact h

/-- The normalized equations always imply the ordinary equations, even at
zero where the split edge's ordinary equation vanishes identically. -/
theorem splitConstraintMap_ker_le (H : SimpleGraph (Option V))
    (p : V → E) (root : V) (r : E) (t : ℝ) :
    LinearMap.ker (splitConstraintMap H p root r t) ≤
      LinearMap.ker (motionMap H (splitPlacement p root r t)) := by
  classical
  intro u hu
  rw [mem_ker_motionMap]
  intro a b hab
  have h := congrFun (LinearMap.mem_ker.mp hu) ⟨(a, b), hab⟩
  rw [splitConstraintMap_apply] at h
  simp only [Pi.zero_apply] at h
  split_ifs at h with he
  · rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [splitPlacement, add_sub_cancel_left, real_inner_smul_left, h, mul_zero]
    · have hs : p root - (p root + t • r) = -(t • r) := by abel
      simp only [splitPlacement, hs, inner_neg_left, real_inner_smul_left, h, mul_zero, neg_zero]
  · exact h

/-- Exactness at the coincident-vertex limit. The separating hypothesis
says that the common-neighbor differences, together with `r`, span space. -/
theorem splitConstraintMap_exact_at_zero
    {G : SimpleGraph V} {H : SimpleGraph (Option V)}
    (p : V → E) (root : V) (r : E) (hp : IsRigid G p)
    (hroot : H.Adj none (some root))
    (hcover : ∀ a b, G.Adj a b → ∃ x y : Option V,
      collapseVertex root x = a ∧ collapseVertex root y = b ∧ H.Adj x y)
    {C : Type*} (c : C → V)
    (hleft : ∀ i, H.Adj none (some (c i)))
    (hright : ∀ i, H.Adj (some root) (some (c i)))
    (hsep : ∀ z : E, (∀ i, ⟪p root - p (c i), z⟫_ℝ = 0) → ⟪r, z⟫_ℝ = 0 → z = 0) :
    LinearMap.range (trivialMotionMap (splitPlacement p root r 0)) =
      LinearMap.ker (splitConstraintMap H p root r 0) := by
  apply le_antisymm
  · rintro u ⟨a, rfl⟩
    apply LinearMap.mem_ker.mpr
    exact LinearMap.congr_fun (splitConstraintMap_comp_trivialMotionMap H p root r 0) a
  · intro u hu
    let δ := u none - u (some root)
    have hδ : δ = 0 := by
      apply hsep δ
      · intro i
        have hne : c i ≠ root := by
          intro hi
          have hbad := hright i
          simp [hi] at hbad
        have hL := congrFun (LinearMap.mem_ker.mp hu) ⟨(none, some (c i)), hleft i⟩
        have hR := congrFun (LinearMap.mem_ker.mp hu)
          ⟨(some root, some (c i)), hright i⟩
        simp [splitConstraintMap_apply, IsSplitEdge, splitPlacement, hne] at hL hR
        dsimp [δ]
        simp only [inner_sub_right] at hL hR ⊢
        linarith
      · have h := congrFun (LinearMap.mem_ker.mp hu) ⟨(none, some root), hroot⟩
        simpa [splitConstraintMap_apply, IsSplitEdge, δ] using h
    have heq : u none = u (some root) := sub_eq_zero.mp hδ
    have huCollapsed : ∀ x : Option V, u x = u (some (collapseVertex root x)) := by
      intro x
      cases x with
      | none => exact heq
      | some a => rfl
    have huMotion := (mem_ker_motionMap H _ u).mp
      (splitConstraintMap_ker_le H p root r 0 hu)
    have huBase : IsMotion G p (fun a => u (some a)) := by
      intro a b hab
      obtain ⟨x, y, hx, hy, hxy⟩ := hcover a b hab
      have h := huMotion x y hxy
      simpa only [splitPlacement_zero, huCollapsed x, huCollapsed y, hx, hy] using h
    obtain ⟨s, A, hA, hrep⟩ := hp (fun a => u (some a)) huBase
    apply (mem_range_trivialMotionMap _ u).mpr
    refine ⟨s, A, hA, ?_⟩
    intro x
    rw [splitPlacement_zero, huCollapsed x]
    exact hrep (collapseVertex root x)

section ContinuousSplit

variable [Fintype V] [FiniteDimensional ℝ E]

omit [Fintype V] [FiniteDimensional ℝ E] in
theorem continuous_splitPlacement (p : V → E) (root : V) (r : E) (v : Option V) :
    Continuous (fun t : ℝ => splitPlacement p root r t v) := by
  cases v with
  | none => exact continuous_const.add (continuous_id.smul continuous_const)
  | some v => exact continuous_const

omit [Fintype V] [FiniteDimensional ℝ E] in
theorem continuousAt_splitConstraintMap (H : SimpleGraph (Option V))
    (p : V → E) (root : V) (r : E) (t₀ : ℝ) (u : Option V → E) :
    ContinuousAt (fun t => splitConstraintMap H p root r t u) t₀ := by
  apply continuousAt_pi.mpr
  intro e
  by_cases he : IsSplitEdge root e.val.1 e.val.2
  · simp only [splitConstraintMap_apply, he, ite_eq_left]
    exact continuousAt_const
  · simp only [splitConstraintMap_apply, he]
    exact ((continuous_splitPlacement p root r e.val.1).continuousAt.sub
      (continuous_splitPlacement p root r e.val.2).continuousAt).inner continuousAt_const

/-- Vertex splitting preserves rigidity when the common-neighbor
differences together with a single direction span the ambient space.
Only the new vertex moves; all old coordinates are retained. -/
theorem exists_rigid_split_of_separating_direction
    {G : SimpleGraph V} {H : SimpleGraph (Option V)}
    (p : V → E) (root : V) (r : E) (hp : IsRigid G p)
    (hroot : H.Adj none (some root))
    (hcover : ∀ a b, G.Adj a b → ∃ x y : Option V,
      collapseVertex root x = a ∧ collapseVertex root y = b ∧ H.Adj x y)
    {C : Type*} (c : C → V)
    (hleft : ∀ i, H.Adj none (some (c i)))
    (hright : ∀ i, H.Adj (some root) (some (c i)))
    (hsep : ∀ z : E, (∀ i, ⟪p root - p (c i), z⟫_ℝ = 0) → ⟪r, z⟫_ℝ = 0 → z = 0) :
    ∃ t : ℝ, 0 < t ∧ IsRigid H (splitPlacement p root r t) := by
  classical
  have hevent := Exactness.eventually_range_eq_ker
    (fun t : ℝ => trivialMotionMap (splitPlacement p root r t))
    (fun t : ℝ => splitConstraintMap H p root r t) 0
    (continuousAt_trivialMotionMap _ 0
      (fun v => (continuous_splitPlacement p root r v).continuousAt))
    (continuousAt_splitConstraintMap H p root r 0)
    (splitConstraintMap_comp_trivialMotionMap H p root r)
    (splitConstraintMap_exact_at_zero p root r hp hroot hcover c hleft hright hsep)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hexact⟩ := (hpos.and (hevent.filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨t, ht, (isRigid_iff_range_eq_ker H _).mpr ?_⟩
  rw [hexact, splitConstraintMap_ker_eq H p root r ht.ne']

omit [Fintype V] in
/-- A family spanning codimension at most one admits one additional
normal that separates every vector. -/
theorem exists_separating_direction {C : Type*} (v : C → E)
    (hdim : finrank ℝ E ≤ finrank ℝ (Submodule.span ℝ (Set.range v)) + 1) :
    ∃ r : E, ∀ z : E, (∀ i, ⟪v i, z⟫_ℝ = 0) → ⟪r, z⟫_ℝ = 0 → z = 0 := by
  let K : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hdimK : finrank ℝ Kᗮ ≤ 1 := by
    have h := K.finrank_add_finrank_orthogonal
    change finrank ℝ E ≤ finrank ℝ K + 1 at hdim
    omega
  obtain ⟨r, hr⟩ := (finrank_le_one_iff (K := ℝ) (V := Kᗮ)).mp hdimK
  refine ⟨r, ?_⟩
  intro z hz hrz
  have hzK : z ∈ Kᗮ := by
    apply (K.mem_orthogonal z).mpr
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hz i
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
    | smul c x _ hx => simp [real_inner_smul_left, hx]
  obtain ⟨a, ha⟩ := hr ⟨z, hzK⟩
  have ha' : a • (r : E) = z := congrArg Subtype.val ha
  have hz0 : ⟪z, z⟫_ℝ = 0 := by
    calc
      ⟪z, z⟫_ℝ = ⟪a • (r : E), z⟫_ℝ := by rw [ha']
      _ = a * ⟪(r : E), z⟫_ℝ := real_inner_smul_left _ _ _
      _ = 0 := by rw [hrz, mul_zero]
  exact inner_self_eq_zero.mp hz0

/-- Whiteley's vertex-splitting principle, with an arbitrary finite
ambient dimension and at least `dim E - 1` independent common-neighbor
differences. The old placement is preserved point by point. -/
theorem exists_rigid_vertex_split
    {G : SimpleGraph V} {H : SimpleGraph (Option V)}
    (p : V → E) (root : V) (hp : IsRigid G p)
    (hroot : H.Adj none (some root))
    (hcover : ∀ a b, G.Adj a b → ∃ x y : Option V,
      collapseVertex root x = a ∧ collapseVertex root y = b ∧ H.Adj x y)
    {C : Type*} [Fintype C] (c : C → V)
    (hleft : ∀ i, H.Adj none (some (c i)))
    (hright : ∀ i, H.Adj (some root) (some (c i)))
    (hind : LinearIndependent ℝ (fun i => p root - p (c i)))
    (hcard : finrank ℝ E ≤ Fintype.card C + 1) :
    ∃ q : Option V → E, IsRigid H q ∧ ∀ v, q (some v) = p v := by
  have hdim : finrank ℝ E ≤
      finrank ℝ (Submodule.span ℝ (Set.range (fun i => p root - p (c i)))) + 1 := by
    rw [finrank_span_eq_card hind]
    exact hcard
  obtain ⟨r, hr⟩ := exists_separating_direction (fun i => p root - p (c i)) hdim
  obtain ⟨t, _, ht⟩ := exists_rigid_split_of_separating_direction
    p root r hp hroot hcover c hleft hright hr
  exact ⟨splitPlacement p root r t, ht, fun _ => rfl⟩

end ContinuousSplit

end Cubical.Rigidity
