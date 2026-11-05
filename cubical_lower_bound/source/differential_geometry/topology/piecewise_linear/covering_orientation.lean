/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import differential_geometry.topology.piecewise_linear.covering_triangulation
import differential_geometry.topology.piecewise_linear.orientation
import differential_geometry.topology.piecewise_linear.orientation_cocycle
import differential_geometry.topology.piecewise_linear.pl_path

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Set _root_.Topology
open scoped unitInterval

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
  {X' : Type u} [TopologicalSpace X'] {p : X' → K.space}
  [Finite (coveringVertex K p)]

local instance (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (s : Finset E) :
    Finite (faceStarComplex L s).faces := (faceStarComplex_faces_finite L s).to_subtype

open Classical in
noncomputable instance finite_coveringComplex_faces : Finite (coveringComplex K p).faces :=
  (coveringComplex_faces_finite K p).to_subtype

open Classical in
theorem IsCombinatorialManifold.coveringComplex
    (hp : IsCoveringMap p) {n : ℕ} (hK : IsCombinatorialManifold n K) :
    IsCombinatorialManifold n (coveringComplex K p) := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
    Classical.decEq _
  cases n with
  | zero =>
      intro z hz
      obtain ⟨v, rfl⟩ := exists_coveringVertexPoint_of_singleton_mem K p hz
      rw [Set.eq_empty_iff_forall_notMem]
      intro q hq
      have hbase := (coveringVertexLink_isGlueIso K p hp v).image₂ q hq
      rw [hK (coveringVertex.base v) (coveringVertex.singleton_base_mem_faces v)] at hbase
      exact hbase
  | succ n =>
      intro z hz
      obtain ⟨v, rfl⟩ := exists_coveringVertexPoint_of_singleton_mem K p hz
      exact (hK (coveringVertex.base v) (coveringVertex.singleton_base_mem_faces v))
        |>.of_isPLHomeomorphOn (coveringVertexLink_isGlueIso K p hp v).isPLHomeomorphOn

open Classical in
noncomputable def CoherentOrientation.coveringVertexLink {n : ℕ}
    (v : coveringVertex K p)
    (o : CoherentOrientation n
      (SimplicialComplex.geometricLink K {coveringVertex.base v}))
    (hp : IsCoveringMap p) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
      Classical.decEq _
    CoherentOrientation n
      (SimplicialComplex.geometricLink (coveringComplex K p)
        {coveringVertexPoint K p v}) := by
  dsimp only
  exact o.map (coveringVertexLink_isGlueIso K p hp v)

open Classical in
theorem isOrientable_coveringVertexLink_iff {n : ℕ}
    (hp : IsCoveringMap p) (v : coveringVertex K p) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
      Classical.decEq _
    IsOrientable n (SimplicialComplex.geometricLink K {coveringVertex.base v}) ↔
      IsOrientable n (SimplicialComplex.geometricLink (coveringComplex K p)
        {coveringVertexPoint K p v}) := by
  dsimp only
  exact isOrientable_iff_of_isGlueIso (coveringVertexLink_isGlueIso K p hp v)

open Classical in
theorem isOrientable_coveringVertexLink_of_isCombinatorialManifoldWithBoundary
    (hp : IsCoveringMap p) {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (v : coveringVertex K p) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
      Classical.decEq _
    IsOrientable n (SimplicialComplex.geometricLink (coveringComplex K p)
      {coveringVertexPoint K p v}) := by
  dsimp only
  apply (isOrientable_coveringVertexLink_iff hp v).mp
  rcases hK (coveringVertex.base v) (coveringVertex.singleton_base_mem_faces v) with hS | hB
  · exact isOrientable_of_isPLSphere hS
  · exact isOrientable_of_isPLBall hB

open Classical in
noncomputable instance SimplicialBoolCocycle.finite_coveringVertex
    (ε : SimplicialBoolCocycle K) :
    Finite (coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj) := by
  apply coveringVertex.finite K
  intro x
  apply Set.finite_coe_iff.mp
  apply Nat.finite_of_card_ne_zero
  rw [ε.card_fiber x]
  decide

open Classical in
theorem SimplicialBoolCocycle.coveringComplex_isCombinatorialManifoldWithBoundary
    (ε : SimplicialBoolCocycle K) {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K) :
    IsCombinatorialManifoldWithBoundary n
      (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj) :=
  isCombinatorialManifoldWithBoundary_coveringComplex K
    ε.toBoolCocycle.toFiberBundleCore.proj ε.isCoveringMap hK

open Classical in
theorem SimplicialBoolCocycle.coveringComplex_isCombinatorialManifold
    (ε : SimplicialBoolCocycle K) {n : ℕ} (hK : IsCombinatorialManifold n K) :
    IsCombinatorialManifold n
      (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj) :=
  hK.coveringComplex ε.isCoveringMap

open Classical in
noncomputable def SimplicialBoolCocycle.coveringComplexHomeomorph
    (ε : SimplicialBoolCocycle K) :
    (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj).space ≃ₜ
      ε.toBoolCocycle.toFiberBundleCore.TotalSpace :=
  coveringSpaceHomeomorph K ε.toBoolCocycle.toFiberBundleCore.proj ε.isCoveringMap

open Classical in
theorem SimplicialBoolCocycle.isOrientable_coveringComplex_vertexLink
    (ε : SimplicialBoolCocycle K) {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (v : coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj) :
    let _ : DecidableEq (EuclideanSpace ℝ
      (Fin (Nat.card (coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj)))) :=
        Classical.decEq _
    IsOrientable n (SimplicialComplex.geometricLink
      (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj)
      {coveringVertexPoint K ε.toBoolCocycle.toFiberBundleCore.proj v}) := by
  dsimp only
  exact isOrientable_coveringVertexLink_of_isCombinatorialManifoldWithBoundary
    ε.isCoveringMap hK v

open Classical in
omit [FiniteDimensional ℝ E] [Finite K.faces] in
private theorem vertex_eq_of_mem_openStar {a b : E}
    (ha : {a} ∈ K.faces) (h : a ∈ openStar K b) : a = b := by
  by_contra hab
  have haHull : a ∈ convexHull ℝ (({a} : Finset E) : Set E) :=
    subset_convexHull ℝ _ (by simp)
  exact h.2 (mem_iUnion₂.mpr
    ⟨{a}, ⟨ha, by simpa using Ne.symm hab⟩, haHull⟩)

open Classical in
omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.toBoolCocycle_indexAt_vertex
    (ε : SimplicialBoolCocycle K) {a : E} (ha : {a} ∈ K.faces) :
    ε.toBoolCocycle.indexAt
      (⟨a, K.subset_space (by simpa using ha) (by simp)⟩ : K.space) = ⟨a, ha⟩ := by
  apply Subtype.ext
  symm
  let x : K.space := ⟨a, K.subset_space (by simpa using ha) (by simp)⟩
  have hmem := ε.toBoolCocycle.mem_baseSet_at x
  change a ∈ openStar K (ε.toBoolCocycle.indexAt x : E) at hmem
  exact vertex_eq_of_mem_openStar ha hmem

omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.localTriv_side_eq_of_path
    (ε : SimplicialBoolCocycle K)
    (i : {v // {v} ∈ K.faces})
    (γ : C(I, ε.toBoolCocycle.toFiberBundleCore.TotalSpace))
    (hγ : ∀ t, (γ t).1 ∈ ε.toBoolCocycle.baseSet i) :
    ((ε.toBoolCocycle.toFiberBundleCore.localTriv i) (γ 0)).2 =
      ((ε.toBoolCocycle.toFiberBundleCore.localTriv i) (γ 1)).2 := by
  have hcont : Continuous fun t =>
      ((ε.toBoolCocycle.toFiberBundleCore.localTriv i) (γ t)).2 := by
    apply continuous_snd.comp
    apply (ε.toBoolCocycle.toFiberBundleCore.localTriv i).continuousOn_toFun.comp_continuous
      γ.continuous
    intro t
    exact hγ t
  exact ((IsLocallyConstant.iff_continuous _).2 hcont).apply_eq_of_preconnectedSpace 0 1

omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.localTriv_side_change
    (ε : SimplicialBoolCocycle K)
    (i j : {v // {v} ∈ K.faces})
    (z : ε.toBoolCocycle.toFiberBundleCore.TotalSpace)
    (hzi : z.1 ∈ ε.toBoolCocycle.baseSet i)
    (hzj : z.1 ∈ ε.toBoolCocycle.baseSet j) :
    ((ε.toBoolCocycle.toFiberBundleCore.localTriv j) z).2 =
      Bool.xor ((ε.toBoolCocycle.toFiberBundleCore.localTriv i) z).2
        (ε.parity i j) := by
  rw [FiberBundleCore.localTriv_apply, FiberBundleCore.localTriv_apply]
  let side : Bool := z.2
  change Bool.xor side
      (ε.parity (ε.toBoolCocycle.indexAt z.1) j) =
    Bool.xor (Bool.xor side
      (ε.parity (ε.toBoolCocycle.indexAt z.1) i)) (ε.parity i j)
  rw [Bool.xor_assoc]
  have hcomp := ε.toBoolCocycle.parity_comp
    (ε.toBoolCocycle.indexAt z.1) i j z.1
      ⟨⟨ε.toBoolCocycle.mem_baseSet_at z.1, hzi⟩, hzj⟩
  change Bool.xor (ε.parity (ε.toBoolCocycle.indexAt z.1) i)
      (ε.parity i j) = ε.parity (ε.toBoolCocycle.indexAt z.1) j at hcomp
  rw [hcomp]

open Classical in
omit [Finite K.faces] [Finite (coveringVertex K p)] in
private theorem coveringEdgeLift_target
    (hp : IsCoveringMap p) (v : coveringVertex K p) (w : E)
    (hvw : {coveringVertex.base v, w} ∈ K.faces) :
    coveringEdgeLift hp v w hvw
      ⟨w, subset_convexHull ℝ _ (by simp)⟩ = (coveringNeighbor hp v w).1 := by
  rw [coveringNeighbor, dite_eq_left hvw]
  rfl

open Classical in
omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.indexAt_coveringVertex
    (ε : SimplicialBoolCocycle K)
    (v : coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj) :
    ε.toBoolCocycle.indexAt v.1.1 =
      ⟨coveringVertex.base v, coveringVertex.singleton_base_mem_faces v⟩ := by
  apply Subtype.ext
  symm
  have hmem := ε.toBoolCocycle.mem_baseSet_at v.1.1
  change coveringVertex.base v ∈
    openStar K (ε.toBoolCocycle.indexAt v.1.1 : E) at hmem
  exact vertex_eq_of_mem_openStar (coveringVertex.singleton_base_mem_faces v) hmem

open Classical in
omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.localTriv_coveringVertex_side
    (ε : SimplicialBoolCocycle K)
    (v : coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj) :
    ((ε.toBoolCocycle.toFiberBundleCore.localTriv
      ⟨coveringVertex.base v, coveringVertex.singleton_base_mem_faces v⟩) v.1).2 = v.1.2 := by
  rw [FiberBundleCore.localTriv_apply]
  change Bool.xor v.1.2
    (ε.parity (ε.toBoolCocycle.indexAt v.1.1)
      (coveringVertex.base v)) = v.1.2
  rw [ε.indexAt_coveringVertex]
  change Bool.xor v.1.2 (ε.parity (coveringVertex.base v) (coveringVertex.base v)) = v.1.2
  rw [ε.self _ (coveringVertex.singleton_base_mem_faces v)]
  cases v.1.2 <;> rfl

open Classical in
theorem SimplicialBoolCocycle.coveringNeighbor_side
    (ε : SimplicialBoolCocycle K)
    (v : coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj)
    (w : E) (hvw : {coveringVertex.base v, w} ∈ K.faces) :
    (coveringNeighbor ε.isCoveringMap v w).1.2 =
      Bool.xor v.1.2 (ε.parity (coveringVertex.base v) w) := by
  let a := coveringVertex.base v
  let s : Finset E := {a, w}
  let C := ε.toBoolCocycle
  let Z := C.toFiberBundleCore
  let g := coveringEdgeLift ε.isCoveringMap v w hvw
  let u := coveringNeighbor ε.isCoveringMap v w
  let sideV : Bool := v.1.2
  let sideU : Bool := u.1.2
  have ha : {a} ∈ K.faces := coveringVertex.singleton_base_mem_faces v
  have hw : {w} ∈ K.faces :=
    K.down_closed hvw (by simp) (Finset.singleton_nonempty w)
  have hs : s ∈ K.faces := by simpa [s, a] using hvw
  have huBase : coveringVertex.base u = w :=
    coveringNeighbor_base_of_face ε.isCoveringMap v w hvw
  let i : {x // {x} ∈ K.faces} := ⟨a, ha⟩
  let j : {x // {x} ∈ K.faces} := ⟨w, hw⟩
  let m : E := s.centroid ℝ id
  have hmOpen : m ∈ openSimplex s :=
    centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)
  have hmHull : m ∈ convexHull ℝ (s : Set E) :=
    openSimplex_subset_convexHull s hmOpen
  have hmStarA : m ∈ openStar K a :=
    SimplicialBoolCocycle.mem_openStar_of_mem_openSimplex hs hmOpen (by simp [s])
  have hmStarW : m ∈ openStar K w :=
    SimplicialBoolCocycle.mem_openStar_of_mem_openSimplex hs hmOpen (by simp [s])
  let xa : convexHull ℝ (s : Set E) :=
    ⟨a, subset_convexHull ℝ _ (by simp [s])⟩
  let xw : convexHull ℝ (s : Set E) :=
    ⟨w, subset_convexHull ℝ _ (by simp [s])⟩
  let xm : convexHull ℝ (s : Set E) := ⟨m, hmHull⟩
  have hsegA : segment ℝ (xa : E) (xm : E) ⊆ convexHull ℝ (s : Set E) :=
    (convex_convexHull ℝ _).segment_subset xa.2 xm.2
  have hsegW : segment ℝ (xw : E) (xm : E) ⊆ convexHull ℝ (s : Set E) :=
    (convex_convexHull ℝ _).segment_subset xw.2 xm.2
  let α : Path xa xm := segmentPath xa xm hsegA
  let β : Path xw xm := segmentPath xw xm hsegW
  let γa : C(I, Z.TotalSpace) := g.comp α.toContinuousMap
  let γw : C(I, Z.TotalSpace) := g.comp β.toContinuousMap
  have hγaBase : ∀ t, (γa t).1 ∈ C.baseSet i := by
    intro t
    change ((g (α t)).1 : E) ∈ openStar K a
    have hproj := congrFun (coveringEdgeLift_projection ε.isCoveringMap v w hvw) (α t)
    have hval : ((g (α t)).1 : E) = (α t : E) := congrArg Subtype.val hproj
    rw [hval]
    apply (SimplicialBoolCocycle.starConvex_openStar ha).segment_subset hmStarA
    exact forall_mem_of_segmentPath xa xm hsegA t
  have hγwBase : ∀ t, (γw t).1 ∈ C.baseSet j := by
    intro t
    change ((g (β t)).1 : E) ∈ openStar K w
    have hproj := congrFun (coveringEdgeLift_projection ε.isCoveringMap v w hvw) (β t)
    have hval : ((g (β t)).1 : E) = (β t : E) := congrArg Subtype.val hproj
    rw [hval]
    apply (SimplicialBoolCocycle.starConvex_openStar hw).segment_subset hmStarW
    exact forall_mem_of_segmentPath xw xm hsegW t
  have hγaStart : γa 0 = v.1 := by
    change g (α 0) = v.1
    rw [α.source]
    exact coveringEdgeLift_source ε.isCoveringMap v w hvw
  have hγaEnd : γa 1 = g xm := by
    change g (α 1) = g xm
    rw [α.target]
  have hγwStart : γw 0 = u.1 := by
    change g (β 0) = u.1
    rw [β.source]
    exact coveringEdgeLift_target ε.isCoveringMap v w hvw
  have hγwEnd : γw 1 = g xm := by
    change g (β 1) = g xm
    rw [β.target]
  have hconstA := ε.localTriv_side_eq_of_path i γa hγaBase
  have hconstW := ε.localTriv_side_eq_of_path j γw hγwBase
  have hmidI : (g xm).1 ∈ C.baseSet i := by
    change ((g xm).1 : E) ∈ openStar K a
    have hproj := congrFun (coveringEdgeLift_projection ε.isCoveringMap v w hvw) xm
    have hval : ((g xm).1 : E) = (xm : E) := congrArg Subtype.val hproj
    rw [hval]
    exact hmStarA
  have hmidJ : (g xm).1 ∈ C.baseSet j := by
    change ((g xm).1 : E) ∈ openStar K w
    have hproj := congrFun (coveringEdgeLift_projection ε.isCoveringMap v w hvw) xm
    have hval : ((g xm).1 : E) = (xm : E) := congrArg Subtype.val hproj
    rw [hval]
    exact hmStarW
  have hchange := ε.localTriv_side_change i j (g xm) hmidI hmidJ
  have hchartU : ((Z.localTriv j) u.1).2 = sideU := by
    have hj :
        (⟨coveringVertex.base u, coveringVertex.singleton_base_mem_faces u⟩ :
          {x // {x} ∈ K.faces}) = j := by
      apply Subtype.ext
      exact huBase
    rw [← hj]
    exact ε.localTriv_coveringVertex_side u
  have hchartV : ((Z.localTriv i) v.1).2 = sideV :=
    ε.localTriv_coveringVertex_side v
  change sideU = Bool.xor sideV (ε.parity a w)
  calc
    sideU = ((Z.localTriv j) u.1).2 := hchartU.symm
    _ = ((Z.localTriv j) (γw 0)).2 :=
      congrArg (fun z : Z.TotalSpace => (((Z.localTriv j) z).2 : Bool)) hγwStart.symm
    _ = ((Z.localTriv j) (γw 1)).2 := hconstW
    _ = ((Z.localTriv j) (g xm)).2 :=
      congrArg (fun z : Z.TotalSpace => (((Z.localTriv j) z).2 : Bool)) hγwEnd
    _ = Bool.xor ((Z.localTriv i) (g xm)).2 (ε.parity i j) := hchange
    _ = Bool.xor ((Z.localTriv i) (γa 1)).2 (ε.parity i j) := by rw [hγaEnd]
    _ = Bool.xor ((Z.localTriv i) (γa 0)).2 (ε.parity i j) :=
      congrArg (fun side => Bool.xor side (ε.parity i j)) hconstA.symm
    _ = Bool.xor ((Z.localTriv i) v.1).2 (ε.parity i j) := by rw [hγaStart]
    _ = Bool.xor sideV (ε.parity i j) :=
      congrArg (fun side => Bool.xor side (ε.parity i j)) hchartV
    _ = Bool.xor sideV (ε.parity a w) := rfl


/- Adaptation: retain the covering-neighbor parity development needed by
CocycleWalkLift; unrelated orientation constructions are outside this project. -/

end DifferentialGeometry.Topology.PiecewiseLinear
