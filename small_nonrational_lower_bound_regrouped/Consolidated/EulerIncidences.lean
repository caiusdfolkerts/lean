module
public import Papers.PolytopeFaceCounting
public import Papers.PolytopeEulerRadialFigure
public import Papers.PolytopeVertexCone
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Real.Basic
public import Lean.Elab.Tactic.Omega
public import Papers.PolytopeBasicExtreme
public import Papers.TwoFaceGraph
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Cubical.Polytope.SecondoIntermedio
public import Cubical.Polytope.ConnettivitaRidgeRiduzione
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/PolytopeEulerLowerFaces.lean -/







@[expose] public section

/-!
# Highest faces and the actual lower vertex figure

A face has highest vertex v exactly when every vertex of
its radial slice has height below v. The converse is proved by applying
the actual local-to-global linear maximum theorem to the face polytope.
The resulting bijection counts precisely the original faces, not assumed
abstract lower links.
-/

noncomputable section

namespace Papers.PolytopeEulerLowerFaces

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeVertexCone Papers.PolytopeEulerRadialFigure
open Papers.PolytopeFaceCounting Papers.PolytopeBalinski
open scoped BigOperators Classical

variable {n : ℕ} {P : ConvexPolytope n} {v : E n}

theorem step_facePolytope_to_original (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F) {x y : E n}
    (hxy : GeneralVertexStep (facePolytope P hF) x y) :
    GeneralVertexStep P x y := by
  obtain ⟨hy,hne,A,hA,hdim,hxA,hyA⟩ := hxy
  have hyP : y ∈ P.vertices := (Finset.mem_filter.mp hy).1
  exact ⟨hyP,hne,A,isFace_of_facePolytope P hF hA,hdim,hxA,hyA⟩

theorem neighborImage_mem_iff (D : DatiFetta P v)
    (F : PositiveVertexStarFace P P.toSet v)
    (y : Papers.PolytopeVertexCone.actualNeighbors P v) :
    (neighborImage (toGaloisData D) D.hv y).val ∈
      ((toGaloisData D).faceEquiv F).carrier ↔ y.val ∈ F.carrier := by
  constructor
  · intro h
    have hsub : (neighborStarFace P D.hv y).carrier ⊆ F.carrier := by
      apply ((toGaloisData D).map_subset_iff _ _).mpr
      rw [neighborImage_face]
      exact Set.singleton_subset_iff.mpr h
    exact hsub (right_mem_segment ℝ _ _)
  · intro hyF
    have hconv : Convex ℝ F.carrier := F.isFace.1.convex (convex_convexHull ℝ _)
    have hsub : (neighborStarFace P D.hv y).carrier ⊆ F.carrier :=
      hconv.segment_subset F.mem_vertex hyF
    have himage := ((toGaloisData D).map_subset_iff _ _).mp hsub
    rw [neighborImage_face] at himage
    exact himage (Set.mem_singleton _)

def TopAt (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ) (v : E n)
    (F : Set (E n)) : Prop :=
  v ∈ F ∧ ∀ w ∈ P.vertices, w ∈ F → w ≠ v → L w < L v

theorem topAt_iff_lower_figure_vertices
    (D : DatiFetta P v) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n)))
    (F : PositiveVertexStarFace P P.toSet v) :
    TopAt P L v F.carrier ↔
      ∀ q : D.politopo.vertices,
        q.val ∈ ((toGaloisData D).faceEquiv F).carrier → L q.val < L v := by
  constructor
  · intro ht q hq
    obtain ⟨y,hyq⟩ := (neighborEquiv (toGaloisData D) D.hv).surjective q
    have hmem : (neighborImage (toGaloisData D) D.hv y).val ∈
        ((toGaloisData D).faceEquiv F).carrier := by
      simpa only [show neighborImage (toGaloisData D) D.hv y = q from hyq] using hq
    have hstep := neighbor_step P v y
    have hylow := ht.2 y.val hstep.1
      ((neighborImage_mem_iff D F y).mp hmem) hstep.2.1.symm
    have hh := (neighborImage_height_lt_iff D L y).mpr hylow
    simpa only [show neighborImage (toGaloisData D) D.hv y = q from hyq] using hh
  · intro hlower
    refine ⟨F.mem_vertex,?_⟩
    intro w hw hwF hwv
    let Q := facePolytope P F.isFace
    have hvQ : v ∈ Q.vertices :=
      Finset.mem_filter.mpr ⟨D.hv,F.mem_vertex⟩
    have hlocal : ∀ y, GeneralVertexStep Q v y → L y ≤ L v := by
      intro y hy
      have hyP := step_facePolytope_to_original P F.isFace hy
      let yy : Papers.PolytopeVertexCone.actualNeighbors P v :=
        ⟨y,Finset.mem_filter.mpr ⟨hyP.1,hyP⟩⟩
      have hyF : y ∈ F.carrier := (Finset.mem_filter.mp hy.1).2
      have himage := (neighborImage_mem_iff D F yy).mpr hyF
      have hlow := hlower (neighborImage (toGaloisData D) D.hv yy) himage
      exact ((neighborImage_height_lt_iff D L yy).mp hlow).le
    have hwQ : w ∈ Q.vertices := Finset.mem_filter.mpr ⟨hw,hwF⟩
    have hmax := maximum_on_vertices_of_neighbors Q L hvQ hlocal w hwQ
    rcases lt_or_eq_of_le hmax with hlt | heq
    · exact hlt
    · exact (hwv (hinj hw D.hv heq)).elim

abbrev TopFace (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (v : E n) (k : ℕ) :=
  {F : Face P k // TopAt P L v F.val.carrier}

def topFaceStar (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (v : E n) (k : ℕ) (F : TopFace P L v (k + 1)) :
    PositiveVertexStarFace P P.toSet v where
  carrier := F.val.val.carrier
  isFace := F.val.val.isFace
  subset_base := face_subset_toSet P F.val.val.isFace
  mem_vertex := F.property.1
  dim_pos := by rw [F.val.property]; omega

def topFaceFigure (D : DatiFetta P v) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n)))
    (k : ℕ) (F : TopFace P L v (k + 1)) :
    FaceIn D.politopo k {q | L q.val < L v} := by
  let S := topFaceStar P L v k F
  let G := (toGaloisData D).faceEquiv S
  have hdim : faceDim G.carrier = k := by
    have h := (toGaloisData D).map_dim S
    change faceDim G.carrier + 1 = faceDim F.val.val.carrier at h
    rw [F.val.property] at h
    omega
  refine ⟨⟨G,hdim⟩,?_⟩
  exact (topAt_iff_lower_figure_vertices D L hinj S).mp F.property

def figureTopFace (D : DatiFetta P v) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n)))
    (k : ℕ) (G : FaceIn D.politopo k {q | L q.val < L v}) :
    TopFace P L v (k + 1) := by
  let S := (toGaloisData D).faceEquiv.symm G.val.val
  have himage : (toGaloisData D).faceEquiv S = G.val.val :=
    (toGaloisData D).faceEquiv.apply_symm_apply _
  have hdim : faceDim S.carrier = k + 1 := by
    have h := (toGaloisData D).map_dim S
    rw [himage,G.val.property] at h
    omega
  refine ⟨⟨⟨S.carrier,S.isFace⟩,hdim⟩,?_⟩
  apply (topAt_iff_lower_figure_vertices D L hinj S).mpr
  intro q hq
  rw [himage] at hq
  exact G.property q hq

def topFaceFigureEquiv (D : DatiFetta P v) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n))) (k : ℕ) :
    TopFace P L v (k + 1) ≃ FaceIn D.politopo k {q | L q.val < L v} where
  toFun := topFaceFigure D L hinj k
  invFun := figureTopFace D L hinj k
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    apply PolytopeFace.ext
    change ((toGaloisData D).faceEquiv.symm
      ((toGaloisData D).faceEquiv (topFaceStar P L v k F))).carrier =
        F.val.val.carrier
    rw [Equiv.symm_apply_apply]
    rfl
  right_inv G := by
    apply Subtype.ext
    apply Subtype.ext
    apply PolytopeFace.ext
    change ((toGaloisData D).faceEquiv
      ((toGaloisData D).faceEquiv.symm G.val.val)).carrier = G.val.val.carrier
    rw [Equiv.apply_symm_apply]

def topTwoFaceLowerEdgeEquiv (D : DatiFetta P v) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n))) :
    TopFace P L v 2 ≃
      ((vertexGraph D.politopo).induce {q : D.politopo.vertices | L q.val < L v}).edgeSet :=
  (topFaceFigureEquiv D L hinj 1).trans
    (inducedEdgeFaceEquiv D.politopo {q | L q.val < L v}).symm

theorem top_two_face_card_eq_lower_edge_card
    (D : DatiFetta P v) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n))) :
    Nat.card (TopFace P L v 2) =
      Nat.card ((vertexGraph D.politopo).induce
        {q : D.politopo.vertices | L q.val < L v}).edgeSet :=
  Nat.card_congr (topTwoFaceLowerEdgeEquiv D L hinj)


theorem exists_topAt (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n)))
    {k : ℕ} (F : Face P k) :
    ∃ v : P.vertices, TopAt P L v.val F.val.carrier := by
  let X := P.vertices.filter fun x => x ∈ F.val.carrier
  have hX : X.Nonempty := by
    obtain ⟨v,hv,hvF⟩ := face_has_vertex P F.val.isFace
    exact ⟨v,Finset.mem_filter.mpr ⟨hv,hvF⟩⟩
  obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image X L hX
  have hvP := (Finset.mem_filter.mp hv).1
  have hvF := (Finset.mem_filter.mp hv).2
  refine ⟨⟨v,hvP⟩,hvF,?_⟩
  intro w hw hwF hwv
  have hle := hmax w (Finset.mem_filter.mpr ⟨hw,hwF⟩)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact (hwv (hinj hw hvP heq)).elim

theorem topAt_unique (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    {F : Set (E n)} {v w : P.vertices}
    (hv : TopAt P L v.val F) (hw : TopAt P L w.val F) : v = w := by
  by_contra hne
  have hvw : v.val ≠ w.val := fun heq => hne (Subtype.ext heq)
  have h1 := hv.2 w.val w.property hw.1 hvw.symm
  have h2 := hw.2 v.val v.property hv.1 hvw
  exact lt_asymm h1 h2

def topFacePartition (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n))) (k : ℕ) :
    (Σ v : P.vertices, TopFace P L v.val k) ≃ Face P k := by
  apply Equiv.ofBijective (fun z => z.2.val)
  constructor
  · rintro ⟨v,F⟩ ⟨w,G⟩ hFG
    change F.val = G.val at hFG
    have hw : TopAt P L w.val F.val.val.carrier := by
      rw [hFG]
      exact G.property
    have hvw : v = w := topAt_unique P L F.property hw
    subst w
    have hface : F = G := Subtype.ext hFG
    cases hface
    rfl
  · intro F
    obtain ⟨v,hv⟩ := exists_topAt P L hinj F
    exact ⟨⟨v,⟨F,hv⟩⟩,rfl⟩

theorem sum_top_face_card (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n))) (k : ℕ) :
    (∑ v : P.vertices, Nat.card (TopFace P L v.val k)) = Nat.card (Face P k) := by
  classical
  letI : Fintype (Face P k) := Fintype.ofFinite _
  letI : ∀ v : P.vertices, Fintype (TopFace P L v.val k) :=
    fun _ => Fintype.ofFinite _
  have hh := Fintype.card_congr (topFacePartition P L hinj k)
  simpa only [Fintype.card_sigma, Nat.card_eq_fintype_card] using hh

end Papers.PolytopeEulerLowerFaces

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/FiniteGraphHeightCount.lean -/









@[expose] public section

/-!
# Finite height counts on an ordinary graph

Each edge is charged to its higher endpoint under an
injective height. The charge decomposition and the two-regular edge count
are proved by explicit finite bijections and the degree-sum formula.
-/

noncomputable section

namespace Papers.FiniteGraphHeightCount

open SimpleGraph
open scoped BigOperators Classical

variable {V : Type*}

abbrev LowerNeighbor (G : SimpleGraph V) (φ : V → ℝ) (v : V) :=
  {w : V // G.Adj v w ∧ φ w < φ v}

def lowerEdgeMap (G : SimpleGraph V) (φ : V → ℝ) :
    (Σ v, LowerNeighbor G φ v) → G.edgeSet :=
  fun e => ⟨s(e.1,e.2.val),e.2.property.1⟩

theorem lowerEdgeMap_injective (G : SimpleGraph V) (φ : V → ℝ) :
    Function.Injective (lowerEdgeMap G φ) := by
  rintro ⟨v,⟨w,hvw,hwv⟩⟩ ⟨x,⟨y,hxy,hyx⟩⟩ heq
  have hp : s(v,w) = s(x,y) := congrArg Subtype.val heq
  rcases Sym2.eq_iff.mp hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact (lt_asymm hwv hyx).elim

theorem lowerEdgeMap_surjective (G : SimpleGraph V) (φ : V → ℝ)
    (hinj : Function.Injective φ) :
    Function.Surjective (lowerEdgeMap G φ) := by
  intro e
  let a := e.val.out.1
  let b := e.val.out.2
  have hab : G.Adj a b := by
    change s(e.val.out.1,e.val.out.2) ∈ G.edgeSet
    rw [Sym2.mk_fst_out_snd_out]
    exact e.property
  rcases lt_trichotomy (φ a) (φ b) with hlt | heq | hgt
  · refine ⟨⟨b,⟨a,hab.symm,hlt⟩⟩,?_⟩
    apply Subtype.ext
    change s(b,a) = e.val
    exact Sym2.eq_swap.trans (Sym2.mk_fst_out_snd_out e.val)
  · exact (hab.ne (hinj heq)).elim
  · refine ⟨⟨a,⟨b,hab,hgt⟩⟩,?_⟩
    apply Subtype.ext
    exact Sym2.mk_fst_out_snd_out e.val

def lowerEdgeEquiv (G : SimpleGraph V) (φ : V → ℝ)
    (hinj : Function.Injective φ) :
    (Σ v, LowerNeighbor G φ v) ≃ G.edgeSet :=
  Equiv.ofBijective (lowerEdgeMap G φ)
    ⟨lowerEdgeMap_injective G φ,lowerEdgeMap_surjective G φ hinj⟩

theorem sum_lower_card_eq_edge_card [Fintype V]
    (G : SimpleGraph V) (φ : V → ℝ) (hinj : Function.Injective φ) :
    (∑ v, Nat.card (LowerNeighbor G φ v)) = Nat.card G.edgeSet := by
  classical
  letI : ∀ v, Fintype (LowerNeighbor G φ v) := fun _ => Fintype.ofFinite _
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  have hh := Fintype.card_congr (lowerEdgeEquiv G φ hinj)
  simpa only [Fintype.card_sigma, Nat.card_eq_fintype_card] using hh

theorem two_regular_edge_card [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v = 2) :
    Nat.card G.edgeSet = Nat.card V := by
  classical
  have hh := G.sum_degrees_eq_twice_card_edges
  have htwo : 2 * Fintype.card V = 2 * G.edgeFinset.card := by
    simpa [hdeg, mul_comm] using hh
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  exact Nat.mul_left_cancel (by decide : 0 < 2) htwo.symm

theorem euler_of_local_indices
    [Fintype V] (down topFaces : V → ℕ) (lo hi : V) (hne : lo ≠ hi)
    (hloD : down lo = 0) (hloF : topFaces lo = 0)
    (hhi : down hi = topFaces hi)
    (hregular : ∀ v, v ≠ lo → v ≠ hi → down v = topFaces v + 1) :
    (Fintype.card V : ℤ) - (∑ v, (down v : ℤ)) +
      (∑ v, (topFaces v : ℤ)) = 2 := by
  have hlocal (v : V) :
      (1 : ℤ) - down v + topFaces v =
        (if v = lo then 1 else 0) + (if v = hi then 1 else 0) := by
    by_cases hvlo : v = lo
    · subst v
      simp [hloD,hloF,hne]
    · by_cases hvhi : v = hi
      · subst v
        simp only [hvlo,if_false,if_true]
        omega
      · have hh := hregular v hvlo hvhi
        simp only [hvlo,hvhi,if_false]
        omega
  have hs : (∑ v, ((1 : ℤ) - down v + topFaces v)) = 2 := by
    calc
      _ = ∑ v, ((if v = lo then 1 else 0) + (if v = hi then 1 else 0)) :=
        Finset.sum_congr rfl (fun v _ => hlocal v)
      _ = 2 := by simp [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  simpa using hs

end Papers.FiniteGraphHeightCount

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/PolytopeEulerLocal.lean -/









@[expose] public section

/-!
# Actual local Euler indices in intrinsic dimension three

Interior height levels give proper nonempty connected
subgraphs of the actual polygonal vertex figure. The minimum and maximum
are treated separately. No local Euler equation is assumed.
-/

noncomputable section

namespace Papers.PolytopeEulerLocal

open Set Module SimpleGraph
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeVertexCone Papers.PolytopeBalinski
open Papers.PolytopeFaceCounting Papers.PolytopeEulerRadialFigure
open Papers.PolytopeEulerLowerFaces Papers.FiniteGraphHeightCount
open Papers.RationalityTen.PolygonMorseGraph
open scoped Classical

variable {n : ℕ}

abbrev Low (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ) (v : P.vertices) :=
  LowerNeighbor (vertexGraph P) (fun w : P.vertices => L w.val) v

def lowActualEquiv (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ) (v : P.vertices) :
    Low P L v ≃
      {y : Papers.PolytopeVertexCone.actualNeighbors P v.val // L y.val < L v.val} where
  toFun w := ⟨⟨w.val.val,Finset.mem_filter.mpr
    ⟨w.val.property,w.property.1⟩⟩,w.property.2⟩
  invFun y := ⟨⟨y.val.val,(Finset.mem_filter.mp y.val.property).1⟩,
    (Finset.mem_filter.mp y.val.property).2,y.property⟩
  left_inv w := by cases w; rfl
  right_inv y := by cases y; rfl

def lowFigureEquiv (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (v : P.vertices) (D : DatiFetta P v.val) :
    Low P L v ≃ {q : D.politopo.vertices // L q.val < L v.val} :=
  (lowActualEquiv P L v).trans (lowerNeighborEquiv D L)

def wholeFaceGraphIso (Q : ConvexPolytope n) :
    vertexGraph Q ≃g twoFaceVertexGraph Q Q.toSet where
  toEquiv :=
    { toFun := fun q => ⟨q,Papers.PolytopeBasicExtreme.vertex_mem_body Q q.property⟩
      invFun := fun q => q.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

theorem polygon_vertex_degree_two (Q : ConvexPolytope n) (hdim : Q.dim = 2)
    (q : Q.vertices) : (vertexGraph Q).degree q = 2 := by
  have hh := twoFaceVertexGraph_degree_two Q Q.toSet (toSet_isFace Q)
    (show faceDim Q.toSet = 2 from hdim) (wholeFaceGraphIso Q q)
  rw [(wholeFaceGraphIso Q).degree_eq q] at hh
  exact hh

theorem lower_figure_connected (P : ConvexPolytope n)
    (L : E n →L[ℝ] ℝ) (v : P.vertices) (D : DatiFetta P v.val)
    (hlow : Nonempty (Low P L v)) :
    ((vertexGraph D.politopo).induce
      {q : D.politopo.vertices | L q.val < L v.val}).Connected := by
  obtain ⟨w⟩ := hlow
  let q := lowFigureEquiv P L v D w
  have hpos : ∃ z ∈ D.politopo.vertices, -L v.val < (-L) z :=
    ⟨q.val.val,q.val.property,by simpa using q.property⟩
  have hh := positive_vertexGraph_connected D.politopo (-L) (-L v.val) hpos
  have hs : {z : D.politopo.vertices | -L v.val < (-L) z.val} =
      {z : D.politopo.vertices | L z.val < L v.val} := by
    ext z
    simp
  change ((vertexGraph D.politopo).induce
    {z : D.politopo.vertices | -L v.val < (-L) z.val}).Connected at hh
  exact hs ▸ hh

theorem regular_local_count (P : ConvexPolytope n) (hdim : P.dim = 3)
    (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n)))
    (v : P.vertices) (D : DatiFetta P v.val)
    (hlow : Nonempty (Low P L v))
    (hhigh : ∃ y : Papers.PolytopeVertexCone.actualNeighbors P v.val,
      L v.val < L y.val) :
    Nat.card (Low P L v) = Nat.card (TopFace P L v.val 2) + 1 := by
  let Q := D.politopo
  let S : Set Q.vertices := {q | L q.val < L v.val}
  have hQdim : Q.dim = 2 := figure_dim_two D hdim
  have hdeg : ∀ q, (vertexGraph Q).degree q ≤ 2 := fun q =>
    (polygon_vertex_degree_two Q hQdim q).le
  have hproper : ∃ q : Q.vertices, q ∉ S := by
    obtain ⟨y,hy⟩ := hhigh
    refine ⟨neighborImage (toGaloisData D) D.hv y,?_⟩
    exact not_lt_of_ge ((neighborImage_height_gt_iff D L y).mpr hy).le
  have hc := proper_connected_induce_edge_count (vertexGraph Q)
    (vertexGraph_connected Q) hdeg S hproper
    (lower_figure_connected P L v D hlow)
  have hv := Nat.card_congr (lowFigureEquiv P L v D)
  have hf := top_two_face_card_eq_lower_edge_card D L hinj
  change Nat.card (Low P L v) = Nat.card S at hv
  change Nat.card (TopFace P L v.val 2) =
    Nat.card ((vertexGraph Q).induce S).edgeSet at hf
  omega

theorem minimum_local_count (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (v : P.vertices) (hmin : ∀ w ∈ P.vertices, L v.val ≤ L w) :
    Nat.card (Low P L v) = 0 ∧ Nat.card (TopFace P L v.val 2) = 0 := by
  have hempty : IsEmpty (Low P L v) :=
    ⟨fun w => not_lt_of_ge (hmin w.val.val w.val.property) w.property.2⟩
  have hfempty : IsEmpty (TopFace P L v.val 2) := by
    refine ⟨fun F => ?_⟩
    obtain ⟨w,hw,hwF⟩ := DatiFetta.esiste_vertice_altro
      F.val.val.isFace F.property.1 (by rw [F.val.property]; omega)
    have hwP := Finset.mem_of_mem_erase hw
    have hwv := Finset.ne_of_mem_erase hw
    exact not_lt_of_ge (hmin w hwP) (F.property.2 w hwP hwF hwv)
  letI := hempty
  letI := hfempty
  simp

theorem maximum_local_count (P : ConvexPolytope n) (hdim : P.dim = 3)
    (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n)))
    (v : P.vertices) (D : DatiFetta P v.val)
    (hmax : ∀ w ∈ P.vertices, L w ≤ L v.val) :
    Nat.card (Low P L v) = Nat.card (TopFace P L v.val 2) := by
  let Q := D.politopo
  let S : Set Q.vertices := {q | L q.val < L v.val}
  have hs : S = Set.univ := by
    ext q
    simp only [Set.mem_univ, iff_true]
    obtain ⟨y,hyq⟩ := (neighborEquiv (toGaloisData D) D.hv).surjective q
    have hstep := neighbor_step P v.val y
    have hylt : L y.val < L v.val := by
      rcases lt_or_eq_of_le (hmax y.val hstep.1) with hlt | heq
      · exact hlt
      · exact (hstep.2.1 (hinj hstep.1 v.property heq).symm).elim
    have hh := (neighborImage_height_lt_iff D L y).mpr hylt
    change L q.val < L v.val
    simpa only [show neighborImage (toGaloisData D) D.hv y = q from hyq] using hh
  have hv := Nat.card_congr (lowFigureEquiv P L v D)
  have hf := top_two_face_card_eq_lower_edge_card D L hinj
  have hV : Nat.card S = Nat.card Q.vertices := by
    rw [hs]
    exact Nat.card_congr (Equiv.Set.univ Q.vertices)
  have hE : Nat.card ((vertexGraph Q).induce S).edgeSet =
      Nat.card (vertexGraph Q).edgeSet := by
    rw [hs]
    exact Nat.card_congr (SimpleGraph.induceUnivIso (vertexGraph Q)).mapEdgeSet
  change Nat.card (Low P L v) = Nat.card S at hv
  change Nat.card (TopFace P L v.val 2) =
    Nat.card ((vertexGraph Q).induce S).edgeSet at hf
  have hdegree := two_regular_edge_card (vertexGraph Q)
    (polygon_vertex_degree_two Q (figure_dim_two D hdim))
  omega

end Papers.PolytopeEulerLocal

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/FaceIncidenceEuler.lean -/






@[expose] public section

/-!
# Euler's equation in dimension four from local three-dimensional equations

The relations are ordinary incidences between vertices, edges, two-faces,
and facets.  This double-counting lemma supplies no geometric hypotheses:
the vertex-figure and facet Euler equations must be proved for the actual
polytope before it can be applied.
-/

noncomputable section
namespace Papers.FaceIncidenceEuler

open scoped BigOperators Classical

variable {X Y V E R F : Type*}
  [Fintype X] [Fintype Y] [Fintype V] [Fintype E] [Fintype R] [Fintype F]

def rowCount (inc : X → Y → Prop) (x : X) : ℤ :=
  ∑ y, if inc x y then 1 else 0

def colCount (inc : X → Y → Prop) (y : Y) : ℤ :=
  ∑ x, if inc x y then 1 else 0

theorem total_rows_eq_columns (inc : X → Y → Prop) :
    (∑ x, rowCount inc x) = ∑ y, colCount inc y := by
  unfold rowCount colCount
  exact Finset.sum_comm

theorem sum_constant_columns (inc : X → Y → Prop) (k : ℤ)
    (h : ∀ y, colCount inc y = k) :
    (∑ x, rowCount inc x) = k * Fintype.card Y := by
  rw [total_rows_eq_columns]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_comm _ _

theorem euler_four_from_local_three
    (ve : V → E → Prop) (vr : V → R → Prop) (vf : V → F → Prop)
    (er : E → R → Prop) (ef : E → F → Prop) (rf : R → F → Prop)
    (hendpoints : ∀ e, colCount ve e = 2)
    (hridge : ∀ r, rowCount rf r = 2)
    (hpolygon : ∀ r, colCount vr r = colCount er r)
    (hedgeFigure : ∀ e, rowCount er e = rowCount ef e)
    (hvertexEuler : ∀ v, rowCount ve v - rowCount vr v + rowCount vf v = 2)
    (hfacetEuler : ∀ f, colCount vf f - colCount ef f + colCount rf f = 2) :
    (Fintype.card V : ℤ) - Fintype.card E +
      Fintype.card R - Fintype.card F = 0 := by
  have he := sum_constant_columns ve 2 hendpoints
  have hr : (∑ f, colCount rf f) = 2 * Fintype.card R := by
    rw [← total_rows_eq_columns]
    simp only [hridge, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_comm _ _
  have h01 : (∑ v, rowCount vr v) = ∑ e, rowCount ef e := by
    rw [total_rows_eq_columns vr]
    calc
      (∑ r, colCount vr r) = ∑ r, colCount er r :=
        Finset.sum_congr rfl (fun r _ => hpolygon r)
      _ = ∑ e, rowCount er e := (total_rows_eq_columns er).symm
      _ = ∑ e, rowCount ef e :=
        Finset.sum_congr rfl (fun e _ => hedgeFigure e)
  have hv : (∑ v, rowCount ve v) - (∑ v, rowCount vr v) +
      (∑ v, rowCount vf v) = 2 * Fintype.card V := by
    calc
      _ = ∑ v, (rowCount ve v - rowCount vr v + rowCount vf v) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = ∑ _v : V, (2 : ℤ) :=
        Finset.sum_congr rfl (fun v _ => hvertexEuler v)
      _ = _ := by simp [mul_comm]
  have hf : (∑ f, colCount vf f) - (∑ f, colCount ef f) +
      (∑ f, colCount rf f) = 2 * Fintype.card F := by
    calc
      _ = ∑ f, (colCount vf f - colCount ef f + colCount rf f) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = ∑ _f : F, (2 : ℤ) :=
        Finset.sum_congr rfl (fun f _ => hfacetEuler f)
      _ = _ := by simp [mul_comm]
  rw [he, h01] at hv
  rw [← total_rows_eq_columns vf, ← total_rows_eq_columns ef, hr] at hf
  omega

/-- In dimension three, these are the numerical consequences used by the
small-facet template enumeration once Euler and the genuine incidence
bounds have been supplied. -/
theorem three_dimensional_facet_bound
    {n e f : ℤ} (heuler : n - e + f = 2)
    (hfaceDegree : 3 * f ≤ 2 * e) :
    f ≤ 2 * n - 4 := by
  omega

theorem short_three_dimensional_triangle_bound
    {n e f : ℤ} (hn : n ≤ 7) (heuler : n - e + f = 2)
    (hvertexDegree : 3 * n ≤ 2 * e) :
    2 * e < 4 * f := by
  omega

theorem exists_triangular_face_of_counts
    {I : Type*} [Fintype I] (corners : I → ℕ)
    {n e f : ℤ} (hf : (Fintype.card I : ℤ) = f) (hn : n ≤ 7)
    (heuler : n - e + f = 2) (hvertexDegree : 3 * n ≤ 2 * e)
    (hinc : (∑ i, (corners i : ℤ)) = 2 * e)
    (hmin : ∀ i, 3 ≤ corners i) :
    ∃ i, corners i = 3 := by
  by_contra h
  have hfour : ∀ i, (4 : ℤ) ≤ corners i := by
    intro i
    have hne : corners i ≠ 3 := fun hi => h ⟨i, hi⟩
    have hm := hmin i
    omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfour i)
  have hbound := short_three_dimensional_triangle_bound hn heuler hvertexDegree
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hf, hinc] at hsum
  omega

end Papers.FaceIncidenceEuler

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/RationalityTenMorseEulerCounts.lean -/







@[expose] public section

/-!
# Generic linear heights and finite Morse double counting

The first theorem constructs a linear height separating
any finite set of points. The second derives the ordinary three-dimensional
Euler count from the explicitly stated local lower-link counts. Geometric
identification of these counts with actual vertex figures is a separate
dependency, not silently assumed here.
-/

noncomputable section

namespace Papers.RationalityTen.MorseEulerCounts

open scoped BigOperators Classical
open Papers.FaceIncidenceEuler

theorem exists_linear_height_injective
    {W : Type*} [AddCommGroup W] [Module ℝ W] (s : Finset W) :
    ∃ l : W →ₗ[ℝ] ℝ, Set.InjOn l (s : Set W) := by
  classical
  let I := {p : s × s // p.1 ≠ p.2}
  let d : I → W := fun i => ((i.val.1 : s) : W) - ((i.val.2 : s) : W)
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    apply sub_ne_zero.mpr
    intro heq
    exact i.property (Subtype.ext heq)
  obtain ⟨l, hl⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ) d hd
  refine ⟨l, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  let i : I := ⟨(⟨x,hx⟩, ⟨y,hy⟩), fun heq => hne (congrArg Subtype.val heq)⟩
  apply hl i
  change l (x - y) = 0
  rw [map_sub, hxy, sub_self]

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

/-- Charge each edge and each polygonal face to its unique highest vertex.
At the minimum both charged counts vanish; at the maximum they agree;
every other lower link is a nonempty proper polygonal path. -/
theorem euler_three_from_lower_links
    (edgeTop : E → V) (faceTop : F → V) (lo hi : V)
    (hne : lo ≠ hi)
    (hloE : rowCount (fun v e => edgeTop e = v) lo = 0)
    (hloF : rowCount (fun v f => faceTop f = v) lo = 0)
    (hhi : rowCount (fun v e => edgeTop e = v) hi =
      rowCount (fun v f => faceTop f = v) hi)
    (hregular : ∀ v, v ≠ lo → v ≠ hi →
      rowCount (fun v e => edgeTop e = v) v =
        rowCount (fun v f => faceTop f = v) v + 1) :
    (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F = 2 := by
  let eCount := rowCount (fun v e => edgeTop e = v)
  let fCount := rowCount (fun v f => faceTop f = v)
  have heTotal : (∑ v, eCount v) = (Fintype.card E : ℤ) := by
    have hh := sum_constant_columns (fun v e => edgeTop e = v) 1
      (by intro e; simp [colCount])
    simpa [eCount] using hh
  have hfTotal : (∑ v, fCount v) = (Fintype.card F : ℤ) := by
    have hh := sum_constant_columns (fun v f => faceTop f = v) 1
      (by intro f; simp [colCount])
    simpa [fCount] using hh
  have hlocal (v : V) :
      (1 : ℤ) - eCount v + fCount v =
        (if v = lo then 1 else 0) + (if v = hi then 1 else 0) := by
    by_cases hvlo : v = lo
    · subst v
      simpa [eCount, fCount, hloE, hloF, hne]
    · by_cases hvhi : v = hi
      · subst v
        have hh : eCount hi = fCount hi := hhi
        simp only [hvlo, if_false, if_true]
        omega
      · have hh : eCount v = fCount v + 1 := hregular v hvlo hvhi
        simp only [hvlo, hvhi, if_false]
        omega
  have hsum : (∑ v, (1 - eCount v + fCount v)) = (2 : ℤ) := by
    calc
      _ = ∑ v, ((if v = lo then 1 else 0) + (if v = hi then 1 else 0)) :=
        Finset.sum_congr rfl (fun v _ => hlocal v)
      _ = 2 := by simp [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, heTotal, hfTotal] at hsum
  simpa using hsum

end Papers.RationalityTen.MorseEulerCounts

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/PolytopeEulerThree.lean -/







@[expose] public section

/-!
# Euler's formula for every actual three-dimensional convex polytope

The sole geometric hypothesis is the intrinsic dimension
P.dim = 3. Vertices are the actual extreme vertices of P, and the two face
types are actual exposed subsets with affine dimensions one and two.
The proof derives every local index from the radial vertex figure.
-/

noncomputable section

namespace Papers.PolytopeEulerThree

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeVertexCone Papers.PolytopeBalinski
open Papers.PolytopeFaceCounting Papers.PolytopeEulerLowerFaces
open Papers.PolytopeEulerLocal Papers.FiniteGraphHeightCount
open Papers.RationalityTen.MorseEulerCounts
open scoped BigOperators Classical

variable {n : ℕ}

theorem euler_three (P : ConvexPolytope n) (hdim : P.dim = 3) :
    (P.vertices.card : ℤ) - Nat.card (Face P 1) + Nat.card (Face P 2) = 2 := by
  obtain ⟨l,hl⟩ := exists_linear_height_injective P.vertices
  let L : E n →L[ℝ] ℝ := l.toContinuousLinearMap
  have hinj : Set.InjOn L (P.vertices : Set (E n)) := hl
  have hinjV : Function.Injective (fun v : P.vertices => L v.val) := by
    intro v w hvw
    exact Subtype.ext (hinj v.property w.property hvw)
  have hpos : 1 ≤ faceDim P.toSet := by
    change 1 ≤ P.dim
    omega
  let D (v : P.vertices) : DatiFetta P v.val :=
    Classical.choice (esiste_datiFetta P v.property hpos)
  obtain ⟨x,hx,hxmin⟩ := Finset.exists_max_image P.vertices (-L) P.vertices_nonempty
  obtain ⟨y,hy,hymax⟩ := Finset.exists_max_image P.vertices L P.vertices_nonempty
  let lo : P.vertices := ⟨x,hx⟩
  let hi : P.vertices := ⟨y,hy⟩
  have hmin : ∀ w ∈ P.vertices, L lo.val ≤ L w := by
    intro w hw
    simpa only [ContinuousLinearMap.neg_apply,neg_le_neg_iff] using hxmin w hw
  have hmax : ∀ w ∈ P.vertices, L w ≤ L hi.val := hymax
  have hne : lo ≠ hi := by
    intro hlohi
    obtain ⟨w,hw⟩ := (D lo).hW
    have hwP := Finset.mem_of_mem_erase hw
    have hwlo := Finset.ne_of_mem_erase hw
    have hle : L w ≤ L lo.val := by simpa only [hlohi] using hmax w hwP
    have heq : L w = L lo.val := le_antisymm hle (hmin w hwP)
    exact hwlo (hinj hwP lo.property heq)
  let down : P.vertices → ℕ := fun v => Nat.card (Low P L v)
  let tops : P.vertices → ℕ := fun v => Nat.card (TopFace P L v.val 2)
  have hminimum : down lo = 0 ∧ tops lo = 0 :=
    minimum_local_count P L lo hmin
  have hmaximum : down hi = tops hi :=
    maximum_local_count P hdim L hinj hi (D hi) hmax
  have hregular : ∀ v, v ≠ lo → v ≠ hi → down v = tops v + 1 := by
    intro v hvlo hvhi
    have hlower : L lo.val < L v.val := by
      rcases lt_or_eq_of_le (hmin v.val v.property) with hlt | heq
      · exact hlt
      · exact (hvlo (Subtype.ext (hinj lo.property v.property heq).symm)).elim
    have hupper : L v.val < L hi.val := by
      rcases lt_or_eq_of_le (hmax v.val v.property) with hlt | heq
      · exact hlt
      · exact (hvhi (Subtype.ext (hinj v.property hi.property heq))).elim
    have hneg : (-L) v.val < (-L) lo.val := by simpa using hlower
    obtain ⟨w,hw,hwL⟩ := exists_improving_neighbor P (-L) v.property lo.property hneg
    have hlow : Nonempty (Low P L v) :=
      ⟨⟨⟨w,hw.1⟩,hw,by simpa using hwL⟩⟩
    obtain ⟨z,hz,hzL⟩ := exists_improving_neighbor P L v.property hi.property hupper
    have hhigh : ∃ z : Papers.PolytopeVertexCone.actualNeighbors P v.val,
        L v.val < L z.val :=
      ⟨⟨z,Finset.mem_filter.mpr ⟨hz.1,hz⟩⟩,hzL⟩
    exact regular_local_count P hdim L hinj v (D v) hlow hhigh
  have heTotalNat :
      (∑ v : P.vertices, down v) = Nat.card (vertexGraph P).edgeSet :=
    sum_lower_card_eq_edge_card (vertexGraph P) (fun v : P.vertices => L v.val) hinjV
  have hfTotalNat :
      (∑ v : P.vertices, tops v) = Nat.card (Face P 2) :=
    sum_top_face_card P L hinj 2
  have heTotal : (∑ v : P.vertices, (down v : ℤ)) =
      (Nat.card (vertexGraph P).edgeSet : ℤ) := by
    simpa only [Nat.cast_sum] using congrArg (fun z : ℕ => (z : ℤ)) heTotalNat
  have hfTotal : (∑ v : P.vertices, (tops v : ℤ)) =
      (Nat.card (Face P 2) : ℤ) := by
    simpa only [Nat.cast_sum] using congrArg (fun z : ℕ => (z : ℤ)) hfTotalNat
  have heuler := euler_of_local_indices down tops lo hi hne
    hminimum.1 hminimum.2 hmaximum hregular
  rw [heTotal,hfTotal,graph_edge_card_eq_one_face_card P] at heuler
  simpa only [Fintype.card_coe] using heuler

theorem vertices_add_faces_eq_edges_add_two
    (P : ConvexPolytope n) (hdim : P.dim = 3) :
    P.vertices.card + Nat.card (Face P 2) = Nat.card (Face P 1) + 2 := by
  have hh := euler_three P hdim
  omega

end Papers.PolytopeEulerThree

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/PolytopeIncidenceCounting.lean -/







@[expose] public section

/-!
# Actual incidence dictionaries for Euler counting

All incidence types use membership or inclusion of actual
exposed faces. Every finite equivalence is built from the face polytope or
the proved vertex-figure correspondence. No abstract Euler or manifold
assumption occurs in these definitions.
-/

noncomputable section

namespace Papers.PolytopeIncidenceCounting

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeFaceCounting Papers.PolytopeEulerLocal
open Papers.PolytopeBalinski Papers.FiniteGraphHeightCount
open scoped Classical BigOperators

variable {n : ℕ}

abbrev VerticesOn (P : ConvexPolytope n) (A : Set (E n)) :=
  {v : P.vertices // v.val ∈ A}

abbrev FaceBelow (P : ConvexPolytope n) (A : Set (E n)) (k : ℕ) :=
  {F : Face P k // F.val.carrier ⊆ A}

abbrev Coface (P : ConvexPolytope n) (A : Set (E n)) (k : ℕ) :=
  {F : Face P k // A ⊆ F.val.carrier}

abbrev IncidentFace (P : ConvexPolytope n) (v : E n) (k : ℕ) :=
  {F : Face P k // v ∈ F.val.carrier}

def faceVerticesEquiv (P : ConvexPolytope n) {A : Set (E n)}
    (hA : P.IsFace A) : VerticesOn P A ≃ (facePolytope P hA).vertices where
  toFun v := ⟨v.val.val,Finset.mem_filter.mpr ⟨v.val.property,v.property⟩⟩
  invFun v := ⟨⟨v.val,(Finset.mem_filter.mp v.property).1⟩,
    (Finset.mem_filter.mp v.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def faceBelowEquiv (P : ConvexPolytope n) {A : Set (E n)}
    (hA : P.IsFace A) (k : ℕ) :
    FaceBelow P A k ≃ Face (facePolytope P hA) k where
  toFun F := ⟨⟨F.val.val.carrier,
    facePolytope_isFace_of P hA F.val.val.isFace F.property⟩,F.val.property⟩
  invFun F := ⟨⟨⟨F.val.carrier,
    isFace_of_facePolytope P hA F.val.isFace⟩,F.property⟩,by
      have h := face_subset_toSet (facePolytope P hA) F.val.isFace
      simpa only [facePolytope_toSet] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl

def zeroFace (P : ConvexPolytope n) (v : P.vertices) : Face P 0 :=
  ⟨⟨{v.val},vertex_isFace P v.property⟩,faceDim_singleton _⟩

def zeroFaceEquiv (P : ConvexPolytope n) : P.vertices ≃ Face P 0 := by
  apply Equiv.ofBijective (zeroFace P)
  constructor
  · intro v w h
    apply Subtype.ext
    exact Set.singleton_injective (congrArg (fun F => F.val.carrier) h)
  · intro F
    obtain ⟨v,hv,hF⟩ := actual_zeroFace_is_vertex P F.val.carrier
      F.val.isFace F.property
    refine ⟨⟨v,hv⟩,?_⟩
    apply Subtype.ext
    apply PolytopeFace.ext
    exact hF.symm

def incidentStar (P : ConvexPolytope n) (v : E n) (k : ℕ)
    (F : IncidentFace P v (k + 1)) :
    PositiveVertexStarFace P P.toSet v where
  carrier := F.val.val.carrier
  isFace := F.val.val.isFace
  subset_base := face_subset_toSet P F.val.val.isFace
  mem_vertex := F.property
  dim_pos := by rw [F.val.property]; omega

def incidentFigureEquiv {P : ConvexPolytope n} {v : E n}
    (D : VertexFigureGaloisData P P.toSet v) (k : ℕ) :
    IncidentFace P v (k + 1) ≃ Face D.figure k where
  toFun F := ⟨D.faceEquiv (incidentStar P v k F),by
    have h := D.map_dim (incidentStar P v k F)
    change faceDim (D.faceEquiv (incidentStar P v k F)).carrier + 1 =
      faceDim F.val.val.carrier at h
    rw [F.val.property] at h
    omega⟩
  invFun G := by
    let S := D.faceEquiv.symm G.val
    have himage : D.faceEquiv S = G.val := D.faceEquiv.apply_symm_apply _
    have hd : faceDim S.carrier = k + 1 := by
      have h := D.map_dim S
      rw [himage,G.property] at h
      exact h.symm
    exact ⟨⟨⟨S.carrier,S.isFace⟩,hd⟩,S.mem_vertex⟩
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    apply PolytopeFace.ext
    exact congrArg PositiveVertexStarFace.carrier
      (D.faceEquiv.symm_apply_apply (incidentStar P v k F))
  right_inv G := by
    apply Subtype.ext
    apply PolytopeFace.ext
    exact congrArg PolytopeFace.carrier (D.faceEquiv.apply_symm_apply G.val)

@[simp] theorem incidentFigure_carrier {P : ConvexPolytope n} {v : E n}
    (D : VertexFigureGaloisData P P.toSet v) (k : ℕ)
    (F : IncidentFace P v (k + 1)) :
    ((incidentFigureEquiv D k) F).val.carrier =
      (D.faceEquiv (incidentStar P v k F)).carrier := rfl

/-- A coface interval above an edge becomes an incidence star at one
vertex of the first vertex figure. -/
def cofaceFigureEquiv {P : ConvexPolytope n} {v : E n}
    (D : VertexFigureGaloisData P P.toSet v)
    (A : PositiveVertexStarFace P P.toSet v) (k : ℕ) :
    Coface P A.carrier (k + 1) ≃
      Coface D.figure (D.faceEquiv A).carrier k where
  toFun F := by
    let I : IncidentFace P v (k + 1) :=
      ⟨F.val,F.property A.mem_vertex⟩
    refine ⟨incidentFigureEquiv D k I,?_⟩
    exact (D.map_subset_iff A (incidentStar P v k I)).mp F.property
  invFun G := by
    let I := (incidentFigureEquiv D k).symm G.val
    refine ⟨I.val,?_⟩
    have h : D.faceEquiv (incidentStar P v k I) = G.val.val := by
      exact congrArg Subtype.val ((incidentFigureEquiv D k).apply_symm_apply G.val)
    apply (D.map_subset_iff A (incidentStar P v k I)).mpr
    simpa only [h] using G.property
  left_inv F := by
    apply Subtype.ext
    change ((incidentFigureEquiv D k).symm
      ((incidentFigureEquiv D k) (⟨F.val,F.property A.mem_vertex⟩ : IncidentFace P v (k+1)))).val = F.val
    exact congrArg Subtype.val ((incidentFigureEquiv D k).symm_apply_apply
      (⟨F.val,F.property A.mem_vertex⟩ : IncidentFace P v (k + 1)))
  right_inv G := Subtype.ext ((incidentFigureEquiv D k).apply_symm_apply G.val)

def singletonCofaceEquiv (P : ConvexPolytope n) (v : E n) (k : ℕ) :
    Coface P ({v} : Set (E n)) k ≃ IncidentFace P v k where
  toFun F := ⟨F.val,F.property (Set.mem_singleton v)⟩
  invFun F := ⟨F.val,Set.singleton_subset_iff.mpr F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_eq_two_of_two {T : Type*} (a b : T) (hab : a ≠ b)
    (hcover : ∀ x : T, x = a ∨ x = b) : Nat.card T = 2 := by
  let f : Bool → T := fun t => if t then a else b
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      cases x <;> cases y <;> simp_all [f]
    · intro x
      rcases hcover x with h | h
      · exact ⟨true,by simpa [f] using h.symm⟩
      · exact ⟨false,by simpa [f] using h.symm⟩
  have h := Nat.card_congr (Equiv.ofBijective f hf)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_bool] using h.symm

theorem one_face_vertex_card (P : ConvexPolytope n) (F : Face P 1) :
    Nat.card (VerticesOn P F.val.carrier) = 2 := by
  obtain ⟨e,rfl⟩ := (edgeFaceEquiv P).surjective F
  let x : VerticesOn P (edgeFace P e).val.carrier :=
    ⟨e.val.out.1,(edgeFace_vertex_iff P e _).mpr (Sym2.out_fst_mem _)⟩
  let y : VerticesOn P (edgeFace P e).val.carrier :=
    ⟨e.val.out.2,(edgeFace_vertex_iff P e _).mpr (Sym2.out_snd_mem _)⟩
  have hxy : x ≠ y := by
    intro h
    have hval := congrArg (fun z => z.val.val) h
    exact (edge_out_adj P e).2.1 hval
  apply card_eq_two_of_two x y hxy
  intro z
  have hz := (edgeFace_vertex_iff P e z.val).mp z.property
  rw [← Sym2.mk_fst_out_snd_out e.val,Sym2.mem_iff] at hz
  rcases hz with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- The genuine diamond property implies that a codimension-two face lies
in exactly two facets, in every intrinsic dimension. -/
theorem ridge_coface_card (P : ConvexPolytope n) (k : ℕ)
    (hdim : P.dim = k + 2) (A : Face P k) :
    Nat.card (Coface P A.val.carrier (k + 1)) = 2 := by
  have hAT : A.val.carrier ⊂ P.toSet := by
    refine (face_subset_toSet P A.val.isFace).ssubset_of_ne ?_
    intro h
    have hd := congrArg faceDim h
    change faceDim A.val.carrier = P.dim at hd
    rw [A.property,hdim] at hd
    omega
  obtain ⟨B,hB,hAB,hBT,hdB⟩ := facet_above_proper_face P A.val.isFace hAT
  have hBd : faceDim B = k + 1 := by
    change faceDim B + 1 = P.dim at hdB
    omega
  have hAB' : A.val.carrier ⊂ B := by
    refine hAB.ssubset_of_ne ?_
    intro h
    have hd := congrArg faceDim h
    rw [A.property,hBd] at hd
    omega
  have hrank : faceDim P.toSet = faceDim A.val.carrier + 2 := by
    change P.dim = _
    rw [A.property,hdim]
  obtain ⟨C,hC,hAC,hCT,hCB⟩ :=
    secondo_intermedio P A.val.isFace (toSet_isFace P) hrank hB hAB' hBT
  have hCd : faceDim C = k + 1 := by
    have hlo := faceDim_lt_of_ssubset P A.val.isFace hC hAC
    have hhi := faceDim_lt_of_ssubset P hC (toSet_isFace P) hCT
    change faceDim C < P.dim at hhi
    rw [A.property] at hlo
    omega
  let b : Coface P A.val.carrier (k + 1) := ⟨⟨⟨B,hB⟩,hBd⟩,hAB⟩
  let c : Coface P A.val.carrier (k + 1) := ⟨⟨⟨C,hC⟩,hCd⟩,hAC.1⟩
  have hbc : b ≠ c := by
    intro h
    exact hCB (congrArg (fun z => z.val.val.carrier) h).symm
  apply card_eq_two_of_two b c hbc
  intro F
  have hAF : A.val.carrier ⊂ F.val.val.carrier := by
    refine F.property.ssubset_of_ne ?_
    intro h
    have hd := congrArg faceDim h
    rw [A.property,F.val.property] at hd
    omega
  have hFT : F.val.val.carrier ⊂ P.toSet := by
    refine (face_subset_toSet P F.val.val.isFace).ssubset_of_ne ?_
    intro h
    have hd := congrArg faceDim h
    change faceDim F.val.val.carrier = P.dim at hd
    rw [F.val.property,hdim] at hd
    omega
  have hc := atMostTwo_middle_faces P A.val.isFace (toSet_isFace P) hrank
    hB hAB' hBT hC hAC hCT F.val.val.isFace hAF hFT
  rcases hc with h | h | h
  · exact (hCB h.symm).elim
  · left
    apply Subtype.ext
    apply Subtype.ext
    exact PolytopeFace.ext h.symm
  · right
    apply Subtype.ext
    apply Subtype.ext
    exact PolytopeFace.ext h.symm

theorem polygon_vertices_eq_edges (P : ConvexPolytope n) (hdim : P.dim = 2) :
    Nat.card P.vertices = Nat.card (Face P 1) := by
  have h := two_regular_edge_card (vertexGraph P)
    (polygon_vertex_degree_two P hdim)
  rw [graph_edge_card_eq_one_face_card] at h
  exact h.symm

theorem two_face_vertices_eq_edges (P : ConvexPolytope n) (R : Face P 2) :
    Nat.card (VerticesOn P R.val.carrier) =
      Nat.card (FaceBelow P R.val.carrier 1) := by
  let Q := facePolytope P R.val.isFace
  have hQ : Q.dim = 2 := by
    change faceDim Q.toSet = 2
    rw [facePolytope_toSet]
    exact R.property
  calc
    Nat.card (VerticesOn P R.val.carrier) = Nat.card Q.vertices :=
      Nat.card_congr (faceVerticesEquiv P R.val.isFace)
    _ = Nat.card (Face Q 1) := polygon_vertices_eq_edges Q hQ
    _ = Nat.card (FaceBelow P R.val.carrier 1) :=
      (Nat.card_congr (faceBelowEquiv P R.val.isFace 1)).symm

end Papers.PolytopeIncidenceCounting

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/PolytopeEulerFour.lean -/







@[expose] public section

/-!
# Euler's formula for an actual four-dimensional convex polytope

The proof instantiates the finite double count using
actual exposed-face incidence. Local three-dimensional Euler equations
are supplied by PolytopeEulerThree; edge figures and two-faces are actual
polygons. In particular, no Euler relation, ridge-pairing axiom, or
abstract manifold hypothesis is supplied by the caller.
-/

noncomputable section

namespace Papers.PolytopeEulerFour

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeEulerThree Papers.FaceIncidenceEuler
open scoped BigOperators Classical

variable {n : ℕ}

theorem figure_dim {P : ConvexPolytope n} {v : E n}
    (D : VertexFigureGaloisData P P.toSet v)
    (hv : v ∈ P.vertices) (k : ℕ) (hdim : P.dim = k + 1) :
    D.figure.dim = k := by
  have hp : 1 ≤ faceDim P.toSet := by
    change 1 ≤ P.dim
    omega
  have h := D.figure_dim_add_one (toSet_isFace P)
    (Papers.PolytopeBasicExtreme.vertex_mem_body P hv) hp
  change D.figure.dim + 1 = P.dim at h
  omega

theorem vertex_local_euler (P : ConvexPolytope n) (hdim : P.dim = 4)
    (v : P.vertices) :
    (Nat.card (IncidentFace P v.val 1) : ℤ) -
      Nat.card (IncidentFace P v.val 2) +
      Nat.card (IncidentFace P v.val 3) = 2 := by
  obtain ⟨D⟩ := exists_figure P v.property (by omega)
  have hD : D.figure.dim = 3 := figure_dim D v.property 3 hdim
  have h0 := Nat.card_congr (incidentFigureEquiv D 0)
  have h1 := Nat.card_congr (incidentFigureEquiv D 1)
  have h2 := Nat.card_congr (incidentFigureEquiv D 2)
  have hv := Nat.card_congr (zeroFaceEquiv D.figure)
  have hEuler := euler_three D.figure hD
  have hvc : Nat.card D.figure.vertices = D.figure.vertices.card := by
    simp
  rw [h0,h1,h2,← hv,hvc]
  exact hEuler

theorem facet_local_euler (P : ConvexPolytope n) (F : Face P 3) :
    (Nat.card (VerticesOn P F.val.carrier) : ℤ) -
      Nat.card (FaceBelow P F.val.carrier 1) +
      Nat.card (FaceBelow P F.val.carrier 2) = 2 := by
  let Q := facePolytope P F.val.isFace
  have hQ : Q.dim = 3 := by
    change faceDim Q.toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  rw [Nat.card_congr (faceVerticesEquiv P F.val.isFace),
    Nat.card_congr (faceBelowEquiv P F.val.isFace 1),
    Nat.card_congr (faceBelowEquiv P F.val.isFace 2)]
  simpa using euler_three Q hQ

/-- The second vertex figure at an endpoint of an edge is its genuine
two-dimensional figure. This establishes the edge/triangle/facet
incidence equality used in the four-dimensional double count. -/
theorem edge_figure_counts (P : ConvexPolytope n) (hdim : P.dim = 4)
    (e : Face P 1) :
    Nat.card (Coface P e.val.carrier 2) =
      Nat.card (Coface P e.val.carrier 3) := by
  obtain ⟨v,hv,hve⟩ := face_has_vertex P e.val.isFace
  obtain ⟨D⟩ := exists_figure P hv (by omega)
  have hD : D.figure.dim = 3 := figure_dim D hv 3 hdim
  let A : PositiveVertexStarFace P P.toSet v :=
    { carrier := e.val.carrier
      isFace := e.val.isFace
      subset_base := face_subset_toSet P e.val.isFace
      mem_vertex := hve
      dim_pos := by rw [e.property] }
  have hAd : faceDim (D.faceEquiv A).carrier = 0 := by
    have h := D.map_dim A
    change faceDim (D.faceEquiv A).carrier + 1 = faceDim e.val.carrier at h
    rw [e.property] at h
    omega
  obtain ⟨q,hq,hAq⟩ := actual_zeroFace_is_vertex D.figure
    (D.faceEquiv A).carrier (D.faceEquiv A).isFace hAd
  obtain ⟨D'⟩ := exists_figure D.figure hq (by omega)
  have hD' : D'.figure.dim = 2 := figure_dim D' hq 2 hD
  have h2 : Nat.card (Coface P e.val.carrier 2) =
      Nat.card (Face D'.figure 0) := by
    calc
      _ = Nat.card (Coface D.figure (D.faceEquiv A).carrier 1) :=
        Nat.card_congr (cofaceFigureEquiv D A 1)
      _ = Nat.card (Coface D.figure ({q} : Set (E n)) 1) := by rw [hAq]
      _ = Nat.card (IncidentFace D.figure q 1) :=
        Nat.card_congr (singletonCofaceEquiv D.figure q 1)
      _ = Nat.card (Face D'.figure 0) :=
        Nat.card_congr (incidentFigureEquiv D' 0)
  have h3 : Nat.card (Coface P e.val.carrier 3) =
      Nat.card (Face D'.figure 1) := by
    calc
      _ = Nat.card (Coface D.figure (D.faceEquiv A).carrier 2) :=
        Nat.card_congr (cofaceFigureEquiv D A 2)
      _ = Nat.card (Coface D.figure ({q} : Set (E n)) 2) := by rw [hAq]
      _ = Nat.card (IncidentFace D.figure q 2) :=
        Nat.card_congr (singletonCofaceEquiv D.figure q 2)
      _ = Nat.card (Face D'.figure 1) :=
        Nat.card_congr (incidentFigureEquiv D' 1)
  rw [h2,h3,← Nat.card_congr (zeroFaceEquiv D'.figure)]
  exact polygon_vertices_eq_edges D'.figure hD'

theorem rowCount_card {X Y : Type*} [Fintype X] [Fintype Y]
    (inc : X → Y → Prop) (x : X) :
    rowCount inc x = (Nat.card {y : Y // inc x y} : ℤ) := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  unfold rowCount
  simpa only [Finset.mem_univ,true_and] using
    (Finset.natCast_card_filter (R := ℤ) (fun y => inc x y) Finset.univ).symm

theorem colCount_card {X Y : Type*} [Fintype X] [Fintype Y]
    (inc : X → Y → Prop) (y : Y) :
    colCount inc y = (Nat.card {x : X // inc x y} : ℤ) := by
  exact rowCount_card (fun y x => inc x y) y

/-- Euler's equation with actual vertices and all actual nonempty faces
of dimensions one, two, and three. Ambient dimension is unrestricted. -/
theorem euler_four (P : ConvexPolytope n) (hdim : P.dim = 4) :
    (P.vertices.card : ℤ) - Nat.card (Face P 1) +
      Nat.card (Face P 2) - Nat.card (Face P 3) = 0 := by
  letI : Fintype (Face P 1) := Fintype.ofFinite _
  letI : Fintype (Face P 2) := Fintype.ofFinite _
  letI : Fintype (Face P 3) := Fintype.ofFinite _
  let ve : P.vertices → Face P 1 → Prop := fun v e => v.val ∈ e.val.carrier
  let vr : P.vertices → Face P 2 → Prop := fun v r => v.val ∈ r.val.carrier
  let vf : P.vertices → Face P 3 → Prop := fun v f => v.val ∈ f.val.carrier
  let er : Face P 1 → Face P 2 → Prop := fun e r => e.val.carrier ⊆ r.val.carrier
  let ef : Face P 1 → Face P 3 → Prop := fun e f => e.val.carrier ⊆ f.val.carrier
  let rf : Face P 2 → Face P 3 → Prop := fun r f => r.val.carrier ⊆ f.val.carrier
  have h := euler_four_from_local_three ve vr vf er ef rf
    (by
      intro e
      rw [colCount_card]
      change (Nat.card (VerticesOn P e.val.carrier) : ℤ) = 2
      rw [one_face_vertex_card]
      norm_num)
    (by
      intro r
      rw [rowCount_card]
      change (Nat.card (Coface P r.val.carrier 3) : ℤ) = 2
      rw [ridge_coface_card P 2 hdim r]
      norm_num)
    (by
      intro r
      rw [colCount_card,colCount_card]
      exact_mod_cast two_face_vertices_eq_edges P r)
    (by
      intro e
      rw [rowCount_card,rowCount_card]
      exact_mod_cast edge_figure_counts P hdim e)
    (by
      intro v
      rw [rowCount_card,rowCount_card,rowCount_card]
      exact vertex_local_euler P hdim v)
    (by
      intro f
      rw [colCount_card,colCount_card,colCount_card]
      exact facet_local_euler P f)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using h

theorem vertices_add_two_faces_eq_edges_add_facets
    (P : ConvexPolytope n) (hdim : P.dim = 4) :
    P.vertices.card + Nat.card (Face P 2) =
      Nat.card (Face P 1) + Nat.card (Face P 3) := by
  have h := euler_four P hdim
  omega

end Papers.PolytopeEulerFour

end
end
end BundlePart7
