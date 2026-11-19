module
public import Papers.PolytopeVertexCone
public import Papers.FiniteGraphOptimization
public import Papers.FaceVertexCardinality
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Tactic.Push

@[expose] public section

/-!
# Intrinsic Balinski connectivity

Deleting fewer than dim P vertices leaves the actual edge graph
connected.  The proof uses a height constant on the removed points and
one retained anchor, monotone edge pivots, and finite perturbations.
The ambient space may have dimension greater than dim P.
-/

noncomputable section
namespace Papers.PolytopeBalinski

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeVertexCone Papers.FiniteGraphOptimization
open scoped Classical

variable {n : ℕ}

def vertexGraph (P : ConvexPolytope n) : SimpleGraph P.vertices where
  Adj x y := GeneralVertexStep P (x : E n) (y : E n)
  symm := ⟨by
    rintro x y ⟨hy, hxy, e, he, hde, hxe, hye⟩
    exact ⟨x.2, hxy.symm, e, he, hde, hye, hxe⟩⟩
  loopless := ⟨by
    rintro x ⟨_, hne, _⟩
    exact hne rfl⟩

theorem exists_improving_neighbor (P : ConvexPolytope n)
    (l : E n →L[ℝ] ℝ) {x z : E n}
    (hx : x ∈ P.vertices) (hz : z ∈ P.vertices) (hlt : l x < l z) :
    ∃ y, GeneralVertexStep P x y ∧ l x < l y := by
  by_contra hn
  have hlocal : ∀ y, GeneralVertexStep P x y → l y ≤ l x := by
    intro y hy
    by_contra hny
    exact hn ⟨y, hy, lt_of_not_ge hny⟩
  have hle := maximum_on_vertices_of_neighbors P l hx hlocal z hz
  exact (not_lt_of_ge hle) hlt

theorem exists_strict_vertex_exposer (P : ConvexPolytope n)
    {q : E n} (hq : q ∈ P.vertices) :
    ∃ g : E n →L[ℝ] ℝ, ∀ v ∈ P.vertices, v ≠ q → g v < g q := by
  obtain ⟨g, hg⟩ := (vertex_isFace P hq).1 (Set.singleton_nonempty q)
  have hqmax : ∀ v ∈ P.toSet, g v ≤ g q := by
    have hmem : q ∈ ({q} : Set (E n)) := Set.mem_singleton q
    rw [hg] at hmem
    exact hmem.2
  refine ⟨g, ?_⟩
  intro v hv hvq
  have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hv
  rcases lt_or_eq_of_le (hqmax v hvT) with hlt | heq
  · exact hlt
  · have hmem : v ∈ ({q} : Set (E n)) := by
      rw [hg]
      refine ⟨hvT, ?_⟩
      intro w hw
      rw [heq]
      exact hqmax w hw
    exact (hvq (Set.mem_singleton_iff.mp hmem)).elim

theorem positive_vertexGraph_connected (P : ConvexPolytope n)
    (l : E n →L[ℝ] ℝ) (c : ℝ)
    (hpos : ∃ v ∈ P.vertices, c < l v) :
    ((vertexGraph P).induce {v : P.vertices | c < l (v : E n)}).Connected := by
  classical
  obtain ⟨q, hq, hqmax⟩ :=
    Finset.exists_max_image P.vertices l P.vertices_nonempty
  have hqpos : c < l q := by
    obtain ⟨v, hv, hvc⟩ := hpos
    exact hvc.trans_le (hqmax v hv)
  obtain ⟨g, hg⟩ := exists_strict_vertex_exposer P hq
  let pairs := (P.vertices.product P.vertices).filter
    (fun p : E n × E n => c < l p.1 ∧ l p.2 ≤ c)
  have hgap : ∀ p ∈ pairs, 0 < l p.1 - l p.2 := by
    intro p hp
    have hc := (Finset.mem_filter.mp hp).2
    exact sub_pos.mpr (hc.2.trans_lt hc.1)
  obtain ⟨ε, hε, hpert⟩ :=
    exists_small_positive_perturbation pairs
      (fun p => l p.1 - l p.2) (fun p => g p.1 - g p.2) hgap
  let L : E n →L[ℝ] ℝ := l + ε • g
  have horder : ∀ v ∈ P.vertices, ∀ w ∈ P.vertices,
      c < l v → l w ≤ c → L w < L v := by
    intro v hv w hw hvc hwc
    have hp : (v,w) ∈ pairs :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv,hw⟩,hvc,hwc⟩
    have hh := hpert ε hε le_rfl (v,w) hp
    change 0 < l v - l w + ε * (g v - g w) at hh
    change l w + ε * g w < l v + ε * g v
    nlinarith
  have hLmax : ∀ v ∈ P.vertices, v ≠ q → L v < L q := by
    intro v hv hvq
    have hl := hqmax v hv
    have hh := mul_lt_mul_of_pos_left (hg v hv hvq) hε
    change l v + ε * g v < l q + ε * g q
    linarith
  let Pos : Set P.vertices := {v | c < l (v : E n)}
  let H := (vertexGraph P).induce Pos
  letI : Fintype Pos := Fintype.ofFinite _
  let m : Pos := ⟨⟨q,hq⟩,hqpos⟩
  apply connected_of_strict_descent H (fun v => -L (v.1 : E n)) m
  intro v hvm
  have hvq : (v.1 : E n) ≠ q := by
    intro heq
    apply hvm
    apply Subtype.ext
    exact Subtype.ext heq
  obtain ⟨w, hvw, hwL⟩ :=
    exists_improving_neighbor P L v.1.2 hq (hLmax _ v.1.2 hvq)
  have hwpos : c < l w := by
    by_contra hnot
    have hh := horder _ v.1.2 w hvw.1 v.2 (le_of_not_gt hnot)
    exact (not_lt_of_ge hwL.le) hh
  refine ⟨⟨⟨w,hvw.1⟩,hwpos⟩,hvw,?_⟩
  exact neg_lt_neg hwL

theorem height_constant_on_small_set (P : ConvexPolytope n)
    (S : Finset (E n)) (hcard : S.card < P.dim)
    {v : E n} (hv : v ∈ P.vertices) :
    ∃ l : E n →L[ℝ] ℝ,
      (∀ s ∈ S, l s = l v) ∧ ∃ w ∈ P.vertices, l v < l w := by
  let U : Submodule ℝ (E n) :=
    Submodule.span ℝ (Set.range (fun s : S => (s : E n) - v))
  have hU : finrank ℝ U ≤ S.card := by
    have h := finrank_range_le_card (R := ℝ) (fun s : S => (s : E n) - v)
    simpa only [U, Set.finrank, Fintype.card_coe] using h
  have hnotle : ¬ neighborSpan P v ≤ U := by
    intro hle
    have hh := Submodule.finrank_mono hle
    rw [neighborSpan_eq_vectorSpan P hv] at hh
    change P.dim ≤ finrank ℝ U at hh
    omega
  have hout : ∃ w, GeneralVertexStep P v w ∧ w - v ∉ U := by
    by_contra h
    push_neg at h
    apply hnotle
    apply Submodule.span_le.mpr
    rintro z ⟨w, hw, rfl⟩
    exact h w hw
  obtain ⟨w, hw, hwU⟩ := hout
  have hnotall : ¬ ∀ φ : Module.Dual ℝ (E n),
      φ ∈ U.dualAnnihilator → φ (w - v) = 0 := by
    intro h
    exact hwU ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U (w-v)).mp h)
  push_neg at hnotall
  obtain ⟨φ, hφ, hφwv⟩ := hnotall
  have htie : ∀ s ∈ S, φ s = φ v := by
    intro s hs
    have hmem : s - v ∈ U := Submodule.subset_span ⟨⟨s,hs⟩,rfl⟩
    have hz := (Submodule.mem_dualAnnihilator φ).mp hφ (s-v) hmem
    exact sub_eq_zero.mp (by simpa only [map_sub] using hz)
  have hne : φ w ≠ φ v := by
    intro heq
    apply hφwv
    rw [map_sub, heq, sub_self]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨-φ.toContinuousLinearMap,?_,w,hw.1,?_⟩
    · intro s hs
      change -φ s = -φ v
      rw [htie s hs]
    · exact neg_lt_neg hlt
  · exact ⟨φ.toContinuousLinearMap,htie,w,hw.1,hgt⟩

theorem deleted_reachable_of_nonnegative_height
    (P : ConvexPolytope n) (S : Finset (E n))
    (l : E n →L[ℝ] ℝ) (c : ℝ)
    (hS : ∀ s ∈ S, l s = c)
    (hpos : ∃ v ∈ P.vertices, c < l v)
    (x y : {v : P.vertices | (v : E n) ∉ S})
    (hx : c ≤ l (x.1 : E n)) (hy : c ≤ l (y.1 : E n)) :
    ((vertexGraph P).induce {v : P.vertices | (v : E n) ∉ S}).Reachable x y := by
  let Pos : Set P.vertices := {v | c < l (v : E n)}
  let Del : Set P.vertices := {v | (v : E n) ∉ S}
  let G := vertexGraph P
  have hsub : Pos ⊆ Del := by
    intro v hv hvS
    have hh := hS v hvS
    exact (ne_of_gt hv) hh
  let inclusion : G.induce Pos →g G.induce Del :=
    (G.induceHomOfLE hsub).toHom
  have htoPos : ∀ v : Del, c ≤ l (v.1 : E n) →
      ∃ w : Pos, (G.induce Del).Reachable v (inclusion w) := by
    intro v hv
    by_cases hvpos : c < l (v.1 : E n)
    · exact ⟨⟨v.1,hvpos⟩,SimpleGraph.Reachable.rfl⟩
    · have hvlevel : l (v.1 : E n) = c := le_antisymm (le_of_not_gt hvpos) hv
      obtain ⟨q,hq,hqpos⟩ := hpos
      obtain ⟨w,hvw,hwlevel⟩ :=
        exists_improving_neighbor P l v.1.2 hq (by rw [hvlevel]; exact hqpos)
      have hwpos : c < l w := by simpa only [hvlevel] using hwlevel
      let ww : Pos := ⟨⟨w,hvw.1⟩,hwpos⟩
      have hadj : (G.induce Del).Adj v (inclusion ww) := hvw
      exact ⟨ww,hadj.reachable⟩
  obtain ⟨xp,hxp⟩ := htoPos x hx
  obtain ⟨yp,hyp⟩ := htoPos y hy
  have hpconn := positive_vertexGraph_connected P l c hpos
  have hp : (G.induce Pos).Reachable xp yp := hpconn.preconnected xp yp
  exact hxp.trans ((hp.map inclusion).trans hyp.symm)

theorem deleted_vertexGraph_reachable (P : ConvexPolytope n)
    (S : Finset (E n)) (hcard : S.card < P.dim)
    (x y : {v : P.vertices | (v : E n) ∉ S}) :
    ((vertexGraph P).induce {v : P.vertices | (v : E n) ∉ S}).Reachable x y := by
  obtain ⟨l,hS,hpos⟩ := height_constant_on_small_set P S hcard x.1.2
  by_cases hy : l (x.1 : E n) ≤ l (y.1 : E n)
  · exact deleted_reachable_of_nonnegative_height P S l (l x.1) hS hpos
      x y le_rfl hy
  · have hylt : l (y.1 : E n) < l (x.1 : E n) := lt_of_not_ge hy
    apply deleted_reachable_of_nonnegative_height P S (-l) (-l x.1)
    · intro s hs
      change -l s = -l x.1
      rw [hS s hs]
    · exact ⟨y.1,y.1.2,neg_lt_neg hylt⟩
    · exact le_rfl
    · exact neg_le_neg hylt.le

theorem deleted_vertexGraph_connected (P : ConvexPolytope n)
    (S : Finset (E n)) (hcard : S.card < P.dim) :
    ((vertexGraph P).induce {v : P.vertices | (v : E n) ∉ S}).Connected := by
  have hnonempty : ∃ v ∈ P.vertices, v ∉ S := by
    by_contra h
    push_neg at h
    have hsubset : P.vertices ⊆ S := h
    have hcount := Finset.card_le_card hsubset
    have hbody : P.toSet.Nonempty := by
      obtain ⟨v,hv⟩ := P.vertices_nonempty
      exact ⟨v,subset_convexHull ℝ _ hv⟩
    have hdim := Papers.FaceVertexCardinality.dimension_add_one_le_card_of_subset_hull
      hbody P.vertices Set.Subset.rfl
    change P.dim + 1 ≤ P.vertices.card at hdim
    omega
  obtain ⟨v,hv,hvS⟩ := hnonempty
  letI : Nonempty {w : P.vertices | (w : E n) ∉ S} := ⟨⟨⟨v,hv⟩,hvS⟩⟩
  exact { preconnected := deleted_vertexGraph_reachable P S hcard }

theorem vertexGraph_connected (P : ConvexPolytope n) :
    (vertexGraph P).Connected := by
  obtain ⟨v,hv⟩ := P.vertices_nonempty
  have hpos : ∃ w ∈ P.vertices, (-1 : ℝ) < (0 : E n →L[ℝ] ℝ) w :=
    ⟨v,hv,by norm_num⟩
  let T : Set P.vertices := {w | (-1 : ℝ) < (0 : E n →L[ℝ] ℝ) (w : E n)}
  have hconn : ((vertexGraph P).induce T).Connected :=
    positive_vertexGraph_connected P 0 (-1) hpos
  letI : Nonempty P.vertices := ⟨⟨v,hv⟩⟩
  refine { preconnected := ?_ }
  intro x y
  have hx : x ∈ T := by norm_num [T]
  have hy : y ∈ T := by norm_num [T]
  exact (hconn.preconnected ⟨x,hx⟩ ⟨y,hy⟩).map
    (SimpleGraph.Embedding.induce T).toHom

theorem vertexGraph_preconnected (P : ConvexPolytope n) :
    (vertexGraph P).Preconnected :=
  (vertexGraph_connected P).preconnected

theorem vertexGraph_delete_one_connected (P : ConvexPolytope n)
    (hdim : 2 ≤ P.dim) (q : P.vertices) :
    ((vertexGraph P).induce {r : P.vertices | r ≠ q}).Connected := by
  have hcard : ({(q : E n)} : Finset (E n)).card < P.dim := by
    simpa only [Finset.card_singleton] using (show 1 < P.dim by omega)
  have hc := deleted_vertexGraph_connected P {(q : E n)} hcard
  have hset : {r : P.vertices | (r : E n) ∉ ({(q : E n)} : Finset (E n))} =
      {r : P.vertices | r ≠ q} := by
    ext r
    constructor
    · intro h heq
      apply h
      exact Finset.mem_singleton.mpr (congrArg Subtype.val heq)
    · intro h hr
      apply h
      exact Subtype.ext (Finset.mem_singleton.mp hr)
  rw [hset] at hc
  exact hc

theorem vertexGraph_delete_one_preconnected (P : ConvexPolytope n)
    (hdim : 2 ≤ P.dim) (q : P.vertices) :
    ((vertexGraph P).induce {r : P.vertices | r ≠ q}).Preconnected :=
  (vertexGraph_delete_one_connected P hdim q).preconnected

end Papers.PolytopeBalinski
