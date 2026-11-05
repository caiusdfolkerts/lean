import cubical.polytope.graph
import cubical.polytope.balinski_generale

/-!
# Monotone paths in an actual convex-polytope graph

A linear functional that improves at some vertex improves along an incident
edge. Consequently a strict sublevel graph is connected whenever the
functional separates the vertices. These are geometric theorems, not
assumptions supplied to the graph definition.
-/

open Set
open scoped RealInnerProductSpace

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

theorem exists_improving_step (P : ConvexPolytope n)
    (l : E n →L[ℝ] ℝ) {x : E n} (hx : x ∈ P.vertices)
    (hup : ∃ z ∈ P.vertices, l x < l z) :
    ∃ y : E n, GeneralVertexStep P x y ∧ l x < l y := by
  have hxFace : P.IsFace ({x} : Set (E n)) := vertex_isFace P hx
  obtain ⟨g, hg⟩ := hxFace.1 hxFace.2
  let w : E n := (InnerProductSpace.toDual ℝ (E n)).symm l
  have hwspec : ∀ y : E n, inner ℝ w y = l y := by
    intro y
    exact InnerProductSpace.toDual_symm_apply
  have hwconst : ∀ y ∈ ({x} : Set (E n)), inner ℝ w y = inner ℝ w x := by
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
  have hwup : ∃ z ∈ P.vertices, inner ℝ w x < inner ℝ w z := by
    simpa only [hwspec] using hup
  obtain ⟨F, hF, hxF, himprove⟩ :=
    perno_parametrico_crescente_monotono P hxFace g hg x
      (Set.mem_singleton x) w hwconst hwup
  have hdF : 1 ≤ faceDim F := by
    have hlt := faceDim_lt_of_ssubset P hxFace hF hxF
    rw [faceDim_singleton] at hlt
    omega
  obtain ⟨e, he, hde, hxe, heF⟩ :=
    edge_inside_face_at_vertex P hF hx (hxF.1 (Set.mem_singleton x)) hdF
  obtain ⟨y, hy, hye, hyx, _hseg⟩ := spigolo_segmento P he hde hx hxe
  refine ⟨y, ⟨hy, hyx.symm, e, he, hde, hxe, hye⟩, ?_⟩
  have hymem : y ∉ ({x} : Set (E n)) := by simpa using hyx
  simpa only [hwspec] using himprove y (heF hye) hymem

/-- A local maximum of a linear functional on the graph is a global maximum. -/
theorem local_max_global_max (P : ConvexPolytope n)
    (l : E n →L[ℝ] ℝ) {x : E n} (hx : x ∈ P.vertices)
    (hlocal : ∀ y, GeneralVertexStep P x y → l y ≤ l x) :
    ∀ z ∈ P.vertices, l z ≤ l x := by
  intro z hz
  by_contra h
  obtain ⟨y, hy, hxy⟩ := exists_improving_step P l hx ⟨z, hz, lt_of_not_ge h⟩
  exact (not_lt_of_ge (hlocal y hy)) hxy

/-- Adjacency inside a strict sublevel of a geometric linear functional. -/
def SublevelStep (P : ConvexPolytope n) (l : E n →L[ℝ] ℝ) (c : ℝ)
    (x y : E n) : Prop :=
  x ∈ P.vertices ∧ GeneralVertexStep P x y ∧ l x < c ∧ l y < c

theorem sublevelStep_symm (P : ConvexPolytope n) (l : E n →L[ℝ] ℝ) (c : ℝ)
    {x y : E n} (h : SublevelStep P l c x y) : SublevelStep P l c y x := by
  rcases h with ⟨hx, ⟨hy, hxy, F, hF, hdF, hxF, hyF⟩, hxc, hyc⟩
  exact ⟨hy, ⟨hx, hxy.symm, F, hF, hdF, hyF, hxF⟩, hyc, hxc⟩

theorem sublevel_path_to_min (P : ConvexPolytope n)
    (l : E n →L[ℝ] ℝ) (c : ℝ)
    (hinj : Set.InjOn l (P.vertices : Set (E n)))
    {m x : E n} (hm : m ∈ P.vertices)
    (hmin : ∀ z ∈ P.vertices, l m ≤ l z)
    (hx : x ∈ P.vertices) (hxc : l x < c) :
    Relation.ReflTransGen (SublevelStep P l c) x m := by
  classical
  let X := P.vertices.filter (fun z => l z < c)
  have hxX : x ∈ X := Finset.mem_filter.mpr ⟨hx, hxc⟩
  have hmX : m ∈ X := Finset.mem_filter.mpr ⟨hm, (hmin x hx).trans_lt hxc⟩
  have hlocalglobal : ∀ p ∈ X,
      (∀ q ∈ X, SublevelStep P l c p q → -l q ≤ -l p) →
      ∀ z ∈ X, -l z ≤ -l p := by
    intro p hpX hlocal z hzX
    have hp := Finset.mem_filter.mp hpX
    have hz := Finset.mem_filter.mp hzX
    by_contra h
    have hzp : l z < l p := by linarith
    obtain ⟨q, hq, hpq⟩ := exists_improving_step P (-l) hp.1
      ⟨z, hz.1, by simpa using (neg_lt_neg hzp)⟩
    have hqp : l q < l p := by
      change -l p < -l q at hpq
      linarith
    have hqc : l q < c := hqp.trans hp.2
    have hqX : q ∈ X := Finset.mem_filter.mpr ⟨hq.1, hqc⟩
    have hcontra := hlocal q hqX ⟨hp.1, hq, hp.2, hqc⟩
    linarith
  have hunique : ∀ z ∈ X, z ≠ m → -l z < -l m := by
    intro z hzX hzm
    have hz := (Finset.mem_filter.mp hzX).1
    have hne : l z ≠ l m := fun h => hzm (hinj hz hm h)
    have hle := hmin z hz
    have hlt : l m < l z := lt_of_le_of_ne hle (Ne.symm hne)
    exact neg_lt_neg hlt
  have hpath := camminata_del_simplesso X (SublevelStep P l c) (fun z => -l z)
    hlocalglobal hmX hunique hxX
  exact Relation.ReflTransGen.mono (fun _ _ h => h.2) _ _ hpath

/-- All vertices strictly below a level are connected within that sublevel. -/
theorem sublevel_connected (P : ConvexPolytope n)
    (l : E n →L[ℝ] ℝ) (c : ℝ)
    (hinj : Set.InjOn l (P.vertices : Set (E n)))
    {x y : E n} (hx : x ∈ P.vertices) (hy : y ∈ P.vertices)
    (hxc : l x < c) (hyc : l y < c) :
    Relation.ReflTransGen (SublevelStep P l c) x y := by
  classical
  obtain ⟨m, hm, hmin⟩ := P.vertices.exists_min_image l P.vertices_nonempty
  have hxm := sublevel_path_to_min P l c hinj hm hmin hx hxc
  have hym := sublevel_path_to_min P l c hinj hm hmin hy hyc
  have hmy : Relation.ReflTransGen (SublevelStep P l c) m y := by
    have reverse : ∀ {a b : E n}, Relation.ReflTransGen (SublevelStep P l c) a b →
        Relation.ReflTransGen (SublevelStep P l c) b a := by
      intro a b h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
          exact (Relation.ReflTransGen.single (sublevelStep_symm P l c hstep)).trans ih
    exact reverse hym
  exact hxm.trans hmy

end LeanEval.Geometry.PlatonicClassification
