module

public import Papers.GraphicalZonotopes.PathPlanarity
public import Papers.GraphicalZonotopes.PlanarDrawing
public import Mathlib.Topology.Algebra.Affine

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical Graph
namespace GraphicalZonotopes

/-- A literal noncrossing straight-line drawing gives an ordinary drawing by
simple continuous arcs. The two real-plane representations are related by an
explicit continuous linear equivalence. -/
theorem HasPlaneStraightLineDrawing.hasPlaneDrawing {V : Type*} {G : SimpleGraph V}
    (hG : HasPlaneStraightLineDrawing G) : HasPlaneDrawing G := by
  obtain ⟨p,hp,hvertex,hcross⟩ := hG
  let L : (Fin 2 → ℝ) ≃L[ℝ] Schoenflies.Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let q : V → Schoenflies.Plane := fun v => L (p v)
  have hq : Function.Injective q := L.injective.comp hp
  let drawing : Sym2 V → ℝ → Schoenflies.Plane := fun e t =>
    L (AffineMap.lineMap (p e.out.1) (p e.out.2) t)
  have hadj : ∀ e ∈ G.edgeSet,G.Adj e.out.1 e.out.2 := by
    intro e he
    apply G.mem_edgeSet.mp
    rwa [Sym2.mk_fst_out_snd_out]
  have hlink : ∀ e ∈ G.edgeSet,(PlaneDrawing.planeGraph G q).IsLink
      e (q e.out.1) (q e.out.2) := by
    intro e he
    exact (PlaneDrawing.planeGraph_isLink G q hq _ _ _).mpr
      ⟨(Sym2.mk_fst_out_snd_out e).symm,hadj e he⟩
  have himage : ∀ e,Graph.edgeArc drawing e =
      L '' segment ℝ (p e.out.1) (p e.out.2) := by
    intro e
    rw [segment_eq_image_lineMap,Set.image_image]
    rfl
  have hpull : ∀ e (z : Fin 2 → ℝ),L z ∈ Graph.edgeArc drawing e →
      z ∈ segment ℝ (p e.out.1) (p e.out.2) := by
    intro e z hz
    rw [himage] at hz
    obtain ⟨w,hw,he⟩ := hz
    have hzw : w = z := L.injective he
    exact hzw ▸ hw
  refine ⟨q,hq,drawing,?_⟩
  constructor
  · intro e he
    have heG : e ∈ G.edgeSet := he
    have hcont : Continuous (drawing e) := L.continuous.comp AffineMap.lineMap_continuous
    have hinj : Function.Injective (drawing e) := L.injective.comp
      (AffineMap.lineMap_injective ℝ (fun h => (hadj e heG).ne (hp h)))
    refine ⟨hcont.continuousOn,hinj.injOn,?_⟩
    simpa only [drawing,AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] using hlink e heG
  · intro e x y v hl hv hve
    have heG : e ∈ G.edgeSet := hl.edge_mem
    rw [PlaneDrawing.planeGraph_vertexSet] at hv
    obtain ⟨w,rfl⟩ := hv
    have hseg : p w ∈ segment ℝ (p e.out.1) (p e.out.2) := hpull e (p w) hve
    have hw : w = e.out.1 ∨ w = e.out.2 := by
      by_contra hh
      have h₁ : w ≠ e.out.1 := fun he => hh (Or.inl he)
      have h₂ : w ≠ e.out.2 := fun he => hh (Or.inr he)
      exact hvertex _ _ _ (hadj e heG) h₁ h₂ hseg
    have hwq : q w = q e.out.1 ∨ q w = q e.out.2 :=
      hw.imp (congrArg q) (congrArg q)
    rcases hl.eq_and_eq_or_eq_and_eq (hlink e heG) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hwq
    · exact hwq.symm
  · intro e f he hf hef x hxe hxf
    have heG : e ∈ G.edgeSet := he
    have hfG : f ∈ G.edgeSet := hf
    rw [himage] at hxe
    obtain ⟨z,hz,hzx⟩ := hxe
    have hzf : z ∈ segment ℝ (p f.out.1) (p f.out.2) := by
      apply hpull f z
      rwa [hzx]
    rcases hcross _ _ _ _ (hadj e heG) (hadj f hfG) z hz hzf with h | h | h
    · obtain ⟨hu,hv⟩ := h
      apply False.elim
      apply hef
      calc
        e = s(e.out.1,e.out.2) := (Sym2.mk_fst_out_snd_out e).symm
        _ = s(f.out.1,f.out.2) := by rw [hu,hv]
        _ = f := Sym2.mk_fst_out_snd_out f
    · obtain ⟨hu,hv⟩ := h
      apply False.elim
      apply hef
      calc
        e = s(e.out.1,e.out.2) := (Sym2.mk_fst_out_snd_out e).symm
        _ = s(f.out.2,f.out.1) := by rw [hu,hv]
        _ = s(f.out.1,f.out.2) := Sym2.eq_swap
        _ = f := Sym2.mk_fst_out_snd_out f
    · obtain ⟨w,hwe,hwf,hzw⟩ := h
      have hxq : x = q w := hzx.symm.trans (congrArg L hzw)
      rw [hxq]
      refine ⟨?_,?_,?_⟩
      · rw [PlaneDrawing.planeGraph_vertexSet]
        exact ⟨w,rfl⟩
      · rcases hwe with hew | hew
        · rw [hew]
          exact (hlink e heG).inc_left
        · rw [hew]
          exact (hlink e heG).inc_right
      · rcases hwf with hfw | hfw
        · rw [hfw]
          exact (hlink f hfG).inc_left
        · rw [hfw]
          exact (hlink f hfG).inc_right

/-- The previously checked explicit straight-line sharpness family is planar
under exactly the same ordinary-arc definition used in the planar corollaries. -/
theorem PathDrawing.path_hasPlaneDrawing (n : ℕ) : HasPlaneDrawing (Path.graph n) :=
  (PathDrawing.path_plane_drawing n).hasPlaneDrawing

end GraphicalZonotopes
