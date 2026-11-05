module

public import PaperVerification.ToricChartOpenImmersions
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

/-!
# The actual scheme obtained by gluing a smooth fan

Every cone supplies its actual affine semigroup chart. Face inclusions are
the previously proved open immersions. Their actual intersections prove
local directedness, so Mathlib's scheme gluing construction applies. The
result is a scheme with an actual affine open cover, not a structure whose
fields assume a toric dictionary.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PaperVerification.ToricCharacters
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [CommRing k]

abbrev ConeIndex := {s : Finset (Lattice n) // s ∈ «Σ».cones}

def coneDiagram : «Σ».ConeIndex ⥤ Scheme.{u} where
  obj s := coneChart k s.val
  map f := coneChartFaceMap k (leOfHom f)
  map_id s := coneChartFaceMap_self k s.val
  map_comp f g := (coneChartFaceMap_comp k (leOfHom g) (leOfHom f)).symm

instance coneDiagram_map_isOpenImmersion {s t : «Σ».ConeIndex} (f : s ⟶ t) :
    IsOpenImmersion ((«Σ».coneDiagram k).map f) :=
  «Σ».coneChartFaceMap_isOpenImmersion k t.val s.val t.property (leOfHom f)

/-- The local directedness condition is proved from the actual common-face
pullback, including the underlying point lifting. -/
instance coneDiagram_isLocallyDirected :
    («Σ».coneDiagram k ⋙ Scheme.forget).IsLocallyDirected where
  cond := by
    intro i j q fi fj xi xj h
    let l : «Σ».ConeIndex :=
      ⟨i.val ∩ j.val, «Σ».downward i.val i.property _ Finset.inter_subset_left⟩
    let fli : l ⟶ i := homOfLE Finset.inter_subset_left
    let flj : l ⟶ j := homOfLE Finset.inter_subset_right
    letI := «Σ».coneChartFaceMap_isOpenImmersion k q.val i.val q.property (leOfHom fi)
    letI := «Σ».coneChartFaceMap_isOpenImmersion k q.val j.val q.property (leOfHom fj)
    have H := «Σ».coneChart_faces_isPullback k q.val i.val j.val
      q.property (leOfHom fi) (leOfHom fj)
    change coneChartFaceMap k (leOfHom fi) xi =
      coneChartFaceMap k (leOfHom fj) xj at h
    have hx : xi ∈ Set.range (pullback.snd
        (coneChartFaceMap k (leOfHom fj)) (coneChartFaceMap k (leOfHom fi))) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact ⟨xj, h.symm⟩
    obtain ⟨z, hz⟩ := hx
    let x := H.isoPullback.inv z
    have hxi : coneChartFaceMap k (Finset.inter_subset_left : i.val ∩ j.val ⊆ i.val) x =
        xi := by
      exact (congrArg (fun f => f z) H.isoPullback_inv_snd).trans hz
    have hxj : coneChartFaceMap k (Finset.inter_subset_right : i.val ∩ j.val ⊆ j.val) x =
        xj := by
      apply (coneChartFaceMap k (leOfHom fj)).isOpenEmbedding.injective
      calc
        coneChartFaceMap k (leOfHom fj)
            (coneChartFaceMap k (Finset.inter_subset_right : i.val ∩ j.val ⊆ j.val) x) =
          coneChartFaceMap k (leOfHom fi)
            (coneChartFaceMap k (Finset.inter_subset_left : i.val ∩ j.val ⊆ i.val) x) :=
          congrArg (fun f => f x) H.w
        _ = coneChartFaceMap k (leOfHom fi) xi := by rw [hxi]
        _ = coneChartFaceMap k (leOfHom fj) xj := h
    exact ⟨l, fli, flj, x, hxi, hxj⟩

/-- Genuine Mathlib gluing data, with all its cocycle obligations derived
by locally directed scheme gluing. -/
def fanGlueData : Scheme.GlueData.{u} :=
  Scheme.IsLocallyDirected.glueData («Σ».coneDiagram k)

/-- The actual colimit scheme of the affine charts. -/
def fanScheme : Scheme.{u} := colimit («Σ».coneDiagram k)

def fanChartMap (s : «Σ».ConeIndex) : coneChart k s.val ⟶ «Σ».fanScheme k :=
  colimit.ι («Σ».coneDiagram k) s

instance fanChartMap_isOpenImmersion (s : «Σ».ConeIndex) :
    IsOpenImmersion («Σ».fanChartMap k s) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι («Σ».coneDiagram k) s))

def fanSchemeOpenCover : («Σ».fanScheme k).OpenCover :=
  Scheme.IsLocallyDirected.openCover («Σ».coneDiagram k)

@[reassoc (attr := simp)] theorem fanChartMap_naturality
    {s t : «Σ».ConeIndex} (hst : s.val ⊆ t.val) :
    coneChartFaceMap k hst ≫ «Σ».fanChartMap k t = «Σ».fanChartMap k s :=
  colimit.w («Σ».coneDiagram k) (homOfLE hst)

theorem fanChartMap_jointly_surjective (x : «Σ».fanScheme k) :
    ∃ (s : «Σ».ConeIndex) (y : coneChart k s.val), «Σ».fanChartMap k s y = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective («Σ».coneDiagram k) x

/-- Equality of two points in the glued scheme is witnessed in the actual
intersection cone chart. No larger relation is imposed by the gluing. -/
theorem fanChartMap_eq_iff (s t : «Σ».ConeIndex)
    (x : coneChart k s.val) (y : coneChart k t.val) :
    «Σ».fanChartMap k s x = «Σ».fanChartMap k t y ↔
      ∃ z : coneChart k (s.val ∩ t.val),
        coneChartFaceMap k Finset.inter_subset_left z = x ∧
        coneChartFaceMap k Finset.inter_subset_right z = y := by
  constructor
  · intro h
    obtain ⟨l, fls, flt, z, hzs, hzt⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff («Σ».coneDiagram k)).mp h
    have hl : l.val ⊆ s.val ∩ t.val :=
      Finset.subset_inter (leOfHom fls) (leOfHom flt)
    let z' : coneChart k l.val := z
    have hzs' : coneChartFaceMap k (leOfHom fls) z' = x := hzs
    have hzt' : coneChartFaceMap k (leOfHom flt) z' = y := hzt
    refine ⟨coneChartFaceMap k hl z', ?_, ?_⟩
    · exact (congrArg (fun f : coneChart k l.val ⟶ coneChart k s.val => f z')
        (coneChartFaceMap_comp k
          (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val) hl)).trans hzs'
    · exact (congrArg (fun f : coneChart k l.val ⟶ coneChart k t.val => f z')
        (coneChartFaceMap_comp k
          (Finset.inter_subset_right : s.val ∩ t.val ⊆ t.val) hl)).trans hzt'
  · rintro ⟨z, rfl, rfl⟩
    let l : «Σ».ConeIndex :=
      ⟨s.val ∩ t.val, «Σ».downward s.val s.property _ Finset.inter_subset_left⟩
    change (coneChartFaceMap k (show l.val ⊆ s.val from Finset.inter_subset_left) ≫
      «Σ».fanChartMap k s) z =
      (coneChartFaceMap k (show l.val ⊆ t.val from Finset.inter_subset_right) ≫
        «Σ».fanChartMap k t) z
    rw [«Σ».fanChartMap_naturality, «Σ».fanChartMap_naturality]

/-- The affine overlap in the glued scheme is the common-face chart as
a scheme-theoretic pullback, not merely as a set of points. -/
theorem fanChart_inter_isPullback (s t : «Σ».ConeIndex) :
    IsPullback
      (coneChartFaceMap k (Finset.inter_subset_right : s.val ∩ t.val ⊆ t.val))
      (coneChartFaceMap k (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val))
      («Σ».fanChartMap k t) («Σ».fanChartMap k s) := by
  let l : «Σ».ConeIndex :=
    ⟨s.val ∩ t.val, «Σ».downward s.val s.property _ Finset.inter_subset_left⟩
  letI := «Σ».coneChartFaceMap_isOpenImmersion k s.val l.val s.property Finset.inter_subset_left
  apply IsOpenImmersion.isPullback
  · exact («Σ».fanChartMap_naturality k (s := l) (t := s)
      Finset.inter_subset_left).trans
        («Σ».fanChartMap_naturality k (s := l) (t := t)
          Finset.inter_subset_right).symm
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨z, hz, _⟩ := («Σ».fanChartMap_eq_iff k s t x y).mp hy.symm
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      refine ⟨coneChartFaceMap k Finset.inter_subset_right z, ?_⟩
      exact («Σ».fanChartMap_eq_iff k s t _ _).mpr ⟨z, rfl, rfl⟩ |>.symm

/-- The zero cone is the actual open torus chart. -/
def zeroConeIndex : «Σ».ConeIndex := ⟨∅, «Σ».empty_mem⟩

def torusOpenMap : coneChart k (∅ : Finset (Lattice n)) ⟶ «Σ».fanScheme k :=
  «Σ».fanChartMap k «Σ».zeroConeIndex

instance torusOpenMap_isOpenImmersion : IsOpenImmersion («Σ».torusOpenMap k) :=
  inferInstanceAs (IsOpenImmersion («Σ».fanChartMap k «Σ».zeroConeIndex))

set_option maxHeartbeats 1000000 in
@[reassoc (attr := simp)] theorem torusOpenMap_chart (s : «Σ».ConeIndex) :
    coneChartFaceMap k (Finset.empty_subset s.val) ≫ «Σ».fanChartMap k s =
      «Σ».torusOpenMap k :=
  «Σ».fanChartMap_naturality k (s := «Σ».zeroConeIndex) (t := s)
    (Finset.empty_subset s.val)

end PaperVerification.ToricGeometry.SmoothCompleteFan
