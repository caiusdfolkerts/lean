module
public import consolidated.deletion_geometry
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option Elab.async false

section BundlePart0
/- Source: Cubical/Polytope/Monotone.lean -/
@[expose] public section



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

end
end BundlePart0

section BundlePart1
/- Source: Cubical/Polytope/GenericHeight.lean -/
@[expose] public section



/-! # Generic separating heights for finite configurations -/

open Set

namespace LeanEval.Geometry.PlatonicClassification

variable {n : ℕ}

/-- A finite collection of Euclidean points is separated by one linear functional. -/
theorem exists_separating_functional (S : Finset (E n)) :
    ∃ l : E n →L[ℝ] ℝ, Set.InjOn l (S : Set (E n)) := by
  classical
  let I := {p : S × S // p.1 ≠ p.2}
  let v : I → E n := fun p => p.val.1.val - p.val.2.val
  have hv : ∀ p, v p ≠ 0 := by
    intro p
    apply sub_ne_zero.mpr
    intro h
    exact p.property (Subtype.ext h)
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ) v hv
  refine ⟨f.toContinuousLinearMap, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  let p : I := ⟨(⟨x, hx⟩, ⟨y, hy⟩), fun h => hne (congrArg Subtype.val h)⟩
  have hp := hf p
  change f (x - y) ≠ 0 at hp
  rw [map_sub] at hp
  exact hp (sub_eq_zero.mpr hxy)

/-- Rank by the number of points strictly below a given height. -/
noncomputable def heightRank (S : Finset (E n)) (l : E n →L[ℝ] ℝ) (x : E n) : ℕ := by
  classical
  exact (S.filter (fun y => l y < l x)).card

theorem heightRank_strictMono (S : Finset (E n)) (l : E n →L[ℝ] ℝ)
    {x y : E n} (hx : x ∈ S) (hxy : l x < l y) :
    heightRank S l x < heightRank S l y := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    obtain ⟨hzS, hzx⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hzS, hzx.trans hxy⟩
  · intro heq
    have hxin : x ∈ S.filter (fun z => l z < l y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
    rw [← heq] at hxin
    exact lt_irrefl _ (Finset.mem_filter.mp hxin).2

theorem heightRank_lt_iff (S : Finset (E n)) (l : E n →L[ℝ] ℝ)
    {x y : E n} (hx : x ∈ S) (hy : y ∈ S) :
    heightRank S l x < heightRank S l y ↔ l x < l y := by
  constructor
  · intro h
    by_contra hnot
    have hle : l y ≤ l x := le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · have hrank : heightRank S l y = heightRank S l x := by
        unfold heightRank
        rw [heq]
      omega
    · have hrev := heightRank_strictMono S l hy hlt
      omega
  · exact heightRank_strictMono S l hx

theorem heightRank_injOn (S : Finset (E n)) (l : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn l (S : Set (E n))) :
    Set.InjOn (heightRank S l) (S : Set (E n)) := by
  intro x hx y hy heq
  apply hinj hx hy
  rcases lt_trichotomy (l x) (l y) with hlt | hequal | hgt
  · have h := heightRank_strictMono S l hx hlt
    omega
  · exact hequal
  · have h := heightRank_strictMono S l hy hgt
    omega

end LeanEval.Geometry.PlatonicClassification

end
end BundlePart1

section BundlePart2
/- Source: Cubical/Polytope/FettaVertice.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.FettaVertice.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/






/-!
LA FETTA AL VERTICE — IL CORPO (21 lug 2026).

Primo modulo della figura al vertice: dato un politopo `Q`, un vertice `v`
e un funzionale `l` che separa strettamente `v` da tutti gli altri vertici
(`l w < c < l v`), la fetta `Q.toSet ∩ {l = c}` è l'hull convesso dei punti
`attra w` in cui i segmenti `[v, w]` attraversano il livello.

Il calcolo chiave (`fetta_eq_hull`) è puramente baricentrico: da
`x = a_v • v + ∑ a_w • w` al livello `c` si ricavano pesi
`μ_w = a_w (l v − l w)/(l v − c)` non negativi di somma uno con
`x = ∑ μ_w • attra w`.  Nessun interno relativo, nessun cono tangente.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- I dati di una fetta al vertice: il funzionale separatore `l`, il livello
`c` strettamente fra gli altri vertici e `v`, e almeno un altro vertice. -/
structure DatiFetta (Q : ConvexPolytope n) (v : E n) where
  l : E n →L[ℝ] ℝ
  c : ℝ
  hv : v ∈ Q.vertices
  hvc : c < l v
  hsep : ∀ w ∈ Q.vertices, w ≠ v → l w < c
  hW : (Q.vertices.erase v).Nonempty

namespace DatiFetta

variable {Q : ConvexPolytope n} {v : E n} (D : DatiFetta Q v)

/-- Il punto in cui il segmento `[v, w]` attraversa il livello `l = c`. -/
def attra (w : E n) : E n :=
  v + ((D.l v - D.c) / (D.l v - D.l w)) • (w - v)

theorem sep_of_mem_erase {w : E n} (hw : w ∈ Q.vertices.erase v) :
    D.l w < D.c :=
  D.hsep w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)

theorem numpos : 0 < D.l v - D.c := by linarith [D.hvc]

theorem denpos {w : E n} (hwc : D.l w < D.c) : 0 < D.l v - D.l w := by
  linarith [D.hvc]

theorem tau_pos {w : E n} (hwc : D.l w < D.c) :
    0 < (D.l v - D.c) / (D.l v - D.l w) :=
  div_pos D.numpos (D.denpos hwc)

theorem tau_lt_one {w : E n} (hwc : D.l w < D.c) :
    (D.l v - D.c) / (D.l v - D.l w) < 1 := by
  rw [div_lt_one (D.denpos hwc)]
  linarith

/-- La differenza radiale dell'attraversamento. -/
theorem attra_sub (w : E n) :
    D.attra w - v = ((D.l v - D.c) / (D.l v - D.l w)) • (w - v) := by
  rw [attra, add_sub_cancel_left]

/-- L'attraversamento sta al livello `c`. -/
theorem attra_level {w : E n} (hwc : D.l w < D.c) :
    D.l (D.attra w) = D.c := by
  have hden : D.l v - D.l w ≠ 0 := ne_of_gt (D.denpos hwc)
  rw [attra]
  simp only [map_add, map_smul, map_sub, smul_eq_mul]
  have hcancel : (D.l v - D.c) / (D.l v - D.l w) * (D.l v - D.l w)
      = D.l v - D.c := div_mul_cancel₀ _ hden
  nlinarith [hcancel]

/-- L'attraversamento sta sul segmento `[v, w]`. -/
theorem attra_mem_segment {w : E n} (hwc : D.l w < D.c) :
    D.attra w ∈ segment ℝ v w := by
  refine ⟨1 - (D.l v - D.c) / (D.l v - D.l w),
    (D.l v - D.c) / (D.l v - D.l w),
    by linarith [D.tau_lt_one hwc], le_of_lt (D.tau_pos hwc), by ring, ?_⟩
  rw [attra]
  match_scalars <;> ring

/-- L'attraversamento è distinto dal vertice. -/
theorem attra_ne {w : E n} (hwc : D.l w < D.c) : D.attra w ≠ v := by
  intro h
  have := D.attra_level hwc
  rw [h] at this
  linarith [D.hvc]

/-- L'attraversamento appartiene al corpo del politopo. -/
theorem attra_mem_toSet {w : E n} (hwV : w ∈ Q.vertices)
    (hwc : D.l w < D.c) : D.attra w ∈ Q.toSet := by
  have hvT : v ∈ Q.toSet := subset_convexHull ℝ _ (by exact_mod_cast D.hv)
  have hwT : w ∈ Q.toSet := subset_convexHull ℝ _ (by exact_mod_cast hwV)
  exact (convex_convexHull ℝ _).segment_subset hvT hwT
    (D.attra_mem_segment hwc)

/-- I generatori finiti della fetta: gli attraversamenti degli altri vertici. -/
def gen : Finset (E n) := (Q.vertices.erase v).image D.attra

theorem gen_nonempty : D.gen.Nonempty := D.hW.image D.attra

theorem mem_gen_of_mem_erase {w : E n} (hw : w ∈ Q.vertices.erase v) :
    D.attra w ∈ D.gen := Finset.mem_image_of_mem D.attra hw

/-- **LA FETTA È L'HULL DEGLI ATTRAVERSAMENTI.** -/
theorem fetta_eq_hull :
    Q.toSet ∩ {x | D.l x = D.c} = convexHull ℝ (D.gen : Set (E n)) := by
  classical
  set W : Finset (E n) := Q.vertices.erase v with hWdef
  have hvins : Q.vertices = insert v W := (Finset.insert_erase D.hv).symm
  have hvnotW : v ∉ W := Finset.notMem_erase v Q.vertices
  apply Set.Subset.antisymm
  · rintro x ⟨hxT, hxc⟩
    have hxc' : D.l x = D.c := hxc
    have hxT' : x ∈ convexHull ℝ ((Q.vertices : Finset (E n)) : Set (E n)) :=
      hxT
    rw [Finset.convexHull_eq] at hxT'
    obtain ⟨a, ha0, ha1, hax⟩ := hxT'
    have hxrep : x = ∑ u ∈ Q.vertices, a u • u := by
      rw [← hax, Finset.centerMass_eq_of_sum_1 _ _ ha1]
      rfl
    -- livello: ∑ a u * l u = c
    have hlev : ∑ u ∈ Q.vertices, a u * D.l u = D.c := by
      have hmap := congrArg D.l hxrep
      rw [map_sum] at hmap
      simp only [map_smul, smul_eq_mul] at hmap
      exact hmap.symm.trans hxc'
    -- separazione della somma
    have ha1' : a v + ∑ w ∈ W, a w = 1 := by
      rw [hvins, Finset.sum_insert hvnotW] at ha1
      exact ha1
    have hlev' : a v * D.l v + ∑ w ∈ W, a w * D.l w = D.c := by
      rw [hvins, Finset.sum_insert hvnotW] at hlev
      exact hlev
    have hxrep' : x = a v • v + ∑ w ∈ W, a w • w := by
      rw [hvins, Finset.sum_insert hvnotW] at hxrep
      exact hxrep
    -- i pesi della fetta
    set μ : E n → ℝ := fun w => a w * (D.l v - D.l w) / (D.l v - D.c)
      with hμdef
    have hμ0 : ∀ w ∈ W, 0 ≤ μ w := by
      intro w hw
      exact div_nonneg
        (mul_nonneg (ha0 w (Finset.mem_of_mem_erase hw))
          (le_of_lt (D.denpos (D.sep_of_mem_erase hw))))
        (le_of_lt D.numpos)
    have hnum : ∑ w ∈ W, a w * (D.l v - D.l w) = D.l v - D.c := by
      have hexp : ∀ w ∈ W, a w * (D.l v - D.l w)
          = a w * D.l v - a w * D.l w := fun w _ => mul_sub _ _ _
      rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib,
        ← Finset.sum_mul]
      have h1 : ∑ w ∈ W, a w = 1 - a v := by linarith
      have h2 : ∑ w ∈ W, a w * D.l w = D.c - a v * D.l v := by linarith
      rw [h1, h2]
      ring
    have hμ1 : ∑ w ∈ W, μ w = 1 := by
      have hstep : ∑ w ∈ W, μ w
          = (∑ w ∈ W, a w * (D.l v - D.l w)) / (D.l v - D.c) := by
        rw [Finset.sum_div]
      rw [hstep, hnum, div_self (ne_of_gt D.numpos)]
    -- x è combinazione dei tagli
    have hterm : ∀ w ∈ W, μ w • D.attra w = μ w • v + a w • (w - v) := by
      intro w hw
      have hden : D.l v - D.l w ≠ 0 :=
        ne_of_gt (D.denpos (D.sep_of_mem_erase hw))
      have hd : D.l v - D.c ≠ 0 := ne_of_gt D.numpos
      have hcoef : μ w * ((D.l v - D.c) / (D.l v - D.l w)) = a w := by
        rw [hμdef]
        field_simp
      rw [attra, smul_add, smul_smul, hcoef]
    have hx2 : x = ∑ w ∈ W, μ w • D.attra w := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
        ← Finset.sum_smul, hμ1, one_smul]
      have hsub : ∀ w ∈ W, a w • (w - v) = a w • w - a w • v :=
        fun w _ => smul_sub _ _ _
      rw [Finset.sum_congr rfl hsub, Finset.sum_sub_distrib,
        ← Finset.sum_smul]
      have h1 : ∑ w ∈ W, a w = 1 - a v := by linarith
      rw [h1, hxrep']
      rw [sub_smul, one_smul]
      abel
    have hmem := Finset.centerMass_mem_convexHull W (w := μ) hμ0
      (by rw [hμ1]; norm_num)
      (z := D.attra)
      (fun w hw => Finset.mem_coe.mpr (D.mem_gen_of_mem_erase hw))
    rw [Finset.centerMass_eq_of_sum_1 _ _ hμ1] at hmem
    rw [hx2]
    exact hmem
  · apply convexHull_min
    · intro y hy
      have hy' : y ∈ D.gen := hy
      simp only [gen, Finset.mem_image] at hy'
      obtain ⟨w, hw', rfl⟩ := hy'
      refine ⟨D.attra_mem_toSet (Finset.mem_of_mem_erase hw')
        (D.sep_of_mem_erase hw'), ?_⟩
      exact D.attra_level (D.sep_of_mem_erase hw')
    · exact (convex_convexHull ℝ _).inter
        (convex_hyperplane (LinearMap.isLinear D.l.toLinearMap) D.c)

/-! ## La fetta come politopo -/

/-- Krein–Milman finito: l'hull dei punti estremi dell'hull dei generatori
è l'hull dei generatori.  (L'hull finito è compatto e chiuso.) -/
theorem hull_ext :
    convexHull ℝ ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ)
      = convexHull ℝ (D.gen : Set (E n)) := by
  have hcomp : IsCompact (convexHull ℝ (D.gen : Set (E n))) :=
    D.gen.finite_toSet.isCompact_convexHull ℝ
  have hconv : Convex ℝ (convexHull ℝ (D.gen : Set (E n))) :=
    convex_convexHull ℝ _
  have hKM := closure_convexHull_extremePoints hcomp hconv
  have hfin : ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ).Finite :=
    D.gen.finite_toSet.subset extremePoints_convexHull_subset
  calc convexHull ℝ ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ)
      = closure (convexHull ℝ
          ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ)) :=
        (hfin.isClosed_convexHull ℝ).closure_eq.symm
    _ = convexHull ℝ (D.gen : Set (E n)) := hKM

/-- I punti estremi della fetta formano un insieme finito. -/
theorem ext_finite :
    ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ).Finite :=
  D.gen.finite_toSet.subset extremePoints_convexHull_subset

/-- I punti estremi della fetta sono non vuoti. -/
theorem ext_nonempty :
    ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have h0 := D.hull_ext
  rw [hempty, convexHull_empty] at h0
  obtain ⟨y, hy⟩ := D.gen_nonempty
  have hymem : y ∈ convexHull ℝ (D.gen : Set (E n)) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr hy)
  rw [← h0] at hymem
  exact hymem

/-- **LA FETTA COME POLITOPO**: i vertici sono i punti estremi dell'hull
degli attraversamenti. -/
def politopo : ConvexPolytope n where
  vertices := D.ext_finite.toFinset
  vertices_nonempty := by
    obtain ⟨x, hx⟩ := D.ext_nonempty
    exact ⟨x, (Set.Finite.mem_toFinset _).mpr hx⟩
  vertices_eq_extremePoints := by
    rw [Set.Finite.coe_toFinset, D.hull_ext]

/-- Il corpo del politopo-fetta è esattamente la fetta. -/
theorem politopo_toSet :
    D.politopo.toSet = Q.toSet ∩ {x | D.l x = D.c} := by
  have h1 : D.politopo.toSet = convexHull ℝ
      ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ) := by
    show convexHull ℝ ((D.ext_finite.toFinset : Finset (E n)) : Set (E n)) = _
    rw [Set.Finite.coe_toFinset]
  rw [h1, D.hull_ext, ← D.fetta_eq_hull]

/-! ## Il trasferimento delle facce -/

/-- Una faccia di dimensione positiva che contiene `v` contiene un altro
vertice. -/
theorem esiste_vertice_altro {F : Set (E n)} (hF : Q.IsFace F) (hvF : v ∈ F)
    (hdF : 1 ≤ faceDim F) : ∃ w ∈ Q.vertices.erase v, w ∈ F := by
  classical
  by_contra hcon
  push Not at hcon
  have hfe := face_eq_hull_vertices Q hF
  have hsub : ((Q.vertices.filter (· ∈ F) : Finset (E n)) : Set (E n))
      ⊆ ({v} : Set (E n)) := by
    intro u hu
    have hu' : u ∈ Q.vertices.filter (· ∈ F) := by exact_mod_cast hu
    have huV : u ∈ Q.vertices := (Finset.mem_filter.mp hu').1
    have huF : u ∈ F := (Finset.mem_filter.mp hu').2
    by_contra huv
    have huv' : u ≠ v := by simpa using huv
    exact hcon u (Finset.mem_erase.mpr ⟨huv', huV⟩) huF
  have hFsub : F ⊆ ({v} : Set (E n)) := by
    rw [hfe]
    exact convexHull_min hsub (convex_singleton v)
  have hFeq : F = ({v} : Set (E n)) :=
    Set.Subset.antisymm hFsub (Set.singleton_subset_iff.mpr hvF)
  rw [hFeq, faceDim_singleton] at hdF
  omega

/-- **AVANTI**: la fetta di una faccia dello star è una faccia del
politopo-fetta, esposta dallo stesso funzionale. -/
theorem faccia_fetta {F : Set (E n)} (hF : Q.IsFace F) (hvF : v ∈ F)
    (hdF : 1 ≤ faceDim F) :
    D.politopo.IsFace (F ∩ {x | D.l x = D.c}) := by
  obtain ⟨w₀, hw₀W, hw₀F⟩ := esiste_vertice_altro hF hvF hdF
  have hw₀c := D.sep_of_mem_erase hw₀W
  have hattra₀F : D.attra w₀ ∈ F :=
    (hF.1.convex (convex_convexHull ℝ _)).segment_subset hvF hw₀F
      (D.attra_mem_segment hw₀c)
  have hne : (F ∩ {x | D.l x = D.c}).Nonempty :=
    ⟨D.attra w₀, hattra₀F, D.attra_level hw₀c⟩
  refine ⟨?_, hne⟩
  intro _
  obtain ⟨f, hf⟩ := hF.1 hF.2
  refine ⟨f, ?_⟩
  rw [D.politopo_toSet]
  ext x
  constructor
  · rintro ⟨hxF, hxc⟩
    have hx' := hxF
    rw [hf] at hx'
    exact ⟨⟨hx'.1, hxc⟩, fun y hy => hx'.2 y hy.1⟩
  · rintro ⟨⟨hxT, hxc⟩, hxmax⟩
    have hatt' := hattra₀F
    rw [hf] at hatt'
    have h1 : f (D.attra w₀) ≤ f x :=
      hxmax _ ⟨hatt'.1, D.attra_level hw₀c⟩
    refine ⟨?_, hxc⟩
    rw [hf]
    exact ⟨hxT, fun y hy => le_trans (hatt'.2 y hy) h1⟩

/-- **MONOTONIA**: se la fetta di `F₁` sta nella fetta di `F₂`, allora
`F₁ ⊆ F₂`.  Il punto di attraversamento è interno al segmento `[v, w]`, e
un funzionale massimo lì è massimo anche in `w`. -/
theorem fetta_mono {F₁ F₂ : Set (E n)} (hF₁ : Q.IsFace F₁) (hvF₁ : v ∈ F₁)
    (hF₂ : Q.IsFace F₂) (hvF₂ : v ∈ F₂)
    (hsub : F₁ ∩ {x | D.l x = D.c} ⊆ F₂ ∩ {x | D.l x = D.c}) :
    F₁ ⊆ F₂ := by
  classical
  obtain ⟨f₂, hf₂⟩ := hF₂.1 hF₂.2
  have hv₂ := hvF₂
  rw [hf₂] at hv₂
  have hfe := face_eq_hull_vertices Q hF₁
  rw [hfe]
  apply convexHull_min ?_ (hF₂.1.convex (convex_convexHull ℝ _))
  intro u hu
  have hu' : u ∈ Q.vertices.filter (· ∈ F₁) := by exact_mod_cast hu
  have huV : u ∈ Q.vertices := (Finset.mem_filter.mp hu').1
  have huF₁ : u ∈ F₁ := (Finset.mem_filter.mp hu').2
  by_cases huv : u = v
  · subst huv
    exact hvF₂
  · have huW : u ∈ Q.vertices.erase v := Finset.mem_erase.mpr ⟨huv, huV⟩
    have huc : D.l u < D.c := D.sep_of_mem_erase huW
    have hattra₁ : D.attra u ∈ F₁ :=
      (hF₁.1.convex (convex_convexHull ℝ _)).segment_subset hvF₁ huF₁
        (D.attra_mem_segment huc)
    have hattra₂ : D.attra u ∈ F₂ :=
      (hsub ⟨hattra₁, D.attra_level huc⟩).1
    have hatt := hattra₂
    rw [hf₂] at hatt
    have heq : f₂ (D.attra u) = f₂ v :=
      le_antisymm (hv₂.2 _ hatt.1) (hatt.2 v hv₂.1)
    have hexp : f₂ (D.attra u)
        = f₂ v + ((D.l v - D.c) / (D.l v - D.l u)) * (f₂ u - f₂ v) := by
      rw [attra]
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
    have hzero : ((D.l v - D.c) / (D.l v - D.l u)) * (f₂ u - f₂ v) = 0 := by
      linarith [hexp, heq]
    have hf₂u : f₂ u = f₂ v := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h (ne_of_gt (D.tau_pos huc))
      · linarith
    rw [hf₂]
    have huT : u ∈ Q.toSet := subset_convexHull ℝ _ (by exact_mod_cast huV)
    exact ⟨huT, fun y hy => (hv₂.2 y hy).trans_eq hf₂u.symm⟩

/-- **INDIETRO**: ogni faccia del politopo-fetta è la fetta di una faccia
dello star.  Il funzionale è `g + t⋆ · l` con `t⋆ = (M − g v)/(l v − c)`:
sui vertici `w` con `p(w)` argmax il rapporto incrementale vale
esattamente `t⋆`, sugli altri è strettamente minore. -/
theorem faccia_dalla_fetta {G : Set (E n)} (hG : D.politopo.IsFace G) :
    ∃ F : Set (E n), Q.IsFace F ∧ v ∈ F ∧ 1 ≤ faceDim F ∧
      F ∩ {x | D.l x = D.c} = G := by
  obtain ⟨g, hg⟩ := hG.1 hG.2
  rw [D.politopo_toSet] at hg
  obtain ⟨x₀, hx₀⟩ := hG.2
  have hx₀' := hx₀
  rw [hg] at hx₀'
  set M : ℝ := g x₀ with hM
  set t : ℝ := (M - g v) / (D.l v - D.c) with ht
  set f : E n →L[ℝ] ℝ := g + t • D.l with hfdef
  have hfapp : ∀ x, f x = g x + t * D.l x := by
    intro x
    simp [hfdef]
  have hvT : v ∈ Q.toSet := subset_convexHull ℝ _ (by exact_mod_cast D.hv)
  -- il fatto chiave sui vertici
  have hkey : ∀ w ∈ Q.vertices.erase v,
      f v - f w = ((D.l v - D.l w) / (D.l v - D.c)) * (M - g (D.attra w)) := by
    intro w hw
    have hwc := D.sep_of_mem_erase hw
    have hden : D.l v - D.l w ≠ 0 := ne_of_gt (D.denpos hwc)
    have hd : D.l v - D.c ≠ 0 := ne_of_gt D.numpos
    have hgatt : g (D.attra w)
        = g v + ((D.l v - D.c) / (D.l v - D.l w)) * (g w - g v) := by
      rw [attra]
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
    rw [hfapp, hfapp, hgatt, ht]
    field_simp
    ring
  -- massimo in v sui vertici
  have hfvert : ∀ u ∈ (Q.vertices : Set (E n)), f u ≤ f v := by
    intro u huS
    have huV : u ∈ Q.vertices := by exact_mod_cast huS
    by_cases huv : u = v
    · subst huv
      exact le_refl _
    · have huW : u ∈ Q.vertices.erase v := Finset.mem_erase.mpr ⟨huv, huV⟩
      have hwc := D.sep_of_mem_erase huW
      have hattmem : D.attra u ∈ Q.toSet ∩ {x | D.l x = D.c} :=
        ⟨D.attra_mem_toSet (Finset.mem_of_mem_erase huW) hwc,
          D.attra_level hwc⟩
      have hle : g (D.attra u) ≤ M := hx₀'.2 _ hattmem
      have hfrac : 0 ≤ (D.l v - D.l u) / (D.l v - D.c) :=
        le_of_lt (div_pos (D.denpos hwc) D.numpos)
      have hk := hkey u huW
      nlinarith [mul_nonneg hfrac (by linarith : (0:ℝ) ≤ M - g (D.attra u))]
  have hfmax : ∀ y ∈ Q.toSet, f y ≤ f v := le_su_toSet Q f hfvert
  set Fs : Set (E n) := {x ∈ Q.toSet | ∀ y ∈ Q.toSet, f y ≤ f x} with hFs
  have hvF : v ∈ Fs := ⟨hvT, hfmax⟩
  have hFface : Q.IsFace Fs := ⟨fun _ => ⟨f, rfl⟩, ⟨v, hvF⟩⟩
  -- t·(l v − c) = M − g v
  have ht' : t * D.l v - t * D.c = M - g v := by
    rw [← mul_sub]
    exact div_mul_cancel₀ _ (ne_of_gt D.numpos)
  have hfv : f v = M + t * D.c := by
    have := hfapp v
    linarith
  -- la fetta di Fs è G
  have hslice : Fs ∩ {x | D.l x = D.c} = G := by
    ext x
    constructor
    · rintro ⟨⟨hxT, hxmax⟩, hxc⟩
      rw [hg]
      refine ⟨⟨hxT, hxc⟩, ?_⟩
      intro y hy
      have h1 := hxmax y hy.1
      rw [hfapp, hfapp] at h1
      have hyc : D.l y = D.c := hy.2
      have hxc' : D.l x = D.c := hxc
      rw [hyc, hxc'] at h1
      linarith
    · intro hxG
      have hx' := hxG
      rw [hg] at hx'
      have hgx : g x = M :=
        le_antisymm (hx₀'.2 x hx'.1) (hx'.2 x₀ hx₀'.1)
      have hxc : D.l x = D.c := hx'.1.2
      have hfx : f x = M + t * D.c := by
        rw [hfapp, hgx, hxc]
      refine ⟨⟨hx'.1.1, ?_⟩, hxc⟩
      intro y hy
      calc f y ≤ f v := hfmax y hy
        _ = f x := by rw [hfv, hfx]
    -- fine hslice
  have hx₀F : x₀ ∈ Fs := by
    have hx₀G : x₀ ∈ G := hx₀
    rw [← hslice] at hx₀G
    exact hx₀G.1
  have hx₀v : x₀ ≠ v := by
    intro h
    have hc := hx₀'.1.2
    rw [h] at hc
    have : D.l v = D.c := hc
    linarith [D.hvc]
  have hdim : 1 ≤ faceDim Fs := by
    have hmem : x₀ - v ∈ vectorSpan ℝ Fs := vsub_mem_vectorSpan ℝ hx₀F hvF
    have hne0 : x₀ - v ≠ 0 := sub_ne_zero.mpr hx₀v
    have hle : Submodule.span ℝ {x₀ - v} ≤ vectorSpan ℝ Fs := by
      rw [Submodule.span_le]
      exact Set.singleton_subset_iff.mpr hmem
    have h2 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hne0] at h2
    exact h2
  exact ⟨Fs, hFface, hvF, hdim, hslice⟩

/-- **LO SHIFT DIMENSIONALE**: la fetta di una faccia dello star ha
dimensione esattamente una in meno.  `vectorSpan F` si spezza come
`vectorSpan (F ∩ H) ⊔ ℝ·(p(w₀) − v)`: i due addendi si intersecano solo
nell'origine perché il primo sta nel nucleo di `l` e il secondo no. -/
theorem fetta_faceDim {F : Set (E n)} (hF : Q.IsFace F) (hvF : v ∈ F)
    (hdF : 1 ≤ faceDim F) :
    faceDim (F ∩ {x | D.l x = D.c}) + 1 = faceDim F := by
  classical
  obtain ⟨w₀, hw₀W, hw₀F⟩ := esiste_vertice_altro hF hvF hdF
  have hw₀c := D.sep_of_mem_erase hw₀W
  have hFconv : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hatt₀F : D.attra w₀ ∈ F :=
    hFconv.segment_subset hvF hw₀F (D.attra_mem_segment hw₀c)
  have hatt₀H : D.l (D.attra w₀) = D.c := D.attra_level hw₀c
  set U : Submodule ℝ (E n) := vectorSpan ℝ F with hU
  set U' : Submodule ℝ (E n) :=
    vectorSpan ℝ (F ∩ {x | D.l x = D.c}) with hU'
  set L : Submodule ℝ (E n) := Submodule.span ℝ {D.attra w₀ - v} with hL
  set K : Submodule ℝ (E n) := LinearMap.ker D.l.toLinearMap with hK
  -- inclusioni elementari
  have h1 : U' ≤ U := vectorSpan_mono ℝ Set.inter_subset_left
  have h2 : L ≤ U := by
    rw [hL, Submodule.span_le, Set.singleton_subset_iff]
    exact vsub_mem_vectorSpan ℝ hatt₀F hvF
  -- la fetta vive nel nucleo di l
  have h4 : U' ≤ K := by
    rw [hU']
    have hbase : D.attra w₀ ∈ F ∩ {x | D.l x = D.c} := ⟨hatt₀F, hatt₀H⟩
    rw [vectorSpan_eq_span_vsub_set_right ℝ hbase, Submodule.span_le]
    rintro z ⟨x, hx, rfl⟩
    have hxc : D.l x = D.c := hx.2
    rw [hK, SetLike.mem_coe, LinearMap.mem_ker]
    show D.l (x - D.attra w₀) = 0
    rw [map_sub, hxc, hatt₀H, sub_self]
  -- la retta trasversale incontra il nucleo solo nell'origine
  have h5 : L ⊓ K = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxL, hxK⟩
    rw [hL] at hxL
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxL
    have hxK' : D.l.toLinearMap (a • (D.attra w₀ - v)) = 0 := hxK
    have hval : D.l.toLinearMap (a • (D.attra w₀ - v))
        = a * (D.c - D.l v) := by
      rw [map_smul, smul_eq_mul]
      show a * D.l (D.attra w₀ - v) = _
      rw [map_sub, hatt₀H]
    rw [hval] at hxK'
    have hane : D.c - D.l v ≠ 0 := by linarith [D.hvc]
    have ha : a = 0 := by
      rcases mul_eq_zero.mp hxK' with h | h
      · exact h
      · exact absurd h hane
    rw [ha, zero_smul]
  -- lo span della faccia è generato dalla fetta più la trasversale
  have h3 : U ≤ U' ⊔ L := by
    have hfe := face_eq_hull_vertices Q hF
    have hUv : U = vectorSpan ℝ
        ((Q.vertices.filter (· ∈ F) : Finset (E n)) : Set (E n)) := by
      rw [hU]
      conv_lhs => rw [hfe]
      rw [← direction_affineSpan, affineSpan_convexHull,
        direction_affineSpan]
    have hvmem : v ∈
        ((Q.vertices.filter (· ∈ F) : Finset (E n)) : Set (E n)) := by
      exact_mod_cast Finset.mem_filter.mpr ⟨D.hv, hvF⟩
    rw [hUv, vectorSpan_eq_span_vsub_set_right ℝ hvmem, Submodule.span_le]
    rintro z ⟨u, hu, rfl⟩
    have hu' : u ∈ Q.vertices.filter (· ∈ F) := by exact_mod_cast hu
    have huV : u ∈ Q.vertices := (Finset.mem_filter.mp hu').1
    have huF : u ∈ F := (Finset.mem_filter.mp hu').2
    show u - v ∈ (U' ⊔ L : Submodule ℝ (E n))
    by_cases huv : u = v
    · subst huv
      simp
    · have huW : u ∈ Q.vertices.erase v := Finset.mem_erase.mpr ⟨huv, huV⟩
      have huc := D.sep_of_mem_erase huW
      have hattuF : D.attra u ∈ F :=
        hFconv.segment_subset hvF huF (D.attra_mem_segment huc)
      have hd1 : D.attra u - D.attra w₀ ∈ U' := by
        rw [hU']
        exact vsub_mem_vectorSpan ℝ ⟨hattuF, D.attra_level huc⟩
          ⟨hatt₀F, hatt₀H⟩
      have hd2 : D.attra w₀ - v ∈ L := by
        rw [hL]
        exact Submodule.mem_span_singleton_self _
      have hsum : D.attra u - v ∈ (U' ⊔ L : Submodule ℝ (E n)) := by
        have hsplit : D.attra u - v
            = (D.attra u - D.attra w₀) + (D.attra w₀ - v) := by abel
        rw [hsplit]
        exact Submodule.add_mem _ (Submodule.mem_sup_left hd1)
          (Submodule.mem_sup_right hd2)
      have hscal : u - v
          = ((D.l v - D.l u) / (D.l v - D.c)) • (D.attra u - v) := by
        rw [D.attra_sub u, smul_smul]
        have hden : D.l v - D.l u ≠ 0 := ne_of_gt (D.denpos huc)
        have hd : D.l v - D.c ≠ 0 := ne_of_gt D.numpos
        rw [show (D.l v - D.l u) / (D.l v - D.c)
            * ((D.l v - D.c) / (D.l v - D.l u)) = 1 by field_simp, one_smul]
      rw [hscal]
      exact Submodule.smul_mem _ _ hsum
  -- l'assemblaggio dei ranghi
  have hsup : U' ⊔ L = U := le_antisymm (sup_le h1 h2) h3
  have hinf : U' ⊓ L = ⊥ := by
    rw [← le_bot_iff, ← h5]
    exact le_inf inf_le_right (inf_le_left.trans h4)
  have hrk := Submodule.finrank_sup_add_finrank_inf_eq U' L
  rw [hsup, hinf] at hrk
  have hL1 : Module.finrank ℝ L = 1 := by
    rw [hL]
    apply finrank_span_singleton
    intro h0
    have hattv : D.attra w₀ = v := by
      have := sub_eq_zero.mp h0
      exact this
    rw [hattv] at hatt₀H
    linarith [D.hvc]
  have hbot : Module.finrank ℝ (⊥ : Submodule ℝ (E n)) = 0 := finrank_bot ℝ _
  show Module.finrank ℝ U' + 1 = Module.finrank ℝ U
  omega

end DatiFetta

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart2

section BundlePart3
/- Source: Cubical/Polytope/PoligonoConnesso.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.PoligonoConnesso.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/














/-!
FASE 3A, F9a — LA CONNETTIVITÀ DEL POLIGONO (18 lug 2026).

In un poligono (politopo di rango 2) il grafo dei vertici con gli spigoli
come lati è connesso: la camminata del simplesso con il potenziale dato
dall'espositore del vertice bersaglio. Il principio locale-globale è il
cono al vertice (ConoVertice); i vicini di un vertice sono gli altri
estremi dei suoi (esattamente due) spigoli; il massimo del potenziale è
unico per la caratterizzazione argmax del vertice esposto.

Prima un attrezzo: un vertice del politopo dentro uno spigolo-segmento ne
è un estremo (parametrizzazione + estremalità).
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Un vertice del politopo dentro un segmento ne è un estremo. -/
theorem vertice_estremo_del_segmento (P : ConvexPolytope n)
    {e : Set (E n)} (he : P.IsFace e)
    {a b : E n} (hseg : e = segment ℝ a b) (hab : a ≠ b)
    {x : E n} (hxV : x ∈ P.vertices) (hxe : x ∈ e) :
    x = a ∨ x = b := by
  classical
  by_contra hcon
  push_neg at hcon
  have hex : x ∈ e.extremePoints ℝ := vertice_estremo_in_faccia P he hxV hxe
  have hxseg : x ∈ segment ℝ a b := by
    rw [← hseg]
    exact hxe
  obtain ⟨s, t, hs, ht, hst, hx⟩ := hxseg
  have hae : a ∈ e := by
    rw [hseg]
    exact left_mem_segment ℝ a b
  have hbe : b ∈ e := by
    rw [hseg]
    exact right_mem_segment ℝ a b
  -- s e t sono entrambi positivi, altrimenti x sarebbe un estremo
  have hspos : 0 < s := by
    rcases lt_or_eq_of_le hs with h | h
    · exact h
    · exfalso
      apply hcon.2
      have ht1 : t = 1 := by
        rw [← h] at hst
        simpa using hst
      rw [← hx, ← h, ht1]
      simp
  have htpos : 0 < t := by
    rcases lt_or_eq_of_le ht with h | h
    · exact h
    · exfalso
      apply hcon.1
      have hs1 : s = 1 := by
        rw [← h] at hst
        simpa using hst
      rw [← hx, ← h, hs1]
      simp
  have hopen : x ∈ openSegment ℝ a b := ⟨s, t, hspos, htpos, hst, hx⟩
  have h2 := hex.2 hae hbe hopen
  exact hcon.1 h2.symm

/-- **LA CONNETTIVITÀ DEL POLIGONO**: due vertici qualsiasi di un poligono
sono collegati da un cammino di spigoli (la relazione: essere entrambi
vertici del politopo dentro uno spigolo comune, con estremi distinti). -/
theorem poligono_connesso (Q : ConvexPolytope n)
    (hdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2)
    {x₀ xs : E n} (hx₀ : x₀ ∈ Q.vertices) (hxs : xs ∈ Q.vertices) :
    Relation.ReflTransGen
      (fun p q => q ∈ Q.vertices ∧ p ≠ q ∧
        ∃ e : Set (E n), Q.IsFace e ∧ faceDim e = 1 ∧ p ∈ e ∧ q ∈ e)
      x₀ xs := by
  classical
  -- il potenziale: l'espositore del vertice bersaglio
  obtain ⟨l, hl⟩ := (vertex_isFace Q hxs).1 (Set.singleton_nonempty xs)
  have hxsT : xs ∈ Q.toSet := by
    have h1 : xs ∈ ({xs} : Set (E n)) := rfl
    rw [hl] at h1
    exact h1.1
  have hlmax : ∀ y ∈ Q.toSet, l y ≤ l xs := by
    have h1 : xs ∈ ({xs} : Set (E n)) := rfl
    rw [hl] at h1
    exact h1.2
  have hlchar : ∀ q ∈ Q.toSet, l q = l xs → q = xs := by
    intro q hq hlq
    have h1 : q ∈ ({xs} : Set (E n)) := by
      rw [hl]
      exact ⟨hq, fun y hy => le_trans (hlmax y hy) (le_of_eq hlq.symm)⟩
    exact h1
  -- la camminata astratta con X = vertici, adiacenza via spigoli
  have hcam := camminata_del_simplesso (α := E n) Q.vertices
    (fun p q => p ≠ q ∧
      ∃ e : Set (E n), Q.IsFace e ∧ faceDim e = 1 ∧ p ∈ e ∧ q ∈ e)
    (fun y => l y) ?_ hxs ?_ hx₀
  · -- adattamento della relazione
    refine Relation.ReflTransGen.mono ?_ _ _ hcam
    rintro p q ⟨hqX, hpq, e, he⟩
    exact ⟨hqX, hpq, e, he⟩
  · -- il principio locale-globale
    intro w hwV hloc z hzV
    -- i due spigoli di w nel poligono
    have hwT : w ∈ Q.toSet := subset_convexHull ℝ _ hwV
    have hvface : Q.IsFace ({w} : Set (E n)) := vertex_isFace Q hwV
    have hgap : faceDim ({w} : Set (E n)) + 2 ≤
        Module.finrank ℝ (vectorSpan ℝ Q.toSet) := by
      rw [faceDim_singleton, hdim]
    obtain ⟨e₁, he₁, hwe₁, he₁ne⟩ := interpolazione Q hvface hgap
    have hde₁ : faceDim e₁ = 1 := by
      have h1 := faceDim_lt_of_ssubset Q hvface he₁ hwe₁
      rw [faceDim_singleton] at h1
      have hss : e₁ ⊂ Q.toSet :=
        ⟨face_subset_toSet Q he₁, fun hsup => he₁ne
          (Set.Subset.antisymm (face_subset_toSet Q he₁) hsup)⟩
      have h2 := faceDim_lt_of_ssubset Q he₁ (toSet_isFace Q) hss
      have h3 : faceDim Q.toSet = 2 := hdim
      omega
    have hwmem₁ : w ∈ e₁ := hwe₁.subset rfl
    obtain ⟨e₂, he₂, hde₂, hwmem₂, he₂ne⟩ := secondo_spigolo Q hdim hwV
      he₁ hde₁ hwmem₁
    -- gli estremi dei due spigoli
    obtain ⟨a, haV, hae, haw, hsega⟩ := spigolo_segmento Q he₁ hde₁ hwV hwmem₁
    obtain ⟨b, hbV, hbe, hbw, hsegb⟩ := spigolo_segmento Q he₂ hde₂ hwV hwmem₂
    -- gli estremi sono vicini nel grafo: il potenziale non cresce
    have hha : l a ≤ l w := by
      apply hloc a haV
      exact ⟨fun h => haw h.symm, e₁, he₁, hde₁, hwmem₁, hae⟩
    have hhb : l b ≤ l w := by
      apply hloc b hbV
      exact ⟨fun h => hbw h.symm, e₂, he₂, hde₂, hwmem₂, hbe⟩
    -- il locale-globale del cono
    have := locale_globale Q hdim hwV he₁ hde₁ he₂ hde₂
      (fun h => he₂ne h.symm) hae haw hsega hbe hbw hsegb hwmem₁ hwmem₂
      l hha hhb
    exact this z (subset_convexHull ℝ _ hzV)
  · -- il massimo è unico
    intro z hzV hzne
    have hzT : z ∈ Q.toSet := subset_convexHull ℝ _ hzV
    rcases lt_or_eq_of_le (hlmax z hzT) with h | h
    · exact h
    · exact absurd (hlchar z hzT h) hzne

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart3

section BundlePart4
/- Source: Cubical/Polytope/ConnettivitaRidgeBase.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ConnettivitaRidgeBase.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




/-!
CONNETTIVITÀ DEL RIDGE-GRAPH — BASE BIDIMENSIONALE (20 lug 2026).

In una faccia `B` di dimensione intrinseca due, le faccette sono gli
spigoli.  Si sceglie un vertice su ciascuno spigolo e si usa la
connettività del grafo dei vertici del sotto-politopo `B`.  Ogni passo
del cammino di vertici fornisce uno spigolo; lo spigolo corrente e quello
nuovo condividono la zero-faccia data dal vertice corrente.

Il risultato è ambientale (`E n` per `n` arbitrario), non richiede piena
dimensionalità né regolarità, ed ha esattamente la relazione richiesta da
`RidgeConnectedAboveOne`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La base `faceDim B = 2` del muro locale delle ridge. -/
theorem ridgeConnected_in_faceDim_two (P : ConvexPolytope n)
    (B : Set (E n)) (hB : P.IsFace B) (hdB : faceDim B = 2) :
    ∀ (A A' : Set (E n)), P.IsFace A → P.IsFace A' →
      A ⊂ B → A' ⊂ B →
      faceDim A + 1 = faceDim B → faceDim A' + 1 = faceDim B →
      Relation.ReflTransGen
        (fun X Y : Set (E n) =>
          P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
            faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
            ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
              faceDim R + 2 = faceDim B)
        A A' := by
  classical
  intro A A' hA hA' hAB hA'B hdA hdA'
  let Q : ConvexPolytope n := facePolytope P hB
  have hQT : Q.toSet = B := facePolytope_toSet P hB
  have hAQ : Q.IsFace A := facePolytope_isFace_of P hB hA hAB.1
  have hA'Q : Q.IsFace A' := facePolytope_isFace_of P hB hA' hA'B.1
  have hdAone : faceDim A = 1 := by omega
  have hdA'one : faceDim A' = 1 := by omega
  obtain ⟨x, hx⟩ := (facePolytope Q hAQ).vertices_nonempty
  obtain ⟨x', hx'⟩ := (facePolytope Q hA'Q).vertices_nonempty
  have hxQ : x ∈ Q.vertices := (Finset.mem_filter.mp hx).1
  have hxA : x ∈ A := (Finset.mem_filter.mp hx).2
  have hx'Q : x' ∈ Q.vertices := (Finset.mem_filter.mp hx').1
  have hx'A' : x' ∈ A' := (Finset.mem_filter.mp hx').2
  have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2 := by
    rw [hQT]
    exact hdB
  let VertRel : E n → E n → Prop := fun p q =>
    q ∈ Q.vertices ∧ p ≠ q ∧
      ∃ e : Set (E n), Q.IsFace e ∧ faceDim e = 1 ∧ p ∈ e ∧ q ∈ e
  let RidgeRel : Set (E n) → Set (E n) → Prop := fun X Y =>
    P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
      faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
      ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
        faceDim R + 2 = faceDim B
  have edge_in_B : ∀ {e : Set (E n)}, Q.IsFace e → faceDim e = 1 →
      P.IsFace e ∧ e ⊂ B := by
    intro e he hde
    have heP : P.IsFace e := isFace_of_facePolytope P hB he
    have heBsub : e ⊆ B := by
      rw [← hQT]
      exact face_subset_toSet Q he
    refine ⟨heP, heBsub.ssubset_of_ne ?_⟩
    intro heq
    have hdim := congrArg faceDim heq
    rw [hde, hdB] at hdim
    omega
  have ridge_step_at_vertex : ∀ {p : E n} {X Y : Set (E n)},
      p ∈ Q.vertices → P.IsFace X → faceDim X = 1 → X ⊂ B → p ∈ X →
      P.IsFace Y → faceDim Y = 1 → Y ⊂ B → p ∈ Y → RidgeRel X Y := by
    intro p X Y hpQ hX hdX hXB hpX hY hdY hYB hpY
    have hpFaceQ : Q.IsFace ({p} : Set (E n)) := vertex_isFace Q hpQ
    have hpFaceP : P.IsFace ({p} : Set (E n)) :=
      isFace_of_facePolytope P hB hpFaceQ
    have hpXstrict : ({p} : Set (E n)) ⊂ X := by
      refine (Set.singleton_subset_iff.mpr hpX).ssubset_of_ne ?_
      intro heq
      have hdim := congrArg faceDim heq
      rw [faceDim_singleton, hdX] at hdim
      omega
    have hpYstrict : ({p} : Set (E n)) ⊂ Y := by
      refine (Set.singleton_subset_iff.mpr hpY).ssubset_of_ne ?_
      intro heq
      have hdim := congrArg faceDim heq
      rw [faceDim_singleton, hdY] at hdim
      omega
    exact ⟨hX, hY, hXB, hYB, by omega, by omega,
      {p}, hpFaceP, hpXstrict, hpYstrict, by
        rw [faceDim_singleton, hdB]⟩
  have hverts : Relation.ReflTransGen VertRel x x' := by
    exact poligono_connesso Q hQdim hxQ hx'Q
  have transfer : ∀ {q : E n}, Relation.ReflTransGen VertRel x q →
      ∃ X : Set (E n),
        Relation.ReflTransGen RidgeRel A X ∧
        P.IsFace X ∧ faceDim X = 1 ∧ X ⊂ B ∧ q ∈ Q.vertices ∧ q ∈ X := by
    intro q hpath
    induction hpath with
    | refl =>
        exact ⟨A, Relation.ReflTransGen.refl, hA, hdAone, hAB, hxQ, hxA⟩
    | @tail p q hprev hstep ih =>
        obtain ⟨X, hAX, hX, hdX, hXB, hpQ, hpX⟩ := ih
        obtain ⟨hqQ, _hpq, e, heQ, hde, hpe, hqe⟩ := hstep
        obtain ⟨heP, heB⟩ := edge_in_B heQ hde
        have hstep' : RidgeRel X e :=
          ridge_step_at_vertex hpQ hX hdX hXB hpX heP hde heB hpe
        exact ⟨e, hAX.tail hstep', heP, hde, heB, hqQ, hqe⟩
  obtain ⟨X, hAX, hX, hdX, hXB, hx'Q', hx'X⟩ := transfer hverts
  have hlast : RidgeRel X A' :=
    ridge_step_at_vertex hx'Q' hX hdX hXB hx'X hA' hdA'one hA'B hx'A'
  exact hAX.tail hlast

/-- La base bidimensionale, già confezionata come restrizione di
`RidgeConnectedAboveOne`. -/
theorem ridgeConnectedAboveOne_dim_two (P : ConvexPolytope n) :
    ∀ (B : Set (E n)), P.IsFace B → faceDim B = 2 →
      ∀ (A A' : Set (E n)), P.IsFace A → P.IsFace A' →
        A ⊂ B → A' ⊂ B →
        faceDim A + 1 = faceDim B → faceDim A' + 1 = faceDim B →
        Relation.ReflTransGen
          (fun X Y : Set (E n) =>
            P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
              faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
              ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
                faceDim R + 2 = faceDim B)
          A A' := by
  intro B hB hdB
  exact ridgeConnected_in_faceDim_two P B hB hdB

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart4

section BundlePart5
/- Source: Cubical/Polytope/SecondaFaccetta.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.SecondaFaccetta.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/










/-!
FASE 3A — LA SECONDA FACCETTA (18 lug 2026).

Il lato «almeno due» del diamante: in un politopo full-dim di ℝ³, ogni
spigolo contenuto in una faccetta A sta anche in una seconda faccetta ≠ A.
Stesso perno esplicito del secondo spigolo, un gradino sopra: w ≠ 0 nel
complemento ortogonale di vectorSpan A, ψ = l_δ + t*·⟪w,·⟫ col rapporto
critico sui vertici del lato buono. ⟪w,·⟫ è costante su A ma l_δ vi morde
(un punto a₁ ∈ A ∖ δ sta strettamente sotto il massimo), quindi un punto
di A dentro l'argmax è assurdo: questo esclude in un colpo solo F = corpo
e F = A. L'argmax contiene δ e il vertice critico fuori dallo span di δ,
quindi ha rango ≥ 2: è la seconda faccetta.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **LA SECONDA FACCETTA**: in un politopo full-dim di ℝ³ ogni spigolo di
una faccetta sta anche in un'altra faccetta. -/
theorem seconda_faccetta (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {δ : Set (E 3)} (hδ : P.IsFace δ) (hdδ : faceDim δ = 1)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) (hδA : δ ⊆ A) :
    ∃ A' : Set (E 3), P.IsFace A' ∧ faceDim A' = 2 ∧ δ ⊆ A' ∧ A' ≠ A := by
  classical
  -- l'espositore dello spigolo
  obtain ⟨l, hl⟩ := hδ.1 hδ.2
  obtain ⟨p₀, hp₀δ⟩ := hδ.2
  have hp₀T : p₀ ∈ P.toSet := by
    have := hp₀δ
    rw [hl] at this
    exact this.1
  have hlmax : ∀ y ∈ P.toSet, l y ≤ l p₀ := by
    have := hp₀δ
    rw [hl] at this
    exact this.2
  have hlchar : ∀ q ∈ P.toSet, l q = l p₀ → q ∈ δ := by
    intro q hq hlq
    rw [hl]
    exact ⟨hq, fun y hy => le_trans (hlmax y hy) (le_of_eq hlq.symm)⟩
  have hlconst : ∀ z ∈ δ, l z = l p₀ := by
    intro z hz
    have hz' := hz
    rw [hl] at hz'
    exact le_antisymm (hlmax z hz'.1) (hz'.2 p₀ hp₀T)
  -- il punto di A fuori da δ
  have ha₁ : ∃ a₁ ∈ A, a₁ ∉ δ := by
    by_contra hall
    push_neg at hall
    have hsub : A ⊆ δ := hall
    have hle := vectorSpan_mono ℝ hsub
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank ℝ (vectorSpan ℝ A) = 2 := hdA
    have h3 : Module.finrank ℝ (vectorSpan ℝ δ) = 1 := hdδ
    omega
  obtain ⟨a₁, ha₁A, ha₁δ⟩ := ha₁
  have ha₁T : a₁ ∈ P.toSet := face_subset_toSet P hA ha₁A
  have ha₁lt : l a₁ < l p₀ := by
    rcases lt_or_eq_of_le (hlmax a₁ ha₁T) with h | h
    · exact h
    · exact absurd (hlchar a₁ ha₁T h) ha₁δ
  -- w non nullo ortogonale allo span della faccetta
  have hwex : ∃ w : E 3, w ∈ (vectorSpan ℝ A)ᗮ ∧ w ≠ 0 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal
      (K := vectorSpan ℝ A)
    have hdA' : Module.finrank ℝ (vectorSpan ℝ A) = 2 := hdA
    have hE : Module.finrank ℝ (E 3) = 3 := by
      rw [finrank_euclideanSpace]
      simp
    have hperp : 1 ≤ Module.finrank ℝ (vectorSpan ℝ A)ᗮ := by omega
    have hne : (vectorSpan ℝ A)ᗮ ≠ ⊥ := by
      intro h
      rw [h] at hperp
      simp [finrank_bot] at hperp
    obtain ⟨w, hwmem, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨w, hwmem, hwne⟩
  obtain ⟨w, hwperp, hwne⟩ := hwex
  -- ⟪w,·⟫ è costante su A
  have hwconstA : ∀ z ∈ A, ∀ z' ∈ A, ⟪w, z⟫ = ⟪w, z'⟫ := by
    intro z hz z' hz'
    have hmem : z - z' ∈ vectorSpan ℝ A := vsub_mem_vectorSpan ℝ hz hz'
    have h1 : ⟪z - z', w⟫ = 0 := by
      have := (Submodule.mem_orthogonal (vectorSpan ℝ A) w).mp hwperp
      exact this (z - z') hmem
    rw [real_inner_comm] at h1
    rw [inner_sub_right] at h1
    linarith
  -- w vive nello span del corpo (full-dim ⟹ tutto)
  have hwW : w ∈ vectorSpan ℝ P.toSet := by
    have htop : vectorSpan ℝ P.toSet = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
      rw [h1, finrank_euclideanSpace]
      simp
    rw [htop]
    trivial
  obtain ⟨u₀, hu₀V, hu₀ne⟩ := exists_vertex_inner_ne P hp₀T hwW hwne
  -- costruzione parametrizzata dal segno
  have costruzione : ∀ w' : E 3, (∀ z ∈ A, ∀ z' ∈ A, ⟪w', z⟫ = ⟪w', z'⟫) →
      (∃ u ∈ P.vertices, ⟪w', p₀⟫ < ⟪w', u⟫) →
      ∃ A' : Set (E 3), P.IsFace A' ∧ faceDim A' = 2 ∧ δ ⊆ A' ∧ A' ≠ A := by
    intro w' hw'A hup
    obtain ⟨ux, huxV, huxgt⟩ := hup
    set S : Finset (E 3) := P.vertices.filter (fun u => ⟪w', p₀⟫ < ⟪w', u⟫)
      with hS
    have hSne : S.Nonempty := ⟨ux, Finset.mem_filter.mpr ⟨huxV, huxgt⟩⟩
    set r : E 3 → ℝ := fun u => (l p₀ - l u) / (⟪w', u⟫ - ⟪w', p₀⟫) with hr
    obtain ⟨us, husS, husmin⟩ := S.exists_min_image r hSne
    have husV : us ∈ P.vertices := (Finset.mem_filter.mp husS).1
    have husgt : ⟪w', p₀⟫ < ⟪w', us⟫ := (Finset.mem_filter.mp husS).2
    have husT : us ∈ P.toSet := subset_convexHull ℝ _ husV
    have husδ : us ∉ δ := by
      intro h
      have h1 := hw'A us (hδA h) p₀ (hδA hp₀δ)
      rw [h1] at husgt
      exact lt_irrefl _ husgt
    have huslt : l us < l p₀ := by
      rcases lt_or_eq_of_le (hlmax us husT) with h | h
      · exact h
      · exact absurd (hlchar us husT h) husδ
    set t : ℝ := r us with ht
    have htpos : 0 < t := by
      rw [ht, hr]
      apply div_pos
      · linarith
      · linarith
    set ψ : E 3 →L[ℝ] ℝ := l + t • innerSL ℝ w' with hψ
    have hψval : ∀ y : E 3, ψ y = l y + t * ⟪w', y⟫ := by
      intro y
      rw [hψ]
      simp
    have hvert : ∀ u ∈ P.vertices, ψ u ≤ ψ p₀ := by
      intro u huV
      rw [hψval, hψval]
      by_cases hside : ⟪w', p₀⟫ < ⟪w', u⟫
      · have huS : u ∈ S := Finset.mem_filter.mpr ⟨huV, hside⟩
        have hrle : t ≤ r u := husmin u huS
        have hgap : (0:ℝ) < ⟪w', u⟫ - ⟪w', p₀⟫ := by linarith
        have h1 : t * (⟪w', u⟫ - ⟪w', p₀⟫) ≤ r u * (⟪w', u⟫ - ⟪w', p₀⟫) :=
          mul_le_mul_of_nonneg_right hrle (le_of_lt hgap)
        have h2 : r u * (⟪w', u⟫ - ⟪w', p₀⟫) = l p₀ - l u := by
          show (l p₀ - l u) / (⟪w', u⟫ - ⟪w', p₀⟫) * (⟪w', u⟫ - ⟪w', p₀⟫) =
            l p₀ - l u
          exact div_mul_cancel₀ _ (ne_of_gt hgap)
        nlinarith
      · push_neg at hside
        have h1 : l u ≤ l p₀ := hlmax u (subset_convexHull ℝ _ huV)
        have h2 : t * ⟪w', u⟫ ≤ t * ⟪w', p₀⟫ :=
          mul_le_mul_of_nonneg_left hside (le_of_lt htpos)
        linarith
    have hbody : ∀ y ∈ P.toSet, ψ y ≤ ψ p₀ := by
      intro y hy
      have hconv : Convex ℝ {z : E 3 | ψ z ≤ ψ p₀} := by
        apply convex_halfSpace_le
        exact ψ.toLinearMap.isLinear
      have hsub : (P.vertices : Set (E 3)) ⊆ {z : E 3 | ψ z ≤ ψ p₀} := by
        intro u hu
        exact hvert u (Finset.mem_coe.mp hu)
      exact convexHull_min hsub hconv hy
    -- ψ è costante su δ (entrambi i pezzi lo sono)
    have hψδ : ∀ z ∈ δ, ψ z = ψ p₀ := by
      intro z hz
      rw [hψval, hψval, hlconst z hz, hw'A z (hδA hz) p₀ (hδA hp₀δ)]
    set F : Set (E 3) := {x ∈ P.toSet | ∀ y ∈ P.toSet, ψ y ≤ ψ x} with hF
    have hδF : δ ⊆ F := by
      intro z hz
      refine ⟨face_subset_toSet P hδ hz, ?_⟩
      intro y hy
      rw [hψδ z hz]
      exact hbody y hy
    have hp₀F : p₀ ∈ F := hδF hp₀δ
    have hFface : P.IsFace F := ⟨fun _ => ⟨ψ, rfl⟩, ⟨p₀, hp₀F⟩⟩
    -- il vertice critico è in F
    have htie : ψ us = ψ p₀ := by
      rw [hψval, hψval]
      have hgap : (0:ℝ) < ⟪w', us⟫ - ⟪w', p₀⟫ := by linarith
      have h2 : t * (⟪w', us⟫ - ⟪w', p₀⟫) = l p₀ - l us := by
        show (l p₀ - l us) / (⟪w', us⟫ - ⟪w', p₀⟫) * (⟪w', us⟫ - ⟪w', p₀⟫) =
          l p₀ - l us
        exact div_mul_cancel₀ _ (ne_of_gt hgap)
      nlinarith [h2]
    have husF : us ∈ F := by
      refine ⟨husT, ?_⟩
      intro y hy
      rw [htie]
      exact hbody y hy
    -- il punto a₁ di A non può stare in F
    have ha₁F : a₁ ∉ F := by
      intro hmem
      have h1 : ψ a₁ = ψ p₀ :=
        le_antisymm (hbody a₁ ha₁T) (hmem.2 p₀ hp₀T)
      rw [hψval, hψval] at h1
      have h2 : ⟪w', a₁⟫ = ⟪w', p₀⟫ := hw'A a₁ ha₁A p₀ (hδA hp₀δ)
      have h4 : l a₁ = l p₀ := by
        rw [h2] at h1
        linarith
      exact ha₁δ (hlchar a₁ ha₁T h4)
    have hFneT : F ≠ P.toSet := by
      intro h
      exact ha₁F (h ▸ ha₁T)
    have hFneA : F ≠ A := by
      intro h
      exact ha₁F (h ▸ ha₁A)
    -- l è costante sullo span affine di δ
    have hconstspan : ∀ y ∈ affineSpan ℝ δ, l y = l p₀ := by
      intro y hy
      have heqon : Set.EqOn (⇑l.toLinearMap.toAffineMap)
          (⇑(AffineMap.const ℝ (E 3) (l p₀))) δ := by
        intro z hz
        simp [hlconst z hz]
      have h2 := AffineMap.eqOn_affineSpan (k := ℝ) heqon
      have := h2 hy
      simpa using this
    -- il secondo punto di δ e l'indipendenza dei due spostamenti
    obtain ⟨z₁, hz₁δ, hz₁p₀⟩ := faccia_ha_secondo_punto hdδ (v := p₀)
    have hLI : LinearIndependent ℝ ![us - p₀, z₁ - p₀] := by
      rw [linearIndependent_fin2]
      constructor
      · show z₁ - p₀ ≠ 0
        exact sub_ne_zero.mpr hz₁p₀
      · intro a
        show a • (z₁ - p₀) ≠ us - p₀
        intro heq
        have hmem : us ∈ affineSpan ℝ δ := by
          have h1 : a • (z₁ -ᵥ p₀) +ᵥ p₀ ∈ affineSpan ℝ δ :=
            AffineSubspace.smul_vsub_vadd_mem _ a
              (subset_affineSpan ℝ _ hz₁δ)
              (subset_affineSpan ℝ _ hp₀δ)
              (subset_affineSpan ℝ _ hp₀δ)
          have h2 : a • (z₁ -ᵥ p₀) +ᵥ p₀ = us := by
            have h3 : us - p₀ = a • (z₁ - p₀) := heq.symm
            have h4 : us = a • (z₁ - p₀) + p₀ := by
              have := congrArg (fun q => q + p₀) h3
              simpa using this
            rw [h4]
            rfl
          rw [h2] at h1
          exact h1
        have h5 : l us = l p₀ := hconstspan us hmem
        exact husδ (hlchar us husT h5)
    -- rango ≥ 2 per F
    have hsl : Submodule.span ℝ (Set.range ![us - p₀, z₁ - p₀]) ≤
        vectorSpan ℝ F := by
      rw [Submodule.span_le]
      rintro z ⟨i, rfl⟩
      rcases i with ⟨iv, hi⟩
      interval_cases iv
      · show (![us - p₀, z₁ - p₀] : Fin 2 → E 3) 0 ∈ vectorSpan ℝ F
        show us - p₀ ∈ vectorSpan ℝ F
        exact vsub_mem_vectorSpan ℝ husF hp₀F
      · show (![us - p₀, z₁ - p₀] : Fin 2 → E 3) 1 ∈ vectorSpan ℝ F
        show z₁ - p₀ ∈ vectorSpan ℝ F
        exact vsub_mem_vectorSpan ℝ (hδF hz₁δ) hp₀F
    have hd2le : 2 ≤ Module.finrank ℝ (vectorSpan ℝ F) := by
      have h1 : Module.finrank ℝ (Submodule.span ℝ
          (Set.range ![us - p₀, z₁ - p₀])) = 2 := by
        rw [finrank_span_eq_card hLI]
        simp
      have h2 := Submodule.finrank_mono hsl
      omega
    have hdlt : Module.finrank ℝ (vectorSpan ℝ F) < 3 := by
      have hss : F ⊂ P.toSet :=
        ⟨fun x hx => hx.1, fun hsup => hFneT
          (Set.Subset.antisymm (fun x hx => hx.1) hsup)⟩
      have h1 := faceDim_lt_of_ssubset P hFface (toSet_isFace P) hss
      have h2 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
      have h3 : Module.finrank ℝ (vectorSpan ℝ F) <
          Module.finrank ℝ (vectorSpan ℝ P.toSet) := h1
      omega
    refine ⟨F, hFface, ?_, hδF, hFneA⟩
    show Module.finrank ℝ (vectorSpan ℝ F) = 2
    omega
  -- il segno giusto
  rcases lt_or_gt_of_ne hu₀ne with hlt | hgt
  · apply costruzione (-w)
    · intro z hz z' hz'
      rw [inner_neg_left, inner_neg_left, hwconstA z hz z' hz']
    · refine ⟨u₀, hu₀V, ?_⟩
      rw [inner_neg_left, inner_neg_left]
      linarith
  · exact costruzione w hwconstA ⟨u₀, hu₀V, hgt⟩

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart5

section BundlePart6
/- Source: Cubical/Polytope/Fondamenta.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Fondamenta.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/


/-!
CAMPAGNA #50 — MODULO DEFINIZIONI (disegno del gate cieco, 17 lug 2026).

Le nozioni su cui vive il teorema `cyclicallyRegular_schlafli`:

* `FiniteConvexPolytope A` — hull convesso di un insieme finito i cui vertici
  dichiarati sono ESATTAMENTE i punti estremi (lo stesso patto del benchmark
  lean-eval, ma su spazio astratto A: si vincola l'oggetto, non l'ambiente).
* `IsFace` / `IsFacet` — facce esposte non vuote; faccette = facce di span 2D.
* `IsRegularFacet` — poligono regolare PER ORBITA di una rotazione: niente
  liste di angoli postulategli dentro (la riparazione anti-trappola del gate).
  La congruenza dei lati consecutivi è GRATIS dall'isometria.
* `CyclicVertexData` / `IsCyclicVertex` — il fan di q faccette attorno a un
  vertice, permutato ciclicamente da un'isometria che fissa il vertice e
  preserva il politopo.
* `IsCyclicallyRegularOfType` — il predicato del teorema di classificazione.

La disuguaglianza angolare NON compare in alcuna definizione: è il TEOREMA
(kill-gate `spike_somma_sotto_due_pi`, già kernel-certificato al giorno zero).
-/

open Set Metric
open scoped RealInnerProductSpace

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- Un politopo convesso su uno spazio con prodotto interno reale: hull convesso
di un insieme finito non vuoto di punti, i cui vertici dichiarati sono
esattamente i punti estremi dell'hull. -/
structure FiniteConvexPolytope (A : Type*) [NormedAddCommGroup A]
    [InnerProductSpace ℝ A] where
  vertices : Finset A
  nonempty : vertices.Nonempty
  vertices_eq_extremePoints :
    (vertices : Set A) = (convexHull ℝ (vertices : Set A)).extremePoints ℝ

namespace FiniteConvexPolytope

variable (P : FiniteConvexPolytope A)

/-- Il corpo convesso del politopo. -/
def toSet : Set A := convexHull ℝ (P.vertices : Set A)

/-- Una faccia: sottoinsieme esposto e non vuoto del corpo. -/
def IsFace (F : Set A) : Prop :=
  IsExposed ℝ P.toSet F ∧ F.Nonempty

/-- Una faccetta: faccia il cui span direzionale è un piano. -/
def IsFacet (F : Set A) : Prop :=
  P.IsFace F ∧ Module.finrank ℝ (vectorSpan ℝ F) = 2

/-- Faccetta p-gonale REGOLARE, definita per orbita: esiste un'isometria affine
ρ che manda la faccetta in sé, il cui ciclo su un vertice di partenza ha
esattamente p punti distinti, chiude dopo p passi, genera la faccetta come hull
convesso, e ha passo di lunghezza ℓ. La congruenza di TUTTI i lati consecutivi
segue gratis dall'isometria; nessun angolo è postulato. -/
def IsRegularFacet (F : Set A) (p : ℕ) (ℓ : ℝ) : Prop :=
  P.IsFacet F ∧ 0 < ℓ ∧ 3 ≤ p ∧
  ∃ (ρ : A ≃ᵃⁱ[ℝ] A) (x₀ : A),
    x₀ ∈ F ∧
    (⇑ρ) '' F = F ∧
    Function.Injective (fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀) ∧
    (⇑ρ)^[p] x₀ = x₀ ∧
    F = convexHull ℝ (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀) ∧
    dist x₀ (ρ x₀) = ℓ

/-- I dati di un vertice q-ciclico: le faccette incidenti a v enumerate da
`Fin q`, un'isometria σ che fissa v, preserva il politopo e ruota il fan di un
passo, e la completezza locale del fan (faccette consecutive condividono uno
spigolo per v: il loro incontro contiene v e un punto ulteriore). -/
structure CyclicVertexData (v : A) (q : ℕ) where
  /-- l'enumerazione ciclica delle faccette incidenti a v -/
  faccetta : Fin q → Set A
  isFacet : ∀ i, P.IsFacet (faccetta i)
  mem_v : ∀ i, v ∈ faccetta i
  distinte : Function.Injective faccetta
  complete : ∀ F : Set A, P.IsFacet F → v ∈ F → ∃ i, F = faccetta i
  /-- la simmetria ciclica locale -/
  σ : A ≃ᵃⁱ[ℝ] A
  fissa_v : σ v = v
  preserva : (⇑σ) '' P.toSet = P.toSet
  ruota : ∀ i : Fin q, (⇑σ) '' faccetta i = faccetta (finRotate q i)
  /-- faccette consecutive si toccano in uno spigolo per v, non solo in v -/
  spigolo : ∀ i : Fin q,
    ∃ x, x ≠ v ∧ x ∈ faccetta i ∩ faccetta (finRotate q i)
  /-- struttura di fan (pseudovarietà): un punto di spigolo diverso da v
  appartiene SOLO alle due faccette che quello spigolo condividono. Nessun
  angolo, nessun conteggio: è la proprietà «ogni spigolo ha due facce». -/
  spigolo_due : ∀ i j : Fin q, ∀ x,
    x ∈ faccetta i ∩ faccetta (finRotate q i) → x ≠ v →
    x ∈ faccetta j → j = i ∨ j = finRotate q i

/-- Vertice q-ciclico (forma proposizionale). -/
def IsCyclicVertex (v : A) (q : ℕ) : Prop :=
  Nonempty (P.CyclicVertexData v q)

/-- Il predicato del teorema di classificazione: politopo 3-dimensionale con
faccette p-gonali regolari di lato comune ℓ e ogni vertice q-ciclico. -/
def IsCyclicallyRegularOfType (p q : ℕ) : Prop :=
  Module.finrank ℝ (vectorSpan ℝ (P.vertices : Set A)) = 3 ∧
  3 ≤ p ∧ 3 ≤ q ∧
  ∃ ℓ > 0,
    (∀ F, P.IsFacet F → P.IsRegularFacet F p ℓ) ∧
    (∀ v ∈ P.vertices, P.IsCyclicVertex v q)

end FiniteConvexPolytope

/-- Due faccette distinte passanti per un punto estremo si incontrano, da quel
punto, lungo un'unica semiretta: due loro punti non estremi hanno vettori
radiali positivamente proporzionali. -/
theorem intersezione_spigolo_semiretta (P : FiniteConvexPolytope A)
    {F G : Set A} (hF : P.IsFacet F) (hG : P.IsFacet G) (hFG : F ≠ G)
    {v : A} (hvF : v ∈ F) (hvG : v ∈ G)
    (hvex : v ∈ P.toSet.extremePoints ℝ)
    {x y : A} (hx : x ∈ F ∩ G) (hy : y ∈ F ∩ G) (hxv : x ≠ v) (hyv : y ≠ v) :
    ∃ c : ℝ, 0 < c ∧ y - v = c • (x - v) := by
  have hvI : v ∈ F ∩ G := ⟨hvF, hvG⟩
  have hxsub : x - v ≠ 0 := sub_ne_zero.mpr hxv
  have hdep : ¬LinearIndependent ℝ ![x - v, y - v] := by
    intro hli
    let S : Submodule ℝ A := vectorSpan ℝ (F ∩ G)
    have hSF : S ≤ vectorSpan ℝ F := vectorSpan_mono ℝ inter_subset_left
    have hxS : x - v ∈ S := vsub_mem_vectorSpan ℝ hx hvI
    have hyS : y - v ∈ S := vsub_mem_vectorSpan ℝ hy hvI
    have hSfin : FiniteDimensional ℝ S := by
      letI : FiniteDimensional ℝ (vectorSpan ℝ F) :=
        FiniteDimensional.of_finrank_pos (by rw [hF.2]; norm_num)
      exact FiniteDimensional.of_injective (Submodule.inclusion hSF)
        (Submodule.inclusion_injective hSF)
    letI : FiniteDimensional ℝ S := hSfin
    let b : Fin 2 → S := ![⟨x - v, hxS⟩, ⟨y - v, hyS⟩]
    have hlib : LinearIndependent ℝ b := by
      apply LinearIndependent.of_comp S.subtype
      have hb : S.subtype ∘ b = ![x - v, y - v] := by
        funext k
        fin_cases k <;> rfl
      rw [hb]
      exact hli
    have hSge : 2 ≤ Module.finrank ℝ S := by
      simpa using hlib.fintype_card_le_finrank
    have hSle : Module.finrank ℝ S ≤ 2 := by
      letI : FiniteDimensional ℝ (vectorSpan ℝ F) :=
        FiniteDimensional.of_finrank_pos (by rw [hF.2]; norm_num)
      simpa [hF.2] using Submodule.finrank_mono hSF
    have hSrank : Module.finrank ℝ S = 2 := le_antisymm hSle hSge
    have hspanF : vectorSpan ℝ (F ∩ G) = vectorSpan ℝ F := by
      letI : FiniteDimensional ℝ (vectorSpan ℝ F) :=
        FiniteDimensional.of_finrank_pos (by rw [hF.2]; norm_num)
      exact Submodule.eq_of_le_of_finrank_eq hSF (hSrank.trans hF.2.symm)
    have hSG : S ≤ vectorSpan ℝ G := vectorSpan_mono ℝ inter_subset_right
    have hspanG : vectorSpan ℝ (F ∩ G) = vectorSpan ℝ G := by
      letI : FiniteDimensional ℝ (vectorSpan ℝ G) :=
        FiniteDimensional.of_finrank_pos (by rw [hG.2]; norm_num)
      exact Submodule.eq_of_le_of_finrank_eq hSG (hSrank.trans hG.2.symm)
    have haffF : affineSpan ℝ (F ∩ G) = affineSpan ℝ F := by
      apply AffineSubspace.ext_of_direction_eq
      · simpa only [direction_affineSpan] using hspanF
      · exact ⟨v, mem_affineSpan ℝ hvI, mem_affineSpan ℝ hvF⟩
    have haffG : affineSpan ℝ (F ∩ G) = affineSpan ℝ G := by
      apply AffineSubspace.ext_of_direction_eq
      · simpa only [direction_affineSpan] using hspanG
      · exact ⟨v, mem_affineSpan ℝ hvI, mem_affineSpan ℝ hvG⟩
    have hFGsub : F ⊆ G := by
      obtain ⟨l, hGl⟩ := hG.1.1 ⟨v, hvG⟩
      have hvmax := hvG
      rw [hGl] at hvmax
      let H : AffineSubspace ℝ A := AffineSubspace.mk' v l.ker
      have hIH : affineSpan ℝ (F ∩ G) ≤ H := by
        apply affineSpan_le.2
        intro z hz
        have hzmax := hz.2
        rw [hGl] at hzmax
        have hlz : l z = l v := le_antisymm (hvmax.2 z hzmax.1) (hzmax.2 v hvmax.1)
        change z - v ∈ l.ker
        change l (z - v) = 0
        rw [map_sub, hlz, sub_self]
      intro z hzF
      have hzH : z ∈ H := hIH (haffF.symm ▸ mem_affineSpan ℝ hzF)
      have hlz : l z = l v := by
        change z - v ∈ l.ker at hzH
        change l (z - v) = 0 at hzH
        rwa [map_sub, sub_eq_zero] at hzH
      rw [hGl]
      exact ⟨hF.1.1.subset hzF, fun w hw => (hvmax.2 w hw).trans_eq hlz.symm⟩
    have hGFsub : G ⊆ F := by
      obtain ⟨l, hFl⟩ := hF.1.1 ⟨v, hvF⟩
      have hvmax := hvF
      rw [hFl] at hvmax
      let H : AffineSubspace ℝ A := AffineSubspace.mk' v l.ker
      have hIH : affineSpan ℝ (F ∩ G) ≤ H := by
        apply affineSpan_le.2
        intro z hz
        have hzmax := hz.1
        rw [hFl] at hzmax
        have hlz : l z = l v := le_antisymm (hvmax.2 z hzmax.1) (hzmax.2 v hvmax.1)
        change z - v ∈ l.ker
        change l (z - v) = 0
        rw [map_sub, hlz, sub_self]
      intro z hzG
      have hzH : z ∈ H := hIH (haffG.symm ▸ mem_affineSpan ℝ hzG)
      have hlz : l z = l v := by
        change z - v ∈ l.ker at hzH
        change l (z - v) = 0 at hzH
        rwa [map_sub, sub_eq_zero] at hzH
      rw [hFl]
      exact ⟨hG.1.1.subset hzG, fun w hw => (hvmax.2 w hw).trans_eq hlz.symm⟩
    exact hFG (Set.Subset.antisymm hFGsub hGFsub)
  rw [LinearIndependent.pair_iff' hxsub] at hdep
  push Not at hdep
  obtain ⟨c, hc⟩ := hdep
  have hrel : y - v = c • (x - v) := hc.symm
  have hc0 : c ≠ 0 := by
    intro hczero
    apply hyv
    apply sub_eq_zero.mp
    rw [hrel, hczero, zero_smul]
  have hc_nonneg : 0 ≤ c := by
    by_contra hcn
    have hcneg : c < 0 := lt_of_not_ge hcn
    have hden : 1 - c ≠ 0 := by linarith
    have htpos : 0 < (1 - c)⁻¹ := inv_pos.mpr (by linarith)
    have htlt : (1 - c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    have hscalar : (1 - c)⁻¹ * (c - 1) + 1 = 0 := by
      field_simp [hden]
      ring
    have hline : AffineMap.lineMap x y ((1 - c)⁻¹ : ℝ) = v := by
      apply sub_eq_zero.mp
      calc
        AffineMap.lineMap x y ((1 - c)⁻¹ : ℝ) - v =
            (1 - c)⁻¹ • (y - x) + x - v := by rw [AffineMap.lineMap_apply_module']
        _ = (1 - c)⁻¹ • ((y - v) - (x - v)) + (x - v) := by module
        _ = (1 - c)⁻¹ • (c • (x - v) - (x - v)) + (x - v) := by rw [hrel]
        _ = ((1 - c)⁻¹ * (c - 1) + 1) • (x - v) := by module
        _ = 0 := by rw [hscalar, zero_smul]
    have hvopen : v ∈ openSegment ℝ x y := by
      rw [← hline]
      exact lineMap_mem_openSegment ℝ x y ⟨htpos, htlt⟩
    have hxP : x ∈ P.toSet := hF.1.1.subset hx.1
    have hyP : y ∈ P.toSet := hF.1.1.subset hy.1
    exact hxv ((mem_extremePoints.mp hvex).2 x hxP y hyP hvopen).1
  exact ⟨c, lt_of_le_of_ne hc_nonneg (Ne.symm hc0), hrel⟩

/-- La simmetria ciclica manda lo spigolo fra due faccette consecutive nello
spigolo successivo del fan. -/
theorem spigolo_trasportato (P : FiniteConvexPolytope A) {v : A} {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) :
    (⇑D.σ) '' (D.faccetta i ∩ D.faccetta (finRotate q i)) =
      D.faccetta (finRotate q i) ∩ D.faccetta (finRotate q (finRotate q i)) := by
  rw [Set.image_inter D.σ.injective, D.ruota i, D.ruota (finRotate q i)]

/-- Il trasporto ciclico di un punto non vertice dello spigolo resta sullo
spigolo successivo, resta distinto dal vertice e conserva la distanza da esso. -/
theorem punto_spigolo_trasportato (P : FiniteConvexPolytope A) {v : A} {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) {x : A} :
    x ∈ D.faccetta i ∩ D.faccetta (finRotate q i) → x ≠ v →
      D.σ x ∈ D.faccetta (finRotate q i) ∩
          D.faccetta (finRotate q (finRotate q i)) ∧
        D.σ x ≠ v ∧ ‖D.σ x - v‖ = ‖x - v‖ := by
  intro hx hxv
  have hmem : D.σ x ∈ (⇑D.σ) ''
      (D.faccetta i ∩ D.faccetta (finRotate q i)) := ⟨x, hx, rfl⟩
  rw [spigolo_trasportato P D i] at hmem
  refine ⟨hmem, ?_, ?_⟩
  · simpa [D.fissa_v] using D.σ.injective.ne hxv
  · calc
      ‖D.σ x - v‖ = dist (D.σ x) v := (dist_eq_norm _ _).symm
      _ = dist (D.σ x) (D.σ v) := by rw [D.fissa_v]
      _ = dist x v := D.σ.dist_map x v
      _ = ‖x - v‖ := dist_eq_norm _ _

/-- Una faccetta ammette un funzionale di supporto costante su di essa e
strettamente minore su ogni punto non vertice degli spigoli che non le
appartengono. L'esclusione è scritta come `j ≠ i` e `finRotate q j ≠ i`, cioè
nega precisamente i due modi in cui lo spigolo `j` può appartenere alla
faccetta `i`. -/
theorem funzionale_faccetta (P : FiniteConvexPolytope A) {v : A} {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) :
    ∃ l : A →L[ℝ] ℝ,
      (∀ x ∈ D.faccetta i, l x = l v) ∧
      (∀ j : Fin q, j ≠ i → finRotate q j ≠ i →
        ∀ x, x ∈ D.faccetta j ∩ D.faccetta (finRotate q j) → x ≠ v →
          l x < l v) := by
  obtain ⟨l, hil⟩ := (D.isFacet i).1.1 ⟨v, D.mem_v i⟩
  have hvmax := D.mem_v i
  rw [hil] at hvmax
  refine ⟨l, ?_, ?_⟩
  · intro x hxi
    have hxmax := hxi
    rw [hil] at hxmax
    exact le_antisymm (hvmax.2 x hxmax.1) (hxmax.2 v hvmax.1)
  · intro j hji hrji x hxedge hxv
    have hxnoti : x ∉ D.faccetta i := by
      intro hxi
      rcases D.spigolo_due j i x hxedge hxv hxi with h | h
      · exact hji h.symm
      · exact hrji h.symm
    have hxP : x ∈ P.toSet := (D.isFacet j).1.1.subset hxedge.1
    have hxnotmax : ¬∀ w ∈ P.toSet, l w ≤ l x := by
      intro hxmax
      apply hxnoti
      rw [hil]
      exact ⟨hxP, hxmax⟩
    push Not at hxnotmax
    obtain ⟨w, hwP, hxw⟩ := hxnotmax
    exact hxw.trans_le (hvmax.2 w hwP)

/-!
## Riepilogo dei raccordi consegnati

* `intersezione_spigolo_semiretta`: l'intersezione di due faccette distinte da
  un vertice estremo è radialmente una semiretta.
* `spigolo_trasportato`: la simmetria del fan manda ogni spigolo consecutivo
  nello spigolo consecutivo successivo.
* `punto_spigolo_trasportato`: il punto trasportato resta non vertice e conserva
  la sua distanza dal vertice fisso.
* `funzionale_faccetta`: il supporto esposto è costante sulla faccetta e
  strettamente più basso sugli spigoli che non le appartengono.
-/

/-!
A9 — IL FAN NELLO SPAZIO (campagna #50, assemblaggio).

Dal `CyclicVertexData` alle direzioni unitarie degli spigoli: scelta dei
punti, passo isometrico L uᵢ = uᵢ₊₁ (via A1+A2), e INIETTIVITÀ delle
direzioni. La scoperta che semplifica: l'iniettività non richiede
propagazione — se due spigoli condividono la semiretta, il punto più vicino
a v giace per convessità in una faccetta estranea all'altro spigolo, e
`spigolo_due` chiude direttamente, per ogni coppia, con q ≥ 3.
-/

section FanNelloSpazio

open FiniteConvexPolytope

/-- finRotate non ha punti fissi (q ≥ 2). -/
theorem finRotate_ne_self {q : ℕ} (hq : 2 ≤ q) (i : Fin q) :
    finRotate q i ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
  rw [finRotate_apply]
  intro h
  have hone : (1 : Fin (m + 2)) = 0 := by
    calc (1 : Fin (m + 2)) = i + 1 - i := by abel
      _ = i - i := by rw [h]
      _ = 0 := by abel
  have := congrArg Fin.val hone
  simp at this

/-- finRotate applicato due volte non torna (q ≥ 3). -/
theorem finRotate_due_ne {q : ℕ} (hq : 3 ≤ q) (i : Fin q) :
    finRotate q (finRotate q i) ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 3 := ⟨q - 3, by omega⟩
  rw [finRotate_apply, finRotate_apply]
  intro h
  have hdue : (2 : Fin (m + 3)) = 0 := by
    calc (2 : Fin (m + 3)) = i + 1 + 1 - i := by abel
      _ = i - i := by rw [h]
      _ = 0 := by abel
  have hval := congrArg Fin.val hdue
  have hmod : ((2 : Fin (m + 3)) : ℕ) = 2 := by
    have : (2 : ℕ) % (m + 3) = 2 := Nat.mod_eq_of_lt (by omega)
    simpa [Fin.coe_ofNat_eq_mod] using this
  rw [hmod, Fin.val_zero] at hval
  omega

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- Il punto di spigolo scelto tra la faccetta i e la successiva. -/
noncomputable def punto (P : FiniteConvexPolytope A) (v : A) {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) : A :=
  (D.spigolo i).choose

theorem punto_spec (P : FiniteConvexPolytope A) (v : A) {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) :
    punto P v D i ≠ v ∧
      punto P v D i ∈ D.faccetta i ∩ D.faccetta (finRotate q i) :=
  (D.spigolo i).choose_spec

/-- La direzione unitaria dello spigolo i. -/
noncomputable def dir (P : FiniteConvexPolytope A) (v : A) {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) : A :=
  ‖punto P v D i - v‖⁻¹ • (punto P v D i - v)

theorem dir_unitaria (P : FiniteConvexPolytope A) (v : A) {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) : ‖dir P v D i‖ = 1 := by
  have h := (punto_spec P v D i).1
  have hne : ‖punto P v D i - v‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  rw [dir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]

/-- Le faccette sono convesse. -/
theorem faccetta_convessa (P : FiniteConvexPolytope A) {v : A} {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) : Convex ℝ (D.faccetta i) :=
  (D.isFacet i).1.1.convex (convex_convexHull ℝ _)

/-- INIETTIVITÀ DELLE DIREZIONI: due spigoli distinti non condividono la
semiretta da v. Il punto più vicino cade nella faccetta sbagliata e
`spigolo_due` chiude. Non serve l'estremalità di v. -/
theorem dir_iniettiva (P : FiniteConvexPolytope A) (v : A) {q : ℕ}
    (hq : 3 ≤ q) (D : P.CyclicVertexData v q) :
    Function.Injective (dir P v D) := by
  intro i j hij
  by_contra hne
  have hi := punto_spec P v D i
  have hj := punto_spec P v D j
  have hnormi : (0 : ℝ) < ‖punto P v D i - v‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hi.1)
  have hnormj : (0 : ℝ) < ‖punto P v D j - v‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hj.1)
  -- dal comune versore: punto i − v = t • (punto j − v) con t > 0
  have hrad : punto P v D i - v
      = (‖punto P v D i - v‖ / ‖punto P v D j - v‖) • (punto P v D j - v) := by
    calc punto P v D i - v
        = ‖punto P v D i - v‖ • dir P v D i := by
          rw [dir, smul_smul, mul_inv_cancel₀ (ne_of_gt hnormi), one_smul]
      _ = ‖punto P v D i - v‖ • dir P v D j := by rw [hij]
      _ = (‖punto P v D i - v‖ / ‖punto P v D j - v‖)
            • (punto P v D j - v) := by
          rw [dir, smul_smul, div_eq_mul_inv]
  rcases le_total ‖punto P v D i - v‖ ‖punto P v D j - v‖ with hle | hle
  · -- punto i ∈ [v, punto j] ⊆ faccetta j ∩ faccetta (j+1)
    have hseg : punto P v D i ∈ segment ℝ v (punto P v D j) := by
      rw [segment_eq_image']
      refine ⟨‖punto P v D i - v‖ / ‖punto P v D j - v‖,
        ⟨div_nonneg hnormi.le hnormj.le, (div_le_one hnormj).mpr hle⟩, ?_⟩
      show v + (‖punto P v D i - v‖ / ‖punto P v D j - v‖)
          • (punto P v D j - v) = punto P v D i
      rw [← hrad]
      abel
    have hmem1 : punto P v D i ∈ D.faccetta j :=
      (faccetta_convessa P D j).segment_subset (D.mem_v j) hj.2.1 hseg
    have hmem2 : punto P v D i ∈ D.faccetta (finRotate q j) :=
      (faccetta_convessa P D (finRotate q j)).segment_subset
        (D.mem_v (finRotate q j)) hj.2.2 hseg
    by_cases h2 : j = finRotate q i
    · -- j = i+1: la faccetta buona è j+1 = i+2
      have hk1 : finRotate q j ≠ i := by
        rw [h2]; exact finRotate_due_ne hq i
      have hk2 : finRotate q j ≠ finRotate q i := by
        intro h
        exact finRotate_ne_self (by omega) i (h2 ▸ (finRotate q).injective h)
      rcases D.spigolo_due i (finRotate q j) (punto P v D i) hi.2 hi.1 hmem2
        with h | h
      · exact hk1 h
      · exact hk2 h
    · -- j ∉ {i, i+1}: la faccetta buona è j
      rcases D.spigolo_due i j (punto P v D i) hi.2 hi.1 hmem1 with h | h
      · exact hne h.symm
      · exact h2 h
  · -- simmetrico: punto j ∈ [v, punto i]
    have hrad' : punto P v D j - v
        = (‖punto P v D j - v‖ / ‖punto P v D i - v‖) • (punto P v D i - v) := by
      symm
      calc (‖punto P v D j - v‖ / ‖punto P v D i - v‖) • (punto P v D i - v)
          = (‖punto P v D j - v‖ / ‖punto P v D i - v‖)
              • ((‖punto P v D i - v‖ / ‖punto P v D j - v‖)
              • (punto P v D j - v)) := by rw [← hrad]
        _ = ((‖punto P v D j - v‖ / ‖punto P v D i - v‖)
              * (‖punto P v D i - v‖ / ‖punto P v D j - v‖))
              • (punto P v D j - v) := by rw [smul_smul]
        _ = (1 : ℝ) • (punto P v D j - v) := by
            congr 1
            rw [div_mul_div_comm,
              mul_comm ‖punto P v D i - v‖ ‖punto P v D j - v‖]
            exact div_self (ne_of_gt (mul_pos hnormj hnormi))
        _ = punto P v D j - v := one_smul ℝ _
    have hseg : punto P v D j ∈ segment ℝ v (punto P v D i) := by
      rw [segment_eq_image']
      refine ⟨‖punto P v D j - v‖ / ‖punto P v D i - v‖,
        ⟨div_nonneg hnormj.le hnormi.le, (div_le_one hnormi).mpr hle⟩, ?_⟩
      show v + (‖punto P v D j - v‖ / ‖punto P v D i - v‖)
          • (punto P v D i - v) = punto P v D j
      rw [← hrad']
      abel
    have hmem1 : punto P v D j ∈ D.faccetta i :=
      (faccetta_convessa P D i).segment_subset (D.mem_v i) hi.2.1 hseg
    have hmem2 : punto P v D j ∈ D.faccetta (finRotate q i) :=
      (faccetta_convessa P D (finRotate q i)).segment_subset
        (D.mem_v (finRotate q i)) hi.2.2 hseg
    by_cases h2 : i = finRotate q j
    · have hk1 : finRotate q i ≠ j := by
        rw [h2]; exact finRotate_due_ne hq j
      have hk2 : finRotate q i ≠ finRotate q j := by
        intro h
        exact finRotate_ne_self (by omega) j (h2 ▸ (finRotate q).injective h)
      rcases D.spigolo_due j (finRotate q i) (punto P v D j) hj.2 hj.1 hmem2
        with h | h
      · exact hk1 h
      · exact hk2 h
    · rcases D.spigolo_due j i (punto P v D j) hj.2 hj.1 hmem1 with h | h
      · exact hne h
      · exact h2 h

/-- IL PASSO DEL FAN NELLO SPAZIO: la parte lineare di σ manda la direzione
dello spigolo i in quella dello spigolo i+1 (via A1 + A2). -/
theorem dir_passo (P : FiniteConvexPolytope A) (v : A) {q : ℕ}
    (hq : 3 ≤ q) (D : P.CyclicVertexData v q)
    (hvex : v ∈ P.toSet.extremePoints ℝ) (i : Fin q) :
    D.σ.linearIsometryEquiv (dir P v D i) = dir P v D (finRotate q i) := by
  have hi := punto_spec P v D i
  have htr := punto_spigolo_trasportato P D i hi.2 hi.1
  have hnext := punto_spec P v D (finRotate q i)
  have hFG : D.faccetta (finRotate q i)
      ≠ D.faccetta (finRotate q (finRotate q i)) := by
    intro h
    exact finRotate_ne_self (by omega) (finRotate q i) (D.distinte h).symm
  obtain ⟨c, hc0, hc⟩ := intersezione_spigolo_semiretta P
    (D.isFacet (finRotate q i)) (D.isFacet (finRotate q (finRotate q i)))
    hFG (D.mem_v _) (D.mem_v _) hvex htr.1 hnext.2 htr.2.1 hnext.1
  -- hc : punto (i+1) − v = c • (σ (punto i) − v)
  have hlin : D.σ.linearIsometryEquiv (punto P v D i - v)
      = D.σ (punto P v D i) - v := by
    have h := D.σ.map_vsub (punto P v D i) v
    rw [D.fissa_v] at h
    simpa using h
  have hnorm : ‖punto P v D (finRotate q i) - v‖ = c * ‖punto P v D i - v‖ := by
    rw [hc, norm_smul, Real.norm_eq_abs, abs_of_pos hc0, htr.2.2]
  have hnormi : ‖punto P v D i - v‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hi.1)
  rw [dir, dir, map_smul, hlin, hnorm, hc, smul_smul]
  congr 1
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hni : ‖punto P v D i - v‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hi.1)
  rw [mul_inv]
  field_simp

end FanNelloSpazio

end
end BundlePart6

section BundlePart7
/- Source: Cubical/Polytope/FanVertice.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.FanVertice.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/





/-!
# KG-3A2: il fan al vertice dalla flag-transitivita

Versione condizionale ammessa dal fascicolo 14.  La simmetria `σ` non e'
postulata: viene estratta da `IsRegular` applicata alle bandiere `F` e `G`.
Le faccette vengono poi *definite* come l'orbita della faccetta di `F`.

Restano espliciti due input del cantiere delle facce:

* `FanOrbitCertificate`: l'orbita scelta chiude esattamente dopo `q` passi,
  e' semplice, e comprende tutte le faccette per `v`;
* `EdgeInAtMostTwoFacets`: il lemma geometrico locale che un punto interno a
  uno spigolo di due faccette non appartiene a una terza faccetta.

Le bandiere `L` e `R` certificano che le prime due faccette dell'orbita
condividono davvero uno spigolo per `v`.  L'esistenza di queste bandiere e dei
certificati e' precisamente il cantiere Q1; Q0 e' importato dal modulo
kernel-certificato `PerturbazioneFinita`.
-/

open Set
open scoped Topology RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification
namespace ConvexPolytope

/-- Il contratto benchmark visto come il politopo astratto usato dal predicato
locale.  I campi coincidono definizionalmente. -/
def asFinite {n : ℕ} (P : ConvexPolytope n) : FiniteConvexPolytope (E n) where
  vertices := P.vertices
  nonempty := P.vertices_nonempty
  vertices_eq_extremePoints := P.vertices_eq_extremePoints

@[simp] theorem asFinite_toSet {n : ℕ} (P : ConvexPolytope n) :
    P.asFinite.toSet = P.toSet := rfl

@[simp] theorem asFinite_isFacet_iff (P : ConvexPolytope 3) (A : Set (E 3)) :
    P.asFinite.IsFacet A ↔ P.IsFace A ∧ faceDim A = 2 := Iff.rfl

/-- La `k`-esima immagine di una faccetta di bandiera. -/
def iteratedFacet {P : ConvexPolytope 3} (σ : Isom 3) (F : P.Flag) (k : ℕ) :
    Set (E 3) :=
  ((σ : E 3 → E 3)^[k]) '' F.face 2

/-- L'orbita finita, indicizzata da `Fin q`, della faccetta di `F`. -/
def facetOrbit {P : ConvexPolytope 3} {q : ℕ} (σ : Isom 3) (F : P.Flag)
    (i : Fin q) : Set (E 3) :=
  iteratedFacet σ F i.val

@[simp] theorem iteratedFacet_zero {P : ConvexPolytope 3} (σ : Isom 3)
    (F : P.Flag) : iteratedFacet σ F 0 = F.face 2 := by
  simp [iteratedFacet]

theorem image_iteratedFacet {P : ConvexPolytope 3} (σ : Isom 3) (F : P.Flag)
    (k : ℕ) :
    (σ : E 3 → E 3) '' iteratedFacet σ F k = iteratedFacet σ F (k + 1) := by
  rw [iteratedFacet, iteratedFacet, Set.image_image]
  congr 1
  funext x
  exact (Function.iterate_succ_apply' (σ : E 3 → E 3) k x).symm

/-- Dati finiti/combinatori dell'orbita.  La legge di rotazione non e' un
campo: verra' dedotta dagli iterati e da `period`. -/
structure FanOrbitCertificate (P : ConvexPolytope 3) (v : E 3) (q : ℕ)
    (F : P.Flag) (σ : Isom 3) : Prop where
  period : iteratedFacet σ F q = F.face 2
  isFacet : ∀ i : Fin q,
    P.IsFace (facetOrbit σ F i) ∧ faceDim (facetOrbit σ F i) = 2
  injective : Function.Injective (fun i : Fin q => facetOrbit σ F i)
  complete : ∀ A : Set (E 3), P.IsFace A → faceDim A = 2 → v ∈ A →
    ∃ i : Fin q, A = facetOrbit σ F i

/-- Forma generale del solo lemma di intersezione ammesso dal fascicolo:
una terza faccetta per `v` che contiene un punto non terminale dello spigolo
comune di `A` e `B` coincide con `A` oppure con `B`. -/
def EdgeInAtMostTwoFacets (P : ConvexPolytope 3) (v : E 3) : Prop :=
  ∀ ⦃A B C : Set (E 3)⦄,
    P.IsFace A → faceDim A = 2 →
    P.IsFace B → faceDim B = 2 →
    P.IsFace C → faceDim C = 2 →
    A ≠ B → v ∈ A → v ∈ B → v ∈ C →
    ∀ ⦃x : E 3⦄, x ∈ A ∩ B → x ≠ v → x ∈ C → C = A ∨ C = B

theorem finRotate_ne_self {q : ℕ} (hq : 2 ≤ q) (i : Fin q) :
    finRotate q i ≠ i := by
  cases q with
  | zero => omega
  | succ n =>
      by_cases hi : i = Fin.last n
      · subst i
        intro h
        have hv := congrArg Fin.val h
        simp only [finRotate_last, Fin.val_zero, Fin.val_last] at hv
        omega
      · intro h
        have hv := congrArg Fin.val h
        rw [coe_finRotate_of_ne_last hi] at hv
        omega

/-- Un'orbita chiusa al passo `q` e' ruotata da `σ` secondo `finRotate`. -/
theorem facetOrbit_ruota {P : ConvexPolytope 3} {q : ℕ} (hq : 1 ≤ q)
    (σ : Isom 3) (F : P.Flag) (hperiod : iteratedFacet σ F q = F.face 2)
    (i : Fin q) :
    (σ : E 3 → E 3) '' facetOrbit σ F i =
      facetOrbit σ F (finRotate q i) := by
  cases q with
  | zero => omega
  | succ n =>
      by_cases hi : i = Fin.last n
      · subst i
        rw [facetOrbit, facetOrbit, finRotate_last, Fin.val_last, Fin.val_zero]
        rw [image_iteratedFacet]
        simpa using hperiod
      · rw [facetOrbit, facetOrbit, image_iteratedFacet]
        congr 1
        exact (coe_finRotate_of_ne_last hi).symm

/-!
`horbit` e' deliberatamente quantificato su ogni trasportatore di bandiere:
`IsRegular` sceglie esistenzialmente `σ`, e il certificato Q1 deve potersi
applicare alla scelta prodotta dal kernel senza un operatore di scelta esterno.
-/

/-- **KG-3A2, versione condizionale.** Dalla flag-transitivita', da due
bandiere che selezionano il passo del fan, dalle bandiere dello spigolo base e
dai due lemmi locali Q1, si ottengono esattamente i dati del predicato
`CyclicVertexData`, incluso `spigolo_due`. -/
theorem fan_vertice_condizionale (P : ConvexPolytope 3) (h : P.IsRegular)
    {v : E 3} {q : ℕ} (hq : 3 ≤ q)
    (F G L R : P.Flag)
    (hF0 : F.face 0 = {v}) (hG0 : G.face 0 = {v})
    (hL0 : L.face 0 = {v})
    (hLF : L.face 2 = F.face 2) (hRG : R.face 2 = G.face 2)
    (hLR : L.face 1 = R.face 1)
    (horbit : ∀ σ : Isom 3, P.isSymmetry σ →
      (∀ k : Fin 3, (σ : E 3 → E 3) '' F.face k = G.face k) →
      FanOrbitCertificate P v q F σ)
    (hedge_two : EdgeInAtMostTwoFacets P v) :
    Nonempty (P.asFinite.CyclicVertexData v q) := by
  obtain ⟨σ, hσP, hσflag⟩ := h.2 F G
  have C : FanOrbitCertificate P v q F σ := horbit σ hσP hσflag

  have hσv : σ v = v := by
    have hv : σ v ∈ (σ : E 3 → E 3) '' F.face 0 := by
      exact ⟨v, by simp [hF0], rfl⟩
    rw [hσflag 0, hG0] at hv
    simpa using hv

  have hvF : v ∈ F.face 2 := by
    apply (F.strict_mono 0 2 (by decide)).1
    simp [hF0]

  have hmem : ∀ i : Fin q, v ∈ facetOrbit σ F i := by
    intro i
    refine ⟨v, hvF, ?_⟩
    exact (show Function.IsFixedPt (σ : E 3 → E 3) v from hσv).iterate i.val

  have hruota : ∀ i : Fin q,
      (σ : E 3 → E 3) '' facetOrbit σ F i =
        facetOrbit σ F (finRotate q i) :=
    facetOrbit_ruota (by omega) σ F C.period

  have hbase : ∃ x : E 3,
      x ≠ v ∧ x ∈ F.face 2 ∩ G.face 2 := by
    have hss : L.face 0 ⊂ L.face 1 := L.strict_mono 0 1 (by decide)
    obtain ⟨x, hxL1, hxL0⟩ := Set.exists_of_ssubset hss
    have hxne : x ≠ v := by
      intro hxv
      apply hxL0
      simp [hL0, hxv]
    have hxF : x ∈ F.face 2 := by
      rw [← hLF]
      exact (L.strict_mono 1 2 (by decide)).1 hxL1
    have hxR1 : x ∈ R.face 1 := by
      rw [← hLR]
      exact hxL1
    have hxG : x ∈ G.face 2 := by
      rw [← hRG]
      exact (R.strict_mono 1 2 (by decide)).1 hxR1
    exact ⟨x, hxne, hxF, hxG⟩
  obtain ⟨x₀, hx₀v, hx₀F, hx₀G⟩ := hbase

  refine ⟨{
    faccetta := facetOrbit σ F
    isFacet := ?_
    mem_v := hmem
    distinte := C.injective
    complete := ?_
    σ := σ
    fissa_v := hσv
    preserva := ?_
    ruota := hruota
    spigolo := ?_
    spigolo_due := ?_
  }⟩
  · intro i
    exact (asFinite_isFacet_iff P _).2 (C.isFacet i)
  · intro A hA hvA
    exact C.complete A hA.1 hA.2 hvA
  · simpa [ConvexPolytope.isSymmetry] using hσP
  · intro i
    let xᵢ : E 3 := ((σ : E 3 → E 3)^[i.val]) x₀
    have hxᵢ_this : xᵢ ∈ facetOrbit σ F i := by
      exact ⟨x₀, hx₀F, rfl⟩
    have hx₀image : x₀ ∈ (σ : E 3 → E 3) '' F.face 2 := by
      rw [hσflag 2]
      exact hx₀G
    obtain ⟨y, hyF, hσy⟩ := hx₀image
    have hxᵢ_image : xᵢ ∈ (σ : E 3 → E 3) '' facetOrbit σ F i := by
      refine ⟨((σ : E 3 → E 3)^[i.val]) y, ⟨y, hyF, rfl⟩, ?_⟩
      dsimp [xᵢ]
      rw [← hσy]
      exact (Function.iterate_succ_apply' (σ : E 3 → E 3) i.val y).symm.trans
        (Function.iterate_succ_apply (σ : E 3 → E 3) i.val y)
    have hxᵢ_next : xᵢ ∈ facetOrbit σ F (finRotate q i) := by
      rw [← hruota i]
      exact hxᵢ_image
    have hxᵢv : xᵢ ≠ v := by
      intro heq
      apply hx₀v
      apply (σ.injective.iterate i.val)
      rw [(show Function.IsFixedPt (σ : E 3 → E 3) v from hσv).iterate i.val]
      exact heq
    exact ⟨xᵢ, hxᵢv, hxᵢ_this, hxᵢ_next⟩
  · intro i j x hxedge hxv hxj
    have hne : facetOrbit σ F i ≠ facetOrbit σ F (finRotate q i) := by
      intro heq
      have := C.injective heq
      exact (finRotate_ne_self (by omega) i) this.symm
    rcases hedge_two (C.isFacet i).1 (C.isFacet i).2
        (C.isFacet (finRotate q i)).1 (C.isFacet (finRotate q i)).2
        (C.isFacet j).1 (C.isFacet j).2 hne (hmem i)
        (hmem (finRotate q i)) (hmem j) hxedge hxv hxj with hj | hj
    · exact Or.inl (C.injective hj)
    · exact Or.inr (C.injective hj)

end ConvexPolytope
end LeanEval.Geometry.PlatonicClassification

/-!
CONSEGNA

File: `FanVertice.lean`
Teorema:
`LeanEval.Geometry.PlatonicClassification.ConvexPolytope.fan_vertice_condizionale`

Forma: KG-3A2 condizionale.  Ipotesi residue dichiarate:

1. quattro bandiere `F,G,L,R`; `F -> G` seleziona il passo della simmetria,
   mentre `L,R` attraversano lo spigolo comune delle prime due faccette;
2. `FanOrbitCertificate`: periodo esatto indicizzato, faccette dell'orbita,
   iniettivita' e completezza al vertice;
3. `EdgeInAtMostTwoFacets`: il lemma generale d'intersezione di tre faccette
   esplicitamente autorizzato dal fascicolo.

Non sono assunte ne' una simmetria `σ`, ne' la legge `ruota`, ne' i testimoni
`spigolo`, ne' `spigolo_due` nella forma indicizzata del risultato.  `σ` viene
da `IsRegular`; `ruota` dagli iterati e dal periodo; `spigolo` dalle bandiere;
`spigolo_due` dal lemma generale e dall'iniettivita' dell'orbita.

-/

end
end
end BundlePart7

section BundlePart8
/- Source: Cubical/Polytope/ScaricoSpigolo.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ScaricoSpigolo.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/





/-!
FASE 3A — SCARICO DI `EdgeInAtMostTwoFacets` (18 lug 2026).

Il predicato locale assunto dal gemello KG-3A2 vale INCONDIZIONATAMENTE:
è esattamente la forma quantificata del diamante.
-/

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **Il lemma locale del fan è un teorema**: in ogni politopo di ℝ³, per
ogni punto `v`, uno spigolo sta in al più due faccette. -/
theorem edgeInAtMostTwoFacets_vale (P : ConvexPolytope 3) (v : E 3) :
    ConvexPolytope.EdgeInAtMostTwoFacets P v := by
  intro A B C hA hdA hB hdB hC hdC hAB hvA hvB hvC x hx hxv hxC
  exact spigolo_in_due_faccette P v hA hdA hB hdB hC hdC hAB hvA hvB hvC
    hx hxv hxC

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart8

section BundlePart9
/- Source: Cubical/Polytope/ConnessioneVentaglio.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ConnessioneVentaglio.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




















open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Due faccette per v condividono uno spigolo per v. -/
def SpigoloComune (P : ConvexPolytope 3) (v : E 3) (A B : Set (E 3)) : Prop :=
  ∃ δ : Set (E 3), P.IsFace δ ∧ faceDim δ = 1 ∧ v ∈ δ ∧ δ ⊆ A ∧ δ ⊆ B

/-- Gli spigoli del politopo che passano per `v`, come tipo finito. -/
def SpigoloPer (P : ConvexPolytope 3) (v : E 3) :=
  {e : Set (E 3) // P.IsFace e ∧ faceDim e = 1 ∧ v ∈ e}

namespace SpigoloPer

variable (P : ConvexPolytope 3) (v : E 3)

instance : DecidableEq (SpigoloPer P v) := Classical.decEq _

/-- Il secondo estremo, scelto una volta per tutte. -/
noncomputable def altro (hv : v ∈ P.vertices) (e : SpigoloPer P v) : E 3 :=
  Classical.choose (spigolo_segmento P e.property.1 e.property.2.1 hv e.property.2.2)

theorem altro_spec (hv : v ∈ P.vertices) (e : SpigoloPer P v) :
    altro P v hv e ∈ P.vertices ∧ altro P v hv e ∈ e.val ∧
      altro P v hv e ≠ v ∧
      e.val = segment ℝ v (altro P v hv e) :=
  Classical.choose_spec
    (spigolo_segmento P e.property.1 e.property.2.1 hv e.property.2.2)

/-- Punto in cui lo spigolo taglia il livello `l = c`. -/
noncomputable def taglio (hv : v ∈ P.vertices) (l : E 3 →L[ℝ] ℝ) (c : ℝ)
    (e : SpigoloPer P v) : E 3 :=
  v + ((l v - c) / (l v - l (altro P v hv e))) • (altro P v hv e - v)

theorem taglio_fatti (hv : v ∈ P.vertices) (l : E 3 →L[ℝ] ℝ) (c : ℝ)
    (hc : c < l v) (e : SpigoloPer P v)
    (ha : l (altro P v hv e) < c) :
    taglio P v hv l c e ∈ e.val ∧
      l (taglio P v hv l c e) = c ∧
      e.val ∩ {y | l y = c} = {taglio P v hv l c e} := by
  classical
  let a : E 3 := altro P v hv e
  let θ : ℝ := (l v - c) / (l v - l a)
  have hden : 0 < l v - l a := by linarith
  have hnum : 0 < l v - c := by linarith
  have hθ0 : 0 < θ := by
    exact div_pos hnum hden
  have hθ1 : θ < 1 := by
    rw [div_lt_one hden]
    linarith
  have hseg : e.val = segment ℝ v a := (altro_spec P v hv e).2.2.2
  have hxform : taglio P v hv l c e = v + θ • (a - v) := rfl
  have hxseg : taglio P v hv l c e ∈ e.val := by
    rw [hseg, hxform]
    refine ⟨1 - θ, θ, by linarith, le_of_lt hθ0, by ring, ?_⟩
    match_scalars <;> ring
  have hxlevel : l (taglio P v hv l c e) = c := by
    rw [hxform]
    simp only [map_add, map_smul, map_sub, smul_eq_mul]
    have hdenne : l v - l a ≠ 0 := ne_of_gt hden
    have hcancel : (l v - c) / (l v - l a) * (l v - l a) = l v - c :=
      div_mul_cancel₀ _ hdenne
    nlinarith
  refine ⟨hxseg, hxlevel, Set.Subset.antisymm ?_ ?_⟩
  · intro y hy
    have hye : y ∈ segment ℝ v a := by simpa [hseg] using hy.1
    rcases hye with ⟨r, s, hr, hs, hrs, hyform⟩
    have hylevel : l y = c := hy.2
    have hsθ : s = θ := by
      rw [← hyform] at hylevel
      simp only [map_add, map_smul, smul_eq_mul] at hylevel
      have hrform : r = 1 - s := by linarith
      rw [hrform] at hylevel
      have heq : s * (l v - l a) = l v - c := by linarith
      apply (eq_div_iff (ne_of_gt hden)).2
      linarith
    have hry : r = 1 - θ := by linarith
    rw [Set.mem_singleton_iff]
    rw [hxform, ← hyform, hsθ, hry]
    match_scalars <;> ring
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ⟨hxseg, hxlevel⟩

end SpigoloPer

/-- Un livello che separa `v` da tutti gli altri vertici. -/
theorem esiste_livello_separatore (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) :
    ∃ l : E 3 →L[ℝ] ℝ, ∃ c : ℝ,
      c < l v ∧ ∀ u ∈ P.vertices, u ≠ v → l u < c := by
  classical
  have hvface : P.IsFace ({v} : Set (E 3)) := vertex_isFace P hv
  obtain ⟨l, hlmem, hlchar⟩ := espositore_di_faccia P hvface
  have hvT : v ∈ P.toSet := (hlmem v (Set.mem_singleton v)).1
  have hlmax : ∀ y ∈ P.toSet, l y ≤ l v :=
    (hlmem v (Set.mem_singleton v)).2
  have hlstrict : ∀ u ∈ P.vertices, u ≠ v → l u < l v := by
    intro u huV huv
    have huT : u ∈ P.toSet := subset_convexHull ℝ _ huV
    rcases lt_or_eq_of_le (hlmax u huT) with h | h
    · exact h
    · have huSing : u ∈ ({v} : Set (E 3)) :=
        hlchar u huT (fun z hz => le_trans (hlmax z hz) (le_of_eq h.symm))
      exact (huv (Set.mem_singleton_iff.mp huSing)).elim
  have hsing_ne : ({v} : Set (E 3)) ≠ P.toSet := by
    intro heq
    have hPdim : faceDim P.toSet = 3 := hfull
    rw [← heq, faceDim_singleton] at hPdim
    omega
  obtain ⟨w, hwV, hwne⟩ := exists_vertex_notMem_of_ne_toSet P hvface hsing_ne
  have hwv : w ≠ v := by
    intro h
    subst w
    exact hwne (Set.mem_singleton v)
  let S : Finset (E 3) := P.vertices.erase v
  have hSne : S.Nonempty := ⟨w, Finset.mem_erase.mpr ⟨hwv, hwV⟩⟩
  obtain ⟨m, hmS, hmmax⟩ := S.exists_max_image l hSne
  let c : ℝ := (l v + l m) / 2
  have hmlt : l m < l v := by
    exact hlstrict m (Finset.mem_of_mem_erase hmS) (Finset.ne_of_mem_erase hmS)
  refine ⟨l, c, by dsimp [c]; linarith, ?_⟩
  intro u huV huv
  have huS : u ∈ S := Finset.mem_erase.mpr ⟨huv, huV⟩
  have hule : l u ≤ l m := hmmax u huS
  dsimp [c]
  linarith

/-- In una faccetta, dato uno dei due spigoli per `v`, esiste un unico
altro spigolo per `v`. -/
theorem unico_altro_spigolo_nella_faccetta (P : ConvexPolytope 3)
    {v : E 3} (hv : v ∈ P.vertices)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) (hvA : v ∈ A)
    (e : SpigoloPer P v) (heA : e.val ⊆ A) :
    ∃ e' : SpigoloPer P v, e'.val ⊆ A ∧ e' ≠ e ∧
      ∀ d : SpigoloPer P v, d.val ⊆ A → d ≠ e → d = e' := by
  classical
  let Q : ConvexPolytope 3 := facePolytope P hA
  have hQT : Q.toSet = A := facePolytope_toSet P hA
  have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2 := by
    rw [hQT]
    exact hdA
  have hvQ : v ∈ Q.vertices := by
    exact Finset.mem_filter.mpr ⟨hv, hvA⟩
  have heQ : Q.IsFace e.val := facePolytope_isFace_of P hA e.property.1 heA
  obtain ⟨g, hgQ, hdg, hvg, hgne⟩ :=
    secondo_spigolo Q hQdim hvQ heQ e.property.2.1 e.property.2.2
  have hgP : P.IsFace g := isFace_of_facePolytope P hA hgQ
  have hgA : g ⊆ A := by
    have := face_subset_toSet Q hgQ
    rwa [hQT] at this
  let e' : SpigoloPer P v := ⟨g, hgP, hdg, hvg⟩
  have he'ne : e' ≠ e := by
    intro h
    apply hgne
    exact congrArg Subtype.val h
  refine ⟨e', hgA, he'ne, ?_⟩
  intro d hdA hde
  have hdQ : Q.IsFace d.val := facePolytope_isFace_of P hA d.property.1 hdA
  by_contra hde'
  have he_g : e.val ≠ g := fun h => hgne h.symm
  have he_d : e.val ≠ d.val := fun h => hde (Subtype.ext h.symm)
  have hg_d : g ≠ d.val := fun h => hde' (Subtype.ext h.symm)
  exact diamante_poligono Q hQdim heQ e.property.2.1 hgQ hdg hdQ d.property.2.1
    he_g he_d hg_d e.property.2.2 hvg d.property.2.2

/-- La sezione di una faccetta al livello separatore è il segmento fra gli
attraversamenti dei suoi due spigoli per `v`. -/
theorem sezione_faccetta_segmento (P : ConvexPolytope 3)
    {v : E 3} (hv : v ∈ P.vertices)
    (l : E 3 →L[ℝ] ℝ) (c : ℝ) (hc : c < l v)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) (hvA : v ∈ A)
    (e₁ e₂ : SpigoloPer P v) (he₁A : e₁.val ⊆ A) (he₂A : e₂.val ⊆ A)
    (hne : e₁ ≠ e₂)
    (ha₁ : l (SpigoloPer.altro P v hv e₁) < c)
    (ha₂ : l (SpigoloPer.altro P v hv e₂) < c) :
    A ∩ {y | l y = c} =
      segment ℝ (SpigoloPer.taglio P v hv l c e₁)
        (SpigoloPer.taglio P v hv l c e₂) := by
  classical
  let Q : ConvexPolytope 3 := facePolytope P hA
  have hQT : Q.toSet = A := facePolytope_toSet P hA
  have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2 := by
    rw [hQT]
    exact hdA
  have hvQ : v ∈ Q.vertices := Finset.mem_filter.mpr ⟨hv, hvA⟩
  have he₁Q : Q.IsFace e₁.val := facePolytope_isFace_of P hA e₁.property.1 he₁A
  have he₂Q : Q.IsFace e₂.val := facePolytope_isFace_of P hA e₂.property.1 he₂A
  let a : E 3 := SpigoloPer.altro P v hv e₁
  let b : E 3 := SpigoloPer.altro P v hv e₂
  let x₁ : E 3 := SpigoloPer.taglio P v hv l c e₁
  let x₂ : E 3 := SpigoloPer.taglio P v hv l c e₂
  have ha₁e : a ∈ e₁.val := (SpigoloPer.altro_spec P v hv e₁).2.1
  have ha₁v : a ≠ v := (SpigoloPer.altro_spec P v hv e₁).2.2.1
  have hseg₁ : e₁.val = segment ℝ v a :=
    (SpigoloPer.altro_spec P v hv e₁).2.2.2
  have ha₂e : b ∈ e₂.val := (SpigoloPer.altro_spec P v hv e₂).2.1
  have ha₂v : b ≠ v := (SpigoloPer.altro_spec P v hv e₂).2.2.1
  have hseg₂ : e₂.val = segment ℝ v b :=
    (SpigoloPer.altro_spec P v hv e₂).2.2.2
  have hval₁ : l x₁ = c :=
    (SpigoloPer.taglio_fatti P v hv l c hc e₁ ha₁).2.1
  have hval₂ : l x₂ = c :=
    (SpigoloPer.taglio_fatti P v hv l c hc e₂ ha₂).2.1
  have hx₁A : x₁ ∈ A := he₁A
    (SpigoloPer.taglio_fatti P v hv l c hc e₁ ha₁).1
  have hx₂A : x₂ ∈ A := he₂A
    (SpigoloPer.taglio_fatti P v hv l c hc e₂ ha₂).1
  have hneval : e₁.val ≠ e₂.val := fun h => hne (Subtype.ext h)
  apply Set.Subset.antisymm
  · intro y hy
    have hyQ : y ∈ Q.toSet := by
      rw [hQT]
      exact hy.1
    obtain ⟨s, t, hs, ht, hyform⟩ :=
      cono_al_vertice Q hQdim hvQ he₁Q e₁.property.2.1
        he₂Q e₂.property.2.1 hneval ha₁e ha₁v hseg₁
        ha₂e ha₂v hseg₂ e₁.property.2.2 e₂.property.2.2 y hyQ
    have hyval : l y = l v + s * (l a - l v) + t * (l b - l v) := by
      rw [hyform]
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
    have hbalance : s * (l v - l a) + t * (l v - l b) = l v - c := by
      have := hy.2
      change l y = c at this
      linarith
    have hD : 0 < l v - c := by linarith
    have hd₁ : 0 < l v - l a := by
      change l a < c at ha₁
      linarith
    have hd₂ : 0 < l v - l b := by
      change l b < c at ha₂
      linarith
    let lam : ℝ := s * (l v - l a) / (l v - c)
    let mu : ℝ := t * (l v - l b) / (l v - c)
    have hlam : 0 ≤ lam := div_nonneg (mul_nonneg hs (le_of_lt hd₁)) (le_of_lt hD)
    have hmu : 0 ≤ mu := div_nonneg (mul_nonneg ht (le_of_lt hd₂)) (le_of_lt hD)
    have hsum : lam + mu = 1 := by
      rw [← add_div]
      rw [hbalance, div_self (ne_of_gt hD)]
    refine ⟨lam, mu, hlam, hmu, hsum, ?_⟩
    change lam • x₁ + mu • x₂ = y
    have hx₁form : x₁ = v + ((l v - c) / (l v - l a)) • (a - v) := rfl
    have hx₂form : x₂ = v + ((l v - c) / (l v - l b)) • (b - v) := rfl
    rw [hx₁form, hx₂form, hyform]
    dsimp [lam, mu]
    match_scalars
    all_goals
      field_simp
      try ring_nf at hbalance ⊢
      try nlinarith [hbalance]
  · intro y hy
    have hyA : y ∈ A :=
      (hA.1.convex (convex_convexHull ℝ _)).segment_subset hx₁A hx₂A hy
    have hylevel : l y = c := by
      rcases hy with ⟨r, s, hr, hs, hrs, hyform⟩
      rw [← hyform]
      simp only [map_add, map_smul, smul_eq_mul]
      rw [hval₁, hval₂]
      rw [← add_mul, hrs, one_mul]
    exact ⟨hyA, hylevel⟩

/-- Due spigoli per lo stesso vertice che hanno un secondo punto comune
coincidono. -/
theorem spigoli_eq_of_punto_comune (P : ConvexPolytope 3) {v x : E 3}
    {e d : Set (E 3)}
    (he : P.IsFace e) (hde : faceDim e = 1) (hve : v ∈ e)
    (hd : P.IsFace d) (hdd : faceDim d = 1) (hvd : v ∈ d)
    (hxe : x ∈ e) (hxd : x ∈ d) (hxv : x ≠ v) : e = d := by
  have hint : P.IsFace (e ∩ d) := ⟨he.1.inter hd.1, ⟨v, hve, hvd⟩⟩
  have hge : 1 ≤ Module.finrank ℝ (vectorSpan ℝ (e ∩ d)) :=
    finrank_pos_di_due ⟨hve, hvd⟩ ⟨hxe, hxd⟩ hxv
  have heqint : e ∩ d = e := by
    apply Set.Subset.antisymm Set.inter_subset_left
    by_contra hnot
    have hss : e ∩ d ⊂ e := ⟨Set.inter_subset_left, hnot⟩
    have hlt := faceDim_lt_of_ssubset P hint he hss
    have hlt' : Module.finrank ℝ (vectorSpan ℝ (e ∩ d)) < 1 := by
      have hlt0 : Module.finrank ℝ (vectorSpan ℝ (e ∩ d)) <
          Module.finrank ℝ (vectorSpan ℝ e) := hlt
      have hedim : Module.finrank ℝ (vectorSpan ℝ e) = 1 := hde
      omega
    omega
  have hed : e ⊆ d := by
    intro y hy
    have : y ∈ e ∩ d := by rwa [heqint]
    exact this.2
  apply Set.Subset.antisymm hed
  by_contra hnot
  have hss : e ⊂ d := ⟨hed, hnot⟩
  have hlt := faceDim_lt_of_ssubset P he hd hss
  have hlt' : Module.finrank ℝ (vectorSpan ℝ e) <
      Module.finrank ℝ (vectorSpan ℝ d) := hlt
  have hde' : Module.finrank ℝ (vectorSpan ℝ e) = 1 := hde
  have hdd' : Module.finrank ℝ (vectorSpan ℝ d) = 1 := hdd
  omega

/-- Due faccette distinte che contengono lo stesso spigolo si intersecano
esattamente in quello spigolo. -/
theorem intersezione_faccette_eq_spigolo (P : ConvexPolytope 3)
    {e A B : Set (E 3)}
    (he : P.IsFace e) (hde : faceDim e = 1)
    (hA : P.IsFace A) (hdA : faceDim A = 2)
    (hB : P.IsFace B) (hdB : faceDim B = 2)
    (heA : e ⊆ A) (heB : e ⊆ B) (hAB : A ≠ B) : A ∩ B = e := by
  obtain ⟨v, hve⟩ := he.2
  have hint : P.IsFace (A ∩ B) := ⟨hA.1.inter hB.1, ⟨v, heA hve, heB hve⟩⟩
  have hintA : A ∩ B ⊂ A := by
    refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
    have hAleB : A ⊆ B := fun x hx => (hsup hx).2
    have hss : A ⊂ B := ⟨hAleB, fun hBA => hAB (Set.Subset.antisymm hAleB hBA)⟩
    have hlt := faceDim_lt_of_ssubset P hA hB hss
    omega
  have hdintlt := faceDim_lt_of_ssubset P hint hA hintA
  have heint : e ⊆ A ∩ B := fun x hx => ⟨heA hx, heB hx⟩
  have hge : 1 ≤ Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) := by
    have hmono := vectorSpan_mono ℝ heint
    have hfin := Submodule.finrank_mono hmono
    have hedim : Module.finrank ℝ (vectorSpan ℝ e) = 1 := hde
    omega
  have hdint : faceDim (A ∩ B) = 1 := by
    show Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) = 1
    have hdA' : Module.finrank ℝ (vectorSpan ℝ A) = 2 := hdA
    have hdintlt' : Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) < 2 := by
      have hlt0 : Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) <
          Module.finrank ℝ (vectorSpan ℝ A) := hdintlt
      omega
    omega
  apply Set.Subset.antisymm
  · by_contra hnot
    have hss : e ⊂ A ∩ B := ⟨heint, hnot⟩
    have hlt := faceDim_lt_of_ssubset P he hint hss
    have hlt' : Module.finrank ℝ (vectorSpan ℝ e) <
        Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) := hlt
    have hde' : Module.finrank ℝ (vectorSpan ℝ e) = 1 := hde
    have hdint' : Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) = 1 := hdint
    omega
  · exact heint

/-- Attraversamenti di spigoli distinti sono distinti. -/
theorem tagli_distinti (P : ConvexPolytope 3) {v : E 3} (hv : v ∈ P.vertices)
    (l : E 3 →L[ℝ] ℝ) (c : ℝ) (hc : c < l v)
    (e d : SpigoloPer P v) (hed : e ≠ d)
    (hae : l (SpigoloPer.altro P v hv e) < c)
    (had : l (SpigoloPer.altro P v hv d) < c) :
    SpigoloPer.taglio P v hv l c e ≠ SpigoloPer.taglio P v hv l c d := by
  intro h
  let x := SpigoloPer.taglio P v hv l c e
  have hxe : x ∈ e.val := (SpigoloPer.taglio_fatti P v hv l c hc e hae).1
  have hxd : x ∈ d.val := by
    change SpigoloPer.taglio P v hv l c e ∈ d.val
    rw [h]
    exact (SpigoloPer.taglio_fatti P v hv l c hc d had).1
  have hxv : x ≠ v := by
    intro hx
    have hxlevel := (SpigoloPer.taglio_fatti P v hv l c hc e hae).2.1
    change l x = c at hxlevel
    rw [hx] at hxlevel
    linarith
  have heq := spigoli_eq_of_punto_comune P e.property.1 e.property.2.1
    e.property.2.2 d.property.1 d.property.2.1 d.property.2.2 hxe hxd hxv
  exact hed (Subtype.ext heq)

/-- Il cono della sezione nel punto che attraversa uno spigolo comune a due
faccette. Le due direzioni sono quelle verso gli altri spigoli delle due
faccette. -/
theorem cono_al_taglio (P : ConvexPolytope 3) {v : E 3} (hv : v ∈ P.vertices)
    (l : E 3 →L[ℝ] ℝ) (c : ℝ) (hc : c < l v)
    (hvert : ∀ u ∈ P.vertices, u ≠ v → l u < c)
    (e eA eB : SpigoloPer P v)
    {A B : Set (E 3)}
    (hA : P.IsFace A) (hdA : faceDim A = 2) (_hvA : v ∈ A)
    (hB : P.IsFace B) (hdB : faceDim B = 2) (_hvB : v ∈ B)
    (heA : e.val ⊆ A) (heB : e.val ⊆ B) (hAB : A ≠ B)
    (heAA : eA.val ⊆ A) (heBB : eB.val ⊆ B)
    (heAne : eA ≠ e) (heBne : eB ≠ e) :
    ∀ z ∈ P.toSet ∩ {q | l q = c},
      ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
        z = SpigoloPer.taglio P v hv l c e +
          s • (SpigoloPer.taglio P v hv l c eA -
            SpigoloPer.taglio P v hv l c e) +
          t • (SpigoloPer.taglio P v hv l c eB -
            SpigoloPer.taglio P v hv l c e) := by
  classical
  let x : E 3 := SpigoloPer.taglio P v hv l c e
  let yA : E 3 := SpigoloPer.taglio P v hv l c eA
  let yB : E 3 := SpigoloPer.taglio P v hv l c eB
  have hae : l (SpigoloPer.altro P v hv e) < c :=
    hvert _ (SpigoloPer.altro_spec P v hv e).1
      (SpigoloPer.altro_spec P v hv e).2.2.1
  have haA : l (SpigoloPer.altro P v hv eA) < c :=
    hvert _ (SpigoloPer.altro_spec P v hv eA).1
      (SpigoloPer.altro_spec P v hv eA).2.2.1
  have haB : l (SpigoloPer.altro P v hv eB) < c :=
    hvert _ (SpigoloPer.altro_spec P v hv eB).1
      (SpigoloPer.altro_spec P v hv eB).2.2.1
  have hxe : x ∈ e.val := (SpigoloPer.taglio_fatti P v hv l c hc e hae).1
  have hyAeA : yA ∈ eA.val :=
    (SpigoloPer.taglio_fatti P v hv l c hc eA haA).1
  have hyBeB : yB ∈ eB.val :=
    (SpigoloPer.taglio_fatti P v hv l c hc eB haB).1
  have hxval : l x = c := (SpigoloPer.taglio_fatti P v hv l c hc e hae).2.1
  have hyAval : l yA = c :=
    (SpigoloPer.taglio_fatti P v hv l c hc eA haA).2.1
  have hyBval : l yB = c :=
    (SpigoloPer.taglio_fatti P v hv l c hc eB haB).2.1
  have hxA : x ∈ A := heA hxe
  have hxB : x ∈ B := heB hxe
  have hyAA : yA ∈ A := heAA hyAeA
  have hyBB : yB ∈ B := heBB hyBeB
  have hyAne : yA ≠ x :=
    tagli_distinti P hv l c hc eA e heAne haA hae
  have hyBne : yB ≠ x :=
    tagli_distinti P hv l c hc eB e heBne haB hae
  have hint : A ∩ B = e.val :=
    intersezione_faccette_eq_spigolo P e.property.1 e.property.2.1
      hA hdA hB hdB heA heB hAB
  have hyBnotA : yB ∉ A := by
    intro hyBA
    have hyBe : yB ∈ e.val := by
      rw [← hint]
      exact ⟨hyBA, hyBB⟩
    have hyBsing : yB ∈ ({x} : Set (E 3)) := by
      rw [← (SpigoloPer.taglio_fatti P v hv l c hc e hae).2.2]
      exact ⟨hyBe, hyBval⟩
    exact hyBne (Set.mem_singleton_iff.mp hyBsing)
  have hyAnotB : yA ∉ B := by
    intro hyAB
    have hyAe : yA ∈ e.val := by
      rw [← hint]
      exact ⟨hyAA, hyAB⟩
    have hyAsing : yA ∈ ({x} : Set (E 3)) := by
      rw [← (SpigoloPer.taglio_fatti P v hv l c hc e hae).2.2]
      exact ⟨hyAe, hyAval⟩
    exact hyAne (Set.mem_singleton_iff.mp hyAsing)
  obtain ⟨lA, hmemA, hcharA⟩ := espositore_di_faccia P hA
  obtain ⟨lB, hmemB, hcharB⟩ := espositore_di_faccia P hB
  have hAx : ∀ z ∈ P.toSet, lA z ≤ lA x := (hmemA x hxA).2
  have hBx : ∀ z ∈ P.toSet, lB z ≤ lB x := (hmemB x hxB).2
  have hAyA : lA yA = lA x := by
    exact le_antisymm ((hmemA x hxA).2 yA (hmemA yA hyAA).1)
      ((hmemA yA hyAA).2 x (hmemA x hxA).1)
  have hByB : lB yB = lB x := by
    exact le_antisymm ((hmemB x hxB).2 yB (hmemB yB hyBB).1)
      ((hmemB yB hyBB).2 x (hmemB x hxB).1)
  have hAyB : lA yB < lA x := by
    rcases lt_or_eq_of_le (hAx yB (hmemB yB hyBB).1) with h | h
    · exact h
    · have : yB ∈ A := hcharA yB (hmemB yB hyBB).1
          (fun z hz => le_trans (hAx z hz) (le_of_eq h.symm))
      exact (hyBnotA this).elim
  have hByA : lB yA < lB x := by
    rcases lt_or_eq_of_le (hBx yA (hmemA yA hyAA).1) with h | h
    · exact h
    · have : yA ∈ B := hcharB yA (hmemA yA hyAA).1
          (fun z hz => le_trans (hBx z hz) (le_of_eq h.symm))
      exact (hyAnotB this).elim
  let u : E 3 := yA - x
  let w : E 3 := yB - x
  have hAu : lA u = 0 := by
    dsimp [u]
    simp only [map_sub]
    linarith
  have hAw : lA w < 0 := by
    dsimp [w]
    simp only [map_sub]
    linarith
  have hBu : lB u < 0 := by
    dsimp [u]
    simp only [map_sub]
    linarith
  have hBw : lB w = 0 := by
    dsimp [w]
    simp only [map_sub]
    linarith
  have hLI : LinearIndependent ℝ ![u, w] := by
    rw [linearIndependent_fin2]
    constructor
    · show w ≠ 0
      exact sub_ne_zero.mpr hyBne
    · intro q
      show q • w ≠ u
      intro hq
      have hmap := congrArg lA hq
      simp only [map_smul, smul_eq_mul] at hmap
      rw [hAu] at hmap
      have hq0 : q = 0 := by nlinarith
      rw [hq0, zero_smul] at hq
      exact (sub_ne_zero.mpr hyAne) hq.symm
  let U : Submodule ℝ (E 3) := Submodule.span ℝ (Set.range ![u, w])
  have hUker : U ≤ LinearMap.ker l.toLinearMap := by
    rw [Submodule.span_le]
    rintro q ⟨i, rfl⟩
    rcases i with ⟨iv, hi⟩
    interval_cases iv
    · show l u = 0
      dsimp [u]
      simp only [map_sub]
      linarith
    · show l w = 0
      dsimp [w]
      simp only [map_sub]
      linarith
  have hsurj : Function.Surjective l.toLinearMap := by
    intro r
    refine ⟨(r / (l v - c)) • (v - x), ?_⟩
    change l ((r / (l v - c)) • (v - x)) = r
    simp only [map_smul, map_sub, smul_eq_mul]
    rw [hxval]
    exact div_mul_cancel₀ r (ne_of_gt (by linarith : 0 < l v - c))
  have hrange : Module.finrank ℝ (LinearMap.range l.toLinearMap) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  have hker : Module.finrank ℝ (LinearMap.ker l.toLinearMap) = 2 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker l.toLinearMap
    have hE : Module.finrank ℝ (E 3) = 3 := by
      rw [finrank_euclideanSpace]
      simp
    omega
  have hUdim : Module.finrank ℝ U = 2 := by
    dsimp [U]
    rw [finrank_span_eq_card hLI]
    simp
  have hUeq : U = LinearMap.ker l.toLinearMap := by
    apply Submodule.eq_of_le_of_finrank_le hUker
    omega
  intro z hz
  have hzker : z - x ∈ LinearMap.ker l.toLinearMap := by
    change l (z - x) = 0
    simp only [map_sub]
    have hzval : l z = c := hz.2
    linarith
  rw [← hUeq] at hzker
  obtain ⟨coef, hcoef⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hzker
  rw [Fin.sum_univ_two] at hcoef
  have hcoef' : coef 0 • u + coef 1 • w = z - x := hcoef
  have hzform : z = x + coef 0 • u + coef 1 • w := by
    have h := congrArg (fun q => q + x) hcoef'
    simp at h
    rw [← h]
    abel
  have hAz : lA z = lA x + coef 1 * lA w := by
    rw [hzform]
    simp only [map_add, map_smul, smul_eq_mul, hAu, mul_zero, add_zero]
  have hBz : lB z = lB x + coef 0 * lB u := by
    rw [hzform]
    simp only [map_add, map_smul, smul_eq_mul, hBw, mul_zero, add_zero]
  have ht : 0 ≤ coef 1 := by
    have hmax := hAx z hz.1
    rw [hAz] at hmax
    by_contra hneg
    push Not at hneg
    nlinarith
  have hs : 0 ≤ coef 0 := by
    have hmax := hBx z hz.1
    rw [hBz] at hmax
    by_contra hneg
    push Not at hneg
    nlinarith
  exact ⟨coef 0, coef 1, hs, ht, hzform⟩

/-- Le due faccette di uno spigolo e, in ciascuna, l'altro spigolo per `v`. -/
structure StellaSpigolo (P : ConvexPolytope 3) (v : E 3)
    (e : SpigoloPer P v) where
  A : Set (E 3)
  B : Set (E 3)
  hA : P.IsFace A
  hdA : faceDim A = 2
  hB : P.IsFace B
  hdB : faceDim B = 2
  heA : e.val ⊆ A
  heB : e.val ⊆ B
  hAB : A ≠ B
  eA : SpigoloPer P v
  eB : SpigoloPer P v
  heAA : eA.val ⊆ A
  heBB : eB.val ⊆ B
  heAne : eA ≠ e
  heBne : eB ≠ e

/-- Ogni spigolo per un vertice di un politopo 3D full-dimensional ha una
stella completa. -/
theorem stella_spigolo_esiste (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) (e : SpigoloPer P v) :
    Nonempty (StellaSpigolo P v e) := by
  classical
  have hPdim : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
  have hgap : faceDim e.val + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ P.toSet) := by
    rw [e.property.2.1, hPdim]
  obtain ⟨A, hA, heAss, hAne⟩ := interpolazione P e.property.1 hgap
  have heA : e.val ⊆ A := heAss.subset
  have hdA : faceDim A = 2 := by
    show Module.finrank ℝ (vectorSpan ℝ A) = 2
    have hlo0 := faceDim_lt_of_ssubset P e.property.1 hA heAss
    have hlo : Module.finrank ℝ (vectorSpan ℝ e.val) <
        Module.finrank ℝ (vectorSpan ℝ A) := hlo0
    have hedim : Module.finrank ℝ (vectorSpan ℝ e.val) = 1 := e.property.2.1
    have hAss : A ⊂ P.toSet :=
      ⟨face_subset_toSet P hA, fun hsub =>
        hAne (Set.Subset.antisymm (face_subset_toSet P hA) hsub)⟩
    have hhi0 := faceDim_lt_of_ssubset P hA (toSet_isFace P) hAss
    have hhi : Module.finrank ℝ (vectorSpan ℝ A) <
        Module.finrank ℝ (vectorSpan ℝ P.toSet) := hhi0
    omega
  obtain ⟨B, hB, hdB, heB, hBA⟩ :=
    seconda_faccetta P hfull e.property.1 e.property.2.1 hA hdA heA
  have hvA : v ∈ A := heA e.property.2.2
  have hvB : v ∈ B := heB e.property.2.2
  obtain ⟨eA, heAA, heAne, huniqA⟩ :=
    unico_altro_spigolo_nella_faccetta P hv hA hdA hvA e heA
  obtain ⟨eB, heBB, heBne, huniqB⟩ :=
    unico_altro_spigolo_nella_faccetta P hv hB hdB hvB e heB
  exact ⟨⟨A, B, hA, hdA, hB, hdB, heA, heB, hBA.symm,
    eA, eB, heAA, heBB, heAne, heBne⟩⟩

/-- Scelta canonica (classica) della stella di ogni spigolo. -/
noncomputable def stellaSpigolo (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) (e : SpigoloPer P v) :
    StellaSpigolo P v e :=
  Classical.choice (stella_spigolo_esiste P hfull hv e)

/-- Principio locale-globale sulla sezione, ricavato dal cono al taglio. -/
theorem locale_globale_taglio (P : ConvexPolytope 3) {v : E 3}
    (hv : v ∈ P.vertices) (l : E 3 →L[ℝ] ℝ) (c : ℝ) (hc : c < l v)
    (hvert : ∀ u ∈ P.vertices, u ≠ v → l u < c)
    (e : SpigoloPer P v) (D : StellaSpigolo P v e)
    (h : E 3 →L[ℝ] ℝ)
    (hA : h (SpigoloPer.taglio P v hv l c D.eA) ≤
      h (SpigoloPer.taglio P v hv l c e))
    (hB : h (SpigoloPer.taglio P v hv l c D.eB) ≤
      h (SpigoloPer.taglio P v hv l c e)) :
    ∀ z ∈ P.toSet ∩ {q | l q = c},
      h z ≤ h (SpigoloPer.taglio P v hv l c e) := by
  intro z hz
  obtain ⟨s, t, hs, ht, hzform⟩ :=
    cono_al_taglio P hv l c hc hvert e D.eA D.eB
      D.hA D.hdA (D.heA e.property.2.2)
      D.hB D.hdB (D.heB e.property.2.2)
      D.heA D.heB D.hAB D.heAA D.heBB D.heAne D.heBne z hz
  have hval : h z = h (SpigoloPer.taglio P v hv l c e) +
      s * (h (SpigoloPer.taglio P v hv l c D.eA) -
        h (SpigoloPer.taglio P v hv l c e)) +
      t * (h (SpigoloPer.taglio P v hv l c D.eB) -
        h (SpigoloPer.taglio P v hv l c e)) := by
    rw [hzform]
    simp only [map_add, map_smul, map_sub, smul_eq_mul]
  rw [hval]
  nlinarith [mul_nonneg hs (by linarith : 0 ≤
      h (SpigoloPer.taglio P v hv l c e) -
        h (SpigoloPer.taglio P v hv l c D.eA)),
    mul_nonneg ht (by linarith : 0 ≤
      h (SpigoloPer.taglio P v hv l c e) -
        h (SpigoloPer.taglio P v hv l c D.eB))]

/-- Adiacenza fra spigoli del fan: sono contenuti in una stessa faccetta. -/
def CondividonoFaccetta (P : ConvexPolytope 3) (v : E 3)
    (e d : SpigoloPer P v) : Prop :=
  ∃ A : Set (E 3), P.IsFace A ∧ faceDim A = 2 ∧ e.val ⊆ A ∧ d.val ⊆ A

/-- La camminata del simplesso sulla sezione connette qualunque coppia di
spigoli per il vertice. -/
theorem spigoli_del_ventaglio_connessi (P : ConvexPolytope 3)
    (hfull : P.IsFullDim) {v : E 3} (hv : v ∈ P.vertices)
    (e₀ es : SpigoloPer P v) :
    Relation.ReflTransGen (CondividonoFaccetta P v) e₀ es := by
  classical
  obtain ⟨l, c, hc, hvert⟩ := esiste_livello_separatore P hfull hv
  let Ds : StellaSpigolo P v es := stellaSpigolo P hfull hv es
  obtain ⟨lA, hmemA, hcharA⟩ := espositore_di_faccia P Ds.hA
  obtain ⟨lB, hmemB, hcharB⟩ := espositore_di_faccia P Ds.hB
  let h : E 3 →L[ℝ] ℝ := lA + lB
  let φ : SpigoloPer P v → ℝ :=
    fun e => h (SpigoloPer.taglio P v hv l c e)
  let FaceType := {f : Set (E 3) // P.IsFace f}
  letI : Fintype FaceType := (facce_finite P).fintype
  let incl : SpigoloPer P v → FaceType := fun e => ⟨e.val, e.property.1⟩
  have hincl : Function.Injective incl := by
    intro e d hed
    apply Subtype.ext
    exact congrArg (fun f : FaceType => f.val) hed
  letI : Fintype (SpigoloPer P v) := Fintype.ofInjective incl hincl
  let X : Finset (SpigoloPer P v) := Finset.univ
  have hlg : ∀ e ∈ X,
      (∀ d ∈ X, CondividonoFaccetta P v e d → φ d ≤ φ e) →
      ∀ z ∈ X, φ z ≤ φ e := by
    intro e heX hloc z hzX
    let D : StellaSpigolo P v e := stellaSpigolo P hfull hv e
    have hadjA : CondividonoFaccetta P v e D.eA :=
      ⟨D.A, D.hA, D.hdA, D.heA, D.heAA⟩
    have hadjB : CondividonoFaccetta P v e D.eB :=
      ⟨D.B, D.hB, D.hdB, D.heB, D.heBB⟩
    have hleA : h (SpigoloPer.taglio P v hv l c D.eA) ≤
        h (SpigoloPer.taglio P v hv l c e) := by
      exact hloc D.eA (by simp [X]) hadjA
    have hleB : h (SpigoloPer.taglio P v hv l c D.eB) ≤
        h (SpigoloPer.taglio P v hv l c e) := by
      exact hloc D.eB (by simp [X]) hadjB
    have haz : l (SpigoloPer.altro P v hv z) < c :=
      hvert _ (SpigoloPer.altro_spec P v hv z).1
        (SpigoloPer.altro_spec P v hv z).2.2.1
    have hxzK : SpigoloPer.taglio P v hv l c z ∈
        P.toSet ∩ {q | l q = c} := by
      refine ⟨face_subset_toSet P z.property.1
          (SpigoloPer.taglio_fatti P v hv l c hc z haz).1, ?_⟩
      exact (SpigoloPer.taglio_fatti P v hv l c hc z haz).2.1
    have hle := locale_globale_taglio P hv l c hc hvert e D h hleA hleB
      (SpigoloPer.taglio P v hv l c z) hxzK
    exact hle
  let xs : E 3 := SpigoloPer.taglio P v hv l c es
  have haes : l (SpigoloPer.altro P v hv es) < c :=
    hvert _ (SpigoloPer.altro_spec P v hv es).1
      (SpigoloPer.altro_spec P v hv es).2.2.1
  have hxse : xs ∈ es.val :=
    (SpigoloPer.taglio_fatti P v hv l c hc es haes).1
  have hxsA : xs ∈ Ds.A := Ds.heA hxse
  have hxsB : xs ∈ Ds.B := Ds.heB hxse
  have hmaxA : ∀ q ∈ P.toSet, lA q ≤ lA xs := (hmemA xs hxsA).2
  have hmaxB : ∀ q ∈ P.toSet, lB q ≤ lB xs := (hmemB xs hxsB).2
  have hinter : Ds.A ∩ Ds.B = es.val :=
    intersezione_faccette_eq_spigolo P es.property.1 es.property.2.1
      Ds.hA Ds.hdA Ds.hB Ds.hdB Ds.heA Ds.heB Ds.hAB
  have hunico : ∀ z ∈ X, z ≠ es → φ z < φ es := by
    intro z hzX hzes
    have haz : l (SpigoloPer.altro P v hv z) < c :=
      hvert _ (SpigoloPer.altro_spec P v hv z).1
        (SpigoloPer.altro_spec P v hv z).2.2.1
    let xz : E 3 := SpigoloPer.taglio P v hv l c z
    have hxze : xz ∈ z.val := (SpigoloPer.taglio_fatti P v hv l c hc z haz).1
    have hxzT : xz ∈ P.toSet := face_subset_toSet P z.property.1 hxze
    have hxzval : l xz = c :=
      (SpigoloPer.taglio_fatti P v hv l c hc z haz).2.1
    have hAle : lA xz ≤ lA xs := hmaxA xz hxzT
    have hBle : lB xz ≤ lB xs := hmaxB xz hxzT
    have hsumle : φ z ≤ φ es := by
      dsimp [φ, h]
      simp only [add_apply]
      change lA xz + lB xz ≤ lA xs + lB xs
      linarith
    rcases lt_or_eq_of_le hsumle with hlt | heq
    · exact hlt
    · exfalso
      have heqsum : lA xz + lB xz = lA xs + lB xs := by
        simpa [φ, h, xz, xs] using heq
      have heqA : lA xz = lA xs := by linarith
      have heqB : lB xz = lB xs := by linarith
      have hxzA : xz ∈ Ds.A := hcharA xz hxzT
        (fun q hq => le_trans (hmaxA q hq) (le_of_eq heqA.symm))
      have hxzB : xz ∈ Ds.B := hcharB xz hxzT
        (fun q hq => le_trans (hmaxB q hq) (le_of_eq heqB.symm))
      have hxzes : xz ∈ es.val := by
        rw [← hinter]
        exact ⟨hxzA, hxzB⟩
      have hxsing : xz ∈ ({xs} : Set (E 3)) := by
        rw [← (SpigoloPer.taglio_fatti P v hv l c hc es haes).2.2]
        exact ⟨hxzes, hxzval⟩
      have hxzeq : xz = xs := Set.mem_singleton_iff.mp hxsing
      have hdist := tagli_distinti P hv l c hc z es hzes haz haes
      exact hdist hxzeq
  have hwalk := camminata_del_simplesso X (CondividonoFaccetta P v) φ
    hlg (xs := es) (by simp [X]) hunico (x₀ := e₀) (by simp [X])
  exact Relation.ReflTransGen.mono (fun _ _ hstep => hstep.2) _ _ hwalk

/-- Ogni faccetta che contiene `v` contiene uno spigolo per `v`. -/
theorem esiste_spigolo_nella_faccetta (P : ConvexPolytope 3)
    {v : E 3} (hv : v ∈ P.vertices)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) (hvA : v ∈ A) :
    ∃ e : SpigoloPer P v, e.val ⊆ A := by
  classical
  let Q : ConvexPolytope 3 := facePolytope P hA
  have hQT : Q.toSet = A := facePolytope_toSet P hA
  have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2 := by
    rw [hQT]
    exact hdA
  have hvQ : v ∈ Q.vertices := Finset.mem_filter.mpr ⟨hv, hvA⟩
  have hvface : Q.IsFace ({v} : Set (E 3)) := vertex_isFace Q hvQ
  have hgap : faceDim ({v} : Set (E 3)) + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ Q.toSet) := by
    rw [faceDim_singleton, hQdim]
  obtain ⟨g, hgQ, hvg, hgne⟩ := interpolazione Q hvface hgap
  have hdg : faceDim g = 1 := by
    show Module.finrank ℝ (vectorSpan ℝ g) = 1
    have hlo0 := faceDim_lt_of_ssubset Q hvface hgQ hvg
    have hlo : Module.finrank ℝ (vectorSpan ℝ ({v} : Set (E 3))) <
        Module.finrank ℝ (vectorSpan ℝ g) := hlo0
    have hdv : Module.finrank ℝ (vectorSpan ℝ ({v} : Set (E 3))) = 0 :=
      faceDim_singleton v
    have hgss : g ⊂ Q.toSet :=
      ⟨face_subset_toSet Q hgQ, fun hsub =>
        hgne (Set.Subset.antisymm (face_subset_toSet Q hgQ) hsub)⟩
    have hhi0 := faceDim_lt_of_ssubset Q hgQ (toSet_isFace Q) hgss
    have hhi : Module.finrank ℝ (vectorSpan ℝ g) <
        Module.finrank ℝ (vectorSpan ℝ Q.toSet) := hhi0
    omega
  have hgP : P.IsFace g := isFace_of_facePolytope P hA hgQ
  have hgA : g ⊆ A := by
    have := face_subset_toSet Q hgQ
    rwa [hQT] at this
  have hvgmem : v ∈ g := hvg.subset (Set.mem_singleton v)
  exact ⟨⟨g, hgP, hdg, hvgmem⟩, hgA⟩

/-- Trasferimento di un cammino di spigoli a un cammino di faccette. -/
theorem trasferisci_cammino_spigoli (P : ConvexPolytope 3) {v : E 3}
    {A : Set (E 3)} (_hA : P.IsFace A) (_hdA : faceDim A = 2) (_hvA : v ∈ A)
    {e₀ es : SpigoloPer P v} (he₀A : e₀.val ⊆ A)
    (hcam : Relation.ReflTransGen (CondividonoFaccetta P v) e₀ es) :
    ∀ {B : Set (E 3)}, P.IsFace B → faceDim B = 2 → v ∈ B → es.val ⊆ B →
      Relation.ReflTransGen
        (fun X Y => (P.IsFace Y ∧ faceDim Y = 2 ∧ v ∈ Y) ∧
          SpigoloComune P v X Y) A B := by
  induction hcam with
  | refl =>
      intro B hB hdB hvB heB
      apply Relation.ReflTransGen.single
      exact ⟨⟨hB, hdB, hvB⟩,
        ⟨e₀.val, e₀.property.1, e₀.property.2.1, e₀.property.2.2,
          he₀A, heB⟩⟩
  | @tail b d hprev hadj ih =>
      intro B hB hdB hvB hdBsub
      obtain ⟨C, hC, hdC, hbC, hdCsub⟩ := hadj
      have hvC : v ∈ C := hbC b.property.2.2
      have hAC := ih hC hdC hvC hbC
      have hCB : Relation.ReflTransGen
          (fun X Y => (P.IsFace Y ∧ faceDim Y = 2 ∧ v ∈ Y) ∧
            SpigoloComune P v X Y) C B := by
        apply Relation.ReflTransGen.single
        exact ⟨⟨hB, hdB, hvB⟩,
          ⟨d.val, d.property.1, d.property.2.1, d.property.2.2,
            hdCsub, hdBsub⟩⟩
      exact hAC.trans hCB

theorem ventaglio_connesso (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices)
    {A B : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) (hvA : v ∈ A)
    (hB : P.IsFace B) (hdB : faceDim B = 2) (hvB : v ∈ B) :
    Relation.ReflTransGen
      (fun X Y => (P.IsFace Y ∧ faceDim Y = 2 ∧ v ∈ Y) ∧ SpigoloComune P v X Y)
      A B := by
  obtain ⟨eA, heAA⟩ := esiste_spigolo_nella_faccetta P hv hA hdA hvA
  obtain ⟨eB, heBB⟩ := esiste_spigolo_nella_faccetta P hv hB hdB hvB
  have hcam := spigoli_del_ventaglio_connessi P hfull hv eA eB
  exact trasferisci_cammino_spigoli P hA hdA hvA heAA hcam hB hdB hvB heBB

/-- In un politopo full-dimensional di `ℝ³`, ogni vertice appartiene ad
almeno tre faccette a due a due distinte. -/
theorem tre_faccette_al_vertice_conn (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) :
    ∃ A B C : Set (E 3),
      P.IsFace A ∧ faceDim A = 2 ∧ v ∈ A ∧
      P.IsFace B ∧ faceDim B = 2 ∧ v ∈ B ∧
      P.IsFace C ∧ faceDim C = 2 ∧ v ∈ C ∧
      A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  classical
  obtain ⟨F, hFv⟩ := bandiera_al_vertice P hfull hv
  have hve : v ∈ F.face 1 := by
    have hsub := (F.strict_mono 0 1 (by decide)).subset
    apply hsub
    rw [hFv]
    exact Set.mem_singleton v
  let e : SpigoloPer P v :=
    ⟨F.face 1, F.isFace 1, F.dim_eq 1, hve⟩
  let A : Set (E 3) := F.face 2
  have hA : P.IsFace A := F.isFace 2
  have hdA : faceDim A = 2 := F.dim_eq 2
  have heA : e.val ⊆ A := (F.strict_mono 1 2 (by decide)).subset
  have hvA : v ∈ A := heA e.property.2.2
  obtain ⟨B, hB, hdB, heB, hBA⟩ :=
    seconda_faccetta P hfull e.property.1 e.property.2.1 hA hdA heA
  have hvB : v ∈ B := heB e.property.2.2
  obtain ⟨e', he'A, he'ne, huniq⟩ :=
    unico_altro_spigolo_nella_faccetta P hv hA hdA hvA e heA
  obtain ⟨C, hC, hdC, he'C, hCA⟩ :=
    seconda_faccetta P hfull e'.property.1 e'.property.2.1 hA hdA he'A
  have hvC : v ∈ C := he'C e'.property.2.2
  have hAB : A ≠ B := hBA.symm
  have hAC : A ≠ C := hCA.symm
  have hBC : B ≠ C := by
    intro hBCeq
    have hinter : A ∩ B = e.val :=
      intersezione_faccette_eq_spigolo P e.property.1 e.property.2.1
        hA hdA hB hdB heA heB hAB
    let p : E 3 := SpigoloPer.altro P v hv e'
    have hpe' : p ∈ e'.val := (SpigoloPer.altro_spec P v hv e').2.1
    have hpv : p ≠ v := (SpigoloPer.altro_spec P v hv e').2.2.1
    have hpB : p ∈ B := by
      rw [hBCeq]
      exact he'C hpe'
    have hpe : p ∈ e.val := by
      rw [← hinter]
      exact ⟨he'A hpe', hpB⟩
    have heq := spigoli_eq_of_punto_comune P e'.property.1 e'.property.2.1
      e'.property.2.2 e.property.1 e.property.2.1 e.property.2.2
      hpe' hpe hpv
    exact he'ne (Subtype.ext heq)
  exact ⟨A, B, C, hA, hdA, hvA, hB, hdB, hvB, hC, hdC, hvC,
    hAB, hAC, hBC⟩

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart9

section BundlePart10
/- Source: Cubical/Polytope/FaccetteConnesse.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.FaccetteConnesse.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/








open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ}

/-! The convex hull of the image of a finite polytope, with the redundant
image points removed.  This is deliberately stated for a continuous linear
map: the quotient used below is not injective. -/
noncomputable def linearImagePolytope (P : ConvexPolytope n)
    (f : E n →L[ℝ] E m) : ConvexPolytope m := by
  classical
  let S : Finset (E m) := P.vertices.image f
  let K : Set (E m) := convexHull ℝ (S : Set (E m))
  let V : Finset (E m) := S.filter (fun x => x ∈ K.extremePoints ℝ)
  have hSne : S.Nonempty := P.vertices_nonempty.image f
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hSne
    exact ⟨x, subset_convexHull ℝ _ (by exact_mod_cast hx)⟩
  have hKcompact : IsCompact K := S.finite_toSet.isCompact_convexHull ℝ
  have hVne : V.Nonempty := by
    obtain ⟨x, hx⟩ := hKcompact.extremePoints_nonempty hKne
    have hxS : x ∈ (S : Set (E m)) := extremePoints_convexHull_subset hx
    exact ⟨x, Finset.mem_filter.mpr ⟨by exact_mod_cast hxS, hx⟩⟩
  have hVset : (V : Set (E m)) = K.extremePoints ℝ := by
    ext x
    simp only [V, Finset.mem_coe, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hx
      exact ⟨by exact_mod_cast (extremePoints_convexHull_subset hx), hx⟩
  have hKV : convexHull ℝ (V : Set (E m)) = K := by
    have hKM := closure_convexHull_extremePoints hKcompact (convex_convexHull ℝ _)
    rw [← hVset] at hKM
    rw [← hKM]
    exact (V.finite_toSet.isClosed_convexHull ℝ).closure_eq.symm
  exact
    { vertices := V
      vertices_nonempty := hVne
      vertices_eq_extremePoints := by
        rw [hKV, hVset] }

theorem linearImagePolytope_toSet (P : ConvexPolytope n)
    (f : E n →L[ℝ] E m) :
    (linearImagePolytope P f).toSet = f '' P.toSet := by
  classical
  let S : Finset (E m) := P.vertices.image f
  let K : Set (E m) := convexHull ℝ (S : Set (E m))
  let V : Finset (E m) := S.filter (fun x => x ∈ K.extremePoints ℝ)
  have hKcompact : IsCompact K := S.finite_toSet.isCompact_convexHull ℝ
  have hVset : (V : Set (E m)) = K.extremePoints ℝ := by
    ext x
    simp only [V, Finset.mem_coe, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hx
      exact ⟨by exact_mod_cast (extremePoints_convexHull_subset hx), hx⟩
  have hKV : convexHull ℝ (V : Set (E m)) = K := by
    have hKM := closure_convexHull_extremePoints hKcompact (convex_convexHull ℝ _)
    rw [← hVset] at hKM
    rw [← hKM]
    exact (V.finite_toSet.isClosed_convexHull ℝ).closure_eq.symm
  change convexHull ℝ
      (((linearImagePolytope P f).vertices : Finset (E m)) : Set (E m)) = _
  change convexHull ℝ (V : Set (E m)) = _
  rw [hKV]
  have hS : (S : Set (E m)) = f '' (P.vertices : Set (E n)) := by
    ext x
    simp [S]
  rw [show K = convexHull ℝ (S : Set (E m)) from rfl, hS]
  exact (f.toLinearMap.toAffineMap.image_convexHull
    (P.vertices : Set (E n))).symm

/-! Orthogonal projection to `Uᵌ ∩ W` is the concrete quotient of `W`
by `U`.  The point of the next lemma is the exact fibre statement; no
ambient full-dimensionality is used. -/
theorem relative_starProjection_fiber
    {U W : Submodule ℝ (E n)} (hUW : U ≤ W) {x y : E n}
    (hxyW : x - y ∈ W) :
    (U.orthogonal ⊓ W).starProjection x =
        (U.orthogonal ⊓ W).starProjection y ↔
      x - y ∈ U := by
  let V : Submodule ℝ (E n) := U.orthogonal ⊓ W
  constructor
  · intro hproj
    have hzero : V.starProjection (x - y) = 0 := by
      rw [map_sub, hproj, sub_self]
    have hperp : x - y ∈ V.orthogonal := by
      rw [← V.ker_starProjection]
      exact hzero
    let p : E n := U.orthogonal.starProjection (x - y)
    have hpUperp : p ∈ U.orthogonal :=
      U.orthogonal.starProjection_apply_mem (x - y)
    have hdiffU : x - y - p ∈ U := by
      dsimp [p]
      rw [Submodule.starProjection_orthogonal_val]
      simpa only [sub_sub_cancel] using U.starProjection_apply_mem (x - y)
    have hpW : p ∈ W := by
      have hpform : p = (x - y) - (x - y - p) := by abel
      rw [hpform]
      exact W.sub_mem hxyW (hUW hdiffU)
    have hpV : p ∈ V := ⟨hpUperp, hpW⟩
    have hdp : inner ℝ (x - y) p = 0 := by
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal V (x - y)).mp hperp p hpV
    have hdiffp : inner ℝ (x - y - p) p = 0 := by
      exact (Submodule.mem_orthogonal U p).mp hpUperp (x - y - p) hdiffU
    have hpp : inner ℝ p p = 0 := by
      rw [inner_sub_left] at hdiffp
      linarith
    have hpzero : p = 0 := inner_self_eq_zero.mp hpp
    simpa [hpzero] using hdiffU
  · intro hxyU
    have hxyVperp : x - y ∈ V.orthogonal := by
      intro z hz
      rw [real_inner_comm]
      exact hz.1 (x - y) hxyU
    have hzero : V.starProjection (x - y) = 0 := by
      exact V.starProjection_apply_eq_zero_iff.mpr hxyVperp
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero

theorem relative_sub_starProjection_mem
    {U W : Submodule ℝ (E n)} (hUW : U ≤ W) {z : E n} (hzW : z ∈ W) :
    z - (U.orthogonal ⊓ W).starProjection z ∈ U := by
  let V : Submodule ℝ (E n) := U.orthogonal ⊓ W
  have hpV : V.starProjection z ∈ V := V.starProjection_apply_mem z
  have hdiffW : z - V.starProjection z ∈ W :=
    W.sub_mem hzW hpV.2
  apply (relative_starProjection_fiber hUW hdiffW).mp
  exact (V.starProjection_eq_self_iff.mpr hpV).symm

theorem relative_image_isFace (P : ConvexPolytope n)
    {A B C : Set (E n)} (hA : P.IsFace A) (hB : P.IsFace B)
    (hC : P.IsFace C) (hAB : A ⊆ B) (hAC : A ⊆ C) (hCB : C ⊆ B)
    (e : ↥((vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B) ≃L[ℝ] E 3) :
    let V := (vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B
    let q : E n →L[ℝ] E 3 :=
      e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
    let Q := linearImagePolytope (facePolytope P hB) q
    Q.IsFace (q '' C) := by
  classical
  dsimp only
  let U : Submodule ℝ (E n) := vectorSpan ℝ A
  let W : Submodule ℝ (E n) := vectorSpan ℝ B
  let V : Submodule ℝ (E n) := U.orthogonal ⊓ W
  let q : E n →L[ℝ] E 3 :=
    e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
  let Q := linearImagePolytope (facePolytope P hB) q
  let QB := facePolytope P hB
  have hCQB : QB.IsFace C := facePolytope_isFace_of P hB hC hCB
  obtain ⟨l, hmem, hchar⟩ := espositore_di_faccia QB hCQB
  obtain ⟨a, haA⟩ := hA.2
  have hUW : U ≤ W := vectorSpan_mono ℝ hAB
  have hkill : U ≤ LinearMap.ker l.toLinearMap := by
    change vectorSpan ℝ A ≤ LinearMap.ker l.toLinearMap
    rw [vectorSpan_eq_span_vsub_set_right ℝ haA, Submodule.span_le]
    rintro z ⟨x, hxA, rfl⟩
    change l (x - a) = 0
    rw [map_sub]
    have hxC : x ∈ C := hAC hxA
    have haC : a ∈ C := hAC haA
    have heq : l x = l a := by
      exact le_antisymm ((hmem a haC).2 x (hmem x hxC).1)
        ((hmem x hxC).2 a (hmem a haC).1)
    linarith
  let pull : E 3 →L[ℝ] E n :=
    V.subtypeL.comp e.symm.toContinuousLinearMap
  let l3 : E 3 →L[ℝ] ℝ := l.comp pull
  have hlinear : ∀ z ∈ W, l3 (q z) = l z := by
    intro z hzW
    have hdiff : z - V.starProjection z ∈ U :=
      relative_sub_starProjection_mem hUW hzW
    have hzero : l (z - V.starProjection z) = 0 := hkill hdiff
    rw [map_sub] at hzero
    have heval : (pull (q z) : E n) = V.starProjection z := by
      dsimp only [pull, q, ContinuousLinearMap.comp_apply]
      have heq := e.symm_apply_apply (V.orthogonalProjectionOnto z)
      change ((e.symm (e (V.orthogonalProjectionOnto z)) : V) : E n) =
        V.starProjection z
      rw [heq]
      rfl
    change l (pull (q z)) = l z
    rw [heval]
    linarith
  let κ : ℝ := l3 (q a) - l a
  have hfactor : ∀ z ∈ B, l3 (q z) = l z + κ := by
    intro z hzB
    have haB : a ∈ B := hAB haA
    have hzaW : z - a ∈ W := vsub_mem_vectorSpan ℝ hzB haB
    have hlin := hlinear (z - a) hzaW
    simp only [map_sub] at hlin
    dsimp [κ]
    linarith
  have hQT : Q.toSet = q '' B := by
    rw [linearImagePolytope_toSet, facePolytope_toSet P hB]
  refine ⟨?_, hC.2.image q⟩
  intro _hne
  refine ⟨l3, Set.ext ?_⟩
  intro y
  constructor
  · rintro ⟨x, hxC, rfl⟩
    have hxB : x ∈ B := hCB hxC
    refine ⟨?_, ?_⟩
    · rw [hQT]
      exact ⟨x, hxB, rfl⟩
    · intro y' hy'
      rw [hQT] at hy'
      obtain ⟨z, hzB, rfl⟩ := hy'
      rw [hfactor x hxB, hfactor z hzB]
      have hzQB : z ∈ QB.toSet := by
        change z ∈ (facePolytope P hB).toSet
        rwa [facePolytope_toSet P hB]
      simpa [add_comm] using add_le_add_right ((hmem x hxC).2 z hzQB) κ
  · rintro ⟨hyQ, hymax⟩
    rw [hQT] at hyQ
    obtain ⟨x, hxB, rfl⟩ := hyQ
    refine ⟨x, ?_, rfl⟩
    have hxQB : x ∈ QB.toSet := by
      change x ∈ (facePolytope P hB).toSet
      rwa [facePolytope_toSet P hB]
    apply hchar x hxQB
    intro z hzQB
    have hzB : z ∈ B := by
      change z ∈ (facePolytope P hB).toSet at hzQB
      rwa [facePolytope_toSet P hB] at hzQB
    have hle := hymax (q z) (by rw [hQT]; exact ⟨z, hzB, rfl⟩)
    rw [hfactor x hxB, hfactor z hzB] at hle
    linarith

theorem relative_image_saturated (P : ConvexPolytope n)
    {A B C : Set (E n)} (hA : P.IsFace A) (hB : P.IsFace B)
    (hC : P.IsFace C) (hAB : A ⊆ B) (hAC : A ⊆ C) (hCB : C ⊆ B)
    (e : ↥((vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B) ≃L[ℝ] E 3) :
    let V := (vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B
    let q : E n →L[ℝ] E 3 :=
      e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
    ∀ x ∈ B, x ∈ q ⁻¹' (q '' C) → x ∈ C := by
  classical
  dsimp only
  let U : Submodule ℝ (E n) := vectorSpan ℝ A
  let W : Submodule ℝ (E n) := vectorSpan ℝ B
  let V : Submodule ℝ (E n) := U.orthogonal ⊓ W
  let q : E n →L[ℝ] E 3 :=
    e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
  let QB := facePolytope P hB
  have hCQB : QB.IsFace C := facePolytope_isFace_of P hB hC hCB
  obtain ⟨l, hmem, hchar⟩ := espositore_di_faccia QB hCQB
  obtain ⟨a, haA⟩ := hA.2
  have hUW : U ≤ W := vectorSpan_mono ℝ hAB
  have hkill : U ≤ LinearMap.ker l.toLinearMap := by
    change vectorSpan ℝ A ≤ LinearMap.ker l.toLinearMap
    rw [vectorSpan_eq_span_vsub_set_right ℝ haA, Submodule.span_le]
    rintro z ⟨y, hyA, rfl⟩
    change l (y - a) = 0
    rw [map_sub]
    have hyC : y ∈ C := hAC hyA
    have haC : a ∈ C := hAC haA
    have heq : l y = l a := by
      exact le_antisymm ((hmem a haC).2 y (hmem y hyC).1)
        ((hmem y hyC).2 a (hmem a haC).1)
    linarith
  intro x hxB hximage
  obtain ⟨c, hcC, hqc⟩ := hximage
  have hxcW : x - c ∈ W :=
    vsub_mem_vectorSpan ℝ hxB (hCB hcC)
  have hprojSubtype : V.orthogonalProjectionOnto x =
      V.orthogonalProjectionOnto c := by
    apply e.injective
    exact hqc.symm
  have hproj : V.starProjection x = V.starProjection c := by
    exact congrArg (fun z : V => (z : E n)) hprojSubtype
  have hxcU : x - c ∈ U :=
    (relative_starProjection_fiber hUW hxcW).mp hproj
  have hzero : l (x - c) = 0 := hkill hxcU
  rw [map_sub] at hzero
  have hxQB : x ∈ QB.toSet := by
    change x ∈ (facePolytope P hB).toSet
    rwa [facePolytope_toSet P hB]
  apply hchar x hxQB
  intro z hzQB
  have hle := (hmem c hcC).2 z hzQB
  linarith

theorem relative_lift_isFace (P : ConvexPolytope n)
    {A B : Set (E n)} (_hA : P.IsFace A) (hB : P.IsFace B)
    (e : ↥((vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B) ≃L[ℝ] E 3)
    {Y : Set (E 3)} :
    let V := (vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B
    let q : E n →L[ℝ] E 3 :=
      e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
    let Q := linearImagePolytope (facePolytope P hB) q
    Q.IsFace Y → P.IsFace (B ∩ q ⁻¹' Y) := by
  classical
  dsimp only
  let V := (vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B
  let q : E n →L[ℝ] E 3 :=
    e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
  let QB := facePolytope P hB
  let Q := linearImagePolytope QB q
  intro hY
  obtain ⟨l3, hmem, hchar⟩ := espositore_di_faccia Q hY
  let l : E n →L[ℝ] ℝ := l3.comp q
  have hQT : Q.toSet = q '' B := by
    rw [linearImagePolytope_toSet, facePolytope_toSet P hB]
  have hLiftNe : (B ∩ q ⁻¹' Y).Nonempty := by
    obtain ⟨y, hyY⟩ := hY.2
    have hyQ : y ∈ Q.toSet := face_subset_toSet Q hY hyY
    rw [hQT] at hyQ
    obtain ⟨x, hxB, rfl⟩ := hyQ
    exact ⟨x, hxB, hyY⟩
  have hLiftQB : QB.IsFace (B ∩ q ⁻¹' Y) := by
    refine ⟨?_, hLiftNe⟩
    intro _hne
    refine ⟨l, Set.ext ?_⟩
    intro x
    constructor
    · rintro ⟨hxB, hqxY⟩
      have hqxQ : q x ∈ Q.toSet := by
        rw [hQT]
        exact ⟨x, hxB, rfl⟩
      refine ⟨?_, ?_⟩
      · change x ∈ (facePolytope P hB).toSet
        rwa [facePolytope_toSet P hB]
      · intro z hzQB
        have hzB : z ∈ B := by
          change z ∈ (facePolytope P hB).toSet at hzQB
          rwa [facePolytope_toSet P hB] at hzQB
        change l3 (q z) ≤ l3 (q x)
        exact (hmem (q x) hqxY).2 (q z) (by
          rw [hQT]
          exact ⟨z, hzB, rfl⟩)
    · rintro ⟨hxQB, hxmax⟩
      have hxB : x ∈ B := by
        change x ∈ (facePolytope P hB).toSet at hxQB
        rwa [facePolytope_toSet P hB] at hxQB
      refine ⟨hxB, ?_⟩
      apply hchar (q x) (by rw [hQT]; exact ⟨x, hxB, rfl⟩)
      intro y hyQ
      rw [hQT] at hyQ
      obtain ⟨z, hzB, rfl⟩ := hyQ
      apply hxmax z
      change z ∈ (facePolytope P hB).toSet
      rwa [facePolytope_toSet P hB]
  exact isFace_of_facePolytope P hB hLiftQB

theorem residuo_passo_sinistro (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (H K : P.Flag) (i ip : Fin n)
    (hHK : ∀ j : Fin n, j ≠ i → K.face j = H.face j) :
    Relation.ReflTransGen
      (fun S T : P.Flag =>
        T = adjacentFlag P hfull S i ∨ T = adjacentFlag P hfull S ip)
      H K := by
  by_cases heq : K.face i = H.face i
  · have hflag : K = H := by
      apply flag_ext
      funext j
      by_cases hji : j = i
      · simpa [hji] using heq
      · exact hHK j hji
    rw [hflag]
  · have hadj : FlagAdjacentAt P H K i := ⟨hHK, heq⟩
    exact Relation.ReflTransGen.single
      (Or.inl (adjacentFlag_eq_of_isAdjacent P hfull i hadj))

theorem residuo_passo_destro (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (H K : P.Flag) (i ip : Fin n)
    (hHK : ∀ j : Fin n, j ≠ ip → K.face j = H.face j) :
    Relation.ReflTransGen
      (fun S T : P.Flag =>
        T = adjacentFlag P hfull S i ∨ T = adjacentFlag P hfull S ip)
      H K := by
  by_cases heq : K.face ip = H.face ip
  · have hflag : K = H := by
      apply flag_ext
      funext j
      by_cases hjip : j = ip
      · simpa [hjip] using heq
      · exact hHK j hjip
    rw [hflag]
  · have hadj : FlagAdjacentAt P H K ip := ⟨hHK, heq⟩
    exact Relation.ReflTransGen.single
      (Or.inr (adjacentFlag_eq_of_isAdjacent P hfull ip hadj))

theorem residuo_salto_tre_connesso (P : ConvexPolytope n)
    {A B : Set (E n)} (hA : P.IsFace A) (hB : P.IsFace B) (hAB : A ⊂ B)
    (hrank : faceDim B = faceDim A + 3)
    {X X' : Set (E n)} (hX : P.IsFace X) (hX' : P.IsFace X')
    (hAX : A ⊂ X) (hXB : X ⊂ B) (hAX' : A ⊂ X') (hX'B : X' ⊂ B)
    (hdX : faceDim X = faceDim A + 2) (hdX' : faceDim X' = faceDim A + 2) :
    Relation.ReflTransGen
      (fun Y Z : Set (E n) =>
        P.IsFace Y ∧ P.IsFace Z ∧ A ⊂ Y ∧ A ⊂ Z ∧ Y ⊂ B ∧ Z ⊂ B ∧
          faceDim Y = faceDim A + 2 ∧ faceDim Z = faceDim A + 2 ∧
          ∃ R : Set (E n), P.IsFace R ∧ A ⊂ R ∧ R ⊂ Y ∧ R ⊂ Z ∧
            faceDim R = faceDim A + 1)
      X X' := by
  classical
  let U : Submodule ℝ (E n) := vectorSpan ℝ A
  let W : Submodule ℝ (E n) := vectorSpan ℝ B
  let V : Submodule ℝ (E n) := U.orthogonal ⊓ W
  have hUW : U ≤ W := vectorSpan_mono ℝ hAB.1
  have hdimV : Module.finrank ℝ V = 3 := by
    have hadd := Submodule.finrank_add_inf_finrank_orthogonal hUW
    change Module.finrank ℝ U + Module.finrank ℝ V =
      Module.finrank ℝ W at hadd
    change Module.finrank ℝ W = Module.finrank ℝ U + 3 at hrank
    omega
  let e : V ≃L[ℝ] E 3 := ContinuousLinearEquiv.ofFinrankEq (by
    rw [hdimV, finrank_euclideanSpace]
    simp)
  let q : E n →L[ℝ] E 3 :=
    e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
  let QB := facePolytope P hB
  let Q := linearImagePolytope QB q
  have hQT : Q.toSet = q '' B := by
    rw [linearImagePolytope_toSet, facePolytope_toSet P hB]
  have himage_face : ∀ {C : Set (E n)}, P.IsFace C → A ⊆ C → C ⊆ B →
      Q.IsFace (q '' C) := by
    intro C hC hAC hCB
    simpa [U, W, V, q, QB, Q] using
      (relative_image_isFace P hA hB hC hAB.1 hAC hCB e)
  have hsaturated : ∀ {C : Set (E n)}, P.IsFace C → A ⊆ C → C ⊆ B →
      ∀ x ∈ B, x ∈ q ⁻¹' (q '' C) → x ∈ C := by
    intro C hC hAC hCB
    simpa [U, W, V, q] using
      (relative_image_saturated P hA hB hC hAB.1 hAC hCB e)
  have hstrict_image : ∀ {C D : Set (E n)}, P.IsFace C →
      A ⊆ C → C ⊂ D → D ⊆ B → q '' C ⊂ q '' D := by
    intro C D hC hAC hCD hDB
    refine ⟨Set.image_mono hCD.1, ?_⟩
    intro hback
    obtain ⟨d, hdD, hdC⟩ := Set.exists_of_ssubset hCD
    apply hdC
    apply hsaturated hC hAC (hCD.1.trans hDB) d (hDB hdD)
    exact hback ⟨d, hdD, rfl⟩
  obtain ⟨a, haA⟩ := hA.2
  have hqA : ∀ z ∈ A, q z = q a := by
    intro z hzA
    have hzaU : z - a ∈ U := vsub_mem_vectorSpan ℝ hzA haA
    have hzaW : z - a ∈ W := hUW hzaU
    have hproj : V.starProjection z = V.starProjection a :=
      (relative_starProjection_fiber hUW hzaW).mpr hzaU
    change e (V.orthogonalProjectionOnto z) =
      e (V.orthogonalProjectionOnto a)
    apply congrArg e
    exact Subtype.ext hproj
  have hAimage : q '' A = ({q a} : Set (E 3)) := by
    ext y
    constructor
    · rintro ⟨z, hzA, rfl⟩
      exact Set.mem_singleton_iff.mpr (hqA z hzA)
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      exact ⟨a, haA, hy.symm⟩
  obtain ⟨C, hC, hAC, hCX, hdC⟩ :=
    faccia_intermedia P hA hX hAX (by exact hdX)
  obtain ⟨C', hC', hAC', hC'X', hdC'⟩ :=
    faccia_intermedia P hA hX' hAX' (by exact hdX')
  have hAq := himage_face hA (Subset.rfl) hAB.1
  have hCq := himage_face hC hAC.1 (hCX.1.trans hXB.1)
  have hC'q := himage_face hC' hAC'.1 (hC'X'.1.trans hX'B.1)
  have hXq := himage_face hX hAX.1 hXB.1
  have hX'q := himage_face hX' hAX'.1 hX'B.1
  have hqAC : q '' A ⊂ q '' C :=
    hstrict_image hA (Subset.rfl) hAC (hCX.1.trans hXB.1)
  have hqCX : q '' C ⊂ q '' X :=
    hstrict_image hC hAC.1 hCX hXB.1
  have hqXB : q '' X ⊂ Q.toSet := by
    rw [hQT]
    exact hstrict_image hX hAX.1 hXB (Subset.rfl)
  have hqAC' : q '' A ⊂ q '' C' :=
    hstrict_image hA (Subset.rfl) hAC' (hC'X'.1.trans hX'B.1)
  have hqC'X' : q '' C' ⊂ q '' X' :=
    hstrict_image hC' hAC'.1 hC'X' hX'B.1
  have hqX'B : q '' X' ⊂ Q.toSet := by
    rw [hQT]
    exact hstrict_image hX' hAX'.1 hX'B (Subset.rfl)
  have hdAq : faceDim (q '' A) = 0 := by
    rw [hAimage, faceDim_singleton]
  have hdCq_lt := faceDim_lt_of_ssubset Q hAq hCq hqAC
  have hdXq_lt := faceDim_lt_of_ssubset Q hCq hXq hqCX
  have hdQ_lt := faceDim_lt_of_ssubset Q hXq (toSet_isFace Q) hqXB
  have hdQ_le : faceDim Q.toSet ≤ 3 := by
    unfold faceDim
    calc
      Module.finrank ℝ (vectorSpan ℝ Q.toSet) ≤
          Module.finrank ℝ (E 3) := (vectorSpan ℝ Q.toSet).finrank_le
      _ = 3 := by rw [finrank_euclideanSpace]; simp
  have hdQT : faceDim Q.toSet = 3 := by omega
  have hfullQ : Q.IsFullDim := hdQT
  have hdXq : faceDim (q '' X) = 2 := by omega
  have hdC'q_lt := faceDim_lt_of_ssubset Q hAq hC'q hqAC'
  have hdX'q_lt := faceDim_lt_of_ssubset Q hC'q hX'q hqC'X'
  have hdQ'_lt := faceDim_lt_of_ssubset Q hX'q (toSet_isFace Q) hqX'B
  have hdX'q : faceDim (q '' X') = 2 := by omega
  have hqaX : q a ∈ q '' X := ⟨a, hAX.1 haA, rfl⟩
  have hqaX' : q a ∈ q '' X' := ⟨a, hAX'.1 haA, rfl⟩
  have hqaV : q a ∈ Q.vertices := by
    obtain ⟨v, hv⟩ := (facePolytope Q hAq).vertices_nonempty
    have hv' := Finset.mem_filter.mp hv
    have hvA : v ∈ q '' A := hv'.2
    rw [hAimage, Set.mem_singleton_iff] at hvA
    rw [hvA] at hv'
    exact hv'.1
  have hcam := ventaglio_connesso Q hfullQ hqaV
    hXq hdXq hqaX hX'q hdX'q hqaX'
  let lift : Set (E 3) → Set (E n) := fun Y => B ∩ q ⁻¹' Y
  have hlift_face : ∀ {Y : Set (E 3)}, Q.IsFace Y → P.IsFace (lift Y) := by
    intro Y hY
    simpa [U, W, V, q, QB, Q, lift] using
      (relative_lift_isFace P hA hB e hY)
  have hlift_image : ∀ {Y : Set (E 3)}, Y ⊆ Q.toSet → q '' lift Y = Y := by
    intro Y hYQ
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hyY
      have hyQ : y ∈ Q.toSet := hYQ hyY
      rw [hQT] at hyQ
      obtain ⟨x, hxB, rfl⟩ := hyQ
      exact ⟨x, ⟨hxB, hyY⟩, rfl⟩
  have hlift_mono : ∀ {Y Z : Set (E 3)}, Y ⊆ Z → lift Y ⊆ lift Z := by
    intro Y Z hYZ x hx
    exact ⟨hx.1, hYZ hx.2⟩
  have hlift_strict : ∀ {Y Z : Set (E 3)}, Y ⊆ Q.toSet → Z ⊆ Q.toSet →
      Y ⊂ Z → lift Y ⊂ lift Z := by
    intro Y Z hYQ hZQ hYZ
    refine ⟨hlift_mono hYZ.1, ?_⟩
    intro hback
    have himageBack : q '' lift Z ⊆ q '' lift Y := Set.image_mono hback
    rw [hlift_image hZQ, hlift_image hYQ] at himageBack
    exact hYZ.2 himageBack
  have hlift_original : ∀ {D : Set (E n)}, P.IsFace D → A ⊆ D → D ⊆ B →
      lift (q '' D) = D := by
    intro D hD hAD hDB
    apply Set.Subset.antisymm
    · intro x hx
      exact hsaturated hD hAD hDB x hx.1 hx.2
    · intro x hxD
      exact ⟨hDB hxD, ⟨x, hxD, rfl⟩⟩
  have hlift_top : lift Q.toSet = B := by
    apply Set.Subset.antisymm
    · exact fun _ hx => hx.1
    · intro x hxB
      refine ⟨hxB, ?_⟩
      rw [hQT]
      exact ⟨x, hxB, rfl⟩
  let Valid : Set (E 3) → Prop := fun Y =>
    Q.IsFace Y ∧ faceDim Y = 2 ∧ q a ∈ Y
  have hstartValid : Valid (q '' X) := ⟨hXq, hdXq, hqaX⟩
  have hend_valid : ∀ {Y : Set (E 3)},
      Relation.ReflTransGen
        (fun S T => (Q.IsFace T ∧ faceDim T = 2 ∧ q a ∈ T) ∧
          SpigoloComune Q (q a) S T)
        (q '' X) Y → Valid Y := by
    intro Y hpath
    induction hpath with
    | refl => exact hstartValid
    | tail _ hstep _ => exact hstep.1
  let Rel : Set (E n) → Set (E n) → Prop := fun Y Z =>
    P.IsFace Y ∧ P.IsFace Z ∧ A ⊂ Y ∧ A ⊂ Z ∧
      Y ⊂ B ∧ Z ⊂ B ∧
      faceDim Y = faceDim A + 2 ∧ faceDim Z = faceDim A + 2 ∧
      ∃ R : Set (E n), P.IsFace R ∧ A ⊂ R ∧ R ⊂ Y ∧ R ⊂ Z ∧
        faceDim R = faceDim A + 1
  have hlift_step : ∀ {Y Z : Set (E 3)}, Valid Y →
      ((Q.IsFace Z ∧ faceDim Z = 2 ∧ q a ∈ Z) ∧
        SpigoloComune Q (q a) Y Z) →
      Rel (lift Y) (lift Z) := by
    intro Y Z hY hstep
    change Q.IsFace Y ∧ faceDim Y = 2 ∧ q a ∈ Y at hY
    obtain ⟨hZ, hsp⟩ := hstep
    obtain ⟨δ, hδ, hdδ, hqaδ, hδY, hδZ⟩ := hsp
    have hYsub : Y ⊆ Q.toSet := face_subset_toSet Q hY.1
    have hZsub : Z ⊆ Q.toSet := face_subset_toSet Q hZ.1
    have hδsub : δ ⊆ Q.toSet := face_subset_toSet Q hδ
    have hAqsubδ : q '' A ⊆ δ := by
      rw [hAimage]
      exact Set.singleton_subset_iff.mpr hqaδ
    have hAqδ : q '' A ⊂ δ := by
      refine ⟨hAqsubδ, ?_⟩
      intro hback
      have heq : δ = q '' A := Set.Subset.antisymm hback hAqsubδ
      rw [heq, hdAq] at hdδ
      omega
    have hδYstrict : δ ⊂ Y := by
      refine ⟨hδY, ?_⟩
      intro hYδ
      have heq : Y = δ := Set.Subset.antisymm hYδ hδY
      have hdY := hY.2.1
      rw [heq, hdδ] at hdY
      omega
    have hδZstrict : δ ⊂ Z := by
      refine ⟨hδZ, ?_⟩
      intro hZδ
      have heq : Z = δ := Set.Subset.antisymm hZδ hδZ
      have hdZ := hZ.2.1
      rw [heq, hdδ] at hdZ
      omega
    have hYtop : Y ⊂ Q.toSet := by
      refine ⟨hYsub, ?_⟩
      intro htopY
      have heq : Y = Q.toSet := Set.Subset.antisymm hYsub htopY
      have hdY := hY.2.1
      rw [heq, hdQT] at hdY
      omega
    have hZtop : Z ⊂ Q.toSet := by
      refine ⟨hZsub, ?_⟩
      intro htopZ
      have heq : Z = Q.toSet := Set.Subset.antisymm hZsub htopZ
      have hdZ := hZ.2.1
      rw [heq, hdQT] at hdZ
      omega
    have hLAδ : A ⊂ lift δ := by
      rw [← hlift_original hA (Subset.rfl) hAB.1]
      exact hlift_strict (face_subset_toSet Q hAq) hδsub hAqδ
    have hLδY : lift δ ⊂ lift Y :=
      hlift_strict hδsub hYsub hδYstrict
    have hLδZ : lift δ ⊂ lift Z :=
      hlift_strict hδsub hZsub hδZstrict
    have hLYB : lift Y ⊂ B := by
      rw [← hlift_top]
      exact hlift_strict hYsub (Subset.rfl) hYtop
    have hLZB : lift Z ⊂ B := by
      rw [← hlift_top]
      exact hlift_strict hZsub (Subset.rfl) hZtop
    have hLδ := hlift_face hδ
    have hLY := hlift_face hY.1
    have hLZ := hlift_face hZ.1
    have hdAδ := faceDim_lt_of_ssubset P hA hLδ hLAδ
    have hdδY := faceDim_lt_of_ssubset P hLδ hLY hLδY
    have hdYB := faceDim_lt_of_ssubset P hLY hB hLYB
    have hdδZ := faceDim_lt_of_ssubset P hLδ hLZ hLδZ
    have hdZB := faceDim_lt_of_ssubset P hLZ hB hLZB
    have hdLδ : faceDim (lift δ) = faceDim A + 1 := by omega
    have hdLY : faceDim (lift Y) = faceDim A + 2 := by omega
    have hdLZ : faceDim (lift Z) = faceDim A + 2 := by omega
    exact ⟨hLY, hLZ, hLAδ.trans hLδY, hLAδ.trans hLδZ,
      hLYB, hLZB, hdLY, hdLZ,
      lift δ, hLδ, hLAδ, hLδY, hLδZ, hdLδ⟩
  have valid_path : ∀ {Y Z : Set (E 3)}, Valid Y →
      Relation.ReflTransGen
        (fun S T => (Q.IsFace T ∧ faceDim T = 2 ∧ q a ∈ T) ∧
          SpigoloComune Q (q a) S T) Y Z → Valid Z := by
    intro Y Z hY hpath
    induction hpath with
    | refl => exact hY
    | tail _ hstep _ => exact hstep.1
  have transfer_path : ∀ {Y Z : Set (E 3)}, Valid Y →
      (hpath : Relation.ReflTransGen
        (fun S T => (Q.IsFace T ∧ faceDim T = 2 ∧ q a ∈ T) ∧
          SpigoloComune Q (q a) S T) Y Z) →
      Relation.ReflTransGen Rel (lift Y) (lift Z) := by
    intro Y Z hY hpath
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | @tail D E hprev hstep ih =>
        exact Relation.ReflTransGen.tail ih
          (hlift_step (valid_path hY hprev) hstep)
  have hlift_cam : Relation.ReflTransGen Rel (lift (q '' X)) (lift (q '' X')) :=
    transfer_path hstartValid hcam
  change Relation.ReflTransGen Rel X X'
  rw [← hlift_original hX hAX.1 hXB.1,
    ← hlift_original hX' hAX'.1 hX'B.1]
  exact hlift_cam

theorem residuo_rango_tre_connesso (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F G : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (houtside : ∀ k : Fin n, k ≠ i → (k : ℕ) ≠ (i : ℕ) + 1 →
      F.face k = G.face k) :
    Relation.ReflTransGen
      (fun X Y : P.Flag =>
        Y = adjacentFlag P hfull X i ∨
        Y = adjacentFlag P hfull X ⟨(i : ℕ) + 1, hi⟩)
      F G := by
  classical
  let ip : Fin n := ⟨(i : ℕ) + 1, hi⟩
  have hipval : (ip : ℕ) = (i : ℕ) + 1 := rfl
  by_cases hi0 : (i : ℕ) = 0
  · have hiplt : i < ip := by
      rw [Fin.lt_def]
      omega
    obtain ⟨B, hB, hdB, hFipB, hBsub, hDB⟩ :=
      faccia_sopra P hfull F ip
    have hGipB : G.face ip ⊂ B := by
      apply hDB (G.face ip) (G.isFace ip) (G.dim_eq ip)
      intro j hj
      have hji : j ≠ i := ne_of_gt (lt_trans hiplt hj)
      have hjipval : (j : ℕ) ≠ (i : ℕ) + 1 := by
        intro hval
        have hjip : j = ip := Fin.ext hval
        rw [hjip] at hj
        exact (lt_irrefl ip) hj
      rw [houtside j hji hjipval]
      exact G.strict_mono ip j hj
    obtain ⟨v, hFv⟩ := faccia_dim0_singoletto (F.isFace i).2 (by
      rw [F.dim_eq, hi0])
    obtain ⟨w, hGw⟩ := faccia_dim0_singoletto (G.isFace i).2 (by
      rw [G.dim_eq, hi0])
    have hvP : v ∈ P.vertices := by
      obtain ⟨u, hu⟩ := (facePolytope P (F.isFace i)).vertices_nonempty
      have hu' : u ∈ P.vertices ∧ u ∈ F.face i := Finset.mem_filter.mp hu
      have huv : u = v := by
        rw [hFv] at hu'
        exact Set.mem_singleton_iff.mp hu'.2
      exact huv ▸ hu'.1
    have hwP : w ∈ P.vertices := by
      obtain ⟨u, hu⟩ := (facePolytope P (G.isFace i)).vertices_nonempty
      have hu' : u ∈ P.vertices ∧ u ∈ G.face i := Finset.mem_filter.mp hu
      have huw : u = w := by
        rw [hGw] at hu'
        exact Set.mem_singleton_iff.mp hu'.2
      exact huw ▸ hu'.1
    have hvB : v ∈ B := by
      apply hFipB.1
      apply (F.strict_mono i ip hiplt).1
      rw [hFv]
      exact Set.mem_singleton v
    have hwB : w ∈ B := by
      apply hGipB.1
      apply (G.strict_mono i ip hiplt).1
      rw [hGw]
      exact Set.mem_singleton w
    let Q := facePolytope P hB
    have hvQ : v ∈ Q.vertices := by
      change v ∈ P.vertices.filter (· ∈ B)
      exact Finset.mem_filter.mpr ⟨hvP, hvB⟩
    have hwQ : w ∈ Q.vertices := by
      change w ∈ P.vertices.filter (· ∈ B)
      exact Finset.mem_filter.mpr ⟨hwP, hwB⟩
    have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2 := by
      change faceDim Q.toSet = 2
      rw [facePolytope_toSet P hB, hdB]
      omega
    have hverts := poligono_connesso Q hQdim hvQ hwQ
    let VertRel : E n → E n → Prop := fun p q =>
      q ∈ Q.vertices ∧ p ≠ q ∧
        ∃ e : Set (E n), Q.IsFace e ∧ faceDim e = 1 ∧ p ∈ e ∧ q ∈ e
    let MoveRel : P.Flag → P.Flag → Prop := fun H K =>
      K = adjacentFlag P hfull H i ∨ K = adjacentFlag P hfull H ip
    change Relation.ReflTransGen VertRel v w at hverts
    have transfer : ∀ {q : E n}, Relation.ReflTransGen VertRel v q →
        ∃ H : P.Flag, Relation.ReflTransGen MoveRel F H ∧
          H.face i = {q} ∧
          ∀ k : Fin n, k ≠ i → k ≠ ip → H.face k = F.face k := by
      intro q hpath
      induction hpath with
      | refl =>
          exact ⟨F, Relation.ReflTransGen.refl, hFv, fun _ _ _ => rfl⟩
      | @tail p q hprev hstep ih =>
          obtain ⟨H, hFH, hHi, hHout⟩ := ih
          obtain ⟨hqQ, _hpq, e, heQ, hde, hpe, hqe⟩ := hstep
          have heP : P.IsFace e := isFace_of_facePolytope P hB heQ
          have heBsub : e ⊆ B := by
            rw [← facePolytope_toSet P hB]
            exact face_subset_toSet Q heQ
          have heB : e ⊂ B := by
            refine ⟨heBsub, ?_⟩
            intro hBe
            have heq : e = B := Set.Subset.antisymm heBsub hBe
            rw [heq, hdB] at hde
            omega
          have hpE : H.face i ⊂ e := by
            rw [hHi]
            refine (Set.singleton_subset_iff.mpr hpe).ssubset_of_ne ?_
            intro heq
            have hdim := congrArg faceDim heq
            rw [faceDim_singleton, hde] at hdim
            omega
          have hdeip : faceDim e = (ip : ℕ) := by
            rw [hde]
            omega
          have hsottoE : ∀ j : Fin n, j < ip → H.face j ⊂ e := by
            apply catena_sotto P H (i := ip) (im := i) (by omega)
            exact hpE
          have hsopraE : ∀ j : Fin n, ip < j → e ⊂ H.face j := by
            intro j hj
            have hji : j ≠ i := ne_of_gt (lt_trans hiplt hj)
            have hjip : j ≠ ip := ne_of_gt hj
            rw [hHout j hji hjip]
            exact ssubset_of_ssubset_of_subset heB (hBsub j hj)
          let H₁ : P.Flag := sostituisci P H ip e heP hdeip hsottoE hsopraE
          have hHH₁ : Relation.ReflTransGen MoveRel H H₁ := by
            apply residuo_passo_destro P hfull H H₁ i ip
            intro j hjip
            exact sostituisci_face_ne P H ip e heP hdeip hsottoE hsopraE hjip
          have hH₁e : H₁.face ip = e := sostituisci_face_self ..
          have hqQ' := hqQ
          change q ∈ P.vertices.filter (· ∈ B) at hqQ'
          have hqP : q ∈ P.vertices := (Finset.mem_filter.mp hqQ').1
          have hqFace : P.IsFace ({q} : Set (E n)) := vertex_isFace P hqP
          have hqdim : faceDim ({q} : Set (E n)) = (i : ℕ) := by
            rw [faceDim_singleton, hi0]
          have hqE : ({q} : Set (E n)) ⊂ e := by
            refine (Set.singleton_subset_iff.mpr hqe).ssubset_of_ne ?_
            intro heq
            have hdim := congrArg faceDim heq
            rw [faceDim_singleton, hde] at hdim
            omega
          have hsottoQ : ∀ j : Fin n, j < i → H₁.face j ⊂ ({q} : Set (E n)) := by
            intro j hj
            rw [Fin.lt_def] at hj
            omega
          have hsopraQ : ∀ j : Fin n, i < j → ({q} : Set (E n)) ⊂ H₁.face j := by
            apply catena_sopra P H₁ (i := i) (ip := ip) (by omega)
            rw [hH₁e]
            exact hqE
          let H₂ : P.Flag := sostituisci P H₁ i ({q} : Set (E n)) hqFace
            hqdim hsottoQ hsopraQ
          have hH₁H₂ : Relation.ReflTransGen MoveRel H₁ H₂ := by
            apply residuo_passo_sinistro P hfull H₁ H₂ i ip
            intro j hji
            exact sostituisci_face_ne P H₁ i ({q} : Set (E n)) hqFace
              hqdim hsottoQ hsopraQ hji
          refine ⟨H₂, hFH.trans (hHH₁.trans hH₁H₂), ?_, ?_⟩
          · exact sostituisci_face_self ..
          · intro k hki hkip
            rw [sostituisci_face_ne P H₁ i ({q} : Set (E n)) hqFace
                hqdim hsottoQ hsopraQ hki,
              sostituisci_face_ne P H ip e heP hdeip hsottoE hsopraE hkip]
            exact hHout k hki hkip
    obtain ⟨H, hFH, hHi, hHout⟩ := transfer hverts
    have hHG : Relation.ReflTransGen MoveRel H G := by
      apply residuo_passo_destro P hfull H G i ip
      intro k hkip
      by_cases hki : k = i
      · rw [hki, hHi, hGw]
      · rw [hHout k hki hkip]
        exact (houtside k hki (by
          intro hkval
          exact hkip (Fin.ext hkval))).symm
    exact hFH.trans hHG
  · obtain ⟨iv, hiv⟩ : ∃ iv : ℕ, (i : ℕ) = iv + 1 :=
      ⟨(i : ℕ) - 1, by omega⟩
    have hivn : iv < n := by omega
    let im : Fin n := ⟨iv, hivn⟩
    have him : (im : ℕ) + 1 = (i : ℕ) := by
      change iv + 1 = (i : ℕ)
      omega
    have himlt : im < i := by rw [Fin.lt_def]; omega
    have hiplt : i < ip := by rw [Fin.lt_def]; omega
    let A : Set (E n) := F.face im
    obtain ⟨B, hB, hdB, hFipB, hBsub, hDB⟩ :=
      faccia_sopra P hfull F ip
    have hFGim : F.face im = G.face im := by
      apply houtside im
      · intro h
        have := congrArg Fin.val h
        omega
      · omega
    have hGipB : G.face ip ⊂ B := by
      apply hDB (G.face ip) (G.isFace ip) (G.dim_eq ip)
      intro j hj
      have hji : j ≠ i := by
        intro h
        rw [h] at hj
        exact (not_lt_of_ge (le_of_lt hiplt)) hj
      have hjipval : (j : ℕ) ≠ (i : ℕ) + 1 := by
        intro hval
        have hjip : j = ip := Fin.ext hval
        rw [hjip] at hj
        exact (lt_irrefl ip) hj
      rw [houtside j hji hjipval]
      exact G.strict_mono ip j hj
    have hAGip : A ⊂ G.face ip := by
      change F.face im ⊂ G.face ip
      rw [hFGim]
      exact G.strict_mono im ip (lt_trans himlt hiplt)
    have hAFip : A ⊂ F.face ip := F.strict_mono im ip (lt_trans himlt hiplt)
    have hAB : A ⊂ B := hAFip.trans hFipB
    have hrankAB : faceDim B = faceDim A + 3 := by
      rw [hdB, F.dim_eq]
      omega
    have hdFip : faceDim (F.face ip) = faceDim A + 2 := by
      rw [F.dim_eq, F.dim_eq]
      omega
    have hdGip : faceDim (G.face ip) = faceDim A + 2 := by
      rw [G.dim_eq, F.dim_eq]
      omega
    have hfaces := residuo_salto_tre_connesso P (F.isFace im) hB hAB
      hrankAB (F.isFace ip) (G.isFace ip) hAFip hFipB hAGip hGipB
      hdFip hdGip
    let FaceRel : Set (E n) → Set (E n) → Prop := fun Y Z =>
      P.IsFace Y ∧ P.IsFace Z ∧ A ⊂ Y ∧ A ⊂ Z ∧
        Y ⊂ B ∧ Z ⊂ B ∧
        faceDim Y = faceDim A + 2 ∧ faceDim Z = faceDim A + 2 ∧
        ∃ R : Set (E n), P.IsFace R ∧ A ⊂ R ∧ R ⊂ Y ∧ R ⊂ Z ∧
          faceDim R = faceDim A + 1
    let MoveRel : P.Flag → P.Flag → Prop := fun H K =>
      K = adjacentFlag P hfull H i ∨ K = adjacentFlag P hfull H ip
    change Relation.ReflTransGen FaceRel (F.face ip) (G.face ip) at hfaces
    have transfer : ∀ {Y : Set (E n)},
        Relation.ReflTransGen FaceRel (F.face ip) Y →
        ∃ H : P.Flag, Relation.ReflTransGen MoveRel F H ∧
          H.face ip = Y ∧
          ∀ k : Fin n, k ≠ i → k ≠ ip → H.face k = F.face k := by
      intro Y hpath
      induction hpath with
      | refl =>
          exact ⟨F, Relation.ReflTransGen.refl, rfl, fun _ _ _ => rfl⟩
      | @tail Y Z hprev hstep ih =>
          obtain ⟨H, hFH, hHip, hHout⟩ := ih
          obtain ⟨_hY, hZ, _hAY, _hAZ, _hYB, hZB, _hdY, hdZ,
            R, hR, hAR, hRY, hRZ, hdR⟩ := hstep
          have hHim : H.face im = A := by
            rw [hHout im (ne_of_lt himlt) (by
              intro h
              have := congrArg Fin.val h
              omega)]
          have hdRi : faceDim R = (i : ℕ) := by
            rw [hdR, F.dim_eq]
            omega
          have hsottoR : ∀ j : Fin n, j < i → H.face j ⊂ R := by
            apply catena_sotto P H him
            rw [hHim]
            exact hAR
          have hsopraR : ∀ j : Fin n, i < j → R ⊂ H.face j := by
            apply catena_sopra P H (ip := ip) (by omega)
            rw [hHip]
            exact hRY
          let H₁ : P.Flag := sostituisci P H i R hR hdRi hsottoR hsopraR
          have hHH₁ : Relation.ReflTransGen MoveRel H H₁ := by
            apply residuo_passo_sinistro P hfull H H₁ i ip
            intro j hji
            exact sostituisci_face_ne P H i R hR hdRi hsottoR hsopraR hji
          have hH₁R : H₁.face i = R := sostituisci_face_self ..
          have hdZi : faceDim Z = (ip : ℕ) := by
            rw [hdZ, F.dim_eq]
            omega
          have hsottoZ : ∀ j : Fin n, j < ip → H₁.face j ⊂ Z := by
            apply catena_sotto P H₁ (im := i) (by omega)
            rw [hH₁R]
            exact hRZ
          have hsopraZ : ∀ j : Fin n, ip < j → Z ⊂ H₁.face j := by
            intro j hj
            have hji : j ≠ i := ne_of_gt (lt_trans hiplt hj)
            have hjip : j ≠ ip := ne_of_gt hj
            rw [sostituisci_face_ne P H i R hR hdRi hsottoR hsopraR hji,
              hHout j hji hjip]
            exact ssubset_of_ssubset_of_subset hZB (hBsub j hj)
          let H₂ : P.Flag := sostituisci P H₁ ip Z hZ hdZi hsottoZ hsopraZ
          have hH₁H₂ : Relation.ReflTransGen MoveRel H₁ H₂ := by
            apply residuo_passo_destro P hfull H₁ H₂ i ip
            intro j hjip
            exact sostituisci_face_ne P H₁ ip Z hZ hdZi hsottoZ hsopraZ hjip
          refine ⟨H₂, hFH.trans (hHH₁.trans hH₁H₂), ?_, ?_⟩
          · exact sostituisci_face_self ..
          · intro k hki hkip
            rw [sostituisci_face_ne P H₁ ip Z hZ hdZi hsottoZ hsopraZ hkip,
              sostituisci_face_ne P H i R hR hdRi hsottoR hsopraR hki]
            exact hHout k hki hkip
    obtain ⟨H, hFH, hHip, hHout⟩ := transfer hfaces
    have hHG : Relation.ReflTransGen MoveRel H G := by
      apply residuo_passo_sinistro P hfull H G i ip
      intro k hki
      by_cases hkip : k = ip
      · rw [hkip, hHip]
      · rw [hHout k hki hkip]
        exact (houtside k hki (by
          intro hkval
          exact hkip (Fin.ext hkval))).symm
    exact hFH.trans hHG

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart10

section BundlePart11
/- Source: Cubical/Polytope/ConnettivitaRidgeTre.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ConnettivitaRidgeTre.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/





/-!
CONNETTIVITÀ DEL RIDGE-GRAPH — DIMENSIONE INTRINSECA TRE (20 lug 2026).

Balinski-light generale collega un vertice di una faccetta iniziale a un
vertice della faccetta finale.  Ogni spigolo della camminata si estende a
una faccetta.  Attorno al vertice corrente, la connessione fra la
faccetta corrente e quella scelta sopra lo spigolo è esattamente il
residuo di salto tre già provato in `FaccetteConnesse`.

Il teorema vale in `E n` arbitrario: conta solo `faceDim B = 3`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il caso intrinseco tridimensionale del muro locale. -/
theorem ridgeConnected_in_faceDim_three (P : ConvexPolytope n)
    (B : Set (E n)) (hB : P.IsFace B) (hdB : faceDim B = 3) :
    ∀ (A A' : Set (E n)), P.IsFace A → P.IsFace A' →
      A ⊂ B → A' ⊂ B →
      faceDim A + 1 = faceDim B → faceDim A' + 1 = faceDim B →
      Relation.ReflTransGen
        (fun X Y : Set (E n) =>
          P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
            faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
            ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
              faceDim R + 2 = faceDim B)
        A A' := by
  classical
  intro A A' hA hA' hAB hA'B hdA hdA'
  let Q : ConvexPolytope n := facePolytope P hB
  have hQT : Q.toSet = B := facePolytope_toSet P hB
  have hQdim : faceDim Q.toSet = 3 := by rw [hQT, hdB]
  have hAQ : Q.IsFace A := facePolytope_isFace_of P hB hA hAB.1
  have hA'Q : Q.IsFace A' := facePolytope_isFace_of P hB hA' hA'B.1
  have hdAtwo : faceDim A = 2 := by omega
  have hdA'two : faceDim A' = 2 := by omega
  obtain ⟨x, hx⟩ := (facePolytope Q hAQ).vertices_nonempty
  obtain ⟨x', hx'⟩ := (facePolytope Q hA'Q).vertices_nonempty
  have hxQ : x ∈ Q.vertices := (Finset.mem_filter.mp hx).1
  have hxA : x ∈ A := (Finset.mem_filter.mp hx).2
  have hx'Q : x' ∈ Q.vertices := (Finset.mem_filter.mp hx').1
  have hx'A' : x' ∈ A' := (Finset.mem_filter.mp hx').2
  let RidgeRel : Set (E n) → Set (E n) → Prop := fun X Y =>
    P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
      faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
      ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
        faceDim R + 2 = faceDim B
  have face_strict_B : ∀ {X : Set (E n)}, Q.IsFace X → faceDim X = 2 →
      P.IsFace X ∧ X ⊂ B := by
    intro X hX hdX
    have hXP : P.IsFace X := isFace_of_facePolytope P hB hX
    have hsub : X ⊆ B := by
      rw [← hQT]
      exact face_subset_toSet Q hX
    refine ⟨hXP, hsub.ssubset_of_ne ?_⟩
    intro heq
    have := congrArg faceDim heq
    rw [hdX, hdB] at this
    omega
  have star_path : ∀ {v : E n} {X Y : Set (E n)},
      v ∈ Q.vertices → Q.IsFace X → faceDim X = 2 → v ∈ X →
      Q.IsFace Y → faceDim Y = 2 → v ∈ Y →
      Relation.ReflTransGen RidgeRel X Y := by
    intro v X Y hvQ hX hdX hvX hY hdY hvY
    have hvFace : Q.IsFace ({v} : Set (E n)) := vertex_isFace Q hvQ
    have hvXstrict : ({v} : Set (E n)) ⊂ X := by
      refine (Set.singleton_subset_iff.mpr hvX).ssubset_of_ne ?_
      intro heq
      have := congrArg faceDim heq
      rw [faceDim_singleton, hdX] at this
      omega
    have hvYstrict : ({v} : Set (E n)) ⊂ Y := by
      refine (Set.singleton_subset_iff.mpr hvY).ssubset_of_ne ?_
      intro heq
      have := congrArg faceDim heq
      rw [faceDim_singleton, hdY] at this
      omega
    have hXtop : X ⊂ Q.toSet := by
      refine (face_subset_toSet Q hX).ssubset_of_ne ?_
      intro heq
      have := congrArg faceDim heq
      rw [hdX, hQdim] at this
      omega
    have hYtop : Y ⊂ Q.toSet := by
      refine (face_subset_toSet Q hY).ssubset_of_ne ?_
      intro heq
      have := congrArg faceDim heq
      rw [hdY, hQdim] at this
      omega
    have hres := residuo_salto_tre_connesso Q hvFace (toSet_isFace Q)
      (hvXstrict.trans hXtop) (by rw [hQdim, faceDim_singleton])
      hX hY hvXstrict hXtop hvYstrict hYtop
      (by rw [faceDim_singleton, hdX])
      (by rw [faceDim_singleton, hdY])
    refine Relation.ReflTransGen.mono ?_ _ _ hres
    rintro S T ⟨hS, hT, _hvS, _hvT, hStop, hTtop,
      hdS, hdT, R, hR, _hvR, hRS, hRT, hdR⟩
    have hdStwo : faceDim S = 2 := by
      simpa only [faceDim_singleton, zero_add] using hdS
    have hdTtwo : faceDim T = 2 := by
      simpa only [faceDim_singleton, zero_add] using hdT
    have hdRone : faceDim R = 1 := by
      simpa only [faceDim_singleton, zero_add] using hdR
    obtain ⟨hSP, hSB⟩ := face_strict_B hS hdStwo
    obtain ⟨hTP, hTB⟩ := face_strict_B hT hdTtwo
    have hRP : P.IsFace R := isFace_of_facePolytope P hB hR
    exact ⟨hSP, hTP, hSB, hTB, by omega, by omega,
      R, hRP, hRS, hRT, by
        rw [hdRone, hdB]⟩
  have hverts : Relation.ReflTransGen (GeneralVertexStep Q) x x' :=
    balinski_light_general Q hxQ hx'Q
  have transfer : ∀ {q : E n}, Relation.ReflTransGen (GeneralVertexStep Q) x q →
      ∃ X : Set (E n), Relation.ReflTransGen RidgeRel A X ∧
        Q.IsFace X ∧ faceDim X = 2 ∧ q ∈ Q.vertices ∧ q ∈ X := by
    intro q hpath
    induction hpath with
    | refl => exact ⟨A, Relation.ReflTransGen.refl, hAQ, hdAtwo, hxQ, hxA⟩
    | @tail p q hprev hstep ih =>
        obtain ⟨X, hAX, hX, hdX, hpQ, hpX⟩ := ih
        obtain ⟨hqQ, _hpq, e, he, hde, hpe, hqe⟩ := hstep
        have heTop : e ⊂ Q.toSet := by
          refine (face_subset_toSet Q he).ssubset_of_ne ?_
          intro heq
          have := congrArg faceDim heq
          rw [hde, hQdim] at this
          omega
        obtain ⟨D, hD, heD, hDtop, hdD⟩ := faccia_intermedia Q he
          (toSet_isFace Q) heTop (by rw [hQdim, hde])
        have hdDtwo : faceDim D = 2 := by omega
        have hpD : p ∈ D := heD.1 hpe
        have hqD : q ∈ D := heD.1 hqe
        have hXD := star_path hpQ hX hdX hpX hD hdDtwo hpD
        exact ⟨D, hAX.trans hXD, hD, hdDtwo, hqQ, hqD⟩
  obtain ⟨X, hAX, hX, hdX, hx'Q', hx'X⟩ := transfer hverts
  exact hAX.trans (star_path hx'Q' hX hdX hx'X hA'Q hdA'two hx'A')

/-- Tutto il muro fino alla dimensione intrinseca tre inclusa. -/
theorem ridgeConnected_in_faceDim_le_three (P : ConvexPolytope n)
    (B : Set (E n)) (hB : P.IsFace B) (hdlo : 2 ≤ faceDim B)
    (hdhi : faceDim B ≤ 3) :
    ∀ (A A' : Set (E n)), P.IsFace A → P.IsFace A' →
      A ⊂ B → A' ⊂ B →
      faceDim A + 1 = faceDim B → faceDim A' + 1 = faceDim B →
      Relation.ReflTransGen
        (fun X Y : Set (E n) =>
          P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
            faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
            ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
              faceDim R + 2 = faceDim B)
        A A' := by
  have hdim : faceDim B = 2 ∨ faceDim B = 3 := by omega
  rcases hdim with hdim | hdim
  · exact ridgeConnected_in_faceDim_two P B hB hdim
  · exact ridgeConnected_in_faceDim_three P B hB hdim

/-- Se il politopo ha dimensione intrinseca al più tre, l'intero
`RidgeConnectedAboveOne` è chiuso, senza piena dimensionalità. -/
theorem ridgeConnectedAboveOne_of_dim_le_three (P : ConvexPolytope n)
    (hdP : faceDim P.toSet ≤ 3) : RidgeConnectedAboveOne P := by
  intro B hB hdB
  have hdBhi : faceDim B ≤ 3 := by
    have hspan : vectorSpan ℝ B ≤ vectorSpan ℝ P.toSet :=
      vectorSpan_mono ℝ (face_subset_toSet P hB)
    have hdim := Submodule.finrank_mono hspan
    exact hdim.trans hdP
  exact ridgeConnected_in_faceDim_le_three P B hB hdB hdBhi

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart11

section BundlePart12
/- Source: Cubical/Polytope/ConnettivitaRidgeRiduzione.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ConnettivitaRidgeRiduzione.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/





/-!
RIDUZIONE ESATTA DEL MURO DEL RIDGE-GRAPH (20 lug 2026).

La base intrinseca 2 e il caso intrinseco 3 sono chiusi nei moduli
precedenti.  In rango superiore, Balinski-light riduce la connettività
globale delle faccette alla connettività locale delle faccette incidenti
a uno stesso vertice.  Ogni spigolo della camminata si estende a una
faccetta mediante massimalità nella famiglia finita delle facce proprie.

La definizione `VertexStarRidgeConnectedAboveThree` è quindi il
sotto-kill-gate preciso rimasto: è la connettività del grafo delle
faccette nello star di un vertice, per una faccia di dimensione almeno
quattro.  Il teorema finale di questo file dimostra, senza assiomi
aggiuntivi, che tale enunciato implica esattamente
`RidgeConnectedAboveOne`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il passo del ridge-graph delle faccette proprie di `B`. -/
def RidgeStepIn (P : ConvexPolytope n) (B : Set (E n))
    (X Y : Set (E n)) : Prop :=
  P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
    faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
    ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
      faceDim R + 2 = faceDim B

/-- Sotto-kill-gate superiore: due faccette di `B` incidenti allo stesso
vertice sono connesse per ridge, restando dentro `B`.  La soglia `4`
esclude esattamente i ranghi già chiusi in
`ConnettivitaRidgeBase` e `ConnettivitaRidgeTre`. -/
def VertexStarRidgeConnectedAboveThree (P : ConvexPolytope n) : Prop :=
  ∀ (B : Set (E n)) (hB : P.IsFace B), 4 ≤ faceDim B →
    ∀ v : E n, v ∈ (facePolytope P hB).vertices →
      ∀ (X Y : Set (E n)), P.IsFace X → P.IsFace Y →
        X ⊂ B → Y ⊂ B →
        faceDim X + 1 = faceDim B →
        faceDim Y + 1 = faceDim B →
        v ∈ X → v ∈ Y →
        Relation.ReflTransGen (RidgeStepIn P B) X Y

/-- Ogni faccia propria è contenuta in una faccetta.  Non si assume
piena dimensionalità: la dimensione è quella intrinseca di `Q`.

La prova sceglie una faccia massimale fra le facce proprie che contengono
`e`.  Se il salto alla faccia totale fosse almeno due,
`interpolazione` produrrebbe una faccia propria strettamente maggiore,
contraddicendo la massimalità. -/
theorem facet_above_proper_face (Q : ConvexPolytope n)
    {e : Set (E n)} (he : Q.IsFace e) (heTop : e ⊂ Q.toSet) :
    ∃ D : Set (E n), Q.IsFace D ∧ e ⊆ D ∧ D ⊂ Q.toSet ∧
      faceDim D + 1 = faceDim Q.toSet := by
  classical
  let S : Set (Set (E n)) :=
    {D | Q.IsFace D ∧ e ⊆ D ∧ D ≠ Q.toSet}
  have hSfinite : S.Finite := by
    apply (facce_finite Q).subset
    intro D hD
    exact hD.1
  have heS : e ∈ S := ⟨he, Subset.rfl, heTop.ne⟩
  obtain ⟨D, heD, hDmax⟩ := hSfinite.exists_le_maximal heS
  have hDS : D ∈ S := hDmax.1
  have hDTop : D ⊂ Q.toSet :=
    (face_subset_toSet Q hDS.1).ssubset_of_ne hDS.2.2
  have hdimlt := faceDim_lt_of_ssubset Q hDS.1 (toSet_isFace Q) hDTop
  have hfacet : faceDim D + 1 = faceDim Q.toSet := by
    by_contra hne
    have hgap : faceDim D + 2 ≤
        Module.finrank ℝ (vectorSpan ℝ Q.toSet) := by
      change faceDim D + 2 ≤ faceDim Q.toSet
      omega
    obtain ⟨D', hD', hDD', hD'ne⟩ := interpolazione Q hDS.1 hgap
    have hD'S : D' ∈ S :=
      ⟨hD', hDS.2.1.trans hDD'.1, hD'ne⟩
    have hD'D : D' ⊆ D := hDmax.2 hD'S hDD'.1
    exact hDD'.ne (Set.Subset.antisymm hDD'.1 hD'D)
  exact ⟨D, hDS.1, heD, hDTop, hfacet⟩

/-- **RIDUZIONE COMPLETA**: Balinski-light più la connettività degli
star dei vertici in dimensione almeno quattro chiudono tutto
`RidgeConnectedAboveOne`. -/
theorem ridgeConnectedAboveOne_of_vertexStarAboveThree
    (P : ConvexPolytope n)
    (hstar : VertexStarRidgeConnectedAboveThree P) :
    RidgeConnectedAboveOne P := by
  classical
  intro B hB hdB A A' hA hA' hAB hA'B hdA hdA'
  by_cases hdhi : faceDim B ≤ 3
  · exact ridgeConnected_in_faceDim_le_three P B hB hdB hdhi
      A A' hA hA' hAB hA'B hdA hdA'
  · have hdBfour : 4 ≤ faceDim B := by omega
    let Q : ConvexPolytope n := facePolytope P hB
    have hQT : Q.toSet = B := facePolytope_toSet P hB
    have hQdim : faceDim Q.toSet = faceDim B := by rw [hQT]
    have hAQ : Q.IsFace A := facePolytope_isFace_of P hB hA hAB.1
    have hA'Q : Q.IsFace A' := facePolytope_isFace_of P hB hA' hA'B.1
    obtain ⟨x, hx⟩ := (facePolytope Q hAQ).vertices_nonempty
    obtain ⟨x', hx'⟩ := (facePolytope Q hA'Q).vertices_nonempty
    have hxQ : x ∈ Q.vertices := (Finset.mem_filter.mp hx).1
    have hxA : x ∈ A := (Finset.mem_filter.mp hx).2
    have hx'Q : x' ∈ Q.vertices := (Finset.mem_filter.mp hx').1
    have hx'A' : x' ∈ A' := (Finset.mem_filter.mp hx').2
    have hverts : Relation.ReflTransGen (GeneralVertexStep Q) x x' :=
      balinski_light_general Q hxQ hx'Q
    change Relation.ReflTransGen (RidgeStepIn P B) A A'
    have transfer : ∀ {q : E n},
        Relation.ReflTransGen (GeneralVertexStep Q) x q →
        ∃ X : Set (E n),
          Relation.ReflTransGen (RidgeStepIn P B) A X ∧
          P.IsFace X ∧ X ⊂ B ∧
          faceDim X + 1 = faceDim B ∧
          q ∈ Q.vertices ∧ q ∈ X := by
      intro q hpath
      induction hpath with
      | refl =>
          exact ⟨A, Relation.ReflTransGen.refl, hA, hAB, hdA, hxQ, hxA⟩
      | @tail p q hprev hstep ih =>
          obtain ⟨X, hAX, hXP, hXB, hdX, hpQ, hpX⟩ := ih
          obtain ⟨hqQ, _hpq, e, he, hde, hpe, hqe⟩ := hstep
          have heTop : e ⊂ Q.toSet := by
            refine (face_subset_toSet Q he).ssubset_of_ne ?_
            intro heq
            have hdim := congrArg faceDim heq
            rw [hde, hQdim] at hdim
            omega
          obtain ⟨D, hDQ, heD, hDTop, hdD⟩ :=
            facet_above_proper_face Q he heTop
          have hDP : P.IsFace D := isFace_of_facePolytope P hB hDQ
          have hDB : D ⊂ B := by simpa only [hQT] using hDTop
          have hdDB : faceDim D + 1 = faceDim B := by
            rw [← hQdim]
            exact hdD
          have hpD : p ∈ D := heD hpe
          have hqD : q ∈ D := heD hqe
          have hXD := hstar B hB hdBfour p hpQ X D hXP hDP
            hXB hDB hdX hdDB hpX hpD
          exact ⟨D, hAX.trans hXD, hDP, hDB, hdDB, hqQ, hqD⟩
    obtain ⟨X, hAX, hXP, hXB, hdX, hx'Q', hx'X⟩ := transfer hverts
    exact hAX.trans
      (hstar B hB hdBfour x' hx'Q' X A' hXP hA' hXB hA'B
        hdX hdA' hx'X hx'A')

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart12

section BundlePart13
/- Source: Cubical/Polytope/VertexFigureRidge.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.VertexFigureRidge.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/



/-!
FIGURA AL VERTICE: INTERFACCIA ESATTA DEL SOTTO-KILL-GATE (21 lug 2026).

Questo file non postula assiomi e non costruisce surrettiziamente una
proiezione del residuo.  Isola i dati combinatori esatti di una vera figura
al vertice: le facce non puntuali di `B` che contengono `v` sono equivalenti,
conservando l'ordine, alle facce di un politopo di dimensione inferiore; la
dimensione scende esattamente di uno.

Da questi dati si dimostra:

* il trasporto di un cammino di ridge della figura in un cammino nello star;
* per induzione forte sulla dimensione intrinseca, `RidgeConnectedAboveOne`
  per ogni politopo;
* quindi il target `VertexStarRidgeConnectedAboveThree`.

L'unico enunciato geometrico ancora richiesto è
`VertexFigureGaloisExists`: l'esistenza di questi dati per ogni faccia e
vertice.  Lasciarlo come ipotesi esplicita rende il confine del lavoro
kernel-certificato controllabile con `#print axioms`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una faccia di dimensione positiva di `P`, contenuta in `B` e incidente
al vertice marcato `v`.  Sono precisamente le facce che devono sopravvivere
nella figura al vertice; la faccia puntuale `{v}` corrisponderebbe alla
faccia vuota, esclusa dalla nozione `IsFace` del benchmark. -/
structure PositiveVertexStarFace (P : ConvexPolytope n)
    (B : Set (E n)) (v : E n) where
  carrier : Set (E n)
  isFace : P.IsFace carrier
  subset_base : carrier ⊆ B
  mem_vertex : v ∈ carrier
  dim_pos : 1 ≤ faceDim carrier

/-- Una faccia non vuota ordinaria di un politopo. -/
structure PolytopeFace (P : ConvexPolytope n) where
  carrier : Set (E n)
  isFace : P.IsFace carrier

@[ext]
theorem PositiveVertexStarFace.ext
    {P : ConvexPolytope n} {B : Set (E n)} {v : E n}
    {F G : PositiveVertexStarFace P B v} (h : F.carrier = G.carrier) :
    F = G := by
  cases F
  cases G
  cases h
  rfl

@[ext]
theorem PolytopeFace.ext {P : ConvexPolytope n}
    {F G : PolytopeFace P} (h : F.carrier = G.carrier) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- I dati di Galois necessari e sufficienti della figura al vertice.

`faceEquiv` identifica le facce positive dello star con tutte le facce della
figura. `map_subset_iff` dice che è una equivalenza d'ordine, mentre
`map_dim` registra lo shift di dimensione. -/
structure VertexFigureGaloisData (P : ConvexPolytope n)
    (B : Set (E n)) (v : E n) where
  figure : ConvexPolytope n
  faceEquiv : PositiveVertexStarFace P B v ≃ PolytopeFace figure
  map_subset_iff : ∀ F G,
    F.carrier ⊆ G.carrier ↔
      (faceEquiv F).carrier ⊆ (faceEquiv G).carrier
  map_dim : ∀ F,
    faceDim (faceEquiv F).carrier + 1 = faceDim F.carrier

/-- Il solo gate geometrico rimasto: ogni intervallo di facce sopra un
vertice ammette una vera figura al vertice con la corrispondenza di Galois e
lo shift dimensionale. -/
def VertexFigureGaloisExists : Prop :=
  ∀ {n : ℕ} (P : ConvexPolytope n) (B : Set (E n))
    (hB : P.IsFace B) (v : E n),
    v ∈ (facePolytope P hB).vertices →
    1 ≤ faceDim B →
    Nonempty (VertexFigureGaloisData P B v)

namespace VertexFigureGaloisData

variable {P : ConvexPolytope n} {B : Set (E n)} {v : E n}

/-- L'equivalenza d'ordine preserva e riflette le inclusioni strette. -/
theorem map_ssubset_iff (D : VertexFigureGaloisData P B v)
    (F G : PositiveVertexStarFace P B v) :
    F.carrier ⊂ G.carrier ↔
      (D.faceEquiv F).carrier ⊂ (D.faceEquiv G).carrier := by
  constructor
  · intro hFG
    refine ⟨(D.map_subset_iff F G).mp hFG.1, ?_⟩
    intro hback
    have hGF : G.carrier ⊆ F.carrier :=
      (D.map_subset_iff G F).mpr hback
    exact hFG.2 hGF
  · intro hFG
    refine ⟨(D.map_subset_iff F G).mpr hFG.1, ?_⟩
    intro hback
    have hGF : (D.faceEquiv G).carrier ⊆
        (D.faceEquiv F).carrier :=
      (D.map_subset_iff G F).mp hback
    exact hFG.2 hGF

/-- La faccia superiore dello star corrisponde al corpo intero della figura. -/
theorem map_top_eq_toSet (D : VertexFigureGaloisData P B v)
    (hB : P.IsFace B) (hvB : v ∈ B) (hdB : 1 ≤ faceDim B) :
    (D.faceEquiv
      { carrier := B
        isFace := hB
        subset_base := Subset.rfl
        mem_vertex := hvB
        dim_pos := hdB }).carrier = D.figure.toSet := by
  let T : PositiveVertexStarFace P B v :=
    { carrier := B
      isFace := hB
      subset_base := Subset.rfl
      mem_vertex := hvB
      dim_pos := hdB }
  let U : PolytopeFace D.figure :=
    { carrier := D.figure.toSet
      isFace := toSet_isFace D.figure }
  have hUT : (D.faceEquiv.symm U).carrier ⊆ T.carrier :=
    (D.faceEquiv.symm U).subset_base
  have himage : U.carrier ⊆ (D.faceEquiv T).carrier := by
    have h := (D.map_subset_iff (D.faceEquiv.symm U) T).mp hUT
    simpa only [D.faceEquiv.apply_symm_apply] using h
  apply Set.Subset.antisymm
  · exact face_subset_toSet D.figure (D.faceEquiv T).isFace
  · exact himage

/-- La dimensione intrinseca della figura è esattamente una in meno della
dimensione della faccia di base. -/
theorem figure_dim_add_one (D : VertexFigureGaloisData P B v)
    (hB : P.IsFace B) (hvB : v ∈ B) (hdB : 1 ≤ faceDim B) :
    faceDim D.figure.toSet + 1 = faceDim B := by
  let T : PositiveVertexStarFace P B v :=
    { carrier := B
      isFace := hB
      subset_base := Subset.rfl
      mem_vertex := hvB
      dim_pos := hdB }
  have hdim := D.map_dim T
  have htop := D.map_top_eq_toSet hB hvB hdB
  simpa only [T, htop] using hdim

/-- Trasporto fondamentale: la connettività ridge della figura al vertice
implica la connettività delle faccette dello star corrispondente. -/
theorem star_path_of_ridgeConnected
    (D : VertexFigureGaloisData P B v)
    (hB : P.IsFace B) (hdB : 4 ≤ faceDim B) (hvB : v ∈ B)
    (hridge : RidgeConnectedAboveOne D.figure)
    (X Y : Set (E n)) (hX : P.IsFace X) (hY : P.IsFace Y)
    (hXB : X ⊂ B) (hYB : Y ⊂ B)
    (hdX : faceDim X + 1 = faceDim B)
    (hdY : faceDim Y + 1 = faceDim B)
    (hvX : v ∈ X) (hvY : v ∈ Y) :
    Relation.ReflTransGen (RidgeStepIn P B) X Y := by
  classical
  have hdXpos : 1 ≤ faceDim X := by omega
  have hdYpos : 1 ≤ faceDim Y := by omega
  let SX : PositiveVertexStarFace P B v :=
    { carrier := X
      isFace := hX
      subset_base := hXB.1
      mem_vertex := hvX
      dim_pos := hdXpos }
  let SY : PositiveVertexStarFace P B v :=
    { carrier := Y
      isFace := hY
      subset_base := hYB.1
      mem_vertex := hvY
      dim_pos := hdYpos }
  let FX : PolytopeFace D.figure := D.faceEquiv SX
  let FY : PolytopeFace D.figure := D.faceEquiv SY
  have hdimFigure : faceDim D.figure.toSet + 1 = faceDim B :=
    D.figure_dim_add_one hB hvB (by omega)
  have hFXsub : FX.carrier ⊆ D.figure.toSet :=
    face_subset_toSet D.figure FX.isFace
  have hFYsub : FY.carrier ⊆ D.figure.toSet :=
    face_subset_toSet D.figure FY.isFace
  have hFXproper : FX.carrier ⊂ D.figure.toSet := by
    refine hFXsub.ssubset_of_ne ?_
    intro heq
    have hdim := congrArg faceDim heq
    have hshift := D.map_dim SX
    change faceDim FX.carrier + 1 = faceDim X at hshift
    omega
  have hFYproper : FY.carrier ⊂ D.figure.toSet := by
    refine hFYsub.ssubset_of_ne ?_
    intro heq
    have hdim := congrArg faceDim heq
    have hshift := D.map_dim SY
    change faceDim FY.carrier + 1 = faceDim Y at hshift
    omega
  have hdFX : faceDim FX.carrier + 1 = faceDim D.figure.toSet := by
    have hshift := D.map_dim SX
    change faceDim FX.carrier + 1 = faceDim X at hshift
    omega
  have hdFY : faceDim FY.carrier + 1 = faceDim D.figure.toSet := by
    have hshift := D.map_dim SY
    change faceDim FY.carrier + 1 = faceDim Y at hshift
    omega
  have hpath := hridge D.figure.toSet (toSet_isFace D.figure)
    (by omega) FX.carrier FY.carrier FX.isFace FY.isFace
    hFXproper hFYproper hdFX hdFY
  let lift : Set (E n) → PositiveVertexStarFace P B v := fun Z =>
    if hZ : D.figure.IsFace Z then
      D.faceEquiv.symm { carrier := Z, isFace := hZ }
    else SX
  have lift_of_face : ∀ (Z : Set (E n)) (hZ : D.figure.IsFace Z),
      lift Z = D.faceEquiv.symm { carrier := Z, isFace := hZ } := by
    intro Z hZ
    simp only [lift, dif_pos hZ]
  let FigureRidgeStep : Set (E n) → Set (E n) → Prop :=
    fun S T =>
      D.figure.IsFace S ∧ D.figure.IsFace T ∧
        S ⊂ D.figure.toSet ∧ T ⊂ D.figure.toSet ∧
        faceDim S + 1 = faceDim D.figure.toSet ∧
        faceDim T + 1 = faceDim D.figure.toSet ∧
        ∃ R : Set (E n), D.figure.IsFace R ∧ R ⊂ S ∧ R ⊂ T ∧
          faceDim R + 2 = faceDim D.figure.toSet
  change Relation.ReflTransGen FigureRidgeStep FX.carrier FY.carrier at hpath
  have lift_step : ∀ {S T : Set (E n)}, FigureRidgeStep S T →
      RidgeStepIn P B (lift S).carrier (lift T).carrier := by
    intro S T hST
    obtain ⟨hS, hT, _hStop, _hTtop, hdS, hdT,
      R, hR, hRS, hRT, hdR⟩ := hST
    let FS : PolytopeFace D.figure := { carrier := S, isFace := hS }
    let FT : PolytopeFace D.figure := { carrier := T, isFace := hT }
    let FR : PolytopeFace D.figure := { carrier := R, isFace := hR }
    let LS : PositiveVertexStarFace P B v := D.faceEquiv.symm FS
    let LT : PositiveVertexStarFace P B v := D.faceEquiv.symm FT
    let LR : PositiveVertexStarFace P B v := D.faceEquiv.symm FR
    have hliftS : lift S = LS := by
      rw [lift_of_face S hS]
    have hliftT : lift T = LT := by
      rw [lift_of_face T hT]
    rw [hliftS, hliftT]
    have hLRLS : LR.carrier ⊂ LS.carrier := by
      apply (D.map_ssubset_iff LR LS).mpr
      simpa only [LS, LR, D.faceEquiv.apply_symm_apply] using hRS
    have hLRLT : LR.carrier ⊂ LT.carrier := by
      apply (D.map_ssubset_iff LR LT).mpr
      simpa only [LT, LR, D.faceEquiv.apply_symm_apply] using hRT
    have hdimLS := D.map_dim LS
    have hdimLT := D.map_dim LT
    have hdimLR := D.map_dim LR
    have hLSimage : (D.faceEquiv LS).carrier = S := by
      change (D.faceEquiv (D.faceEquiv.symm FS)).carrier = S
      rw [D.faceEquiv.apply_symm_apply]
    have hLTimage : (D.faceEquiv LT).carrier = T := by
      change (D.faceEquiv (D.faceEquiv.symm FT)).carrier = T
      rw [D.faceEquiv.apply_symm_apply]
    have hLRimage : (D.faceEquiv LR).carrier = R := by
      change (D.faceEquiv (D.faceEquiv.symm FR)).carrier = R
      rw [D.faceEquiv.apply_symm_apply]
    let Top : PositiveVertexStarFace P B v :=
      { carrier := B
        isFace := hB
        subset_base := Subset.rfl
        mem_vertex := hvB
        dim_pos := by omega }
    have hTopimage : (D.faceEquiv Top).carrier = D.figure.toSet := by
      change (D.faceEquiv
        { carrier := B
          isFace := hB
          subset_base := Subset.rfl
          mem_vertex := hvB
          dim_pos := (by omega) }).carrier = D.figure.toSet
      exact D.map_top_eq_toSet hB hvB (by omega)
    have hLStop : LS.carrier ⊂ B := by
      apply (D.map_ssubset_iff LS Top).mpr
      rw [hLSimage, hTopimage]
      exact _hStop
    have hLTtop : LT.carrier ⊂ B := by
      apply (D.map_ssubset_iff LT Top).mpr
      rw [hLTimage, hTopimage]
      exact _hTtop
    rw [hLSimage] at hdimLS
    rw [hLTimage] at hdimLT
    rw [hLRimage] at hdimLR
    exact ⟨LS.isFace, LT.isFace, hLStop, hLTtop,
      by omega, by omega,
      LR.carrier, LR.isFace, hLRLS, hLRLT, by omega⟩
  have hlifted : Relation.ReflTransGen (RidgeStepIn P B)
      (lift FX.carrier).carrier (lift FY.carrier).carrier :=
    Relation.ReflTransGen.lift (fun Z => (lift Z).carrier)
    (fun _ _ h => lift_step h) _ _ hpath
  have hliftFX : (lift FX.carrier).carrier = X := by
    have h := lift_of_face FX.carrier FX.isFace
    rw [h]
    change (D.faceEquiv.symm (D.faceEquiv SX)).carrier = X
    rw [D.faceEquiv.symm_apply_apply]
  have hliftFY : (lift FY.carrier).carrier = Y := by
    have h := lift_of_face FY.carrier FY.isFace
    rw [h]
    change (D.faceEquiv.symm (D.faceEquiv SY)).carrier = Y
    rw [D.faceEquiv.symm_apply_apply]
  rwa [hliftFX, hliftFY] at hlifted

end VertexFigureGaloisData

/-- Induzione forte completa: l'esistenza uniforme delle figure al vertice
chiude `RidgeConnectedAboveOne` in ogni dimensione intrinseca. -/
theorem ridgeConnectedAboveOne_of_vertexFigureGalois
    (hfigure : VertexFigureGaloisExists) :
    ∀ {n : ℕ} (P : ConvexPolytope n), RidgeConnectedAboveOne P := by
  classical
  have by_dim : ∀ k : ℕ, ∀ {n : ℕ} (P : ConvexPolytope n),
      faceDim P.toSet = k → RidgeConnectedAboveOne P := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro n P hPk
        by_cases hk : k ≤ 3
        · exact ridgeConnectedAboveOne_of_dim_le_three P (by omega)
        · apply ridgeConnectedAboveOne_of_vertexStarAboveThree P
          intro B hB hdB v hv X Y hX hY hXB hYB hdX hdY hvX hvY
          have hvB : v ∈ B := by
            have hv := Finset.mem_filter.mp hv
            exact hv.2
          obtain ⟨D⟩ := hfigure P B hB v hv (by omega)
          have hdimD : faceDim D.figure.toSet + 1 = faceDim B :=
            D.figure_dim_add_one hB hvB (by omega)
          have hB_le : faceDim B ≤ faceDim P.toSet := by
            exact Submodule.finrank_mono
              (vectorSpan_mono ℝ (face_subset_toSet P hB))
          have hDlt : faceDim D.figure.toSet < k := by omega
          have hDridge : RidgeConnectedAboveOne D.figure :=
            ih (faceDim D.figure.toSet) hDlt D.figure rfl
          exact D.star_path_of_ridgeConnected hB hdB hvB hDridge
            X Y hX hY hXB hYB hdX hdY hvX hvY
  intro n P
  exact by_dim (faceDim P.toSet) P rfl

/-- Riduzione finale onesta: la corrispondenza di Galois delle vere figure
al vertice implica esattamente il target richiesto. -/
theorem vertexStar_ridge_connected_of_vertexFigureGalois
    (hfigure : VertexFigureGaloisExists) (P : ConvexPolytope n) :
    VertexStarRidgeConnectedAboveThree P := by
  classical
  intro B hB hdB v hv X Y hX hY hXB hYB hdX hdY hvX hvY
  have hvB : v ∈ B := (Finset.mem_filter.mp hv).2
  obtain ⟨D⟩ := hfigure P B hB v hv (by omega)
  exact D.star_path_of_ridgeConnected hB hdB hvB
    (ridgeConnectedAboveOne_of_vertexFigureGalois hfigure D.figure)
    X Y hX hY hXB hYB hdX hdY hvX hvY

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart13

section BundlePart14
/- Source: Cubical/Polytope/FiguraAlVertice.lean -/
@[expose] public section
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.FiguraAlVertice.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/






/-!
LA FIGURA AL VERTICE ESISTE — CHIUSURA DEL SOTTO-KILL-GATE (21 lug 2026).

`vertexFigure_galois_exists` fornisce, per ogni faccia `B` e vertice `v`,
i dati di Galois `VertexFigureGaloisData`: la figura è il politopo-fetta
di `FettaVertice` al livello separatore, l'equivalenza è
`F ↦ F ∩ {l = c}` con inversa data da `faccia_dalla_fetta`, l'ordine è
preservato da `fetta_mono` e lo shift dimensionale è `fetta_faceDim`.

Corollari apicali, ora INCONDIZIONATI:
* `vertexStar_ridge_connected` — il sotto-kill-gate della campagna;
* `ridgeConnectedAboveOne_sempre` — il muro del ridge-graph, per ogni
  politopo e ogni dimensione;
* `galleryConnected_sempre` — la connettività globale delle gallerie;
* `vertices_eq_simpleVertexOrbit_sempre` — U4: i vertici sono l'orbita
  del vertice base sotto il gruppo delle riflessioni semplici.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il livello separatore esiste per ogni vertice di un politopo di
dimensione positiva. -/
theorem esiste_datiFetta (Q : ConvexPolytope n) {v : E n}
    (hv : v ∈ Q.vertices) (hdQ : 1 ≤ faceDim Q.toSet) :
    Nonempty (DatiFetta Q v) := by
  classical
  obtain ⟨l, hl⟩ := (vertex_isFace Q hv).1 (Set.singleton_nonempty v)
  have hvmem : v ∈ ({v} : Set (E n)) := Set.mem_singleton v
  rw [hl] at hvmem
  have hstrict : ∀ u ∈ Q.vertices, u ≠ v → l u < l v := by
    intro u huV huv
    have huT : u ∈ Q.toSet := subset_convexHull ℝ _ (by exact_mod_cast huV)
    rcases lt_or_eq_of_le (hvmem.2 u huT) with h | h
    · exact h
    · exfalso
      apply huv
      have hu1 : u ∈ ({v} : Set (E n)) := by
        rw [hl]
        exact ⟨huT, fun z hz => le_trans (hvmem.2 z hz) (le_of_eq h.symm)⟩
      exact Set.mem_singleton_iff.mp hu1
  have hW : (Q.vertices.erase v).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hverts : Q.vertices = {v} := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        by_contra hwv
        have hmem : w ∈ Q.vertices.erase v :=
          Finset.mem_erase.mpr ⟨by simpa using hwv, hw⟩
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty w)
      · have h1 : 1 ≤ Q.vertices.card := Finset.card_pos.mpr ⟨v, hv⟩
        simpa using h1
    have hT : Q.toSet = ({v} : Set (E n)) := by
      show convexHull ℝ ((Q.vertices : Finset (E n)) : Set (E n)) = _
      rw [hverts]
      simp
    rw [hT, faceDim_singleton] at hdQ
    omega
  obtain ⟨m, hmW, hmmax⟩ := (Q.vertices.erase v).exists_max_image l hW
  have hmlt : l m < l v :=
    hstrict m (Finset.mem_of_mem_erase hmW) (Finset.ne_of_mem_erase hmW)
  refine ⟨⟨l, (l v + l m) / 2, hv, by linarith, ?_, hW⟩⟩
  intro w hwV hwv
  have hle := hmmax w (Finset.mem_erase.mpr ⟨hwv, hwV⟩)
  linarith

/-- **LA FIGURA AL VERTICE ESISTE.**  Il sotto-kill-gate della campagna
è chiuso: ogni intervallo di facce sopra un vertice ammette una vera
figura al vertice con la corrispondenza di Galois e lo shift
dimensionale. -/
theorem vertexFigure_galois_exists : VertexFigureGaloisExists := by
  intro n P B hB v hv hdB
  classical
  have hQT : (facePolytope P hB).toSet = B := facePolytope_toSet P hB
  have hdQ : 1 ≤ faceDim (facePolytope P hB).toSet := by
    rw [hQT]
    exact hdB
  obtain ⟨D⟩ := esiste_datiFetta (facePolytope P hB) hv hdQ
  choose Finv hFinvQ hFinvV hFinvD hFinvS using
    fun (G : PolytopeFace D.politopo) => D.faccia_dalla_fetta G.isFace
  refine ⟨⟨D.politopo,
    { toFun := fun F =>
        ⟨F.carrier ∩ {x | D.l x = D.c},
          D.faccia_fetta
            (facePolytope_isFace_of P hB F.isFace F.subset_base)
            F.mem_vertex F.dim_pos⟩
      invFun := fun G =>
        ⟨Finv G, isFace_of_facePolytope P hB (hFinvQ G),
          by
            have hsub := face_subset_toSet (facePolytope P hB) (hFinvQ G)
            rwa [hQT] at hsub,
          hFinvV G, hFinvD G⟩
      left_inv := ?_
      right_inv := ?_ }, ?_, ?_⟩⟩
  · -- left_inv: l'unicità della faccia con fetta data
    intro F
    apply PositiveVertexStarFace.ext
    have hQF : (facePolytope P hB).IsFace F.carrier :=
      facePolytope_isFace_of P hB F.isFace F.subset_base
    have hs := hFinvS ⟨F.carrier ∩ {x | D.l x = D.c},
      D.faccia_fetta (facePolytope_isFace_of P hB F.isFace F.subset_base)
        F.mem_vertex F.dim_pos⟩
    apply Set.Subset.antisymm
    · exact D.fetta_mono (hFinvQ _) (hFinvV _) hQF F.mem_vertex hs.subset
    · exact D.fetta_mono hQF F.mem_vertex (hFinvQ _) (hFinvV _)
        hs.symm.subset
  · -- right_inv: la fetta della faccia scelta è la faccia di partenza
    intro G
    apply PolytopeFace.ext
    exact hFinvS G
  · -- map_subset_iff
    intro F G
    constructor
    · intro hsub
      exact fun x hx => ⟨hsub hx.1, hx.2⟩
    · intro hsub
      exact D.fetta_mono
        (facePolytope_isFace_of P hB F.isFace F.subset_base) F.mem_vertex
        (facePolytope_isFace_of P hB G.isFace G.subset_base) G.mem_vertex
        hsub
  · -- map_dim
    intro F
    exact D.fetta_faceDim
      (facePolytope_isFace_of P hB F.isFace F.subset_base)
      F.mem_vertex F.dim_pos

/-! ## I corollari apicali, ora incondizionati -/

/-- **IL SOTTO-KILL-GATE È CHIUSO**: la connettività ridge dello star di
ogni vertice, per ogni politopo. -/
theorem vertexStar_ridge_connected (P : ConvexPolytope n) :
    VertexStarRidgeConnectedAboveThree P :=
  vertexStar_ridge_connected_of_vertexFigureGalois
    vertexFigure_galois_exists P

/-- **IL MURO DEL RIDGE-GRAPH È CADUTO**: `RidgeConnectedAboveOne` vale
per ogni politopo, in ogni dimensione. -/
theorem ridgeConnectedAboveOne_sempre (P : ConvexPolytope n) :
    RidgeConnectedAboveOne P :=
  ridgeConnectedAboveOne_of_vertexFigureGalois vertexFigure_galois_exists P

/-- **LA CONNETTIVITÀ GLOBALE DELLE GALLERIE**, incondizionata. -/
theorem galleryConnected_sempre (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F G : P.Flag) : GalleryConnected P F G :=
  galleryConnected_of_ridgeConnectedAboveOne P hfull
    (ridgeConnectedAboveOne_sempre P) F G


end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart14

section BundlePart15
/- Source: Cubical/Polytope/VertexSlice.lean -/
@[expose] public section



/-!
# Concrete vertex figures and descending links

The geometric vertex figure is a separating hyperplane slice of the
polytope. Its vertices correspond to the actual neighbors of the cut-off
vertex. Their coordinates lie on the corresponding edges with positive
interpolation parameter, so the sign of every other linear height is
preserved relative to the cut-off vertex.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ} {P : ConvexPolytope n}

/-- Neighbors of one actual polytope vertex. -/
abbrev NeighborOf (v : VertexType P) :=
  {w : VertexType P // (polytopeGraph P).Adj v w}

/-- Adjacency in a descending vertex link, expressed by geometric two-faces. -/
def LowerTwoFaceRelation (v : VertexType P) (l : E n →L[ℝ] ℝ)
    (a b : NeighborOf v) : Prop :=
  l a.val.val < l v.val ∧ l b.val.val < l v.val ∧ a ≠ b ∧
    ∃ F : Set (E n), P.IsFace F ∧ faceDim F = 2 ∧
      v.val ∈ F ∧ a.val.val ∈ F ∧ b.val.val ∈ F

namespace DatiFetta

variable {v : E n} (D : DatiFetta P v)

theorem attra_mem_face {F : Set (E n)} (hF : P.IsFace F) (hvF : v ∈ F)
    {w : E n} (hw : w ∈ P.vertices) (hwF : w ∈ F) (hwv : w ≠ v) :
    D.attra w ∈ F :=
  (hF.1.convex (convex_convexHull ℝ _)).segment_subset hvF hwF
    (D.attra_mem_segment (D.hsep w hw hwv))

theorem edge_slice_data {F : Set (E n)} (hF : P.IsFace F) (hdF : faceDim F = 1)
    (hvF : v ∈ F) {w : E n} (hw : w ∈ P.vertices) (hwF : w ∈ F) (hwv : w ≠ v) :
    F ∩ {x | D.l x = D.c} = {D.attra w} ∧
      D.attra w ∈ D.politopo.vertices := by
  have hslice := D.faccia_fetta hF hvF (by omega)
  have hdim : faceDim (F ∩ {x | D.l x = D.c}) = 0 := by
    have hh := D.fetta_faceDim hF hvF (by omega)
    omega
  obtain ⟨q, hqset, hqvert⟩ := punto_di_faccia0_e_vertice D.politopo hslice hdim
  have hmem : D.attra w ∈ F ∩ {x | D.l x = D.c} :=
    ⟨D.attra_mem_face hF hvF hw hwF hwv, D.attra_level (D.hsep w hw hwv)⟩
  rw [hqset] at hmem
  have heq : D.attra w = q := Set.mem_singleton_iff.mp hmem
  exact ⟨hqset.trans (congrArg (fun z => ({z} : Set (E n))) heq.symm), heq.symm ▸ hqvert⟩

theorem attra_height_sub (l : E n →L[ℝ] ℝ) (w : E n) :
    l (D.attra w) - l v =
      ((D.l v - D.c) / (D.l v - D.l w)) * (l w - l v) := by
  rw [← map_sub, D.attra_sub, map_smul, map_sub]
  rfl

theorem attra_lt_base_iff (l : E n →L[ℝ] ℝ)
    {w : E n} (hw : w ∈ P.vertices) (hwv : w ≠ v) :
    l (D.attra w) < l v ↔ l w < l v := by
  have ht := D.tau_pos (D.hsep w hw hwv)
  have heq := D.attra_height_sub l w
  constructor <;> intro h <;> nlinarith

end DatiFetta

namespace DatiFetta

variable {v : VertexType P} (D : DatiFetta P v.val)

theorem neighbor_ne_base (a : NeighborOf v) : a.val.val ≠ v.val := by
  intro h
  exact a.property.1 (Subtype.ext h.symm)

noncomputable def neighborToFigureVertex (a : NeighborOf v) : VertexType D.politopo := by
  refine ⟨D.attra a.val.val, ?_⟩
  obtain ⟨F, hF, hdF, hvF, haF⟩ := a.property.2
  exact (D.edge_slice_data hF hdF hvF a.val.property haF (neighbor_ne_base a)).2

@[simp] theorem neighborToFigureVertex_val (a : NeighborOf v) :
    (D.neighborToFigureVertex a).val = D.attra a.val.val := rfl

theorem neighborToFigureVertex_injective : Function.Injective D.neighborToFigureVertex := by
  intro a b hab
  have hab' : D.attra a.val.val = D.attra b.val.val := congrArg Subtype.val hab
  obtain ⟨F, hF, hdF, hvF, haF⟩ := a.property.2
  obtain ⟨G, hG, hdG, hvG, hbG⟩ := b.property.2
  have hFs := (D.edge_slice_data hF hdF hvF a.val.property haF (neighbor_ne_base a)).1
  have hGs := (D.edge_slice_data hG hdG hvG b.val.property hbG (neighbor_ne_base b)).1
  have hGF : G ⊆ F := D.fetta_mono hG hvG hF hvF (by rw [hGs, hFs, hab'])
  have hseg := edge_eq_segment P hF hdF v.property a.val.property hvF haF
    (neighbor_ne_base a).symm
  have hbend := vertice_in_segmento_estremo_generico P hF hseg b.val.property (hGF hbG)
  apply Subtype.ext
  apply Subtype.ext
  rcases hbend with hb | hb
  · exact (neighbor_ne_base b hb).elim
  · exact hb.symm

theorem neighborToFigureVertex_surjective : Function.Surjective D.neighborToFigureVertex := by
  intro q
  have hqF := vertex_isFace D.politopo q.property
  obtain ⟨F, hF, hvF, hdpos, hslice⟩ := D.faccia_dalla_fetta hqF
  have hdF : faceDim F = 1 := by
    have hh := D.fetta_faceDim hF hvF hdpos
    rw [hslice, faceDim_singleton] at hh
    omega
  obtain ⟨w, hw, hwF, hwv, _hseg⟩ := spigolo_segmento P hF hdF v.property hvF
  let a : NeighborOf v := ⟨⟨w, hw⟩, ⟨by
    intro h
    exact hwv (congrArg Subtype.val h).symm,
    F, hF, hdF, hvF, hwF⟩⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  have hh := (D.edge_slice_data hF hdF hvF hw hwF hwv).1
  rw [hslice] at hh
  exact (Set.singleton_injective hh).symm

/-- Actual neighbors correspond bijectively to the extreme points of the slice. -/
noncomputable def neighborEquiv : NeighborOf v ≃ VertexType D.politopo :=
  Equiv.ofBijective D.neighborToFigureVertex
    ⟨D.neighborToFigureVertex_injective, D.neighborToFigureVertex_surjective⟩

@[simp] theorem neighborEquiv_val (a : NeighborOf v) :
    (D.neighborEquiv a).val = D.attra a.val.val := rfl

theorem neighborEquiv_lt_base_iff (l : E n →L[ℝ] ℝ) (a : NeighborOf v) :
    l (D.neighborEquiv a).val < l v.val ↔ l a.val.val < l v.val :=
  D.attra_lt_base_iff l a.val.property (neighbor_ne_base a)

/-- An edge in the vertex figure is exactly a two-face through the base vertex. -/
theorem neighborEquiv_adj_iff (a b : NeighborOf v) :
    (polytopeGraph D.politopo).Adj (D.neighborEquiv a) (D.neighborEquiv b) ↔
      a ≠ b ∧ ∃ F : Set (E n), P.IsFace F ∧ faceDim F = 2 ∧
        v.val ∈ F ∧ a.val.val ∈ F ∧ b.val.val ∈ F := by
  constructor
  · rintro ⟨hne, G, hG, hdG, haG, hbG⟩
    have hab : a ≠ b := fun h => hne (congrArg D.neighborEquiv h)
    obtain ⟨F, hF, hvF, hdpos, hslice⟩ := D.faccia_dalla_fetta hG
    have hdF : faceDim F = 2 := by
      have hh := D.fetta_faceDim hF hvF hdpos
      rw [hslice, hdG] at hh
      omega
    have neighbor_mem : ∀ c : NeighborOf v,
        (D.neighborEquiv c).val ∈ G → c.val.val ∈ F := by
      intro c hcG
      obtain ⟨e, he, hde, hve, hce⟩ := c.property.2
      have hes := (D.edge_slice_data he hde hve c.val.property hce (neighbor_ne_base c)).1
      have heF : e ⊆ F := D.fetta_mono he hve hF hvF (by
        rw [hes, hslice]
        exact Set.singleton_subset_iff.mpr hcG)
      exact heF hce
    exact ⟨hab, F, hF, hdF, hvF, neighbor_mem a haG, neighbor_mem b hbG⟩
  · rintro ⟨hne, F, hF, hdF, hvF, haF, hbF⟩
    have hslice := D.faccia_fetta hF hvF (by omega)
    have hdim : faceDim (F ∩ {x | D.l x = D.c}) = 1 := by
      have hh := D.fetta_faceDim hF hvF (by omega)
      omega
    refine ⟨fun h => hne (D.neighborEquiv.injective h), _, hslice, hdim, ?_, ?_⟩
    · exact ⟨D.attra_mem_face hF hvF a.val.property haF (neighbor_ne_base a),
        D.attra_level (D.hsep _ a.val.property (neighbor_ne_base a))⟩
    · exact ⟨D.attra_mem_face hF hvF b.val.property hbF (neighbor_ne_base b),
        D.attra_level (D.hsep _ b.val.property (neighbor_ne_base b))⟩

/-- The descending link of a geometric polytope vertex is connected. -/
theorem lowerNeighbors_connected (l : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn l (D.politopo.vertices : Set (E n)))
    (a b : NeighborOf v) (ha : l a.val.val < l v.val) (hb : l b.val.val < l v.val) :
    Relation.ReflTransGen (LowerTwoFaceRelation v l) a b := by
  classical
  let f (q : E n) : NeighborOf v :=
    if hq : q ∈ D.politopo.vertices then D.neighborEquiv.symm ⟨q, hq⟩ else a
  have f_on (q : E n) (hq : q ∈ D.politopo.vertices) :
      D.neighborEquiv (f q) = ⟨q, hq⟩ := by
    simp only [f, dite_eq_left hq, Equiv.apply_symm_apply]
  have f_apply (a' : NeighborOf v) : f (D.neighborEquiv a').val = a' := by
    apply D.neighborEquiv.injective
    exact f_on _ (D.neighborEquiv a').property
  have hpath := sublevel_connected D.politopo l (l v.val) hinj
    (D.neighborEquiv a).property (D.neighborEquiv b).property
    ((D.neighborEquiv_lt_base_iff l a).mpr ha)
    ((D.neighborEquiv_lt_base_iff l b).mpr hb)
  have hmap : ∀ p q, SublevelStep D.politopo l (l v.val) p q →
      LowerTwoFaceRelation v l (f p) (f q) := by
    rintro p q ⟨hp, ⟨hq, hpq, G, hG, hdG, hpG, hqG⟩, hlp, hlq⟩
    have hAdj : (polytopeGraph D.politopo).Adj
        (D.neighborEquiv (f p)) (D.neighborEquiv (f q)) := by
      rw [f_on p hp, f_on q hq]
      exact ⟨fun h => hpq (congrArg Subtype.val h), G, hG, hdG, hpG, hqG⟩
    have hpl : l (f p).val.val < l v.val :=
      (D.neighborEquiv_lt_base_iff l (f p)).mp (by rw [f_on p hp]; exact hlp)
    have hql : l (f q).val.val < l v.val :=
      (D.neighborEquiv_lt_base_iff l (f q)).mp (by rw [f_on q hq]; exact hlq)
    exact ⟨hpl, hql, (D.neighborEquiv_adj_iff (f p) (f q)).mp hAdj⟩
  have hlift := Relation.ReflTransGen.lift f hmap _ _ hpath
  change Relation.ReflTransGen (LowerTwoFaceRelation v l)
    (f (D.neighborEquiv a).val) (f (D.neighborEquiv b).val) at hlift
  simpa only [f_apply] using hlift

end DatiFetta

end LeanEval.Geometry.PlatonicClassification

end
end BundlePart15

section BundlePart16
/- Source: Cubical/Polytope/FaceIncidence.lean -/
@[expose] public section



/-! # Finite geometric face incidence and double counting -/

open Set
open Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

abbrev DimFaceType (P : ConvexPolytope n) (i : ℕ) :=
  {F : FaceType P // faceDim F.val = i}

abbrev IncidentFaceType (P : ConvexPolytope n) (v : VertexType P) (i : ℕ) :=
  {F : FaceType P // faceDim F.val = i ∧ v.val ∈ F.val}

instance dimFaceTypeFintype (P : ConvexPolytope n) (i : ℕ) : Fintype (DimFaceType P i) :=
  Fintype.ofFinite _

instance incidentFaceTypeFintype (P : ConvexPolytope n) (v : VertexType P) (i : ℕ) :
    Fintype (IncidentFaceType P v i) := Fintype.ofFinite _

def incidentFaceNumber (P : ConvexPolytope n) (v : VertexType P) (i : ℕ) : ℕ :=
  Fintype.card (IncidentFaceType P v i)

theorem card_dimFaceType (P : ConvexPolytope n) (i : ℕ) :
    Fintype.card (DimFaceType P i) = faceNumber P i := by
  classical
  let e : DimFaceType P i ≃ ↥((faceSet P).filter (fun F => faceDim F = i)) :=
    { toFun := fun F => ⟨F.val.val, Finset.mem_filter.mpr ⟨(mem_faceSet P _).mpr F.val.property, F.property⟩⟩
      invFun := fun F => ⟨⟨F.val, (mem_faceSet P _).mp (Finset.mem_filter.mp F.property).1⟩,
        (Finset.mem_filter.mp F.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

theorem incidentFaceNumber_eq (P : ConvexPolytope n) (v : VertexType P) (i : ℕ) :
    incidentFaceNumber P v i =
      ((faceSet P).filter (fun F => faceDim F = i ∧ v.val ∈ F)).card := by
  classical
  let e : IncidentFaceType P v i ≃
      ↥((faceSet P).filter (fun F => faceDim F = i ∧ v.val ∈ F)) :=
    { toFun := fun F => ⟨F.val.val, Finset.mem_filter.mpr ⟨(mem_faceSet P _).mpr F.val.property, F.property⟩⟩
      invFun := fun F => ⟨⟨F.val, (mem_faceSet P _).mp (Finset.mem_filter.mp F.property).1⟩,
        (Finset.mem_filter.mp F.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

/-- A flag consisting of a vertex and an incident face can be indexed in
either order. The vertices remain the actual geometric extreme points. -/
def vertexFaceIncidenceEquiv (P : ConvexPolytope n) (i : ℕ) :
    (Σ v : VertexType P, IncidentFaceType P v i) ≃
      (Σ F : DimFaceType P i, VertexType (facePolytope P F.val.property)) where
  toFun p := ⟨⟨p.2.val, p.2.property.1⟩,
    ⟨p.1.val, Finset.mem_filter.mpr ⟨p.1.property, p.2.property.2⟩⟩⟩
  invFun p := ⟨⟨p.2.val, (Finset.mem_filter.mp p.2.property).1⟩,
    ⟨p.1.val, p.1.property, (Finset.mem_filter.mp p.2.property).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Double-count incidences between vertices and faces of fixed dimension. -/
theorem sum_incidentFaceNumber (P : ConvexPolytope n) (i : ℕ) :
    ∑ v : VertexType P, incidentFaceNumber P v i =
      ∑ F : DimFaceType P i, (facePolytope P F.val.property).vertices.card := by
  have h := Fintype.card_congr (vertexFaceIncidenceEquiv P i)
  simpa only [Fintype.card_sigma, incidentFaceNumber, VertexType, Fintype.card_coe] using h

theorem sum_incidentFaceNumber_of_uniform_vertices (P : ConvexPolytope n) (i k : ℕ)
    (hvertices : ∀ F : DimFaceType P i,
      (facePolytope P F.val.property).vertices.card = k) :
    ∑ v : VertexType P, incidentFaceNumber P v i = faceNumber P i * k := by
  rw [sum_incidentFaceNumber]
  simp [hvertices, card_dimFaceType]

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart16

section BundlePart17
/- Source: Cubical/Polytope/VertexSliceCounts.lean -/
@[expose] public section




/-! # Geometric vertex-figure dimension and face incidence counts -/

open Set
open Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ} {P : ConvexPolytope n}

/-- Positive-dimensional faces incident to a specified geometric vertex. -/
abbrev PositiveFaceStar (P : ConvexPolytope n) (v : VertexType P) :=
  {F : FaceType P // v.val ∈ F.val ∧ 1 ≤ faceDim F.val}

instance positiveFaceStarFintype (P : ConvexPolytope n) (v : VertexType P) :
    Fintype (PositiveFaceStar P v) := Fintype.ofFinite _

namespace DatiFetta

variable {v : VertexType P} (D : DatiFetta P v.val)

def sliceFace (F : PositiveFaceStar P v) : FaceType D.politopo :=
  ⟨F.val.val ∩ {x | D.l x = D.c}, D.faccia_fetta F.val.property F.property.1 F.property.2⟩

theorem sliceFace_injective : Function.Injective D.sliceFace := by
  intro F G h
  have hset : F.val.val ∩ {x | D.l x = D.c} = G.val.val ∩ {x | D.l x = D.c} :=
    congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  exact Set.Subset.antisymm
    (D.fetta_mono F.val.property F.property.1 G.val.property G.property.1 hset.subset)
    (D.fetta_mono G.val.property G.property.1 F.val.property F.property.1 hset.symm.subset)

theorem sliceFace_surjective : Function.Surjective D.sliceFace := by
  intro G
  obtain ⟨F, hF, hvF, hdF, hslice⟩ := D.faccia_dalla_fetta G.property
  exact ⟨⟨⟨F, hF⟩, hvF, hdF⟩, Subtype.ext hslice⟩

/-- The complete face correspondence for the actual hyperplane slice. -/
def sliceFaceOrderIso : PositiveFaceStar P v ≃o FaceType D.politopo where
  __ := Equiv.ofBijective D.sliceFace ⟨D.sliceFace_injective, D.sliceFace_surjective⟩
  map_rel_iff' := by
    intro F G
    constructor
    · exact D.fetta_mono F.val.property F.property.1 G.val.property G.property.1
    · intro h x hx
      exact ⟨h hx.1, hx.2⟩

@[simp] theorem sliceFaceOrderIso_val (F : PositiveFaceStar P v) :
    (D.sliceFaceOrderIso F).val = F.val.val ∩ {x | D.l x = D.c} := rfl

theorem sliceFaceOrderIso_dimension (F : PositiveFaceStar P v) :
    faceDim (D.sliceFaceOrderIso F).val + 1 = faceDim F.val.val :=
  D.fetta_faceDim F.val.property F.property.1 F.property.2

/-- A vertex figure has intrinsic dimension one less than its polytope. -/
theorem politopo_dim_add_one (hdim : 1 ≤ P.dim) : D.politopo.dim + 1 = P.dim := by
  have hvP : v.val ∈ P.toSet := subset_convexHull ℝ _ v.property
  have hdim' := D.fetta_faceDim (toSet_isFace P) hvP hdim
  rw [← D.politopo_toSet] at hdim'
  exact hdim'

def incidentFaceSliceEquiv (i : ℕ) :
    IncidentFaceType P v (i + 1) ≃ DimFaceType D.politopo i := by
  let e : IncidentFaceType P v (i + 1) ≃
      {F : PositiveFaceStar P v // faceDim F.val.val = i + 1} :=
    { toFun := fun F => ⟨⟨F.val, F.property.2, by omega⟩, F.property.1⟩
      invFun := fun F => ⟨F.val.val, F.property, F.val.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine e.trans (D.sliceFaceOrderIso.toEquiv.subtypeEquiv ?_)
  intro F
  have hdim := D.sliceFaceOrderIso_dimension F
  change faceDim F.val.val = i + 1 ↔ faceDim (D.sliceFaceOrderIso F).val = i
  omega

/-- Every face of a vertex figure corresponds to exactly one incident face
of the original polytope, with dimension increased by one. -/
theorem faceNumber_eq_incidentFaceNumber (i : ℕ) :
    faceNumber D.politopo i = incidentFaceNumber P v (i + 1) := by
  rw [← card_dimFaceType]
  exact (Fintype.card_congr (D.incidentFaceSliceEquiv i)).symm

theorem vertices_card_eq_degree :
    D.politopo.vertices.card = (polytopeGraph P).degree v := by
  have h := Fintype.card_congr D.neighborEquiv
  change Fintype.card ((polytopeGraph P).neighborSet v) =
    Fintype.card (VertexType D.politopo) at h
  rw [SimpleGraph.card_neighborSet_eq_degree] at h
  simpa [VertexType] using h.symm

end DatiFetta

/-- Sum all vertex-figure face numbers by double-counting geometric incidences. -/
theorem sum_vertexFigure_faceNumber (D : (v : VertexType P) → DatiFetta P v.val) (i : ℕ) :
    ∑ v : VertexType P, faceNumber (D v).politopo i =
      ∑ F : DimFaceType P (i + 1), (facePolytope P F.val.property).vertices.card := by
  simp_rw [DatiFetta.faceNumber_eq_incidentFaceNumber]
  exact sum_incidentFaceNumber P (i + 1)

theorem sum_vertexFigure_faceNumber_of_uniform_vertices
    (D : (v : VertexType P) → DatiFetta P v.val) (i k : ℕ)
    (hvertices : ∀ F : DimFaceType P (i + 1),
      (facePolytope P F.val.property).vertices.card = k) :
    ∑ v : VertexType P, faceNumber (D v).politopo i = faceNumber P (i + 1) * k := by
  simp_rw [DatiFetta.faceNumber_eq_incidentFaceNumber]
  exact sum_incidentFaceNumber_of_uniform_vertices P (i + 1) k hvertices

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart17

section BundlePart18
/- Source: Cubical/Polytope/SimplicialPolytope.lean -/
@[expose] public section



/-!
# Geometric simplices and simplicial convex polytopes

Simpliciality means affine independence of the actual extreme vertices of
every facet. Its equivalent vertex-count characterization is derived from
the affine dimension, rather than included as an unrelated hypothesis.
-/

open Set
open Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

theorem dim_eq_vertices_span (P : ConvexPolytope n) :
    P.dim = Module.finrank ℝ (vectorSpan ℝ (P.vertices : Set (E n))) := by
  unfold ConvexPolytope.dim ConvexPolytope.toSet
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]

theorem facePolytope_dim (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F) :
    (facePolytope P hF).dim = faceDim F := by
  change faceDim (facePolytope P hF).toSet = faceDim F
  rw [facePolytope_toSet]

theorem vertices_affineIndependent_iff (P : ConvexPolytope n) :
    AffineIndependent ℝ (fun v : VertexType P => v.val) ↔
      P.vertices.card = P.dim + 1 := by
  have hrange : Set.range (fun v : VertexType P => v.val) = (P.vertices : Set (E n)) :=
    Subtype.range_coe
  have hdim : Module.finrank ℝ (vectorSpan ℝ
      (Set.range (fun v : VertexType P => v.val))) = P.dim := by
    rw [hrange, ← dim_eq_vertices_span]
  constructor
  · intro hi
    letI : Nonempty (VertexType P) := by
      obtain ⟨v, hv⟩ := P.vertices_nonempty
      exact ⟨⟨v, hv⟩⟩
    have h := hi.finrank_vectorSpan_add_one
    rw [hdim] at h
    simpa [VertexType] using h.symm
  · intro hc
    have hc' : Fintype.card (VertexType P) = P.dim + 1 := by
      simpa [VertexType] using hc
    exact (affineIndependent_iff_finrank_vectorSpan_eq ℝ _ hc').mpr hdim

/-- Every facet is the convex hull of an affinely independent vertex family. -/
def IsSimplicial (P : ConvexPolytope n) : Prop :=
  ∀ (F : Set (E n)) (hF : P.IsFace F), faceDim F + 1 = P.dim →
    AffineIndependent ℝ (fun v : VertexType (facePolytope P hF) => v.val)

theorem isSimplicial_iff_facet_vertices_card (P : ConvexPolytope n) :
    IsSimplicial P ↔ ∀ (F : Set (E n)) (hF : P.IsFace F),
      faceDim F + 1 = P.dim → (facePolytope P hF).vertices.card = P.dim := by
  constructor
  · intro hs F hF hdF
    have hcard := (vertices_affineIndependent_iff (facePolytope P hF)).mp (hs F hF hdF)
    rwa [facePolytope_dim P hF, hdF] at hcard
  · intro hs F hF hdF
    apply (vertices_affineIndependent_iff (facePolytope P hF)).mpr
    rw [facePolytope_dim, hdF]
    exact hs F hF hdF

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart18

section BundlePart19
/- Source: Cubical/Polytope/SimplexFaces.lean -/
@[expose] public section


/-! # Exposed faces of an actual geometric simplex -/

open Set
open Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- The convex hull of a subset of extreme vertices contains no other
extreme vertex of the original polytope. -/
theorem vertices_filter_convexHull_subset (P : ConvexPolytope n)
    (S : Finset (E n)) (hS : S ⊆ P.vertices) :
    P.vertices.filter (fun x => x ∈ convexHull ℝ (S : Set (E n))) = S := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hxP, hxS⟩
    have hxext : x ∈ P.toSet.extremePoints ℝ := by
      change x ∈ (convexHull ℝ (P.vertices : Set (E n))).extremePoints ℝ
      rw [← P.vertices_eq_extremePoints]
      exact hxP
    have hsub : convexHull ℝ (S : Set (E n)) ⊆ P.toSet :=
      convexHull_mono (fun _ h => hS h)
    exact extremePoints_convexHull_subset
      (inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hxS, hxext⟩)
  · intro hx
    exact ⟨hS hx, subset_convexHull ℝ _ hx⟩

theorem affineIndependent_face_vertices (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    {F : Set (E n)} (hF : P.IsFace F) :
    AffineIndependent ℝ (fun v : VertexType (facePolytope P hF) => v.val) := by
  let f : VertexType (facePolytope P hF) → VertexType P :=
    fun v => ⟨v.val, (Finset.mem_filter.mp v.property).1⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun q : VertexType P => q.val) h)
  exact hi.comp_embedding ⟨f, hf⟩

/-- Removing one vertex from a simplex leaves an exposed face whenever the
remaining vertex set is nonempty. -/
theorem simplex_erase_isFace (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (x : VertexType P) (hne : (P.vertices.erase x.val).Nonempty) :
    P.IsFace (convexHull ℝ ((P.vertices.erase x.val : Finset (E n)) : Set (E n))) := by
  let S := P.vertices.erase x.val
  obtain ⟨u, hu⟩ := hne
  have huS : u ∈ S := hu
  have huP : u ∈ P.vertices := Finset.mem_of_mem_erase hu
  have hi' : AffineIndepOn ℝ id (P.vertices : Set (E n)) := hi
  have hxnot : x.val ∉ affineSpan ℝ (S : Set (E n)) := by
    have h := hi'.notMem_affineSpan_sdiff x.property
    simpa [S, Finset.coe_erase] using h
  have hxsubnot : x.val - u ∉ vectorSpan ℝ (S : Set (E n)) := by
    rw [← direction_affineSpan]
    intro h
    exact hxnot ((AffineSubspace.vsub_right_mem_direction_iff_mem
      (mem_affineSpan ℝ huS) x.val).mp h)
  obtain ⟨f, hfzero, hfx⟩ := LinearMap.exists_extend_of_notMem
    (0 : vectorSpan ℝ (S : Set (E n)) →ₗ[ℝ] ℝ) hxsubnot (-1)
  let l : E n →L[ℝ] ℝ := f.toContinuousLinearMap
  have hconstant : ∀ w ∈ S, l w = l u := by
    intro w hw
    have hwu : w - u ∈ vectorSpan ℝ (S : Set (E n)) :=
      vsub_mem_vectorSpan ℝ hw huS
    have h := congrArg (fun g : vectorSpan ℝ (S : Set (E n)) →ₗ[ℝ] ℝ => g ⟨w-u, hwu⟩) hfzero
    change f (w-u) = 0 at h
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  have hxlow : l x.val = l u - 1 := by
    rw [map_sub] at hfx
    change f x.val = f u - 1
    linarith
  have hmaxverts : ∀ w ∈ (P.vertices : Set (E n)), l w ≤ l u := by
    intro w hw
    by_cases hwx : w = x.val
    · rw [hwx, hxlow]
      linarith
    · exact (hconstant w (Finset.mem_erase.mpr ⟨hwx, hw⟩)).le
  have hmax := le_su_toSet P l hmaxverts
  let F := l.toExposed P.toSet
  have hF : P.IsFace F :=
    ⟨ContinuousLinearMap.toExposed.isExposed,
      ⟨u, subset_convexHull ℝ _ huP, hmax⟩⟩
  have hvertices : P.vertices.filter (fun w => w ∈ F) = S := by
    ext w
    simp only [Finset.mem_filter, S, Finset.mem_erase]
    constructor
    · rintro ⟨hwP, hwF⟩
      refine ⟨?_, hwP⟩
      intro hwx
      have hule : l u ≤ l w := hwF.2 u (subset_convexHull ℝ _ huP)
      rw [hwx, hxlow] at hule
      linarith
    · rintro ⟨hwx, hwP⟩
      refine ⟨hwP, subset_convexHull ℝ _ hwP, ?_⟩
      intro z hz
      rw [hconstant w (Finset.mem_erase.mpr ⟨hwx, hwP⟩)]
      exact hmax z hz
  have hset := face_eq_hull_vertices P hF
  rw [hvertices] at hset
  exact hset ▸ hF

/-- Every nonempty subset of a simplex's vertices spans an exposed face. -/
theorem simplex_subset_isFace (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (S : Finset (E n)) (hS : S ⊆ P.vertices) (hne : S.Nonempty) :
    P.IsFace (convexHull ℝ (S : Set (E n))) := by
  have aux : ∀ k : ℕ, ∀ Q : ConvexPolytope n, Q.vertices.card ≤ k →
      AffineIndependent ℝ (fun v : VertexType Q => v.val) →
      ∀ T : Finset (E n), T ⊆ Q.vertices → T.Nonempty →
        Q.IsFace (convexHull ℝ (T : Set (E n))) := by
    intro k
    induction k with
    | zero =>
      intro Q hcard _ T _ _
      have hpos := Finset.card_pos.mpr Q.vertices_nonempty
      omega
    | succ k ih =>
      intro Q hcard hAI T hT hTne
      by_cases heq : T = Q.vertices
      · subst T
        exact toSet_isFace Q
      obtain ⟨x, hxQ, hxT⟩ := Finset.exists_of_ssubset (hT.ssubset_of_ne heq)
      have hTErase : T ⊆ Q.vertices.erase x := by
        intro y hy
        refine Finset.mem_erase.mpr ⟨?_, hT hy⟩
        intro hyx
        exact hxT (hyx ▸ hy)
      have hErase := simplex_erase_isFace Q hAI ⟨x, hxQ⟩ (hTne.mono hTErase)
      let R := facePolytope Q hErase
      have hRverts : R.vertices = Q.vertices.erase x :=
        vertices_filter_convexHull_subset Q _ (Finset.erase_subset _ _)
      have hRcard : R.vertices.card ≤ k := by
        rw [hRverts, Finset.card_erase_of_mem hxQ]
        omega
      have hTR : T ⊆ R.vertices := by rwa [hRverts]
      exact isFace_of_facePolytope Q hErase
        (ih R hRcard (affineIndependent_face_vertices Q hAI hErase) T hTR hTne)
  exact aux P.vertices.card P le_rfl hi S hS hne

theorem simplex_face_vertices_card (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    {F : Set (E n)} (hF : P.IsFace F) :
    (facePolytope P hF).vertices.card = faceDim F + 1 := by
  have h := (vertices_affineIndependent_iff (facePolytope P hF)).mp
    (affineIndependent_face_vertices P hi hF)
  rwa [facePolytope_dim] at h

theorem simplex_subset_dimension (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (S : Finset (E n)) (hS : S ⊆ P.vertices) (hne : S.Nonempty) :
    faceDim (convexHull ℝ (S : Set (E n))) + 1 = S.card := by
  have hF := simplex_subset_isFace P hi S hS hne
  have hcard := simplex_face_vertices_card P hi hF
  have hvertices : (facePolytope P hF).vertices = S :=
    vertices_filter_convexHull_subset P S hS
  rw [hvertices] at hcard
  exact hcard.symm

/-- The graph of an actual geometric simplex is complete. -/
theorem simplex_graph_adj (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (u v : VertexType P) (hne : u ≠ v) : (polytopeGraph P).Adj u v := by
  have hne' : u.val ≠ v.val := fun h => hne (Subtype.ext h)
  have hsub : ({u.val, v.val} : Finset (E n)) ⊆ P.vertices := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨u.property, v.property⟩
  have hnePair : ({u.val, v.val} : Finset (E n)).Nonempty := by simp
  have hF := simplex_subset_isFace P hi _ hsub hnePair
  have hdF := simplex_subset_dimension P hi _ hsub hnePair
  have hc : ({u.val, v.val} : Finset (E n)).card = 2 := by simp [hne']
  refine ⟨hne, convexHull ℝ (({u.val, v.val} : Finset (E n)) : Set (E n)),
    hF, by omega, ?_, ?_⟩
  · exact subset_convexHull ℝ _ (by simp)
  · exact subset_convexHull ℝ _ (by simp)

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart19

section BundlePart20
/- Source: Cubical/Polytope/GraphConnectivity.lean -/
@[expose] public section



/-! # Connectivity of the actual convex-polytope edge graph -/

namespace LeanEval.Geometry.PlatonicClassification

variable {n : ℕ}

theorem polytopeGraph_reachable (P : ConvexPolytope n) (x y : VertexType P) :
    (polytopeGraph P).Reachable x y := by
  have hpath := balinski_light_general P x.property y.property
  have lift_path : ∀ z : E n, Relation.ReflTransGen (GeneralVertexStep P) x.val z →
      ∃ hz : z ∈ P.vertices, (polytopeGraph P).Reachable x ⟨z, hz⟩ := by
    intro z h
    induction h with
    | refl => exact ⟨x.property, SimpleGraph.Reachable.refl _⟩
    | @tail z w hzw hstep ih =>
      obtain ⟨hz, hxz⟩ := ih
      rcases hstep with ⟨hw, hzwne, F, hF, hdF, hzF, hwF⟩
      refine ⟨hw, hxz.trans ?_⟩
      apply SimpleGraph.Adj.reachable
      exact ⟨fun heq => hzwne (congrArg Subtype.val heq), F, hF, hdF, hzF, hwF⟩
  obtain ⟨hy, hxy⟩ := lift_path y.val hpath
  exact hxy

/-- Every nonempty convex polytope has a connected edge graph, including a point. -/
theorem polytopeGraph_connected (P : ConvexPolytope n) : (polytopeGraph P).Connected where
  preconnected := polytopeGraph_reachable P
  nonempty := by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨⟨v, hv⟩⟩

end LeanEval.Geometry.PlatonicClassification

end
end BundlePart20
