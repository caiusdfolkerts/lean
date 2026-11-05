module
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.InnerProductSpace.Affine
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Interval.Set.Monotone
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

set_option Elab.async false

section BundlePart0
/- Source: Cubical/Polytope/Imports.lean -/





















@[expose] public section

end
end BundlePart0

section BundlePart1
/- Source: Cubical/Polytope/Definitions.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module ChallengeDeps.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/


@[expose] public section

namespace LeanEval
namespace Geometry
namespace PlatonicClassification

/-!
# Platonic classification

§42 of Knill's *Some Fundamental Theorems in Mathematics*. The count
`p_d` of regular convex `d`-polytopes (Platonic polytopes) up to
similarity is `p_2 = ∞` (regular polygons), `p_3 = 5` (Euclid XIII —
tetrahedron, cube, octahedron, dodecahedron, icosahedron), `p_4 = 6`
(Schläfli 1850s — 5-cell, 8-cell, 16-cell, 24-cell, 120-cell, 600-cell),
and `p_d = 3` for every `d ≥ 5` (regular simplex, hypercube,
cross-polytope).

mathlib has `convexHull`, `extremePoints`, `IsExposed`, `vectorSpan`,
`AffineIsometryEquiv`, and `Set.encard`, but **no convex-polytope
datatype**, no face lattice, no regular-polytope concept, and none of the
classification counts. The Challenge ships ~1.5 pages of definitions
(`ConvexPolytope`, `dim`, `IsFace`, `Flag`, `isSymmetry`, `IsRegular`,
`Similar`, `regularPolytopes`, `regularSimilar`, `platonicCount`) on top
of mathlib.
-/

open scoped Topology

/-- The Euclidean model space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A **convex polytope** in `ℝⁿ`: the convex hull of a finite nonempty set
whose listed vertices are exactly the extreme points of the hull. -/
structure ConvexPolytope (n : ℕ) where
  vertices : Finset (E n)
  vertices_nonempty : vertices.Nonempty
  vertices_eq_extremePoints :
    (vertices : Set (E n)) =
      Set.extremePoints ℝ (convexHull ℝ ((vertices : Set (E n))))

namespace ConvexPolytope

/-- The underlying convex set of the polytope. -/
def toSet {n : ℕ} (P : ConvexPolytope n) : Set (E n) :=
  convexHull ℝ ((P.vertices : Set (E n)))

/-- The affine dimension of `P`. -/
noncomputable def dim {n : ℕ} (P : ConvexPolytope n) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ P.toSet)

/-- `P` is **full-dimensional** if `dim P = n`. -/
def IsFullDim {n : ℕ} (P : ConvexPolytope n) : Prop := P.dim = n

/-- A **face** of `P` is a nonempty exposed subset. -/
def IsFace {n : ℕ} (P : ConvexPolytope n) (F : Set (E n)) : Prop :=
  IsExposed ℝ P.toSet F ∧ F.Nonempty

/-- The affine dimension of a subset of `ℝⁿ`. -/
noncomputable def faceDim {n : ℕ} (F : Set (E n)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ F)

/-- A **flag** of a full-dimensional `n`-polytope `P`: a strictly
increasing chain `F_0 ⊂ F_1 ⊂ ⋯ ⊂ F_{n−1}` of faces with `faceDim F_k = k`. -/
structure Flag {n : ℕ} (P : ConvexPolytope n) where
  face : Fin n → Set (E n)
  isFace : ∀ k, P.IsFace (face k)
  dim_eq : ∀ k : Fin n, faceDim (face k) = k.val
  strict_mono : ∀ i j : Fin n, i < j → face i ⊂ face j

/-- Affine isometries of `ℝⁿ` — the rigid motions. -/
abbrev Isom (n : ℕ) := E n ≃ᵃⁱ[ℝ] E n

/-- `φ` is a **symmetry** of `P` if it maps `P` onto itself. -/
def isSymmetry {n : ℕ} (P : ConvexPolytope n) (φ : Isom n) : Prop :=
  ((φ : E n → E n)) '' P.toSet = P.toSet

/-- `P` is **regular** (Platonic) if it is full-dimensional and its
symmetry group acts transitively on its flags. -/
def IsRegular {n : ℕ} (P : ConvexPolytope n) : Prop :=
  P.IsFullDim ∧
    ∀ F G : P.Flag, ∃ φ : Isom n,
      P.isSymmetry φ ∧
        ∀ k : Fin n, ((φ : E n → E n)) '' F.face k = G.face k

/-- Two polytopes are **similar** when related by a positive scaling and an
affine isometry. -/
def Similar {n : ℕ} (P Q : ConvexPolytope n) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ φ : Isom n,
    Q.toSet = (fun x : E n => a • x) '' ((φ : E n → E n) '' P.toSet)

end ConvexPolytope

/-- The set of regular (Platonic) polytopes in dimension `d`. -/
def regularPolytopes (d : ℕ) : Set (ConvexPolytope d) :=
  {P | P.IsRegular}

/-- The similarity relation on regular polytopes in dimension `d`. -/
def regularSimilar (d : ℕ) (P Q : regularPolytopes d) : Prop :=
  ConvexPolytope.Similar (P : ConvexPolytope d) (Q : ConvexPolytope d)

/-- `p_d` — count of Platonic polytopes in dimension `d` up to similarity,
in `ℕ∞ = ℕ ∪ {⊤}` so `⊤` records "infinitely many". -/
noncomputable def platonicCount (d : ℕ) : ℕ∞ :=
  Set.encard {S : Set (regularPolytopes d) |
    ∃ P, S = {Q : regularPolytopes d | regularSimilar d P Q}}



end PlatonicClassification
end Geometry
end LeanEval

end
end BundlePart1

section BundlePart2
/- Source: Cubical/Polytope/FacciaArgmax.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.FacciaArgmax.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/


@[expose] public section

/-!
L3 — LA FACCIA ARGMAX VIVE SUI VERTICI (campagna #50, lato faccetta, G1-mio).

Se un funzionale lineare continuo raggiunge il suo massimo sull'hull convesso
di un insieme finito in un punto y, allora y è combinazione convessa dei SOLI
generatori che sono anch'essi argmax. Con questo, la faccia esposta 1D del
poligono (lo spigolo del fan, via A13) si schiaccia sull'hull dei vertici
argmax: l'ingresso di L2' (argmax del coseno ⟹ posizioni adiacenti).
-/

open scoped RealInnerProductSpace

namespace PlatoniciL3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Il massimo di un funzionale su un hull finito è raggiunto solo con pesi
concentrati sui generatori argmax: y sta nell'hull dei generatori argmax. -/
theorem faccia_argmax (s : Finset E) (l : E →L[ℝ] ℝ) {y : E}
    (hy : y ∈ convexHull ℝ (s : Set E))
    (hmax : ∀ w ∈ convexHull ℝ (s : Set E), l w ≤ l y) :
    y ∈ convexHull ℝ {x ∈ (s : Set E) | l x = l y} := by
  classical
  rw [Finset.convexHull_eq] at hy
  obtain ⟨w, hw0, hw1, hwy⟩ := hy
  have hM : ∀ x ∈ s, l x ≤ l y := fun x hx =>
    hmax x (subset_convexHull ℝ _ hx)
  -- rappresentazione come somma pesata
  have hyrep : y = ∑ x ∈ s, w x • x := by
    rw [← hwy, Finset.centerMass_eq_of_sum_1 _ _ hw1]
    rfl
  have hly : l y = ∑ x ∈ s, w x * l x := by
    rw [hyrep, map_sum]
    congr 1
    funext x
    rw [map_smul]
    rfl
  -- ogni generatore con peso positivo è argmax
  have hactive : ∀ x ∈ s, 0 < w x → l x = l y := by
    intro x hx hwx
    by_contra hne
    have hlt : l x < l y := lt_of_le_of_ne (hM x hx) hne
    have hsum : ∑ z ∈ s, w z * l z < ∑ z ∈ s, w z * l y := by
      apply Finset.sum_lt_sum
      · intro z hz
        exact mul_le_mul_of_nonneg_left (hM z hz) (hw0 z hz)
      · exact ⟨x, hx, mul_lt_mul_of_pos_left hlt hwx⟩
    rw [← Finset.sum_mul, hw1, one_mul] at hsum
    rw [hly] at hsum
    exact lt_irrefl _ hsum
  -- i pesi dei non-argmax sono nulli
  have hzero : ∀ x ∈ s, ¬(l x = l y) → w x = 0 := by
    intro x hx hne
    by_contra hw
    exact hne (hactive x hx (lt_of_le_of_ne (hw0 x hx) (Ne.symm hw)))
  -- restrizione al supporto argmax
  set sf : Finset E := s.filter (fun x => l x = l y) with hsfdef
  have hsub : sf ⊆ s := Finset.filter_subset _ _
  have hw1' : ∑ x ∈ sf, w x = 1 := by
    rw [← hw1]
    symm
    apply (Finset.sum_subset hsub ?_).symm
    intro x hx hnx
    apply hzero x hx
    intro heq
    exact hnx (Finset.mem_filter.mpr ⟨hx, heq⟩)
  have hyrep' : y = ∑ x ∈ sf, w x • x := by
    rw [hyrep]
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have : w x = 0 := by
      apply hzero x hx
      intro heq
      exact hnx (Finset.mem_filter.mpr ⟨hx, heq⟩)
    rw [this, zero_smul]
  -- conclusione: y ∈ hull dei generatori argmax
  have hmem : y ∈ convexHull ℝ (sf : Set E) := by
    rw [Finset.convexHull_eq]
    refine ⟨w, fun z hz => hw0 z (hsub hz), hw1', ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1']
    exact hyrep'.symm
  have hset : (sf : Set E) = {x ∈ (s : Set E) | l x = l y} := by
    rw [hsfdef]
    ext x
    simp [Finset.mem_filter]
  rw [← hset]
  exact hmem

end PlatoniciL3

end
end BundlePart2

section BundlePart3
/- Source: Cubical/Polytope/PerturbazioneFinita.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.PerturbazioneFinita.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




@[expose] public section

/-!
FASE 3A, Q0 — IL LEMMA DELLA PERTURBAZIONE FINITA (18 lug 2026).

«In un politopo, una faccia esposta di una faccia esposta è esposta.»
Falso per convessi generali; vero per politopi: se f = argmax di l su P
ed e = argmax di l' su f, allora e = argmax di l + ε·l' su P, con ε sotto
il gap minimo di l sui vertici fuori da f (il gap esiste: vertici FINITI).
Chiusura della direzione ⊇ con `faccia_argmax` (la concentrazione dei pesi
sui generatori argmax). Da Q0: spigoli delle faccette, bandiere complete,
la bandiera compagna di KG-3A1.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

open Classical in
/-- Ogni faccia (esposta, non vuota) di un politopo è l'hull dei vertici che
contiene: il pattern del tetraedro, in forma generale sul contratto. -/
theorem face_eq_hull_vertices (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) :
    f = convexHull ℝ ((P.vertices.filter (· ∈ f) : Finset (E n)) : Set (E n)) := by
  classical
  let S : Finset (E n) := P.vertices.filter (· ∈ f)
  have hPcompact : IsCompact P.toSet :=
    (P.vertices.finite_toSet.isCompact_convexHull ℝ)
  have hFcompact : IsCompact f := hf.1.isCompact hPcompact
  have hFconvex : Convex ℝ f := hf.1.convex (convex_convexHull ℝ _)
  have hKM := closure_convexHull_extremePoints hFcompact hFconvex
  have hext : f.extremePoints ℝ = (S : Set (E n)) := by
    rw [hf.1.isExtreme.extremePoints_eq]
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff]
    change (x ∈ f ∧ x ∈ P.toSet.extremePoints ℝ) ↔
      x ∈ P.vertices ∧ x ∈ f
    rw [ConvexPolytope.toSet, ← P.vertices_eq_extremePoints]
    tauto
  calc
    f = closure (convexHull ℝ (f.extremePoints ℝ)) := hKM.symm
    _ = closure (convexHull ℝ (S : Set (E n))) := by rw [hext]
    _ = convexHull ℝ (S : Set (E n)) :=
      (S.finite_toSet.isClosed_convexHull ℝ).closure_eq
    _ = convexHull ℝ
        ((P.vertices.filter (· ∈ f) : Finset (E n)) : Set (E n)) := rfl

open Classical in
/-- Un funzionale limitato sui vertici è limitato sul corpo. -/
theorem le_su_toSet (P : ConvexPolytope n) (g : E n →L[ℝ] ℝ) {c : ℝ}
    (hv : ∀ v ∈ (P.vertices : Set (E n)), g v ≤ c) :
    ∀ x ∈ P.toSet, g x ≤ c := by
  intro x hx
  have hsub : (P.vertices : Set (E n)) ⊆ {z : E n | g z ≤ c} := hv
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear g.toLinearMap) c) hx

/-- Q0, IL LEMMA-CHIAVE: una faccia esposta non vuota di una faccia di un
politopo è una faccia del politopo. -/
theorem isFace_of_isExposed_isFace (P : ConvexPolytope n)
    {f e : Set (E n)} (hf : P.IsFace f) (he : IsExposed ℝ f e)
    (hene : e.Nonempty) : P.IsFace e := by
  classical
  obtain ⟨l, hl⟩ := hf.1 hf.2
  obtain ⟨l', hl'⟩ := he hene
  have hene' := hene
  obtain ⟨x₀, hx₀⟩ := hene'
  have hx₀f : x₀ ∈ f := by rw [hl'] at hx₀; exact hx₀.1
  have hx₀T : x₀ ∈ P.toSet := by rw [hl] at hx₀f; exact hx₀f.1
  -- il valore comune di l su f
  set M : ℝ := l x₀ with hM
  have hlf : ∀ z ∈ f, l z = M := by
    intro z hz
    rw [hl] at hz hx₀f
    exact le_antisymm (hx₀f.2 z hz.1) (hz.2 x₀ hx₀f.1)
  have hlmax : ∀ y ∈ P.toSet, l y ≤ M := by
    intro y hy
    rw [hl] at hx₀f
    exact hx₀f.2 y hy
  -- caso A: tutti i vertici stanno in f ⟹ f = toSet
  by_cases hA : ∀ v ∈ P.vertices, v ∈ f
  · have hTf : P.toSet ⊆ f := by
      have hsub : (P.vertices : Set (E n)) ⊆ f := fun v hv =>
        hA v (by exact_mod_cast hv)
      have hconv : Convex ℝ f := hf.1.convex (convex_convexHull ℝ _)
      exact convexHull_min hsub hconv
    have hfT : f = P.toSet := by
      apply Set.Subset.antisymm ?_ hTf
      rw [hl]; exact fun z hz => hz.1
    refine ⟨?_, hene⟩
    intro _
    refine ⟨l', ?_⟩
    rw [hl', hfT]
  -- caso B: c'è un vertice fuori da f
  · push_neg at hA
    obtain ⟨v₀, hv₀V, hv₀f⟩ := hA
    set Vout : Finset (E n) := P.vertices.filter (· ∉ f) with hVout
    have hVoutne : Vout.Nonempty := ⟨v₀, by simp [hVout, hv₀V, hv₀f]⟩
    -- il gap δ
    set mout : ℝ := (Vout.image (fun v => l v)).max'
      (hVoutne.image _) with hmout
    have hmout_lt : mout < M := by
      have : ∀ b ∈ Vout.image (fun v => l v), b < M := by
        intro b hb
        obtain ⟨v, hvin, rfl⟩ := Finset.mem_image.mp hb
        have hvV : v ∈ P.vertices := (Finset.mem_filter.mp hvin).1
        have hvnf : v ∉ f := (Finset.mem_filter.mp hvin).2
        have hle : l v ≤ M := hlmax v (subset_convexHull ℝ _ (by exact_mod_cast hvV))
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exfalso
          apply hvnf
          rw [hl]
          exact ⟨subset_convexHull ℝ _ (by exact_mod_cast hvV),
            fun y hy => h ▸ hlmax y hy⟩
      rw [hmout]
      exact (Finset.max'_lt_iff _ (hVoutne.image _)).mpr this
    set δ : ℝ := M - mout with hδ
    have hδpos : 0 < δ := by simp [hδ]; linarith
    -- il tetto C di |l'| sui vertici
    have hVne : P.vertices.Nonempty := P.vertices_nonempty
    set C : ℝ := (P.vertices.image (fun v => |l' v|)).max'
      (hVne.image _) with hC
    have hCnneg : 0 ≤ C := by
      obtain ⟨v, hv⟩ := hVne
      have : |l' v| ∈ P.vertices.image (fun v => |l' v|) :=
        Finset.mem_image_of_mem _ hv
      rw [hC]
      exact le_trans (abs_nonneg (l' v))
        (Finset.le_max' (P.vertices.image (fun w => |l' w|)) (|l' v|) this)
    have hl'le : ∀ x ∈ P.toSet, l' x ≤ C := by
      apply le_su_toSet
      intro v hv
      have hvV : v ∈ P.vertices := by exact_mod_cast hv
      have hCb : |l' v| ≤ C := by
        rw [hC]
        exact Finset.le_max' (P.vertices.image (fun w => |l' w|)) (|l' v|)
          (Finset.mem_image_of_mem (fun w => |l' w|) hvV)
      linarith [le_abs_self (l' v)]
    have hl'ge : ∀ x ∈ P.toSet, -C ≤ l' x := by
      have h2 : ∀ x ∈ P.toSet, (-l') x ≤ C := by
        apply le_su_toSet
        intro v hv
        have hvV : v ∈ P.vertices := by exact_mod_cast hv
        have h2a : |l' v| ≤ C := by
          rw [hC]
          exact Finset.le_max' (P.vertices.image (fun w => |l' w|)) (|l' v|)
            (Finset.mem_image_of_mem (fun w => |l' w|) hvV)
        have h2b := neg_abs_le (l' v)
        simp only [ContinuousLinearMap.neg_apply]
        linarith
      intro x hx
      have := h2 x hx
      simp only [ContinuousLinearMap.neg_apply] at this
      linarith
    -- la perturbazione
    set ε : ℝ := δ / (2 * C + 1) with hε
    have hεpos : 0 < ε := div_pos hδpos (by linarith)
    have h2C1 : (0:ℝ) < 2 * C + 1 := by linarith
    have hεδ : ε * (2 * C + 1) = δ := by
      rw [hε]
      field_simp
    have hεC : 2 * ε * C < δ := by nlinarith
    -- il funzionale perturbato
    set L : E n →L[ℝ] ℝ := l + ε • l' with hLdef
    have hLapp : ∀ x, L x = l x + ε * l' x := by
      intro x
      simp [hLdef, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
    refine ⟨?_, hene⟩
    intro _
    refine ⟨L, ?_⟩
    ext x
    constructor
    · intro hx
      have hxf : x ∈ f := by rw [hl'] at hx; exact hx.1
      have hxT : x ∈ P.toSet := by rw [hl] at hxf; exact hxf.1
      refine ⟨hxT, ?_⟩
      intro y hy
      have hvert : ∀ v ∈ (P.vertices : Set (E n)), L v ≤ L x := by
        intro v hvS
        have hvV : v ∈ P.vertices := by exact_mod_cast hvS
        have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hvS
        by_cases hvf : v ∈ f
        · have h1 : l v = M := hlf v hvf
          have h2 : l' v ≤ l' x := by
            rw [hl'] at hx
            exact hx.2 v hvf
          rw [hLapp, hLapp, h1, hlf x hxf]
          nlinarith
        · have h1 : l v ≤ mout := by
            rw [hmout]
            exact Finset.le_max' (Vout.image (fun w => l w)) (l v)
              (Finset.mem_image_of_mem (fun w => l w) (by simp [hVout, hvV, hvf]))
          have h2 : l' v ≤ C := by
            have hb : |l' v| ≤ C := by
              rw [hC]
              exact Finset.le_max' (P.vertices.image (fun w => |l' w|)) (|l' v|)
                (Finset.mem_image_of_mem (fun w => |l' w|) hvV)
            linarith [le_abs_self (l' v)]
          have h3 : -C ≤ l' x := hl'ge x hxT
          rw [hLapp, hLapp, hlf x hxf]
          have hmoutδ : mout = M - δ := by rw [hδ]; ring
          nlinarith
      exact le_su_toSet P L hvert y hy
    · rintro ⟨hxT, hxmax⟩
      have hxhull := PlatoniciL3.faccia_argmax P.vertices L
        (y := x) hxT (fun w hw => hxmax w hw)
      have hVL : {z ∈ (P.vertices : Set (E n)) | L z = L x} ⊆ e := by
        rintro v ⟨hvS, hvL⟩
        have hvV : v ∈ P.vertices := by exact_mod_cast hvS
        have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hvS
        have hcomp : L x₀ ≤ L x := hxmax x₀ hx₀T
        have hLx₀ : L x₀ = M + ε * l' x₀ := by
          rw [hLapp, hM]
        have hvf : v ∈ f := by
          by_contra hvnf
          have h1 : l v ≤ mout := by
            rw [hmout]
            exact Finset.le_max' (Vout.image (fun w => l w)) (l v)
              (Finset.mem_image_of_mem (fun w => l w) (by simp [hVout, hvV, hvnf]))
          have h2 : l' v ≤ C := by
            have hb : |l' v| ≤ C := by
              rw [hC]
              exact Finset.le_max' (P.vertices.image (fun w => |l' w|)) (|l' v|)
                (Finset.mem_image_of_mem (fun w => |l' w|) hvV)
            linarith [le_abs_self (l' v)]
          have h3 : -C ≤ l' x₀ := hl'ge x₀ hx₀T
          have h5 : L v = l v + ε * l' v := hLapp v
          have hmoutδ : mout = M - δ := by rw [hδ]; ring
          rw [hvL] at h5
          nlinarith
        have hlv : l v = M := hlf v hvf
        have h7 : L x₀ ≤ L v := by rw [hvL]; exact hcomp
        rw [hLapp, hLapp, hlv, hM] at h7
        have h8 : l' x₀ ≤ l' v := by
          have h6 : ε * l' x₀ ≤ ε * l' v := by linarith
          exact le_of_mul_le_mul_left h6 hεpos
        rw [hl']
        refine ⟨hvf, ?_⟩
        intro y hyf
        have h9 : l' y ≤ l' x₀ := by
          rw [hl'] at hx₀
          exact hx₀.2 y hyf
        linarith
      have hecvx : Convex ℝ e := he.convex (hf.1.convex (convex_convexHull ℝ _))
      have hsub : convexHull ℝ {z ∈ (P.vertices : Set (E n)) | L z = L x} ⊆ e :=
        convexHull_min hVL hecvx
      exact hsub hxhull

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart3

section BundlePart4
/- Source: Cubical/Polytope/SottoPolitopo.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.SottoPolitopo.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




@[expose] public section

/-!
FASE 3A, Q2 — LA FACCIA COME SOTTO-POLITOPO (18 lug 2026).

Il motore della ricorsione per le bandiere in OGNI dimensione: una faccia f
di un politopo P, coi vertici filtrati, è essa stessa un `ConvexPolytope`
(i suoi estremi sono esattamente i vertici di P dentro f). Le facce del
sotto-politopo sono facce di P (Q0) e viceversa per restrizione del
funzionale. Con questo, l'esistenza delle bandiere scende di dimensione
in dimensione.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

open Classical in
/-- Una faccia di un politopo, vista come politopo (vertici filtrati). -/
noncomputable def facePolytope (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) : ConvexPolytope n where
  vertices := P.vertices.filter (· ∈ f)
  vertices_nonempty := by
    obtain ⟨x, hx⟩ := hf.2
    have hfe := face_eq_hull_vertices P hf
    rw [hfe] at hx
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at hx
    simp at hx
  vertices_eq_extremePoints := by
    have hfe := face_eq_hull_vertices P hf
    rw [← hfe, hf.1.isExtreme.extremePoints_eq]
    ext x
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hxV, hxf⟩
      refine ⟨hxf, ?_⟩
      have h1 : x ∈ (P.vertices : Set (E n)) := by exact_mod_cast hxV
      rw [P.vertices_eq_extremePoints] at h1
      exact h1
    · rintro ⟨hxf, hxe⟩
      have h1 : x ∈ (P.vertices : Set (E n)) := by
        rw [P.vertices_eq_extremePoints]
        exact hxe
      exact ⟨by exact_mod_cast h1, hxf⟩

open Classical in
theorem facePolytope_toSet (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) : (facePolytope P hf).toSet = f :=
  (face_eq_hull_vertices P hf).symm

open Classical in
/-- Eredità (su): una faccia del sotto-politopo è una faccia del politopo. -/
theorem isFace_of_facePolytope (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) {g : Set (E n)}
    (hg : (facePolytope P hf).IsFace g) : P.IsFace g := by
  have h1 : IsExposed ℝ f g := by
    rw [← facePolytope_toSet P hf]
    exact hg.1
  exact isFace_of_isExposed_isFace P hf h1 hg.2

open Classical in
/-- Eredità (giù): una faccia di P contenuta in f è faccia del sotto-politopo. -/
theorem facePolytope_isFace_of (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) {g : Set (E n)} (hg : P.IsFace g)
    (hsub : g ⊆ f) : (facePolytope P hf).IsFace g := by
  refine ⟨?_, hg.2⟩
  have hfT : f ⊆ P.toSet := by
    obtain ⟨lf, hlf⟩ := hf.1 hf.2
    rw [hlf]
    exact fun z hz => hz.1
  intro hne
  obtain ⟨l, hl⟩ := hg.1 hne
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀g : x₀ ∈ g := hx₀
  refine ⟨l, ?_⟩
  rw [facePolytope_toSet P hf]
  ext x
  constructor
  · intro hx
    have hxg := hx
    rw [hl] at hxg
    refine ⟨hsub hx, ?_⟩
    intro y hy
    exact hxg.2 y (hfT hy)
  · rintro ⟨hxf, hxmax⟩
    rw [hl]
    have hx₀f : x₀ ∈ f := hsub hx₀g
    have hx₀m := hxmax x₀ hx₀f
    rw [hl] at hx₀g
    refine ⟨hfT hxf, ?_⟩
    intro y hy
    calc l y ≤ l x₀ := hx₀g.2 y hy
      _ ≤ l x := hx₀m

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart4

section BundlePart5
/- Source: Cubical/Polytope/Faces.lean -/



@[expose] public section

/-!
# Finite face sets of genuine convex polytopes

These results concern exposed geometric faces of a convex hull.  No
combinatorial incidence or face-count property is assumed in the definitions.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- A finite convex polytope has only finitely many nonempty faces. -/
theorem finite_isFace (P : ConvexPolytope n) :
    Set.Finite {F : Set (E n) | P.IsFace F} := by
  classical
  apply (P.vertices.powerset.finite_toSet.image
    (fun s : Finset (E n) => convexHull ℝ (s : Set (E n)))).subset
  intro F hF
  refine ⟨P.vertices.filter (· ∈ F), ?_, ?_⟩
  · exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · exact (face_eq_hull_vertices P hF).symm

/-- Geometric faces are determined by the vertices they contain. -/
theorem face_eq_iff_vertices_eq (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G) :
    F = G ↔ (∀ v ∈ P.vertices, v ∈ F ↔ v ∈ G) := by
  classical
  constructor
  · intro h v hv
    rw [h]
  · intro h
    rw [face_eq_hull_vertices P hF, face_eq_hull_vertices P hG]
    congr 2
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, hvF⟩
      exact ⟨hv, (h v hv).mp hvF⟩
    · rintro ⟨hv, hvG⟩
      exact ⟨hv, (h v hv).mpr hvG⟩

/-- Nonempty intersections of faces are common faces, geometrically. -/
theorem isFace_inter (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hne : (F ∩ G).Nonempty) : P.IsFace (F ∩ G) :=
  ⟨hF.1.inter hG.1, hne⟩

/-- All nonempty faces, represented as geometric subsets. -/
noncomputable def faceSet (P : ConvexPolytope n) : Finset (Set (E n)) :=
  (finite_isFace P).toFinset

@[simp] theorem mem_faceSet (P : ConvexPolytope n) (F : Set (E n)) :
    F ∈ faceSet P ↔ P.IsFace F := by
  classical
  simp [faceSet]

/-- The number of geometric faces of affine dimension `i`. -/
noncomputable def faceNumber (P : ConvexPolytope n) (i : ℕ) : ℕ := by
  classical
  exact ((faceSet P).filter (fun F => faceDim F = i)).card

end LeanEval.Geometry.PlatonicClassification

end
end BundlePart5

section BundlePart6
/- Source: Cubical/Polytope/VerticiEsposti.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.VerticiEsposti.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




@[expose] public section

/-!
FASE 3A, Q1 — I VERTICI SONO FACCE ESPOSTE (18 lug 2026).

Primo gradino dell'esistenza delle bandiere: per ogni vertice v di un
politopo, {v} è una faccia (esposta, non vuota). Dimostrazione: v è un punto
estremo, quindi NON sta nell'hull degli altri vertici (altrimenti l'hull
collasserebbe e v sarebbe tra i punti estremi di un hull che non lo
contiene); Hahn-Banach geometrico separa v da quell'hull compatto; l'argmax
del separatore si concentra su v (faccia_argmax).
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

open Classical in
/-- Un vertice non sta nell'hull degli altri vertici. -/
theorem vertex_notMem_hull_erase (P : ConvexPolytope n) {v : E n}
    (hv : v ∈ P.vertices) :
    v ∉ convexHull ℝ ((P.vertices.erase v : Finset (E n)) : Set (E n)) := by
  intro hmem
  have hsub : (P.vertices : Set (E n))
      ⊆ convexHull ℝ ((P.vertices.erase v : Finset (E n)) : Set (E n)) := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv; exact hmem
    · exact subset_convexHull ℝ _ (by
        exact_mod_cast Finset.mem_erase.mpr ⟨hwv, by exact_mod_cast hw⟩)
  have hhull : convexHull ℝ ((P.vertices : Finset (E n)) : Set (E n))
      = convexHull ℝ ((P.vertices.erase v : Finset (E n)) : Set (E n)) := by
    apply Set.Subset.antisymm
    · exact convexHull_min hsub (convex_convexHull ℝ _)
    · apply convexHull_mono
      intro w hw
      have := Finset.erase_subset (s := P.vertices) (a := v)
      exact_mod_cast this (by exact_mod_cast hw)
  have hvext : v ∈ (convexHull ℝ ((P.vertices : Finset (E n)) : Set (E n))).extremePoints ℝ := by
    rw [← P.vertices_eq_extremePoints]
    exact_mod_cast hv
  rw [hhull] at hvext
  have hin : v ∈ ((P.vertices.erase v : Finset (E n)) : Set (E n)) :=
    extremePoints_convexHull_subset hvext
  have : v ∈ P.vertices.erase v := by exact_mod_cast hin
  exact (Finset.mem_erase.mp this).1 rfl

open Classical in
/-- Q1: ogni vertice è una faccia (esposta, non vuota) del politopo. -/
theorem vertex_isFace (P : ConvexPolytope n) {v : E n}
    (hv : v ∈ P.vertices) : P.IsFace ({v} : Set (E n)) := by
  classical
  refine ⟨?_, Set.singleton_nonempty v⟩
  intro _
  by_cases hK : (P.vertices.erase v).Nonempty
  · -- separazione di Hahn-Banach dal compatto hull(altri)
    set K : Set (E n) :=
      convexHull ℝ ((P.vertices.erase v : Finset (E n)) : Set (E n)) with hKdef
    have hKconv : Convex ℝ K := convex_convexHull ℝ _
    have hKclosed : IsClosed K :=
      (P.vertices.erase v).finite_toSet.isClosed_convexHull ℝ
    have hvK : v ∉ K := vertex_notMem_hull_erase P hv
    obtain ⟨l, u, hlt, hu⟩ :=
      geometric_hahn_banach_closed_point hKconv hKclosed hvK
    refine ⟨l, ?_⟩
    ext x
    constructor
    · rintro rfl
      refine ⟨subset_convexHull ℝ _ (by exact_mod_cast hv), ?_⟩
      -- l ≤ l v su tutto il corpo, via i vertici
      intro y hy
      have hvert : ∀ w ∈ (P.vertices : Set (E n)), l w ≤ l x := by
        intro w hw
        by_cases hwv : w = x
        · subst hwv; exact le_refl _
        · have hwK : w ∈ K := subset_convexHull ℝ _ (by
            exact_mod_cast Finset.mem_erase.mpr ⟨hwv, by exact_mod_cast hw⟩)
          exact le_of_lt (lt_trans (hlt w hwK) hu)
      exact le_su_toSet P l hvert y hy
    · rintro ⟨hxT, hxmax⟩
      have hxhull := PlatoniciL3.faccia_argmax P.vertices l
        (y := x) hxT (fun w hw => hxmax w hw)
      have hset : {z ∈ (P.vertices : Set (E n)) | l z = l x} ⊆ ({v} : Set (E n)) := by
        rintro w ⟨hwS, hwl⟩
        have hwV : w ∈ P.vertices := by exact_mod_cast hwS
        by_contra hwv
        have hwv' : w ≠ v := by simpa using hwv
        have hwK : w ∈ K := subset_convexHull ℝ _ (by
          exact_mod_cast Finset.mem_erase.mpr ⟨hwv', hwV⟩)
        -- l w < u < l v ≤ l x = l w: assurdo
        have h1 : l w < u := hlt w hwK
        have h2 : u < l v := hu
        have h3 : l v ≤ l x := hxmax v (subset_convexHull ℝ _ (by exact_mod_cast hv))
        rw [hwl] at h1
        linarith
      have : convexHull ℝ {z ∈ (P.vertices : Set (E n)) | l z = l x}
          ⊆ ({v} : Set (E n)) := by
        have hconv : Convex ℝ ({v} : Set (E n)) := convex_singleton v
        exact convexHull_min hset hconv
      exact this hxhull
  · -- vertici = {v}: il corpo È {v}, esposto dal funzionale nullo
    have hverts : P.vertices = {v} := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        by_contra hwv
        have : w ∈ P.vertices.erase v :=
          Finset.mem_erase.mpr ⟨by simpa using hwv, hw⟩
        exact hK ⟨w, this⟩
      · have h1 : 1 ≤ P.vertices.card :=
          Finset.card_pos.mpr ⟨v, hv⟩
        simpa using h1
    have hT : P.toSet = ({v} : Set (E n)) := by
      show convexHull ℝ ((P.vertices : Finset (E n)) : Set (E n)) = _
      rw [hverts]
      simp
    refine ⟨0, ?_⟩
    rw [hT]
    ext x
    simp

end PlatonicClassification
end Geometry
end LeanEval
end
end
end BundlePart6

section BundlePart7
/- Source: Cubical/Polytope/DimStretta.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.DimStretta.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/





@[expose] public section

/-!
FASE 3A, Q3-S3b — FACCIA STRETTA ⟹ DIMENSIONE STRETTA (18 lug 2026).

Se f ⊊ g sono facce di un politopo, dim f < dim g. Via il sotto-politopo:
f è faccia propria di g; il suo espositore l non è costante su g (il vertice
fuori sta sotto il massimo); se le dimensioni fossero pari, gli span affini
coinciderebbero e l sarebbe costante su aff(g): assurdo.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

open Classical in
/-- S3b: tra facce, l'inclusione stretta forza la dimensione stretta. -/
theorem faceDim_lt_of_ssubset (P : ConvexPolytope n) {f g : Set (E n)}
    (hf : P.IsFace f) (hg : P.IsFace g) (hsub : f ⊂ g) :
    faceDim f < faceDim g := by
  classical
  -- f è faccia del sotto-politopo di g
  have hfQ : (facePolytope P hg).IsFace f :=
    facePolytope_isFace_of P hg hf hsub.1
  -- un vertice di g fuori da f
  have hgconv : Convex ℝ g := hg.1.convex (convex_convexHull ℝ _)
  have hout : ∃ w ∈ (facePolytope P hg).vertices, w ∉ f := by
    by_contra hall
    push_neg at hall
    have hsubg : g ⊆ f := by
      have h1 : g = (facePolytope P hg).toSet := (facePolytope_toSet P hg).symm
      rw [h1]
      have hsubv : ((facePolytope P hg).vertices : Set (E n)) ⊆ f := fun w hw =>
        hall w (by exact_mod_cast hw)
      have hfconv : Convex ℝ f := hf.1.convex (convex_convexHull ℝ _)
      exact convexHull_min hsubv hfconv
    exact hsub.2 hsubg
  obtain ⟨w, hwV, hwf⟩ := hout
  have hwg : w ∈ g := by
    have h1 : w ∈ (facePolytope P hg).toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hwV)
    rwa [facePolytope_toSet P hg] at h1
  -- l'espositore di f dentro g
  obtain ⟨l, hl⟩ := hfQ.1 hf.2
  rw [facePolytope_toSet P hg] at hl
  obtain ⟨x₀, hx₀⟩ := hf.2
  have hx₀' := hx₀
  rw [hl] at hx₀'
  set M : ℝ := l x₀ with hM
  have hlf : ∀ z ∈ f, l z = M := by
    intro z hz
    have hz' := hz
    rw [hl] at hz'
    exact le_antisymm (hx₀'.2 z hz'.1) (hz'.2 x₀ hx₀'.1)
  have hlw : l w < M := by
    rcases lt_or_eq_of_le (hx₀'.2 w hwg) with h | h
    · exact h
    · exfalso
      apply hwf
      rw [hl]
      exact ⟨hwg, fun y hy => h ▸ hx₀'.2 y hy⟩
  -- dimensioni: ≤ dalla monotonia; se pari, span affini uguali
  have hmono : vectorSpan ℝ f ≤ vectorSpan ℝ g :=
    vectorSpan_mono ℝ hsub.1
  have hle : faceDim f ≤ faceDim g := Submodule.finrank_mono hmono
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hspan_eq : vectorSpan ℝ f = vectorSpan ℝ g := by
      apply Submodule.eq_of_le_of_finrank_le hmono
      show faceDim g ≤ faceDim f
      exact le_of_eq heq.symm
    have haff_le : affineSpan ℝ f ≤ affineSpan ℝ g := affineSpan_mono ℝ hsub.1
    have haff_eq : affineSpan ℝ f = affineSpan ℝ g := by
      have hx₀m : x₀ ∈ affineSpan ℝ f := subset_affineSpan ℝ _ hx₀
      apply le_antisymm haff_le
      intro y hy
      have hdir : (affineSpan ℝ f).direction = (affineSpan ℝ g).direction := by
        rw [direction_affineSpan, direction_affineSpan, hspan_eq]
      have h1 : y -ᵥ x₀ ∈ (affineSpan ℝ g).direction :=
        AffineSubspace.vsub_mem_direction hy (haff_le hx₀m)
      rw [← hdir] at h1
      have := AffineSubspace.vadd_mem_of_mem_direction h1 hx₀m
      simpa using this
    -- l è costante su affineSpan f = affineSpan g ∋ w: assurdo
    have hconst : ∀ y ∈ affineSpan ℝ f, l y = M := by
      intro y hy
      have heqon : Set.EqOn (⇑l.toLinearMap.toAffineMap)
          (⇑(AffineMap.const ℝ (E n) M)) f := by
        intro z hz
        simp [hlf z hz]
      have h2 := AffineMap.eqOn_affineSpan (k := ℝ) heqon  -- nome da verificare
      have := h2 hy
      simpa using this
    have hw_aff : w ∈ affineSpan ℝ f := by
      rw [haff_eq]
      exact subset_affineSpan ℝ _ hwg
    have := hconst w hw_aff
    linarith

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart7

section BundlePart8
/- Source: Cubical/Polytope/DueFunzionali.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.DueFunzionali.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/



@[expose] public section

/-!
FASE 3A, Q3-S3a — DUE FUNZIONALI INDIPENDENTI DALLA CODIMENSIONE ≥ 2.

Il pezzo di algebra lineare dell'interpolazione: se U ≤ W con
finrank U + 2 ≤ finrank W, il complemento ortogonale di U dentro W contiene
due vettori linearmente indipendenti (i cui funzionali interni si annullano
su U). Serviranno per i due perni del trucco di S3.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

variable {n : ℕ}

/-- Dalla codimensione ≥ 2: due vettori indipendenti in W ⊓ Uᗮ. -/
theorem exists_two_orthogonal_indep {U W : Submodule ℝ (E n)}
    (hUW : U ≤ W) (hcodim : Module.finrank ℝ U + 2 ≤ Module.finrank ℝ W) :
    ∃ w₁ w₂ : E n, w₁ ∈ W ∧ w₂ ∈ W ∧
      (∀ u ∈ U, ⟪w₁, u⟫ = 0) ∧ (∀ u ∈ U, ⟪w₂, u⟫ = 0) ∧
      LinearIndependent ℝ ![w₁, w₂] := by
  classical
  -- il complemento ortogonale relativo V := Uᗮ ⊓ W ha finrank ≥ 2
  set V : Submodule ℝ (E n) := Uᗮ ⊓ W with hV
  have hdim : Module.finrank ℝ U + Module.finrank ℝ V = Module.finrank ℝ W := by
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal hUW
    rw [hV]
    rw [inf_comm] at h1 ⊢
    exact h1
  have hVdim : 2 ≤ Module.finrank ℝ V := by omega
  -- due vettori indipendenti in V
  obtain ⟨v, hvV, hv0⟩ : ∃ v ∈ V, v ≠ 0 := by
    by_contra hall
    push_neg at hall
    have : V = ⊥ := by
      ext x
      simp only [Submodule.mem_bot]
      exact ⟨fun hx => hall x hx, fun hx => hx ▸ V.zero_mem⟩
    rw [this] at hVdim
    simp at hVdim
  -- lo span di v dentro V non è tutto V (finrank 1 < 2): esiste v' fuori
  have hspan_lt : Module.finrank ℝ (Submodule.span ℝ {v}) < Module.finrank ℝ V := by
    rw [finrank_span_singleton hv0]
    omega
  obtain ⟨v', hv'V, hv'span⟩ : ∃ v' ∈ V, v' ∉ Submodule.span ℝ {v} := by
    by_contra hall
    push_neg at hall
    have hle : V ≤ Submodule.span ℝ {v} := fun x hx => hall x hx
    have := Submodule.finrank_mono hle
    omega
  refine ⟨v, v', hvV.2, hv'V.2, ?_, ?_, ?_⟩
  · intro u hu
    have h1 : v ∈ Uᗮ := hvV.1
    have h2 := (Submodule.mem_orthogonal U v).mp h1 u hu
    rw [real_inner_comm]
    exact h2
  · intro u hu
    have h1 : v' ∈ Uᗮ := hv'V.1
    have h2 := (Submodule.mem_orthogonal U v').mp h1 u hu
    rw [real_inner_comm]
    exact h2
  · rw [linearIndependent_fin2]
    constructor
    · intro h
      have h' : v' = 0 := h
      apply hv'span
      rw [h']
      exact Submodule.zero_mem _
    · intro a h
      have h' : v = a • v' := h.symm
      by_cases ha : a = 0
      · subst ha
        simp at h'
        exact hv0 h'
      · apply hv'span
        have hvv : v' = a⁻¹ • v := by
          rw [h', smul_smul, inv_mul_cancel₀ ha, one_smul]
        rw [hvv]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

end PlatonicClassification
end Geometry
end LeanEval
end
end
end BundlePart8

section BundlePart9
/- Source: Cubical/Polytope/Perno.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Perno.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/






@[expose] public section

/-!
FASE 3A, Q3-S1 — IL PERNO (18 lug 2026).

Sopra ogni faccia propria di un politopo c'è una faccia strettamente più
grande.  Il secondo funzionale è costruito col residuo ortogonale rispetto
alla direzione affine della faccia; il tempo di perturbazione è il minimo
dei rapporti critici sui vertici sui quali quel funzionale cresce.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

open Classical in
/-- Q3-S1, il passo di perno: ogni faccia propria è contenuta strettamente
in un'altra faccia. -/
theorem perno (P : ConvexPolytope n) {f : Set (E n)} (hf : P.IsFace f)
    (hproper : ∃ v ∈ P.vertices, v ∉ f) :
    ∃ f' : Set (E n), P.IsFace f' ∧ f ⊂ f' := by
  classical
  obtain ⟨l, hl⟩ := hf.1 hf.2
  obtain ⟨p₀, hp₀f⟩ := hf.2
  obtain ⟨u, huV, huf⟩ := hproper
  have hp₀T : p₀ ∈ P.toSet := by
    rw [hl] at hp₀f
    exact hp₀f.1
  have huT : u ∈ P.toSet :=
    subset_convexHull ℝ _ (by exact_mod_cast huV)

  -- Il valore del primo funzionale sulla faccia.
  set M : ℝ := l p₀ with hM
  have hlf : ∀ z ∈ f, l z = M := by
    intro z hz
    rw [hl] at hz hp₀f
    exact le_antisymm (hp₀f.2 z hz.1) (hz.2 p₀ hp₀f.1)
  have hlmax : ∀ y ∈ P.toSet, l y ≤ M := by
    intro y hy
    rw [hl] at hp₀f
    exact hp₀f.2 y hy
  have hl_strict : ∀ v ∈ P.vertices, v ∉ f → l v < M := by
    intro v hvV hvf
    have hvT : v ∈ P.toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hvV)
    have hvle := hlmax v hvT
    rcases lt_or_eq_of_le hvle with h | h
    · exact h
    · exfalso
      apply hvf
      rw [hl]
      exact ⟨hvT, fun y hy => h ▸ hlmax y hy⟩
  have hlu : l u < M := hl_strict u huV huf

  -- Poiché l è costante su f, è costante anche sul suo affine span.
  -- Il vertice esterno u è quindi automaticamente trasverso.
  have huaff : u ∉ affineSpan ℝ f := by
    intro hu
    let A : AffineSubspace ℝ (E n) :=
      AffineSubspace.mk' p₀ (LinearMap.ker l.toLinearMap)
    have hfA : f ⊆ (A : Set (E n)) := by
      intro z hz
      change z - p₀ ∈ LinearMap.ker l.toLinearMap
      rw [LinearMap.mem_ker]
      simp [hlf z hz, hM]
    have hspan : affineSpan ℝ f ≤ A := (affineSpan_le).2 hfA
    have huA := hspan hu
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker] at huA
    have hzero : l u - l p₀ = 0 := by simpa using huA
    rw [← hM] at hzero
    linarith

  -- Residuo ortogonale di u-p₀ rispetto alla direzione affine di f.
  set S : Submodule ℝ (E n) := vectorSpan ℝ f with hS
  set d : E n := u - p₀ with hd
  set w : E n := d - S.starProjection d with hw
  have hdS : d ∉ S := by
    intro hdmem
    apply huaff
    have hpaff : p₀ ∈ affineSpan ℝ f := mem_affineSpan ℝ hp₀f
    have := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan hpaff hdmem
    simpa [d] using this
  have hwne : w ≠ 0 := by
    intro hwzero
    have hzero : d - S.starProjection d = 0 := by simpa [w] using hwzero
    have hproj : S.starProjection d = d := (sub_eq_zero.mp hzero).symm
    exact hdS (Submodule.starProjection_eq_self_iff.mp hproj)

  set l₂ : E n →L[ℝ] ℝ := innerSL ℝ w with hl₂
  have hl₂const : ∀ z ∈ f, l₂ z = l₂ p₀ := by
    intro z hz
    have hzS : z - p₀ ∈ S := by
      rw [hS]
      simpa using vsub_mem_vectorSpan ℝ hz hp₀f
    have ho := Submodule.starProjection_inner_eq_zero d (z - p₀) hzS
    change inner ℝ w z = inner ℝ w p₀
    rw [← sub_eq_zero, ← inner_sub_right]
    simpa [w] using ho
  have horth : inner ℝ w (S.starProjection d) = 0 := by
    have hpS : S.starProjection d ∈ S := S.starProjection_apply_mem d
    change inner ℝ (d - S.starProjection d) (S.starProjection d) = 0
    exact Submodule.starProjection_inner_eq_zero d (S.starProjection d) hpS
  have hwd : inner ℝ w d = inner ℝ w w := by
    calc
      inner ℝ w d = inner ℝ w (w + S.starProjection d) := by
        congr 2
        simp [w]
      _ = inner ℝ w w + inner ℝ w (S.starProjection d) :=
        inner_add_right _ _ _
      _ = inner ℝ w w := by rw [horth, add_zero]
  have hl₂gap : l₂ u - l₂ p₀ = ‖w‖ ^ 2 := by
    change inner ℝ w u - inner ℝ w p₀ = ‖w‖ ^ 2
    rw [← inner_sub_right]
    change inner ℝ w d = ‖w‖ ^ 2
    rw [hwd, real_inner_self_eq_norm_sq]
  have hl₂up : l₂ p₀ < l₂ u := by
    have hn : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hwne)
    linarith

  -- Vertici sui quali l₂ cresce e relativi rapporti critici.
  set Vup : Finset (E n) :=
    P.vertices.filter (fun v => l₂ p₀ < l₂ v) with hVup
  have huUp : u ∈ Vup := by simp [hVup, huV, hl₂up]
  have hVupne : Vup.Nonempty := ⟨u, huUp⟩
  set ratio : E n → ℝ :=
    fun v => (M - l v) / (l₂ v - l₂ p₀) with hratio
  have hratio_pos : ∀ v ∈ Vup, 0 < ratio v := by
    intro v hvUp
    have hv := Finset.mem_filter.mp hvUp
    have hvnf : v ∉ f := by
      intro hvf
      have := hl₂const v hvf
      linarith
    have hnum : 0 < M - l v := by
      have := hl_strict v hv.1 hvnf
      linarith
    have hden : 0 < l₂ v - l₂ p₀ := by linarith
    rw [hratio]
    exact div_pos hnum hden
  set R : Finset ℝ := Vup.image ratio with hR
  have hRne : R.Nonempty := hVupne.image ratio
  set t : ℝ := R.min' hRne with ht
  have htpos : 0 < t := by
    have htmem : t ∈ R := by
      rw [ht]
      exact Finset.min'_mem R hRne
    obtain ⟨v, hvUp, hvt⟩ := Finset.mem_image.mp (by simpa [hR] using htmem)
    rw [← hvt]
    exact hratio_pos v hvUp

  -- Il funzionale al primo tempo critico.
  set L : E n →L[ℝ] ℝ := l + t • l₂ with hL
  have hLapp : ∀ x, L x = l x + t * l₂ x := by
    intro x
    simp [hL, smul_eq_mul]
  have hvert : ∀ v ∈ (P.vertices : Set (E n)),
      L v ≤ M + t * l₂ p₀ := by
    intro v hvS
    have hvV : v ∈ P.vertices := by exact_mod_cast hvS
    have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hvS
    by_cases hvup : l₂ p₀ < l₂ v
    · have hvUp : v ∈ Vup := by simp [hVup, hvV, hvup]
      have hratioR : ratio v ∈ R := by
        rw [hR]
        exact Finset.mem_image_of_mem ratio hvUp
      have htle : t ≤ ratio v := by
        rw [ht]
        exact Finset.min'_le R (ratio v) hratioR
      have hden : 0 < l₂ v - l₂ p₀ := by linarith
      have hmul : t * (l₂ v - l₂ p₀) ≤ M - l v := by
        calc
          t * (l₂ v - l₂ p₀) ≤ ratio v * (l₂ v - l₂ p₀) :=
            mul_le_mul_of_nonneg_right htle (le_of_lt hden)
          _ = M - l v := by
            rw [hratio]
            field_simp
      rw [hLapp]
      linarith
    · have hlv := hlmax v hvT
      have hl₂v : l₂ v ≤ l₂ p₀ := le_of_not_gt hvup
      rw [hLapp]
      nlinarith
  have hLbound : ∀ y ∈ P.toSet, L y ≤ M + t * l₂ p₀ :=
    le_su_toSet P L hvert

  -- Un vertice realizza il minimo: al tempo t entra nell'argmax.
  have htmem : t ∈ R := by
    rw [ht]
    exact Finset.min'_mem R hRne
  obtain ⟨vcrit, hvcritUp, hvcritEq⟩ :=
    Finset.mem_image.mp (by simpa [hR] using htmem)
  have hvcritV : vcrit ∈ P.vertices := (Finset.mem_filter.mp hvcritUp).1
  have hvcritGrow : l₂ p₀ < l₂ vcrit := (Finset.mem_filter.mp hvcritUp).2
  have hvcrit_notf : vcrit ∉ f := by
    intro hvcf
    have := hl₂const vcrit hvcf
    linarith
  have hvcritL : L vcrit = M + t * l₂ p₀ := by
    have hden : l₂ vcrit - l₂ p₀ ≠ 0 := by linarith
    have heq : t * (l₂ vcrit - l₂ p₀) = M - l vcrit := by
      rw [← hvcritEq, hratio]
      field_simp
    rw [hLapp]
    linarith

  set f' : Set (E n) :=
    {x ∈ P.toSet | ∀ y ∈ P.toSet, L y ≤ L x} with hf'def
  have hsub : f ⊆ f' := by
    intro x hxf
    have hxT : x ∈ P.toSet := by
      rw [hl] at hxf
      exact hxf.1
    have hLx : L x = M + t * l₂ p₀ := by
      rw [hLapp, hlf x hxf, hl₂const x hxf]
    refine ⟨hxT, ?_⟩
    intro y hy
    exact (hLbound y hy).trans_eq hLx.symm
  have hvcritT : vcrit ∈ P.toSet :=
    subset_convexHull ℝ _ (by exact_mod_cast hvcritV)
  have hvcritf' : vcrit ∈ f' := by
    refine ⟨hvcritT, ?_⟩
    intro y hy
    exact (hLbound y hy).trans_eq hvcritL.symm
  have hf'ne : f'.Nonempty := ⟨p₀, hsub hp₀f⟩
  have hf'face : P.IsFace f' := by
    refine ⟨?_, hf'ne⟩
    intro _
    refine ⟨L, ?_⟩
    rfl

  refine ⟨f', hf'face, ?_⟩
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨hsub, ?_⟩
  intro hff'
  apply hvcrit_notf
  rw [hff']
  exact hvcritf'

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart9

section BundlePart10
/- Source: Cubical/Polytope/Interpolazione.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Interpolazione.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/









@[expose] public section

/-!
FASE 3A, Q3-S3 — INTERPOLAZIONE (18 lug 2026).

Il perno viene prima reso parametrico nella direzione ortogonale `w`.
Se la nuova faccia coincide con tutto il politopo, il funzionale perturbato
e' costante sui vertici. Due direzioni indipendenti rendono impossibile che
questo caso degenere si presenti entrambe le volte.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

open Classical in
/-- Versione crescente del perno parametrico. Nel caso in cui la faccia
costruita sia tutto il corpo, conserva la costanza del funzionale sui
vertici. -/
theorem perno_parametrico_crescente (P : ConvexPolytope n) {f : Set (E n)}
    (_hf : P.IsFace f) (l : E n →L[ℝ] ℝ)
    (hl : f = {x ∈ P.toSet | ∀ y ∈ P.toSet, l y ≤ l x})
    (p₀ : E n) (hp₀f : p₀ ∈ f) (w : E n)
    (hwconst : ∀ z ∈ f, inner ℝ w z = inner ℝ w p₀)
    (hup : ∃ u ∈ P.vertices, inner ℝ w p₀ < inner ℝ w u) :
    ∃ f' : Set (E n), P.IsFace f' ∧ f ⊂ f' ∧
      (f' ≠ P.toSet ∨
        ∃ t : ℝ, 0 < t ∧ ∃ c : ℝ,
          ∀ v ∈ P.vertices, l v + t * inner ℝ w v = c) := by
  classical
  obtain ⟨u, huV, huup⟩ := hup
  have hp₀T : p₀ ∈ P.toSet := by
    rw [hl] at hp₀f
    exact hp₀f.1
  set M : ℝ := l p₀ with hM
  have hlf : ∀ z ∈ f, l z = M := by
    intro z hz
    rw [hl] at hz hp₀f
    exact le_antisymm (hp₀f.2 z hz.1) (hz.2 p₀ hp₀f.1)
  have hlmax : ∀ y ∈ P.toSet, l y ≤ M := by
    intro y hy
    rw [hl] at hp₀f
    exact hp₀f.2 y hy
  have hl_strict : ∀ v ∈ P.vertices, v ∉ f → l v < M := by
    intro v hvV hvf
    have hvT : v ∈ P.toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hvV)
    rcases lt_or_eq_of_le (hlmax v hvT) with h | h
    · exact h
    · exfalso
      apply hvf
      rw [hl]
      exact ⟨hvT, fun y hy => h ▸ hlmax y hy⟩
  have huf : u ∉ f := by
    intro h
    have := hwconst u h
    linarith

  set l₂ : E n →L[ℝ] ℝ := innerSL ℝ w with hl₂
  have hl₂const : ∀ z ∈ f, l₂ z = l₂ p₀ := by
    intro z hz
    simpa [l₂] using hwconst z hz
  have hl₂up : l₂ p₀ < l₂ u := by simpa [l₂] using huup

  set Vup : Finset (E n) :=
    P.vertices.filter (fun v => l₂ p₀ < l₂ v) with hVup
  have huUp : u ∈ Vup := by simp [hVup, huV, hl₂up]
  have hVupne : Vup.Nonempty := ⟨u, huUp⟩
  set ratio : E n → ℝ :=
    fun v => (M - l v) / (l₂ v - l₂ p₀) with hratio
  have hratio_pos : ∀ v ∈ Vup, 0 < ratio v := by
    intro v hvUp
    have hv := Finset.mem_filter.mp hvUp
    have hvnf : v ∉ f := by
      intro hvf
      have := hl₂const v hvf
      linarith
    have hnum : 0 < M - l v := by
      have := hl_strict v hv.1 hvnf
      linarith
    have hden : 0 < l₂ v - l₂ p₀ := by linarith
    rw [hratio]
    exact div_pos hnum hden
  set R : Finset ℝ := Vup.image ratio with hR
  have hRne : R.Nonempty := hVupne.image ratio
  set t : ℝ := R.min' hRne with ht
  have htpos : 0 < t := by
    have htmem : t ∈ R := by
      rw [ht]
      exact Finset.min'_mem R hRne
    obtain ⟨v, hvUp, hvt⟩ :=
      Finset.mem_image.mp (by simpa [hR] using htmem)
    rw [← hvt]
    exact hratio_pos v hvUp

  set L : E n →L[ℝ] ℝ := l + t • l₂ with hL
  have hLapp : ∀ x, L x = l x + t * l₂ x := by
    intro x
    simp [hL, smul_eq_mul]
  have hvert : ∀ v ∈ (P.vertices : Set (E n)),
      L v ≤ M + t * l₂ p₀ := by
    intro v hvS
    have hvV : v ∈ P.vertices := by exact_mod_cast hvS
    have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hvS
    by_cases hvup : l₂ p₀ < l₂ v
    · have hvUp : v ∈ Vup := by simp [hVup, hvV, hvup]
      have hratioR : ratio v ∈ R := by
        rw [hR]
        exact Finset.mem_image_of_mem ratio hvUp
      have htle : t ≤ ratio v := by
        rw [ht]
        exact Finset.min'_le R (ratio v) hratioR
      have hden : 0 < l₂ v - l₂ p₀ := by linarith
      have hmul : t * (l₂ v - l₂ p₀) ≤ M - l v := by
        calc
          t * (l₂ v - l₂ p₀) ≤ ratio v * (l₂ v - l₂ p₀) :=
            mul_le_mul_of_nonneg_right htle (le_of_lt hden)
          _ = M - l v := by
            rw [hratio]
            field_simp
      rw [hLapp]
      linarith
    · have hlv := hlmax v hvT
      have hl₂v : l₂ v ≤ l₂ p₀ := le_of_not_gt hvup
      rw [hLapp]
      nlinarith
  have hLbound : ∀ y ∈ P.toSet, L y ≤ M + t * l₂ p₀ :=
    le_su_toSet P L hvert

  have htmem : t ∈ R := by
    rw [ht]
    exact Finset.min'_mem R hRne
  obtain ⟨vcrit, hvcritUp, hvcritEq⟩ :=
    Finset.mem_image.mp (by simpa [hR] using htmem)
  have hvcritV : vcrit ∈ P.vertices := (Finset.mem_filter.mp hvcritUp).1
  have hvcritGrow : l₂ p₀ < l₂ vcrit :=
    (Finset.mem_filter.mp hvcritUp).2
  have hvcrit_notf : vcrit ∉ f := by
    intro hvcf
    have := hl₂const vcrit hvcf
    linarith
  have hvcritL : L vcrit = M + t * l₂ p₀ := by
    have hden : l₂ vcrit - l₂ p₀ ≠ 0 := by linarith
    have heq : t * (l₂ vcrit - l₂ p₀) = M - l vcrit := by
      rw [← hvcritEq, hratio]
      field_simp
    rw [hLapp]
    linarith

  set f' : Set (E n) :=
    {x ∈ P.toSet | ∀ y ∈ P.toSet, L y ≤ L x} with hf'def
  have hsub : f ⊆ f' := by
    intro x hxf
    have hxT : x ∈ P.toSet := by
      rw [hl] at hxf
      exact hxf.1
    have hLx : L x = M + t * l₂ p₀ := by
      rw [hLapp, hlf x hxf, hl₂const x hxf]
    refine ⟨hxT, ?_⟩
    intro y hy
    exact (hLbound y hy).trans_eq hLx.symm
  have hvcritT : vcrit ∈ P.toSet :=
    subset_convexHull ℝ _ (by exact_mod_cast hvcritV)
  have hvcritf' : vcrit ∈ f' := by
    refine ⟨hvcritT, ?_⟩
    intro y hy
    exact (hLbound y hy).trans_eq hvcritL.symm
  have hf'ne : f'.Nonempty := ⟨p₀, hsub hp₀f⟩
  have hf'face : P.IsFace f' := by
    refine ⟨?_, hf'ne⟩
    intro _
    exact ⟨L, rfl⟩
  have hfstrict : f ⊂ f' := by
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨hsub, ?_⟩
    intro hff'
    apply hvcrit_notf
    rw [hff']
    exact hvcritf'

  refine ⟨f', hf'face, hfstrict, ?_⟩
  by_cases hproper : f' ≠ P.toSet
  · exact Or.inl hproper
  · right
    refine ⟨t, htpos, M + t * inner ℝ w p₀, ?_⟩
    intro v hvV
    have hvT : v ∈ P.toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hvV)
    have hvf' : v ∈ f' := by rw [not_ne_iff.mp hproper]; exact hvT
    have hp₀max : L p₀ ≤ L v := hvf'.2 p₀ hp₀T
    have hLp₀ : L p₀ = M + t * l₂ p₀ := by
      rw [hLapp, hM]
    have hLv : L v = M + t * l₂ p₀ :=
      le_antisymm (hLbound v hvT) (by linarith)
    simpa [hLapp, l₂] using hLv

open Classical in
/-- Perno parametrico senza scelta di orientazione. Il coefficiente della
perturbazione e' non nullo; puo' essere negativo quando `w` va orientato nel
verso opposto. -/
theorem perno_parametrico (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) (l : E n →L[ℝ] ℝ)
    (hl : f = {x ∈ P.toSet | ∀ y ∈ P.toSet, l y ≤ l x})
    (p₀ : E n) (hp₀f : p₀ ∈ f) (w : E n)
    (hwconst : ∀ z ∈ f, inner ℝ w z = inner ℝ w p₀)
    (hvar : ∃ u ∈ P.vertices, inner ℝ w u ≠ inner ℝ w p₀) :
    ∃ f' : Set (E n), P.IsFace f' ∧ f ⊂ f' ∧
      (f' ≠ P.toSet ∨
        ∃ t : ℝ, t ≠ 0 ∧ ∃ c : ℝ,
          ∀ v ∈ P.vertices, l v + t * inner ℝ w v = c) := by
  classical
  obtain ⟨u, huV, hune⟩ := hvar
  rcases lt_or_gt_of_ne hune with hlt | hgt
  · have hup : ∃ u ∈ P.vertices,
        inner ℝ (-w) p₀ < inner ℝ (-w) u := by
      refine ⟨u, huV, ?_⟩
      simpa using hlt
    have hwconst' : ∀ z ∈ f,
        inner ℝ (-w) z = inner ℝ (-w) p₀ := by
      intro z hz
      simpa using congrArg Neg.neg (hwconst z hz)
    obtain ⟨f', hf', hff', halt⟩ :=
      perno_parametrico_crescente P hf l hl p₀ hp₀f (-w) hwconst' hup
    refine ⟨f', hf', hff', ?_⟩
    rcases halt with hproper | ⟨t, htpos, c, hc⟩
    · exact Or.inl hproper
    · right
      refine ⟨-t, by linarith, c, ?_⟩
      intro v hv
      have := hc v hv
      simpa using this
  · have hup : ∃ u ∈ P.vertices,
        inner ℝ w p₀ < inner ℝ w u := ⟨u, huV, hgt⟩
    obtain ⟨f', hf', hff', halt⟩ :=
      perno_parametrico_crescente P hf l hl p₀ hp₀f w hwconst hup
    refine ⟨f', hf', hff', ?_⟩
    rcases halt with hproper | ⟨t, htpos, c, hc⟩
    · exact Or.inl hproper
    · exact Or.inr ⟨t, ne_of_gt htpos, c, hc⟩

open Classical in
/-- Un vettore non nullo nella direzione affine del politopo induce un
funzionale interno non costante sui vertici. -/
theorem exists_vertex_inner_ne (P : ConvexPolytope n) {p w : E n}
    (hp : p ∈ P.toSet) (hw : w ∈ vectorSpan ℝ P.toSet) (hwne : w ≠ 0) :
    ∃ v ∈ P.vertices, inner ℝ w v ≠ inner ℝ w p := by
  classical
  by_contra hall
  push Not at hall
  let A : E n →ᵃ[ℝ] ℝ := (innerSL ℝ w).toLinearMap.toAffineMap
  let C : E n →ᵃ[ℝ] ℝ := AffineMap.const ℝ (E n) (inner ℝ w p)
  have hagree : Set.EqOn A C (P.vertices : Set (E n)) := by
    intro v hv
    change inner ℝ w v = inner ℝ w p
    exact hall v (by exact_mod_cast hv)
  have hspan := AffineMap.eqOn_affineSpan (k := ℝ) hagree
  have hpaff : p ∈ affineSpan ℝ (P.vertices : Set (E n)) := by
    have hpaffT : p ∈ affineSpan ℝ P.toSet :=
      subset_affineSpan ℝ P.toSet hp
    simpa [ConvexPolytope.toSet] using hpaffT
  have hwdir : w ∈ (affineSpan ℝ (P.vertices : Set (E n))).direction := by
    rw [← direction_affineSpan] at hw
    simpa [ConvexPolytope.toSet] using hw
  have hpw : w +ᵥ p ∈ affineSpan ℝ (P.vertices : Set (E n)) :=
    AffineSubspace.vadd_mem_of_mem_direction hwdir hpaff
  have h1 := hspan hpw
  have h2 := hspan hpaff
  have hadd : inner ℝ w (w + p) = inner ℝ w p := by
    simpa [A, C] using h1
  have hzero : inner ℝ w w = 0 := by
    rw [inner_add_right] at hadd
    linarith
  exact hwne (inner_self_eq_zero.mp hzero)

open Classical in
/-- S3: tra una faccia e un politopo con salto di dimensione almeno due
esiste una faccia intermedia propria. -/
theorem interpolazione (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f)
    (hgap : faceDim f + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ P.toSet)) :
    ∃ f' : Set (E n), P.IsFace f' ∧ f ⊂ f' ∧ f' ≠ P.toSet := by
  classical
  obtain ⟨l, hl⟩ := hf.1 hf.2
  obtain ⟨p₀, hp₀f⟩ := hf.2
  have hp₀T : p₀ ∈ P.toSet := by
    rw [hl] at hp₀f
    exact hp₀f.1
  set U : Submodule ℝ (E n) := vectorSpan ℝ f with hU
  set W : Submodule ℝ (E n) := vectorSpan ℝ P.toSet with hW
  have hfT : f ⊆ P.toSet := by
    intro x hx
    rw [hl] at hx
    exact hx.1
  have hUW : U ≤ W := by
    rw [hU, hW]
    exact vectorSpan_mono ℝ hfT
  have hcodim : Module.finrank ℝ U + 2 ≤ Module.finrank ℝ W := by
    simpa [hU, hW, faceDim] using hgap
  obtain ⟨w₁, w₂, hw₁W, hw₂W, hw₁orth, hw₂orth, hLI⟩ :=
    exists_two_orthogonal_indep (U := U) (W := W) hUW hcodim
  have hw₁ne : w₁ ≠ 0 := by
    simpa using hLI.ne_zero 0
  have hw₂ne : w₂ ≠ 0 := by
    simpa using hLI.ne_zero 1
  have hw₁const : ∀ z ∈ f, inner ℝ w₁ z = inner ℝ w₁ p₀ := by
    intro z hz
    have hzU : z - p₀ ∈ U := by
      rw [hU]
      simpa using vsub_mem_vectorSpan ℝ hz hp₀f
    have ho := hw₁orth (z - p₀) hzU
    rw [← sub_eq_zero, ← inner_sub_right]
    exact ho
  have hw₂const : ∀ z ∈ f, inner ℝ w₂ z = inner ℝ w₂ p₀ := by
    intro z hz
    have hzU : z - p₀ ∈ U := by
      rw [hU]
      simpa using vsub_mem_vectorSpan ℝ hz hp₀f
    have ho := hw₂orth (z - p₀) hzU
    rw [← sub_eq_zero, ← inner_sub_right]
    exact ho
  have hw₁var : ∃ v ∈ P.vertices,
      inner ℝ w₁ v ≠ inner ℝ w₁ p₀ := by
    apply exists_vertex_inner_ne P hp₀T
    · simpa [hW] using hw₁W
    · exact hw₁ne
  have hw₂var : ∃ v ∈ P.vertices,
      inner ℝ w₂ v ≠ inner ℝ w₂ p₀ := by
    apply exists_vertex_inner_ne P hp₀T
    · simpa [hW] using hw₂W
    · exact hw₂ne

  obtain ⟨f₁, hf₁, hff₁, halt₁⟩ :=
    perno_parametrico P hf l hl p₀ hp₀f w₁ hw₁const hw₁var
  rcases halt₁ with hf₁proper | ⟨t₁, ht₁, c₁, hc₁⟩
  · exact ⟨f₁, hf₁, hff₁, hf₁proper⟩
  obtain ⟨f₂, hf₂, hff₂, halt₂⟩ :=
    perno_parametrico P hf l hl p₀ hp₀f w₂ hw₂const hw₂var
  rcases halt₂ with hf₂proper | ⟨t₂, ht₂, c₂, hc₂⟩
  · exact ⟨f₂, hf₂, hff₂, hf₂proper⟩

  exfalso
  set q : E n := t₁ • w₁ - t₂ • w₂ with hq
  have hqW : q ∈ W := by
    exact W.sub_mem (W.smul_mem t₁ hw₁W) (W.smul_mem t₂ hw₂W)
  have hqconst : ∀ v ∈ P.vertices, inner ℝ q v = c₁ - c₂ := by
    intro v hv
    have h1 := hc₁ v hv
    have h2 := hc₂ v hv
    calc
      inner ℝ q v = t₁ * inner ℝ w₁ v - t₂ * inner ℝ w₂ v := by
        rw [hq, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
      _ = c₁ - c₂ := by linarith
  obtain ⟨v₀, hv₀V⟩ := P.vertices_nonempty
  have hv₀T : v₀ ∈ P.toSet :=
    subset_convexHull ℝ _ (by exact_mod_cast hv₀V)
  have hqzero : q = 0 := by
    by_contra hqne
    obtain ⟨v, hvV, hvne⟩ := exists_vertex_inner_ne P hv₀T
      (by simpa [hW] using hqW) hqne
    apply hvne
    rw [hqconst v hvV, hqconst v₀ hv₀V]
  have heq : t₁ • w₁ = t₂ • w₂ := by
    exact sub_eq_zero.mp (by simpa [hq] using hqzero)
  have hwrel := congrArg (fun x : E n => t₁⁻¹ • x) heq
  have hwrel' : w₁ = (t₁⁻¹ * t₂) • w₂ := by
    simpa [smul_smul, ht₁] using hwrel
  have hpair := (linearIndependent_fin2.mp hLI).2 (t₁⁻¹ * t₂)
  exact hpair hwrel'.symm

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart10

section BundlePart11
/- Source: Cubical/Polytope/ScalaBandiere.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ScalaBandiere.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/








@[expose] public section

/-!
FASE 3A, Q3-S4 — LA SCALA: facet_exists e la catena delle facce (18 lug 2026).

Con l'interpolazione (S3) e la dimensione stretta (S3b): da un vertice si sale
di faccia in faccia fino alla faccetta (dim esattamente d−1); con il
sotto-politopo (Q2) si scende ricorsivamente costruendo la catena completa
di facce di dimensioni esatte 0,1,…,d−1. LE BANDIERE ESISTONO, in ogni
dimensione.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il corpo è una faccia di sé stesso (esposto dal funzionale nullo). -/
theorem toSet_isFace (P : ConvexPolytope n) : P.IsFace P.toSet := by
  constructor
  · intro _
    refine ⟨0, ?_⟩
    ext x
    simp
  · obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨v, subset_convexHull ℝ _ (by exact_mod_cast hv)⟩

/-- Ogni faccia sta nel corpo. -/
theorem face_subset_toSet (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) : f ⊆ P.toSet := by
  obtain ⟨l, hl⟩ := hf.1 hf.2
  rw [hl]
  exact fun z hz => hz.1

/-- S4a: ogni politopo di dimensione ≥ 1 ha una faccetta (dim esattamente d−1). -/
theorem facet_exists (P : ConvexPolytope n)
    (hd : 1 ≤ Module.finrank ℝ (vectorSpan ℝ P.toSet)) :
    ∃ f : Set (E n), P.IsFace f ∧
      faceDim f = Module.finrank ℝ (vectorSpan ℝ P.toSet) - 1 := by
  classical
  set d : ℕ := Module.finrank ℝ (vectorSpan ℝ P.toSet) with hdd
  suffices H : ∀ k : ℕ, ∀ f : Set (E n), P.IsFace f →
      d - 1 - faceDim f ≤ k → faceDim f ≤ d - 1 →
      ∃ g : Set (E n), P.IsFace g ∧ faceDim g = d - 1 by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    have h0 : P.IsFace ({v} : Set (E n)) := vertex_isFace P hv
    have hdim0 : faceDim ({v} : Set (E n)) = 0 := by
      show Module.finrank ℝ (vectorSpan ℝ ({v} : Set (E n))) = 0
      rw [vectorSpan_singleton]
      simp
    exact H (d - 1) {v} h0 (by omega) (by omega)
  intro k
  induction k with
  | zero =>
    intro f hf hk hle
    exact ⟨f, hf, by omega⟩
  | succ m ih =>
    intro f hf hk hle
    by_cases heq : faceDim f = d - 1
    · exact ⟨f, hf, heq⟩
    · have hgap : faceDim f + 2 ≤ d := by omega
      obtain ⟨f', hf', hsub, hne⟩ := interpolazione P hf hgap
      have hlt : faceDim f < faceDim f' := faceDim_lt_of_ssubset P hf hf' hsub
      have hlt2 : faceDim f' < d := by
        have hss : f' ⊂ P.toSet := ⟨face_subset_toSet P hf', hne ∘ (fun h =>
          Set.Subset.antisymm (face_subset_toSet P hf') h)⟩
        have := faceDim_lt_of_ssubset P hf' (toSet_isFace P) hss
        exact this
      exact ih f' hf' (by omega) (by omega)

/-- S4b: la catena completa — per ogni politopo, una successione di facce di
dimensioni esatte 0,…,d−1, strettamente crescente. -/
theorem chain_exists (P : ConvexPolytope n) :
    ∀ d : ℕ, Module.finrank ℝ (vectorSpan ℝ P.toSet) = d →
    ∃ c : ℕ → Set (E n),
      (∀ k, k < d → P.IsFace (c k) ∧ faceDim (c k) = k) ∧
      (∀ j k, j < k → k < d → c j ⊂ c k) := by
  classical
  intro d
  induction d generalizing P with
  | zero =>
    intro _
    exact ⟨fun _ => ∅, fun k hk => absurd hk (by omega),
      fun j k hjk hk => absurd hk (by omega)⟩
  | succ m ih =>
    intro hdim
    -- la faccetta di dimensione m
    have hd1 : 1 ≤ Module.finrank ℝ (vectorSpan ℝ P.toSet) := by omega
    obtain ⟨f, hf, hfdim⟩ := facet_exists P hd1
    rw [hdim] at hfdim
    simp only [Nat.add_sub_cancel] at hfdim
    -- ricorsione nel sotto-politopo
    have hsubdim : Module.finrank ℝ (vectorSpan ℝ (facePolytope P hf).toSet) = m := by
      rw [facePolytope_toSet P hf]
      exact hfdim
    obtain ⟨c', hc'1, hc'2⟩ := ih (facePolytope P hf) hsubdim
    refine ⟨fun k => if k = m then f else c' k, ?_, ?_⟩
    · intro k hk
      by_cases hkm : k = m
      · subst hkm
        simp only [if_pos rfl]
        exact ⟨hf, hfdim⟩
      · have hklt : k < m := by omega
        simp only [if_neg hkm]
        obtain ⟨h1, h2⟩ := hc'1 k hklt
        exact ⟨isFace_of_facePolytope P hf h1, h2⟩
    · intro j k hjk hk
      by_cases hkm : k = m
      · subst hkm
        have hjm : j ≠ k := by omega
        have hjlt : j < k := hjk
        simp only [if_pos rfl, if_neg hjm]
        obtain ⟨h1, h2⟩ := hc'1 j hjlt
        constructor
        · have hsub1 : c' j ⊆ (facePolytope P hf).toSet :=
            face_subset_toSet (facePolytope P hf) h1
          rwa [facePolytope_toSet P hf] at hsub1
        · intro hcontra
          have hsub1 : c' j ⊆ (facePolytope P hf).toSet :=
            face_subset_toSet (facePolytope P hf) h1
          rw [facePolytope_toSet P hf] at hsub1
          have hfeq : c' j = f := Set.Subset.antisymm hsub1 hcontra
          have := h2
          rw [hfeq] at this
          omega
      · have hklt : k < m := by omega
        have hjm : j ≠ m := by omega
        simp only [if_neg hkm, if_neg hjm]
        exact hc'2 j k hjk hklt

/-- S4: LE BANDIERE ESISTONO — ogni politopo full-dimensionale ha una Flag. -/
theorem flag_exists (P : ConvexPolytope n) (hfull : P.IsFullDim) :
    Nonempty (P.Flag) := by
  classical
  have hdim : Module.finrank ℝ (vectorSpan ℝ P.toSet) = n := hfull
  obtain ⟨c, hc1, hc2⟩ := chain_exists P n hdim
  refine ⟨⟨fun k => c k, ?_, ?_, ?_⟩⟩
  · intro k
    exact (hc1 k k.isLt).1
  · intro k
    exact (hc1 k k.isLt).2
  · intro i j hij
    exact hc2 i j hij j.isLt

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart11

section BundlePart12
/- Source: Cubical/Polytope/BandieraCompagna.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.BandieraCompagna.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/









@[expose] public section

/-!
FASE 3A — LA BANDIERA COMPAGNA (18 lug 2026).

Scarico completo di KG-3A1: per OGNI bandiera F di un politopo 3D esiste una
bandiera G con la stessa faccetta e spigolo diverso. Costruzione: nel
sotto-politopo Q della faccetta (dim 2) c'è un vertice w fuori dallo spigolo
(altrimenti lo spigolo conterrebbe tutti i vertici e sarebbe l'intera
faccetta); {w} è faccia (Q1), l'interpolazione (S3) dà uno spigolo f' ∋ w,
e f' ≠ F.face 1 perché w ∉ F.face 1. Corollario: `rho_orbitale_libero` —
in un politopo regolare ogni bandiera ammette una simmetria che fissa la
faccetta e muove lo spigolo, SENZA ipotesi condizionali.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La dimensione di un singoletto è 0. -/
theorem faceDim_singleton (v : E n) : faceDim ({v} : Set (E n)) = 0 := by
  show Module.finrank ℝ (vectorSpan ℝ ({v} : Set (E n))) = 0
  rw [vectorSpan_singleton]
  simp

/-- Una faccia diversa dal corpo lascia fuori almeno un vertice. -/
theorem exists_vertex_notMem_of_ne_toSet (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) (hne : f ≠ P.toSet) :
    ∃ w ∈ P.vertices, w ∉ f := by
  by_contra hall
  push_neg at hall
  have hconv : Convex ℝ f := hf.1.convex (convex_convexHull ℝ _)
  have hsub : P.toSet ⊆ f := by
    show convexHull ℝ ((P.vertices : Set (E n))) ⊆ f
    apply convexHull_min ?_ hconv
    intro x hx
    exact hall x (Finset.mem_coe.mp hx)
  exact hne (Set.Subset.antisymm (face_subset_toSet P hf) hsub)

/-- **LA BANDIERA COMPAGNA**: per ogni bandiera di un politopo 3D esiste una
bandiera con la stessa faccetta e spigolo diverso. -/
theorem compagna_exists (P : ConvexPolytope 3) (F : P.Flag) :
    ∃ G : P.Flag, G.face 2 = F.face 2 ∧ G.face 1 ≠ F.face 1 := by
  classical
  have hfacet : P.IsFace (F.face 2) := F.isFace 2
  have hQtoSet : (facePolytope P hfacet).toSet = F.face 2 :=
    facePolytope_toSet P hfacet
  have hQdim :
      Module.finrank ℝ (vectorSpan ℝ (facePolytope P hfacet).toSet) = 2 := by
    rw [hQtoSet]
    exact F.dim_eq 2
  -- lo spigolo di F è una faccia del sotto-politopo della faccetta
  have hesub : F.face 1 ⊆ F.face 2 := (F.strict_mono 1 2 (by decide)).subset
  have he : (facePolytope P hfacet).IsFace (F.face 1) :=
    facePolytope_isFace_of P hfacet (F.isFace 1) hesub
  -- lo spigolo non è tutta la faccetta (dim 1 contro 2)
  have hene : F.face 1 ≠ (facePolytope P hfacet).toSet := by
    intro h
    have h1 : faceDim (F.face 1) = 1 := F.dim_eq 1
    have h2 : faceDim (F.face 1) = 2 := by
      show Module.finrank ℝ (vectorSpan ℝ (F.face 1)) = 2
      rw [h, hQdim]
    omega
  -- un vertice della faccetta fuori dallo spigolo
  obtain ⟨w, hwV, hwe⟩ :=
    exists_vertex_notMem_of_ne_toSet (facePolytope P hfacet) he hene
  have hwF : (facePolytope P hfacet).IsFace ({w} : Set (E 3)) :=
    vertex_isFace (facePolytope P hfacet) hwV
  -- interpolazione: uno spigolo nuovo che passa per w
  have hgap : faceDim ({w} : Set (E 3)) + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ (facePolytope P hfacet).toSet) := by
    rw [faceDim_singleton, hQdim]
  obtain ⟨f', hf', hwf', hf'ne⟩ := interpolazione (facePolytope P hfacet) hwF hgap
  have hf'sub : f' ⊆ F.face 2 := by
    have := face_subset_toSet (facePolytope P hfacet) hf'
    rwa [hQtoSet] at this
  have hdimf' : faceDim f' = 1 := by
    have h1 : 0 < faceDim f' := by
      have hlt := faceDim_lt_of_ssubset (facePolytope P hfacet) hwF hf' hwf'
      rw [faceDim_singleton] at hlt
      omega
    have hss : f' ⊂ (facePolytope P hfacet).toSet :=
      ⟨face_subset_toSet (facePolytope P hfacet) hf', fun hsup =>
        hf'ne (Set.Subset.antisymm
          (face_subset_toSet (facePolytope P hfacet) hf') hsup)⟩
    have h2 := faceDim_lt_of_ssubset (facePolytope P hfacet) hf'
      (toSet_isFace (facePolytope P hfacet)) hss
    have h3 : faceDim (facePolytope P hfacet).toSet = 2 := hQdim
    omega
  -- le tre inclusioni strette
  have h12 : f' ⊂ F.face 2 := by
    refine ⟨hf'sub, fun hsup => ?_⟩
    have : faceDim (F.face 2) ≤ faceDim f' :=
      le_of_eq (congrArg faceDim (Set.Subset.antisymm hsup hf'sub))
    have h4 : faceDim (F.face 2) = 2 := F.dim_eq 2
    omega
  have h02 : ({w} : Set (E 3)) ⊂ F.face 2 := hwf'.trans h12
  -- la bandiera compagna
  refine ⟨⟨fun k => if k.val = 0 then {w} else if k.val = 1 then f' else F.face 2,
    ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro k
    rcases k with ⟨kv, hk⟩
    interval_cases kv
    · exact isFace_of_facePolytope P hfacet hwF
    · exact isFace_of_facePolytope P hfacet hf'
    · exact F.isFace 2
  · intro k
    rcases k with ⟨kv, hk⟩
    interval_cases kv
    · exact faceDim_singleton w
    · exact hdimf'
    · exact F.dim_eq 2
  · intro i j hij
    rcases i with ⟨iv, hi⟩
    rcases j with ⟨jv, hj⟩
    have hij' : iv < jv := hij
    have hcasi : (iv = 0 ∧ jv = 1) ∨ (iv = 0 ∧ jv = 2) ∨ (iv = 1 ∧ jv = 2) := by
      omega
    rcases hcasi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
    · exact hwf'
    · exact h02
    · exact h12
  · rfl
  · show f' ≠ F.face 1
    intro h
    rw [h] at hwf'
    exact hwe (hwf'.subset rfl)

/-- KG-3A1, forma ratificata: con la compagna e la flag-transitività, la
simmetria che fissa la faccetta e muove lo spigolo. -/
theorem rho_orbitale (P : ConvexPolytope 3) (h : P.IsRegular)
    (F G : P.Flag) (hfacet : G.face 2 = F.face 2)
    (hedge : G.face 1 ≠ F.face 1) :
    ∃ ρ : Isom 3, P.isSymmetry ρ ∧
      ((ρ : E 3 → E 3)) '' (F.face 2) = F.face 2 ∧
      ((ρ : E 3 → E 3)) '' (F.face 1) ≠ F.face 1 := by
  obtain ⟨ρ, hρ, hface⟩ := h.2 F G
  refine ⟨ρ, hρ, (hface 2).trans hfacet, ?_⟩
  intro hfixed
  exact hedge ((hface 1).symm.trans hfixed)

/-- **KG-3A1 SCARICATO**: in un politopo 3D regolare, OGNI bandiera ammette
una simmetria che fissa la faccetta e muove lo spigolo. Nessuna ipotesi
condizionale residua. -/
theorem rho_orbitale_libero (P : ConvexPolytope 3) (h : P.IsRegular)
    (F : P.Flag) :
    ∃ ρ : Isom 3, P.isSymmetry ρ ∧
      ((ρ : E 3 → E 3)) '' (F.face 2) = F.face 2 ∧
      ((ρ : E 3 → E 3)) '' (F.face 1) ≠ F.face 1 := by
  obtain ⟨G, hG2, hG1⟩ := compagna_exists P F
  exact rho_orbitale P h F G hG2 hG1

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart12

section BundlePart13
/- Source: Cubical/Polytope/BandieraVertice.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.BandieraVertice.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/










@[expose] public section

/-!
FASE 3A — LA BANDIERA AL VERTICE E LA FINITEZZA DELLE FACCE (18 lug 2026).

Tre attrezzi per il fan: (1) una faccia di dimensione 0 è un singoletto;
(2) per OGNI vertice di un politopo full-dim di ℝ³ esiste una bandiera che
parte da quel vertice (con la scala: interpolazione dal singoletto, e nel
caso il salto arrivi subito alla faccetta si ridiscende nel sotto-politopo);
(3) le facce di un politopo sono finite (ogni faccia è l'hull dei propri
vertici, e i sottoinsiemi dei vertici sono finiti).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una faccia di dimensione 0 è un singoletto. -/
theorem faccia_dim0_singoletto {f : Set (E n)} (hne : f.Nonempty)
    (hd : faceDim f = 0) : ∃ x, f = {x} := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, ?_⟩
  ext y
  constructor
  · intro hy
    have hmem : y - x ∈ vectorSpan ℝ f := vsub_mem_vectorSpan ℝ hy hx
    have hbot : vectorSpan ℝ f = ⊥ := by
      have hd' : Module.finrank ℝ (vectorSpan ℝ f) = 0 := hd
      exact Submodule.finrank_eq_zero.mp hd'
    rw [hbot] at hmem
    have : y - x = 0 := hmem
    have : y = x := by
      have h1 := congrArg (fun q => q + x) this
      simpa using h1
    exact this ▸ rfl
  · intro hy
    rw [Set.mem_singleton_iff.mp hy]
    exact hx

/-- Per ogni vertice di un politopo full-dim di ℝ³ c'è una bandiera che
parte da quel vertice. -/
theorem bandiera_al_vertice (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) :
    ∃ F : P.Flag, F.face 0 = {v} := by
  classical
  have hvface : P.IsFace ({v} : Set (E 3)) := vertex_isFace P hv
  have hd0 : faceDim ({v} : Set (E 3)) = 0 := faceDim_singleton v
  have hgap0 : faceDim ({v} : Set (E 3)) + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ P.toSet) := by
    have h1 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
    rw [hd0, h1]
    omega
  obtain ⟨g, hg, hvg, hgne⟩ := interpolazione P hvface hgap0
  have hdg : 0 < faceDim g := by
    have h1 := faceDim_lt_of_ssubset P hvface hg hvg
    rw [hd0] at h1
    omega
  have hdg3 : faceDim g < 3 := by
    have hss : g ⊂ P.toSet :=
      ⟨face_subset_toSet P hg, fun hsup => hgne
        (Set.Subset.antisymm (face_subset_toSet P hg) hsup)⟩
    have h1 := faceDim_lt_of_ssubset P hg (toSet_isFace P) hss
    have h2 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
    have h3 : Module.finrank ℝ (vectorSpan ℝ g) <
        Module.finrank ℝ (vectorSpan ℝ P.toSet) := h1
    have h4 : faceDim g = Module.finrank ℝ (vectorSpan ℝ g) := rfl
    omega
  have hvmemg : v ∈ g := hvg.subset rfl
  -- due casi: g è uno spigolo o una faccetta
  rcases Nat.lt_or_ge (faceDim g) 2 with hcase | hcase
  · -- g spigolo: lo si estende a faccetta
    have hdg1 : faceDim g = 1 := by omega
    have hgapg : faceDim g + 2 ≤
        Module.finrank ℝ (vectorSpan ℝ P.toSet) := by
      have h1 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
      rw [hdg1, h1]
    obtain ⟨A, hA, hgA, hAne⟩ := interpolazione P hg hgapg
    have hdA : faceDim A = 2 := by
      have h1 := faceDim_lt_of_ssubset P hg hA hgA
      have hss : A ⊂ P.toSet :=
        ⟨face_subset_toSet P hA, fun hsup => hAne
          (Set.Subset.antisymm (face_subset_toSet P hA) hsup)⟩
      have h2 := faceDim_lt_of_ssubset P hA (toSet_isFace P) hss
      have h3 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
      have h4 : faceDim A = Module.finrank ℝ (vectorSpan ℝ A) := rfl
      have h5 : Module.finrank ℝ (vectorSpan ℝ A) <
          Module.finrank ℝ (vectorSpan ℝ P.toSet) := h2
      omega
    refine ⟨⟨fun k => if k.val = 0 then {v} else if k.val = 1 then g else A,
      ?_, ?_, ?_⟩, rfl⟩
    · intro k
      rcases k with ⟨kv, hk⟩
      interval_cases kv
      · exact hvface
      · exact hg
      · exact hA
    · intro k
      rcases k with ⟨kv, hk⟩
      interval_cases kv
      · exact hd0
      · exact hdg1
      · exact hdA
    · intro i j hij
      rcases i with ⟨iv, hi⟩
      rcases j with ⟨jv, hj⟩
      have hij' : iv < jv := hij
      have hcasi : (iv = 0 ∧ jv = 1) ∨ (iv = 0 ∧ jv = 2) ∨
          (iv = 1 ∧ jv = 2) := by omega
      rcases hcasi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
      · exact hvg
      · exact hvg.trans hgA
      · exact hgA
  · -- g faccetta: si ridiscende nel sotto-politopo per trovare lo spigolo
    have hdg2 : faceDim g = 2 := by omega
    have hQdim : Module.finrank ℝ
        (vectorSpan ℝ (facePolytope P hg).toSet) = 2 := by
      rw [facePolytope_toSet P hg]
      exact hdg2
    have hvQ : (facePolytope P hg).IsFace ({v} : Set (E 3)) :=
      facePolytope_isFace_of P hg hvface (Set.singleton_subset_iff.mpr hvmemg)
    have hgapQ : faceDim ({v} : Set (E 3)) + 2 ≤
        Module.finrank ℝ (vectorSpan ℝ (facePolytope P hg).toSet) := by
      rw [hd0, hQdim]
    obtain ⟨e, he, hve, hene⟩ := interpolazione (facePolytope P hg) hvQ hgapQ
    have hdE : faceDim e = 1 := by
      have h1 := faceDim_lt_of_ssubset (facePolytope P hg) hvQ he hve
      rw [hd0] at h1
      have hss : e ⊂ (facePolytope P hg).toSet :=
        ⟨face_subset_toSet (facePolytope P hg) he, fun hsup => hene
          (Set.Subset.antisymm
            (face_subset_toSet (facePolytope P hg) he) hsup)⟩
      have h2 := faceDim_lt_of_ssubset (facePolytope P hg) he
        (toSet_isFace (facePolytope P hg)) hss
      have h3 : faceDim (facePolytope P hg).toSet = 2 := hQdim
      omega
    have heP : P.IsFace e := isFace_of_facePolytope P hg he
    have hesub : e ⊆ g := by
      have h1 := face_subset_toSet (facePolytope P hg) he
      rwa [facePolytope_toSet P hg] at h1
    have heg : e ⊂ g := by
      refine ⟨hesub, fun hsup => ?_⟩
      have h1 : e = g := Set.Subset.antisymm hesub hsup
      rw [h1] at hdE
      omega
    refine ⟨⟨fun k => if k.val = 0 then {v} else if k.val = 1 then e else g,
      ?_, ?_, ?_⟩, rfl⟩
    · intro k
      rcases k with ⟨kv, hk⟩
      interval_cases kv
      · exact hvface
      · exact heP
      · exact hg
    · intro k
      rcases k with ⟨kv, hk⟩
      interval_cases kv
      · exact hd0
      · exact hdE
      · exact hdg2
    · intro i j hij
      rcases i with ⟨iv, hi⟩
      rcases j with ⟨jv, hj⟩
      have hij' : iv < jv := hij
      have hcasi : (iv = 0 ∧ jv = 1) ∨ (iv = 0 ∧ jv = 2) ∨
          (iv = 1 ∧ jv = 2) := by omega
      rcases hcasi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
      · exact hve
      · exact hvg
      · exact heg

/-- Le facce di un politopo sono finite. -/
theorem facce_finite (P : ConvexPolytope n) :
    {f : Set (E n) | P.IsFace f}.Finite := by
  classical
  apply (P.vertices.powerset.finite_toSet.image
    (fun s : Finset (E n) => convexHull ℝ (s : Set (E n)))).subset
  intro F hF
  refine ⟨P.vertices.filter (· ∈ F), ?_, ?_⟩
  · exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · exact (face_eq_hull_vertices P hF).symm

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart13

section BundlePart14
/- Source: Cubical/Polytope/Diamante.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Diamante.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/





@[expose] public section

/-!
FASE 3A — IL DIAMANTE (18 lug 2026).

La proprietà del diamante in dimensione 3, forma forte: tre faccette a due a
due distinte di un politopo in ℝ³ non possono condividere due punti distinti.
Dimostrazione senza quozienti: gli espositori delle tre faccette si annullano
sulla direzione dello spigolo comune; scelto in ogni faccetta un punto fuori
dalla retta dello spigolo, i tre spostamenti più la direzione dello spigolo
sono quattro vettori in ℝ³, quindi dipendenti; applicando i tre espositori
alla relazione di dipendenza restano tre equazioni a coefficienti strettamente
negativi che impongono ai prodotti dei coefficienti tre segni a due a due
opposti: impossibile. Corollario: uno spigolo sta in al più due faccette
(la forma quantificata attesa da `EdgeInAtMostTwoFacets`).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Estrazione dell'espositore di una faccia: appartenenza e massimalità. -/
theorem espositore_di_faccia (P : ConvexPolytope n) {g : Set (E n)}
    (hg : P.IsFace g) :
    ∃ l : E n →L[ℝ] ℝ,
      (∀ y ∈ g, y ∈ P.toSet ∧ ∀ z ∈ P.toSet, l z ≤ l y) ∧
      (∀ q ∈ P.toSet, (∀ z ∈ P.toSet, l z ≤ l q) → q ∈ g) := by
  obtain ⟨l, hl⟩ := hg.1 hg.2
  refine ⟨l, ?_, ?_⟩
  · intro y hy
    rw [hl] at hy
    exact ⟨hy.1, hy.2⟩
  · intro q hq hmax
    rw [hl]
    exact ⟨hq, hmax⟩

/-- La retta per due punti distinti ha direzione di rango 1. -/
theorem finrank_direction_retta {v x : E n} (hvx : v ≠ x) :
    Module.finrank ℝ ((affineSpan ℝ ({v, x} : Set (E n))).direction) = 1 := by
  rw [direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.mpr hvx)

/-- Un insieme di rango ≤ 1 contenente due punti distinti ha per span affine
la retta per quei due punti. -/
theorem affineSpan_eq_retta {g : Set (E n)} {v x : E n} (hvx : v ≠ x)
    (hvg : v ∈ g) (hxg : x ∈ g)
    (hdim : Module.finrank ℝ (vectorSpan ℝ g) ≤ 1) :
    affineSpan ℝ g = affineSpan ℝ ({v, x} : Set (E n)) := by
  have hsub : ({v, x} : Set (E n)) ⊆ g := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz1
    · exact hvg
    · rcases Set.mem_singleton_iff.mp hz1 with rfl
      exact hxg
  have hle : affineSpan ℝ ({v, x} : Set (E n)) ≤ affineSpan ℝ g :=
    affineSpan_mono ℝ hsub
  have hdireq : (affineSpan ℝ ({v, x} : Set (E n))).direction =
      (affineSpan ℝ g).direction := by
    apply Submodule.eq_of_le_of_finrank_le (AffineSubspace.direction_le hle)
    rw [finrank_direction_retta hvx, direction_affineSpan]
    exact hdim
  exact (AffineSubspace.ext_of_direction_eq hdireq
    ⟨v, subset_affineSpan ℝ _ (Set.mem_insert v {x}),
      subset_affineSpan ℝ _ hvg⟩).symm

/-- In un insieme di rango 2 c'è un punto fuori da ogni retta. -/
theorem punto_fuori_retta {g : Set (E n)} (v x : E n) (hvx : v ≠ x)
    (hdim : faceDim g = 2) :
    ∃ p ∈ g, p ∉ affineSpan ℝ ({v, x} : Set (E n)) := by
  by_contra hall
  push_neg at hall
  have hsub : g ⊆ (affineSpan ℝ ({v, x} : Set (E n)) : Set (E n)) := hall
  have hle : affineSpan ℝ g ≤ affineSpan ℝ ({v, x} : Set (E n)) :=
    affineSpan_le.mpr hsub
  have h1 : Module.finrank ℝ ((affineSpan ℝ g).direction) ≤
      Module.finrank ℝ ((affineSpan ℝ ({v, x} : Set (E n))).direction) :=
    Submodule.finrank_mono (AffineSubspace.direction_le hle)
  rw [finrank_direction_retta hvx, direction_affineSpan] at h1
  have hdim' : Module.finrank ℝ (vectorSpan ℝ g) = 2 := hdim
  omega

/-- Se due facce distinte di dimensione 2 condividono due punti distinti,
un punto dell'una fuori dalla retta comune non sta nell'altra. -/
theorem fuori_dalla_terza (P : ConvexPolytope n) {Φ Ψ : Set (E n)} {v x : E n}
    (hΦ : P.IsFace Φ) (hΨ : P.IsFace Ψ) (hne : Φ ≠ Ψ)
    (hdΦ : faceDim Φ = 2) (hdΨ : faceDim Ψ = 2) (hvx : v ≠ x)
    (hvΦ : v ∈ Φ) (hxΦ : x ∈ Φ) (hvΨ : v ∈ Ψ) (hxΨ : x ∈ Ψ)
    {p : E n} (hpΨ : p ∈ Ψ)
    (hpL : p ∉ affineSpan ℝ ({v, x} : Set (E n))) : p ∉ Φ := by
  intro hpΦ
  have hint : P.IsFace (Φ ∩ Ψ) := ⟨hΦ.1.inter hΨ.1, ⟨v, hvΦ, hvΨ⟩⟩
  have hssub : Φ ∩ Ψ ⊂ Φ := by
    refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
    have hΦΨ : Φ ⊆ Ψ := fun z hz => (hsup hz).2
    have hss : Φ ⊂ Ψ := ⟨hΦΨ, fun h => hne (Set.Subset.antisymm hΦΨ h)⟩
    have := faceDim_lt_of_ssubset P hΦ hΨ hss
    omega
  have hdim : faceDim (Φ ∩ Ψ) < 2 := by
    have := faceDim_lt_of_ssubset P hint hΦ hssub
    omega
  have hdim' : Module.finrank ℝ (vectorSpan ℝ (Φ ∩ Ψ)) ≤ 1 := by
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Φ ∩ Ψ)) < 2 := hdim
    omega
  have hspan : affineSpan ℝ (Φ ∩ Ψ) = affineSpan ℝ ({v, x} : Set (E n)) :=
    affineSpan_eq_retta hvx ⟨hvΦ, hvΨ⟩ ⟨hxΦ, hxΨ⟩ hdim'
  apply hpL
  rw [← hspan]
  exact subset_affineSpan ℝ _ ⟨hpΦ, hpΨ⟩

/-- Il valore dell'espositore su un punto di un'altra faccia, fuori dalla
retta comune, è strettamente sotto il massimo. -/
theorem strict_su_terza (P : ConvexPolytope n) {Φ Ψ : Set (E n)} {v x : E n}
    {lΦ : E n →L[ℝ] ℝ}
    (hΦ : P.IsFace Φ) (hΨ : P.IsFace Ψ) (hne : Φ ≠ Ψ)
    (hdΦ : faceDim Φ = 2) (hdΨ : faceDim Ψ = 2) (hvx : v ≠ x)
    (hvΦ : v ∈ Φ) (hxΦ : x ∈ Φ) (hvΨ : v ∈ Ψ) (hxΨ : x ∈ Ψ)
    (hmem : ∀ y ∈ Φ, y ∈ P.toSet ∧ ∀ z ∈ P.toSet, lΦ z ≤ lΦ y)
    (hmax : ∀ q ∈ P.toSet, (∀ z ∈ P.toSet, lΦ z ≤ lΦ q) → q ∈ Φ)
    {p : E n} (hpΨ : p ∈ Ψ)
    (hpL : p ∉ affineSpan ℝ ({v, x} : Set (E n))) :
    lΦ p < lΦ v := by
  have hpP : p ∈ P.toSet := face_subset_toSet P hΨ hpΨ
  have hle : lΦ p ≤ lΦ v := (hmem v hvΦ).2 p hpP
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    have hpΦ : p ∈ Φ := hmax p hpP
      (fun z hz => le_trans ((hmem v hvΦ).2 z hz) (le_of_eq h.symm))
    exact fuori_dalla_terza P hΦ hΨ hne hdΦ hdΨ hvx hvΦ hxΦ hvΨ hxΨ hpΨ hpL hpΦ

/-- Da `gi·a + gj·b = 0` con `a, b < 0` e `gi, gj ≠ 0` segue `gi·gj < 0`. -/
theorem segno_opposto {gi gj a b : ℝ} (hrel : gi * a + gj * b = 0)
    (ha : a < 0) (hb : b < 0) (hgi : gi ≠ 0) (hgj : gj ≠ 0) :
    gi * gj < 0 := by
  rcases lt_or_gt_of_ne hgi with h | h
  · have h1 : 0 < gi * a := mul_pos_of_neg_of_neg h ha
    have h3 : 0 < gj := by
      by_contra hle
      push_neg at hle
      have h2 : 0 ≤ (-gj) * (-b) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    exact mul_neg_of_neg_of_pos h h3
  · have h1 : gi * a < 0 := mul_neg_of_pos_of_neg h ha
    have h3 : gj < 0 := by
      by_contra hle
      push_neg at hle
      have h2 : 0 ≤ gj * (-b) := mul_nonneg hle (by linarith)
      nlinarith
    exact mul_neg_of_pos_of_neg h h3

/-- **IL DIAMANTE, forma forte**: in un politopo di ℝ³ tre faccette a due a
due distinte non possono condividere due punti distinti. -/
theorem diamante (P : ConvexPolytope 3) {A B C : Set (E 3)}
    (hA : P.IsFace A) (hdA : faceDim A = 2)
    (hB : P.IsFace B) (hdB : faceDim B = 2)
    (hC : P.IsFace C) (hdC : faceDim C = 2)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    {v x : E 3} (hvx : v ≠ x)
    (hvA : v ∈ A) (hvB : v ∈ B) (hvC : v ∈ C)
    (hxA : x ∈ A) (hxB : x ∈ B) (hxC : x ∈ C) : False := by
  classical
  obtain ⟨lA, hmemA, hmaxA⟩ := espositore_di_faccia P hA
  obtain ⟨lB, hmemB, hmaxB⟩ := espositore_di_faccia P hB
  obtain ⟨lC, hmemC, hmaxC⟩ := espositore_di_faccia P hC
  obtain ⟨p1, hp1A, hp1L⟩ := punto_fuori_retta (g := A) v x hvx hdA
  obtain ⟨p2, hp2B, hp2L⟩ := punto_fuori_retta (g := B) v x hvx hdB
  obtain ⟨p3, hp3C, hp3L⟩ := punto_fuori_retta (g := C) v x hvx hdC
  -- costanza dell'espositore sulla propria faccia
  have costanza : ∀ {D : Set (E 3)} {lD : E 3 →L[ℝ] ℝ},
      (∀ y ∈ D, y ∈ P.toSet ∧ ∀ z ∈ P.toSet, lD z ≤ lD y) →
      ∀ {y y' : E 3}, y ∈ D → y' ∈ D → lD y = lD y' := by
    intro D lD hmem y y' hy hy'
    exact le_antisymm ((hmem y' hy').2 y (hmem y hy).1)
      ((hmem y hy).2 y' (hmem y' hy').1)
  -- le sei disuguaglianze strette
  have sAB := strict_su_terza P hA hB hAB hdA hdB hvx hvA hxA hvB hxB
    hmemA hmaxA hp2B hp2L
  have sAC := strict_su_terza P hA hC hAC hdA hdC hvx hvA hxA hvC hxC
    hmemA hmaxA hp3C hp3L
  have sBA := strict_su_terza P hB hA (Ne.symm hAB) hdB hdA hvx hvB hxB hvA hxA
    hmemB hmaxB hp1A hp1L
  have sBC := strict_su_terza P hB hC hBC hdB hdC hvx hvB hxB hvC hxC
    hmemB hmaxB hp3C hp3L
  have sCA := strict_su_terza P hC hA (Ne.symm hAC) hdC hdA hvx hvC hxC hvA hxA
    hmemC hmaxC hp1A hp1L
  have sCB := strict_su_terza P hC hB (Ne.symm hBC) hdC hdB hvx hvC hxC hvB hxB
    hmemC hmaxC hp2B hp2L
  -- quattro vettori in ℝ³: dipendenti
  have hdep : ¬ LinearIndependent ℝ (fun i : Fin 4 =>
      if i.val = 0 then p1 - v else if i.val = 1 then p2 - v
      else if i.val = 2 then p3 - v else x - v) := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    rw [finrank_euclideanSpace] at hcard
    have h4 : (4 : ℕ) ≤ 3 := by simpa [Fintype.card_fin] using hcard
    omega
  obtain ⟨gc, hgsum, i0, hgne⟩ := Fintype.not_linearIndependent_iff.mp hdep
  rw [Fin.sum_univ_four] at hgsum
  have hgsum4 : gc 0 • (p1 - v) + gc 1 • (p2 - v) + gc 2 • (p3 - v) +
      gc 3 • (x - v) = 0 := hgsum
  have hnz4 : gc 0 ≠ 0 ∨ gc 1 ≠ 0 ∨ gc 2 ≠ 0 ∨ gc 3 ≠ 0 := by
    rcases i0 with ⟨iv, hi⟩
    interval_cases iv
    · exact Or.inl hgne
    · exact Or.inr (Or.inl hgne)
    · exact Or.inr (Or.inr (Or.inl hgne))
    · exact Or.inr (Or.inr (Or.inr hgne))
  -- applicazione dei tre espositori
  have hMA := congrArg (fun w => lA w) hgsum4
  have hMB := congrArg (fun w => lB w) hgsum4
  have hMC := congrArg (fun w => lC w) hgsum4
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at hMA hMB hMC
  -- gli azzeramenti: punto proprio e direzione dello spigolo
  have eA1 : lA (p1 - v) = 0 := by
    rw [map_sub]
    have h := costanza hmemA hp1A hvA
    linarith
  have eAt : lA (x - v) = 0 := by
    rw [map_sub]
    have h := costanza hmemA hxA hvA
    linarith
  have eB2 : lB (p2 - v) = 0 := by
    rw [map_sub]
    have h := costanza hmemB hp2B hvB
    linarith
  have eBt : lB (x - v) = 0 := by
    rw [map_sub]
    have h := costanza hmemB hxB hvB
    linarith
  have eC3 : lC (p3 - v) = 0 := by
    rw [map_sub]
    have h := costanza hmemC hp3C hvC
    linarith
  have eCt : lC (x - v) = 0 := by
    rw [map_sub]
    have h := costanza hmemC hxC hvC
    linarith
  -- le tre relazioni residue
  have relA : gc 1 * lA (p2 - v) + gc 2 * lA (p3 - v) = 0 := by
    rw [eA1, eAt] at hMA
    linarith
  have relB : gc 0 * lB (p1 - v) + gc 2 * lB (p3 - v) = 0 := by
    rw [eB2, eBt] at hMB
    linarith
  have relC : gc 0 * lC (p1 - v) + gc 1 * lC (p2 - v) = 0 := by
    rw [eC3, eCt] at hMC
    linarith
  -- le sei negatività
  have ha : lA (p2 - v) < 0 := by rw [map_sub]; linarith [sAB]
  have hb : lA (p3 - v) < 0 := by rw [map_sub]; linarith [sAC]
  have hc : lB (p1 - v) < 0 := by rw [map_sub]; linarith [sBA]
  have hd : lB (p3 - v) < 0 := by rw [map_sub]; linarith [sBC]
  have he : lC (p1 - v) < 0 := by rw [map_sub]; linarith [sCA]
  have hf : lC (p2 - v) < 0 := by rw [map_sub]; linarith [sCB]
  -- collasso: se i primi tre coefficienti sono nulli, tutti lo sono
  have hxv0 : x - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hvx)
  have hcollasso : gc 0 = 0 → gc 1 = 0 → gc 2 = 0 → False := by
    intro h0 h1 h2
    rw [h0, h1, h2] at hgsum4
    simp only [zero_smul, zero_add] at hgsum4
    rcases smul_eq_zero.mp hgsum4 with h3 | h3
    · rcases hnz4 with h | h | h | h
      · exact h h0
      · exact h h1
      · exact h h2
      · exact h h3
    · exact hxv0 h3
  -- nessuno dei tre coefficienti è nullo
  have hα : gc 0 ≠ 0 := by
    intro h0
    have hγ : gc 2 = 0 := by
      have hrb : gc 2 * lB (p3 - v) = 0 := by
        rw [h0] at relB
        linarith
      rcases mul_eq_zero.mp hrb with h | h
      · exact h
      · exact absurd h (ne_of_lt hd)
    have hβ : gc 1 = 0 := by
      have hrc : gc 1 * lC (p2 - v) = 0 := by
        rw [h0] at relC
        linarith
      rcases mul_eq_zero.mp hrc with h | h
      · exact h
      · exact absurd h (ne_of_lt hf)
    exact hcollasso h0 hβ hγ
  have hβ : gc 1 ≠ 0 := by
    intro h1
    have hγ : gc 2 = 0 := by
      have hra : gc 2 * lA (p3 - v) = 0 := by
        rw [h1] at relA
        linarith
      rcases mul_eq_zero.mp hra with h | h
      · exact h
      · exact absurd h (ne_of_lt hb)
    have hα0 : gc 0 = 0 := by
      have hrc : gc 0 * lC (p1 - v) = 0 := by
        rw [h1] at relC
        linarith
      rcases mul_eq_zero.mp hrc with h | h
      · exact h
      · exact absurd h (ne_of_lt he)
    exact hcollasso hα0 h1 hγ
  have hγ : gc 2 ≠ 0 := by
    intro h2
    have hβ0 : gc 1 = 0 := by
      have hra : gc 1 * lA (p2 - v) = 0 := by
        rw [h2] at relA
        linarith
      rcases mul_eq_zero.mp hra with h | h
      · exact h
      · exact absurd h (ne_of_lt ha)
    have hα0 : gc 0 = 0 := by
      have hrb : gc 0 * lB (p1 - v) = 0 := by
        rw [h2] at relB
        linarith
      rcases mul_eq_zero.mp hrb with h | h
      · exact h
      · exact absurd h (ne_of_lt hc)
    exact hcollasso hα0 hβ0 h2
  -- i tre prodotti a segni opposti: impossibile
  have hβγ : gc 1 * gc 2 < 0 := segno_opposto relA ha hb hβ hγ
  have hαγ : gc 0 * gc 2 < 0 := segno_opposto relB hc hd hα hγ
  have hαβ : gc 0 * gc 1 < 0 := segno_opposto relC he hf hα hβ
  have hpos : 0 < (gc 0 * gc 1) * (gc 0 * gc 2) := mul_pos_of_neg_of_neg hαβ hαγ
  nlinarith [hpos, hβγ, sq_nonneg (gc 0)]

/-- **Uno spigolo sta in al più due faccette** — la forma quantificata
attesa dal predicato `EdgeInAtMostTwoFacets` del fascicolo sul fan. -/
theorem spigolo_in_due_faccette (P : ConvexPolytope 3) (v : E 3)
    ⦃A B C : Set (E 3)⦄
    (hA : P.IsFace A) (hdA : faceDim A = 2)
    (hB : P.IsFace B) (hdB : faceDim B = 2)
    (hC : P.IsFace C) (hdC : faceDim C = 2)
    (hAB : A ≠ B) (hvA : v ∈ A) (hvB : v ∈ B) (hvC : v ∈ C)
    ⦃x : E 3⦄ (hx : x ∈ A ∩ B) (hxv : x ≠ v) (hxC : x ∈ C) :
    C = A ∨ C = B := by
  by_contra hcon
  push_neg at hcon
  exact diamante P hA hdA hB hdB hC hdC hAB
    (fun h => hcon.1 h.symm) (fun h => hcon.2 h.symm)
    (Ne.symm hxv) hvA hvB hvC hx.1 hx.2 hxC

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart14

section BundlePart15
/- Source: Cubical/Polytope/Diamante2D.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Diamante2D.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/






@[expose] public section

/-!
FASE 3A, F2 — IL DIAMANTE 2D (18 lug 2026).

Un vertice di un poligono (politopo di rango 2) sta in al più due spigoli.
Stessa strategia del diamante 3D, un gradino sotto: i tre spostamenti dai
punti secondi degli spigoli vivono nel `vectorSpan` di rango 2 del poligono,
quindi sono dipendenti; i tre espositori uccidono ciascuno il proprio
termine e lasciano tre relazioni a coefficienti strettamente negativi con
prodotti a segni impossibili. Qui il politopo può vivere in E n qualunque:
conta solo il rango 2 del suo span.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una faccia di dimensione ≥ 1 contenente `v` contiene un punto ≠ `v`. -/
theorem faccia_ha_secondo_punto {g : Set (E n)} (hd : faceDim g = 1)
    {v : E n} : ∃ p ∈ g, p ≠ v := by
  by_contra hall
  push_neg at hall
  have hsub : g ⊆ ({v} : Set (E n)) := fun p hp => hall p hp
  have hle := vectorSpan_mono ℝ hsub
  rw [vectorSpan_singleton] at hle
  have h0 : Module.finrank ℝ (vectorSpan ℝ g) ≤
      Module.finrank ℝ (⊥ : Submodule ℝ (E n)) := Submodule.finrank_mono hle
  have hb : Module.finrank ℝ (⊥ : Submodule ℝ (E n)) = 0 := finrank_bot ℝ (E n)
  have hd' : Module.finrank ℝ (vectorSpan ℝ g) = 1 := hd
  omega

/-- Due punti distinti in una faccia forzano rango ≥ 1. -/
theorem finrank_pos_di_due {g : Set (E n)} {v p : E n}
    (hv : v ∈ g) (hp : p ∈ g) (hne : p ≠ v) :
    1 ≤ Module.finrank ℝ (vectorSpan ℝ g) := by
  have hmem : p -ᵥ v ∈ vectorSpan ℝ g := vsub_mem_vectorSpan ℝ hp hv
  have hle : Submodule.span ℝ {p -ᵥ v} ≤ vectorSpan ℝ g := by
    rw [Submodule.span_le]
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hmem
  have h1 := Submodule.finrank_mono hle
  rw [finrank_span_singleton (vsub_ne_zero.mpr hne)] at h1
  exact h1

/-- **IL DIAMANTE 2D**: in un politopo di rango 2, tre spigoli a due a due
distinti non possono passare tutti per lo stesso punto. -/
theorem diamante_poligono (R : ConvexPolytope n)
    (hdim : Module.finrank ℝ (vectorSpan ℝ R.toSet) = 2)
    {e₁ e₂ e₃ : Set (E n)}
    (h1 : R.IsFace e₁) (hd1 : faceDim e₁ = 1)
    (h2 : R.IsFace e₂) (hd2 : faceDim e₂ = 1)
    (h3 : R.IsFace e₃) (hd3 : faceDim e₃ = 1)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    {v : E n} (hv1 : v ∈ e₁) (hv2 : v ∈ e₂) (hv3 : v ∈ e₃) : False := by
  classical
  obtain ⟨l₁, hmem₁, hmax₁⟩ := espositore_di_faccia R h1
  obtain ⟨l₂, hmem₂, hmax₂⟩ := espositore_di_faccia R h2
  obtain ⟨l₃, hmem₃, hmax₃⟩ := espositore_di_faccia R h3
  obtain ⟨p₁, hp1, hp1v⟩ := faccia_ha_secondo_punto hd1 (v := v)
  obtain ⟨p₂, hp2, hp2v⟩ := faccia_ha_secondo_punto hd2 (v := v)
  obtain ⟨p₃, hp3, hp3v⟩ := faccia_ha_secondo_punto hd3 (v := v)
  -- costanza dell'espositore sulla propria faccia
  have costanza : ∀ {D : Set (E n)} {lD : E n →L[ℝ] ℝ},
      (∀ y ∈ D, y ∈ R.toSet ∧ ∀ z ∈ R.toSet, lD z ≤ lD y) →
      ∀ {y y' : E n}, y ∈ D → y' ∈ D → lD y = lD y' := by
    intro D lD hmem y y' hy hy'
    exact le_antisymm ((hmem y' hy').2 y (hmem y hy).1)
      ((hmem y hy).2 y' (hmem y' hy').1)
  -- il punto secondo di uno spigolo non sta in un altro spigolo
  have fuori : ∀ {ei ej : Set (E n)}, R.IsFace ei → R.IsFace ej → ei ≠ ej →
      faceDim ei = 1 → faceDim ej = 1 → v ∈ ei → v ∈ ej →
      ∀ {p : E n}, p ∈ ej → p ≠ v → p ∉ ei := by
    intro ei ej hei hej hne hdi hdj hvi hvj p hpj hpv hpi
    have hint : R.IsFace (ei ∩ ej) := ⟨hei.1.inter hej.1, ⟨v, hvi, hvj⟩⟩
    have hssub : ei ∩ ej ⊂ ei := by
      refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
      have hij : ei ⊆ ej := fun z hz => (hsup hz).2
      have hss : ei ⊂ ej := ⟨hij, fun h => hne (Set.Subset.antisymm hij h)⟩
      have := faceDim_lt_of_ssubset R hei hej hss
      omega
    have hlt := faceDim_lt_of_ssubset R hint hei hssub
    have hge : 1 ≤ Module.finrank ℝ (vectorSpan ℝ (ei ∩ ej)) :=
      finrank_pos_di_due ⟨hvi, hvj⟩ ⟨hpi, hpj⟩ hpv
    have hlt' : Module.finrank ℝ (vectorSpan ℝ (ei ∩ ej)) < 1 := by
      have h : Module.finrank ℝ (vectorSpan ℝ (ei ∩ ej)) <
          Module.finrank ℝ (vectorSpan ℝ ei) := hlt
      have hdi' : Module.finrank ℝ (vectorSpan ℝ ei) = 1 := hdi
      omega
    omega
  -- le sei disuguaglianze strette
  have strict : ∀ {ei ej : Set (E n)} {li : E n →L[ℝ] ℝ},
      R.IsFace ei → R.IsFace ej → ei ≠ ej →
      faceDim ei = 1 → faceDim ej = 1 → v ∈ ei → v ∈ ej →
      (∀ y ∈ ei, y ∈ R.toSet ∧ ∀ z ∈ R.toSet, li z ≤ li y) →
      (∀ q ∈ R.toSet, (∀ z ∈ R.toSet, li z ≤ li q) → q ∈ ei) →
      ∀ {p : E n}, p ∈ ej → p ≠ v → li p < li v := by
    intro ei ej li hei hej hne hdi hdj hvi hvj hmem hmax p hpj hpv
    have hpR : p ∈ R.toSet := face_subset_toSet R hej hpj
    have hle : li p ≤ li v := (hmem v hvi).2 p hpR
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hpi : p ∈ ei := hmax p hpR
        (fun z hz => le_trans ((hmem v hvi).2 z hz) (le_of_eq h.symm))
      exact fuori hei hej hne hdi hdj hvi hvj hpj hpv hpi
  have s12 := strict h1 h2 h12 hd1 hd2 hv1 hv2 hmem₁ hmax₁ hp2 hp2v
  have s13 := strict h1 h3 h13 hd1 hd3 hv1 hv3 hmem₁ hmax₁ hp3 hp3v
  have s21 := strict h2 h1 (Ne.symm h12) hd2 hd1 hv2 hv1 hmem₂ hmax₂ hp1 hp1v
  have s23 := strict h2 h3 h23 hd2 hd3 hv2 hv3 hmem₂ hmax₂ hp3 hp3v
  have s31 := strict h3 h1 (Ne.symm h13) hd3 hd1 hv3 hv1 hmem₃ hmax₃ hp1 hp1v
  have s32 := strict h3 h2 (Ne.symm h23) hd3 hd2 hv3 hv2 hmem₃ hmax₃ hp2 hp2v
  -- tre spostamenti nel rango 2: dipendenti
  have hdep : ¬ LinearIndependent ℝ (fun i : Fin 3 =>
      if i.val = 0 then p₁ - v else if i.val = 1 then p₂ - v else p₃ - v) := by
    intro hli
    have hcard : Module.finrank ℝ (Submodule.span ℝ
        (Set.range (fun i : Fin 3 =>
          if i.val = 0 then p₁ - v else if i.val = 1 then p₂ - v
          else p₃ - v))) = 3 := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    have hsp : Submodule.span ℝ (Set.range (fun i : Fin 3 =>
        if i.val = 0 then p₁ - v else if i.val = 1 then p₂ - v
        else p₃ - v)) ≤ vectorSpan ℝ R.toSet := by
      rw [Submodule.span_le]
      rintro z ⟨i, rfl⟩
      rcases i with ⟨iv, hi⟩
      interval_cases iv
      · exact vsub_mem_vectorSpan ℝ (face_subset_toSet R h1 hp1)
          (face_subset_toSet R h1 hv1)
      · exact vsub_mem_vectorSpan ℝ (face_subset_toSet R h2 hp2)
          (face_subset_toSet R h2 hv2)
      · exact vsub_mem_vectorSpan ℝ (face_subset_toSet R h3 hp3)
          (face_subset_toSet R h3 hv3)
    have h3' := Submodule.finrank_mono hsp
    omega
  obtain ⟨gc, hgsum, i0, hgne⟩ := Fintype.not_linearIndependent_iff.mp hdep
  rw [Fin.sum_univ_three] at hgsum
  have hgsum3 : gc 0 • (p₁ - v) + gc 1 • (p₂ - v) + gc 2 • (p₃ - v) = 0 :=
    hgsum
  have hnz3 : gc 0 ≠ 0 ∨ gc 1 ≠ 0 ∨ gc 2 ≠ 0 := by
    rcases i0 with ⟨iv, hi⟩
    interval_cases iv
    · exact Or.inl hgne
    · exact Or.inr (Or.inl hgne)
    · exact Or.inr (Or.inr hgne)
  -- applicazione dei tre espositori
  have hM1 := congrArg (fun w => l₁ w) hgsum3
  have hM2 := congrArg (fun w => l₂ w) hgsum3
  have hM3 := congrArg (fun w => l₃ w) hgsum3
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at hM1 hM2 hM3
  have e11 : l₁ (p₁ - v) = 0 := by
    rw [map_sub]
    have h := costanza hmem₁ hp1 hv1
    linarith
  have e22 : l₂ (p₂ - v) = 0 := by
    rw [map_sub]
    have h := costanza hmem₂ hp2 hv2
    linarith
  have e33 : l₃ (p₃ - v) = 0 := by
    rw [map_sub]
    have h := costanza hmem₃ hp3 hv3
    linarith
  have rel₁ : gc 1 * l₁ (p₂ - v) + gc 2 * l₁ (p₃ - v) = 0 := by
    rw [e11] at hM1
    linarith
  have rel₂ : gc 0 * l₂ (p₁ - v) + gc 2 * l₂ (p₃ - v) = 0 := by
    rw [e22] at hM2
    linarith
  have rel₃ : gc 0 * l₃ (p₁ - v) + gc 1 * l₃ (p₂ - v) = 0 := by
    rw [e33] at hM3
    linarith
  -- le sei negatività
  have na : l₁ (p₂ - v) < 0 := by rw [map_sub]; linarith [s12]
  have nb : l₁ (p₃ - v) < 0 := by rw [map_sub]; linarith [s13]
  have nc : l₂ (p₁ - v) < 0 := by rw [map_sub]; linarith [s21]
  have nd : l₂ (p₃ - v) < 0 := by rw [map_sub]; linarith [s23]
  have ne' : l₃ (p₁ - v) < 0 := by rw [map_sub]; linarith [s31]
  have nf : l₃ (p₂ - v) < 0 := by rw [map_sub]; linarith [s32]
  -- nessun coefficiente è nullo
  have hα : gc 0 ≠ 0 := by
    intro h0
    have hγ : gc 2 = 0 := by
      have hr : gc 2 * l₂ (p₃ - v) = 0 := by
        rw [h0] at rel₂
        linarith
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · exact absurd h (ne_of_lt nd)
    have hβ : gc 1 = 0 := by
      have hr : gc 1 * l₃ (p₂ - v) = 0 := by
        rw [h0] at rel₃
        linarith
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · exact absurd h (ne_of_lt nf)
    rcases hnz3 with h | h | h
    · exact h h0
    · exact h hβ
    · exact h hγ
  have hβ : gc 1 ≠ 0 := by
    intro h1'
    have hγ : gc 2 = 0 := by
      have hr : gc 2 * l₁ (p₃ - v) = 0 := by
        rw [h1'] at rel₁
        linarith
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · exact absurd h (ne_of_lt nb)
    have hα0 : gc 0 = 0 := by
      have hr : gc 0 * l₃ (p₁ - v) = 0 := by
        rw [h1'] at rel₃
        linarith
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · exact absurd h (ne_of_lt ne')
    rcases hnz3 with h | h | h
    · exact h hα0
    · exact h h1'
    · exact h hγ
  have hγ : gc 2 ≠ 0 := by
    intro h2'
    have hβ0 : gc 1 = 0 := by
      have hr : gc 1 * l₁ (p₂ - v) = 0 := by
        rw [h2'] at rel₁
        linarith
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · exact absurd h (ne_of_lt na)
    have hα0 : gc 0 = 0 := by
      have hr : gc 0 * l₂ (p₁ - v) = 0 := by
        rw [h2'] at rel₂
        linarith
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · exact absurd h (ne_of_lt nc)
    rcases hnz3 with h | h | h
    · exact h hα0
    · exact h hβ0
    · exact h h2'
  -- i tre prodotti a segni opposti: impossibile
  have hβγ : gc 1 * gc 2 < 0 := segno_opposto rel₁ na nb hβ hγ
  have hαγ : gc 0 * gc 2 < 0 := segno_opposto rel₂ nc nd hα hγ
  have hαβ : gc 0 * gc 1 < 0 := segno_opposto rel₃ ne' nf hα hβ
  have hpos : 0 < (gc 0 * gc 1) * (gc 0 * gc 2) := mul_pos_of_neg_of_neg hαβ hαγ
  nlinarith [hpos, hβγ, sq_nonneg (gc 0)]

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart15

section BundlePart16
/- Source: Cubical/Polytope/SecondoSpigolo.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.SecondoSpigolo.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/









@[expose] public section

/-!
FASE 3A, F3 — IL SECONDO SPIGOLO (18 lug 2026).

In un poligono (politopo di rango 2), ogni vertice con un spigolo e₁ ha un
secondo spigolo e₂ ≠ e₁. Perno esplicito: scelto w ≠ 0 nello span del
poligono ortogonale alla direzione u₁ − v di e₁, si ruota l'espositore del
vertice: ψ = l_v + t*·⟪w,·⟫ col t* critico (minimo dei rapporti sui vertici
dal lato buono di w). L'argmax di ψ è una faccia per definizione; contiene v
e il vertice critico u*, quindi ha rango ≥ 1; e u₁ NON può starci (ψ(u₁) =
ψ(v) forzerebbe l_v(u₁) = l_v(v), cioè u₁ = v): questo esclude in un colpo
solo sia F = e₁ sia F = corpo. Dunque F è uno spigolo per v diverso da e₁.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Nello span di rango ≥ 2 c'è un vettore non nullo ortogonale a una
direzione data. -/
theorem esiste_ortogonale_nello_span {W : Submodule ℝ (E n)}
    (hW : 2 ≤ Module.finrank ℝ W) (d : E n) :
    ∃ w : E n, w ∈ W ∧ w ≠ 0 ∧ ⟪w, d⟫ = 0 := by
  classical
  set f : W →ₗ[ℝ] ℝ := (innerSL ℝ d).toLinearMap.comp W.subtype with hf
  have hrange : Module.finrank ℝ (LinearMap.range f) ≤ 1 := by
    have h1 : Module.finrank ℝ (LinearMap.range f) ≤ Module.finrank ℝ ℝ :=
      Submodule.finrank_le _
    simpa using h1
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hker : 1 ≤ Module.finrank ℝ (LinearMap.ker f) := by omega
  have hne : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h] at hker
    simp [finrank_bot] at hker
  obtain ⟨w, hwker, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨(w : E n), w.2, ?_, ?_⟩
  · intro h
    apply hwne
    exact Subtype.ext h
  · have h1 : f w = 0 := hwker
    have h2 : ⟪d, (w : E n)⟫ = 0 := h1
    rw [real_inner_comm] at h2
    exact h2

/-- **IL SECONDO SPIGOLO**: in un poligono ogni vertice con uno spigolo ne
ha un secondo, diverso. -/
theorem secondo_spigolo (Q : ConvexPolytope n)
    (hdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2)
    {v : E n} (hv : v ∈ Q.vertices)
    {e₁ : Set (E n)} (he₁ : Q.IsFace e₁) (hde₁ : faceDim e₁ = 1)
    (hve₁ : v ∈ e₁) :
    ∃ e₂ : Set (E n), Q.IsFace e₂ ∧ faceDim e₂ = 1 ∧ v ∈ e₂ ∧ e₂ ≠ e₁ := by
  classical
  -- l'espositore del vertice
  obtain ⟨l, hl⟩ := (vertex_isFace Q hv).1 (Set.singleton_nonempty v)
  have hvT : v ∈ Q.toSet := by
    have : v ∈ ({v} : Set (E n)) := rfl
    rw [hl] at this
    exact this.1
  have hlmax : ∀ y ∈ Q.toSet, l y ≤ l v := by
    have : v ∈ ({v} : Set (E n)) := rfl
    rw [hl] at this
    exact this.2
  have hlchar : ∀ q ∈ Q.toSet, l q = l v → q = v := by
    intro q hq hlq
    have : q ∈ ({v} : Set (E n)) := by
      rw [hl]
      exact ⟨hq, fun y hy => le_trans (hlmax y hy) (le_of_eq hlq.symm)⟩
    exact this
  -- il secondo punto di e₁ e la sua direzione
  obtain ⟨u₁, hu₁e, hu₁v⟩ := faccia_ha_secondo_punto hde₁ (v := v)
  have hu₁T : u₁ ∈ Q.toSet := face_subset_toSet Q he₁ hu₁e
  -- u₁ non è argmax
  have hu₁lt : l u₁ < l v := by
    rcases lt_or_eq_of_le (hlmax u₁ hu₁T) with h | h
    · exact h
    · exact absurd (hlchar u₁ hu₁T h) hu₁v
  -- w ortogonale alla direzione di e₁, dentro lo span
  obtain ⟨w, hwW, hwne, hwd⟩ := esiste_ortogonale_nello_span
    (le_of_eq hdim.symm) (u₁ - v)
  -- un vertice dove ⟪w,·⟫ si muove
  obtain ⟨u₀, hu₀V, hu₀ne⟩ := exists_vertex_inner_ne Q hvT hwW hwne
  -- senza perdita di generalità il lato positivo è abitato:
  -- costruzione parametrizzata dal segno
  have costruzione : ∀ w' : E n, ⟪w', u₁ - v⟫ = 0 →
      (∃ u ∈ Q.vertices, ⟪w', v⟫ < ⟪w', u⟫) →
      ∃ e₂ : Set (E n), Q.IsFace e₂ ∧ faceDim e₂ = 1 ∧ v ∈ e₂ ∧ e₂ ≠ e₁ := by
    intro w' hw'd hup
    obtain ⟨ux, huxV, huxgt⟩ := hup
    -- i vertici dal lato positivo
    set S : Finset (E n) := Q.vertices.filter (fun u => ⟪w', v⟫ < ⟪w', u⟫)
      with hS
    have hSne : S.Nonempty := ⟨ux, Finset.mem_filter.mpr ⟨huxV, huxgt⟩⟩
    -- il rapporto critico
    set r : E n → ℝ := fun u => (l v - l u) / (⟪w', u⟫ - ⟪w', v⟫) with hr
    obtain ⟨us, husS, husmin⟩ := S.exists_min_image r hSne
    have husV : us ∈ Q.vertices := (Finset.mem_filter.mp husS).1
    have husgt : ⟪w', v⟫ < ⟪w', us⟫ := (Finset.mem_filter.mp husS).2
    have husne : us ≠ v := by
      intro h
      rw [h] at husgt
      exact lt_irrefl _ husgt
    have husT : us ∈ Q.toSet := subset_convexHull ℝ _ husV
    have huslt : l us < l v := by
      rcases lt_or_eq_of_le (hlmax us husT) with h | h
      · exact h
      · exact absurd (hlchar us husT h) husne
    set t : ℝ := r us with ht
    have htpos : 0 < t := by
      rw [ht, hr]
      apply div_pos
      · linarith
      · linarith
    -- il funzionale ruotato
    set ψ : E n →L[ℝ] ℝ := l + t • innerSL ℝ w' with hψ
    have hψval : ∀ y : E n, ψ y = l y + t * ⟪w', y⟫ := by
      intro y
      rw [hψ]
      simp
    -- tutti i vertici stanno sotto ψ v
    have hvert : ∀ u ∈ Q.vertices, ψ u ≤ ψ v := by
      intro u huV
      rw [hψval, hψval]
      by_cases hside : ⟪w', v⟫ < ⟪w', u⟫
      · -- lato positivo: il rapporto domina
        have huS : u ∈ S := Finset.mem_filter.mpr ⟨huV, hside⟩
        have hrle : t ≤ r u := husmin u huS
        have hgap : (0:ℝ) < ⟪w', u⟫ - ⟪w', v⟫ := by linarith
        have h1 : t * (⟪w', u⟫ - ⟪w', v⟫) ≤ r u * (⟪w', u⟫ - ⟪w', v⟫) :=
          mul_le_mul_of_nonneg_right hrle (le_of_lt hgap)
        have h2 : r u * (⟪w', u⟫ - ⟪w', v⟫) = l v - l u := by
          rw [hr]
          field_simp
        nlinarith
      · -- lato non positivo: entrambi i pezzi scendono
        push_neg at hside
        have h1 : l u ≤ l v := hlmax u (subset_convexHull ℝ _ huV)
        have h2 : t * ⟪w', u⟫ ≤ t * ⟪w', v⟫ :=
          mul_le_mul_of_nonneg_left hside (le_of_lt htpos)
        linarith
    -- estensione all'hull: il semispazio è convesso
    have hbody : ∀ y ∈ Q.toSet, ψ y ≤ ψ v := by
      intro y hy
      have hconv : Convex ℝ {z : E n | ψ z ≤ ψ v} := by
        apply convex_halfSpace_le
        exact ψ.toLinearMap.isLinear
      have hsub : (Q.vertices : Set (E n)) ⊆ {z : E n | ψ z ≤ ψ v} := by
        intro u hu
        exact hvert u (Finset.mem_coe.mp hu)
      have := convexHull_min hsub hconv
      exact this hy
    -- la faccia argmax di ψ
    set F : Set (E n) := {x ∈ Q.toSet | ∀ y ∈ Q.toSet, ψ y ≤ ψ x} with hF
    have hvF : v ∈ F := ⟨hvT, hbody⟩
    have hFface : Q.IsFace F := by
      refine ⟨fun _ => ⟨ψ, rfl⟩, ⟨v, hvF⟩⟩
    -- il vertice critico è in F: pareggio esatto
    have htie : ψ us = ψ v := by
      rw [hψval, hψval]
      have hgap : (0:ℝ) < ⟪w', us⟫ - ⟪w', v⟫ := by linarith
      have h2 : t * (⟪w', us⟫ - ⟪w', v⟫) = l v - l us := by
        show (l v - l us) / (⟪w', us⟫ - ⟪w', v⟫) * (⟪w', us⟫ - ⟪w', v⟫) =
          l v - l us
        exact div_mul_cancel₀ _ (ne_of_gt hgap)
      nlinarith [h2]
    have husF : us ∈ F := by
      refine ⟨husT, ?_⟩
      intro y hy
      rw [htie]
      exact hbody y hy
    -- u₁ non può stare in F
    have hu₁F : u₁ ∉ F := by
      intro hmem
      have h1 : ψ u₁ = ψ v :=
        le_antisymm (hbody u₁ hu₁T) (hmem.2 v hvT)
      rw [hψval, hψval] at h1
      have h2 : ⟪w', u₁⟫ = ⟪w', v⟫ := by
        have h3 : ⟪w', u₁ - v⟫ = 0 := hw'd
        rw [inner_sub_right] at h3
        linarith
      have h4 : l u₁ = l v := by
        rw [h2] at h1
        linarith
      exact hu₁v (hlchar u₁ hu₁T h4)
    -- F non è il corpo e non è e₁
    have hFne : F ≠ Q.toSet := by
      intro h
      exact hu₁F (h ▸ hu₁T)
    have hFne₁ : F ≠ e₁ := by
      intro h
      exact hu₁F (h ▸ hu₁e)
    -- la dimensione è esattamente 1
    have hd1 : 1 ≤ Module.finrank ℝ (vectorSpan ℝ F) :=
      finrank_pos_di_due hvF husF husne
    have hd2 : Module.finrank ℝ (vectorSpan ℝ F) < 2 := by
      have hss : F ⊂ Q.toSet :=
        ⟨fun x hx => hx.1, fun hsup => hFne
          (Set.Subset.antisymm (fun x hx => hx.1) hsup)⟩
      have h1 := faceDim_lt_of_ssubset Q hFface (toSet_isFace Q) hss
      have h2 : faceDim Q.toSet = 2 := hdim
      have h3 : Module.finrank ℝ (vectorSpan ℝ F) <
          Module.finrank ℝ (vectorSpan ℝ Q.toSet) := h1
      omega
    refine ⟨F, hFface, ?_, hvF, hFne₁⟩
    show Module.finrank ℝ (vectorSpan ℝ F) = 1
    omega
  -- il segno giusto
  rcases lt_or_gt_of_ne hu₀ne with hlt | hgt
  · -- ⟪w,u₀⟫ < ⟪w,v⟫: si usa −w
    apply costruzione (-w)
    · rw [inner_neg_left, hwd, neg_zero]
    · refine ⟨u₀, hu₀V, ?_⟩
      rw [inner_neg_left, inner_neg_left]
      linarith
  · -- ⟪w,u₀⟫ > ⟪w,v⟫: si usa w
    exact costruzione w hwd ⟨u₀, hu₀V, hgt⟩

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart16

section BundlePart17
/- Source: Cubical/Polytope/ConoVertice.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ConoVertice.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/









@[expose] public section

/-!
FASE 3A, F4a-F4b — SEGMENTO E CONO AL VERTICE (18 lug 2026).

(1) Un vertice del politopo è estremo in ogni faccia che lo contiene.
(2) Uno spigolo (faccia di rango 1) che contiene un vertice del politopo è
il segmento tra quel vertice e un secondo estremo: le coordinate lungo la
direzione dello spigolo sono confinate in [0, s_a] perché una coordinata
negativa metterebbe il vertice nell'openSegment tra due punti della faccia.
(3) Il lemma del cono nel poligono: al vertice w con spigoli [w,a] e [w,b],
tutto il poligono sta in w + s(a−w) + t(b−w) con s,t ≥ 0: il segno di t si
legge sull'espositore di e₁ (che uccide a−w e morde b−w), quello di s
sull'espositore di e₂. Corollario locale-globale: un funzionale che non
cresce verso a né verso b è massimo su tutto il poligono in w.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Un vertice del politopo è estremo in ogni faccia che lo contiene. -/
theorem vertice_estremo_in_faccia (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) {w : E n} (hwV : w ∈ P.vertices) (hwf : w ∈ f) :
    w ∈ f.extremePoints ℝ := by
  have hex : w ∈ P.toSet.extremePoints ℝ := by
    have h1 : w ∈ (P.vertices : Set (E n)) := Finset.mem_coe.mpr hwV
    rw [P.vertices_eq_extremePoints] at h1
    exact h1
  refine ⟨hwf, ?_⟩
  intro x hx y hy hseg
  exact hex.2 (face_subset_toSet P hf hx) (face_subset_toSet P hf hy) hseg

/-- Uno spigolo con un vertice del politopo è il segmento fino a un secondo
estremo. -/
theorem spigolo_segmento (P : ConvexPolytope n) {e : Set (E n)}
    (he : P.IsFace e) (hde : faceDim e = 1)
    {w : E n} (hwV : w ∈ P.vertices) (hwe : w ∈ e) :
    ∃ a : E n, a ∈ P.vertices ∧ a ∈ e ∧ a ≠ w ∧ e = segment ℝ w a := by
  classical
  obtain ⟨u, hue, huw⟩ := faccia_ha_secondo_punto hde (v := w)
  set d : E n := u - w with hd
  have hdne : d ≠ 0 := sub_ne_zero.mpr huw
  have hdd : (0:ℝ) < ⟪d, d⟫ := real_inner_self_pos.mpr hdne
  -- lo span dello spigolo è la retta di d
  have hspan : vectorSpan ℝ e = Submodule.span ℝ {d} := by
    have hle : Submodule.span ℝ {d} ≤ vectorSpan ℝ e := by
      rw [Submodule.span_le]
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact vsub_mem_vectorSpan ℝ hue hwe
    apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
    rw [finrank_span_singleton hdne]
    have h1 : Module.finrank ℝ (vectorSpan ℝ e) = 1 := hde
    omega
  -- coordinate lungo lo spigolo
  have hcoord : ∀ z ∈ e, ∃ s : ℝ, z = w + s • d := by
    intro z hz
    have h1 : z - w ∈ vectorSpan ℝ e := vsub_mem_vectorSpan ℝ hz hwe
    rw [hspan] at h1
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp h1
    refine ⟨s, ?_⟩
    have h2 := congrArg (fun q => q + w) hs
    simp at h2
    rw [← h2]
    abel
  have hval : ∀ z : E n, ∀ s : ℝ, z = w + s • d → ⟪d, z - w⟫ = s * ⟪d, d⟫ := by
    intro z s hs
    rw [hs]
    simp [inner_smul_right]
  -- il massimo della coordinata su un vertice dello spigolo
  set V : Finset (E n) := (facePolytope P he).vertices with hV
  have hVne : V.Nonempty := (facePolytope P he).vertices_nonempty
  have hVsube : (V : Set (E n)) ⊆ e := by
    intro x hx
    have h1 : x ∈ (facePolytope P he).toSet := subset_convexHull ℝ _ hx
    rwa [facePolytope_toSet P he] at h1
  obtain ⟨a, haV, hamax⟩ := V.exists_max_image (fun z => ⟪d, z⟫) hVne
  have hae : a ∈ e := hVsube haV
  have hmax : ∀ z ∈ e, ⟪d, z⟫ ≤ ⟪d, a⟫ := by
    intro z hz
    have hz' : z ∈ convexHull ℝ (V : Set (E n)) := by
      have h1 := face_eq_hull_vertices P he
      rw [h1] at hz
      exact hz
    have hconv : Convex ℝ {y : E n | ⟪d, y⟫ ≤ ⟪d, a⟫} := by
      apply convex_halfSpace_le
      exact (innerSL ℝ d).toLinearMap.isLinear
    have hsub : (V : Set (E n)) ⊆ {y : E n | ⟪d, y⟫ ≤ ⟪d, a⟫} := by
      intro x hx
      exact hamax x (Finset.mem_coe.mp hx)
    exact convexHull_min hsub hconv hz'
  obtain ⟨sa, hsa⟩ := hcoord a hae
  have hsage : 1 ≤ sa := by
    have h1 : ⟪d, u⟫ ≤ ⟪d, a⟫ := hmax u hue
    have h2 : ⟪d, u - w⟫ ≤ ⟪d, a - w⟫ := by
      rw [inner_sub_right, inner_sub_right]
      linarith
    have h3 : ⟪d, u - w⟫ = ⟪d, d⟫ := by rw [hd]
    have h4 := hval a sa hsa
    nlinarith
  have hsapos : 0 < sa := by linarith
  -- w è l'estremo inferiore: nessuna coordinata negativa
  have hwex : w ∈ e.extremePoints ℝ := vertice_estremo_in_faccia P he hwV hwe
  have hmin : ∀ z ∈ e, ∀ s : ℝ, z = w + s • d → 0 ≤ s := by
    intro z hz sz hsz
    by_contra hneg
    push_neg at hneg
    have hτ : (0:ℝ) < sa - sz := by linarith
    have hne : sa - sz ≠ 0 := ne_of_gt hτ
    have hcomb : w ∈ openSegment ℝ z a := by
      refine ⟨sa / (sa - sz), -sz / (sa - sz), ?_, ?_, ?_, ?_⟩
      · exact div_pos hsapos hτ
      · exact div_pos (by linarith) hτ
      · have h5 : sa / (sa - sz) + -sz / (sa - sz) = (sa + -sz) / (sa - sz) :=
          (add_div sa (-sz) (sa - sz)).symm
        rw [h5]
        have h6 : sa + -sz = sa - sz := by ring
        rw [h6]
        exact div_self hne
      · rw [hsz, hsa]
        match_scalars <;> field_simp <;> ring
    have hzw : z = w := hwex.2 hz hae hcomb
    rw [hzw] at hsz
    have h0 : sz • d = 0 := by
      have := congrArg (fun q => q - w) hsz
      simpa using this.symm
    rcases smul_eq_zero.mp h0 with h | h
    · linarith
    · exact hdne h
  have haPV : a ∈ P.vertices := by
    have h1 := haV
    rw [hV] at h1
    exact (Finset.mem_filter.mp h1).1
  refine ⟨a, haPV, hae, ?_, ?_⟩
  · intro h
    rw [h] at hsa
    have h0 : sa • d = 0 := by
      have := congrArg (fun q => q - w) hsa
      simpa using this.symm
    rcases smul_eq_zero.mp h0 with h1 | h1
    · linarith
    · exact hdne h1
  · apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨s, hs⟩ := hcoord z hz
      have hs0 : 0 ≤ s := hmin z hz s hs
      have hssa : s ≤ sa := by
        have h1 : ⟪d, z⟫ ≤ ⟪d, a⟫ := hmax z hz
        have h2 : ⟪d, z - w⟫ ≤ ⟪d, a - w⟫ := by
          rw [inner_sub_right, inner_sub_right]
          linarith
        have h3 := hval z s hs
        have h4 := hval a sa hsa
        nlinarith
      refine ⟨1 - s / sa, s / sa, ?_, ?_, by ring, ?_⟩
      · have h1 : s / sa ≤ 1 := by
          rw [div_le_one hsapos]
          exact hssa
        linarith
      · exact div_nonneg hs0 (le_of_lt hsapos)
      · rw [hs, hsa]
        match_scalars <;> field_simp <;> ring
    · have hconv : Convex ℝ e := he.1.convex (convex_convexHull ℝ _)
      exact hconv.segment_subset hwe hae

/-- **IL CONO AL VERTICE DEL POLIGONO**: al vertice w con spigoli [w,a] e
[w,b] distinti, ogni punto del poligono è w + s(a−w) + t(b−w) con s,t ≥ 0. -/
theorem cono_al_vertice (Q : ConvexPolytope n)
    (hdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2)
    {w : E n} (hwV : w ∈ Q.vertices)
    {e₁ e₂ : Set (E n)} (he₁ : Q.IsFace e₁) (hde₁ : faceDim e₁ = 1)
    (he₂ : Q.IsFace e₂) (hde₂ : faceDim e₂ = 1) (hne : e₁ ≠ e₂)
    {a b : E n} (hae : a ∈ e₁) (haw : a ≠ w) (hseg₁ : e₁ = segment ℝ w a)
    (hbe : b ∈ e₂) (hbw : b ≠ w) (hseg₂ : e₂ = segment ℝ w b)
    (hwe₁ : w ∈ e₁) (hwe₂ : w ∈ e₂) :
    ∀ z ∈ Q.toSet, ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      z = w + s • (a - w) + t • (b - w) := by
  classical
  -- gli espositori dei due spigoli
  obtain ⟨l₁, hl₁⟩ := he₁.1 he₁.2
  obtain ⟨l₂, hl₂⟩ := he₂.1 he₂.2
  have hmax₁ : ∀ y ∈ Q.toSet, l₁ y ≤ l₁ w := by
    have h1 := hwe₁
    rw [hl₁] at h1
    exact h1.2
  have hmax₂ : ∀ y ∈ Q.toSet, l₂ y ≤ l₂ w := by
    have h1 := hwe₂
    rw [hl₂] at h1
    exact h1.2
  have hchar₁ : ∀ q ∈ Q.toSet, l₁ q = l₁ w → q ∈ e₁ := by
    intro q hq hlq
    rw [hl₁]
    exact ⟨hq, fun y hy => le_trans (hmax₁ y hy) (le_of_eq hlq.symm)⟩
  have hchar₂ : ∀ q ∈ Q.toSet, l₂ q = l₂ w → q ∈ e₂ := by
    intro q hq hlq
    rw [hl₂]
    exact ⟨hq, fun y hy => le_trans (hmax₂ y hy) (le_of_eq hlq.symm)⟩
  -- valori: l₁ uccide a, morde b; l₂ uccide b, morde a
  have hl₁a : l₁ a = l₁ w := by
    have h1 := hae
    rw [hl₁] at h1
    exact le_antisymm (hmax₁ a (face_subset_toSet Q he₁ hae))
      (h1.2 w (face_subset_toSet Q he₁ hwe₁))
  have hl₂b : l₂ b = l₂ w := by
    have h1 := hbe
    rw [hl₂] at h1
    exact le_antisymm (hmax₂ b (face_subset_toSet Q he₂ hbe))
      (h1.2 w (face_subset_toSet Q he₂ hwe₂))
  -- b ∉ e₁ (due punti comuni forzerebbero rango ≥ 1 dell'intersezione)
  have hfuori : ∀ {p : E n}, p ∈ e₂ → p ≠ w → p ∉ e₁ := by
    intro p hpe₂ hpw hpe₁
    have hint : Q.IsFace (e₁ ∩ e₂) := ⟨he₁.1.inter he₂.1, ⟨w, hwe₁, hwe₂⟩⟩
    have hssub : e₁ ∩ e₂ ⊂ e₁ := by
      refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
      have h12 : e₁ ⊆ e₂ := fun z hz => (hsup hz).2
      have hss : e₁ ⊂ e₂ := ⟨h12, fun h => hne (Set.Subset.antisymm h12 h)⟩
      have := faceDim_lt_of_ssubset Q he₁ he₂ hss
      omega
    have hlt := faceDim_lt_of_ssubset Q hint he₁ hssub
    have hge : 1 ≤ Module.finrank ℝ (vectorSpan ℝ (e₁ ∩ e₂)) :=
      finrank_pos_di_due ⟨hwe₁, hwe₂⟩ ⟨hpe₁, hpe₂⟩ hpw
    have hlt' : Module.finrank ℝ (vectorSpan ℝ (e₁ ∩ e₂)) < 1 := by
      have h1 : Module.finrank ℝ (vectorSpan ℝ (e₁ ∩ e₂)) <
          Module.finrank ℝ (vectorSpan ℝ e₁) := hlt
      have h2 : Module.finrank ℝ (vectorSpan ℝ e₁) = 1 := hde₁
      omega
    omega
  have hfuori' : ∀ {p : E n}, p ∈ e₁ → p ≠ w → p ∉ e₂ := by
    intro p hpe₁ hpw hpe₂
    exact hfuori hpe₂ hpw hpe₁
  have hl₁b : l₁ b < l₁ w := by
    rcases lt_or_eq_of_le (hmax₁ b (face_subset_toSet Q he₂ hbe)) with h | h
    · exact h
    · exact absurd (hchar₁ b (face_subset_toSet Q he₂ hbe) h) (hfuori hbe hbw)
  have hl₂a : l₂ a < l₂ w := by
    rcases lt_or_eq_of_le (hmax₂ a (face_subset_toSet Q he₁ hae)) with h | h
    · exact h
    · exact absurd (hchar₂ a (face_subset_toSet Q he₁ hae) h) (hfuori' hae haw)
  -- le due direzioni sono indipendenti e generano lo span del poligono
  have hLI : LinearIndependent ℝ ![a - w, b - w] := by
    rw [linearIndependent_fin2]
    constructor
    · show b - w ≠ 0
      exact sub_ne_zero.mpr hbw
    · intro c
      show c • (b - w) ≠ a - w
      intro heq
      -- a sarebbe sulla retta di e₂: l₂ costante ⟹ a ∈ e₂: assurdo
      have ha' : a = c • (b - w) + w := by
        have h2 := congrArg (fun q => q + w) heq
        simp at h2
        exact h2.symm
      have hval : l₂ a = c * (l₂ b - l₂ w) + l₂ w := by
        rw [ha']
        simp [map_add, map_smul, map_sub, smul_eq_mul]
      rw [hl₂b] at hval
      simp at hval
      exact absurd (hchar₂ a (face_subset_toSet Q he₁ hae) hval)
        (hfuori' hae haw)
  have hspan2 : Submodule.span ℝ (Set.range ![a - w, b - w]) =
      vectorSpan ℝ Q.toSet := by
    have hle : Submodule.span ℝ (Set.range ![a - w, b - w]) ≤
        vectorSpan ℝ Q.toSet := by
      rw [Submodule.span_le]
      rintro z ⟨i, rfl⟩
      rcases i with ⟨iv, hi⟩
      interval_cases iv
      · show (![a - w, b - w] : Fin 2 → E n) 0 ∈ vectorSpan ℝ Q.toSet
        show a - w ∈ vectorSpan ℝ Q.toSet
        exact vsub_mem_vectorSpan ℝ (face_subset_toSet Q he₁ hae)
          (face_subset_toSet Q he₁ hwe₁)
      · show (![a - w, b - w] : Fin 2 → E n) 1 ∈ vectorSpan ℝ Q.toSet
        show b - w ∈ vectorSpan ℝ Q.toSet
        exact vsub_mem_vectorSpan ℝ (face_subset_toSet Q he₂ hbe)
          (face_subset_toSet Q he₂ hwe₂)
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [finrank_span_eq_card hLI]
    simp [hdim]
  -- la scrittura in coordinate e i segni
  intro z hz
  have hzmem : z - w ∈ Submodule.span ℝ (Set.range ![a - w, b - w]) := by
    rw [hspan2]
    exact vsub_mem_vectorSpan ℝ hz (face_subset_toSet Q he₁ hwe₁)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hzmem
  rw [Fin.sum_univ_two] at hc
  have hc' : c 0 • (a - w) + c 1 • (b - w) = z - w := hc
  have hzval : z = w + c 0 • (a - w) + c 1 • (b - w) := by
    have := congrArg (fun q => q + w) hc'
    simp at this
    rw [← this]
    abel
  -- l₁ dà il segno di c 1
  have hs1 : l₁ z = l₁ w + c 1 * (l₁ b - l₁ w) := by
    rw [hzval]
    simp [map_add, map_smul, map_sub, smul_eq_mul, hl₁a]
  have ht : 0 ≤ c 1 := by
    have h1 := hmax₁ z hz
    rw [hs1] at h1
    by_contra hneg
    push_neg at hneg
    nlinarith
  -- l₂ dà il segno di c 0
  have hs2 : l₂ z = l₂ w + c 0 * (l₂ a - l₂ w) := by
    rw [hzval]
    simp [map_add, map_smul, map_sub, smul_eq_mul, hl₂b]
  have hs : 0 ≤ c 0 := by
    have h1 := hmax₂ z hz
    rw [hs2] at h1
    by_contra hneg
    push_neg at hneg
    nlinarith
  exact ⟨c 0, c 1, hs, ht, hzval⟩

/-- **LOCALE-GLOBALE**: un funzionale che al vertice w non cresce verso i
due estremi vicini è massimo su tutto il poligono in w. -/
theorem locale_globale (Q : ConvexPolytope n)
    (hdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2)
    {w : E n} (hwV : w ∈ Q.vertices)
    {e₁ e₂ : Set (E n)} (he₁ : Q.IsFace e₁) (hde₁ : faceDim e₁ = 1)
    (he₂ : Q.IsFace e₂) (hde₂ : faceDim e₂ = 1) (hne : e₁ ≠ e₂)
    {a b : E n} (hae : a ∈ e₁) (haw : a ≠ w) (hseg₁ : e₁ = segment ℝ w a)
    (hbe : b ∈ e₂) (hbw : b ≠ w) (hseg₂ : e₂ = segment ℝ w b)
    (hwe₁ : w ∈ e₁) (hwe₂ : w ∈ e₂)
    (h : E n →L[ℝ] ℝ) (hha : h a ≤ h w) (hhb : h b ≤ h w) :
    ∀ z ∈ Q.toSet, h z ≤ h w := by
  intro z hz
  obtain ⟨s, t, hs, ht, hzval⟩ := cono_al_vertice Q hdim hwV he₁ hde₁ he₂ hde₂
    hne hae haw hseg₁ hbe hbw hseg₂ hwe₁ hwe₂ z hz
  have hval : h z = h w + s * (h a - h w) + t * (h b - h w) := by
    rw [hzval]
    simp [map_add, map_smul, map_sub, smul_eq_mul]
  nlinarith [mul_nonneg hs (by linarith : (0:ℝ) ≤ h w - h a),
    mul_nonneg ht (by linarith : (0:ℝ) ≤ h w - h b)]

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart17

section BundlePart18
/- Source: Cubical/Polytope/DueVertici.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.DueVertici.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




@[expose] public section

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : Nat}

/-- A zero-dimensional nonempty face is a singleton at a vertex. -/
theorem punto_di_faccia0_e_vertice (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F) (hdF : faceDim F = 0) :
    Exists fun v : E n =>
      And (F = ({v} : Set (E n))) (Membership.mem P.vertices v) := by
  choose v hFv using faccia_dim0_singoletto hF.2 hdF
  refine Exists.intro v (And.intro hFv ?_)
  have hexposed : IsExposed Real P.toSet ({v} : Set (E n)) := by
    simpa only [hFv] using hF.1
  have hvext : Membership.mem (P.toSet.extremePoints Real) v :=
    hexposed.isExtreme.mem_extremePoints
  have hvertices := P.vertices_eq_extremePoints
  rw [ConvexPolytope.toSet, hvertices.symm] at hvext
  exact hvext

/-- The only vertices of a segment-face are its endpoints, in any rank. -/
theorem vertice_in_segmento_estremo_generico (P : ConvexPolytope n)
    {delta : Set (E n)} (hdelta : P.IsFace delta) {x y z : E n}
    (hseg : delta = segment Real x y)
    (hz : Membership.mem P.vertices z) (hzdelta : Membership.mem delta z) :
    Or (z = x) (z = y) := by
  have hzext : Membership.mem (delta.extremePoints Real) z :=
    vertice_estremo_in_faccia P hdelta hz hzdelta
  have hxdelta : Membership.mem delta x := by
    rw [hseg]
    exact left_mem_segment Real x y
  have hydelta : Membership.mem delta y := by
    rw [hseg]
    exact right_mem_segment Real x y
  have hzseg : Membership.mem (segment Real x y) z := by
    simpa only [hseg] using hzdelta
  have hends : Or (x = z) (y = z) :=
    (mem_extremePoints_iff_forall_segment.mp hzext).2
      x hxdelta y hydelta hzseg
  exact hends.imp Eq.symm Eq.symm

/-- Every edge has exactly one zero-face different from a fixed zero-face. -/
theorem due_vertici_per_spigolo (P : ConvexPolytope n)
    {delta : Set (E n)} (hdelta : P.IsFace delta)
    (hddelta : faceDim delta = 1)
    {V : Set (E n)} (hV : P.IsFace V) (hdV : faceDim V = 0)
    (hVdelta : V < delta) :
    ExistsUnique fun W : Set (E n) =>
      And (And (P.IsFace W) (And (faceDim W = 0) (W < delta)))
        (Not (W = V)) := by
  choose v hVeq hvP using punto_di_faccia0_e_vertice P hV hdV
  have hvV : Membership.mem V v := by
    rw [hVeq]
    exact Set.mem_singleton v
  have hvdelta : Membership.mem delta v := hVdelta.le hvV
  choose a haP hadelta hav hseg using
    spigolo_segmento P hdelta hddelta hvP hvdelta
  refine ExistsUnique.intro ({a} : Set (E n)) ?_ ?_
  next =>
    have haFace : P.IsFace ({a} : Set (E n)) := vertex_isFace P haP
    have hda : faceDim ({a} : Set (E n)) = 0 := faceDim_singleton a
    have hasub : ({a} : Set (E n)) <= delta :=
      Set.singleton_subset_iff.mpr hadelta
    have haneqdelta : Not (({a} : Set (E n)) = delta) := by
      intro haeqdelta
      have hdelta0 : faceDim delta = 0 := by
        rw [haeqdelta] at hda
        exact hda
      omega
    have hass : ({a} : Set (E n)) < delta :=
      lt_of_le_of_ne hasub haneqdelta
    have haneV : Not (({a} : Set (E n)) = V) := by
      intro haeqV
      apply hav
      have hsingle : ({a} : Set (E n)) = {v} := haeqV.trans hVeq
      exact Set.singleton_injective hsingle
    exact And.intro (And.intro haFace (And.intro hda hass)) haneV
  next =>
    intro W hW
    have hWFace : P.IsFace W := hW.1.1
    have hdW : faceDim W = 0 := hW.1.2.1
    have hWdelta : W < delta := hW.1.2.2
    have hWneV : Not (W = V) := hW.2
    choose x hWeq hxP using punto_di_faccia0_e_vertice P hWFace hdW
    have hxW : Membership.mem W x := by
      rw [hWeq]
      exact Set.mem_singleton x
    have hxdelta : Membership.mem delta x := hWdelta.le hxW
    have hxend := vertice_in_segmento_estremo_generico P hdelta hseg hxP hxdelta
    cases hxend with
    | inl hxv =>
        have hWV : W = V := by
          calc
            W = {x} := hWeq
            _ = {v} := by rw [hxv]
            _ = V := hVeq.symm
        exact (hWneV hWV).elim
    | inr hxa =>
        calc
          W = {x} := hWeq
          _ = {a} := by rw [hxa]

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart18

section BundlePart19
/- Source: Cubical/Polytope/Graph.lean -/





@[expose] public section

/-!
# The actual edge graph of a finite convex polytope

Vertices are precisely the extreme points listed by the geometric polytope.
Two distinct vertices are adjacent when they lie on a common exposed face
of affine dimension one.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- The nonempty geometric face poset, ordered by inclusion. -/
abbrev FaceType (P : ConvexPolytope n) := {F : Set (E n) // P.IsFace F}

noncomputable instance faceTypeFintype (P : ConvexPolytope n) :
    Fintype (FaceType P) := (finite_isFace P).fintype

/-- Vertices of a geometric convex polytope. -/
abbrev VertexType (P : ConvexPolytope n) := {v : E n // v ∈ P.vertices}

/-- The ordinary graph of vertices and edges of a convex polytope. -/
def polytopeGraph (P : ConvexPolytope n) : SimpleGraph (VertexType P) where
  Adj u v := u ≠ v ∧ ∃ F : Set (E n),
    P.IsFace F ∧ faceDim F = 1 ∧ u.val ∈ F ∧ v.val ∈ F
  symm := by
    constructor
    rintro u v ⟨hne, F, hF, hdF, hu, hv⟩
    exact ⟨hne.symm, F, hF, hdF, hv, hu⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- Counting zero-dimensional faces agrees with counting extreme vertices. -/
theorem faceNumber_zero (P : ConvexPolytope n) :
    faceNumber P 0 = P.vertices.card := by
  classical
  have hfaces : (faceSet P).filter (fun F => faceDim F = 0) =
      P.vertices.image (fun v : E n => ({v} : Set (E n))) := by
    ext F
    simp only [Finset.mem_filter, mem_faceSet, Finset.mem_image]
    constructor
    · rintro ⟨hF, hd⟩
      obtain ⟨v, rfl, hv⟩ := punto_di_faccia0_e_vertice P hF hd
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨vertex_isFace P hv, faceDim_singleton v⟩
  unfold faceNumber
  rw [hfaces]
  exact Finset.card_image_of_injective _ (fun _ _ h => Set.singleton_injective h)

/-- An exposed edge is the segment joining any two distinct vertices on it. -/
theorem edge_eq_segment (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F) (hdF : faceDim F = 1)
    {u v : E n} (hu : u ∈ P.vertices) (hv : v ∈ P.vertices)
    (huF : u ∈ F) (hvF : v ∈ F) (hne : u ≠ v) :
    F = segment ℝ u v := by
  obtain ⟨w, hw, hwF, hwu, hseg⟩ := spigolo_segmento P hF hdF hu huF
  have hvend : v = u ∨ v = w :=
    vertice_in_segmento_estremo_generico P hF hseg hv hvF
  rcases hvend with hvu | hvw
  · exact (hne hvu.symm).elim
  · simpa only [← hvw] using hseg

/-- The geometric edge containing two distinct vertices is unique. -/
theorem edge_unique (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hdF : faceDim F = 1) (hdG : faceDim G = 1)
    {u v : E n} (hu : u ∈ P.vertices) (hv : v ∈ P.vertices)
    (huF : u ∈ F) (hvF : v ∈ F) (huG : u ∈ G) (hvG : v ∈ G)
    (hne : u ≠ v) : F = G := by
  rw [edge_eq_segment P hF hdF hu hv huF hvF hne,
    edge_eq_segment P hG hdG hu hv huG hvG hne]

end LeanEval.Geometry.PlatonicClassification

end
end BundlePart19

section BundlePart20
/- Source: Cubical/Polytope/FacciaIntermedia.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.FacciaIntermedia.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/







@[expose] public section

/-!
MOTORE COXETER, PASSO 1 — LA FACCIA INTERMEDIA ESISTE (19 lug 2026).

Il lato «almeno uno» del diamante in rango arbitrario, ottenuto SENZA
teoria nuova: la relativizzazione era già nell'infrastruttura. Il
sotto-politopo di una faccia (`facePolytope`) ha per corpo la faccia
stessa, eredita le facce nei due versi, e `interpolazione` non chiede la
piena dimensionalità nell'ambiente ma lavora sulla dimensione intrinseca
`finrank (vectorSpan toSet)`. Dunque, date `A ⊂ B` con salto di rango 2:
si scende nel sotto-politopo di `B`, si interpola, si risale.

Correzione del vaglio avversariale accolta: questo è il lato facile; il
kill-gate vero («esattamente due») è un teorema separato.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **LA FACCIA INTERMEDIA**: fra due facce a salto di rango 2 ne esiste
una di rango intermedio. -/
theorem faccia_intermedia (P : ConvexPolytope n) {A B : Set (E n)}
    (hA : P.IsFace A) (hB : P.IsFace B) (hAB : A ⊂ B)
    (hrank : faceDim B = faceDim A + 2) :
    ∃ C : Set (E n), P.IsFace C ∧ A ⊂ C ∧ C ⊂ B ∧
      faceDim C = faceDim A + 1 := by
  classical
  -- si scende nel sotto-politopo della faccia superiore
  set Q : ConvexPolytope n := facePolytope P hB with hQ
  have hQtoSet : Q.toSet = B := facePolytope_toSet P hB
  have hAQ : Q.IsFace A := facePolytope_isFace_of P hB hA hAB.subset
  -- il salto di rango, letto sulla dimensione intrinseca di Q
  have hgap : faceDim A + 2 ≤ Module.finrank ℝ (vectorSpan ℝ Q.toSet) := by
    rw [hQtoSet]
    have hBdim : Module.finrank ℝ (vectorSpan ℝ B) = faceDim A + 2 := hrank
    omega
  -- l'interpolazione dentro Q
  obtain ⟨C, hCQ, hACss, hCne⟩ := interpolazione Q hAQ hgap
  -- risalita a P
  have hCP : P.IsFace C := isFace_of_facePolytope P hB hCQ
  have hCB : C ⊆ B := by
    have h1 := face_subset_toSet Q hCQ
    rwa [hQtoSet] at h1
  have hCssB : C ⊂ B := by
    refine hCB.ssubset_of_ne ?_
    intro hEq
    apply hCne
    rw [hEq, hQtoSet]
  -- la dimensione è esattamente quella intermedia
  have hlo0 := faceDim_lt_of_ssubset P hA hCP hACss
  have hhi0 := faceDim_lt_of_ssubset P hCP hB hCssB
  have hlo : Module.finrank ℝ (vectorSpan ℝ A) <
      Module.finrank ℝ (vectorSpan ℝ C) := hlo0
  have hhi : Module.finrank ℝ (vectorSpan ℝ C) <
      Module.finrank ℝ (vectorSpan ℝ B) := hhi0
  have hBd : Module.finrank ℝ (vectorSpan ℝ B) =
      Module.finrank ℝ (vectorSpan ℝ A) + 2 := hrank
  refine ⟨C, hCP, hACss, hCssB, ?_⟩
  show Module.finrank ℝ (vectorSpan ℝ C) =
    Module.finrank ℝ (vectorSpan ℝ A) + 1
  omega

/-- Forma d'uso sulle bandiere: fra `F.face (i-1)` e `F.face (i+1)` esiste
una faccia intermedia di rango `i` (in particolare la stessa `F.face i`,
ma il teorema dà l'esistenza in forma riutilizzabile per l'adiacenza). -/
theorem faccia_intermedia_di_bandiera (P : ConvexPolytope n) (F : P.Flag)
    {i j : Fin n} (hij : (i : ℕ) + 2 = (j : ℕ)) :
    ∃ C : Set (E n), P.IsFace C ∧ F.face i ⊂ C ∧ C ⊂ F.face j ∧
      faceDim C = faceDim (F.face i) + 1 := by
  have hlt : i < j := by
    rw [Fin.lt_def]
    omega
  refine faccia_intermedia P (F.isFace i) (F.isFace j)
    (F.strict_mono i j hlt) ?_
  rw [F.dim_eq i, F.dim_eq j]
  omega

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart20

section BundlePart21
/- Source: Cubical/Polytope/DiamanteRelativo.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.DiamanteRelativo.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




@[expose] public section

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : Nat}

theorem affineSpan_eq_of_subset_of_faceDim_eq {f g : Set (E n)}
    (hf : f.Nonempty) (hfg : f ⊆ g) (hdim : faceDim f = faceDim g) :
    affineSpan Real f = affineSpan Real g := by
  obtain ⟨a, ha⟩ := hf
  have hspan_le : vectorSpan Real f ≤ vectorSpan Real g :=
    vectorSpan_mono Real hfg
  have hspan_eq : vectorSpan Real f = vectorSpan Real g := by
    apply Submodule.eq_of_le_of_finrank_le hspan_le
    show faceDim g ≤ faceDim f
    exact le_of_eq hdim.symm
  have haff_le : affineSpan Real f ≤ affineSpan Real g :=
    affineSpan_mono Real hfg
  apply le_antisymm haff_le
  intro y hy
  have haff : a ∈ affineSpan Real f := subset_affineSpan Real f ha
  have hdir : (affineSpan Real f).direction =
      (affineSpan Real g).direction := by
    rw [direction_affineSpan, direction_affineSpan, hspan_eq]
  have hy_dir : y -ᵥ a ∈ (affineSpan Real g).direction :=
    AffineSubspace.vsub_mem_direction hy (haff_le haff)
  rw [← hdir] at hy_dir
  have := AffineSubspace.vadd_mem_of_mem_direction hy_dir haff
  simpa using this

theorem exists_point_outside_affineSpan_of_faceDim_lt {f g : Set (E n)}
    (hlt : faceDim f < faceDim g) :
    ∃ p ∈ g, p ∉ affineSpan Real f := by
  by_contra hall
  push Not at hall
  have haff_le : affineSpan Real g ≤ affineSpan Real f :=
    affineSpan_le.mpr hall
  have hdir_le : (affineSpan Real g).direction ≤
      (affineSpan Real f).direction := AffineSubspace.direction_le haff_le
  have hrank := Submodule.finrank_mono hdir_le
  rw [direction_affineSpan, direction_affineSpan] at hrank
  have hlt' : Module.finrank Real (vectorSpan Real f) <
      Module.finrank Real (vectorSpan Real g) := hlt
  exact (not_lt_of_ge hrank) hlt'

theorem fuori_dalla_terza_relativo (P : ConvexPolytope n)
    {A Ci Cj : Set (E n)}
    (hA : P.IsFace A) (hCi : P.IsFace Ci) (hCj : P.IsFace Cj)
    (hAi : A ⊂ Ci) (hAj : A ⊂ Cj)
    (hdCi : faceDim Ci = faceDim A + 1)
    (hdCj : faceDim Cj = faceDim A + 1) (hne : Ci ≠ Cj)
    {p : E n} (hpj : p ∈ Cj) (hpout : p ∉ affineSpan Real A) :
    p ∉ Ci := by
  intro hpi
  obtain ⟨a, ha⟩ := hA.2
  have hint : P.IsFace (Ci ∩ Cj) :=
    ⟨hCi.1.inter hCj.1, ⟨a, hAi.1 ha, hAj.1 ha⟩⟩
  have hinter_strict : Ci ∩ Cj ⊂ Ci := by
    refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
    have hij : Ci ⊆ Cj := fun z hz => (hsup hz).2
    have hstrict : Ci ⊂ Cj :=
      ⟨hij, fun hji => hne (Set.Subset.antisymm hij hji)⟩
    have hlt := faceDim_lt_of_ssubset P hCi hCj hstrict
    omega
  have hinter_lt := faceDim_lt_of_ssubset P hint hCi hinter_strict
  have hAinter : A ⊆ Ci ∩ Cj := fun z hz => ⟨hAi.1 hz, hAj.1 hz⟩
  have hdim_le : faceDim A ≤ faceDim (Ci ∩ Cj) := by
    exact Submodule.finrank_mono (vectorSpan_mono Real hAinter)
  have hdim_eq : faceDim A = faceDim (Ci ∩ Cj) := by
    omega
  have haff_eq : affineSpan Real A = affineSpan Real (Ci ∩ Cj) :=
    affineSpan_eq_of_subset_of_faceDim_eq hA.2 hAinter hdim_eq
  apply hpout
  rw [haff_eq]
  exact subset_affineSpan Real (Ci ∩ Cj) ⟨hpi, hpj⟩

theorem proiezione_tre_vettori
    {U W : Submodule Real (E n)} (hUW : U ≤ W)
    (hdim : Module.finrank Real W = Module.finrank Real U + 2)
    {v1 v2 v3 : E n}
    (hv1W : v1 ∈ W) (hv2W : v2 ∈ W) (hv3W : v3 ∈ W)
    (hv1U : v1 ∉ U) (hv2U : v2 ∉ U) (hv3U : v3 ∉ U) :
    ∃ q1 q2 q3 : E n,
      q1 ∈ U.orthogonal ⊓ W ∧
      q2 ∈ U.orthogonal ⊓ W ∧
      q3 ∈ U.orthogonal ⊓ W ∧
      q1 ≠ 0 ∧ q2 ≠ 0 ∧ q3 ≠ 0 ∧
      v1 - q1 ∈ U ∧ v2 - q2 ∈ U ∧ v3 - q3 ∈ U ∧
      Module.finrank Real (U.orthogonal ⊓ W : Submodule Real (E n)) = 2 := by
  let q1 : E n := U.orthogonal.starProjection v1
  let q2 : E n := U.orthogonal.starProjection v2
  let q3 : E n := U.orthogonal.starProjection v3
  have difference : ∀ v : E n,
      v - U.orthogonal.starProjection v ∈ U := by
    intro v
    rw [Submodule.starProjection_orthogonal_val]
    simp
  have hq1d : v1 - q1 ∈ U := difference v1
  have hq2d : v2 - q2 ∈ U := difference v2
  have hq3d : v3 - q3 ∈ U := difference v3
  have hq1perp : q1 ∈ U.orthogonal :=
    U.orthogonal.starProjection_apply_mem v1
  have hq2perp : q2 ∈ U.orthogonal :=
    U.orthogonal.starProjection_apply_mem v2
  have hq3perp : q3 ∈ U.orthogonal :=
    U.orthogonal.starProjection_apply_mem v3
  have hq1W : q1 ∈ W := by
    have : q1 = v1 - (v1 - q1) := by abel
    rw [this]
    exact W.sub_mem hv1W (hUW hq1d)
  have hq2W : q2 ∈ W := by
    have : q2 = v2 - (v2 - q2) := by abel
    rw [this]
    exact W.sub_mem hv2W (hUW hq2d)
  have hq3W : q3 ∈ W := by
    have : q3 = v3 - (v3 - q3) := by abel
    rw [this]
    exact W.sub_mem hv3W (hUW hq3d)
  have hq1ne : q1 ≠ 0 := by
    intro hq
    apply hv1U
    simpa [hq] using hq1d
  have hq2ne : q2 ≠ 0 := by
    intro hq
    apply hv2U
    simpa [hq] using hq2d
  have hq3ne : q3 ≠ 0 := by
    intro hq
    apply hv3U
    simpa [hq] using hq3d
  have hdimV : Module.finrank Real
      (U.orthogonal ⊓ W : Submodule Real (E n)) = 2 := by
    have hadd := Submodule.finrank_add_inf_finrank_orthogonal hUW
    omega
  exact ⟨q1, q2, q3, ⟨hq1perp, hq1W⟩, ⟨hq2perp, hq2W⟩,
    ⟨hq3perp, hq3W⟩, hq1ne, hq2ne, hq3ne, hq1d, hq2d, hq3d, hdimV⟩

theorem conteggio_dimensionale {V : Submodule Real (E n)}
    (hdim : Module.finrank Real V = 2) {q1 q2 q3 : E n}
    (hq1 : q1 ∈ V) (hq2 : q2 ∈ V) (hq3 : q3 ∈ V) :
    ¬ LinearIndependent Real (fun i : Fin 3 =>
      if i.val = 0 then q1 else if i.val = 1 then q2 else q3) := by
  intro hli
  have hspan : Submodule.span Real (Set.range (fun i : Fin 3 =>
      if i.val = 0 then q1 else if i.val = 1 then q2 else q3)) ≤ V := by
    rw [Submodule.span_le]
    rintro z ⟨i, rfl⟩
    rcases i with ⟨iv, hi⟩
    interval_cases iv
    · exact hq1
    · exact hq2
    · exact hq3
  have hrank_span : Module.finrank Real (Submodule.span Real
      (Set.range (fun i : Fin 3 =>
        if i.val = 0 then q1 else if i.val = 1 then q2 else q3))) = 3 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hle := Submodule.finrank_mono hspan
  omega

theorem atMostTwo_middle_faces (P : ConvexPolytope n) {A B : Set (E n)}
    (hA : P.IsFace A) (hB : P.IsFace B)
    (hrank : faceDim B = faceDim A + 2)
    {C1 C2 C3 : Set (E n)}
    (hC1 : P.IsFace C1) (hA1 : A ⊂ C1) (h1B : C1 ⊂ B)
    (hC2 : P.IsFace C2) (hA2 : A ⊂ C2) (h2B : C2 ⊂ B)
    (hC3 : P.IsFace C3) (hA3 : A ⊂ C3) (h3B : C3 ⊂ B) :
    C1 = C2 ∨ C1 = C3 ∨ C2 = C3 := by
  classical
  by_contra hall
  push Not at hall
  rcases hall with ⟨h12, h13, h23⟩
  have hdC1lo := faceDim_lt_of_ssubset P hA hC1 hA1
  have hdC1hi := faceDim_lt_of_ssubset P hC1 hB h1B
  have hdC2lo := faceDim_lt_of_ssubset P hA hC2 hA2
  have hdC2hi := faceDim_lt_of_ssubset P hC2 hB h2B
  have hdC3lo := faceDim_lt_of_ssubset P hA hC3 hA3
  have hdC3hi := faceDim_lt_of_ssubset P hC3 hB h3B
  have hdC1 : faceDim C1 = faceDim A + 1 := by omega
  have hdC2 : faceDim C2 = faceDim A + 1 := by omega
  have hdC3 : faceDim C3 = faceDim A + 1 := by omega
  let Q := facePolytope P hB
  have hC1Q : Q.IsFace C1 := facePolytope_isFace_of P hB hC1 h1B.1
  have hC2Q : Q.IsFace C2 := facePolytope_isFace_of P hB hC2 h2B.1
  have hC3Q : Q.IsFace C3 := facePolytope_isFace_of P hB hC3 h3B.1
  obtain ⟨a, haA⟩ := hA.2
  obtain ⟨p1, hp1C, hp1out⟩ :=
    exists_point_outside_affineSpan_of_faceDim_lt hdC1lo
  obtain ⟨p2, hp2C, hp2out⟩ :=
    exists_point_outside_affineSpan_of_faceDim_lt hdC2lo
  obtain ⟨p3, hp3C, hp3out⟩ :=
    exists_point_outside_affineSpan_of_faceDim_lt hdC3lo
  have hp12 : p2 ∉ C1 := fuori_dalla_terza_relativo P hA hC1 hC2
    hA1 hA2 hdC1 hdC2 h12 hp2C hp2out
  have hp13 : p3 ∉ C1 := fuori_dalla_terza_relativo P hA hC1 hC3
    hA1 hA3 hdC1 hdC3 h13 hp3C hp3out
  have hp21 : p1 ∉ C2 := fuori_dalla_terza_relativo P hA hC2 hC1
    hA2 hA1 hdC2 hdC1 h12.symm hp1C hp1out
  have hp23 : p3 ∉ C2 := fuori_dalla_terza_relativo P hA hC2 hC3
    hA2 hA3 hdC2 hdC3 h23 hp3C hp3out
  have hp31 : p1 ∉ C3 := fuori_dalla_terza_relativo P hA hC3 hC1
    hA3 hA1 hdC3 hdC1 h13.symm hp1C hp1out
  have hp32 : p2 ∉ C3 := fuori_dalla_terza_relativo P hA hC3 hC2
    hA3 hA2 hdC3 hdC2 h23.symm hp2C hp2out
  obtain ⟨l1, hmem1, hmax1⟩ := espositore_di_faccia Q hC1Q
  obtain ⟨l2, hmem2, hmax2⟩ := espositore_di_faccia Q hC2Q
  obtain ⟨l3, hmem3, hmax3⟩ := espositore_di_faccia Q hC3Q
  have costanza : ∀ {D : Set (E n)} {lD : E n →L[Real] Real},
      (∀ y ∈ D, y ∈ Q.toSet ∧ ∀ z ∈ Q.toSet, lD z ≤ lD y) →
      ∀ {y y' : E n}, y ∈ D → y' ∈ D → lD y = lD y' := by
    intro D lD hmem y y' hy hy'
    exact le_antisymm ((hmem y' hy').2 y (hmem y hy).1)
      ((hmem y hy).2 y' (hmem y' hy').1)
  have strict : ∀ {Ci Cj : Set (E n)} {li : E n →L[Real] Real},
      Q.IsFace Ci → Q.IsFace Cj →
      (∀ y ∈ Ci, y ∈ Q.toSet ∧ ∀ z ∈ Q.toSet, li z ≤ li y) →
      (∀ q ∈ Q.toSet, (∀ z ∈ Q.toSet, li z ≤ li q) → q ∈ Ci) →
      a ∈ Ci → ∀ {p : E n}, p ∈ Cj → p ∉ Ci → li p < li a := by
    intro Ci Cj li hi hj hmem hmax ha p hpj hpnot
    have hpQ : p ∈ Q.toSet := face_subset_toSet Q hj hpj
    have hle : li p ≤ li a := (hmem a ha).2 p hpQ
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      apply hpnot
      exact hmax p hpQ
        (fun z hz => le_trans ((hmem a ha).2 z hz) (le_of_eq heq.symm))
  have s12 := strict hC1Q hC2Q hmem1 hmax1 (hA1.1 haA) hp2C hp12
  have s13 := strict hC1Q hC3Q hmem1 hmax1 (hA1.1 haA) hp3C hp13
  have s21 := strict hC2Q hC1Q hmem2 hmax2 (hA2.1 haA) hp1C hp21
  have s23 := strict hC2Q hC3Q hmem2 hmax2 (hA2.1 haA) hp3C hp23
  have s31 := strict hC3Q hC1Q hmem3 hmax3 (hA3.1 haA) hp1C hp31
  have s32 := strict hC3Q hC2Q hmem3 hmax3 (hA3.1 haA) hp2C hp32
  let U : Submodule Real (E n) := vectorSpan Real A
  let W : Submodule Real (E n) := vectorSpan Real B
  let v1 : E n := p1 - a
  let v2 : E n := p2 - a
  let v3 : E n := p3 - a
  have hUW : U ≤ W := vectorSpan_mono Real (hA1.1.trans h1B.1)
  have hv1W : v1 ∈ W := vsub_mem_vectorSpan Real (h1B.1 hp1C)
    (h1B.1 (hA1.1 haA))
  have hv2W : v2 ∈ W := vsub_mem_vectorSpan Real (h2B.1 hp2C)
    (h2B.1 (hA2.1 haA))
  have hv3W : v3 ∈ W := vsub_mem_vectorSpan Real (h3B.1 hp3C)
    (h3B.1 (hA3.1 haA))
  have hv1U : v1 ∉ U := by
    intro hv
    apply hp1out
    have hvdir : p1 - a ∈ (affineSpan Real A).direction := by
      rw [direction_affineSpan]
      simpa [U, v1] using hv
    simpa using AffineSubspace.vadd_mem_of_mem_direction hvdir
      (subset_affineSpan Real A haA)
  have hv2U : v2 ∉ U := by
    intro hv
    apply hp2out
    have hvdir : p2 - a ∈ (affineSpan Real A).direction := by
      rw [direction_affineSpan]
      simpa [U, v2] using hv
    simpa using AffineSubspace.vadd_mem_of_mem_direction hvdir
      (subset_affineSpan Real A haA)
  have hv3U : v3 ∉ U := by
    intro hv
    apply hp3out
    have hvdir : p3 - a ∈ (affineSpan Real A).direction := by
      rw [direction_affineSpan]
      simpa [U, v3] using hv
    simpa using AffineSubspace.vadd_mem_of_mem_direction hvdir
      (subset_affineSpan Real A haA)
  have hdimW : Module.finrank Real W = Module.finrank Real U + 2 := by
    change faceDim B = faceDim A + 2
    exact hrank
  obtain ⟨q1, q2, q3, hq1V, hq2V, hq3V, hq1ne, hq2ne, hq3ne,
      hv1q, hv2q, hv3q, hdimV⟩ :=
    proiezione_tre_vettori hUW hdimW hv1W hv2W hv3W hv1U hv2U hv3U
  have hdep := conteggio_dimensionale hdimV hq1V hq2V hq3V
  obtain ⟨gc, hgsum, i0, hgne⟩ := Fintype.not_linearIndependent_iff.mp hdep
  rw [Fin.sum_univ_three] at hgsum
  have hgsum3 : gc 0 • q1 + gc 1 • q2 + gc 2 • q3 = 0 := hgsum
  have hnz3 : gc 0 ≠ 0 ∨ gc 1 ≠ 0 ∨ gc 2 ≠ 0 := by
    rcases i0 with ⟨iv, hi⟩
    interval_cases iv
    · exact Or.inl hgne
    · exact Or.inr (Or.inl hgne)
    · exact Or.inr (Or.inr hgne)
  have kills : ∀ {Ci : Set (E n)} {li : E n →L[Real] Real},
      (∀ y ∈ Ci, y ∈ Q.toSet ∧ ∀ z ∈ Q.toSet, li z ≤ li y) →
      A ⊆ Ci → U ≤ LinearMap.ker li.toLinearMap := by
    intro Ci li hmem hAC
    change vectorSpan Real A ≤ LinearMap.ker li.toLinearMap
    rw [vectorSpan_eq_span_vsub_set_right Real haA, Submodule.span_le]
    rintro z ⟨x, hx, rfl⟩
    change li (x - a) = 0
    rw [map_sub]
    have heq := costanza hmem (hAC hx) (hAC haA)
    linarith
  have hkill1 := kills hmem1 hA1.1
  have hkill2 := kills hmem2 hA2.1
  have hkill3 := kills hmem3 hA3.1
  have eval_projection : ∀ (li : E n →L[Real] Real),
      U ≤ LinearMap.ker li.toLinearMap →
      ∀ (v q : E n), v - q ∈ U → li q = li v := by
    intro li hkill v q hvq
    have hz : li (v - q) = 0 := hkill hvq
    rw [map_sub] at hz
    linarith
  have hM1 := congrArg (fun w => l1 w) hgsum3
  have hM2 := congrArg (fun w => l2 w) hgsum3
  have hM3 := congrArg (fun w => l3 w) hgsum3
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at hM1 hM2 hM3
  have e11 : l1 q1 = 0 := by
    rw [eval_projection l1 hkill1 v1 q1 hv1q]
    change l1 (p1 - a) = 0
    rw [map_sub]
    have heq := costanza hmem1 hp1C (hA1.1 haA)
    linarith
  have e22 : l2 q2 = 0 := by
    rw [eval_projection l2 hkill2 v2 q2 hv2q]
    change l2 (p2 - a) = 0
    rw [map_sub]
    have heq := costanza hmem2 hp2C (hA2.1 haA)
    linarith
  have e33 : l3 q3 = 0 := by
    rw [eval_projection l3 hkill3 v3 q3 hv3q]
    change l3 (p3 - a) = 0
    rw [map_sub]
    have heq := costanza hmem3 hp3C (hA3.1 haA)
    linarith
  have rel1 : gc 1 * l1 q2 + gc 2 * l1 q3 = 0 := by
    rw [e11] at hM1
    linarith
  have rel2 : gc 0 * l2 q1 + gc 2 * l2 q3 = 0 := by
    rw [e22] at hM2
    linarith
  have rel3 : gc 0 * l3 q1 + gc 1 * l3 q2 = 0 := by
    rw [e33] at hM3
    linarith
  have n12 : l1 q2 < 0 := by
    rw [eval_projection l1 hkill1 v2 q2 hv2q]
    change l1 (p2 - a) < 0
    rw [map_sub]
    linarith
  have n13 : l1 q3 < 0 := by
    rw [eval_projection l1 hkill1 v3 q3 hv3q]
    change l1 (p3 - a) < 0
    rw [map_sub]
    linarith
  have n21 : l2 q1 < 0 := by
    rw [eval_projection l2 hkill2 v1 q1 hv1q]
    change l2 (p1 - a) < 0
    rw [map_sub]
    linarith
  have n23 : l2 q3 < 0 := by
    rw [eval_projection l2 hkill2 v3 q3 hv3q]
    change l2 (p3 - a) < 0
    rw [map_sub]
    linarith
  have n31 : l3 q1 < 0 := by
    rw [eval_projection l3 hkill3 v1 q1 hv1q]
    change l3 (p1 - a) < 0
    rw [map_sub]
    linarith
  have n32 : l3 q2 < 0 := by
    rw [eval_projection l3 hkill3 v2 q2 hv2q]
    change l3 (p2 - a) < 0
    rw [map_sub]
    linarith
  have hc0 : gc 0 ≠ 0 := by
    intro h0
    have h2 : gc 2 = 0 := by
      have hz : gc 2 * l2 q3 = 0 := by rw [h0] at rel2; linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt n23)
    have h1 : gc 1 = 0 := by
      have hz : gc 1 * l3 q2 = 0 := by rw [h0] at rel3; linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt n32)
    rcases hnz3 with h | h | h
    · exact h h0
    · exact h h1
    · exact h h2
  have hc1 : gc 1 ≠ 0 := by
    intro h1
    have h2 : gc 2 = 0 := by
      have hz : gc 2 * l1 q3 = 0 := by rw [h1] at rel1; linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt n13)
    have h0 : gc 0 = 0 := by
      have hz : gc 0 * l3 q1 = 0 := by rw [h1] at rel3; linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt n31)
    rcases hnz3 with h | h | h
    · exact h h0
    · exact h h1
    · exact h h2
  have hc2 : gc 2 ≠ 0 := by
    intro h2
    have h1 : gc 1 = 0 := by
      have hz : gc 1 * l1 q2 = 0 := by rw [h2] at rel1; linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt n12)
    have h0 : gc 0 = 0 := by
      have hz : gc 0 * l2 q1 = 0 := by rw [h2] at rel2; linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt n21)
    rcases hnz3 with h | h | h
    · exact h h0
    · exact h h1
    · exact h h2
  have h12s : gc 1 * gc 2 < 0 := segno_opposto rel1 n12 n13 hc1 hc2
  have h02s : gc 0 * gc 2 < 0 := segno_opposto rel2 n21 n23 hc0 hc2
  have h01s : gc 0 * gc 1 < 0 := segno_opposto rel3 n31 n32 hc0 hc1
  have hpos : 0 < (gc 0 * gc 1) * (gc 0 * gc 2) :=
    mul_pos_of_neg_of_neg h01s h02s
  nlinarith [hpos, h12s, sq_nonneg (gc 0)]

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart21

section BundlePart22
/- Source: Cubical/Polytope/SecondoIntermedio.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.SecondoIntermedio.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/





@[expose] public section

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : Nat}

theorem normale_relativa {A B : Set (E n)} (hAB : A <= B)
    (hrank : faceDim B = faceDim A + 1) :
    Exists fun w : E n =>
      And (Membership.mem (Min.min (vectorSpan Real A).orthogonal
        (vectorSpan Real B)) w) (Ne w 0) := by
  let U : Submodule Real (E n) := vectorSpan Real A
  let W : Submodule Real (E n) := vectorSpan Real B
  have hUW : U <= W := vectorSpan_mono Real hAB
  have hdim : Module.finrank Real W = Module.finrank Real U + 1 := by
    change faceDim B = faceDim A + 1
    exact hrank
  have hadd := Submodule.finrank_add_inf_finrank_orthogonal hUW
  let V : Submodule Real (E n) := Min.min U.orthogonal W
  have hone : Module.finrank Real V = 1 := by
    dsimp [V]
    omega
  have hpos : 0 < Module.finrank Real V := by omega
  letI : Nontrivial V := Module.finrank_pos_iff.mp hpos
  let w : V := (exists_ne (0 : V)).choose
  have hwne : Ne w 0 := (exists_ne (0 : V)).choose_spec
  have hwval : Ne (w : E n) 0 := by
    intro h
    apply hwne
    exact Subtype.ext h
  exact Exists.intro (w : E n) (And.intro w.property hwval)

theorem pivot_relativo (P : ConvexPolytope n) {A B : Set (E n)}
    (hA : P.IsFace A) (hB : P.IsFace B)
    (hrank : faceDim B = faceDim A + 2)
    {C : Set (E n)} (hC : P.IsFace C) (hAC : A < C) (hCB : C < B) :
    Exists fun C' : Set (E n) =>
      And (P.IsFace C') (And (A < C') (And (C' < B) (Ne C' C))) := by
  classical
  let Q : ConvexPolytope n := facePolytope P hB
  have hQtoSet : Q.toSet = B := facePolytope_toSet P hB
  have hAQ : Q.IsFace A :=
    facePolytope_isFace_of P hB hA (hAC.le.trans hCB.le)
  have hCQ : Q.IsFace C := facePolytope_isFace_of P hB hC hCB.le
  have hdClo := faceDim_lt_of_ssubset P hA hC hAC
  have hdChi := faceDim_lt_of_ssubset P hC hB hCB
  have hdC : faceDim C = faceDim A + 1 := by omega
  have hdCB : faceDim B = faceDim C + 1 := by omega
  let p0 : E n := hA.2.choose
  have hp0A : Membership.mem A p0 := hA.2.choose_spec
  let hc1ex := Set.exists_of_ssubset hAC
  let c1 : E n := hc1ex.choose
  have hc1spec := hc1ex.choose_spec
  have hc1C : Membership.mem C c1 := hc1spec.1
  have hc1A : Not (Membership.mem A c1) := hc1spec.2
  let hlex := hAQ.1 hAQ.2
  let l := hlex.choose
  have hl := hlex.choose_spec
  have hp0Q : Membership.mem Q.toSet p0 := face_subset_toSet Q hAQ hp0A
  have hlmax : forall y, Membership.mem Q.toSet y -> l y <= l p0 := by
    intro y hy
    have hp := hp0A
    rw [hl] at hp
    exact hp.2 y hy
  have hlchar : forall q, Membership.mem Q.toSet q -> l q = l p0 ->
      Membership.mem A q := by
    intro q hq heq
    rw [hl]
    exact And.intro hq
      (fun y hy => le_trans (hlmax y hy) (le_of_eq heq.symm))
  have hlconst : forall z, Membership.mem A z -> l z = l p0 := by
    intro z hz
    have hz' := hz
    rw [hl] at hz'
    exact le_antisymm (hlmax z hz'.1) (hz'.2 p0 hp0Q)
  have hc1Q : Membership.mem Q.toSet c1 := face_subset_toSet Q hCQ hc1C
  have hc1lt : l c1 < l p0 := by
    apply lt_of_le_of_ne (hlmax c1 hc1Q)
    exact fun heq => hc1A (hlchar c1 hc1Q heq)
  let hwex := normale_relativa hCB.le hdCB
  let w : E n := hwex.choose
  have hw := hwex.choose_spec.1
  have hwne := hwex.choose_spec.2
  have hwperp : Membership.mem (vectorSpan Real C).orthogonal w := hw.1
  have hwB : Membership.mem (vectorSpan Real B) w := hw.2
  have hwconstC : forall z, Membership.mem C z ->
      forall z', Membership.mem C z' ->
      inner Real w z = inner Real w z' := by
    intro z hz z' hz'
    have hmem : Membership.mem (vectorSpan Real C) (z - z') :=
      vsub_mem_vectorSpan Real hz hz'
    have hzero : inner Real (z - z') w = 0 := by
      have horth :=
        (Submodule.mem_orthogonal (vectorSpan Real C) w).mp hwperp
      exact horth (z - z') hmem
    rw [real_inner_comm] at hzero
    rw [inner_sub_right] at hzero
    linarith
  have hwQ : Membership.mem (vectorSpan Real Q.toSet) w := by
    simpa [hQtoSet] using hwB
  let hu0ex := exists_vertex_inner_ne Q hp0Q hwQ hwne
  let u0 : E n := hu0ex.choose
  have hu0spec := hu0ex.choose_spec
  have hu0V := hu0spec.1
  have hu0ne := hu0spec.2
  have costruzione : forall w' : E n,
      (forall z, Membership.mem C z -> forall z', Membership.mem C z' ->
        inner Real w' z = inner Real w' z') ->
      (Exists fun u => And (Membership.mem Q.vertices u)
        (inner Real w' p0 < inner Real w' u)) ->
      Exists fun F : Set (E n) =>
        And (P.IsFace F) (And (A < F) (And (F < B) (Ne F C))) := by
    intro w' hw'C hup
    let ux : E n := hup.choose
    have huxV := hup.choose_spec.1
    have huxgt := hup.choose_spec.2
    let S : Finset (E n) :=
      Q.vertices.filter (fun u => inner Real w' p0 < inner Real w' u)
    have hSne : S.Nonempty := Exists.intro ux
      (Finset.mem_filter.mpr (And.intro huxV huxgt))
    let r : E n -> Real := fun u =>
      (l p0 - l u) / (inner Real w' u - inner Real w' p0)
    let husex := S.exists_min_image r hSne
    let us : E n := husex.choose
    have husspec := husex.choose_spec
    have husS := husspec.1
    have husmin := husspec.2
    have husV : Membership.mem Q.vertices us :=
      (Finset.mem_filter.mp husS).1
    have husgt : inner Real w' p0 < inner Real w' us :=
      (Finset.mem_filter.mp husS).2
    have husQ : Membership.mem Q.toSet us := subset_convexHull Real _ husV
    have husC : Not (Membership.mem C us) := by
      intro hus
      have heq := hw'C us hus p0 (hAC.le hp0A)
      rw [heq] at husgt
      exact lt_irrefl _ husgt
    have husA : Not (Membership.mem A us) := fun hus => husC (hAC.le hus)
    have huslt : l us < l p0 := by
      apply lt_of_le_of_ne (hlmax us husQ)
      exact fun heq => husA (hlchar us husQ heq)
    let t : Real := r us
    have htpos : 0 < t := by
      dsimp [t, r]
      exact div_pos (by linarith) (by linarith)
    let psi : ContinuousLinearMap (RingHom.id Real) (E n) Real :=
      l + HSMul.hSMul t (innerSL Real w')
    have hpsival : forall y : E n,
        psi y = l y + t * inner Real w' y := by
      intro y
      dsimp [psi]
      simp [smul_apply, smul_eq_mul]
    have hvert : forall u, Membership.mem Q.vertices u -> psi u <= psi p0 := by
      intro u huV
      rw [hpsival, hpsival]
      by_cases hside : inner Real w' p0 < inner Real w' u
      case pos =>
        have huS : Membership.mem S u :=
          Finset.mem_filter.mpr (And.intro huV hside)
        have hrle : t <= r u := husmin u huS
        have hgap : 0 < inner Real w' u - inner Real w' p0 := by linarith
        have hmul : t * (inner Real w' u - inner Real w' p0) <=
            r u * (inner Real w' u - inner Real w' p0) :=
          mul_le_mul_of_nonneg_right hrle (le_of_lt hgap)
        have hcancel : r u * (inner Real w' u - inner Real w' p0) =
            l p0 - l u := by
          dsimp [r]
          field_simp
        nlinarith
      case neg =>
        push Not at hside
        have hlu : l u <= l p0 :=
          hlmax u (subset_convexHull Real _ huV)
        have hmul : t * inner Real w' u <= t * inner Real w' p0 :=
          mul_le_mul_of_nonneg_left hside (le_of_lt htpos)
        linarith
    have hbody : forall y, Membership.mem Q.toSet y -> psi y <= psi p0 := by
      intro y hy
      have hconv : Convex Real
          ((fun z : E n => psi z <= psi p0) : Set (E n)) := by
        apply convex_halfSpace_le
        exact psi.toLinearMap.isLinear
      have hsub : (Q.vertices : Set (E n)) <=
          ((fun z : E n => psi z <= psi p0) : Set (E n)) := by
        intro u hu
        exact hvert u (Finset.mem_coe.mp hu)
      exact convexHull_min hsub hconv hy
    have hpsiA : forall z, Membership.mem A z -> psi z = psi p0 := by
      intro z hz
      rw [hpsival, hpsival, hlconst z hz,
        hw'C z (hAC.le hz) p0 (hAC.le hp0A)]
    let F : Set (E n) := fun x =>
      And (Membership.mem Q.toSet x)
        (forall y, Membership.mem Q.toSet y -> psi y <= psi x)
    have hAF : A <= F := by
      intro z hz
      apply And.intro (face_subset_toSet Q hAQ hz)
      intro y hy
      rw [hpsiA z hz]
      exact hbody y hy
    have hp0F : Membership.mem F p0 := hAF hp0A
    have hFQ : Q.IsFace F := And.intro
      (fun _ => Exists.intro psi rfl) (Exists.intro p0 hp0F)
    have htie : psi us = psi p0 := by
      rw [hpsival, hpsival]
      have hgap : 0 < inner Real w' us - inner Real w' p0 := by linarith
      have hcancel : t * (inner Real w' us - inner Real w' p0) =
          l p0 - l us := by
        dsimp [t, r]
        field_simp
      nlinarith
    have husF : Membership.mem F us := by
      apply And.intro husQ
      intro y hy
      rw [htie]
      exact hbody y hy
    have hc1F : Not (Membership.mem F c1) := by
      intro hmem
      have heqpsi : psi c1 = psi p0 :=
        le_antisymm (hbody c1 hc1Q) (hmem.2 p0 hp0Q)
      rw [hpsival, hpsival] at heqpsi
      have heqinner : inner Real w' c1 = inner Real w' p0 :=
        hw'C c1 hc1C p0 (hAC.le hp0A)
      rw [heqinner] at heqpsi
      have : l c1 = l p0 := by linarith
      exact (ne_of_lt hc1lt) this
    have hFP : P.IsFace F := isFace_of_facePolytope P hB hFQ
    have hAFstrict : A < F := by
      apply And.intro hAF
      intro hFA
      exact husA (hFA husF)
    have hFBsub : F <= B := by
      intro x hx
      rw [hQtoSet.symm]
      exact hx.1
    have hFBstrict : F < B := by
      apply And.intro hFBsub
      intro hBF
      exact hc1F (hBF (hCB.le hc1C))
    have hFneC : Ne F C := by
      intro heq
      apply hc1F
      rw [heq]
      exact hc1C
    exact Exists.intro F
      (And.intro hFP (And.intro hAFstrict (And.intro hFBstrict hFneC)))
  by_cases hgt : inner Real w p0 < inner Real w u0
  case pos =>
    exact costruzione w hwconstC
      (Exists.intro u0 (And.intro hu0V hgt))
  case neg =>
    have hlt : inner Real w u0 < inner Real w p0 := by
      apply lt_of_le_of_ne (le_of_not_gt hgt)
      exact hu0ne
    exact costruzione (-w)
      (by
        intro z hz z' hz'
        rw [inner_neg_left, inner_neg_left, hwconstC z hz z' hz'])
      (Exists.intro u0 (And.intro hu0V (by
        rw [inner_neg_left, inner_neg_left]
        linarith)))

theorem secondo_intermedio (P : ConvexPolytope n) {A B : Set (E n)}
    (hA : P.IsFace A) (hB : P.IsFace B)
    (hrank : faceDim B = faceDim A + 2)
    {C : Set (E n)} (hC : P.IsFace C) (hAC : A < C) (hCB : C < B) :
    Exists fun C' : Set (E n) =>
      And (P.IsFace C') (And (A < C') (And (C' < B) (Ne C' C))) := by
  exact pivot_relativo P hA hB hrank hC hAC hCB

theorem existsUnique_other_middle (P : ConvexPolytope n)
    {A B : Set (E n)} (hA : P.IsFace A) (hB : P.IsFace B)
    (hrank : faceDim B = faceDim A + 2)
    {C : Set (E n)} (hC : P.IsFace C) (hAC : A < C) (hCB : C < B) :
    ExistsUnique fun C' : Set (E n) =>
      And (And (P.IsFace C') (And (A < C') (C' < B))) (Ne C' C) := by
  classical
  let hC'ex := secondo_intermedio P hA hB hrank hC hAC hCB
  let C' : Set (E n) := hC'ex.choose
  have hC'spec := hC'ex.choose_spec
  have hC'face := hC'spec.1
  have hAC' := hC'spec.2.1
  have hC'B := hC'spec.2.2.1
  have hC'C := hC'spec.2.2.2
  refine ExistsUnique.intro C'
    (And.intro (And.intro hC'face (And.intro hAC' hC'B)) hC'C) ?_
  intro C'' hC''
  have hcases := atMostTwo_middle_faces P hA hB hrank
    hC hAC hCB hC'face hAC' hC'B
    hC''.1.1 hC''.1.2.1 hC''.1.2.2
  have hnotFirst : Ne C C' := hC'C.symm
  have hnotSecond : Ne C C'' := hC''.2.symm
  have hC'C'' : C' = C'' :=
    (hcases.resolve_left hnotFirst).resolve_left hnotSecond
  exact hC'C''.symm

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart22

section BundlePart23
/- Source: Cubical/Polytope/FlagAdiacente.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.FlagAdiacente.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/








@[expose] public section

/-!
MOTORE COXETER, PASSO 4 — L'ADIACENZA DI BANDIERE (19 lug 2026).

La bandiera adiacente in rango `i`: stessa catena ovunque, faccia diversa
al solo rango `i`. Qui il montaggio per i ranghi con un vicino sopra e
uno sotto dentro la catena (0 < i, con la faccia superiore che è
`F.face (i+1)` per i ranghi interni e `P.toSet` per il rango massimo):
il diamante ∃! fornisce la faccia sostitutiva, `Function.update` rimonta
la bandiera, e i tre campi (`isFace`, `dim_eq`, `strict_mono`) si
verificano per casi.

Il caso di bordo `i = 0` (due vertici per spigolo) arriva dal fascicolo
40 e si innesterà nello stesso schema.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Bandiere adiacenti al rango `i`: coincidono ovunque tranne che in `i`. -/
def FlagAdjacentAt (P : ConvexPolytope n) (F G : P.Flag) (i : Fin n) :
    Prop :=
  (∀ j : Fin n, j ≠ i → G.face j = F.face j) ∧ G.face i ≠ F.face i

/-- La bandiera ottenuta sostituendo la faccia al rango `i`. -/
noncomputable def sostituisci (P : ConvexPolytope n) (F : P.Flag)
    (i : Fin n) (C : Set (E n)) (hC : P.IsFace C)
    (hdim : faceDim C = (i : ℕ))
    (hsotto : ∀ j : Fin n, j < i → F.face j ⊂ C)
    (hsopra : ∀ j : Fin n, i < j → C ⊂ F.face j) : P.Flag where
  face := Function.update F.face i C
  isFace := by
    intro k
    by_cases hk : k = i
    · rw [hk, Function.update_self]
      exact hC
    · rw [Function.update_of_ne hk]
      exact F.isFace k
  dim_eq := by
    intro k
    by_cases hk : k = i
    · rw [hk, Function.update_self]
      exact hdim
    · rw [Function.update_of_ne hk]
      exact F.dim_eq k
  strict_mono := by
    intro j k hjk
    by_cases hj : j = i
    · subst hj
      have hk : j ≠ k := ne_of_lt hjk
      rw [Function.update_self, Function.update_of_ne (Ne.symm hk)]
      exact hsopra k hjk
    · by_cases hk : k = i
      · subst hk
        rw [Function.update_of_ne hj, Function.update_self]
        exact hsotto j hjk
      · rw [Function.update_of_ne hj, Function.update_of_ne hk]
        exact F.strict_mono j k hjk

@[simp] theorem sostituisci_face_self (P : ConvexPolytope n) (F : P.Flag)
    (i : Fin n) (C : Set (E n)) (hC hdim hsotto hsopra) :
    (sostituisci P F i C hC hdim hsotto hsopra).face i = C :=
  Function.update_self ..

@[simp] theorem sostituisci_face_ne (P : ConvexPolytope n) (F : P.Flag)
    (i : Fin n) (C : Set (E n)) (hC hdim hsotto hsopra)
    {j : Fin n} (hj : j ≠ i) :
    (sostituisci P F i C hC hdim hsotto hsopra).face j = F.face j :=
  Function.update_of_ne hj _ _

/-- Le facce sotto la sostituita restano dentro: la catena sotto `i` è
già dentro `F.face (i-1) ⊂ C` quando `C` viene dal diamante. -/
theorem catena_sotto (P : ConvexPolytope n) (F : P.Flag) {i : Fin n}
    {C : Set (E n)} {im : Fin n} (him : (im : ℕ) + 1 = (i : ℕ))
    (hAC : F.face im ⊂ C) :
    ∀ j : Fin n, j < i → F.face j ⊂ C := by
  intro j hj
  by_cases hjim : j = im
  · rw [hjim]; exact hAC
  · have hjlt : j < im := by
      rw [Fin.lt_def] at hj ⊢
      have hne : (j : ℕ) ≠ (im : ℕ) := fun h => hjim (Fin.ext h)
      omega
    exact (F.strict_mono j im hjlt).trans hAC

/-- Le facce sopra la sostituita restano fuori. -/
theorem catena_sopra (P : ConvexPolytope n) (F : P.Flag) {i : Fin n}
    {C : Set (E n)} {ip : Fin n} (hip : (i : ℕ) + 1 = (ip : ℕ))
    (hCB : C ⊂ F.face ip) :
    ∀ j : Fin n, i < j → C ⊂ F.face j := by
  intro j hj
  by_cases hjip : j = ip
  · rw [hjip]; exact hCB
  · have hjgt : ip < j := by
      rw [Fin.lt_def] at hj ⊢
      have hne : (j : ℕ) ≠ (ip : ℕ) := fun h => hjip (Fin.ext h)
      omega
    exact hCB.trans (F.strict_mono ip j hjgt)

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart23

section BundlePart24
/- Source: Cubical/Polytope/AdiacenzaUnica.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.AdiacenzaUnica.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/








@[expose] public section

/-!
MOTORE COXETER, PASSO 6 — L'ADIACENZA È UNICA (19 lug 2026).

Il teorema unificato: per ogni bandiera `F` di un politopo pieno e ogni
rango `i`, esiste UN'UNICA bandiera adiacente a `F` in `i`. I tre casi
del vaglio (i = 0, interno, i = n−1) si compattano in due grazie alla
«faccia sopra» unificata: `F.face (i+1)` per i ranghi interni, `P.toSet`
per il rango massimo — in entrambi i casi una faccia di dimensione
`i+1` che contiene strettamente `F.face i`.

- `i = 0`: l'altro vertice dello spigolo (`due_vertici_per_spigolo`).
- `i > 0`: il diamante relativo (`existsUnique_other_middle`).

Il rimontaggio in bandiera passa per `sostituisci` (Function.update),
l'unicità per l'estensionalità delle bandiere: la catena determina la
bandiera, perché gli altri campi sono proposizioni.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Estensionalità delle bandiere: la catena di facce determina la
bandiera (gli altri campi sono proposizioni). -/
theorem flag_ext {P : ConvexPolytope n} {F G : P.Flag}
    (h : F.face = G.face) : F = G := by
  cases F with
  | mk f hf hd hm =>
    cases G with
    | mk g hg hd' hm' =>
      dsimp only at h
      subst h
      rfl

/-- La «faccia sopra» il rango `i`: `F.face (i+1)` per i ranghi interni,
`P.toSet` per il rango massimo. In entrambi i casi: una faccia di
dimensione `i+1` sopra `F.face i`, sotto tutte le facce dei ranghi
superiori, e massimale fra le facce di dimensione `i` incastrate
nella coda della bandiera. -/
theorem faccia_sopra (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F : P.Flag) (i : Fin n) :
    ∃ B : Set (E n), P.IsFace B ∧ faceDim B = (i : ℕ) + 1 ∧
      F.face i ⊂ B ∧
      (∀ j : Fin n, i < j → B ⊆ F.face j) ∧
      (∀ D : Set (E n), P.IsFace D → faceDim D = (i : ℕ) →
        (∀ j : Fin n, i < j → D ⊂ F.face j) → D ⊂ B) := by
  by_cases hi : (i : ℕ) + 1 < n
  · -- rango interno: B = F.face (i+1)
    refine ⟨F.face ⟨(i : ℕ) + 1, hi⟩, F.isFace _, ?_, ?_, ?_, ?_⟩
    · exact F.dim_eq _
    · refine F.strict_mono i ⟨(i : ℕ) + 1, hi⟩ ?_
      rw [Fin.lt_def]
      show (i : ℕ) < (i : ℕ) + 1
      omega
    · intro j hj
      rcases Nat.lt_or_ge ((i : ℕ) + 1) (j : ℕ) with hlt | hge
      · refine (F.strict_mono ⟨(i : ℕ) + 1, hi⟩ j ?_).subset
        rw [Fin.lt_def]
        show (i : ℕ) + 1 < (j : ℕ)
        exact hlt
      · have hje : j = ⟨(i : ℕ) + 1, hi⟩ := by
          apply Fin.ext
          show (j : ℕ) = (i : ℕ) + 1
          rw [Fin.lt_def] at hj
          omega
        subst hje
        exact subset_rfl
    · intro D _ _ hDj
      refine hDj ⟨(i : ℕ) + 1, hi⟩ ?_
      rw [Fin.lt_def]
      show (i : ℕ) < (i : ℕ) + 1
      omega
  · -- rango massimo: B = P.toSet
    have hin : (i : ℕ) + 1 = n := by
      have := i.isLt
      omega
    have hPdim : faceDim P.toSet = n := hfull
    refine ⟨P.toSet, toSet_isFace P, ?_, ?_, ?_, ?_⟩
    · rw [hPdim]
      omega
    · refine (face_subset_toSet P (F.isFace i)).ssubset_of_ne ?_
      intro heq
      have hdi := F.dim_eq i
      rw [heq, hPdim] at hdi
      have := i.isLt
      omega
    · intro j hj
      exfalso
      rw [Fin.lt_def] at hj
      have := j.isLt
      omega
    · intro D hD hdD _
      refine (face_subset_toSet P hD).ssubset_of_ne ?_
      intro heq
      rw [heq, hPdim] at hdD
      omega

/-- **Il teorema dell'adiacenza**: per ogni bandiera `F` di un politopo
pieno e ogni rango `i`, esiste un'unica bandiera adiacente a `F` in `i`.
È il primo cancello del motore Coxeter: la mossa elementare sulle
bandiere è ben definita e involutiva. -/
theorem existsUnique_flag_adjacent (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    ∃! G : P.Flag, FlagAdjacentAt P F G i := by
  obtain ⟨B, hB, hdB, hFiB, hBsub, hDB⟩ := faccia_sopra P hfull F i
  -- Passo 1: l'unica faccia sostitutiva al rango i.
  have hQ : ∃! C : Set (E n),
      (P.IsFace C ∧ faceDim C = (i : ℕ) ∧
        (∀ j : Fin n, j < i → F.face j ⊂ C) ∧ C ⊂ B) ∧
      C ≠ F.face i := by
    by_cases hi0 : (i : ℕ) = 0
    · -- caso di bordo: l'altro vertice dello spigolo B
      have hdB1 : faceDim B = 1 := by rw [hdB, hi0]
      have hdV : faceDim (F.face i) = 0 := by
        rw [F.dim_eq]
        exact hi0
      have hVB : F.face i < B := hFiB
      obtain ⟨W, ⟨⟨hWface, hWdim, hWB⟩, hWne⟩, hWuniq⟩ :=
        due_vertici_per_spigolo P hB hdB1 (F.isFace i) hdV hVB
      refine ⟨W, ⟨⟨hWface, ?_, ?_, hWB⟩, hWne⟩, ?_⟩
      · rw [hWdim, hi0]
      · intro j hj
        exfalso
        rw [Fin.lt_def, hi0] at hj
        omega
      · intro C hC
        refine hWuniq C ⟨⟨hC.1.1, ?_, hC.1.2.2.2⟩, hC.2⟩
        rw [hC.1.2.1, hi0]
    · -- caso generale: il diamante relativo sotto B
      have hipos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi0
      obtain ⟨iv, hiv⟩ : ∃ iv : ℕ, (i : ℕ) = iv + 1 :=
        ⟨(i : ℕ) - 1, by omega⟩
      have hivn : iv < n := by
        have := i.isLt
        omega
      have him : ((⟨iv, hivn⟩ : Fin n) : ℕ) + 1 = (i : ℕ) := by
        show iv + 1 = (i : ℕ)
        omega
      have himlt : (⟨iv, hivn⟩ : Fin n) < i := by
        rw [Fin.lt_def]
        show iv < (i : ℕ)
        omega
      have hrank : faceDim B = faceDim (F.face ⟨iv, hivn⟩) + 2 := by
        rw [hdB, F.dim_eq]
        show (i : ℕ) + 1 = iv + 2
        omega
      have hAC : F.face ⟨iv, hivn⟩ < F.face i := F.strict_mono _ i himlt
      have hCB : F.face i < B := hFiB
      obtain ⟨C', ⟨⟨hC'face, hAC', hC'B⟩, hC'ne⟩, hC'uniq⟩ :=
        existsUnique_other_middle P (F.isFace ⟨iv, hivn⟩) hB hrank
          (F.isFace i) hAC hCB
      have hdC' : faceDim C' = (i : ℕ) := by
        have h1 := faceDim_lt_of_ssubset P (F.isFace ⟨iv, hivn⟩) hC'face hAC'
        have h2 := faceDim_lt_of_ssubset P hC'face hB hC'B
        rw [F.dim_eq] at h1
        rw [hdB] at h2
        have h1' : iv < faceDim C' := h1
        omega
      refine ⟨C', ⟨⟨hC'face, hdC', ?_, hC'B⟩, hC'ne⟩, ?_⟩
      · exact catena_sotto P F him hAC'
      · intro C hC
        exact hC'uniq C ⟨⟨hC.1.1, hC.1.2.2.1 _ himlt, hC.1.2.2.2⟩, hC.2⟩
  -- Passo 2: il rimontaggio in bandiera e l'unicità.
  obtain ⟨C, ⟨⟨hCface, hCdim, hCsotto, hCB⟩, hCne⟩, hCuniq⟩ := hQ
  have hCsopra : ∀ j : Fin n, i < j → C ⊂ F.face j := by
    intro j hj
    exact ssubset_of_ssubset_of_subset hCB (hBsub j hj)
  refine ⟨sostituisci P F i C hCface hCdim hCsotto hCsopra, ⟨?_, ?_⟩, ?_⟩
  · intro j hj
    exact sostituisci_face_ne P F i C hCface hCdim hCsotto hCsopra hj
  · rw [sostituisci_face_self]
    exact hCne
  · intro G' hG'
    obtain ⟨hG'eq, hG'ne⟩ := hG'
    have hQ' : (P.IsFace (G'.face i) ∧ faceDim (G'.face i) = (i : ℕ) ∧
        (∀ j : Fin n, j < i → F.face j ⊂ G'.face i) ∧ G'.face i ⊂ B) ∧
        G'.face i ≠ F.face i := by
      refine ⟨⟨G'.isFace i, G'.dim_eq i, ?_, ?_⟩, hG'ne⟩
      · intro j hj
        rw [← hG'eq j (ne_of_lt hj)]
        exact G'.strict_mono j i hj
      · refine hDB (G'.face i) (G'.isFace i) (G'.dim_eq i) ?_
        intro j hj
        rw [← hG'eq j (ne_of_gt hj)]
        exact G'.strict_mono i j hj
    have hCeq : G'.face i = C := hCuniq (G'.face i) hQ'
    apply flag_ext
    funext j
    by_cases hj : j = i
    · subst hj
      rw [sostituisci_face_self]
      exact hCeq
    · rw [sostituisci_face_ne P F i C hCface hCdim hCsotto hCsopra hj]
      exact hG'eq j hj

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart24

section BundlePart25
/- Source: Cubical/Polytope/MossaInvolutiva.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.MossaInvolutiva.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/





@[expose] public section

/-!
MOTORE COXETER, PASSO 7 — LA MOSSA INVOLUTIVA (19 lug 2026).

Dal teorema di unicità l'adiacenza diventa una FUNZIONE sulle bandiere:
`adjacentFlag P hfull F i` è l'unica bandiera adiacente a `F` in `i`.
La relazione è simmetrica, quindi la mossa è un'involuzione senza punti
fissi: il germe combinatorio delle riflessioni semplici `rᵢ² = 1`.
-/

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La bandiera adiacente a `F` al rango `i` (l'unica). -/
noncomputable def adjacentFlag (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F : P.Flag) (i : Fin n) : P.Flag :=
  (existsUnique_flag_adjacent P hfull F i).choose

theorem adjacentFlag_isAdjacent (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    FlagAdjacentAt P F (adjacentFlag P hfull F i) i :=
  (existsUnique_flag_adjacent P hfull F i).choose_spec.1

/-- Ogni bandiera adiacente a `F` in `i` È la bandiera adiacente. -/
theorem adjacentFlag_eq_of_isAdjacent (P : ConvexPolytope n)
    (hfull : P.IsFullDim) {F G : P.Flag} (i : Fin n)
    (h : FlagAdjacentAt P F G i) : G = adjacentFlag P hfull F i :=
  (existsUnique_flag_adjacent P hfull F i).choose_spec.2 G h

/-- L'adiacenza di bandiere è simmetrica. -/
theorem flagAdjacentAt_symm (P : ConvexPolytope n) {F G : P.Flag}
    {i : Fin n} (h : FlagAdjacentAt P F G i) :
    FlagAdjacentAt P G F i :=
  ⟨fun j hj => (h.1 j hj).symm, (h.2).symm⟩

/-- **La mossa è un'involuzione**: andare e tornare riporta a `F`. -/
theorem adjacentFlag_involutive (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    adjacentFlag P hfull (adjacentFlag P hfull F i) i = F :=
  (adjacentFlag_eq_of_isAdjacent P hfull i
    (flagAdjacentAt_symm P (adjacentFlag_isAdjacent P hfull F i))).symm

/-- La mossa non ha punti fissi. -/
theorem adjacentFlag_ne (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F : P.Flag) (i : Fin n) :
    adjacentFlag P hfull F i ≠ F := by
  intro heq
  have h := (adjacentFlag_isAdjacent P hfull F i).2
  rw [heq] at h
  exact h rfl

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart25

section BundlePart26
/- Source: Cubical/Polytope/Equivarianza.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Equivarianza.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/






@[expose] public section

/-!
MOTORE COXETER, PASSO 8 — L'AZIONE SULLE BANDIERE E L'EQUIVARIANZA
(19 lug 2026).

I lemmi d'immagine della fase 3A (Immagini.lean) rifatti in dimensione
arbitraria: una simmetria trasporta facce in facce preservando la
dimensione. Ne segue l'azione `mapFlag` delle simmetrie sulle bandiere
e il lemma di EQUIVARIANZA: la mossa di adiacenza commuta con l'azione.
Con l'unicità già certificata, la commutazione è un montaggio: l'immagine
dell'adiacente è adiacente all'immagine, dunque È l'adiacente
dell'immagine.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Le esposizioni si trasportano lungo le isometrie affini (ogni `n`). -/
theorem isExposed_image_isomN (φ : Isom n) {A B : Set (E n)}
    (h : IsExposed ℝ A B) : IsExposed ℝ ((⇑φ) '' A) ((⇑φ) '' B) := by
  intro hne
  obtain ⟨b, hbB⟩ := hne
  obtain ⟨a, haB, hab⟩ := hbB
  obtain ⟨l, hl⟩ := h ⟨a, haB⟩
  let l' : E n →L[ℝ] ℝ :=
    l.comp φ.symm.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  have hl' (x : E n) : l' (φ x) = l x - l (φ.symm 0) := by
    have hm := φ.symm.map_vsub (φ x) 0
    have hm' : φ.symm.linearIsometryEquiv (φ x) = x - φ.symm 0 := by
      simpa using hm
    simp only [l', ContinuousLinearMap.comp_apply]
    change l (φ.symm.linearIsometryEquiv (φ x)) = _
    rw [hm', map_sub]
  refine ⟨l', Set.ext ?_⟩
  intro x
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [hl] at hb
    refine ⟨⟨b, hb.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hl' y, hl' b]
    exact sub_le_sub_right (hb.2 y hy) _
  · rintro ⟨hxA, hxmax⟩
    obtain ⟨a, ha, rfl⟩ := hxA
    refine ⟨a, ?_, rfl⟩
    rw [hl]
    refine ⟨ha, ?_⟩
    intro y hy
    have hle := hxmax (φ y) ⟨y, hy, rfl⟩
    rw [hl' y, hl' a] at hle
    linarith

/-- Le isometrie affini preservano la dimensione delle facce (ogni `n`). -/
theorem faceDim_image_isomN (φ : Isom n) (F : Set (E n)) :
    faceDim ((⇑φ) '' F) = faceDim F := by
  unfold ConvexPolytope.faceDim
  have hmap := φ.toAffineEquiv.toAffineMap.map_vectorSpan (s := F)
  change Submodule.map (φ.toAffineEquiv.linear : E n →ₗ[ℝ] E n)
    (vectorSpan ℝ F) = vectorSpan ℝ ((⇑φ) '' F) at hmap
  rw [← hmap]
  exact φ.toAffineEquiv.linear.finrank_map_eq (vectorSpan ℝ F)

/-- Una simmetria trasporta facce in facce (ogni `n`). -/
theorem isFace_image_isomN {P : ConvexPolytope n} (φ : Isom n)
    (hφ : P.isSymmetry φ) {F : Set (E n)} (hF : P.IsFace F) :
    P.IsFace ((⇑φ) '' F) := by
  refine ⟨?_, hF.2.image _⟩
  rw [← hφ]
  exact isExposed_image_isomN φ hF.1

/-- L'identità è una simmetria (ogni `n`). -/
theorem symmetry_reflN (P : ConvexPolytope n) :
    P.isSymmetry (AffineIsometryEquiv.refl ℝ (E n)) :=
  Set.image_id _

/-- Le simmetrie sono chiuse per composizione (ogni `n`). -/
theorem symmetry_transN {P : ConvexPolytope n} {φ ψ : Isom n}
    (hφ : P.isSymmetry φ) (hψ : P.isSymmetry ψ) :
    P.isSymmetry (φ.trans ψ) := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    (⇑(φ.trans ψ)) '' P.toSet = (⇑ψ) '' ((⇑φ) '' P.toSet) := by
      rw [Set.image_image]
      rfl
    _ = P.toSet := by rw [hφ, hψ]

/-- Le simmetrie sono chiuse per inversa (ogni `n`). -/
theorem symmetry_symmN {P : ConvexPolytope n} {φ : Isom n}
    (hφ : P.isSymmetry φ) : P.isSymmetry φ.symm := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    (⇑φ.symm) '' P.toSet = (⇑φ.symm) '' ((⇑φ) '' P.toSet) := by rw [hφ]
    _ = P.toSet := φ.toEquiv.symm_image_image P.toSet

/-- **L'azione delle simmetrie sulle bandiere**: l'immagine di una
bandiera lungo una simmetria è una bandiera. -/
noncomputable def mapFlag (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) (F : P.Flag) : P.Flag where
  face k := (⇑φ) '' F.face k
  isFace k := isFace_image_isomN φ hφ (F.isFace k)
  dim_eq k := by
    rw [faceDim_image_isomN]
    exact F.dim_eq k
  strict_mono i j hij := by
    have h := F.strict_mono i j hij
    have hparts := Set.ssubset_iff_subset_ne.mp h
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.image_mono hparts.1, ?_⟩
    intro heq
    exact hparts.2 ((Set.image_injective.mpr φ.injective) heq)

@[simp] theorem mapFlag_face (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) (F : P.Flag) (k : Fin n) :
    (mapFlag P hφ F).face k = (⇑φ) '' F.face k := rfl

/-- L'adiacenza è equivariante: l'azione conserva la relazione. -/
theorem flagAdjacentAt_map (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) {F G : P.Flag} {i : Fin n}
    (h : FlagAdjacentAt P F G i) :
    FlagAdjacentAt P (mapFlag P hφ F) (mapFlag P hφ G) i := by
  constructor
  · intro j hj
    show (⇑φ) '' G.face j = (⇑φ) '' F.face j
    rw [h.1 j hj]
  · show (⇑φ) '' G.face i ≠ (⇑φ) '' F.face i
    intro heq
    exact h.2 ((Set.image_injective.mpr φ.injective) heq)

/-- **EQUIVARIANZA DELLA MOSSA**: la mossa di adiacenza commuta con
l'azione delle simmetrie. Il cuore: per l'unicità, l'immagine
dell'adiacente — che è adiacente all'immagine — È l'adiacente
dell'immagine. -/
theorem mapFlag_adjacentFlag (P : ConvexPolytope n) (hfull : P.IsFullDim)
    {φ : Isom n} (hφ : P.isSymmetry φ) (F : P.Flag) (i : Fin n) :
    mapFlag P hφ (adjacentFlag P hfull F i) =
      adjacentFlag P hfull (mapFlag P hφ F) i :=
  adjacentFlag_eq_of_isAdjacent P hfull i
    (flagAdjacentAt_map P hφ (adjacentFlag_isAdjacent P hfull F i))

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart26

section BundlePart27
/- Source: Cubical/Polytope/Gallerie.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Gallerie.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/







@[expose] public section

/-!
MOTORE COXETER, PASSO 12 — IL LINGUAGGIO DELLE GALLERIE (19 lug 2026).

La mossa elementare (`FlagStep`) e la connessione per gallerie
(`GalleryConnected`, chiusura riflessivo-transitiva). Qui i lemmi
strutturali: la mossa è simmetrica, la connessione è un'equivalenza,
e l'azione delle simmetrie la rispetta. Il teorema profondo — OGNI due
bandiere sono connesse — è il muro successivo e vivrà in un modulo suo.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La mossa elementare: `G` differisce da `F` in un solo rango. -/
def FlagStep (P : ConvexPolytope n) (F G : P.Flag) : Prop :=
  ∃ i : Fin n, FlagAdjacentAt P F G i

/-- Connessione per gallerie: una catena finita di mosse elementari. -/
def GalleryConnected (P : ConvexPolytope n) (F G : P.Flag) : Prop :=
  Relation.ReflTransGen (FlagStep P) F G

/-- La mossa elementare è simmetrica. -/
theorem flagStep_symm (P : ConvexPolytope n) {F G : P.Flag}
    (h : FlagStep P F G) : FlagStep P G F := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, flagAdjacentAt_symm P hi⟩

theorem galleryConnected_refl (P : ConvexPolytope n) (F : P.Flag) :
    GalleryConnected P F F :=
  Relation.ReflTransGen.refl

theorem galleryConnected_trans (P : ConvexPolytope n) {F G H : P.Flag}
    (h₁ : GalleryConnected P F G) (h₂ : GalleryConnected P G H) :
    GalleryConnected P F H :=
  Relation.ReflTransGen.trans h₁ h₂

/-- La connessione per gallerie è simmetrica. -/
theorem galleryConnected_symm (P : ConvexPolytope n) {F G : P.Flag}
    (h : GalleryConnected P F G) : GalleryConnected P G F := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (flagStep_symm P hstep)) ih

/-- Un passo di adiacenza è una galleria. -/
theorem galleryConnected_adjacent (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    GalleryConnected P F (adjacentFlag P hfull F i) :=
  Relation.ReflTransGen.single ⟨i, adjacentFlag_isAdjacent P hfull F i⟩

/-- Le simmetrie trasportano mosse in mosse. -/
theorem flagStep_map (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) {F G : P.Flag} (h : FlagStep P F G) :
    FlagStep P (mapFlag P hφ F) (mapFlag P hφ G) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, flagAdjacentAt_map P hφ hi⟩

/-- **Equivarianza delle gallerie**: l'azione rispetta la connessione. -/
theorem galleryConnected_map (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) {F G : P.Flag} (h : GalleryConnected P F G) :
    GalleryConnected P (mapFlag P hφ F) (mapFlag P hφ G) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (flagStep_map P hφ hstep)

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart27

section BundlePart28
/- Source: Cubical/Polytope/Connettivita.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Connettivita.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/








@[expose] public section

/-!
MOTORE COXETER, PASSO 17 — INFRASTRUTTURA DELLE GALLERIE E IL MURO
(19 lug 2026).

Il muro grande del motore resta la connettività: che ogni due bandiere
siano collegate da una galleria. Qui NON lo si dimostra. Si certifica
l'infrastruttura che servirà alla dimostrazione, e si scrive il muro
nella sua forma corretta, che è locale e più debole della tesi:

`RidgeConnected P` — dentro ogni faccia `B`, due facce di codimensione 1
sono collegate da una catena in cui consecutive si incontrano in una
faccia di codimensione 2. È la connettività del grafo delle faccette
(Balinski in forma debole), il fatto geometrico da cui la connettività
per gallerie discende per induzione sul rango.

Attenzione a non confondere questo con l'enunciato «due bandiere che
coincidono sopra il rango massimo sono connesse», che è vacuo: coincidere
sopra `n − 1` non è un'ipotesi, è la tesi generale travestita.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Due bandiere coincidono dal rango `m` in su. -/
def AgreeAbove (P : ConvexPolytope n) (F G : P.Flag) (m : ℕ) : Prop :=
  ∀ k : Fin n, m ≤ (k : ℕ) → F.face k = G.face k

theorem agreeAbove_zero (P : ConvexPolytope n) {F G : P.Flag}
    (h : AgreeAbove P F G 0) : F = G := by
  apply flag_ext
  funext k
  exact h k (Nat.zero_le _)

theorem agreeAbove_mono (P : ConvexPolytope n) {F G : P.Flag} {m m' : ℕ}
    (hmm : m ≤ m') (h : AgreeAbove P F G m) : AgreeAbove P F G m' :=
  fun k hk => h k (le_trans hmm hk)

/-- Sopra il rango massimo l'ipotesi è vuota: `AgreeAbove _ _ n` non dice
nulla. Registrato esplicitamente per non scambiarlo per un'induzione. -/
theorem agreeAbove_of_ge (P : ConvexPolytope n) (F G : P.Flag) {m : ℕ}
    (hm : n ≤ m) : AgreeAbove P F G m := by
  intro k hk
  exfalso
  have := k.isLt
  omega

/-- Bandiere adiacenti coincidono sopra il rango della mossa più uno. -/
theorem agreeAbove_of_adjacent (P : ConvexPolytope n) {F G : P.Flag}
    {i : Fin n} (h : FlagAdjacentAt P F G i) :
    AgreeAbove P F G ((i : ℕ) + 1) := by
  intro k hk
  refine (h.1 k (fun hki => ?_)).symm
  rw [hki] at hk
  omega

/-- Se due bandiere coincidono fuori da un rango, sono connesse (uguali
oppure adiacenti). -/
theorem galleryConnected_of_agree_except (P : ConvexPolytope n)
    (F G : P.Flag) (i : Fin n)
    (h : ∀ j : Fin n, j ≠ i → F.face j = G.face j) :
    GalleryConnected P F G := by
  by_cases heq : G.face i = F.face i
  · have hFG : F = G := by
      apply flag_ext
      funext k
      by_cases hk : k = i
      · rw [hk, heq]
      · exact h k hk
    rw [hFG]
    exact galleryConnected_refl P G
  · exact Relation.ReflTransGen.single
      ⟨i, ⟨fun j hj => (h j hj).symm, heq⟩⟩

/-- **IL MURO, in forma locale.** Dentro ogni faccia `B`, due facce di
codimensione 1 in `B` sono collegate da una catena di facce di
codimensione 1 in cui due consecutive si incontrano in una faccia di
codimensione 2. È la connettività del grafo delle faccette. -/
def RidgeConnected (P : ConvexPolytope n) : Prop :=
  ∀ (B : Set (E n)), P.IsFace B →
    ∀ (A A' : Set (E n)), P.IsFace A → P.IsFace A' →
      A ⊂ B → A' ⊂ B →
      faceDim A + 1 = faceDim B → faceDim A' + 1 = faceDim B →
      Relation.ReflTransGen
        (fun X Y : Set (E n) =>
          P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
            faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
            ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
              faceDim R + 2 = faceDim B)
        A A'

/-- La relazione di adiacenza fra faccette è simmetrica. -/
theorem ridgeStep_symm (P : ConvexPolytope n) (B X Y : Set (E n))
    (h : P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
      faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
      ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
        faceDim R + 2 = faceDim B) :
    P.IsFace Y ∧ P.IsFace X ∧ Y ⊂ B ∧ X ⊂ B ∧
      faceDim Y + 1 = faceDim B ∧ faceDim X + 1 = faceDim B ∧
      ∃ R : Set (E n), P.IsFace R ∧ R ⊂ Y ∧ R ⊂ X ∧
        faceDim R + 2 = faceDim B := by
  obtain ⟨hX, hY, hXB, hYB, hdX, hdY, R, hR, hRX, hRY, hdR⟩ := h
  exact ⟨hY, hX, hYB, hXB, hdY, hdX, R, hR, hRY, hRX, hdR⟩

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart28

section BundlePart29
/- Source: Cubical/Polytope/ConnettivitaGlobale.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ConnettivitaGlobale.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




@[expose] public section

/-!
MOTORE COXETER, U4 — DAL MURO LOCALE ALLE GALLERIE GLOBALI (20 lug 2026).

Questo modulo isola e chiude la riduzione combinatoria

`RidgeConnected P → ∀ F G : P.Flag, GalleryConnected P F G`.

Il caso inferiore non usa `RidgeConnected`: due bandiere che coincidono
dal rango 1 differiscono al più nel rango 0.  Nel passo induttivo, la
catena di faccette fornita da `RidgeConnected` viene sollevata a bandiere.
Per ogni ridge si ricostruisce una catena completa sotto di esso; così le
due bandiere ai lati del ridge differiscono in un solo rango.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La forma corretta e sufficiente del muro locale.  Il vincolo
`2 ≤ faceDim B` è essenziale perché il modello di faccia del benchmark
esclude la faccia vuota: per `faceDim B = 1` non esiste una ridge di
dimensione `-1`, e quel caso delle gallerie si risolve direttamente. -/
def RidgeConnectedAboveOne (P : ConvexPolytope n) : Prop :=
  ∀ (B : Set (E n)), P.IsFace B → 2 ≤ faceDim B →
    ∀ (A A' : Set (E n)), P.IsFace A → P.IsFace A' →
      A ⊂ B → A' ⊂ B →
      faceDim A + 1 = faceDim B → faceDim A' + 1 = faceDim B →
      Relation.ReflTransGen
        (fun X Y : Set (E n) =>
          P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
            faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
            ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
              faceDim R + 2 = faceDim B)
        A A'

theorem ridgeConnectedAboveOne_of_ridgeConnected (P : ConvexPolytope n)
    (h : RidgeConnected P) : RidgeConnectedAboveOne P := by
  intro B hB _hdB
  exact h B hB

/-- Una catena completa che termina in una faccia assegnata. -/
theorem chain_ending_at_face (P : ConvexPolytope n)
    {A : Set (E n)} (hA : P.IsFace A) {d : ℕ} (hdA : faceDim A = d) :
    ∃ c : ℕ → Set (E n),
      c d = A ∧
      (∀ k, k ≤ d → P.IsFace (c k) ∧ faceDim (c k) = k) ∧
      (∀ j k, j < k → k ≤ d → c j ⊂ c k) := by
  classical
  let Q : ConvexPolytope n := facePolytope P hA
  have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = d := by
    dsimp only [Q]
    rw [facePolytope_toSet P hA]
    exact hdA
  obtain ⟨c', hc'1, hc'2⟩ := chain_exists Q d hQdim
  refine ⟨fun k => if k = d then A else c' k, ?_, ?_, ?_⟩
  · change (if d = d then A else c' d) = A
    rw [if_pos rfl]
  · intro k hk
    change P.IsFace (if k = d then A else c' k) ∧
      faceDim (if k = d then A else c' k) = k
    by_cases hkd : k = d
    · rw [if_pos hkd]
      exact ⟨hA, hdA.trans hkd.symm⟩
    · rw [if_neg hkd]
      have hklt : k < d := by omega
      obtain ⟨hkface, hkdim⟩ := hc'1 k hklt
      exact ⟨isFace_of_facePolytope P hA hkface, hkdim⟩
  · intro j k hjk hk
    change (if j = d then A else c' j) ⊂
      (if k = d then A else c' k)
    by_cases hkd : k = d
    · have hjd : j ≠ d := by omega
      rw [if_pos hkd, if_neg hjd]
      obtain ⟨hjface, hjdim⟩ := hc'1 j (by omega)
      have hjsub : c' j ⊆ A := by
        have := face_subset_toSet Q hjface
        simpa only [Q, facePolytope_toSet P hA] using this
      refine hjsub.ssubset_of_ne ?_
      intro heq
      have := congrArg faceDim heq
      rw [hjdim, hdA] at this
      omega
    · have hklt : k < d := by omega
      have hjd : j ≠ d := by omega
      rw [if_neg hkd, if_neg hjd]
      exact hc'2 j k hjk hklt

/-- Ricostruisce la parte inferiore di una bandiera in modo che passi per
la faccia `R`, lasciando invariati tutti i ranghi da `i` in su. -/
theorem rechain_below_face (P : ConvexPolytope n) (F : P.Flag)
    (i : Fin n) (hi : 0 < (i : ℕ))
    {R : Set (E n)} (hR : P.IsFace R)
    (hdR : faceDim R + 1 = (i : ℕ)) (hRi : R ⊂ F.face i) :
    ∃ H : P.Flag,
      AgreeAbove P F H (i : ℕ) ∧
      ∀ j : Fin n, j < i → H.face j ⊆ R := by
  classical
  let d : ℕ := (i : ℕ) - 1
  have hdR' : faceDim R = d := by
    dsimp only [d]
    omega
  obtain ⟨c, hcd, hcface, hcmono⟩ := chain_ending_at_face P hR hdR'
  let H : P.Flag :=
    { face := fun k => if k < i then c k else F.face k
      isFace := by
        intro k
        by_cases hki : k < i
        · rw [if_pos hki]
          exact (hcface k (by dsimp only [d]; omega)).1
        · rw [if_neg hki]
          exact F.isFace k
      dim_eq := by
        intro k
        by_cases hki : k < i
        · rw [if_pos hki]
          exact (hcface k (by dsimp only [d]; omega)).2
        · rw [if_neg hki]
          exact F.dim_eq k
      strict_mono := by
        intro a b hab
        by_cases hbi : b < i
        · have hai : a < i := lt_trans hab hbi
          rw [if_pos hai, if_pos hbi]
          exact hcmono a b hab (by dsimp only [d]; omega)
        · rw [if_neg hbi]
          by_cases hai : a < i
          · rw [if_pos hai]
            have hac : c a ⊆ R := by
              by_cases had : (a : ℕ) = d
              · rw [had, hcd]
              · rw [← hcd]
                exact (hcmono a d (by dsimp only [d]; omega) (le_refl d)).1
            have hib : F.face i ⊆ F.face b := by
              rcases eq_or_lt_of_le (show i ≤ b by omega) with hib | hib
              · rw [hib]
              · exact (F.strict_mono i b hib).1
            have hsub : c a ⊆ F.face b := hac.trans (hRi.1.trans hib)
            refine hsub.ssubset_of_ne ?_
            intro heq
            have hdim := congrArg faceDim heq
            rw [(hcface a (by dsimp only [d]; omega)).2, F.dim_eq] at hdim
            omega
          · rw [if_neg hai]
            exact F.strict_mono a b hab }
  refine ⟨H, ?_, ?_⟩
  · intro k hk
    change F.face k = (if k < i then c k else F.face k)
    rw [if_neg (by omega)]
  · intro j hji
    change (if j < i then c j else F.face j) ⊆ R
    rw [if_pos hji]
    by_cases hjd : (j : ℕ) = d
    · rw [hjd, hcd]
    · rw [← hcd]
      exact (hcmono j d (by dsimp only [d]; omega) (le_refl d)).1

/-- Versione parametrica del passo induttivo: `AgreeAbove m` implica una
galleria, per ogni `m ≤ n`, sotto l'ipotesi locale `RidgeConnected`. -/
theorem galleryConnected_of_agreeAbove_of_ridgeConnectedAboveOne
    (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (hridge : RidgeConnectedAboveOne P) :
    ∀ m : ℕ, m ≤ n → ∀ F G : P.Flag,
      AgreeAbove P F G m → GalleryConnected P F G := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hmn F G hagree
      rcases m with _ | m
      · have hFG := agreeAbove_zero P hagree
        subst G
        exact galleryConnected_refl P F
      · by_cases hm0 : m = 0
        · subst m
          apply galleryConnected_of_agree_except P F G ⟨0, by omega⟩
          intro j hj
          exact hagree j (by
            have hjne : (j : ℕ) ≠ 0 := by
              intro hjzero
              apply hj
              apply Fin.ext
              exact hjzero
            omega)
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          let i : Fin n := ⟨m, by omega⟩
          have hidim : faceDim (F.face i) = m := F.dim_eq i
          obtain ⟨B, hB, hdB, hFiB, hGiB, hBupper⟩ :
              ∃ B : Set (E n), P.IsFace B ∧ faceDim B = m + 1 ∧
                F.face i ⊂ B ∧ G.face i ⊂ B ∧
                ∀ k : Fin n, i < k → B ⊆ F.face k := by
            by_cases htop : m + 1 = n
            · have htopdim : faceDim P.toSet = n := hfull
              refine ⟨P.toSet, toSet_isFace P, ?_, ?_, ?_, ?_⟩
              · rw [htopdim, htop]
              · refine (face_subset_toSet P (F.isFace i)).ssubset_of_ne ?_
                intro heq
                have hdim := congrArg faceDim heq
                rw [F.dim_eq, htopdim] at hdim
                dsimp only [i] at hdim
                omega
              · refine (face_subset_toSet P (G.isFace i)).ssubset_of_ne ?_
                intro heq
                have hdim := congrArg faceDim heq
                rw [G.dim_eq, htopdim] at hdim
                dsimp only [i] at hdim
                omega
              · intro k hik
                exfalso
                have hik' := hik
                change m < (k : ℕ) at hik'
                have hklt := k.isLt
                omega
            · let ip : Fin n := ⟨m + 1, by omega⟩
              have hiip : i < ip := by
                change m < m + 1
                omega
              have hFGip : F.face ip = G.face ip :=
                hagree ip (by dsimp only [ip]; omega)
              refine ⟨F.face ip, F.isFace ip, F.dim_eq ip,
                F.strict_mono i ip hiip, ?_, ?_⟩
              · rw [hFGip]
                exact G.strict_mono i ip hiip
              · intro k hik
                have hik' := hik
                change m < (k : ℕ) at hik'
                have hipkle : ip ≤ k := by
                  change m + 1 ≤ (k : ℕ)
                  omega
                rcases eq_or_lt_of_le hipkle with hipk | hipk
                · rw [hipk]
                · exact (F.strict_mono ip k hipk).1
          have hfaces := hridge B hB (by rw [hdB]; omega)
            (F.face i) (G.face i)
            (F.isFace i) (G.isFace i) hFiB hGiB (by rw [F.dim_eq, hdB])
            (by rw [G.dim_eq, hdB])
          let FaceRel : Set (E n) → Set (E n) → Prop := fun X Y =>
            P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
              faceDim X + 1 = faceDim B ∧
              faceDim Y + 1 = faceDim B ∧
              ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
                faceDim R + 2 = faceDim B
          change Relation.ReflTransGen FaceRel (F.face i) (G.face i) at hfaces
          have transfer : ∀ {X : Set (E n)},
              Relation.ReflTransGen FaceRel (F.face i) X →
              ∃ K : P.Flag, GalleryConnected P F K ∧ K.face i = X ∧
                ∀ k : Fin n, i < k → K.face k = F.face k := by
            intro X hpath
            induction hpath with
            | refl =>
                exact ⟨F, galleryConnected_refl P F, rfl, fun _ _ => rfl⟩
            | @tail X Y hprev hstep ihpath =>
                obtain ⟨K, hFK, hKi, hKup⟩ := ihpath
                obtain ⟨hX, hY, _hXB, hYB, _hdX, hdY,
                  R, hR, hRX, hRY, hdR⟩ := hstep
                have hRKi : R ⊂ K.face i := by simpa [hKi] using hRX
                have hdR' : faceDim R + 1 = (i : ℕ) := by
                  dsimp only [i]
                  rw [hdB] at hdR
                  omega
                obtain ⟨H, hKH, hHbelow⟩ :=
                  rechain_below_face P K i (by dsimp only [i]; omega)
                    hR hdR' hRKi
                have hKgalH : GalleryConnected P K H :=
                  ih m (Nat.lt_succ_self m) (by omega) K H hKH
                have hdYi : faceDim Y = (i : ℕ) := by
                  dsimp only [i]
                  rw [hdB] at hdY
                  omega
                have hsottoY : ∀ j : Fin n, j < i → H.face j ⊂ Y := by
                  intro j hji
                  have hsub : H.face j ⊆ Y := (hHbelow j hji).trans hRY.1
                  refine hsub.ssubset_of_ne ?_
                  intro heq
                  have hdim := congrArg faceDim heq
                  rw [H.dim_eq, hdYi] at hdim
                  omega
                have hsopraY : ∀ j : Fin n, i < j → Y ⊂ H.face j := by
                  intro j hij
                  have hHF : H.face j = F.face j :=
                    (hKH j (by
                      have hij' := hij
                      change m < (j : ℕ) at hij'
                      omega)).symm.trans (hKup j hij)
                  rw [hHF]
                  have hsub : Y ⊆ F.face j := hYB.1.trans (hBupper j hij)
                  refine hsub.ssubset_of_ne ?_
                  intro heq
                  have hdim := congrArg faceDim heq
                  rw [hdYi, F.dim_eq] at hdim
                  omega
                let L : P.Flag := sostituisci P H i Y hY hdYi hsottoY hsopraY
                have hHL : GalleryConnected P H L :=
                  galleryConnected_of_agree_except P H L i (by
                    intro j hji
                    exact (sostituisci_face_ne P H i Y hY hdYi
                      hsottoY hsopraY hji).symm)
                refine ⟨L, hFK.trans (hKgalH.trans hHL),
                  sostituisci_face_self P H i Y hY hdYi hsottoY hsopraY, ?_⟩
                intro k hik
                rw [sostituisci_face_ne P H i Y hY hdYi hsottoY hsopraY
                  (ne_of_gt hik)]
                exact (hKH k (by dsimp only [i]; omega)).symm.trans (hKup k hik)
          obtain ⟨K, hFK, hKi, hKup⟩ := transfer hfaces
          have hKGagree : AgreeAbove P K G m := by
            intro k hk
            by_cases hki : k = i
            · rw [hki, hKi]
            · have hik : i < k := by
                have hkne : (k : ℕ) ≠ m := by
                  intro hkm
                  apply hki
                  apply Fin.ext
                  simpa only [i] using hkm
                change m < (k : ℕ)
                omega
              rw [hKup k hik]
              exact hagree k (by
                have hik' := hik
                change m < (k : ℕ) at hik'
                omega)
          exact hFK.trans (ih m (Nat.lt_succ_self m) (by omega) K G hKGagree)

/-- **IL MURO LOCALE (nella forma sufficiente) IMPLICA LA CONNETTIVITÀ
GLOBALE DELLE GALLERIE.** -/
theorem galleryConnected_of_ridgeConnectedAboveOne
    (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (hridge : RidgeConnectedAboveOne P) (F G : P.Flag) :
    GalleryConnected P F G := by
  apply galleryConnected_of_agreeAbove_of_ridgeConnectedAboveOne
    P hfull hridge n
    (le_refl n) F G
  exact agreeAbove_of_ge P F G (le_refl n)

/-- Wrapper compatibile con la definizione storica (più forte del
necessario) di `Connettivita.lean`. -/
theorem galleryConnected_of_ridgeConnected
    (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (hridge : RidgeConnected P) (F G : P.Flag) :
    GalleryConnected P F G :=
  galleryConnected_of_ridgeConnectedAboveOne P hfull
    (ridgeConnectedAboveOne_of_ridgeConnected P hridge) F G

/-- La definizione storica `RidgeConnected` è troppo forte al bordo
inferiore: appena esiste un rango 1, forza due zero-facce distinte di uno
spigolo a essere uguali.  Questo lemma certifica il motivo per cui il
kill-gate utile è `RidgeConnectedAboveOne`. -/
theorem not_ridgeConnected_of_flag_two_le
    (P : ConvexPolytope n) (hn : 2 ≤ n) (F : P.Flag) :
    ¬ RidgeConnected P := by
  intro hridge
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi01 : i0 < i1 := by
    change 0 < 1
    omega
  have hVδ : F.face i0 ⊂ F.face i1 := F.strict_mono i0 i1 hi01
  obtain ⟨W, hW, _hWunique⟩ := due_vertici_per_spigolo P
    (F.isFace i1) (by simpa only [i1] using F.dim_eq i1)
    (F.isFace i0) (by simpa only [i0] using F.dim_eq i0) hVδ
  have hpath := hridge (F.face i1) (F.isFace i1)
    (F.face i0) W (F.isFace i0) hW.1.1 hVδ hW.1.2.2
    (by rw [F.dim_eq, F.dim_eq])
    (by rw [hW.1.2.1, F.dim_eq])
  have hstep_false : ∀ {X Y : Set (E n)},
      (P.IsFace X ∧ P.IsFace Y ∧ X ⊂ F.face i1 ∧ Y ⊂ F.face i1 ∧
        faceDim X + 1 = faceDim (F.face i1) ∧
        faceDim Y + 1 = faceDim (F.face i1) ∧
        ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
          faceDim R + 2 = faceDim (F.face i1)) → False := by
    intro X Y h
    obtain ⟨_hX, _hY, _hXB, _hYB, _hdX, _hdY,
      R, _hR, _hRX, _hRY, hdR⟩ := h
    have hdEdge : faceDim (F.face i1) = 1 := by
      simpa only [i1] using F.dim_eq i1
    rw [hdEdge] at hdR
    omega
  have hEq : F.face i0 = W := by
    induction hpath with
    | refl => rfl
    | tail _ hstep _ => exact (hstep_false hstep).elim
  exact hW.2 hEq.symm

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart29

section BundlePart30
/- Source: Cubical/Polytope/FaceOrder.lean -/





@[expose] public section

/-!
# Combinatorial equivalences preserve geometric face dimension

An order isomorphism of nonempty geometric face posets already preserves
dimension. The proof uses complete flags and strict growth of affine
dimension along a proper inclusion of exposed faces. Thus no separate rank
preservation assumption is needed in the definition of a cubical polytope.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ} {P : ConvexPolytope n} {Q : ConvexPolytope m}

theorem faceOrderIso_dimension_le (φ : FaceType P ≃o FaceType Q)
    (F : FaceType P) : faceDim F.val ≤ faceDim (φ F).val := by
  classical
  let d := faceDim F.val
  obtain ⟨c, hcd, hcface, hcmono⟩ := chain_ending_at_face P F.property (d := d) rfl
  let C (k : ℕ) : FaceType P :=
    if hk : k ≤ d then ⟨c k, (hcface k hk).1⟩ else F
  have hC (k : ℕ) (hk : k ≤ d) : (C k).val = c k := by
    simp only [C, dif_pos hk]
  have hCd : C d = F := by
    apply Subtype.ext
    exact (hC d le_rfl).trans hcd
  have hstrict : StrictMonoOn (fun k => faceDim (φ (C k)).val) (Iic d) := by
    intro i hi j hj hij
    apply faceDim_lt_of_ssubset Q (φ (C i)).property (φ (C j)).property
    have hCij : C i < C j := by
      change (C i).val ⊂ (C j).val
      rw [hC i hi, hC j hj]
      exact hcmono i j hij hj
    exact φ.strictMono hCij
  have hbound := hstrict.Iic_id_le d le_rfl
  simpa only [hCd, d] using hbound

/-- Combinatorial equivalence of ordinary face posets preserves dimension. -/
theorem faceOrderIso_dimension (φ : FaceType P ≃o FaceType Q)
    (F : FaceType P) : faceDim (φ F).val = faceDim F.val := by
  apply le_antisymm
  · simpa using faceOrderIso_dimension_le φ.symm (φ F)
  · exact faceOrderIso_dimension_le φ F

end LeanEval.Geometry.PlatonicClassification

end
end BundlePart30

section BundlePart31
/- Source: Papers/PolytopeGeometry.lean -/




@[expose] public section

/-!
# Geometric consequences of ordinary combinatorial equivalence

These results do not add rank, incidence, or general-position hypotheses to
the face-order isomorphism.  They extract them from the actual convex bodies.
-/

noncomputable section

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace Papers.Polytopes

variable {d e : ℕ}

theorem vertex_mem_body (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) : v ∈ P.toSet :=
  subset_convexHull ℝ _ hv

theorem vertex_is_extreme (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) : v ∈ P.toSet.extremePoints ℝ := by
  change v ∈ (convexHull ℝ (P.vertices : Set (E d))).extremePoints ℝ
  rw [← P.vertices_eq_extremePoints]
  exact hv

theorem vertex_mem_segment_iff (P : ConvexPolytope d) {x y z : E d}
    (hx : x ∈ P.vertices) (hy : y ∈ P.vertices) (hz : z ∈ P.vertices) :
    z ∈ segment ℝ x y ↔ z = x ∨ z = y := by
  constructor
  · intro h
    exact ((mem_extremePoints_iff_forall_segment.mp (vertex_is_extreme P hz)).2
      x (vertex_mem_body P hx) y (vertex_mem_body P hy) h).imp Eq.symm Eq.symm
  · rintro (h | h)
    · rw [h]
      exact left_mem_segment ℝ x y
    · rw [h]
      exact right_mem_segment ℝ x y

/-- No three distinct actual vertices are collinear, in any dimension. -/
theorem vertices_not_collinear (P : ConvexPolytope d) {x y z : E d}
    (hx : x ∈ P.vertices) (hy : y ∈ P.vertices) (hz : z ∈ P.vertices)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬Collinear ℝ ({x, y, z} : Set (E d)) := by
  intro h
  rcases h.wbtw_or_wbtw_or_wbtw with h | h | h
  · rcases (vertex_mem_segment_iff P hx hz hy).mp h.mem_segment with h | h
    · exact hxy h.symm
    · exact hyz h
  · rcases (vertex_mem_segment_iff P hy hx hz).mp h.mem_segment with h | h
    · exact hyz h.symm
    · exact hxz h.symm
  · rcases (vertex_mem_segment_iff P hz hy hx).mp h.mem_segment with h | h
    · exact hxz h
    · exact hxy h

/-- A face's affine span cannot pick up an additional point of the body. -/
theorem body_inter_affineSpan_face (P : ConvexPolytope d)
    {F : Set (E d)} (hF : P.IsFace F) :
    P.toSet ∩ (affineSpan ℝ F : Set (E d)) = F := by
  obtain ⟨x₀, hx₀⟩ := hF.2
  obtain ⟨l, hl⟩ := hF.1 hF.2
  have hx₀' : x₀ ∈ P.toSet ∧ ∀ y ∈ P.toSet, l y ≤ l x₀ := by
    rw [hl] at hx₀
    exact hx₀
  have hconst : Set.EqOn l.toLinearMap.toAffineMap
      (AffineMap.const ℝ (E d) (l x₀)) F := by
    intro y hy
    have hy' : y ∈ P.toSet ∧ ∀ z ∈ P.toSet, l z ≤ l y := by
      rw [hl] at hy
      exact hy
    exact le_antisymm (hx₀'.2 y hy'.1) (hy'.2 x₀ hx₀'.1)
  have hspan := AffineMap.eqOn_affineSpan (k := ℝ) hconst
  apply Set.Subset.antisymm
  · rintro y ⟨hyP, hyspan⟩
    rw [hl]
    refine ⟨hyP, fun z hz => ?_⟩
    have hy : l y = l x₀ := hspan hyspan
    rw [hy]
    exact hx₀'.2 z hz
  · intro y hy
    exact ⟨hF.1.subset hy, subset_affineSpan ℝ _ hy⟩

theorem vertex_notMem_affineSpan_face (P : ConvexPolytope d)
    {F : Set (E d)} (hF : P.IsFace F) {v : E d}
    (hv : v ∈ P.vertices) (hvF : v ∉ F) : v ∉ affineSpan ℝ F := by
  intro h
  apply hvF
  rw [← body_inter_affineSpan_face P hF]
  exact ⟨vertex_mem_body P hv, h⟩

def vertexFace (P : ConvexPolytope d) (v : VertexType P) : FaceType P :=
  ⟨{v.val}, vertex_isFace P v.property⟩

@[simp] theorem vertexFace_val (P : ConvexPolytope d) (v : VertexType P) :
    (vertexFace P v).val = {v.val} := rfl

@[simp] theorem vertexFace_dim (P : ConvexPolytope d) (v : VertexType P) :
    faceDim (vertexFace P v).val = 0 := faceDim_singleton v.val

theorem vertexFace_injective (P : ConvexPolytope d) :
    Function.Injective (vertexFace P) := by
  intro v w h
  apply Subtype.ext
  exact Set.singleton_injective (congrArg Subtype.val h)

@[simp] theorem vertexFace_le_iff (P : ConvexPolytope d) (v : VertexType P)
    (F : FaceType P) : vertexFace P v ≤ F ↔ v.val ∈ F.val :=
  Set.singleton_subset_iff

theorem exists_vertex_of_zero_face (P : ConvexPolytope d) (F : FaceType P)
    (hd : faceDim F.val = 0) : ∃ v : VertexType P, vertexFace P v = F := by
  obtain ⟨v, hvF, hv⟩ := punto_di_faccia0_e_vertice P F.property hd
  exact ⟨⟨v, hv⟩, Subtype.ext hvF.symm⟩

/-- The vertex induced by an isomorphism of ordinary nonempty face posets. -/
def imageVertex {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (v : VertexType P) : VertexType Q :=
  Classical.choose (exists_vertex_of_zero_face Q (φ (vertexFace P v))
    ((faceOrderIso_dimension φ (vertexFace P v)).trans (vertexFace_dim P v)))

@[simp] theorem imageVertex_face {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (v : VertexType P) :
    vertexFace Q (imageVertex φ v) = φ (vertexFace P v) :=
  Classical.choose_spec (exists_vertex_of_zero_face Q (φ (vertexFace P v))
    ((faceOrderIso_dimension φ (vertexFace P v)).trans (vertexFace_dim P v)))

@[simp] theorem imageVertex_mem_iff {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (v : VertexType P) (F : FaceType P) :
    (imageVertex φ v).val ∈ (φ F).val ↔ v.val ∈ F.val := by
  rw [← vertexFace_le_iff, imageVertex_face, φ.le_iff_le, vertexFace_le_iff]

/-- Vertex correspondence is derived from the face-order isomorphism. -/
def vertexEquivOfFaceOrder {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : VertexType P ≃ VertexType Q where
  toFun := imageVertex φ
  invFun := imageVertex φ.symm
  left_inv v := by
    apply vertexFace_injective P
    rw [imageVertex_face, imageVertex_face, OrderIso.symm_apply_apply]
  right_inv v := by
    apply vertexFace_injective Q
    rw [imageVertex_face, imageVertex_face, OrderIso.apply_symm_apply]

theorem faceOrderIso_vertex_card {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : P.vertices.card = Q.vertices.card := by
  classical
  simpa only [VertexType, Fintype.card_coe] using
    Fintype.card_congr (vertexEquivOfFaceOrder φ)

def wholeFace (P : ConvexPolytope d) : FaceType P :=
  ⟨P.toSet, IsExposed.refl _, by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨v, vertex_mem_body P hv⟩⟩

theorem le_wholeFace (P : ConvexPolytope d) (F : FaceType P) :
    F ≤ wholeFace P := F.property.1.subset

@[simp] theorem image_wholeFace {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : φ (wholeFace P) = wholeFace Q := by
  apply le_antisymm
  · exact le_wholeFace Q _
  · have h := φ.monotone (le_wholeFace P (φ.symm (wholeFace Q)))
    simpa using h

theorem faceOrderIso_polytope_dim {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : Q.dim = P.dim := by
  have h := faceOrderIso_dimension φ (wholeFace P)
  rw [image_wholeFace] at h
  exact h

end Papers.Polytopes

end
end
end BundlePart31

section BundlePart32
/- Source: Papers/CompleteFaceLattice.lean -/




@[expose] public section

/-!
# Including the empty face

The polytope foundation stores nonempty exposed faces. This file proves that
its notion of combinatorial equivalence is equivalent to an order isomorphism
of the complete exposed-face posets, including the empty face.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def CompleteFaceType {d : ℕ} (P : ConvexPolytope d) :=
  {F : Set (E d) // IsExposed ℝ P.toSet F}

instance {d : ℕ} (P : ConvexPolytope d) : PartialOrder (CompleteFaceType P) :=
  inferInstanceAs (PartialOrder {F : Set (E d) // IsExposed ℝ P.toSet F})

instance {d : ℕ} (P : ConvexPolytope d) : OrderBot (CompleteFaceType P) where
  bot := ⟨∅, isExposed_empty⟩
  bot_le _ := Set.empty_subset _

theorem completeFace_ne_bot_iff {d : ℕ} {P : ConvexPolytope d} (F : CompleteFaceType P) :
    F ≠ ⊥ ↔ F.val.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  exact not_congr ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

def nonemptyFaceOrderIso {d : ℕ} (P : ConvexPolytope d) :
    FaceType P ≃o {F : CompleteFaceType P // F ≠ ⊥} where
  toFun F := ⟨⟨F.val, F.property.1⟩,
    (completeFace_ne_bot_iff _).mpr F.property.2⟩
  invFun F := ⟨F.val.val, F.val.property, (completeFace_ne_bot_iff F.val).mp F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def completeFaceOrderIso {d : ℕ} (P : ConvexPolytope d) :
    WithBot (FaceType P) ≃o CompleteFaceType P := by
  classical
  exact (nonemptyFaceOrderIso P).withBotCongr.trans WithBot.subtypeOrderIso

def extendFaceOrderIso {d e : ℕ} {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : CompleteFaceType P ≃o CompleteFaceType Q :=
  (completeFaceOrderIso P).symm.trans (φ.withBotCongr.trans (completeFaceOrderIso Q))

def restrictCompleteFaceOrderIso {d e : ℕ} {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : CompleteFaceType P ≃o CompleteFaceType Q) : FaceType P ≃o FaceType Q := by
  let ψ : {F : CompleteFaceType P // F ≠ ⊥} ≃o {F : CompleteFaceType Q // F ≠ ⊥} := {
    toFun := fun F => ⟨φ F.val, by
      intro h
      apply F.property
      apply φ.injective
      simpa only [φ.map_bot] using h⟩
    invFun := fun F => ⟨φ.symm F.val, by
      intro h
      apply F.property
      apply φ.symm.injective
      simpa only [φ.symm.map_bot] using h⟩
    left_inv := fun F => Subtype.ext (φ.symm_apply_apply F.val)
    right_inv := fun F => Subtype.ext (φ.apply_symm_apply F.val)
    map_rel_iff' := φ.le_iff_le }
  exact (nonemptyFaceOrderIso P).trans (ψ.trans (nonemptyFaceOrderIso Q).symm)

theorem nonempty_face_iso_iff_complete_face_iso {d e : ℕ}
    (P : ConvexPolytope d) (Q : ConvexPolytope e) :
    Nonempty (FaceType P ≃o FaceType Q) ↔ Nonempty (CompleteFaceType P ≃o CompleteFaceType Q) :=
  ⟨fun ⟨φ⟩ => ⟨extendFaceOrderIso φ⟩, fun ⟨φ⟩ => ⟨restrictCompleteFaceOrderIso φ⟩⟩

end Papers.Polytopes

end
end
end BundlePart32

section BundlePart33
/- Source: Papers/PolytopeTargets.lean -/








@[expose] public section

/-!
# Exact geometric targets for the two polytope papers

All objects below are actual finite convex hulls with their extreme vertices.
Faces are exposed faces, and combinatorial equivalence is an order isomorphism
of their ordinary face posets. In particular, neither field realizability nor
Minkowski decomposability is encoded by a conclusion to be proved.

The declarations ending in `Claim` are proposition-valued definitions recording
the original targets. Their presence does NOT assert or prove these claims.
-/

noncomputable section

open Set
open scoped Classical
open scoped Pointwise
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace Papers.Polytopes

variable {d : ℕ}

/-- The actual combinatorial equivalence relation on nonempty face posets.
The omitted empty face can be adjoined as a new least element. -/
def CombinatoriallyEquivalent (P Q : ConvexPolytope d) : Prop :=
  Nonempty (FaceType P ≃o FaceType Q)

/-- Adjoining the empty face gives exactly the ordinary complete face-lattice
notion of combinatorial equivalence. -/
theorem combinatoriallyEquivalent_iff_complete_face_iso (P Q : ConvexPolytope d) :
    CombinatoriallyEquivalent P Q ↔
      Nonempty (CompleteFaceType P ≃o CompleteFaceType Q) :=
  nonempty_face_iso_iff_complete_face_iso P Q

theorem CombinatoriallyEquivalent.refl (P : ConvexPolytope d) :
    CombinatoriallyEquivalent P P := ⟨OrderIso.refl _⟩

theorem CombinatoriallyEquivalent.symm {P Q : ConvexPolytope d}
    (h : CombinatoriallyEquivalent P Q) : CombinatoriallyEquivalent Q P :=
  h.elim (fun e => ⟨e.symm⟩)

theorem CombinatoriallyEquivalent.trans {P Q R : ConvexPolytope d}
    (h₁ : CombinatoriallyEquivalent P Q) (h₂ : CombinatoriallyEquivalent Q R) :
    CombinatoriallyEquivalent P R :=
  h₁.elim (fun e₁ => h₂.elim (fun e₂ => ⟨e₁.trans e₂⟩))

/-- A positive homothety, exactly as in the paper's cited definition.
A point summand is trivial because the other summand is a translate of P. -/
def IsHomotheticCopy (P A : ConvexPolytope d) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ b : E d,
    A.toSet = (fun x : E d => r • x + b) '' P.toSet

/-- Ordinary nontrivial Minkowski decomposability, allowing summands of
any affine dimension in the ambient space. -/
def MinkowskiDecomposable (P : ConvexPolytope d) : Prop :=
  ∃ A B : ConvexPolytope d,
    P.toSet = A.toSet + B.toSet ∧
    ¬IsHomotheticCopy P A ∧ ¬IsHomotheticCopy P B

def ConditionallyDecomposable (P : ConvexPolytope d) : Prop :=
  (∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ MinkowskiDecomposable Q) ∧
  (∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ ¬MinkowskiDecomposable Q)

/-- Theorem 1 of the conditional-decomposability paper, including sharpness
for every dimension, not only a lower bound or a fixed-dimensional case. -/
def ConditionalDecomposabilityClaim : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    (∀ P : ConvexPolytope d, P.IsFullDim → ConditionallyDecomposable P →
      4 * d - 4 ≤ P.vertices.card) ∧
    (∃ P : ConvexPolytope d, P.IsFullDim ∧ ConditionallyDecomposable P ∧
      P.vertices.card = 4 * d - 4)

def CoordinatesIn (K : Subfield ℝ) (P : ConvexPolytope d) : Prop :=
  ∀ v ∈ P.vertices, ∀ i : Fin d, v i ∈ K

def RationalCoordinates (P : ConvexPolytope d) : Prop :=
  ∀ v ∈ P.vertices, ∀ i : Fin d, ∃ q : ℚ, (q : ℝ) = v i

def RealizableOver (P : ConvexPolytope d) (K : Subfield ℝ) : Prop :=
  ∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ CoordinatesIn K Q

theorem realizableOver_iff_complete_face_iso (P : ConvexPolytope d) (K : Subfield ℝ) :
    RealizableOver P K ↔ ∃ Q : ConvexPolytope d,
      Nonempty (CompleteFaceType P ≃o CompleteFaceType Q) ∧ CoordinatesIn K Q := by
  constructor
  · rintro ⟨Q, hPQ, hK⟩
    exact ⟨Q, (combinatoriallyEquivalent_iff_complete_face_iso P Q).mp hPQ, hK⟩
  · rintro ⟨Q, hPQ, hK⟩
    exact ⟨Q, (combinatoriallyEquivalent_iff_complete_face_iso P Q).mpr hPQ, hK⟩

def RationallyRealizable (P : ConvexPolytope d) : Prop :=
  ∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ RationalCoordinates Q

/-- Density in the space of labeled realizations, expressed without choosing
an enumeration of the vertices. The face-poset isomorphism identifies the
labels, and every vertex must move by less than the prescribed tolerance. -/
def RationallyDense (P : ConvexPolytope d) : Prop :=
  ∀ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q →
    ∀ ε : ℝ, 0 < ε →
      ∃ R : ConvexPolytope d, ∃ φ : FaceType Q ≃o FaceType R,
        RationalCoordinates R ∧
        ∀ v : VertexType Q, dist (imageVertex φ v).val v.val < ε

theorem RationallyDense.realizable {P : ConvexPolytope d}
    (h : RationallyDense P) : RationallyRealizable P := by
  obtain ⟨Q, φ, hQ, _⟩ := h P (CombinatoriallyEquivalent.refl P) 1 zero_lt_one
  exact ⟨Q, ⟨φ⟩, hQ⟩

/-- Theorem 1 of the nonrational four-polytope paper. -/
def SeventeenVertexFieldClaim : Prop :=
  ∃ P : ConvexPolytope 4, P.IsFullDim ∧ P.vertices.card = 17 ∧
    ∀ K : Subfield ℝ, RealizableOver P K ↔ Real.sqrt 5 ∈ K

/-- Theorem 2 of the nonrational four-polytope paper. -/
def RationalityThroughTenClaim : Prop :=
  ∀ P : ConvexPolytope 4, P.IsFullDim → P.vertices.card ≤ 10 → RationallyRealizable P

/-- Taking a nonempty subset of actual extreme vertices produces the
ordinary convex hull of exactly those vertices. -/
def vertexSubsetPolytope (P : ConvexPolytope d) (S : Finset (E d))
    (hne : S.Nonempty) (hsub : S ⊆ P.vertices) : ConvexPolytope d where
  vertices := S
  vertices_nonempty := hne
  vertices_eq_extremePoints := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxP : x ∈ P.vertices := hsub hx
      have hxext : x ∈ P.toSet.extremePoints ℝ := by
        change x ∈ (convexHull ℝ (P.vertices : Set (E d))).extremePoints ℝ
        rw [← P.vertices_eq_extremePoints]
        exact hxP
      have hhull : convexHull ℝ (S : Set (E d)) ⊆ P.toSet := by
        apply convexHull_mono
        exact hsub
      exact inter_extremePoints_subset_extremePoints_of_subset hhull
        ⟨subset_convexHull ℝ _ hx, hxext⟩
    · exact extremePoints_convexHull_subset

def deleteVertex (P : ConvexPolytope d) (v : E d)
    (hne : (P.vertices.erase v).Nonempty) : ConvexPolytope d :=
  vertexSubsetPolytope P (P.vertices.erase v) hne (Finset.erase_subset _ _)

@[simp] theorem deleteVertex_vertices (P : ConvexPolytope d) (v : E d)
    (hne : (P.vertices.erase v).Nonempty) :
    (deleteVertex P v hne).vertices = P.vertices.erase v := rfl

@[simp] theorem deleteVertex_toSet (P : ConvexPolytope d) (v : E d)
    (hne : (P.vertices.erase v).Nonempty) :
    (deleteVertex P v hne).toSet = convexHull ℝ (P.vertices.erase v : Set (E d)) := rfl

def IsSimpleVertex (P : ConvexPolytope d) (v : VertexType P) : Prop := by
  classical
  exact (polytopeGraph P).degree v = P.dim

/-- The field-equality assertion of Theorem 3. Its additional density and
combinatorial-deletion assertions require separate targets. -/
def SimpleDeletionFieldsClaim : Prop :=
  ∀ (d : ℕ) (P : ConvexPolytope d) (v : VertexType P),
    P.IsFullDim → d + 1 < P.vertices.card → IsSimpleVertex P v →
    ∀ hne : (P.vertices.erase v.val).Nonempty,
      ∀ K : Subfield ℝ, RealizableOver P K ↔ RealizableOver (deleteVertex P v.val hne) K

/-- The full Theorem 3: deletion preserves dimension, is determined by the
original face lattice and distinguished vertex, preserves every real
realization field, and preserves rational density in both directions. -/
def SimpleDeletionClaim : Prop :=
  ∀ (d : ℕ) (P : ConvexPolytope d) (v : VertexType P),
    P.IsFullDim → d + 1 < P.vertices.card → IsSimpleVertex P v →
    ∃ hne : (P.vertices.erase v.val).Nonempty,
      (deleteVertex P v.val hne).IsFullDim ∧
      (∀ (Q : ConvexPolytope d) (φ : FaceType P ≃o FaceType Q)
          (hneQ : (Q.vertices.erase (imageVertex φ v).val).Nonempty),
        CombinatoriallyEquivalent (deleteVertex P v.val hne)
          (deleteVertex Q (imageVertex φ v).val hneQ)) ∧
      (∀ K : Subfield ℝ,
        RealizableOver P K ↔ RealizableOver (deleteVertex P v.val hne) K) ∧
      (RationallyDense P ↔ RationallyDense (deleteVertex P v.val hne))

/-- Corollary 4, with the exact simple-vertex hypothesis. -/
def ElevenVertexSimpleClaim : Prop :=
  ∀ P : ConvexPolytope 4, P.IsFullDim → P.vertices.card = 11 →
    (∃ v : VertexType P, IsSimpleVertex P v) → RationallyRealizable P

end Papers.Polytopes

end
end
end BundlePart33

section BundlePart34
/- Source: Papers/FiniteHullCertificates.lean -/




@[expose] public section

/-!
# Finite supporting-form certificates for actual convex polytopes

A certificate is used only to supply linear inequalities.  The conclusions
about extreme points and exposed faces are derived with Mathlib convexity.
-/

noncomputable section
open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace Papers.Polytopes

variable {d n m : ℕ}

theorem linear_lower_bound_on_hull (s : Finset (E d))
    (l : E d →L[ℝ] ℝ) (c : ℝ) (h : ∀ v ∈ s, c ≤ l v) :
    ∀ x ∈ convexHull ℝ (s : Set (E d)), c ≤ l x := by
  exact convexHull_min h (convex_halfSpace_ge (LinearMap.isLinear l.toLinearMap) c)

/-- A strict linear minimum on the generators is an exposed point of their
ordinary convex hull. -/
theorem strict_minimum_is_exposed (s : Finset (E d)) {v : E d} (hv : v ∈ s)
    (l : E d →L[ℝ] ℝ) (hstrict : ∀ w ∈ s, w ≠ v → l v < l w) :
    IsExposed ℝ (convexHull ℝ (s : Set (E d))) {v} := by
  have hmin : ∀ w ∈ convexHull ℝ (s : Set (E d)), l v ≤ l w := by
    apply linear_lower_bound_on_hull s l (l v)
    intro w hw
    by_cases h : w = v
    · simp [h]
    · exact (hstrict w hw h).le
  intro _
  refine ⟨-l, ?_⟩
  ext x
  constructor
  · rintro rfl
    exact ⟨subset_convexHull ℝ _ hv, fun w hw => by
      simpa only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] using hmin w hw⟩
  · rintro ⟨hx, hmax⟩
    have hxv : l x = l v := by
      have h := hmax v (subset_convexHull ℝ _ hv)
      simp only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] at h
      exact le_antisymm h (hmin x hx)
    have hxHull := PlatoniciL3.faccia_argmax s (-l) hx hmax
    have hsub : {w ∈ (s : Set (E d)) | (-l) w = (-l) x} ⊆ {v} := by
      rintro w ⟨hw, heq⟩
      change w = v
      by_contra hne
      have hlt := hstrict w hw hne
      simp only [ContinuousLinearMap.neg_apply, neg_inj] at heq
      rw [heq, hxv] at hlt
      exact lt_irrefl _ hlt
    exact (convexHull_min hsub (convex_singleton v)) hxHull

def polytopeOfStrictMinima (s : Finset (E d)) (hne : s.Nonempty)
    (hmin : ∀ v ∈ s, ∃ l : E d →L[ℝ] ℝ, ∀ w ∈ s, w ≠ v → l v < l w) :
    ConvexPolytope d where
  vertices := s
  vertices_nonempty := hne
  vertices_eq_extremePoints := by
    apply Set.Subset.antisymm
    · intro v hv
      obtain ⟨l, hl⟩ := hmin v hv
      exact (strict_minimum_is_exposed s hv l hl).isExtreme.mem_extremePoints
    · exact extremePoints_convexHull_subset

/-- Nonnegative forms separating ordered pairs of labels imply that every
label represents an actual extreme vertex. -/
def polytopeOfSeparatingSupports (p : Fin n → E d) (hn : 0 < n)
    (l : Fin m → E d →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hl : ∀ f v, c f ≤ l f (p v))
    (hsep : ∀ v w, v ≠ w → ∃ f, l f (p v) = c f ∧ c f < l f (p w)) :
    ConvexPolytope d := by
  classical
  let s := Finset.univ.image p
  have hs : s.Nonempty := ⟨p ⟨0, hn⟩, Finset.mem_image.mpr
    ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  apply polytopeOfStrictMinima s hs
  intro x hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  let selected : Finset (Fin m) := Finset.univ.filter (fun f => l f (p v) = c f)
  refine ⟨∑ f ∈ selected, l f, ?_⟩
  intro y hy hyne
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hy
  have hvw : v ≠ w := by
    intro h
    subst w
    exact hyne rfl
  obtain ⟨f, hfv, hfw⟩ := hsep v w hvw
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_lt_sum
  · intro g hg
    rw [(Finset.mem_filter.mp hg).2]
    exact hl g w
  · exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfv⟩, by simpa [hfv] using hfw⟩

@[simp] theorem polytopeOfSeparatingSupports_vertices
    (p : Fin n → E d) (hn : 0 < n)
    (l : Fin m → E d →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hl : ∀ f v, c f ≤ l f (p v))
    (hsep : ∀ v w, v ≠ w → ∃ f, l f (p v) = c f ∧ c f < l f (p w)) :
    (polytopeOfSeparatingSupports p hn l c hl hsep).vertices = Finset.univ.image p := rfl

theorem separatingSupports_injective (p : Fin n → E d)
    (l : Fin m → E d →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hsep : ∀ v w, v ≠ w → ∃ f, l f (p v) = c f ∧ c f < l f (p w)) :
    Function.Injective p := by
  intro v w hvw
  by_contra hne
  obtain ⟨f, hfv, hfw⟩ := hsep v w hne
  rw [← hvw, hfv] at hfw
  exact lt_irrefl _ hfw

theorem polytopeOfSeparatingSupports_card
    (p : Fin n → E d) (hn : 0 < n)
    (l : Fin m → E d →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hl : ∀ f v, c f ≤ l f (p v))
    (hsep : ∀ v w, v ≠ w → ∃ f, l f (p v) = c f ∧ c f < l f (p w)) :
    (polytopeOfSeparatingSupports p hn l c hl hsep).vertices.card = n := by
  classical
  rw [polytopeOfSeparatingSupports_vertices,
    Finset.card_image_of_injective _ (separatingSupports_injective p l c hsep)]
  simp

def minimumFace (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ) (c : ℝ) : Set (E d) :=
  {x ∈ P.toSet | l x = c}

theorem minimumFace_isFace (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ v ∈ P.vertices, c ≤ l v)
    (hattained : ∃ v ∈ P.vertices, l v = c) : P.IsFace (minimumFace P l c) := by
  obtain ⟨v, hv, hvc⟩ := hattained
  have hvbody : v ∈ P.toSet := subset_convexHull ℝ _ hv
  have hglobal := linear_lower_bound_on_hull P.vertices l c hbound
  refine ⟨?_, ⟨v, hvbody, hvc⟩⟩
  intro _
  refine ⟨-l, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, fun y hy => ?_⟩
    simp only [ContinuousLinearMap.neg_apply, neg_le_neg_iff]
    rw [hxc]
    exact hglobal y hy
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, le_antisymm ?_ (hglobal x hx)⟩
    have h := hmax v hvbody
    simp only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] at h
    simpa [hvc] using h

end Papers.Polytopes

end
end
end BundlePart34

section BundlePart35
/- Source: Cubical/Polytope/PernoMonotono.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.PernoMonotono.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/



@[expose] public section

/-!
PERNO MONOTONO (20 lug 2026).

È la variante orientata del perno finito: se un funzionale `h` cresce da
una faccia esposta `f` verso almeno un vertice, al primo tempo critico si
ottiene una faccia più grande `f'`; inoltre ogni punto nuovo di `f'` ha
valore di `h` strettamente maggiore del valore (costante) su `f`.

Quest'ultima clausola, assente dalla firma storica di
`perno_parametrico_crescente`, è ciò che permette il pivot monotono del
grafo dei vertici in dimensione arbitraria.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

theorem perno_parametrico_crescente_monotono
    (P : ConvexPolytope n) {f : Set (E n)}
    (_hf : P.IsFace f) (l : E n →L[ℝ] ℝ)
    (hl : f = {x ∈ P.toSet | ∀ y ∈ P.toSet, l y ≤ l x})
    (p₀ : E n) (hp₀f : p₀ ∈ f) (w : E n)
    (hwconst : ∀ z ∈ f, inner ℝ w z = inner ℝ w p₀)
    (hup : ∃ u ∈ P.vertices, inner ℝ w p₀ < inner ℝ w u) :
    ∃ f' : Set (E n), P.IsFace f' ∧ f ⊂ f' ∧
      ∀ y ∈ f', y ∉ f → inner ℝ w p₀ < inner ℝ w y := by
  classical
  obtain ⟨u, huV, huup⟩ := hup
  have hp₀T : p₀ ∈ P.toSet := by
    rw [hl] at hp₀f
    exact hp₀f.1
  set M : ℝ := l p₀ with hM
  have hlf : ∀ z ∈ f, l z = M := by
    intro z hz
    rw [hl] at hz hp₀f
    exact le_antisymm (hp₀f.2 z hz.1) (hz.2 p₀ hp₀f.1)
  have hlmax : ∀ y ∈ P.toSet, l y ≤ M := by
    intro y hy
    rw [hl] at hp₀f
    exact hp₀f.2 y hy
  have hl_strict : ∀ y ∈ P.toSet, y ∉ f → l y < M := by
    intro y hyT hyf
    rcases lt_or_eq_of_le (hlmax y hyT) with h | h
    · exact h
    · exfalso
      apply hyf
      rw [hl]
      exact ⟨hyT, fun z hz => le_trans (hlmax z hz) (le_of_eq h.symm)⟩
  have huf : u ∉ f := by
    intro h
    have := hwconst u h
    linarith

  set l₂ : E n →L[ℝ] ℝ := innerSL ℝ w with hl₂
  have hl₂const : ∀ z ∈ f, l₂ z = l₂ p₀ := by
    intro z hz
    simpa [l₂] using hwconst z hz
  have hl₂up : l₂ p₀ < l₂ u := by simpa [l₂] using huup

  set Vup : Finset (E n) :=
    P.vertices.filter (fun v => l₂ p₀ < l₂ v) with hVup
  have huUp : u ∈ Vup := by simp [hVup, huV, hl₂up]
  have hVupne : Vup.Nonempty := ⟨u, huUp⟩
  set ratio : E n → ℝ :=
    fun v => (M - l v) / (l₂ v - l₂ p₀) with hratio
  have hratio_pos : ∀ v ∈ Vup, 0 < ratio v := by
    intro v hvUp
    have hv := Finset.mem_filter.mp hvUp
    have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hv.1
    have hvnf : v ∉ f := by
      intro hvf
      have := hl₂const v hvf
      linarith
    have hnum : 0 < M - l v := by
      have := hl_strict v hvT hvnf
      linarith
    have hden : 0 < l₂ v - l₂ p₀ := by linarith
    rw [hratio]
    exact div_pos hnum hden
  set R : Finset ℝ := Vup.image ratio with hR
  have hRne : R.Nonempty := hVupne.image ratio
  set t : ℝ := R.min' hRne with ht
  have htpos : 0 < t := by
    have htmem : t ∈ R := by
      rw [ht]
      exact Finset.min'_mem R hRne
    obtain ⟨v, hvUp, hvt⟩ :=
      Finset.mem_image.mp (by simpa [hR] using htmem)
    rw [← hvt]
    exact hratio_pos v hvUp

  set L : E n →L[ℝ] ℝ := l + t • l₂ with hL
  have hLapp : ∀ x, L x = l x + t * l₂ x := by
    intro x
    simp [hL, smul_eq_mul]
  have hvert : ∀ v ∈ (P.vertices : Set (E n)),
      L v ≤ M + t * l₂ p₀ := by
    intro v hvS
    have hvV : v ∈ P.vertices := by exact_mod_cast hvS
    have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hvS
    by_cases hvup : l₂ p₀ < l₂ v
    · have hvUp : v ∈ Vup := by simp [hVup, hvV, hvup]
      have hratioR : ratio v ∈ R := by
        rw [hR]
        exact Finset.mem_image_of_mem ratio hvUp
      have htle : t ≤ ratio v := by
        rw [ht]
        exact Finset.min'_le R (ratio v) hratioR
      have hden : 0 < l₂ v - l₂ p₀ := by linarith
      have hmul : t * (l₂ v - l₂ p₀) ≤ M - l v := by
        calc
          t * (l₂ v - l₂ p₀) ≤ ratio v * (l₂ v - l₂ p₀) :=
            mul_le_mul_of_nonneg_right htle (le_of_lt hden)
          _ = M - l v := by
            rw [hratio]
            field_simp
      rw [hLapp]
      linarith
    · have hlv := hlmax v hvT
      have hl₂v : l₂ v ≤ l₂ p₀ := le_of_not_gt hvup
      rw [hLapp]
      nlinarith
  have hLbound : ∀ y ∈ P.toSet, L y ≤ M + t * l₂ p₀ :=
    le_su_toSet P L hvert

  have htmem : t ∈ R := by
    rw [ht]
    exact Finset.min'_mem R hRne
  obtain ⟨vcrit, hvcritUp, hvcritEq⟩ :=
    Finset.mem_image.mp (by simpa [hR] using htmem)
  have hvcritV : vcrit ∈ P.vertices := (Finset.mem_filter.mp hvcritUp).1
  have hvcritGrow : l₂ p₀ < l₂ vcrit := (Finset.mem_filter.mp hvcritUp).2
  have hvcrit_notf : vcrit ∉ f := by
    intro hvcf
    have := hl₂const vcrit hvcf
    linarith
  have hvcritL : L vcrit = M + t * l₂ p₀ := by
    have hden : l₂ vcrit - l₂ p₀ ≠ 0 := by linarith
    have heq : t * (l₂ vcrit - l₂ p₀) = M - l vcrit := by
      rw [← hvcritEq, hratio]
      field_simp
    rw [hLapp]
    linarith

  set f' : Set (E n) :=
    {x ∈ P.toSet | ∀ y ∈ P.toSet, L y ≤ L x} with hf'def
  have hsub : f ⊆ f' := by
    intro x hxf
    have hxT : x ∈ P.toSet := by
      rw [hl] at hxf
      exact hxf.1
    have hLx : L x = M + t * l₂ p₀ := by
      rw [hLapp, hlf x hxf, hl₂const x hxf]
    refine ⟨hxT, ?_⟩
    intro y hy
    exact (hLbound y hy).trans_eq hLx.symm
  have hvcritT : vcrit ∈ P.toSet :=
    subset_convexHull ℝ _ (by exact_mod_cast hvcritV)
  have hvcritf' : vcrit ∈ f' := by
    refine ⟨hvcritT, ?_⟩
    intro y hy
    exact (hLbound y hy).trans_eq hvcritL.symm
  have hf'ne : f'.Nonempty := ⟨p₀, hsub hp₀f⟩
  have hf'face : P.IsFace f' := by
    refine ⟨?_, hf'ne⟩
    intro _
    exact ⟨L, rfl⟩
  have hf'strict : f ⊂ f' := by
    refine hsub.ssubset_of_ne ?_
    intro heq
    exact hvcrit_notf (heq ▸ hvcritf')
  refine ⟨f', hf'face, hf'strict, ?_⟩
  intro y hyf' hynf
  have hyT : y ∈ P.toSet := hyf'.1
  have hly : l y < M := hl_strict y hyT hynf
  have hLle : L p₀ ≤ L y := hyf'.2 p₀ hp₀T
  rw [hLapp, hLapp, ← hM] at hLle
  have : l₂ p₀ < l₂ y := by nlinarith
  simpa [l₂] using this

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart35

section BundlePart36
/- Source: Cubical/Polytope/OrbitaVertici.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.OrbitaVertici.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




@[expose] public section

/-!
MOTORE COXETER, U4 — RIDUZIONE DELLA SURIETTIVITÀ ORBITALE (20 lug 2026).

Questo modulo chiude i due tratti non topologici di U4:

* ogni vertice di un politopo pieno in `E n`, per `n > 0`, è la faccia
  zero di una bandiera;
* una galleria dalla bandiera base a una bandiera radicata in `u` produce
  un elemento del sottogruppo semplice che manda il vertice base in `u`.

L'unica ipotesi lasciata esplicita nella suriettività finale è quindi la
connettività globale delle gallerie.  Nessun assioma geometrico viene
nascosto nella definizione dell'orbita.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una faccetta che contiene un vertice assegnato.  È la versione
radicata di `facet_exists`: l'invariante `v ∈ f` è preservato quando
`interpolazione` fa salire la faccia corrente. -/
theorem facet_exists_at_vertex (P : ConvexPolytope n) {d : ℕ}
    (hdim : Module.finrank ℝ (vectorSpan ℝ P.toSet) = d + 1)
    {v : E n} (hv : v ∈ P.vertices) :
    ∃ f : Set (E n), P.IsFace f ∧ faceDim f = d ∧ v ∈ f := by
  classical
  suffices H : ∀ k : ℕ, ∀ f : Set (E n), P.IsFace f → v ∈ f →
      d - faceDim f ≤ k → faceDim f ≤ d →
      ∃ g : Set (E n), P.IsFace g ∧ faceDim g = d ∧ v ∈ g by
    have hvface : P.IsFace ({v} : Set (E n)) := vertex_isFace P hv
    have hd0 : faceDim ({v} : Set (E n)) = 0 := faceDim_singleton v
    exact H d {v} hvface (Set.mem_singleton v)
      (by rw [hd0]; omega) (by rw [hd0]; omega)
  intro k
  induction k with
  | zero =>
      intro f hf hvf hk _hle
      exact ⟨f, hf, by omega, hvf⟩
  | succ m ih =>
      intro f hf hvf hk hle
      by_cases heq : faceDim f = d
      · exact ⟨f, hf, heq, hvf⟩
      · have hgap : faceDim f + 2 ≤
            Module.finrank ℝ (vectorSpan ℝ P.toSet) := by
          rw [hdim]
          omega
        obtain ⟨f', hf', hff', hf'ne⟩ := interpolazione P hf hgap
        have hvf' : v ∈ f' := hff'.1 hvf
        have hlt : faceDim f < faceDim f' :=
          faceDim_lt_of_ssubset P hf hf' hff'
        have hf'top : f' ⊂ P.toSet := by
          refine ⟨face_subset_toSet P hf', ?_⟩
          intro htop
          exact hf'ne (Set.Subset.antisymm (face_subset_toSet P hf') htop)
        have hltTop : faceDim f' <
            Module.finrank ℝ (vectorSpan ℝ P.toSet) :=
          faceDim_lt_of_ssubset P hf' (toSet_isFace P) hf'top
        apply ih f' hf' hvf'
        · omega
        · rw [hdim] at hltTop
          omega

/-- Catena completa radicata in un vertice.  A differenza di
`chain_exists`, conserva esplicitamente `c 0 = {v}`. -/
theorem chain_exists_at_vertex (P : ConvexPolytope n) :
    ∀ d : ℕ, Module.finrank ℝ (vectorSpan ℝ P.toSet) = d →
    ∀ v : E n, v ∈ P.vertices →
    ∃ c : ℕ → Set (E n),
      c 0 = {v} ∧
      (∀ k, k < d → P.IsFace (c k) ∧ faceDim (c k) = k) ∧
      (∀ j k, j < k → k < d → c j ⊂ c k) := by
  classical
  intro d
  induction d generalizing P with
  | zero =>
      intro _ v _hv
      exact ⟨fun _ => {v}, rfl,
        fun k hk => absurd hk (by omega),
        fun j k hjk hk => absurd hk (by omega)⟩
  | succ m ih =>
      intro hdim v hv
      obtain ⟨f, hf, hfdim, hvf⟩ :=
        facet_exists_at_vertex P hdim hv
      let Q : ConvexPolytope n := facePolytope P hf
      have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = m := by
        dsimp only [Q]
        rw [facePolytope_toSet P hf]
        exact hfdim
      have hvQ : v ∈ Q.vertices := by
        change v ∈ P.vertices.filter (· ∈ f)
        exact Finset.mem_filter.mpr ⟨hv, hvf⟩
      obtain ⟨c', hc'0, hc'1, hc'2⟩ := ih Q hQdim v hvQ
      have hfzero : m = 0 → f = ({v} : Set (E n)) := by
        intro hm
        obtain ⟨x, hx⟩ := faccia_dim0_singoletto hf.2 (by simpa [hm] using hfdim)
        have hvx : v = x := by
          rw [hx] at hvf
          exact Set.mem_singleton_iff.mp hvf
        simpa [hvx] using hx
      refine ⟨fun k => if k = m then f else c' k, ?_, ?_, ?_⟩
      · change (if 0 = m then f else c' 0) = {v}
        by_cases hm : m = 0
        · rw [if_pos hm.symm, hfzero hm]
        · rw [if_neg (Ne.symm hm), hc'0]
      · intro k hk
        change P.IsFace (if k = m then f else c' k) ∧
          faceDim (if k = m then f else c' k) = k
        by_cases hkm : k = m
        · rw [if_pos hkm]
          exact ⟨hf, hfdim.trans hkm.symm⟩
        · have hklt : k < m := by omega
          rw [if_neg hkm]
          obtain ⟨hkface, hkdim⟩ := hc'1 k hklt
          exact ⟨isFace_of_facePolytope P hf hkface, hkdim⟩
      · intro j k hjk hk
        change (if j = m then f else c' j) ⊂
          (if k = m then f else c' k)
        by_cases hkm : k = m
        · have hjm : j ≠ m := by omega
          rw [if_pos hkm, if_neg hjm]
          obtain ⟨hjface, hjdim⟩ := hc'1 j (by omega)
          have hjsub : c' j ⊆ f := by
            have := face_subset_toSet Q hjface
            simpa only [Q, facePolytope_toSet P hf] using this
          refine hjsub.ssubset_of_ne ?_
          intro heq
          have := congrArg faceDim heq
          rw [hjdim, hfdim] at this
          omega
        · have hklt : k < m := by omega
          have hjm : j ≠ m := by omega
          simp only [if_neg hkm, if_neg hjm]
          exact hc'2 j k hjk hklt

/-- Ogni vertice di un politopo pieno di dimensione ambiente positiva
radica una bandiera, in dimensione arbitraria. -/
theorem bandiera_al_vertice_generica (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (hn : 0 < n) {v : E n} (hv : v ∈ P.vertices) :
    ∃ F : P.Flag, F.face ⟨0, hn⟩ = {v} := by
  classical
  have hdim : Module.finrank ℝ (vectorSpan ℝ P.toSet) = n := hfull
  obtain ⟨c, hc0, hc1, hc2⟩ := chain_exists_at_vertex P n hdim v hv
  refine ⟨⟨fun k => c k, ?_, ?_, ?_⟩, ?_⟩
  · intro k
    exact (hc1 k k.isLt).1
  · intro k
    exact (hc1 k k.isLt).2
  · intro i j hij
    exact hc2 i j hij j.isLt
  · exact hc0


end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart36

section BundlePart37
/- Source: Cubical/Polytope/Camminata.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Camminata.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/


@[expose] public section

/-!
FASE 3A, F4c — LA CAMMINATA DEL SIMPLESSO, FORMA ASTRATTA (18 lug 2026).

Su un insieme finito con una relazione di adiacenza, un potenziale che
soddisfa il principio locale-globale (chi non cresce verso i vicini è
massimo globale) e ha un massimo unico x⋆ costringe ogni punto a essere
connesso a x⋆: la componente di partenza contiene il proprio argmax, che
non può essere un massimo locale diverso da x⋆.
-/

namespace LeanEval.Geometry.PlatonicClassification

/-- **LA CAMMINATA DEL SIMPLESSO**: con il principio locale-globale e un
massimo unico, ogni nodo è connesso al massimo. -/
theorem camminata_del_simplesso {α : Type*} [DecidableEq α]
    (X : Finset α) (adj : α → α → Prop) (φ : α → ℝ)
    (hlg : ∀ x ∈ X, (∀ y ∈ X, adj x y → φ y ≤ φ x) →
      ∀ z ∈ X, φ z ≤ φ x)
    {xs : α} (hxs : xs ∈ X)
    (hunico : ∀ z ∈ X, z ≠ xs → φ z < φ xs)
    {x₀ : α} (hx₀ : x₀ ∈ X) :
    Relation.ReflTransGen (fun p q => q ∈ X ∧ adj p q) x₀ xs := by
  classical
  set raggiunto : α → Prop :=
    fun q => Relation.ReflTransGen (fun p q => q ∈ X ∧ adj p q) x₀ q
    with hragg
  set R : Finset α := X.filter (fun q => raggiunto q) with hR
  have hx₀R : x₀ ∈ R := Finset.mem_filter.mpr ⟨hx₀, Relation.ReflTransGen.refl⟩
  have hRne : R.Nonempty := ⟨x₀, hx₀R⟩
  obtain ⟨m, hmR, hmmax⟩ := R.exists_max_image φ hRne
  have hmX : m ∈ X := (Finset.mem_filter.mp hmR).1
  have hmragg : raggiunto m := (Finset.mem_filter.mp hmR).2
  by_cases hms : m = xs
  · rw [hms] at hmragg
    exact hmragg
  · exfalso
    -- m non è massimo globale, quindi ha un vicino migliore
    have hnotmax : ¬ (∀ y ∈ X, adj m y → φ y ≤ φ m) := by
      intro hloc
      have h1 := hlg m hmX hloc xs hxs
      have h2 := hunico m hmX hms
      linarith
    push_neg at hnotmax
    obtain ⟨y, hyX, hadj, hlt⟩ := hnotmax
    -- il vicino è raggiunto, quindi sta in R: contraddice l'argmax
    have hyragg : raggiunto y := hmragg.tail ⟨hyX, hadj⟩
    have hyR : y ∈ R := Finset.mem_filter.mpr ⟨hyX, hyragg⟩
    have := hmmax y hyR
    linarith

end LeanEval.Geometry.PlatonicClassification

end
end BundlePart37

section BundlePart38
/- Source: Cubical/Polytope/BalinskiGenerale.lean -/

/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.BalinskiGenerale.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/







@[expose] public section

/-!
BALINSKI-LIGHT IN DIMENSIONE ARBITRARIA (20 lug 2026).

Il grafo degli estremi di un politopo convesso finito è connesso, anche
quando il politopo non è pieno nell'ambiente.  Il passo locale è il pivot
monotono: se un funzionale cresce verso qualche vertice, il primo tempo
critico produce una faccia più grande della zero-faccia corrente e tutti
i suoi punti nuovi migliorano il funzionale.  Una catena radicata estrae
da tale faccia uno spigolo uscente.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Da una faccia positiva che contiene un vertice si estrae uno spigolo
che contiene lo stesso vertice. -/
theorem edge_inside_face_at_vertex (P : ConvexPolytope n)
    {f : Set (E n)} (hf : P.IsFace f) {x : E n}
    (hxV : x ∈ P.vertices) (hxf : x ∈ f) (hdpos : 1 ≤ faceDim f) :
    ∃ e : Set (E n),
      P.IsFace e ∧ faceDim e = 1 ∧ x ∈ e ∧ e ⊆ f := by
  classical
  let Q : ConvexPolytope n := facePolytope P hf
  have hQT : Q.toSet = f := facePolytope_toSet P hf
  have hxQ : x ∈ Q.vertices := by
    change x ∈ P.vertices.filter (· ∈ f)
    exact Finset.mem_filter.mpr ⟨hxV, hxf⟩
  let d : ℕ := faceDim f
  have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = d := by
    change faceDim Q.toSet = d
    rw [hQT]
  have hdpos' : 1 ≤ d := by simpa only [d] using hdpos
  by_cases hd : d = 1
  · refine ⟨f, hf, ?_, hxf, Subset.rfl⟩
    simpa [d] using hd
  · have hd2 : 2 ≤ d := by
      omega
    obtain ⟨c, hc0, hcface, hcmono⟩ :=
      chain_exists_at_vertex Q d hQdim x hxQ
    have hc1 := hcface 1 (by omega)
    have hc01 := hcmono 0 1 (by omega) (by omega)
    have hxc1 : x ∈ c 1 := by
      apply hc01.1
      rw [hc0]
      exact Set.mem_singleton x
    have hc1sub : c 1 ⊆ f := by
      rw [← hQT]
      exact face_subset_toSet Q hc1.1
    exact ⟨c 1, isFace_of_facePolytope P hf hc1.1,
      hc1.2, hxc1, hc1sub⟩

/-- Relazione orientata usata dalla camminata: il punto di arrivo è un
vertice e i due punti sono gli estremi distinti di uno spigolo comune. -/
def GeneralVertexStep (P : ConvexPolytope n) (p q : E n) : Prop :=
  q ∈ P.vertices ∧ p ≠ q ∧
    ∃ e : Set (E n), P.IsFace e ∧ faceDim e = 1 ∧ p ∈ e ∧ q ∈ e

/-- **BALINSKI-LIGHT GENERALE**: due vertici di qualunque politopo finito
sono collegati da una camminata di spigoli.  Non servono né
`P.IsFullDim` né una restrizione sull'ambiente. -/
theorem balinski_light_general (P : ConvexPolytope n)
    {x₀ xs : E n} (hx₀ : x₀ ∈ P.vertices) (hxs : xs ∈ P.vertices) :
    Relation.ReflTransGen (GeneralVertexStep P) x₀ xs := by
  classical
  obtain ⟨l, hl⟩ := (vertex_isFace P hxs).1 (Set.singleton_nonempty xs)
  have hxsT : xs ∈ P.toSet := by
    have hmem : xs ∈ ({xs} : Set (E n)) := Set.mem_singleton xs
    rw [hl] at hmem
    exact hmem.1
  have hlmax : ∀ y ∈ P.toSet, l y ≤ l xs := by
    have hmem : xs ∈ ({xs} : Set (E n)) := Set.mem_singleton xs
    rw [hl] at hmem
    exact hmem.2
  have hlchar : ∀ q ∈ P.toSet, l q = l xs → q = xs := by
    intro q hq heq
    have hmem : q ∈ ({xs} : Set (E n)) := by
      rw [hl]
      exact ⟨hq, fun y hy => le_trans (hlmax y hy) (le_of_eq heq.symm)⟩
    exact Set.mem_singleton_iff.mp hmem
  let EdgeAdj : E n → E n → Prop := fun p q =>
    p ≠ q ∧ ∃ e : Set (E n),
      P.IsFace e ∧ faceDim e = 1 ∧ p ∈ e ∧ q ∈ e
  have hlocal_global : ∀ x ∈ P.vertices,
      (∀ y ∈ P.vertices, EdgeAdj x y → l y ≤ l x) →
      ∀ z ∈ P.vertices, l z ≤ l x := by
    intro x hxV hlocal z hzV
    by_contra hnot
    have hlxz : l x < l z := lt_of_not_ge hnot
    have hxFace : P.IsFace ({x} : Set (E n)) := vertex_isFace P hxV
    obtain ⟨g, hg⟩ := hxFace.1 hxFace.2
    let w : E n := (InnerProductSpace.toDual ℝ (E n)).symm l
    have hwspec : ∀ y : E n, inner ℝ w y = l y := by
      intro y
      dsimp only [w]
      exact InnerProductSpace.toDual_symm_apply
    have hwconst : ∀ y ∈ ({x} : Set (E n)),
        inner ℝ w y = inner ℝ w x := by
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
    have hwup : ∃ u ∈ P.vertices, inner ℝ w x < inner ℝ w u := by
      exact ⟨z, hzV, by simpa only [hwspec] using hlxz⟩
    obtain ⟨f, hf, hxf, himprove⟩ :=
      perno_parametrico_crescente_monotono P hxFace g hg x
        (Set.mem_singleton x) w hwconst hwup
    have hfdimpos : 1 ≤ faceDim f := by
      have hlt := faceDim_lt_of_ssubset P hxFace hf hxf
      rw [faceDim_singleton] at hlt
      omega
    obtain ⟨e, he, hde, hxe, hef⟩ :=
      edge_inside_face_at_vertex P hf hxV (hxf.1 (Set.mem_singleton x)) hfdimpos
    obtain ⟨y, hyV, hye, hyne, _hseg⟩ :=
      spigolo_segmento P he hde hxV hxe
    have hynot : y ∉ ({x} : Set (E n)) := by
      simpa [Set.mem_singleton_iff] using hyne
    have hxylt : l x < l y := by
      have hinc := himprove y (hef hye) hynot
      simpa only [hwspec] using hinc
    have hxyle : l y ≤ l x :=
      hlocal y hyV ⟨hyne.symm, e, he, hde, hxe, hye⟩
    linarith
  have hunique : ∀ z ∈ P.vertices, z ≠ xs → l z < l xs := by
    intro z hzV hzne
    have hzT : z ∈ P.toSet := subset_convexHull ℝ _ hzV
    rcases lt_or_eq_of_le (hlmax z hzT) with hlt | heq
    · exact hlt
    · exact (hzne (hlchar z hzT heq)).elim
  have hwalk := camminata_del_simplesso P.vertices EdgeAdj l
    hlocal_global hxs hunique hx₀
  exact Relation.ReflTransGen.mono (by
    rintro p q ⟨hqV, hpq, e, he, hde, hpe, hqe⟩
    exact ⟨hqV, hpq, e, he, hde, hpe, hqe⟩) _ _ hwalk

end LeanEval.Geometry.PlatonicClassification

end
end
end BundlePart38

section BundlePart39
/- Source: Papers/ParallelMaps.lean -/





@[expose] public section

/-!
# Parallel maps on actual polytope edges

The edge relation is the geometric one: two distinct extreme vertices on an
exposed one-dimensional face. The local maximum principle is derived from
the finite face pivot, and all statements below concern this actual graph.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Pointwise RealInnerProductSpace
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def IsParallelMap (P : ConvexPolytope d) (f : E d → E d) : Prop :=
  ∀ x ∈ P.vertices, ∀ y ∈ P.vertices, GeneralVertexStep P x y →
    ∃ c : ℝ, f y - f x = c • (y - x)

def IsPositiveParallelMap (P : ConvexPolytope d) (f : E d → E d) : Prop :=
  ∀ x ∈ P.vertices, ∀ y ∈ P.vertices, GeneralVertexStep P x y →
    ∃ c : ℝ, 0 < c ∧ f y - f x = c • (y - x)

theorem IsPositiveParallelMap.parallel {P : ConvexPolytope d} {f : E d → E d}
    (h : IsPositiveParallelMap P f) : IsParallelMap P f := by
  intro x hx y hy hxy
  obtain ⟨c, _, hc⟩ := h x hx y hy hxy
  exact ⟨c, hc⟩

def IsHomothetyOnVertices (P : ConvexPolytope d) (f : E d → E d) : Prop :=
  ∃ a : ℝ, ∃ b : E d, ∀ v ∈ P.vertices, f v = a • v + b

/-- Failure of a global linear maximum gives an actual increasing edge. -/
theorem exists_increasing_edge (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ)
    {x z : E d} (hx : x ∈ P.vertices) (hz : z ∈ P.vertices) (hlt : l x < l z) :
    ∃ y : E d, GeneralVertexStep P x y ∧ l x < l y := by
  have hxFace : P.IsFace ({x} : Set (E d)) := vertex_isFace P hx
  obtain ⟨g, hg⟩ := hxFace.1 hxFace.2
  let w : E d := (InnerProductSpace.toDual ℝ (E d)).symm l
  have hw (y : E d) : inner ℝ w y = l y := InnerProductSpace.toDual_symm_apply
  have hconst : ∀ y ∈ ({x} : Set (E d)), inner ℝ w y = inner ℝ w x := by
    rintro y rfl
    rfl
  obtain ⟨F, hF, hproper, himprove⟩ := perno_parametrico_crescente_monotono
    P hxFace g hg x (Set.mem_singleton x) w hconst ⟨z, hz, by simpa only [hw] using hlt⟩
  have hdim : 1 ≤ faceDim F := by
    have h := faceDim_lt_of_ssubset P hxFace hF hproper
    rw [faceDim_singleton] at h
    omega
  obtain ⟨e, he, hde, hxe, heF⟩ := edge_inside_face_at_vertex P hF hx
    (hproper.1 (Set.mem_singleton x)) hdim
  obtain ⟨y, hy, hye, hyx, _⟩ := spigolo_segmento P he hde hx hxe
  refine ⟨y, ⟨hy, hyx.symm, e, he, hde, hxe, hye⟩, ?_⟩
  have hyout : y ∉ ({x} : Set (E d)) := by simpa only [Set.mem_singleton_iff] using hyx
  simpa only [hw] using himprove y (heF hye) hyout

theorem positive_parallel_max_reflect {P : ConvexPolytope d} {f : E d → E d}
    (hf : IsPositiveParallelMap P f) (l : E d →L[ℝ] ℝ)
    {x : E d} (hx : x ∈ P.vertices)
    (hmax : ∀ y ∈ P.vertices, l (f y) ≤ l (f x)) :
    ∀ y ∈ P.vertices, l y ≤ l x := by
  intro z hz
  by_contra hnot
  obtain ⟨y, hxy, hlt⟩ := exists_increasing_edge P l hx hz (lt_of_not_ge hnot)
  obtain ⟨c, hc, heq⟩ := hf x hx y hxy.1 hxy
  have h := congrArg l heq
  simp only [map_sub, map_smul, smul_eq_mul] at h
  have hle := hmax y hxy.1
  nlinarith

/-- A parallel map remains constant under a supporting functional along
each face on which that functional is constant. -/
theorem parallel_constant_on_face {P : ConvexPolytope d} {f : E d → E d}
    (hf : IsParallelMap P f) {F : Set (E d)} (hF : P.IsFace F)
    (l : E d →L[ℝ] ℝ) (hconst : ∀ x ∈ F, ∀ y ∈ F, l x = l y)
    {x y : E d} (hx : x ∈ P.vertices) (hy : y ∈ P.vertices)
    (hxF : x ∈ F) (hyF : y ∈ F) : l (f x) = l (f y) := by
  classical
  let Q := facePolytope P hF
  have hxQ : x ∈ Q.vertices := Finset.mem_filter.mpr ⟨hx, hxF⟩
  have hyQ : y ∈ Q.vertices := Finset.mem_filter.mpr ⟨hy, hyF⟩
  have hw := balinski_light_general Q hxQ hyQ
  have hwalk : ∀ z, Relation.ReflTransGen (GeneralVertexStep Q) x z →
      z ∈ Q.vertices ∧ l (f z) = l (f x) := by
    intro z hpath
    induction hpath with
    | refl => exact ⟨hxQ, rfl⟩
    | @tail u v hpath huv ih =>
      have hu := Finset.mem_filter.mp ih.1
      have hv := Finset.mem_filter.mp huv.1
      obtain ⟨_, hne, e, he, hde, hue, hve⟩ := huv
      have hstep : GeneralVertexStep P u v :=
        ⟨hv.1, hne, e, isFace_of_facePolytope P hF he, hde, hue, hve⟩
      obtain ⟨c, hc⟩ := hf u hu.1 v hv.1 hstep
      have h := congrArg l hc
      simp only [map_sub, map_smul, smul_eq_mul, hconst v hv.2 u hu.2,
        sub_self, mul_zero, sub_eq_zero] at h
      exact ⟨Finset.mem_filter.mpr hv, h.trans ih.2⟩
  exact (hwalk y hw).2.symm

theorem positive_parallel_max_preserve {P : ConvexPolytope d} {f : E d → E d}
    (hf : IsPositiveParallelMap P f) (l : E d →L[ℝ] ℝ)
    {x : E d} (hx : x ∈ P.vertices)
    (hmax : ∀ y ∈ P.vertices, l y ≤ l x) :
    ∀ y ∈ P.vertices, l (f y) ≤ l (f x) := by
  classical
  obtain ⟨w, hw, hwm⟩ := P.vertices.exists_max_image (fun y => l (f y)) P.vertices_nonempty
  have hwmax := positive_parallel_max_reflect hf l hw hwm
  let F : Set (E d) := {z ∈ P.toSet | ∀ y ∈ P.toSet, l y ≤ l z}
  have hxF : x ∈ F := ⟨subset_convexHull ℝ _ hx, le_su_toSet P l hmax⟩
  have hwF : w ∈ F := ⟨subset_convexHull ℝ _ hw, le_su_toSet P l hwmax⟩
  have hF : P.IsFace F := ⟨by intro _; exact ⟨l, rfl⟩, ⟨x, hxF⟩⟩
  have hconst : ∀ a ∈ F, ∀ b ∈ F, l a = l b := by
    intro a ha b hb
    exact le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)
  have heq := parallel_constant_on_face hf.parallel hF l hconst hx hw hxF hwF
  intro y hy
  exact (hwm y hy).trans_eq heq.symm

theorem positive_parallel_strict_max_preserve {P : ConvexPolytope d} {f : E d → E d}
    (hf : IsPositiveParallelMap P f) (l : E d →L[ℝ] ℝ)
    {x : E d} (hx : x ∈ P.vertices)
    (hstrict : ∀ y ∈ P.vertices, y ≠ x → l y < l x) :
    ∀ y ∈ P.vertices, y ≠ x → l (f y) < l (f x) := by
  have hmax : ∀ y ∈ P.vertices, l y ≤ l x := by
    intro y hy
    by_cases h : y = x
    · simp [h]
    · exact (hstrict y hy h).le
  have hfm := positive_parallel_max_preserve hf l hx hmax
  intro y hy hyx
  refine lt_of_le_of_ne (hfm y hy) ?_
  intro heq
  have hym : ∀ z ∈ P.vertices, l (f z) ≤ l (f y) := by
    intro z hz
    exact (hfm z hz).trans_eq heq.symm
  have h := positive_parallel_max_reflect hf l hy hym x hx
  exact (not_le_of_gt (hstrict y hy hyx)) h

theorem exists_vertex_exposer (P : ConvexPolytope d) {x : E d} (hx : x ∈ P.vertices) :
    ∃ l : E d →L[ℝ] ℝ, ∀ y ∈ P.vertices, y ≠ x → l y < l x := by
  obtain ⟨l, hl⟩ := (vertex_isFace P hx).1 (Set.singleton_nonempty x)
  have hm : x ∈ {z ∈ P.toSet | ∀ y ∈ P.toSet, l y ≤ l z} := by
    rw [← hl]
    exact Set.mem_singleton x
  refine ⟨l, ?_⟩
  intro y hy hyx
  have hybody : y ∈ P.toSet := subset_convexHull ℝ _ hy
  refine lt_of_le_of_ne (hm.2 y hybody) ?_
  intro heq
  apply hyx
  have hyface : y ∈ ({x} : Set (E d)) := by
    rw [hl]
    exact ⟨hybody, fun z hz => (hm.2 z hz).trans_eq heq.symm⟩
  exact hyface

def positiveMapPolytope (P : ConvexPolytope d) (f : E d → E d)
    (hf : IsPositiveParallelMap P f) : ConvexPolytope d := by
  classical
  apply polytopeOfStrictMinima (P.vertices.image f) (P.vertices_nonempty.image f)
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨l, hl⟩ := exists_vertex_exposer P hv
  refine ⟨-l, ?_⟩
  intro y hy hyne
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  have hwv : w ≠ v := by intro h; exact hyne (congrArg f h)
  simpa only [ContinuousLinearMap.neg_apply, neg_lt_neg_iff] using
    positive_parallel_strict_max_preserve hf l hv hl w hw hwv

@[simp] theorem positiveMapPolytope_vertices (P : ConvexPolytope d) (f : E d → E d)
    (hf : IsPositiveParallelMap P f) :
    (positiveMapPolytope P f hf).vertices = P.vertices.image f := rfl

end Papers.Polytopes

end
end
end BundlePart39

section BundlePart40
/- Source: Papers/EdgeSpan.lean -/




@[expose] public section

/-!
# The directions of the edges at one vertex span the polytope

The proof uses the actual edge maximum principle. A functional that is
constant on the neighbors of a vertex is constant on every vertex, hence
on the whole convex hull. Separation of linear subspaces then gives the
span equality, without a full-dimensionality assumption.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem vertex_max_of_edge_max (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ)
    {v : E d} (hv : v ∈ P.vertices)
    (hmax : ∀ y, GeneralVertexStep P v y → l y ≤ l v) :
    ∀ z ∈ P.toSet, l z ≤ l v := by
  apply le_su_toSet P l
  intro z hz
  by_contra h
  obtain ⟨y, hstep, hlt⟩ := exists_increasing_edge P l hv hz (lt_of_not_ge h)
  exact (not_lt_of_ge (hmax y hstep)) hlt

theorem linear_constant_of_neighbors (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ)
    {v : E d} (hv : v ∈ P.vertices)
    (hconst : ∀ y, GeneralVertexStep P v y → l y = l v) :
    ∀ z ∈ P.toSet, l z = l v := by
  have hu := vertex_max_of_edge_max P l hv (fun y hy => (hconst y hy).le)
  have hl := vertex_max_of_edge_max P (-l) hv (by
    intro y hy
    simp only [ContinuousLinearMap.neg_apply, hconst y hy, le_refl])
  intro z hz
  exact le_antisymm (hu z hz) (by
    simpa only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] using hl z hz)

theorem vectorSpan_le_ker_of_constant (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ)
    (c : ℝ) (hconst : ∀ z ∈ P.toSet, l z = c) :
    vectorSpan ℝ P.toSet ≤ l.toLinearMap.ker := by
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  intro z hz
  obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_vsub.mp hz
  change l (p - q) = 0
  rw [map_sub, hconst p hp, hconst q hq, sub_self]

def edgeStarSpan (P : ConvexPolytope d) (v : E d) : Submodule ℝ (E d) :=
  Submodule.span ℝ {w | ∃ y, GeneralVertexStep P v y ∧ w = y - v}

theorem edgeStarSpan_eq_vectorSpan (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) : edgeStarSpan P v = vectorSpan ℝ P.toSet := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨y, hy, rfl⟩
    exact vsub_mem_vectorSpan ℝ (subset_convexHull ℝ _ hy.1)
      (subset_convexHull ℝ _ hv)
  · intro z hz
    by_contra hnot
    obtain ⟨g, hgz, hgW⟩ := Submodule.exists_le_ker_of_notMem hnot
    let l : E d →L[ℝ] ℝ := g.toContinuousLinearMap
    have hneighbors : ∀ y, GeneralVertexStep P v y → l y = l v := by
      intro y hy
      have hmem : y - v ∈ edgeStarSpan P v :=
        Submodule.subset_span ⟨y, hy, rfl⟩
      have hzero : g (y - v) = 0 := hgW hmem
      change g y = g v
      simpa only [map_sub, sub_eq_zero] using hzero
    have hbody := linear_constant_of_neighbors P l hv hneighbors
    have hzero : l z = 0 := vectorSpan_le_ker_of_constant P l (l v) hbody hz
    exact hgz hzero

theorem fullDim_edgeStarSpan (P : ConvexPolytope d) (hP : P.IsFullDim)
    {v : E d} (hv : v ∈ P.vertices) : edgeStarSpan P v = ⊤ := by
  rw [edgeStarSpan_eq_vectorSpan P hv]
  apply Submodule.eq_top_of_finrank_eq
  change finrank ℝ (vectorSpan ℝ P.toSet) = finrank ℝ (E d)
  rw [finrank_euclideanSpace_fin]
  exact hP

end Papers.Polytopes

end
end
end BundlePart40

section BundlePart41
/- Source: Papers/SimpleVertexBasis.lean -/




@[expose] public section

/-!
# The genuine edge basis at a simple vertex

The basis is derived from actual incident edges and full dimensionality.
Its coordinate functionals are nonnegative on the whole body, by the
edge maximum principle. Thus the orthant normalization used for deletion
is a conclusion of simplicity, rather than an extra geometric assumption.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem adj_iff_generalVertexStep (P : ConvexPolytope d) (u v : VertexType P) :
    (polytopeGraph P).Adj u v ↔ GeneralVertexStep P u.val v.val := by
  constructor
  · rintro ⟨hne, e, he, hde, hue, hve⟩
    exact ⟨v.property, fun h => hne (Subtype.ext h), e, he, hde, hue, hve⟩
  · rintro ⟨_, hne, e, he, hde, hue, hve⟩
    exact ⟨fun h => hne (congrArg Subtype.val h), e, he, hde, hue, hve⟩

abbrev NeighborIndex (P : ConvexPolytope d) (v : VertexType P) :=
  (polytopeGraph P).neighborSet v

def neighborDirection (P : ConvexPolytope d) (v : VertexType P)
    (u : NeighborIndex P v) : E d := u.val.val - v.val

theorem range_neighborDirection (P : ConvexPolytope d) (v : VertexType P) :
    Set.range (neighborDirection P v) =
      {w | ∃ y, GeneralVertexStep P v.val y ∧ w = y - v.val} := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.val.val, (adj_iff_generalVertexStep P v u.val).mp u.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨⟨y, hy.1⟩, (adj_iff_generalVertexStep P v ⟨y, hy.1⟩).mpr hy⟩, rfl⟩

theorem span_neighborDirection (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) : Submodule.span ℝ (Set.range (neighborDirection P v)) = ⊤ := by
  rw [range_neighborDirection]
  exact fullDim_edgeStarSpan P hP v.property

theorem card_neighbors_of_simple (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) :
    Fintype.card (NeighborIndex P v) = finrank ℝ (E d) := by
  rw [SimpleGraph.card_neighborSet_eq_degree, finrank_euclideanSpace_fin]
  exact hs.trans hP

/-- No linear independence hypothesis is assumed: it follows from the
degree-d condition and the actual edge-star spanning theorem. -/
theorem simple_neighbor_directions_independent
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) :
    LinearIndependent ℝ (neighborDirection P v) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank
    (by rw [span_neighborDirection P hP v]) (card_neighbors_of_simple P hP v hs)

def simpleVertexBasis (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) : Basis (NeighborIndex P v) ℝ (E d) :=
  basisOfTopLeSpanOfCardEqFinrank (neighborDirection P v)
    (by rw [span_neighborDirection P hP v]) (card_neighbors_of_simple P hP v hs)

@[simp] theorem simpleVertexBasis_apply
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (u : NeighborIndex P v) :
    simpleVertexBasis P hP v hs u = u.val.val - v.val := by
  simp only [simpleVertexBasis, coe_basisOfTopLeSpanOfCardEqFinrank, neighborDirection]

/-- The ordinary edge-basis coordinates of every body point are
nonnegative after translating the simple vertex to the origin. -/
theorem simpleVertexBasis_coordinates_nonneg
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (x : E d) (hx : x ∈ P.toSet)
    (i : NeighborIndex P v) :
    0 ≤ (simpleVertexBasis P hP v hs).repr (x - v.val) i := by
  let b := simpleVertexBasis P hP v hs
  let l : E d →L[ℝ] ℝ := (b.coord i).toContinuousLinearMap
  have hmax : ∀ y, GeneralVertexStep P v.val y → (-l) y ≤ (-l) v.val := by
    intro y hy
    let u : NeighborIndex P v :=
      ⟨⟨y, hy.1⟩, (adj_iff_generalVertexStep P v ⟨y, hy.1⟩).mpr hy⟩
    have heq : l (y - v.val) = if i = u then 1 else 0 := by
      change b.coord i (y - v.val) = _
      have hbu : b u = y - v.val := simpleVertexBasis_apply P hP v hs u
      rw [← hbu]
      simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, eq_comm]
    have hn : 0 ≤ l (y - v.val) := by
      rw [heq]
      split_ifs <;> norm_num
    simp only [map_sub] at hn
    change -l y ≤ -l v.val
    linarith
  have h := vertex_max_of_edge_max P (-l) v.property hmax x hx
  change 0 ≤ l (x - v.val)
  simp only [map_sub, ContinuousLinearMap.neg_apply] at *
  linarith

end Papers.Polytopes

end
end
end BundlePart41

section BundlePart42
/- Source: Papers/SubpolytopeFaces.lean -/





@[expose] public section

/-!
# Retaining exposed faces in a smaller convex hull

An exposed face remains a face of any intermediate polytope containing it.
In particular an actual edge remains an edge after deleting other vertices.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem face_of_body_subset (P Q : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) (hQP : Q.toSet ⊆ P.toSet) (hFQ : F ⊆ Q.toSet) : Q.IsFace F := by
  obtain ⟨x, hx⟩ := hF.2
  obtain ⟨l, hl⟩ := hF.1 hF.2
  have hxP : x ∈ P.toSet ∧ ∀ y ∈ P.toSet, l y ≤ l x := by
    have hx' := hx
    rw [hl] at hx'
    exact hx'
  refine ⟨?_, ⟨x, hx⟩⟩
  intro _
  refine ⟨l, ?_⟩
  ext z
  constructor
  · intro hz
    have hzP : z ∈ P.toSet ∧ ∀ y ∈ P.toSet, l y ≤ l z := by
      have hz' := hz
      rw [hl] at hz'
      exact hz'
    exact ⟨hFQ hz, fun y hy => hzP.2 y (hQP hy)⟩
  · rintro ⟨hzQ, hzmax⟩
    rw [hl]
    exact ⟨hQP hzQ, fun y hy => (hxP.2 y hy).trans (hzmax x (hFQ hx))⟩

theorem vertexSubset_body_subset (P : ConvexPolytope d) (S : Finset (E d))
    (hne : S.Nonempty) (hsub : S ⊆ P.vertices) :
    (vertexSubsetPolytope P S hne hsub).toSet ⊆ P.toSet :=
  convexHull_mono hsub

theorem step_in_vertexSubset (P : ConvexPolytope d) (S : Finset (E d))
    (hne : S.Nonempty) (hsub : S ⊆ P.vertices)
    {x y : E d} (hx : x ∈ S) (hy : y ∈ S) (hxy : GeneralVertexStep P x y) :
    GeneralVertexStep (vertexSubsetPolytope P S hne hsub) x y := by
  obtain ⟨_, hneXY, F, hF, hdF, hxF, hyF⟩ := hxy
  have hseg : F = segment ℝ x y := edge_eq_segment P hF hdF (hsub hx) (hsub hy) hxF hyF hneXY
  have hFQ : F ⊆ (vertexSubsetPolytope P S hne hsub).toSet := by
    rw [hseg]
    exact (convex_convexHull ℝ (S : Set (E d))).segment_subset
      (subset_convexHull ℝ _ hx) (subset_convexHull ℝ _ hy)
  exact ⟨hy, hneXY, F, face_of_body_subset P _ hF
    (vertexSubset_body_subset P S hne hsub) hFQ, hdF, hxF, hyF⟩

theorem vectorSpan_polytope_vertices (P : ConvexPolytope d) :
    vectorSpan ℝ P.toSet = vectorSpan ℝ (P.vertices : Set (E d)) := by
  change vectorSpan ℝ (convexHull ℝ (P.vertices : Set (E d))) = _
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]

theorem actual_vertices_card_gt_dim (P : ConvexPolytope d) : P.dim < P.vertices.card := by
  letI : Nonempty (VertexType P) := by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨⟨v, hv⟩⟩
  have h := finrank_vectorSpan_range_add_one_le ℝ
    (fun v : VertexType P => v.val)
  have hrange : Set.range (fun v : VertexType P => v.val) = (P.vertices : Set (E d)) := by
    ext v
    simp
  rw [hrange, ← vectorSpan_polytope_vertices P] at h
  have hcard : Fintype.card (VertexType P) = P.vertices.card := by simp
  rw [hcard] at h
  exact Nat.lt_of_succ_le h

theorem deleteVertex_coordinates (P : ConvexPolytope d) (K : Subfield ℝ)
    (hK : CoordinatesIn K P) (v : E d) (hne : (P.vertices.erase v).Nonempty) :
    CoordinatesIn K (deleteVertex P v hne) := by
  intro w hw i
  exact hK w (Finset.mem_of_mem_erase hw) i

end Papers.Polytopes

end
end
end BundlePart42

section BundlePart43
/- Source: Papers/FiniteConvexGeometry.lean -/










@[expose] public section

/-!
# Finite convex hulls and one-dimensional exposed faces

The argument for `mem_hull_of_maximizers` is adapted from Daniele Cappello's
Apache-2.0-licensed `FacciaArgmax` module; see THIRD_PARTY.md. Its proof needs
only a normed vector space, so the stronger inner-product hypothesis in that
source is omitted here.
-/

noncomputable section
namespace Papers.Geometry
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_hull_of_maximizers (s : Finset E) (l : E →L[ℝ] ℝ) {y : E}
    (hy : y ∈ convexHull ℝ (s : Set E))
    (hmax : ∀ w ∈ convexHull ℝ (s : Set E), l w ≤ l y) :
    y ∈ convexHull ℝ {x ∈ (s : Set E) | l x = l y} := by
  classical
  rw [Finset.convexHull_eq] at hy
  obtain ⟨w, hw0, hw1, hwy⟩ := hy
  have hM : ∀ x ∈ s, l x ≤ l y := fun x hx =>
    hmax x (subset_convexHull ℝ _ hx)
  have hyrep : y = ∑ x ∈ s, w x • x := by
    rw [← hwy, Finset.centerMass_eq_of_sum_1 _ _ hw1]
    rfl
  have hly : l y = ∑ x ∈ s, w x * l x := by
    rw [hyrep, map_sum]
    congr 1
    funext x
    rw [map_smul]
    rfl
  have hactive : ∀ x ∈ s, 0 < w x → l x = l y := by
    intro x hx hwx
    by_contra hne
    have hlt : l x < l y := lt_of_le_of_ne (hM x hx) hne
    have hsum : ∑ z ∈ s, w z * l z < ∑ z ∈ s, w z * l y := by
      apply Finset.sum_lt_sum
      · intro z hz
        exact mul_le_mul_of_nonneg_left (hM z hz) (hw0 z hz)
      · exact ⟨x, hx, mul_lt_mul_of_pos_left hlt hwx⟩
    rw [← Finset.sum_mul, hw1, one_mul] at hsum
    rw [hly] at hsum
    exact lt_irrefl _ hsum
  have hzero : ∀ x ∈ s, ¬l x = l y → w x = 0 := by
    intro x hx hne
    by_contra hw
    exact hne (hactive x hx (lt_of_le_of_ne (hw0 x hx) (Ne.symm hw)))
  let sf : Finset E := s.filter (fun x => l x = l y)
  have hsub : sf ⊆ s := Finset.filter_subset _ _
  have hw1' : ∑ x ∈ sf, w x = 1 := by
    rw [← hw1]
    symm
    apply (Finset.sum_subset hsub ?_).symm
    intro x hx hnx
    apply hzero x hx
    intro heq
    exact hnx (Finset.mem_filter.mpr ⟨hx, heq⟩)
  have hyrep' : y = ∑ x ∈ sf, w x • x := by
    rw [hyrep]
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have : w x = 0 := by
      apply hzero x hx
      intro heq
      exact hnx (Finset.mem_filter.mpr ⟨hx, heq⟩)
    rw [this, zero_smul]
  have hmem : y ∈ convexHull ℝ (sf : Set E) := by
    rw [Finset.convexHull_eq]
    refine ⟨w, fun z hz => hw0 z (hsub hz), hw1', ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1']
    exact hyrep'.symm
  have hset : (sf : Set E) = {x ∈ (s : Set E) | l x = l y} := by
    ext x
    simp [sf]
  rw [← hset]
  exact hmem

theorem mem_hull_of_minimizers (s : Finset E) (l : E →L[ℝ] ℝ) {y : E}
    (hy : y ∈ convexHull ℝ (s : Set E))
    (hmin : ∀ w ∈ convexHull ℝ (s : Set E), l y ≤ l w) :
    y ∈ convexHull ℝ {x ∈ (s : Set E) | l x = l y} := by
  simpa only [ContinuousLinearMap.neg_apply, neg_inj] using
    mem_hull_of_maximizers s (-l) hy (by
      simpa only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] using hmin)

theorem linear_lower_bound_on_convexHull (s : Set E) (l : E →L[ℝ] ℝ)
    (a : ℝ) (ha : ∀ x ∈ s, a ≤ l x) :
    ∀ x ∈ convexHull ℝ s, a ≤ l x :=
  convexHull_min ha (convex_halfSpace_ge (LinearMap.isLinear l.toLinearMap) a)

/-- A finite convex hull contained in an affine line is a genuine closed
segment with endpoints among its generators. Degenerate segments are allowed. -/
theorem finite_hull_parallel_eq_segment (s : Finset E) (hs : s.Nonempty)
    (δ : E) (hδ : δ ≠ 0)
    (hparallel : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ Submodule.span ℝ {δ}) :
    ∃ x ∈ s, ∃ y ∈ s, convexHull ℝ (s : Set E) = segment ℝ x y := by
  classical
  have hnot : δ ∉ (⊥ : Submodule ℝ E) := by simpa using hδ
  obtain ⟨g, hg, _⟩ := Submodule.exists_le_ker_of_notMem hnot
  let l : E →ₗ[ℝ] ℝ := (g δ)⁻¹ • g
  have hl : l δ = 1 := by simp [l, hg]
  obtain ⟨x, hx, hxmin⟩ := s.exists_min_image l hs
  obtain ⟨y, hy, hymax⟩ := s.exists_max_image l hs
  have hform (z : E) (hz : z ∈ s) : z - x = (l z - l x) • δ := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hparallel z hz x hx)
    have he : a = l z - l x := by
      have h := congrArg l ha
      simpa only [map_smul, map_sub, smul_eq_mul, hl, mul_one] using h
    exact (he ▸ ha).symm
  have hgen : (s : Set E) ⊆ segment ℝ x y := by
    intro z hz
    have hlow := hxmin z hz
    have hupp := hymax z hz
    have hxy := hxmin y hy
    by_cases hb : l y - l x = 0
    · have hzval : l z - l x = 0 := by linarith
      have hzx : z = x := by
        have h := hform z hz
        rw [hzval, zero_smul, sub_eq_zero] at h
        exact h
      rw [hzx]
      exact left_mem_segment ℝ x y
    · have hbpos : 0 < l y - l x := lt_of_le_of_ne (sub_nonneg.mpr hxy) (Ne.symm hb)
      rw [segment_eq_image']
      refine ⟨(l z - l x) / (l y - l x), ⟨div_nonneg (sub_nonneg.mpr hlow) hbpos.le,
        (div_le_one hbpos).mpr (by linarith)⟩, ?_⟩
      change x + ((l z - l x) / (l y - l x)) • (y - x) = z
      rw [hform y hy, smul_smul, div_mul_cancel₀ _ hb, ← hform z hz]
      module
  refine ⟨x, hx, y, hy, Set.Subset.antisymm
    (convexHull_min hgen (convex_segment x y)) ?_⟩
  exact (convex_convexHull ℝ (s : Set E)).segment_subset
    (subset_convexHull ℝ _ hx) (subset_convexHull ℝ _ hy)

end Papers.Geometry

end
end
end BundlePart43

section BundlePart44
/- Source: Papers/SimpleVertexCorner.lean -/







@[expose] public section

/-!
# Cutting off the corner at a simple vertex

The height is the sum of the genuine edge-basis coordinates. It is zero
at the chosen vertex and one at every neighbor. Every other actual vertex
has height strictly greater than one. Deleting the simple vertex is
exactly the intersection with the height-at-least-one halfspace.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def cornerHeight (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (x : E d) : ℝ :=
  ∑ i : NeighborIndex P v, (simpleVertexBasis P hP v hs).repr (x - v.val) i

@[simp] theorem cornerHeight_self (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) :
    cornerHeight P hP v hs v.val = 0 := by
  simp [cornerHeight]

@[simp] theorem cornerHeight_neighbor (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (u : NeighborIndex P v) :
    cornerHeight P hP v hs u.val.val = 1 := by
  unfold cornerHeight
  rw [← simpleVertexBasis_apply P hP v hs u, Basis.repr_self]
  simp

theorem mem_corner_simplex_of_height_le_one
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (x : E d) (hx : x ∈ P.toSet)
    (hheight : cornerHeight P hP v hs x ≤ 1) :
    x ∈ convexHull ℝ (insert v.val (Set.range (fun u : NeighborIndex P v => u.val.val))) := by
  let b := simpleVertexBasis P hP v hs
  let c : NeighborIndex P v → ℝ := fun i => b.repr (x - v.val) i
  let w : Option (NeighborIndex P v) → ℝ
    | none => 1 - ∑ i, c i
    | some i => c i
  let z : Option (NeighborIndex P v) → E d
    | none => v.val
    | some i => i.val.val
  have hc : ∀ i, 0 ≤ c i := simpleVertexBasis_coordinates_nonneg P hP v hs x hx
  have hsum : ∑ i, c i ≤ 1 := hheight
  have hrep : ∑ i, c i • (i.val.val - v.val) = x - v.val := by
    simpa only [b, c, simpleVertexBasis_apply] using b.sum_repr (x - v.val)
  have hsumx : ∑ i, c i • i.val.val = x - v.val + (∑ i, c i) • v.val := by
    calc
      _ = ∑ i, (c i • (i.val.val - v.val) + c i • v.val) := by
        apply Finset.sum_congr rfl
        intro i _
        module
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_smul, hrep]
  apply mem_convexHull_of_exists_fintype w z
  · intro o
    cases o with
    | none => exact sub_nonneg.mpr hsum
    | some i => exact hc i
  · simp only [Fintype.sum_option, w]
    ring
  · intro o
    cases o with
    | none => exact Set.mem_insert _ _
    | some i => exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
  · simp only [Fintype.sum_option, w, z]
    rw [hsumx]
    module

/-- The strict corner inequality follows from extremality, without an
extra general-position or nondegeneracy assumption. -/
theorem cornerHeight_gt_one_of_non_neighbor
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) {x : E d} (hx : x ∈ P.vertices)
    (hxv : x ≠ v.val) (hnot : ¬GeneralVertexStep P v.val x) :
    1 < cornerHeight P hP v hs x := by
  by_contra h
  let S : Set (E d) := insert v.val (Set.range (fun u : NeighborIndex P v => u.val.val))
  have hS : S ⊆ (P.vertices : Set (E d)) := by
    rintro y (rfl | ⟨u, rfl⟩)
    · exact v.property
    · exact u.val.property
  have hxc : x ∈ convexHull ℝ S :=
    mem_corner_simplex_of_height_le_one P hP v hs x (vertex_mem_body P hx) (le_of_not_gt h)
  have hext : x ∈ (convexHull ℝ S).extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset (convexHull_mono hS)
      ⟨hxc, vertex_is_extreme P hx⟩
  have hxS : x ∈ S := extremePoints_convexHull_subset hext
  rcases hxS with h | ⟨u, rfl⟩
  · exact hxv h
  · exact hnot ((adj_iff_generalVertexStep P v u.val).mp u.property)

theorem cornerHeight_ge_one_of_ne
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) {x : E d} (hx : x ∈ P.vertices) (hxv : x ≠ v.val) :
    1 ≤ cornerHeight P hP v hs x := by
  by_cases hstep : GeneralVertexStep P v.val x
  · let u : NeighborIndex P v :=
      ⟨⟨x, hx⟩, (adj_iff_generalVertexStep P v ⟨x, hx⟩).mpr hstep⟩
    exact (cornerHeight_neighbor P hP v hs u).ge
  · exact (cornerHeight_gt_one_of_non_neighbor P hP v hs hx hxv hstep).le

theorem cornerHeight_eq_linear (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (x : E d) :
    cornerHeight P hP v hs x =
      (simpleVertexBasis P hP v hs).sumCoords x -
        (simpleVertexBasis P hP v hs).sumCoords v.val := by
  rw [← map_sub]
  change (∑ i, (simpleVertexBasis P hP v hs).repr (x - v.val) i) =
    ((simpleVertexBasis P hP v hs).repr (x - v.val)).sum (fun _ => id)
  exact (Finsupp.sum_fintype ((simpleVertexBasis P hP v hs).repr (x - v.val))
    (fun (_ : NeighborIndex P v) (r : ℝ) => r) (fun _ => rfl)).symm

theorem neighbor_mem_deletion (P : ConvexPolytope d) (v : VertexType P)
    (hne : (P.vertices.erase v.val).Nonempty) (u : NeighborIndex P v) :
    u.val.val ∈ (deleteVertex P v.val hne).toSet := by
  apply subset_convexHull ℝ _
  apply Finset.mem_erase.mpr
  have hstep := (adj_iff_generalVertexStep P v u.val).mp u.property
  exact ⟨hstep.2.1.symm, u.val.property⟩

/-- Deletion of a simple vertex is the literal geometric corner cut. -/
theorem deleteVertex_eq_height_halfspace
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hne : (P.vertices.erase v.val).Nonempty) :
    (deleteVertex P v.val hne).toSet =
      {x ∈ P.toSet | 1 ≤ cornerHeight P hP v hs x} := by
  let b := simpleVertexBasis P hP v hs
  let h : E d →L[ℝ] ℝ := b.sumCoords.toContinuousLinearMap
  have hformula (x : E d) : cornerHeight P hP v hs x = h x - h v.val :=
    cornerHeight_eq_linear P hP v hs x
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨vertexSubset_body_subset P _ hne (Finset.erase_subset _ _) hx, ?_⟩
    have hbound : ∀ y ∈ P.vertices.erase v.val, 1 + h v.val ≤ h y := by
      intro y hy
      have hc := cornerHeight_ge_one_of_ne P hP v hs
        (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)
      rw [hformula] at hc
      linarith
    have hc := Papers.Geometry.linear_lower_bound_on_convexHull
      (P.vertices.erase v.val : Set (E d)) h (1 + h v.val) hbound x hx
    rw [hformula]
    linarith
  · rintro x ⟨hxP, hxheight⟩
    by_contra hxQ
    obtain ⟨l, a, hbound, hax⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (P.vertices.erase v.val : Set (E d)))
      ((P.vertices.erase v.val).finite_toSet.isClosed_convexHull ℝ) hxQ
    have hav : a < l v.val := by
      by_contra hav
      have hpbound : ∀ y ∈ P.vertices, l y ≤ a := by
        intro y hy
        by_cases hyv : y = v.val
        · simpa only [hyv] using (le_of_not_gt hav)
        · exact (hbound y (subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hyv, hy⟩))).le
      exact (not_lt_of_ge (le_su_toSet P l hpbound x hxP)) hax
    let c : NeighborIndex P v → ℝ := fun i => b.repr (x - v.val) i
    have hc : ∀ i, 0 ≤ c i := simpleVertexBasis_coordinates_nonneg P hP v hs x hxP
    have hlrep : l x - l v.val = ∑ i, c i * (l i.val.val - l v.val) := by
      rw [← map_sub, ← b.sum_repr (x - v.val), map_sum]
      simp only [map_smul, smul_eq_mul, b, simpleVertexBasis_apply, map_sub, c]
    have hsbound : (∑ i, c i * (l i.val.val - l v.val)) ≤
        (∑ i, c i) * (a - l v.val) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (sub_le_sub_right (hbound _ (neighbor_mem_deletion P v hne i)).le _) (hc i)
    have hsumge : 1 ≤ ∑ i, c i := hxheight
    have hprod := mul_le_mul_of_nonpos_right hsumge (sub_nonpos.mpr hav.le)
    rw [one_mul] at hprod
    linarith

end Papers.Polytopes

end
end
end BundlePart44

section BundlePart45
/- Source: Papers/SimpleDeletionDimension.lean -/



@[expose] public section

/-!
# Full dimension after deletion of a simple vertex

The strict vertex-count hypothesis provides a vertex outside the corner
simplex. A functional constant on the deletion is constant on every
neighbor, and the edge-basis expansion at that extra vertex forces its
common edge increment to vanish. The functional is therefore zero. This
proves full dimension without assuming that the deleted hull is a polytope
of the desired dimension.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def neighborVertices (P : ConvexPolytope d) (v : VertexType P) : Finset (E d) :=
  Finset.univ.image (fun u : NeighborIndex P v => u.val.val)

theorem neighborVertices_card (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) : (neighborVertices P v).card = d := by
  rw [neighborVertices, Finset.card_image_of_injective _
    (fun u w h => Subtype.ext (Subtype.ext h)), Finset.card_univ,
    card_neighbors_of_simple P hP v hs, finrank_euclideanSpace_fin]

theorem vertex_notMem_neighborVertices (P : ConvexPolytope d) (v : VertexType P) :
    v.val ∉ neighborVertices P v := by
  intro h
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
  exact ((adj_iff_generalVertexStep P v u.val).mp u.property).2.1 hu.symm

theorem exists_vertex_outside_corner (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card) :
    ∃ x ∈ P.vertices, x ≠ v.val ∧ ¬GeneralVertexStep P v.val x := by
  have hcount : (insert v.val (neighborVertices P v)).card < P.vertices.card := by
    rw [Finset.card_insert_of_notMem (vertex_notMem_neighborVertices P v),
      neighborVertices_card P hP v hs]
    exact hcard
  obtain ⟨x, hx, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcount
  have hxv : x ≠ v.val := by
    intro h
    apply hnot
    rw [h]
    exact Finset.mem_insert_self _ _
  refine ⟨x, hx, hxv, ?_⟩
  intro hstep
  apply hnot
  apply Finset.mem_insert_of_mem
  let u : NeighborIndex P v :=
    ⟨⟨x, hx⟩, (adj_iff_generalVertexStep P v ⟨x, hx⟩).mpr hstep⟩
  exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

theorem linearMap_eq_cornerHeight_mul
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (l : E d →ₗ[ℝ] ℝ) (c : ℝ)
    (hconst : ∀ u : NeighborIndex P v, l u.val.val = c) (x : E d) :
    l (x - v.val) = cornerHeight P hP v hs x * (c - l v.val) := by
  let b := simpleVertexBasis P hP v hs
  rw [← b.sum_repr (x - v.val), map_sum]
  simp only [map_smul, smul_eq_mul, b, simpleVertexBasis_apply, map_sub, hconst]
  rw [← Finset.sum_mul]
  simp only [cornerHeight, map_sub]

/-- The full-dimensionality assertion in Theorem 3, for every ambient
dimension and every simple vertex satisfying the paper's count hypothesis. -/
theorem deleteVertex_fullDim_of_simple
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) :
    (deleteVertex P v.val hne).IsFullDim := by
  obtain ⟨x, hx, hxv, hxnot⟩ := exists_vertex_outside_corner P hP v hs hcard
  let Q := deleteVertex P v.val hne
  let W := vectorSpan ℝ Q.toSet
  let b := simpleVertexBasis P hP v hs
  have hxQ : x ∈ Q.toSet :=
    subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hxv, hx⟩)
  have hheight := cornerHeight_gt_one_of_non_neighbor P hP v hs hx hxv hxnot
  have htop : W = ⊤ := by
    by_contra hW
    obtain ⟨z, hz⟩ : ∃ z : E d, z ∉ W := by
      by_contra h
      push_neg at h
      apply hW
      exact top_unique (fun z _ => h z)
    obtain ⟨g, hgz, hgW⟩ := Submodule.exists_le_ker_of_notMem hz
    let c := g x
    have hconst : ∀ y ∈ Q.toSet, g y = c := by
      intro y hy
      have hzero : g (y - x) = 0 := hgW (vsub_mem_vectorSpan ℝ hy hxQ)
      simpa only [map_sub, sub_eq_zero] using hzero
    have hneighbors : ∀ u : NeighborIndex P v, g u.val.val = c :=
      fun u => hconst _ (neighbor_mem_deletion P v hne u)
    have hline := linearMap_eq_cornerHeight_mul P hP v hs g c hneighbors x
    rw [map_sub] at hline
    have hproduct : (cornerHeight P hP v hs x - 1) * (c - g v.val) = 0 := by
      dsimp only [c] at *
      nlinarith [hline]
    have hzero : c - g v.val = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr (ne_of_gt hheight))
    have hbzero : ∀ u, g (b u) = 0 := by
      intro u
      rw [show b u = u.val.val - v.val from simpleVertexBasis_apply P hP v hs u,
        map_sub, hneighbors u, hzero]
    have h := congrArg g (b.sum_repr z)
    simp only [map_sum, map_smul, hbzero, smul_zero, Finset.sum_const_zero] at h
    exact hgz h.symm
  change finrank ℝ W = d
  rw [htop, finrank_top, finrank_euclideanSpace_fin]

theorem simpleDeletion_nonempty
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card) :
    (P.vertices.erase v.val).Nonempty := by
  obtain ⟨x, hx, hxv, _⟩ := exists_vertex_outside_corner P hP v hs hcard
  exact ⟨x, Finset.mem_erase.mpr ⟨hxv, hx⟩⟩

end Papers.Polytopes

end
end
end BundlePart45

section BundlePart46
/- Source: Papers/SimpleDeletionFacet.lean -/




@[expose] public section

/-!
# The new simplex facet after deleting a simple vertex

The new face is the convex hull of precisely the actual neighbors. Its
supporting equation and its dimension are derived from the edge basis.
No combinatorial truncation operation is assumed in the statement.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem neighborIndex_nonempty_of_vertex_count
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card) :
    Nonempty (NeighborIndex P v) := by
  rcases isEmpty_or_nonempty (NeighborIndex P v) with he | hn
  · letI := he
    obtain ⟨x, hx, hxv, hxnot⟩ := exists_vertex_outside_corner P hP v hs hcard
    have h := cornerHeight_gt_one_of_non_neighbor P hP v hs hx hxv hxnot
    simp [cornerHeight] at h
    linarith
  · exact hn

theorem neighborVertices_coe (P : ConvexPolytope d) (v : VertexType P) :
    (neighborVertices P v : Set (E d)) =
      Set.range (fun u : NeighborIndex P v => u.val.val) := by
  ext x
  simp [neighborVertices]

theorem simple_neighbors_affineIndependent
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) :
    AffineIndependent ℝ (fun u : NeighborIndex P v => u.val.val) := by
  have h := (simple_neighbor_directions_independent P hP v hs).affineIndependent
  convert h.vadd (v := v.val) using 1
  funext u
  change u.val.val = v.val + (u.val.val - v.val)
  abel

def deletionFacetSet (P : ConvexPolytope d) (v : VertexType P) : Set (E d) :=
  convexHull ℝ (neighborVertices P v : Set (E d))

theorem deletionFacetSet_dimension
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card) :
    faceDim (deletionFacetSet P v) + 1 = d := by
  letI := neighborIndex_nonempty_of_vertex_count P hP v hs hcard
  have h := (simple_neighbors_affineIndependent P hP v hs).finrank_vectorSpan_add_one
  rw [card_neighbors_of_simple P hP v hs, finrank_euclideanSpace_fin] at h
  change finrank ℝ (vectorSpan ℝ (convexHull ℝ _)) + 1 = d
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan,
    neighborVertices_coe]
  exact h

/-- The cut hyperplane exposes exactly the neighbor simplex in the actual
deleted convex hull. -/
theorem deletionFacetSet_isFace
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) :
    (deleteVertex P v.val hne).IsFace (deletionFacetSet P v) := by
  letI := neighborIndex_nonempty_of_vertex_count P hP v hs hcard
  let Q := deleteVertex P v.val hne
  let l : E d →L[ℝ] ℝ := (simpleVertexBasis P hP v hs).sumCoords.toContinuousLinearMap
  have hformula (x : E d) : cornerHeight P hP v hs x = l x - l v.val :=
    cornerHeight_eq_linear P hP v hs x
  have hbound : ∀ x ∈ Q.vertices, 1 + l v.val ≤ l x := by
    intro x hx
    have hh := cornerHeight_ge_one_of_ne P hP v hs
      (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
    rw [hformula] at hh
    linarith
  have hattained : ∃ x ∈ Q.vertices, l x = 1 + l v.val := by
    let u : NeighborIndex P v := Classical.choice inferInstance
    refine ⟨u.val.val, ?_, ?_⟩
    · exact Finset.mem_erase.mpr
        ⟨((adj_iff_generalVertexStep P v u.val).mp u.property).2.1.symm, u.val.property⟩
    · have h := cornerHeight_neighbor P hP v hs u
      rw [hformula] at h
      linarith
  have hF := minimumFace_isFace Q l (1 + l v.val) hbound hattained
  have hvertices : Q.vertices.filter (fun x => x ∈ minimumFace Q l (1 + l v.val)) =
      neighborVertices P v := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ, _, heq⟩ := Finset.mem_filter.mp hx
      have hxP : x ∈ P.vertices := Finset.mem_of_mem_erase hxQ
      have hxv : x ≠ v.val := Finset.ne_of_mem_erase hxQ
      have hstep : GeneralVertexStep P v.val x := by
        by_contra hnot
        have hgt := cornerHeight_gt_one_of_non_neighbor P hP v hs hxP hxv hnot
        rw [hformula, heq] at hgt
        linarith
      let u : NeighborIndex P v :=
        ⟨⟨x, hxP⟩, (adj_iff_generalVertexStep P v ⟨x, hxP⟩).mpr hstep⟩
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    · intro hx
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
      have huQ : u.val.val ∈ Q.vertices := Finset.mem_erase.mpr
        ⟨((adj_iff_generalVertexStep P v u.val).mp u.property).2.1.symm, u.val.property⟩
      refine Finset.mem_filter.mpr ⟨huQ, vertex_mem_body Q huQ, ?_⟩
      have h := cornerHeight_neighbor P hP v hs u
      rw [hformula] at h
      linarith
  have hset : minimumFace Q l (1 + l v.val) = deletionFacetSet P v := by
    rw [face_eq_hull_vertices Q hF, hvertices]
    rfl
  exact hset ▸ hF

end Papers.Polytopes

end
end
end BundlePart46

section BundlePart47
/- Source: Papers/SimpleDeletionFaces.lean -/



@[expose] public section

/-!
# The complete face dictionary for simple-vertex deletion

Every old face retains the convex hull of its remaining vertices. The only
other faces are the nonempty subsets of the neighbor simplex. This statement
uses actual exposed faces and actual vertices throughout; in particular, it
does not assume an abstract truncation or a combinatorial face dictionary.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem face_inter_subpolytope (P Q : ConvexPolytope d)
    (hQP : Q.toSet ⊆ P.toSet) {F : Set (E d)} (hF : P.IsFace F)
    (hne : (F ∩ Q.toSet).Nonempty) : Q.IsFace (F ∩ Q.toSet) := by
  obtain ⟨w, hwF, hwQ⟩ := hne
  obtain ⟨l, hl⟩ := hF.1 hF.2
  have hwmax : ∀ x ∈ P.toSet, l x ≤ l w := by
    have h : w ∈ P.toSet ∧ ∀ x ∈ P.toSet, l x ≤ l w := by
      have hw' := hwF
      rw [hl] at hw'
      exact hw'
    exact h.2
  refine ⟨?_, ⟨w, hwF, hwQ⟩⟩
  intro _
  refine ⟨l, ?_⟩
  ext x
  constructor
  · rintro ⟨hxF, hxQ⟩
    rw [hl] at hxF
    exact ⟨hxQ, fun y hy => hxF.2 y (hQP hy)⟩
  · rintro ⟨hxQ, hxmax⟩
    refine ⟨?_, hxQ⟩
    rw [hl]
    exact ⟨hQP hxQ, fun y hy => (hwmax y hy).trans (hxmax w hwQ)⟩

/-- An old nonempty face survives by erasing just the deleted vertex,
provided at least one of its vertices remains. -/
theorem old_face_after_vertex_deletion (P : ConvexPolytope d)
    (v : VertexType P) (hne : (P.vertices.erase v.val).Nonempty)
    {F : Set (E d)} (hF : P.IsFace F)
    (hremain : ((P.vertices.filter (· ∈ F)).erase v.val).Nonempty) :
    (deleteVertex P v.val hne).IsFace
      (convexHull ℝ (((P.vertices.filter (· ∈ F)).erase v.val : Finset (E d)) : Set (E d))) := by
  let Q := deleteVertex P v.val hne
  obtain ⟨w, hw⟩ := hremain
  obtain ⟨hwv, hw⟩ := Finset.mem_erase.mp hw
  obtain ⟨hwP, hwF⟩ := Finset.mem_filter.mp hw
  have hwQ : w ∈ Q.toSet :=
    vertex_mem_body Q (Finset.mem_erase.mpr ⟨hwv, hwP⟩)
  have h := face_inter_subpolytope P Q
    (vertexSubset_body_subset P _ hne (Finset.erase_subset _ _)) hF
    ⟨w, hwF, hwQ⟩
  have heq : F ∩ Q.toSet =
      convexHull ℝ (((P.vertices.filter (· ∈ F)).erase v.val : Finset (E d)) : Set (E d)) := by
    rw [face_eq_hull_vertices Q h]
    apply congrArg (convexHull ℝ)
    ext x
    simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff]
    change (x ∈ P.vertices.erase v.val ∧ x ∈ F ∧ x ∈ Q.toSet) ↔
      x ∈ (P.vertices.filter (· ∈ F)).erase v.val
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hxv, hxP⟩, hxF, _⟩
      exact ⟨hxv, hxP, hxF⟩
    · rintro ⟨hxv, hxP, hxF⟩
      exact ⟨⟨hxv, hxP⟩, hxF,
        vertex_mem_body Q (Finset.mem_erase.mpr ⟨hxv, hxP⟩)⟩
  exact heq ▸ h

/-- Every nonempty subset of the neighbor simplex is a genuine exposed
face of the deletion. The exposing functional comes from the edge basis. -/
theorem neighbor_subset_isFace
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty)
    (S : Finset (E d)) (hS : S.Nonempty) (hsub : S ⊆ neighborVertices P v) :
    (deleteVertex P v.val hne).IsFace (convexHull ℝ (S : Set (E d))) := by
  let b := simpleVertexBasis P hP v hs
  let l : E d →L[ℝ] ℝ :=
    (b.constr ℝ (fun u => if u.val.val ∈ S then (1 : ℝ) else 0)).toContinuousLinearMap
  have hvalue (u : NeighborIndex P v) :
      l u.val.val - l v.val = if u.val.val ∈ S then 1 else 0 := by
    rw [← map_sub, ← simpleVertexBasis_apply P hP v hs u]
    exact b.constr_basis ℝ _ u
  have hbound : ∀ x ∈ neighborVertices P v, l x ≤ l v.val + 1 := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    have h := hvalue u
    split_ifs at h <;> linarith
  have hiff : ∀ x ∈ neighborVertices P v,
      l x = l v.val + 1 ↔ x ∈ S := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    have h := hvalue u
    split_ifs at h with hu
    · exact ⟨fun _ => hu, fun _ => by linarith⟩
    · constructor
      · intro h'
        linarith
      · exact fun h' => (hu h').elim
  have hglobal : ∀ x ∈ deletionFacetSet P v, l x ≤ l v.val + 1 :=
    convexHull_min hbound (convex_halfSpace_le (LinearMap.isLinear l.toLinearMap) _)
  have hSconstant : ∀ x ∈ convexHull ℝ (S : Set (E d)), l x = l v.val + 1 := by
    apply convexHull_min ?_ (convex_hyperplane (LinearMap.isLinear l.toLinearMap) _)
    intro x hx
    exact (hiff x (hsub hx)).mpr hx
  have hST : convexHull ℝ (S : Set (E d)) ⊆ deletionFacetSet P v :=
    convexHull_mono hsub
  obtain ⟨w, hw⟩ := hS
  have hwHull : w ∈ convexHull ℝ (S : Set (E d)) := subset_convexHull ℝ _ hw
  have hex : IsExposed ℝ (deletionFacetSet P v) (convexHull ℝ (S : Set (E d))) := by
    intro _
    refine ⟨l, ?_⟩
    ext x
    constructor
    · intro hx
      refine ⟨hST hx, ?_⟩
      intro y hy
      rw [hSconstant x hx]
      exact hglobal y hy
    · rintro ⟨hxT, hxmax⟩
      have hxeq : l x = l v.val + 1 :=
        le_antisymm (hglobal x hxT) (by
          have h := hxmax w (hST hwHull)
          rw [hSconstant w hwHull] at h
          exact h)
      have hxHull := PlatoniciL3.faccia_argmax (neighborVertices P v) l hxT hxmax
      apply convexHull_mono (s := {y ∈ (neighborVertices P v : Set (E d)) | l y = l x}) ?_ hxHull
      rintro y ⟨hy, hyl⟩
      exact (hiff y hy).mp (hyl.trans hxeq)
  exact isFace_of_isExposed_isFace _
    (deletionFacetSet_isFace P hP v hs hcard hne) hex ⟨w, hwHull⟩

/-- A functional strictly larger at the removed corner cannot attain its
maximum over the deletion at an old nonneighbor. -/
theorem nonneighbor_strict_bound
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (l : E d →L[ℝ] ℝ) (M : ℝ)
    (hbound : ∀ u : NeighborIndex P v, l u.val.val ≤ M) (hv : M < l v.val)
    {x : E d} (hx : x ∈ P.vertices) (hxv : x ≠ v.val)
    (hnot : ¬GeneralVertexStep P v.val x) : l x < M := by
  let b := simpleVertexBasis P hP v hs
  let c : NeighborIndex P v → ℝ := fun i => b.repr (x - v.val) i
  have hc : ∀ i, 0 ≤ c i :=
    simpleVertexBasis_coordinates_nonneg P hP v hs x (vertex_mem_body P hx)
  have hrep : l x - l v.val = ∑ i, c i * (l i.val.val - l v.val) := by
    rw [← map_sub, ← b.sum_repr (x - v.val), map_sum]
    simp only [map_smul, smul_eq_mul, b, simpleVertexBasis_apply, map_sub, c]
  have hsbound : (∑ i, c i * (l i.val.val - l v.val)) ≤
      (∑ i, c i) * (M - l v.val) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hbound i) _) (hc i)
  have hsum : 1 < ∑ i, c i :=
    cornerHeight_gt_one_of_non_neighbor P hP v hs hx hxv hnot
  have hprod := mul_lt_mul_of_neg_right hsum (sub_neg.mpr hv)
  rw [one_mul] at hprod
  linarith

/-- The full geometric face dictionary. Neither branch assumes that the
candidate hull is a face of the deletion. -/
theorem simpleDeletion_face_iff
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) (F : Set (E d)) :
    (deleteVertex P v.val hne).IsFace F ↔
      (∃ G : Set (E d), P.IsFace G ∧
        ((P.vertices.filter (· ∈ G)).erase v.val).Nonempty ∧
        F = convexHull ℝ (((P.vertices.filter (· ∈ G)).erase v.val : Finset (E d)) : Set (E d))) ∨
      (∃ S : Finset (E d), S.Nonempty ∧ S ⊆ neighborVertices P v ∧
        F = convexHull ℝ (S : Set (E d))) := by
  let Q := deleteVertex P v.val hne
  constructor
  · intro hF
    obtain ⟨w, hw⟩ := (facePolytope Q hF).vertices_nonempty
    obtain ⟨hwQ, hwF⟩ := Finset.mem_filter.mp hw
    obtain ⟨l, hl⟩ := hF.1 hF.2
    have hwm : w ∈ Q.toSet ∧ ∀ x ∈ Q.toSet, l x ≤ l w := by
      have hw' := hwF
      rw [hl] at hw'
      exact hw'
    have hFiff (x : E d) (hx : x ∈ Q.toSet) : x ∈ F ↔ l x = l w := by
      rw [hl]
      constructor
      · rintro ⟨_, hxmax⟩
        exact le_antisymm (hwm.2 x hx) (hxmax w hwm.1)
      · intro heq
        exact ⟨hx, fun y hy => by rw [heq]; exact hwm.2 y hy⟩
    by_cases hv : l v.val ≤ l w
    · left
      let G := minimumFace P (-l) (-l w)
      have hG : P.IsFace G := by
        apply minimumFace_isFace
        · intro x hx
          change -l w ≤ -l x
          apply neg_le_neg
          by_cases hxv : x = v.val
          · simpa only [hxv] using hv
          · exact hwm.2 x (vertex_mem_body Q (Finset.mem_erase.mpr ⟨hxv, hx⟩))
        · exact ⟨w, Finset.mem_of_mem_erase hwQ, rfl⟩
      have hvertices : Q.vertices.filter (· ∈ F) = (P.vertices.filter (· ∈ G)).erase v.val := by
        ext x
        constructor
        · rintro hx
          obtain ⟨hxQ, hxF⟩ := Finset.mem_filter.mp hx
          refine Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hxQ,
            Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hxQ, ?_⟩⟩
          exact ⟨vertex_mem_body P (Finset.mem_of_mem_erase hxQ),
            congrArg Neg.neg ((hFiff x (vertex_mem_body Q hxQ)).mp hxF)⟩
        · intro hx
          obtain ⟨hxv, hx⟩ := Finset.mem_erase.mp hx
          obtain ⟨hxP, hxG⟩ := Finset.mem_filter.mp hx
          have hxQ : x ∈ Q.vertices := Finset.mem_erase.mpr ⟨hxv, hxP⟩
          refine Finset.mem_filter.mpr ⟨hxQ, (hFiff x (vertex_mem_body Q hxQ)).mpr ?_⟩
          exact neg_injective hxG.2
      refine ⟨G, hG, ?_, ?_⟩
      · rw [← hvertices]
        exact ⟨w, Finset.mem_filter.mpr ⟨hwQ, hwF⟩⟩
      · rw [face_eq_hull_vertices Q hF, hvertices]
    · right
      refine ⟨Q.vertices.filter (· ∈ F), ⟨w, Finset.mem_filter.mpr ⟨hwQ, hwF⟩⟩,
        ?_, face_eq_hull_vertices Q hF⟩
      intro x hx
      obtain ⟨hxQ, hxF⟩ := Finset.mem_filter.mp hx
      have hxP : x ∈ P.vertices := Finset.mem_of_mem_erase hxQ
      have hxv : x ≠ v.val := Finset.ne_of_mem_erase hxQ
      have hstep : GeneralVertexStep P v.val x := by
        by_contra hnot
        have hlt := nonneighbor_strict_bound P hP v hs l (l w)
          (fun u => hwm.2 _ (neighbor_mem_deletion P v hne u))
          (lt_of_not_ge hv) hxP hxv hnot
        rw [(hFiff x (vertex_mem_body Q hxQ)).mp hxF] at hlt
        exact lt_irrefl _ hlt
      let u : NeighborIndex P v :=
        ⟨⟨x, hxP⟩, (adj_iff_generalVertexStep P v ⟨x, hxP⟩).mpr hstep⟩
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  · rintro (⟨G, hG, hr, rfl⟩ | ⟨S, hS, hsub, rfl⟩)
    · exact old_face_after_vertex_deletion P v hne hG hr
    · exact neighbor_subset_isFace P hP v hs hcard hne S hS hsub

end Papers.Polytopes

end
end
end BundlePart47

section BundlePart48
/- Source: Papers/FaceVertexDictionary.lean -/



@[expose] public section

/-!
# Recovering the ordinary face order from vertex incidences

This is a geometric equivalence, derived from the convex-hull theorem for
actual faces. It is used to turn the simple-deletion face dictionary into
an order isomorphism, rather than weakening combinatorial equivalence to
an assumed list of incidences.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ}

theorem vertex_mem_hull_vertexSubset_iff (P : ConvexPolytope d)
    (S : Finset (E d)) (hsub : S ⊆ P.vertices) (v : VertexType P) :
    v.val ∈ convexHull ℝ (S : Set (E d)) ↔ v.val ∈ S := by
  constructor
  · intro hv
    have hext : v.val ∈ (convexHull ℝ (S : Set (E d))).extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset (convexHull_mono hsub)
        ⟨hv, vertex_is_extreme P v.property⟩
    exact extremePoints_convexHull_subset hext
  · exact fun hv => subset_convexHull ℝ (S : Set (E d)) hv

/-- Map a finite subset of actual vertices through an arbitrary vertex
bijection. Nonvertices in the input are deliberately irrelevant. -/
def mapVertexFinset (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q) (S : Finset (E d)) : Finset (E e) :=
  (Finset.univ.filter (fun v : VertexType P => v.val ∈ S)).image (fun v => (b v).val)

theorem mapVertexFinset_mem_iff (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q) (S : Finset (E d)) (v : VertexType P) :
    (b v).val ∈ mapVertexFinset P Q b S ↔ v.val ∈ S := by
  simp only [mapVertexFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, heq⟩
    have h : w = v := b.injective (Subtype.ext heq)
    simpa only [h] using hw
  · exact fun h => ⟨v, h, rfl⟩

theorem mapVertexFinset_subset (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q) (S : Finset (E d)) :
    mapVertexFinset P Q b S ⊆ Q.vertices := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact (b v).property

theorem mapVertexFinset_nonempty (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q) (S : Finset (E d))
    (hS : S.Nonempty) (hsub : S ⊆ P.vertices) :
    (mapVertexFinset P Q b S).Nonempty := by
  obtain ⟨v, hv⟩ := hS
  exact ⟨(b ⟨v, hsub hv⟩).val, (mapVertexFinset_mem_iff P Q b S ⟨v, hsub hv⟩).mpr hv⟩

theorem face_le_iff_vertex_incidence (P : ConvexPolytope d) (F G : FaceType P) :
    F ≤ G ↔ ∀ v : VertexType P, v.val ∈ F.val → v.val ∈ G.val := by
  constructor
  · exact fun h v hv => h hv
  · intro h
    change F.val ⊆ G.val
    rw [face_eq_hull_vertices P F.property]
    apply convexHull_min ?_ (G.property.1.convex (convex_convexHull ℝ _))
    intro x hx
    obtain ⟨hxP, hxF⟩ := Finset.mem_filter.mp hx
    exact h ⟨x, hxP⟩ hxF

theorem face_eq_of_vertex_incidence (P : ConvexPolytope d) (F G : FaceType P)
    (h : ∀ v : VertexType P, v.val ∈ F.val ↔ v.val ∈ G.val) : F = G := by
  apply le_antisymm
  · exact (face_le_iff_vertex_incidence P F G).mpr (fun v => (h v).mp)
  · exact (face_le_iff_vertex_incidence P G F).mpr (fun v => (h v).mpr)

/-- A bijection preserving exactly the full families of actual face-vertex
sets induces an ordinary face-poset order isomorphism. Both coverage
directions are required. -/
def faceOrderIsoOfVertexIncidence (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q)
    (hforward : ∀ F : FaceType P, ∃ G : FaceType Q,
      ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val)
    (hbackward : ∀ G : FaceType Q, ∃ F : FaceType P,
      ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val) :
    FaceType P ≃o FaceType Q := by
  let f : FaceType P → FaceType Q := fun F => Classical.choose (hforward F)
  let g : FaceType Q → FaceType P := fun G => Classical.choose (hbackward G)
  have hf (F : FaceType P) (v : VertexType P) :
      (b v).val ∈ (f F).val ↔ v.val ∈ F.val :=
    Classical.choose_spec (hforward F) v
  have hg (G : FaceType Q) (v : VertexType P) :
      (b v).val ∈ G.val ↔ v.val ∈ (g G).val :=
    Classical.choose_spec (hbackward G) v
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · intro F
    apply face_eq_of_vertex_incidence P
    intro v
    exact (hg (f F) v).symm.trans (hf F v)
  · intro G
    apply face_eq_of_vertex_incidence Q
    intro w
    obtain ⟨v, rfl⟩ := b.surjective w
    exact (hf (g G) v).trans (hg G v).symm
  · intro F G
    rw [face_le_iff_vertex_incidence Q, face_le_iff_vertex_incidence P]
    constructor
    · intro h v hv
      exact (hf G v).mp (h (b v) ((hf F v).mpr hv))
    · intro h w hw
      obtain ⟨v, rfl⟩ := b.surjective w
      exact (hf G v).mpr (h v ((hf F v).mp hw))

theorem imageVertex_adj_iff {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (u v : VertexType P) :
    (polytopeGraph Q).Adj (imageVertex φ u) (imageVertex φ v) ↔
      (polytopeGraph P).Adj u v := by
  constructor
  · rintro ⟨hne, F, hF, hdim, huF, hvF⟩
    let G : FaceType P := φ.symm ⟨F, hF⟩
    have hφG : φ G = ⟨F, hF⟩ := φ.apply_symm_apply _
    refine ⟨fun h => hne (congrArg (imageVertex φ) h), G.val, G.property, ?_, ?_, ?_⟩
    · have h := faceOrderIso_dimension φ G
      rw [hφG] at h
      exact h.symm.trans hdim
    · apply (imageVertex_mem_iff φ u G).mp
      simpa only [hφG] using huF
    · apply (imageVertex_mem_iff φ v G).mp
      simpa only [hφG] using hvF
  · rintro ⟨hne, F, hF, hdim, huF, hvF⟩
    let G : FaceType P := ⟨F, hF⟩
    refine ⟨fun h => hne ((vertexEquivOfFaceOrder φ).injective h),
      (φ G).val, (φ G).property, ?_, ?_, ?_⟩
    · exact (faceOrderIso_dimension φ G).trans hdim
    · exact (imageVertex_mem_iff φ u G).mpr huF
    · exact (imageVertex_mem_iff φ v G).mpr hvF

/-- Edge adjacency, and hence the actual neighbor set of a deleted simple
vertex, is determined by the face order. -/
def vertexGraphIsoOfFaceOrder {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : polytopeGraph P ≃g polytopeGraph Q where
  toEquiv := vertexEquivOfFaceOrder φ
  map_rel_iff' := by
    intro u v
    exact imageVertex_adj_iff φ u v

end Papers.Polytopes

end
end
end BundlePart48

section BundlePart49
/- Source: Papers/SimpleDeletionIntrinsic.lean -/




@[expose] public section

/-!
# The intrinsic combinatorial type of simple-vertex deletion

The bijection on remaining vertices is induced by the original ordinary
face-order isomorphism. The complete geometric face dictionary supplies
both directions of face coverage; the vertex-incidence theorem then
constructs the required ordinary face-order isomorphism.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem mem_neighborVertices_iff_adj (P : ConvexPolytope d)
    (v u : VertexType P) :
    u.val ∈ neighborVertices P v ↔ (polytopeGraph P).Adj v u := by
  constructor
  · intro hu
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hu
    have heq : w.val = u := Subtype.ext hw
    exact heq ▸ w.property
  · intro hu
    exact Finset.mem_image.mpr ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩

def deleteVertexEquiv {P Q : ConvexPolytope d}
    (b : VertexType P ≃ VertexType Q) (v : VertexType P) (w : VertexType Q)
    (hb : b v = w) (hneP : (P.vertices.erase v.val).Nonempty)
    (hneQ : (Q.vertices.erase w.val).Nonempty) :
    VertexType (deleteVertex P v.val hneP) ≃ VertexType (deleteVertex Q w.val hneQ) where
  toFun x := ⟨(b ⟨x.val, Finset.mem_of_mem_erase x.property⟩).val,
    Finset.mem_erase.mpr ⟨by
      intro heq
      have h : b ⟨x.val, Finset.mem_of_mem_erase x.property⟩ = b v :=
        (Subtype.ext heq).trans hb.symm
      exact (Finset.ne_of_mem_erase x.property) (congrArg Subtype.val (b.injective h)),
      (b ⟨x.val, Finset.mem_of_mem_erase x.property⟩).property⟩⟩
  invFun y := ⟨(b.symm ⟨y.val, Finset.mem_of_mem_erase y.property⟩).val,
    Finset.mem_erase.mpr ⟨by
      intro heq
      have h : b.symm ⟨y.val, Finset.mem_of_mem_erase y.property⟩ = v := Subtype.ext heq
      have h' := congrArg b h
      rw [b.apply_symm_apply, hb] at h'
      exact (Finset.ne_of_mem_erase y.property) (congrArg Subtype.val h'),
      (b.symm ⟨y.val, Finset.mem_of_mem_erase y.property⟩).property⟩⟩
  left_inv x := by
    apply Subtype.ext
    change (b.symm (b ⟨x.val, Finset.mem_of_mem_erase x.property⟩)).val = x.val
    rw [b.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    change (b (b.symm ⟨y.val, Finset.mem_of_mem_erase y.property⟩)).val = y.val
    rw [b.apply_symm_apply]

@[simp] theorem deleteVertexEquiv_apply_val {P Q : ConvexPolytope d}
    (b : VertexType P ≃ VertexType Q) (v : VertexType P) (w : VertexType Q)
    (hb : b v = w) (hneP : (P.vertices.erase v.val).Nonempty)
    (hneQ : (Q.vertices.erase w.val).Nonempty)
    (x : VertexType (deleteVertex P v.val hneP)) :
    (deleteVertexEquiv b v w hb hneP hneQ x).val =
      (b ⟨x.val, Finset.mem_of_mem_erase x.property⟩).val := rfl

theorem deleteVertexEquiv_inverse {P Q : ConvexPolytope d}
    (b : VertexType P ≃ VertexType Q) (v : VertexType P) (w : VertexType Q)
    (hb : b v = w) (hb' : b.symm w = v)
    (hneP : (P.vertices.erase v.val).Nonempty)
    (hneQ : (Q.vertices.erase w.val).Nonempty)
    (x : VertexType (deleteVertex P v.val hneP)) :
    deleteVertexEquiv b.symm w v hb' hneQ hneP
      (deleteVertexEquiv b v w hb hneP hneQ x) = x := by
  apply Subtype.ext
  change (b.symm (b ⟨x.val, Finset.mem_of_mem_erase x.property⟩)).val = x.val
  rw [b.symm_apply_apply]

theorem isSimple_imageVertex {P Q : ConvexPolytope d}
    (φ : FaceType P ≃o FaceType Q) (v : VertexType P)
    (hs : IsSimpleVertex P v) : IsSimpleVertex Q (imageVertex φ v) := by
  change (polytopeGraph Q).degree ((vertexGraphIsoOfFaceOrder φ) v) = Q.dim
  rw [(vertexGraphIsoOfFaceOrder φ).degree_eq, faceOrderIso_polytope_dim φ]
  exact hs

theorem vertex_mem_remaining_face_hull_iff (P : ConvexPolytope d)
    (v x : VertexType P) (hxv : x ≠ v) (G : Set (E d)) :
    x.val ∈ convexHull ℝ
      (((P.vertices.filter (· ∈ G)).erase v.val : Finset (E d)) : Set (E d)) ↔ x.val ∈ G := by
  rw [vertex_mem_hull_vertexSubset_iff P _
    (fun _ h => (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).1) x]
  have hxne : x.val ≠ v.val := fun h => hxv (Subtype.ext h)
  constructor
  · intro h
    exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).2
  · intro hxG
    exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_filter.mpr ⟨x.property, hxG⟩⟩

theorem deletion_face_forward {P Q : ConvexPolytope d}
    (φ : FaceType P ≃o FaceType Q) (hP : P.IsFullDim)
    (v : VertexType P) (w : VertexType Q) (hvw : imageVertex φ v = w)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hneP : (P.vertices.erase v.val).Nonempty)
    (hneQ : (Q.vertices.erase w.val).Nonempty)
    (F : FaceType (deleteVertex P v.val hneP)) :
    ∃ G : FaceType (deleteVertex Q w.val hneQ),
      ∀ x : VertexType (deleteVertex P v.val hneP),
        (deleteVertexEquiv (vertexEquivOfFaceOrder φ) v w hvw hneP hneQ x).val ∈ G.val ↔
          x.val ∈ F.val := by
  let b := vertexEquivOfFaceOrder φ
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  have hsQ : IsSimpleVertex Q w := hvw ▸ isSimple_imageVertex φ v hs
  have hcardQ : d + 1 < Q.vertices.card := by
    rw [← faceOrderIso_vertex_card φ]
    exact hcard
  rcases (simpleDeletion_face_iff P hP v hs hcard hneP F.val).mp F.property with
    ⟨H, hH, hremain, hF⟩ | ⟨S, hS, hsub, hF⟩
  · let H' : FaceType Q := φ ⟨H, hH⟩
    have hremainQ : ((Q.vertices.filter (· ∈ H'.val)).erase w.val).Nonempty := by
      obtain ⟨x, hx⟩ := hremain
      obtain ⟨hxv, hx⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxP, hxH⟩ := Finset.mem_filter.mp hx
      let u : VertexType P := ⟨x, hxP⟩
      refine ⟨(b u).val, Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨(b u).property, ?_⟩⟩⟩
      · intro heq
        have h : b u = b v := (Subtype.ext heq).trans hvw.symm
        exact hxv (congrArg Subtype.val (b.injective h))
      · exact (imageVertex_mem_iff φ u ⟨H, hH⟩).mpr hxH
    let G : FaceType (deleteVertex Q w.val hneQ) :=
      ⟨_, old_face_after_vertex_deletion Q w hneQ H'.property hremainQ⟩
    refine ⟨G, ?_⟩
    intro x
    let u : VertexType P := ⟨x.val, Finset.mem_of_mem_erase x.property⟩
    have huv : u ≠ v := fun h => (Finset.ne_of_mem_erase x.property) (congrArg Subtype.val h)
    have hbu : b u ≠ w := by
      intro h
      exact huv (b.injective (h.trans hvw.symm))
    change (b u).val ∈ G.val ↔ u.val ∈ F.val
    rw [hF]
    change (b u).val ∈ convexHull ℝ
      (((Q.vertices.filter (· ∈ H'.val)).erase w.val : Finset (E d)) : Set (E d)) ↔ _
    rw [vertex_mem_remaining_face_hull_iff Q w (b u) hbu H'.val,
      vertex_mem_remaining_face_hull_iff P v u huv H]
    exact imageVertex_mem_iff φ u ⟨H, hH⟩
  · let S' := mapVertexFinset P Q b S
    have hSvertices : S ⊆ P.vertices := by
      intro x hx
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (hsub hx)
      exact u.val.property
    have hS' : S'.Nonempty := mapVertexFinset_nonempty P Q b S hS hSvertices
    have hsub' : S' ⊆ neighborVertices Q w := by
      intro y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
      have huS : u.val ∈ S := (Finset.mem_filter.mp hu).2
      have hadj := (mem_neighborVertices_iff_adj P v u).mp (hsub huS)
      apply (mem_neighborVertices_iff_adj Q w (b u)).mpr
      rw [← hvw]
      exact (imageVertex_adj_iff φ v u).mpr hadj
    let G : FaceType (deleteVertex Q w.val hneQ) :=
      ⟨_, neighbor_subset_isFace Q hQ w hsQ hcardQ hneQ S' hS' hsub'⟩
    refine ⟨G, ?_⟩
    intro x
    let u : VertexType P := ⟨x.val, Finset.mem_of_mem_erase x.property⟩
    change (b u).val ∈ convexHull ℝ (S' : Set (E d)) ↔ u.val ∈ F.val
    rw [hF, vertex_mem_hull_vertexSubset_iff Q S' (mapVertexFinset_subset P Q b S) (b u),
      vertex_mem_hull_vertexSubset_iff P S hSvertices u]
    exact mapVertexFinset_mem_iff P Q b S u

/-- Simple-vertex deletion has a combinatorially determined face poset.
The input is the ordinary original face-order isomorphism, with no
additional rank, incidence, or deletion-compatibility hypothesis. -/
theorem simpleDeletion_combinatoriallyEquivalent
    {P Q : ConvexPolytope d} (φ : FaceType P ≃o FaceType Q)
    (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hneP : (P.vertices.erase v.val).Nonempty)
    (hneQ : (Q.vertices.erase (imageVertex φ v).val).Nonempty) :
    CombinatoriallyEquivalent (deleteVertex P v.val hneP)
      (deleteVertex Q (imageVertex φ v).val hneQ) := by
  let w := imageVertex φ v
  let b := vertexEquivOfFaceOrder φ
  let b' := deleteVertexEquiv b v w rfl hneP hneQ
  have hbback : imageVertex φ.symm w = v := b.symm_apply_apply v
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  have hsQ : IsSimpleVertex Q w := isSimple_imageVertex φ v hs
  have hcardQ : d + 1 < Q.vertices.card := by
    rw [← faceOrderIso_vertex_card φ]
    exact hcard
  refine ⟨faceOrderIsoOfVertexIncidence _ _ b'
    (deletion_face_forward φ hP v w rfl hs hcard hneP hneQ) ?_⟩
  intro G
  obtain ⟨F, hF⟩ := deletion_face_forward φ.symm hQ w v hbback hsQ hcardQ hneQ hneP G
  refine ⟨F, ?_⟩
  intro x
  have h := (hF (b' x)).symm
  have heq : deleteVertexEquiv (vertexEquivOfFaceOrder φ.symm) w v hbback hneQ hneP (b' x) = x := by
    apply Subtype.ext
    change (b.symm (b ⟨x.val, Finset.mem_of_mem_erase x.property⟩)).val = x.val
    rw [b.symm_apply_apply]
  simpa only [heq] using h

/-- The geometric and combinatorial clauses of the deletion theorem,
including the existence of a nonempty, full-dimensional deleted hull. -/
theorem simpleDeletion_geometry
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card) :
    ∃ hne : (P.vertices.erase v.val).Nonempty,
      (deleteVertex P v.val hne).IsFullDim ∧
      ∀ (Q : ConvexPolytope d) (φ : FaceType P ≃o FaceType Q)
          (hneQ : (Q.vertices.erase (imageVertex φ v).val).Nonempty),
        CombinatoriallyEquivalent (deleteVertex P v.val hne)
          (deleteVertex Q (imageVertex φ v).val hneQ) := by
  let hne := simpleDeletion_nonempty P hP v hs hcard
  exact ⟨hne, deleteVertex_fullDim_of_simple P hP v hs hcard hne,
    fun _ φ hneQ => simpleDeletion_combinatoriallyEquivalent φ hP v hs hcard hne hneQ⟩

/-- Deletion carries every realization over K to a realization of the
intrinsic deleted type over the same K. The reverse implication requires
the separate restoration theorem. -/
theorem RealizableOver.delete_of_simple
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) (K : Subfield ℝ)
    (hPK : RealizableOver P K) : RealizableOver (deleteVertex P v.val hne) K := by
  obtain ⟨Q, ⟨φ⟩, hQK⟩ := hPK
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  have hsQ : IsSimpleVertex Q (imageVertex φ v) := isSimple_imageVertex φ v hs
  have hcardQ : d + 1 < Q.vertices.card := by
    rw [← faceOrderIso_vertex_card φ]
    exact hcard
  let hneQ := simpleDeletion_nonempty Q hQ (imageVertex φ v) hsQ hcardQ
  exact ⟨deleteVertex Q (imageVertex φ v).val hneQ,
    simpleDeletion_combinatoriallyEquivalent φ hP v hs hcard hne hneQ,
    deleteVertex_coordinates Q K hQK (imageVertex φ v).val hneQ⟩

end Papers.Polytopes

end
end
end BundlePart49


#print axioms Papers.Polytopes.simpleDeletion_geometry
