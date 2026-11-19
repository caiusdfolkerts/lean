module

public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Strict.Extreme
public import Mathlib.Analysis.InnerProductSpace.Affine
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Logic.Relation
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Interval.Set.Monotone
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Tauto
@[expose] public section

noncomputable section

/-!
# Consolidated verification sources

Generated only to avoid repeatedly loading the same pinned Mathlib files.
Public theorem statements and proofs preserve their original content.
See FoundationBundle.sources.json for exact source ranges, hashes, and private
helper alpha-renamings, topological source order, and scope adjustments.
-/

/- Original source: Cubical/Polytope/Imports.lean -/
section VerificationSource000
























end VerificationSource000

/- Original source: Cubical/Polytope/Definitions.lean -/
section VerificationSource001
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module ChallengeDeps.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/


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
end VerificationSource001

/- Original source: Cubical/Polytope/FacciaArgmax.lean -/
section VerificationSource002
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.FacciaArgmax.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/


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
end VerificationSource002

/- Original source: Cubical/Polytope/PerturbazioneFinita.lean -/
section VerificationSource003
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.PerturbazioneFinita.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




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
end VerificationSource003

/- Original source: Cubical/Polytope/SottoPolitopo.lean -/
section VerificationSource004
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.SottoPolitopo.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




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
end VerificationSource004

/- Original source: Cubical/Polytope/Faces.lean -/
section VerificationSource005


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
end VerificationSource005

/- Original source: Papers/FiniteHullCertificates.lean -/
section VerificationSource006






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
end VerificationSource006

/- Original source: Cubical/Polytope/VerticiEsposti.lean -/
section VerificationSource007
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.VerticiEsposti.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




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
end LeanEval.Geometry.PlatonicClassification
end
end VerificationSource007

/- Original source: Cubical/Polytope/DimStretta.lean -/
section VerificationSource008
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.DimStretta.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/





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
end VerificationSource008

/- Original source: Cubical/Polytope/DueFunzionali.lean -/
section VerificationSource009
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.DueFunzionali.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/



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
end LeanEval.Geometry.PlatonicClassification
end
end VerificationSource009

/- Original source: Cubical/Polytope/Perno.lean -/
section VerificationSource010
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Perno.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/






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
end VerificationSource010

/- Original source: Cubical/Polytope/Interpolazione.lean -/
section VerificationSource011
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Interpolazione.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/









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
end VerificationSource011

/- Original source: Cubical/Polytope/ScalaBandiere.lean -/
section VerificationSource012
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ScalaBandiere.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/








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
end VerificationSource012

/- Original source: Cubical/Polytope/BandieraCompagna.lean -/
section VerificationSource013
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.BandieraCompagna.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/









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
end VerificationSource013

/- Original source: Cubical/Polytope/BandieraVertice.lean -/
section VerificationSource014
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.BandieraVertice.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/










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
end VerificationSource014

/- Original source: Cubical/Polytope/Diamante.lean -/
section VerificationSource015
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Diamante.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/





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
end VerificationSource015

/- Original source: Cubical/Polytope/Diamante2D.lean -/
section VerificationSource016
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Diamante2D.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/






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
end VerificationSource016

/- Original source: Cubical/Polytope/SecondoSpigolo.lean -/
section VerificationSource017
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.SecondoSpigolo.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/









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
end VerificationSource017

/- Original source: Cubical/Polytope/ConoVertice.lean -/
section VerificationSource018
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ConoVertice.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/









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
end VerificationSource018

/- Original source: Cubical/Polytope/DueVertici.lean -/
section VerificationSource019
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.DueVertici.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




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
end VerificationSource019

/- Original source: Cubical/Polytope/Graph.lean -/
section VerificationSource020




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
end VerificationSource020

/- Original source: CubicalIndecomposability/LabelledFaces.lean -/
section VerificationSource021





/-!
# Exposed faces from finite support certificates

All sets in this file are ordinary exposed subsets of a real convex hull.
Finite vertex masks are only names for those subsets.  The correspondence
between inclusion of masks and inclusion of geometric faces is proved here.
-/

noncomputable section

namespace CubicalIndecomposability

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

variable {n : ℕ} {V I : Type*} [Fintype V] [DecidableEq V]

/-- Supporting equalities can be combined by addition: nonnegative slacks
cannot cancel. -/
theorem sum_support_eq_iff (P : ConvexPolytope n)
    (l : I → E n →L[ℝ] ℝ) (c : I → ℝ) (rows : Finset I)
    (hbound : ∀ i, ∀ x ∈ P.vertices, c i ≤ l i x)
    (x : E n) (hx : x ∈ P.vertices) :
    (∑ i ∈ rows, l i x) = (∑ i ∈ rows, c i) ↔
      ∀ i ∈ rows, l i x = c i := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _hi => sub_nonneg.mpr (hbound i x hx))]
  simp only [sub_eq_zero]

/-- The face cut out by a finite collection of supporting equalities. -/
def supportIntersection (P : ConvexPolytope n)
    (l : I → E n →L[ℝ] ℝ) (c : I → ℝ) (rows : Finset I) : Set (E n) :=
  minimumFace P (∑ i ∈ rows, l i) (∑ i ∈ rows, c i)

theorem supportIntersection_isFace (P : ConvexPolytope n)
    (l : I → E n →L[ℝ] ℝ) (c : I → ℝ) (rows : Finset I)
    (hbound : ∀ i, ∀ x ∈ P.vertices, c i ≤ l i x)
    (hattained : ∃ x ∈ P.vertices, ∀ i ∈ rows, l i x = c i) :
    P.IsFace (supportIntersection P l c rows) := by
  apply minimumFace_isFace
  · intro x hx
    simp only [ContinuousLinearMap.sum_apply]
    exact Finset.sum_le_sum fun i hi => hbound i x hx
  · obtain ⟨x, hx, h⟩ := hattained
    refine ⟨x, hx, ?_⟩
    simp only [ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl h

theorem vertex_mem_supportIntersection (P : ConvexPolytope n)
    (l : I → E n →L[ℝ] ℝ) (c : I → ℝ) (rows : Finset I)
    (hbound : ∀ i, ∀ x ∈ P.vertices, c i ≤ l i x)
    (x : E n) (hx : x ∈ P.vertices) :
    x ∈ supportIntersection P l c rows ↔ ∀ i ∈ rows, l i x = c i := by
  change (x ∈ P.toSet ∧ _) ↔ _
  have hxbody : x ∈ P.toSet := subset_convexHull ℝ _ hx
  rw [and_iff_right hxbody]
  simp only [ContinuousLinearMap.sum_apply]
  exact sum_support_eq_iff P l c rows hbound x hx

/-- A labelled face is exactly the hull of its labelled vertices. -/
theorem face_eq_label_hull (P : ConvexPolytope n) (p : V → E n)
    (hp : P.vertices = Finset.univ.image p)
    {F : Set (E n)} (hF : P.IsFace F) (s : Finset V)
    (hs : ∀ v, p v ∈ F ↔ v ∈ s) :
    F = convexHull ℝ (p '' (s : Set V)) := by
  classical
  rw [face_eq_hull_vertices P hF]
  congr 1
  ext x
  simp only [Finset.mem_coe, Finset.mem_filter, hp,
    Finset.mem_image, Finset.mem_univ, true_and, Set.mem_image]
  constructor
  · rintro ⟨⟨v, rfl⟩, hv⟩
    exact ⟨v, (hs v).mp hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, (hs v).mpr hv⟩

/-- Exact vertex labels reflect geometric face inclusion. -/
theorem face_subset_iff_labels (P : ConvexPolytope n) (p : V → E n)
    (hp : P.vertices = Finset.univ.image p)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (s t : Finset V) (hs : ∀ v, p v ∈ F ↔ v ∈ s)
    (ht : ∀ v, p v ∈ G ↔ v ∈ t) :
    F ⊆ G ↔ s ⊆ t := by
  constructor
  · intro h v hv
    exact (ht v).mp (h ((hs v).mpr hv))
  · intro h
    rw [face_eq_label_hull P p hp hF s hs,
      face_eq_label_hull P p hp hG t ht]
    exact convexHull_mono (Set.image_mono h)

theorem face_eq_iff_labels (P : ConvexPolytope n) (p : V → E n)
    (hp : P.vertices = Finset.univ.image p)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (s t : Finset V) (hs : ∀ v, p v ∈ F ↔ v ∈ s)
    (ht : ∀ v, p v ∈ G ↔ v ∈ t) :
    F = G ↔ s = t := by
  constructor
  · intro h
    apply Finset.Subset.antisymm
    · exact (face_subset_iff_labels P p hp hF hG s t hs ht).mp h.le
    · exact (face_subset_iff_labels P p hp hG hF t s ht hs).mp h.ge
  · intro h
    apply Set.Subset.antisymm
    · exact (face_subset_iff_labels P p hp hF hG s t hs ht).mpr h.le
    · exact (face_subset_iff_labels P p hp hG hF t s ht hs).mpr h.ge

theorem face_ssubset_iff_labels (P : ConvexPolytope n) (p : V → E n)
    (hp : P.vertices = Finset.univ.image p)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (s t : Finset V) (hs : ∀ v, p v ∈ F ↔ v ∈ s)
    (ht : ∀ v, p v ∈ G ↔ v ∈ t) :
    F ⊂ G ↔ s ⊂ t := by
  rw [ssubset_iff_subset_ne, Finset.ssubset_iff_subset_ne]
  exact and_congr (face_subset_iff_labels P p hp hF hG s t hs ht)
    (not_congr (face_eq_iff_labels P p hp hF hG s t hs ht))

/-- Five strictly nested nonempty faces in four-space must have dimensions
zero, one, two, three and four.  Thus incidence flags suffice to certify
dimensions without introducing a numerical rank assertion. -/
theorem dimension_of_five_face_flag (P : ConvexPolytope 4)
    (F : Fin 5 → Set (E 4)) (hF : ∀ i, P.IsFace (F i))
    (h01 : F 0 ⊂ F 1) (h12 : F 1 ⊂ F 2)
    (h23 : F 2 ⊂ F 3) (h34 : F 3 ⊂ F 4) :
    ∀ i : Fin 5, faceDim (F i) = (i : ℕ) := by
  have hd01 := faceDim_lt_of_ssubset P (hF 0) (hF 1) h01
  have hd12 := faceDim_lt_of_ssubset P (hF 1) (hF 2) h12
  have hd23 := faceDim_lt_of_ssubset P (hF 2) (hF 3) h23
  have hd34 := faceDim_lt_of_ssubset P (hF 3) (hF 4) h34
  have htop : faceDim (F 4) ≤ 4 := by
    change Module.finrank ℝ (vectorSpan ℝ (F 4)) ≤ 4
    have h := Submodule.finrank_le (vectorSpan ℝ (F 4))
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using h
  intro i
  fin_cases i
  · change faceDim (F 0) = 0
    omega
  · change faceDim (F 1) = 1
    omega
  · change faceDim (F 2) = 2
    omega
  · change faceDim (F 3) = 3
    omega
  · change faceDim (F 4) = 4
    omega

end CubicalIndecomposability
end
end VerificationSource021

/- Original source: Cubical/Polytope/FacciaIntermedia.lean -/
section VerificationSource022
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.FacciaIntermedia.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/







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
end VerificationSource022

/- Original source: Cubical/Polytope/DiamanteRelativo.lean -/
section VerificationSource023
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.DiamanteRelativo.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




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
end VerificationSource023

/- Original source: Cubical/Polytope/SecondoIntermedio.lean -/
section VerificationSource024
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.SecondoIntermedio.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/





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
end VerificationSource024

/- Original source: Cubical/Polytope/FlagAdiacente.lean -/
section VerificationSource025
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.FlagAdiacente.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/








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
end VerificationSource025

/- Original source: Cubical/Polytope/AdiacenzaUnica.lean -/
section VerificationSource026
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.AdiacenzaUnica.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/








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
end VerificationSource026

/- Original source: Cubical/Polytope/MossaInvolutiva.lean -/
section VerificationSource027
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.MossaInvolutiva.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/





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
end VerificationSource027

/- Original source: Cubical/Polytope/Equivarianza.lean -/
section VerificationSource028
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Equivarianza.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/






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
end VerificationSource028

/- Original source: Cubical/Polytope/Gallerie.lean -/
section VerificationSource029
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Gallerie.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/







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
end VerificationSource029

/- Original source: Cubical/Polytope/Connettivita.lean -/
section VerificationSource030
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Connettivita.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/








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
end VerificationSource030

/- Original source: Cubical/Polytope/ConnettivitaGlobale.lean -/
section VerificationSource031
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ConnettivitaGlobale.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




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
end VerificationSource031

/- Original source: Cubical/Polytope/FaceOrder.lean -/
section VerificationSource032




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
end VerificationSource032

/- Original source: Cubical/Polytope/Ortoplesse.lean -/
section VerificationSource033
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Ortoplesse.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




/-!
L'ortoplesse in dimensione arbitraria: i vertici sono `±eᵢ`.
La parte costruttiva fino a `verticiOrto_eq_extremePoints` riprende
`BOZZA_Ortoplesse.lean` (fascicolo 51).
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Il vertice `±eᵢ` dell'ortoplesse. -/
noncomputable def vertOrto {d : ℕ} (p : Fin d × Bool) : E d :=
  EuclideanSpace.single p.1 (if p.2 then (1 : ℝ) else (-1 : ℝ))

theorem vertOrto_apply {d : ℕ} (p : Fin d × Bool) (k : Fin d) :
    vertOrto p k = if k = p.1 then (if p.2 then (1 : ℝ) else (-1 : ℝ))
      else 0 := by
  unfold vertOrto
  rw [PiLp.single_apply]

@[simp] theorem vertOrto_self {d : ℕ} (p : Fin d × Bool) :
    vertOrto p p.1 = if p.2 then (1 : ℝ) else (-1 : ℝ) := by
  simp [vertOrto_apply]

theorem vertOrto_injective {d : ℕ} :
    Function.Injective (vertOrto (d := d)) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ hpq
  have hval := congrArg (fun x : E d => x i) hpq
  simp only [vertOrto_apply] at hval
  have hidx : i = j := by
    by_contra hne
    rcases s <;> simp [hne] at hval
  subst j
  have hbool : s = t := by
    cases s <;> cases t
    · rfl
    · norm_num at hval
    · norm_num at hval
    · rfl
  subst t
  rfl

noncomputable def verticiOrto (d : ℕ) : Finset (E d) :=
  (Finset.univ : Finset (Fin d × Bool)).image vertOrto

theorem mem_verticiOrto {d : ℕ} {x : E d} :
    x ∈ verticiOrto d ↔ ∃ p : Fin d × Bool, vertOrto p = x := by
  simp [verticiOrto]

theorem card_verticiOrto (d : ℕ) : (verticiOrto d).card = 2 * d := by
  rw [verticiOrto, Finset.card_image_of_injective _ vertOrto_injective]
  simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  omega

theorem verticiOrto_nonempty {d : ℕ} (hd : 0 < d) :
    (verticiOrto d).Nonempty := by
  refine ⟨vertOrto (⟨0, hd⟩, true), ?_⟩
  exact mem_verticiOrto.mpr ⟨(⟨0, hd⟩, true), rfl⟩

theorem norm_vertOrto {d : ℕ} (p : Fin d × Bool) : ‖vertOrto p‖ = 1 := by
  rw [vertOrto]
  rw [PiLp.norm_single]
  split <;> norm_num

theorem cosferico_extremePoints {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace ℝ A] [Nontrivial A]
    (x : A) (r : ℝ) (V : Set A) (hV : V ⊆ sphere x r) :
    (convexHull ℝ V).extremePoints ℝ = V := by
  -- The parallelogram identity gives strict convexity of an inner-product norm.
  letI : StrictConvexSpace ℝ A :=
    StrictConvexSpace.of_norm_add_ne_two fun u w hu hw hne hsum => by
      have hpar := parallelogram_law_with_norm_mul ℝ u w
      rw [hu, hw, hsum] at hpar
      have hzero : ‖u - w‖ = 0 := by nlinarith [norm_nonneg (u - w)]
      exact hne (sub_eq_zero.mp (norm_eq_zero.mp hzero))
  refine le_antisymm extremePoints_convexHull_subset ?_
  have hball : convexHull ℝ V ⊆ closedBall x r :=
    convexHull_min (hV.trans sphere_subset_closedBall) (convex_closedBall x r)
  intro v hv
  have hsfera : v ∈ (closedBall x r).extremePoints ℝ := by
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    exact hV hv
  exact inter_extremePoints_subset_extremePoints_of_subset hball
    ⟨subset_convexHull ℝ V hv, hsfera⟩

theorem verticiOrto_eq_extremePoints (d : ℕ) :
    ((verticiOrto d : Finset (E d)) : Set (E d)) =
      Set.extremePoints ℝ
        (convexHull ℝ ((verticiOrto d : Finset (E d)) : Set (E d))) := by
  by_cases hd : d = 0
  · subst d
    simp [verticiOrto]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    let i : Fin d := ⟨0, hdpos⟩
    have hne : (0 : E d) ≠ vertOrto (i, true) := by
      intro h
      have hi := congrArg (fun x : E d => x i) h
      simp [vertOrto_apply] at hi
    haveI : Nontrivial (E d) := ⟨⟨0, vertOrto (i, true), hne⟩⟩
    symm
    apply cosferico_extremePoints 0 1
    intro v hv
    rw [mem_sphere_zero_iff_norm]
    have hv' : v ∈ verticiOrto d := by exact_mod_cast hv
    rw [mem_verticiOrto] at hv'
    obtain ⟨p, rfl⟩ := hv'
    exact norm_vertOrto p

/-- L'ortoplesse, sul dominio corretto `d ≥ 1`. -/
noncomputable def ortoplesse (d : ℕ) (hd : 1 ≤ d) : ConvexPolytope d :=
  ⟨verticiOrto d, verticiOrto_nonempty hd, verticiOrto_eq_extremePoints d⟩

theorem card_ortoplesse (d : ℕ) (hd : 1 ≤ d) :
    (ortoplesse d hd).vertices.card = 2 * d := by
  exact card_verticiOrto d

/-- L'ortoplesse genera affineamente tutto `E d`. -/
theorem ortoplesse_isFullDim (d : ℕ) (hd : 1 ≤ d) :
    (ortoplesse d hd).IsFullDim := by
  let W : Submodule ℝ (E d) := vectorSpan ℝ (ortoplesse d hd).toSet
  have hbasis : ∀ i : Fin d, (EuclideanSpace.basisFun (Fin d) ℝ) i ∈ W := by
    intro i
    have hpV : vertOrto (i, true) ∈ verticiOrto d :=
      mem_verticiOrto.mpr ⟨(i, true), rfl⟩
    have hnV : vertOrto (i, false) ∈ verticiOrto d :=
      mem_verticiOrto.mpr ⟨(i, false), rfl⟩
    have hp : vertOrto (i, true) ∈ (ortoplesse d hd).toSet := by
      exact subset_convexHull ℝ _ (by exact_mod_cast hpV)
    have hn : vertOrto (i, false) ∈ (ortoplesse d hd).toSet := by
      exact subset_convexHull ℝ _ (by exact_mod_cast hnV)
    have hdiff : vertOrto (i, true) - vertOrto (i, false) ∈ W :=
      vsub_mem_vectorSpan ℝ hp hn
    change EuclideanSpace.single i 1 - EuclideanSpace.single i (-1) ∈ W at hdiff
    rw [EuclideanSpace.basisFun_apply]
    have htwice : (2 : ℝ) • EuclideanSpace.single i 1 ∈ W := by
      simpa only [PiLp.single_neg, sub_neg_eq_add, two_smul] using hdiff
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp htwice
  have hW : W = ⊤ := by
    apply (Submodule.eq_top_iff').2
    intro x
    rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
    exact Submodule.sum_mem W fun i _ => W.smul_mem _ (hbasis i)
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim]
  change Module.finrank ℝ W = d
  rw [hW, finrank_top, finrank_euclideanSpace]
  simp

/-- L'isometria di `ℝ` data da un segno in `{ -1, 1 }`. -/
noncomputable def isometriaSegno (s : ({-1, 1} : Set ℝ)) : ℝ ≃ₗᵢ[ℝ] ℝ :=
  if (s : ℝ) = 1 then LinearIsometryEquiv.refl ℝ ℝ
  else LinearIsometryEquiv.neg ℝ

@[simp] theorem isometriaSegno_apply (s : ({-1, 1} : Set ℝ)) (x : ℝ) :
    isometriaSegno s x = (s : ℝ) * x := by
  unfold isometriaSegno
  split_ifs with h
  · rw [h]
    simp
  · have hs : (s : ℝ) = -1 := by
      have hm := s.property
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with hm | hm
      · exact hm
      · exact (h hm).elim
    rw [hs]
    simp

/-- La parte lineare della permutazione firmata: prima cambia il segno
della coordinata `i`, poi la porta nella coordinata `σ i`. -/
noncomputable def segnoLinear (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) : E d ≃ₗᵢ[ℝ] E d :=
  (LinearIsometryEquiv.piLpCongrRight 2 (fun i => isometriaSegno (ε i))).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ)

/-- La permutazione firmata delle coordinate, come isometria affine. -/
noncomputable def segnoPerm (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) : Isom d :=
  (segnoLinear d σ ε).toAffineIsometryEquiv

@[simp] theorem segnoLinear_single (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) (i : Fin d) (a : ℝ) :
    segnoLinear d σ ε (EuclideanSpace.single i a) =
      EuclideanSpace.single (σ i) ((ε i : ℝ) * a) := by
  simp [segnoLinear]

@[simp] theorem segnoPerm_apply (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) (x : E d) :
    segnoPerm d σ ε x = segnoLinear d σ ε x := rfl

theorem segnoPerm_mem_verticiOrto (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) {v : E d}
    (hv : v ∈ verticiOrto d) : segnoPerm d σ ε v ∈ verticiOrto d := by
  rw [mem_verticiOrto] at hv
  obtain ⟨⟨i, b⟩, rfl⟩ := hv
  have hs := (ε i).property
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with hs | hs <;> cases b
  · apply mem_verticiOrto.mpr
    refine ⟨(σ i, true), ?_⟩
    simp [vertOrto, hs]
  · apply mem_verticiOrto.mpr
    refine ⟨(σ i, false), ?_⟩
    simp [vertOrto, hs]
  · apply mem_verticiOrto.mpr
    refine ⟨(σ i, false), ?_⟩
    simp [vertOrto, hs]
  · apply mem_verticiOrto.mpr
    refine ⟨(σ i, true), ?_⟩
    simp [vertOrto, hs]

theorem segnoPerm_image_verticiOrto (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) :
    (segnoPerm d σ ε : E d → E d) '' (verticiOrto d : Set (E d)) =
      (verticiOrto d : Set (E d)) := by
  have hfin : Finset.image (segnoPerm d σ ε : E d → E d) (verticiOrto d) =
      verticiOrto d := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact segnoPerm_mem_verticiOrto d σ ε hu
    · rw [Finset.card_image_of_injective _ (segnoPerm d σ ε).injective]
  rw [← Finset.coe_image, hfin]

theorem segnoPerm_isSymmetry (d : ℕ) (hd : 1 ≤ d)
    (σ : Equiv.Perm (Fin d)) (ε : Fin d → ({-1, 1} : Set ℝ)) :
    (ortoplesse d hd).isSymmetry (segnoPerm d σ ε) := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (segnoPerm d σ ε : E d → E d) ''
        convexHull ℝ ((ortoplesse d hd).vertices : Set (E d)) =
      convexHull ℝ ((segnoPerm d σ ε : E d → E d) ''
        ((ortoplesse d hd).vertices : Set (E d))) := by
          exact (segnoPerm d σ ε).toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((ortoplesse d hd).vertices : Set (E d)) := by
      rw [show ((ortoplesse d hd).vertices : Set (E d)) =
          (verticiOrto d : Set (E d)) by rfl,
        segnoPerm_image_verticiOrto]

end LeanEval.Geometry.PlatonicClassification
end
end VerificationSource033

/- Original source: Cubical/Polytope/OrtoplesseFacce.lean -/
section VerificationSource034
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.OrtoplesseFacce.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- The two vertices over one coordinate are opposites. -/
theorem vertOrto_not_eq_neg {d : ℕ} (i : Fin d) (b : Bool) :
    vertOrto (i, !b) = -vertOrto (i, b) := by
  ext k
  by_cases h : k = i <;> cases b <;> simp [vertOrto_apply, h]

open Classical in
/-- A proper face of the cross-polytope contains at most one of the two
vertices over each coordinate. -/
theorem ortoplesse_face_no_antipodi (d : ℕ) (hd : 1 ≤ d)
    {f : Set (E d)} (hf : (ortoplesse d hd).IsFace f) (hproper : faceDim f < d)
    {i : Fin d} {b c : Bool}
    (hb : vertOrto (i, b) ∈ (ortoplesse d hd).vertices.filter (· ∈ f))
    (hc : vertOrto (i, c) ∈ (ortoplesse d hd).vertices.filter (· ∈ f)) :
    b = c := by
  by_contra hbc
  let P := ortoplesse d hd
  have hbF : vertOrto (i, b) ∈ f := (Finset.mem_filter.mp hb).2
  have hcF : vertOrto (i, c) ∈ f := (Finset.mem_filter.mp hc).2
  obtain ⟨l, hmem, hchar⟩ := espositore_di_faccia P hf
  have hbdata := hmem (vertOrto (i, b)) hbF
  have hcdata := hmem (vertOrto (i, c)) hcF
  have hsame : l (vertOrto (i, b)) = l (vertOrto (i, c)) :=
    le_antisymm (hcdata.2 _ hbdata.1) (hbdata.2 _ hcdata.1)
  have hopp : vertOrto (i, c) = -vertOrto (i, b) := by
    have hcnot : c = !b := by cases b <;> cases c <;> simp_all
    rw [hcnot, vertOrto_not_eq_neg]
  have hneg : l (vertOrto (i, c)) = -l (vertOrto (i, b)) := by
    rw [hopp, map_neg]
  have hbzero : l (vertOrto (i, b)) = 0 := by linarith
  have hall : ∀ v ∈ P.vertices, v ∈ f := by
    intro v hv
    have hv' : v ∈ verticiOrto d := hv
    rw [mem_verticiOrto] at hv'
    obtain ⟨⟨j, s⟩, rfl⟩ := hv'
    have hvP : vertOrto (j, s) ∈ P.toSet :=
      subset_convexHull ℝ _ (by
        exact_mod_cast (mem_verticiOrto.mpr ⟨(j, s), rfl⟩))
    have hopV : vertOrto (j, !s) ∈ P.vertices := by
      exact mem_verticiOrto.mpr ⟨(j, !s), rfl⟩
    have hopP : vertOrto (j, !s) ∈ P.toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hopV)
    have hvle : l (vertOrto (j, s)) ≤ 0 := by
      simpa [hbzero] using hbdata.2 (vertOrto (j, s)) hvP
    have hople : l (vertOrto (j, !s)) ≤ 0 := by
      simpa [hbzero] using hbdata.2 (vertOrto (j, !s)) hopP
    have hopval : l (vertOrto (j, !s)) = -l (vertOrto (j, s)) := by
      rw [vertOrto_not_eq_neg, map_neg]
    have hvzero : l (vertOrto (j, s)) = 0 := by linarith
    apply hchar (vertOrto (j, s)) hvP
    intro z hz
    calc
      l z ≤ l (vertOrto (i, b)) := hbdata.2 z hz
      _ = l (vertOrto (j, s)) := by rw [hbzero, hvzero]
  have hfP : f ⊆ P.toSet := fun y hy => (hmem y hy).1
  have hPf : P.toSet ⊆ f := by
    apply convexHull_min
    · intro v hv
      exact hall v (by exact_mod_cast hv)
    · exact hf.1.convex (convex_convexHull ℝ _)
  have heq : f = P.toSet := Set.Subset.antisymm hfP hPf
  have hdim : faceDim f = d := by
    rw [heq]
    exact ortoplesse_isFullDim d hd
  omega

open Classical in
/-- The vertices contained in a proper face of the cross-polytope are
linearly, hence affinely, independent. -/
theorem ortoplesse_face_affineIndependent (d : ℕ) (hd : 1 ≤ d)
    {f : Set (E d)} (hf : (ortoplesse d hd).IsFace f) (hproper : faceDim f < d) :
    AffineIndependent ℝ
      ((↑) : {x // x ∈
        (((ortoplesse d hd).vertices.filter (· ∈ f) : Finset (E d)) : Set (E d))} →
        E d) := by
  let S : Finset (E d) := (ortoplesse d hd).vertices.filter (· ∈ f)
  apply LinearIndependent.affineIndependent
  rw [Fintype.linearIndependent_iff]
  intro g hsum x
  have hxvert : (x : E d) ∈ verticiOrto d := (Finset.mem_filter.mp x.property).1
  rw [mem_verticiOrto] at hxvert
  obtain ⟨⟨i, b⟩, hxeq⟩ := hxvert
  have hyzero : ∀ y : {x // x ∈ (S : Set (E d))}, y ≠ x → (y : E d) i = 0 := by
    intro y hyx
    have hyvert : (y : E d) ∈ verticiOrto d := (Finset.mem_filter.mp y.property).1
    rw [mem_verticiOrto] at hyvert
    obtain ⟨⟨j, c⟩, hyeq⟩ := hyvert
    rw [← hyeq]
    by_cases hij : i = j
    · subst j
      have hxbmem : vertOrto (i, b) ∈
          (ortoplesse d hd).vertices.filter (· ∈ f) := by
        rw [hxeq]
        exact x.property
      have hycmem : vertOrto (i, c) ∈
          (ortoplesse d hd).vertices.filter (· ∈ f) := by
        rw [hyeq]
        exact y.property
      have hbc : b = c := ortoplesse_face_no_antipodi d hd hf hproper
        (i := i) (b := b) (c := c) hxbmem hycmem
      exfalso
      apply hyx
      apply Subtype.ext
      calc
        (y : E d) = vertOrto (i, c) := hyeq.symm
        _ = vertOrto (i, b) := by rw [hbc]
        _ = (x : E d) := hxeq
    · simp [vertOrto_apply, hij]
  have hcoord := congrArg (fun z : E d => z i) hsum
  have hsum' : ∑ y, g y * (y : E d) i = 0 := by
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcoord
  have hsingle : (∑ y, g y * (y : E d) i) = g x * (x : E d) i := by
    apply Finset.sum_eq_single x
    · intro y _ hyx
      rw [hyzero y hyx, mul_zero]
    · simp
  rw [hsingle] at hsum'
  have hxnonzero : (x : E d) i ≠ 0 := by
    rw [← hxeq]
    rw [vertOrto_self (i, b)]
    cases b <;> norm_num
  exact (mul_eq_zero.mp hsum').resolve_right hxnonzero

open Classical in
/-- Every proper face of the cross-polytope is a simplex. -/
theorem ortoplesse_face_card (d : ℕ) (hd : 1 ≤ d)
    {f : Set (E d)} (hf : (ortoplesse d hd).IsFace f) (hproper : faceDim f < d) :
    ((ortoplesse d hd).vertices.filter (· ∈ f)).card = faceDim f + 1 := by
  let S : Finset (E d) := (ortoplesse d hd).vertices.filter (· ∈ f)
  have hFS : f = convexHull ℝ (S : Set (E d)) := face_eq_hull_vertices _ hf
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hne := hf.2
    rw [hFS, h] at hne
    simp at hne
  have hSind : AffineIndependent ℝ
      ((↑) : {x // x ∈ (S : Set (E d))} → E d) := by
    simpa only [S] using ortoplesse_face_affineIndependent d hd hf hproper
  letI : Nonempty {x // x ∈ (S : Set (E d))} :=
    ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  have hdim := hSind.finrank_vectorSpan_add_one
  have hrange : Set.range ((↑) : {x // x ∈ (S : Set (E d))} → E d) =
      (S : Set (E d)) := Subtype.range_coe_subtype
  rw [hrange] at hdim
  have hdim' : Module.finrank ℝ (vectorSpan ℝ (S : Set (E d))) = faceDim f := by
    symm
    unfold faceDim
    rw [hFS, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  rw [hdim'] at hdim
  change S.card = faceDim f + 1
  simpa using hdim.symm

def finPredSame {d : ℕ} (k : Fin d) (_hk : k.val ≠ 0) : Fin d :=
  ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩

@[simp] theorem finPredSame_val {d : ℕ} (k : Fin d) (hk : k.val ≠ 0) :
    (finPredSame k hk).val = k.val - 1 := rfl

open Classical in
noncomputable def ortoplesseFlagVertices (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) : Finset (E d) :=
  (ortoplesse d hd).vertices.filter (· ∈ F.face k)

open Classical in
noncomputable def ortoplesseFlagPrev (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) : Finset (E d) :=
  if hk : k.val = 0 then ∅ else
    ortoplesseFlagVertices d hd F (finPredSame k hk)

open Classical in
theorem ortoplesseFlagVertices_card (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    (ortoplesseFlagVertices d hd F k).card = k.val + 1 := by
  have hproper : faceDim (F.face k) < d := by
    rw [F.dim_eq]
    exact k.isLt
  simpa [ortoplesseFlagVertices, F.dim_eq] using
    ortoplesse_face_card d hd (F.isFace k) hproper

open Classical in
theorem ortoplesseFlagVertices_mono (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) {i j : Fin d} (hij : i ≤ j) :
    ortoplesseFlagVertices d hd F i ⊆ ortoplesseFlagVertices d hd F j := by
  intro v hv
  rw [ortoplesseFlagVertices, Finset.mem_filter] at hv ⊢
  refine ⟨hv.1, ?_⟩
  rcases hij.eq_or_lt with rfl | hij
  · exact hv.2
  · exact (F.strict_mono i j hij).1 hv.2

open Classical in
theorem ortoplesseFlagStep_nonempty (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    (ortoplesseFlagVertices d hd F k \ ortoplesseFlagPrev d hd F k).Nonempty := by
  by_cases hk : k.val = 0
  · have hc := ortoplesseFlagVertices_card d hd F k
    simpa [ortoplesseFlagPrev, hk] using
      (Finset.card_pos.mp (by omega : 0 < (ortoplesseFlagVertices d hd F k).card))
  · let p : Fin d := finPredSame k hk
    have hpk : p < k := by
      apply Fin.mk_lt_mk.mpr
      simp
      omega
    have hsub : ortoplesseFlagVertices d hd F p ⊆
        ortoplesseFlagVertices d hd F k :=
      ortoplesseFlagVertices_mono d hd F hpk.le
    have hcp := ortoplesseFlagVertices_card d hd F p
    have hck := ortoplesseFlagVertices_card d hd F k
    have hcdiff :
        (ortoplesseFlagVertices d hd F k \
          ortoplesseFlagVertices d hd F p).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, hcp, hck]
      simp [p]
      omega
    have hne : (ortoplesseFlagVertices d hd F k \
        ortoplesseFlagVertices d hd F p).Nonempty :=
      Finset.card_pos.mp (by omega)
    simpa [ortoplesseFlagPrev, hk, p] using hne

open Classical in
noncomputable def ortoplesseFlagNew (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) : E d :=
  (ortoplesseFlagStep_nonempty d hd F k).choose

open Classical in
theorem ortoplesseFlagNew_mem (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    ortoplesseFlagNew d hd F k ∈ ortoplesseFlagVertices d hd F k :=
  (Finset.mem_sdiff.mp
    (ortoplesseFlagStep_nonempty d hd F k).choose_spec).1

open Classical in
theorem ortoplesseFlagNew_not_prev (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    ortoplesseFlagNew d hd F k ∉ ortoplesseFlagPrev d hd F k :=
  (Finset.mem_sdiff.mp
    (ortoplesseFlagStep_nonempty d hd F k).choose_spec).2

open Classical in
theorem ortoplesseFlagNew_injective (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) :
    Function.Injective (ortoplesseFlagNew d hd F) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hj0 : j.val ≠ 0 := by omega
    let p : Fin d := finPredSame j hj0
    have hip : i ≤ p := by
      apply Fin.mk_le_mk.mpr
      omega
    have himem : ortoplesseFlagNew d hd F i ∈
        ortoplesseFlagVertices d hd F p :=
      ortoplesseFlagVertices_mono d hd F hip
        (ortoplesseFlagNew_mem d hd F i)
    have hjnot : ortoplesseFlagNew d hd F j ∉
        ortoplesseFlagVertices d hd F p := by
      simpa [ortoplesseFlagPrev, hj0, p] using
        ortoplesseFlagNew_not_prev d hd F j
    exact hjnot (hij ▸ himem)
  · have hi0 : i.val ≠ 0 := by omega
    let p : Fin d := finPredSame i hi0
    have hjp : j ≤ p := by
      apply Fin.mk_le_mk.mpr
      omega
    have hjmem : ortoplesseFlagNew d hd F j ∈
        ortoplesseFlagVertices d hd F p :=
      ortoplesseFlagVertices_mono d hd F hjp
        (ortoplesseFlagNew_mem d hd F j)
    have hinot : ortoplesseFlagNew d hd F i ∉
        ortoplesseFlagVertices d hd F p := by
      simpa [ortoplesseFlagPrev, hi0, p] using
        ortoplesseFlagNew_not_prev d hd F i
    exact hinot (hij.symm ▸ hjmem)

open Classical in
theorem ortoplesseFlagVertices_eq_image_Iic (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    ortoplesseFlagVertices d hd F k =
      (Finset.Iic k).image (ortoplesseFlagNew d hd F) := by
  symm
  apply (Finset.eq_of_subset_of_card_le ?_ ?_)
  · intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    exact ortoplesseFlagVertices_mono d hd F (Finset.mem_Iic.mp hj)
      (ortoplesseFlagNew_mem d hd F j)
  · rw [Finset.card_image_of_injective _ (ortoplesseFlagNew_injective d hd F),
      ortoplesseFlagVertices_card d hd F k]
    simp

open Classical in
noncomputable def ortoplesseFlagCode (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) : Fin d × Bool :=
  (mem_verticiOrto.mp
    (show ortoplesseFlagNew d hd F k ∈ verticiOrto d from
      (Finset.mem_filter.mp (ortoplesseFlagNew_mem d hd F k)).1)).choose

open Classical in
theorem ortoplesseFlagCode_spec (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    vertOrto (ortoplesseFlagCode d hd F k) = ortoplesseFlagNew d hd F k :=
  (mem_verticiOrto.mp
    (show ortoplesseFlagNew d hd F k ∈ verticiOrto d from
      (Finset.mem_filter.mp (ortoplesseFlagNew_mem d hd F k)).1)).choose_spec

open Classical in
theorem ortoplesseFlagCode_fst_injective (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) :
    Function.Injective (fun k => (ortoplesseFlagCode d hd F k).1) := by
  intro i j hij
  let k : Fin d := max i j
  have himem : vertOrto (ortoplesseFlagCode d hd F i) ∈
      (ortoplesse d hd).vertices.filter (· ∈ F.face k) := by
    rw [ortoplesseFlagCode_spec]
    have hmono := ortoplesseFlagVertices_mono d hd F (show i ≤ k from le_max_left _ _)
    exact hmono (ortoplesseFlagNew_mem d hd F i)
  have hjmem : vertOrto (ortoplesseFlagCode d hd F j) ∈
      (ortoplesse d hd).vertices.filter (· ∈ F.face k) := by
    rw [ortoplesseFlagCode_spec]
    have hmono := ortoplesseFlagVertices_mono d hd F (show j ≤ k from le_max_right _ _)
    exact hmono (ortoplesseFlagNew_mem d hd F j)
  have hproper : faceDim (F.face k) < d := by
    rw [F.dim_eq]
    exact k.isLt
  have hbool : (ortoplesseFlagCode d hd F i).2 =
      (ortoplesseFlagCode d hd F j).2 :=
    ortoplesse_face_no_antipodi d hd (F.isFace k) hproper
      (i := (ortoplesseFlagCode d hd F i).1)
      (b := (ortoplesseFlagCode d hd F i).2)
      (c := (ortoplesseFlagCode d hd F j).2) himem (by simpa [hij] using hjmem)
  apply ortoplesseFlagNew_injective d hd F
  rw [← ortoplesseFlagCode_spec d hd F i,
    ← ortoplesseFlagCode_spec d hd F j]
  exact congrArg vertOrto (Prod.ext hij hbool)

open Classical in
noncomputable def ortoplesseFlagIndexEquiv (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) : Equiv.Perm (Fin d) :=
  Equiv.ofBijective (fun k => (ortoplesseFlagCode d hd F k).1)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨ortoplesseFlagCode_fst_injective d hd F, rfl⟩)

@[simp] theorem ortoplesseFlagIndexEquiv_apply (d : ℕ) (hd : 1 ≤ d)
    (F : (ortoplesse d hd).Flag) (k : Fin d) :
    ortoplesseFlagIndexEquiv d hd F k = (ortoplesseFlagCode d hd F k).1 := rfl

open Classical in
noncomputable def ortoplesseFlagPerm (d : ℕ) (hd : 1 ≤ d)
    (F G : (ortoplesse d hd).Flag) : Equiv.Perm (Fin d) :=
  (ortoplesseFlagIndexEquiv d hd F).symm.trans
    (ortoplesseFlagIndexEquiv d hd G)

open Classical in
noncomputable def ortoplesseFlagSign (d : ℕ) (hd : 1 ≤ d)
    (F G : (ortoplesse d hd).Flag) (i : Fin d) : ({-1, 1} : Set ℝ) :=
  let k := (ortoplesseFlagIndexEquiv d hd F).symm i
  if (ortoplesseFlagCode d hd F k).2 = (ortoplesseFlagCode d hd G k).2 then
    ⟨1, by simp⟩ else ⟨-1, by simp⟩

open Classical in
theorem ortoplesseFlagIsom_new (d : ℕ) (hd : 1 ≤ d)
    (F G : (ortoplesse d hd).Flag) (k : Fin d) :
    segnoPerm d (ortoplesseFlagPerm d hd F G) (ortoplesseFlagSign d hd F G)
        (ortoplesseFlagNew d hd F k) =
      ortoplesseFlagNew d hd G k := by
  rw [← ortoplesseFlagCode_spec d hd F k,
    ← ortoplesseFlagCode_spec d hd G k]
  rcases hF : ortoplesseFlagCode d hd F k with ⟨i, b⟩
  rcases hG : ortoplesseFlagCode d hd G k with ⟨j, c⟩
  simp only [vertOrto, segnoPerm_apply, segnoLinear_single]
  have hi : ortoplesseFlagIndexEquiv d hd F k = i := by
    rw [ortoplesseFlagIndexEquiv_apply, hF]
  have hj : ortoplesseFlagIndexEquiv d hd G k = j := by
    rw [ortoplesseFlagIndexEquiv_apply, hG]
  have hperm : ortoplesseFlagPerm d hd F G i = j := by
    change ortoplesseFlagIndexEquiv d hd G
      ((ortoplesseFlagIndexEquiv d hd F).symm i) = j
    have hirank : (ortoplesseFlagIndexEquiv d hd F).symm i = k := by
      rw [← hi]
      exact (ortoplesseFlagIndexEquiv d hd F).symm_apply_apply k
    rw [hirank, hj]
  rw [hperm]
  apply congrArg (EuclideanSpace.single j)
  have hirank : (ortoplesseFlagIndexEquiv d hd F).symm i = k := by
    rw [← hi]
    exact (ortoplesseFlagIndexEquiv d hd F).symm_apply_apply k
  unfold ortoplesseFlagSign
  dsimp only
  rw [hirank, hF, hG]
  cases b <;> cases c <;> norm_num

open Classical in
theorem ortoplesseFlagIsom_image_vertices (d : ℕ) (hd : 1 ≤ d)
    (F G : (ortoplesse d hd).Flag) (k : Fin d) :
    Finset.image
        (segnoPerm d (ortoplesseFlagPerm d hd F G) (ortoplesseFlagSign d hd F G))
        (ortoplesseFlagVertices d hd F k) =
      ortoplesseFlagVertices d hd G k := by
  rw [ortoplesseFlagVertices_eq_image_Iic d hd F k,
    ortoplesseFlagVertices_eq_image_Iic d hd G k]
  ext x
  simp only [Finset.mem_image, Finset.mem_Iic]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, (ortoplesseFlagIsom_new d hd F G j).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨ortoplesseFlagNew d hd F j, ⟨j, hj, rfl⟩,
      ortoplesseFlagIsom_new d hd F G j⟩

open Classical in
theorem ortoplesseFlagIsom_image_face (d : ℕ) (hd : 1 ≤ d)
    (F G : (ortoplesse d hd).Flag) (k : Fin d) :
    (segnoPerm d (ortoplesseFlagPerm d hd F G) (ortoplesseFlagSign d hd F G) :
        E d → E d) '' F.face k = G.face k := by
  let φ := segnoPerm d (ortoplesseFlagPerm d hd F G) (ortoplesseFlagSign d hd F G)
  calc
    (φ : E d → E d) '' F.face k =
        (φ : E d → E d) '' convexHull ℝ
          ((ortoplesseFlagVertices d hd F k : Finset (E d)) : Set (E d)) := by
      rw [face_eq_hull_vertices (ortoplesse d hd) (F.isFace k)]
      rfl
    _ = convexHull ℝ ((φ : E d → E d) ''
          ((ortoplesseFlagVertices d hd F k : Finset (E d)) : Set (E d))) := by
      exact φ.toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ
          ((ortoplesseFlagVertices d hd G k : Finset (E d)) : Set (E d)) := by
      rw [← Finset.coe_image, ortoplesseFlagIsom_image_vertices d hd F G k]
    _ = G.face k := by
      rw [face_eq_hull_vertices (ortoplesse d hd) (G.isFace k)]
      rfl

open Classical in
theorem ortoplesse_isRegular (d : ℕ) (hd : 1 ≤ d) : (ortoplesse d hd).IsRegular := by
  refine ⟨ortoplesse_isFullDim d hd, ?_⟩
  intro F G
  refine ⟨segnoPerm d (ortoplesseFlagPerm d hd F G) (ortoplesseFlagSign d hd F G),
    segnoPerm_isSymmetry d hd _ _, ?_⟩
  exact ortoplesseFlagIsom_image_face d hd F G

/-- The cross-polytope is one of the regular polytopes counted in dimension `d`. -/
theorem ortoplesse_mem_regularPolytopes (d : ℕ) (hd : 1 ≤ d) :
    ortoplesse d hd ∈ regularPolytopes d :=
  ortoplesse_isRegular d hd

end LeanEval.Geometry.PlatonicClassification
end
end VerificationSource034

/- Original source: Cubical/Polytope/Ipercubo.lean -/
section VerificationSource035
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Ipercubo.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/


/-!
L'ipercubo regolare in dimensione arbitraria.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Un vertice dell'ipercubo, codificato dai suoi segni. -/
noncomputable def vertIper {d : ℕ} (s : Fin d → Bool) : E d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => if s i then 1 else -1)

@[simp] theorem vertIper_apply {d : ℕ} (s : Fin d → Bool) (i : Fin d) :
    vertIper s i = if s i then (1 : ℝ) else -1 := by
  simp [vertIper]

theorem vertIper_injective {d : ℕ} :
    Function.Injective (vertIper (d := d)) := by
  intro s t h
  funext i
  have hi := congrArg (fun x : E d => x i) h
  simp only [vertIper_apply] at hi
  cases hsi : s i <;> cases hti : t i <;> simp_all <;> norm_num at hi

/-- I `2^d` vertici dell'ipercubo. -/
noncomputable def verticiIper (d : ℕ) : Finset (E d) :=
  (Finset.univ : Finset (Fin d → Bool)).image vertIper

theorem mem_verticiIper {d : ℕ} {x : E d} :
    x ∈ verticiIper d ↔ ∃ s : Fin d → Bool, vertIper s = x := by
  simp [verticiIper]

theorem card_verticiIper (d : ℕ) : (verticiIper d).card = 2 ^ d := by
  rw [verticiIper, Finset.card_image_of_injective _ vertIper_injective]
  simp

theorem norm_sq_vertIper {d : ℕ} (s : Fin d → Bool) :
    ‖vertIper s‖ ^ 2 = d := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vertIper_apply]
  have hone : ∀ i : Fin d,
      ‖(if s i = true then (1 : ℝ) else -1)‖ ^ 2 = 1 := by
    intro i
    cases s i <;> norm_num
  simp_rw [hone]
  simp

theorem norm_vertIper {d : ℕ} (s : Fin d → Bool) :
    ‖vertIper s‖ = Real.sqrt d := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), norm_sq_vertIper]
  simp

theorem verticiIper_eq_extremePoints (d : ℕ) :
    ((verticiIper d : Finset (E d)) : Set (E d)) =
      Set.extremePoints ℝ
        (convexHull ℝ ((verticiIper d : Finset (E d)) : Set (E d))) := by
  by_cases hd : d = 0
  · subst d
    have hsingle : ((verticiIper 0 : Finset (E 0)) : Set (E 0)) = {0} := by
      ext x
      constructor
      · intro _
        exact Subsingleton.elim x 0
      · rintro rfl
        exact_mod_cast (mem_verticiIper.mpr ⟨fun i => i.elim0, Subsingleton.elim _ _⟩)
    rw [hsingle]
    simp
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    let i : Fin d := ⟨0, hdpos⟩
    have hne : (0 : E d) ≠ vertIper (fun _ => true) := by
      intro h
      have hi := congrArg (fun x : E d => x i) h
      simp at hi
    haveI : Nontrivial (E d) := ⟨⟨0, vertIper (fun _ => true), hne⟩⟩
    symm
    apply cosferico_extremePoints 0 (Real.sqrt d)
    intro v hv
    rw [mem_sphere_zero_iff_norm]
    have hv' : v ∈ verticiIper d := by exact_mod_cast hv
    rw [mem_verticiIper] at hv'
    obtain ⟨s, rfl⟩ := hv'
    exact norm_vertIper s

theorem verticiIper_nonempty (d : ℕ) : (verticiIper d).Nonempty := by
  refine ⟨vertIper (fun _ => true), mem_verticiIper.mpr ?_⟩
  exact ⟨fun _ => true, rfl⟩

/-- L'ipercubo, sul dominio non degenere `d ≥ 1`. -/
noncomputable def ipercubo (d : ℕ) (_hd : 1 ≤ d) : ConvexPolytope d :=
  ⟨verticiIper d, verticiIper_nonempty d, verticiIper_eq_extremePoints d⟩

theorem card_ipercubo (d : ℕ) (hd : 1 ≤ d) :
    (ipercubo d hd).vertices.card = 2 ^ d :=
  card_verticiIper d

/-- Cambia il segno della sola coordinata `i`. -/
def boolFlip {d : ℕ} (s : Fin d → Bool) (i : Fin d) : Fin d → Bool :=
  Function.update s i (!s i)

@[simp] theorem boolFlip_same {d : ℕ} (s : Fin d → Bool) (i : Fin d) :
    boolFlip s i i = !s i := by
  simp [boolFlip]

@[simp] theorem boolFlip_ne {d : ℕ} (s : Fin d → Bool) {i j : Fin d} (h : j ≠ i) :
    boolFlip s i j = s j := by
  simp [boolFlip, h]

theorem vertIper_sub_flip {d : ℕ} (s : Fin d → Bool) (i : Fin d) :
    vertIper s - vertIper (boolFlip s i) =
      (if s i then (2 : ℝ) else -2) •
        (EuclideanSpace.basisFun (Fin d) ℝ) i := by
  ext j
  by_cases hji : j = i
  · subst j
    cases hsi : s i <;>
      simp [hsi, EuclideanSpace.basisFun_apply] <;> norm_num
  · cases s i <;> simp [hji, EuclideanSpace.basisFun_apply]

theorem ipercubo_isFullDim (d : ℕ) (hd : 1 ≤ d) :
    (ipercubo d hd).IsFullDim := by
  let W : Submodule ℝ (E d) := vectorSpan ℝ (ipercubo d hd).toSet
  let s : Fin d → Bool := fun _ => true
  have hbasis : ∀ i : Fin d, (EuclideanSpace.basisFun (Fin d) ℝ) i ∈ W := by
    intro i
    have hsV : vertIper s ∈ verticiIper d := mem_verticiIper.mpr ⟨s, rfl⟩
    have hfV : vertIper (boolFlip s i) ∈ verticiIper d :=
      mem_verticiIper.mpr ⟨boolFlip s i, rfl⟩
    have hs : vertIper s ∈ (ipercubo d hd).toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hsV)
    have hf : vertIper (boolFlip s i) ∈ (ipercubo d hd).toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hfV)
    have hdiff : vertIper s - vertIper (boolFlip s i) ∈ W :=
      vsub_mem_vectorSpan ℝ hs hf
    rw [vertIper_sub_flip] at hdiff
    simp only [s, if_true] at hdiff
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp hdiff
  have hW : W = ⊤ := by
    apply (Submodule.eq_top_iff').2
    intro x
    rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
    exact Submodule.sum_mem W fun i _ => W.smul_mem _ (hbasis i)
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim]
  change Module.finrank ℝ W = d
  rw [hW, finrank_top, finrank_euclideanSpace]
  simp

theorem mem_verticiIper_iff {d : ℕ} {x : E d} :
    x ∈ verticiIper d ↔ ∀ i : Fin d, x i = 1 ∨ x i = -1 := by
  constructor
  · intro hx i
    obtain ⟨s, rfl⟩ := mem_verticiIper.mp hx
    cases hsi : s i
    · right
      rw [vertIper_apply, hsi]
      simp
    · left
      rw [vertIper_apply, hsi]
      simp
  · intro hx
    let s : Fin d → Bool := fun i => decide (x i = 1)
    apply mem_verticiIper.mpr
    refine ⟨s, ?_⟩
    ext i
    rcases hx i with hi | hi
    · have hs : s i = true := by simp [s, hi]
      rw [vertIper_apply, hs, hi]
      simp
    · have hne : x i ≠ 1 := by linarith
      have hs : s i = false := by simp [s, hne]
      rw [vertIper_apply, hs, hi]
      simp

@[simp] theorem segnoLinear_apply_coord (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) (x : E d) (i : Fin d) :
    segnoLinear d σ ε x (σ i) = (ε i : ℝ) * x i := by
  simp [segnoLinear]

theorem segnoPerm_mem_verticiIper (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) {v : E d}
    (hv : v ∈ verticiIper d) : segnoPerm d σ ε v ∈ verticiIper d := by
  rw [mem_verticiIper_iff] at hv ⊢
  intro j
  let i : Fin d := σ.symm j
  have hj : σ i = j := σ.apply_symm_apply j
  have hcoord : segnoPerm d σ ε v j = (ε i : ℝ) * v i := by
    rw [← hj]
    exact segnoLinear_apply_coord d σ ε v i
  rw [hcoord]
  have hs := (ε i).property
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with hs | hs <;> rcases hv i with hv | hv <;>
    rw [hs, hv] <;> norm_num

theorem segnoPerm_image_verticiIper (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ε : Fin d → ({-1, 1} : Set ℝ)) :
    (segnoPerm d σ ε : E d → E d) '' (verticiIper d : Set (E d)) =
      (verticiIper d : Set (E d)) := by
  have hfin : Finset.image (segnoPerm d σ ε : E d → E d) (verticiIper d) =
      verticiIper d := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact segnoPerm_mem_verticiIper d σ ε hu
    · rw [Finset.card_image_of_injective _ (segnoPerm d σ ε).injective]
  rw [← Finset.coe_image, hfin]

theorem segnoPerm_isSymmetry_ipercubo (d : ℕ) (hd : 1 ≤ d)
    (σ : Equiv.Perm (Fin d)) (ε : Fin d → ({-1, 1} : Set ℝ)) :
    (ipercubo d hd).isSymmetry (segnoPerm d σ ε) := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (segnoPerm d σ ε : E d → E d) ''
        convexHull ℝ ((ipercubo d hd).vertices : Set (E d)) =
      convexHull ℝ ((segnoPerm d σ ε : E d → E d) ''
        ((ipercubo d hd).vertices : Set (E d))) := by
          exact (segnoPerm d σ ε).toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((ipercubo d hd).vertices : Set (E d)) := by
      rw [show ((ipercubo d hd).vertices : Set (E d)) =
          (verticiIper d : Set (E d)) by rfl,
        segnoPerm_image_verticiIper]

/-- Mescola, coordinata per coordinata, due codici di vertice. -/
def boolMix {d : ℕ} (a b m : Fin d → Bool) : Fin d → Bool :=
  fun i => if m i then a i else b i

@[simp] theorem boolMix_apply {d : ℕ} (a b m : Fin d → Bool) (i : Fin d) :
    boolMix a b m i = if m i then a i else b i := rfl

theorem vertIper_mix_add {d : ℕ} (a b m : Fin d → Bool) :
    vertIper (boolMix a b m) + vertIper (boolMix a b (fun i => !(m i))) =
      vertIper a + vertIper b := by
  ext i
  cases hmi : m i
  · simp [hmi]
    ring
  · simp [hmi]

open Classical in
/-- Le facce dell'ipercubo sono chiuse rispetto al mescolamento indipendente
delle coordinate di due loro vertici. -/
theorem ipercubo_face_mix (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) {a b : Fin d → Bool}
    (haF : vertIper a ∈ f) (hbF : vertIper b ∈ f) (m : Fin d → Bool) :
    vertIper (boolMix a b m) ∈ f := by
  let P := ipercubo d hd
  let u := vertIper (boolMix a b m)
  let u' := vertIper (boolMix a b (fun i => !(m i)))
  have haP : vertIper a ∈ P.toSet :=
    subset_convexHull ℝ _ (by
      exact_mod_cast (mem_verticiIper.mpr ⟨a, rfl⟩))
  have hbP : vertIper b ∈ P.toSet :=
    subset_convexHull ℝ _ (by
      exact_mod_cast (mem_verticiIper.mpr ⟨b, rfl⟩))
  have huP : u ∈ P.toSet :=
    subset_convexHull ℝ _ (by
      exact_mod_cast (mem_verticiIper.mpr ⟨boolMix a b m, rfl⟩))
  have hu'P : u' ∈ P.toSet :=
    subset_convexHull ℝ _ (by
      exact_mod_cast
        (mem_verticiIper.mpr ⟨boolMix a b (fun i => !(m i)), rfl⟩))
  obtain ⟨l, hmem, hchar⟩ := espositore_di_faccia P hf
  have ha := hmem (vertIper a) haF
  have hb := hmem (vertIper b) hbF
  have hab : l (vertIper a) = l (vertIper b) :=
    le_antisymm (hb.2 _ haP) (ha.2 _ hbP)
  have hsum : u + u' = vertIper a + vertIper b :=
    vertIper_mix_add a b m
  have hlsum := congrArg l hsum
  simp only [map_add] at hlsum
  have hlu_le : l u ≤ l (vertIper a) := ha.2 _ huP
  have hlu'_le : l u' ≤ l (vertIper a) := ha.2 _ hu'P
  have hlu : l u = l (vertIper a) := by linarith
  apply hchar u huP
  intro z hz
  rw [hlu]
  exact ha.2 z hz

open Classical in
/-- Coordinate che possono variare in una faccia, rispetto a un suo vertice base. -/
noncomputable def iperFaceFree {d : ℕ} (f : Set (E d)) (s : Fin d → Bool) :
    Finset (Fin d) :=
  Finset.univ.filter (fun i => ∃ t : Fin d → Bool, vertIper t ∈ f ∧ t i ≠ s i)

open Classical in
theorem mem_iperFaceFree {d : ℕ} {f : Set (E d)} {s : Fin d → Bool} {i : Fin d} :
    i ∈ iperFaceFree f s ↔
      ∃ t : Fin d → Bool, vertIper t ∈ f ∧ t i ≠ s i := by
  simp [iperFaceFree]

open Classical in
theorem ipercubo_face_singleFlip (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) {s : Fin d → Bool} (hs : vertIper s ∈ f)
    {i : Fin d} (hi : i ∈ iperFaceFree f s) :
    vertIper (boolFlip s i) ∈ f := by
  obtain ⟨t, htF, hti⟩ := mem_iperFaceFree.mp hi
  have hit : t i = !s i := by
    cases hsi : s i <;> cases hti' : t i <;> simp_all
  let m : Fin d → Bool := fun j => decide (j = i)
  have hmix := ipercubo_face_mix d hd hf htF hs m
  convert hmix using 1
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp [boolMix, boolFlip, m, hit]
  · simp [boolMix, boolFlip, m, hji]

/-- Sostituisce in `s` con i valori di `t` le coordinate di `A`. -/
def boolPatch {d : ℕ} (s t : Fin d → Bool) (A : Finset (Fin d)) : Fin d → Bool :=
  fun i => if i ∈ A then t i else s i

@[simp] theorem boolPatch_apply {d : ℕ} (s t : Fin d → Bool)
    (A : Finset (Fin d)) (i : Fin d) :
    boolPatch s t A i = if i ∈ A then t i else s i := rfl

open Classical in
theorem ipercubo_face_patch (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) {s : Fin d → Bool} (hs : vertIper s ∈ f)
    (t : Fin d → Bool) {A : Finset (Fin d)} (hA : A ⊆ iperFaceFree f s) :
    vertIper (boolPatch s t A) ∈ f := by
  induction A using Finset.induction_on with
  | empty =>
      have hpatch : boolPatch s t ∅ = s := by
        funext i
        simp [boolPatch]
      rw [hpatch]
      exact hs
  | @insert i A hi ih =>
      have hAsub : A ⊆ iperFaceFree f s :=
        fun j hj => hA (Finset.mem_insert_of_mem hj)
      have hprev := ih hAsub
      by_cases hti : t i = s i
      · convert hprev using 1
        congr 1
        funext j
        by_cases hji : j = i
        · subst j
          simp [boolPatch, hti]
        · simp [boolPatch, hji]
      · have hiFree : i ∈ iperFaceFree f s := hA (by simp)
        have hflip := ipercubo_face_singleFlip d hd hf hs hiFree
        let m : Fin d → Bool := fun j => decide (j = i)
        have hmix := ipercubo_face_mix d hd hf hflip hprev m
        convert hmix using 1
        congr 1
        funext j
        by_cases hji : j = i
        · subst j
          have hnot : (!s i) = t i := by
            cases hsi : s i <;> cases hti' : t i <;> simp_all
          simp [boolMix, boolPatch, boolFlip, m, hnot]
        · simp [boolMix, boolPatch, m, hji]

open Classical in
/-- Classificazione dei vertici di una faccia: fuori dalle coordinate libere
tutti i segni coincidono con quelli del vertice base. -/
theorem vertIper_mem_face_iff (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) {s : Fin d → Bool} (hs : vertIper s ∈ f)
    (t : Fin d → Bool) :
    vertIper t ∈ f ↔ ∀ i ∉ iperFaceFree f s, t i = s i := by
  constructor
  · intro ht i hi
    by_contra hne
    exact hi (mem_iperFaceFree.mpr ⟨t, ht, hne⟩)
  · intro ht
    have hp := ipercubo_face_patch d hd hf hs t
      (show iperFaceFree f s ⊆ iperFaceFree f s from fun _ h => h)
    convert hp using 1
    congr 1
    funext i
    by_cases hi : i ∈ iperFaceFree f s
    · simp [boolPatch, hi]
    · simp [boolPatch, hi, ht i hi]

/-- Sottospazio generato dagli assi di un insieme di coordinate. -/
noncomputable def iperCoordSpan {d : ℕ} (A : Finset (Fin d)) : Submodule ℝ (E d) :=
  Submodule.span ℝ
    ((fun i : Fin d => (EuclideanSpace.basisFun (Fin d) ℝ) i) '' (A : Set (Fin d)))

theorem basis_mem_iperCoordSpan {d : ℕ} {A : Finset (Fin d)} {i : Fin d}
    (hi : i ∈ A) :
    (EuclideanSpace.basisFun (Fin d) ℝ) i ∈ iperCoordSpan A := by
  apply Submodule.subset_span
  exact ⟨i, by exact_mod_cast hi, rfl⟩

theorem mem_iperCoordSpan_of_eq_zero {d : ℕ} {A : Finset (Fin d)} {x : E d}
    (hx : ∀ i ∉ A, x i = 0) : x ∈ iperCoordSpan A := by
  rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ∈ A
  · exact (iperCoordSpan A).smul_mem _ (basis_mem_iperCoordSpan hi)
  · have hrepr : ((EuclideanSpace.basisFun (Fin d) ℝ).repr x) i = 0 := by
      rw [EuclideanSpace.basisFun_repr]
      exact hx i hi
    rw [hrepr, zero_smul]
    exact (iperCoordSpan A).zero_mem

theorem finrank_iperCoordSpan {d : ℕ} (A : Finset (Fin d)) :
    Module.finrank ℝ (iperCoordSpan A) = A.card := by
  let b : {i : Fin d // i ∈ A} → E d :=
    fun i => (EuclideanSpace.basisFun (Fin d) ℝ) i.1
  have hb : LinearIndependent ℝ b := by
    exact (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.linearIndependent.comp
      (fun i : {i : Fin d // i ∈ A} => i.1) Subtype.val_injective
  have hrange : Set.range b =
      (fun i : Fin d => (EuclideanSpace.basisFun (Fin d) ℝ) i) ''
        (A : Set (Fin d)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, by exact_mod_cast i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by exact_mod_cast hi⟩, rfl⟩
  unfold iperCoordSpan
  rw [← hrange, finrank_span_eq_card hb]
  simp

open Classical in
/-- Il sottospazio direttore di una faccia dell'ipercubo è generato
esattamente dagli assi delle sue coordinate libere. -/
theorem ipercubo_face_vectorSpan (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) {s : Fin d → Bool} (hs : vertIper s ∈ f) :
    vectorSpan ℝ f = iperCoordSpan (iperFaceFree f s) := by
  let S : Finset (E d) := (ipercubo d hd).vertices.filter (· ∈ f)
  have hsS : vertIper s ∈ (S : Set (E d)) := by
    exact_mod_cast (Finset.mem_filter.mpr
      ⟨mem_verticiIper.mpr ⟨s, rfl⟩, hs⟩)
  have hFS : f = convexHull ℝ (S : Set (E d)) :=
    face_eq_hull_vertices _ hf
  have hspan : vectorSpan ℝ f = vectorSpan ℝ (S : Set (E d)) := by
    rw [hFS, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  rw [hspan]
  apply le_antisymm
  · rw [vectorSpan_eq_span_vsub_set_right ℝ hsS, Submodule.span_le]
    rintro y ⟨x, hxS, rfl⟩
    have hxV : x ∈ (ipercubo d hd).vertices :=
      (Finset.mem_filter.mp (by exact_mod_cast hxS)).1
    have hxF : x ∈ f :=
      (Finset.mem_filter.mp (by exact_mod_cast hxS)).2
    obtain ⟨t, rfl⟩ := mem_verticiIper.mp hxV
    apply mem_iperCoordSpan_of_eq_zero
    intro i hi
    have hit := (vertIper_mem_face_iff d hd hf hs t).mp hxF i hi
    simp [hit]
  · unfold iperCoordSpan
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i ∈ iperFaceFree f s := by exact_mod_cast hi
    have hflipF := ipercubo_face_singleFlip d hd hf hs hi'
    have hflipS : vertIper (boolFlip s i) ∈ (S : Set (E d)) := by
      exact_mod_cast (Finset.mem_filter.mpr
        ⟨mem_verticiIper.mpr ⟨boolFlip s i, rfl⟩, hflipF⟩)
    have hdiff : vertIper s - vertIper (boolFlip s i) ∈
        vectorSpan ℝ (S : Set (E d)) :=
      vsub_mem_vectorSpan ℝ hsS hflipS
    rw [vertIper_sub_flip] at hdiff
    by_cases hsi : s i
    · simp [hsi] at hdiff
      simpa [EuclideanSpace.basisFun_apply] using hdiff
    · simp [hsi] at hdiff
      simpa [EuclideanSpace.basisFun_apply] using hdiff

theorem ipercubo_face_free_card (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) {s : Fin d → Bool} (hs : vertIper s ∈ f) :
    (iperFaceFree f s).card = faceDim f := by
  unfold faceDim
  rw [ipercubo_face_vectorSpan d hd hf hs, finrank_iperCoordSpan]

open Classical in
theorem ipercubo_face_vertices_nonempty (d : ℕ) (hd : 1 ≤ d) {f : Set (E d)}
    (hf : (ipercubo d hd).IsFace f) :
    ((ipercubo d hd).vertices.filter (· ∈ f)).Nonempty := by
  let S : Finset (E d) := (ipercubo d hd).vertices.filter (· ∈ f)
  have hFS : f = convexHull ℝ (S : Set (E d)) := face_eq_hull_vertices _ hf
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hS : S = ∅ := by simpa [S] using h
  have hne := hf.2
  rw [hFS, hS] at hne
  simp at hne

open Classical in
/-- Codice del vertice iniziale di una bandiera. -/
noncomputable def ipercuboFlagBaseCode (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) : Fin d → Bool := by
  let z : Fin d := ⟨0, hd⟩
  let v := (ipercubo_face_vertices_nonempty d hd (F.isFace z)).choose
  have hv : v ∈ verticiIper d :=
    (Finset.mem_filter.mp
      (ipercubo_face_vertices_nonempty d hd (F.isFace z)).choose_spec).1
  exact (mem_verticiIper.mp hv).choose

open Classical in
theorem ipercuboFlagBaseCode_spec (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) :
    vertIper (ipercuboFlagBaseCode d hd F) ∈ F.face ⟨0, hd⟩ := by
  let z : Fin d := ⟨0, hd⟩
  let v := (ipercubo_face_vertices_nonempty d hd (F.isFace z)).choose
  have hvS := (ipercubo_face_vertices_nonempty d hd (F.isFace z)).choose_spec
  have hvV : v ∈ verticiIper d := (Finset.mem_filter.mp hvS).1
  have hvF : v ∈ F.face z := (Finset.mem_filter.mp hvS).2
  have hcode : vertIper (ipercuboFlagBaseCode d hd F) = v := by
    exact (mem_verticiIper.mp hvV).choose_spec
  rwa [hcode]

theorem ipercuboFlagBaseCode_mem (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    vertIper (ipercuboFlagBaseCode d hd F) ∈ F.face k := by
  let z : Fin d := ⟨0, hd⟩
  have hz := ipercuboFlagBaseCode_spec d hd F
  by_cases hk : k.val = 0
  · have hkz : k = z := by ext; simpa [z] using hk
    simpa [hkz, z] using hz
  · have hzk : z < k := by
      apply Fin.mk_lt_mk.mpr
      omega
    exact (F.strict_mono z k hzk).1 hz

open Classical in
/-- Coordinate libere nella faccia di rango `k` di una bandiera. -/
noncomputable def ipercuboFlagFree (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) : Finset (Fin d) :=
  iperFaceFree (F.face k) (ipercuboFlagBaseCode d hd F)

theorem ipercuboFlagFree_card (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    (ipercuboFlagFree d hd F k).card = k.val := by
  rw [ipercuboFlagFree, ipercubo_face_free_card d hd (F.isFace k)
    (ipercuboFlagBaseCode_mem d hd F k), F.dim_eq]

open Classical in
theorem ipercuboFlagFree_mono (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) {i j : Fin d} (hij : i ≤ j) :
    ipercuboFlagFree d hd F i ⊆ ipercuboFlagFree d hd F j := by
  intro q hq
  obtain ⟨t, htF, htq⟩ := mem_iperFaceFree.mp hq
  apply mem_iperFaceFree.mpr
  refine ⟨t, ?_, htq⟩
  rcases hij.eq_or_lt with rfl | hij
  · exact htF
  · exact (F.strict_mono i j hij).1 htF

open Classical in
/-- Stadio successivo delle coordinate libere; dopo l'ultima faccia è `univ`. -/
noncomputable def ipercuboFlagNextFree (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) : Finset (Fin d) :=
  if hk : k.val + 1 < d then
    ipercuboFlagFree d hd F ⟨k.val + 1, hk⟩
  else Finset.univ

open Classical in
theorem ipercuboFlagFree_subset_next (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagFree d hd F k ⊆ ipercuboFlagNextFree d hd F k := by
  by_cases hk : k.val + 1 < d
  · simp only [ipercuboFlagNextFree, dif_pos hk]
    apply ipercuboFlagFree_mono d hd F
    exact Fin.mk_le_mk.mpr (Nat.le_succ k.val)
  · simp [ipercuboFlagNextFree, hk]

open Classical in
theorem ipercuboFlagNextFree_card (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    (ipercuboFlagNextFree d hd F k).card = k.val + 1 := by
  by_cases hk : k.val + 1 < d
  · simp [ipercuboFlagNextFree, hk, ipercuboFlagFree_card]
  · have heq : d = k.val + 1 := by omega
    simp [ipercuboFlagNextFree, heq]

open Classical in
theorem ipercuboFlagStep_card (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    (ipercuboFlagNextFree d hd F k \ ipercuboFlagFree d hd F k).card = 1 := by
  rw [Finset.card_sdiff_of_subset (ipercuboFlagFree_subset_next d hd F k),
    ipercuboFlagNextFree_card, ipercuboFlagFree_card]
  omega

open Classical in
theorem ipercuboFlagStep_nonempty (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    (ipercuboFlagNextFree d hd F k \ ipercuboFlagFree d hd F k).Nonempty := by
  apply Finset.card_pos.mp
  rw [ipercuboFlagStep_card]
  decide

open Classical in
noncomputable def ipercuboFlagCoord (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) : Fin d :=
  (ipercuboFlagStep_nonempty d hd F k).choose

open Classical in
theorem ipercuboFlagCoord_mem_next (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagCoord d hd F k ∈ ipercuboFlagNextFree d hd F k :=
  (Finset.mem_sdiff.mp
    (ipercuboFlagStep_nonempty d hd F k).choose_spec).1

open Classical in
theorem ipercuboFlagCoord_not_free (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagCoord d hd F k ∉ ipercuboFlagFree d hd F k :=
  (Finset.mem_sdiff.mp
    (ipercuboFlagStep_nonempty d hd F k).choose_spec).2

open Classical in
theorem ipercuboFlagCoord_mem_free_of_lt (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) {i j : Fin d} (hij : i < j) :
    ipercuboFlagCoord d hd F i ∈ ipercuboFlagFree d hd F j := by
  have hisucc : i.val + 1 < d := by omega
  have hmem : ipercuboFlagCoord d hd F i ∈
      ipercuboFlagFree d hd F ⟨i.val + 1, hisucc⟩ := by
    simpa [ipercuboFlagNextFree, hisucc] using
      ipercuboFlagCoord_mem_next d hd F i
  apply ipercuboFlagFree_mono d hd F (i := ⟨i.val + 1, hisucc⟩) (j := j)
  · exact Fin.mk_le_mk.mpr (by omega)
  · exact hmem

open Classical in
theorem ipercuboFlagCoord_injective (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) :
    Function.Injective (ipercuboFlagCoord d hd F) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · exact (ipercuboFlagCoord_not_free d hd F j)
      (hij ▸ ipercuboFlagCoord_mem_free_of_lt d hd F hijlt)
  · exact (ipercuboFlagCoord_not_free d hd F i)
      (hij.symm ▸ ipercuboFlagCoord_mem_free_of_lt d hd F hjilt)

open Classical in
noncomputable def ipercuboFlagCoordEquiv (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) : Equiv.Perm (Fin d) :=
  Equiv.ofBijective (ipercuboFlagCoord d hd F)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨ipercuboFlagCoord_injective d hd F, rfl⟩)

@[simp] theorem ipercuboFlagCoordEquiv_apply (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagCoordEquiv d hd F k = ipercuboFlagCoord d hd F k := rfl

open Classical in
theorem ipercuboFlagFree_eq_image_Iio (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagFree d hd F k =
      (Finset.Iio k).image (ipercuboFlagCoord d hd F) := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact ipercuboFlagCoord_mem_free_of_lt d hd F (Finset.mem_Iio.mp hi)
  · rw [Finset.card_image_of_injective _ (ipercuboFlagCoord_injective d hd F),
      ipercuboFlagFree_card]
    simp

open Classical in
/-- Restrizione alle coordinate di `A` dei codici che coincidono con `s`
fuori da `A`. -/
noncomputable def iperAgreeEquiv {d : ℕ} (A : Finset (Fin d)) (s : Fin d → Bool) :
    {t : Fin d → Bool // ∀ i, i ∉ A → t i = s i} ≃ ({i : Fin d // i ∈ A} → Bool) where
  toFun t i := t.1 i.1
  invFun u := ⟨fun i => if hi : i ∈ A then u ⟨i, hi⟩ else s i, by
    intro i hi
    simp [hi]⟩
  left_inv t := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ A
    · simp [hi]
    · simp [hi, t.2 i hi]
  right_inv u := by
    funext i
    simp [i.2]

open Classical in
theorem card_signs_agree {d : ℕ} (A : Finset (Fin d)) (s : Fin d → Bool) :
    ((Finset.univ : Finset (Fin d → Bool)).filter
      (fun t => ∀ i, i ∉ A → t i = s i)).card = 2 ^ A.card := by
  calc
    ((Finset.univ : Finset (Fin d → Bool)).filter
        (fun t => ∀ i, i ∉ A → t i = s i)).card =
        (Finset.univ : Finset ({i : Fin d // i ∈ A} → Bool)).card := by
      refine Finset.card_bij'
        (fun t _ i => t i.1)
        (fun u _ i => if hi : i ∈ A then u ⟨i, hi⟩ else s i)
        (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro u _
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro i hi
        simp [hi]
      · intro t ht
        funext i
        by_cases hi : i ∈ A
        · simp [hi]
        · have hit := (Finset.mem_filter.mp ht).2 i hi
          simp [hi, hit]
      · intro u _
        funext i
        simp [i.2]
    _ = 2 ^ A.card := by simp

open Classical in
noncomputable def ipercuboFlagVertices (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) : Finset (E d) :=
  (ipercubo d hd).vertices.filter (· ∈ F.face k)

open Classical in
theorem ipercuboFlagVertices_eq_image_codes (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagVertices d hd F k =
      ((Finset.univ : Finset (Fin d → Bool)).filter
        (fun t => vertIper t ∈ F.face k)).image vertIper := by
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_filter.mp hx
    obtain ⟨t, rfl⟩ := mem_verticiIper.mp hx'.1
    exact Finset.mem_image.mpr ⟨t, by simp [hx'.2], rfl⟩
  · intro hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have htF : vertIper t ∈ F.face k := by simpa using (Finset.mem_filter.mp ht).2
    exact Finset.mem_filter.mpr ⟨mem_verticiIper.mpr ⟨t, rfl⟩, htF⟩

open Classical in
theorem ipercuboFlagVertices_card (d : ℕ) (hd : 1 ≤ d)
    (F : (ipercubo d hd).Flag) (k : Fin d) :
    (ipercuboFlagVertices d hd F k).card = 2 ^ k.val := by
  rw [ipercuboFlagVertices_eq_image_codes,
    Finset.card_image_of_injective _ vertIper_injective]
  have hfilter :
      (Finset.univ : Finset (Fin d → Bool)).filter
          (fun t => vertIper t ∈ F.face k) =
        (Finset.univ : Finset (Fin d → Bool)).filter
          (fun t => ∀ i, i ∉ ipercuboFlagFree d hd F k →
            t i = ipercuboFlagBaseCode d hd F i) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact vertIper_mem_face_iff d hd (F.isFace k)
      (ipercuboFlagBaseCode_mem d hd F k) t
  rw [hfilter, card_signs_agree, ipercuboFlagFree_card]

open Classical in
noncomputable def ipercuboFlagPerm (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) : Equiv.Perm (Fin d) :=
  (ipercuboFlagCoordEquiv d hd F).symm.trans
    (ipercuboFlagCoordEquiv d hd G)

@[simp] theorem ipercuboFlagPerm_coord (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) (k : Fin d) :
    ipercuboFlagPerm d hd F G (ipercuboFlagCoord d hd F k) =
      ipercuboFlagCoord d hd G k := by
  change ipercuboFlagCoordEquiv d hd G
    ((ipercuboFlagCoordEquiv d hd F).symm
      (ipercuboFlagCoordEquiv d hd F k)) = _
  rw [(ipercuboFlagCoordEquiv d hd F).symm_apply_apply]
  rfl

open Classical in
theorem ipercuboFlagPerm_mem_free_iff (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) (k : Fin d) (i : Fin d) :
    ipercuboFlagPerm d hd F G i ∈ ipercuboFlagFree d hd G k ↔
      i ∈ ipercuboFlagFree d hd F k := by
  rw [ipercuboFlagFree_eq_image_Iio, ipercuboFlagFree_eq_image_Iio]
  constructor
  · intro hi
    obtain ⟨r, hr, hir⟩ := Finset.mem_image.mp hi
    apply Finset.mem_image.mpr
    refine ⟨r, hr, ?_⟩
    apply (ipercuboFlagPerm d hd F G).injective
    rw [ipercuboFlagPerm_coord]
    exact hir
  · intro hi
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_image.mpr
    exact ⟨r, hr, (ipercuboFlagPerm_coord d hd F G r).symm⟩

open Classical in
/-- Segni che mandano il vertice base di `F` in quello di `G`. -/
noncomputable def ipercuboFlagSign (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) (i : Fin d) : ({-1, 1} : Set ℝ) :=
  if ipercuboFlagBaseCode d hd F i =
      ipercuboFlagBaseCode d hd G (ipercuboFlagPerm d hd F G i) then
    ⟨1, by simp⟩ else ⟨-1, by simp⟩

open Classical in
theorem ipercuboFlagIsom_base (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) :
    segnoPerm d (ipercuboFlagPerm d hd F G) (ipercuboFlagSign d hd F G)
        (vertIper (ipercuboFlagBaseCode d hd F)) =
      vertIper (ipercuboFlagBaseCode d hd G) := by
  let σ := ipercuboFlagPerm d hd F G
  let ε := ipercuboFlagSign d hd F G
  ext j
  let i : Fin d := σ.symm j
  have hj : σ i = j := σ.apply_symm_apply j
  rw [← hj]
  change segnoLinear d (ipercuboFlagPerm d hd F G)
      (ipercuboFlagSign d hd F G)
        (vertIper (ipercuboFlagBaseCode d hd F))
          (ipercuboFlagPerm d hd F G i) =
    vertIper (ipercuboFlagBaseCode d hd G) (ipercuboFlagPerm d hd F G i)
  rw [segnoLinear_apply_coord]
  unfold ipercuboFlagSign
  dsimp only
  cases hF : ipercuboFlagBaseCode d hd F i <;>
    cases hG : ipercuboFlagBaseCode d hd G (ipercuboFlagPerm d hd F G i) <;>
      simp [hF, hG]

open Classical in
theorem ipercuboFlagIsom_mem_vertices (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) (k : Fin d) {v : E d}
    (hv : v ∈ ipercuboFlagVertices d hd F k) :
    segnoPerm d (ipercuboFlagPerm d hd F G) (ipercuboFlagSign d hd F G) v ∈
      ipercuboFlagVertices d hd G k := by
  let σ := ipercuboFlagPerm d hd F G
  let ε := ipercuboFlagSign d hd F G
  have hv' := Finset.mem_filter.mp hv
  obtain ⟨t, rfl⟩ := mem_verticiIper.mp hv'.1
  have hyV : segnoPerm d σ ε (vertIper t) ∈ verticiIper d :=
    segnoPerm_mem_verticiIper d σ ε (mem_verticiIper.mpr ⟨t, rfl⟩)
  obtain ⟨u, hu⟩ := mem_verticiIper.mp hyV
  have htfree := (vertIper_mem_face_iff d hd (F.isFace k)
    (ipercuboFlagBaseCode_mem d hd F k) t).mp hv'.2
  have hufree : ∀ j ∉ ipercuboFlagFree d hd G k,
      u j = ipercuboFlagBaseCode d hd G j := by
    intro j hj
    let i : Fin d := σ.symm j
    have hji : σ i = j := σ.apply_symm_apply j
    have hi : i ∉ ipercuboFlagFree d hd F k := by
      intro hiF
      apply hj
      rw [← hji]
      exact (ipercuboFlagPerm_mem_free_iff d hd F G k i).mpr hiF
    have hti := htfree i hi
    have hcoord : vertIper u j =
        vertIper (ipercuboFlagBaseCode d hd G) j := by
      calc
        vertIper u j = segnoPerm d σ ε (vertIper t) j := by rw [hu]
        _ = segnoPerm d σ ε
            (vertIper (ipercuboFlagBaseCode d hd F)) j := by
              rw [← hji]
              change segnoLinear d σ ε (vertIper t) (σ i) =
                segnoLinear d σ ε
                  (vertIper (ipercuboFlagBaseCode d hd F)) (σ i)
              rw [segnoLinear_apply_coord, segnoLinear_apply_coord]
              simp only [vertIper_apply]
              rw [hti]
        _ = vertIper (ipercuboFlagBaseCode d hd G) j := by
              rw [ipercuboFlagIsom_base d hd F G]
    cases huj : u j <;>
      cases hGj : ipercuboFlagBaseCode d hd G j <;>
        simp [huj, hGj] at hcoord ⊢ <;> norm_num at hcoord
  apply Finset.mem_filter.mpr
  refine ⟨hyV, ?_⟩
  rw [← hu]
  exact (vertIper_mem_face_iff d hd (G.isFace k)
    (ipercuboFlagBaseCode_mem d hd G k) u).mpr hufree

open Classical in
theorem ipercuboFlagIsom_image_vertices (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) (k : Fin d) :
    Finset.image
        (segnoPerm d (ipercuboFlagPerm d hd F G) (ipercuboFlagSign d hd F G))
        (ipercuboFlagVertices d hd F k) =
      ipercuboFlagVertices d hd G k := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact ipercuboFlagIsom_mem_vertices d hd F G k hu
  · rw [Finset.card_image_of_injective _
      (segnoPerm d (ipercuboFlagPerm d hd F G)
        (ipercuboFlagSign d hd F G)).injective,
      ipercuboFlagVertices_card, ipercuboFlagVertices_card]

open Classical in
theorem ipercuboFlagIsom_image_face (d : ℕ) (hd : 1 ≤ d)
    (F G : (ipercubo d hd).Flag) (k : Fin d) :
    (segnoPerm d (ipercuboFlagPerm d hd F G) (ipercuboFlagSign d hd F G) :
        E d → E d) '' F.face k = G.face k := by
  let φ := segnoPerm d (ipercuboFlagPerm d hd F G) (ipercuboFlagSign d hd F G)
  calc
    (φ : E d → E d) '' F.face k =
        (φ : E d → E d) '' convexHull ℝ
          ((ipercuboFlagVertices d hd F k : Finset (E d)) : Set (E d)) := by
      rw [face_eq_hull_vertices (ipercubo d hd) (F.isFace k)]
      rfl
    _ = convexHull ℝ ((φ : E d → E d) ''
          ((ipercuboFlagVertices d hd F k : Finset (E d)) : Set (E d))) := by
      exact φ.toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ
          ((ipercuboFlagVertices d hd G k : Finset (E d)) : Set (E d)) := by
      rw [← Finset.coe_image, ipercuboFlagIsom_image_vertices d hd F G k]
    _ = G.face k := by
      rw [face_eq_hull_vertices (ipercubo d hd) (G.isFace k)]
      rfl

open Classical in
theorem ipercubo_isRegular (d : ℕ) (hd : 1 ≤ d) :
    (ipercubo d hd).IsRegular := by
  refine ⟨ipercubo_isFullDim d hd, ?_⟩
  intro F G
  refine ⟨segnoPerm d (ipercuboFlagPerm d hd F G) (ipercuboFlagSign d hd F G),
    segnoPerm_isSymmetry_ipercubo d hd _ _, ?_⟩
  exact ipercuboFlagIsom_image_face d hd F G

theorem ipercubo_mem_regularPolytopes (d : ℕ) (hd : 1 ≤ d) :
    ipercubo d hd ∈ regularPolytopes d :=
  ipercubo_isRegular d hd

end LeanEval.Geometry.PlatonicClassification
end
end VerificationSource035

/- Original source: Cubical/Polytope/Cubical.lean -/
section VerificationSource036



/-!
# Geometric meaning of “cubical”

The standard cube is the convex hull of all sign vectors. A polytope is
cubical when each facet has the ordinary nonempty face poset of a cube.
No lower bound, bipartition, connectivity, or rigidity claim enters this
definition. Rank preservation follows from `faceOrderIso_dimension`.
-/

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- The standard geometric cube in every dimension, including dimension zero. -/
noncomputable def standardCube (d : ℕ) : ConvexPolytope d :=
  ⟨verticiIper d, verticiIper_nonempty d, verticiIper_eq_extremePoints d⟩

@[simp] theorem standardCube_vertices_card (d : ℕ) :
    (standardCube d).vertices.card = 2 ^ d := card_verticiIper d

theorem standardCube_eq_ipercubo (d : ℕ) (hd : 1 ≤ d) :
    standardCube d = ipercubo d hd := rfl

/-- Combinatorial equivalence of finite convex polytopes. -/
def CombinatoriallyEquivalent {n m : ℕ}
    (P : ConvexPolytope n) (Q : ConvexPolytope m) : Prop :=
  Nonempty (FaceType P ≃o FaceType Q)

/-- Every geometric facet is combinatorially a cube of the required dimension. -/
def IsCubical {n : ℕ} (P : ConvexPolytope n) : Prop :=
  ∀ (F : Set (E n)) (hF : P.IsFace F),
    faceDim F + 1 = P.dim →
    CombinatoriallyEquivalent (facePolytope P hF) (standardCube (P.dim - 1))

/-- Each two-dimensional face has exactly four extreme vertices. -/
def HasQuadrilateralTwoFaces {n : ℕ} (P : ConvexPolytope n) : Prop :=
  ∀ (F : Set (E n)) (hF : P.IsFace F), faceDim F = 2 →
    (facePolytope P hF).vertices.card = 4

end LeanEval.Geometry.PlatonicClassification
end VerificationSource036

/- Original source: Cubical/Polytope/CombinatorialTransport.lean -/
section VerificationSource037



/-!
# Transporting vertices, incidence, and edges by a face-poset isomorphism

The maps in this file are induced by ordinary geometric singleton faces.
They identify the actual extreme vertices and actual edge graphs, without
adding a separate combinatorial correspondence to the hypotheses.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ} {P : ConvexPolytope n} {Q : ConvexPolytope m}

abbrev ZeroFaceType (P : ConvexPolytope n) := {F : FaceType P // faceDim F.val = 0}

def vertexZeroFace (P : ConvexPolytope n) (v : VertexType P) : ZeroFaceType P :=
  ⟨⟨{v.val}, vertex_isFace P v.property⟩, faceDim_singleton v.val⟩

theorem vertexZeroFace_bijective (P : ConvexPolytope n) :
    Function.Bijective (vertexZeroFace P) := by
  constructor
  · intro u v h
    apply Subtype.ext
    apply Set.singleton_injective
    exact congrArg (fun F : ZeroFaceType P ↦ F.val.val) h
  · rintro ⟨⟨F, hF⟩, hdim⟩
    obtain ⟨v, rfl, hv⟩ := punto_di_faccia0_e_vertice P hF hdim
    exact ⟨⟨v, hv⟩, rfl⟩

def vertexFaceEquiv (P : ConvexPolytope n) : VertexType P ≃ ZeroFaceType P :=
  Equiv.ofBijective (vertexZeroFace P) (vertexZeroFace_bijective P)

def zeroFaceOrderEquiv (φ : FaceType P ≃o FaceType Q) : ZeroFaceType P ≃ ZeroFaceType Q where
  toFun F := ⟨φ F.val, (faceOrderIso_dimension φ F.val).trans F.property⟩
  invFun F := ⟨φ.symm F.val, (faceOrderIso_dimension φ.symm F.val).trans F.property⟩
  left_inv F := Subtype.ext (φ.symm_apply_apply F.val)
  right_inv F := Subtype.ext (φ.apply_symm_apply F.val)

/-- The vertex bijection determined by a combinatorial equivalence. -/
def vertexOrderEquiv (φ : FaceType P ≃o FaceType Q) : VertexType P ≃ VertexType Q :=
  (vertexFaceEquiv P).trans ((zeroFaceOrderEquiv φ).trans (vertexFaceEquiv Q).symm)

theorem singleton_vertexOrderEquiv (φ : FaceType P ≃o FaceType Q) (v : VertexType P) :
    (φ ⟨{v.val}, vertex_isFace P v.property⟩).val = {(vertexOrderEquiv φ v).val} := by
  have h := (vertexFaceEquiv Q).apply_symm_apply
    (zeroFaceOrderEquiv φ (vertexFaceEquiv P v))
  exact (congrArg (fun F : ZeroFaceType Q ↦ F.val.val) h).symm

/-- Incidence with every face is preserved by the induced vertex bijection. -/
theorem vertexOrderEquiv_mem_iff (φ : FaceType P ≃o FaceType Q)
    (v : VertexType P) (F : FaceType P) :
    (vertexOrderEquiv φ v).val ∈ (φ F).val ↔ v.val ∈ F.val := by
  calc
    (vertexOrderEquiv φ v).val ∈ (φ F).val ↔
        {(vertexOrderEquiv φ v).val} ⊆ (φ F).val := Set.singleton_subset_iff.symm
    _ ↔ (φ ⟨{v.val}, vertex_isFace P v.property⟩).val ⊆ (φ F).val := by
      rw [singleton_vertexOrderEquiv]
    _ ↔ ({v.val} : Set (E n)) ⊆ F.val := φ.le_iff_le
    _ ↔ v.val ∈ F.val := Set.singleton_subset_iff

/-- The genuine edge graph is an invariant of the ordinary face poset. -/
def graphOrderIso (φ : FaceType P ≃o FaceType Q) : polytopeGraph P ≃g polytopeGraph Q where
  __ := vertexOrderEquiv φ
  map_rel_iff' := by
    intro u v
    change (polytopeGraph Q).Adj (vertexOrderEquiv φ u) (vertexOrderEquiv φ v) ↔
      (polytopeGraph P).Adj u v
    constructor
    · rintro ⟨hne, F, hF, hdim, hu, hv⟩
      let S : FaceType Q := ⟨F, hF⟩
      refine ⟨fun h ↦ hne (congrArg (vertexOrderEquiv φ) h),
        (φ.symm S).val, (φ.symm S).property, ?_, ?_, ?_⟩
      · exact (faceOrderIso_dimension φ.symm S).trans hdim
      · apply (vertexOrderEquiv_mem_iff φ u (φ.symm S)).mp
        simpa only [φ.apply_symm_apply] using hu
      · apply (vertexOrderEquiv_mem_iff φ v (φ.symm S)).mp
        simpa only [φ.apply_symm_apply] using hv
    · rintro ⟨hne, F, hF, hdim, hu, hv⟩
      let S : FaceType P := ⟨F, hF⟩
      refine ⟨fun h ↦ hne ((vertexOrderEquiv φ).injective h),
        (φ S).val, (φ S).property, ?_, ?_, ?_⟩
      · exact (faceOrderIso_dimension φ S).trans hdim
      · exact (vertexOrderEquiv_mem_iff φ u S).mpr hu
      · exact (vertexOrderEquiv_mem_iff φ v S).mpr hv

theorem vertices_card_eq_of_faceOrderIso (φ : FaceType P ≃o FaceType Q) :
    P.vertices.card = Q.vertices.card := by
  simpa [VertexType] using Fintype.card_congr (vertexOrderEquiv φ)

end LeanEval.Geometry.PlatonicClassification
end
end VerificationSource037

/- Original source: Cubical/Polytope/PernoMonotono.lean -/
section VerificationSource038
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.PernoMonotono.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/



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
end VerificationSource038

/- Original source: Cubical/Polytope/OrbitaVertici.lean -/
section VerificationSource039
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.OrbitaVertici.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/




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
end VerificationSource039

/- Original source: Cubical/Polytope/Camminata.lean -/
section VerificationSource040
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.Camminata.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/


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
end VerificationSource040

/- Original source: Cubical/Polytope/BalinskiGenerale.lean -/

end -- global noncomputable section
end -- global public section
