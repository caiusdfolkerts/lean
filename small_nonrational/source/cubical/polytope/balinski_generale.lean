module
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.BalinskiGenerale.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/
public import Cubical.Polytope.Imports
public import Cubical.Polytope.PernoMonotono
public import Cubical.Polytope.OrbitaVertici
public import Cubical.Polytope.ConoVertice
public import Cubical.Polytope.Camminata
public import Mathlib.Analysis.InnerProductSpace.Dual

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
