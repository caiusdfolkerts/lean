/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ConnettivitaRidgeRiduzione.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/
import cubical.polytope.imports
import cubical.polytope.connettivita_ridge_tre
import cubical.polytope.bandiera_vertice
import cubical.polytope.interpolazione

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
