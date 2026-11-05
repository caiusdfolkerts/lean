/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ConnettivitaRidgeBase.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/
import cubical.polytope.imports
import cubical.polytope.connettivita_globale
import cubical.polytope.poligono_connesso

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
