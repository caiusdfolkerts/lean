/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ConnettivitaRidgeTre.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/
import cubical.polytope.imports
import cubical.polytope.connettivita_ridge_base
import cubical.polytope.balinski_generale
import cubical.polytope.faccette_connesse

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
