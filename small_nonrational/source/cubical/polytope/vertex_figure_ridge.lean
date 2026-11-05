module
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.VertexFigureRidge.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/
public import Cubical.Polytope.Imports
public import Cubical.Polytope.ConnettivitaRidgeRiduzione

@[expose] public section

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
