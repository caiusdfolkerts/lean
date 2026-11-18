module
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.ConnettivitaGlobale.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/
public import Cubical.Polytope.Imports
public import Cubical.Polytope.Connettivita
public import Cubical.Polytope.DueVertici

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
