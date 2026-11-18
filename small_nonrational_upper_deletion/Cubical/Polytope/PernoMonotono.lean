module
/-
Adapted from SolarYs431/lean-eval-platonic-classification, original module Submission.PernoMonotono.
Copyright 2026 Daniele Cappello. Licensed under Apache-2.0.
Source provenance and adaptation details: THIRD_PARTY.md.
-/
public import Cubical.Polytope.Imports
public import Cubical.Polytope.Interpolazione

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
