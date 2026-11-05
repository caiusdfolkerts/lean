/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
See https://www.apache.org/licenses/LICENSE-2.0 for the license.

Parts adapted from the pinned openai/math proofs in Smooth/DimensionFormula,
Smooth/PointwiseDimension, and Smooth/FieldAffineChartDimension. The theorem
below uses only nonemptiness, and holds over every field. No integrality or
irreducibility assumption is added to the paper's geometric statement.
-/
module

public import PaperVerification.StandardSmoothKrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension

/-!
# Smooth relative dimension agrees with actual scheme dimension

The comparison uses the ordinary topological Krull dimension, defined through
chains of irreducible closed subsets. Local standard smooth presentations give
the upper bound on every chain. Any nonempty affine standard smooth chart
supplies the lower bound. Disconnected and reducible schemes are allowed.
-/

@[expose] public section
noncomputable section

universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace Order

namespace PaperVerification.SmoothSchemeKrullDimension

variable {X : Scheme.{u}}

theorem topologicalKrullDim_eq_orderKrullDim (X : Scheme.{u}) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

theorem affineOpen_orderKrullDim_eq_ringKrullDim (U : X.Opens) (hU : IsAffineOpen U) :
    Order.krullDim U = ringKrullDim Γ(X, U) := by
  calc
    Order.krullDim U = topologicalKrullDim U :=
      (topologicalKrullDim_eq_orderKrullDim U.toScheme).symm
    _ = topologicalKrullDim (PrimeSpectrum Γ(X, U)) :=
      hU.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
    _ = ringKrullDim Γ(X, U) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _

/-- A specialization chain lies in any open neighborhood of its least point. -/
theorem orderKrullDim_le_of_open_neighborhoods (X : Scheme.{u}) (d : ℕ)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Order.krullDim U ≤ (d : ℕ)) :
    Order.krullDim X ≤ (d : ℕ) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI := hX
      rw [Order.krullDim_eq_bot]
      exact bot_le
  | inr hX =>
      letI := hX
      rw [Order.krullDim_eq_iSup_length]
      refine WithBot.coe_le_coe.mpr (iSup_le fun l ↦ ?_)
      obtain ⟨U, hhead, hU⟩ := h l.head
      have hmem (i : Fin (l.length + 1)) : l i ∈ U := by
        have hle : l.head ≤ l i := l.monotone (Fin.zero_le i)
        rw [Scheme.le_iff_specializes] at hle
        exact hle.mem_open U.isOpen hhead
      have hlt (a b : U.toScheme) (hab : U.ι.base a < U.ι.base b) : a < b := by
        rw [lt_iff_le_not_ge]
        constructor
        · rw [Scheme.le_iff_specializes]
          apply U.isOpenEmbedding.isInducing.specializes_iff.mp
          rw [← Scheme.le_iff_specializes]
          exact hab.le
        · intro hback
          apply not_le_of_gt hab
          rw [Scheme.le_iff_specializes] at hback ⊢
          exact U.isOpenEmbedding.isInducing.specializes_iff.mpr hback
      let lU : LTSeries U :=
        { length := l.length
          toFun := fun i ↦ ⟨l i, hmem i⟩
          step := fun i ↦ by
            simpa only [Set.mem_ofPred_eq] using
              hlt (⟨l i.castSucc, hmem i.castSucc⟩ : U.toScheme)
                (⟨l i.succ, hmem i.succ⟩ : U.toScheme) (l.step i) }
      have hlength : (l.length : WithBot ℕ∞) ≤ Order.krullDim U :=
        Order.le_krullDim_iff.mpr ⟨lU, rfl⟩
      exact WithBot.coe_le_coe.mp (hlength.trans hU)

variable {K : Type u} [Field K] {d : ℕ}

/-- Over a field the affine target neighborhood in the definition of smooth
relative dimension is necessarily the whole field spectrum. -/
theorem exists_affine_field_chart (p : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension d p] (x : X) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U),
      RingHom.IsStandardSmoothOfRelativeDimension d
        ((p.appTop ≫ X.presheaf.map U.leTop.op).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) := by
  obtain ⟨V, _, U, hU, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := p) x
  have hV : V = ⊤ := by
    apply top_unique
    intro y _
    have hy : p x = y := Subsingleton.elim _ _
    exact hy ▸ e hx
  subst V
  have hzero : (Scheme.ΓSpecIso (.of K)).inv.hom.IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  refine ⟨U, hU, hx, ?_⟩
  have happ : p.appLE ⊤ U e = p.appTop ≫ X.presheaf.map U.leTop.op := rfl
  simpa only [Nat.add_zero, happ] using hstd.comp hzero

/-- Native smooth relative dimension bounds the actual topological dimension. -/
theorem topologicalKrullDim_le (p : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension d p] :
    topologicalKrullDim X ≤ (d : ℕ) := by
  rw [topologicalKrullDim_eq_orderKrullDim]
  apply orderKrullDim_le_of_open_neighborhoods X d
  intro x
  obtain ⟨U, hU, hx, hstd⟩ := exists_affine_field_chart (d := d) p x
  refine ⟨U, hx, ?_⟩
  rw [affineOpen_orderKrullDim_eq_ringKrullDim U hU]
  exact StandardSmoothKrullDimension.standardSmooth_ringKrullDim_le hstd

/-- A nonempty scheme smooth of relative dimension d over a field has
topological Krull dimension exactly d, without an irreducibility assumption. -/
theorem topologicalKrullDim_eq [Nonempty X] (p : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension d p] : topologicalKrullDim X = (d : ℕ) := by
  apply le_antisymm (topologicalKrullDim_le (d := d) p)
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hU, hx, hstd⟩ := exists_affine_field_chart (d := d) p x
  letI : Nonempty U := ⟨⟨x, hx⟩⟩
  have hUdim : topologicalKrullDim U = (d : ℕ) := by
    rw [topologicalKrullDim_eq_orderKrullDim U.toScheme,
      affineOpen_orderKrullDim_eq_ringKrullDim U hU]
    exact StandardSmoothKrullDimension.standardSmooth_ringKrullDim_eq hstd
  rw [← hUdim]
  exact topologicalKrullDim_subspace_le X (U : Set X)

end PaperVerification.SmoothSchemeKrullDimension
