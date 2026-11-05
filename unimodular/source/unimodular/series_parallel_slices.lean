module

public import Unimodular.SeriesParallelFanObstructions

@[expose] public section

open scoped BigOperators Pointwise Topology
open Set TauCeti.Toric

namespace Unimodular.SeriesParallel

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Contract precisely the basis coordinates outside the indicated distinct rows. -/
def deletedOutside {k : ℕ} (r : Fin k ↪ I) : Finset I :=
  Finset.univ \ Finset.univ.map r

/-- The surviving coordinate labels are exactly the selected labels, with their
original ordering retained. -/
def survivorEquiv {k : ℕ} (r : Fin k ↪ I) :
    Fin k ≃ {i : I // i ∉ deletedOutside r} :=
  Equiv.ofBijective (fun j => ⟨r j, by simp [deletedOutside]⟩) (by
    constructor
    · intro i j h
      exact r.injective (congrArg Subtype.val h)
    · intro i
      have hi : i.val ∈ Finset.univ.map r := by
        simpa [deletedOutside] using i.property
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi
      exact ⟨j, Subtype.ext hj⟩)

/-- The exact standard integral basis in the surviving ordered coordinates. -/
def sliceBasis {k : ℕ} (r : Fin k ↪ I) :
    Module.Basis (Fin k) ℤ ({i : I // i ∉ deletedOutside r} → ℤ) :=
  (Pi.basisFun ℤ _).reindex (survivorEquiv r).symm

@[simp] theorem sliceBasis_repr_projection {k : ℕ} {N : Type*}
    [AddCommGroup N] [Module ℤ N] (b : Module.Basis I ℤ N)
    (r : Fin k ↪ I) (u : N) (j : Fin k) :
    (sliceBasis r).repr (CoordinateQuotients.projection b (deletedOutside r) u) j =
      b.repr u (r j) := by
  rw [sliceBasis, Module.Basis.repr_reindex_apply]
  rfl

@[simp] theorem sliceBasis_image {k : ℕ} {N : Type*}
    [AddCommGroup N] [Module ℤ N] (b : Module.Basis I ℤ N)
    (r : Fin k ↪ I) (j : Fin k) :
    CoordinateQuotients.projection b (deletedOutside r) (b (r j)) = sliceBasis r j := by
  apply (sliceBasis r).repr.injective
  ext i
  rw [sliceBasis_repr_projection, Module.Basis.repr_self_apply,
    Module.Basis.repr_self_apply]
  simp only [r.injective.eq_iff]

lemma slice_projection_ne_zero {k : ℕ} {N : Type*}
    [AddCommGroup N] [Module ℤ N] (b : Module.Basis I ℤ N)
    (r : Fin k ↪ I) (u : N) (j : Fin k) (hj : b.repr u (r j) ≠ 0) :
    CoordinateQuotients.projection b (deletedOutside r) u ≠ 0 := by
  intro h
  apply hj
  rw [← sliceBasis_repr_projection b r u j, h]
  simp

variable {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : N →+ V}

/-- Any selected basis-coordinate slice is realized by the exact actual fan
quotient; all selected basis vectors remain primitive rays. -/
theorem exists_coordinate_slice (Φ : Fan ι)
    (hcomplete : Φ.IsComplete) (hregular : Φ.IsRegular)
    (hcriterion : ConeBases.PositiveCriterion Φ)
    (b : Module.Basis I ℤ N) (hb : ∀ i, ConeBases.IsRay Φ (b i))
    {k : ℕ} (r : Fin k ↪ I) :
    ∃ Ψ : Fan (CoordinateQuotients.quotientEmbedding (deletedOutside r)),
      Ψ.IsComplete ∧ Ψ.IsRegular ∧ ConeBases.PositiveCriterion Ψ ∧
      (∀ j, ConeBases.IsRay Ψ (sliceBasis r j)) ∧
      ∀ u, ConeBases.IsRay Φ u →
        CoordinateQuotients.projection b (deletedOutside r) u ≠ 0 →
        ConeBases.IsRay Ψ (CoordinateQuotients.projection b (deletedOutside r) u) := by
  obtain ⟨Ψ, hc, hr, hp, hΨrays⟩ :=
    RayContractions.exists_coordinate_contraction Φ hcomplete hregular hcriterion b
      (deletedOutside r) (fun i _ => hb i)
  refine ⟨Ψ, hc, hr, hp, ?_, ?_⟩
  · intro j
    exact (hΨrays _).mpr ⟨b (r j), hb (r j), sliceBasis_image b r j,
      (sliceBasis r).ne_zero j⟩
  · intro u hu hn
    exact (hΨrays _).mpr ⟨u, hu, rfl, hn⟩

/-- No six-cycle support pattern can occur on any three selected rows of an
arbitrary-rank ray basis. The other coordinates of all rays are unrestricted. -/
theorem fan_no_triangle_rows (Φ : Fan ι)
    (hcomplete : Φ.IsComplete) (hregular : Φ.IsRegular)
    (hcriterion : ConeBases.PositiveCriterion Φ)
    (b : Module.Basis I ℤ N) (hb : ∀ i, ConeBases.IsRay Φ (b i))
    (r : Fin 3 ↪ I) (v₀ v₁ v₂ : N)
    (hv₀ : ConeBases.IsRay Φ v₀) (hv₁ : ConeBases.IsRay Φ v₁)
    (hv₂ : ConeBases.IsRay Φ v₂)
    (hs₀ : ∀ i, b.repr v₀ (r i) ≠ 0 ↔ i = 0 ∨ i = 1)
    (hs₁ : ∀ i, b.repr v₁ (r i) ≠ 0 ↔ i = 0 ∨ i = 2)
    (hs₂ : ∀ i, b.repr v₂ (r i) ≠ 0 ↔ i = 1 ∨ i = 2) : False := by
  obtain ⟨Ψ, hc, hr, hp, hb', hmap⟩ :=
    exists_coordinate_slice Φ hcomplete hregular hcriterion b hb r
  let q := CoordinateQuotients.projection b (deletedOutside r)
  apply fan_no_triangle_support Ψ hc hr hp (sliceBasis r) hb' (q v₀) (q v₁) (q v₂)
  · exact hmap v₀ hv₀ (slice_projection_ne_zero b r v₀ 0 ((hs₀ 0).mpr (Or.inl rfl)))
  · exact hmap v₁ hv₁ (slice_projection_ne_zero b r v₁ 0 ((hs₁ 0).mpr (Or.inl rfl)))
  · exact hmap v₂ hv₂ (slice_projection_ne_zero b r v₂ 1 ((hs₂ 1).mpr (Or.inl rfl)))
  · intro i
    simpa [q] using hs₀ i
  · intro i
    simpa [q] using hs₁ i
  · intro i
    simpa [q] using hs₂ i

/-- No induced domino support pattern can occur on any three selected rows of
an arbitrary-rank ray basis. This is the full minor argument, not a rank bound
on the original fan. -/
theorem fan_no_domino_rows (Φ : Fan ι)
    (hcomplete : Φ.IsComplete) (hregular : Φ.IsRegular)
    (hcriterion : ConeBases.PositiveCriterion Φ)
    (b : Module.Basis I ℤ N) (hb : ∀ i, ConeBases.IsRay Φ (b i))
    (r : Fin 3 ↪ I) (v₀ v₁ v₂ : N)
    (hv₀ : ConeBases.IsRay Φ v₀) (hv₁ : ConeBases.IsRay Φ v₁)
    (hv₂ : ConeBases.IsRay Φ v₂)
    (hs₀ : ∀ i, b.repr v₀ (r i) ≠ 0 ↔ i = 0 ∨ i = 1)
    (hs₁ : ∀ i, b.repr v₁ (r i) ≠ 0)
    (hs₂ : ∀ i, b.repr v₂ (r i) ≠ 0 ↔ i = 1 ∨ i = 2) : False := by
  obtain ⟨Ψ, hc, hr, hp, hb', hmap⟩ :=
    exists_coordinate_slice Φ hcomplete hregular hcriterion b hb r
  let q := CoordinateQuotients.projection b (deletedOutside r)
  apply fan_no_domino_support Ψ hc hr hp (sliceBasis r) hb' (q v₀) (q v₁) (q v₂)
  · exact hmap v₀ hv₀ (slice_projection_ne_zero b r v₀ 0 ((hs₀ 0).mpr (Or.inl rfl)))
  · exact hmap v₁ hv₁ (slice_projection_ne_zero b r v₁ 0 (hs₁ 0))
  · exact hmap v₂ hv₂ (slice_projection_ne_zero b r v₂ 1 ((hs₂ 1).mpr (Or.inl rfl)))
  · intro i
    simpa [q] using hs₀ i
  · intro i
    simpa [q] using hs₁ i
  · intro i
    simpa [q] using hs₂ i

#print axioms Unimodular.SeriesParallel.fan_no_triangle_rows
#print axioms Unimodular.SeriesParallel.fan_no_domino_rows

end
end Unimodular.SeriesParallel
