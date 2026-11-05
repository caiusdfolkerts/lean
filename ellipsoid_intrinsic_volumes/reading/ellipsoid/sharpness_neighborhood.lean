module

public import Ellipsoid.FixedVolumeSharpness
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# The literal sphere neighbourhood in the sharpness assertion

For a sphere every permutation of its semiaxes is the same constant list.
Thus the coordinate neighbourhood used by the constructive sharpness proofs
is exactly the neighbourhood for the manuscript's unordered-axis distance.
These are equivalences for the actual distance, not alternative definitions.
-/

noncomputable section

namespace EllipsoidVerification

theorem FullEllipsoid.axisDistance_sphere {n : ℕ} (E : FullEllipsoid n)
    (r : ℝ) (hr : 0 < r) :
    E.axisDistance (FullEllipsoid.sphere n r hr) =
      ⨆ i : Fin n, |E.semiaxis i - r| := by
  simp [FullEllipsoid.axisDistance, FullEllipsoid.sphere]

theorem FullEllipsoid.axisDistance_sphere_lt_iff {n : ℕ} (hn : 0 < n)
    (E : FullEllipsoid n) (r : ℝ) (hr : 0 < r) (δ : ℝ) :
    E.axisDistance (FullEllipsoid.sphere n r hr) < δ ↔
      ∀ i, |E.semiaxis i - r| < δ := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [E.axisDistance_sphere]
  constructor
  · intro h i
    exact (le_ciSup (Set.finite_range _).bddAbove i).trans_lt h
  · intro h
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun i : Fin n => |E.semiaxis i - r|) Finset.univ_nonempty
    exact (ciSup_le (fun i => hmax i (Finset.mem_univ i))).trans_lt (h j)

/-- The sharpness witnesses lie in every open ball about the prescribed
sphere for the exact unordered-axis distance printed in Theorem 1.2. -/
theorem sharp_holder_recovery_near_sphere
    (n : ℕ) (hn : 0 < n) (a b r : ℝ) (ha : 0 < a) (har : a < r) (hrb : r < b)
    (γ : ℝ) (hγ : 1 / (n : ℝ) < γ) (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ E F : FullEllipsoid n,
      E.axesIn a b ∧ F.axesIn a b ∧
      E.axisDistance (FullEllipsoid.sphere n r (ha.trans har)) < δ ∧
      F.axisDistance (FullEllipsoid.sphere n r (ha.trans har)) < δ ∧
      C * Real.rpow (E.volumeDistance F) γ < E.axisDistance F := by
  obtain ⟨E, F, hE, hF, hEr, hFr, hbad⟩ :=
    sharp_holder_recovery n hn a b r ha har hrb γ hγ δ C hδ hC
  exact ⟨E, F, hE, hF,
    (E.axisDistance_sphere_lt_iff hn r (ha.trans har) δ).mpr hEr,
    (F.axisDistance_sphere_lt_iff hn r (ha.trans har) δ).mpr hFr, hbad⟩

/-- The same literal sphere neighbourhood for the equal-volume clause. -/
theorem sharp_holder_recovery_at_fixed_volume_near_sphere
    (n : ℕ) (hn : 2 ≤ n) (a b r : ℝ) (ha : 0 < a) (har : a < r) (hrb : r < b)
    (γ : ℝ) (hγ : 1 / (n : ℝ) < γ) (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ E F : FullEllipsoid n,
      E.axesIn a b ∧ F.axesIn a b ∧
      E.axisDistance (FullEllipsoid.sphere n r (ha.trans har)) < δ ∧
      F.axisDistance (FullEllipsoid.sphere n r (ha.trans har)) < δ ∧
      E.volume n = F.volume n ∧
      C * Real.rpow (E.volumeDistance F) γ < E.axisDistance F := by
  have hn0 : 0 < n := by omega
  obtain ⟨E, F, hE, hF, hEr, hFr, hvolume, hbad⟩ :=
    sharp_holder_recovery_at_fixed_volume n hn a b r ha har hrb γ hγ δ C hδ hC
  exact ⟨E, F, hE, hF,
    (E.axisDistance_sphere_lt_iff hn0 r (ha.trans har) δ).mpr hEr,
    (F.axisDistance_sphere_lt_iff hn0 r (ha.trans har) δ).mpr hFr, hvolume, hbad⟩

end EllipsoidVerification
