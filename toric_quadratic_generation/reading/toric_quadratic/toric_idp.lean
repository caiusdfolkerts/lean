module
public import PaperVerification.ToricDilations
public import PaperVerification.ToricBoundary
@[expose] public section
/-!
# Induction in the full integer-decomposition degree and face dimension

Interior targets use the actual Lemma 4.2 construction. Boundary targets use
integer decomposition on their actual proper faces, with no degree restriction.
The second theorem packages the remaining dimension induction through saturated
integral affine face charts.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped Pointwise
open PaperVerification.ToricExchange

namespace LatticePolytope

/-- Lowering a geometric edge-length bound preserves its meaning. -/
theorem edgesAtLeast_mono {n : ℕ} (P : LatticePolytope n) {a b : ℕ}
    (hP : P.EdgesAtLeast b) (hab : a ≤ b) : P.EdgesAtLeast a := by
  intro v w hvw
  obtain ⟨vZ, wZ, hvZ, hwZ, hlen⟩ := hP v w hvw
  exact ⟨vZ, wZ, hvZ, hwZ, hab.trans hlen⟩

/-- The full all-degree induction: actual interior splitting plus integer
decomposition on proper faces imply integer decomposition of the whole polytope. -/
theorem idp_of_boundary_faces {n : ℕ} (P : LatticePolytope n)
    (hP : P.Smooth) (hlP : P.EdgesAtLeast n)
    (hfaces : ∀ F : Set (Ambient n), F.Nonempty → Convex ℝ F →
      IsExtreme ℝ P.carrier F → F ≠ P.carrier →
      IntegerDecompositionProperty (embed n) F) :
    P.HasIDP := by
  change IntegerDecompositionProperty (embed n) P.carrier
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk z hz
    obtain ⟨x, hx, hz⟩ := hz
    by_cases hkone : k = 1
    · subst k
      have hzP : embed n z ∈ P.carrier := by rw [hz]; simpa using hx
      exact ⟨{⟨z, hzP⟩}, by simp, by simp⟩
    · have hprev : 0 < k - 1 := by omega
      have hprevlt : k - 1 < k := by omega
      have hprevadd : k - 1 + 1 = k := by omega
      by_cases hint : x ∈ interior P.carrier
      · have hm : embed n z ∈ interior (P.minkowskiSum (P.dilate (k - 1) hprev)) := by
          rw [P.minkowskiSum_dilate, hprevadd]
          have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
          rw [interior_smul₀ hkR]
          exact ⟨x, hint, hz.symm⟩
        obtain ⟨a, b, ha, hb, hab⟩ := P.interior_lattice_decomposition
          (P.dilate (k - 1) hprev) hP (P.smooth_dilate hP (k - 1) hprev)
          (P.sameNormalFan_dilate (k - 1) hprev) hlP
          (P.edgesAtLeast_dilate hlP (k - 1) hprev) z hm
        rw [P.carrier_dilate] at hb
        obtain ⟨y, hy, hyb⟩ := hb
        obtain ⟨s, hcard, htotal⟩ := ih (k - 1) hprevlt (by omega) b ⟨y, hy, hyb.symm⟩
        refine ⟨⟨a, ha⟩ ::ₘ s, ?_, ?_⟩
        · simpa only [Multiset.card_cons, hcard, hprevadd]
        · simpa only [total_cons, htotal] using hab
      · obtain ⟨F, hxF, hFc, hFP, hFproper⟩ := P.boundary_proper_face x hx hint
        obtain ⟨s, hcard, htotal⟩ := hfaces F ⟨x, hxF⟩ hFc hFP hFproper
          k hk z ⟨x, hxF, hz⟩
        let inc : latticePoints (embed n) F → latticePoints (embed n) P.carrier :=
          fun a => ⟨a, hFP.subset a.property⟩
        refine ⟨s.map inc, ?_, ?_⟩
        · simpa only [Multiset.card_map] using hcard
        · have hsum : total (latticePoints (embed n) P.carrier) (s.map inc) =
              total (latticePoints (embed n) F) s := by
            simp only [total, Multiset.map_map]
            rfl
          exact hsum.trans htotal

/-- Dimension induction transfers the exact edge threshold to every saturated
proper face. This theorem is the induction principle; its chart hypothesis must
be supplied by the separate face-inheritance construction. -/
theorem idp_of_smooth_face_charts
    (hcharts : ∀ n : ℕ, ∀ P : LatticePolytope n,
      P.Smooth → P.EdgesAtLeast n → ∀ F : Set (Ambient n),
      F.Nonempty → Convex ℝ F → IsExtreme ℝ P.carrier F → F ≠ P.carrier →
      ∃ (d : ℕ) (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n),
        d < n ∧ Q.Smooth ∧ Q.EdgesAtLeast n ∧ e.realMap '' Q.carrier = F) :
    ∀ n : ℕ, ∀ P : LatticePolytope n, P.Smooth → P.EdgesAtLeast n → P.HasIDP := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hP hlP
    apply P.idp_of_boundary_faces hP hlP
    intro F hFne hFc hFP hFproper
    obtain ⟨d, Q, e, hdn, hQ, hlQ, heQ⟩ := hcharts n P hP hlP F hFne hFc hFP hFproper
    have hQidp := ih d hdn Q hQ (Q.edgesAtLeast_mono hlQ hdn.le)
    have h := e.integerDecompositionProperty_image Q.carrier hQidp
    simpa only [heQ] using h

end LatticePolytope

end PaperVerification.ToricGeometry
