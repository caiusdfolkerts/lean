module

public import Continuation.CycleBounds.WallDegrees
public import Continuation.Divisor.InvariantCurves
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.FanPurity

@[expose] public section

/-! # Proposition6.8 for every intrinsic invariant integral curve

The input curve is an arbitrary integral closed equivariant curve scheme. The
recovered orbit-closure classification, its ordinary Krull dimension, and the
actual pullback comparison reduce it to a wall curve. No wall presentation is
assumed for the input curve.
-/

noncomputable section
universe u
namespace PaperVerification.ToricGeometry
open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
attribute [local instance] Classical.propDecidable

/-- Ordinary rational-curve degree is preserved by pullback along an actual
isomorphism over the original field. -/
theorem rationalCurveHasDegree_pullbackIso (k : Type u) [Field k]
    {C D : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    [D.Over (Spec (CommRingCat.of k))] (e : C ≅ D)
    [e.hom.IsOver (Spec (CommRingCat.of k))]
    (M : D.Modules) (d : ℤ) (hd : RationalCurveHasDegree k M d) :
    RationalCurveHasDegree k ((Scheme.Modules.pullback e.hom).obj M) d := by
  obtain ⟨f, hf, hfd⟩ := hd
  letI := hf
  let g := e ≪≫ f
  have heq : g.inv ≫ e.hom = f.inv := by
    simp [g, Category.assoc]
  let J : (Scheme.Modules.pullback g.inv).obj ((Scheme.Modules.pullback e.hom).obj M) ≅
      (Scheme.Modules.pullback f.inv).obj M :=
    (Scheme.Modules.pullbackComp g.inv e.hom).app M ≪≫
      (Scheme.Modules.pullbackCongr heq).app M
  have hg : g.hom.IsOver (Spec (CommRingCat.of k)) := by
    change (e.hom ≫ f.hom).IsOver (Spec (CommRingCat.of k))
    infer_instance
  exact ⟨g, hg, (projectiveLineHasDegree_iso k J d).mpr hfd⟩

namespace SmoothCompleteFan
open Unimodular.CycleBounds Unimodular.SeriesParallel
variable {n : ℕ} (F : SmoothCompleteFan n) (k : Type u) [Field k]

/-- The positive Thomsen coefficients change by the actual integral character
pairings when a lift of a torus stratum is translated. -/
theorem thomsenCoefficients_add_lattice (θ : Module.Dual ℝ (Ambient n))
    (m u : Lattice n) :
    F.thomsenCoefficients (θ + dotProductEquiv ℝ (Fin n) (embed n m)) u =
      F.thomsenCoefficients θ u + integerPairing u m := by
  have hp : dotProductEquiv ℝ (Fin n) (embed n m) (embed n u) =
      (integerPairing u m : ℝ) := by
    change dotProduct (embed n m) (embed n u) = _
    rw [dotProduct_comm]
    exact normalRay_pairing_lattice u m
  change ⌈θ (embed n u) + dotProductEquiv ℝ (Fin n) (embed n m) (embed n u)⌉ = _
  rw [hp, Int.ceil_add_intCast]
  rfl

/-- Changing the lift of a stratum gives an actual principal change of the
Cartier sheaf, so the positive Thomsen line bundle descends to the torus. -/
theorem thomsenCartier_add_lattice (θ : Module.Dual ℝ (Ambient n)) (m : Lattice n) :
    (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).LinearlyEquivalent
      (F.fanCartierData k F.isPure
        (F.thomsenCoefficients (θ + dotProductEquiv ℝ (Fin n) (embed n m)))) := by
  apply F.fanCartierData_characterTranslation k F.isPure
    (F.thomsenCoefficients θ)
    (F.thomsenCoefficients (θ + dotProductEquiv ℝ (Fin n) (embed n m))) (-m)
  intro u _
  rw [F.thomsenCoefficients_add_lattice]
  simp only [integerPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]

/-- The ordinary intersection number is independent of the integral translate
chosen to lift an arrangement stratum of the real torus. -/
theorem thomsen_invariantCurve_degree_add_lattice
    (θ : Module.Dual ℝ (Ambient n)) (m : Lattice n)
    (C : InvariantIntegralCurve k n (F.fanSchemeOver k)) (d : ℤ) :
    RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf) d ↔
    RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (F.fanCartierData k F.isPure
          (F.thomsenCoefficients (θ + dotProductEquiv ℝ (Fin n) (embed n m)))).sheaf) d := by
  obtain ⟨e⟩ := F.thomsenCartier_add_lattice k θ m
  exact rationalCurveHasDegree_iso k
    ((Scheme.Modules.pullback C.inclusion.left).mapIso e) d

/-- Every genuine invariant integral curve is one of the actual wall curves,
up to an isomorphism commuting with its inclusion in the original fan scheme. -/
theorem invariantIntegralCurve_wallIso
    (C : InvariantIntegralCurve k n (F.fanSchemeOver k)) :
    ∃ (s : F.fullCones) (j : Fin n), ∃ e : C.curve.left ≅ F.wallCurve s j k,
      e.hom.IsOver (Spec (CommRingCat.of k)) ∧
      e.hom ≫ F.wallCurveInclusion s j k = C.inclusion.left := by
  classical
  obtain ⟨s, I, hI, e, he⟩ := F.invariantIntegralCurve_isOrbitClosure_fullCone k F.isPure C
  let Γ := F.completeQuotientStarFan (F.fullConeBasis s) I hI
  have hΓpure : Γ.IsPure := F.completeQuotientStarFan_isPure F.isPure (F.fullConeBasis s) I hI
  have hdim : n - I.card = 1 := by
    have h := IsHomeomorph.topologicalKrullDim_eq _
      ((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom.homeomorph.isHomeomorph
    change topologicalKrullDim C.curve.left = topologicalKrullDim (Γ.fanScheme k) at h
    rw [C.dimension, Γ.fanScheme_topologicalKrullDim k hΓpure] at h
    exact_mod_cast h.symm
  have hex : ∃ j : Fin n, j ∉ I := by
    by_contra hn
    push_neg at hn
    have hfull : I = Finset.univ := Finset.eq_univ_iff_forall.mpr hn
    rw [hfull, Finset.card_fin] at hdim
    omega
  obtain ⟨j, hj⟩ := hex
  have hIeq : I = Finset.univ.erase j := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      exact Finset.mem_erase.mpr ⟨fun hij ↦ hj (hij ▸ hi), Finset.mem_univ i⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
      omega
  subst I
  let e' : C.curve.left ≅ F.wallCurve s j k :=
    (Over.forget (Spec (CommRingCat.of k))).mapIso e
  refine ⟨s, j, e', ?_, ?_⟩
  · change e.hom.left.IsOver (Spec (CommRingCat.of k))
    infer_instance
  · exact he

/-- Proposition6.8: the actual restricted Thomsen line bundle on every intrinsic
invariant integral curve has an ordinary degree at most the geometric stratum
dimension. The fan is smooth and complete; projectivity is not assumed. -/
theorem thomsen_invariantCurve_degree_bound {V : Type*} [Fintype V]
    (G : IncidenceGraph V F.rays) (hG : G.edges = Set.univ) (hK : ¬G.HasK4Minor)
    (δ : Lattice n →ₗ[ℤ] (V → ℤ)) (hinj : Function.Injective δ)
    (hδ : ∀ u : F.rays, δ u.val = Pi.single (G.source u) 1 - Pi.single (G.target u) 1)
    (θ : Module.Dual ℝ (Ambient n))
    (C : InvariantIntegralCurve k n (F.fanSchemeOver k)) :
    ∃ d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf) d ∧
      d ≤ (F.thomsenStratumDimension θ : ℤ) := by
  obtain ⟨s, j, e, heOver, he⟩ := F.invariantIntegralCurve_wallIso k C
  letI := heOver
  obtain ⟨t, w, ht, hwj, _, _, _⟩ := F.exists_full_opposite_wall F.isPure s j
  obtain ⟨d, hd, hbound⟩ := F.thomsen_wallCurve_degree_bound G hG hK δ hinj hδ k
    F.isPure θ s j t w ht hwj
  have hd' := ((F.wallCurveFan s j).oneDimensionalHasDegree_iff_rationalCurve k
    (F.wallIndices_codimension s j) _ d).mp hd
  let M := (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf
  let J : (Scheme.Modules.pullback e.hom).obj
      ((Scheme.Modules.pullback (F.wallCurveInclusion s j k)).obj M) ≅
        (Scheme.Modules.pullback C.inclusion.left).obj M :=
    (Scheme.Modules.pullbackComp e.hom (F.wallCurveInclusion s j k)).app M ≪≫
      (Scheme.Modules.pullbackCongr he).app M
  exact ⟨d, (rationalCurveHasDegree_iso k J d).mp
    (rationalCurveHasDegree_pullbackIso k e _ d hd'), hbound⟩

/-- The same bound for any degree witness; uniqueness prevents the choice of
curve coordinates or of an isomorphism with the projective line from mattering. -/
theorem thomsen_invariantCurve_every_degree_bound {V : Type*} [Fintype V]
    (G : IncidenceGraph V F.rays) (hG : G.edges = Set.univ) (hK : ¬G.HasK4Minor)
    (δ : Lattice n →ₗ[ℤ] (V → ℤ)) (hinj : Function.Injective δ)
    (hδ : ∀ u : F.rays, δ u.val = Pi.single (G.source u) 1 - Pi.single (G.target u) 1)
    (θ : Module.Dual ℝ (Ambient n))
    (C : InvariantIntegralCurve k n (F.fanSchemeOver k)) (d : ℤ)
    (hd : RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf) d) :
    d ≤ (F.thomsenStratumDimension θ : ℤ) := by
  obtain ⟨e, he, hbound⟩ := F.thomsen_invariantCurve_degree_bound k G hG hK δ hinj hδ θ C
  rwa [rationalCurveHasDegree_unique k hd he]

#print axioms thomsen_invariantCurve_every_degree_bound
end SmoothCompleteFan
end PaperVerification.ToricGeometry
