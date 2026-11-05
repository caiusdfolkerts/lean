module

public import PaperVerification.ToricEquivariantPullbacks
public import PaperVerification.ToricInvariantChartPrimes
public import PaperVerification.ToricInvariantCurveBounds
public import PaperVerification.ToricMonomialImageComparison
public import PaperVerification.ToricFanDimension
public import PaperVerification.ToricOrbitActions

@[expose] public section

/-!
# Actual invariant integral curves are orbit closures

An invariant integral closed subscheme meets a full affine chart.  Its
actual equivariant pullback has a prime monomial kernel, which is the
coordinate-face kernel.  This gives a common dense open subscheme with
the quotient-star orbit closure.  Equality of the two actual closed
immersion kernels then identifies the whole schemes.  Ordinary Krull
dimension, rather than a prescribed fan rank, forces the quotient fan
of a curve to have rank one.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

/-- The orbit-closure classification is derived from the actual action
on an arbitrary integral closed subscheme.  In particular the curve
need not be presented by an orbit or a fan wall. -/
theorem invariantIntegralCurve_isOrbitClosure (hpure : «Σ».IsPure)
    (C : InvariantIntegralCurve k n («Σ».fanSchemeOver k)) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
      (hF : I.image b ∈ «Σ».cones),
      ∃ e : C.curve ≅ («Σ».completeQuotientStarFan b I hF).fanSchemeOver k,
        e.hom.left ≫ «Σ».orbitClosureMap k b I hF = C.inclusion.left := by
  let G := splitTorusOver k (Lattice n)
  obtain ⟨s, hs⟩ := «Σ».fullChartOpen_cover k hpure
    (C.inclusion.left (genericPoint C.curve.left))
  let j : (coneChart k s.val).asOver (Spec (CommRingCat.of k)) ⟶ «Σ».fanSchemeOver k :=
    («Σ».fanChartMap k («Σ».fullConeIndex s)).asOver (Spec (CommRingCat.of k))
  letI : IsOpenImmersion j.left := by
    change IsOpenImmersion («Σ».fanChartMap k («Σ».fullConeIndex s))
    infer_instance
  letI : IsModHom G j := «Σ».fanChartMap_isModHom k («Σ».fullConeIndex s)
  let Y := pullback j C.inclusion
  let p : Y ⟶ (coneChart k s.val).asOver (Spec (CommRingCat.of k)) :=
    pullback.fst j C.inclusion
  let q : Y ⟶ C.curve := pullback.snd j C.inclusion
  letI : ModObj G Y := equivariantPullbackModObj G j C.inclusion
  letI : IsModHom G p := equivariantPullback_fst_isModHom G j C.inclusion
  letI : IsModHom G q := equivariantPullback_snd_isModHom G j C.inclusion
  letI : IsClosedImmersion p.left := overPullback_fst_isClosedImmersion j C.inclusion
  letI : IsOpenImmersion q.left := overPullback_snd_isOpenImmersion j C.inclusion
  letI : Nonempty Y.left := overPullback_nonempty j C.inclusion
    (genericPoint C.curve.left) hs
  letI : IsIntegral Y.left := isIntegral_of_isOpenImmersion q.left
  let b := «Σ».fullConeBasis s
  let p₀ : Y ⟶ monoidChartSchemeOver k (dualConeMonoid s.val) := p
  letI : IsClosedImmersion p₀.left := inferInstanceAs (IsClosedImmersion p.left)
  letI : IsModHom G p₀ := inferInstanceAs (IsModHom G p)
  obtain ⟨I, E, hE⟩ := invariant_integral_closed_fullChart_faceIso_of_basis
    k b s.val («Σ».fullConeBasis_ray_set s) Y p₀
  have hIs : I.image b ⊆ s.val := by
    rw [«Σ».fullConeBasis_ray_set s]
    exact Finset.image_subset_image (Finset.subset_univ I)
  have hF : I.image b ∈ «Σ».cones :=
    «Σ».downward s.val («Σ».fullCones_mem s) _ hIs
  let Γ := «Σ».completeQuotientStarFan b I hF
  let t : «Σ».OrbitConeIndex b I := ⟨s.val, «Σ».fullCones_mem s, hIs⟩
  let t₀ : Γ.ConeIndex := «Σ».orbitConeQuotientIndex b I hF t
  let U := coneChart k (orbitQuotientCone b I s.val)
  let a : U ⟶ C.curve.left := E.inv ≫ q.left
  let z : U ⟶ Γ.fanScheme k := Γ.fanChartMap k t₀
  let i : Γ.fanScheme k ⟶ «Σ».fanScheme k := «Σ».orbitClosureMap k b I hF
  let c : C.curve.left ⟶ «Σ».fanScheme k := C.inclusion.left
  let j₀ : coneChart k s.val ⟶ «Σ».fanScheme k := j.left
  let p₁ : Y.left ⟶ coneChart k s.val := p.left
  let f : U ⟶ coneChart k s.val := orbitQuotientChartMap k b I s.val hIs
  letI : IsClosedImmersion c := C.closed
  letI : IsIntegral U := Γ.coneChart_isIntegral k t₀
  letI : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion (E.inv ≫ q.left))
  letI : IsOpenImmersion z := inferInstanceAs (IsOpenImmersion (Γ.fanChartMap k t₀))
  letI : IsSchemeTheoreticallyDominant a := IsSchemeTheoreticallyDominant.of_isDominant a
  letI : IsSchemeTheoreticallyDominant z := IsSchemeTheoreticallyDominant.of_isDominant z
  letI : IsClosedImmersion i := inferInstanceAs
    (IsClosedImmersion («Σ».orbitClosureMap k b I hF))
  have hpq : p₁ ≫ j₀ = q.left ≫ c :=
    (overPullback_isPullback j C.inclusion).w
  have hE' : E.hom ≫ f = p₁ := hE
  have hinv : E.inv ≫ p₁ = f := by
    calc
      E.inv ≫ p₁ = E.inv ≫ (E.hom ≫ f) :=
        congrArg (fun q : Y.left ⟶ coneChart k s.val => E.inv ≫ q) hE'.symm
      _ = f := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hcommon : a ≫ c = z ≫ i := by
    calc
      a ≫ c = E.inv ≫ (q.left ≫ c) := Category.assoc E.inv q.left c
      _ = E.inv ≫ (p₁ ≫ j₀) :=
        congrArg (fun q : Y.left ⟶ «Σ».fanScheme k => E.inv ≫ q) hpq.symm
      _ = (E.inv ≫ p₁) ≫ j₀ := (Category.assoc E.inv p₁ j₀).symm
      _ = f ≫ j₀ := congrArg (fun q : U ⟶ coneChart k s.val => q ≫ j₀) hinv
      _ = z ≫ i := («Σ».orbitClosureMap_chart k b I hF t).symm
  let F := closedImageIsoOfDenseComposite a z c i hcommon
  have hFmap : F.hom ≫ i = c :=
    closedImageIsoOfDenseComposite_embedding a z c i hcommon
  have hiBase : i ≫ («Σ».fanSchemeOver k).hom = (Γ.fanSchemeOver k).hom :=
    comp_over («Σ».orbitClosureMap k b I hF) (Spec (CommRingCat.of k))
  have hbase : F.hom ≫ (Γ.fanSchemeOver k).hom = C.curve.hom := by
    calc
      F.hom ≫ (Γ.fanSchemeOver k).hom = F.hom ≫ (i ≫ («Σ».fanSchemeOver k).hom) :=
        congrArg (fun q : Γ.fanScheme k ⟶ Spec (CommRingCat.of k) => F.hom ≫ q) hiBase.symm
      _ = (F.hom ≫ i) ≫ («Σ».fanSchemeOver k).hom :=
        (Category.assoc F.hom i («Σ».fanSchemeOver k).hom).symm
      _ = c ≫ («Σ».fanSchemeOver k).hom :=
        congrArg (fun q : C.curve.left ⟶ «Σ».fanScheme k => q ≫ («Σ».fanSchemeOver k).hom) hFmap
      _ = C.curve.hom := C.inclusion.w
  exact ⟨b, I, hF, Over.isoMk F hbase, hFmap⟩

/-- Every genuine invariant integral curve is the projective line over
the original field.  The rank-one conclusion follows from the curve's
ordinary Krull dimension. -/
theorem invariantIntegralCurve_exists_projectiveLineIso (hpure : «Σ».IsPure)
    (C : InvariantIntegralCurve k n («Σ».fanSchemeOver k)) :
    ∃ e : C.curve.left ≅ projectiveLineScheme k,
      e.hom.IsOver (Spec (CommRingCat.of k)) := by
  obtain ⟨b, I, hF, e, he⟩ := «Σ».invariantIntegralCurve_isOrbitClosure k hpure C
  let Γ := «Σ».completeQuotientStarFan b I hF
  have hpureΓ : Γ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  have hdim : n-I.card = 1 := by
    have h := IsHomeomorph.topologicalKrullDim_eq _
      ((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom.homeomorph.isHomeomorph
    change topologicalKrullDim C.curve.left = topologicalKrullDim (Γ.fanScheme k) at h
    rw [C.dimension, Γ.fanScheme_topologicalKrullDim k hpureΓ] at h
    exact_mod_cast h.symm
  let e₀ := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  let e₁ := oneDimensionalFanSchemeIso Γ hdim k
  refine ⟨e₀ ≪≫ e₁, ?_⟩
  change (e.hom.left ≫ e₁.hom).IsOver (Spec (CommRingCat.of k))
  letI : e₁.hom.IsOver (Spec (CommRingCat.of k)) := inferInstanceAs
    ((oneDimensionalFanSchemeIso Γ hdim k).hom.IsOver (Spec (CommRingCat.of k)))
  refine ⟨?_⟩
  change (e.hom.left ≫ e₁.hom) ≫ (projectiveLineScheme k ↘ Spec (CommRingCat.of k)) =
    C.curve.hom
  exact (Category.assoc e.hom.left e₁.hom _).trans
    ((congrArg (fun q : Γ.fanScheme k ⟶ Spec (CommRingCat.of k) => e.hom.left ≫ q)
      (comp_over e₁.hom (Spec (CommRingCat.of k)))).trans e.hom.w)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.invariantIntegralCurve_isOrbitClosure
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.invariantIntegralCurve_exists_projectiveLineIso
