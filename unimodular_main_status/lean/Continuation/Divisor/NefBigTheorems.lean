module

public import Continuation.Divisor.WeilCurveDegree

/-!
# Ordinary nefness of the intrinsic anticanonical line bundle

The degree is the residue-degree-weighted degree of a genuine Cartier
presentation on each proper integral curve. Independence of the rational
section is proved using the norm/order formula and principal degree zero.
A nonzero global section gives an effective zero divisor. This proves
nefness on all proper integral test curves, including singular curves,
without a Riemann–Roch or cohomology-finiteness assumption.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u

namespace Unimodular.NefBig
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open PaperVerification.ToricSchemes PaperVerification.ToricGeometry

section Generation
variable {X Y : Scheme.{u}}

/-- Ordinary global generation survives every actual sheaf pullback. -/
theorem isGloballyGenerated_pullback (f : X ⟶ Y) (L : InvertibleSheaf Y)
    (hL : L.IsGloballyGenerated) :
    ((InvertibleSheaf.pullback f).obj L).IsGloballyGenerated := by
  letI : Limits.PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  obtain ⟨G⟩ := hL.nonempty_generatingSections
  apply InvertibleSheaf.isGloballyGenerated_iff_nonempty_generatingSections.mpr
  exact ⟨G.map (Scheme.Modules.pullback f) (Scheme.Modules.pullbackObjUnitIso f).symm⟩

theorem nonzero_section_of_isGloballyGenerated [IsIntegral X]
    (L : InvertibleSheaf X) (hL : L.IsGloballyGenerated) :
    ∃ s : Γ(L.obj, ⊤), s ≠ 0 := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨s, hs⟩ := InvertibleSheaf.isGloballyGenerated_iff.mp hL x
  refine ⟨s, ?_⟩
  intro hzero
  rw [hzero, Scheme.Modules.nonvanishingLocus_zero] at hs
  exact hs
end Generation

section Curves
variable (k : Type u) [Field k] {X : Scheme.{u}}

/-- Nonnegative ordinary degree on every proper integral curve mapping
to the scheme. The curve need not be smooth, regular, or geometrically
integral. Noetherianity is derived from properness over the field. -/
def IsNefOnCurves (L : InvertibleSheaf X) : Prop :=
  ∀ (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] [IsIntegral C]
    [IsProper (C ↘ Spec (CommRingCat.of k))],
    ∀ hdim : topologicalKrullDim C = 1, ∀ f : C ⟶ X,
      letI : IsNoetherian C := Intersection.properFieldScheme_isNoetherian
        (C ↘ Spec (CommRingCat.of k))
      0 ≤ Intersection.lineBundleDegree (C ↘ Spec (CommRingCat.of k)) hdim.le
        ((InvertibleSheaf.pullback f).obj L).obj

/-- A nonzero global section supplies the effective Cartier zero divisor
whose ordinary degree proves nefness. -/
theorem isNefOnCurves_of_isGloballyGenerated (L : InvertibleSheaf X)
    (hL : L.IsGloballyGenerated) : IsNefOnCurves k L := by
  intro C hbase hintegral hproper hdim f
  letI : IsNoetherian C := Intersection.properFieldScheme_isNoetherian
    (C ↘ Spec (CommRingCat.of k))
  obtain ⟨s, hs⟩ := nonzero_section_of_isGloballyGenerated
    ((InvertibleSheaf.pullback f).obj L) (isGloballyGenerated_pullback f L hL)
  exact Intersection.lineBundleDegree_nonneg_of_nonzero_globalSection
    (C ↘ Spec (CommRingCat.of k)) hdim.le _ s hs

/-- In particular, the ordinary definition testing every proper integral
closed curve in the scheme holds. This comparison is literal. -/
theorem isNef_of_isNefOnCurves [X.Over (Spec (CommRingCat.of k))]
    (L : InvertibleSheaf X) (hL : IsNefOnCurves k L) :
    AlgebraicGeometry.IsNef (baseField := k) L.obj := by
  intro C
  exact hL C.carrier C.dim_eq_one C.ι
end Curves

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]

/-- The weak-Fano numerical conclusion concerns the actual dual of the
top universal Kähler exterior bundle and the actual section spaces. -/
theorem anticanonical_nef_and_big_of_support (h : F.IsNef (fun _ => 1)) :
    IsNefOnCurves k (anticanonicalLineBundle F k) ∧
      IsBig k (anticanonicalLineBundle F k).obj :=
  ⟨isNefOnCurves_of_isGloballyGenerated k _
      (anticanonical_isGloballyGenerated_of_support F k h),
    anticanonical_isBig F k⟩

/-- The nef-and-big clause of Theorem 7.1 in every rank and over every
field, for every smooth complete fan on the full type-A root system.
Projectivity is not an extra hypothesis. -/
theorem theorem_7_1_anticanonical_nef_and_big
    (hroots : Unimodular.TypeABoundary.HasTypeARays F) :
    Smooth (F.fanScheme k ↘ Spec (CommRingCat.of k)) ∧
      topologicalKrullDim (F.fanScheme k) = n ∧
      IsNefOnCurves k (anticanonicalLineBundle F k) ∧
      IsBig k (anticanonicalLineBundle F k).obj :=
  ⟨fanScheme_smooth F k, F.fanScheme_topologicalKrullDim k F.isPure,
    anticanonical_nef_and_big_of_support F k
      (Unimodular.TypeABoundary.unitBoundary_convexSupport F hroots)⟩

/-- The same conclusion with the intrinsic all-integral-closed-curve
predicate from the recovered ordinary intersection theory. -/
theorem theorem_7_1_geometric_nef_and_big
    (hroots : Unimodular.TypeABoundary.HasTypeARays F) :
    AlgebraicGeometry.IsNef (baseField := k) (anticanonicalLineBundle F k).obj ∧
      IsBig k (anticanonicalLineBundle F k).obj := by
  obtain ⟨hn, hb⟩ := anticanonical_nef_and_big_of_support F k
    (Unimodular.TypeABoundary.unitBoundary_convexSupport F hroots)
  exact ⟨isNef_of_isNefOnCurves k _ hn, hb⟩

#print axioms isNefOnCurves_of_isGloballyGenerated
#print axioms isNef_of_isNefOnCurves
#print axioms theorem_7_1_anticanonical_nef_and_big
#print axioms theorem_7_1_geometric_nef_and_big
end Unimodular.NefBig
