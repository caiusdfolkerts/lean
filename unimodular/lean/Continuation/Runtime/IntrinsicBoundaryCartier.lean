module

public import Continuation.Runtime.BoundaryValuationTransport
public import Continuation.Fano.ActualBoundaryCartierCoefficients
public import Continuation.Geometry.CanonicalTransport

/-! Actual boundary Cartier coefficients, their literal section inequalities,
and the intrinsic anticanonical sheaf under the reconstructed scheme
isomorphism. The canonical target is the existing universal Kähler top
exterior-power dual; its comparison is proved, not assumed. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open PaperVerification.ToricGeometry PaperVerification.ToricCharacters
open Unimodular.NefBig
open scoped Classical

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [IsLocallyNoetherian X.left]
    (T : SplitToricEmbedding k n X)

/-- Literal coefficients at all actual prime divisors. Off the specified
torus boundary and in other codimensions the value is zero. -/
def boundaryCoefficient (a : Lattice n → ℤ) (x : X.left) : ℤ :=
  if Order.coheight x = 1 ∧ x ∈ T.boundary then a (T.valuationVector x) else 0

/-- Equality to the actual Weil coefficient of an actual Cartier divisor. -/
def HasBoundaryCoefficients (D : CartierData X.left) (a : Lattice n → ℤ) : Prop :=
  D.weilCoefficient = T.boundaryCoefficient a

theorem HasBoundaryCoefficients.unique [Smooth X.hom]
    {D E : CartierData X.left} {a : Lattice n → ℤ}
    (hD : T.HasBoundaryCoefficients D a) (hE : T.HasBoundaryCoefficients E a) :
    D.Equivalent E :=
  CartierData.equivalent_of_weilCoefficient_eq X.hom D E (hD.trans hE.symm)

variable (F : SmoothCompleteFan n) (e : F.fanSchemeOver k ≅ X)
    (htorus : (F.intrinsicToricEmbedding k).torus ≫ e.hom = T.torus)

local instance fanOverIntegral : IsIntegral (F.fanSchemeOver k).left := by
  change IsIntegral (F.fanScheme k)
  infer_instance
local instance fanOverLocallyNoetherian : IsLocallyNoetherian (F.fanSchemeOver k).left := by
  change IsLocallyNoetherian (F.fanScheme k)
  infer_instance

/-- The actual pullback along the inverse scheme isomorphism, with its
literal rational-function embedding retained. -/
def boundaryCartierOfPresentation (a : Lattice n → ℤ) : CartierData X.left :=
  (F.fanCartierData k F.isPure a).dominantPullback e.inv.left

theorem fanCartier_hasBoundaryCoefficients (a : Lattice n → ℤ) :
    (F.intrinsicToricEmbedding k).HasBoundaryCoefficients
      (F.fanCartierData k F.isPure a) a := by
  funext x
  by_cases hc : Order.coheight x = 1
  · by_cases hb : x ∈ (F.intrinsicToricEmbedding k).boundary
    · rw [boundaryCoefficient, if_pos (show Order.coheight x = 1 ∧ x ∈ (F.intrinsicToricEmbedding k).boundary from ⟨hc,hb⟩)]
      exact F.fanCartier_weilCoefficient_boundary k a ⟨x, hc, hb⟩
    · rw [boundaryCoefficient, if_neg (fun h => hb h.2)]
      exact F.fanCartier_weilCoefficient_off_boundary k a x hb
  · rw [CartierData.weilCoefficient_eq_zero_of_coheight_ne_one _ hc,
      boundaryCoefficient, if_neg (fun h => hc h.1)]

include htorus in
/-- The equality of coefficients is proved from the actual local-ring
pullback and torus-character triangle. It is not supplied as input. -/
theorem boundaryCartierOfPresentation_hasCoefficients (a : Lattice n → ℤ) :
    T.HasBoundaryCoefficients (boundaryCartierOfPresentation F e a) a := by
  funext x
  have hinv := (F.intrinsicToricEmbedding k).torus_preserving_inverse T e htorus
  have hc : Order.coheight (e.inv.left x) = Order.coheight x :=
    coheight_eq_of_isOpenImmersion e.inv.left
  have hb : e.inv.left x ∈ (F.intrinsicToricEmbedding k).boundary ↔ x ∈ T.boundary :=
    T.boundary_mem_map_iff (F.intrinsicToricEmbedding k) e.symm hinv x
  have hv : (F.intrinsicToricEmbedding k).valuationVector (e.inv.left x) =
      T.valuationVector x :=
    T.valuationVector_map (F.intrinsicToricEmbedding k) e.symm hinv x
  change ((F.fanCartierData k F.isPure a).dominantPullback e.inv.left).weilCoefficient x = _
  letI : IsIntegral ((Over.forget (Spec (CommRingCat.of k))).obj X) := ‹IsIntegral X.left›
  letI : IsIntegral ((Over.forget (Spec (CommRingCat.of k))).obj (F.fanSchemeOver k)) := fanOverIntegral F
  letI : IsLocallyNoetherian ((Over.forget (Spec (CommRingCat.of k))).obj X) := ‹IsLocallyNoetherian X.left›
  letI : IsLocallyNoetherian ((Over.forget (Spec (CommRingCat.of k))).obj (F.fanSchemeOver k)) := fanOverLocallyNoetherian F
  erw [(F.fanCartierData k F.isPure a).weilCoefficient_dominantPullback_iso
    ((Over.forget _).mapIso e.symm) x]
  change (F.fanCartierData k F.isPure a).weilCoefficient (e.inv.left x) = _
  rw [congrFun (fanCartier_hasBoundaryCoefficients F a) (e.inv.left x)]
  simp only [boundaryCoefficient, hc, hb, hv]

include F e htorus in
theorem exists_boundaryCartier_of_presentation (a : Lattice n → ℤ) :
    ∃ D : CartierData X.left, T.HasBoundaryCoefficients D a :=
  ⟨boundaryCartierOfPresentation F e a,
    T.boundaryCartierOfPresentation_hasCoefficients F e htorus a⟩

/-- Every Cartier representative with these actual coefficients has the
same ordinary sheaf as the constructed genuine pullback. -/
def boundaryCartierPresentationSheafIso [Smooth X.hom]
    (D : CartierData X.left) (a : Lattice n → ℤ)
    (hD : T.HasBoundaryCoefficients D a) :
    D.sheaf ≅ (Scheme.Modules.pullback e.inv.left).obj
      (F.fanCartierData k F.isPure a).sheaf :=
  (HasBoundaryCoefficients.unique T hD (T.boundaryCartierOfPresentation_hasCoefficients F e htorus a)).choose ≪≫
    ((F.fanCartierData k F.isPure a).dominantPullbackSheafIso e.inv.left).symm

/-- The intrinsic unit-boundary Cartier divisor is the actual anticanonical
line bundle: the ordinary internal-Hom dual of the actual top exterior
power of relative Kähler differentials. -/
def unitBoundaryCartierAnticanonicalIso [Smooth X.hom]
    (D : CartierData X.left) (hD : T.HasBoundaryCoefficients D (fun _ => 1)) :
    D.sheaf ≅
      (topDifferentialSheaf k X.left n).dual :=
  T.boundaryCartierPresentationSheafIso F e htorus D (fun _ => 1) hD ≪≫
    (Scheme.Modules.pullback e.inv.left).mapIso
      (anticanonical_unitBoundaryIso F k).symm ≪≫
    fanAnticanonicalPullbackIso F k e.inv.left

include F e htorus in
/-- Every character is tested against every actual boundary coefficient;
the section is a genuine global section of the original Cartier sheaf. -/
theorem boundaryCartier_character_section_iff [Smooth X.hom]
    (D : CartierData X.left) (a : Lattice n → ℤ)
    (hD : T.HasBoundaryCoefficients D a) (m : Lattice n) :
    T.intrinsicCharacter m ∈ D.sectionValueRange ⊤ ↔
      ∀ q : T.BoundaryPrime, -a (T.boundaryValuation q) ≤
        integerPairing (T.boundaryValuation q) m := by
  let C := F.fanCartierData k F.isPure a
  have hDE := HasBoundaryCoefficients.unique T hD (T.boundaryCartierOfPresentation_hasCoefficients F e htorus a)
  rw [D.equivalent_sectionValueRange _ hDE ⊤]
  have hinv := (F.intrinsicToricEmbedding k).torus_preserving_inverse T e htorus
  have hchar := T.intrinsicCharacter_pullback (F.intrinsicToricEmbedding k) e.symm hinv m
  letI : IsIntegral ((Over.forget (Spec (CommRingCat.of k))).obj X) := ‹IsIntegral X.left›
  letI : IsIntegral ((Over.forget (Spec (CommRingCat.of k))).obj (F.fanSchemeOver k)) := fanOverIntegral F
  erw [← hchar, C.globalSectionRange_schemeIso_iff ((Over.forget _).mapIso e.symm)]
  rw [F.intrinsicCharacter_fan k]
  change F.torusRationalMap k (AddMonoidAlgebra.single m 1) ∈
    Set.range (C.sectionValue ⊤) ↔ _
  rw [F.torusRationalMap_mem_fanCartier_globalRange_iff k F.isPure a,
    single_mem_characterModule]
  have hfan : m ∈ F.fanIntegralExponents a ↔
      ∀ p : (F.intrinsicToricEmbedding k).BoundaryPrime,
        -a ((F.intrinsicToricEmbedding k).boundaryValuation p) ≤
          integerPairing ((F.intrinsicToricEmbedding k).boundaryValuation p) m := by
    change (∀ u ∈ F.rays, -(a u : ℝ) ≤
      dotProductEquiv ℝ (Fin n) (embed n u) (embed n m)) ↔ _
    simp only [SmoothCompleteFan.normalRay_pairing_lattice]
    constructor
    · intro h p
      exact_mod_cast h _ (F.boundaryValuation_mem_rays k p)
    · intro h u hu
      obtain ⟨p, hp⟩ := F.exists_boundaryPrime_valuation k u hu
      have hi := h p
      rw [hp] at hi
      exact_mod_cast hi
  rw [hfan]
  constructor
  · intro h q
    obtain ⟨p, rfl⟩ := ((F.intrinsicToricEmbedding k).boundaryPrimeEquiv T e htorus).surjective q
    simpa only [(F.intrinsicToricEmbedding k).boundaryValuation_equiv T e htorus] using h p
  · intro h p
    simpa only [(F.intrinsicToricEmbedding k).boundaryValuation_equiv T e htorus] using
      h ((F.intrinsicToricEmbedding k).boundaryPrimeEquiv T e htorus p)

#print axioms HasBoundaryCoefficients.unique
#print axioms boundaryCartierOfPresentation_hasCoefficients
#print axioms unitBoundaryCartierAnticanonicalIso
#print axioms boundaryCartier_character_section_iff

end PaperVerification.ToricSchemes.SplitToricEmbedding

#check PaperVerification.ToricSchemes.SplitToricEmbedding.unitBoundaryCartierAnticanonicalIso
