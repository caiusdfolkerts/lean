module

public import Continuation.CycleBounds.InvariantAll
public import Mathlib.Topology.Covering.Quotient

/-!
# The actual strata in the real character torus

The lifted cells used in the proof descend to subsets of the literal additive
quotient `M_ℝ / M`. Their dimension is independent of every lifted representative,
and their positive Thomsen sheaves agree up to the proved principal character
translation. The final statement therefore quantifies strata in the torus itself.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators

namespace Unimodular.CycleBounds
open Set
variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Finite I]

/-- An open unit slab contains no integral level. Hence a cell has exactly
the active hyperplanes of any one of its points. -/
theorem integral_iff_of_mem_integerStratum (f : I → W →ₗ[ℝ] ℝ) {x y : W}
    (hy : y ∈ integerStratum f x) (i : I) :
    (∃ z : ℤ, f i y = (z : ℝ)) ↔ ∃ z : ℤ, f i x = (z : ℝ) := by
  by_cases hi : ∃ z : ℤ, f i x = (z : ℝ)
  · have he := hy i
    rw [if_pos hi] at he
    rw [he]
  · have he := hy i
    rw [if_neg hi] at he
    constructor
    · rintro ⟨z, hz⟩
      rw [hz] at he
      have hlo : ⌊f i x⌋ < z := by exact_mod_cast he.1
      have hhi : z < ⌈f i x⌉ := by exact_mod_cast he.2
      have hwidth := Int.ceil_le_floor_add_one (f i x)
      omega
    · exact fun h => (hi h).elim

theorem integerStratumDirection_eq_of_mem (f : I → W →ₗ[ℝ] ℝ) {x y : W}
    (hy : y ∈ integerStratum f x) :
    integerStratumDirection f y = integerStratumDirection f x := by
  ext d
  change (∀ i, (∃ z : ℤ, f i y = (z : ℝ)) → f i d = 0) ↔
    (∀ i, (∃ z : ℤ, f i x = (z : ℝ)) → f i d = 0)
  simp only [integral_iff_of_mem_integerStratum f hy]

theorem integerStratum_eq_of_mem (f : I → W →ₗ[ℝ] ℝ) {x y : W}
    (hy : y ∈ integerStratum f x) : integerStratum f y = integerStratum f x := by
  ext z
  apply forall_congr'
  intro i
  have hyi := hy i
  by_cases hi : ∃ k : ℤ, f i x = (k : ℝ)
  · have hiy := (integral_iff_of_mem_integerStratum f hy i).mpr hi
    rw [if_pos hi] at hyi
    simp only [if_pos hi, if_pos hiy, hyi]
  · have hiy : ¬∃ k : ℤ, f i y = (k : ℝ) :=
      fun h ↦ hi ((integral_iff_of_mem_integerStratum f hy i).mp h)
    have hxcast : f i x ∉ Set.range (Int.cast : ℤ → ℝ) := by
      rintro ⟨k, hk⟩
      exact hi ⟨k, hk.symm⟩
    have hycast : f i y ∉ Set.range (Int.cast : ℤ → ℝ) := by
      rintro ⟨k, hk⟩
      exact hiy ⟨k, hk.symm⟩
    have hceil := ceil_eq_of_mem_integerStratum f hy i
    have hxceil := (Int.ceil_eq_floor_add_one_iff_notMem (f i x)).mpr hxcast
    have hyceil := (Int.ceil_eq_floor_add_one_iff_notMem (f i y)).mpr hycast
    have hfloor : ⌊f i y⌋ = ⌊f i x⌋ := by omega
    simp only [if_neg hi, if_neg hiy, hceil, hfloor]

/-- Restricting a cell to any open neighborhood of one of its points preserves
its affine dimension. This is the local geometric dimension used in quotient
charts, rather than a number defined from the intersection bound. -/
theorem direction_integerStratum_inter_open_eq (f : I → W →ₗ[ℝ] ℝ) (x : W)
    (U : Set W) (hU : IsOpen U) (hx : x ∈ U) :
    (affineSpan ℝ (integerStratum f x ∩ U)).direction =
      integerStratumDirection f x := by
  let D := integerStratumDirection f x
  let B : Set D := (⋂ i : I, if ∃ z : ℤ, f i x = (z : ℝ) then Set.univ else
    {d | (⌊f i x⌋ : ℝ) < f i (x + d.val) ∧ f i (x + d.val) < (⌈f i x⌉ : ℝ)}) ∩
      {d | x + d.val ∈ U}
  have hB : IsOpen B := by
    refine IsOpen.inter ?_ (hU.preimage (continuous_const.add continuous_subtype_val))
    apply isOpen_iInter_of_finite
    intro i
    by_cases hi : ∃ z : ℤ, f i x = (z : ℝ)
    · simp only [if_pos hi]
      exact isOpen_univ
    · simp only [if_neg hi]
      have hc : Continuous (fun d : D ↦ f i (x + d.val)) :=
        (f i).continuous_of_finiteDimensional.comp
          (continuous_const.add continuous_subtype_val)
      exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hzero : (0 : D) ∈ B := by
    refine ⟨?_, by simpa using hx⟩
    apply Set.mem_iInter.mpr
    intro i
    have hh := self_mem_integerStratum f x i
    by_cases hi : ∃ z : ℤ, f i x = (z : ℝ)
    · simp [hi]
    · simpa [hi] using hh
  let A : D →ᵃ[ℝ] W :=
    (AffineEquiv.constVAdd ℝ W x).toAffineMap.comp D.subtype.toAffineMap
  have hA (d : D) : A d = x + d.val := rfl
  have himage : A '' B = integerStratum f x ∩ U := by
    ext y
    constructor
    · rintro ⟨d, hd, rfl⟩
      refine ⟨?_, hd.2⟩
      intro i
      rw [hA]
      by_cases hi : ∃ z : ℤ, f i x = (z : ℝ)
      · simp only [if_pos hi, map_add, d.property i hi, add_zero]
      · simpa only [if_neg hi, Set.mem_setOf_eq] using Set.mem_iInter.mp hd.1 i
    · rintro ⟨hy, hyU⟩
      have hd : y - x ∈ D := by
        intro i hi
        have hh := hy i
        rw [if_pos hi] at hh
        simp only [map_sub, hh, sub_self]
      refine ⟨⟨y - x, hd⟩, ⟨?_, by simpa using hyU⟩, by simp [hA]⟩
      apply Set.mem_iInter.mpr
      intro i
      have hh := hy i
      by_cases hi : ∃ z : ℤ, f i x = (z : ℝ)
      · simp [hi]
      · simpa only [if_neg hi, Set.mem_setOf_eq, add_sub_cancel] using hh
  have hspan : affineSpan ℝ B = ⊤ := hB.affineSpan_eq_top ⟨0, hzero⟩
  rw [← himage, ← AffineSubspace.map_span, hspan, AffineSubspace.map_direction,
    AffineSubspace.direction_top]
  change Submodule.map D.subtype (⊤ : Submodule ℝ D) = D
  simp

end Unimodular.CycleBounds

namespace PaperVerification.ToricGeometry

/-- The real character torus is the actual quotient by the embedded integral
character lattice. -/
abbrev CharacterTorus (n : ℕ) := Ambient n ⧸ (embed n).range

def characterTorusProjection (n : ℕ) : Ambient n →+ CharacterTorus n :=
  QuotientAddGroup.mk' (embed n).range

/-- The embedded character lattice is genuinely discrete in the Euclidean
topology: the unit ball around zero contains no other lattice point. -/
instance discreteTopology_embedRange (n : ℕ) : DiscreteTopology (embed n).range := by
  refine discreteTopology_iff_isOpen_singleton_zero.mpr
    ⟨Metric.ball 0 1, Metric.isOpen_ball, ?_⟩
  ext x
  rw [Set.mem_preimage, mem_ball_zero_iff, pi_norm_lt_iff zero_lt_one,
    Set.mem_singleton_iff]
  simp_rw [← ZeroMemClass.coe_eq_zero, funext_iff, Pi.zero_apply, Real.norm_eq_abs]
  obtain ⟨z, hz⟩ := x.property
  refine forall_congr' fun i ↦ ?_
  have hi : (z i : ℝ) = (x : Ambient n) i := congrFun hz i
  rw [← hi, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt,
    Int.abs_lt_one_iff, Int.cast_eq_zero]

/-- The actual quotient map has local homeomorphism charts. Thus the affine
cell dimensions below are dimensions in local charts of the real torus. -/
theorem characterTorusProjection_isLocalHomeomorph (n : ℕ) :
    IsLocalHomeomorph (characterTorusProjection n) := by
  have h : IsDiscrete ((embed n).range : Set (Ambient n)) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  exact ((embed n).range.isAddQuotientCoveringMap_of_comm h).isLocalHomeomorph

theorem characterTorusProjection_eq_iff {n : ℕ} (x y : Ambient n) :
    characterTorusProjection n x = characterTorusProjection n y ↔
      ∃ m : Lattice n, y = x + embed n m := by
  rw [characterTorusProjection, QuotientAddGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, ⟨m, rfl⟩, hz⟩
    exact ⟨m, hz.symm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨embed n m, ⟨m, rfl⟩, rfl⟩

namespace SmoothCompleteFan
open Unimodular.CycleBounds Unimodular.SeriesParallel
open PaperVerification.ToricSchemes
open AlgebraicGeometry CategoryTheory
variable {n : ℕ} (F : SmoothCompleteFan n)

/-- The stratum as a subset of `M_ℝ / M`, not only as a lifted cell. -/
def torusStratum (θ : Module.Dual ℝ (Ambient n)) : Set (CharacterTorus n) :=
  characterTorusProjection n '' F.thomsenStratum θ

/-- Near a lift of a stratum, taking the inverse image from the quotient
introduces no additional translated cell. The active integer levels are
isolated, and the inactive forms remain inside their original open unit slabs. -/
theorem exists_torusStratum_localization (θ : Module.Dual ℝ (Ambient n)) :
    ∃ U : Set (Ambient n), IsOpen U ∧
      (dotProductEquiv ℝ (Fin n)).symm θ ∈ U ∧
      characterTorusProjection n ⁻¹' F.torusStratum θ ∩ U =
        F.thomsenStratum θ ∩ U := by
  let x := (dotProductEquiv ℝ (Fin n)).symm θ
  let N : Set (Ambient n) := ⋂ u : F.rays,
    if ∃ k : ℤ, F.thomsenForms u x = (k : ℝ) then
      {y | F.thomsenForms u x - 1 < F.thomsenForms u y ∧
        F.thomsenForms u y < F.thomsenForms u x + 1}
    else {y | (⌊F.thomsenForms u x⌋ : ℝ) < F.thomsenForms u y ∧
      F.thomsenForms u y < (⌈F.thomsenForms u x⌉ : ℝ)}
  have hNo : IsOpen N := by
    apply isOpen_iInter_of_finite
    intro u
    have hc := (F.thomsenForms u).continuous_of_finiteDimensional
    split_ifs <;>
      exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hNx : x ∈ N := by
    apply Set.mem_iInter.mpr
    intro u
    by_cases hu : ∃ k : ℤ, F.thomsenForms u x = (k : ℝ)
    · simp only [if_pos hu, Set.mem_setOf_eq]
      constructor <;> linarith
    · simpa only [if_neg hu, Set.mem_setOf_eq] using
        self_mem_integerStratum F.thomsenForms x u
  refine ⟨N, hNo, hNx, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨z, hz, hzy⟩, hyN⟩
    obtain ⟨m, hm⟩ := (characterTorusProjection_eq_iff z y).mp hzy
    refine ⟨?_, hyN⟩
    change y ∈ integerStratum F.thomsenForms x
    intro u
    have hb := Set.mem_iInter.mp hyN u
    by_cases hu : ∃ k : ℤ, F.thomsenForms u x = (k : ℝ)
    · rw [if_pos hu] at hb ⊢
      change F.thomsenForms u x - 1 < F.thomsenForms u y ∧
        F.thomsenForms u y < F.thomsenForms u x + 1 at hb
      obtain ⟨k, hk⟩ := hu
      have hzval := hz u
      rw [if_pos ⟨k, hk⟩] at hzval
      have hpair : F.thomsenForms u (embed n m) = (integerPairing u.val m : ℝ) :=
        normalRay_pairing_lattice u.val m
      have hyval : F.thomsenForms u y = ((k + integerPairing u.val m : ℤ) : ℝ) := by
        rw [hm, map_add, hzval, hk, hpair, Int.cast_add]
      rw [hyval, hk] at hb
      have hlo : k - 1 < k + integerPairing u.val m := by exact_mod_cast hb.1
      have hhi : k + integerPairing u.val m < k + 1 := by exact_mod_cast hb.2
      have hm0 : integerPairing u.val m = 0 := by omega
      rw [hm0, add_zero] at hyval
      exact hyval.trans hk.symm
    · simpa only [if_neg hu, Set.mem_setOf_eq] using hb
  · rintro ⟨hy, hyN⟩
    exact ⟨Set.mem_image_of_mem _ hy, hyN⟩

/-- Every torus stratum has an actual local quotient chart whose lifted
intersection has its stated affine dimension. Together with representative
independence, this identifies the dimension with the local affine-arrangement
dimension in the torus, including all lower-dimensional strata. -/
theorem torusStratum_local_chart (θ : Module.Dual ℝ (Ambient n)) :
    ∃ U : Set (Ambient n), IsOpen U ∧
      (dotProductEquiv ℝ (Fin n)).symm θ ∈ U ∧
      Topology.IsOpenEmbedding (U.domRestrict (characterTorusProjection n)) ∧
      characterTorusProjection n ⁻¹' F.torusStratum θ ∩ U =
        F.thomsenStratum θ ∩ U ∧
      Module.finrank ℝ (affineSpan ℝ (F.thomsenStratum θ ∩ U)).direction =
        F.thomsenStratumDimension θ := by
  obtain ⟨N, hNo, hNx, hN⟩ := F.exists_torusStratum_localization θ
  obtain ⟨e, hxe, hq⟩ := characterTorusProjection_isLocalHomeomorph n
    ((dotProductEquiv ℝ (Fin n)).symm θ)
  let U := e.source ∩ N
  have hUo : IsOpen U := e.open_source.inter hNo
  have hxU : (dotProductEquiv ℝ (Fin n)).symm θ ∈ U := ⟨hxe, hNx⟩
  refine ⟨U, hUo, hxU, ?_, ?_, ?_⟩
  · have hi : Topology.IsOpenEmbedding (Set.inclusion Set.inter_subset_left : U → e.source) := by
      refine ⟨.inclusion Set.inter_subset_left, ?_⟩
      rw [Set.range_inclusion]
      exact isOpen_induced hUo
    have hfun : U.domRestrict (characterTorusProjection n) =
        e.source.domRestrict e ∘ (Set.inclusion Set.inter_subset_left : U → e.source) := by
      funext y
      change characterTorusProjection n y.val = e y.val
      exact congrFun hq y.val
    rw [hfun]
    exact e.isOpenEmbedding_restrict.comp hi
  · ext y
    have hy := Set.ext_iff.mp hN y
    simp only [Set.mem_inter_iff] at hy
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    tauto
  · unfold thomsenStratumDimension thomsenStratum
    rw [direction_integerStratum_inter_open_eq F.thomsenForms _ U hUo hxU,
      direction_integerStratum_eq]

lemma thomsenStratumDimension_eq_of_mem (θ : Module.Dual ℝ (Ambient n))
    {x : Ambient n} (hx : x ∈ F.thomsenStratum θ) :
    F.thomsenStratumDimension (dotProductEquiv ℝ (Fin n) x) =
      F.thomsenStratumDimension θ := by
  unfold thomsenStratumDimension thomsenStratum
  rw [LinearEquiv.symm_apply_apply, finrank_integerStratum,
    finrank_integerStratum, integerStratumDirection_eq_of_mem F.thomsenForms hx]

theorem torusStratum_eq_of_mem (θ : Module.Dual ℝ (Ambient n))
    {x : Ambient n} (hx : x ∈ F.thomsenStratum θ) :
    F.torusStratum (dotProductEquiv ℝ (Fin n) x) = F.torusStratum θ := by
  unfold torusStratum thomsenStratum
  rw [LinearEquiv.symm_apply_apply, integerStratum_eq_of_mem F.thomsenForms hx]

/-- Any two lifts of the same actual torus stratum have the same geometric
affine-cell dimension. -/
theorem thomsenStratumDimension_eq_of_torusStratum_eq
    (θ φ : Module.Dual ℝ (Ambient n)) (h : F.torusStratum θ = F.torusStratum φ) :
    F.thomsenStratumDimension θ = F.thomsenStratumDimension φ := by
  let y := (dotProductEquiv ℝ (Fin n)).symm φ
  have hy : characterTorusProjection n y ∈ F.torusStratum θ := by
    rw [h]
    exact Set.mem_image_of_mem _ (self_mem_integerStratum F.thomsenForms y)
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨m, hm⟩ := (characterTorusProjection_eq_iff x y).mp hxy
  have hφ : φ = dotProductEquiv ℝ (Fin n) x +
      dotProductEquiv ℝ (Fin n) (embed n m) := by
    have he := congrArg (dotProductEquiv ℝ (Fin n)) hm
    simpa only [y, LinearEquiv.apply_symm_apply, map_add] using he
  rw [hφ, F.thomsenStratumDimension_add_lattice,
    F.thomsenStratumDimension_eq_of_mem θ hx]

/-- The collection of actual arrangement strata in the character torus. -/
def TorusStratum := {S : Set (CharacterTorus n) //
  ∃ θ : Module.Dual ℝ (Ambient n), S = F.torusStratum θ}

namespace TorusStratum
variable {F}

def representative (σ : F.TorusStratum) : Module.Dual ℝ (Ambient n) :=
  σ.property.choose

theorem carrier_eq (σ : F.TorusStratum) :
    σ.val = F.torusStratum σ.representative := σ.property.choose_spec

/-- The ordinary affine dimension of a lift; the following theorem proves
that no choice of representative changes this number. -/
def dimension (σ : F.TorusStratum) : ℕ :=
  F.thomsenStratumDimension σ.representative

theorem dimension_eq (σ : F.TorusStratum) (θ : Module.Dual ℝ (Ambient n))
    (hθ : σ.val = F.torusStratum θ) : σ.dimension = F.thomsenStratumDimension θ :=
  F.thomsenStratumDimension_eq_of_torusStratum_eq σ.representative θ
    (σ.carrier_eq.symm.trans hθ)

/-- At every point of the quotient stratum, an actual local quotient chart
identifies that stratum with its affine arrangement cell, of dimension
`σ.dimension`. This supplies the local geometric meaning of the dimension. -/
theorem local_chart (σ : F.TorusStratum) {p : CharacterTorus n} (hp : p ∈ σ.val) :
    ∃ (x : Ambient n) (U : Set (Ambient n)),
      characterTorusProjection n x = p ∧ IsOpen U ∧ x ∈ U ∧
      Topology.IsOpenEmbedding (U.domRestrict (characterTorusProjection n)) ∧
      characterTorusProjection n ⁻¹' σ.val ∩ U =
        F.thomsenStratum (dotProductEquiv ℝ (Fin n) x) ∩ U ∧
      Module.finrank ℝ
        (affineSpan ℝ (F.thomsenStratum (dotProductEquiv ℝ (Fin n) x) ∩ U)).direction =
          σ.dimension := by
  rw [σ.carrier_eq] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  have hσ : σ.val = F.torusStratum (dotProductEquiv ℝ (Fin n) x) :=
    σ.carrier_eq.trans (F.torusStratum_eq_of_mem σ.representative hx).symm
  obtain ⟨U, ho, hxU, he, hU, hd⟩ :=
    F.torusStratum_local_chart (dotProductEquiv ℝ (Fin n) x)
  rw [LinearEquiv.symm_apply_apply] at hxU
  refine ⟨x, U, hxp, ho, hxU, he, ?_, ?_⟩
  · simpa only [hσ] using hU
  · exact hd.trans (σ.dimension_eq _ hσ).symm

end TorusStratum

universe u
variable (k : Type u) [Field k]

/-- The genuine Cartier sheaves obtained from any two representatives of
one torus stratum are linearly equivalent by an integral character. -/
theorem thomsenCartier_same_torusStratum
    (θ φ : Module.Dual ℝ (Ambient n)) (h : F.torusStratum θ = F.torusStratum φ) :
    (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).LinearlyEquivalent
      (F.fanCartierData k F.isPure (F.thomsenCoefficients φ)) := by
  let y := (dotProductEquiv ℝ (Fin n)).symm φ
  have hy : characterTorusProjection n y ∈ F.torusStratum θ := by
    rw [h]
    exact Set.mem_image_of_mem _ (self_mem_integerStratum F.thomsenForms y)
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨m, hm⟩ := (characterTorusProjection_eq_iff x y).mp hxy
  have hφ : φ = dotProductEquiv ℝ (Fin n) x +
      dotProductEquiv ℝ (Fin n) (embed n m) := by
    have he := congrArg (dotProductEquiv ℝ (Fin n)) hm
    simpa only [y, LinearEquiv.apply_symm_apply, map_add] using he
  apply F.fanCartierData_characterTranslation k F.isPure
    (F.thomsenCoefficients θ) (F.thomsenCoefficients φ) (-m)
  intro v hv
  rw [hφ, F.thomsenCoefficients_add_lattice,
    F.thomsenCoefficients_eq_of_mem_stratum θ hx ⟨v, hv⟩]
  simp only [integerPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib,
    sub_neg_eq_add]

/-- Proposition6.8 on the literal real torus, for every stratum and every
one of its representatives, and every intrinsic invariant integral curve. -/
theorem proposition_6_8_torusStrata {V : Type*} [Fintype V]
    (G : IncidenceGraph V F.rays) (hG : G.edges = Set.univ) (hK : ¬G.HasK4Minor)
    (δ : Lattice n →ₗ[ℤ] (V → ℤ)) (hinj : Function.Injective δ)
    (hδ : ∀ v : F.rays, δ v.val = Pi.single (G.source v) 1 - Pi.single (G.target v) 1)
    (σ : F.TorusStratum) (θ : Module.Dual ℝ (Ambient n))
    (hθ : σ.val = F.torusStratum θ)
    (C : InvariantIntegralCurve k n (F.fanSchemeOver k)) :
    ∃ d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf) d ∧
      d ≤ (σ.dimension : ℤ) := by
  rw [σ.dimension_eq θ hθ]
  exact F.thomsen_invariantCurve_degree_bound k G hG hK δ hinj hδ θ C

/-- A representative-free form of Proposition6.8: every actual torus stratum
has its positive Thomsen sheaf, well defined up to the proved character
translation, and every invariant integral curve satisfies the bound. -/
theorem proposition_6_8_on_characterTorus {V : Type*} [Fintype V]
    (G : IncidenceGraph V F.rays) (hG : G.edges = Set.univ) (hK : ¬G.HasK4Minor)
    (δ : Lattice n →ₗ[ℤ] (V → ℤ)) (hinj : Function.Injective δ)
    (hδ : ∀ v : F.rays, δ v.val = Pi.single (G.source v) 1 - Pi.single (G.target v) 1)
    (σ : F.TorusStratum) (C : InvariantIntegralCurve k n (F.fanSchemeOver k)) :
    ∃ d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (F.fanCartierData k F.isPure (F.thomsenCoefficients σ.representative)).sheaf) d ∧
      d ≤ (σ.dimension : ℤ) :=
  F.proposition_6_8_torusStrata k G hG hK δ hinj hδ σ σ.representative σ.carrier_eq C

#print axioms characterTorusProjection_isLocalHomeomorph
#print axioms TorusStratum.local_chart
#print axioms thomsenStratumDimension_eq_of_torusStratum_eq
#print axioms thomsenCartier_same_torusStratum
#print axioms proposition_6_8_torusStrata
#print axioms proposition_6_8_on_characterTorus

end SmoothCompleteFan
end PaperVerification.ToricGeometry
