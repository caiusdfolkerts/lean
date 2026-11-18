module

public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import sunlet.dimension_algebra
public import sunlet.polynomial_image
public import sunlet.rational_partials
public import sunlet.verified_network_graph

/-! Exact ordinary proof stage 2 of 3.
All source bodies below are preserved from the canonical project.
Generation alone is not verification; require a successful stock Lean check. -/

@[expose] public section

#eval IO.println "NETWORK_STAGE_IMPORTS_COMPLETE VerifiedNetworkAlgebra"

section NetworkStageSource_Sunlet_NetworkGluing


/-!
# Matching a cut-edge grading

The exponent vectors of a glued Fourier coordinate are pairs of exponent
vectors with the same cut-edge class. This module proves the linear-algebra
identity underlying the cut-edge dimension subtraction. The span is computed
from the matched pairs themselves; no dimension formula is assumed.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkGluing

variable {K C I J V W : Type*} [Field K] [Fintype C] [DecidableEq C]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A linear extension of a family of vectors indexed by the cut-edge classes. -/
def anchorLift (a : C → V) : (C → K) →ₗ[K] V :=
  ∑ c : C, (LinearMap.proj c).smulRight (a c)

@[simp] theorem anchorLift_apply (a : C → V) (z : C → K) :
    anchorLift a z = ∑ c : C, z c • a c := by
  simp [anchorLift]

@[simp] theorem anchorLift_single (a : C → V) (c : C) :
    anchorLift a (Pi.single c (1 : K)) = a c := by
  simp [anchorLift_apply, Pi.single_apply]

/-- All pairs of coordinates with matching cut-edge class. -/
abbrev Matched (d : I → C) (e : J → C) := {ij : I × J // d ij.1 = e ij.2}

/-- The actual span of the paired exponent vectors. -/
def matchedSpan (f : I → V) (g : J → W) (d : I → C) (e : J → C) :
    Submodule K (V × W) :=
  Submodule.span K (Set.range fun p : Matched d e => (f p.val.1, g p.val.2))

/-- The grading balance along a cut edge. -/
def balance (D : V →ₗ[K] (C → K)) (E : W →ₗ[K] (C → K)) :
    (V × W) →ₗ[K] (C → K) :=
  D.comp (LinearMap.fst K V W) - E.comp (LinearMap.snd K V W)

@[simp] theorem balance_apply (D : V →ₗ[K] (C → K)) (E : W →ₗ[K] (C → K))
    (v : V) (w : W) : balance D E (v,w) = D v - E w := rfl

/-- Matching the class labels imposes exactly equality of the two gradings. -/
theorem matchedSpan_eq_ker
    (f : I → V) (g : J → W) (d : I → C) (e : J → C)
    (D : V →ₗ[K] (C → K)) (E : W →ₗ[K] (C → K))
    (hf : Submodule.span K (Set.range f) = ⊤)
    (hg : Submodule.span K (Set.range g) = ⊤)
    (hDf : ∀ i, D (f i) = Pi.single (d i) 1)
    (hEg : ∀ j, E (g j) = Pi.single (e j) 1)
    (a : C → I) (b : C → J) (ha : ∀ c, d (a c) = c) (hb : ∀ c, e (b c) = c) :
    matchedSpan f g d e = LinearMap.ker (balance D E) := by
  let S := matchedSpan (K := K) f g d e
  let L := anchorLift (K := K) (fun c => g (b c))
  have hpair (i : I) (j : J) (h : d i = e j) : (f i,g j) ∈ S :=
    Submodule.subset_span ⟨⟨(i,j),h⟩,rfl⟩
  have hgraph (v : V) : (v,L (D v)) ∈ S := by
    have hv : v ∈ Submodule.span K (Set.range f) := by rw [hf]; trivial
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨i,rfl⟩ := hv
        rw [hDf]
        simpa [L] using hpair i (b (d i)) (hb (d i)).symm
    | zero => simpa only [map_zero, Prod.zero_eq_mk] using (S.zero_mem : (0 : V × W) ∈ S)
    | add v w hv hw ihv ihw =>
        simpa only [map_add, Prod.mk_add_mk] using S.add_mem ihv ihw
    | smul c v hv ih =>
        simpa only [map_smul, Prod.smul_mk] using S.smul_mem c ih
  have hvertical (w : W) : (0,w-L (E w)) ∈ S := by
    have hw : w ∈ Submodule.span K (Set.range g) := by rw [hg]; trivial
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨j,rfl⟩ := hw
        have h1 := hpair (a (e j)) j (ha (e j))
        have h2 := hpair (a (e j)) (b (e j)) ((ha (e j)).trans (hb (e j)).symm)
        have hh := S.sub_mem h1 h2
        simpa [hEg,L] using hh
    | zero => simpa only [map_zero, sub_zero, Prod.zero_eq_mk] using (S.zero_mem : (0 : V × W) ∈ S)
    | add v w hv hw ihv ihw =>
        simpa [map_add, add_sub_add_comm] using S.add_mem ihv ihw
    | smul c v hv ih =>
        simpa [map_smul, smul_sub] using S.smul_mem c ih
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    change balance D E (f p.val.1, g p.val.2) = 0
    simp only [balance_apply,hDf,hEg,p.property,sub_self]
  · intro x hx
    have hDE : D x.1 = E x.2 := sub_eq_zero.mp hx
    have hh := S.add_mem (hgraph x.1) (hvertical x.2)
    simpa [hDE,add_comm] using hh

/-- The cut-edge grading map is onto as soon as every class occurs. -/
theorem balance_surjective
    (f : I → V) (d : I → C) (D : V →ₗ[K] (C → K)) (E : W →ₗ[K] (C → K))
    (hDf : ∀ i, D (f i) = Pi.single (d i) 1)
    (a : C → I) (ha : ∀ c, d (a c) = c) : Function.Surjective (balance D E) := by
  intro z
  refine ⟨(anchorLift (fun c => f (a c)) z,0),?_⟩
  simp only [balance_apply,map_zero,sub_zero,anchorLift_apply,map_sum,map_smul,hDf,ha]
  ext c
  simp [Pi.single_apply]

/-- The dimension loss is exactly one for every cut-edge class. -/
theorem finrank_matchedSpan [Module.Finite K V] [Module.Finite K W]
    (f : I → V) (g : J → W) (d : I → C) (e : J → C)
    (D : V →ₗ[K] (C → K)) (E : W →ₗ[K] (C → K))
    (hf : Submodule.span K (Set.range f) = ⊤)
    (hg : Submodule.span K (Set.range g) = ⊤)
    (hDf : ∀ i, D (f i) = Pi.single (d i) 1)
    (hEg : ∀ j, E (g j) = Pi.single (e j) 1)
    (a : C → I) (b : C → J) (ha : ∀ c, d (a c) = c) (hb : ∀ c, e (b c) = c) :
    Module.finrank K (matchedSpan (K := K) f g d e) =
      Module.finrank K V + Module.finrank K W - Fintype.card C := by
  rw [matchedSpan_eq_ker f g d e D E hf hg hDf hEg a b ha hb]
  have hs := balance_surjective f d D E hDf a ha
  have h := LinearMap.finrank_range_add_finrank_ker (balance D E)
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_pi,Module.finrank_prod] at h
  omega

/-- The same computation for families that span proper subspaces of their
ambient parameter spaces. -/
theorem finrank_matchedSpan_subspaces [Module.Finite K V] [Module.Finite K W]
    (f : I → V) (g : J → W) (d : I → C) (e : J → C)
    (D : V →ₗ[K] (C → K)) (E : W →ₗ[K] (C → K))
    (hDf : ∀ i,D (f i)=Pi.single (d i) 1)
    (hEg : ∀ j,E (g j)=Pi.single (e j) 1)
    (a : C → I) (b : C → J) (ha : ∀ c,d (a c)=c) (hb : ∀ c,e (b c)=c) :
    Module.finrank K (matchedSpan (K := K) f g d e) =
      Module.finrank K (Submodule.span K (Set.range f)) +
        Module.finrank K (Submodule.span K (Set.range g)) - Fintype.card C := by
  let V' := Submodule.span K (Set.range f)
  let W' := Submodule.span K (Set.range g)
  let f' : I → V' := fun i => ⟨f i,Submodule.subset_span ⟨i,rfl⟩⟩
  let g' : J → W' := fun j => ⟨g j,Submodule.subset_span ⟨j,rfl⟩⟩
  have hf' : Submodule.span K (Set.range f')=⊤ :=
    (Submodule.span_range_subtype_eq_top_iff V' _).mpr rfl
  have hg' : Submodule.span K (Set.range g')=⊤ :=
    (Submodule.span_range_subtype_eq_top_iff W' _).mpr rfl
  let T : (V' × W') →ₗ[K] (V × W) := V'.subtype.prodMap W'.subtype
  have hT : Function.Injective T := by
    intro x y h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact Subtype.ext (congrArg Prod.snd h)
  have heq : (matchedSpan (K := K) f' g' d e).map T=matchedSpan (K := K) f g d e := by
    rw [matchedSpan,Submodule.map_span]
    rw [← Set.range_comp]
    rfl
  rw [← heq,← (Submodule.equivMapOfInjective T hT (matchedSpan f' g' d e)).finrank_eq]
  exact finrank_matchedSpan f' g' d e (D.comp V'.subtype) (E.comp W'.subtype)
    hf' hg' hDf hEg a b ha hb

/-- Rescaling individual nonzero rows does not alter their span. This is
the passage from ordinary to logarithmic Jacobian rows. -/
theorem span_pointwise_smul (f : I → V) (s : I → K) (hs : ∀ i,s i≠0) :
    Submodule.span K (Set.range fun i => s i • f i)=Submodule.span K (Set.range f) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change f i ∈ Submodule.span K (Set.range fun i => s i • f i)
    have h := (Submodule.span K (Set.range fun i => s i • f i)).smul_mem
      (s i)⁻¹ (Submodule.subset_span ⟨i,rfl⟩)
    simpa only [smul_smul,inv_mul_cancel₀ (hs i),one_smul] using h

end Sunlet.NetworkGluing
end
end NetworkStageSource_Sunlet_NetworkGluing
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkGluing"

section NetworkStageSource_Sunlet_NetworkDifferentials


/-!
# Differentials of a rational coordinate field

This module supplies the characteristic-zero dimension bridge needed for
cut-edge gluing. The relevant vector space is the span of the differentials
of the actual coordinate functions. Its dimension is the transcendence
degree of their generated field, and hence the Krull dimension of the
coordinate algebra. No Jacobian criterion is assumed as an axiom.
-/

noncomputable section

open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin
open KaehlerDifferential

namespace Sunlet.NetworkDifferentials

section TranscendenceBasis

variable {K E I : Type*} [Field K] [Field E] [Algebra K E] [Fintype I]

/-- A separable algebraic extension of a rational field has one independent
differential for each element of the chosen transcendence basis. -/
theorem finrank_kaehler_of_transcendence_basis
    (v : I → E) (hv : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) E] :
    Module.finrank E Ω[E⁄K] = Fintype.card I := by
  let P := MvPolynomial I K
  let A := Algebra.adjoin K (Set.range v)
  let F := IntermediateField.adjoin K (Set.range v)
  let e : P ≃ₐ[K] A := hv.aevalEquiv
  let vF : I → F := fun i => ⟨v i,IntermediateField.subset_adjoin K _ ⟨i,rfl⟩⟩
  let evF : P →ₐ[K] F := MvPolynomial.aeval vF
  letI : Algebra P F := evF.toRingHom.toAlgebra
  letI : Algebra P E := (MvPolynomial.aeval v).toRingHom.toAlgebra
  letI : IsScalarTower K P F := IsScalarTower.of_algHom evF
  letI : IsScalarTower K P E := IsScalarTower.of_algHom (MvPolynomial.aeval v)
  have he : ∀ p : P, algebraMap P F p = algebraMap A F (e p) := by
    intro p
    apply Subtype.ext
    change (F.val.comp evF) p = (MvPolynomial.aeval v) p
    congr 1
    ext i
    simp [evF,vF]
  letI : IsFractionRing P F := IsFractionRing.of_ringEquiv_left e.toRingEquiv he
  letI : IsScalarTower P F E := IsScalarTower.of_algebraMap_eq fun p => by
    change (MvPolynomial.aeval v) p = (F.val.comp evF) p
    congr 1
    ext i
    simp [evF,vF]
  letI : Algebra.FormallyEtale P F :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  letI : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  letI : Algebra.FormallyEtale P E := Algebra.FormallyEtale.comp P F E
  let b : Module.Basis I E (E ⊗[P] Ω[P⁄K]) :=
    Algebra.TensorProduct.basis E (KaehlerDifferential.mvPolynomialBasis K I)
  let c : Module.Basis I E Ω[E⁄K] :=
    b.map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K P E)
  exact Module.finrank_eq_card_basis c

/-- For a finitely generated extension of a perfect field, the dimension of
the module of differentials equals the transcendence degree. -/
theorem finrank_kaehler_eq_trdeg [PerfectField K] [Algebra.EssFiniteType K E] :
    Module.finrank E Ω[E⁄K] = (Algebra.trdeg K E).toNat := by
  obtain ⟨s,hs,hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K E
  have hrange : Set.range ((↑) : s → E) = (s : Set E) := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x,hx⟩,rfl⟩
  letI : Algebra.IsSeparable
      (IntermediateField.adjoin K (Set.range ((↑) : s → E))) E := by
    rw [hrange]
    exact hsep
  rw [finrank_kaehler_of_transcendence_basis ((↑) : s → E) hs.1]
  rw [← hs.cardinalMk_eq_trdeg]
  simp

end TranscendenceBasis

section BaseChange

variable (K F E : Type*) [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]

/-- Separably generated field extension preserves independent
differentials. This is the injective half of the Jacobi--Zariski sequence. -/
theorem mapBaseChange_injective [Algebra.FormallySmooth F E] :
    Function.Injective (KaehlerDifferential.mapBaseChange K F E) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y,rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange K F E x).mp hx
  rw [Subsingleton.elim y 0,map_zero]

end BaseChange

section GeneratedField

variable {K E O : Type*} [Field K] [Field E] [Algebra K E]

def differentialSpan (q : O → E) : Submodule E Ω[E⁄K] :=
  Submodule.span E (Set.range fun i => KaehlerDifferential.D K E (q i))

/-- Passing from polynomial expressions to the field they generate does
not enlarge the span of their differentials. -/
theorem differential_mem_span_of_mem_adjoin (q : O → E)
    {x : E} (hx : x ∈ IntermediateField.adjoin K (Set.range q)) :
    KaehlerDifferential.D K E x ∈ differentialSpan (K := K) q := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      exact Submodule.subset_span ⟨i,rfl⟩
  | algebraMap x => simp [differentialSpan]
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (differentialSpan (K := K) q).add_mem ihx ihy
  | inv x hx ih =>
      rw [Derivation.leibniz_inv]
      exact (differentialSpan (K := K) q).smul_mem _ ih
  | mul x y hx hy ihx ihy =>
      rw [Derivation.leibniz]
      exact (differentialSpan (K := K) q).add_mem
        ((differentialSpan (K := K) q).smul_mem x ihy)
        ((differentialSpan (K := K) q).smul_mem y ihx)

/-- The actual differential span is the image of the base changed
differential module of the generated field. -/
theorem differentialSpan_eq_range (q : O → E) :
    differentialSpan (K := K) q =
      LinearMap.range (KaehlerDifferential.mapBaseChange K
        (IntermediateField.adjoin K (Set.range q)) E) := by
  let F := IntermediateField.adjoin K (Set.range q)
  let S := differentialSpan (K := K) q
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    refine ⟨(1 : E) ⊗ₜ KaehlerDifferential.D K F
      ⟨q i,IntermediateField.subset_adjoin K _ ⟨i,rfl⟩⟩,?_⟩
    rw [KaehlerDifferential.mapBaseChange_tmul,one_smul]
    change KaehlerDifferential.map K K F E (KaehlerDifferential.D K F _) = _
    rw [KaehlerDifferential.map_D]
    rfl
  · rintro _ ⟨x,rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simpa using S.zero_mem
    | add x y hx hy => simpa only [map_add] using S.add_mem hx hy
    | tmul x y =>
        rw [KaehlerDifferential.mapBaseChange_tmul]
        apply S.smul_mem
        have hy : y ∈ Submodule.span F (Set.range (KaehlerDifferential.D K F)) := by
          rw [KaehlerDifferential.span_range_derivation]
          trivial
        induction hy using Submodule.span_induction with
        | mem y hy =>
            obtain ⟨z,rfl⟩ := hy
            rw [KaehlerDifferential.map_D]
            exact differential_mem_span_of_mem_adjoin q z.property
        | zero => simpa using S.zero_mem
        | add y z hy hz ihy ihz => simpa only [map_add] using S.add_mem ihy ihz
        | smul c y hy ih =>
            rw [map_smul]
            exact S.smul_mem (algebraMap F E c) ih

/-- The differential rank counts the transcendence degree of the actual
field generated by the coordinate functions. -/
theorem finrank_differentialSpan [CharZero K] [Algebra.EssFiniteType K E]
    [Finite O] (q : O → E) :
    Module.finrank E (differentialSpan (K := K) q) =
      (Algebra.trdeg K (IntermediateField.adjoin K (Set.range q))).toNat := by
  let F := IntermediateField.adjoin K (Set.range q)
  letI : Algebra.EssFiniteType K F := IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite (Set.finite_range q))
  letI : Algebra.EssFiniteType F E := Algebra.EssFiniteType.of_comp K F E
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  letI : Algebra.FormallySmooth F E := inferInstance
  rw [differentialSpan_eq_range]
  rw [LinearMap.finrank_range_of_inj (mapBaseChange_injective K F E)]
  rw [Module.finrank_baseChange,finrank_kaehler_eq_trdeg]

/-- The Krull dimension of the literal substitution quotient equals the
dimension of the span of the coordinate differentials. -/
theorem coordinate_dimension_eq_differential_rank [CharZero K]
    [Algebra.EssFiniteType K E] [Fintype O] (q : O → E) :
    ringKrullDim (MvPolynomial O K ⧸
      RingHom.ker (MvPolynomial.aeval q : MvPolynomial O K →ₐ[K] E)) =
      (Module.finrank E (differentialSpan (K := K) q) : ℕ) := by
  let A := Algebra.adjoin K (Set.range q)
  let F := IntermediateField.adjoin K (Set.range q)
  letI : Algebra.FiniteType K A := Algebra.FiniteType.adjoin_of_finite (Set.finite_range q)
  have hAF : Algebra.trdeg K A = Algebra.trdeg K F := by
    simpa only [trdeg_eq_zero,add_zero] using (trdeg_add_eq K A (A := F))
  rw [ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientKerEquivRange (MvPolynomial.aeval q : MvPolynomial O K →ₐ[K] E)).toRingEquiv]
  change ringKrullDim ↥(MvPolynomial.aeval q : MvPolynomial O K →ₐ[K] E).range = _
  rw [← Algebra.adjoin_range_eq_range_aeval]
  rw [DimensionAlgebra.ringKrullDim_eq_trdeg_toNat K A,hAF,
    finrank_differentialSpan]

end GeneratedField

section RationalCoordinates

open RationalPartials
variable {K I O : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- The usual coordinate basis of the differentials of a rational
function field, constructed by étale localization of the polynomial basis. -/
def rationalDifferentialBasis :
    Module.Basis I (FunctionField K I) Ω[FunctionField K I⁄K] :=
  (Algebra.TensorProduct.basis (FunctionField K I)
    (KaehlerDifferential.mvPolynomialBasis K I)).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
        (PolynomialRing K I) (FunctionField K I))

@[simp] theorem rationalDifferentialBasis_apply (i : I) :
    rationalDifferentialBasis (K := K) i =
      KaehlerDifferential.D K (FunctionField K I) (coordinateVariable i) := by
  simp [rationalDifferentialBasis,coordinateVariable]

/-- Coordinates in the universal differential module are the previously
constructed rational partial derivatives. -/
theorem rationalDifferentialBasis_repr_D (f : FunctionField K I) (i : I) :
    (rationalDifferentialBasis (K := K)).repr
      (KaehlerDifferential.D K (FunctionField K I) f) i =
        partialDerivative i f := by
  have h : ((Finsupp.lapply i).comp
      (rationalDifferentialBasis (K := K)).repr.toLinearMap).compDer
        (KaehlerDifferential.D K (FunctionField K I)) = partialDerivative i := by
    apply RationalPartials.ext
    intro j
    change (rationalDifferentialBasis (K := K)).repr
      (KaehlerDifferential.D K (FunctionField K I) (coordinateVariable j)) i = _
    rw [← rationalDifferentialBasis_apply]
    simp only [Module.Basis.repr_self,partial_variable,Finsupp.single_apply,eq_comm]
  exact congrArg (fun d : Derivation K (FunctionField K I) (FunctionField K I) => d f) h

def rationalDifferentialCoordinates :
    Ω[FunctionField K I⁄K] ≃ₗ[FunctionField K I] (I → FunctionField K I) :=
  (rationalDifferentialBasis (K := K)).repr.trans
    (Finsupp.linearEquivFunOnFinite (FunctionField K I) (FunctionField K I) I)

@[simp] theorem rationalDifferentialCoordinates_D (f : FunctionField K I) :
    rationalDifferentialCoordinates (K := K)
      (KaehlerDifferential.D K (FunctionField K I) f) =
        fun i => partialDerivative i f := by
  ext i
  exact rationalDifferentialBasis_repr_D f i

def gradientSpan (q : O → FunctionField K I) :
    Submodule (FunctionField K I) (I → FunctionField K I) :=
  Submodule.span (FunctionField K I) (Set.range fun o i => partialDerivative i (q o))

theorem map_differentialSpan_eq_gradientSpan (q : O → FunctionField K I) :
    (differentialSpan (K := K) q).map
      (rationalDifferentialCoordinates (K := K)).toLinearMap = gradientSpan q := by
  rw [differentialSpan,Submodule.map_span]
  rw [← Set.range_comp]
  change Submodule.span (FunctionField K I)
    (Set.range fun o => rationalDifferentialCoordinates (K := K)
      (KaehlerDifferential.D K (FunctionField K I) (q o))) = gradientSpan q
  simp only [rationalDifferentialCoordinates_D,gradientSpan]

/-- The characteristic-zero Jacobian dimension theorem for the literal
rational parametrization, with all algebraic dependencies checked. -/
theorem coordinate_dimension_eq_gradient_rank [CharZero K] [Fintype O]
    (q : O → FunctionField K I) :
    ringKrullDim (MvPolynomial O K ⧸
      RingHom.ker (MvPolynomial.aeval q : MvPolynomial O K →ₐ[K] FunctionField K I)) =
      (Module.finrank (FunctionField K I) (gradientSpan q) : ℕ) := by
  letI : Algebra.EssFiniteType (PolynomialRing K I) (FunctionField K I) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (PolynomialRing K I))
  letI : Algebra.EssFiniteType K (FunctionField K I) :=
    Algebra.EssFiniteType.comp K (PolynomialRing K I) (FunctionField K I)
  rw [coordinate_dimension_eq_differential_rank,← map_differentialSpan_eq_gradientSpan]
  rw [LinearEquiv.finrank_map_eq]

end RationalCoordinates

end Sunlet.NetworkDifferentials
end
end NetworkStageSource_Sunlet_NetworkDifferentials
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkDifferentials"

section NetworkStageSource_Sunlet_NetworkCutDimension


/-!
# The dimension subtraction at a cut edge

The proof uses the actual products of coordinate rational functions in
disjoint parameter sets. After division by those nonzero functions, their
Jacobian rows are matched pairs. The cut-leaf Euler derivations give the
class grading, so the matched-pair linear algebra computes the rank exactly.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkCutDimension

open RationalPartials NetworkDifferentials NetworkGluing

section LinearAlgebra

variable {F A B I : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]

theorem finrank_span_pair_zero (f : I → A) :
    Module.finrank F (Submodule.span F (Set.range fun i => (f i,(0 : B)))) =
      Module.finrank F (Submodule.span F (Set.range f)) := by
  let T := LinearMap.inl F A B
  have hT : Function.Injective T := by
    intro x y h
    exact congrArg Prod.fst h
  have heq : (Submodule.span F (Set.range f)).map T =
      Submodule.span F (Set.range fun i => (f i,(0 : B))) := by
    rw [Submodule.map_span]
    rw [← Set.range_comp]
    rfl
  rw [← heq]
  exact (Submodule.equivMapOfInjective T hT _).finrank_eq.symm

theorem finrank_span_zero_pair (g : I → B) :
    Module.finrank F (Submodule.span F (Set.range fun i => ((0 : A),g i))) =
      Module.finrank F (Submodule.span F (Set.range g)) := by
  let T := LinearMap.inr F A B
  have hT : Function.Injective T := by
    intro x y h
    exact congrArg Prod.snd h
  have heq : (Submodule.span F (Set.range g)).map T =
      Submodule.span F (Set.range fun i => ((0 : A),g i)) := by
    rw [Submodule.map_span]
    rw [← Set.range_comp]
    rfl
  rw [← heq]
  exact (Submodule.equivMapOfInjective T hT _).finrank_eq.symm

end LinearAlgebra

variable {K P Q I J C : Type*} [Field K] [Fintype P] [Fintype Q]
  [DecidableEq P] [DecidableEq Q] [Fintype C] [DecidableEq C]

abbrev E := FunctionField K (P ⊕ Q)

local notation "𝔽" => E (K := K) (P := P) (Q := Q)

def logGradient (f : 𝔽) : (P ⊕ Q) → 𝔽 :=
  fun j => partialDerivative j f/f

def leftRow (f : 𝔽) : P → 𝔽 :=
  fun p => partialDerivative (.inl p) f/f

def rightRow (g : 𝔽) : Q → 𝔽 :=
  fun q => partialDerivative (.inr q) g/g

def splitGradient : ((P ⊕ Q) → 𝔽) ≃ₗ[𝔽] ((P → 𝔽) × (Q → 𝔽)) :=
  LinearEquiv.sumArrowLequivProdArrow P Q 𝔽 𝔽

theorem span_logGradient (f : I → 𝔽)
    (hf : ∀ i,f i≠0) :
    Submodule.span 𝔽 (Set.range fun i => logGradient (f i))=gradientSpan f := by
  have heq : (fun i => logGradient (f i)) =
      (fun i => (f i)⁻¹ • (fun j => partialDerivative j (f i))) := by
    funext i j
    simp only [logGradient,div_eq_mul_inv,Pi.smul_apply,smul_eq_mul,mul_comm]
  rw [heq]
  exact span_pointwise_smul (fun i j => partialDerivative j (f i))
    (fun i => (f i)⁻¹) (fun i => inv_ne_zero (hf i))

theorem split_logGradient_left (f : 𝔽)
    (h : ∀ q,partialDerivative (.inr q) f=0) :
    splitGradient (logGradient f)=(leftRow f,0) := by
  apply Prod.ext
  · rfl
  · funext q
    simp [splitGradient,logGradient,h]

theorem split_logGradient_right (g : 𝔽)
    (h : ∀ p,partialDerivative (.inl p) g=0) :
    splitGradient (logGradient g)=(0,rightRow g) := by
  apply Prod.ext
  · funext p
    simp [splitGradient,logGradient,h]
  · rfl

theorem split_logGradient_product
    (f g : 𝔽) (hf : f≠0) (hg : g≠0)
    (hfg : ∀ q,partialDerivative (.inr q) f=0)
    (hgf : ∀ p,partialDerivative (.inl p) g=0) :
    splitGradient (logGradient (f*g))=(leftRow f,rightRow g) := by
  apply Prod.ext
  · funext p
    simp only [splitGradient,LinearEquiv.sumArrowLequivProdArrow_apply_fst,
      logGradient,leftRow,Derivation.leibniz,smul_eq_mul,hgf,mul_zero,zero_add]
    field_simp [hf,hg] <;> ring
  · funext q
    simp only [splitGradient,LinearEquiv.sumArrowLequivProdArrow_apply_snd,
      logGradient,rightRow,Derivation.leibniz,smul_eq_mul,hfg,mul_zero,add_zero]
    field_simp [hf,hg] <;> ring

theorem finrank_gradientSpan_left
    (f : I → 𝔽) (hf : ∀ i,f i≠0)
    (hfg : ∀ i q,partialDerivative (.inr q) (f i)=0) :
    Module.finrank 𝔽 (gradientSpan f)=
      Module.finrank 𝔽 (Submodule.span 𝔽 (Set.range fun i => leftRow (f i))) := by
  rw [← span_logGradient f hf]
  rw [← LinearEquiv.finrank_map_eq (splitGradient (K := K))]
  rw [Submodule.map_span]
  rw [← Set.range_comp]
  change Module.finrank 𝔽 (Submodule.span 𝔽
    (Set.range fun i => splitGradient (logGradient (f i)))) = _
  have hrow : (fun i => splitGradient (logGradient (f i))) =
      (fun i => (leftRow (f i), (0 : Q → 𝔽))) := by
    funext i
    exact split_logGradient_left (f i) (hfg i)
  rw [hrow]
  exact finrank_span_pair_zero _

theorem finrank_gradientSpan_right
    (g : J → 𝔽) (hg : ∀ j,g j≠0)
    (hgf : ∀ j p,partialDerivative (.inl p) (g j)=0) :
    Module.finrank 𝔽 (gradientSpan g)=
      Module.finrank 𝔽 (Submodule.span 𝔽 (Set.range fun j => rightRow (g j))) := by
  rw [← span_logGradient g hg]
  rw [← LinearEquiv.finrank_map_eq (splitGradient (K := K))]
  rw [Submodule.map_span]
  rw [← Set.range_comp]
  change Module.finrank 𝔽 (Submodule.span 𝔽
    (Set.range fun j => splitGradient (logGradient (g j)))) = _
  have hrow : (fun j => splitGradient (logGradient (g j))) =
      (fun j => ((0 : P → 𝔽), rightRow (g j))) := by
    funext j
    exact split_logGradient_right (g j) (hgf j)
  rw [hrow]
  exact finrank_span_zero_pair _

/-- Exact rank of the matched product coordinates. The hypotheses on D and
H are the cut-leaf Euler identities and are verified from the original
edge monomials when this theorem is applied to a network. -/
theorem gradient_rank_matched_products
    (f : I → 𝔽) (g : J → 𝔽)
    (d : I → C) (e : J → C)
    (hf : ∀ i,f i≠0) (hg : ∀ j,g j≠0)
    (hfg : ∀ i q,partialDerivative (.inr q) (f i)=0)
    (hgf : ∀ j p,partialDerivative (.inl p) (g j)=0)
    (D : (P → 𝔽) →ₗ[𝔽] (C → 𝔽)) (H : (Q → 𝔽) →ₗ[𝔽] (C → 𝔽))
    (hDf : ∀ i,D (leftRow (f i))=Pi.single (d i) 1)
    (hHg : ∀ j,H (rightRow (g j))=Pi.single (e j) 1)
    (a : C → I) (b : C → J) (ha : ∀ c,d (a c)=c) (hb : ∀ c,e (b c)=c) :
    Module.finrank 𝔽 (gradientSpan (fun p : Matched d e => f p.val.1*g p.val.2)) =
      Module.finrank 𝔽 (gradientSpan f)+Module.finrank 𝔽 (gradientSpan g)-Fintype.card C := by
  rw [finrank_gradientSpan_left f hf hfg,finrank_gradientSpan_right g hg hgf]
  rw [← span_logGradient (fun p : Matched d e => f p.val.1*g p.val.2)
    (fun p => mul_ne_zero (hf p.val.1) (hg p.val.2))]
  rw [← LinearEquiv.finrank_map_eq (splitGradient (K := K))]
  rw [Submodule.map_span]
  rw [← Set.range_comp]
  change Module.finrank 𝔽 (Submodule.span 𝔽
    (Set.range fun p : Matched d e => splitGradient
      (logGradient (f p.val.1*g p.val.2)))) = _
  have hrow : (fun p : Matched d e => splitGradient
      (logGradient (f p.val.1*g p.val.2))) =
      (fun p : Matched d e => (leftRow (f p.val.1), rightRow (g p.val.2))) := by
    funext p
    exact split_logGradient_product _ _ (hf p.val.1) (hg p.val.2)
      (hfg p.val.1) (hgf p.val.2)
  rw [hrow]
  exact finrank_matchedSpan_subspaces (fun i => leftRow (f i))
    (fun j => rightRow (g j)) d e D H hDf hHg a b ha hb

/-- The cut-edge formula for the actual coordinate-ring quotients. All
three rings are defined by substitution of the displayed functions. -/
theorem dimension_matched_products [CharZero K] [Fintype I] [Fintype J]
    (f : I → 𝔽) (g : J → 𝔽)
    (d : I → C) (e : J → C)
    (hf : ∀ i,f i≠0) (hg : ∀ j,g j≠0)
    (hfg : ∀ i q,partialDerivative (.inr q) (f i)=0)
    (hgf : ∀ j p,partialDerivative (.inl p) (g j)=0)
    (D : (P → 𝔽) →ₗ[𝔽] (C → 𝔽)) (H : (Q → 𝔽) →ₗ[𝔽] (C → 𝔽))
    (hDf : ∀ i,D (leftRow (f i))=Pi.single (d i) 1)
    (hHg : ∀ j,H (rightRow (g j))=Pi.single (e j) 1)
    (a : C → I) (b : C → J) (ha : ∀ c,d (a c)=c) (hb : ∀ c,e (b c)=c)
    (d₁ d₂ : ℕ)
    (hd₁ : ringKrullDim (MvPolynomial I K ⧸ RingHom.ker (MvPolynomial.aeval (R := K) f))=d₁)
    (hd₂ : ringKrullDim (MvPolynomial J K ⧸ RingHom.ker (MvPolynomial.aeval (R := K) g))=d₂) :
    ringKrullDim (MvPolynomial (Matched d e) K ⧸
      RingHom.ker (MvPolynomial.aeval (R := K) fun p : Matched d e => f p.val.1*g p.val.2)) =
        (d₁+d₂-Fintype.card C : ℕ) := by
  classical
  rw [coordinate_dimension_eq_gradient_rank] at hd₁ hd₂ ⊢
  have h₁ : Module.finrank 𝔽 (gradientSpan f)=d₁ := by exact_mod_cast hd₁
  have h₂ : Module.finrank 𝔽 (gradientSpan g)=d₂ := by exact_mod_cast hd₂
  rw [gradient_rank_matched_products f g d e hf hg hfg hgf D H hDf hHg a b ha hb,h₁,h₂]

end Sunlet.NetworkCutDimension
end
end NetworkStageSource_Sunlet_NetworkCutDimension
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkCutDimension"

section NetworkStageSource_Sunlet_NetworkFourierTerms


/-!
# Finite sums of Fourier tree monomials

The displayed-tree parametrization is a finite sum of monomials with
coefficient one. This module checks its nonvanishing, the cut-leaf Euler
identities, invariance under relabelling, and the product identity obtained
by combining independent displayed-tree choices.
-/

noncomputable section
open scoped BigOperators


namespace Sunlet.NetworkDifferentials

open RationalPartials
variable {K P Q : Type*} [Field K] [DecidableEq P]

/-- Rational partial differentiation agrees exactly with polynomial
partial differentiation on the polynomial subring. -/
theorem partial_polynomial (i : P) (p : MvPolynomial P K) :
    partialDerivative i
      (algebraMap (MvPolynomial P K) (FunctionField K P) p)=
        algebraMap (MvPolynomial P K) (FunctionField K P) (MvPolynomial.pderiv i p) := by
  have h : (partialDerivative (k := K) i).compAlgebraMap (MvPolynomial P K)=
      (Algebra.linearMap (MvPolynomial P K) (FunctionField K P)).compDer
        (MvPolynomial.pderiv i) := by
    apply MvPolynomial.derivation_ext
    intro j
    change partialDerivative i (coordinateVariable j)=
      algebraMap (MvPolynomial P K) (FunctionField K P) (MvPolynomial.pderiv i (MvPolynomial.X j))
    rw [partial_variable]
    simp [MvPolynomial.pderiv_X,Pi.single_apply]
  exact congrArg (fun D : Derivation K (MvPolynomial P K) (FunctionField K P) => D p) h

theorem pderiv_rename_inl_inr [DecidableEq Q] (q : Q) (p : MvPolynomial P K) :
    MvPolynomial.pderiv (Sum.inr q) (MvPolynomial.rename Sum.inl p)=0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr => simp [hp,hr]
  | mul_X p i hp => simp [Derivation.leibniz,hp,MvPolynomial.pderiv_X,Pi.single_apply]

theorem pderiv_rename_inr_inl [DecidableEq Q] (p : P) (q : MvPolynomial Q K) :
    MvPolynomial.pderiv (Sum.inl p) (MvPolynomial.rename Sum.inr q)=0 := by
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add q r hq hr => simp [hq,hr]
  | mul_X q i hq => simp [Derivation.leibniz,hq,MvPolynomial.pderiv_X,Pi.single_apply]

end Sunlet.NetworkDifferentials
end
end NetworkStageSource_Sunlet_NetworkFourierTerms
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkFourierTerms"

section NetworkStageSource_Sunlet_NetworkPolynomialGluing


/-!
# Polynomial cut-edge dimension theorem

This specializes the rational differential calculation to polynomial
component maps in disjoint edge variables. The hypotheses are the literal
cut-leaf Euler identities, nonzero coordinate polynomials, and occurrence
of every class. The conclusion concerns the ordinary substitution kernels
of the polynomial maps, rather than a stipulated dimension invariant.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkPolynomialGluing

open RationalPartials NetworkDifferentials NetworkCutDimension NetworkGluing

variable {K P Q I J C : Type*} [Field K] [Fintype P] [Fintype Q]
  [DecidableEq P] [DecidableEq Q] [Fintype C] [DecidableEq C]

abbrev CombinedField := FunctionField K (P ⊕ Q)

local notation "𝔽" => CombinedField (K := K) (P := P) (Q := Q)

def polynomialInclusion : MvPolynomial (P ⊕ Q) K →ₐ[K] 𝔽 :=
  IsScalarTower.toAlgHom K (MvPolynomial (P ⊕ Q) K) (FunctionField K (P ⊕ Q))

def leftInclusion : MvPolynomial P K →ₐ[K] 𝔽 :=
  polynomialInclusion.comp (MvPolynomial.rename Sum.inl)

def rightInclusion : MvPolynomial Q K →ₐ[K] 𝔽 :=
  polynomialInclusion.comp (MvPolynomial.rename Sum.inr)

theorem polynomialInclusion_injective :
    Function.Injective (polynomialInclusion (K := K) (P := P) (Q := Q)) :=
  IsFractionRing.injective _ _

theorem leftInclusion_injective :
    Function.Injective (leftInclusion (K := K) (P := P) (Q := Q)) :=
  polynomialInclusion_injective.comp (MvPolynomial.rename_injective _ Sum.inl_injective)

theorem rightInclusion_injective :
    Function.Injective (rightInclusion (K := K) (P := P) (Q := Q)) :=
  polynomialInclusion_injective.comp (MvPolynomial.rename_injective _ Sum.inr_injective)

theorem left_partial (i : P) (p : MvPolynomial P K) :
    partialDerivative (Sum.inl i) (leftInclusion (Q := Q) p)=
      leftInclusion (MvPolynomial.pderiv i p) := by
  rw [leftInclusion,AlgHom.comp_apply]
  change partialDerivative (Sum.inl i)
    (algebraMap (MvPolynomial (P ⊕ Q) K) _ (MvPolynomial.rename Sum.inl p))=_
  rw [partial_polynomial,MvPolynomial.pderiv_rename Sum.inl_injective]
  rfl

theorem right_partial (j : Q) (q : MvPolynomial Q K) :
    partialDerivative (Sum.inr j) (rightInclusion (P := P) q)=
      rightInclusion (MvPolynomial.pderiv j q) := by
  rw [rightInclusion,AlgHom.comp_apply]
  change partialDerivative (Sum.inr j)
    (algebraMap (MvPolynomial (P ⊕ Q) K) _ (MvPolynomial.rename Sum.inr q))=_
  rw [partial_polynomial,MvPolynomial.pderiv_rename Sum.inr_injective]
  rfl

theorem left_cross_partial (j : Q) (p : MvPolynomial P K) :
    partialDerivative (Sum.inr j) (leftInclusion p)=0 := by
  change partialDerivative (Sum.inr j)
    (algebraMap (MvPolynomial (P ⊕ Q) K) _ (MvPolynomial.rename Sum.inl p))=0
  rw [partial_polynomial,pderiv_rename_inl_inr,map_zero]

theorem right_cross_partial (i : P) (q : MvPolynomial Q K) :
    partialDerivative (Sum.inl i) (rightInclusion q)=0 := by
  change partialDerivative (Sum.inl i)
    (algebraMap (MvPolynomial (P ⊕ Q) K) _ (MvPolynomial.rename Sum.inr q))=0
  rw [partial_polynomial,pderiv_rename_inr_inl,map_zero]

def leftGrading (leaf : C → P) :
    (P → 𝔽) →ₗ[𝔽] (C → 𝔽) where
  toFun v c := leftInclusion (MvPolynomial.X (leaf c))*v (leaf c)
  map_add' v w := by funext c; simp [mul_add]
  map_smul' a v := by funext c; simp [mul_left_comm,mul_assoc]

def rightGrading (leaf : C → Q) :
    (Q → 𝔽) →ₗ[𝔽] (C → 𝔽) where
  toFun v c := rightInclusion (MvPolynomial.X (leaf c))*v (leaf c)
  map_add' v w := by funext c; simp [mul_add]
  map_smul' a v := by funext c; simp [mul_left_comm,mul_assoc]

theorem left_euler_grading (p : MvPolynomial P K) (hp : p≠0)
    (leaf : C → P) (d : C)
    (heuler : ∀ c,MvPolynomial.X (leaf c)*MvPolynomial.pderiv (leaf c) p=
      if c=d then p else 0) :
    leftGrading (Q := Q) leaf (leftRow (leftInclusion p))=Pi.single d 1 := by
  ext c
  change leftInclusion (MvPolynomial.X (leaf c)) *
    (partialDerivative (Sum.inl (leaf c)) (leftInclusion p)/leftInclusion p)=_
  rw [left_partial,← mul_div_assoc,← map_mul,heuler]
  have h : leftInclusion (Q := Q) p≠0 :=
    fun hz => hp (leftInclusion_injective (hz.trans (map_zero _).symm))
  by_cases hc : c=d <;> simp [hc,Pi.single_apply,h]

theorem right_euler_grading (q : MvPolynomial Q K) (hq : q≠0)
    (leaf : C → Q) (d : C)
    (heuler : ∀ c,MvPolynomial.X (leaf c)*MvPolynomial.pderiv (leaf c) q=
      if c=d then q else 0) :
    rightGrading (P := P) leaf (rightRow (rightInclusion q))=Pi.single d 1 := by
  ext c
  change rightInclusion (MvPolynomial.X (leaf c)) *
    (partialDerivative (Sum.inr (leaf c)) (rightInclusion q)/rightInclusion q)=_
  rw [right_partial,← mul_div_assoc,← map_mul,heuler]
  have h : rightInclusion (P := P) q≠0 :=
    fun hz => hq (rightInclusion_injective (hz.trans (map_zero _).symm))
  by_cases hc : c=d <;> simp [hc,Pi.single_apply,h]

theorem kernel_aeval_of_injective {A B O : Type*} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) (hφ : Function.Injective φ)
    (p : O → A) :
    RingHom.ker (MvPolynomial.aeval (R := K) (fun o => φ (p o)))=
      RingHom.ker (MvPolynomial.aeval (R := K) p) := by
  have hc : MvPolynomial.aeval (R := K) (fun o => φ (p o))=φ.comp (MvPolynomial.aeval (R := K) p) := by
    ext o
    simp
  rw [hc]
  exact RingHom.ker_comp_of_injective _ hφ

/-- Different index sets for the same literal coordinate functions give
isomorphic coordinate rings. This allows redundant orbit-indexed
coordinates without changing the model. -/
def coordinateRingEquivOfRange {A O O' : Type*} [CommRing A] [Algebra K A]
    (p : O → A) (q : O' → A) (h : Set.range p=Set.range q) :
    (MvPolynomial O K ⧸ RingHom.ker (MvPolynomial.aeval (R := K) p)) ≃ₐ[K]
      (MvPolynomial O' K ⧸ RingHom.ker (MvPolynomial.aeval (R := K) q)) := by
  have he : (MvPolynomial.aeval (R := K) p).range=(MvPolynomial.aeval (R := K) q).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval,← Algebra.adjoin_range_eq_range_aeval,h]
  exact (Ideal.quotientKerEquivRange (MvPolynomial.aeval (R := K) p)).trans
    ((Subalgebra.equivOfEq _ _ he).trans
      (Ideal.quotientKerEquivRange (MvPolynomial.aeval (R := K) q)).symm)

theorem dimension_eq_of_range {A O O' : Type*} [CommRing A] [Algebra K A]
    (p : O → A) (q : O' → A) (h : Set.range p=Set.range q) :
    ringKrullDim (MvPolynomial O K ⧸ RingHom.ker (MvPolynomial.aeval (R := K) p))=
      ringKrullDim (MvPolynomial O' K ⧸ RingHom.ker (MvPolynomial.aeval (R := K) q)) :=
  ringKrullDim_eq_of_ringEquiv (coordinateRingEquivOfRange p q h).toRingEquiv

def pairedPolynomial (p : I → MvPolynomial P K) (q : J → MvPolynomial Q K)
    (ij : I × J) : MvPolynomial (P ⊕ Q) K :=
  MvPolynomial.rename Sum.inl (p ij.1)*MvPolynomial.rename Sum.inr (q ij.2)

/-- The complete polynomial cut-edge dimension formula. -/
theorem dimension_pairedPolynomial [CharZero K] [Fintype I] [Fintype J]
    (p : I → MvPolynomial P K) (q : J → MvPolynomial Q K)
    (d : I → C) (e : J → C) (leafP : C → P) (leafQ : C → Q)
    (hp : ∀ i,p i≠0) (hq : ∀ j,q j≠0)
    (hP : ∀ i c,MvPolynomial.X (leafP c)*MvPolynomial.pderiv (leafP c) (p i)=
      if c=d i then p i else 0)
    (hQ : ∀ j c,MvPolynomial.X (leafQ c)*MvPolynomial.pderiv (leafQ c) (q j)=
      if c=e j then q j else 0)
    (a : C → I) (b : C → J) (ha : ∀ c,d (a c)=c) (hb : ∀ c,e (b c)=c)
    (d₁ d₂ : ℕ)
    (hd₁ : ringKrullDim (MvPolynomial I K ⧸ RingHom.ker (MvPolynomial.aeval (R := K) p))=d₁)
    (hd₂ : ringKrullDim (MvPolynomial J K ⧸ RingHom.ker (MvPolynomial.aeval (R := K) q))=d₂) :
    ringKrullDim (MvPolynomial (Matched d e) K ⧸ RingHom.ker
      (MvPolynomial.aeval (R := K) fun ij : Matched d e => pairedPolynomial p q ij.val)) =
        (d₁+d₂-Fintype.card C : ℕ) := by
  classical
  let f : I → 𝔽 := fun i => leftInclusion (p i)
  let g : J → 𝔽 := fun j => rightInclusion (q j)
  have hf : ∀ i,f i≠0 := fun i hz =>
    hp i (leftInclusion_injective (hz.trans (map_zero _).symm))
  have hg : ∀ j,g j≠0 := fun j hz =>
    hq j (rightInclusion_injective (hz.trans (map_zero _).symm))
  have hdf : ringKrullDim (MvPolynomial I K ⧸ RingHom.ker (MvPolynomial.aeval (R := K) f))=d₁ := by
    rw [kernel_aeval_of_injective leftInclusion leftInclusion_injective]
    exact hd₁
  have hdg : ringKrullDim (MvPolynomial J K ⧸ RingHom.ker (MvPolynomial.aeval (R := K) g))=d₂ := by
    rw [kernel_aeval_of_injective rightInclusion rightInclusion_injective]
    exact hd₂
  have h := dimension_matched_products f g d e hf hg
    (fun i j => left_cross_partial j (p i)) (fun j i => right_cross_partial i (q j))
    (leftGrading leafP) (rightGrading leafQ)
    (fun i => left_euler_grading (p i) (hp i) leafP (d i) (hP i))
    (fun j => right_euler_grading (q j) (hq j) leafQ (e j) (hQ j))
    a b ha hb d₁ d₂ hdf hdg
  have hk : RingHom.ker (MvPolynomial.aeval (R := K) fun ij : Matched d e => f ij.val.1*g ij.val.2)=
      RingHom.ker (MvPolynomial.aeval (R := K) fun ij : Matched d e => pairedPolynomial p q ij.val) := by
    convert kernel_aeval_of_injective polynomialInclusion polynomialInclusion_injective
      (fun ij : Matched d e => pairedPolynomial p q ij.val) using 1
    congr 1
    ext ij
    simp [f,g,pairedPolynomial,leftInclusion,rightInclusion]
  rwa [hk] at h

end Sunlet.NetworkPolynomialGluing
end
end NetworkStageSource_Sunlet_NetworkPolynomialGluing
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkPolynomialGluing"

section NetworkStageSource_Sunlet_NetworkOrientation


/-!
# Reversing edge directions without assuming inverse-stable orbits

Reversing an edge negates its conserved group flow. If negation permutes
the class labels, the corresponding Fourier polynomial is obtained by
that permutation of the edge parameters. Hence the full substitution
ideal is independent of the auxiliary choices of edge direction.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkOrientation

open NetworkIncidenceFlows NetworkFlowGluing

variable {V E L S G C K : Type*} [Fintype V] [Fintype E] [Fintype L] [Fintype S]
  [DecidableEq V] [DecidableEq E] [AddCommGroup G] [Fintype G] [DecidableEq G]
  [DecidableEq C] [CommSemiring K]

def flipData (N : Data V E L S) (flip : E → Bool) : Data V E L S where
  source e := if flip e then N.target e else N.source e
  target e := if flip e then N.source e else N.target e
  leaf := N.leaf
  active := N.active

def flipFlow (flip : E → Bool) (x : E → G) : E → G :=
  fun e => if flip e then -x e else x e

@[simp] theorem flipFlow_twice (flip : E → Bool) (x : E → G) :
    flipFlow flip (flipFlow flip x)=x := by
  funext e
  cases h : flip e <;> simp [flipFlow,h]

theorem divergence_flip (N : Data V E L S) (flip : E → Bool) (x : E → G) (v : V) :
    divergence (flipData N flip).source (flipData N flip).target (flipFlow flip x) v=
      divergence N.source N.target x v := by
  simp only [divergence,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  cases hf : flip e <;> simp [flipData,flipFlow,hf] <;> split_ifs <;> simp <;> abel

theorem valid_flip_iff (N : Data V E L S) (flip : E → Bool) (g : L → G)
    (s : S) (x : E → G) :
    Valid (flipData N flip) g s (flipFlow flip x) ↔ Valid N g s x := by
  have hz (e : E) : flipFlow flip x e=0 ↔ x e=0 := by
    cases h : flip e <;> simp [flipFlow,h]
  change ((∀ e,e∉N.active s → flipFlow flip x e=0) ∧
    ∀ v,divergence (flipData N flip).source (flipData N flip).target
      (flipFlow flip x) v=leafBoundary N.leaf g v) ↔
    ((∀ e,e∉N.active s → x e=0) ∧
      ∀ v,divergence N.source N.target x v=leafBoundary N.leaf g v)
  simp only [hz,divergence_flip]

def flipTermEquiv (N : Data V E L S) (flip : E → Bool) (g : L → G) :
    Term N g ≃ Term (flipData N flip) g where
  toFun t := ⟨(t.val.1,flipFlow flip t.val.2),
    (valid_flip_iff N flip g t.val.1 t.val.2).mpr t.property⟩
  invFun t := ⟨(t.val.1,flipFlow flip t.val.2),by
    apply (valid_flip_iff N flip g t.val.1 (flipFlow flip t.val.2)).mp
    simpa only [flipFlow_twice] using t.property⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact flipFlow_twice flip t.val.2
  right_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact flipFlow_twice flip t.val.2

def parameterEquiv (flip : E → Bool) (neg : C ≃ C) : (E × C) ≃ (E × C) where
  toFun ec := (ec.1,if flip ec.1 then neg ec.2 else ec.2)
  invFun ec := (ec.1,if flip ec.1 then neg.symm ec.2 else ec.2)
  left_inv ec := by rcases ec with ⟨e,c⟩; cases h : flip e <;> simp [h]
  right_inv ec := by rcases ec with ⟨e,c⟩; cases h : flip e <;> simp [h]

theorem rename_termPolynomial (N : Data V E L S) (flip : E → Bool)
    (q : G → C) (neg : C ≃ C) (hneg : ∀ a,q (-a)=neg (q a))
    (g : L → G) (t : Term N g) :
    MvPolynomial.rename (parameterEquiv flip neg)
      (termPolynomial (K := K) N q t)=
        termPolynomial (flipData N flip) q (flipTermEquiv N flip g t) := by
  rw [termPolynomial_eq_prod,termPolynomial_eq_prod,map_prod]
  apply Finset.prod_congr rfl
  intro e he
  cases hf : flip e <;>
    simp [MvPolynomial.rename_X,parameterEquiv,flipTermEquiv,flipFlow,hf,hneg]

theorem coordinate_flip (N : Data V E L S) (flip : E → Bool)
    (q : G → C) (neg : C ≃ C) (hneg : ∀ a,q (-a)=neg (q a))
    (g : Flow L G) :
    NetworkIncidenceFlows.coordinate (K := K) (flipData N flip) q g=
      MvPolynomial.rename (parameterEquiv flip neg) (NetworkIncidenceFlows.coordinate N q g) := by
  symm
  rw [coordinate_eq_sum_terms,coordinate_eq_sum_terms,map_sum]
  exact Fintype.sum_equiv (flipTermEquiv N flip g.val) _ _
    (rename_termPolynomial N flip q neg hneg g.val)

/-- Arbitrary orientation changes preserve the complete polynomial
equation ideal. Negation is a class permutation, not an assumed equality
of each class with its negative. -/
theorem kernel_coordinate_flip (N : Data V E L S) (flip : E → Bool)
    (q : G → C) (neg : C ≃ C) (hneg : ∀ a,q (-a)=neg (q a)) :
    RingHom.ker (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) (flipData N flip) q))=
      RingHom.ker (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) N q)) := by
  have h : MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) (flipData N flip) q)=
      (MvPolynomial.rename (parameterEquiv flip neg)).comp
        (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) N q)) := by
    ext g : 1
    simpa only [MvPolynomial.aeval_X,AlgHom.comp_apply] using coordinate_flip (K := K) N flip q neg hneg g
  rw [h]
  ext p
  change MvPolynomial.rename (R := K) (parameterEquiv flip neg)
      (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) N q) p)=0 ↔
    MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) N q) p=0
  constructor
  · intro hp
    apply MvPolynomial.rename_injective (R := K) _ (parameterEquiv flip neg).injective
    simpa only [map_zero] using hp
  · intro hp
    simp only [hp,map_zero]

end Sunlet.NetworkOrientation
end
end NetworkStageSource_Sunlet_NetworkOrientation
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkOrientation"

section NetworkStageSource_Sunlet_NetworkIncidenceIso


/-!
# Reindexing the literal incidence model

Vertex, edge, leaf, and displayed-choice bijections transport conserved
flows explicitly. The Fourier coordinates are related by an injective
renaming of the actual edge parameters. Thus graph isomorphisms give
isomorphic coordinate rings, with every leaf assignment retained.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkIncidenceIso

open NetworkIncidenceFlows NetworkFlowGluing

variable {V E L S V' E' L' S' G C K : Type*}
  [Fintype V] [Fintype E] [Fintype L] [Fintype S]
  [Fintype V'] [Fintype E'] [Fintype L'] [Fintype S']
  [DecidableEq V] [DecidableEq E] [DecidableEq V'] [DecidableEq E']
  [AddCommGroup G] [Fintype G] [DecidableEq G] [DecidableEq C]

structure Iso (N : Data V E L S) (M : Data V' E' L' S') where
  vertices : V ≃ V'
  edges : E ≃ E'
  leaves : L ≃ L'
  choices : S ≃ S'
  source : ∀ e,vertices (N.source e)=M.source (edges e)
  target : ∀ e,vertices (N.target e)=M.target (edges e)
  leaf : ∀ l,vertices (N.leaf l)=M.leaf (leaves l)
  active : ∀ s e,e∈N.active s ↔ edges e∈M.active (choices s)

def Iso.symm {N : Data V E L S} {M : Data V' E' L' S'} (f : Iso N M) : Iso M N where
  vertices := f.vertices.symm
  edges := f.edges.symm
  leaves := f.leaves.symm
  choices := f.choices.symm
  source e := by
    apply f.vertices.injective
    simpa using (f.source (f.edges.symm e)).symm
  target e := by
    apply f.vertices.injective
    simpa using (f.target (f.edges.symm e)).symm
  leaf l := by
    apply f.vertices.injective
    simpa using (f.leaf (f.leaves.symm l)).symm
  active s e := by
    simpa using (f.active (f.choices.symm s) (f.edges.symm e)).symm

namespace Iso

variable {N : Data V E L S} {M : Data V' E' L' S'} (f : Iso N M)

def flowEquiv : Flow L G ≃ Flow L' G where
  toFun g := ⟨fun l => g.val (f.leaves.symm l),by
    have h := Fintype.sum_equiv f.leaves g.val (fun l => g.val (f.leaves.symm l))
      (fun l => by simp)
    exact h.symm.trans g.property⟩
  invFun g := ⟨fun l => g.val (f.leaves l),by
    have h := Fintype.sum_equiv f.leaves (fun l => g.val (f.leaves l)) g.val (fun l => rfl)
    exact h.trans g.property⟩
  left_inv g := by apply Subtype.ext; funext l; simp
  right_inv g := by apply Subtype.ext; funext l; simp

theorem divergence_transport (x : E → G) (v : V) :
    divergence M.source M.target (fun e => x (f.edges.symm e)) (f.vertices v)=
      divergence N.source N.target x v := by
  unfold divergence
  congr 1
  · symm
    apply Fintype.sum_equiv f.edges
    intro e
    rw [← f.source]
    simp
  · symm
    apply Fintype.sum_equiv f.edges
    intro e
    rw [← f.target]
    simp

theorem leafBoundary_transport (g : L → G) (v : V) :
    leafBoundary M.leaf (fun l => g (f.leaves.symm l)) (f.vertices v)=
      leafBoundary N.leaf g v := by
  unfold leafBoundary
  symm
  apply Fintype.sum_equiv f.leaves
  intro l
  rw [← f.leaf]
  simp

theorem valid_transport_iff (g : L → G) (s : S) (x : E → G) :
    Valid M (fun l => g (f.leaves.symm l)) (f.choices s) (fun e => x (f.edges.symm e)) ↔
      Valid N g s x := by
  constructor
  · intro h
    constructor
    · intro e he
      have he' : f.edges e∉M.active (f.choices s) := fun h' => he ((f.active s e).mpr h')
      simpa using h.1 (f.edges e) he'
    · intro v
      simpa only [f.divergence_transport,f.leafBoundary_transport] using h.2 (f.vertices v)
  · intro h
    constructor
    · intro e he
      have he' : f.edges.symm e∉N.active s := by
        intro h'
        exact he (by simpa using (f.active s (f.edges.symm e)).mp h')
      exact h.1 _ he'
    · intro v
      obtain ⟨v,rfl⟩ := f.vertices.surjective v
      rw [f.divergence_transport,f.leafBoundary_transport]
      exact h.2 v

def termEquiv (g : L → G) : Term N g ≃ Term M (fun l => g (f.leaves.symm l)) where
  toFun t := ⟨(f.choices t.val.1,fun e => t.val.2 (f.edges.symm e)),
    (f.valid_transport_iff g t.val.1 t.val.2).mpr t.property⟩
  invFun t := ⟨(f.choices.symm t.val.1,fun e => t.val.2 (f.edges e)),by
    apply (f.valid_transport_iff g (f.choices.symm t.val.1) (fun e => t.val.2 (f.edges e))).mp
    simpa only [Equiv.apply_symm_apply] using t.property⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · exact f.choices.symm_apply_apply _
    · funext e; exact congrArg t.val.2 (f.edges.symm_apply_apply e)
  right_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · exact f.choices.apply_symm_apply _
    · funext e; exact congrArg t.val.2 (f.edges.apply_symm_apply e)

def parameterEquiv : (E × C) ≃ (E' × C) := f.edges.prodCongr (Equiv.refl C)

variable [CommSemiring K]

theorem termPolynomial_transport (q : G → C) (g : L → G) (t : Term N g) :
    MvPolynomial.rename (f.parameterEquiv (C := C)) (termPolynomial (K := K) N q t)=
      termPolynomial M q (f.termEquiv g t) := by
  rw [termPolynomial_eq_prod,termPolynomial_eq_prod,map_prod]
  apply Finset.prod_bij (fun e _ => f.edges e)
  · intro e he
    exact (f.active t.val.1 e).mp he
  · intro e he e' he' h
    exact f.edges.injective h
  · intro e he
    refine ⟨f.edges.symm e,?_,by simp⟩
    change e∈M.active (f.choices t.val.1) at he
    exact (f.active t.val.1 (f.edges.symm e)).mpr (by simpa using he)
  · intro e he
    simp [MvPolynomial.rename_X,parameterEquiv,termEquiv]

theorem coordinate_transport (q : G → C) (g : Flow L G) :
    MvPolynomial.rename (f.parameterEquiv (C := C)) (NetworkIncidenceFlows.coordinate (K := K) N q g)=
      NetworkIncidenceFlows.coordinate M q (f.flowEquiv g) := by
  rw [coordinate_eq_sum_terms,coordinate_eq_sum_terms,map_sum]
  exact Fintype.sum_equiv (f.termEquiv g.val) _ _ (f.termPolynomial_transport q g.val)

include f in
theorem terms_exist_transport
    (h : ∀ g : Flow L G,Nonempty (Term N g.val)) :
    ∀ g : Flow L' G,Nonempty (Term M g.val) := by
  intro g
  obtain ⟨t⟩ := h (f.flowEquiv.symm g)
  have he := congrArg Subtype.val (f.flowEquiv.apply_symm_apply g)
  change (fun l => (f.flowEquiv.symm g).val (f.leaves.symm l))=g.val at he
  rw [← he]
  exact ⟨f.termEquiv (f.flowEquiv.symm g).val t⟩

include f in
/-- Literal reindexing of a finite incidence network preserves the
ordinary Krull dimension of its Fourier image coordinate ring. -/
theorem dimension_transport {k : Type*} [Field k] (q : G → C) :
    ringKrullDim (MvPolynomial (Flow L G) k ⧸ RingHom.ker
      (MvPolynomial.aeval (R := k) (NetworkIncidenceFlows.coordinate (K := k) N q)))=
      ringKrullDim (MvPolynomial (Flow L' G) k ⧸ RingHom.ker
        (MvPolynomial.aeval (R := k) (NetworkIncidenceFlows.coordinate (K := k) M q))) := by
  have hc : MvPolynomial.aeval (R := k) (fun g : Flow L G => NetworkIncidenceFlows.coordinate (K := k) M q (f.flowEquiv g))=
      (MvPolynomial.rename (f.parameterEquiv (C := C))).comp
        (MvPolynomial.aeval (R := k) (NetworkIncidenceFlows.coordinate (K := k) N q)) := by
    ext g : 1
    simpa only [MvPolynomial.aeval_X,AlgHom.comp_apply] using (f.coordinate_transport (K := k) q g).symm
  have hk : RingHom.ker (MvPolynomial.aeval (R := k)
      (fun g : Flow L G => NetworkIncidenceFlows.coordinate (K := k) M q (f.flowEquiv g)))=
        RingHom.ker (MvPolynomial.aeval (R := k) (NetworkIncidenceFlows.coordinate (K := k) N q)) := by
    rw [hc]
    ext p
    change MvPolynomial.rename (R := k) (f.parameterEquiv (C := C))
        (MvPolynomial.aeval (R := k) (NetworkIncidenceFlows.coordinate (K := k) N q) p)=0 ↔
      MvPolynomial.aeval (R := k) (NetworkIncidenceFlows.coordinate (K := k) N q) p=0
    constructor
    · intro hp
      apply MvPolynomial.rename_injective (R := k) _ (f.parameterEquiv (C := C)).injective
      simpa only [map_zero] using hp
    · intro hp
      simp only [hp,map_zero]
  have hr : Set.range (fun g : Flow L G => NetworkIncidenceFlows.coordinate (K := k) M q (f.flowEquiv g))=
      Set.range (NetworkIncidenceFlows.coordinate (K := k) M q) := by
    ext p
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨f.flowEquiv g,rfl⟩
    · rintro ⟨g,rfl⟩
      exact ⟨f.flowEquiv.symm g,by simp⟩
  rw [← hk]
  exact NetworkPolynomialGluing.dimension_eq_of_range _ _ hr

end Iso

end Sunlet.NetworkIncidenceIso
end
end NetworkStageSource_Sunlet_NetworkIncidenceIso
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkIncidenceIso"

section NetworkStageSource_Sunlet_NetworkGraphOrientation


/-!
# Independence of the auxiliary directions on an actual graph

The two possible directions of each undirected edge are compared using
the literal `Sym2` endpoint identity. The general incidence edge-flip
theorem then gives equality of the full model ideals.
-/

noncomputable section

namespace Sunlet.NetworkGraphOrientation

open SimpleGraph NetworkGraphDecomposition NetworkGraphModel NetworkIncidenceFlows

variable {V G C K : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup G] [Fintype G] [DecidableEq G] [DecidableEq C]

theorem data_ext {V E L S : Type*} [Fintype E]
    {N M : Data V E L S} (hs : N.source=M.source) (ht : N.target=M.target)
    (hl : N.leaf=M.leaf) (ha : N.active=M.active) : N=M := by
  cases N
  cases M
  simp_all

theorem source_ne_target (H : SimpleGraph V) (O : Orientation H) (e : H.edgeSet) :
    O.source e≠O.target e := by
  apply SimpleGraph.ne_of_adj
  apply (SimpleGraph.mem_edgeSet (G := H)).mp
  rw [O.edge_eq]
  exact e.property

def flip (H : SimpleGraph V) (O P : Orientation H) (e : H.edgeSet) : Bool :=
  decide (P.source e=O.target e)

theorem endpoints (H : SimpleGraph V) (O P : Orientation H) (e : H.edgeSet) :
    (if flip H O P e then O.target e else O.source e)=P.source e ∧
    (if flip H O P e then O.source e else O.target e)=P.target e := by
  have he : s(P.source e,P.target e)=s(O.source e,O.target e) :=
    (P.edge_eq e).trans (O.edge_eq e).symm
  rcases Sym2.eq_iff.mp he with h|h
  · simp [flip,h.1,h.2,source_ne_target H O e]
  · simp [flip,h.1,h.2]

theorem flipData_eq (H : SimpleGraph V) (O P : Orientation H) (R : ReticulationData H) :
    NetworkOrientation.flipData (incidenceData H O R) (flip H O P)=incidenceData H P R := by
  apply data_ext
  · funext e
    exact (endpoints H O P e).1
  · funext e
    exact (endpoints H O P e).2
  · rfl
  · rfl

theorem terms_exist (H : SimpleGraph V) (O P : Orientation H) (R : ReticulationData H)
    (h : ∀ g : NetworkFlowGluing.Flow (Leaf H) G,Nonempty (Term (incidenceData H O R) g.val)) :
    ∀ g : NetworkFlowGluing.Flow (Leaf H) G,Nonempty (Term (incidenceData H P R) g.val) := by
  intro g
  rw [← flipData_eq H O P R]
  obtain ⟨t⟩ := h g
  exact ⟨NetworkOrientation.flipTermEquiv (incidenceData H O R) (flip H O P) g.val t⟩

/-- For an orbit partition, reversing any subset of edge orientations
preserves the exact defining ideal, with every leaf coordinate fixed. -/
theorem definingIdeal_eq [CommSemiring K] (H : SimpleGraph V)
    (O P : Orientation H) (R : ReticulationData H)
    (q : G → C) (neg : C ≃ C) (hneg : ∀ a,q (-a)=neg (q a)) :
    NetworkGraphModel.definingIdeal (K := K) H P R q=
      NetworkGraphModel.definingIdeal (K := K) H O R q := by
  change RingHom.ker (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (incidenceData H P R) q))=
    RingHom.ker (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (incidenceData H O R) q))
  rw [← flipData_eq H O P R]
  exact NetworkOrientation.kernel_coordinate_flip (incidenceData H O R) (flip H O P) q neg hneg

end Sunlet.NetworkGraphOrientation
end
end NetworkStageSource_Sunlet_NetworkGraphOrientation
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkGraphOrientation"

section NetworkStageSource_Sunlet_NetworkIncidenceCut


/-!
# Cutting the literal conserved-flow model

The bridge is oriented from the right component to the left component.
Its left cut leaf is outgoing and its right cut leaf is incoming. Both
copies therefore carry the same edge-flow value, while the two new leaf
labels have opposite signs. This convention avoids a hidden negation in
the edge-parameter identification.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkIncidenceCut

open NetworkIncidenceFlows NetworkFlowGluing

variable {V W E F L R S T G C K : Type*}
  [Fintype V] [Fintype W] [Fintype E] [Fintype F]
  [Fintype L] [Fintype R] [Fintype S] [Fintype T]
  [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
  [AddCommGroup G] [Fintype G] [DecidableEq G] [DecidableEq C]

def outCut (N : Data V E L S) (a : V) : Data (Option V) (Option E) (Option L) S where
  source e := match e with | none => none | some e => some (N.source e)
  target e := match e with | none => some a | some e => some (N.target e)
  leaf l := match l with | none => none | some l => some (N.leaf l)
  active s := insert none ((N.active s).image some)

def inCut (N : Data V E L S) (a : V) : Data (Option V) (Option E) (Option L) S where
  source e := match e with | none => some a | some e => some (N.source e)
  target e := match e with | none => none | some e => some (N.target e)
  leaf l := match l with | none => none | some l => some (N.leaf l)
  active s := insert none ((N.active s).image some)

/-- Actual joining of the two endpoint-incidence systems. -/
def glue (N : Data V E L S) (a : V) (M : Data W F R T) (b : W) :
    Data (V ⊕ W) (Option (E ⊕ F)) (L ⊕ R) (S × T) where
  source e := match e with
    | none => .inr b
    | some (.inl e) => .inl (N.source e)
    | some (.inr f) => .inr (M.source f)
  target e := match e with
    | none => .inl a
    | some (.inl e) => .inl (N.target e)
    | some (.inr f) => .inr (M.target f)
  leaf l := match l with | .inl l => .inl (N.leaf l) | .inr r => .inr (M.leaf r)
  active s := insert none (((N.active s.1).image (fun e => some (.inl e))) ∪
    ((M.active s.2).image (fun f => some (.inr f))))

@[simp] theorem outCut_divergence_none (N : Data V E L S) (a : V)
    (x : Option E → G) : divergence (outCut N a).source (outCut N a).target x none=x none := by
  simp [divergence,outCut,Fintype.sum_option]

@[simp] theorem inCut_divergence_none (N : Data V E L S) (a : V)
    (x : Option E → G) : divergence (inCut N a).source (inCut N a).target x none=-x none := by
  simp [divergence,inCut,Fintype.sum_option]

@[simp] theorem cut_leafBoundary_none (N : Data V E L S) (a : V) (g : Option L → G) :
    leafBoundary (outCut N a).leaf g none=g none := by
  simp [leafBoundary,outCut,Fintype.sum_option]

@[simp] theorem inCut_leafBoundary_none (N : Data V E L S) (a : V) (g : Option L → G) :
    leafBoundary (inCut N a).leaf g none=g none := by
  simp [leafBoundary,inCut,Fintype.sum_option]

@[simp] theorem outCut_divergence_some (N : Data V E L S) (a v : V)
    (x : Option E → G) :
    divergence (outCut N a).source (outCut N a).target x (some v)=
      divergence N.source N.target (fun e => x (some e)) v-
        (if a=v then x none else 0) := by
  simp [divergence,outCut,Fintype.sum_option] <;> abel

@[simp] theorem inCut_divergence_some (N : Data V E L S) (a v : V)
    (x : Option E → G) :
    divergence (inCut N a).source (inCut N a).target x (some v)=
      divergence N.source N.target (fun e => x (some e)) v+
        (if a=v then x none else 0) := by
  simp [divergence,inCut,Fintype.sum_option] <;> abel

@[simp] theorem outCut_leafBoundary_some (N : Data V E L S) (a v : V) (g : Option L → G) :
    leafBoundary (outCut N a).leaf g (some v)=
      leafBoundary N.leaf (fun l => g (some l)) v := by
  simp [leafBoundary,outCut,Fintype.sum_option]

@[simp] theorem inCut_leafBoundary_some (N : Data V E L S) (a v : V) (g : Option L → G) :
    leafBoundary (inCut N a).leaf g (some v)=
      leafBoundary N.leaf (fun l => g (some l)) v := by
  simp [leafBoundary,inCut,Fintype.sum_option]

@[simp] theorem glue_divergence_left (N : Data V E L S) (a v : V)
    (M : Data W F R T) (b : W) (x : Option (E ⊕ F) → G) :
    divergence (glue N a M b).source (glue N a M b).target x (.inl v)=
      divergence N.source N.target (fun e => x (some (.inl e))) v-
        (if a=v then x none else 0) := by
  simp [divergence,glue,Fintype.sum_option,Fintype.sum_sum_type] <;> abel

@[simp] theorem glue_divergence_right (N : Data V E L S) (a : V)
    (M : Data W F R T) (b w : W) (x : Option (E ⊕ F) → G) :
    divergence (glue N a M b).source (glue N a M b).target x (.inr w)=
      divergence M.source M.target (fun f => x (some (.inr f))) w+
        (if b=w then x none else 0) := by
  simp [divergence,glue,Fintype.sum_option,Fintype.sum_sum_type] <;> abel

@[simp] theorem glue_leafBoundary_left (N : Data V E L S) (a v : V)
    (M : Data W F R T) (b : W) (g : L ⊕ R → G) :
    leafBoundary (glue N a M b).leaf g (.inl v)=
      leafBoundary N.leaf (fun l => g (.inl l)) v := by
  simp [leafBoundary,glue,Fintype.sum_sum_type]

@[simp] theorem glue_leafBoundary_right (N : Data V E L S) (a : V)
    (M : Data W F R T) (b w : W) (g : L ⊕ R → G) :
    leafBoundary (glue N a M b).leaf g (.inr w)=
      leafBoundary M.leaf (fun r => g (.inr r)) w := by
  simp [leafBoundary,glue,Fintype.sum_sum_type]

theorem bridge_value (N : Data V E L S) (a : V) (M : Data W F R T) (b : W)
    {g : L ⊕ R → G} (t : Term (glue N a M b) g) :
    t.val.2 none=-(∑ l,g (.inl l)) := by
  have h := fun v => t.property.2 (Sum.inl v)
  simp only [glue_divergence_left,glue_leafBoundary_left] at h
  have hh := congrArg (fun z : V → G => ∑ v,z v) (funext h)
  simp only [Finset.sum_sub_distrib,sum_divergence,sum_leafBoundary,
    Finset.sum_ite_eq,Finset.mem_univ,if_true,zero_sub] at hh
  exact eq_neg_of_add_eq_zero_left (by rw [← hh]; abel)

def leftTerm (N : Data V E L S) (a : V) (M : Data W F R T) (b : W)
    (g : Flow (L ⊕ R) G) (t : Term (glue N a M b) g.val) :
    Term (outCut N a) (leftFlow g).val := by
  let x : Option E → G := fun e => match e with
    | none => t.val.2 none
    | some e => t.val.2 (some (.inl e))
  refine ⟨(t.val.1.1,x),?_,?_⟩
  · intro e he
    cases e with
    | none => exact (he (by simp [outCut])).elim
    | some e =>
        apply t.property.1
        simpa [outCut,glue] using he
  · intro v
    cases v with
    | none =>
        simpa [x,leftFlow] using bridge_value N a M b t
    | some v =>
        simpa [x,leftFlow] using t.property.2 (Sum.inl v)

def rightTerm (N : Data V E L S) (a : V) (M : Data W F R T) (b : W)
    (g : Flow (L ⊕ R) G) (t : Term (glue N a M b) g.val) :
    Term (inCut M b) (rightFlow g).val := by
  let x : Option F → G := fun f => match f with
    | none => t.val.2 none
    | some f => t.val.2 (some (.inr f))
  refine ⟨(t.val.1.2,x),?_,?_⟩
  · intro f hf
    cases f with
    | none => exact (hf (by simp [inCut])).elim
    | some f =>
        apply t.property.1
        simpa [inCut,glue] using hf
  · intro w
    cases w with
    | none =>
        have hv := bridge_value N a M b t
        have hc := cut_labels_opposite g
        change -(∑ l,g.val (.inl l))=-(-(∑ r,g.val (.inr r))) at hc
        simp only [inCut_divergence_none,inCut_leafBoundary_none,x,rightFlow]
        rw [hv,hc,neg_neg]
    | some w =>
        simpa [x,rightFlow] using t.property.2 (Sum.inr w)

theorem cut_term_values_equal (N : Data V E L S) (a : V) (M : Data W F R T) (b : W)
    (g : Flow (L ⊕ R) G)
    (u : Term (outCut N a) (leftFlow g).val)
    (v : Term (inCut M b) (rightFlow g).val) : u.val.2 none=v.val.2 none := by
  have hu := u.property.2 none
  have hv := v.property.2 none
  simp only [outCut_divergence_none,cut_leafBoundary_none] at hu
  simp only [inCut_divergence_none,inCut_leafBoundary_none] at hv
  rw [hu,cut_labels_opposite,← hv,neg_neg]

def joinTerm (N : Data V E L S) (a : V) (M : Data W F R T) (b : W)
    (g : Flow (L ⊕ R) G)
    (u : Term (outCut N a) (leftFlow g).val)
    (v : Term (inCut M b) (rightFlow g).val) : Term (glue N a M b) g.val := by
  let x : Option (E ⊕ F) → G := fun e => match e with
    | none => u.val.2 none
    | some (.inl e) => u.val.2 (some e)
    | some (.inr f) => v.val.2 (some f)
  refine ⟨((u.val.1,v.val.1),x),?_,?_⟩
  · intro e he
    rcases e with _ | (e | f)
    · exact (he (by simp [glue])).elim
    · apply u.property.1
      simpa [outCut,glue] using he
    · apply v.property.1
      simpa [inCut,glue] using he
  · intro w
    cases w with
    | inl w => simpa [x,leftFlow] using u.property.2 (some w)
    | inr w =>
        simpa [x,rightFlow,cut_term_values_equal N a M b g u v] using v.property.2 (some w)

/-- Every conserved flow on the joined graph corresponds to exactly one
pair of conserved component flows. Both directions are explicit. -/
def cutTermEquiv (N : Data V E L S) (a : V) (M : Data W F R T) (b : W)
    (g : Flow (L ⊕ R) G) :
    Term (glue N a M b) g.val ≃
      Term (outCut N a) (leftFlow g).val × Term (inCut M b) (rightFlow g).val where
  toFun t := (leftTerm N a M b g t,rightTerm N a M b g t)
  invFun t := joinTerm N a M b g t.1 t.2
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext e
      rcases e with _ | (e | f) <;> rfl
  right_inv uv := by
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · funext e
        cases e <;> rfl
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · funext f
        cases f with
        | none => exact cut_term_values_equal N a M b g uv.1 uv.2
        | some f => rfl

end Sunlet.NetworkIncidenceCut
end
end NetworkStageSource_Sunlet_NetworkIncidenceCut
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkIncidenceCut"

section NetworkStageSource_Sunlet_NetworkGraphCut


/-!
# The actual graph bridge cut and its Fourier incidence data

The component and edge bijections come from a bridge in the original
simple graph. Reticulation pairs are lifted from the same original cycle
edges. The local and joined incidence maps therefore retain the original
graph, all displayed-tree choices, and all leaf coordinates.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkGraphCut

open SimpleGraph NetworkGraphDecomposition NetworkGraphModel NetworkIncidenceFlows
open NetworkIncidenceCut

attribute [local instance] Classical.propDecidable

variable {V G C K : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup G] [Fintype G] [DecidableEq G] [DecidableEq C]

/-- Reticulation edges restrict through actual induced cycles, including
the common reticulation vertex. -/
def restrictReticulation (H : SimpleGraph V) (R : ReticulationData H) (U : Set V) :
    ReticulationData (H.induce U) where
  incoming c b := inducedCycleEdge H U c (R.incoming (cycleMapInduce H U c) b)
    (R.cycle_mem (cycleMapInduce H U c) b)
  distinct c := by
    intro h
    have hh := congrArg (inducedEdgeEmbedding H U) h
    simp only [inducedCycleEdge_map] at hh
    exact R.distinct (cycleMapInduce H U c) hh
  cycle_mem c b := inducedCycleEdge_mem H U c _ _
  common_vertex c := by
    apply inducedEdges_common_vertex H U
    simp only [inducedCycleEdge_map]
    exact R.common_vertex (cycleMapInduce H U c)

@[simp] theorem restrict_incoming_map (H : SimpleGraph V) (R : ReticulationData H)
    (U : Set V) (c : Cycle (H.induce U)) (b : Bool) :
    inducedEdgeEmbedding H U ((restrictReticulation H R U).incoming c b)=
      R.incoming (cycleMapInduce H U c) b :=
  inducedCycleEdge_map H U c (R.incoming (cycleMapInduce H U c) b)
    (R.cycle_mem (cycleMapInduce H U c) b)

def cutReticulation (H : SimpleGraph V) (R : ReticulationData H) (u v : V) :
    ReticulationData (cutGraph H u v) := restrictReticulation H R (cutVertices H u v)

@[simp] theorem cut_incoming_map (H : SimpleGraph V) (R : ReticulationData H)
    (u v : V) (c : Cycle (cutGraph H u v)) (b : Bool) :
    inducedEdgeEmbedding H (cutVertices H u v) ((cutReticulation H R u v).incoming c b)=
      R.incoming (cycleMapInduce H (cutVertices H u v) c) b :=
  restrict_incoming_map H R (cutVertices H u v) c b

/-- Orient an actual graph by transporting the source and target of
incidence data whose endpoint pair is proved to be its actual edge. -/
def orientationOfData {W E L S : Type*} [Fintype E]
    (H : SimpleGraph V) (N : Data W E L S) (vertices : W ≃ V) (edges : E ≃ H.edgeSet)
    (hend : ∀ e,s(vertices (N.source e),vertices (N.target e))=(edges e).val) :
    Orientation H where
  source e := vertices (N.source (edges.symm e))
  target e := vertices (N.target (edges.symm e))
  edge_eq e := by simpa using hend (edges.symm e)

def coreData (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) :
    Data (cutSide H u v) (CoreEdge H u v) (OldLeafSide H u v) (Choice (cutGraph H u v)) where
  source := (canonicalOrientation (H.induce (cutSide H u v))).source
  target := (canonicalOrientation (H.induce (cutSide H u v))).target
  leaf l := ⟨l.val.val,l.property⟩
  active s := Finset.univ.filter fun e =>
    cutEdgeEquiv H u v hadj hb (some e)∈
      activeEdges (cutGraph H u v) (cutReticulation H R u v) s

def attachment (H : SimpleGraph V) (u v : V) : cutSide H u v :=
  ⟨u,show (cutBase H u v).Reachable u u from SimpleGraph.Reachable.refl u⟩

theorem cutEdgeEquiv_apply (H : SimpleGraph V) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) (e : Option (CoreEdge H u v)) :
    cutEdgeEquiv H u v hadj hb e=cutEdgeMap H u v hadj e := rfl

theorem coreEdgeEquiv_apply (H : SimpleGraph V) (u v : V)
    (hH : H.Connected) (hadj : H.Adj u v) (hb : H.IsBridge s(u,v))
    (e : Option (CoreEdge H u v ⊕ CoreEdge H v u)) :
    coreEdgeEquiv H u v hH hadj hb e=coreEdgeSumMap H u v hadj e := rfl

theorem cut_none_active (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) (s : Choice (cutGraph H u v)) :
    cutEdgeEquiv H u v hadj hb none∈activeEdges (cutGraph H u v) (cutReticulation H R u v) s := by
  simp only [activeEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  intro c he
  have hh := congrArg (inducedEdgeEmbedding H (cutVertices H u v)) he
  have hmap : (⟨s(u,v),hadj⟩ : H.edgeSet)=
      R.incoming (cycleMapInduce H (cutVertices H u v) c) (s c) := by
    simpa [cutEdgeEquiv_apply] using hh
  apply bridge_not_mem_cycle H hb (cycleMapInduce H (cutVertices H u v) c)
  exact Eq.mpr (congrArg (fun e : H.edgeSet =>
    e.val∈(cycleMapInduce H (cutVertices H u v) c).val) hmap) (R.cycle_mem _ _)

theorem incoming_has_core (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v))
    (c : Cycle (cutGraph H u v)) (b : Bool) :
    ∃ e : CoreEdge H u v,
      inducedEdgeEmbedding H (cutSide H u v) e=
        R.incoming (cycleMapInduce H (cutVertices H u v) c) b := by
  let ec := (cutReticulation H R u v).incoming c b
  obtain ⟨d,hd⟩ := (cutEdgeEquiv H u v hadj hb).surjective ec
  cases d with
  | none =>
    have ha := cut_none_active H R u v hadj hb (fun _ => b)
    have hn : cutEdgeEquiv H u v hadj hb none≠ec := by
      exact (Finset.mem_filter.mp ha).2 c
    exact (hn hd).elim
  | some e =>
    refine ⟨e,?_⟩
    have hh := congrArg (inducedEdgeEmbedding H (cutVertices H u v)) hd
    simpa [cutEdgeEquiv_apply,ec] using hh

theorem outCut_endpoints (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) (e : Option (CoreEdge H u v)) :
    s((cutVertexEquiv H u v hb).symm
        ((outCut (coreData H R u v hadj hb) (attachment H u v)).source e),
      (cutVertexEquiv H u v hb).symm
        ((outCut (coreData H R u v hadj hb) (attachment H u v)).target e))=
      (cutEdgeEquiv H u v hadj hb e).val := by
  cases e with
  | none => exact Sym2.eq_swap
  | some e =>
    let O := canonicalOrientation (H.induce (cutSide H u v))
    let emb : cutSide H u v → cutVertices H u v := fun x => ⟨x.val,Or.inl x.property⟩
    change Sym2.map emb s(O.source e,O.target e)=Sym2.map emb e.val
    rw [O.edge_eq]

theorem inCut_endpoints (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) (e : Option (CoreEdge H u v)) :
    s((cutVertexEquiv H u v hb).symm
        ((inCut (coreData H R u v hadj hb) (attachment H u v)).source e),
      (cutVertexEquiv H u v hb).symm
        ((inCut (coreData H R u v hadj hb) (attachment H u v)).target e))=
      (cutEdgeEquiv H u v hadj hb e).val := by
  cases e with
  | none => rfl
  | some e =>
    let O := canonicalOrientation (H.induce (cutSide H u v))
    let emb : cutSide H u v → cutVertices H u v := fun x => ⟨x.val,Or.inl x.property⟩
    change Sym2.map emb s(O.source e,O.target e)=Sym2.map emb e.val
    rw [O.edge_eq]

def outOrientation (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) : Orientation (cutGraph H u v) :=
  orientationOfData (cutGraph H u v)
    (outCut (coreData H R u v hadj hb) (attachment H u v))
    (cutVertexEquiv H u v hb).symm (cutEdgeEquiv H u v hadj hb)
    (outCut_endpoints H R u v hadj hb)

def inOrientation (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) : Orientation (cutGraph H u v) :=
  orientationOfData (cutGraph H u v)
    (inCut (coreData H R u v hadj hb) (attachment H u v))
    (cutVertexEquiv H u v hb).symm (cutEdgeEquiv H u v hadj hb)
    (inCut_endpoints H R u v hadj hb)

def outIso (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) :
    NetworkIncidenceIso.Iso
      (outCut (coreData H R u v hadj hb) (attachment H u v))
      (incidenceData (cutGraph H u v) (outOrientation H R u v hadj hb)
        (cutReticulation H R u v)) where
  vertices := (cutVertexEquiv H u v hb).symm
  edges := cutEdgeEquiv H u v hadj hb
  leaves := (cutLeafEquiv H u v hadj hb).symm
  choices := Equiv.refl _
  source e := by simp only [incidenceData,outOrientation,orientationOfData,Equiv.symm_apply_apply]
  target e := by simp only [incidenceData,outOrientation,orientationOfData,Equiv.symm_apply_apply]
  leaf l := by cases l <;> rfl
  active s e := by
    cases e with
    | none => simpa [outCut,incidenceData] using cut_none_active H R u v hadj hb s
    | some e =>
      simp [outCut,coreData,incidenceData] <;>
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]

def inIso (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) :
    NetworkIncidenceIso.Iso
      (inCut (coreData H R u v hadj hb) (attachment H u v))
      (incidenceData (cutGraph H u v) (inOrientation H R u v hadj hb)
        (cutReticulation H R u v)) where
  vertices := (cutVertexEquiv H u v hb).symm
  edges := cutEdgeEquiv H u v hadj hb
  leaves := (cutLeafEquiv H u v hadj hb).symm
  choices := Equiv.refl _
  source e := by simp only [incidenceData,inOrientation,orientationOfData,Equiv.symm_apply_apply]
  target e := by simp only [incidenceData,inOrientation,orientationOfData,Equiv.symm_apply_apply]
  leaf l := by cases l <;> rfl
  active s e := by
    cases e with
    | none => simpa [inCut,incidenceData] using cut_none_active H R u v hadj hb s
    | some e =>
      simp [inCut,coreData,incidenceData] <;>
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem swap_bridge (H : SimpleGraph V) (u v : V) (hb : H.IsBridge s(u,v)) :
    H.IsBridge s(v,u) := by simpa only [Sym2.eq_swap] using hb

def choiceEquiv (H : SimpleGraph V) (u v : V) (hH : H.Connected) (hb : H.IsBridge s(u,v)) :
    Choice (cutGraph H u v) × Choice (cutGraph H v u) ≃ Choice H where
  toFun ss c := Sum.elim ss.1 ss.2 ((cutCycleEquiv H u v hH hb).symm c)
  invFun s := (fun c =>s (cutCycleEquiv H u v hH hb (.inl c)),
    fun c =>s (cutCycleEquiv H u v hH hb (.inr c)))
  left_inv ss := by
    apply Prod.ext <;> funext c <;>
      simp only [Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]
  right_inv s := by
    funext c
    obtain ⟨d,rfl⟩ := (cutCycleEquiv H u v hH hb).surjective c
    cases d <;> simp only [Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]

@[simp] theorem choiceEquiv_left (H : SimpleGraph V) (u v : V)
    (hH : H.Connected) (hb : H.IsBridge s(u,v))
    (ss : Choice (cutGraph H u v) × Choice (cutGraph H v u)) (c : Cycle (cutGraph H u v)) :
    choiceEquiv H u v hH hb ss (cycleMapInduce H (cutVertices H u v) c)=ss.1 c := by
  change choiceEquiv H u v hH hb ss (cutCycleEquiv H u v hH hb (.inl c))=ss.1 c
  change Sum.elim ss.1 ss.2 ((cutCycleEquiv H u v hH hb).symm
    (cutCycleEquiv H u v hH hb (.inl c)))=ss.1 c
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem choiceEquiv_right (H : SimpleGraph V) (u v : V)
    (hH : H.Connected) (hb : H.IsBridge s(u,v))
    (ss : Choice (cutGraph H u v) × Choice (cutGraph H v u)) (c : Cycle (cutGraph H v u)) :
    choiceEquiv H u v hH hb ss (cycleMapInduce H (cutVertices H v u) c)=ss.2 c := by
  change choiceEquiv H u v hH hb ss (cutCycleEquiv H u v hH hb (.inr c))=ss.2 c
  change Sum.elim ss.1 ss.2 ((cutCycleEquiv H u v hH hb).symm
    (cutCycleEquiv H u v hH hb (.inr c)))=ss.2 c
  rw [Equiv.symm_apply_apply]
  rfl

theorem core_active_iff (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v))
    (s : Choice (cutGraph H u v)) (e : CoreEdge H u v) :
    e∈(coreData H R u v hadj hb).active s ↔
      ∀ c : Cycle (cutGraph H u v),inducedEdgeEmbedding H (cutSide H u v) e≠
        R.incoming (cycleMapInduce H (cutVertices H u v) c) (s c) := by
  simp only [coreData,Finset.mem_filter,Finset.mem_univ,true_and,activeEdges]
  apply forall_congr'
  intro c
  constructor
  · intro hn he
    apply hn
    apply (inducedEdgeEmbedding H (cutVertices H u v)).injective
    simpa [cutEdgeEquiv_apply] using he
  · intro hn he
    apply hn
    have hh := congrArg (inducedEdgeEmbedding H (cutVertices H u v)) he
    simpa [cutEdgeEquiv_apply] using hh

theorem global_left_active_iff (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hH : H.Connected) (hadj : H.Adj u v) (hb : H.IsBridge s(u,v))
    (ss : Choice (cutGraph H u v) × Choice (cutGraph H v u)) (e : CoreEdge H u v) :
    inducedEdgeEmbedding H (cutSide H u v) e∈activeEdges H R (choiceEquiv H u v hH hb ss) ↔
      e∈(coreData H R u v hadj hb).active ss.1 := by
  rw [core_active_iff]
  simp only [activeEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h c
    simpa using h (cycleMapInduce H (cutVertices H u v) c)
  · intro h c
    obtain ⟨d,rfl⟩ := (cutCycleEquiv H u v hH hb).surjective c
    cases d with
    | inl c =>
      change inducedEdgeEmbedding H (cutSide H u v) e≠
        R.incoming (cycleMapInduce H (cutVertices H u v) c)
          (choiceEquiv H u v hH hb ss (cycleMapInduce H (cutVertices H u v) c))
      simpa only [choiceEquiv_left] using h c
    | inr c =>
      change inducedEdgeEmbedding H (cutSide H u v) e≠
        R.incoming (cycleMapInduce H (cutVertices H v u) c)
          (choiceEquiv H u v hH hb ss (cycleMapInduce H (cutVertices H v u) c))
      rw [choiceEquiv_right]
      obtain ⟨f,hf⟩ := incoming_has_core H R v u hadj.symm (swap_bridge H u v hb) c (ss.2 c)
      rw [← hf]
      exact coreEdges_distinct H u v hH hb e f

theorem global_right_active_iff (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hH : H.Connected) (hadj : H.Adj u v) (hb : H.IsBridge s(u,v))
    (ss : Choice (cutGraph H u v) × Choice (cutGraph H v u)) (e : CoreEdge H v u) :
    inducedEdgeEmbedding H (cutSide H v u) e∈activeEdges H R (choiceEquiv H u v hH hb ss) ↔
      e∈(coreData H R v u hadj.symm (swap_bridge H u v hb)).active ss.2 := by
  rw [core_active_iff]
  simp only [activeEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h c
    simpa using h (cycleMapInduce H (cutVertices H v u) c)
  · intro h c
    obtain ⟨d,rfl⟩ := (cutCycleEquiv H u v hH hb).surjective c
    cases d with
    | inl c =>
      change inducedEdgeEmbedding H (cutSide H v u) e≠
        R.incoming (cycleMapInduce H (cutVertices H u v) c)
          (choiceEquiv H u v hH hb ss (cycleMapInduce H (cutVertices H u v) c))
      rw [choiceEquiv_left]
      obtain ⟨f,hf⟩ := incoming_has_core H R u v hadj hb c (ss.1 c)
      rw [← hf]
      exact (coreEdges_distinct H u v hH hb f e).symm
    | inr c =>
      change inducedEdgeEmbedding H (cutSide H v u) e≠
        R.incoming (cycleMapInduce H (cutVertices H v u) c)
          (choiceEquiv H u v hH hb ss (cycleMapInduce H (cutVertices H v u) c))
      simpa only [choiceEquiv_right] using h c

def joinedData (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) :=
  glue (coreData H R u v hadj hb) (attachment H u v)
    (coreData H R v u hadj.symm (swap_bridge H u v hb)) (attachment H v u)

theorem joined_endpoints (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hH : H.Connected) (hadj : H.Adj u v) (hb : H.IsBridge s(u,v))
    (e : Option (CoreEdge H u v ⊕ CoreEdge H v u)) :
    s(coreVertexEquiv H u v hH hb ((joinedData H R u v hadj hb).source e),
      coreVertexEquiv H u v hH hb ((joinedData H R u v hadj hb).target e))=
        (coreEdgeEquiv H u v hH hadj hb e).val := by
  rcases e with _|e
  · exact Sym2.eq_swap
  · rcases e with e|e
    · let O := canonicalOrientation (H.induce (cutSide H u v))
      change Sym2.map Subtype.val s(O.source e,O.target e)=Sym2.map Subtype.val e.val
      rw [O.edge_eq]
    · let O := canonicalOrientation (H.induce (cutSide H v u))
      change Sym2.map Subtype.val s(O.source e,O.target e)=Sym2.map Subtype.val e.val
      rw [O.edge_eq]

def joinedOrientation (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hH : H.Connected) (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) : Orientation H :=
  orientationOfData H (joinedData H R u v hadj hb)
    (coreVertexEquiv H u v hH hb) (coreEdgeEquiv H u v hH hadj hb)
    (joined_endpoints H R u v hH hadj hb)

/-- The generic incidence glue is proved isomorphic to the original
graph model. Its vertex, edge, leaf and displayed-choice bijections are
all constructed from the actual bridge cut. -/
def joinedIso (H : SimpleGraph V) (R : ReticulationData H) (u v : V)
    (hH : H.Connected) (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) :
    NetworkIncidenceIso.Iso (joinedData H R u v hadj hb)
      (incidenceData H (joinedOrientation H R u v hH hadj hb) R) where
  vertices := coreVertexEquiv H u v hH hb
  edges := coreEdgeEquiv H u v hH hadj hb
  leaves := (leafPartitionEquiv H u v hH hb).symm
  choices := choiceEquiv H u v hH hb
  source e := by simp only [incidenceData,joinedOrientation,orientationOfData,Equiv.symm_apply_apply]
  target e := by simp only [incidenceData,joinedOrientation,orientationOfData,Equiv.symm_apply_apply]
  leaf l := by cases l <;> rfl
  active ss e := by
    rcases e with _|e
    · have ha := bridge_mem_active H R (⟨s(u,v),hadj⟩ : H.edgeSet) hb
        (choiceEquiv H u v hH hb ss)
      simpa [joinedData,glue,incidenceData,coreEdgeEquiv_apply,coreEdgeSumMap] using ha
    · rcases e with e|e
      · simpa [joinedData,glue,incidenceData,coreEdgeEquiv_apply,coreEdgeSumMap] using
          (global_left_active_iff H R u v hH hadj hb ss e).symm
      · simpa [joinedData,glue,incidenceData,coreEdgeEquiv_apply,coreEdgeSumMap] using
          (global_right_active_iff H R u v hH hadj hb ss e).symm

end Sunlet.NetworkGraphCut
end
end NetworkStageSource_Sunlet_NetworkGraphCut
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkGraphCut"

section NetworkStageSource_Sunlet_NetworkIncidencePolynomialCut


/-!
# Polynomial factorization across the actual cut

The conserved-flow bijection is now applied to the finite polynomial sum.
Multiplying the two bridge parameter families gives the original graph
map, and setting one family to one is a specialization inverse. Therefore
the joined Fourier map and the component product have the same complete
ideal of polynomial equations.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkIncidenceCut

open NetworkIncidenceFlows NetworkFlowGluing

variable {V W E F L R S T G C K : Type*}
  [Fintype V] [Fintype W] [Fintype E] [Fintype F]
  [Fintype L] [Fintype R] [Fintype S] [Fintype T]
  [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
  [AddCommGroup G] [Fintype G] [DecidableEq G] [DecidableEq C]
  [CommSemiring K]

def inflateParameters : MvPolynomial (Option (E ⊕ F) × C) K →ₐ[K]
    MvPolynomial ((Option E × C) ⊕ (Option F × C)) K :=
  MvPolynomial.aeval (R := K) fun ec => match ec.1 with
  | none => MvPolynomial.X (.inl (none,ec.2))*MvPolynomial.X (.inr (none,ec.2))
  | some (.inl e) => MvPolynomial.X (.inl (some e,ec.2))
  | some (.inr f) => MvPolynomial.X (.inr (some f,ec.2))

def specializeParameters : MvPolynomial ((Option E × C) ⊕ (Option F × C)) K →ₐ[K]
    MvPolynomial (Option (E ⊕ F) × C) K :=
  MvPolynomial.aeval (R := K) fun ec => match ec with
  | .inl (none,c) => MvPolynomial.X (none,c)
  | .inl (some e,c) => MvPolynomial.X (some (.inl e),c)
  | .inr (none,_) => 1
  | .inr (some f,c) => MvPolynomial.X (some (.inr f),c)

theorem specialize_inflateParameters :
    (specializeParameters (K := K) (C := C) (E := E) (F := F)).comp inflateParameters=
      AlgHom.id K _ := by
  ext ec
  rcases ec with ⟨e,c⟩
  rcases e with _ | (e | f) <;> simp [inflateParameters,specializeParameters]

theorem inflateParameters_injective :
    Function.Injective (inflateParameters (K := K) (C := C) (E := E) (F := F)) := by
  apply Function.LeftInverse.injective
    (g := specializeParameters (K := K) (C := C) (E := E) (F := F))
  intro p
  exact AlgHom.congr_fun specialize_inflateParameters p

theorem outCut_active_prod {A : Type*} [CommMonoid A]
    (N : Data V E L S) (a : V) (s : S) (f : Option E → A) :
    (∏ e∈(outCut N a).active s,f e)=f none*∏ e∈N.active s,f (some e) := by
  classical
  simp [outCut,Finset.prod_image,(Option.some_injective E).injOn]

theorem inCut_active_prod {A : Type*} [CommMonoid A]
    (N : Data V E L S) (a : V) (s : S) (f : Option E → A) :
    (∏ e∈(inCut N a).active s,f e)=f none*∏ e∈N.active s,f (some e) := by
  classical
  simp [inCut,Finset.prod_image,(Option.some_injective E).injOn]

theorem glue_active_prod {A : Type*} [CommMonoid A]
    (N : Data V E L S) (a : V) (M : Data W F R T) (b : W)
    (s : S × T) (f : Option (E ⊕ F) → A) :
    (∏ e∈(glue N a M b).active s,f e)=
      f none*(∏ e∈N.active s.1,f (some (.inl e)))*
        ∏ e∈M.active s.2,f (some (.inr e)) := by
  classical
  have hd : Disjoint ((N.active s.1).image (fun e => some (Sum.inl e : E ⊕ F)))
      ((M.active s.2).image (fun f => some (Sum.inr f : E ⊕ F))) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨f,hf,h⟩ := Finset.mem_image.mp hz'
    cases h
  have hn : (none : Option (E ⊕ F)) ∉
      ((N.active s.1).image (fun e => some (Sum.inl e : E ⊕ F))) ∪
        ((M.active s.2).image (fun f => some (Sum.inr f : E ⊕ F))) := by simp
  simp only [glue,Finset.prod_insert hn,Finset.prod_union hd]
  rw [Finset.prod_image (by intro x hx y hy h; exact Sum.inl_injective (Option.some.inj h)),
    Finset.prod_image (by intro x hx y hy h; exact Sum.inr_injective (Option.some.inj h))]
  exact (mul_assoc _ _ _).symm

theorem inflate_termPolynomial (N : Data V E L S) (a : V)
    (M : Data W F R T) (b : W) (q : G → C) (g : Flow (L ⊕ R) G)
    (t : Term (glue N a M b) g.val) :
    inflateParameters (termPolynomial (K := K) (glue N a M b) q t)=
      MvPolynomial.rename Sum.inl (termPolynomial (outCut N a) q (leftTerm N a M b g t))*
        MvPolynomial.rename Sum.inr (termPolynomial (inCut M b) q (rightTerm N a M b g t)) := by
  rw [termPolynomial_eq_prod,glue_active_prod,
    termPolynomial_eq_prod,outCut_active_prod,termPolynomial_eq_prod,inCut_active_prod]
  simp only [map_mul,map_prod,MvPolynomial.rename_X,inflateParameters,MvPolynomial.aeval_X,
    leftTerm,rightTerm]
  ac_rfl

/-- Exact factorization of the Fourier coordinate polynomial across the
bridge. It follows from the explicit conserved-flow bijection. -/
theorem inflate_coordinate (N : Data V E L S) (a : V)
    (M : Data W F R T) (b : W) (q : G → C) (g : Flow (L ⊕ R) G) :
    inflateParameters (NetworkIncidenceFlows.coordinate (K := K) (glue N a M b) q g)=
      MvPolynomial.rename Sum.inl (NetworkIncidenceFlows.coordinate (outCut N a) q (leftFlow g))*
        MvPolynomial.rename Sum.inr (NetworkIncidenceFlows.coordinate (inCut M b) q (rightFlow g)) := by
  rw [coordinate_eq_sum_terms,map_sum]
  simp_rw [inflate_termPolynomial N a M b q g]
  calc
    _ = ∑ uv : Term (outCut N a) (leftFlow g).val × Term (inCut M b) (rightFlow g).val,
        MvPolynomial.rename Sum.inl (termPolynomial (outCut N a) q uv.1)*
          MvPolynomial.rename Sum.inr (termPolynomial (inCut M b) q uv.2) :=
      Fintype.sum_equiv (cutTermEquiv N a M b g) _ _ (fun t => rfl)
    _ = _ := by
      rw [coordinate_eq_sum_terms,coordinate_eq_sum_terms,map_sum,map_sum]
      simp only [Fintype.sum_prod_type,Finset.sum_mul_sum]

/-- Cutting and rejoining preserves the entire Fourier equation ideal. -/
theorem kernel_coordinate_glue (N : Data V E L S) (a : V)
    (M : Data W F R T) (b : W) (q : G → C) :
    RingHom.ker (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) (glue N a M b) q))=
      RingHom.ker (MvPolynomial.aeval (R := K) (NetworkFlowGluing.gluedCoordinate
        (NetworkIncidenceFlows.coordinate (K := K) (outCut N a) q) (NetworkIncidenceFlows.coordinate (K := K) (inCut M b) q))) := by
  have h : MvPolynomial.aeval (R := K) (NetworkFlowGluing.gluedCoordinate
      (NetworkIncidenceFlows.coordinate (K := K) (outCut N a) q) (NetworkIncidenceFlows.coordinate (K := K) (inCut M b) q))=
      (inflateParameters (K := K) (C := C) (E := E) (F := F)).comp
        (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) (glue N a M b) q)) := by
    ext g : 1
    simpa only [MvPolynomial.aeval_X,AlgHom.comp_apply,NetworkFlowGluing.gluedCoordinate] using
      (inflate_coordinate N a M b q g).symm
  rw [h]
  ext p
  simp only [RingHom.mem_ker,AlgHom.comp_apply]
  constructor
  · intro hp
    rw [hp,map_zero]
  · intro hp
    apply inflateParameters_injective (K := K) (C := C) (E := E) (F := F)
    simpa only [map_zero] using hp

end Sunlet.NetworkIncidenceCut
end
end NetworkStageSource_Sunlet_NetworkIncidencePolynomialCut
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkIncidencePolynomialCut"

section NetworkStageSource_Sunlet_NetworkIncidenceDimension


/-!
# Cut-edge dimension for the literal conserved-flow model

All algebraic hypotheses of the polynomial gluing theorem are discharged
here: the cut-leaf degree is read from conservation, every orbit class
occurs among actual zero-sum leaf flows, and class matching is converted
to group-label matching by an automorphism of the conserved-flow terms.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkIncidenceCut

open NetworkIncidenceFlows NetworkFlowGluing NetworkPolynomialGluing NetworkGluing

variable {V W E F L R S T G C K : Type*}
  [Fintype V] [Fintype W] [Fintype E] [Fintype F]
  [Fintype L] [Fintype R] [Fintype S] [Fintype T]
  [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
  [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype C] [DecidableEq C]
  [Field K] [CharZero K]

def flowWithCut (l : L) (a : G) : Flow (Option L) G := by
  classical
  refine ⟨fun o => o.elim a (fun j => if j=l then -a else 0),?_⟩
  simp [Fintype.sum_option]

@[simp] theorem flowWithCut_none (l : L) (a : G) : (flowWithCut l a).val none=a := rfl

theorem outCut_coordinate_euler (N : Data V E L S) (a : V) (q : G → C)
    (g : Flow (Option L) G) (c : C) :
    MvPolynomial.X (none,c)*MvPolynomial.pderiv (none,c) (NetworkIncidenceFlows.coordinate (K := K) (outCut N a) q g)=
      if c=q (g.val none) then NetworkIncidenceFlows.coordinate (outCut N a) q g else 0 := by
  classical
  have hv (t : Term (outCut N a) g.val) : t.val.2 none=g.val none := by
    simpa using t.property.2 none
  simp only [NetworkIncidenceFlows.coordinate,map_sum,Finset.mul_sum,MvPolynomial.X_mul_pderiv_monomial,
    exponent_at_edge]
  simp_rw [hv]
  by_cases hc : c=q (g.val none) <;> simp [outCut,hc,eq_comm]

theorem inCut_coordinate_euler (N : Data V E L S) (a : V) (q : G → C)
    (g : Flow (Option L) G) (c : C) :
    MvPolynomial.X (none,c)*MvPolynomial.pderiv (none,c) (NetworkIncidenceFlows.coordinate (K := K) (inCut N a) q g)=
      if c=q (-g.val none) then NetworkIncidenceFlows.coordinate (inCut N a) q g else 0 := by
  classical
  have hv (t : Term (inCut N a) g.val) : t.val.2 none=-g.val none := by
    have h : -t.val.2 none=g.val none := by simpa using t.property.2 none
    exact eq_neg_of_add_eq_zero_left (by rw [← h]; exact add_neg_cancel _)
  simp only [NetworkIncidenceFlows.coordinate,map_sum,Finset.mul_sum,MvPolynomial.X_mul_pderiv_monomial,
    exponent_at_edge]
  simp_rw [hv]
  by_cases hc : c=q (-g.val none) <;> simp [inCut,hc,eq_comm]

/-- The cut-edge dimension formula for the original finite Fourier flow
sum, including arbitrary orbit partitions under negation. -/
theorem coordinate_dimension_glue [Nonempty L] [Nonempty R]
    (N : Data V E L S) (a : V) (M : Data W F R T) (b : W)
    (q : G → C) (hq : Function.Surjective q)
    (horbit : ∀ x y,q x=q y → ∃ φ : G ≃+ G,(∀ z,q (φ z)=q z) ∧ φ x=y)
    (hN : ∀ g : Flow (Option L) G,Nonempty (Term (outCut N a) g.val))
    (hM : ∀ g : Flow (Option R) G,Nonempty (Term (inCut M b) g.val))
    (d₁ d₂ : ℕ)
    (hd₁ : ringKrullDim (MvPolynomial (Flow (Option L) G) K ⧸ RingHom.ker
      (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) (outCut N a) q)))=d₁)
    (hd₂ : ringKrullDim (MvPolynomial (Flow (Option R) G) K ⧸ RingHom.ker
      (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) (inCut M b) q)))=d₂) :
    ringKrullDim (MvPolynomial (Flow (L ⊕ R) G) K ⧸ RingHom.ker
      (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) (glue N a M b) q)))=
        (d₁+d₂-Fintype.card C : ℕ) := by
  classical
  let p := NetworkIncidenceFlows.coordinate (K := K) (outCut N a) q
  let r := NetworkIncidenceFlows.coordinate (K := K) (inCut M b) q
  let d : Flow (Option L) G → C := fun g => q (g.val none)
  let e : Flow (Option R) G → C := fun g => q (-g.val none)
  let rep : C → G := fun c => Classical.choose (hq c)
  have hrep : ∀ c,q (rep c)=c := fun c => Classical.choose_spec (hq c)
  let anchorL : C → Flow (Option L) G :=
    fun c => flowWithCut (Classical.choice ‹Nonempty L›) (rep c)
  let anchorR : C → Flow (Option R) G :=
    fun c => flowWithCut (Classical.choice ‹Nonempty R›) (-rep c)
  have ha : ∀ c,d (anchorL c)=c := by intro c; simpa [d,anchorL] using hrep c
  have hb : ∀ c,e (anchorR c)=c := by intro c; simpa [e,anchorR] using hrep c
  have hp : ∀ g,p g≠0 := fun g => coordinate_ne_zero_of_term
    (outCut N a) q g (Classical.choice (hN g))
  have hr : ∀ g,r g≠0 := fun g => coordinate_ne_zero_of_term
    (inCut M b) q g (Classical.choice (hM g))
  have hdim := dimension_pairedPolynomial p r d e (fun c => (none,c)) (fun c => (none,c))
    hp hr (outCut_coordinate_euler N a q) (inCut_coordinate_euler M b q)
    anchorL anchorR ha hb d₁ d₂ hd₁ hd₂
  have hrange := classMatched_range_eq_glued_range q horbit p r
    (fun φ hφ g => coordinate_mapFlow (inCut M b) q φ hφ g)
  have heq := dimension_eq_of_range (K := K)
    (fun ij : ClassMatched (L := L) (R := R) q => pairedCoordinate p r ij.val)
    (NetworkFlowGluing.gluedCoordinate p r) hrange
  rw [kernel_coordinate_glue N a M b q]
  exact heq.symm.trans hdim

end Sunlet.NetworkIncidenceCut
end
end NetworkStageSource_Sunlet_NetworkIncidenceDimension
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkIncidenceDimension"

section NetworkStageSource_Sunlet_NetworkGraphCutDimension


/-!
# Dimension and existence of Fourier flows across an actual bridge

This module applies the polynomial gluing theorem to the graph incidence
isomorphisms. All hypotheses refer to the actual component graph models.
-/

noncomputable section

namespace Sunlet.NetworkGraphCut

open SimpleGraph NetworkGraphDecomposition NetworkGraphModel NetworkIncidenceFlows
open NetworkIncidenceCut

attribute [local instance] Classical.propDecidable

variable {V G C K : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype C] [DecidableEq C]

def HasAllFlows (H : SimpleGraph V) (O : Orientation H) (R : ReticulationData H) : Prop :=
  ∀ g : NetworkFlowGluing.Flow (Leaf H) G,Nonempty (Term (incidenceData H O R) g.val)

theorem hasAllFlows_cut (H : SimpleGraph V) (O : Orientation H) (R : ReticulationData H)
    (u v : V) (hH : H.Connected) (hadj : H.Adj u v) (hb : H.IsBridge s(u,v))
    (hL : HasAllFlows (G := G) (cutGraph H u v) (outOrientation H R u v hadj hb)
      (cutReticulation H R u v))
    (hR : HasAllFlows (G := G) (cutGraph H v u)
      (inOrientation H R v u hadj.symm (swap_bridge H u v hb)) (cutReticulation H R v u)) :
    HasAllFlows (G := G) H O R := by
  have hN := (outIso H R u v hadj hb).symm.terms_exist_transport hL
  have hM := (inIso H R v u hadj.symm (swap_bridge H u v hb)).symm.terms_exist_transport hR
  have hjoined : ∀ g : NetworkFlowGluing.Flow (OldLeafSide H u v ⊕ OldLeafSide H v u) G,
      Nonempty (Term (joinedData H R u v hadj hb) g.val) := by
    intro g
    obtain ⟨tL⟩ := hN (NetworkFlowGluing.leftFlow g)
    obtain ⟨tR⟩ := hM (NetworkFlowGluing.rightFlow g)
    exact ⟨joinTerm (coreData H R u v hadj hb) (attachment H u v)
      (coreData H R v u hadj.symm (swap_bridge H u v hb)) (attachment H v u) g tL tR⟩
  exact NetworkGraphOrientation.terms_exist H (joinedOrientation H R u v hH hadj hb) O R
    ((joinedIso H R u v hH hadj hb).terms_exist_transport hjoined)

/-- The precise graph cut-edge dimension formula. Its local hypotheses
are the component graphs' actual coordinate-ring dimensions and the
existence of conserved Fourier flows, both established by graph induction. -/
theorem dimension_cut [Field K] [CharZero K]
    (H : SimpleGraph V) (O : Orientation H) (R : ReticulationData H)
    (u v : V) (hH : H.Connected) (hadj : H.Adj u v) (hb : H.IsBridge s(u,v))
    [Nonempty (OldLeafSide H u v)] [Nonempty (OldLeafSide H v u)]
    (q : G → C) (hq : Function.Surjective q)
    (horbit : ∀ x y,q x=q y → ∃ φ : G ≃+ G,(∀ z,q (φ z)=q z) ∧ φ x=y)
    (neg : C ≃ C) (hneg : ∀ a,q (-a)=neg (q a))
    (hL : HasAllFlows (G := G) (cutGraph H u v) (outOrientation H R u v hadj hb)
      (cutReticulation H R u v))
    (hR : HasAllFlows (G := G) (cutGraph H v u)
      (inOrientation H R v u hadj.symm (swap_bridge H u v hb)) (cutReticulation H R v u))
    (dL dR : ℕ)
    (hdL : ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Leaf (cutGraph H u v)) G) K ⧸
      NetworkGraphModel.definingIdeal (K := K) (cutGraph H u v)
        (outOrientation H R u v hadj hb) (cutReticulation H R u v) q)=dL)
    (hdR : ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Leaf (cutGraph H v u)) G) K ⧸
      NetworkGraphModel.definingIdeal (K := K) (cutGraph H v u)
        (inOrientation H R v u hadj.symm (swap_bridge H u v hb))
        (cutReticulation H R v u) q)=dR) :
    ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Leaf H) G) K ⧸
      NetworkGraphModel.definingIdeal (K := K) H O R q)=
        (dL+dR-Fintype.card C : ℕ) := by
  have hN := (outIso H R u v hadj hb).symm.terms_exist_transport hL
  have hM := (inIso H R v u hadj.symm (swap_bridge H u v hb)).symm.terms_exist_transport hR
  have hdN := ((outIso H R u v hadj hb).dimension_transport (k := K) q).trans hdL
  have hdM := ((inIso H R v u hadj.symm (swap_bridge H u v hb)).dimension_transport (k := K) q).trans hdR
  have hd := coordinate_dimension_glue (coreData H R u v hadj hb) (attachment H u v)
    (coreData H R v u hadj.symm (swap_bridge H u v hb)) (attachment H v u)
    q hq horbit hN hM dL dR hdN hdM
  rw [NetworkGraphOrientation.definingIdeal_eq H (joinedOrientation H R u v hH hadj hb) O R
    q neg hneg]
  exact ((joinedIso H R u v hH hadj hb).dimension_transport (k := K) q).symm.trans hd

theorem oldLeafSide_nonempty (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (u v : V) (hadj : H.Adj u v) (hb : H.IsBridge s(u,v)) :
    Nonempty (OldLeafSide H u v) := by
  have hn := (binaryCactus_counts (cutGraph H u v)
    (cutGraph_isBinaryCactus H hH u v hadj hb)).2
  have he := cut_leafCount H u v hadj hb
  exact (Nat.card_pos_iff.mp (by omega : 0<Nat.card (OldLeafSide H u v))).1

end Sunlet.NetworkGraphCut
end
end NetworkStageSource_Sunlet_NetworkGraphCutDimension
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkGraphCutDimension"

section NetworkStageSource_Sunlet_NetworkGroupRelations


/-!
# Elementary relations on a finite group

These two field-valued relation lemmas are shared by the claw dimension
calculation and the path/sunlet exponent calculations. Keeping them here
makes the functional-kernel arguments independent of algebraic geometry.
The public theorem names are unchanged.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkClaw

variable {G C E : Type*} [AddCommGroup G] [Fintype G] [Field E] [CharZero E]

/-- An additive function from a finite group to a characteristic-zero field
vanishes. The proof sums over all group elements, so it makes no cyclicity
or prime-order assumption. -/
theorem additive_function_zero (f : G → E)
    (hf : ∀ a b, f (a + b) = f a + f b) : ∀ a, f a = 0 := by
  intro a
  have he : (∑ b : G, f (a + b)) = ∑ b : G, f b :=
    Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun b => rfl)
  simp_rw [hf] at he
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at he
  have hz : (Fintype.card G : E) * f a = 0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Exact kernel after fixing the first two zero-class scalings. -/
theorem normalized_relation_zero (q : G → C) (hq : Function.Surjective q)
    (α β γ : C → E) (hα : α (q 0) = 0) (hβ : β (q 0) = 0)
    (h : ∀ a b, α (q a) + β (q b) + γ (q (-(a + b))) = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have hg (a : G) : γ (q (-a)) = -α (q a) := by
    have hh := h a 0
    simp only [add_zero, hβ] at hh
    linear_combination hh
  have hb (a : G) : β (q a) = α (q a) := by
    have hh := h 0 a
    simp only [zero_add, hα, hg] at hh
    linear_combination hh
  have haadd (a b : G) : α (q (a + b)) = α (q a) + α (q b) := by
    have hh := h a b
    rw [hg, hb] at hh
    linear_combination -hh
  have ha0 := additive_function_zero (fun a => α (q a)) haadd
  have ha : α = 0 := by
    funext c
    obtain ⟨a, rfl⟩ := hq c
    exact ha0 a
  have hbb : β = 0 := by
    funext c
    obtain ⟨a, rfl⟩ := hq c
    rw [hb, ha]
  refine ⟨ha, hbb, ?_⟩
  funext c
  obtain ⟨a, rfl⟩ := hq c
  have hh := hg (-a)
  simpa [ha] using hh

end Sunlet.NetworkClaw
end
end NetworkStageSource_Sunlet_NetworkGroupRelations
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkGroupRelations"

section NetworkStageSource_Sunlet_FieldImageDimension

/-! Dimension of a literal rational-image coordinate algebra from an
actual finite extension of its coordinate field. -/

noncomputable section

namespace Sunlet.FieldImageDimension

open scoped IntermediateField.algebraAdjoinAdjoin
variable {k J O : Type*} [Field k] [Fintype J] [Fintype O] [DecidableEq J]

/-- The quotient is by substitution of the displayed rational coordinates.
Its dimension is the number of independent source variables when the
source field is proved finite over the field generated by those coordinates. -/
theorem dimension_of_finite
    (q : O → RationalPartials.FunctionField k J)
    [Module.Finite (IntermediateField.adjoin k (Set.range q)) (RationalPartials.FunctionField k J)] :
    ringKrullDim (MvPolynomial O k ⧸ RingHom.ker (MvPolynomial.aeval (R := k) q)) =
      (Fintype.card J : ℕ) := by
  let E := RationalPartials.FunctionField k J
  let A := Algebra.adjoin k (Set.range q)
  let F := IntermediateField.adjoin k (Set.range q)
  letI : Algebra.FiniteType k A := Algebra.FiniteType.adjoin_of_finite (Set.finite_range q)
  letI : Algebra.IsAlgebraic A E := Algebra.IsAlgebraic.trans A F E
  have hAE : Algebra.trdeg k A = Algebra.trdeg k E := by
    simpa only [trdeg_eq_zero (R := A) (A := E), add_zero] using (trdeg_add_eq k A (A := E))
  let P := MvPolynomial J k
  letI : Algebra.IsAlgebraic P E := IsLocalization.isAlgebraic E (nonZeroDivisors P)
  have hPE : Algebra.trdeg k P = Algebra.trdeg k E := by
    simpa only [trdeg_eq_zero (R := P) (A := E), add_zero] using (trdeg_add_eq k P (A := E))
  have hdim : ringKrullDim A = (Fintype.card J : ℕ) := by
    rw [DimensionAlgebra.ringKrullDim_eq_trdeg_toNat k A, hAE, ← hPE]
    simp [P, MvPolynomial.trdeg_of_isDomain]
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (MvPolynomial.aeval (R := k) q)).toRingEquiv]
  have he : A = (MvPolynomial.aeval (R := k) q).range :=
    Algebra.adjoin_range_eq_range_aeval k q
  exact (ringKrullDim_eq_of_ringEquiv (Subalgebra.equivOfEq A _ he).toRingEquiv).symm.trans hdim

end Sunlet.FieldImageDimension
end
end NetworkStageSource_Sunlet_FieldImageDimension
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.FieldImageDimension"

section NetworkStageSource_Sunlet_NetworkClaw


/-!
# The actual three-leaf tree block

The leaf-flow coordinate is the product of the three class parameters.
Two independent edge scalings are removed explicitly. The normalized
function field is proved finite and separable over its displayed-coordinate
field by applying the finite-group additive relation to actual derivations.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkClaw

/-- Vanishing field-valued derivations annihilates the universal differential
module. This local helper keeps the tree block independent of the contact proof. -/
theorem formallyUnramified_of_derivations_zero
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (h : ∀ D : Derivation F E E, D = 0) : Algebra.FormallyUnramified F E := by
  constructor
  apply (Module.subsingleton_dual_iff E).mp
  constructor
  intro φ ψ
  apply (KaehlerDifferential.linearMapEquivDerivation F E).injective
  exact (h _).trans (h _).symm

variable {G C k E : Type*} [AddCommGroup G] [Fintype G]
  [Fintype C] [DecidableEq C] [Field k] [CharZero k] [Field E] [CharZero E]

abbrev Variable (c0 : C) := (Bool × {c : C // c ≠ c0}) ⊕ C
abbrev PolynomialRing (k C : Type*) [Field k] (c0 : C) := MvPolynomial (Variable c0) k
abbrev FunctionField (k C : Type*) [Field k] (c0 : C) := FractionRing (PolynomialRing k C c0)

variable (c0 : C)

def x (j : Variable c0) : FunctionField k C c0 :=
  RationalPartials.coordinateVariable j

theorem x_ne_zero (j : Variable c0) : x (k := k) c0 j ≠ 0 := by
  exact fun h => MvPolynomial.X_ne_zero j
    ((IsFractionRing.injective (PolynomialRing k C c0) (FunctionField k C c0))
      (by simpa [x, RationalPartials.coordinateVariable] using h))

def side (b : Bool) (c : C) : FunctionField k C c0 :=
  if hc : c = c0 then 1 else x c0 (.inl (b, ⟨c, hc⟩))

def third (c : C) : FunctionField k C c0 := x c0 (.inr c)

@[simp] theorem side_zero (b : Bool) : side (k := k) c0 b c0 = 1 := by simp [side]

theorem side_ne_zero (b : Bool) (c : C) : side (k := k) c0 b c ≠ 0 := by
  unfold side
  split_ifs
  · exact one_ne_zero
  · exact x_ne_zero c0 _

theorem third_ne_zero (c : C) : third (k := k) c0 c ≠ 0 := x_ne_zero c0 _

variable {c0}

def normalizedCoordinate (q : G → C) (ab : G × G) : FunctionField k C (q 0) :=
  side (q 0) false (q ab.1) * side (q 0) true (q ab.2) *
    third (q 0) (q (-(ab.1 + ab.2)))

abbrev coordinateField (q : G → C) : IntermediateField k (FunctionField k C (q 0)) :=
  IntermediateField.adjoin k (Set.range (normalizedCoordinate (k := k) q))

lemma log_leibniz {F : Type*} [Field F] [Algebra F E]
    (D : Derivation F E E) (a b c : E) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    D (a * b * c) / (a * b * c) = D a / a + D b / b + D c / c := by
  simp only [D.leibniz, smul_eq_mul]
  field_simp
  ring

/-- Every derivation over the actual coordinate field kills every
independent normalized parameter. -/
theorem derivations_zero (q : G → C) (hq : Function.Surjective q)
    (D : Derivation (coordinateField (k := k) q)
      (FunctionField k C (q 0)) (FunctionField k C (q 0))) : D = 0 := by
  let α : C → FunctionField k C (q 0) := fun c =>
    D (side (q 0) false c) / side (q 0) false c
  let β : C → FunctionField k C (q 0) := fun c =>
    D (side (q 0) true c) / side (q 0) true c
  let γ : C → FunctionField k C (q 0) := fun c =>
    D (third (q 0) c) / third (q 0) c
  have hq0 (a b : G) : D (normalizedCoordinate (k := k) q (a,b)) = 0 := by
    exact D.map_algebraMap (⟨normalizedCoordinate q (a,b),
      IntermediateField.subset_adjoin k _ ⟨(a,b), rfl⟩⟩ : coordinateField q)
  have hrel : ∀ a b, α (q a) + β (q b) + γ (q (-(a+b))) = 0 := by
    intro a b
    have hh := log_leibniz D (side (q 0) false (q a)) (side (q 0) true (q b))
      (third (q 0) (q (-(a+b)))) (side_ne_zero _ _ _) (side_ne_zero _ _ _)
      (third_ne_zero _ _)
    change D (normalizedCoordinate q (a,b)) / normalizedCoordinate q (a,b) = _ at hh
    rw [hq0, zero_div] at hh
    exact hh.symm
  obtain ⟨hα, hβ, hγ⟩ := normalized_relation_zero q hq α β γ
    (by simp [α]) (by simp [β]) hrel
  have hcoords (j : Variable (q 0)) : D (x (k := k) (q 0) j) = 0 := by
    rcases j with ⟨b,c⟩ | c
    · cases b
      · have hz := congrFun hα c.val
        change D (side (q 0) false c.val) / side (q 0) false c.val = 0 at hz
        have hh := (div_eq_zero_iff.mp hz).resolve_right (side_ne_zero _ _ _)
        simpa [side, c.property] using hh
      · have hz := congrFun hβ c.val
        change D (side (q 0) true c.val) / side (q 0) true c.val = 0 at hz
        have hh := (div_eq_zero_iff.mp hz).resolve_right (side_ne_zero _ _ _)
        simpa [side, c.property] using hh
    · have hz := congrFun hγ c
      change D (third (q 0) c) / third (q 0) c = 0 at hz
      exact (div_eq_zero_iff.mp hz).resolve_right (third_ne_zero _ _)
  have hd : D.restrictScalars k = 0 := by
    apply RationalPartials.ext
    intro j
    exact hcoords j
  apply Derivation.ext
  intro t
  exact congrArg (fun d : Derivation k (FunctionField k C (q 0))
    (FunctionField k C (q 0)) => d t) hd

/-- Finiteness is proved for the actual normalized tree map. -/
theorem finite_separable (q : G → C) (hq : Function.Surjective q) :
    Module.Finite (coordinateField (k := k) q) (FunctionField k C (q 0)) ∧
      Algebra.IsSeparable (coordinateField (k := k) q) (FunctionField k C (q 0)) := by
  letI : Algebra.EssFiniteType (PolynomialRing k C (q 0)) (FunctionField k C (q 0)) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (PolynomialRing k C (q 0)))
  letI : Algebra.EssFiniteType k (FunctionField k C (q 0)) :=
    Algebra.EssFiniteType.comp k (PolynomialRing k C (q 0)) (FunctionField k C (q 0))
  letI : Algebra.EssFiniteType (coordinateField (k := k) q) (FunctionField k C (q 0)) :=
    Algebra.EssFiniteType.of_comp k (coordinateField (k := k) q) (FunctionField k C (q 0))
  letI : Algebra.FormallyUnramified (coordinateField (k := k) q)
      (FunctionField k C (q 0)) :=
    formallyUnramified_of_derivations_zero _ _ (derivations_zero q hq)
  exact ⟨Algebra.FormallyUnramified.finite_of_free _ _,
    Algebra.FormallyUnramified.isSeparable _ _⟩

theorem variable_card (q : G → C) :
    Fintype.card (Variable (q 0)) = 3 * Fintype.card C - 2 := by
  have hn : Fintype.card {c : C // c ≠ q 0} = Fintype.card C - 1 := by
    simpa using Fintype.card_subtype_compl (fun c : C => c = q 0)
  have hp : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨q 0⟩
  simp only [Variable, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, hn]
  omega

/-- The ordinary prime-ideal-chain dimension of the normalized coordinate
ring, with no Jacobian-rank definition of dimension. -/
theorem normalized_coordinate_dimension (q : G → C) (hq : Function.Surjective q) :
    ringKrullDim (MvPolynomial (G × G) k ⧸
      RingHom.ker (MvPolynomial.aeval (R := k) (normalizedCoordinate (k := k) q))) =
        (3 * Fintype.card C - 2 : ℕ) := by
  letI := (finite_separable (k := k) q hq).1
  simpa only [variable_card] using
    FieldImageDimension.dimension_of_finite (normalizedCoordinate (k := k) q)

abbrev OriginalPolynomialRing (k C : Type*) [Field k] := MvPolynomial (Fin 3 × C) k

def originalCoordinate (q : G → C) (ab : G × G) : OriginalPolynomialRing k C :=
  MvPolynomial.X (0, q ab.1) * MvPolynomial.X (1, q ab.2) *
    MvPolynomial.X (2, q (-(ab.1 + ab.2)))

def sidePolynomial (c0 : C) (b : Bool) (c : C) : PolynomialRing k C c0 :=
  if hc : c = c0 then 1 else MvPolynomial.X (.inl (b, ⟨c, hc⟩))

def normalizedPolynomial (q : G → C) (ab : G × G) : PolynomialRing k C (q 0) :=
  sidePolynomial (q 0) false (q ab.1) * sidePolynomial (q 0) true (q ab.2) *
    MvPolynomial.X (.inr (q (-(ab.1 + ab.2))))

lemma map_sidePolynomial (c0 : C) (b : Bool) (c : C) :
    algebraMap (PolynomialRing k C c0) (FunctionField k C c0)
      (sidePolynomial c0 b c) = side c0 b c := by
  unfold sidePolynomial side
  split_ifs <;> simp [x, RationalPartials.coordinateVariable]

lemma map_normalizedPolynomial (q : G → C) (ab : G × G) :
    algebraMap (PolynomialRing k C (q 0)) (FunctionField k C (q 0))
      (normalizedPolynomial q ab) = normalizedCoordinate q ab := by
  simp [normalizedPolynomial, normalizedCoordinate, map_sidePolynomial, third, x,
    RationalPartials.coordinateVariable]

def specializeOriginal (c0 : C) : OriginalPolynomialRing k C →ₐ[k] PolynomialRing k C c0 :=
  MvPolynomial.aeval (R := k) (fun ic =>
    if ic.1 = 0 then sidePolynomial c0 false ic.2
    else if ic.1 = 1 then sidePolynomial c0 true ic.2
    else MvPolynomial.X (.inr ic.2))

lemma specialize_originalCoordinate (q : G → C) (ab : G × G) :
    specializeOriginal (k := k) (q 0) (originalCoordinate q ab) = normalizedPolynomial q ab := by
  simp [specializeOriginal, originalCoordinate, normalizedPolynomial]

abbrev OriginalFunctionField (k C : Type*) [Field k] := FractionRing (OriginalPolynomialRing k C)

def originalX (ic : Fin 3 × C) : OriginalFunctionField k C :=
  RationalPartials.coordinateVariable ic

lemma originalX_ne_zero (ic : Fin 3 × C) : originalX (k := k) ic ≠ 0 := by
  exact fun h => MvPolynomial.X_ne_zero ic
    ((IsFractionRing.injective (OriginalPolynomialRing k C) (OriginalFunctionField k C))
      (by simpa [originalX, RationalPartials.coordinateVariable] using h))

def rescaleNormalized (c0 : C) : PolynomialRing k C c0 →ₐ[k] OriginalFunctionField k C :=
  MvPolynomial.aeval (R := k) fun j => match j with
    | .inl (b,c) => originalX ((if b then 1 else 0), c.val) /
        originalX ((if b then 1 else 0), c0)
    | .inr c => originalX (2,c) * originalX (0,c0) * originalX (1,c0)

lemma rescale_sidePolynomial (c0 : C) (b : Bool) (c : C) :
    rescaleNormalized (k := k) c0 (sidePolynomial c0 b c) =
      originalX ((if b then 1 else 0), c) / originalX ((if b then 1 else 0), c0) := by
  by_cases hc : c = c0
  · subst c
    simp [sidePolynomial, originalX_ne_zero]
  · simp [sidePolynomial, hc, rescaleNormalized]

lemma rescale_normalizedPolynomial (q : G → C) (ab : G × G) :
    rescaleNormalized (k := k) (q 0) (normalizedPolynomial q ab) =
      algebraMap (OriginalPolynomialRing k C) (OriginalFunctionField k C)
        (originalCoordinate q ab) := by
  have h0 := originalX_ne_zero (k := k) (0,q 0)
  have h1 := originalX_ne_zero (k := k) (1,q 0)
  have hX (c : C) : rescaleNormalized (k := k) (q 0) (MvPolynomial.X (.inr c)) =
      originalX (2,c) * originalX (0,q 0) * originalX (1,q 0) := by
    simp [rescaleNormalized]
  have ho : algebraMap (OriginalPolynomialRing k C) (OriginalFunctionField k C)
      (originalCoordinate q ab) =
        originalX (0,q ab.1) * originalX (1,q ab.2) * originalX (2,q (-(ab.1+ab.2))) := by
    simp [originalCoordinate, originalX, RationalPartials.coordinateVariable]
  rw [ho, normalizedPolynomial, map_mul, map_mul,
    rescale_sidePolynomial, rescale_sidePolynomial, hX]
  simp only [Bool.false_eq_true, ↓reduceIte]
  field_simp [h0,h1] <;> ring

/-- Exact equality of substitution kernels proves that removing the two
scalings neither deletes nor adds equations of the tree model. -/
theorem original_kernel_eq_normalized (q : G → C) :
    PolynomialImage.definingIdeal (originalCoordinate (k := k) q) =
      RingHom.ker (MvPolynomial.aeval (R := k) (normalizedCoordinate (k := k) q)) := by
  let f := PolynomialImage.comorphism (originalCoordinate (k := k) q)
  let g := MvPolynomial.aeval (R := k) (normalizedPolynomial (k := k) q)
  let h := MvPolynomial.aeval (R := k) (normalizedCoordinate (k := k) q)
  have hfg : (specializeOriginal (k := k) (q 0)).comp f = g := by
    ext ab : 1
    simpa only [AlgHom.comp_apply, PolynomialImage.comorphism, f, g, MvPolynomial.aeval_X]
      using specialize_originalCoordinate (k := k) q ab
  have hgf : (rescaleNormalized (k := k) (q 0)).comp g =
      (IsScalarTower.toAlgHom k (OriginalPolynomialRing k C) (OriginalFunctionField k C)).comp f := by
    ext ab : 1
    simpa only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
      PolynomialImage.comorphism, f, g, MvPolynomial.aeval_X]
      using rescale_normalizedPolynomial (k := k) q ab
  have hgh : (IsScalarTower.toAlgHom k (PolynomialRing k C (q 0))
      (FunctionField k C (q 0))).comp g = h := by
    ext ab : 1
    simpa only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, g, h, MvPolynomial.aeval_X]
      using map_normalizedPolynomial (k := k) q ab
  ext p
  change f p = 0 ↔ h p = 0
  constructor
  · intro hp
    have hg : g p = 0 := by
      rw [← hfg]
      simp [hp]
    rw [← hgh]
    simp [hg]
  · intro hp
    have hg : g p = 0 := by
      apply IsFractionRing.injective (PolynomialRing k C (q 0)) (FunctionField k C (q 0))
      have hh := AlgHom.congr_fun hgh p
      simpa only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, hp, map_zero] using hh
    apply IsFractionRing.injective (OriginalPolynomialRing k C) (OriginalFunctionField k C)
    have hh := AlgHom.congr_fun hgf p
    simpa only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, hg, map_zero] using hh.symm

/-- The actual affine image closure of the three-leaf flow parameterization
has dimension3r−2 for every surjective class map of a finite abelian group.
In particular this covers every automorphism-orbit model used in the paper. -/
theorem imageClosure_dimension (q : G → C) (hq : Function.Surjective q) :
    ringKrullDim (MvPolynomial (G × G) k ⧸ MvPolynomial.vanishingIdeal k
      (PolynomialImage.closure (originalCoordinate (k := k) q))) =
        (3 * Fintype.card C - 2 : ℕ) := by
  rw [PolynomialImage.vanishingIdeal_imageClosure, original_kernel_eq_normalized]
  exact normalized_coordinate_dimension q hq

end Sunlet.NetworkClaw
end
end NetworkStageSource_Sunlet_NetworkClaw
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkClaw"

section NetworkStageSource_Sunlet_NetworkClawFlow


/-!
# Leaf-flow coordinates for the three-leaf tree

This identifies the pair-indexed normal form with the literal three leaf
labels whose sum is zero. It also transports the actual coordinate-ring
dimension through that equivalence.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkClaw

variable {G C k : Type*} [AddCommGroup G] [Fintype G]
  [Fintype C] [DecidableEq C] [Field k] [CharZero k]

abbrev FlowIndex (G : Type*) [AddCommGroup G] :=
  {g : Fin 3 → G // ∑ i, g i = 0}

def flowEquiv : G × G ≃ FlowIndex G where
  toFun ab := ⟨![ab.1, ab.2, -(ab.1 + ab.2)], by simp [Fin.sum_univ_three]⟩
  invFun g := (g.val 0, g.val 1)
  left_inv ab := by simp
  right_inv g := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · have hh := g.property
      rw [Fin.sum_univ_three] at hh
      have hh' : (g.val 0 + g.val 1) + g.val 2 = 0 := by
        simpa only [add_assoc] using hh
      exact (eq_neg_of_add_eq_zero_right hh').symm

def flowCoordinate (q : G → C) (g : FlowIndex G) : OriginalPolynomialRing k C :=
  ∏ i : Fin 3, MvPolynomial.X (i, q (g.val i))

@[simp] theorem flowCoordinate_flowEquiv (q : G → C) (ab : G × G) :
    flowCoordinate (k := k) q (flowEquiv ab) = originalCoordinate q ab := by
  simp [flowCoordinate, flowEquiv, originalCoordinate, Fin.prod_univ_succ, mul_assoc]

theorem flow_coordinate_range (q : G → C) :
    Set.range (flowCoordinate (k := k) q) = Set.range (originalCoordinate (k := k) q) := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨flowEquiv.symm g, ?_⟩
    rw [← flowCoordinate_flowEquiv, Equiv.apply_symm_apply]
  · rintro ⟨ab, rfl⟩
    exact ⟨flowEquiv ab, flowCoordinate_flowEquiv q ab⟩

def flowCoordinateRingEquiv (q : G → C) :
    (MvPolynomial (FlowIndex G) k ⧸ PolynomialImage.definingIdeal (flowCoordinate (k := k) q)) ≃ₐ[k]
      (MvPolynomial (G × G) k ⧸ PolynomialImage.definingIdeal (originalCoordinate (k := k) q)) := by
  have hr : PolynomialImage.imageAlgebra (flowCoordinate (k := k) q) =
      PolynomialImage.imageAlgebra (originalCoordinate (k := k) q) := by
    change (MvPolynomial.aeval (R := k) (flowCoordinate q)).range =
      (MvPolynomial.aeval (R := k) (originalCoordinate q)).range
    rw [← Algebra.adjoin_range_eq_range_aeval, ← Algebra.adjoin_range_eq_range_aeval]
    rw [flow_coordinate_range]
  exact (PolynomialImage.coordinateRingEquivImage (flowCoordinate q)).trans
    ((Subalgebra.equivOfEq _ _ hr).trans
      (PolynomialImage.coordinateRingEquivImage (originalCoordinate q)).symm)

/-- The literal three-leaf, zero-sum-flow polynomial model has the
dimension used for the tree blocks in Corollary8.1. -/
theorem three_leaf_flow_dimension (q : G → C) (hq : Function.Surjective q) :
    ringKrullDim (MvPolynomial (FlowIndex G) k ⧸ MvPolynomial.vanishingIdeal k
      (PolynomialImage.closure (flowCoordinate (k := k) q))) =
        (3 * Fintype.card C - 2 : ℕ) := by
  rw [PolynomialImage.vanishingIdeal_imageClosure]
  rw [ringKrullDim_eq_of_ringEquiv (flowCoordinateRingEquiv (k := k) q).toRingEquiv]
  rw [← PolynomialImage.vanishingIdeal_imageClosure]
  exact imageClosure_dimension q hq

end Sunlet.NetworkClaw
end
end NetworkStageSource_Sunlet_NetworkClawFlow
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkClawFlow"

section NetworkStageSource_Sunlet_NetworkLeafEdge


/-!
# The single-edge base case in the network induction

For a two-leaf edge the Fourier coordinates are indexed by pairs whose sum
is zero. The coordinate with flow `(a,-a)` is the edge parameter of the
class containing `a`. This module identifies its actual image-coordinate
ring with a polynomial ring on the classes.
-/

noncomputable section

namespace Sunlet.NetworkLeafEdge

variable {K G C : Type*} [Field K]

def coordinatePolynomial (q : G → C) (a : G) : MvPolynomial C K :=
  MvPolynomial.X (q a)

theorem comorphism_eq_rename (q : G → C) :
    PolynomialImage.comorphism (coordinatePolynomial (K := K) q) =
      MvPolynomial.rename q := by
  ext a
  simp [PolynomialImage.comorphism, coordinatePolynomial]

/-- This is an isomorphism of the literal substitution-kernel quotient. -/
def coordinateRingEquiv (q : G → C) (hq : Function.Surjective q) :
    (MvPolynomial G K ⧸ PolynomialImage.definingIdeal (coordinatePolynomial (K := K) q)) ≃+*
      MvPolynomial C K :=
  RingHom.quotientKerEquivOfSurjective (f :=
    (PolynomialImage.comorphism (coordinatePolynomial (K := K) q)).toRingHom) (by
      change Function.Surjective (PolynomialImage.comorphism (coordinatePolynomial (K := K) q))
      rw [comorphism_eq_rename]
      exact MvPolynomial.rename_surjective q hq)

theorem imageClosure_dimension [Infinite K] [Fintype C]
    (q : G → C) (hq : Function.Surjective q) :
    ringKrullDim (MvPolynomial G K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (coordinatePolynomial (K := K) q))) =
        (Fintype.card C : ℕ) := by
  rw [PolynomialImage.vanishingIdeal_imageClosure]
  rw [ringKrullDim_eq_of_ringEquiv (coordinateRingEquiv (K := K) q hq)]
  simp

variable [AddCommGroup G]

abbrev FlowIndex (G : Type*) [AddCommGroup G] :=
  {ab : G × G // ab.1 + ab.2 = 0}

def flowClass (q : G → C) (ab : FlowIndex G) : C := q ab.val.1

theorem flowClass_surjective (q : G → C) (hq : Function.Surjective q) :
    Function.Surjective (flowClass q) := by
  intro i
  obtain ⟨a, ha⟩ := hq i
  exact ⟨⟨(a, -a), add_neg_cancel a⟩, ha⟩

/-- The actual two-leaf, one-edge group-based model has one independent
coordinate per parameter class, including the zero class. -/
theorem two_leaf_edge_dimension [Infinite K] [Fintype C]
    (q : G → C) (hq : Function.Surjective q) :
    ringKrullDim (MvPolynomial (FlowIndex G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (coordinatePolynomial (K := K) (flowClass q)))) =
        (Fintype.card C : ℕ) :=
  imageClosure_dimension (flowClass q) (flowClass_surjective q hq)

/-- Formula (10) also holds for the allowed graph having one edge, no cycles,
and no internal vertices. This supplies the omitted base case in its induction. -/
theorem two_leaf_edge_formula [Infinite K] [Fintype C]
    (q : G → C) (hq : Function.Surjective q) (δ : ℕ) :
    ringKrullDim (MvPolynomial (FlowIndex G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (coordinatePolynomial (K := K) (flowClass q)))) =
        ((Fintype.card C - 1) * (1 - 0) + 1 - δ * 0 : ℕ) := by
  letI : Nonempty C := ⟨q 0⟩
  have hc : 0 < Fintype.card C := Fintype.card_pos
  rw [two_leaf_edge_dimension q hq]
  congr 1
  omega

end Sunlet.NetworkLeafEdge
end
end NetworkStageSource_Sunlet_NetworkLeafEdge
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkLeafEdge"

#print axioms Sunlet.NetworkGraphCut.dimension_cut
#eval IO.println "NETWORK_STAGE_SOURCE_COMPLETE VerifiedNetworkAlgebra"
