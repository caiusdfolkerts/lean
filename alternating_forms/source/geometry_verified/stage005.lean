module

public import geometry_verified.stage004
import all geometry_verified.stage004
public import geometry_verified.stage000
import all geometry_verified.stage000
public import paper_verification.projective_line_algebra
import all paper_verification.projective_line_algebra
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import paper_verification.literal005
import all paper_verification.literal005
public import paper_verification.relative_projective_geometry2
import all paper_verification.relative_projective_geometry2
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import geometry_verified.stage002
import all geometry_verified.stage002
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Sites.EpiMono
public import geometry_verified.stage003
import all geometry_verified.stage003
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

set_option Elab.async false

section GeometryLiteralSource032
/- Original source: PaperVerification.LerayCoverVanishing -/


/-!
# Acyclic and sectionless finite covers

If an abelian sheaf has zero cohomology in every degree on every nonempty
finite intersection of a finite open cover, then it has zero global cohomology.
The proof uses the genuine Čech–Leray comparison and the actual section groups.
The cover need not consist of affine opens. In particular it applies to the
preimages of an affine frame cover under a projective-line bundle.
-/

@[expose] public section
noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti.CategoryTheory

namespace PaperVerification.LerayCoverVanishing

variable {X : TopCat.{u}} {ι : Type u} [Finite ι]
  (U : ι → Opens X) (hU : iSup U = ⊤)
  (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

include hU

/-- A finite cover whose every intersection is acyclic in all degrees
forces global acyclicity, including degree zero. -/
theorem cohomology_subsingleton
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ q, Subsingleton (F.H' q (s.inf U)))
    (q : ℕ) : Subsingleton (Sheaf.H F q) := by
  classical
  let K := (cechComplexFunctor U).obj F.obj
  have hsections (n : ℕ) (a : Fin (n + 1) → ι) :
      Subsingleton (F.obj.obj (op (∏ᶜ fun j ↦ U (a j)))) := by
    have heq : (∏ᶜ fun j ↦ U (a j)) = (Finset.univ.image a).inf U :=
      CompleteLattice.finite_product_eq_finset_image_inf U a
    have hzero : Subsingleton (F.H' 0 (∏ᶜ fun j ↦ U (a j))) := by
      rw [heq]
      exact hF _ (Finset.univ_nonempty.image a) 0
    letI := hzero
    exact (cohomologyZeroSectionsEquiv F _).symm.injective.subsingleton
  have hterm (n : ℕ) : IsZero (K.X n) := by
    change IsZero (∏ᶜ fun a : Fin (n + 1) → ι ↦
      F.obj.obj (op (∏ᶜ fun j ↦ U (a j))))
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Pi.hom_ext
    intro a
    letI := hsections n a
    exact (AddCommGrpCat.isZero_of_subsingleton _).eq_of_tgt _ _
  have hhomology : IsZero (K.homology q) :=
    (K.sc q).isZero_homology_of_isZero_X₂ (hterm q)
  let e := TauCeti.Topology.homologyCechComplexIsoH U hU F
    (fun s hs k ↦ hF s hs (k + 1)) q
  exact AddCommGrpCat.subsingleton_of_isZero (hhomology.of_iso e.symm)

end PaperVerification.LerayCoverVanishing
end
end
end GeometryLiteralSource032

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: PaperVerification.LerayCoverVanishing"

section GeometryLiteralSource033
/- Original source: PaperVerification.SegreCoordinateLocalization -/
/-
The proof of `addMonoidAlgebra_localization` is an additive adaptation of
TauCeti.Algebra.MonoidAlgebra.Localization at commit
06d5bb4e3ebb737dc6538567f5c53bf8800b9362, released under Apache 2.0.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
-/


/-!
# Coordinate localizations as literal Laurent monomial algebras

Inverting the product of the coordinates indexed by `S` gives exactly the
Laurent monomials whose exponents outside `S` are nonnegative. The proof gives
the full universal localization property; it does not merely embed a selected
finite set of fractions. This is the local algebra needed to connect the
monomial Čech calculation to sections on intersections of projective charts.
-/

set_option autoImplicit false

@[expose] public section

namespace PaperVerification.Segre.CoordinateLocalization

open scoped BigOperators

variable {K I : Type*} [CommRing K] [Fintype I] [DecidableEq I]

/-- Exponents of exactly the monomials available after inverting the coordinates in `S`. -/
def allowedExponents (S : Finset I) : AddSubmonoid (I → ℤ) where
  carrier := {a | ∀ i, i ∉ S → 0≤a i}
  zero_mem' := by intro i _; exact le_refl 0
  add_mem' ha hb := by intro i hi; exact add_nonneg (ha i hi) (hb i hi)

def naturalExponentMap (S : Finset I) : (I →₀ ℕ) →+ allowedExponents S where
  toFun a := ⟨fun i => (a i : ℤ),by intro i _; exact Int.natCast_nonneg _⟩
  map_zero' := Subtype.ext (by funext i; rfl)
  map_add' a b := Subtype.ext (by funext i; exact Int.natCast_add _ _)

theorem naturalExponentMap_injective (S : Finset I) : Function.Injective (naturalExponentMap S) := by
  intro a b hab
  ext i
  exact Int.natCast_inj.mp (congrFun (congrArg Subtype.val hab) i)

/-- The squarefree exponent of the product of the coordinates in `S`. -/
noncomputable def denominatorExponent (S : Finset I) : I →₀ ℕ :=
  ∑ i ∈ S, Finsupp.single i 1

@[simp] theorem denominatorExponent_apply (S : Finset I) (i : I) :
    denominatorExponent S i=if i∈S then 1 else 0 := by
  classical
  simp [denominatorExponent,Finsupp.single_apply]

noncomputable def inverseDenominator (S : Finset I) : allowedExponents S :=
  ⟨fun i => if i∈S then -1 else 0,by intro i hi; simp only [if_neg hi,le_refl]⟩

theorem denominator_add_inverse (S : Finset I) :
    naturalExponentMap S (denominatorExponent S)+inverseDenominator S=0 := by
  apply Subtype.ext
  funext i
  change (denominatorExponent S i : ℤ)+(if i∈S then -1 else 0)=0
  rw [denominatorExponent_apply]
  split_ifs <;> rfl

/-- A common denominator clears every negative exponent in a Laurent monomial. -/
theorem exponent_clear_denominator (S : Finset I) (a : allowedExponents S) :
    ∃ m : ℕ, a+m • naturalExponentMap S (denominatorExponent S) ∈ Set.range (naturalExponentMap S) := by
  classical
  let m : ℕ := ∑ i, (-a.val i).toNat
  have hm (i : I) : (-a.val i).toNat≤m := by
    change (-a.val i).toNat≤∑ j,(-a.val j).toNat
    exact Finset.single_le_sum (fun j _ => Nat.zero_le ((-a.val j).toNat))
      (Finset.mem_univ i)
  have hn (i : I) : 0≤a.val i+(if i∈S then (m : ℤ) else 0) := by
    by_cases hi : i∈S
    · rw [if_pos hi]
      have := hm i
      have hc : -a.val i≤((-a.val i).toNat : ℤ) := by omega
      omega
    · rw [if_neg hi,add_zero]
      exact a.property i hi
  let b : I →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun i => (a.val i+(if i∈S then (m : ℤ) else 0)).toNat)
  refine ⟨m,b,?_⟩
  apply Subtype.ext
  funext i
  change ((a.val i+(if i∈S then (m : ℤ) else 0)).toNat : ℤ) =
    a.val i + m • ((denominatorExponent S i : ℕ) : ℤ)
  rw [Int.toNat_of_nonneg (hn i),denominatorExponent_apply]
  split_ifs <;> simp

/-- The exact monomial algebra of a coordinate localization. -/
abbrev LocalLaurent (K I : Type*) [CommRing K] (S : Finset I) :=
  AddMonoidAlgebra K (allowedExponents S)

noncomputable def localizationMap (S : Finset I) : MvPolynomial I K →ₐ[K] LocalLaurent K I S :=
  AddMonoidAlgebra.mapDomainAlgHom K K (naturalExponentMap S)

noncomputable instance localizationAlgebra (S : Finset I) :
    Algebra (MvPolynomial I K) (LocalLaurent K I S) :=
  (localizationMap (K := K) S).toRingHom.toAlgebra

theorem localizationMap_injective (S : Finset I) : Function.Injective (localizationMap (K := K) S) :=
  AddMonoidAlgebra.mapDomain_injective (naturalExponentMap_injective S)

/-- The image of the denominator monomial has its literal negative-exponent inverse. -/
theorem denominator_isUnit (S : Finset I) :
    IsUnit (AddMonoidAlgebra.single (naturalExponentMap S (denominatorExponent S)) (1 : K)) := by
  refine ⟨⟨AddMonoidAlgebra.single (naturalExponentMap S (denominatorExponent S)) (1 : K),
    AddMonoidAlgebra.single (inverseDenominator S) 1,?_,?_⟩,rfl⟩
  · change AddMonoidAlgebra.single (naturalExponentMap S (denominatorExponent S)) (1 : K)*
      AddMonoidAlgebra.single (inverseDenominator S) (1 : K)=1
    rw [AddMonoidAlgebra.single_mul_single,denominator_add_inverse,one_mul,
      ← AddMonoidAlgebra.one_def]
  · change AddMonoidAlgebra.single (inverseDenominator S) (1 : K)*
      AddMonoidAlgebra.single (naturalExponentMap S (denominatorExponent S)) (1 : K)=1
    rw [AddMonoidAlgebra.single_mul_single,add_comm,denominator_add_inverse,one_mul,
      ← AddMonoidAlgebra.one_def]

section GeneralMonoidLocalization

variable {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]

/-- The induced monoid-algebra map has the full localization property. -/
theorem addMonoidAlgebra_localization (f : M →+ N) (hf : Function.Injective f) (x : M)
    (hx : IsUnit (AddMonoidAlgebra.single (f x) (1 : K)))
    (hsurj : ∀ y : N, ∃ m : ℕ, y+m • f x ∈ Set.range f) :
    letI := (AddMonoidAlgebra.mapDomainRingHom K f).toAlgebra
    IsLocalization.Away (AddMonoidAlgebra.single x (1 : K)) (AddMonoidAlgebra K N) := by
  letI := (AddMonoidAlgebra.mapDomainRingHom K f).toAlgebra
  have halg : ∀ a : AddMonoidAlgebra K M,
      algebraMap (AddMonoidAlgebra K M) (AddMonoidAlgebra K N) a =
        AddMonoidAlgebra.mapDomain f a := fun a => by
    rw [RingHom.algebraMap_toAlgebra,AddMonoidAlgebra.mapDomainRingHom_apply]
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [halg,AddMonoidAlgebra.mapDomain_single]
    exact hx
  · intro s
    induction s using AddMonoidAlgebra.induction_on with
    | of y =>
      obtain ⟨m,z,hz⟩ := hsurj y
      refine ⟨m,AddMonoidAlgebra.single z 1,?_⟩
      simp [halg,hz]
    | add s t hs ht =>
      obtain ⟨m,a,ha⟩ := hs
      obtain ⟨r,b,hb⟩ := ht
      refine ⟨m+r,a*AddMonoidAlgebra.single x 1^r+b*AddMonoidAlgebra.single x 1^m,?_⟩
      simp only [map_add,map_mul,map_pow]
      rw [← ha,← hb]
      ring
    | smul c s hs =>
      obtain ⟨m,a,ha⟩ := hs
      refine ⟨m,algebraMap K (AddMonoidAlgebra K M) c*a,?_⟩
      have ha' : s*AddMonoidAlgebra.mapDomain f (AddMonoidAlgebra.single x 1)^m =
          AddMonoidAlgebra.mapDomain f a := by simpa only [halg] using ha
      simp only [Algebra.smul_def,halg]
      rw [mul_assoc,ha',AddMonoidAlgebra.mapDomain_mul]
      congr 1
      exact ((AddMonoidAlgebra.mapDomainAlgHom K K f).commutes c).symm
  · intro a b hab
    exact ⟨0,by rw [AddMonoidAlgebra.mapDomain_injective hf hab]⟩

end GeneralMonoidLocalization

theorem denominator_monomial_eq_prod (S : Finset I) :
    MvPolynomial.monomial (denominatorExponent S) (1 : K) = ∏ i ∈ S, MvPolynomial.X i := by
  rw [denominatorExponent,MvPolynomial.monomial_sum_one]
  rfl

/-- All and only coordinate Laurent polynomials form the standard coordinate localization. -/
noncomputable instance localLaurent_isLocalization (S : Finset I) :
    IsLocalization.Away (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial I K)) (LocalLaurent K I S) := by
  rw [← denominator_monomial_eq_prod]
  exact addMonoidAlgebra_localization (naturalExponentMap S) (naturalExponentMap_injective S)
    (denominatorExponent S) (denominator_isUnit S) (exponent_clear_denominator S)

/-- The actual localization is canonically the Laurent coefficient model. -/
noncomputable def coordinateLocalizationEquiv (S : Finset I) :
    Localization.Away (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial I K)) ≃ₐ[MvPolynomial I K]
      LocalLaurent K I S :=
  IsLocalization.algEquiv (Submonoid.powers (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial I K))) _ _

end PaperVerification.Segre.CoordinateLocalization
end
end GeometryLiteralSource033

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: PaperVerification.SegreCoordinateLocalization"

section GeometryLiteralSource034
/- Original source: PaperVerification.SegreLocalizationGrading -/


/-!
# Integer degrees and homogeneous fractions in coordinate localizations

The Laurent model carries its literal total-exponent grading. Every element
of degree `t` has one homogeneous numerator over a power of the coordinate
product, with numerator degree exactly the denominator degree plus `t`.
This is the precise form required by the twisting-sheaf section comparison.
-/

set_option autoImplicit false

@[expose] public section

namespace PaperVerification.Segre.CoordinateLocalization

open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

def totalDegree (S : Finset I) : allowedExponents S →+ ℤ where
  toFun a := ∑ i, a.val i
  map_zero' := by simp
  map_add' a b := by simp only [AddSubmonoid.coe_add,Pi.add_apply,Finset.sum_add_distrib]

abbrev localDegree (S : Finset I) (t : ℤ) : Submodule K (LocalLaurent K I S) :=
  AddMonoidAlgebra.gradeBy K (totalDegree S) t

theorem totalDegree_natural (S : Finset I) (a : I →₀ ℕ) :
    totalDegree S (naturalExponentMap S a)=(a.degree : ℤ) := by
  change (∑ i, (a i : ℤ)) = (a.degree : ℤ)
  simp only [Finsupp.degree_eq_sum, Nat.cast_sum]

theorem localizationMap_coeff (S : Finset I) (p : MvPolynomial I K) (a : I →₀ ℕ) :
    (localizationMap S p).coeff (naturalExponentMap S a)=p.coeff a :=
  Finsupp.mapDomain_apply_of_injective (naturalExponentMap_injective S) p.coeff a

/-- The integer grading of a polynomial image is precisely its ordinary monomial grading. -/
theorem localizationMap_mem_degree_iff (S : Finset I) (p : MvPolynomial I K) (t : ℤ) :
    localizationMap S p ∈ localDegree S t ↔
      ∀ a : I →₀ ℕ, p.coeff a≠0 → (a.degree : ℤ)=t := by
  classical
  constructor
  · intro hp a ha
    have hm : naturalExponentMap S a ∈ (localizationMap S p).coeff.support := by
      rw [Finsupp.mem_support_iff,localizationMap_coeff]
      exact ha
    simpa only [totalDegree_natural] using hp _ hm
  · intro hp a ha
    have hc : (Finsupp.mapDomain (naturalExponentMap S) p.coeff) a≠0 :=
      Finsupp.mem_support_iff.mp ha
    obtain ⟨b,rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hc
    rw [Finsupp.mapDomain_apply_of_injective (naturalExponentMap_injective S)] at hc
    exact (totalDegree_natural S b).trans (hp b hc)

theorem localizationMap_mem_degree (S : Finset I) {j : ℕ} {p : MvPolynomial I K}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule I K j) :
    localizationMap S p ∈ localDegree S (j : ℤ) := by
  apply (localizationMap_mem_degree_iff S p j).mpr
  intro a ha
  have h : a.degree=j := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp ha
  exact congrArg (fun z : ℕ => (z : ℤ)) h

theorem homogeneous_of_localizationMap_mem (S : Finset I) {j : ℕ} {p : MvPolynomial I K}
    (hp : localizationMap S p ∈ localDegree S (j : ℤ)) :
    p ∈ MvPolynomial.homogeneousSubmodule I K j := by
  intro a ha
  have h : a.degree=j := Int.natCast_inj.mp ((localizationMap_mem_degree_iff S p j).mp hp a ha)
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h

/-- The polynomial whose inversion defines the chart intersection. -/
noncomputable def denominator (S : Finset I) : MvPolynomial I K := ∏ i ∈ S, MvPolynomial.X i

theorem localizationMap_denominator (S : Finset I) :
    localizationMap S (denominator (K := K) S) =
      AddMonoidAlgebra.single (naturalExponentMap S (denominatorExponent S)) 1 := by
  rw [denominator,← denominator_monomial_eq_prod]
  exact AddMonoidAlgebra.mapDomain_single

theorem denominator_homogeneous (S : Finset I) :
    denominator (K := K) S ∈ MvPolynomial.homogeneousSubmodule I K S.card := by
  apply (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
  simpa only [denominator,Finset.sum_const,smul_eq_mul,mul_one] using
    MvPolynomial.IsHomogeneous.prod S (fun i => (MvPolynomial.X i : MvPolynomial I K))
      (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X (R := K) i)

theorem denominator_image_isUnit (S : Finset I) :
    IsUnit (localizationMap S (denominator (K := K) S)) := by
  rw [localizationMap_denominator]
  exact denominator_isUnit S

theorem denominator_image_degree (S : Finset I) :
    localizationMap S (denominator (K := K) S) ∈ localDegree S (S.card : ℤ) :=
  localizationMap_mem_degree S (denominator_homogeneous S)

/-- The homogeneous numerator/denominator representation of every Laurent section. -/
theorem homogeneous_fraction (S : Finset I) (hS : S.Nonempty) (t : ℤ)
    (x : LocalLaurent K I S) (hx : x ∈ localDegree S t) :
    ∃ (m j : ℕ) (p : MvPolynomial I K),
      (j : ℤ)=(m*S.card : ℕ)+t ∧
      p ∈ MvPolynomial.homogeneousSubmodule I K j ∧
      x*(localizationMap S (denominator S))^m=localizationMap S p := by
  classical
  letI : IsLocalization.Away (denominator (K := K) S) (LocalLaurent K I S) := by
    change IsLocalization.Away (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial I K))
      (LocalLaurent K I S)
    exact localLaurent_isLocalization S
  obtain ⟨m,p,hp⟩ := IsLocalization.Away.surj (denominator (K := K) S) x
  change x*(localizationMap S (denominator S))^m=localizationMap S p at hp
  have hdeg : localizationMap S p ∈ localDegree S (t+m • (S.card : ℤ)) := by
    rw [← hp]
    exact SetLike.mul_mem_graded hx (SetLike.pow_mem_graded m (denominator_image_degree S))
  by_cases hp0 : p=0
  · have hx0 : x=0 := by
      apply (IsUnit.mul_left_eq_zero ((denominator_image_isUnit S).pow m)).mp
      rw [hp,hp0,map_zero]
    let r : ℕ := (-t).toNat
    have hr : -t≤(r : ℤ) := by dsimp [r]; omega
    have hcard : 0<S.card := hS.card_pos
    have hmul : r≤r*S.card := Nat.le_mul_of_pos_right r hcard
    have hmul' : (r : ℤ)≤((r*S.card : ℕ) : ℤ) := by omega
    have hnonneg : 0≤((r*S.card : ℕ) : ℤ)+t := by omega
    refine ⟨r,(((r*S.card : ℕ) : ℤ)+t).toNat,0,?_,?_,?_⟩
    · exact Int.toNat_of_nonneg hnonneg
    · exact Submodule.zero_mem _
    · rw [hx0,zero_mul,map_zero]
  · obtain ⟨a,ha⟩ := MvPolynomial.exists_coeff_ne_zero hp0
    have he := (localizationMap_mem_degree_iff S p _).mp hdeg a ha
    have hnonneg : 0≤t+m • (S.card : ℤ) := he ▸ Int.natCast_nonneg a.degree
    refine ⟨m,(t+m • (S.card : ℤ)).toNat,p,?_,?_,hp⟩
    · rw [Int.toNat_of_nonneg hnonneg]
      simp only [nsmul_eq_mul,Int.natCast_mul]
      omega
    · apply homogeneous_of_localizationMap_mem S
      rw [Int.toNat_of_nonneg hnonneg]
      exact hdeg

end PaperVerification.Segre.CoordinateLocalization
end
end GeometryLiteralSource034

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: PaperVerification.SegreLocalizationGrading"

section GeometryLiteralSource035
/- Original source: TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The twisting sheaves are quasi-coherent

Let `A = ⨁ᵢ 𝒜 i` be an `ℕ`-graded commutative ring. This file proves that the twisting sheaves
`𝒪(n)` on `Proj A` are quasi-coherent, for every `n ∈ ℤ` and without assuming that `A` is generated
in degree one (`AlgebraicGeometry.Proj.isQuasicoherent_twistingSheaf`).

The standard opens `D₊(f)`, for `f` homogeneous of positive degree `d`, are affine and cover
`Proj A`. A function on `D₊(f)` is a fraction `a = g / fᵏ` with `g` homogeneous of degree `k d`,
and it is invertible exactly on `D₊(fg)` (`AlgebraicGeometry.Proj.basicOpen_awayToSection_mk`).
Using the description of the sections of `𝒪(n)` over standard opens as fractions
(`AlgebraicGeometry.Proj.twistingSheaf.exists_eq_const_basicOpen` and
`AlgebraicGeometry.Proj.twistingSheaf.const_eq_zero_iff`), we show that the restriction
`Γ(D₊(f), 𝒪(n)) → Γ(D₊(fg), 𝒪(n))` is the localization at `a`. Quasi-coherence then follows from
the affine-local criterion `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocalizedModule`.

Since quasi-coherence is local, this is the input needed to show that the twisting sheaves `𝒪(n)`
of a relative `Proj`, which restrict to the twisting sheaves of its charts, are quasi-coherent.

## Main results

* `AlgebraicGeometry.Proj.isQuasicoherent_twistingSheaf`: `𝒪(n)` is quasi-coherent.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.11(b).
* [Stacks, Lemma 27.10.3 (01MM)](https://stacks.math.columbia.edu/tag/01MM)
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace HomogeneousLocalization

namespace AlgebraicGeometry.Proj

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜] {n : ℤ}

namespace twistingSheaf

/-- A section `c` of the structure sheaf over `U` acts on the sections of `𝒪(n)` over a basic
open `(Proj 𝒜).basicOpen b ≤ U` through its restriction (`Scheme.Modules.moduleBasicOpen`), that
is pointwise through its values in the homogeneous localizations. -/
private theorem smul_basicOpen_apply {U : (Proj 𝒜).Opens} (b c : Γ(Proj 𝒜, U))
    (t : Γ(twistingSheaf 𝒜 n, (Proj 𝒜).basicOpen b)) (x : (Proj 𝒜).basicOpen b) :
    (c • t).1 x = (c.1 ⟨x.1, (Proj 𝒜).basicOpen_le b x.2⟩).val * t.1 x :=
  (rfl)

variable {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) {k : ℕ} {g : A} (hg : g ∈ 𝒜 (k • d))

/-- The powers of the function `g / fᵏ` on `D₊(f)` take the values `(g / fᵏ)ᴺ` in the
localizations. -/
private theorem val_awayToSection_mk_pow_apply (N : ℕ) (y : basicOpen 𝒜 f) :
    (((awayToSection 𝒜 f (Away.mk 𝒜 hf k g hg)) ^ N).1 y).val =
      Localization.mk g ⟨f ^ k, fun h ↦ y.2 (y.1.isPrime.mem_of_pow_mem k h)⟩ ^ N :=
  (congrArg val (Proj.pow_apply _ _ _ N)).trans
    ((val_pow _ _).trans (congrArg (· ^ N) (val_awayToSection_mk_apply ..)))

/-- Every section of `𝒪(n)` over the locus `D₊(fg)` where `a = g / fᵏ` is invertible becomes,
after multiplication by a power of `a`, the restriction of a section over `D₊(f)`. -/
private theorem exists_pow_smul_eq_basicOpenRestrict (hd : 0 < d)
    (t : Γ(twistingSheaf 𝒜 n, (Proj 𝒜).basicOpen (awayToSection 𝒜 f (Away.mk 𝒜 hf k g hg)))) :
    ∃ (m : ℕ) (s : Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 f)),
      awayToSection 𝒜 f (Away.mk 𝒜 hf k g hg) ^ m • t =
        (twistingSheaf 𝒜 n).basicOpenRestrict (awayToSection 𝒜 f (Away.mk 𝒜 hf k g hg)) s := by
  have hV := basicOpen_awayToSection_mk hf k g hg
  -- on `D₊(fg)`, `t` is a fraction `R / (fg)ᵐ`, and `(g / fᵏ)ᵐ • t` is `R / f^(m (k + 1))`
  obtain ⟨m, J, hJ, R, hR, ht⟩ :=
    exists_eq_const_basicOpen (SetLike.mul_mem_graded hf hg) (by omega)
      ((twistingSheaf 𝒜 n).presheaf.map (homOfLE hV.ge).op t)
  refine ⟨m, const (i := (m * (k + 1)) • d) (j := J)
    (by rw [hJ]; simp only [smul_eq_mul]; push_cast; ring) R (f ^ (m * (k + 1))) hR
    (SetLike.pow_mem_graded _ hf) _ (fun x hx h ↦ hx (x.isPrime.mem_of_pow_mem _ h)), ?_⟩
  refine Eq.trans ?_ ((Scheme.Modules.basicOpenRestrict_apply _ _ _).trans (res_const ..)).symm
  refine ext fun x ↦ ?_
  have hx : x.1 ∈ basicOpen 𝒜 (f * g) := hV ▸ x.2
  have e : t.1 x = _ := (res_apply _ t ⟨x.1, hx⟩).symm.trans
    (congr($ht.1 ⟨x.1, hx⟩).trans (const_apply ..))
  refine (smul_basicOpen_apply _ _ t x).trans (Eq.trans ?_ (const_apply ..).symm)
  refine (congrArg₂ (· * ·)
    (val_awayToSection_mk_pow_apply hf hg m ⟨x.1, (Proj 𝒜).basicOpen_le _ x.2⟩) e).trans ?_
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-- A section of `𝒪(n)` over `D₊(f)` vanishing on the locus `D₊(fg)` where `a = g / fᵏ` is
invertible is killed by a power of `a`. -/
private theorem exists_pow_smul_eq_zero (hd : 0 < d) (s : Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 f))
    (hs : (twistingSheaf 𝒜 n).basicOpenRestrict (awayToSection 𝒜 f (Away.mk 𝒜 hf k g hg)) s = 0) :
    ∃ N : ℕ, awayToSection 𝒜 f (Away.mk 𝒜 hf k g hg) ^ N • s = 0 := by
  have hV := basicOpen_awayToSection_mk hf k g hg
  -- `s` is a fraction `R / fᵐ`; it vanishes on `D₊(fg)`, so `(fg)ᴺ R = 0`, and then
  -- `(g / fᵏ)ᴺ • s = gᴺ R / f^(k N + m)` vanishes on `D₊(f)`
  obtain ⟨m, J, hJ, R, hR, hs'⟩ := exists_eq_const_basicOpen hf hd s
  have hfm : f ^ m ∈ 𝒜 (m * d) := by simpa using SetLike.pow_mem_graded m hf
  have hfgf : basicOpen 𝒜 (f * g) ≤ basicOpen 𝒜 f := hV.ge.trans ((Proj 𝒜).basicOpen_le _)
  have h0 : const hJ R (f ^ m) hR hfm (basicOpen 𝒜 (f * g))
      (fun x hx h ↦ hfgf hx (x.isPrime.mem_of_pow_mem m h)) = 0 := by
    refine (res_const hJ R (f ^ m) hR hfm _ (homOfLE hfgf)).symm.trans
      ((congrArg _ hs'.symm).trans ?_)
    have := congr((twistingSheaf 𝒜 n).presheaf.map (homOfLE hV.ge).op $hs)
    rwa [Scheme.Modules.basicOpenRestrict_apply, map_zero, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp] at this
  obtain ⟨N, hN⟩ := (const_eq_zero_iff (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜
    (by omega) (SetLike.mul_mem_graded hf hg)) ..).1 h0
  refine ⟨N, ext fun x ↦ ?_⟩
  have e : s.1 x = _ := congr($hs'.1 x).trans (const_apply ..)
  refine (smul_apply _ _ x).trans ((congrArg₂ (· * ·)
    (val_awayToSection_mk_pow_apply hf hg N x) e).trans (Eq.trans ?_ (zero_apply x).symm))
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk'_apply,
    IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨f ^ N, fun h ↦ x.2 (x.1.isPrime.mem_of_pow_mem N h)⟩, by linear_combination hN⟩

/-- For `f` homogeneous of positive degree and a function `a` on `D₊(f)`, the restriction of
sections of `𝒪(n)` from `D₊(f)` to the locus `(Proj 𝒜).basicOpen a` where `a` is invertible is
the localization at `a`. Once `isQuasicoherent_twistingSheaf` is available, this is a case of
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict`. -/
private theorem isLocalizedModule_basicOpenRestrict (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (a : Γ(Proj 𝒜, basicOpen 𝒜 f)) :
    IsLocalizedModule.Away a ((twistingSheaf 𝒜 n).basicOpenRestrict a) := by
  -- `a` is a fraction `g / fᵏ`
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (basicOpenIsoAway 𝒜 f hf hd).hom).2 a
  obtain ⟨k, g, hg, rfl⟩ := Away.mk_surjective 𝒜 hf a
  rw [basicOpenIsoAway_hom]
  exact .mk_of_addCommGroup (Scheme.Modules.isUnit_algebraMap_end_basicOpen _ _)
    (exists_pow_smul_eq_basicOpenRestrict hf hg hd) (exists_pow_smul_eq_zero hf hg hd)

end twistingSheaf

variable (𝒜 n) in
/-- **The twisting sheaves `𝒪(n)` are quasi-coherent.** -/
instance isQuasicoherent_twistingSheaf : (twistingSheaf 𝒜 n).IsQuasicoherent :=
  -- the standard opens `D₊(f)`, `f` homogeneous of positive degree, form an affine open cover
  Scheme.Modules.isQuasicoherent_of_isLocalizedModule (ι := {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2})
    _ (fun p ↦ basicOpen 𝒜 p.1.1) (fun p ↦ isAffineOpen_basicOpen 𝒜 p.1.1 p.2.2 p.2.1)
    (eq_top_iff.2 fun x _ ↦ by
      obtain ⟨i, hi, f, hf, hfx⟩ := ProjectiveSpectrum.exists_le_mem_notMem (𝒜 := 𝒜) x 1
      exact Opens.mem_iSup.2 ⟨⟨(f, i), by omega, hf⟩, hfx⟩)
    fun p a ↦ twistingSheaf.isLocalizedModule_basicOpenRestrict p.2.2 p.2.1 a

end AlgebraicGeometry.Proj
end
end
end GeometryLiteralSource035

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent"

section GeometryLiteralSource036
/- Original source: PaperVerification.SegreTwistingSections -/


/-!
# Actual twisting-sheaf sections and Laurent homogeneous components

For a nonempty set of coordinate charts, the sections of `O(t)` on their
intersection are canonically the total-degree-`t` part of the coordinate
Laurent algebra. The map is evaluation in the actual prime localizations
used by the twisting sheaf. Its surjectivity uses the proved standard-open
section theorem, and its injectivity uses the standard-open vanishing criterion, over any
commutative base ring. Thus this comparison includes the whole section group.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.TwistingSections

open CoordinateLocalization AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

local notation "P" => MvPolynomial I K
local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K

instance denominator_isLocalization (S : Finset I) :
    IsLocalization.Away (denominator (K := K) S) (LocalLaurent K I S) := by
  change IsLocalization.Away (∏ i ∈ S, (MvPolynomial.X i : P)) (LocalLaurent K I S)
  exact localLaurent_isLocalization S

def chartIntersection (S : Finset I) : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 (denominator S)

/-- The canonical localization map to every actual point of the chart intersection. -/
def toPoint (S : Finset I) (x : chartIntersection (K := K) S) :
    LocalLaurent K I S →+* ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val := by
  letI : x.val.asHomogeneousIdeal.toIdeal.IsPrime := x.val.isPrime
  exact IsLocalization.Away.lift (denominator S)
    (g := algebraMap P (ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val))
    (IsLocalization.map_units _
      (⟨denominator S, x.property⟩ : x.val.asHomogeneousIdeal.toIdeal.primeCompl))

@[simp] theorem toPoint_polynomial (S : Finset I) (x : chartIntersection (K := K) S)
    (p : P) : toPoint S x (localizationMap S p)=algebraMap P _ p := by
  letI : x.val.asHomogeneousIdeal.toIdeal.IsPrime := x.val.isPrime
  exact IsLocalization.Away.lift_eq _ _ _

theorem chart_le_power (S : Finset I) (m : ℕ) :
    chartIntersection (K := K) S ≤ Proj.basicOpen 𝒜 ((denominator S)^m) := by
  intro x hx hp
  exact hx (x.isPrime.mem_of_pow_mem m hp)

/-- A homogeneous Laurent fraction has the expected value in every point localization. -/
theorem toPoint_fraction (S : Finset I) (x : chartIntersection (K := K) S)
    (z : LocalLaurent K I S) (m : ℕ) (p : P)
    (hz : z*(localizationMap S (denominator S))^m=localizationMap S p) :
    toPoint S x z = Localization.mk p
      ⟨(denominator S)^m,chart_le_power S m x.property⟩ := by
  letI : x.val.asHomogeneousIdeal.toIdeal.IsPrime := x.val.isPrime
  let d : x.val.asHomogeneousIdeal.toIdeal.primeCompl :=
    ⟨(denominator S)^m,chart_le_power S m x.property⟩
  apply (IsLocalization.map_units
    (ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val) d).mul_left_injective
  have he := congrArg (toPoint S x) hz
  rw [map_mul,map_pow,toPoint_polynomial,toPoint_polynomial,← map_pow] at he
  exact he.trans (by
    simpa only [Localization.mk_eq_mk'_apply] using
      (IsLocalization.mk'_spec (ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val) p d).symm)

/-- The entire homogeneous Laurent component maps to actual sections. -/
def toSection (S : Finset I) (hS : S.Nonempty) (t : ℤ)
    (z : localDegree (K := K) S t) : Γ(Proj.twistingSheaf 𝒜 t,chartIntersection S) :=
  ⟨fun x => toPoint S x z.val,by
    obtain ⟨m,j,p,hj,hp,hz⟩ := homogeneous_fraction S hS t z.val z.property
    have hd : (denominator (K := K) S)^m ∈ 𝒜 (m*S.card) := by
      simpa [nsmul_eq_mul] using SetLike.pow_mem_graded m (denominator_homogeneous S)
    have he : (fun x : chartIntersection (K := K) S => toPoint S x z.val) =
        (Proj.twistingSheaf.const hj p ((denominator S)^m) hp hd _ (chart_le_power S m)).val := by
      funext x
      exact toPoint_fraction S x z.val m p hz
    exact he.symm ▸
      (Proj.twistingSheaf.const hj p ((denominator S)^m) hp hd _ (chart_le_power S m)).property⟩

@[simp] theorem toSection_apply (S : Finset I) (hS : S.Nonempty) (t : ℤ)
    (z : localDegree (K := K) S t) (x : chartIntersection (K := K) S) :
    (toSection S hS t z).val x=toPoint S x z.val := rfl

def toSectionHom (S : Finset I) (hS : S.Nonempty) (t : ℤ) :
    localDegree (K := K) S t →+ Γ(Proj.twistingSheaf 𝒜 t,chartIntersection S) where
  toFun := toSection S hS t
  map_zero' := Proj.twistingSheaf.ext (fun x => map_zero (toPoint S x))
  map_add' z w := Proj.twistingSheaf.ext (fun x => map_add (toPoint S x) z.val w.val)

/-- The standard-open vanishing criterion detects every homogeneous Laurent element.
This uses localization at a power of the denominator, so it works over an arbitrary
commutative base ring, including rings with zero divisors. -/
theorem toSection_eq_zero (S : Finset I) (hS : S.Nonempty) (t : ℤ)
    (z : localDegree (K := K) S t) (h : toSection S hS t z = 0) : z = 0 := by
  obtain ⟨m,j,p,hj,hp,hz⟩ := homogeneous_fraction S hS t z.val z.property
  have hd : (denominator (K := K) S)^m ∈ 𝒜 (m*S.card) := by
    simpa [nsmul_eq_mul] using SetLike.pow_mem_graded m (denominator_homogeneous S)
  have he : toSection S hS t z =
      Proj.twistingSheaf.const hj p ((denominator S)^m) hp hd _ (chart_le_power S m) :=
    Proj.twistingSheaf.ext (fun x => toPoint_fraction S x z.val m p hz)
  obtain ⟨N,hN⟩ := (Proj.twistingSheaf.const_eq_zero_iff
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hS.card_pos (denominator_homogeneous S))
    hj hp hd (chart_le_power S m)).mp (he.symm.trans h)
  have hp0 : localizationMap S p = 0 := by
    apply (IsUnit.mul_left_eq_zero ((denominator_image_isUnit (K := K) S).pow N)).mp
    rw [mul_comm]
    simpa only [map_mul,map_pow,map_zero] using congrArg (localizationMap S) hN
  apply Subtype.ext
  apply (IsUnit.mul_left_eq_zero ((denominator_image_isUnit (K := K) S).pow m)).mp
  rw [hz,hp0]

/-- No section information is lost in the Laurent-to-sheaf comparison. -/
theorem toSection_injective (S : Finset I) (hS : S.Nonempty) (t : ℤ) :
    Function.Injective (toSection (K := K) S hS t) := by
  intro z w h
  apply sub_eq_zero.mp
  apply toSection_eq_zero S hS t
  change toSectionHom S hS t (z-w) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr h

def inverseElement (S : Finset I) : LocalLaurent K I S :=
  AddMonoidAlgebra.single (inverseDenominator S) 1

theorem inverseElement_mul_denominator (S : Finset I) :
    inverseElement (K := K) S * localizationMap S (denominator S)=1 := by
  rw [inverseElement,localizationMap_denominator,AddMonoidAlgebra.single_mul_single,
    add_comm,denominator_add_inverse,one_mul,← AddMonoidAlgebra.one_def]

theorem inverseElement_degree (S : Finset I) :
    inverseElement (K := K) S ∈ localDegree S (-(S.card : ℤ)) := by
  have he : totalDegree S (inverseDenominator S)=-(S.card : ℤ) := by
    simp [totalDegree,inverseDenominator]
  rw [← he]
  exact AddMonoidAlgebra.single_mem_gradeBy _ _ _

theorem fraction_mem_degree (S : Finset I) (t : ℤ) (m j : ℕ) (p : P)
    (hj : (j : ℤ)=(m*S.card : ℕ)+t) (hp : p ∈ 𝒜 j) :
    localizationMap S p*(inverseElement S)^m ∈ localDegree (K := K) S t := by
  have h := SetLike.mul_mem_graded (localizationMap_mem_degree S hp)
    (SetLike.pow_mem_graded m (inverseElement_degree (K := K) S))
  have he : (j : ℤ)+m • (-(S.card : ℤ))=t := by
    simp only [nsmul_eq_mul,Int.natCast_mul,mul_neg] at hj ⊢
    omega
  simpa only [he] using h

theorem toSection_surjective (S : Finset I) (hS : S.Nonempty) (t : ℤ) :
    Function.Surjective (toSection (K := K) S hS t) := by
  intro s
  obtain ⟨m,j,hj,p,hp,hs⟩ := Proj.twistingSheaf.exists_eq_const_basicOpen
    (denominator_homogeneous (K := K) S) hS.card_pos s
  let z : LocalLaurent K I S := localizationMap S p*(inverseElement S)^m
  have hz : z*(localizationMap S (denominator S))^m=localizationMap S p := by
    dsimp [z]
    rw [mul_assoc,← mul_pow,inverseElement_mul_denominator,one_pow,mul_one]
  refine ⟨⟨z,fraction_mem_degree S t m j p hj hp⟩,?_⟩
  rw [hs]
  apply Proj.twistingSheaf.ext
  intro x
  exact toPoint_fraction S x z m p hz

/-- Canonical comparison with the full actual twisting-sheaf section group. -/
def sectionsEquiv (S : Finset I) (hS : S.Nonempty) (t : ℤ) :
    localDegree (K := K) S t ≃+ Γ(Proj.twistingSheaf 𝒜 t,chartIntersection S) :=
  AddEquiv.ofBijective (toSectionHom S hS t)
    ⟨toSection_injective S hS t,toSection_surjective S hS t⟩

end PaperVerification.Segre.TwistingSections
end
end
end GeometryLiteralSource036

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: PaperVerification.SegreTwistingSections"

section GeometryLiteralSource037
/- Original source: PaperVerification.SegreTwistingRestrictions -/


/-!
# Naturality of the Laurent description of twisting-sheaf sections

The map on coordinate intersections is the literal inclusion of Laurent
monomials. Its total-degree restriction commutes with the actual sheaf
restriction map. Consequently the coefficient calculation is compatible
with every face of the Čech complex, not merely with its separate terms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.CoordinateLocalization

open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

/-- Enlarging the inverted coordinate set preserves each literal exponent. -/
def exponentInclusion {S T : Finset I} (h : S ⊆ T) : allowedExponents S →+ allowedExponents T where
  toFun a := ⟨a.val,fun i hi => a.property i (fun hs => hi (h hs))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem exponentInclusion_val {S T : Finset I} (h : S ⊆ T) (a : allowedExponents S) :
    (exponentInclusion h a).val=a.val := rfl

theorem exponentInclusion_injective {S T : Finset I} (h : S ⊆ T) :
    Function.Injective (exponentInclusion h) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun x : allowedExponents T => x.val) hab)

/-- The actual inclusion of coordinate Laurent algebras. -/
def localRestriction {S T : Finset I} (h : S ⊆ T) :
    LocalLaurent K I S →ₐ[K] LocalLaurent K I T :=
  AddMonoidAlgebra.mapDomainAlgHom K K (exponentInclusion h)

@[simp] theorem localRestriction_polynomial {S T : Finset I} (h : S ⊆ T)
    (p : MvPolynomial I K) :
    localRestriction h (localizationMap S p)=localizationMap T p := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (exponentInclusion h)
    (Finsupp.mapDomain (naturalExponentMap S) p.coeff)=
      Finsupp.mapDomain (naturalExponentMap T) p.coeff
  rw [← Finsupp.mapDomain_comp]
  rfl

@[simp] theorem localRestriction_coeff {S T : Finset I} (h : S ⊆ T)
    (z : LocalLaurent K I S) (a : allowedExponents S) :
    (localRestriction h z).coeff (exponentInclusion h a)=z.coeff a :=
  Finsupp.mapDomain_apply_of_injective (exponentInclusion_injective h) z.coeff a

theorem localRestriction_mem_degree {S T : Finset I} (h : S ⊆ T) {t : ℤ}
    {z : LocalLaurent K I S} (hz : z ∈ localDegree S t) :
    localRestriction h z ∈ localDegree T t := by
  intro a ha
  have hc : Finsupp.mapDomain (exponentInclusion h) z.coeff a≠0 :=
    Finsupp.mem_support_iff.mp ha
  obtain ⟨b,rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hc
  rw [Finsupp.mapDomain_apply_of_injective (exponentInclusion_injective h)] at hc
  exact hz b (Finsupp.mem_support_iff.mpr hc)

/-- Restriction on each whole homogeneous component. -/
def degreeRestriction {S T : Finset I} (h : S ⊆ T) (t : ℤ) :
    localDegree (K := K) S t →ₗ[K] localDegree (K := K) T t :=
  (localRestriction (K := K) h).toLinearMap.restrict
    (fun _ hz => localRestriction_mem_degree (K := K) h hz)

@[simp] theorem degreeRestriction_val {S T : Finset I} (h : S ⊆ T) (t : ℤ)
    (z : localDegree (K := K) S t) :
    (degreeRestriction h t z).val=localRestriction h z.val := rfl

end PaperVerification.Segre.CoordinateLocalization

namespace PaperVerification.Segre.TwistingSections

open CoordinateLocalization AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

local notation "P" => MvPolynomial I K
local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K

theorem chartIntersection_antitone {S T : Finset I} (h : S ⊆ T) :
    chartIntersection (K := K) T ≤ chartIntersection S :=
  Proj.basicOpen_mono 𝒜 _ _
    (Finset.prod_dvd_prod_of_subset S T (fun i => (MvPolynomial.X i : P)) h)

/-- The localization map at a point is unchanged by enlarging the denominator set. -/
theorem toPoint_localRestriction {S T : Finset I} (h : S ⊆ T)
    (x : chartIntersection (K := K) T) (z : LocalLaurent K I S) :
    toPoint T x (localRestriction h z)=
      toPoint S ⟨x.val,chartIntersection_antitone h x.property⟩ z := by
  have he : (toPoint T x).comp (localRestriction h).toRingHom=
      toPoint S ⟨x.val,chartIntersection_antitone h x.property⟩ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (denominator (K := K) S))
    apply RingHom.ext
    intro p
    change toPoint T x (localRestriction h (localizationMap S p)) =
      toPoint S ⟨x.val,chartIntersection_antitone h x.property⟩ (localizationMap S p)
    simp only [localRestriction_polynomial,toPoint_polynomial]
  exact congrArg (fun f => f z) he

/-- The full section comparison respects every actual restriction map. -/
theorem sectionsEquiv_restriction {S T : Finset I} (h : S ⊆ T)
    (hS : S.Nonempty) (hT : T.Nonempty) (t : ℤ) (z : localDegree (K := K) S t) :
    (Proj.twistingSheaf 𝒜 t).presheaf.map (homOfLE (chartIntersection_antitone h)).op
        (sectionsEquiv S hS t z) =
      sectionsEquiv T hT t (degreeRestriction h t z) := by
  apply Proj.twistingSheaf.ext
  intro x
  exact (toPoint_localRestriction h x z.val).symm

end PaperVerification.Segre.TwistingSections
end
end
end GeometryLiteralSource037

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: PaperVerification.SegreTwistingRestrictions"

section GeometryLiteralSource038
/- Original source: PaperVerification.SegreCechCoordinates -/


/-!
# Full Laurent coefficient coordinates on all Čech terms

The whole degree component of every coordinate localization is identified
with its allowed Laurent coefficients. The finite product over chart tuples
commutes with finite-support Laurent coefficients. These equivalences retain
all monomials and all chart tuples, including repeated indices.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PaperVerification.Segre.CoordinateLocalization

open CechMonomials
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

/-- Laurent exponents of fixed degree allowed on a coordinate intersection. -/
def allowedDegreeExponents (S : Finset I) (t : ℤ) : Set (DegreeExponent I t) :=
  {a | ∀ i, i ∉ S → 0≤a.val i}

abbrev coefficientSpace (S : Finset I) (t : ℤ) :
    Submodule K (DegreeExponent I t →₀ K) :=
  Finsupp.supported K K (allowedDegreeExponents S t)

/-- Exchanging the order of the degree and denominator conditions. -/
def allowedDegreeEquiv (S : Finset I) (t : ℤ) :
    {a : allowedExponents S // totalDegree S a=t} ≃ allowedDegreeExponents S t where
  toFun a := ⟨⟨a.val.val,a.property⟩,a.val.property⟩
  invFun a := ⟨⟨a.val.val,a.property⟩,a.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Passing to coefficients preserves exactly the entire homogeneous submodule. -/
def homogeneousCoefficients (S : Finset I) (t : ℤ) :
    localDegree (K := K) S t ≃ₗ[K]
      Finsupp.supported K K {a : allowedExponents S | totalDegree S a=t} where
  toFun z := ⟨z.val.coeff,z.property⟩
  invFun z := ⟨AddMonoidAlgebra.ofCoeff z.val,z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every Laurent coefficient on the intersection, with no truncation. -/
def localCoefficientEquiv (S : Finset I) (t : ℤ) :
    localDegree (K := K) S t ≃ₗ[K] coefficientSpace (K := K) S t :=
  (homogeneousCoefficients (K := K) S t).trans
    ((Finsupp.supportedEquivFinsupp (R := K) {a : allowedExponents S | totalDegree S a=t}).trans
      ((Finsupp.domLCongr (allowedDegreeEquiv S t)).trans
        (Finsupp.supportedEquivFinsupp (R := K) (allowedDegreeExponents S t)).symm))

/-- The equivalence reads the literal coefficient whenever the exponent is allowed. -/
theorem localCoefficientEquiv_apply (S : Finset I) (t : ℤ)
    (z : localDegree (K := K) S t) (a : DegreeExponent I t)
    (ha : a ∈ allowedDegreeExponents S t) :
    (localCoefficientEquiv S t z).val a=z.val.coeff ⟨a.val,ha⟩ := by
  classical
  simp [localCoefficientEquiv,homogeneousCoefficients,allowedDegreeEquiv,
    Finsupp.supportedEquivFinsupp_symm_apply_coe,Finsupp.extendDomain_apply,ha]; rfl

theorem localCoefficientEquiv_apply_of_not_allowed (S : Finset I) (t : ℤ)
    (z : localDegree (K := K) S t) (a : DegreeExponent I t)
    (ha : a ∉ allowedDegreeExponents S t) : (localCoefficientEquiv S t z).val a=0 :=
  ((Finsupp.mem_supported' K _).mp (localCoefficientEquiv S t z).property) a ha

/-- The coefficient inclusion on a smaller chart is literally extension by zero. -/
def coefficientRestriction {S T : Finset I} (h : S ⊆ T) (t : ℤ) :
    coefficientSpace (K := K) S t →ₗ[K] coefficientSpace (K := K) T t :=
  Submodule.inclusion (Finsupp.supported_mono (fun a ha i hi => ha i (fun hs => hi (h hs))))

@[simp] theorem coefficientRestriction_apply {S T : Finset I} (h : S ⊆ T) (t : ℤ)
    (z : coefficientSpace (K := K) S t) (a : DegreeExponent I t) :
    (coefficientRestriction h t z).val a = z.val a := rfl

/-- Actual coordinate restriction leaves every Laurent coefficient unchanged. -/
theorem localCoefficientEquiv_restriction {S T : Finset I} (h : S ⊆ T) (t : ℤ)
    (z : localDegree (K := K) S t) :
    localCoefficientEquiv T t (degreeRestriction h t z)=
      coefficientRestriction h t (localCoefficientEquiv S t z) := by
  classical
  apply Subtype.ext
  ext a
  by_cases ha : a ∈ allowedDegreeExponents S t
  · have haT : a ∈ allowedDegreeExponents T t := fun i hi => ha i (fun hs => hi (h hs))
    rw [localCoefficientEquiv_apply T t _ a haT]
    change (localRestriction h z.val).coeff ⟨a.val,haT⟩=
      (localCoefficientEquiv S t z).val a
    rw [localCoefficientEquiv_apply S t z a ha]
    exact localRestriction_coeff h z.val ⟨a.val,ha⟩
  · rw [show (coefficientRestriction h t (localCoefficientEquiv S t z)).val a=0 from
      localCoefficientEquiv_apply_of_not_allowed S t z a ha]
    by_cases haT : a ∈ allowedDegreeExponents T t
    · rw [localCoefficientEquiv_apply T t _ a haT]
      change Finsupp.mapDomain (exponentInclusion h) z.val.coeff ⟨a.val,haT⟩=0
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨b,hb⟩
      apply ha
      have hv : b.val=a.val := congrArg Subtype.val hb
      change ∀ i, i ∉ S → 0 ≤ a.val i
      have hb : ∀ i, i ∉ S → 0 ≤ b.val i := b.property
      simpa only [hv] using hb
    · exact localCoefficientEquiv_apply_of_not_allowed T t _ a haT

end PaperVerification.Segre.CoordinateLocalization

namespace PaperVerification.Segre.CechMonomials

open CoordinateLocalization
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

/-- All distinct chart indices appearing in a tuple. -/
def tupleCoordinates {q : ℕ} (a : Fin q → I) : Finset I := Finset.univ.image a

@[simp] theorem mem_tupleCoordinates {q : ℕ} (a : Fin q → I) (i : I) :
    i ∈ tupleCoordinates a ↔ i ∈ Set.range a := by
  simp [tupleCoordinates,Set.mem_range]

theorem tupleCoordinates_nonempty {q : ℕ} (a : Fin (q+1) → I) :
    (tupleCoordinates a).Nonempty := ⟨a 0,by simp⟩

theorem allowedDegreeExponents_iff {q : ℕ} (t : ℤ) (a : Fin q → I)
    (v : DegreeExponent I t) :
    v ∈ allowedDegreeExponents (tupleCoordinates a) t ↔ negativeSupport v.val ⊆ Set.range a := by
  constructor
  · intro h i hi
    by_contra hn
    exact (not_lt_of_ge (h i (by simpa using hn))) hi
  · intro h i hi
    by_contra hn
    exact hi ((mem_tupleCoordinates a i).mpr (h (lt_of_not_ge hn)))

section FiniteExchange

variable {A B : Type*} [Fintype B]

/-- Finite products commute with arbitrary finite-support coefficient expansions. -/
def finitePiExchange : (A →₀ B → K) ≃ₗ[K] B → A →₀ K where
  toFun f b := Finsupp.mapRange (fun g : B → K => g b) rfl f
  invFun f := by
    classical
    exact Finsupp.onFinset (Finset.univ.biUnion (fun b => (f b).support))
      (fun a b => f b a) (by
        intro a ha
        by_contra hn
        apply ha
        funext b
        have hb : a ∉ (f b).support := by
          intro hm
          exact hn (Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ b,hm⟩)
        exact Finsupp.notMem_support_iff.mp hb)
  left_inv f := by ext a b; rfl
  right_inv f := by ext b a; rfl
  map_add' f g := by ext b a; rfl
  map_smul' c f := by ext b a; rfl

@[simp] theorem finitePiExchange_apply (f : A →₀ B → K) (b : B) (a : A) :
    (finitePiExchange (K := K) (A := A) (B := B)) f b a=f a b := rfl

@[simp] theorem finitePiExchange_symm_apply (f : B → A →₀ K) (a : A) (b : B) :
    (finitePiExchange (K := K) (A := A) (B := B)).symm f a b=f b a := rfl

end FiniteExchange

/-- The Laurent support condition is exactly the allowed denominator condition on each tuple. -/
def laurentCoefficientEquiv (t : ℤ) (q : ℕ) :
    laurentCochains (I := I) (K := K) t q ≃ₗ[K]
      ((a : Fin q → I) → coefficientSpace (K := K) (tupleCoordinates a) t) where
  toFun f a := ⟨(finitePiExchange (K := K) (A := DegreeExponent I t) (B := Fin q → I)) f.val a,by
    intro v hv
    rw [allowedDegreeExponents_iff]
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hv) (f.property v a hn)⟩
  invFun f := ⟨(finitePiExchange (K := K) (A := DegreeExponent I t) (B := Fin q → I)).symm (fun a => (f a).val),by
    intro v a hn
    apply ((Finsupp.mem_supported' K _).mp (f a).property) v
    rwa [allowedDegreeExponents_iff]⟩
  left_inv f := by apply Subtype.ext; ext v a; rfl
  right_inv f := by funext a; apply Subtype.ext; ext v; rfl
  map_add' f g := by funext a; apply Subtype.ext; ext v; rfl
  map_smul' c f := by funext a; apply Subtype.ext; ext v; rfl

@[simp] theorem laurentCoefficientEquiv_apply (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := I) (K := K) t q) (a : Fin q → I)
    (v : DegreeExponent I t) :
    (laurentCoefficientEquiv t q f a).val v=f.val v a := rfl

/-- The whole tuple product of homogeneous localization components is the Laurent Čech term. -/
def laurentLocalEquiv (t : ℤ) (q : ℕ) :
    laurentCochains (I := I) (K := K) t q ≃ₗ[K]
      ((a : Fin q → I) → localDegree (K := K) (tupleCoordinates a) t) :=
  (laurentCoefficientEquiv t q).trans
    (LinearEquiv.piCongrRight (fun a => (localCoefficientEquiv (tupleCoordinates a) t).symm))

theorem laurentLocalEquiv_coeff (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := I) (K := K) t q) (a : Fin q → I)
    (v : DegreeExponent I t) :
    (localCoefficientEquiv (tupleCoordinates a) t (laurentLocalEquiv t q f a)).val v=f.val v a := by
  simp only [laurentLocalEquiv,LinearEquiv.trans_apply,LinearEquiv.piCongrRight_apply,
    LinearEquiv.apply_symm_apply,laurentCoefficientEquiv_apply]

end PaperVerification.Segre.CechMonomials
end
end
end GeometryLiteralSource038

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: PaperVerification.SegreCechCoordinates"

section GeometryLiteralSource039
/- Original source: PaperVerification.SegreTwistingCechExact -/


/-!
# Exactness for the actual twisting-sheaf section tuples

The Laurent contraction is transported through the full, restriction-natural
section equivalence. The resulting differential is the actual alternating
sum of sheaf restrictions. Exactness therefore concerns all actual sections
on all coordinate intersections, rather than a formally declared model.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.CechMonomials

open CoordinateLocalization
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

theorem tupleCoordinates_delete_subset {q : ℕ} (a : Fin (q+1) → I) (j : Fin (q+1)) :
    tupleCoordinates (a ∘ j.succAbove) ⊆ tupleCoordinates a := by
  intro i hi
  rw [mem_tupleCoordinates] at hi ⊢
  obtain ⟨r,hr⟩ := hi
  exact ⟨j.succAbove r,hr⟩

/-- The coefficient differential agrees with the alternating sum of localization restrictions. -/
theorem laurentLocalEquiv_differential (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := I) (K := K) t q) (a : Fin (q+1) → I) :
    laurentLocalEquiv t (q+1)
        ⟨laurentDifferential (I := I) (K := K) t q f.val,laurentDifferential_mem f.property⟩ a =
      ∑ j : Fin (q+1), (-1 : ℤ)^j.val •
        degreeRestriction (tupleCoordinates_delete_subset a j) t
          (laurentLocalEquiv t q f (a ∘ j.succAbove)) := by
  apply (localCoefficientEquiv (tupleCoordinates a) t).injective
  apply Subtype.ext
  ext v
  simp only [map_sum,map_zsmul,localCoefficientEquiv_restriction,
    Submodule.coe_sum,Submodule.coe_smul_of_tower,
    Finset.sum_apply',Finsupp.smul_apply,coefficientRestriction_apply,
    laurentLocalEquiv_coeff,laurentDifferential_apply]
  change differential q (f.val v) a =
    ∑ j : Fin (q+1), (-1 : ℤ)^j.val • f.val v (a ∘ j.succAbove)
  simp only [differential_apply,zsmul_eq_mul,Int.cast_pow,Int.cast_neg,Int.cast_one]

end PaperVerification.Segre.CechMonomials

namespace PaperVerification.Segre.TwistingSections

open CoordinateLocalization CechMonomials AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K

/-- The full tuple group of actual sections on coordinate intersections. -/
abbrev SectionCochain (t : ℤ) (q : ℕ) :=
  (a : Fin (q+1) → I) → Γ(Proj.twistingSheaf 𝒜 t,chartIntersection (tupleCoordinates a))

/-- The complete, canonical term equivalence to actual sheaf sections. -/
def sectionCochainEquiv (t : ℤ) (q : ℕ) :
    laurentCochains (I := I) (K := K) t (q+1) ≃+ SectionCochain (I := I) (K := K) t q :=
  (laurentLocalEquiv t (q+1)).toAddEquiv.trans
    (AddEquiv.piCongrRight (fun a =>
      sectionsEquiv (tupleCoordinates a) (tupleCoordinates_nonempty a) t))

@[simp] theorem sectionCochainEquiv_apply (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := I) (K := K) t (q+1)) (a : Fin (q+1) → I) :
    sectionCochainEquiv t q f a =
      sectionsEquiv (tupleCoordinates a) (tupleCoordinates_nonempty a) t
        (laurentLocalEquiv t (q+1) f a) := rfl

/-- The literal alternating sum of the actual sheaf restriction maps. -/
def sectionDifferential (t : ℤ) (q : ℕ) :
    SectionCochain (I := I) (K := K) t q →+
      SectionCochain (I := I) (K := K) t (q+1) where
  toFun f a := ∑ j : Fin (q+2), (-1 : ℤ)^j.val •
    (Proj.twistingSheaf 𝒜 t).presheaf.map
      (homOfLE (chartIntersection_antitone (tupleCoordinates_delete_subset a j))).op
      (f (a ∘ j.succAbove))
  map_zero' := by funext a; simp
  map_add' f g := by funext a; simp only [Pi.add_apply,map_add,zsmul_add,Finset.sum_add_distrib]

@[simp] theorem sectionDifferential_apply (t : ℤ) (q : ℕ)
    (f : SectionCochain (I := I) (K := K) t q) (a : Fin (q+2) → I) :
    sectionDifferential t q f a = ∑ j : Fin (q+2), (-1 : ℤ)^j.val •
      (Proj.twistingSheaf 𝒜 t).presheaf.map
        (homOfLE (chartIntersection_antitone (tupleCoordinates_delete_subset a j))).op
        (f (a ∘ j.succAbove)) := rfl

/-- The full section equivalences intertwine the literal two differentials. -/
theorem sectionCochainEquiv_differential (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := I) (K := K) t (q+1)) :
    sectionCochainEquiv t (q+1)
        ⟨laurentDifferential (I := I) (K := K) t (q+1) f.val,laurentDifferential_mem f.property⟩ =
      sectionDifferential t q (sectionCochainEquiv t q f) := by
  funext a
  rw [sectionCochainEquiv_apply,laurentLocalEquiv_differential]
  simp only [map_sum,map_zsmul,sectionDifferential_apply,sectionCochainEquiv_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z => (-1 : ℤ)^j.val • z)
    (sectionsEquiv_restriction (tupleCoordinates_delete_subset a j)
      (tupleCoordinates_nonempty (a ∘ j.succAbove)) (tupleCoordinates_nonempty a) t
      (laurentLocalEquiv t (q+1) f (a ∘ j.succAbove))).symm

theorem sectionDifferential_squared (t : ℤ) (q : ℕ)
    (f : SectionCochain (I := I) (K := K) t q) :
    sectionDifferential t (q+1) (sectionDifferential t q f)=0 := by
  obtain ⟨g,rfl⟩ := (sectionCochainEquiv t q).surjective f
  rw [← sectionCochainEquiv_differential,← sectionCochainEquiv_differential]
  have hz : (⟨laurentDifferential (I := I) (K := K) t (q+2) (laurentDifferential (I := I) (K := K) t (q+1) g.val),
      laurentDifferential_mem (laurentDifferential_mem g.property)⟩ :
      laurentCochains (I := I) (K := K) t (q+3))=0 :=
    Subtype.ext (laurentDifferential_squared t (q+1) g.val)
  rw [hz,map_zero]

/-- Every actual positive-degree cocycle below projective dimension is a boundary. -/
theorem section_exact_below_dimension (t : ℤ) (q : ℕ) (hq : q+2<Fintype.card I)
    (f : SectionCochain (I := I) (K := K) t (q+1))
    (hc : sectionDifferential t (q+1) f=0) :
    ∃ g : SectionCochain (I := I) (K := K) t q, sectionDifferential t q g=f := by
  obtain ⟨v,rfl⟩ := (sectionCochainEquiv t (q+1)).surjective f
  have hv : laurentDifferential (I := I) (K := K) t (q+2) v.val=0 := by
    have he : (⟨laurentDifferential (I := I) (K := K) t (q+2) v.val,laurentDifferential_mem v.property⟩ :
        laurentCochains (I := I) (K := K) t (q+3))=0 := by
      apply (sectionCochainEquiv t (q+2)).injective
      simpa only [sectionCochainEquiv_differential,map_zero] using hc
    exact congrArg Subtype.val he
  obtain ⟨w,hw,hd⟩ := laurent_exact_below_dimension t (q+1) hq v.val v.property hv
  refine ⟨sectionCochainEquiv t q ⟨w,hw⟩,?_⟩
  rw [← sectionCochainEquiv_differential]
  exact congrArg (sectionCochainEquiv t (q+1)) (Subtype.ext hd)

/-- Every actual positive-degree cocycle vanishes for twists at least `-N` on `P^N`. -/
theorem section_exact_of_twist (t : ℤ) (ht : -(Fintype.card I : ℤ)<t) (q : ℕ)
    (f : SectionCochain (I := I) (K := K) t (q+1))
    (hc : sectionDifferential t (q+1) f=0) :
    ∃ g : SectionCochain (I := I) (K := K) t q, sectionDifferential t q g=f := by
  obtain ⟨v,rfl⟩ := (sectionCochainEquiv t (q+1)).surjective f
  have hv : laurentDifferential (I := I) (K := K) t (q+2) v.val=0 := by
    have he : (⟨laurentDifferential (I := I) (K := K) t (q+2) v.val,laurentDifferential_mem v.property⟩ :
        laurentCochains (I := I) (K := K) t (q+3))=0 := by
      apply (sectionCochainEquiv t (q+2)).injective
      simpa only [sectionCochainEquiv_differential,map_zero] using hc
    exact congrArg Subtype.val he
  obtain ⟨w,hw,hd⟩ := laurent_exact_of_twist t ht (q+1) v.val v.property hv
  refine ⟨sectionCochainEquiv t q ⟨w,hw⟩,?_⟩
  rw [← sectionCochainEquiv_differential]
  exact congrArg (sectionCochainEquiv t (q+1)) (Subtype.ext hd)

/-- Actual compatible chart sections of negative twist are zero. -/
theorem section_global_cocycle_eq_zero (hI : 1<Fintype.card I) (t : ℤ) (ht : t<0)
    (f : SectionCochain (I := I) (K := K) t 0) (hc : sectionDifferential t 0 f=0) : f=0 := by
  obtain ⟨v,rfl⟩ := (sectionCochainEquiv t 0).surjective f
  have hv : laurentDifferential (I := I) (K := K) t 1 v.val=0 := by
    have he : (⟨laurentDifferential (I := I) (K := K) t 1 v.val,laurentDifferential_mem v.property⟩ :
        laurentCochains (I := I) (K := K) t 2)=0 := by
      apply (sectionCochainEquiv t 1).injective
      simpa only [sectionCochainEquiv_differential,map_zero] using hc
    exact congrArg Subtype.val he
  have hz := laurent_global_cocycle_eq_zero hI t ht v.val v.property hv
  rw [show v=0 from Subtype.ext hz,map_zero]

end PaperVerification.Segre.TwistingSections
end
end
end GeometryLiteralSource039

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: PaperVerification.SegreTwistingCechExact"

section GeometryLiteralSource040
/- Original source: TauCeti.Topology.Sheaves.Cartan -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Cartan's criterion: Čech acyclicity on a basis implies cohomological acyclicity

Let `X` be a topological space and `B` a set of opens of `X` which is closed under binary
intersections, consists of quasi-compact opens, and is a basis of the topology inside each of its
members. Let `F` be a sheaf of abelian groups on `X` which is Čech acyclic for the finite covers of
members of `B` by members of `B`: for every finite nonempty family `U i` in `B` and every `Y ∈ B`
contained in their union, the augmented Čech complex of `V ↦ F(Y ∩ V)` for `U`, that is, of the
cover of `Y` by the opens `Y ∩ U i`, is exact (`TauCeti.Topology.IsCechAcyclicOn`). Then `F` has
no cohomology in positive degrees on the members of `B`
(`TauCeti.Topology.subsingleton_H'_succ_of_isCechAcyclicOn`).

This is how the vanishing of the higher cohomology of a quasi-coherent sheaf on an affine scheme is
deduced from the exactness of the Čech complexes of standard covers, with `B` the basic opens.

The proof is by dimension shifting along the chosen embedding `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` of `F` into an
injective sheaf, which is flasque, so that its Čech complexes are exact for all finite covers
(`TopCat.Sheaf.quasiIso_cechAugmentation_prod_of_isFlasque`).

* On every `Y ∈ B`, the map `I(Y) ⟶ Q(Y)` is onto. A section `s` of `Q` over `Y` lifts locally,
  hence, `Y` being quasi-compact, on a finite cover of `Y` by members of `B`. The image presheaf
  `G` of `I ⟶ Q` sits in a sequence `0 ⟶ F ⟶ I ⟶ G ⟶ 0` of presheaves which is exact on every
  open, so the Čech complexes of the cover form a short exact sequence, and `G` is Čech acyclic
  for the cover because `F` and `I` are (`quasiIso_cechAugmentation_X₃_of_shortExact`). In degree
  `0` this is the sheaf condition for `G`, so the local lifts of `s` glue to a section of `G`
  over `Y`, which comes from `I(Y)` and maps to `s`.
* Hence `H¹(Y, F) = 0` for `Y ∈ B`, and the sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` is exact on the
  members of `B`, which are closed under finite intersections. Its Čech complexes for covers by
  members of `B` are then short exact, so `Q` is Čech acyclic on `B` as well.
* Finally `Hⁿ⁺²(Y, F) ≅ Hⁿ⁺¹(Y, Q)`, and induction on the degree, for all sheaves at once,
  concludes.

## Main definitions

* `TauCeti.Topology.IsCechAcyclicOn B F`: `F` is Čech acyclic for the finite covers of members of
  `B` by members of `B`.

## Main results

* `TauCeti.Topology.subsingleton_H'_succ_of_isCechAcyclicOn`: Cartan's criterion, `Hⁿ⁺¹(Y, F) = 0`
  for every member `Y` of `B`.
* `TauCeti.Topology.prod_pi_mem_of_inf_mem`: a set of opens closed under binary intersections
  contains the finite intersections `Y ∩ U (a 0) ∩ ⋯ ∩ U (a n)` of its members.
* `TopCat.Sheaf.exists_mem_lift_of_epi`: along an epimorphism of sheaves, sections lift locally on
  the members of a set of opens which contains a basis inside each of its members.

## References

* The Stacks Project, Lemma 20.11.9 (Cartan's criterion), whose proof is followed here, and
  Lemma 30.2.2 (tag 01XB), where it is applied to the standard opens of an affine scheme.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TauCeti.CategoryTheory

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}}

/-- A sheaf `F` of abelian groups on `X` is *Čech acyclic on* a set `B` of opens if for every
finite nonempty family `U i` of members of `B` and every member `Y` of `B` contained in their union,
the augmented Čech complex `0 ⟶ F(Y) ⟶ Č⁰(U, F(Y ∩ -)) ⟶ Č¹(U, F(Y ∩ -)) ⟶ ⋯` of the cover of `Y`
by the opens `Y ∩ U i` is exact. -/
def IsCechAcyclicOn (B : Set (Opens X))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Prop :=
  ∀ ⦃ι : Type u⦄ [Finite ι] [Nonempty ι] (U : ι → Opens X) (Y : Opens X), Y ∈ B →
    (∀ i, U i ∈ B) → Y ≤ ⨆ i, U i →
      QuasiIso (cechAugmentation U isTerminalTop ((prod.functor.obj Y).op ⋙ F.obj))

variable {B : Set (Opens X)}

/-- Unfolding `IsCechAcyclicOn`: Čech acyclicity on `B` is the exactness of the augmented Čech
complexes of the finite covers of members of `B` by members of `B`. -/
theorem isCechAcyclicOn_iff {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} :
    IsCechAcyclicOn B F ↔
      ∀ ⦃ι : Type u⦄ [Finite ι] [Nonempty ι] (U : ι → Opens X) (Y : Opens X), Y ∈ B →
        (∀ i, U i ∈ B) → Y ≤ ⨆ i, U i →
          QuasiIso (cechAugmentation U isTerminalTop ((prod.functor.obj Y).op ⋙ F.obj)) :=
  Iff.rfl

/-- Let `B` be a set of opens containing, inside each of its members, a basis of the topology of
that member. Along an epimorphism of sheaves `π : F ⟶ G`, a section of `G` over a member `Y` of `B`
lifts, near every point of `Y`, on a member of `B` contained in `Y`. -/
theorem _root_.TopCat.Sheaf.exists_mem_lift_of_epi
    (hbasis : ∀ U ∈ B, ∀ V : Opens X, V ≤ U → ∀ x ∈ V, ∃ W ∈ B, x ∈ W ∧ W ≤ V)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (π : F ⟶ G) [Epi π]
    {Y : Opens X} (hY : Y ∈ B) (s : G.obj.obj (op Y)) (x : X) (hx : x ∈ Y) :
    ∃ V ∈ B, x ∈ V ∧ ∃ h : V ≤ Y, ∃ t : F.obj.obj (op V),
      π.hom.app (op V) t = G.obj.map (homOfLE h).op s := by
  have : Sheaf.IsLocallySurjective π := (Sheaf.isLocallySurjective_iff_epi' _ π).2 inferInstance
  obtain ⟨V, f, ⟨t, ht⟩, hxV⟩ :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology X) π.hom s x hx
  obtain ⟨W, hW, hxW, hWV⟩ := hbasis Y hY V f.le x hxV
  refine ⟨W, hW, hxW, hWV.trans f.le, F.obj.map (homOfLE hWV).op t, ?_⟩
  rw [← ConcreteCategory.comp_apply, π.hom.naturality, ConcreteCategory.comp_apply, ht,
    ← ConcreteCategory.comp_apply, ← G.obj.map_comp]
  rfl

variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The sequence of presheaves `0 ⟶ F ⟶ I ⟶ G ⟶ 0`, where `F ⟶ I` is the chosen embedding into an
injective sheaf and `G` is the image presheaf of `I ⟶ Q`, for `Q` its cokernel sheaf. -/
private abbrev imageSeq : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk (Injective.ι F).hom (factorThruImage (cokernel.π (Injective.ι F)).hom) (by
    rw [← cancel_mono (image.ι _), Category.assoc, image.fac, zero_comp]
    exact ((injectiveCokernelSequence F).map (sheafToPresheaf _ AddCommGrpCat.{u})).zero)

/-- The sequence `0 ⟶ F ⟶ I ⟶ G ⟶ 0` is exact on every open: the kernel of `I(V) ⟶ Q(V)` is
`F(V)`, and `G(V)` is the image of `I(V)` in `Q(V)`. -/
private lemma imageSeq_shortExact (V : (Opens X)ᵒᵖ) :
    ((imageSeq F).map ((evaluation _ AddCommGrpCat.{u}).obj V)).ShortExact := by
  have hE := (injectiveCokernelSequence_shortExact F).exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ AddCommGrpCat.{u} ⋙ (evaluation _ AddCommGrpCat.{u}).obj V)
    inferInstance inferInstance
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff] at hE ⊢
    intro x hx
    apply hE x
    dsimp at hx ⊢
    have h := congrArg ((image.ι (cokernel.π (Injective.ι F)).hom).app V) hx
    rwa [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, image.fac, map_zero] at h
  · exact Functor.map_mono (sheafToPresheaf _ AddCommGrpCat.{u} ⋙
      (evaluation _ AddCommGrpCat.{u}).obj V) (Injective.ι F)
  · dsimp
    infer_instance

variable {F}

/-- For `F` Čech acyclic on `B`, the image presheaf of `I ⟶ Q` is Čech acyclic for the finite
covers of members of `B` by members of `B`, like `F` and the flasque sheaf `I`. -/
private lemma quasiIso_cechAugmentation_image (hF : IsCechAcyclicOn B F) {ι : Type u} [Finite ι]
    [Nonempty ι] (U : ι → Opens X) {Y : Opens X} (hY : Y ∈ B) (hU : ∀ i, U i ∈ B)
    (hYU : Y ≤ ⨆ i, U i) :
    QuasiIso (cechAugmentation U isTerminalTop
      ((prod.functor.obj Y).op ⋙ Limits.image (cokernel.π (Injective.ι F)).hom)) := by
  have : TopCat.Presheaf.IsFlasque (TopCat.Sheaf.presheaf (Injective.under F)) :=
    isFlasque_of_injective (Injective.under F)
  exact quasiIso_cechAugmentation_X₃_of_shortExact U isTerminalTop
    ((imageSeq F).map ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
      (prod.functor.obj Y).op))
    (imageSeq_shortExact F _) (fun _ _ ↦ imageSeq_shortExact F _) (hF U Y hY hU hYU)
    (TopCat.Sheaf.quasiIso_cechAugmentation_prod_of_isFlasque (Injective.under F) U Y hYU)

/-- Let `π : F₂ ⟶ F₃` be a morphism of sheaves, `G` its image presheaf, and `U i` opens covering
`Y`. If `G` satisfies the sheaf condition for this cover, in the form of the exactness of its
augmented Čech complex in degree `0`, then sections `x i` of `G` over the opens `Y ⨯ U i`, whose
images in `F₃` are restrictions of a single section `s` of `F₃` over `Y`, glue to a section of `G`
over `Y ⨯ ⊤`. -/
private lemma exists_map_eq_of_cover
    {F₂ F₃ : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (π : F₂ ⟶ F₃) {ι : Type u}
    (U : ι → Opens X) {Y : Opens X}
    (hG : QuasiIso (cechAugmentation U isTerminalTop
      ((prod.functor.obj Y).op ⋙ Limits.image π.hom)))
    (s : F₃.obj.obj (op Y)) (x : ∀ i, (Limits.image π.hom).obj (op (Y ⨯ U i)))
    (hx : ∀ i {V : Opens X} (e : V ⟶ Y ⨯ U i),
      (image.ι π.hom).app (op V) ((Limits.image π.hom).map e.op (x i)) =
        F₃.obj.map (e ≫ prod.fst).op s) :
    ∃ g : (Limits.image π.hom).obj (op (Y ⨯ ⊤)), ∀ i (r : Y ⨯ U i ⟶ Y ⨯ ⊤),
      (Limits.image π.hom).map r.op g = x i := by
  have hι (V : (Opens X)ᵒᵖ) : Function.Injective ((image.ι π.hom).app V) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have h := (Presieve.isSheafFor_comp_forget_addCommGrpCat_iff _ _).2
    ((quasiIsoAt_cechAugmentation_zero_iff U isTerminalTop _).1 (hG.quasiIsoAt 0))
  have hπ : (fun i ↦ isTerminalTop.from (U i)) = fun i ↦ homOfLE le_top :=
    funext fun _ ↦ Subsingleton.elim _ _
  rw [hπ, Presieve.isSheafFor_arrows_iff] at h
  obtain ⟨g, hg, -⟩ := h x ((Presieve.Arrows.compatible_homOfLE_iff
    (P := ((prod.functor.obj Y).op ⋙ Limits.image π.hom) ⋙ forget AddCommGrpCat)
    (fun _ ↦ le_top) x).2
    fun i j ↦ hι _ ((hx i ((prod.functor.obj Y).map (homOfLE inf_le_left))).trans
      (Eq.trans (congrArg (fun f ↦ F₃.obj.map (Quiver.Hom.op f) s) (Subsingleton.elim _ _))
        (hx j ((prod.functor.obj Y).map (homOfLE inf_le_right))).symm)))
  -- `hg i` is stated for the presheaf `(prod.functor.obj Y).op ⋙ G`, whose maps are those of `G`
  exact ⟨g, fun i r ↦ (congrArg (fun f ↦ (Limits.image π.hom).map (Quiver.Hom.op f) g)
    (Subsingleton.elim r ((prod.functor.obj Y).map (homOfLE le_top)))).trans (hg i)⟩

/-- Let `π : F₂ ⟶ F₃` be a morphism of sheaves, and let `U i` be opens covering `Y`. If the image
presheaf of `π` satisfies the sheaf condition for this cover, in the form of the exactness of its
augmented Čech complex in degree `0`, then a section of `F₃` over `Y` whose restrictions to the
`U i` lift to `F₂` lifts to `F₂` itself. -/
private lemma exists_eq_of_cover {F₂ F₃ : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (π : F₂ ⟶ F₃) {ι : Type u} (U : ι → Opens X) {Y : Opens X}
    (hUY : ∀ i, U i ≤ Y) (hYU : Y ≤ ⨆ i, U i)
    (hG : QuasiIso (cechAugmentation U isTerminalTop
      ((prod.functor.obj Y).op ⋙ Limits.image π.hom)))
    (s : F₃.obj.obj (op Y)) (t : ∀ i, F₂.obj.obj (op (U i)))
    (ht : ∀ i, π.hom.app (op (U i)) (t i) = F₃.obj.map (homOfLE (hUY i)).op s) :
    ∃ t' : F₂.obj.obj (op Y), π.hom.app (op Y) t' = s := by
  have hfac (V : (Opens X)ᵒᵖ) (y : F₂.obj.obj V) :
      (image.ι π.hom).app V ((factorThruImage π.hom).app V y) = π.hom.app V y := by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, image.fac]
  -- the lifts `t i`, restricted to `Y ⨯ U i`, as sections of the image presheaf
  let x (i : ι) : (Limits.image π.hom).obj (op (Y ⨯ U i)) :=
    (factorThruImage π.hom).app (op (Y ⨯ U i)) (F₂.obj.map (prod.snd : Y ⨯ U i ⟶ U i).op (t i))
  have hx (i : ι) {V : Opens X} (e : V ⟶ Y ⨯ U i) :
      (image.ι π.hom).app (op V) ((Limits.image π.hom).map e.op (x i)) =
        F₃.obj.map (e ≫ prod.fst).op s := by
    rw [NatTrans.naturality_apply]
    dsimp only [x]
    rw [hfac, NatTrans.naturality_apply, ht, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
    exact congrArg (fun f ↦ F₃.obj.map (Quiver.Hom.op f) s) (Subsingleton.elim _ _)
  obtain ⟨g, hg⟩ := exists_map_eq_of_cover π U hG s x hx
  obtain ⟨t', rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).1
    (inferInstance : Epi ((factorThruImage π.hom).app (op (Y ⨯ ⊤)))) g
  refine ⟨F₂.obj.map (prod.lift (𝟙 Y) (isTerminalTop.from Y)).op t', ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' F₃ U Y (fun i ↦ homOfLE (hUY i)) hYU _ _ fun i ↦ ?_
  let e : U i ⟶ Y ⨯ U i := prod.lift (homOfLE (hUY i)) (𝟙 _)
  let r : Y ⨯ U i ⟶ Y ⨯ ⊤ := prod.map (𝟙 Y) (isTerminalTop.from (U i))
  calc F₃.obj.map (homOfLE (hUY i)).op (π.hom.app (op Y)
          (F₂.obj.map (prod.lift (𝟙 Y) (isTerminalTop.from Y)).op t'))
      _ = π.hom.app (op (U i)) (F₂.obj.map (e ≫ r).op t') := by
        rw [← NatTrans.naturality_apply π.hom, ← Functor.map_comp_apply, ← op_comp]
        exact congrArg (fun f ↦ π.hom.app _ (F₂.obj.map (Quiver.Hom.op f) t'))
          (Subsingleton.elim _ _)
      _ = (image.ι π.hom).app (op (U i)) ((Limits.image π.hom).map e.op
          ((Limits.image π.hom).map r.op ((factorThruImage π.hom).app (op (Y ⨯ ⊤)) t'))) := by
        rw [← NatTrans.naturality_apply (factorThruImage π.hom),
          ← NatTrans.naturality_apply (factorThruImage π.hom), hfac, op_comp,
          Functor.map_comp_apply]
      _ = F₃.obj.map (homOfLE (hUY i)).op s := by
        rw [hg i r, hx i e]
        exact congrArg (fun f ↦ F₃.obj.map (Quiver.Hom.op f) s) (Subsingleton.elim _ _)

section

variable (hinf : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V ∈ B) (hcpt : ∀ U ∈ B, IsCompact (U : Set X))
  (hbasis : ∀ U ∈ B, ∀ V : Opens X, V ≤ U → ∀ x ∈ V, ∃ W ∈ B, x ∈ W ∧ W ≤ V)

include hinf in
/-- A set of opens closed under binary intersections contains the intersection of a member with
finitely many members. -/
private lemma inf_finsetInf_mem {ι : Type u} {U : ι → Opens X} (hU : ∀ i, U i ∈ B) {Y : Opens X}
    (hY : Y ∈ B) (s : Finset ι) : Y ⊓ s.inf U ∈ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hY
  | insert a s _ ih =>
    rw [Finset.inf_insert, inf_left_comm]
    exact hinf _ (hU a) _ ih

include hinf in
/-- If a set `B` of opens is closed under binary intersections, then the product of a member `Y`
with finitely many members `U (a 0), …, U (a n)`, which in the poset of opens is their
intersection, is again a member. -/
theorem prod_pi_mem_of_inf_mem {ι : Type u} {U : ι → Opens X} (hU : ∀ i, U i ∈ B) {Y : Opens X}
    (hY : Y ∈ B) (n : ℕ) (a : Fin (n + 1) → ι) : (Y ⨯ ∏ᶜ fun j ↦ U (a j)) ∈ B := by
  classical
  rw [CompleteLattice.prod_eq_inf, CompleteLattice.finite_product_eq_finset_image_inf]
  exact inf_finsetInf_mem hinf hU hY _

include hcpt hbasis in
/-- For `F` Čech acyclic on `B`, sections of the cokernel `Q` of the chosen embedding `F ⟶ I` into
an injective sheaf lift to `I` over every member of `B`. -/
private lemma surjective_app_cokernel_π (hF : IsCechAcyclicOn B F) {Y : Opens X} (hY : Y ∈ B) :
    Function.Surjective ((cokernel.π (Injective.ι F)).hom.app (op Y)) := by
  intro s
  choose V hVB hxV hVY t ht using fun x : Y ↦
    TopCat.Sheaf.exists_mem_lift_of_epi hbasis (cokernel.π (Injective.ι F)) hY s x.1 x.2
  obtain ⟨c, hc⟩ := (hcpt Y hY).elim_finite_subcover (fun x : Y ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen) (fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV _⟩)
  -- an empty subcover only covers the empty open, over which every section vanishes
  cases isEmpty_or_nonempty c with
  | inl _ =>
    have hY₀ : Y = ⊥ := eq_bot_iff.2 fun y hy ↦ by
      obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 (hc hy)
      exact isEmptyElim (⟨x, hx⟩ : c)
    have := AddCommGrpCat.subsingleton_of_isZero ((isZero_zero _).of_iso
      ((isZero_zero _).isoIsTerminal
        (TopCat.Sheaf.isTerminalOfEqEmpty (cokernel (Injective.ι F)) hY₀)).symm)
    exact ⟨0, @Subsingleton.elim _ this _ _⟩
  | inr _ => ?_
  let U : c → Opens X := fun x ↦ V x
  have hYU : Y ≤ ⨆ x, U x := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hc hy)
    exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hyx⟩
  exact exists_eq_of_cover _ U (fun x ↦ hVY x) hYU
    (quasiIso_cechAugmentation_image hF U hY (fun x ↦ hVB x) hYU) s (fun x ↦ t x)
    (fun x ↦ ht x)

include hcpt hbasis in
/-- A sheaf which is Čech acyclic on `B` has no degree one cohomology on the members of `B`. -/
private lemma subsingleton_H'_one (hF : IsCechAcyclicOn B F) {Y : Opens X} (hY : Y ∈ B) :
    Subsingleton (F.H' 1 Y) :=
  Sheaf.H'.subsingleton_X₁_one (injectiveCokernelSequence_shortExact F) Y
    (surjective_app_cokernel_π hcpt hbasis hF hY)
    (subsingleton_H'_succ_of_isFlasque (Injective.under F) 0 Y)

include hinf hcpt hbasis in
/-- The cokernel `Q` of the chosen embedding of a sheaf `F` which is Čech acyclic on `B` into an
injective sheaf is again Čech acyclic on `B`. -/
private lemma isCechAcyclicOn_cokernel (hF : IsCechAcyclicOn B F) :
    IsCechAcyclicOn B (cokernel (Injective.ι F)) := by
  intro ι _ _ U Y hY hU hYU
  have : TopCat.Presheaf.IsFlasque (TopCat.Sheaf.presheaf (Injective.under F)) :=
    isFlasque_of_injective (Injective.under F)
  have hS (V : Opens X) (hV : V ∈ B) :=
    Sheaf.H'.shortExact_map_sheafSections (injectiveCokernelSequence_shortExact F) V
      (subsingleton_H'_one hcpt hbasis hF hV)
  exact quasiIso_cechAugmentation_X₃_of_shortExact U isTerminalTop
    (((injectiveCokernelSequence F).map (sheafToPresheaf _ AddCommGrpCat.{u})).map
      ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj (prod.functor.obj Y).op))
    (hS _ (by simpa [CompleteLattice.prod_eq_inf] using hY))
    (fun n a ↦ hS _ (prod_pi_mem_of_inf_mem hinf hU hY n a)) (hF U Y hY hU hYU)
    (TopCat.Sheaf.quasiIso_cechAugmentation_prod_of_isFlasque (Injective.under F) U Y hYU)

include hinf hcpt hbasis in
/-- **Cartan's criterion.** Let `B` be a set of quasi-compact opens of `X` which is closed under
binary intersections and contains, inside each of its members, a basis of the topology of that
member. A sheaf of abelian groups which is Čech acyclic for the finite covers of members of `B` by
members of `B` has no cohomology in positive degrees on the members of `B`. -/
theorem subsingleton_H'_succ_of_isCechAcyclicOn (hF : IsCechAcyclicOn B F) {Y : Opens X}
    (hY : Y ∈ B) (n : ℕ) : Subsingleton (F.H' (n + 1) Y) := by
  induction n generalizing F with
  | zero => exact subsingleton_H'_one hcpt hbasis hF hY
  | succ n ih =>
    exact Sheaf.H'.subsingleton_X₁ (injectiveCokernelSequence_shortExact F) Y (n + 1)
      (ih (isCechAcyclicOn_cokernel hinf hcpt hbasis hF))
      (subsingleton_H'_succ_of_isFlasque (Injective.under F) (n + 1) Y)

end

end TauCeti.Topology
end
end
end GeometryLiteralSource040

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.Topology.Sheaves.Cartan"

section GeometryLiteralSource041
/- Original source: TauCeti.AlgebraicGeometry.Cohomology.Affine -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Serre's vanishing theorem on affine opens

Let `M` be a quasi-coherent sheaf of modules on a scheme `X`. This file proves that `M` has no
cohomology in positive degrees on any affine open `U` of `X`: `Hⁿ(U, M) = 0` for `n > 0`, with no
Noetherian hypothesis on `X` or on `Γ(X, U)`. In particular a quasi-coherent sheaf on an affine
scheme, and on the spectrum `Spec R` of any commutative ring, has no higher cohomology. This is the
input that makes Čech complexes of finite affine covers compute the cohomology of quasi-coherent
sheaves on schemes with affine diagonal.

The proof applies Cartan's criterion (`TauCeti.Topology.subsingleton_H'_succ_of_isCechAcyclicOn`)
to the basic opens of `U`, which are quasi-compact, closed under intersection
(`AlgebraicGeometry.Scheme.basicOpen_mul`) and form a basis of the topology of `U`. What has to be
checked is that every finite cover of a basic open `Y` of `U` by basic opens of `U` is acyclic for
`M` (`AlgebraicGeometry.Scheme.Modules.isCechAcyclicOn_range_basicOpen`). This is proved by
induction on the number of members.

* For two members `D(c)` and `D(d)` covering `Y`, the augmented Čech complex is exact as soon as
  every section of `M` over `D(c) ∩ D(d)` is a difference of restrictions of sections over
  `D(c)` and `D(d)`, by
  `TauCeti.CategoryTheory.quasiIso_cechAugmentation_fin_two_iff_isSheafFor_and_surjective`.
  Here `d ^ n • z` extends to `D(c)` and `c ^ m • z` extends to `D(d)`
  (`AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_map`), and `c ^ m` and `d ^ n` generate
  the unit ideal of `Γ(X, Y)`.
* For a cover by `D(f a)` and the `D(f i)`, `i ∈ s`, a relation `1 = a · f a + z` with `z` in the
  ideal generated by the `f i`, `i ∈ s`, gives a basic open `D(z)` contained in the union of the
  `D(f i)`, `i ∈ s`, such that `Y ⊆ D(f a) ∪ D(z)`. The cover is compared with the two-member
  cover by `D(f a)` and `D(z)`, by
  `TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff_of_fin_two_of_quasiIso_prod`, and its
  restriction to `D(z)` with the smaller cover by the `D(f i)`, `i ∈ s`
  (`TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff_of_quasiIso_prod`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.isCechAcyclicOn_range_basicOpen`: finite covers of basic
  opens of an affine open by basic opens are acyclic for a quasi-coherent sheaf.
* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen`: Serre's
  vanishing theorem on the affine opens of a scheme.
* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isAffine`: the same on an
  affine scheme, for example on `Spec R`, as an instance.
* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isAffineHom`: the same on the
  source of an affine morphism (for example a finite morphism) to an affine scheme.

## References

* The Stacks Project, Lemma 30.2.2 (tag 01XB), whose proof via Cartan's criterion is followed
  here.
* R. Hartshorne, *Algebraic Geometry*, Theorem III.3.5 (the Noetherian case) and Exercise III.4.11.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry TauCeti.CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]

/-- **Mayer-Vietoris surjectivity for two basic opens.** If an affine open `W` is covered by the
basic opens `D(c)` and `D(d)` of `c, d ∈ Γ(X, W)`, then every section of a quasi-coherent sheaf over
`D(c) ∩ D(d)` is the difference of the restrictions of sections over `D(c)` and over `D(d)`. -/
private lemma exists_sub_eq {W A₀ A₁ A₀₁ : X.Opens} (hW : IsAffineOpen W) (c d : Γ(X, W))
    (h₀ : X.basicOpen c = A₀) (h₁ : X.basicOpen d = A₁) (h₀₁ : A₀ ⊓ A₁ = A₀₁)
    (hcd : W ≤ A₀ ⊔ A₁) (i₀ : A₀₁ ⟶ A₀) (i₁ : A₀₁ ⟶ A₁) (z : Γ(M, A₀₁)) :
    ∃ (a : Γ(M, A₀)) (b : Γ(M, A₁)), M.presheaf.map i₀.op a - M.presheaf.map i₁.op b = z := by
  subst h₀ h₁ h₀₁
  obtain rfl : i₀ = homOfLE inf_le_left := Subsingleton.elim _ _
  obtain rfl : i₁ = homOfLE inf_le_right := Subsingleton.elim _ _
  have hle : X.basicOpen c ⊓ X.basicOpen d ≤ W := inf_le_left.trans (X.basicOpen_le c)
  -- restriction of functions from `W` to `D(c) ∩ D(d)`
  let ρ := X.presheaf.map (homOfLE hle).op
  -- `d ^ n • z` extends to `D(c)`, and `c ^ m • z` extends to `D(d)`
  obtain ⟨n, y, hy⟩ := M.exists_pow_smul_eq_map (hW.basicOpen c)
    (X.presheaf.map (homOfLE (X.basicOpen_le c)).op d) (by rw [Scheme.basicOpen_res])
    inf_le_left z
  obtain ⟨m, y', hy'⟩ := M.exists_pow_smul_eq_map (hW.basicOpen d)
    (X.presheaf.map (homOfLE (X.basicOpen_le d)).op c)
    (by rw [Scheme.basicOpen_res, inf_comm]) inf_le_right z
  have hρ {V : X.Opens} (hV : V ≤ W) (h : X.basicOpen c ⊓ X.basicOpen d ≤ V) (r : Γ(X, W)) :
      X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE hV).op r) = ρ r := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    -- the two composite inclusions agree, as morphisms in the poset of opens
    rfl
  rw [hρ] at hy hy'
  -- `c ^ m` and `d ^ n` generate the unit ideal of `Γ(X, W)`
  have hpow (f : Γ(X, W)) (k : ℕ) : X.basicOpen f ≤ X.basicOpen (f ^ k) := by
    rcases k.eq_zero_or_pos with rfl | hk
    · simpa using X.basicOpen_le f
    · rw [Scheme.basicOpen_pow _ _ hk]
  obtain ⟨p, q, hpq⟩ := Ideal.mem_span_pair.1 ((hW.self_le_iSup_basicOpen_iff
    (s := {c ^ m, d ^ n})).1 (hcd.trans (sup_le
      ((hpow c m).trans (le_iSup_of_le ⟨c ^ m, by simp⟩ le_rfl))
      ((hpow d n).trans (le_iSup_of_le ⟨d ^ n, by simp⟩ le_rfl)))) ▸ Submodule.mem_top :
        (1 : Γ(X, W)) ∈ Ideal.span {c ^ m, d ^ n})
  refine ⟨X.presheaf.map (homOfLE (X.basicOpen_le c)).op q • y,
    -(X.presheaf.map (homOfLE (X.basicOpen_le d)).op p • y'), ?_⟩
  -- the restriction of `p * c ^ m + q * d ^ n = 1` to `D(c) ∩ D(d)`
  have h1 : ρ q * ρ d ^ n + ρ p * ρ c ^ m = 1 := by
    rw [add_comm]
    simpa using congrArg ρ hpq
  -- both summands are multiples of `z`, with coefficients adding up to `1`
  rw [map_neg, sub_neg_eq_add, M.map_smul, M.map_smul, hρ, hρ, ← hy, ← hy']
  rw [smul_smul, smul_smul, ← add_smul, h1, one_smul]

variable {U : X.Opens}

variable (hU : IsAffineOpen U)

include hU in
/-- **Covers by two basic opens.** Let `U` be an affine open and `Y`, `T 0`, `T 1` basic opens of
`U` with `Y ⊆ T 0 ∪ T 1`. The cover of `Y` by `Y ∩ T 0` and `Y ∩ T 1` is acyclic for a
quasi-coherent sheaf. -/
private lemma quasiIso_cechAugmentation_fin_two {Y : X.Opens}
    (hY : Y ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f) (T : Fin 2 → X.Opens)
    (hT : ∀ i, T i ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f) (hYT : Y ≤ T 0 ⊔ T 1) :
    QuasiIso (cechAugmentation T isTerminalTop
      ((prod.functor.obj Y).op ⋙ ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj)) := by
  rw [quasiIso_cechAugmentation_fin_two_iff_isSheafFor_and_surjective]
  refine ⟨TopCat.Sheaf.isSheafFor_ofArrows_prod ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    Y T (hYT.trans (sup_le (le_iSup T 0) (le_iSup T 1))), fun z ↦ ?_⟩
  obtain ⟨g, rfl⟩ := hY
  obtain ⟨f₀, hf₀⟩ := hT 0
  obtain ⟨f₁, hf₁⟩ := hT 1
  have hres (f : Γ(X, U)) (V : X.Opens) (hV : X.basicOpen f = V) :
      X.basicOpen (X.presheaf.map (homOfLE (X.basicOpen_le g)).op f) = (X.basicOpen g ⨯ V) := by
    rw [Scheme.basicOpen_res, CompleteLattice.prod_eq_inf, hV]
  have e01 : (X.basicOpen g ⨯ T 0) ⊓ (X.basicOpen g ⨯ T 1) = (X.basicOpen g ⨯ (T 0 ⊓ T 1)) := by
    simp only [CompleteLattice.prod_eq_inf]
    exact (inf_inf_distrib_left _ _ _).symm
  have hcov : X.basicOpen g ≤ (X.basicOpen g ⨯ T 0) ⊔ (X.basicOpen g ⨯ T 1) := by
    rw [CompleteLattice.prod_eq_inf, CompleteLattice.prod_eq_inf, ← inf_sup_left]
    exact le_inf le_rfl hYT
  obtain ⟨a, b, hab⟩ := M.exists_sub_eq (A₀ := (X.basicOpen g ⨯ T 0)) (A₁ := (X.basicOpen g ⨯ T 1))
    (A₀₁ := (X.basicOpen g ⨯ (T 0 ⊓ T 1))) (hU.basicOpen g)
    _ _ (hres f₀ _ hf₀) (hres f₁ _ hf₁) e01 hcov
    ((prod.functor.obj (X.basicOpen g)).map (homOfLE inf_le_left))
    ((prod.functor.obj (X.basicOpen g)).map (homOfLE inf_le_right)) z
  exact ⟨(a, b), hab⟩

include hU in
/-- **Finite covers by basic opens.** Let `U` be an affine open, `s` a nonempty finite set of
indices of basic opens `V i` of `U`, and `Y` a basic open of `U` contained in their union. The
cover of `Y` by the opens `Y ∩ V i`, `i ∈ s`, is acyclic for a quasi-coherent sheaf.

The proof is by induction on `s`. For `s = {a} ∪ s'`, choose a basic open `V₁` contained in the
union of the `V i`, `i ∈ s'`, such that `Y ⊆ V a ∪ V₁`. The cover is compared with the two-member
cover by `V a` and `V₁`, whose restrictions to finite intersections are acyclic by the two-member
case. Its restrictions to `V a` and to `V a ∩ V₁` have a member containing everything, and its
restriction to `V₁` is compared with the smaller cover by the `V i`, `i ∈ s'`. -/
private lemma quasiIso_cechAugmentation_finset {ι : Type u} (V : ι → X.Opens)
    (hV : ∀ i, V i ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f) {s : Finset ι}
    (hs : s.Nonempty) (Y : X.Opens) (hY : Y ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f)
    (hYs : Y ≤ s.sup V) :
    QuasiIso (cechAugmentation (fun i : s ↦ V i) isTerminalTop
      ((prod.functor.obj Y).op ⋙ ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj)) := by
  induction hs using Finset.Nonempty.cons_induction generalizing Y with
  | singleton a =>
    exact quasiIso_cechAugmentation_prod_of_hom _ isTerminalTop _ Y
      (i₀ := ⟨a, Finset.mem_singleton_self a⟩) (homOfLE (by simpa using hYs))
  | cons a s ha hs ih =>
    obtain ⟨V₁, hV₁, hYV₁, hV₁s⟩ := hU.exists_mem_range_basicOpen_le_sup hY (hV a) V hV s
      (by simpa [Finset.sup_cons] using hYs)
    let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
    let W : Finset.cons a s ha → X.Opens := fun i ↦ V i
    let W' : s → X.Opens := fun i ↦ V i
    let T : Fin 2 → X.Opens := ![V a, V₁]
    have ha' : a ∈ Finset.cons a s ha := Finset.mem_cons_self a s
    have hT : ∀ i, T i ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f :=
      Fin.forall_fin_two.2 ⟨hV a, hV₁⟩
    have hYT₁ : (Y ⨯ T 1) ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f := by
      rw [CompleteLattice.prod_eq_inf]
      exact Scheme.inf_mem_range_basicOpen _ hY _ hV₁
    -- restricting to `T 1` and then to `Y` is restricting to `Y ∩ T 1`
    let e := Functor.isoWhiskerRight (NatIso.op (prod.functorLeftComp Y (T 1))) F.obj
    refine (quasiIso_cechAugmentation_iff_of_fin_two_of_quasiIso_prod isTerminalTop
      ((prod.functor.obj Y).op ⋙ F.obj) T W (fun n b ↦ ?_)
      (quasiIso_cechAugmentation_prod_of_hom W isTerminalTop _ (T 0) (i₀ := ⟨a, ha'⟩) (𝟙 _)) ?_
      (quasiIso_cechAugmentation_prod_of_hom W isTerminalTop _ (T 0 ⨯ T 1) (i₀ := ⟨a, ha'⟩)
        prod.fst)).2 (quasiIso_cechAugmentation_fin_two M hU hY T hT hYV₁)
    · -- the two-member cover, restricted to a finite intersection of members of `W`
      exact (quasiIso_cechAugmentation_iff_of_iso _ _ _ (Functor.isoWhiskerRight
        (NatIso.op (prod.functorLeftComp _ _)) F.obj)).2
        (quasiIso_cechAugmentation_fin_two M hU (Topology.prod_pi_mem_of_inf_mem (U := W)
          Scheme.inf_mem_range_basicOpen (fun i ↦ hV i) hY n b) T hT
          ((leOfHom prod.fst).trans hYV₁))
    · -- the restriction to `T 1` is compared with the cover by the `V i`, `i ∈ s`
      refine (quasiIso_cechAugmentation_iff_of_quasiIso_prod W isTerminalTop
        ((prod.functor.obj (T 1)).op ⋙ (prod.functor.obj Y).op ⋙ F.obj) W' (fun n b ↦ ?_)
        (fun n b ↦ ?_)).2 ?_
      · exact (quasiIso_cechAugmentation_iff_of_iso _ _ _ (Functor.isoWhiskerLeft _ e ≪≫
          Functor.isoWhiskerRight (NatIso.op (prod.functorLeftComp _ _)) F.obj)).2
          (ih _ (Topology.prod_pi_mem_of_inf_mem (U := W) Scheme.inf_mem_range_basicOpen
            (fun i ↦ hV i) hYT₁ n b) ((leOfHom (prod.fst ≫ prod.snd)).trans hV₁s))
      · exact quasiIso_cechAugmentation_prod_of_hom W isTerminalTop _ _
          (i₀ := ⟨b 0, Finset.mem_cons_of_mem (b 0).2⟩) (Pi.π _ 0)
      · exact (quasiIso_cechAugmentation_iff_of_iso _ _ _ e).2
          (ih _ hYT₁ ((leOfHom prod.snd).trans hV₁s))

include hU in
/-- **Čech acyclicity of covers by basic opens.** Let `U` be an affine open of a scheme `X` and
`M` a quasi-coherent sheaf of modules on `X`. For every basic open `Y` of `U` and every finite
nonempty family of basic opens of `U` covering `Y`, the augmented Čech complex of `M` for the
induced cover of `Y` is exact. -/
theorem isCechAcyclicOn_range_basicOpen :
    TauCeti.Topology.IsCechAcyclicOn (Set.range fun f : Γ(X, U) ↦ X.basicOpen f)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := by
  rw [TauCeti.Topology.isCechAcyclicOn_iff]
  intro ι _ _ V Y hY hV hYV
  have := Fintype.ofFinite ι
  exact (quasiIso_cechAugmentation_congr isTerminalTop _
    ⟨fun i ↦ ⟨i, Finset.mem_univ i⟩, fun _ ↦ 𝟙 _⟩ ⟨Subtype.val, fun _ ↦ 𝟙 _⟩).2
    (quasiIso_cechAugmentation_finset M hU V hV Finset.univ_nonempty Y hY
      (by rwa [Finset.sup_univ_eq_iSup]))

include hU in
/-- **Serre's vanishing theorem on affine opens** (Hartshorne, *Algebraic Geometry*, Theorem
III.3.5, without the Noetherian hypothesis): a quasi-coherent sheaf of modules has no cohomology in
positive degrees on an affine open subset of a scheme. -/
theorem subsingleton_cohomologyOn_succ_of_isAffineOpen (n : ℕ) :
    Subsingleton (cohomologyOn M (n + 1) U) := by
  refine TauCeti.Topology.subsingleton_H'_succ_of_isCechAcyclicOn Scheme.inf_mem_range_basicOpen
    ?_ ?_ (isCechAcyclicOn_range_basicOpen M hU) ⟨1, Scheme.basicOpen_one _⟩ n
  · rintro _ ⟨f, rfl⟩
    exact (hU.basicOpen f).isCompact
  · rintro _ ⟨f, rfl⟩ V hV x hx
    obtain ⟨g, hg, hxg⟩ := hU.exists_basicOpen_le ⟨x, hx⟩ (X.basicOpen_le f (hV hx))
    exact ⟨_, ⟨g, rfl⟩, hxg, hg⟩

/-- **Serre's vanishing theorem on affine schemes**: a quasi-coherent sheaf of modules on an
affine scheme, for example on the spectrum `Spec R` of any commutative ring, has no cohomology in
positive degrees. -/
instance subsingleton_cohomology_succ_of_isAffine [IsAffine X] (n : ℕ) :
    Subsingleton (Cohomology M (n + 1)) := by
  have := subsingleton_cohomologyOn_succ_of_isAffineOpen M (isAffineOpen_top X) n
  exact (cohomologyOnTopIso M (n + 1)).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

/-- A quasi-coherent sheaf on the source of an affine morphism to an affine scheme (for example, on
a scheme finite over a field) has no cohomology in positive degrees. -/
theorem subsingleton_cohomology_succ_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    [IsAffine S] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (Cohomology M (n + 1)) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  exact subsingleton_cohomology_succ_of_isAffine M n

end AlgebraicGeometry.Scheme.Modules
end
end
end GeometryLiteralSource041

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.AlgebraicGeometry.Cohomology.Affine"

section GeometryLiteralSource042
/- Original source: PaperVerification.AffineCechComparison -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Čech comparison for finite affine covers

This is the additive comparison from
`TauCeti.AlgebraicGeometry.Cohomology.Cech.Basic`, with only the dependencies
needed for that comparison. The scalar-action and affine-pushforward
extensions in the larger upstream module are unnecessary here.
-/

@[expose] public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.CategoryTheory TauCeti.AlgebraicGeometry.Scheme.Modules

namespace PaperVerification.AffineCechComparison

universe u
variable {X : Scheme.{u}} {ι : Type u} [Finite ι]

/-- A finite cover with affine intersections computes actual sheaf cohomology. -/
def homologyCechComplexIsoCohomology (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U))
    (hcover : iSup U = ⊤) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    ((cechComplexFunctor U).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj).homology n ≅
      AddCommGrpCat.of (Cohomology M n) :=
  TauCeti.Topology.homologyCechComplexIsoH U hcover _
    (fun s hs k => AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen
      M (hU s hs) k) n

end PaperVerification.AffineCechComparison
end
end
end GeometryLiteralSource042

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: PaperVerification.AffineCechComparison"

