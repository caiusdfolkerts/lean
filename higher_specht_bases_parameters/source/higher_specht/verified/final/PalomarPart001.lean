module

public import higher_specht.verified.final.PalomarPart000
import all higher_specht.verified.final.PalomarPart000
public import higher_specht.verified.remaining04_geometry_complete
public import tau_ceti.ring_theory.koszul_complex.basis
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.RingTheory.Regular.Flat
public import tau_ceti.ring_theory.koszul_complex.regular
public import Mathlib.CategoryTheory.Monoidal.Tor
public import tau_ceti.linear_algebra.exterior_power.localization
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import tau_ceti.algebra.category.module_cat.projective.dimension
public import tau_ceti.data.e_nat.basic
public import tau_ceti.linear_algebra.dual.right_action
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import tau_ceti.algebra.category.module_cat.coextend_scalars
public import tau_ceti.algebra.homology.ext.basic
public import tau_ceti.ring_theory.regular_local_ring.projective_dimension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
public import Mathlib.RingTheory.LocalProperties.InjectiveDimension

/- Generated ordinary source-preserving proof stage. See audit/staged_specht_remaining/Final/manifest.json. -/

@[expose] public section

section CanonicalSource23
/- Source: HigherSpecht/FiniteDualProjectiveDimension.lean -/



/-!
# Finite injective dimension and the projective dimension of the dual

A finite B-projective A-module admits a finite A-free presentation whose
kernel is again finite B-projective. Its genuine B-dual sequence is exact.
Relative Ext dimension shifting then proves finite projective dimension of
the original module from a relative Ext bound on its dual. Applied to the
regular module's dual, this is the needed implication from finite
self-injective dimension; no duality equivalence is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian Module

universe u

namespace HigherSpecht

variable (B A : Type u) [CommRing B] [CommRing A] [Algebra B A]

/-- The homothety equivalence is linear over A as well as over B. -/
def relativeDualHomothetyLinearEquiv [Module.Free B A] [Module.Finite B A] :
    A ≃ₗ[A] ParameterDual B A (RelativeDual B A) := by
  have h : (fun a : A => LinearMap.lsmul A (RelativeDual B A) a) =
      relativeDualHomothetyEquiv (B := B) (A := A) := by
    funext a
    apply LinearMap.ext
    intro f
    exact (relativeDualHomothetyEquiv_apply a f).symm
  refine LinearEquiv.ofBijective (LinearMap.lsmul A (RelativeDual B A)) ?_
  change Function.Bijective (fun a : A => LinearMap.lsmul A (RelativeDual B A) a)
  rw [h]
  exact (relativeDualHomothetyEquiv (B := B) (A := A)).bijective

/-- A splitting of the transpose gives a splitting of the original map
by actual finite-projective bidual evaluation. -/
theorem exists_section_of_dual_retraction
    {M P : Type u} [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower B A M] [Module.Finite B M] [Module.Projective B M]
    [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower B A P]
    [Module.Finite B P] [Module.Projective B P]
    (f : P →ₗ[A] M)
    (r : ParameterDual B A P →ₗ[A] ParameterDual B A M)
    (hr : r.comp (parameterDualMap (B := B) f) = LinearMap.id) :
    ∃ s : M →ₗ[A] P, f.comp s = LinearMap.id := by
  let eM := parameterBidualEquiv (B := B) (A := A) (M := M)
  let eP := parameterBidualEquiv (B := B) (A := A) (M := P)
  let s : M →ₗ[A] P :=
    eP.symm.toLinearMap.comp ((parameterDualMap (B := B) r).comp eM.toLinearMap)
  refine ⟨s, ?_⟩
  ext m
  apply eM.injective
  apply LinearMap.ext
  intro l
  have hs : eP (s m) = parameterDualMap (B := B) r (eM m) :=
    eP.apply_symm_apply _
  have hl := LinearMap.congr_fun hs (parameterDualMap (B := B) f l)
  have hrl := LinearMap.congr_fun hr l
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hrl
  change l (f (s m)) = l m
  simpa only [eP, eM, parameterBidualEquiv_apply, parameterDualMap_apply,
    LinearMap.comp_apply, LinearMap.id_apply, hrl] using hl

/-- The kernel of a surjection onto a B-projective module is B-projective.
The splitting is the actual B-linear splitting of its kernel sequence. -/
theorem kernel_projective_over_base
    {M P : Type u} [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower B A M] [Module.Projective B M]
    [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower B A P]
    [Module.Projective B P]
    (f : P →ₗ[A] M) (hf : Function.Surjective f) :
    Module.Projective B (LinearMap.ker f) := by
  let S : ShortComplex (ModuleCat.{u} B) :=
    ShortComplex.moduleCatMk ((LinearMap.ker f).subtype.restrictScalars B)
      (f.restrictScalars B) (by ext x; exact x.property)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_ker_map f) Subtype.val_injective hf
  haveI : Projective S.X₃ :=
    show Projective (ModuleCat.of B M) from inferInstance
  let split := hS.splittingOfProjective
  exact Module.Projective.of_split ((LinearMap.ker f).subtype.restrictScalars B)
    split.r.hom (ModuleCat.hom_ext_iff.mp split.f_r)

/-- The actual dual exact sequence transfers a finite relative Ext bound
to an ordinary projective-dimension bound. -/
theorem hasProjectiveDimensionLE_of_parameterDual_bound
    [IsNoetherianRing B] [Module.Free B A] [Module.Finite B A]
    (d : ℕ) (M : Type u) [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower B A M] [Module.Finite B M] [Module.Projective B M]
    (h : ParameterExtBound B A (ParameterDual B A M) d) :
    HasProjectiveDimensionLE (ModuleCat.of A M) d := by
  induction d generalizing M with
  | zero =>
      letI := HasExt.standard (ModuleCat.{u} A)
      letI : Module.Finite A M := Module.Finite.of_restrictScalars_finite B A M
      obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' A M
      let K := LinearMap.ker f
      letI : Module.Projective B K := kernel_projective_over_base B A f hf
      letI : Module.Finite B K :=
        Module.Finite.of_injective ((LinearMap.ker f).subtype.restrictScalars B)
          Subtype.val_injective
      letI : Module.Finite B (ParameterDual B A K) := parameterDual_finite
      letI : Module.Projective B (ParameterDual B A K) := parameterDual_projective
      let S := parameterDualShortComplex (B := B) (LinearMap.ker f).subtype f
        (by ext x; exact x.property)
      have hS : S.ShortExact := parameterDualShortComplex_shortExact
        (LinearMap.ker f).subtype f (LinearMap.exact_subtype_ker_map f)
          Subtype.val_injective hf
      obtain ⟨r', hr'⟩ := hS.exists_f_comp_eq_of_ext_eq_zero
        (h (ParameterDual B A K) 1 (by decide)) (𝟙 S.X₁)
      have hr : r'.hom.comp (parameterDualMap (B := B) f) = LinearMap.id := by
        exact ModuleCat.hom_ext_iff.mp hr'
      obtain ⟨s, hs⟩ := exists_section_of_dual_retraction B A f r'.hom hr
      letI : Module.Projective A M := Module.Projective.of_split s f hs
      exact inferInstance
  | succ d ih =>
      letI : Module.Finite A M := Module.Finite.of_restrictScalars_finite B A M
      obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' A M
      let K := LinearMap.ker f
      letI : Module.Projective B K := kernel_projective_over_base B A f hf
      letI : Module.Finite B K :=
        Module.Finite.of_injective ((LinearMap.ker f).subtype.restrictScalars B)
          Subtype.val_injective
      let T := parameterDualShortComplex (B := B) (LinearMap.ker f).subtype f
        (by ext x; exact x.property)
      have hT : T.ShortExact := parameterDualShortComplex_shortExact
        (LinearMap.ker f).subtype f (LinearMap.exact_subtype_ker_map f)
          Subtype.val_injective hf
      have hK : ParameterExtBound B A (ParameterDual B A K) d :=
        parameterExtBound_cokernel B A hT h (parameterExtBound_dualFiniteFree B A r)
      have hpdK := ih K hK
      let S : ShortComplex (ModuleCat.{u} A) :=
        ShortComplex.moduleCatMk (LinearMap.ker f).subtype f
          (by ext x; exact x.property)
      have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
        (LinearMap.exact_subtype_ker_map f) Subtype.val_injective hf
      haveI : Projective S.X₂ :=
        show Projective (ModuleCat.of A (Fin r → A)) from inferInstance
      exact hS.hasProjectiveDimensionLT_X₃ (d + 1) hpdK
        (hasProjectiveDimensionLT_of_ge S.X₂ 1 (d + 1 + 1) (by omega))

/-- Finite self-injective dimension of the algebra implies finite
projective dimension of its actual finite-free relative dual. -/
theorem relativeDual_hasProjectiveDimensionLE_of_selfInjectiveDimension
    [IsNoetherianRing B] [Module.Free B A] [Module.Finite B A]
    (d : ℕ) (h : HasInjectiveDimensionLE (ModuleCat.of A A) d) :
    HasProjectiveDimensionLE (ModuleCat.of A (RelativeDual B A)) d := by
  letI : Module.Free B (RelativeDual B A) :=
    Module.Free.of_equiv (RelativeDual.linearEquiv B A).symm
  letI : Module.Finite B (RelativeDual B A) :=
    Module.Finite.equiv (RelativeDual.linearEquiv B A).symm
  apply hasProjectiveDimensionLE_of_parameterDual_bound B A d (RelativeDual B A)
  exact parameterExtBound_equiv B A (relativeDualHomothetyLinearEquiv B A)
    (parameterExtBound_of_hasInjectiveDimensionLE B A A d h)

end HigherSpecht
end
end CanonicalSource23

section CanonicalSource24
/- Source: HigherSpecht/FreeHomothetyRankOne.lean -/



/-!
# Free modules with only scalar endomorphisms

The conclusion is an actual cyclic generator. It follows directly from
coordinate projections on a basis: a projection onto one basis vector
cannot be a scalar if another basis vector exists. This avoids relying
on a numerical rank equation or on a Gorenstein characterization.
-/

noncomputable section

open Module
open scoped Classical

universe u

namespace HigherSpecht

variable {A : Type u} [CommRing A] [Nontrivial A]

/-- A nonzero free module whose every endomorphism is scalar has an
actual single generator. No domain or field hypothesis is needed. -/
theorem cyclic_of_free_of_surjective_homothety
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Free A M] [Nontrivial M]
    (h : Function.Surjective (fun a : A => LinearMap.lsmul A M a)) :
    ∃ m : M, Submodule.span A {m} = ⊤ := by
  let b := Module.Free.chooseBasis A M
  obtain ⟨i⟩ := b.index_nonempty
  let p : Module.End A M := b.constr A (fun j => if j = i then b j else 0)
  obtain ⟨a, ha⟩ := h p
  have ha1 : a = 1 := by
    have ht := congrArg (fun f : Module.End A M => b.repr (f (b i)) i) ha
    simpa [p, Basis.constr_basis] using ht
  have hindex (j : Module.Free.ChooseBasisIndex A M) : j = i := by
    by_contra hji
    have ht := congrArg (fun f : Module.End A M => b.repr (f (b j)) j) ha
    have ha0 : a = 0 := by simpa [p, hji, Basis.constr_basis] using ht
    exact one_ne_zero (ha1.symm.trans ha0)
  have hrange : Set.range b = {b i} := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact congrArg b (hindex j)
    · intro hx
      exact ⟨i, hx.symm⟩
  exact ⟨b i, hrange ▸ b.span_eq⟩

/-- The actual relative dual is nonzero because its faithful homotheties
include the distinct actions of zero and one. -/
theorem relativeDual_nontrivial (B : Type u) [CommRing B] [Algebra B A]
    [Module.Free B A] [Module.Finite B A] : Nontrivial (RelativeDual B A) := by
  by_contra h
  haveI : Subsingleton (RelativeDual B A) := not_nontrivial_iff_subsingleton.mp h
  have hh : relativeDualHomothetyLinearEquiv B A (0 : A) =
      relativeDualHomothetyLinearEquiv B A (1 : A) := by
    exact Subsingleton.elim _ _
  exact zero_ne_one ((relativeDualHomothetyLinearEquiv B A).injective hh)

/-- Once the genuine relative dual is free over A, its faithful full
endomorphism ring forces it to be free of rank one, with an actual generator. -/
theorem relativeDual_cyclic_of_free (B : Type u) [CommRing B] [Algebra B A]
    [Module.Free B A] [Module.Finite B A] [Module.Free A (RelativeDual B A)] :
    ∃ f : RelativeDual B A, Submodule.span A {f} = ⊤ := by
  letI := relativeDual_nontrivial (A := A) B
  apply cyclic_of_free_of_surjective_homothety (RelativeDual B A)
  change Function.Surjective (relativeDualHomothetyLinearEquiv B A)
  exact (relativeDualHomothetyLinearEquiv B A).surjective

end HigherSpecht
end
end CanonicalSource24

section CanonicalSource25
/- Source: HigherSpecht/FiniteLocalDualDepth.lean -/



/-!
# Depth and freeness of the actual relative dual at a local finite algebra

The flat local depth formula bounds the depth below by the depth of the
regular local base.  Finite integrality bounds the dimension above by the
same number.  Thus every nonzero module flat over that base has full depth.
The genuine Auslander--Buchsbaum formula then turns a finite projective
dimension of the relative dual into freeness over the local algebra.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian IsLocalRing Module

universe u

namespace HigherSpecht

variable {R A : Type u} [CommRing R] [CommRing A]
  [Algebra R A] [IsLocalRing R] [IsLocalRing A] [Module.Finite R A]

theorem finiteLocalAlgebra_isLocalHom : IsLocalHom (algebraMap R A) := by
  refine ⟨fun r hr => ?_⟩
  by_contra hru
  have hrm : r ∈ IsLocalRing.maximalIdeal R := hru
  have hi : algebraMap R A r ∈ IsLocalRing.maximalIdeal A := by
    change r ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap R A)
    rw [Ideal.comap_eq_maximalIdeal_of_isIntegral (R := R)]
    exact hrm
  exact hi hr

/-- Full depth of a nonzero finite module flat over the regular local
base.  The equality concerns the actual Ext-defined depth. -/
theorem depth_eq_regularBase_of_finite_flat
    [IsRegularLocalRing R]
    (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] [Module.Flat R N]
    [Nontrivial N] :
    depth (ModuleCat.of A N) = depth (ModuleCat.of R R) := by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  letI : IsLocalHom (algebraMap R A) := finiteLocalAlgebra_isLocalHom
  have hlo : depth (ModuleCat.of R R) ≤ depth (ModuleCat.of A N) := by
    have h := depth_tensorProduct_eq_add_of_flat
      (R := R) (S := A) (N := N) (M := R)
    rw [depth_eq_of_linearEquiv (TensorProduct.AlgebraTensorModule.rid R A N)] at h
    rw [h]
    exact le_add_of_nonneg_right zero_le
  have hhi : (depth (ModuleCat.of A N) : WithBot ℕ∞) ≤
      (depth (ModuleCat.of R R) : WithBot ℕ∞) := by
    calc
      (depth (ModuleCat.of A N) : WithBot ℕ∞) ≤ Module.supportDim A N :=
        depth_le_supportDim
      _ ≤ ringKrullDim A := Module.supportDim_le_ringKrullDim A N
      _ ≤ ringKrullDim R := TauCeti.ringKrullDim_le_of_isIntegral
      _ = (depth (ModuleCat.of R R) : WithBot ℕ∞) :=
        TauCeti.IsRegularLocalRing.depth_eq_ringKrullDim.symm
  exact le_antisymm (WithBot.coe_le_coe.mp hhi) hlo

theorem depth_eq_self_of_finite_flat_regularBase
    [IsRegularLocalRing R] [Module.Flat R A]
    (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] [Module.Flat R N]
    [Nontrivial N] :
    depth (ModuleCat.of A N) = depth (ModuleCat.of A A) := by
  rw [depth_eq_regularBase_of_finite_flat (R := R) N,
    depth_eq_regularBase_of_finite_flat (R := R) A]

/-- A nonzero finite module of full depth and finite projective dimension
is free over the actual Noetherian local ring. -/
theorem free_of_finiteProjectiveDimension_of_depth_eq
    [IsNoetherianRing A]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Nontrivial N] (d : ℕ)
    (hpd : HasProjectiveDimensionLE (ModuleCat.of A N) d)
    (hdepth : depth (ModuleCat.of A N) = depth (ModuleCat.of A A)) :
    Module.Free A N := by
  have hpdle := (projectiveDimension_le_iff (ModuleCat.of A N) d).mpr hpd
  have hpdtop : projectiveDimension (ModuleCat.of A N) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hpdle (by
      have hd : ((d : ℕ∞) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d)
      simpa only [WithBot.coe_natCast, WithBot.coe_top] using hd))
  have hbot : projectiveDimension (ModuleCat.of A N) ≠ ⊥ := by
    rw [ne_eq, projectiveDimension_eq_bot_iff]
    exact fun h => not_subsingleton N (ModuleCat.subsingleton_of_isZero h)
  obtain ⟨p, hp⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hptop : p ≠ ⊤ := fun h => hpdtop (by simpa only [h, WithBot.coe_top] using hp.symm)
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hptop
  have hdepthtop : depth (ModuleCat.of A A) ≠ ⊤ :=
    fun h => not_subsingleton A ((depth_eq_top_iff _).mp h)
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hdepthtop
  have hab := ModuleCat.projectiveDimension_add_depth_eq_depth
    (ModuleCat.of A N) hpdtop
  rw [hdepth, ← hp, ← he] at hab
  have hnat : k + e = e := by exact_mod_cast hab
  have hk : k = 0 := by omega
  have hpdzero : projectiveDimension (ModuleCat.of A N) = 0 := by
    simpa only [hk, ENat.natCast_zero, WithBot.coe_zero] using hp.symm
  letI : Projective (ModuleCat.of A N) :=
    ((projectiveDimension_eq_zero_iff _).mp hpdzero).1
  letI : Module.Projective A N :=
    (IsProjective.iff_projective N).mpr inferInstance
  exact Module.free_of_flat_of_isLocalRing

theorem relativeDual_nontrivial_of_finite_free
    [Module.Free R A] : Nontrivial (RelativeDual R A) := by
  exact relativeDual_nontrivial (A := A) R

/-- The local relative dual is free as soon as the actual local algebra
has finite self-injective dimension. -/
theorem relativeDual_free_of_local_selfInjectiveDimension
    [IsRegularLocalRing R] [Module.Free R A]
    (d : ℕ) (h : HasInjectiveDimensionLE (ModuleCat.of A A) d) :
    Module.Free A (RelativeDual R A) := by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  letI : Module.Free R (RelativeDual R A) :=
    Module.Free.of_equiv (RelativeDual.linearEquiv R A).symm
  letI : Module.Finite R (RelativeDual R A) :=
    Module.Finite.equiv (RelativeDual.linearEquiv R A).symm
  letI : Module.Finite A (RelativeDual R A) :=
    Module.Finite.of_restrictScalars_finite R A _
  letI : Nontrivial (RelativeDual R A) :=
    relativeDual_nontrivial_of_finite_free
  apply free_of_finiteProjectiveDimension_of_depth_eq (RelativeDual R A) d
    (relativeDual_hasProjectiveDimensionLE_of_selfInjectiveDimension R A d h)
  exact depth_eq_self_of_finite_flat_regularBase (R := R) (RelativeDual R A)

/-- This is an actual cyclic generator, obtained from freeness and
homothety, rather than a numerical definition of type one. -/
theorem relativeDual_cyclic_of_local_selfInjectiveDimension
    [IsRegularLocalRing R] [Module.Free R A]
    (d : ℕ) (h : HasInjectiveDimensionLE (ModuleCat.of A A) d) :
    ∃ f : RelativeDual R A, Submodule.span A {f} = ⊤ := by
  letI := relativeDual_free_of_local_selfInjectiveDimension (R := R) d h
  exact relativeDual_cyclic_of_free R

end HigherSpecht
end
end CanonicalSource25

section CanonicalSource26
/- Source: HigherSpecht/RingEquivInjectiveDimension.lean -/



/-! # Self-injective dimension under an actual ring equivalence -/

noncomputable section

open CategoryTheory

namespace HigherSpecht

universe u

variable {R S : Type u} [Ring R] [Ring S]

attribute [local instance] RingHomInvPair.of_ringEquiv

local instance ringEquivToRingHomInvPair (e : R ≃+* S) :
    RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e

local instance ringEquivSymmToRingHomInvPair (e : R ≃+* S) :
    RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm e

def ringEquivRegularModule (e : R ≃+* S) :
    ModuleCat.of R R ≃ₛₗ[e.toRingHom] ModuleCat.of S S where
  __ := e.toAddEquiv
  map_smul' r x := e.map_mul r x

theorem selfInjectiveDimensionLE_iff_of_ringEquiv (e : R ≃+* S) (d : ℕ) :
    HasInjectiveDimensionLE (ModuleCat.of R R) d ↔
      HasInjectiveDimensionLE (ModuleCat.of S S) d :=
  ModuleCat.hasInjectiveDimensionLE_iff_of_semiLinearEquiv e
    (ringEquivRegularModule e) d

end HigherSpecht
end
end CanonicalSource26

section CanonicalSource27
/- Source: HigherSpecht/UntruncatedOrigin.lean -/



/-!
# The actual homogeneous-origin localization of the untruncated ring

Both augmentation maps are evaluation at zero.  The special-fiber
kernel is identified using the genuine parameter basis, and its
nilpotence is the already established Springer nilpotence theorem.
These facts instantiate the finite local-fiber construction with no
localness, depth, or cyclicity premise on the quotient.
-/

noncomputable section

open TauCeti Module MvPolynomial
open scoped Classical TensorProduct

namespace HigherSpecht

variable (K : Type*) [Field K]

def untruncatedAugmentation (n : ℕ) (lam : YoungDiagram) :
    UntruncatedRing K n lam →ₐ[K] K :=
  Ideal.Quotient.liftₐ (untruncatedIdeal K n lam)
    (MvPolynomial.aeval fun _ : Fin n => (0 : K)) (by
      intro p hp
      have hz := untruncatedIdeal_le_constantCoeff_ker (R := K) n lam hp
      simpa only [RingHom.mem_ker, MvPolynomial.aeval_zero',
        Algebra.algebraMap_self, RingHom.id_apply] using hz)

@[simp] theorem untruncatedAugmentation_mk
    (n : ℕ) (lam : YoungDiagram) (p : PolynomialRing n K) :
    untruncatedAugmentation K n lam (Ideal.Quotient.mk (untruncatedIdeal K n lam) p) =
      p.constantCoeff := by
  change (MvPolynomial.aeval (fun _ : Fin n => (0 : K))) p = p.constantCoeff
  simp only [MvPolynomial.aeval_zero', Algebra.algebraMap_self, RingHom.id_apply]

def elementaryOriginAugmentation (n : ℕ) (lam : YoungDiagram) :
    ElementaryParameterRing K n lam →ₐ[K] K :=
  MvPolynomial.aeval fun _ : Fin (n - lam.card) => (0 : K)

@[simp] theorem elementaryOriginAugmentation_apply
    (n : ℕ) (lam : YoungDiagram) (p : ElementaryParameterRing K n lam) :
    elementaryOriginAugmentation K n lam p = p.constantCoeff := by
  simp only [elementaryOriginAugmentation, MvPolynomial.aeval_zero',
    Algebra.algebraMap_self, RingHom.id_apply]

abbrev untruncatedOrigin (n : ℕ) (lam : YoungDiagram) :
    Ideal (UntruncatedRing K n lam) := RingHom.ker (untruncatedAugmentation K n lam)

abbrev untruncatedOriginBase (n : ℕ) (lam : YoungDiagram) :=
  parameterOriginBase (elementaryOriginAugmentation K n lam)

abbrev untruncatedOriginAlgebra (n : ℕ) (lam : YoungDiagram) :=
  parameterOriginBaseChange (UntruncatedRing K n lam) (elementaryOriginAugmentation K n lam)

theorem untruncatedAugmentation_comp_specialFiber
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (untruncatedAugmentation K n (adjoinOnes lam (n - lam.card))).comp
        (specialFiberQuotientMap K n lam hk) = untruncatedAugmentation K n lam := by
  ext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [AlgHom.comp_apply, specialFiberQuotientMap_mk, untruncatedAugmentation_mk]

theorem specialFiberQuotientMap_ker_le_parameterIdeal
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    RingHom.ker (specialFiberQuotientMap K n lam hk) ≤
      (RingHom.ker (elementaryOriginAugmentation K n lam)).map
        (algebraMap (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)) := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  intro x hx
  let b := untruncatedMonomialParameterBasis K n lam hk
  have hc (i : SpecialFiberMonomialIndex n lam) :
      elementaryOriginAugmentation K n lam (b.repr x i) = 0 := by
    have hi := congrArg (fun z => (specialFiberCoefficientBasis K n lam hk).repr z i)
      (show specialFiberQuotientMap K n lam hk x = 0 from hx)
    simpa only [elementaryOriginAugmentation_apply, b, specialFiberQuotientMap_repr,
      map_zero, Finsupp.zero_apply] using hi
  rw [← b.sum_repr x]
  apply Ideal.sum_mem
  intro i _
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hc i))

theorem untruncatedAugmentation_nilpotent_fullSize
    (n : ℕ) (mu : YoungDiagram) (hcard : mu.card = n)
    (x : UntruncatedRing K n mu) (hx : untruncatedAugmentation K n mu x = 0) :
    IsNilpotent x := by
  subst n
  exact springer_isNilpotent_of_augmentation_eq_zero mu hx

theorem untruncatedOriginAlgebra_isLocalRing
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsLocalRing (untruncatedOriginAlgebra K n lam) := by
  letI := untruncated_parameter_finite_allCoefficients K n lam hk
  apply parameterOriginBaseChange_isLocalRing
    (elementaryOriginAugmentation K n lam) (specialFiberQuotientMap K n lam hk)
    (fun p => by simpa only [elementaryOriginAugmentation_apply] using
      specialFiberQuotientMap_algebraMap K n lam hk p)
    (untruncatedAugmentation K n (adjoinOnes lam (n - lam.card)))
    (specialFiberQuotientMap_surjective K n lam hk)
    (specialFiberQuotientMap_ker_le_parameterIdeal K n lam hk)
  exact untruncatedAugmentation_nilpotent_fullSize K n _
    (by rw [adjoinOnes_card, Nat.add_sub_of_le hk])

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def untruncatedOriginLocalizationEquiv
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Localization.AtPrime (untruncatedOrigin K n lam) ≃ₐ[UntruncatedRing K n lam]
      untruncatedOriginAlgebra K n lam := by
  letI := untruncated_parameter_finite_allCoefficients K n lam hk
  have e := parameterOriginLocalizationEquiv
      (elementaryOriginAugmentation K n lam) (specialFiberQuotientMap K n lam hk)
      (fun p => by simpa only [elementaryOriginAugmentation_apply] using
        specialFiberQuotientMap_algebraMap K n lam hk p)
      (untruncatedAugmentation K n (adjoinOnes lam (n - lam.card)))
      (specialFiberQuotientMap_surjective K n lam hk)
      (specialFiberQuotientMap_ker_le_parameterIdeal K n lam hk)
      (untruncatedAugmentation_nilpotent_fullSize K n _
        (by rw [adjoinOnes_card, Nat.add_sub_of_le hk]))
  exact Eq.mp
    (congrArg (fun eps : UntruncatedRing K n lam →ₐ[K] K =>
      Localization.AtPrime (RingHom.ker eps) ≃ₐ[UntruncatedRing K n lam]
        untruncatedOriginAlgebra K n lam)
      (untruncatedAugmentation_comp_specialFiber K n lam hk)) e

theorem untruncatedOriginAlgebra_free
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Free (untruncatedOriginBase K n lam) (untruncatedOriginAlgebra K n lam) := by
  letI := untruncated_parameter_free_allCoefficients K n lam hk
  infer_instance

theorem untruncatedOriginAlgebra_finite
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Finite (untruncatedOriginBase K n lam) (untruncatedOriginAlgebra K n lam) := by
  letI := untruncated_parameter_finite_allCoefficients K n lam hk
  infer_instance

/-- Gorensteinness supplies a genuine cyclic generator of the relative
dual at the homogeneous origin, by the actual local homological proof. -/
theorem untruncatedOrigin_relativeDual_cyclic_of_gorenstein
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hG : IsGorensteinRing (UntruncatedRing K n lam)) :
    ∃ f : RelativeDual (untruncatedOriginBase K n lam) (untruncatedOriginAlgebra K n lam),
      Submodule.span (untruncatedOriginAlgebra K n lam) {f} = ⊤ := by
  letI := untruncatedOriginAlgebra_isLocalRing K n lam hk
  letI := untruncatedOriginAlgebra_free K n lam hk
  letI := untruncatedOriginAlgebra_finite K n lam hk
  obtain ⟨d, hd⟩ := hG.2 ⟨untruncatedOrigin K n lam, inferInstance⟩
  have hC := (selfInjectiveDimensionLE_iff_of_ringEquiv
    (untruncatedOriginLocalizationEquiv K n lam hk).toRingEquiv d).mp hd
  exact relativeDual_cyclic_of_local_selfInjectiveDimension
    (R := untruncatedOriginBase K n lam) d hC

end HigherSpecht
end
end CanonicalSource27

section CanonicalSource28
/- Source: HigherSpecht/FiniteBasisDualSpecialization.lean -/



/-!
# Specialization of a finite free relative dual

The map below evaluates the coefficients of a functional in an actual
finite basis.  Its compatibility with multiplication follows from its
evaluation formula.  Thus an actual cyclic generator specializes to a
cyclic generator of the dual of the closed fiber.  Restriction to the
augmentation annihilator then bounds its genuine vector-space dimension.
-/

noncomputable section

open Module
open scoped Classical

namespace HigherSpecht

section Specialization

variable {R C K Q ι : Type*} [CommRing R] [CommRing C] [Algebra R C]
  [Field K] [CommRing Q] [Algebra K Q] [Fintype ι]
  (b : Basis ι R C) (c : Basis ι K Q) (rho : R →+* K) (q : C →+* Q)
  (hqScalar : ∀ r, q (algebraMap R C r) = algebraMap K Q (rho r))
  (hbc : ∀ i, q (b i) = c i)

def finiteBasisDualSpecialization (f : RelativeDual R C) : RelativeDual K Q :=
  c.constr K (fun i => rho (f (b i)))

@[simp] theorem finiteBasisDualSpecialization_basis (f : RelativeDual R C) (i : ι) :
    finiteBasisDualSpecialization b c rho f (c i) = rho (f (b i)) :=
  Basis.constr_basis _ _ _ _

include hqScalar hbc in
theorem finiteBasisDualSpecialization_eval (f : RelativeDual R C) (z : C) :
    finiteBasisDualSpecialization b c rho f (q z) = rho (f z) := by
  have hsmul (r : R) (x : C) : q (r • x) = rho r • q x := by
    rw [Algebra.smul_def, map_mul, hqScalar, Algebra.smul_def]
  rw [← b.sum_repr z]
  simp only [map_sum, hsmul, hbc, map_smul, finiteBasisDualSpecialization_basis,
    smul_eq_mul, map_mul]

include hqScalar hbc in
theorem finiteBasisDualSpecialization_smul
    (hq : Function.Surjective q) (a : C) (f : RelativeDual R C) :
    finiteBasisDualSpecialization b c rho (a • f) =
      q a • finiteBasisDualSpecialization b c rho f := by
  apply RelativeDual.ext
  intro z
  obtain ⟨x, rfl⟩ := hq z
  rw [finiteBasisDualSpecialization_eval b c rho q hqScalar hbc,
    RelativeDual.smul_apply, RelativeDual.smul_apply, ← map_mul,
    finiteBasisDualSpecialization_eval b c rho q hqScalar hbc]

theorem finiteBasisDualSpecialization_surjective (hrho : Function.Surjective rho) :
    Function.Surjective (finiteBasisDualSpecialization b c rho) := by
  intro g
  choose lift hlift using hrho
  let f : RelativeDual R C :=
    RelativeDual.ofLinearMap R C (b.constr R (fun i => lift (g (c i))))
  refine ⟨f, ?_⟩
  apply (RelativeDual.linearEquiv K Q).injective
  apply c.ext
  intro i
  change finiteBasisDualSpecialization b c rho f (c i) = g (c i)
  rw [finiteBasisDualSpecialization_basis]
  change rho ((b.constr R (fun i => lift (g (c i)))) (b i)) = g (c i)
  rw [Basis.constr_basis, hlift]

include hqScalar hbc in
/-- Cyclicity descends through the genuine finite-free dual specialization. -/
theorem relativeDual_cyclic_specializes
    (hrho : Function.Surjective rho) (hq : Function.Surjective q)
    (hcyc : ∃ f : RelativeDual R C, Submodule.span C {f} = ⊤) :
    ∃ g : RelativeDual K Q, Submodule.span Q {g} = ⊤ := by
  obtain ⟨f, hf⟩ := hcyc
  refine ⟨finiteBasisDualSpecialization b c rho f,
    (Submodule.span_singleton_eq_top_iff Q _).mpr ?_⟩
  intro g
  obtain ⟨f', hf'⟩ := finiteBasisDualSpecialization_surjective b c rho hrho g
  obtain ⟨a, ha⟩ := (Submodule.span_singleton_eq_top_iff C f).mp hf f'
  refine ⟨q a, ?_⟩
  rw [← finiteBasisDualSpecialization_smul b c rho q hqScalar hbc hq,
    show a • f = f' from ha, hf']

end Specialization

section Head

variable {K Q : Type*} [Field K] [CommRing Q] [Algebra K Q]

theorem augmentation_annihilator_mul
    (eps : Q →ₐ[K] K) (x : idealKilledSubspace (K := K) (RingHom.ker eps)) (a : Q) :
    a * x.val = eps a • x.val := by
  have h := x.property (a - algebraMap K Q (eps a)) (by
    change eps (a - algebraMap K Q (eps a)) = 0
    simp only [map_sub, eps.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
  rw [sub_mul, sub_eq_zero, ← Algebra.smul_def] at h
  exact h

/-- A cyclic dual has an augmentation-annihilator of dimension at most
one.  The annihilator is an actual subspace of the algebra. -/
theorem finrank_augmentation_annihilator_le_one_of_dual_cyclic
    [Module.Finite K Q]
    (eps : Q →ₐ[K] K)
    (hcyc : ∃ f : RelativeDual K Q, Submodule.span Q {f} = ⊤) :
    Module.finrank K (idealKilledSubspace (K := K) (RingHom.ker eps)) ≤ 1 := by
  let T := idealKilledSubspace (K := K) (RingHom.ker eps)
  obtain ⟨f, hf⟩ := hcyc
  let psi : Module.Dual K T := T.dualRestrict (RelativeDual.linearEquiv K Q f)
  have hspan : Submodule.span K {psi} = ⊤ := by
    apply (Submodule.span_singleton_eq_top_iff K psi).mpr
    intro g
    obtain ⟨g', hg'⟩ := Subspace.dualRestrict_surjective (W := T) g
    obtain ⟨a, ha⟩ := (Submodule.span_singleton_eq_top_iff Q f).mp hf
      ((RelativeDual.linearEquiv K Q).symm g')
    refine ⟨eps a, ?_⟩
    ext x
    have hx := congrArg (fun l : RelativeDual K Q => l x.val) ha
    rw [RelativeDual.smul_apply, mul_comm x.val a,
      augmentation_annihilator_mul eps x a, map_smul] at hx
    have hgx : g' x.val = g x := congrArg (fun l : Module.Dual K T => l x) hg'
    change eps a * f x.val = g x
    exact (show eps a * f x.val = g' x.val from hx).trans hgx
  have hdim : Module.finrank K (Module.Dual K T) ≤ 1 := by
    apply finrank_le_of_span_eq_top (v := fun _ : Fin 1 => psi)
    simpa only [Set.range_const, hspan]
  simpa only [Subspace.dual_finrank_eq] using hdim

end Head

end HigherSpecht
end
end CanonicalSource28

section CanonicalSource29
/- Source: HigherSpecht/OriginDualSpecialization.lean -/



/-!
# From the local canonical module to the actual Springer socle

The local relative dual specializes through the genuine parameter basis.
Its closed-fiber map is proved to be compatible with multiplication.
Consequently a local cyclic generator gives a cyclic dual of the actual
Springer fiber, whose socle has the independently proved tableau dimension.
This supplies the necessary type-one consequence of standard local
Gorensteinness, without assuming a Gorenstein--type characterization.
-/

noncomputable section

open TauCeti Module MvPolynomial
open scoped Classical TensorProduct

namespace HigherSpecht

variable (K : Type*) [Field K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def untruncatedOriginFiberMap
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedOriginAlgebra K n lam →+*
      UntruncatedRing K n (adjoinOnes lam (n - lam.card)) :=
  parameterOriginFiberMap (elementaryOriginAugmentation K n lam)
    (specialFiberQuotientMap K n lam hk)
    (fun p => by simpa only [elementaryOriginAugmentation_apply] using
      specialFiberQuotientMap_algebraMap K n lam hk p)

@[simp] theorem untruncatedOriginFiberMap_algebraMap
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (x : UntruncatedRing K n lam) :
    untruncatedOriginFiberMap K n lam hk
      (algebraMap (UntruncatedRing K n lam) (untruncatedOriginAlgebra K n lam) x) =
      specialFiberQuotientMap K n lam hk x :=
  parameterOriginFiberMap_algebraMap _ _ _ x

theorem untruncatedOriginFiberMap_surjective
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Function.Surjective (untruncatedOriginFiberMap K n lam hk) :=
  parameterOriginFiberMap_surjective _ _ _
    (specialFiberQuotientMap_surjective K n lam hk)

theorem untruncatedOriginFiberMap_base
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (r : untruncatedOriginBase K n lam) :
    untruncatedOriginFiberMap K n lam hk
      (algebraMap (untruncatedOriginBase K n lam) (untruncatedOriginAlgebra K n lam) r) =
      algebraMap K _ (parameterOriginResidue (elementaryOriginAugmentation K n lam) r) :=
  parameterOriginFiberMap_base _ _ _ r

def untruncatedOriginBasis (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis (SpecialFiberMonomialIndex n lam) (untruncatedOriginBase K n lam)
      (untruncatedOriginAlgebra K n lam) :=
  (untruncatedMonomialParameterBasis K n lam hk).baseChange (untruncatedOriginBase K n lam)

@[simp] theorem untruncatedOriginFiberMap_basis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : SpecialFiberMonomialIndex n lam) :
    untruncatedOriginFiberMap K n lam hk (untruncatedOriginBasis K n lam hk i) =
      specialFiberCoefficientBasis K n lam hk i := by
  rw [untruncatedOriginBasis, Basis.baseChange_apply]
  change untruncatedOriginFiberMap K n lam hk
    (algebraMap (UntruncatedRing K n lam) (untruncatedOriginAlgebra K n lam)
      (untruncatedMonomialParameterBasis K n lam hk i)) = _
  rw [untruncatedOriginFiberMap_algebraMap, specialFiberQuotientMap_basis]

theorem specialFiberRelativeDual_cyclic_of_origin_cyclic
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hcyc : ∃ f : RelativeDual (untruncatedOriginBase K n lam)
        (untruncatedOriginAlgebra K n lam),
      Submodule.span (untruncatedOriginAlgebra K n lam) {f} = ⊤) :
    ∃ g : RelativeDual K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))),
      Submodule.span (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) {g} = ⊤ := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  exact relativeDual_cyclic_specializes
    (untruncatedOriginBasis K n lam hk) (specialFiberCoefficientBasis K n lam hk)
    (parameterOriginResidue (elementaryOriginAugmentation K n lam))
    (untruncatedOriginFiberMap K n lam hk)
    (untruncatedOriginFiberMap_base K n lam hk)
    (untruncatedOriginFiberMap_basis K n lam hk)
    (parameterOriginResidue_surjective (elementaryOriginAugmentation K n lam))
    (untruncatedOriginFiberMap_surjective K n lam hk) hcyc

theorem untruncatedAugmentation_annihilator
    (n : ℕ) (lam : YoungDiagram) :
    idealKilledSubspace (K := K) (untruncatedOrigin K n lam) =
      (quotientVariableAnnihilator (untruncatedIdeal K n lam)).restrictScalars K := by
  ext z
  constructor
  · intro hz i
    exact hz (Ideal.Quotient.mk _ (MvPolynomial.X i)) (by
      simp only [RingHom.mem_ker, untruncatedAugmentation_mk, MvPolynomial.constantCoeff_X])
  · intro hz a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    change untruncatedAugmentation K n lam (Ideal.Quotient.mk _ p) = 0 at ha
    rw [untruncatedAugmentation_mk] at ha
    rw [quotient_mul_eq_constant_smul_of_variables_annihilate _ hz p, ha, zero_smul]

theorem fullSize_augmentation_annihilator_finrank
    (n : ℕ) (mu : YoungDiagram) (hcard : mu.card = n) :
    Module.finrank K (idealKilledSubspace (K := K) (untruncatedOrigin K n mu)) =
      Fintype.card (StandardYoungTableau mu) := by
  subst n
  rw [untruncatedAugmentation_annihilator]
  have hs := springer_socle_finrank K mu
  rw [springerSocle, quotient_socle_restrictScalars_eq_variableAnnihilator
    (springerIdeal K mu)
    (fun i => ⟨mu.card, springer_coordinate_pow_card_eq_zero mu i⟩)] at hs
  exact hs

/-- The type-one consequence is deduced from actual localization,
Auslander--Buchsbaum, dual specialization, and the actual socle theorem. -/
theorem untruncated_gorenstein_standardTableau_card_eq_one
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hG : IsGorensteinRing (UntruncatedRing K n lam)) :
    Fintype.card (StandardYoungTableau (adjoinOnes lam (n - lam.card))) = 1 := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  letI : Module.Finite K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) :=
    Module.Finite.of_basis (specialFiberCoefficientBasis K n lam hk)
  have hcyc := specialFiberRelativeDual_cyclic_of_origin_cyclic K n lam hk
    (untruncatedOrigin_relativeDual_cyclic_of_gorenstein K n lam hk hG)
  have hd := finrank_augmentation_annihilator_le_one_of_dual_cyclic
    (untruncatedAugmentation K n (adjoinOnes lam (n - lam.card))) hcyc
  rw [fullSize_augmentation_annihilator_finrank K n _
    (by rw [adjoinOnes_card, Nat.add_sub_of_le hk])] at hd
  have hp : 0 < Fintype.card
      (StandardYoungTableau (adjoinOnes lam (n - lam.card))) := Fintype.card_pos
  omega

end HigherSpecht
end
end CanonicalSource29

section CanonicalSource30
/- Source: HigherSpecht/CompleteIntersectionCases.lean -/



/-!
# The actual complete-intersection presentations in Corollary 7.6

For a column of size `k`, the defining sequence is literally
`e_(n-k+1),...,e_n`.  For a full-size row it is literally `x_0,...,x_(n-1)`.
The empty partition is included: its displayed sequence is empty and its
ideal is zero.  The converse classification is a separate socle argument.
-/

noncomputable section

open TauCeti MvPolynomial Finset RingTheory.Sequence
open scoped Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ} {lam : YoungDiagram}

def elementaryTailEmbedding (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Fin lam.card ↪ Fin n where
  toFun i := ⟨n - lam.card + i.val, by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    change n - lam.card + i.val = n - lam.card + j.val at h
    omega

def elementaryTailSequence (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) :
    List (PolynomialRing n R) :=
  List.ofFn (fun i : Fin lam.card => esymm (Fin n) R (n - lam.card + i.val + 1))

theorem conjugateTail_column_of_card_lt (hcolumn : lam.rowLen 0 ≤ 1)
    (hk : lam.card ≤ n) {t : ℕ} (ht : t < n) :
    conjugateTail n lam t = 0 := by
  rw [← columnTail_eq_conjugateTail lam hk]
  exact columnTail_eq_zero_of_width_le lam (by omega)

theorem conjugateTail_univ (hk : lam.card ≤ n) :
    conjugateTail n lam n = lam.card := by
  rw [← columnTail_eq_conjugateTail lam hk, Nat.sub_self, columnTail_zero]

theorem untruncatedIdeal_column_eq_elementaryTail
    (hk : lam.card ≤ n) (hcolumn : lam.rowLen 0 ≤ 1) :
    untruncatedIdeal R n lam = Ideal.ofList (elementaryTailSequence R n lam) := by
  rw [elementaryTailSequence, Ideal.ofList_ofFn]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨Y, d, hd, hdY, hthreshold, rfl⟩
    have hYn : Y.card ≤ n := by simpa using Y.card_le_univ
    have hYeq : Y.card = n := by
      by_contra hne
      have hz := conjugateTail_column_of_card_lt hcolumn hk
        (Nat.lt_of_le_of_ne hYn hne)
      rw [hz, Nat.cast_zero, sub_zero] at hthreshold
      omega
    have hY : Y = Finset.univ := Y.eq_univ_of_card (by simpa using hYeq)
    subst Y
    simp only [card_univ, Fintype.card_fin, conjugateTail_univ hk] at hdY hthreshold
    have hsmall : n - lam.card < d := by omega
    let i : Fin lam.card := ⟨d - (n - lam.card) - 1, by omega⟩
    apply Ideal.subset_span
    refine ⟨i, ?_⟩
    have hdegree : n - lam.card + i.val + 1 = d := by
      dsimp only [i]
      omega
    change esymm (Fin n) R (n - lam.card + i.val + 1) =
      elementaryOn (Finset.univ : Finset (Fin n)) d
    rw [elementaryOn_univ, hdegree]
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    apply elementaryOn_mem_untruncatedIdeal Finset.univ
      (Nat.zero_lt_succ _) (by simp only [card_univ, Fintype.card_fin]; omega)
    simp only [card_univ, Fintype.card_fin, conjugateTail_univ hk]
    have hi := i.isLt
    omega

theorem elementaryTailSequence_isRegular [IsDomain R]
    (hk : lam.card ≤ n) :
    IsRegular (PolynomialRing n R) (elementaryTailSequence R n lam) := by
  simpa only [elementaryTailSequence, elementaryTailEmbedding,
    Function.Embedding.coeFn_mk] using
    selectedElementary_isRegular R (elementaryTailEmbedding n lam hk)

/-- The complete-intersection direction for every column, including the
empty shape, in every characteristic. -/
theorem untruncated_regularSequencePresentation_of_column [IsDomain R]
    (hk : lam.card ≤ n) (hcolumn : lam.rowLen 0 ≤ 1) :
    IsRegularSequencePresentation (untruncatedIdeal R n lam) :=
  ⟨elementaryTailSequence R n lam, elementaryTailSequence_isRegular hk,
    (untruncatedIdeal_column_eq_elementaryTail hk hcolumn).symm⟩

theorem untruncatedIdeal_full_row_eq_variableIdeal
    (hcard : lam.card = n) (hrow : lam.colLen 0 ≤ 1) :
    untruncatedIdeal R n lam =
      Ideal.ofList (List.ofFn (MvPolynomial.X : Fin n → PolynomialRing n R)) := by
  rw [← blockSpringerIdeal_univ lam hcard.le,
    blockSpringerIdeal_eq_coordinate_of_one_row Finset.univ
      (by simpa only [card_univ, Fintype.card_fin] using hcard.symm) hrow,
    Ideal.ofList_ofFn]
  unfold coordinateIdeal
  congr 1
  ext p
  simp only [Finset.coe_univ, Set.image_univ, Set.mem_range]

theorem untruncated_regularSequencePresentation_of_full_row [IsDomain R]
    (hcard : lam.card = n) (hrow : lam.colLen 0 ≤ 1) :
    IsRegularSequencePresentation (untruncatedIdeal R n lam) := by
  refine ⟨List.ofFn (MvPolynomial.X : Fin n → PolynomialRing n R), ?_,
    (untruncatedIdeal_full_row_eq_variableIdeal hcard hrow).symm⟩
  exact selectedPolynomialVariables_isRegular R (Function.Embedding.refl (Fin n))

theorem corollary_7_6_completeIntersection_sufficiency [IsDomain R]
    (hk : lam.card ≤ n)
    (hshape : lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1) :
    IsRegularSequencePresentation (untruncatedIdeal R n lam) := by
  rcases hshape with hcolumn | ⟨hcard, hrow⟩
  · exact untruncated_regularSequencePresentation_of_column hk hcolumn
  · exact untruncated_regularSequencePresentation_of_full_row hcard hrow

end HigherSpecht
end
end CanonicalSource30

section CanonicalSource31
/- Source: HigherSpecht/CoordinateKoszulZero.lean -/



/-! Zeroth coordinate Koszul homology is the literal augmentation field. -/

noncomputable section

open MvPolynomial Module Finset
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

def quotientConstantAugmentation (I : Ideal (PolynomialRing n K))
    (hI : I ≤ RingHom.ker constantCoeff) : PolynomialRing n K ⧸ I →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval fun _ : Fin n => (0 : K)) (by
    intro p hp
    simpa only [RingHom.mem_ker, MvPolynomial.aeval_zero', Algebra.algebraMap_self, RingHom.id_apply]
      using hI hp)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem quotientConstantAugmentation_mk (I : Ideal (PolynomialRing n K))
    (hI : I ≤ RingHom.ker constantCoeff) (p : PolynomialRing n K) :
    quotientConstantAugmentation I hI (Ideal.Quotient.mk I p) = constantCoeff p := by
  change (MvPolynomial.aeval fun _ : Fin n => (0 : K)) p = constantCoeff p
  simp only [MvPolynomial.aeval_zero', Algebra.algebraMap_self, RingHom.id_apply]

def coordinateAugmentationCoefficient (I : Ideal (PolynomialRing n K))
    (hI : I ≤ RingHom.ker constantCoeff) : CoordinateKoszulCarrier I →ₗ[K] K :=
  (quotientConstantAugmentation I hI).toLinearMap.comp
    (((coordinateKoszulBasis I).coord ∅).restrictScalars K)

@[simp] theorem coordinateAugmentationCoefficient_smul
    (I : Ideal (PolynomialRing n K)) (hI : I ≤ RingHom.ker constantCoeff)
    (c : PolynomialRing n K ⧸ I) (z : CoordinateKoszulCarrier I) :
    coordinateAugmentationCoefficient I hI (c • z) =
      quotientConstantAugmentation I hI c * coordinateAugmentationCoefficient I hI z := by
  simp only [coordinateAugmentationCoefficient, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Basis.coord_apply, map_smul,
    Finsupp.smul_apply, smul_eq_mul, AlgHom.toLinearMap_apply, map_mul]

@[simp] theorem coordinateAugmentationCoefficient_empty
    (I : Ideal (PolynomialRing n K)) (hI : I ≤ RingHom.ker constantCoeff) :
    coordinateAugmentationCoefficient I hI (coordinateKoszulBasis I ∅) = 1 := by
  simp only [coordinateAugmentationCoefficient, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Basis.coord_apply, Basis.repr_self,
    Finsupp.single_eq_same, AlgHom.toLinearMap_apply, map_one]

theorem coordinateAugmentationCoefficient_differential
    (I : Ideal (PolynomialRing n K)) (hI : I ≤ RingHom.ker constantCoeff)
    (z : CoordinateKoszulCarrier I) :
    coordinateAugmentationCoefficient I hI (coordinateKoszulDifferential I z) = 0 := by
  rw [← (coordinateKoszulBasis I).sum_repr z]
  simp only [map_sum, coordinateKoszulDifferential_smul,
    coordinateAugmentationCoefficient_smul]
  apply Finset.sum_eq_zero
  intro s hs
  rw [coordinateKoszulDifferential_basis, map_sum]
  have hz : (∑ j : Fin n, coordinateAugmentationCoefficient I hI
      (if j ∈ s then Ideal.Quotient.mk I (X j) •
        (TauCeti.ExteriorAlgebra.basisEraseSign j s • coordinateKoszulBasis I (s.erase j))
      else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs <;> simp only [coordinateAugmentationCoefficient_smul,
      quotientConstantAugmentation_mk, constantCoeff_X, zero_mul, map_zero]
  rw [hz, mul_zero]

@[simp] theorem coordinateKoszulDifferential_empty (I : Ideal (PolynomialRing n K)) :
    coordinateKoszulDifferential I (coordinateKoszulBasis I ∅) = 0 := by
  rw [coordinateKoszulDifferential_basis]
  simp only [Finset.notMem_empty, if_false, Finset.sum_const_zero]

set_option backward.isDefEq.respectTransparency false in
def constantCoordinateCycles (I : Ideal (PolynomialRing n K)) :
    K →ₗ[K] (coordinateDifferentialGrading I).cycles 0 :=
  (LinearMap.toSpanSingleton K (CoordinateKoszulCarrier I)
    (coordinateKoszulBasis I ∅)).codRestrict _ (fun c => by
      refine ⟨?_, ?_⟩
      · apply (coordinateHomologicalPiece I 0).smul_mem c
        have hgen := coordinateHomologicalPiece_generator I ∅
          (by simp : (↑(∅ : Finset (Fin n)).card : ℤ) = 0)
          (1 : PolynomialRing n K ⧸ I)
        have hunit : (1 : PolynomialRing n K ⧸ I) • coordinateKoszulBasis I ∅ =
            coordinateKoszulBasis I ∅ :=
          one_smul (PolynomialRing n K ⧸ I) (coordinateKoszulBasis I ∅)
        exact hunit ▸ hgen
      · change coordinateKoszulDifferential I (c • coordinateKoszulBasis I ∅) = 0
        rw [map_smul, coordinateKoszulDifferential_empty, smul_zero])

def constantCoordinateHomology (I : Ideal (PolynomialRing n K)) :
    K →ₗ[K] TotalCoordinateKoszulHomology I 0 :=
  ((coordinateDifferentialGrading I).homologyClass 0).comp (constantCoordinateCycles I)

set_option backward.isDefEq.respectTransparency false in
theorem constantCoordinateHomology_injective (I : Ideal (PolynomialRing n K))
    (hI : I ≤ RingHom.ker constantCoeff) : Function.Injective (constantCoordinateHomology I) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro c hc
  have hc' := ((coordinateDifferentialGrading I).homologyClass_eq_zero_iff 0
    (constantCoordinateCycles I c)).mp hc
  obtain ⟨y, hy, hdy⟩ := hc'
  have h := coordinateAugmentationCoefficient_differential I hI y
  change coordinateKoszulDifferential I y = (constantCoordinateCycles I c).val at hdy
  rw [hdy] at h
  change coordinateAugmentationCoefficient I hI
    (c • coordinateKoszulBasis I ∅) = 0 at h
  rw [map_smul, coordinateAugmentationCoefficient_empty, smul_eq_mul, mul_one] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem constantCoordinateHomology_surjective (I : Ideal (PolynomialRing n K)) :
    Function.Surjective (constantCoordinateHomology I) := by
  intro z
  obtain ⟨z, rfl⟩ := (((coordinateDifferentialGrading I).boundaries 0).comap
    ((coordinateDifferentialGrading I).cycles 0).subtype).mkQ_surjective z
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective ((coordinateKoszulBasis I).repr z.val ∅)
  have hrep : z.val = Ideal.Quotient.mk I p • coordinateKoszulBasis I ∅ := by
    rw [hp]
    exact coordinateHomologicalPiece_zero_repr I z.property.1
  let f := p - MvPolynomial.C (constantCoeff p)
  have hf : constantCoeff f = 0 := by simp only [f, map_sub, constantCoeff_C, sub_self]
  obtain ⟨g, hg⟩ := constantCoeff_zero_eq_sum_variables hf
  let y := coordinateKoszulHomotopy I g (coordinateKoszulBasis I ∅)
  have hy : y ∈ coordinateHomologicalPiece I 1 := by
    have hb : coordinateKoszulBasis I ∅ ∈ coordinateHomologicalPiece I 0 := by
      have hgen := coordinateHomologicalPiece_generator I ∅
        (by simp : (↑(∅ : Finset (Fin n)).card : ℤ) = 0)
        (1 : PolynomialRing n K ⧸ I)
      have hunit : (1 : PolynomialRing n K ⧸ I) • coordinateKoszulBasis I ∅ =
          coordinateKoszulBasis I ∅ :=
        one_smul (PolynomialRing n K ⧸ I) (coordinateKoszulBasis I ∅)
      exact hunit ▸ hgen
    have hy' := coordinateHomologicalHomotopy_mem I g (i := 0)
      (z := coordinateKoszulBasis I ∅) hb
    simpa only [zero_add] using hy' 
  have hdy : coordinateKoszulDifferential I y =
      z.val - (constantCoeff p) • coordinateKoszulBasis I ∅ := by
    have h := coordinateKoszulHomotopy_identity I hg (coordinateKoszulBasis I ∅)
    rw [coordinateKoszulDifferential_empty, map_zero, add_zero,
      coordinateKoszulScalar_apply] at h
    rw [h, hrep]
    simp only [f, map_sub]
    rw [sub_smul (Ideal.Quotient.mk I p)
      (Ideal.Quotient.mk I (MvPolynomial.C (constantCoeff p)))
      (coordinateKoszulBasis I ∅)]
    have hc : Ideal.Quotient.mk I (MvPolynomial.C (constantCoeff p)) =
        algebraMap K (PolynomialRing n K ⧸ I) (constantCoeff p) :=
      (Ideal.Quotient.mkₐ K I).commutes (constantCoeff p)
    have hcsmul : Ideal.Quotient.mk I (MvPolynomial.C (constantCoeff p)) •
        coordinateKoszulBasis I ∅ = (constantCoeff p) • coordinateKoszulBasis I ∅ :=
      (congrArg (fun a : PolynomialRing n K ⧸ I => a • coordinateKoszulBasis I ∅) hc).trans
        (IsScalarTower.algebraMap_smul (PolynomialRing n K ⧸ I)
          (constantCoeff p) (coordinateKoszulBasis I ∅))
    exact congrArg
      (fun w : CoordinateKoszulCarrier I => Ideal.Quotient.mk I p • coordinateKoszulBasis I ∅ - w)
      hcsmul
  refine ⟨constantCoeff p, ?_⟩
  symm
  change (coordinateDifferentialGrading I).homologyClass 0 z =
    (coordinateDifferentialGrading I).homologyClass 0 (constantCoordinateCycles I (constantCoeff p))
  rw [← sub_eq_zero, ← map_sub,
    (coordinateDifferentialGrading I).homologyClass_eq_zero_iff]
  exact ⟨y, hy, hdy⟩

def totalCoordinateZeroHomologyEquiv (I : Ideal (PolynomialRing n K))
    (hI : I ≤ RingHom.ker constantCoeff) :
    K ≃ₗ[K] TotalCoordinateKoszulHomology I 0 :=
  LinearEquiv.ofBijective (constantCoordinateHomology I)
    ⟨constantCoordinateHomology_injective I hI, constantCoordinateHomology_surjective I⟩

end HigherSpecht
end
end CanonicalSource31

section CanonicalSource32
/- Source: HigherSpecht/RegularSequenceKoszulBetti.lean -/



/-!
# The actual coordinate Koszul homology of a regular quotient

Adjoining a regular polynomial with zero constant coefficient doubles
homology by the explicit null-homotopy splitting.  Induction gives the
binomial Betti numbers for every regular list, without a homogeneity
assumption.  Top exterior degree then implies that any such quotient
with nonzero coordinate annihilator has one-dimensional annihilator.
-/

noncomputable section

open Module MvPolynomial RingTheory.Sequence
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

theorem regularSequence_next_injective
    (xs : List (PolynomialRing n K))
    (hreg : IsWeaklyRegular (PolynomialRing n K) xs)
    (k : ℕ) (hk : k < xs.length) :
    Function.Injective (fun c : PolynomialRing n K ⧸ Ideal.ofList (xs.take k) =>
      Ideal.Quotient.mk (Ideal.ofList (xs.take k)) xs[k] * c) := by
  have h := hreg.regular_mod_prev k hk
  have htop : (Ideal.ofList (xs.take k) •
      (⊤ : Submodule (PolynomialRing n K) (PolynomialRing n K))) =
      Ideal.ofList (xs.take k) := by
    change Ideal.ofList (xs.take k) * ⊤ = _
    exact Ideal.mul_top _
  rw [htop] at h
  exact h

theorem coordinateKoszul_regular_prefix_betti
    (xs : List (PolynomialRing n K))
    (hreg : IsWeaklyRegular (PolynomialRing n K) xs)
    (hzero : ∀ f ∈ xs, constantCoeff f = 0)
    (k : ℕ) (hk : k ≤ xs.length) :
    (∀ i : ℤ, FiniteDimensional K
      (TotalCoordinateKoszulHomology (Ideal.ofList (xs.take k)) i)) ∧
      ∀ q : ℕ, Module.finrank K
        (TotalCoordinateKoszulHomology (Ideal.ofList (xs.take k)) (q : ℤ)) = k.choose q := by
  induction k with
  | zero =>
    let P (I : Ideal (PolynomialRing n K)) : Prop :=
      (∀ i : ℤ, FiniteDimensional K (TotalCoordinateKoszulHomology I i)) ∧
        ∀ q : ℕ, Module.finrank K (TotalCoordinateKoszulHomology I (q : ℤ)) =
          (0 : ℕ).choose q
    have hbot : P ⊥ := by
      have hf : ∀ i : ℤ, FiniteDimensional K
          (TotalCoordinateKoszulHomology (⊥ : Ideal (PolynomialRing n K)) i) := by
        intro i
        by_cases hi : i < 0
        · letI := totalCoordinateKoszulHomology_subsingleton_of_outside
            (⊥ : Ideal (PolynomialRing n K)) (Or.inl hi)
          infer_instance
        · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hi)
          cases q with
          | zero =>
            exact Module.Finite.equiv
              (totalCoordinateZeroHomologyEquiv (⊥ : Ideal (PolynomialRing n K)) bot_le)
          | succ q =>
            letI := totalCoordinateKoszulHomology_bot_succ_subsingleton (K := K) (n := n) q
            infer_instance
      refine ⟨hf, ?_⟩
      intro q
      cases q with
      | zero =>
        let Z (i : ℤ) : Prop := Module.finrank K
          (TotalCoordinateKoszulHomology (⊥ : Ideal (PolynomialRing n K)) i) = 1
        have hz : Z 0 :=
          (totalCoordinateZeroHomologyEquiv
            (⊥ : Ideal (PolynomialRing n K)) bot_le).finrank_eq.symm.trans
              (Module.finrank_self K)
        have hcast : ((0 : ℕ) : ℤ) = 0 := rfl
        have hz' : Z ((0 : ℕ) : ℤ) := (congrArg Z hcast).mpr hz
        simpa only [Nat.choose_zero_right] using hz' 
      | succ q =>
        letI := totalCoordinateKoszulHomology_bot_succ_subsingleton (K := K) (n := n) q
        rw [Module.finrank_zero_of_subsingleton, Nat.choose_eq_zero_of_lt (by omega)]
    have hI : Ideal.ofList (xs.take 0) = (⊥ : Ideal (PolynomialRing n K)) := by
      simp only [List.take_zero, Ideal.ofList_nil]
    exact (congrArg P hI).mpr hbot
  | succ k ih =>
    have hkl : k < xs.length := by omega
    obtain ⟨hfinite, hdim⟩ := ih (by omega)
    let I := Ideal.ofList (xs.take k)
    let f := xs[k]
    let Q := regularCoordinateHomologicalQuotient I f
      (hzero f (List.getElem_mem hkl)) (regularSequence_next_injective xs hreg k hkl)
    have hideal : Ideal.ofList (xs.take (k + 1)) = adjoinHomogeneousElement I f := by
      rw [List.take_succ_eq_append_getElem hkl, Ideal.ofList_append,
        Ideal.ofList_singleton]
      rfl
    let P (J : Ideal (PolynomialRing n K)) : Prop :=
      (∀ i : ℤ, FiniteDimensional K (TotalCoordinateKoszulHomology J i)) ∧
        ∀ q : ℕ, Module.finrank K (TotalCoordinateKoszulHomology J (q : ℤ)) =
          (k + 1).choose q
    change P (Ideal.ofList (xs.take (k + 1)))
    apply (congrArg P hideal).mpr
    have hf : ∀ i : ℤ, FiniteDimensional K
        (TotalCoordinateKoszulHomology (adjoinHomogeneousElement I f) i) := by
      intro i
      letI := hfinite i
      letI := hfinite (i - 1)
      exact Module.Finite.equiv (Q.homologyEquiv i)
    refine ⟨hf, ?_⟩
    intro q
    letI := hfinite (q : ℤ)
    letI := hfinite ((q : ℤ) - 1)
    rw [Q.finrank_homology (q : ℤ)]
    cases q with
    | zero =>
      letI := totalCoordinateKoszulHomology_subsingleton_of_outside I
        (Or.inl (by norm_num : (0 : ℤ) - 1 < 0))
      rw [hdim 0, Module.finrank_zero_of_subsingleton, add_zero,
        Nat.choose_zero_right, Nat.choose_zero_right]
    | succ q =>
      rw [show ((q + 1 : ℕ) : ℤ) - 1 = (q : ℤ) by omega,
        hdim (q + 1), hdim q, Nat.choose_succ_succ', Nat.add_comm]

theorem coordinateKoszul_regularSequence_betti
    (xs : List (PolynomialRing n K))
    (hreg : IsWeaklyRegular (PolynomialRing n K) xs)
    (hzero : ∀ f ∈ xs, constantCoeff f = 0) :
    (∀ i : ℤ, FiniteDimensional K
      (TotalCoordinateKoszulHomology (Ideal.ofList xs) i)) ∧
      ∀ q : ℕ, Module.finrank K
        (TotalCoordinateKoszulHomology (Ideal.ofList xs) (q : ℤ)) = xs.length.choose q := by
  let P (I : Ideal (PolynomialRing n K)) : Prop :=
    (∀ i : ℤ, FiniteDimensional K (TotalCoordinateKoszulHomology I i)) ∧
      ∀ q : ℕ, Module.finrank K (TotalCoordinateKoszulHomology I (q : ℤ)) =
        xs.length.choose q
  have h : P (Ideal.ofList (xs.take xs.length)) :=
    coordinateKoszul_regular_prefix_betti xs hreg hzero xs.length le_rfl
  have hI : Ideal.ofList (xs.take xs.length) = Ideal.ofList xs := by
    rw [List.take_length]
  exact (congrArg P hI).mp h

theorem regularSequence_length_le_number_variables
    (xs : List (PolynomialRing n K))
    (hreg : IsWeaklyRegular (PolynomialRing n K) xs)
    (hzero : ∀ f ∈ xs, constantCoeff f = 0) : xs.length ≤ n := by
  have hdim := (coordinateKoszul_regularSequence_betti xs hreg hzero).2 xs.length
  by_contra h
  letI := totalCoordinateKoszulHomology_subsingleton_of_outside (Ideal.ofList xs)
    (i := (xs.length : ℤ)) (Or.inr (by exact_mod_cast Nat.lt_of_not_ge h))
  rw [Module.finrank_zero_of_subsingleton, Nat.choose_self] at hdim
  exact (Nat.zero_ne_one hdim)

/-- An arbitrary regular defining sequence with a nonzero top Koszul
annihilator has exactly n members, and that actual annihilator has
dimension one.  No homogeneity, chosen basis, or socle-dimension premise
equal to the conclusion is introduced. -/
theorem regularSequence_variableAnnihilator_finrank_one
    (xs : List (PolynomialRing n K))
    (hreg : IsWeaklyRegular (PolynomialRing n K) xs)
    (hzero : ∀ f ∈ xs, constantCoeff f = 0)
    (hpos : 0 < Module.finrank K
      ((quotientVariableAnnihilator (Ideal.ofList xs)).restrictScalars K)) :
    xs.length = n ∧ Module.finrank K
      ((quotientVariableAnnihilator (Ideal.ofList xs)).restrictScalars K) = 1 := by
  obtain ⟨hfinite, hdim⟩ := coordinateKoszul_regularSequence_betti xs hreg hzero
  have htop : Module.finrank K
      ((quotientVariableAnnihilator (Ideal.ofList xs)).restrictScalars K) =
      xs.length.choose n := by
    rw [← (totalCoordinateTopHomologyEquiv (Ideal.ofList xs)).finrank_eq, hdim n]
  have hle := regularSequence_length_le_number_variables xs hreg hzero
  have hge : n ≤ xs.length := by
    by_contra h
    rw [htop, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)] at hpos
    exact (Nat.lt_irrefl 0) hpos
  have heq : xs.length = n := Nat.le_antisymm hle hge
  exact ⟨heq, by rw [htop, heq, Nat.choose_self]⟩

theorem regularSequencePresentation_variableAnnihilator_finrank_one
    (I : Ideal (PolynomialRing n K)) (hI : I ≤ RingHom.ker constantCoeff)
    (hci : IsRegularSequencePresentation I)
    (hpos : 0 < Module.finrank K ((quotientVariableAnnihilator I).restrictScalars K)) :
    Module.finrank K ((quotientVariableAnnihilator I).restrictScalars K) = 1 := by
  obtain ⟨xs, hreg, hxs⟩ := hci
  have hzero : ∀ f ∈ xs, constantCoeff f = 0 := by
    intro f hf
    exact hI (hxs ▸ Ideal.subset_span hf)
  rw [← hxs] at hpos ⊢
  exact (regularSequence_variableAnnihilator_finrank_one xs hreg.1 hzero hpos).2

end HigherSpecht
end
end CanonicalSource32

section CanonicalSource33
/- Source: HigherSpecht/CompleteIntersectionClassification.lean -/



/-!
# The complete-intersection classification in Corollary 7.6

The reverse implication starts with an arbitrary actual regular defining
sequence.  The actual regular elementary parameters are appended, giving
the Springer special fiber.  Its coordinate Koszul top homology has
dimension one by the proved regular-quotient splitting, and the separately
proved Springer socle formula forces a row or a column.  No homogeneous
defining-sequence assumption is imposed.
-/

noncomputable section

open TauCeti Module MvPolynomial RingTheory.Sequence
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ} {lam : YoungDiagram}

theorem regularSequencePresentation_adjoin
    (I : Ideal (PolynomialRing n K)) (hI : I ≤ RingHom.ker constantCoeff)
    (hci : IsRegularSequencePresentation I) (ys : List (PolynomialRing n K))
    (hy : IsWeaklyRegular (PolynomialRing n K ⧸ I) (ys.map (Ideal.Quotient.mk I)))
    (hzero : ∀ y ∈ ys, constantCoeff y = 0) :
    IsRegularSequencePresentation (I ⊔ Ideal.ofList ys) := by
  obtain ⟨xs, hx, hxs⟩ := hci
  let W (J : Submodule (PolynomialRing n K) (PolynomialRing n K)) : Prop :=
    IsWeaklyRegular (PolynomialRing n K ⧸ J) ys
  have hyR : W I :=
    (isWeaklyRegular_map_algebraMap_iff (PolynomialRing n K ⧸ I)
      (PolynomialRing n K ⧸ I) ys).mp hy
  have htop : (Ideal.ofList xs •
      (⊤ : Submodule (PolynomialRing n K) (PolynomialRing n K))) = I := by
    change Ideal.ofList xs * ⊤ = I
    rw [Ideal.mul_top, hxs]
  have hy' : W (Ideal.ofList xs •
      (⊤ : Submodule (PolynomialRing n K) (PolynomialRing n K))) :=
    (congrArg W htop).mpr hyR
  have hweak : IsWeaklyRegular (PolynomialRing n K) (xs ++ ys) :=
    (isWeaklyRegular_append_iff (PolynomialRing n K) xs ys).mpr ⟨hx.1, hy'⟩
  refine ⟨xs ++ ys, polynomialSequence_isRegular_of_constantCoeff_zero K _ hweak ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hI (hxs ▸ Ideal.subset_span hp)
    · exact hzero p hp
  · rw [Ideal.ofList_append, hxs]

theorem specialFiber_regularSequencePresentation
    (hk : lam.card ≤ n)
    (hci : IsRegularSequencePresentation (untruncatedIdeal K n lam)) :
    IsRegularSequencePresentation (untruncatedIdeal K n (adjoinOnes lam (n - lam.card))) := by
  let m := n - lam.card
  have hideal : untruncatedIdeal K n (adjoinOnes lam m) =
      untruncatedIdeal K n lam ⊔ elementaryParameterIdeal K n m := by
    have h := specialFiberIdeal_eq (R := K) lam m
    have hsize : lam.card + m = n := Nat.add_sub_of_le hk
    rwa [hsize] at h
  rw [hideal]
  have hp : Ideal.ofList (elementaryParameterSequence K n m) =
      elementaryParameterIdeal K n m := by
    have h := elementaryParameterSequence_prefix_ideal (K := K) (n := n) m m le_rfl
    have ht : (elementaryParameterSequence K n m).take m = elementaryParameterSequence K n m :=
      List.take_of_length_le (by simp only [elementaryParameterSequence_length, le_refl])
    rwa [ht] at h
  rw [← hp]
  apply regularSequencePresentation_adjoin _ (untruncatedIdeal_le_constantCoeff_ker n lam)
    hci _ (untruncated_elementarySequence_isWeaklyRegular K n lam hk)
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact constantCoeff_elementaryOn Finset.univ (Nat.zero_lt_succ i.val)

theorem fullSize_variableAnnihilator_finrank (K : Type*) [Field K]
    (n : ℕ) (mu : YoungDiagram) (hcard : mu.card = n) :
    Module.finrank K ((quotientVariableAnnihilator (untruncatedIdeal K n mu)).restrictScalars K) =
      Fintype.card (StandardYoungTableau mu) := by
  subst n
  have hs : springerSocle K mu =
      (quotientVariableAnnihilator (springerIdeal K mu)).restrictScalars K :=
    quotient_socle_restrictScalars_eq_variableAnnihilator (springerIdeal K mu)
      (fun i => ⟨mu.card, springer_coordinate_pow_card_eq_zero mu i⟩)
  rw [show untruncatedIdeal K mu.card mu = springerIdeal K mu from rfl, ← hs]
  exact springer_socle_finrank K mu

theorem standardCount_adjoinOnes_eq_one_of_regularSequencePresentation
    (hk : lam.card ≤ n)
    (hci : IsRegularSequencePresentation (untruncatedIdeal K n lam)) :
    standardCount (adjoinOnes lam (n - lam.card)) = 1 := by
  let mu := adjoinOnes lam (n - lam.card)
  have hcard : mu.card = n := by
    rw [adjoinOnes_card, Nat.add_sub_of_le hk]
  have hdim := fullSize_variableAnnihilator_finrank K n mu hcard
  have hpos : 0 < Module.finrank K
      ((quotientVariableAnnihilator (untruncatedIdeal K n mu)).restrictScalars K) := by
    rw [hdim]
    exact Fintype.card_pos
  have hone := regularSequencePresentation_variableAnnihilator_finrank_one
    (untruncatedIdeal K n mu) (untruncatedIdeal_le_constantCoeff_ker n mu)
    (specialFiber_regularSequencePresentation hk hci) hpos
  rw [hdim] at hone
  simpa only [standardCount_def] using hone

theorem adjoinOnes_extremeShape_iff (hk : lam.card ≤ n) :
    (adjoinOnes lam (n - lam.card)).rowLen 0 ≤ 1 ∨
        (adjoinOnes lam (n - lam.card)).colLen 0 ≤ 1 ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1 := by
  constructor
  · rintro (hcolumn | hrow)
    · exact Or.inl ((YoungDiagram.rowLen_le_of_le (le_adjoinOnes lam (n - lam.card)) 0).trans
        hcolumn)
    · by_cases hcolumn : lam.rowLen 0 ≤ 1
      · exact Or.inl hcolumn
      · have hpos : 0 < lam.colLen 0 := by
          have hcell : (0, 0) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
          exact YoungDiagram.mem_iff_lt_colLen.mp hcell
        rw [adjoinOnes_colLen_zero] at hrow
        exact Or.inr ⟨by omega, by omega⟩
  · rintro (hcolumn | ⟨hcard, hrow⟩)
    · left
      rw [adjoinOnes_rowLen]
      split_ifs <;> omega
    · right
      rw [adjoinOnes_colLen_zero, hcard, Nat.sub_self, add_zero]
      exact hrow

/-- The exact complete-intersection clause of Corollary 7.6. The left
side is an actual regular-sequence presentation in the original ambient
polynomial ring. Both directions retain all fields and the empty cases. -/
theorem corollary_7_6_completeIntersection_iff (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsRegularSequencePresentation (untruncatedIdeal K n lam) ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1 := by
  constructor
  · intro hci
    apply (adjoinOnes_extremeShape_iff hk).mp
    exact standardCount_eq_one_iff.mp
      (standardCount_adjoinOnes_eq_one_of_regularSequencePresentation hk hci)
  · exact corollary_7_6_completeIntersection_sufficiency hk

theorem corollary_7_6_completeIntersection_iff_enlargedShape
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsRegularSequencePresentation (untruncatedIdeal K n lam) ↔
      (adjoinOnes lam (n - lam.card)).rowLen 0 ≤ 1 ∨
        (adjoinOnes lam (n - lam.card)).colLen 0 ≤ 1 :=
  (corollary_7_6_completeIntersection_iff K n lam hk).trans
    (adjoinOnes_extremeShape_iff hk).symm

end HigherSpecht
end
end CanonicalSource33

section CanonicalSource34
/- Source: HigherSpecht/GorensteinClassification.lean -/



/-!
# The standard Gorenstein classification in Corollary 7.6

The left side is the ordinary Noetherian, local finite
self-injective-dimension condition.  Necessity passes through the
actual origin localization and the actual Springer socle.  Sufficiency
uses a genuine cyclic generator of the proved dualizing module.
-/

noncomputable section

open TauCeti Module

namespace HigherSpecht

variable (K : Type*) [Field K]

theorem untruncated_isGorenstein_iff_one_standard_tableau
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsGorensteinRing (UntruncatedRing K n lam) ↔
      Fintype.card (StandardYoungTableau (adjoinOnes lam (n - lam.card))) = 1 :=
  ⟨untruncated_gorenstein_standardTableau_card_eq_one K n lam hk,
    untruncated_isGorenstein_of_one_standard_tableau K n lam hk⟩

/-- The row/column criterion retains all coefficient fields, the empty
diagram, and the case with no elementary parameters. -/
theorem corollary_7_6_gorenstein_iff_enlargedShape
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsGorensteinRing (UntruncatedRing K n lam) ↔
      (adjoinOnes lam (n - lam.card)).rowLen 0 ≤ 1 ∨
        (adjoinOnes lam (n - lam.card)).colLen 0 ≤ 1 := by
  rw [untruncated_isGorenstein_iff_one_standard_tableau K n lam hk,
    ← standardCount_def]
  exact standardCount_eq_one_iff

theorem corollary_7_6_gorenstein_iff
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsGorensteinRing (UntruncatedRing K n lam) ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1 :=
  (corollary_7_6_gorenstein_iff_enlargedShape K n lam hk).trans
    (adjoinOnes_extremeShape_iff hk)

/-- The two conditions are equivalent for these actual quotient rings;
neither side is defined by the shape criterion. -/
theorem corollary_7_6_gorenstein_iff_completeIntersection
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsGorensteinRing (UntruncatedRing K n lam) ↔
      IsRegularSequencePresentation (untruncatedIdeal K n lam) :=
  (corollary_7_6_gorenstein_iff K n lam hk).trans
    (corollary_7_6_completeIntersection_iff K n lam hk).symm

end HigherSpecht
end
end CanonicalSource34

section CanonicalSource1000
/- Source: HigherSpecht/AdmissibleParameterBasis.lean -/



/-!
# The coefficient extension of the prescribed parameter basis

Remark 6.2 concerns the unchanged, unnormalized higher Specht representatives.
The finite prescribed Griffin bases give the full untruncated vector basis by
degreewise stabilization. Expanding the elementary-parameter monomial basis
then proves independence over the actual parameter ring, and the already
proved span transfer proves spanning over that ring.

The final statements have no finite-basis premise. They cover every good-
characteristic field, the exact localization `ℤ[1/n!]`, and, more generally,
every nontrivial commutative ring in which `n!` is a unit. The actual one-row
member proves the necessity of the stated field-characteristic condition.
-/

noncomputable section

open TauCeti Module MvPolynomial

namespace HigherSpecht

theorem untruncatedFamily_linearIndependent_parameters_of_vector_independence
    (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hv : LinearIndependent R (untruncatedVectorFamily R n lam hk)) :
    LinearIndependent (ElementaryParameterRing R n lam)
      (untruncatedFamily R n lam hk) := by
  apply linearIndependent_scalarRing_of_expansion
    (MvPolynomial.basisMonomials (Fin (n - lam.card)) R)
  have h := hv.comp parameterVectorIndex parameterVectorIndex_injective
  simpa only [MvPolynomial.coe_basisMonomials, parameter_monomial_smul,
    Function.comp_def] using h

/-- The generic stabilization-to-parameter-basis transfer. The following
unconditional endpoints instantiate its finite-basis input with proved bases. -/
def untruncatedParameterBasisFromAnyFiniteBases
    (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := R) (griffinFamily R n lam hk s)) :
    Basis (UntruncatedIndex n lam hk) (ElementaryParameterRing R n lam)
      (UntruncatedRing R n lam) := by
  let B := untruncatedVectorBasisFromAnyFiniteBases R n lam hk hb
  have hB : (B : UntruncatedVectorIndex n lam hk → UntruncatedRing R n lam) =
      untruncatedVectorFamily R n lam hk :=
    funext (untruncatedVectorBasisFromAnyFiniteBases_apply R n lam hk hb)
  apply Basis.mk
  · apply untruncatedFamily_linearIndependent_parameters_of_vector_independence R n lam hk
    simpa only [← hB] using B.linearIndependent
  · exact untruncatedFamily_spans_parameters_of_vector_span R n lam hk
      (untruncatedVectorFamily_spans_of_finite_bases R n lam hk hb)

@[simp] theorem untruncatedParameterBasisFromAnyFiniteBases_apply
    (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := R) (griffinFamily R n lam hk s))
    (i : UntruncatedIndex n lam hk) :
    untruncatedParameterBasisFromAnyFiniteBases R n lam hk hb i =
      untruncatedFamily R n lam hk i := by
  simp only [untruncatedParameterBasisFromAnyFiniteBases, Basis.mk_apply]

/-- The literal higher Specht free basis over every nontrivial commutative
coefficient ring in which `n!` is a unit. -/
theorem untruncated_specified_parameter_basis_of_factorial_isUnit
    (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hfac : IsUnit (n.factorial : R)) :
    IsSpecifiedBasis (R := ElementaryParameterRing R n lam)
      (untruncatedFamily R n lam hk) := by
  let hb := fun s hs hh =>
    griffin_specifiedBasis_of_factorial_isUnit R n lam hk s hs hh hfac
  exact ⟨untruncatedParameterBasisFromAnyFiniteBases R n lam hk hb,
    untruncatedParameterBasisFromAnyFiniteBases_apply R n lam hk hb⟩

/-- Necessity uses an actual index of the prescribed family: the one-row
tableau pair has polynomial `n!`, also for the empty partition. -/
theorem factorial_ne_zero_of_untruncated_specified_parameter_basis
    (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : IsSpecifiedBasis (R := ElementaryParameterRing R n lam)
      (untruncatedFamily R n lam hk)) :
    (n.factorial : R) ≠ 0 := by
  intro hzero
  obtain ⟨B, hB⟩ := hb
  let i : UntruncatedIndex n lam hk :=
    (oneRowParameterIndex n lam hk 0).base
  have hi : untruncatedFamily R n lam hk i = 0 := by
    change Ideal.Quotient.mk (untruncatedIdeal R n lam)
      (pairPolynomial (oneRowPair n)) = 0
    rw [pairPolynomial_oneRow, map_natCast]
    simpa only [map_natCast, map_zero] using
      congrArg (algebraMap R (UntruncatedRing R n lam)) hzero
  exact B.ne_zero i ((hB i).trans hi)

/-- Remark 6.2: the unchanged parameter higher Specht family is a basis
exactly in characteristic zero or characteristic greater than `n`.
There is no nonempty-partition or positive-variable-count restriction. -/
theorem remark_6_2_untruncated_characteristic
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsSpecifiedBasis (R := ElementaryParameterRing K n lam)
      (untruncatedFamily K n lam hk) ↔
      ringChar K = 0 ∨ n < ringChar K := by
  constructor
  · intro hb
    exact (factorial_ne_zero_iff_characteristic_range K n).mp
      (factorial_ne_zero_of_untruncated_specified_parameter_basis K n lam hk hb)
  · intro hchar
    let hb := fun s hs hh =>
      (corollary_8_1_griffin_characteristic_all_partitions K n lam hk s hs hh).mpr hchar
    exact ⟨untruncatedParameterBasisFromAnyFiniteBases K n lam hk hb,
      untruncatedParameterBasisFromAnyFiniteBases_apply K n lam hk hb⟩

/-- Remark 6.2 over the exact coefficient ring `Localization.Away (n! : ℤ)`.
The basis indices and polynomial representatives are unchanged. -/
theorem remark_6_2_untruncated_localized
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsSpecifiedBasis (R := ElementaryParameterRing (FactorialLocalization n) n lam)
      (untruncatedFamily (FactorialLocalization n) n lam hk) := by
  let hb := fun s hs hh => corollary_8_1_griffin_localized n lam hk s hs hh
  exact ⟨untruncatedParameterBasisFromAnyFiniteBases (FactorialLocalization n) n lam hk hb,
    untruncatedParameterBasisFromAnyFiniteBases_apply (FactorialLocalization n) n lam hk hb⟩

end HigherSpecht
end
end CanonicalSource1000

section CanonicalSource35
/- Source: audit/ExpressionSpechtCopyStatements.lean -/



/-!
# Literal Specht-copy audit for Corollaries 5.3 and 6.7

Pending source only. These statements inspect the actual intertwiner range,
the span of the original quotient polynomials, their genuine permutation
orbits, irreducibility, and equivalence with the ordinary complex Specht
representation. They are not character-equality substitutes.

The finite-family hypotheses match Corollary 5.3's explicit finite nonempty
family and Corollary 6.7's atomic/binary finite-expression operations.
No nullary sum or intersection is asserted.
-/

noncomputable section

open Module MvPolynomial TauCeti TauCeti.YoungTableau HigherSpecht
open scoped Classical

universe u

namespace ExpressionSpechtCopyAudit

theorem finite_expression_copy {n s : ℕ}
    (e : GriffinIdealExpression n s) (hs : 0 < s)
    (i : FiniteHarmonicIndex n s) (hi : i ∈ e.eligible) :
    (e.complexIntertwiner i).range.toSubmodule =
      Submodule.span ℂ (Set.range
        (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
          Ideal.Quotient.mk (e.ideal ℂ) (finiteMasterPolynomial i T))) ∧
    (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
      (e.complexIntertwiner i).range.toSubmodule =
        Submodule.span ℂ (Set.range (fun g : Equiv.Perm (Fin n) =>
          quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ) g
            (Ideal.Quotient.mk (e.ideal ℂ) (finiteMasterPolynomial i T))))) ∧
    Representation.IsIrreducible (e.complexIntertwiner i).range.toRepresentation ∧
    Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ
      (e.complexIntertwiner i).range.toRepresentation) :=
  e.corollary_5_3_specht_copy hs i hi

theorem untruncated_expression_copy {n : ℕ}
    (e : UntruncatedIdealExpression n)
    (i : UnboundedHarmonicIndex n) (hi : i ∈ e.eligible) :
    (e.complexIntertwiner i).range.toSubmodule =
      Submodule.span ℂ (Set.range
        (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
          Ideal.Quotient.mk (e.ideal ℂ) (unboundedMasterPolynomial i T))) ∧
    (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
      (e.complexIntertwiner i).range.toSubmodule =
        Submodule.span ℂ (Set.range (fun g : Equiv.Perm (Fin n) =>
          quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ) g
            (Ideal.Quotient.mk (e.ideal ℂ) (unboundedMasterPolynomial i T))))) ∧
    Representation.IsIrreducible (e.complexIntertwiner i).range.toRepresentation ∧
    Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ
      (e.complexIntertwiner i).range.toRepresentation) :=
  e.corollary_6_7_specht_copy i hi

theorem finite_nonempty_family_copies
    {ι : Type u} [Finite ι] [Nonempty ι] {n s : ℕ} (hs : 0 < s)
    (A : ι → BoundedGriffinShape n s) :
    (∀ i : FiniteHarmonicIndex n s,
      (∃ j, i.toUnboundedHarmonicIndex.eligible (A j).diagram (A j).card_le) →
      ∃ hJ : PermutationStable (⨅ j, griffinIdeal ℂ n (A j).diagram s),
        ∃ V : Subrepresentation (quotientRepresentation (⨅ j, griffinIdeal ℂ n (A j).diagram s) hJ),
          V.toSubmodule = Submodule.span ℂ
            (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
              Ideal.Quotient.mk (⨅ j, griffinIdeal ℂ n (A j).diagram s) (finiteMasterPolynomial i T))) ∧
          (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
            V.toSubmodule = Submodule.span ℂ
              (Set.range (fun g : Equiv.Perm (Fin n) =>
                quotientRepresentation (⨅ j, griffinIdeal ℂ n (A j).diagram s) hJ g
                  (Ideal.Quotient.mk (⨅ j, griffinIdeal ℂ n (A j).diagram s) (finiteMasterPolynomial i T))))) ∧
          Representation.IsIrreducible V.toRepresentation ∧
          Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ V.toRepresentation)) ∧
    (∀ i : FiniteHarmonicIndex n s,
      (∀ j, i.toUnboundedHarmonicIndex.eligible (A j).diagram (A j).card_le) →
      ∃ hJ : PermutationStable (⨆ j, griffinIdeal ℂ n (A j).diagram s),
        ∃ V : Subrepresentation (quotientRepresentation (⨆ j, griffinIdeal ℂ n (A j).diagram s) hJ),
          V.toSubmodule = Submodule.span ℂ
            (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
              Ideal.Quotient.mk (⨆ j, griffinIdeal ℂ n (A j).diagram s) (finiteMasterPolynomial i T))) ∧
          (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
            V.toSubmodule = Submodule.span ℂ
              (Set.range (fun g : Equiv.Perm (Fin n) =>
                quotientRepresentation (⨆ j, griffinIdeal ℂ n (A j).diagram s) hJ g
                  (Ideal.Quotient.mk (⨆ j, griffinIdeal ℂ n (A j).diagram s) (finiteMasterPolynomial i T))))) ∧
          Representation.IsIrreducible V.toRepresentation ∧
          Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ V.toRepresentation)) := by
  simpa only [IsLiteralQuotientSpechtCopy] using
    corollary_5_3_finite_family_specht_copies hs A

theorem untruncated_finite_nonempty_family_copies
    {ι : Type u} [Finite ι] [Nonempty ι] {n : ℕ}
    (A : ι → BoundedUntruncatedShape n) :
    (∀ i : UnboundedHarmonicIndex n,
      (∃ j, i.eligible (A j).diagram (A j).card_le) →
      ∃ hJ : PermutationStable (⨅ j, untruncatedIdeal ℂ n (A j).diagram),
        ∃ V : Subrepresentation (quotientRepresentation (⨅ j, untruncatedIdeal ℂ n (A j).diagram) hJ),
          V.toSubmodule = Submodule.span ℂ
            (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
              Ideal.Quotient.mk (⨅ j, untruncatedIdeal ℂ n (A j).diagram) (unboundedMasterPolynomial i T))) ∧
          (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
            V.toSubmodule = Submodule.span ℂ
              (Set.range (fun g : Equiv.Perm (Fin n) =>
                quotientRepresentation (⨅ j, untruncatedIdeal ℂ n (A j).diagram) hJ g
                  (Ideal.Quotient.mk (⨅ j, untruncatedIdeal ℂ n (A j).diagram) (unboundedMasterPolynomial i T))))) ∧
          Representation.IsIrreducible V.toRepresentation ∧
          Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ V.toRepresentation)) ∧
    (∀ i : UnboundedHarmonicIndex n,
      (∀ j, i.eligible (A j).diagram (A j).card_le) →
      ∃ hJ : PermutationStable (⨆ j, untruncatedIdeal ℂ n (A j).diagram),
        ∃ V : Subrepresentation (quotientRepresentation (⨆ j, untruncatedIdeal ℂ n (A j).diagram) hJ),
          V.toSubmodule = Submodule.span ℂ
            (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
              Ideal.Quotient.mk (⨆ j, untruncatedIdeal ℂ n (A j).diagram) (unboundedMasterPolynomial i T))) ∧
          (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
            V.toSubmodule = Submodule.span ℂ
              (Set.range (fun g : Equiv.Perm (Fin n) =>
                quotientRepresentation (⨆ j, untruncatedIdeal ℂ n (A j).diagram) hJ g
                  (Ideal.Quotient.mk (⨆ j, untruncatedIdeal ℂ n (A j).diagram) (unboundedMasterPolynomial i T))))) ∧
          Representation.IsIrreducible V.toRepresentation ∧
          Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ V.toRepresentation)) := by
  simpa only [IsLiteralQuotientSpechtCopy] using
    corollary_6_7_finite_family_specht_copies A

end ExpressionSpechtCopyAudit

#print HigherSpecht.GriffinIdealExpression.corollary_5_3_specht_copy
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_specht_copy
#print HigherSpecht.UntruncatedIdealExpression.corollary_6_7_specht_copy
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_specht_copy
#print HigherSpecht.corollary_5_3_finite_family_specht_copies
#print axioms HigherSpecht.corollary_5_3_finite_family_specht_copies
#print HigherSpecht.corollary_6_7_finite_family_specht_copies
#print axioms HigherSpecht.corollary_6_7_finite_family_specht_copies
#print axioms ExpressionSpechtCopyAudit.finite_expression_copy
#print axioms ExpressionSpechtCopyAudit.untruncated_expression_copy
#print axioms ExpressionSpechtCopyAudit.finite_nonempty_family_copies
#print axioms ExpressionSpechtCopyAudit.untruncated_finite_nonempty_family_copies
end
end CanonicalSource35

section CanonicalSource36
/- Source: audit/FiniteIdealFamilyStatements.lean -/



/-!
# Literal finite-family correspondence checks

These targets write the actual ideal suprema/infima, prefix-catabolism
conditions, and original higher-Specht products.  They do not define a
finite family by the expression fold whose interpretation is being checked.
The index type is any finite nonempty type, in any universe.

Reconstructed after the runtime outage.  This is pending source, with no
compilation, axiom inspection, or kernel replay asserted.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial HigherSpecht
open scoped Classical

universe u

namespace SpechtFiniteFamilyAudit

/-- The two literal finite-family basis clauses of Corollary 5.3.  Different
partitions may have different sizes; only the ambient `n` and truncation `s`
are shared. -/
def GriffinFiniteFamilyLiteral
    (ι : Type u) [Finite ι] [Nonempty ι]
    (n s : ℕ) (lam : ι → YoungDiagram)
    (hk : ∀ j, (lam j).card ≤ n) : Prop :=
  IsSpecifiedBasis (R := ℂ)
    (fun z : (Σ i : {i : FiniteHarmonicIndex n s //
          ∀ j, i.multiplier.colLen 0 ≤ n - (lam j).card ∧
            CatDominates (prefixTableau i.left (lam j).card
              (by simpa only [YoungDiagram.card_ofPartition] using hk j)) (lam j)},
          StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) =>
      Ideal.Quotient.mk (⨆ j, griffinIdeal ℂ n (lam j) s)
        (rename (finCongr (YoungDiagram.card_ofPartition z.1.val.part))
          (higherSpechtPolynomial z.1.val.left z.2) *
          elementaryMultiplier n n z.1.val.multiplier.rowLen)) ∧
  IsSpecifiedBasis (R := ℂ)
    (fun z : (Σ i : {i : FiniteHarmonicIndex n s //
          ∃ j, i.multiplier.colLen 0 ≤ n - (lam j).card ∧
            CatDominates (prefixTableau i.left (lam j).card
              (by simpa only [YoungDiagram.card_ofPartition] using hk j)) (lam j)},
          StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) =>
      Ideal.Quotient.mk (⨅ j, griffinIdeal ℂ n (lam j) s)
        (rename (finCongr (YoungDiagram.card_ofPartition z.1.val.part))
          (higherSpechtPolynomial z.1.val.left z.2) *
          elementaryMultiplier n n z.1.val.multiplier.rowLen))

theorem corollary_5_3_finiteFamily_literal
    (ι : Type u) [Finite ι] [Nonempty ι]
    (n s : ℕ) (hs : 0 < s) (lam : ι → YoungDiagram)
    (hk : ∀ j, (lam j).card ≤ n)
    (hheight : ∀ j, (lam j).colLen 0 ≤ s) :
    GriffinFiniteFamilyLiteral ι n s lam hk := by
  constructor
  · exact GriffinIdealExpression.corollary_5_3_finiteSum_basis
      (fun j => .atom ⟨lam j, hk j, hheight j⟩) hs
  · exact GriffinIdealExpression.corollary_5_3_finiteIntersection_basis
      (fun j => .atom ⟨lam j, hk j, hheight j⟩) hs

/-- The finite-family vector-space clauses of Corollary 6.7.  There is no
common-size premise for these two basis assertions. -/
def UntruncatedFiniteFamilyLiteral
    (ι : Type u) [Finite ι] [Nonempty ι]
    (n : ℕ) (lam : ι → YoungDiagram)
    (hk : ∀ j, (lam j).card ≤ n) : Prop :=
  IsSpecifiedBasis (R := ℂ)
    (fun z : (Σ i : {i : UnboundedHarmonicIndex n //
          ∀ j, i.multiplier.colLen 0 ≤ n - (lam j).card ∧
            CatDominates (prefixTableau i.left (lam j).card
              (by simpa only [YoungDiagram.card_ofPartition] using hk j)) (lam j)},
          StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) =>
      Ideal.Quotient.mk (⨆ j, untruncatedIdeal ℂ n (lam j))
        (rename (finCongr (YoungDiagram.card_ofPartition z.1.val.part))
          (higherSpechtPolynomial z.1.val.left z.2) *
          elementaryMultiplier n n z.1.val.multiplier.rowLen)) ∧
  IsSpecifiedBasis (R := ℂ)
    (fun z : (Σ i : {i : UnboundedHarmonicIndex n //
          ∃ j, i.multiplier.colLen 0 ≤ n - (lam j).card ∧
            CatDominates (prefixTableau i.left (lam j).card
              (by simpa only [YoungDiagram.card_ofPartition] using hk j)) (lam j)},
          StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) =>
      Ideal.Quotient.mk (⨅ j, untruncatedIdeal ℂ n (lam j))
        (rename (finCongr (YoungDiagram.card_ofPartition z.1.val.part))
          (higherSpechtPolynomial z.1.val.left z.2) *
          elementaryMultiplier n n z.1.val.multiplier.rowLen))

theorem corollary_6_7_finiteFamily_literal
    (ι : Type u) [Finite ι] [Nonempty ι]
    (n : ℕ) (lam : ι → YoungDiagram)
    (hk : ∀ j, (lam j).card ≤ n) :
    UntruncatedFiniteFamilyLiteral ι n lam hk := by
  constructor
  · exact UntruncatedIdealExpression.corollary_6_7_finiteSum_basis
      (fun j => .atom ⟨lam j, hk j⟩)
  · exact UntruncatedIdealExpression.corollary_6_7_finiteIntersection_basis
      (fun j => .atom ⟨lam j, hk j⟩)

end SpechtFiniteFamilyAudit

#print SpechtFiniteFamilyAudit.corollary_5_3_finiteFamily_literal
#print SpechtFiniteFamilyAudit.corollary_6_7_finiteFamily_literal
#print axioms SpechtFiniteFamilyAudit.corollary_5_3_finiteFamily_literal
#print axioms SpechtFiniteFamilyAudit.corollary_6_7_finiteFamily_literal
#print axioms HigherSpecht.UntruncatedIdealExpression.finiteSum_allSize
#print axioms HigherSpecht.UntruncatedIdealExpression.finiteIntersection_allSize
end
end CanonicalSource36

section CanonicalSource37
/- Source: audit/OrderedRootZeroStatements.lean -/



/-!
# Literal zero-parameter identity and coordinate-action check

This gate requires one and the same canonical map to fix every original
Springer class and to intertwine every actual coordinate permutation.  The
last clause exposes its action on an arbitrary polynomial representative.
It is a pending statement check, not a compilation or certification report.
-/

noncomputable section

open TauCeti HigherSpecht
open scoped Classical TensorProduct

namespace SpechtOrderedRootZeroAudit

def NoParameterEquivariantIdentityLiteral
    (R : Type*) [CommRing R] (lam : YoungDiagram) : Prop :=
  (∀ x : PolynomialRing lam.card R ⧸ springerIdeal R lam,
    proposition_7_2_no_parameters R lam
      ((1 : OrderedRootRing R (lam.card - lam.card))
        ⊗ₜ[ElementaryParameterRing R lam.card lam] x) = x) ∧
  (∀ (g : Equiv.Perm (Fin lam.card))
      (z : OrderedRootRing R (lam.card - lam.card)
        ⊗[ElementaryParameterRing R lam.card lam]
          (PolynomialRing lam.card R ⧸ springerIdeal R lam)),
    proposition_7_2_no_parameters R lam
        (elementaryParameterTensorPermutation
          (OrderedRootRing R (lam.card - lam.card)) g z) =
      springerPermutationAlgEquiv lam g
        (proposition_7_2_no_parameters R lam z)) ∧
  (∀ (g : Equiv.Perm (Fin lam.card)) (p : PolynomialRing lam.card R),
    proposition_7_2_no_parameters R lam
        (elementaryParameterTensorPermutation
          (OrderedRootRing R (lam.card - lam.card)) g
          ((1 : OrderedRootRing R (lam.card - lam.card))
            ⊗ₜ[ElementaryParameterRing R lam.card lam]
            Ideal.Quotient.mk (springerIdeal R lam) p)) =
      Ideal.Quotient.mk (springerIdeal R lam) (MvPolynomial.rename g p))

theorem proposition_7_2_no_parameters_equivariant_identity_literal
    (R : Type*) [CommRing R] (lam : YoungDiagram) :
    NoParameterEquivariantIdentityLiteral R lam := by
  refine ⟨proposition_7_2_no_parameters_identity R lam,
    proposition_7_2_no_parameters_permutation R lam, ?_⟩
  intro g p
  exact (proposition_7_2_no_parameters_permutation R lam g
    ((1 : OrderedRootRing R (lam.card - lam.card))
      ⊗ₜ[ElementaryParameterRing R lam.card lam]
        Ideal.Quotient.mk (springerIdeal R lam) p)).trans
    ((congrArg (springerPermutationAlgEquiv (R := R) lam g)
      (proposition_7_2_no_parameters_identity R lam
        (Ideal.Quotient.mk (springerIdeal R lam) p))).trans
      (springerPermutationAlgEquiv_mk (R := R) lam g p))

end SpechtOrderedRootZeroAudit

#print SpechtOrderedRootZeroAudit.proposition_7_2_no_parameters_equivariant_identity_literal
#print axioms SpechtOrderedRootZeroAudit.proposition_7_2_no_parameters_equivariant_identity_literal
end
end CanonicalSource37

section CanonicalSource38
/- Source: audit/SpechtHomologicalStatements.lean -/



/-!
# Literal statement audit for Section 7.1 of the higher Specht manuscript

This file is a pending audit target, not a verification certificate.  It
expands regularity into support and attainment in the actual derived Tor
groups, levelness/type into genuine canonical-module generators, Gorenstein
into local finite self-injective dimension, and complete intersection into
an actual regular sequence generating the stated polynomial ideal.

Every assertion quantifies over all coefficient fields.  The only partition
restriction is its printed size bound.  Zero variables and the empty
partition are included.  The statistic n(lambda) is written as the literal
sum of row index times row length, with row indices starting at zero.
-/

noncomputable section

open CategoryTheory Module TauCeti HigherSpecht
open scoped Classical BigOperators

universe u

namespace SpechtHomologicalAudit

/-- Actual Tor support, including the attained exact regularity value. -/
def RegularityStatement : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n),
    let r : ℤ :=
      ((∑ i ∈ Finset.range (lam.colLen 0), i * lam.rowLen i : ℕ) : ℤ) +
        (n - lam.card : ℕ) * (lam.colLen 0 : ℤ)
    (∀ (i : ℕ) (j : ℤ), n < i ∨ j < i ∨ r < j - i →
      Subsingleton ((untruncatedTorGrading K n lam hk i).piece j)) ∧
      ∃ i : ℕ, i ≤ n ∧
        ¬ Subsingleton ((untruncatedTorGrading K n lam hk i).piece (i + r))

theorem regularity_statement : RegularityStatement := by
  intro K _ n lam hk
  simpa only [springerTopDegree_eq_sum_rows, UntruncatedTorPiece] using
    corollary_7_5_tor_support K n lam hk

/-- The actual Springer socle, rather than a subspace defined by its
expected degree or dimension. -/
def SpringerSocleStatement : Prop :=
  ∀ (K : Type u) [Field K] (mu : YoungDiagram),
    (TauCeti.socle (SpringerRing K mu) (SpringerRing K mu)).restrictScalars K =
      quotientHomogeneousPiece (springerIdeal K mu)
        (∑ i ∈ Finset.range (mu.colLen 0), i * mu.rowLen i) ∧
    Module.finrank K
      ((TauCeti.socle (SpringerRing K mu) (SpringerRing K mu)).restrictScalars K) =
      Fintype.card (StandardYoungTableau mu)

theorem springer_socle_statement : SpringerSocleStatement := by
  intro K _ mu
  simpa only [springerSocle, springerTopDegree_eq_sum_rows] using
    springer_socle_concentrated_and_type K mu

/-- The actual normalized relative dual is dualizing and has precisely
the printed number of generators in precisely the printed degree.
The minimality clause permits arbitrary, not necessarily homogeneous,
finite generating families. -/
def CanonicalModuleStatement : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n),
    let A := UntruncatedRing K n lam
    let omega := UntruncatedRelativeDual K n lam
    let mu := adjoinOnes lam (n - lam.card)
    let degree : ℤ := ((n - lam.card + 1).choose 2 : ℤ) -
      ((∑ i ∈ Finset.range (mu.colLen 0), i * mu.rowLen i : ℕ) : ℤ)
    let count := Fintype.card (StandardYoungTableau mu)
    (∀ (P : Ideal A) [P.IsPrime],
      Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P)) ∧
    (IsNoetherianRing A ∧ Module.Finite A omega ∧
      (∃ d : ℕ, HasInjectiveDimensionLE (ModuleCat.of A omega) d) ∧
      Function.Bijective (fun a : A => LinearMap.lsmul A omega a) ∧
      (letI := HasExt.standard (ModuleCat.{u} A)
       ∀ i : ℕ, 0 < i →
         ∀ e : CategoryTheory.Abelian.Ext (ModuleCat.of A omega) (ModuleCat.of A omega) i, e = 0)) ∧
    (∃ v : Fin count → omega,
      (∀ i, v i ∈ (untruncatedRelativeDualGrading K n lam hk).piece degree) ∧
      Submodule.span A (Set.range v) = ⊤) ∧
    (∀ r (v : Fin r → omega), Submodule.span A (Set.range v) = ⊤ → count ≤ r)

theorem canonical_module_statement : CanonicalModuleStatement := by
  intro K _ n lam hk
  refine ⟨untruncated_isCohenMacaulay_atPrime_allFields K n lam hk, ?_⟩
  simpa only [IsDualizingModule, springerTopDegree_eq_sum_rows] using
    corollary_7_6_canonical_module K n lam hk

/-- The local self-injective-dimension condition is stated explicitly.
The empty partition is included by the column condition. -/
def GorensteinStatement : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n),
    (IsNoetherianRing (UntruncatedRing K n lam) ∧
      ∀ P : PrimeSpectrum (UntruncatedRing K n lam),
        ∃ d : ℕ, HasInjectiveDimensionLE
          (ModuleCat.of (Localization.AtPrime P.asIdeal)
            (Localization.AtPrime P.asIdeal)) d) ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1

theorem gorenstein_statement : GorensteinStatement := by
  intro K _ n lam hk
  simpa only [IsGorensteinRing] using corollary_7_6_gorenstein_iff K n lam hk

/-- The complete-intersection side is an actual regular-sequence
presentation inside the manuscript's polynomial ring. -/
def CompleteIntersectionStatement : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n),
    (∃ xs : List (PolynomialRing n K),
      RingTheory.Sequence.IsRegular (PolynomialRing n K) xs ∧
      Ideal.ofList xs = untruncatedIdeal K n lam) ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1

theorem complete_intersection_statement : CompleteIntersectionStatement := by
  intro K _ n lam hk
  simpa only [IsRegularSequencePresentation] using
    corollary_7_6_completeIntersection_iff K n lam hk

/-- Both standard algebraic conditions hold for exactly the same
actual quotient rings, with no condition defined through the partition. -/
theorem gorenstein_iff_complete_intersection
    (K : Type u) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (IsNoetherianRing (UntruncatedRing K n lam) ∧
      ∀ P : PrimeSpectrum (UntruncatedRing K n lam),
        ∃ d : ℕ, HasInjectiveDimensionLE
          (ModuleCat.of (Localization.AtPrime P.asIdeal)
            (Localization.AtPrime P.asIdeal)) d) ↔
    (∃ xs : List (PolynomialRing n K),
      RingTheory.Sequence.IsRegular (PolynomialRing n K) xs ∧
      Ideal.ofList xs = untruncatedIdeal K n lam) := by
  simpa only [IsGorensteinRing, IsRegularSequencePresentation] using
    corollary_7_6_gorenstein_iff_completeIntersection K n lam hk

end SpechtHomologicalAudit

-- Print the actual mathematical constructions as well as the literal targets.
#print HigherSpecht.polynomialResidueModule
#print HigherSpecht.polynomialTorModule
#print HigherSpecht.polynomialTorGrading
#print HigherSpecht.untruncatedTorGrading
#print HigherSpecht.RelativeDual
#print HigherSpecht.RelativeDual.smul_apply
#print HigherSpecht.untruncatedRelativeDualGrading
#print HigherSpecht.IsDualizingModule
#print HigherSpecht.IsGorensteinRing
#print HigherSpecht.IsRegularSequencePresentation
#print SpechtHomologicalAudit.RegularityStatement
#print SpechtHomologicalAudit.SpringerSocleStatement
#print SpechtHomologicalAudit.CanonicalModuleStatement
#print SpechtHomologicalAudit.GorensteinStatement
#print SpechtHomologicalAudit.CompleteIntersectionStatement
#print axioms SpechtHomologicalAudit.regularity_statement
#print axioms SpechtHomologicalAudit.springer_socle_statement
#print axioms SpechtHomologicalAudit.canonical_module_statement
#print axioms SpechtHomologicalAudit.gorenstein_statement
#print axioms SpechtHomologicalAudit.complete_intersection_statement
#print axioms SpechtHomologicalAudit.gorenstein_iff_complete_intersection
end
end CanonicalSource38

section CanonicalSource39
/- Source: audit/AlternativeMultiplierCopyStatements.lean -/



/-!
# Literal alternative-multiplier copy checks

Every range in these targets is the span of the displayed, unchanged
higher-Specht products.  The multiplier conditions in the theorem gates
refer only to indices used by the actual family.  An actual intertwining
equivalence and irreducibility are both asserted; equality of characters
alone is not the conclusion.

Pending reconstructed source, not a compilation or certification report.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial HigherSpecht
open scoped Classical

namespace SpechtAlternativeMultiplierAudit

def GriffinAlternativeCopyLiteral
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (f : YoungDiagram → PolynomialRing n ℂ) : Prop :=
  ∀ (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part),
    ∃ W : Subrepresentation (griffinRepresentation ℂ n lam s),
      W.toSubmodule =
        Submodule.span ℂ (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
          Ideal.Quotient.mk (griffinIdeal ℂ n lam s)
            (rename (finCongr (YoungDiagram.card_ofPartition part))
              (higherSpechtPolynomial i.left T) * f i.multiplier)) ∧
      Representation.IsIrreducible W.toRepresentation ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver ℂ part) W.toRepresentation)

theorem corollary_4_3_alternativeCopy_literal
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ z : GriffinIndex n lam hk s,
      IsDominanceTriangularMultiplier n z.multiplier (f z.multiplier)) :
    GriffinAlternativeCopyLiteral n lam hk s f := by
  intro part i
  exact corollary_4_3_copy_on_admissible_multipliers
    n lam hk s hs hheight f hf part i

def ExpressionAlternativeCopyLiteral {n s : ℕ}
    (e : GriffinIdealExpression n s)
    (f : YoungDiagram → PolynomialRing n ℂ) : Prop :=
  ∀ i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible},
    ∃ W : Subrepresentation
        (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)),
      W.toSubmodule =
        Submodule.span ℂ (Set.range fun T :
            StandardYoungTableau (YoungDiagram.ofPartition i.val.part) =>
          Ideal.Quotient.mk (e.ideal ℂ)
            (rename (finCongr (YoungDiagram.card_ofPartition i.val.part))
              (higherSpechtPolynomial i.val.left T) * f i.val.multiplier)) ∧
      Representation.IsIrreducible W.toRepresentation ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver ℂ i.val.part) W.toRepresentation)

theorem corollary_5_3_alternativeCopy_literal {n s : ℕ}
    (e : GriffinIdealExpression n s) (hs : 0 < s)
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible},
      IsDominanceTriangularMultiplier n i.val.multiplier (f i.val.multiplier)) :
    ExpressionAlternativeCopyLiteral e f := by
  intro i
  have h := e.corollary_5_3_alternative_copy_onEligible f hf hs i
  refine ⟨e.alternativeCopyOnEligible f hf i, ?_, h.2⟩
  exact h.1

end SpechtAlternativeMultiplierAudit

#print SpechtAlternativeMultiplierAudit.corollary_4_3_alternativeCopy_literal
#print SpechtAlternativeMultiplierAudit.corollary_5_3_alternativeCopy_literal
#print axioms SpechtAlternativeMultiplierAudit.corollary_4_3_alternativeCopy_literal
#print axioms SpechtAlternativeMultiplierAudit.corollary_5_3_alternativeCopy_literal
#print axioms HigherSpecht.griffinFixedCopyOver_toSubmodule
#print axioms HigherSpecht.adaptedGriffinCopy_eq_span
end
end CanonicalSource39

section CanonicalSource40
/- Source: audit/Theorem32SelectedFamilyStatements.lean -/



/-!
# Literal selected-family pairing audit

Reconstructed after the outage. This is a pending source gate, not a
compiler or replay certificate. The entries below are the actual
coefficient functionals and the actual column-Vandermonde witnesses.
-/

noncomputable section

open Module MvPolynomial TauCeti TauCeti.YoungTableau HigherSpecht
open scoped Classical

universe u

namespace SpechtSelectedPairingAudit

theorem literal_entry (K : Type u) [Field K] [CharZero K]
    {μ : YoungDiagram} (A : Finset (StandardYoungTableau μ))
    (T : StandardYoungTableau μ) (e : Fin A.card ≃ A) (i j : Fin A.card) :
    higherSpechtApolarFunctional (K := K) (e i).val T.toTableau
      (higherSpechtPolynomial (e j).val T) =
    (ordinaryAction (higherSpechtPolynomial (R := K) (e j).val T)
      (columnWitness (insertionFilling (e i).val T.toTableau).toEmbedding 1)).coeff
        (insertionRejectionExponent (e i).val T.toTableau) :=
  theorem_3_2_selected_entry A T e i j

theorem literal_triangular_matrix (K : Type u) [Field K] [CharZero K]
    {μ : YoungDiagram} (A : Finset (StandardYoungTableau μ))
    (T : StandardYoungTableau μ) :
    ∃ e : Fin A.card ≃ A,
      Monotone (fun i => higherSpechtPrefixKey (e i).val T.toTableau) ∧
      (∀ i j : Fin A.card, i ≤ j →
        higherSpechtPrefixKey (e i).val T.toTableau =
          higherSpechtPrefixKey (e j).val T.toTableau →
        A.equivFin (e i) ≤ A.equivFin (e j)) ∧
      (∀ i j : Fin A.card, j < i →
        higherSpechtApolarFunctional (K := K) (e i).val T.toTableau
          (higherSpechtPolynomial (e j).val T) = 0) ∧
      (∀ i : Fin A.card,
        higherSpechtApolarFunctional (K := K) (e i).val T.toTableau
          (higherSpechtPolynomial (e i).val T) =
          ((rowFillingStabilizers T.toTableau
            (transportedCocharge (e i).val T.toTableau)).card : K) *
          ((insertionFixedPermutations (e i).val T.toTableau).card : K) *
          ((exponentFactorial (insertionAlpha (e i).val T.toTableau) : K) /
            exponentFactorial (insertionRejectionExponent (e i).val T.toTableau))) ∧
      (∀ i : Fin A.card,
        higherSpechtApolarFunctional (K := K) (e i).val T.toTableau
          (higherSpechtPolynomial (e i).val T) ≠ 0) ∧
      (∀ i : Fin A.card,
        0 < higherSpechtApolarFunctional (K := ℚ) (e i).val T.toTableau
          (higherSpechtPolynomial (e i).val T)) :=
  theorem_3_2_selected_family K A T

end SpechtSelectedPairingAudit

#print HigherSpecht.theorem_3_2_selected_entry
#print axioms HigherSpecht.theorem_3_2_selected_entry
#print HigherSpecht.theorem_3_2_selected_family
#print axioms HigherSpecht.theorem_3_2_selected_family
#print axioms SpechtSelectedPairingAudit.literal_entry
#print axioms SpechtSelectedPairingAudit.literal_triangular_matrix
end
end CanonicalSource40

section CanonicalSource41
/- Source: audit/SpechtIntegralHilbertStatements.lean -/



/-!
# Literal degreewise audit of the finite-s integral normal forms

Reconstructed after the outage. Pending source only: no compilation or
certificate is asserted. The graded piece is written as the actual image
of homogeneous polynomials, and field independence has no characteristic
assumption.
-/

noncomputable section

open Module MvPolynomial TauCeti HigherSpecht
open scoped Classical

universe u v

namespace SpechtIntegralHilbertAudit

theorem integral_degree_basis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) (d : ℕ) :
    ∃ B : Basis {a : GriffinStaircaseExponents n lam s // a.val.degree = d} ℤ
        ((homogeneousSubmodule (Fin n) ℤ d).map
          (Ideal.Quotient.mkₐ ℤ (griffinIdeal ℤ n lam s)).toLinearMap),
      ∀ a, (B a : GriffinRing ℤ n lam s) =
        Ideal.Quotient.mk (griffinIdeal ℤ n lam s)
          (MvPolynomial.monomial a.val.val 1) :=
  lemma_6_4_griffin_degree_integral n lam hk s hs hheight d

theorem degreewise_field_independence
    (K : Type u) (L : Type v) [Field K] [Field L]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) (d : ℕ) :
    Module.finrank K
      ((homogeneousSubmodule (Fin n) K d).map
        (Ideal.Quotient.mkₐ K (griffinIdeal K n lam s)).toLinearMap) =
    Module.finrank L
      ((homogeneousSubmodule (Fin n) L d).map
        (Ideal.Quotient.mkₐ L (griffinIdeal L n lam s)).toLinearMap) :=
  griffinHilbertFunction_independent_field K L n lam hk s hs hheight d

end SpechtIntegralHilbertAudit

#print HigherSpecht.lemma_6_4_griffin_degree_integral
#print axioms HigherSpecht.lemma_6_4_griffin_degree_integral
#print HigherSpecht.griffinHilbertFunction_independent_field
#print axioms HigherSpecht.griffinHilbertFunction_independent_field
#print axioms SpechtIntegralHilbertAudit.integral_degree_basis
#print axioms SpechtIntegralHilbertAudit.degreewise_field_independence
end
end CanonicalSource41

section CanonicalSource42
/- Source: audit/GriffinCharacteristicAllPartitionsStatements.lean -/



noncomputable section
open TauCeti Module

namespace HigherSpechtAudit

/-- A literal basis for the original family, for every partition including
the empty partition, in exactly the admissible field characteristics. -/
theorem griffin_characteristic_all_partitions_statement
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    (∃ B : Basis (HigherSpecht.GriffinIndex n lam hk s) K
        (HigherSpecht.GriffinRing K n lam s),
      ∀ i, B i = HigherSpecht.griffinFamily K n lam hk s i) ↔
      ringChar K = 0 ∨ n < ringChar K :=
  HigherSpecht.corollary_8_1_griffin_characteristic_all_partitions
    K n lam hk s hs hheight

#print griffin_characteristic_all_partitions_statement
#print axioms griffin_characteristic_all_partitions_statement

end HigherSpechtAudit
end
end CanonicalSource42

section CanonicalSource43
/- Source: audit/ParameterPrincipalStatements.lean -/



/-!
# Literal statement checks for Sections 6–8

These statements expose the actual quotients, prescribed representatives,
coefficient rings, and quantifiers. No `*Target` proposition is assumed.
They are source fixtures until this file is compiled against the final
verified stages. The canonical imports above are temporary integration
headers; the final build may replace only that header with the verified
stages that contain these same canonical declarations.

Theorem 6.1 is asserted over every characteristic-zero field, covering its
printed complex-coefficient statement. Corollary 6.5 retains every allowed
partition (including the empty one) and every coefficient field, with no
characteristic hypothesis. Theorem 7.1 retains arbitrary finite root sets,
positive nonzero-root multiplicities, arbitrary zero-root multiplicity, and
all field characteristics. Corollary 8.1 includes the empty partition and
every positive power bound satisfying the paper's height condition; there
is no characteristic bound involving that power parameter.
-/

noncomputable section

open HigherSpecht TauCeti Module MvPolynomial
open scoped Classical BigOperators Polynomial TensorProduct

namespace ParameterPrincipalStatementAudit

/-- The scalar action used by each parameter-basis statement is the actual
map from formal parameters to elementary symmetric polynomial classes. -/
theorem parameter_action (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (j : Fin (n - lam.card)) :
    algebraMap (MvPolynomial (Fin (n - lam.card)) R)
        (PolynomialRing n R ⧸ untruncatedIdeal R n lam) (MvPolynomial.X j) =
      Ideal.Quotient.mk (untruncatedIdeal R n lam)
        (MvPolynomial.esymm (Fin n) R (j.val + 1)) := by
  exact MvPolynomial.aeval_X (elementaryParameterClasses R n lam) j

/-- Theorem 6.1: the literal elementary classes, original higher Specht
representatives, finite free parameter basis, and exact numerical rank. -/
theorem theorem61_basis_rank (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    AlgebraicIndependent K
      (fun j : Fin (n - lam.card) =>
        Ideal.Quotient.mk (untruncatedIdeal K n lam)
          (MvPolynomial.esymm (Fin n) K (j.val + 1))) ∧
    (∃ B : Basis (UntruncatedIndex n lam hk)
        (MvPolynomial (Fin (n - lam.card)) K)
        (PolynomialRing n K ⧸ untruncatedIdeal K n lam),
      ∀ i, B i = Ideal.Quotient.mk (untruncatedIdeal K n lam)
        (MvPolynomial.rename (finCongr i.val.card_eq)
          (higherSpechtPolynomial (R := K) i.val.left i.val.right))) ∧
    Module.Finite (MvPolynomial (Fin (n - lam.card)) K)
      (PolynomialRing n K ⧸ untruncatedIdeal K n lam) ∧
    Module.finrank (MvPolynomial (Fin (n - lam.card)) K)
      (PolynomialRing n K ⧸ untruncatedIdeal K n lam) =
        n.factorial / (∏ j ∈ Finset.range (lam.colLen 0), (lam.rowLen j).factorial) := by
  exact theorem_6_1_basis_and_rank K n lam hk

/-- The representatives of the displayed parameter basis have the actual
polynomial grading, not degrees attached to an abstract basis. -/
theorem theorem61_representative_degree {R : Type*} [CommRing R]
    {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n}
    (i : UntruncatedIndex n lam hk) :
    (MvPolynomial.rename (finCongr i.val.card_eq)
      (higherSpechtPolynomial (R := R) i.val.left i.val.right)).IsHomogeneous
        (cochargeDegree i.val.left) :=
  pairPolynomial_isHomogeneous i.val

/-- Theorem 6.1: ordinary Krull dimension and Cohen–Macaulayness at every
prime localization of the actual polynomial quotient. -/
theorem theorem61_dimension_cm (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    ringKrullDim (PolynomialRing n K ⧸ untruncatedIdeal K n lam) =
        (n - lam.card : ℕ) ∧
    IsNoetherianRing (PolynomialRing n K ⧸ untruncatedIdeal K n lam) ∧
    ∀ (P : Ideal (PolynomialRing n K ⧸ untruncatedIdeal K n lam)) [P.IsPrime],
      Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) := by
  exact theorem_6_1_dimension_and_cohenMacaulay K n lam hk

/-- Corollary 6.5: any integral monomial basis of the specified Springer
special fiber lifts unchanged. The index type has no finiteness premise. -/
theorem corollary65_arbitrary_integral_monomial_lift
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {ι : Type*} (a : ι → Fin n →₀ ℕ)
    (B : Basis ι ℤ
      (PolynomialRing n ℤ ⧸ untruncatedIdeal ℤ n (adjoinOnes lam (n - lam.card))))
    (hB : ∀ i, B i =
      Ideal.Quotient.mk (untruncatedIdeal ℤ n (adjoinOnes lam (n - lam.card)))
        (MvPolynomial.monomial (a i) 1)) :
    ∃ C : Basis ι (MvPolynomial (Fin (n - lam.card)) ℤ)
        (PolynomialRing n ℤ ⧸ untruncatedIdeal ℤ n lam),
      ∀ i, C i = Ideal.Quotient.mk (untruncatedIdeal ℤ n lam)
        (MvPolynomial.monomial (a i) 1) := by
  refine ⟨integralMonomialParameterBasis_of_basis n lam hk a B hB, ?_⟩
  intro i
  exact integralMonomialParameterBasis_of_basis_apply n lam hk a B hB i

/-- Corollary 6.5: the constructed unchanged staircase monomials give an
actual parameter basis over every commutative coefficient ring. -/
theorem corollary65_monomial_basis_all_rings (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    ∃ B : Basis (UntruncatedStaircaseExponents n (adjoinOnes lam (n - lam.card)))
        (MvPolynomial (Fin (n - lam.card)) R)
        (PolynomialRing n R ⧸ untruncatedIdeal R n lam),
      ∀ a, B a = Ideal.Quotient.mk (untruncatedIdeal R n lam)
        (MvPolynomial.monomial a.val 1) := by
  refine ⟨untruncatedMonomialParameterBasis R n lam hk, ?_⟩
  intro a
  exact untruncatedMonomialParameterBasis_apply R n lam hk a

/-- The all-field algebraic conclusions of Corollary 6.5 use the literal
elementary parameter map, exact factorial quotient, and local depth. -/
theorem corollary65_all_fields (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    AlgebraicIndependent K
      (fun j : Fin (n - lam.card) =>
        Ideal.Quotient.mk (untruncatedIdeal K n lam)
          (MvPolynomial.esymm (Fin n) K (j.val + 1))) ∧
    Module.Free (MvPolynomial (Fin (n - lam.card)) K)
      (PolynomialRing n K ⧸ untruncatedIdeal K n lam) ∧
    Module.Finite (MvPolynomial (Fin (n - lam.card)) K)
      (PolynomialRing n K ⧸ untruncatedIdeal K n lam) ∧
    Module.finrank (MvPolynomial (Fin (n - lam.card)) K)
      (PolynomialRing n K ⧸ untruncatedIdeal K n lam) =
        n.factorial / (∏ j ∈ Finset.range (lam.colLen 0), (lam.rowLen j).factorial) ∧
    ringKrullDim (PolynomialRing n K ⧸ untruncatedIdeal K n lam) =
        (n - lam.card : ℕ) ∧
    ∀ (P : Ideal (PolynomialRing n K ⧸ untruncatedIdeal K n lam)) [P.IsPrime],
      Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) := by
  exact corollary_6_5_allFields K n lam hk

theorem corollary65_flat_all_rings (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Flat (MvPolynomial (Fin (n - lam.card)) R)
      (PolynomialRing n R ⧸ untruncatedIdeal R n lam) :=
  untruncated_parameter_flat_allCoefficients R n lam hk

/-- The assignment subtype is independent of the chosen finite-cardinality
instance on each fiber.  This public equality uses `Nat.card` in its literal
predicate, so public algebra-equivalence definitions can transport across it
without exposing a private helper or a chosen subtype `Fintype` instance. -/
theorem rootAssignments_eq_literal {n : ℕ} {ι : Type*} [Fintype ι]
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) :
    PrescribedRootAssignments n (splitRootMultiplicities lam r0 r) =
      {f : Fin n → Option ι // ∀ i : Option ι,
        Nat.card {j : Fin n // f j = i} = i.elim (lam.card + r0) r} := by
  apply congrArg (fun p : (Fin n → Option ι) → Prop => {f // p f})
  funext f
  apply propext
  constructor
  · intro hf i
    simpa only [Fintype.card_eq_nat_card, splitRootMultiplicities] using hf i
  · intro hf i
    simpa only [Fintype.card_eq_nat_card, splitRootMultiplicities] using hf i

/-- Theorem 7.1: the left side spells out the original ideal and parameter
equations. The right side uses the actual assignment type and tensor product. -/
def theorem71_parameter_fiber
    (K : Type*) [Field K] {n m : ℕ} {ι : Type*} [Fintype ι]
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n)
    (r0 : ℕ) (c : ι → K) (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial a =
      Polynomial.X ^ r0 * ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i) :
    (PolynomialRing n K ⧸
      (untruncatedIdeal K n lam ⊔ Ideal.span (Set.range fun j : Fin m =>
        elementaryOn (Finset.univ : Finset (Fin n)) (j.val + 1) - MvPolynomial.C (a j)))) ≃ₐ[K]
      ∀ _f : {f : Fin n → Option ι //
          ∀ i : Option ι, Fintype.card {j : Fin n // f j = i} =
            i.elim (lam.card + r0) r},
        ⨂[K] i : Option ι,
          SpringerRing K (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))) :=
  by
    have hassign : PrescribedRootAssignments n (splitRootMultiplicities lam r0 r) =
        {f : Fin n → Option ι // ∀ i : Option ι,
          Fintype.card {j : Fin n // f j = i} = i.elim (lam.card + r0) r} := by
      simpa only [Fintype.card_eq_nat_card] using
        (rootAssignments_eq_literal (n := n) lam r0 r)
    exact Eq.mp (congrArg (fun J : Type _ =>
      ParameterFiber K n lam m a ≃ₐ[K]
        (J → ⨂[K] i : Option ι,
          SpringerRing K (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))))) hassign)
      (theorem_7_1_parameter_fiber K lam a hsize r0 c hc hcz r hr hfactor)

theorem theorem71_factor_count {n : ℕ} {ι : Type*} [Fintype ι]
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (hsize : lam.card + (r0 + ∑ i, r i) = n) :
    Fintype.card {f : Fin n → Option ι //
      ∀ i : Option ι, Fintype.card {j : Fin n // f j = i} =
        i.elim (lam.card + r0) r} =
      n.factorial / ((lam.card + r0).factorial * ∏ i, (r i).factorial) :=
  by
    simpa only [PrescribedRootAssignments, splitRootMultiplicities,
      Fintype.card_eq_nat_card] using
      (theorem_7_1_number_of_factors lam r0 r hsize)

/-- The nonsplit clause is actual scalar extension, along an arbitrary
field extension where the signed parameter polynomial has the factorization. -/
def theorem71_after_field_extension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    {n m : ℕ} {ι : Type*} [Fintype ι]
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n)
    (r0 : ℕ) (c : ι → L) (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial (fun i => algebraMap K L (a i)) =
      Polynomial.X ^ r0 * ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i) :
    L ⊗[K] (PolynomialRing n K ⧸
      (untruncatedIdeal K n lam ⊔ Ideal.span (Set.range fun j : Fin m =>
        elementaryOn (Finset.univ : Finset (Fin n)) (j.val + 1) - MvPolynomial.C (a j)))) ≃ₐ[L]
      ∀ _f : {f : Fin n → Option ι //
          ∀ i : Option ι, Fintype.card {j : Fin n // f j = i} =
            i.elim (lam.card + r0) r},
        ⨂[L] i : Option ι,
          SpringerRing L (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))) :=
  by
    have hassign : PrescribedRootAssignments n (splitRootMultiplicities lam r0 r) =
        {f : Fin n → Option ι // ∀ i : Option ι,
          Fintype.card {j : Fin n // f j = i} = i.elim (lam.card + r0) r} := by
      simpa only [Fintype.card_eq_nat_card] using
        (rootAssignments_eq_literal (n := n) lam r0 r)
    exact Eq.mp (congrArg (fun J : Type _ =>
      L ⊗[K] ParameterFiber K n lam m a ≃ₐ[L]
        (J → ⨂[L] i : Option ι,
          SpringerRing L (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))))) hassign)
      (theorem_7_1_after_scalar_extension K L lam a hsize r0 c hc hcz r hr hfactor)

/-- The full all-fiber assertion after algebraic closure has no root-choice
or factorization hypothesis: the roots and their multiplicities are taken
from the actual parameter polynomial's root multiset. -/
def theorem71_algebraic_closure (K : Type*) [Field K] {n m : ℕ}
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n) :
    let L := AlgebraicClosure K
    let Q := parameterPolynomial (fun i => algebraMap K L (a i))
    L ⊗[K] (PolynomialRing n K ⧸
      (untruncatedIdeal K n lam ⊔ Ideal.span (Set.range fun j : Fin m =>
        elementaryOn (Finset.univ : Finset (Fin n)) (j.val + 1) - MvPolynomial.C (a j)))) ≃ₐ[L]
      ∀ _f : {f : Fin n → Option (nonzeroRootSet Q) //
          ∀ i : Option (nonzeroRootSet Q), Fintype.card {j : Fin n // f j = i} =
            i.elim (lam.card + Q.roots.count 0) (canonicalRootMultiplicity Q)},
        ⨂[L] i : Option (nonzeroRootSet Q),
          SpringerRing L (i.elim (adjoinOnes lam (Q.roots.count 0))
            (fun j => columnPartition (canonicalRootMultiplicity Q j))) :=
  by
    let L := AlgebraicClosure K
    let Q := parameterPolynomial (fun i => algebraMap K L (a i))
    have hassign : PrescribedRootAssignments n
        (splitRootMultiplicities lam (Q.roots.count 0) (canonicalRootMultiplicity Q)) =
        {f : Fin n → Option (nonzeroRootSet Q) // ∀ i : Option (nonzeroRootSet Q),
          Fintype.card {j : Fin n // f j = i} =
            i.elim (lam.card + Q.roots.count 0) (canonicalRootMultiplicity Q)} := by
      simpa only [Fintype.card_eq_nat_card] using
        (rootAssignments_eq_literal (n := n) lam (Q.roots.count 0) (canonicalRootMultiplicity Q))
    exact Eq.mp (congrArg (fun J : Type _ =>
      L ⊗[K] ParameterFiber K n lam m a ≃ₐ[L]
        (J → ⨂[L] i : Option (nonzeroRootSet Q),
          SpringerRing L (i.elim (adjoinOnes lam (Q.roots.count 0))
            (fun j => columnPartition (canonicalRootMultiplicity Q j))))) hassign)
      (theorem_7_1_algebraicClosure K lam a hsize)

/-- Corollary 8.1, including the empty partition, with the literal
unnormalized finite-family representatives and the full multiplier range. -/
theorem corollary81_griffin_iff (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    (∃ B : Basis (GriffinIndex n lam hk s) K
        (PolynomialRing n K ⧸ griffinIdeal K n lam s),
      ∀ i, B i = Ideal.Quotient.mk (griffinIdeal K n lam s)
        (MvPolynomial.rename (finCongr i.pair.card_eq)
            (higherSpechtPolynomial (R := K) i.pair.left i.pair.right) *
          elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)) ↔
      ringChar K = 0 ∨ n < ringChar K := by
  exact corollary_8_1_griffin_characteristic_all_partitions K n lam hk s hs hheight

theorem corollary81_springer_iff (K : Type*) [Field K] (lam : YoungDiagram) :
    (∃ B : Basis (SpringerIndex lam) K (PolynomialRing lam.card K ⧸ springerIdeal K lam),
      ∀ i, B i = Ideal.Quotient.mk (springerIdeal K lam)
        (MvPolynomial.rename (finCongr i.val.card_eq)
          (higherSpechtPolynomial (R := K) i.val.left i.val.right))) ↔
      ringChar K = 0 ∨ lam.card < ringChar K := by
  exact corollary_8_1_springer_characteristic K lam

/-- The localization is the actual ring obtained by inverting `n!`. -/
theorem corollary81_griffin_localized
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    ∃ B : Basis (GriffinIndex n lam hk s) (Localization.Away (n.factorial : ℤ))
        (PolynomialRing n (Localization.Away (n.factorial : ℤ)) ⧸
          griffinIdeal (Localization.Away (n.factorial : ℤ)) n lam s),
      ∀ i, B i = Ideal.Quotient.mk
        (griffinIdeal (Localization.Away (n.factorial : ℤ)) n lam s)
        (MvPolynomial.rename (finCongr i.pair.card_eq)
            (higherSpechtPolynomial (R := Localization.Away (n.factorial : ℤ))
              i.pair.left i.pair.right) *
          elementaryMultiplier n (n - lam.card) i.multiplier.rowLen) := by
  exact corollary_8_1_griffin_localized n lam hk s hs hheight

theorem corollary81_springer_localized (lam : YoungDiagram) :
    ∃ B : Basis (SpringerIndex lam) (Localization.Away (lam.card.factorial : ℤ))
        (PolynomialRing lam.card (Localization.Away (lam.card.factorial : ℤ)) ⧸
          springerIdeal (Localization.Away (lam.card.factorial : ℤ)) lam),
      ∀ i, B i = Ideal.Quotient.mk
        (springerIdeal (Localization.Away (lam.card.factorial : ℤ)) lam)
        (MvPolynomial.rename (finCongr i.val.card_eq)
          (higherSpechtPolynomial (R := Localization.Away (lam.card.factorial : ℤ))
            i.val.left i.val.right)) := by
  exact corollary_8_1_springer_localized lam

/-- The irreducible finite copy is the span of the actual fixed-left
polynomials, and is equivalent to the ordinary Specht representation. -/
theorem corollary81_griffin_copy {K : Type*} [Field K] {n : ℕ}
    (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part)
    (hchar : ringChar K = 0 ∨ n < ringChar K) (hheight : lam.colLen 0 ≤ s) :
    ∃ V : Subrepresentation (griffinRepresentation K n lam s),
      V.toSubmodule = Submodule.span K
        (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
          Ideal.Quotient.mk (griffinIdeal K n lam s)
            (MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition part))
              (higherSpechtPolynomial i.left T) *
                elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)) ∧
      Representation.IsIrreducible V.toRepresentation ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver K part) V.toRepresentation) := by
  refine ⟨griffinFixedCopyOver K lam hk s part i, ?_, ?_⟩
  · exact griffinFixedCopyOver_toSubmodule K lam hk s part i
  · exact corollary_8_1_griffin_copy_irreducible lam hk s part i hchar hheight

/-- The same literal-span and genuine representation-equivalence check for
every eligible Springer left tableau. -/
theorem corollary81_springer_copy {K : Type*} [Field K]
    (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) (hS : CatDominates S lam)
    (hchar : ringChar K = 0 ∨ lam.card < ringChar K) :
    ∃ V : Subrepresentation (springerRepresentation K lam),
      V.toSubmodule = Submodule.span K
        (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
          Ideal.Quotient.mk (springerIdeal K lam)
            (MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition part))
              (higherSpechtPolynomial S T))) ∧
      Representation.IsIrreducible V.toRepresentation ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver K part) V.toRepresentation) := by
  refine ⟨springerFixedCopyOver K lam part S, ?_, ?_⟩
  · exact springerFixedCopyOver_toSubmodule K lam part S
  · exact corollary_8_1_springer_copy_irreducible lam part S hS hchar

end ParameterPrincipalStatementAudit
end
end CanonicalSource43

section CanonicalSource44
/- Source: HigherSpecht/FinalStatementAudit.lean -/



/-!
# Literal checks of the principal statements

These independently written statements avoid the `*Target` predicates. They
display the actual quotient representatives, Specht-copy spans, degrees, and
simultaneous decompositions. The index definitions are the original ones in
`Statements` and `SimultaneousStatements`; in particular no count, spanning,
catabolism, or representation assertion is an additional hypothesis here.

This file is a final consumer of the endpoint modules. It must not be imported
by those modules or by an umbrella which it itself imports. A staged build may
replace only the three imports above with its final endpoint-closure import.
The declarations and proof bodies below are unchanged by that header rewrite.
-/

noncomputable section

open TauCeti Module MvPolynomial

namespace HigherSpecht.FinalStatementAudit

/-- Theorem 1.1: every basis vector is the prescribed higher Specht coset. -/
theorem theorem_1_1_basis (lam : YoungDiagram) :
    ∃ b : Basis (SpringerIndex lam) ℂ
        (PolynomialRing lam.card ℂ ⧸ springerIdeal ℂ lam),
      ∀ i, b i = Ideal.Quotient.mk (springerIdeal ℂ lam)
        (rename (finCongr i.val.card_eq)
          (higherSpechtPolynomial (R := ℂ) i.val.left i.val.right)) := by
  simpa only [IsSpecifiedBasis, springerFamily, pairPolynomial] using
    (springer_basis_target ℂ lam)

/-- The grading in Theorem 1.1 is the degree of the actual polynomial. -/
theorem theorem_1_1_degree {mu : YoungDiagram}
    (S T : StandardYoungTableau mu) :
    (higherSpechtPolynomial (R := ℂ) S T).IsHomogeneous (cochargeDegree S) :=
  higherSpechtPolynomial_isHomogeneous S T

/-- The fixed-left-tableau span in Theorem 1.1 is the indicated irreducible
Specht module, with its actual induced permutation action. -/
theorem theorem_1_1_copies (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part))
    (hS : CatDominates S lam) :
    (springerFixedCopyOver ℂ lam part S).toSubmodule =
        Submodule.span ℂ (Set.range
          (fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
            Ideal.Quotient.mk (springerIdeal ℂ lam)
              (rename (finCongr (YoungDiagram.card_ofPartition part))
                (higherSpechtPolynomial (R := ℂ) S T)))) ∧
      Representation.IsIrreducible (springerFixedCopyOver ℂ lam part S).toRepresentation ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver ℂ part)
        (springerFixedCopyOver ℂ lam part S).toRepresentation) := by
  refine ⟨?_, ?_⟩
  · simpa only [springerFixedCopySpanOver] using
      (springerFixedCopyOver_toSubmodule ℂ lam part S)
  · exact corollary_8_1_springer_copy_irreducible (K := ℂ) lam part S hS
      (Or.inl (ringChar.eq_zero (R := ℂ)))

/-- Theorem 4.1: all allowed prefixes, descents, and multipliers are retained
by `GriffinIndex`, and the representatives below are exactly `E_eta F_T^S`. -/
theorem theorem_4_1_basis (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hlam : 0 < lam.card) (hheight : lam.colLen 0 ≤ s) :
    ∃ b : Basis (GriffinIndex n lam hk s) ℂ
        (PolynomialRing n ℂ ⧸ griffinIdeal ℂ n lam s),
      ∀ i, b i = Ideal.Quotient.mk (griffinIdeal ℂ n lam s)
        (rename (finCongr i.pair.card_eq)
            (higherSpechtPolynomial (R := ℂ) i.pair.left i.pair.right) *
          elementaryMultiplier n (n - lam.card) i.multiplier.rowLen) := by
  simpa only [IsSpecifiedBasis, griffinFamily, griffinPolynomial, pairPolynomial] using
    (HigherSpecht.theorem_4_1 ℂ n lam hk s hlam hheight)

/-- The multiplier contributes its actual partition size to the degree. -/
theorem theorem_4_1_degree {n : ℕ} {lam : YoungDiagram}
    {hk : lam.card ≤ n} {s : ℕ} (i : GriffinIndex n lam hk s) :
    (rename (finCongr i.pair.card_eq)
        (higherSpechtPolynomial (R := ℂ) i.pair.left i.pair.right) *
      elementaryMultiplier n (n - lam.card) i.multiplier.rowLen).IsHomogeneous
        (cochargeDegree i.pair.left + i.multiplier.card) := by
  simpa only [griffinPolynomial, pairPolynomial] using
    (griffinPolynomial_isHomogeneous (R := ℂ) i)

/-- The irreducible-copy clause of Theorem 4.1 concerns the span of those
same representatives while the right tableau varies. -/
theorem theorem_4_1_copies {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part)
    (hheight : lam.colLen 0 ≤ s) :
    (griffinFixedCopyOver ℂ lam hk s part i).toSubmodule =
        Submodule.span ℂ (Set.range
          (fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
            Ideal.Quotient.mk (griffinIdeal ℂ n lam s)
              (rename (finCongr (YoungDiagram.card_ofPartition part))
                  (higherSpechtPolynomial (R := ℂ) i.left T) *
                elementaryMultiplier n (n - lam.card) i.multiplier.rowLen))) ∧
      Representation.IsIrreducible (griffinFixedCopyOver ℂ lam hk s part i).toRepresentation ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver ℂ part)
        (griffinFixedCopyOver ℂ lam hk s part i).toRepresentation) := by
  refine ⟨?_, ?_⟩
  · simpa only [griffinFixedCopySpanOver] using
      (griffinFixedCopyOver_toSubmodule ℂ lam hk s part i)
  · exact corollary_8_1_griffin_copy_irreducible (K := ℂ) lam hk s part i
      (Or.inl (ringChar.eq_zero (R := ℂ))) hheight

/-- Theorem 5.2: the canonical common vectors give the correct Specht shape,
degree, directness, and every allowed harmonic-space equality simultaneously.
The eligibility predicate and the Specht-copy predicate are expanded here. -/
theorem theorem_5_2_literal (n s : ℕ) (hn : 0 < n) (hs : 0 < s) :
    (∀ i : FiniteHarmonicIndex n s,
      (∃ phi : Representation.IntertwiningMap (YoungIdealRepresentation (K := ℂ) i.part)
          (polynomialRepresentation ℂ n),
        Function.Injective phi ∧
          LinearMap.range phi.toLinearMap = finiteCommonHarmonicCopy i) ∧
      finiteCommonHarmonicCopy i ≤
        homogeneousSubmodule (Fin n) ℂ (cochargeDegree i.left + i.multiplier.card)) ∧
    iSupIndep (finiteCommonHarmonicCopy (n := n) (s := s)) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n), lam.colLen 0 ≤ s →
      ordinaryHarmonics (griffinIdeal ℂ n lam s) =
        ⨆ i : {i : FiniteHarmonicIndex n s //
            i.multiplier.colLen 0 ≤ n - lam.card ∧
              CatDominates (prefixTableau i.left lam.card
                (by simpa only [YoungDiagram.card_ofPartition] using hk)) lam},
          finiteCommonHarmonicCopy i.val := by
  simpa only [IsSpechtPolynomialCopy, UnboundedHarmonicIndex.degree,
    UnboundedHarmonicIndex.eligible] using
    (HigherSpecht.theorem_5_2 n s hn hs)

/-- Theorem 6.6: the actual untruncated common vectors give all partitions,
including the empty partition, with the stated local finiteness by degree. -/
theorem theorem_6_6_literal (n : ℕ) :
    (∀ i : UnboundedHarmonicIndex n,
      (∃ phi : Representation.IntertwiningMap (YoungIdealRepresentation (K := ℂ) i.part)
          (polynomialRepresentation ℂ n),
        Function.Injective phi ∧
          LinearMap.range phi.toLinearMap = untruncatedCommonHarmonicCopy i) ∧
      untruncatedCommonHarmonicCopy i ≤
        homogeneousSubmodule (Fin n) ℂ (cochargeDegree i.left + i.multiplier.card)) ∧
    iSupIndep (untruncatedCommonHarmonicCopy (n := n)) ∧
    (∀ d : ℕ, Set.Finite {i : UnboundedHarmonicIndex n |
      cochargeDegree i.left + i.multiplier.card = d}) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n),
      ordinaryHarmonics (untruncatedIdeal ℂ n lam) =
        ⨆ i : {i : UnboundedHarmonicIndex n //
            i.multiplier.colLen 0 ≤ n - lam.card ∧
              CatDominates (prefixTableau i.left lam.card
                (by simpa only [YoungDiagram.card_ofPartition] using hk)) lam},
          untruncatedCommonHarmonicCopy i.val := by
  simpa only [IsSpechtPolynomialCopy, UnboundedHarmonicIndex.degree,
    UnboundedHarmonicIndex.eligible] using
    (HigherSpecht.theorem_6_6 n)

end HigherSpecht.FinalStatementAudit

-- Each command reports the transitive axioms of the corresponding literal
-- statement above, including the imported proof on which it depends.
#print axioms HigherSpecht.FinalStatementAudit.theorem_1_1_basis
#print axioms HigherSpecht.FinalStatementAudit.theorem_1_1_degree
#print axioms HigherSpecht.FinalStatementAudit.theorem_1_1_copies
#print axioms HigherSpecht.FinalStatementAudit.theorem_4_1_basis
#print axioms HigherSpecht.FinalStatementAudit.theorem_4_1_degree
#print axioms HigherSpecht.FinalStatementAudit.theorem_4_1_copies
#print axioms HigherSpecht.FinalStatementAudit.theorem_5_2_literal
#print axioms HigherSpecht.FinalStatementAudit.theorem_6_6_literal
end
end CanonicalSource44

section CanonicalSource45
/- Source: audit/RequiredAxioms.lean -/


/-!
The complete required endpoint inventory. Each command reports Lean's transitive
axiom closure. This is a final consumer; it does not add hypotheses or proof rules.
The companion required_scope.json records mathematical correspondence, not a
verification certificate. Only a successful checked run supplies that evidence.
-/

-- Theorem 1.1
#print axioms HigherSpecht.springer_basis_target
#print axioms HigherSpecht.corollary_8_1_springer_copy_irreducible
#print axioms HigherSpecht.springerFixedCopyOver_toSubmodule
#print axioms HigherSpecht.FinalStatementAudit.theorem_1_1_basis
#print axioms HigherSpecht.FinalStatementAudit.theorem_1_1_degree
#print axioms HigherSpecht.FinalStatementAudit.theorem_1_1_copies

-- Theorem 3.2
#print axioms HigherSpecht.theorem_3_2_prefix_offDiagonal
#print axioms HigherSpecht.theorem_3_2_diagonal
#print axioms HigherSpecht.theorem_3_2_diagonal_pos
#print axioms HigherSpecht.higherSpechtApolarFunctional_apply
#print axioms HigherSpecht.theorem_3_2_selected_entry
#print axioms SpechtSelectedPairingAudit.literal_entry
#print axioms HigherSpecht.theorem_3_2_selected_family
#print axioms SpechtSelectedPairingAudit.literal_triangular_matrix
#print axioms HigherSpecht.columnInsertionSteps
#print axioms HigherSpecht.columnInsertionSteps_empty
#print axioms HigherSpecht.columnInsertion_pending_nil
#print axioms HigherSpecht.columnInsertion
#print axioms HigherSpecht.columnInsertion_state
#print axioms HigherSpecht.labeledCatRun_complete_unique
#print axioms HigherSpecht.columnInsertion_agrees_with_completed_run
#print axioms HigherSpecht.columnInsertion_output
#print axioms HigherSpecht.columnInsertion_rearrangementWitness

-- Theorem 4.1
#print axioms HigherSpecht.theorem_4_1
#print axioms HigherSpecht.griffin_specifiedBasis
#print axioms HigherSpecht.corollary_8_1_griffin_copy_irreducible
#print axioms HigherSpecht.griffinFixedCopyOver_toSubmodule
#print axioms HigherSpecht.FinalStatementAudit.theorem_4_1_basis
#print axioms HigherSpecht.FinalStatementAudit.theorem_4_1_degree
#print axioms HigherSpecht.FinalStatementAudit.theorem_4_1_copies

-- Corollary 4.3
#print axioms HigherSpecht.corollary_4_3_on_admissible_multipliers
#print axioms HigherSpecht.isDominanceTriangularMultiplier_iff_strictExpansion
#print axioms HigherSpecht.corollary_4_3_monomial
#print axioms HigherSpecht.corollary_4_3_schur
#print axioms HigherSpecht.corollary_4_3_copy_on_admissible_multipliers
#print axioms SpechtAlternativeMultiplierAudit.corollary_4_3_alternativeCopy_literal

-- Theorem 5.2
#print axioms HigherSpecht.theorem_5_2
#print axioms HigherSpecht.FinalStatementAudit.theorem_5_2_literal
#print axioms HigherSpecht.finiteCommonHarmonicVectorWithTableau_covariant
#print axioms HigherSpecht.finiteCommonHarmonicCopyWithTableau_eq
#print axioms HigherSpecht.theorem_5_2_any_right_tableaux
#print axioms HigherSpecht.complexSpechtYoungImage_finrank
#print axioms HigherSpecht.complexYoungIdealSpechtEquiv
#print axioms HigherSpecht.complexYoungIdealRepresentation_isIrreducible
#print axioms HigherSpecht.isSpechtPolynomialCopy_iff_complexSpecht
#print axioms HigherSpecht.theorem_5_2_actual_specht

-- Corollary 5.3
#print axioms HigherSpecht.GriffinIdealExpression.harmonic_decomposition
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_basis
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_frobenius
#print axioms HigherSpecht.corollary_5_3_distributive
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_alternative_basis_onEligible
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_finiteSum_basis
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_finiteIntersection_basis
#print axioms SpechtFiniteFamilyAudit.corollary_5_3_finiteFamily_literal
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_alternative_copy_onEligible
#print axioms SpechtAlternativeMultiplierAudit.corollary_5_3_alternativeCopy_literal
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_specht_copy
#print axioms ExpressionSpechtCopyAudit.finite_expression_copy
#print axioms HigherSpecht.corollary_5_3_finite_family_specht_copies
#print axioms ExpressionSpechtCopyAudit.finite_nonempty_family_copies

-- Corollary 5.5
#print axioms HigherSpecht.springerCommonHarmonicCopy_isSpecht
#print axioms HigherSpecht.springerCommonHarmonicCopies_iSupIndep
#print axioms HigherSpecht.corollary_5_5_decomposition
#print axioms HigherSpecht.corollary_5_5_master
#print axioms HigherSpecht.griffinApolarWitness_full
#print axioms HigherSpecht.griffinWitnessAlpha_full
#print axioms HigherSpecht.griffinWitnessRejection_full
#print axioms HigherSpecht.springerCommonHarmonicVector_literal_formula
#print axioms HigherSpecht.springerCommonHarmonicVectorWithTableau_literal_formula
#print axioms HigherSpecht.springerCommonHarmonicCopyWithTableau_eq
#print axioms HigherSpecht.corollary_5_5_any_right_tableaux
#print axioms HigherSpecht.corollary_5_5_actual_specht

-- Corollary 5.6
#print axioms HigherSpecht.corollary_5_6_basis
#print axioms HigherSpecht.corollary_5_6_frobenius
#print axioms HigherSpecht.untruncatedIdeal_weakDominanceJoin
#print axioms HigherSpecht.dominates_weakDominanceJoin_iff
#print axioms HigherSpecht.finiteEligibility_weakDominanceJoin

-- Corollary 5.7
#print axioms HigherSpecht.commonPairingMatrix_inverse_triangular
#print axioms HigherSpecht.adaptedMasterPolynomial
#print axioms HigherSpecht.adaptedMasterPolynomial_isHomogeneous
#print axioms HigherSpecht.corollary_5_7_of_factorial_isUnit
#print axioms HigherSpecht.corollary_5_7_localized
#print axioms HigherSpecht.corollary_5_7_field
#print axioms HigherSpecht.corollary_5_7_localized_copy
#print axioms HigherSpecht.corollary_5_7_field_copy
#print axioms HigherSpecht.adaptedGriffinCopy_eq_span

-- Theorem 6.1
#print axioms HigherSpecht.theorem_6_1_basis_and_rank
#print axioms HigherSpecht.theorem_6_1_dimension_and_cohenMacaulay
#print axioms HigherSpecht.theorem_6_1_frobenius_series
#print axioms HigherSpecht.elementaryFrobeniusDenominator_isUnit
#print axioms HigherSpecht.character_untruncatedGradedPiece
#print axioms ParameterPrincipalStatementAudit.parameter_action
#print axioms ParameterPrincipalStatementAudit.theorem61_basis_rank
#print axioms ParameterPrincipalStatementAudit.theorem61_representative_degree
#print axioms ParameterPrincipalStatementAudit.theorem61_dimension_cm

-- Remark 6.2
#print axioms HigherSpecht.untruncated_specified_parameter_basis_of_factorial_isUnit
#print axioms HigherSpecht.remark_6_2_untruncated_characteristic
#print axioms HigherSpecht.remark_6_2_untruncated_localized

-- Proposition 6.3
#print axioms HigherSpecht.proposition_6_3
#print axioms HigherSpecht.proposition_6_3_eligibility
#print axioms HigherSpecht.proposition_6_3_frobenius
#print axioms HigherSpecht.proposition_6_3_frobenius_target
#print axioms HigherSpecht.proposition_6_3_flat_lifting
#print axioms HigherSpecht.specialFiberPrescribedLiftBasis_apply
#print axioms HigherSpecht.zeroParameterBaseChangeEquiv_one_tmul_mk
#print axioms HigherSpecht.proposition_6_3_frobenius_quotient

-- Corollary 6.5
#print axioms HigherSpecht.integralMonomialParameterBasis_of_basis
#print axioms HigherSpecht.integralMonomialParameterBasis_of_basis_apply
#print axioms HigherSpecht.untruncatedIntegralMonomialParameterBasis
#print axioms HigherSpecht.untruncatedMonomialParameterBasis
#print axioms HigherSpecht.untruncated_parameter_flat_allCoefficients
#print axioms HigherSpecht.corollary_6_5_allFields
#print axioms HigherSpecht.lemma_6_4_griffin_degree_integral
#print axioms SpechtIntegralHilbertAudit.integral_degree_basis
#print axioms HigherSpecht.griffinHilbertFunction_independent_field
#print axioms SpechtIntegralHilbertAudit.degreewise_field_independence
#print axioms HigherSpecht.griffinMonomialDegreeBasis
#print axioms ParameterPrincipalStatementAudit.corollary65_arbitrary_integral_monomial_lift
#print axioms ParameterPrincipalStatementAudit.corollary65_monomial_basis_all_rings
#print axioms ParameterPrincipalStatementAudit.corollary65_all_fields
#print axioms ParameterPrincipalStatementAudit.corollary65_flat_all_rings

-- Theorem 6.6
#print axioms HigherSpecht.theorem_6_6
#print axioms HigherSpecht.FinalStatementAudit.theorem_6_6_literal
#print axioms HigherSpecht.untruncatedCommonHarmonicVectorWithTableau_covariant
#print axioms HigherSpecht.untruncatedCommonHarmonicCopyWithTableau_eq
#print axioms HigherSpecht.theorem_6_6_any_right_tableaux
#print axioms HigherSpecht.theorem_6_6_actual_specht

-- Corollary 6.7
#print axioms HigherSpecht.corollary_6_7_distributive
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_basis
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_frobenius
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_parameters
#print axioms HigherSpecht.UntruncatedIdealExpression.parameter_algebraicIndependent
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_finiteSum_basis
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_finiteIntersection_basis
#print axioms SpechtFiniteFamilyAudit.corollary_6_7_finiteFamily_literal
#print axioms HigherSpecht.UntruncatedIdealExpression.finiteSum_allSize
#print axioms HigherSpecht.UntruncatedIdealExpression.finiteIntersection_allSize
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_specht_copy
#print axioms ExpressionSpechtCopyAudit.untruncated_expression_copy
#print axioms HigherSpecht.corollary_6_7_finite_family_specht_copies
#print axioms ExpressionSpechtCopyAudit.untruncated_finite_nonempty_family_copies

-- Theorem 7.1
#print axioms HigherSpecht.theorem_7_1_parameter_fiber
#print axioms HigherSpecht.theorem_7_1_split_fiber
#print axioms HigherSpecht.theorem_7_1_number_of_factors
#print axioms HigherSpecht.theorem_7_1_after_scalar_extension
#print axioms HigherSpecht.distinctRootTensorEquiv
#print axioms HigherSpecht.theorem_7_1_algebraicClosure
#print axioms HigherSpecht.theorem_7_1_algebraicClosure_number_of_factors
#print axioms ParameterPrincipalStatementAudit.theorem71_parameter_fiber
#print axioms ParameterPrincipalStatementAudit.theorem71_factor_count
#print axioms ParameterPrincipalStatementAudit.theorem71_after_field_extension
#print axioms ParameterPrincipalStatementAudit.theorem71_algebraic_closure

-- Proposition 7.2
#print axioms HigherSpecht.proposition_7_2_integral_trivialization
#print axioms HigherSpecht.proposition_7_2_integral_trivialization_permutation
#print axioms HigherSpecht.proposition_7_2_integral_induced_tensor
#print axioms HigherSpecht.proposition_7_2_after_field_baseChange
#print axioms HigherSpecht.proposition_7_2_after_field_baseChange_permutation
#print axioms HigherSpecht.proposition_7_2_after_field_baseChange_induced
#print axioms HigherSpecht.proposition_7_2_no_parameters_identity
#print axioms HigherSpecht.orderedRootTrivialization_assigned_coordinate
#print axioms HigherSpecht.proposition_7_2_integral_trivialization_coordinate
#print axioms HigherSpecht.proposition_7_2_after_field_baseChange_coordinate
#print axioms HigherSpecht.proposition_7_2_no_parameters_permutation
#print axioms SpechtOrderedRootZeroAudit.proposition_7_2_no_parameters_equivariant_identity_literal

-- Proposition 7.3
#print axioms HigherSpecht.proposition_7_3_primary_decomposition
#print axioms HigherSpecht.coordinateIdeal_incomparable
#print axioms HigherSpecht.untruncatedIdeal_radical_eq_coordinate_intersection
#print axioms HigherSpecht.proposition_7_3_generic_component_length
#print axioms HigherSpecht.proposition_7_3_multiplicities
#print axioms HigherSpecht.proposition_7_3_standard_graded_multiplicity

-- Corollary 7.4
#print axioms HigherSpecht.untruncated_isReduced_iff
#print axioms HigherSpecht.parameterFiber_geometricallyReduced_iff
#print axioms HigherSpecht.parameterFiber_geometricallyReduced_iff_polynomial
#print axioms HigherSpecht.parameterFiber_geometricallyReduced_iff_squarefree
#print axioms HigherSpecht.parameterPolynomial_separable_iff_geometric_squarefree
#print axioms HigherSpecht.parameter_etale_atPrime_iff_polynomial

-- Corollary 7.5
#print axioms HigherSpecht.corollary_7_5_regularity
#print axioms HigherSpecht.hasUntruncatedTorRegularity_iff
#print axioms HigherSpecht.corollary_7_5_tor_regularity
#print axioms HigherSpecht.corollary_7_5_tor_support
#print axioms SpechtHomologicalAudit.regularity_statement

-- Corollary 7.6
#print axioms HigherSpecht.corollary_7_6_canonical_module
#print axioms HigherSpecht.corollary_7_6_canonical_degree_and_type
#print axioms HigherSpecht.corollary_7_6_gorenstein_iff_enlargedShape
#print axioms HigherSpecht.corollary_7_6_gorenstein_iff
#print axioms HigherSpecht.corollary_7_6_completeIntersection_iff
#print axioms HigherSpecht.untruncatedIdeal_column_eq_elementaryTail
#print axioms HigherSpecht.elementaryTailSequence_isRegular
#print axioms HigherSpecht.untruncated_regularSequencePresentation_of_full_row
#print axioms HigherSpecht.corollary_7_6_gorenstein_iff_completeIntersection
#print axioms SpechtHomologicalAudit.springer_socle_statement
#print axioms SpechtHomologicalAudit.canonical_module_statement
#print axioms SpechtHomologicalAudit.gorenstein_statement
#print axioms SpechtHomologicalAudit.complete_intersection_statement
#print axioms SpechtHomologicalAudit.gorenstein_iff_complete_intersection

-- Corollary 8.1
#print axioms HigherSpecht.corollary_8_1_griffin_characteristic
#print axioms HigherSpecht.corollary_8_1_springer_characteristic
#print axioms HigherSpecht.corollary_8_1_griffin_copy_irreducible
#print axioms HigherSpecht.corollary_8_1_springer_copy_irreducible
#print axioms HigherSpecht.corollary_8_1_griffin_localized
#print axioms HigherSpecht.corollary_8_1_springer_localized
#print axioms HigherSpecht.griffinFixedCopyOver_toSubmodule
#print axioms HigherSpecht.corollary_8_1_griffin_characteristic_all_partitions
#print axioms HigherSpechtAudit.griffin_characteristic_all_partitions_statement
#print axioms HigherSpecht.springerFixedCopyOver_toSubmodule
#print axioms ParameterPrincipalStatementAudit.corollary81_griffin_iff
#print axioms ParameterPrincipalStatementAudit.corollary81_springer_iff
#print axioms ParameterPrincipalStatementAudit.corollary81_griffin_localized
#print axioms ParameterPrincipalStatementAudit.corollary81_springer_localized
#print axioms ParameterPrincipalStatementAudit.corollary81_griffin_copy
#print axioms ParameterPrincipalStatementAudit.corollary81_springer_copy
end CanonicalSource45
