module
public import graph_foundation.part010
public import shared_results.part004
public import paper_results.part004

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.AlcoveCoefficientChange -/
section

/-!
# The integral cellular resolution and every coefficient specialization

The source is the literal resolution over ℤ, with the same face labels and
integer incidence signs. Tensoring its terms over ℤ and transporting the
polynomial action gives exactly the displayed resolution over A. This proves
the claimed universal specialization even when A is not flat over ℤ.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Polymatroid
open FourPapers.PolynomialCoefficientBaseChange
open scoped TensorProduct
universe u v
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
  (A : Type u) [CommRing A] (m : ℕ)

def finitePowerMonomialEquiv (k : Type*) [CommRing k] :
    monomialIdeal k (exponentPowerFamily (finiteRowFamily.{v} n E) m) ≃ₗ[
      MvPolynomial (FiniteVariable.{v} n) k] ↥((finiteSublatticeIdeal n (k:=k) E)^m) :=
  LinearEquiv.ofEq _ _ (finitePowerFamily_ideal (n := n) (k := k) E m)

/-- Coefficient change of the actual target ideal, proved by its monomial
basis and the exact ordinary-power identity. -/
def alcoveTargetBaseChange :
    (A ⊗[ℤ] ↥((finiteSublatticeIdeal n (k:=ℤ) E :
      Ideal (MvPolynomial (FiniteVariable.{v} n) ℤ))^m)) ≃ₗ[A]
        ↥((finiteSublatticeIdeal n (k:=A) E :
          Ideal (MvPolynomial (FiniteVariable.{v} n) A))^m) :=
  (LinearEquiv.baseChange ℤ A _ _
    ((finitePowerMonomialEquiv (E:=E) m ℤ).symm.restrictScalars ℤ)).trans
    ((FourPapers.monomialIdealCoefficientEquiv (R:=ℤ) (A:=A)
      (exponentPowerFamily (finiteRowFamily n E) m)).trans
      ((finitePowerMonomialEquiv (E:=E) m A).restrictScalars A))

theorem alcoveTargetBaseChange_tmul_val (a : A)
    (f : ↥((finiteSublatticeIdeal n (k:=ℤ) E :
      Ideal (MvPolynomial (FiniteVariable.{v} n) ℤ))^m)) :
    (alcoveTargetBaseChange (E:=E) A m (a ⊗ₜ[ℤ] f)).val=
      a • MvPolynomial.map (algebraMap ℤ A) f.val := by
  change ((finitePowerMonomialEquiv (E:=E) m A)
    (FourPapers.monomialIdealCoefficientEquiv (R:=ℤ) (A:=A)
      (exponentPowerFamily (finiteRowFamily n E) m)
        ((LinearEquiv.baseChange ℤ A _ _
          ((finitePowerMonomialEquiv (E:=E) m ℤ).symm.restrictScalars ℤ))
          (a ⊗ₜ[ℤ] f)))).val=_
  rw [LinearEquiv.baseChange_tmul]
  change (FourPapers.monomialIdealCoefficientEquiv (R:=ℤ) (A:=A)
    (exponentPowerFamily (finiteRowFamily n E) m)
      (a ⊗ₜ[ℤ] (finitePowerMonomialEquiv (E:=E) m ℤ).symm f)).val=_
  rw [FourPapers.monomialIdealCoefficientEquiv_tmul_val]
  rfl

def alcoveTargetRealization : Realization (R:=ℤ) (V:=FiniteVariable.{v} n) A
    ↥((finiteSublatticeIdeal n (k:=ℤ) E : Ideal (MvPolynomial (FiniteVariable.{v} n) ℤ))^m)
    ↥((finiteSublatticeIdeal n (k:=A) E : Ideal (MvPolynomial (FiniteVariable.{v} n) A))^m) where
  equivalence := alcoveTargetBaseChange A m
  multiply p z := by
    apply Subtype.ext
    induction z using TensorProduct.induction_on with
    | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, smul_zero]
    | add x y hx hy => simp only [map_add,smul_add,Submodule.coe_add,hx,hy,mul_add]
    | tmul a f =>
        simp only [LinearMap.baseChange_tmul,alcoveTargetBaseChange_tmul_val,
          sourceMultiply_apply,Submodule.coe_smul,smul_eq_mul,map_mul,mul_smul_comm]

/-- Coefficient scalars on the named projective-resolution term are exactly
the inherited action on the corresponding polynomial face submodule. -/
instance alcoveResolution_coefficientModule (k : Type*) [CommRing k] (p : ℕ) :
    Module k ((theorem81_cellularResolution (k := k) hE hne m).complex.X p) :=
  inferInstanceAs (Module k ↥(LabelledSimplicial.chainPiece (k := k)
    (X := FiniteVariable.{v} n) (alcoveFaces hE m) (p+1)))

instance alcoveResolution_coefficientTower (k : Type*) [CommRing k] (p : ℕ) :
    IsScalarTower k (MvPolynomial (FiniteVariable.{v} n) k)
      ((theorem81_cellularResolution (k := k) hE hne m).complex.X p) :=
  inferInstanceAs (IsScalarTower k (MvPolynomial (FiniteVariable.{v} n) k)
    ↥(LabelledSimplicial.chainPiece (k := k)
      (X := FiniteVariable.{v} n) (alcoveFaces hE m) (p+1)))

/-- Every term is the coefficient tensor product of the actual integer
term, with the identical oriented face basis and actual polynomial action. -/
def alcoveTermRealization (p : ℕ) : Realization (R:=ℤ) (V:=FiniteVariable.{v} n) A
    ((theorem81_cellularResolution (k:=ℤ) hE hne m).complex.X p)
    ((theorem81_cellularResolution (k:=A) hE hne m).complex.X p) :=
  LabelledSimplicial.termRealization (alcoveFaces hE m) (p+1)

def theorem81_cellularTermBaseChange (p : ℕ) :
    (A ⊗[ℤ] ((theorem81_cellularResolution (k:=ℤ) hE hne m).complex.X p)) ≃ₗ[A]
      ((theorem81_cellularResolution (k:=A) hE hne m).complex.X p) :=
  (alcoveTermRealization hE hne A m p).equivalence

/-- The named resolution has the literal labelled differential.  Keeping
this value equality separate avoids expanding a projective-resolution
record inside a coefficient-transfer construction. -/
theorem alcoveResolution_differential_hom (k : Type*) [CommRing k] (p : ℕ) :
    (((theorem81_cellularResolution (k := k) hE hne m).complex.d (p+1) p).hom) =
      (LabelledSimplicial.resolutionData (k := k) (alcoveFaces hE m)
        (alcoveFaces_downward hE m) (alcoveVertexLabel hE hne m)).differential p := by
  let D := LabelledSimplicial.resolutionData (k := k) (alcoveFaces hE m)
    (alcoveFaces_downward hE m) (alcoveVertexLabel hE hne m)
  exact congrArg (fun f : D.complex.X (p+1) ⟶ D.complex.X p => f.hom)
    (SubmoduleComplexData.complex_d D p)

theorem theorem81_cellularDifferential_baseChange (p : ℕ) :
    Realization.transfer (V := FiniteVariable.{v} n) A (alcoveTermRealization hE hne A m (p+1))
      (alcoveTermRealization hE hne A m p)
      (((theorem81_cellularResolution (k:=ℤ) hE hne m).complex.d (p+1) p).hom)=
        ((theorem81_cellularResolution (k:=A) hE hne m).complex.d (p+1) p).hom := by
  rw [alcoveResolution_differential_hom hE hne m ℤ p,
    alcoveResolution_differential_hom hE hne m A p]
  exact LabelledSimplicial.coefficientTransfer_differential (R := ℤ) (A := A)
    (X := FiniteVariable.{v} n)
    (alcoveFaces hE m) (alcoveFaces_downward hE m) (alcoveVertexLabel hE hne m) p

def alcoveAugmentation (k : Type*) [CommRing k] :
    ((theorem81_cellularResolution (k:=k) hE hne m).complex.X 0) →ₗ[
      MvPolynomial (FiniteVariable.{v} n) k]
      ↥((finiteSublatticeIdeal n (k:=k) E)^m) :=
  (alcoveResolutionTargetIso (k:=k) hE hne m).hom.hom.comp
    (LabelledSimplicial.augmentation (alcoveFaces hE m) (alcoveVertexLabel hE hne m))

@[simp] theorem alcoveAugmentation_val (k : Type*) [CommRing k]
    (z : (theorem81_cellularResolution (k:=k) hE hne m).complex.X 0) :
    (alcoveAugmentation hE hne m k z).val=
      LabelledSimplicial.augmentationPolynomial (alcoveFaces hE m)
        (alcoveVertexLabel hE hne m) z.val := rfl

theorem alcoveAugmentation_eq_resolution (k : Type*) [CommRing k] :
    alcoveAugmentation hE hne m k=
      ((theorem81_cellularResolution (k:=k) hE hne m).π.f 0).hom := by
  simp only [theorem81_cellularResolution,HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_zero,LabelledSimplicial.resolution,
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  rfl

theorem alcoveTermBaseChange_augmentation
    (z : A ⊗[ℤ] ((theorem81_cellularResolution.{0,v} (k:=ℤ) hE hne m).complex.X 0)) :
    alcoveTargetBaseChange (E:=E) A m
      (((alcoveAugmentation hE hne m ℤ).restrictScalars ℤ).baseChange A z)=
        alcoveAugmentation hE hne m A
          (theorem81_cellularTermBaseChange hE hne A m 0 z) := by
  apply Subtype.ext
  induction z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, Submodule.coe_zero]
  | add x y hx hy => simp only [map_add,Submodule.coe_add,hx,hy]
  | tmul a z =>
      let z' : LabelledSimplicial.chainPiece (k := ℤ) (X := FiniteVariable.{v} n)
          (alcoveFaces hE m) 1 := z
      rw [LinearMap.baseChange_tmul,alcoveTargetBaseChange_tmul_val,alcoveAugmentation_val]
      change a • MvPolynomial.map (algebraMap ℤ A)
          (LabelledSimplicial.augmentationPolynomial (alcoveFaces hE m)
            (alcoveVertexLabel hE hne m) z'.val)=
        LabelledSimplicial.augmentationPolynomial (alcoveFaces hE m)
          (alcoveVertexLabel hE hne m)
          (LabelledSimplicial.termBaseChange (R:=ℤ) (A:=A) (alcoveFaces hE m) 1
            (a ⊗ₜ[ℤ] z')).val
      simpa only [LinearMap.baseChange_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul,
        LinearMap.restrictScalars_apply, LinearMap.domRestrict_apply] using
        (LabelledSimplicial.termBaseChange_augmentation (R := ℤ) (A := A)
          (X := FiniteVariable.{v} n) (alcoveFaces hE m) (alcoveVertexLabel hE hne m)
          (a ⊗ₜ[ℤ] z'))

/-- Augmentations as well as differentials are the literal specializations
of the integer complex. Consequently the finite free cellular resolution
over A is precisely the base change of the one over ℤ. -/
theorem theorem81_cellularAugmentation_baseChange :
    Realization.transfer (V := FiniteVariable.{v} n) A (alcoveTermRealization hE hne A m 0)
      (alcoveTargetRealization (E:=E) A m)
      (((theorem81_cellularResolution (k:=ℤ) hE hne m).π.f 0).hom)=
        ((theorem81_cellularResolution (k:=A) hE hne m).π.f 0).hom := by
  rw [← alcoveAugmentation_eq_resolution,← alcoveAugmentation_eq_resolution]
  apply LinearMap.ext
  intro z
  obtain ⟨x,rfl⟩ := (alcoveTermRealization hE hne A m 0).equivalence.surjective z
  exact (Realization.transfer_equivalence (R := ℤ) (V := FiniteVariable.{v} n)
    A (alcoveTermRealization hE hne A m 0) (alcoveTargetRealization (E := E) A m)
    (alcoveAugmentation hE hne m ℤ) x).trans
      (alcoveTermBaseChange_augmentation hE hne A m x)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.NaturalProjectionPerturbation -/
section

/-!
# Perturbation with a natural projection

For an augmented Čech complex, the projections on intersection homology
can commute exactly with the Čech differential even when the chosen cycle
representatives do not. In that situation the transferred differential is
the displayed differential itself, and the transferred projection is the
original projection. No assertion about a spectral-sequence collapse is
assumed: these are identities of actual linear maps.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.HomologicalPerturbation.LinearContraction
variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : LinearContraction (R:=R) (M:=M) (H:=H))
  (δ : Module.End R M) (D : Module.End R H)
  (hP : C.projection.comp δ=D.comp C.projection)
  (u : (Module.End R M)ˣ) (hu : (u : Module.End R M)=1+δ*C.h)

include hP hu

theorem projection_perturbationUnit :
    C.projection.comp (u : Module.End R M)=C.projection := by
  ext x
  change C.projection ((u : Module.End R M) x)=C.projection x
  rw [hu]
  change C.projection (x+δ (C.h x))=C.projection x
  rw [map_add]
  have he := LinearMap.congr_fun hP (C.h x)
  change C.projection (δ (C.h x))=D (C.projection (C.h x)) at he
  rw [he,C.projection_homotopy_apply,map_zero,add_zero]

theorem projection_perturbationUnit_inv :
    C.projection.comp (↑(u⁻¹) : Module.End R M)=C.projection := by
  ext x
  have he := LinearMap.congr_fun
    (C.projection_perturbationUnit δ D hP u hu) ((↑(u⁻¹) : Module.End R M) x)
  change C.projection ((u : Module.End R M) ((↑(u⁻¹) : Module.End R M) x))=
    C.projection ((↑(u⁻¹) : Module.End R M) x) at he
  have hi : (u : Module.End R M) ((↑(u⁻¹) : Module.End R M) x)=x := by
    change ((u : Module.End R M)*(↑(u⁻¹) : Module.End R M)) x=x
    simp
  rw [hi] at he
  exact he.symm

theorem projection_correction :
    C.projection.comp (correction u δ)=D.comp C.projection := by
  rw [correction,show (↑(u⁻¹) : Module.End R M)*δ=
    (↑(u⁻¹) : Module.End R M).comp δ from rfl,
    ← LinearMap.comp_assoc,C.projection_perturbationUnit_inv δ D hP u hu,hP]

theorem transferredDifferential_eq_of_natural_projection :
    C.transferredDifferential δ u=D := by
  unfold transferredDifferential
  rw [← LinearMap.comp_assoc,C.projection_correction δ D hP u hu,
    LinearMap.comp_assoc,C.retract,LinearMap.comp_id]

theorem transferredProjection_eq_of_natural_projection :
    C.transferredProjection δ u=C.projection := by
  ext x
  change C.projection (x-correction u δ (C.h x))=C.projection x
  rw [map_sub]
  have he := LinearMap.congr_fun (C.projection_correction δ D hP u hu) (C.h x)
  change C.projection (correction u δ (C.h x))=D (C.projection (C.h x)) at he
  rw [he,C.projection_homotopy_apply,map_zero,sub_zero]

end FourPapers.HomologicalPerturbation.LinearContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealQuotientTorShift -/
section

/-! # The actual ideal-to-quotient Tor shift in nonzero fine degree

Creation by a variable occurring in the fine degree contracts the full
polynomial strand. An ideal cycle therefore lifts to a quotient cycle
one exterior degree higher. A quotient filling would give an ideal
filling by subtracting its unprojected boundary. This proves genuine
nonvanishing in Tor, including the shift from ideal homological degree
zero; it is not a numerical shift postulated for Betti tables.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

theorem quotientDegreeHomology_nontrivial_of_ideal
    (B : Family V) (α : Exponent V) (e : V) (he : 0 < α e) (p : ℕ)
    (h : Simplicial.NonzeroHomology (k := k) (koszulFaces B α) p) :
    Nontrivial (ClosedGraphDegreeHomology (k := k) B α (p+1)) := by
  obtain ⟨z, hz, hdz, hnonboundary⟩ := h
  have hzfull : z ∈ Simplicial.Chains (fullKoszulFaces α) p :=
    Simplicial.chains_mono (K := koszulFaces B α) (L := fullKoszulFaces α)
      (fun _ hs => hs.1) p hz
  let f := Simplicial.creation e z
  have hf : f ∈ Simplicial.Chains (fullKoszulFaces α) (p+1) :=
    creation_mem_chains e (fun _ hF => fullKoszulFaces_insert he hF) hzfull
  have hdf : Simplicial.boundary f = z := by
    dsimp only [f]
    rw [Simplicial.boundary_creation, hdz, map_zero, sub_zero]
  let q : TotalFaceModule (k := k) (quotientKoszulFaces B α) :=
    ⟨quotientFaceProjection B α f, relativeProjection_mem _ _ _ _⟩
  have hq : q ∈ totalFacePiece (quotientKoszulFaces B α) (p+1) :=
    quotientFaceProjection_degree B α (p+1) hf
  have hdq : quotientTotalDifferential B α q = 0 := by
    apply Subtype.ext
    change quotientFaceProjection B α
      (Simplicial.boundary (quotientFaceProjection B α f)) = 0
    rw [quotientFaceProjection_boundary B α (chains_mem_basisSpan hf), hdf]
    exact quotientFaceProjection_zero_on_ideal B α (chains_mem_basisSpan hz)
  let c : ClosedGraphDegreeCycles (k := k) B α (p+1) := ⟨q, hdq, hq⟩
  have hc : (Submodule.Quotient.mk c : ClosedGraphDegreeHomology (k := k) B α (p+1)) ≠ 0 := by
    intro hc
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hc
    have hyfull : y.val.val ∈ Simplicial.Chains (fullKoszulFaces α) (p+2) :=
      Simplicial.chains_mono (K := quotientKoszulFaces B α) (L := fullKoszulFaces α)
        (fun _ hs => hs.1) (p+2) y.property
    have hdy : Simplicial.boundary y.val.val ∈
        Simplicial.Chains (fullKoszulFaces α) (p+1) :=
      Simplicial.boundary_mem (fullKoszulFaces_downward α) hyfull
    have heq : quotientFaceProjection B α (Simplicial.boundary y.val.val) =
        quotientFaceProjection B α f :=
      congrArg (fun a : ClosedGraphDegreeCycles (k := k) B α (p+1) => a.val.val) hy
    let a := f - Simplicial.boundary y.val.val
    have hafull : a ∈ Simplicial.Chains (fullKoszulFaces α) (p+1) :=
      Submodule.sub_mem _ hf hdy
    have ha : a ∈ Simplicial.Chains (koszulFaces B α) (p+1) :=
      quotientFaceProjection_zero_mem_ideal_degree B α (p+1) hafull (by
        dsimp only [a]
        rw [map_sub, heq, sub_self])
    apply hnonboundary a ha
    dsimp only [a]
    rw [map_sub, hdf, Simplicial.boundary_boundary, sub_zero]
  exact ⟨⟨Submodule.Quotient.mk c, 0, hc⟩⟩

/-- The constructed class injects into the literal derived Tor of S/I. -/
theorem quotientTor_nonzero_of_ideal [Nontrivial k]
    (B : Family V) (α : Exponent V) (e : V) (he : 0 < α e) (p : ℕ)
    (h : Simplicial.NonzeroHomology (k := k) (koszulFaces B α) p) :
    ¬IsZero (finitePolynomialTor (p+1)
      (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B))) := by
  letI := quotientDegreeHomology_nontrivial_of_ideal B α e he p h
  intro hz
  letI : Subsingleton (finitePolynomialTor (p+1)
      (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B))) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  letI : Subsingleton
      ((ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
        (finitePolynomialTor (p+1)
          (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B)))) := by
    change Subsingleton (finitePolynomialTor (p+1)
      (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B)))
    infer_instance
  letI : Subsingleton ((quotientHomogeneousComplex (k := k) B α).homology (p+1)) :=
    (quotientToDerivedTor_injective B α (p+1)).subsingleton
  have hh : Subsingleton (ClosedGraphDegreeHomology (k := k) B α (p+1)) :=
    (quotientCategoricalDegreeHomologyEquiv B α (p+1)).symm.injective.subsingleton
  exact not_subsingleton _ hh

section Field
variable {K : Type u} [Field K]

theorem quotientTor_nonzero_of_idealBetti
    (B : Family V) (α : Exponent V) (hα : α ≠ 0) (p : ℕ)
    (h : bettiNumber (k := K) B α p ≠ 0) :
    ¬IsZero (finitePolynomialTor (p+1)
      (ModuleCat.of (MvPolynomial V K) (CoefficientQuotient (k := K) B))) := by
  obtain ⟨e, he⟩ : ∃ e, 0 < α e := by
    by_contra! hh
    apply hα
    ext e
    exact Nat.eq_zero_of_le_zero (hh e)
  exact quotientTor_nonzero_of_ideal B α e he p
    ((bettiNumber_pos_iff_faces B α p).mp (Nat.pos_of_ne_zero h))

end Field
end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphFiniteSupport -/
section

/-! # Explicit finite support of monomial-power Koszul homology

If the exponent of a variable in every monomial generator is at most `M`,
then every fine Koszul strand whose exponent in that variable exceeds `M`
is a cone. Exterior creation by that variable is the actual contracting
homotopy. For powers of the squarefree row monomials, `M = m`; consequently
ordinary homology is supported in degrees at most `card V * m`.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u

section CoordinateBounds
variable {V : Type*} [DecidableEq V]

/-- The bound concerns the genuine generators of the ordinary power. -/
theorem exponentPowerFamily_coordinate_le (B : Family V) (v : V) (M : ℕ)
    (hB : ∀ b ∈ B, b v ≤ M) (m : ℕ) :
    ∀ a ∈ exponentPowerFamily B m, a v ≤ m * M := by
  induction m with
  | zero =>
      intro a ha
      have ha0 : a = 0 := Finset.mem_singleton.mp ha
      subst a
      simp only [Finsupp.zero_apply, Nat.zero_mul, le_refl]
  | succ m ih =>
      intro a ha
      obtain ⟨⟨b,c⟩, hbc, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hb,hc⟩ := Finset.mem_product.mp hbc
      have hb' := ih b hb
      have hc' := hB c hc
      simp only [Finsupp.add_apply, Nat.succ_mul]
      omega

end CoordinateBounds

variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Inserting the chosen variable preserves the literal ideal-face
condition, because its generator exponent has already been exceeded. -/
theorem koszulFaces_insert_of_generator_bound (B : Family V) (α : Exponent V)
    (v : V) (M : ℕ) (hB : ∀ b ∈ B, b v ≤ M) (hα : M < α v)
    (F : Finset V) (hF : koszulFaces B α F) :
    koszulFaces B α (insert v F) := by
  refine ⟨?_, ?_⟩
  · intro w
    by_cases hw : w = v
    · subst w
      simp only [faceExponent_apply, Finset.mem_insert_self, if_true]
      omega
    · simpa only [faceExponent_apply, Finset.mem_insert, hw, false_or] using hF.1 w
  · obtain ⟨b, hb, hba⟩ := hF.2
    refine ⟨b, hb, ?_⟩
    intro w
    by_cases hw : w = v
    · subst w
      have hb' := hB b hb
      simp only [Finsupp.tsub_apply, faceExponent_apply, Finset.mem_insert_self, if_true]
      omega
    · simpa only [Finsupp.tsub_apply, faceExponent_apply, Finset.mem_insert,
        hw, false_or] using hba w

/-- This is actual exactness of every augmented face-chain degree,
including degree zero, with primitive given by exterior creation. -/
theorem monomial_fine_exact_of_generator_bound (B : Family V) (α : Exponent V)
    (v : V) (M : ℕ) (hB : ∀ b ∈ B, b v ≤ M) (hα : M < α v) (p : ℕ) :
    Simplicial.ExactIn (k := k) (koszulFaces B α) p :=
  Simplicial.exactIn_of_cone v (koszulFaces_insert_of_generator_bound B α v M hB hα) p

theorem monomial_fine_homology_subsingleton_of_generator_bound
    (B : Family V) (α : Exponent V) (v : V) (M : ℕ)
    (hB : ∀ b ∈ B, b v ≤ M) (hα : M < α v) (p : ℕ) :
    Subsingleton ((homogeneousComplex (k := k) B α).homology p) := by
  apply ModuleCat.subsingleton_of_isZero
  by_contra h
  have hn := (homogeneous_homology_nonzero_iff (k := k) B α p).mp h
  exact ((Simplicial.nonzeroHomology_iff_not_exactIn (koszulFaces B α) p).mp hn)
    (monomial_fine_exact_of_generator_bound B α v M hB hα p)

theorem exists_coordinate_gt_of_degree_gt (α : Exponent V) (M : ℕ)
    (hα : Fintype.card V * M < α.degree) : ∃ v, M < α v := by
  by_contra! h
  have hle : α.degree ≤ Fintype.card V * M := by
    rw [Finsupp.degree_eq_sum]
    calc
      ∑ v : V, α v ≤ ∑ _v : V, M := Finset.sum_le_sum (fun v _ => h v)
      _ = Fintype.card V * M := by simp
  omega

/-- A uniform exponent bound yields an explicit ordinary-degree bound. -/
theorem monomial_fine_homology_subsingleton_of_degree_gt
    (B : Family V) (M : ℕ) (hB : ∀ b ∈ B, ∀ v, b v ≤ M)
    (α : Exponent V) (hα : Fintype.card V * M < α.degree) (p : ℕ) :
    Subsingleton ((homogeneousComplex (k := k) B α).homology p) := by
  obtain ⟨v, hv⟩ := exists_coordinate_gt_of_degree_gt α M hα
  exact monomial_fine_homology_subsingleton_of_generator_bound B α v M
    (fun b hb => hB b hb v) hv p

/-- The chain group itself vanishes beyond the number of variables. -/
theorem monomial_fine_homology_subsingleton_of_exterior_degree_gt
    (B : Family V) (α : Exponent V) (p : ℕ) (hp : Fintype.card V < p) :
    Subsingleton ((homogeneousComplex (k := k) B α).homology p) := by
  apply ModuleCat.subsingleton_of_isZero
  by_contra h
  have hn := (homogeneous_homology_nonzero_iff (k := k) B α p).mp h
  apply ((Simplicial.nonzeroHomology_iff_not_exactIn (koszulFaces B α) p).mp hn)
  apply Simplicial.exactIn_of_no_face
  intro F _ hcard
  have hc := Finset.card_le_univ F
  omega

section Rows
variable {d : ℕ} {n : Fin d → ℕ}

theorem finiteRowFamily_coordinate_le_one (E : Finset (FiniteTuple n))
    (a : Exponent (FiniteVariable.{u} n)) (ha : a ∈ finiteRowFamily n E)
    (v : FiniteVariable.{u} n) : a v ≤ 1 := by
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rcases v with ⟨r, ⟨j⟩⟩
  simp only [finiteRowExponent_apply]
  split_ifs <;> omega

theorem finitePowerFamily_coordinate_le (E : Finset (FiniteTuple n)) (m : ℕ)
    (a : Exponent (FiniteVariable.{u} n))
    (ha : a ∈ exponentPowerFamily (finiteRowFamily n E) m)
    (v : FiniteVariable.{u} n) : a v ≤ m := by
  simpa only [Nat.mul_one] using exponentPowerFamily_coordinate_le
    (finiteRowFamily n E) v 1 (fun b hb => finiteRowFamily_coordinate_le_one E b hb v)
      m a ha

/-- The support bound holds for every row family, independently of any
lattice or closed-graph condition. It is valid over every coefficient ring. -/
theorem finitePowerFamily_homology_subsingleton_of_degree_gt
    (E : Finset (FiniteTuple n)) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n))
    (hα : Fintype.card (FiniteVariable.{u} n) * m < α.degree) (p : ℕ) :
    Subsingleton ((homogeneousComplex (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) α).homology p) :=
  monomial_fine_homology_subsingleton_of_degree_gt
    (exponentPowerFamily (finiteRowFamily n E) m) m
    (fun a ha v => finitePowerFamily_coordinate_le E m a ha v) α hα p

end Rows
end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.HomogeneousPowerCycleGeneration -/
section

/-! # Generation by homologically homogeneous first-power cycles

The proved crossing-block tensor decomposition can be used with homogeneous
factor cycles. This refinement retains their individual homological degrees;
it is the degree-sensitive input to the first-occurrence assertion of 5.3.
All representatives and boundaries below belong to the literal Koszul complex.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {k : Type u} [Field k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def homogeneousFirstPowerProductCycles (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    Set (PowerFaceModule (E := E) (k := k) m α) :=
  {z | ∃ β : Fin m → Exponent (FiniteVariable.{u} n),
    ∃ x : ∀ p, PowerFaceModule (E := E) (k := k) 1 (β p),
      (∑ p, β p) = α ∧
      (∀ p, powerFaceDifferential 1 (β p) (x p) = 0 ∧
        ∃ j, x p ∈ totalFacePiece
          (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) (β p)) j) ∧
      z.val = (List.ofFn (fun p => (x p).val)).prod}

def homogeneousProductCycleBoundarySpan (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    Submodule k (PowerFaceModule (E := E) (k := k) m α) :=
  Submodule.span k (homogeneousFirstPowerProductCycles m α) ⊔
    LinearMap.range (powerFaceDifferential m α)

lemma homogeneousProductCycleBoundarySpan_le_cycles (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) :
    homogeneousProductCycleBoundarySpan (E := E) (k := k) m α ≤
      LinearMap.ker (powerFaceDifferential m α) := by
  apply le_trans (sup_le_sup_right ?_ _)
    (productCycleBoundarySpan_le_cycles (E := E) (k := k) m α)
  apply Submodule.span_mono
  rintro z ⟨β, x, hβ, hx, hz⟩
  exact ⟨β, x, hβ, fun p => (hx p).1, hz⟩

lemma coveredBlockLift_cycle_homogeneousGenerated (hE : finiteLatticeClosed n E)
    {m : ℕ} {α : Exponent (FiniteVariable.{u} n)} (w : AdmissibleChain n E m α)
    (hw : CrossingCovered w.val (α - finiteChainShift n w.val))
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val)))
    (hx : quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val) x = 0) :
    chainTotalEquiv hE m α k (coveredBlockLift hE w hw x) ∈
      homogeneousProductCycleBoundarySpan m α := by
  let v := α - finiteChainShift n w.val
  let P := crossingBlockFaces w.val v
  let β := crossingBlockFineDegree w.val v
  let e := crossingBlockTensorEquiv (k := k) hE w.val v hw
  let c : PowerFaceModule (E := E) (k := k) m (∑ p, β p) ≃ₗ[k]
      PowerFaceModule (E := E) (k := k) m α :=
    facePredicateEquiv _ _ (fun F => by rw [crossingFineDegree_admissible w hw])
  let L := c.toLinearMap.comp (crossingLiftTensorProduct (k := k) hE w.val v)
  have hL (y) : powerFaceDifferential m α (L y) = L (finiteFaceTensorDifferential P y) := by
    apply Subtype.ext
    simp only [powerFaceDifferential, idealTotalDifferential_val, L, c,
      LinearMap.comp_apply, LinearEquiv.coe_coe, facePredicateEquiv_val]
    exact congrArg Subtype.val
      (LinearMap.congr_fun (crossingLiftTensorProduct_is_chain (k := k) hE w.val v) y)
  have hy : e.symm x ∈ LinearMap.ker (finiteFaceTensorDifferential P) := by
    change finiteFaceTensorDifferential P (e.symm x) = 0
    apply e.injective
    rw [map_zero]
    have he := LinearMap.congr_fun (crossingBlockTensorEquiv_is_chain (k := k)
      hE w.val v hw) (e.symm x)
    have hx' : quotientTotalDifferential (finiteChainCoefficientFamily n w.val) v x = 0 := hx
    simp only [e, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at he
    exact he.symm.trans hx'
  have hcycles := quotientFaceTensorHomogeneousCycles (k := k)
    (fun p => finitePredecessorFamily n E (w.val.val p).val)
    (fun p => finiteBlockDegree w.val p v)
  change LinearMap.ker (finiteFaceTensorDifferential P) = _ at hcycles
  rw [hcycles] at hy
  have hspan : Submodule.span k {z | ∃ y : ∀ p, TotalFaceModule (k := k) (P p),
      (∀ p, projectedTotalDifferential (P p) (y p) = 0 ∧
        ∃ j, y p ∈ totalFacePiece (P p) j) ∧ PiTensorProduct.tprod k y = z} ≤
      (homogeneousProductCycleBoundarySpan (E := E) (k := k) m α).comap L := by
    apply Submodule.span_le.mpr
    rintro z ⟨y, hy, rfl⟩
    apply Submodule.mem_sup_left
    apply Submodule.subset_span
    refine ⟨β, (fun p => crossingBlockLift (k := k) hE w.val v p (y p)),
      crossingFineDegree_admissible w hw, ?_, ?_⟩
    · intro p
      refine ⟨?_, ?_⟩
      · rw [crossingBlockLift_differential, (hy p).1, map_zero]
      · obtain ⟨j, hj⟩ := (hy p).2
        exact ⟨j, crossingBlockLift_preserves_degree hE w.val v p j (y p) hj⟩
    · change (crossingLiftTensorProduct hE w.val v (PiTensorProduct.tprod k y)).val = _
      simp only [crossingLiftTensorProduct, LinearMap.comp_apply, PiTensorProduct.map_tprod,
        idealPowerOrderedProduct_tprod_val]
  have hrange : LinearMap.range (finiteFaceTensorDifferential P) ≤
      (homogeneousProductCycleBoundarySpan (E := E) (k := k) m α).comap L := by
    rintro z ⟨y, rfl⟩
    apply Submodule.mem_sup_right
    exact ⟨L y, hL y⟩
  have hmem := (sup_le hspan hrange) hy
  change L (e.symm x) ∈ homogeneousProductCycleBoundarySpan m α at hmem
  simpa only [coveredBlockLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, crossingWholeLift, L, c, e] using hmem

lemma uncoveredBlockLift_cycle_homogeneousBoundary (hE : finiteLatticeClosed n E)
    {m : ℕ} {α : Exponent (FiniteVariable.{u} n)} (w : AdmissibleChain n E m α)
    (hw : ¬CrossingCovered w.val (α - finiteChainShift n w.val))
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val)))
    (hx : quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val) x = 0) :
    chainTotalEquiv hE m α k (uncoveredBlockLift hE w hw x) ∈
      LinearMap.range (powerFaceDifferential m α) := by
  let H := uncoveredBlockHomotopy (k := k) hE w hw
  let s := DFinsupp.lsingle (R := k) (M := fun z : AdmissibleChain n E m α =>
    TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n z.val)
      (α - finiteChainShift n z.val))) w
  refine ⟨chainTotalEquiv hE m α k (s (H x)), ?_⟩
  rw [←chainTotalEquiv_ordinary_differential]
  apply congrArg (chainTotalEquiv hE m α k)
  simp only [uncoveredBlockLift, contractibleBlockLift, LinearMap.add_apply,
    LinearMap.comp_apply, hx, map_zero, add_zero]
  rfl

lemma allPowerBlockLift_cycle_homogeneousGenerated (hE : finiteLatticeClosed n E)
    {m : ℕ} {α : Exponent (FiniteVariable.{u} n)} (w : AdmissibleChain n E m α)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val)))
    (hx : quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val) x = 0) :
    chainTotalEquiv hE m α k (allPowerBlockLift hE w x) ∈
      homogeneousProductCycleBoundarySpan m α := by
  unfold allPowerBlockLift
  split_ifs with hw
  · exact coveredBlockLift_cycle_homogeneousGenerated hE w hw x hx
  · exact Submodule.mem_sup_right (uncoveredBlockLift_cycle_homogeneousBoundary hE w hw x hx)

lemma allPowerChange_cycle_homogeneousGenerated (hE : finiteLatticeClosed n E)
    {m : ℕ} {α : Exponent (FiniteVariable.{u} n)} (x : ChainTotalModule n E m α k)
    (hx : chainTotalSpecialDifferential n E m α k x = 0) :
    chainTotalEquiv hE m α k (allPowerChange hE m α x) ∈ homogeneousProductCycleBoundarySpan m α := by
  let L := (chainTotalEquiv hE m α k).toLinearMap
  have he : L.comp (allPowerChange hE m α) =
      DFinsupp.lsum k (fun w => L.comp (allPowerBlockLift hE w)) := by
    apply DFinsupp.lhom_ext
    intro w y
    simp only [LinearMap.comp_apply, allPowerChange, DFinsupp.lsum_single]
  change (L.comp (allPowerChange hE m α)) x ∈ _
  rw [he, DFinsupp.lsum_apply_apply]
  apply Submodule.dfinsuppSumAddHom_mem
  intro w _
  apply allPowerBlockLift_cycle_homogeneousGenerated hE w (x w)
  exact congrArg (fun y : ChainTotalModule n E m α k => y w) hx

/-- Every cycle in every positive ordinary power is, modulo actual boundaries,
a linear combination of literal products of first-power cycles. All fine
degrees and all homological degrees are included. -/
theorem powerFaceCycles_homogeneousGenerated (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (α : Exponent (FiniteVariable.{u} n)) :
    LinearMap.ker (powerFaceDifferential (E := E) (k := k) m α) =
      Submodule.span k (homogeneousFirstPowerProductCycles m α) ⊔
        LinearMap.range (powerFaceDifferential m α) := by
  apply le_antisymm
  · intro z hz
    change z ∈ homogeneousProductCycleBoundarySpan m α
    obtain ⟨e, he, hchain⟩ := allPowerTotalChainEquiv_exists (k := k) hE m hm α
    let t := chainTotalEquiv hE m α k
    let x := e.symm (t.symm z)
    have hx : chainTotalSpecialDifferential n E m α k x = 0 := by
      apply e.injective
      rw [map_zero]
      have hc := LinearMap.congr_fun hchain x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
      rw [←hc]
      apply t.injective
      rw [map_zero, chainTotalEquiv_ordinary_differential]
      simpa only [x, t, LinearEquiv.apply_symm_apply] using
        (show powerFaceDifferential m α z = 0 from hz)
    have hmem := allPowerChange_cycle_homogeneousGenerated hE x hx
    rw [←he] at hmem
    simpa only [LinearEquiv.coe_coe, x, LinearEquiv.apply_symm_apply, t] using hmem
  · exact homogeneousProductCycleBoundarySpan_le_cycles m α

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.powerFaceCycles_homogeneousGenerated

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.PowerStrandDetection -/
section

/-! # Detecting a homogeneous product in a nonzero power strand

The input is the actual fine Tor Betti number. Its nonzero class is represented
by an exterior cycle, and projection to the specified exterior degree selects
a product of homogeneous first-power cycles which is still a nonboundary.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u

section FaceDegree
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
  (P : Finset V → Prop) (hP : Simplicial.Downward P)

lemma idealTotalDifferential_basis_zero (F : {F // P F}) (hF : F.val.card = 0) :
    idealTotalDifferential (k := k) hP (totalFaceBasis P F) = 0 := by
  apply Subtype.ext
  simp only [idealTotalDifferential_val, totalFaceBasis_val, Submodule.coe_zero]
  exact Simplicial.boundary_zero_degree_zero (Simplicial.basis_mem F.property hF)

lemma idealTotalDifferential_basis_lower (F : {F // P F}) :
    idealTotalDifferential (k := k) hP (totalFaceBasis P F) ∈
      Grading.Piece (totalFaceBasis P) (fun G => G.val.card) (F.val.card - 1) := by
  change _ ∈ Submodule.span k ((totalFaceBasis (k := k) P) '' {G | G.val.card = F.val.card - 1})
  rw [← totalFacePiece_eq_basis_span]
  by_cases hF : F.val.card = 0
  · rw [idealTotalDifferential_basis_zero P hP F hF]
    exact Submodule.zero_mem _
  · obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hF
    change (idealTotalDifferential hP (totalFaceBasis (k := k) P F)).val ∈
      Simplicial.Chains (k := k) P (F.val.card - 1)
    rw [idealTotalDifferential_val, totalFaceBasis_val]
    rw [hp, Nat.succ_sub_one]
    exact Simplicial.boundary_mem hP (Simplicial.basis_mem F.property hp)

end FaceDegree

variable {k : Type u} [Field k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

lemma homogeneousFirstPowerProductCycles_degree {m : ℕ}
    {α : Exponent (FiniteVariable.{u} n)}
    {z : PowerFaceModule (E := E) (k := k) m α}
    (hz : z ∈ homogeneousFirstPowerProductCycles m α) :
    ∃ p, z ∈ totalFacePiece
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) p := by
  obtain ⟨β, x, hβ, hx, hz⟩ := hz
  choose j hj using fun i => (hx i).2
  refine ⟨∑ i, j i, ?_⟩
  change z.val ∈ Simplicial.Chains _ _
  apply faceDegree_of_support _ _ z.property
  rw [hz]
  exact faceDegree_ordered_product m j (fun i => (x i).val)
    (fun i => faceDegree_forget _ _ (hj i))

/-- A nonzero genuine fine Tor strand contains a nonboundary product of
homologically homogeneous cycles from the first ordinary power. -/
theorem powerBetti_nonzero_homogeneous_product (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (α : Exponent (FiniteVariable.{u} n)) (p : ℕ)
    (hβ : bettiNumber (k := k) (exponentPowerFamily (finiteRowFamily n E) m) α p ≠ 0) :
    ∃ z ∈ homogeneousFirstPowerProductCycles (E := E) (k := k) m α,
      z ∈ totalFacePiece (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) p ∧
        z ∉ LinearMap.range (powerFaceDifferential m α) := by
  let P := koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α
  let hP := koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) m) α
  let b := totalFaceBasis (k := k) P
  let degree := fun F : {F // P F} => F.val.card
  let D := powerFaceDifferential (E := E) (k := k) m α
  obtain ⟨z, hz, hcycle, hnot⟩ :=
    (bettiNumber_pos_iff_faces _ α p).mp (Nat.pos_of_ne_zero hβ)
  let Z : PowerFaceModule (E := E) (k := k) m α := ⟨z, chains_mem_basisSpan hz⟩
  have hZ : Z ∈ Grading.Piece b degree p := by
    change Z ∈ Submodule.span k ((totalFaceBasis (k := k) P) '' {F | F.val.card = p})
    rw [← totalFacePiece_eq_basis_span]
    exact hz
  have hDZ : D Z = 0 := Subtype.ext hcycle
  have hZnot : Z ∉ LinearMap.range D := by
    intro h
    obtain ⟨y, hy, he⟩ := BasisHomology.homogeneous_filling b degree D
      (idealTotalDifferential_basis_lower P hP)
      (idealTotalDifferential_basis_zero P hP) p Z hZ h
    have hy' : y ∈ totalFacePiece (k := k) P (p + 1) := by
      rw [totalFacePiece_eq_basis_span]
      exact hy
    exact hnot y.val hy' (congrArg Subtype.val he)
  obtain ⟨x, hx, hp, hn⟩ := BasisHomology.exists_homogeneous_nonboundary b degree D
    (idealTotalDifferential_basis_lower P hP)
    (idealTotalDifferential_basis_zero P hP)
    (homogeneousFirstPowerProductCycles (E := E) (k := k) m α)
    (fun x hx => by
      obtain ⟨q, hq⟩ := homogeneousFirstPowerProductCycles_degree hx
      refine ⟨q, ?_⟩
      change x ∈ Submodule.span k ((totalFaceBasis (k := k) P) '' {F | F.val.card = q})
      rw [← totalFacePiece_eq_basis_span]
      exact hq)
    (le_of_eq (powerFaceCycles_homogeneousGenerated hE m hm α)) p Z hZ hDZ hZnot
  refine ⟨x, hx, ?_, hn⟩
  rw [totalFacePiece_eq_basis_span]
  exact hp

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.powerBetti_nonzero_homogeneous_product

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.WeightedChainFamily -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid Polynomial
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable (m : ℕ) (α : Exponent (FiniteVariable.{u} n))

def chainOrdinaryMatrix (hE : finiteLatticeClosed n E) :
    Matrix (ChainFaceIndex n E m α) (ChainFaceIndex n E m α) k :=
  LinearMap.toMatrix (chainTotalBasis n E m α k) (chainTotalBasis n E m α k)
    (chainTotalOrdinaryDifferential hE m α k)

def chainSpecialMatrix : Matrix (ChainFaceIndex n E m α) (ChainFaceIndex n E m α) k :=
  LinearMap.toMatrix (chainTotalBasis n E m α k) (chainTotalBasis n E m α k)
    (chainTotalSpecialDifferential n E m α k)

def chainChangeMatrix (hE : finiteLatticeClosed n E) :
    Matrix (ChainFaceIndex n E m α) (ChainFaceIndex n E m α) k :=
  LinearMap.toMatrix (chainTotalBasis n E m α k) (chainTotalBasis n E m α k)
    (allPowerChange (k := k) hE m α)

def chainMatrixWeight (a : ChainFaceIndex n E m α) : ℕ := finiteChainFactorWeight.{u} a.1.val

lemma blockMap_basis_weight_ne {R B : Type*} [CommRing R] {M : B → Type*}
    [∀i, AddCommGroup (M i)] [∀i, Module R (M i)] {J : B → Type*}
    (b : ∀i, Module.Basis (J i) R (M i)) (w : B → ℕ)
    (f : ∀i, Module.End R (M i)) (a c : Sigma J) (h : w a.1 ≠ w c.1) :
    (DFinsupp.basis b).repr (DFinsupp.mapRange.linearMap f ((DFinsupp.basis b) a)) c=0 := by
  rcases a with ⟨i,j⟩
  rcases c with ⟨r,t⟩
  have hir : i≠r := fun he => h (congrArg w he)
  rw [dfinsuppBasis_repr_apply,dfinsuppBasis_apply]
  simp [hir]

lemma chainSpecialMatrix_weight_preserving (i j : ChainFaceIndex n E m α)
    (h : chainMatrixWeight m α i ≠ chainMatrixWeight m α j) :
    chainSpecialMatrix (k := k) m α i j=0 := by
  rw [chainSpecialMatrix, LinearMap.toMatrix_apply]
  exact blockMap_basis_weight_ne
    (fun w : AdmissibleChain n E m α => totalFaceBasis (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
        (α-finiteChainShift n w.val)))
    (fun w => finiteChainFactorWeight.{u} w.val)
    (fun w => quotientTotalDifferential (k := k) (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val)) j i (Ne.symm h)

lemma chainSpecialMatrix_nonIncreasing :
    WeightedMatrix.NonIncreasing (chainMatrixWeight m α) (chainSpecialMatrix (E := E) (k := k) m α) := by
  intro i j hij
  exact chainSpecialMatrix_weight_preserving m α i j (ne_of_gt hij)

lemma chainOrdinaryMatrix_nonIncreasing (hE : finiteLatticeClosed n E) :
    WeightedMatrix.NonIncreasing (chainMatrixWeight m α) (chainOrdinaryMatrix (k := k) m α hE) := by
  intro i j hij
  have h := chainTotalDifferential_strictLower hE m α k j i hij.le
  rw [LinearMap.sub_apply,map_sub,Finsupp.sub_apply] at h
  rw [chainOrdinaryMatrix, LinearMap.toMatrix_apply]
  have hz := chainSpecialMatrix_weight_preserving (k := k) m α i j (ne_of_gt hij)
  rw [chainSpecialMatrix, LinearMap.toMatrix_apply] at hz
  rwa [hz, sub_zero] at h

lemma chainChangeMatrix_unitriangular (hE : finiteLatticeClosed n E) (hm : 0< m)
    (i j : ChainFaceIndex n E m α)
    (h : chainMatrixWeight m α j ≤ chainMatrixWeight m α i) :
    chainChangeMatrix (k := k) m α hE i j = if i=j then 1 else 0 := by
  rw [chainChangeMatrix, LinearMap.toMatrix_apply]
  have hh := allPowerChange_lower_basis (k := k) hE hm j i h
  rw [map_sub,Finsupp.sub_apply,Module.Basis.repr_self,Finsupp.single_apply] at hh
  convert sub_eq_zero.mp hh using 1 <;> simp only [eq_comm]

lemma chainMatrix_relation (hE : finiteLatticeClosed n E) :
    chainOrdinaryMatrix (k := k) m α hE * chainChangeMatrix m α hE =
      chainChangeMatrix m α hE * chainSpecialMatrix m α := by
  unfold chainOrdinaryMatrix chainChangeMatrix chainSpecialMatrix
  rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp,
    allPowerChange_is_chain]

/-- The literal integer-weight homogenization of the actual signed ordinary
Koszul matrix in its proved chain-normal-form basis. -/
def weightedChainDifferential (hE : finiteLatticeClosed n E) :
    Matrix (ChainFaceIndex n E m α) (ChainFaceIndex n E m α) k[X] :=
  WeightedMatrix.homogenize (chainMatrixWeight m α) (chainOrdinaryMatrix (k := k) m α hE)

def weightedChainComparison (hE : finiteLatticeClosed n E) :
    Matrix (ChainFaceIndex n E m α) (ChainFaceIndex n E m α) k[X] :=
  WeightedMatrix.homogenize (chainMatrixWeight m α) (chainChangeMatrix (k := k) m α hE)

theorem weightedChainComparison_isUnit (hE : finiteLatticeClosed n E) (hm : 0< m) :
    IsUnit (weightedChainComparison (k := k) m α hE) :=
  WeightedMatrix.homogenize_isUnit _ _ (chainChangeMatrix_unitriangular m α hE hm)

theorem weightedChainComparison_chain (hE : finiteLatticeClosed n E) (hm : 0< m) :
    weightedChainDifferential (k := k) m α hE * weightedChainComparison m α hE =
      weightedChainComparison m α hE * (chainSpecialMatrix m α).map C := by
  have h := (WeightedMatrix.homogenized_chain_isomorphism (chainMatrixWeight m α)
    (chainOrdinaryMatrix (k := k) m α hE) (chainSpecialMatrix m α) (chainChangeMatrix m α hE)
    (chainOrdinaryMatrix_nonIncreasing m α hE) (chainSpecialMatrix_nonIncreasing m α)
    (chainChangeMatrix_unitriangular m α hE hm) (chainMatrix_relation m α hE)).2
  rw [WeightedMatrix.homogenize_weight_preserving _ _ (chainSpecialMatrix_weight_preserving m α)] at h
  exact h

theorem weightedChainComparison_at_zero (hE : finiteLatticeClosed n E) (hm : 0< m)
    (i j : ChainFaceIndex n E m α) :
    (weightedChainComparison (k := k) m α hE i j).eval 0=(1 : Matrix _ _ k) i j :=
  WeightedMatrix.homogenize_unitriangular_at_zero _ _ (chainChangeMatrix_unitriangular m α hE hm) i j

@[simp] theorem weightedChainDifferential_at_one (hE : finiteLatticeClosed n E)
    (i j : ChainFaceIndex n E m α) :
    (weightedChainDifferential (k := k) m α hE i j).eval 1=chainOrdinaryMatrix m α hE i j :=
  WeightedMatrix.homogenize_at_one _ _ _ _

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AllPowerWeightLifting -/
section

/-! # Actual cycle lifting in the multichain weight filtration -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology FourPapers.Universal

theorem basisFiltration_level_eq_weightBelow
    {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis I R M) (w : I → ℕ) (n : ℕ) :
    (basisFiltration b w).level n = weightBelow b w n := by
  ext x
  exact basisFiltration_mem b w n x

theorem triangularEquiv_filtration
    {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis I R M) (w : I → ℕ) (e : M ≃ₗ[R] M)
    (hdiag : ∀ i, b.repr (e (b i)) i = 1)
    (htri : ∀ i j, i ≠ j → w i ≤ w j → b.repr (e (b i)) j = 0)
    (n : ℕ) (x : M) :
    e x ∈ (basisFiltration b w).level n ↔ x ∈ (basisFiltration b w).level n := by
  constructor
  · intro hx
    rw [basisFiltration_level_eq_weightBelow] at hx ⊢
    simpa only [LinearEquiv.symm_apply_apply] using
      triangularInverse_preserves b w e hdiag htri n hx
  · intro hx
    apply basisMap_preserves_of_coefficients b b w w e.toLinearMap _ n x hx
    intro i j hij
    exact htri i j (fun he => (ne_of_lt hij) (congrArg w he)) hij.le

universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def chainWeightFiltration (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    Filtration (K := k) (ChainTotalModule n E m α k) :=
  basisFiltration (chainTotalBasis n E m α k)
    (fun a => finiteChainFactorWeight.{u} a.1.val)

theorem chainSpecial_weight_homogeneous (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (a : ChainFaceIndex n E m α) :
    chainTotalSpecialDifferential n E m α k (chainTotalBasis n E m α k a) ∈
      Grading.Piece (chainTotalBasis n E m α k)
        (fun a => finiteChainFactorWeight.{u} a.1.val) (finiteChainFactorWeight.{u} a.1.val) := by
  rw [Grading.mem_piece]
  intro b hb
  by_contra hne
  have hz := chainSpecialMatrix_weight_preserving (k := k) m α b a hne
  exact hb (by simpa only [chainSpecialMatrix, LinearMap.toMatrix_apply] using hz)

/-- The all-power comparison is unitriangular, so both it and its inverse
preserve the actual finite weight filtration. This transports literal cycles,
not only numerical equality of homology ranks. -/
theorem allPower_chainWeight_liftsCycles (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (α : Exponent (FiniteVariable.{u} n)) :
    LiftsCycles (chainWeightFiltration (k := k) m α)
      (chainWeightFiltration (k := k) m α)
      (chainTotalOrdinaryDifferential hE m α k) := by
  obtain ⟨e, he, hchain⟩ := allPowerTotalChainEquiv_exists (k := k) hE m hm α
  have hdiag (i : ChainFaceIndex n E m α) :
      (chainTotalBasis n E m α k).repr (e (chainTotalBasis n E m α k i)) i = 1 := by
    have h := allPowerChange_lower_basis (k := k) hE hm i i le_rfl
    rw [← he] at h
    simpa only [LinearEquiv.coe_coe, map_sub, Finsupp.sub_apply,
      Module.Basis.repr_self, Finsupp.single_eq_same, sub_eq_zero] using h
  have htri (i j : ChainFaceIndex n E m α) (hij : i ≠ j)
      (hr : finiteChainFactorWeight.{u} i.1.val ≤ finiteChainFactorWeight.{u} j.1.val) :
      (chainTotalBasis n E m α k).repr (e (chainTotalBasis n E m α k i)) j = 0 := by
    have h := allPowerChange_lower_basis (k := k) hE hm i j hr
    rw [← he] at h
    simpa only [LinearEquiv.coe_coe, map_sub, Finsupp.sub_apply,
      Module.Basis.repr_self, Finsupp.single_eq_of_ne hij.symm, sub_zero] using h
  have hlevel := triangularEquiv_filtration (chainTotalBasis n E m α k)
    (fun a => finiteChainFactorWeight.{u} a.1.val) e hdiag htri
  exact liftsCycles_of_filteredEquiv (chainWeightFiltration (k := k) m α)
    (chainWeightFiltration (k := k) m α) (chainTotalSpecialDifferential n E m α k)
    (chainWeightFiltration (k := k) m α) (chainWeightFiltration (k := k) m α)
    (chainTotalOrdinaryDifferential hE m α k) e e hlevel hlevel
    (fun x => LinearMap.congr_fun hchain x)
    (basisHomogeneous_liftsCycles (chainTotalBasis n E m α k)
      (chainTotalBasis n E m α k) (fun a => finiteChainFactorWeight.{u} a.1.val)
      (fun a => finiteChainFactorWeight.{u} a.1.val)
      (chainTotalSpecialDifferential n E m α k) (chainSpecial_weight_homogeneous m α))

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.BottomTorInjection -/
section

/-! # The literal minimum multiplication is injective on Koszul homology -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology FourPapers.Universal

universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (μ : E) (hμ : ∀ a : E, μ.val ≤ a.val)
  (hE : finiteLatticeClosed n E) (m : ℕ) (α : Exponent (FiniteVariable.{u} n))

def bottomChainHomologyMap :
    Homology (chainTotalOrdinaryDifferential hE m α k)
      (chainTotalOrdinaryDifferential hE m α k)
      (chainTotalOrdinaryDifferential_square_zero hE m α k) →ₗ[k]
    Homology (chainTotalOrdinaryDifferential hE (m+1) (α + finiteRowExponent n μ.val) k)
      (chainTotalOrdinaryDifferential hE (m+1) (α + finiteRowExponent n μ.val) k)
      (chainTotalOrdinaryDifferential_square_zero hE (m+1) (α + finiteRowExponent n μ.val) k) :=
  threeTermHomologyMap (K := k)
    (X := ChainTotalModule n E m α k) (Y := ChainTotalModule n E m α k)
    (Z := ChainTotalModule n E m α k)
    (X' := ChainTotalModule n E (m+1) (α + finiteRowExponent n μ.val) k)
    (Y' := ChainTotalModule n E (m+1) (α + finiteRowExponent n μ.val) k)
    (Z' := ChainTotalModule n E (m+1) (α + finiteRowExponent n μ.val) k)
    (chainTotalOrdinaryDifferential hE m α k)
    (chainTotalOrdinaryDifferential hE m α k)
    (chainTotalOrdinaryDifferential_square_zero hE m α k)
    (chainTotalOrdinaryDifferential hE (m+1) (α + finiteRowExponent n μ.val) k)
    (chainTotalOrdinaryDifferential hE (m+1) (α + finiteRowExponent n μ.val) k)
    (chainTotalOrdinaryDifferential_square_zero hE (m+1) (α + finiteRowExponent n μ.val) k)
    (bottomChainMap μ hμ m α) (bottomChainMap μ hμ m α) (bottomChainMap μ hμ m α)
    (fun x => LinearMap.congr_fun (bottomChainMap_differential μ hμ hE m α) x)
    (fun x => LinearMap.congr_fun (bottomChainMap_differential μ hμ hE m α) x)

/-- Multiplication by the actual minimum generator is injective on the
homology of the actual signed upper Koszul complex, in every fine degree.
The proof works over every commutative coefficient ring. -/
theorem bottomChainHomologyMap_injective :
    Function.Injective (bottomChainHomologyMap (k := k) μ hμ hE m α) := by
  let F := basisFiltration (chainTotalBasis n E m α k)
    (fun a => reesVariableWeight (finiteTupleImage E) (finiteTupleToNat μ.val) +
      finiteChainFactorWeight.{u} a.1.val)
  let G := chainWeightFiltration (k := k) (E := E) (m+1)
    (α + finiteRowExponent n μ.val)
  apply threeTermHomologyMap_injective_of_filtered_retraction (K := k)
    (X := ChainTotalModule n E m α k)
    (Y := ChainTotalModule n E (m+1) (α + finiteRowExponent n μ.val) k) F G
    (chainTotalOrdinaryDifferential hE m α k) (chainTotalSpecialDifferential n E m α k)
    (chainTotalOrdinaryDifferential hE (m+1) (α + finiteRowExponent n μ.val) k)
    (chainTotalSpecialDifferential n E (m+1) (α + finiteRowExponent n μ.val) k)
    (chainTotalOrdinaryDifferential_square_zero hE m α k)
    (chainTotalOrdinaryDifferential_square_zero hE (m+1) (α + finiteRowExponent n μ.val) k)
    (bottomChainMap μ hμ m α) (bottomChainRetract μ hμ m α)
    (bottomChainMap_preserves μ hμ m α) (bottomChainRetract_preserves μ hμ m α)
    (fun x => LinearMap.congr_fun (bottomChainMap_differential μ hμ hE m α) x)
    (bottomChainRetract_map μ hμ m α) (bottomChainRetract_special μ hμ m α)
  · intro s x hx
    exact basisStrictLower_level (chainTotalBasis n E m α k) (chainTotalBasis n E m α k)
      _ _ (chainTotalOrdinaryDifferential hE m α k - chainTotalSpecialDifferential n E m α k)
      (fun a b hab => chainTotalDifferential_strictLower hE m α k a b (by omega)) s x hx
  · intro s y hy
    exact basisStrictLower_level
      (chainTotalBasis n E (m+1) (α + finiteRowExponent n μ.val) k)
      (chainTotalBasis n E (m+1) (α + finiteRowExponent n μ.val) k) _ _
      (chainTotalOrdinaryDifferential hE (m+1) (α + finiteRowExponent n μ.val) k -
        chainTotalSpecialDifferential n E (m+1) (α + finiteRowExponent n μ.val) k)
      (chainTotalDifferential_strictLower hE (m+1) (α + finiteRowExponent n μ.val) k) s y hy
  · exact allPower_chainWeight_liftsCycles hE (m+1) (Nat.zero_lt_succ m)
      (α + finiteRowExponent n μ.val)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AdmissibleReesWeights -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid
open scoped Polynomial

section Relations
variable {R : Type*} [Fintype R] [LinearOrder R]
variable {E : Finset (R → ℕ)}

/-- Precisely the strict inequalities selecting the displayed monic heads of
Proposition 2.2. No property of a Koszul complex or comparison map is assumed. -/
structure ReesWeightAdmissible (hE : LatticeClosed E) (ω : ReesVariable E → ℕ) : Prop where
  sorting : ∀ (a b : E), ¬ a.val ≤ b.val → ¬ b.val ≤ a.val →
    Finsupp.weight ω (sortingTailExponent hE a b) <
      Finsupp.weight ω (sortingHeadExponent a b)
  predecessor : ∀ (b a : E), b.val ≤ a.val → b.val ≠ a.val →
    Finsupp.weight ω (coefficientHeadExponent a b) <
      Finsupp.weight ω (coefficientHeadExponent b a)

lemma ReesWeightAdmissible.reduction_strict {hE : LatticeClosed E}
    {ω : ReesVariable E → ℕ} (hω : ReesWeightAdmissible hE ω)
    {c e : ReesVariable E →₀ ℕ} (h : ReesReductionStep hE c e) :
    Finsupp.weight ω e < Finsupp.weight ω c := by
  cases h with
  | sorting a b hab hba hdiv =>
    exact weight_replace_lt ω hdiv (hω.sorting a b hab hba)
  | coefficient b a hba hne hdiv =>
    exact weight_replace_lt ω hdiv (hω.predecessor b a hba hne)

/-- The already constructed normal form decreases every admissible weight.
The proof follows its actual monic reductions; its termination is justified by
the previously verified canonical weight and does not postulate division. -/
theorem reesNormalForm_admissible_weight_le (hE : LatticeClosed E)
    (ω : ReesVariable E → ℕ) (hω : ReesWeightAdmissible hE ω)
    (c : ReesVariable E →₀ ℕ) :
    Finsupp.weight ω (reesNormalForm hE c) ≤ Finsupp.weight ω c := by
  suffices h : ∀ q : ℕ, ∀ c : ReesVariable E →₀ ℕ, reesWeight E c = q →
      Finsupp.weight ω (reesNormalForm hE c) ≤ Finsupp.weight ω c from h _ c rfl
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro c hc
    by_cases hs : ReesStandard c
    · rw [reesNormalForm_of_standard hE hs]
    · obtain ⟨e, he⟩ := exists_reesReduction_of_not_standard hE c hs
      rw [reesNormalForm_eq_of_image_eq hE (reesReduction_image_eq he).symm]
      exact (ih _ ((reesReduction_weight_lt he).trans_eq hc) e rfl).trans
        (hω.reduction_strict he).le

theorem reesNormalForm_admissible_weight_lt (hE : LatticeClosed E)
    (ω : ReesVariable E → ℕ) (hω : ReesWeightAdmissible hE ω)
    {c : ReesVariable E →₀ ℕ} (hc : ¬ ReesStandard c) :
    Finsupp.weight ω (reesNormalForm hE c) < Finsupp.weight ω c := by
  obtain ⟨e, he⟩ := exists_reesReduction_of_not_standard hE c hc
  rw [reesNormalForm_eq_of_image_eq hE (reesReduction_image_eq he).symm]
  exact (reesNormalForm_admissible_weight_le hE ω hω e).trans_lt (hω.reduction_strict he)

end Relations

universe u v
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- An exact finite-variable weight extended by zero to unused columns. Every
relation head and tail in this sublattice uses only the finite variables. -/
def finiteWeightExtension (ω : FiniteReesVariable.{u} E → ℕ) :
    ReesVariable (finiteTupleImage E) → ℕ :=
  Function.extend (finiteReesVariableEmbedding E) ω (fun _ => 0)

@[simp] lemma finiteWeightExtension_embedding (ω : FiniteReesVariable.{u} E → ℕ)
    (x : FiniteReesVariable.{u} E) :
    finiteWeightExtension ω (finiteReesVariableEmbedding E x) = ω x :=
  (finiteReesVariableEmbedding E).injective.extend_apply ω _ x

lemma finiteWeightExtension_weight (ω : FiniteReesVariable.{u} E → ℕ)
    (c : FiniteReesVariable.{u} E →₀ ℕ) :
    Finsupp.weight (finiteWeightExtension ω) (c.embDomain (finiteReesVariableEmbedding E)) =
      Finsupp.weight ω c := by
  refine c.induction ?_ ?_
  · simp
  · intro x r c hx hr ih
    simp only [Finsupp.embDomain_add, Finsupp.embDomain_single, map_add,
      Finsupp.weight_single, finiteWeightExtension_embedding, ih]

/-- The strict monic Gröbner inequalities in the finite presentation. This is
a condition on the weights of the actual displayed relation heads and tails. -/
def FiniteReesWeightAdmissible (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) : Prop :=
  ReesWeightAdmissible (finiteTupleImage_closed hE) (finiteWeightExtension ω)

theorem finiteReesNormalForm_admissible_weight_le (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (hω : FiniteReesWeightAdmissible hE ω)
    (c : FiniteReesVariable.{u} E →₀ ℕ) :
    Finsupp.weight ω (finiteReesNormalForm hE c) ≤ Finsupp.weight ω c := by
  rw [← finiteWeightExtension_weight ω (finiteReesNormalForm hE c),
    finiteReesNormalForm_embedding, ← finiteWeightExtension_weight ω c]
  exact reesNormalForm_admissible_weight_le _ _ hω _

theorem finiteReesNormalForm_admissible_weight_lt (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (hω : FiniteReesWeightAdmissible hE ω)
    {c : FiniteReesVariable.{u} E →₀ ℕ} (hc : ¬ FiniteReesStandard c) :
    Finsupp.weight ω (finiteReesNormalForm hE c) < Finsupp.weight ω c := by
  rw [← finiteWeightExtension_weight ω (finiteReesNormalForm hE c),
    finiteReesNormalForm_embedding, ← finiteWeightExtension_weight ω c]
  exact reesNormalForm_admissible_weight_lt _ _ hω hc

lemma finiteCanonicalExponent_add_normal (hE : finiteLatticeClosed n E)
    (a b : finiteReesExponentMonoid.{u} E) :
    finiteCanonicalExponent hE (a + b) =
      finiteReesNormalForm hE (finiteCanonicalExponent hE a + finiteCanonicalExponent hE b) := by
  apply finiteReesStandard_image_injective hE
    (finiteCanonicalExponent_standard hE _) (finiteReesNormalForm_standard hE _)
  simp only [finiteCanonicalExponent_image, finiteReesNormalForm_image, map_add]
  rfl

@[simp] lemma finiteCanonicalExponent_zero (hE : finiteLatticeClosed n E) :
    finiteCanonicalExponent hE (0 : finiteReesExponentMonoid.{u} E) = 0 := by
  apply finiteReesStandard_image_injective hE (finiteCanonicalExponent_standard hE _)
  · simp [FiniteReesStandard]
  · simp only [finiteCanonicalExponent_image, map_zero]
    rfl

def admissibleStandardWeight (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (a : finiteReesExponentMonoid.{u} E) : ℕ :=
  Finsupp.weight ω (finiteCanonicalExponent hE a)

@[simp] lemma admissibleStandardWeight_zero (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) : admissibleStandardWeight hE ω 0 = 0 := by
  simp [admissibleStandardWeight]

lemma admissibleStandardWeight_subadd (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (hω : FiniteReesWeightAdmissible hE ω)
    (a b : finiteReesExponentMonoid.{u} E) :
    admissibleStandardWeight hE ω (a + b) ≤
      admissibleStandardWeight hE ω a + admissibleStandardWeight hE ω b := by
  unfold admissibleStandardWeight
  rw [finiteCanonicalExponent_add_normal]
  exact (finiteReesNormalForm_admissible_weight_le hE ω hω _).trans_eq (map_add _ _ _)

/-- The actual polynomial-parameter Rees algebra for an arbitrary admissible
integer weight, realized as a subalgebra of its monoid algebra. -/
def admissibleReesFamily (k : Type v) [CommRing k] (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (hω : FiniteReesWeightAdmissible hE ω) :
    Subalgebra k[X] (AddMonoidAlgebra k[X] (finiteReesExponentMonoid.{u} E)) :=
  weightedMonoidAlgebra (admissibleStandardWeight hE ω)
    (admissibleStandardWeight_zero hE ω) (admissibleStandardWeight_subadd hE ω hω)

def admissibleReesFamilyBasis (k : Type v) [CommRing k] (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (hω : FiniteReesWeightAdmissible hE ω) :
    Module.Basis (finiteReesExponentMonoid.{u} E) k[X] (admissibleReesFamily k hE ω hω) :=
  weightedMonoidBasis (admissibleStandardWeight hE ω)
    (admissibleStandardWeight_zero hE ω) (admissibleStandardWeight_subadd hE ω hω)

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.finiteReesNormalForm_admissible_weight_lt
#print axioms FourPapers.Sublattice.admissibleStandardWeight_subadd

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteReesRelationWeights -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def finiteSortingHeadExponent (a b : E) : FiniteReesVariable.{u} E →₀ ℕ :=
  Finsupp.single (Sum.inr a) 1 + Finsupp.single (Sum.inr b) 1

def finiteSortingTailExponent (hE : finiteLatticeClosed n E) (a b : E) :
    FiniteReesVariable.{u} E →₀ ℕ :=
  Finsupp.single (Sum.inr ⟨a.val ⊓ b.val, hE.1 a.val a.property b.val b.property⟩) 1 +
  Finsupp.single (Sum.inr ⟨a.val ⊔ b.val, hE.2 a.val a.property b.val b.property⟩) 1

def finiteCoefficientHeadExponent (b a : E) : FiniteReesVariable.{u} E →₀ ℕ :=
  (finiteRowExponent n b.val - finiteRowExponent n a.val).embDomain Function.Embedding.inl +
    Finsupp.single (Sum.inr a) 1

lemma finiteSortingHeadExponent_embedding (a b : E) :
    (finiteSortingHeadExponent.{u} a b).embDomain (finiteReesVariableEmbedding E) =
      sortingHeadExponent (finiteTupleImageEquiv E a) (finiteTupleImageEquiv E b) := by
  simp [finiteSortingHeadExponent, sortingHeadExponent, finiteReesVariableEmbedding,
    Finsupp.embDomain_add, Finsupp.embDomain_single]

lemma finiteSortingTailExponent_embedding (hE : finiteLatticeClosed n E) (a b : E) :
    (finiteSortingTailExponent.{u} hE a b).embDomain (finiteReesVariableEmbedding E) =
      sortingTailExponent (finiteTupleImage_closed hE) (finiteTupleImageEquiv E a) (finiteTupleImageEquiv E b) := by
  simp only [finiteSortingTailExponent, sortingTailExponent, Finsupp.embDomain_add,
    Finsupp.embDomain_single, finiteReesVariableEmbedding, Function.Embedding.sumMap,
    Equiv.toEmbedding, Sum.map_inr]
  congr 2 <;> apply Subtype.ext

lemma finiteCoefficientHeadExponent_embedding (b a : E) :
    (finiteCoefficientHeadExponent.{u} b a).embDomain (finiteReesVariableEmbedding E) =
      coefficientHeadExponent (finiteTupleImageEquiv E b) (finiteTupleImageEquiv E a) := by
  unfold finiteCoefficientHeadExponent coefficientHeadExponent
  rw [Finsupp.embDomain_add, Finsupp.embDomain_single]
  congr 1
  change ((finiteRowExponent n b.val - finiteRowExponent n a.val).embDomain
    Function.Embedding.inl).embDomain (finiteReesVariableEmbedding E) =
      (rowExponent (finiteTupleToNat b.val) - rowExponent (finiteTupleToNat a.val)).embDomain
        Function.Embedding.inl
  rw [← finiteRowExponent_embedding b.val, ← finiteRowExponent_embedding a.val,
    ← Finsupp.embDomain_tsub, ← Finsupp.embDomain_trans_apply, ← Finsupp.embDomain_trans_apply]
  rfl

lemma finiteSorting_exponent_images (hE : finiteLatticeClosed n E) (a b : E) :
    finiteReesExponentMap E (finiteSortingHeadExponent.{u} a b) =
      finiteReesExponentMap E (finiteSortingTailExponent hE a b) := by
  apply Finsupp.embDomain_injective finiteReesTargetEmbedding
  rw [finiteReesExponentMap_embedding, finiteReesExponentMap_embedding,
    finiteSortingHeadExponent_embedding, finiteSortingTailExponent_embedding]
  exact sorting_exponent_images _ _ _

lemma finiteCoefficient_exponent_images (b a : E) :
    finiteReesExponentMap E (finiteCoefficientHeadExponent.{u} b a) =
      finiteReesExponentMap E (finiteCoefficientHeadExponent a b) := by
  apply Finsupp.embDomain_injective finiteReesTargetEmbedding
  rw [finiteReesExponentMap_embedding, finiteReesExponentMap_embedding,
    finiteCoefficientHeadExponent_embedding, finiteCoefficientHeadExponent_embedding]
  exact coefficient_exponent_images _ _

/-- The finite relations have exactly the admissibility inequalities used by
the all-weights chain proof; extension to unused columns adds no condition. -/
theorem finiteReesWeightAdmissible_iff (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) :
    FiniteReesWeightAdmissible hE ω ↔
      (∀ a b : E, ¬ a.val ≤ b.val → ¬ b.val ≤ a.val →
        Finsupp.weight ω (finiteSortingTailExponent hE a b) <
          Finsupp.weight ω (finiteSortingHeadExponent a b)) ∧
      (∀ b a : E, b.val ≤ a.val → b.val ≠ a.val →
        Finsupp.weight ω (finiteCoefficientHeadExponent a b) <
          Finsupp.weight ω (finiteCoefficientHeadExponent b a)) := by
  constructor
  · intro hω
    constructor
    · intro a b hab hba
      rw [← finiteWeightExtension_weight ω, ← finiteWeightExtension_weight ω,
        finiteSortingHeadExponent_embedding, finiteSortingTailExponent_embedding]
      exact hω.sorting _ _ hab hba
    · intro b a hba hne
      rw [← finiteWeightExtension_weight ω, ← finiteWeightExtension_weight ω,
        finiteCoefficientHeadExponent_embedding, finiteCoefficientHeadExponent_embedding]
      exact hω.predecessor _ _ hba (fun h => hne (finiteTupleToNat_injective h))
  · rintro ⟨hs, hc⟩
    constructor
    · intro a b hab hba
      obtain ⟨a, rfl⟩ := (finiteTupleImageEquiv E).surjective a
      obtain ⟨b, rfl⟩ := (finiteTupleImageEquiv E).surjective b
      rw [← finiteSortingHeadExponent_embedding, ← finiteSortingTailExponent_embedding,
        finiteWeightExtension_weight, finiteWeightExtension_weight]
      exact hs a b hab hba
    · intro b a hba hne
      obtain ⟨b, rfl⟩ := (finiteTupleImageEquiv E).surjective b
      obtain ⟨a, rfl⟩ := (finiteTupleImageEquiv E).surjective a
      rw [← finiteCoefficientHeadExponent_embedding, ← finiteCoefficientHeadExponent_embedding,
        finiteWeightExtension_weight, finiteWeightExtension_weight]
      exact hc b a hba (fun h => hne (congrArg finiteTupleToNat h))

/-- Signed integer admissibility is stated directly for the actual finite
monic sorting and predecessor relations, with no positivity assumption. -/
structure SignedFiniteReesWeightAdmissible (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) : Prop where
  sorting : ∀ a b : E, ¬ a.val ≤ b.val → ¬ b.val ≤ a.val →
    Finsupp.weight ω (finiteSortingTailExponent hE a b) <
      Finsupp.weight ω (finiteSortingHeadExponent a b)
  predecessor : ∀ b a : E, b.val ≤ a.val → b.val ≠ a.val →
    Finsupp.weight ω (finiteCoefficientHeadExponent a b) <
      Finsupp.weight ω (finiteCoefficientHeadExponent b a)

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.finiteReesWeightAdmissible_iff

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AdmissibleChainWeights -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

lemma presentationWeight_embDomain {A B : Type*} (e : A ↪ B) (ω : B → ℕ)
    (c : A →₀ ℕ) : Finsupp.weight ω (c.embDomain e) = Finsupp.weight (fun a => ω (e a)) c := by
  refine c.induction ?_ ?_
  · simp
  · intro a r c ha hr ih
    simp only [Finsupp.embDomain_add, Finsupp.embDomain_single, map_add,
      Finsupp.weight_single, ih]

lemma finiteChainPresentation_add_coefficient {m : ℕ} (w : FiniteMultichain n E m)
    (a b : Exponent (FiniteVariable.{u} n)) :
    finiteChainPresentation w (a + b) =
      finiteChainPresentation w a + b.embDomain Function.Embedding.inl := by
  simp only [finiteChainPresentation, Finsupp.embDomain_add]
  abel

def admissibleIndexWeight (ω : FiniteReesVariable.{u} E → ℕ) {m : ℕ}
    (a : FiniteChainStandardIndex.{u} n E m) : ℕ :=
  Finsupp.weight ω (finiteChainPresentation a.1 a.2.val)

/-- Total coefficient-plus-exterior weight of one chain block in fixed fine
degree. The expression is independent of the exterior face. -/
def admissibleChainWeight (ω : FiniteReesVariable.{u} E → ℕ)
    (α : Exponent (FiniteVariable.{u} n)) {m : ℕ} (w : FiniteMultichain n E m) : ℕ :=
  Finsupp.weight ω (finiteChainPresentation w (α - finiteChainShift n w))

lemma admissibleChainWeight_eq (ω : FiniteReesVariable.{u} E → ℕ)
    (α : Exponent (FiniteVariable.{u} n)) {m : ℕ} (w : FiniteMultichain n E m) :
    admissibleChainWeight ω α w =
      Finsupp.weight (fun v => ω (Sum.inl v)) (α - finiteChainShift n w) +
        ∑ p, ω (Sum.inr (w.val p)) := by
  unfold admissibleChainWeight finiteChainPresentation
  rw [map_add, presentationWeight_embDomain, presentationWeight_embDomain,
    finiteChainMultiplicity_sum, map_sum]
  simp only [Finsupp.weight_single, one_nsmul]
  rfl

lemma admissibleChainWeight_face (ω : FiniteReesVariable.{u} E → ℕ)
    {m : ℕ} {α : Exponent (FiniteVariable.{u} n)} (a : ChainFaceIndex n E m α) :
    admissibleChainWeight ω α a.1.val =
      admissibleIndexWeight ω (chainFaceStandardIndex a) +
        Finsupp.weight (fun v => ω (Sum.inl v)) (faceExponent a.2.val) := by
  have he : finiteChainPresentation a.1.val (α - finiteChainShift n a.1.val) =
      finiteChainPresentation a.1.val
        ((α - finiteChainShift n a.1.val) - faceExponent a.2.val) +
          (faceExponent a.2.val).embDomain Function.Embedding.inl := by
    rw [← finiteChainPresentation_add_coefficient, tsub_add_cancel_of_le a.2.property.1]
  unfold admissibleChainWeight
  rw [he, map_add, presentationWeight_embDomain]
  rfl

lemma chainIndexMultiply_admissible_weight_le (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (hω : FiniteReesWeightAdmissible hE ω)
    {m : ℕ} (a : FiniteChainStandardIndex.{u} n E m) (v : FiniteVariable.{u} n) :
    admissibleIndexWeight ω (chainIndexMultiply hE a v) ≤
      admissibleIndexWeight ω a + ω (Sum.inl v) := by
  unfold admissibleIndexWeight
  rw [chainIndexMultiply_presentation]
  calc
    _ ≤ Finsupp.weight ω
        (finiteChainPresentation a.1 a.2.val + Finsupp.single (Sum.inl v) 1) :=
      finiteReesNormalForm_admissible_weight_le hE ω hω _
    _ = _ := by rw [map_add, Finsupp.weight_single, one_nsmul]

lemma chainIndexMultiply_admissible_weight_lt (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (hω : FiniteReesWeightAdmissible hE ω)
    {m : ℕ} (a : FiniteChainStandardIndex.{u} n E m) (v : FiniteVariable.{u} n)
    (ha : Contains (finiteChainCoefficientFamily n a.1) (a.2.val + Finsupp.single v 1)) :
    admissibleIndexWeight ω (chainIndexMultiply hE a v) <
      admissibleIndexWeight ω a + ω (Sum.inl v) := by
  unfold admissibleIndexWeight
  rw [chainIndexMultiply_presentation]
  have hn : ¬ FiniteReesStandard
      (finiteChainPresentation a.1 a.2.val + Finsupp.single (Sum.inl v) 1) := by
    rw [← finiteChainPresentation_add_row, finiteChainPresentation_standard_iff hE]
    exact fun h => h ha
  simpa only [map_add, Finsupp.weight_single, one_nsmul] using
    finiteReesNormalForm_admissible_weight_lt hE ω hω hn

lemma faceWeight_erase_add {V : Type*} [Fintype V] [LinearOrder V] [DecidableEq V]
    (ω : V → ℕ) (F : Finset V) (v : V) (hv : v ∈ F) :
    Finsupp.weight ω (faceExponent (F.erase v)) + ω v =
      Finsupp.weight ω (faceExponent F) := by
  have he : faceExponent (F.erase v) + Finsupp.single v 1 = faceExponent F := by
    ext x
    by_cases hx : x = v
    · subst x
      simp [faceExponent_apply, hv]
    · simp [faceExponent_apply, Finsupp.single_apply, hx, Ne.symm hx]
  simpa only [map_add, Finsupp.weight_single, one_nsmul] using
    congrArg (Finsupp.weight ω) he

lemma chainFaceErase_admissible_weight_le (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (hω : FiniteReesWeightAdmissible hE ω)
    {m : ℕ} {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) (v : FiniteVariable.{u} n) (hv : v ∈ a.2.val) :
    admissibleChainWeight ω α (chainFaceErase hE a v).1.val ≤
      admissibleChainWeight ω α a.1.val := by
  have hw := chainIndexMultiply_admissible_weight_le hE ω hω (chainFaceStandardIndex a) v
  have hf := faceWeight_erase_add (fun x => ω (Sum.inl x)) a.2.val v hv
  rw [← chainFaceErase_standard hE a v hv] at hw
  rw [admissibleChainWeight_face ω (chainFaceErase hE a v),
    admissibleChainWeight_face ω a, chainFaceErase_val]
  calc
    _ ≤ (admissibleIndexWeight ω (chainFaceStandardIndex a) + ω (Sum.inl v)) +
        Finsupp.weight (fun v => ω (Sum.inl v)) (faceExponent (a.2.val.erase v)) :=
      Nat.add_le_add_right hw _
    _ = _ := by rw [add_assoc, add_comm (ω (Sum.inl v)), hf]

lemma chainFaceErase_admissible_weight_lt (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (hω : FiniteReesWeightAdmissible hE ω)
    {m : ℕ} {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) (v : FiniteVariable.{u} n) (hv : v ∈ a.2.val)
    (hq : ¬ quotientKoszulFaces (finiteChainCoefficientFamily n a.1.val)
      (α - finiteChainShift n a.1.val) (a.2.val.erase v)) :
    admissibleChainWeight ω α (chainFaceErase hE a v).1.val <
      admissibleChainWeight ω α a.1.val := by
  have hf : fullKoszulFaces (α - finiteChainShift n a.1.val) (a.2.val.erase v) :=
    (faceExponent_mono (Finset.erase_subset v a.2.val)).trans a.2.property.1
  have hb : Contains (finiteChainCoefficientFamily n a.1.val)
      ((α - finiteChainShift n a.1.val) - faceExponent (a.2.val.erase v)) := by
    by_contra hn
    exact hq ⟨hf, hn⟩
  have hr := residual_erase_anyDecidable (α - finiteChainShift n a.1.val)
    (F := a.2.val) (x := v) a.2.property.1 hv
  have hb' : Contains (finiteChainCoefficientFamily n a.1.val)
      ((chainFaceStandardIndex a).2.val + Finsupp.single v 1) :=
    (congrArg (Contains (finiteChainCoefficientFamily n a.1.val)) hr).mp hb
  have hw := chainIndexMultiply_admissible_weight_lt hE ω hω (chainFaceStandardIndex a) v hb'
  have he := faceWeight_erase_add (fun x => ω (Sum.inl x)) a.2.val v hv
  rw [← chainFaceErase_standard hE a v hv] at hw
  rw [admissibleChainWeight_face ω (chainFaceErase hE a v),
    admissibleChainWeight_face ω a, chainFaceErase_val]
  calc
    _ < (admissibleIndexWeight ω (chainFaceStandardIndex a) + ω (Sum.inl v)) +
        Finsupp.weight (fun v => ω (Sum.inl v)) (faceExponent (a.2.val.erase v)) :=
      Nat.add_lt_add_right hw _
    _ = _ := by rw [add_assoc, add_comm (ω (Sum.inl v)), he]

theorem chainTotalDifferential_admissible_strictLower (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (hω : FiniteReesWeightAdmissible hE ω)
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k]
    (a c : ChainFaceIndex n E m α)
    (hc : admissibleChainWeight ω α a.1.val ≤ admissibleChainWeight ω α c.1.val) :
    (chainTotalBasis n E m α k).repr
      ((chainTotalOrdinaryDifferential hE m α k - chainTotalSpecialDifferential n E m α k)
        (chainTotalBasis n E m α k a)) c = 0 := by
  rw [LinearMap.sub_apply, chainTotalOrdinaryDifferential_basis,
    chainTotalSpecialDifferential_basis, ← Finset.sum_sub_distrib, map_sum,
    Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro v hv
  by_cases hq : quotientKoszulFaces (finiteChainCoefficientFamily n a.1.val)
      (α - finiteChainShift n a.1.val) (a.2.val.erase v.val)
  · rw [dif_pos hq, chainFaceErase_of_allowed hE a v.val hq, sub_self, map_zero]
    rfl
  · rw [dif_neg hq, sub_zero, map_zsmul_unit, Module.Basis.repr_self]
    have hne : chainFaceErase hE a v.val ≠ c := by
      intro he
      have hh := chainFaceErase_admissible_weight_lt hE ω hω a v.val v.property hq
      rw [he] at hh
      exact (not_lt_of_ge hc) hh
    simp [Finsupp.single_apply, hne]

theorem chainFaceProduct_admissible_weight_le (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (hω : FiniteReesWeightAdmissible hE ω)
    {r s : ℕ} {α β : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E r α) (b : ChainFaceIndex n E s β)
    (h : Disjoint a.2.val b.2.val) :
    admissibleChainWeight ω (α + β) (chainFaceProduct hE a b h).1.val ≤
      admissibleChainWeight ω α a.1.val + admissibleChainWeight ω β b.1.val := by
  have hw : admissibleIndexWeight ω
      (chainIndexProduct hE (chainFaceStandardIndex a) (chainFaceStandardIndex b)) ≤
      admissibleIndexWeight ω (chainFaceStandardIndex a) +
        admissibleIndexWeight ω (chainFaceStandardIndex b) := by
    unfold admissibleIndexWeight
    rw [chainIndexProduct_presentation]
    exact (finiteReesNormalForm_admissible_weight_le hE ω hω _).trans_eq (map_add _ _ _)
  rw [← chainFaceProduct_standard hE a b h] at hw
  rw [admissibleChainWeight_face ω (chainFaceProduct hE a b h),
    admissibleChainWeight_face ω a, admissibleChainWeight_face ω b,
    chainFaceProduct_face, faceExponent_union_of_disjoint _ _ h, map_add]
  omega

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.chainTotalDifferential_admissible_strictLower
#print axioms FourPapers.Sublattice.chainFaceProduct_admissible_weight_le

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.SignedReesWeightShift -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-!
# Removing positivity from the Rees weight

Add a sufficiently large multiple of the existing (fine plus auxiliary)
degree to the presentation weight. Every actual relation has this degree,
so its weight difference is unchanged. On a fixed fine/auxiliary component
the shift is constant, including on exterior factors. This proves, rather
than assumes, the reduction of arbitrary signed weights to positive ones.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

lemma finsupp_degree_embDomain {A B : Type*} (e : A ↪ B) (c : A →₀ ℕ) :
    (c.embDomain e).degree = c.degree := by
  refine c.induction ?_ ?_
  · simp
  · intro a r c ha hr ih
    simp only [Finsupp.embDomain_add, Finsupp.embDomain_single, map_add,
      Finsupp.degree_single, ih]

def finiteReesDegreeCost : FiniteReesVariable.{u} E → ℕ
  | Sum.inl _ => 1
  | Sum.inr _ => d + 1

lemma finiteReesDegreeCost_pos (v : FiniteReesVariable.{u} E) :
    0 < finiteReesDegreeCost v := by
  cases v <;> simp [finiteReesDegreeCost]

lemma finiteReesVariableExponent_degree (v : FiniteReesVariable.{u} E) :
    (finiteReesVariableExponent E v).degree = finiteReesDegreeCost v := by
  cases v with
  | inl v => simp [finiteReesVariableExponent, finiteReesDegreeCost]
  | inr a => simp [finiteReesVariableExponent, finiteReesDegreeCost,
      finsupp_degree_embDomain, finiteRowExponent_degree]

lemma finiteTargetExponent_degree (α : Exponent (FiniteVariable.{u} n)) (m : ℕ) :
    (finiteTargetExponent α m).degree = α.degree + m := by
  simp [finiteTargetExponent, finsupp_degree_embDomain]

def positiveReesWeightShift (ω : FiniteReesVariable.{u} E → ℤ) : ℕ :=
  (∑ v, (ω v).natAbs) + 1

def positiveReesWeight (ω : FiniteReesVariable.{u} E → ℤ)
    (v : FiniteReesVariable.{u} E) : ℕ :=
  (ω v + (positiveReesWeightShift ω : ℤ) * (finiteReesDegreeCost v : ℤ)).toNat

lemma positiveReesWeight_integer_pos (ω : FiniteReesVariable.{u} E → ℤ)
    (v : FiniteReesVariable.{u} E) :
    0 < ω v + (positiveReesWeightShift ω : ℤ) * (finiteReesDegreeCost v : ℤ) := by
  have habs : (ω v).natAbs < positiveReesWeightShift ω := by
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le (ω j).natAbs)
      (Finset.mem_univ v)
    exact lt_of_le_of_lt h (Nat.lt_succ_self _)
  have hneg : -ω v ≤ ((ω v).natAbs : ℤ) := by
    simpa using (Int.le_natAbs (a := -ω v))
  have hcost : (1 : ℤ) ≤ finiteReesDegreeCost v := by
    exact_mod_cast finiteReesDegreeCost_pos v
  have hshift : (0 : ℤ) ≤ positiveReesWeightShift ω := Int.natCast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hcost hshift
  have habs' : ((ω v).natAbs : ℤ) < positiveReesWeightShift ω := by
    exact_mod_cast habs
  nlinarith

lemma positiveReesWeight_cast (ω : FiniteReesVariable.{u} E → ℤ)
    (v : FiniteReesVariable.{u} E) :
    (positiveReesWeight ω v : ℤ) =
      ω v + (positiveReesWeightShift ω : ℤ) * (finiteReesDegreeCost v : ℤ) :=
  Int.toNat_of_nonneg (positiveReesWeight_integer_pos ω v).le

lemma positiveReesWeight_pos (ω : FiniteReesVariable.{u} E → ℤ)
    (v : FiniteReesVariable.{u} E) : 0 < positiveReesWeight ω v := by
  have h := positiveReesWeight_integer_pos ω v
  rw [← positiveReesWeight_cast] at h
  exact_mod_cast h

/-- The shift of every presentation monomial is its actual target degree.
It is not computed from a chosen normal form. -/
theorem positiveReesWeight_weight (ω : FiniteReesVariable.{u} E → ℤ)
    (c : FiniteReesVariable.{u} E →₀ ℕ) :
    (Finsupp.weight (positiveReesWeight ω) c : ℤ) =
      Finsupp.weight ω c + (positiveReesWeightShift ω : ℤ) *
        ((finiteReesExponentMap E c).degree : ℤ) := by
  refine c.induction ?_ ?_
  · simp
  · intro v r c hv hr ih
    simp only [map_add, Finsupp.weight_single, Nat.cast_add,
      finiteReesExponentMap, Finsupp.degree_single, map_nsmul,
      finiteReesVariableExponent_degree, nsmul_eq_mul, Nat.cast_mul] at ih ⊢
    rw [positiveReesWeight_cast, ih]
    push_cast
    ring

theorem positiveReesWeight_difference (ω : FiniteReesVariable.{u} E → ℤ)
    (c e : FiniteReesVariable.{u} E →₀ ℕ)
    (h : finiteReesExponentMap E c = finiteReesExponentMap E e) :
    (Finsupp.weight (positiveReesWeight ω) c : ℤ) -
        (Finsupp.weight (positiveReesWeight ω) e : ℤ) =
      Finsupp.weight ω c - Finsupp.weight ω e := by
  rw [positiveReesWeight_weight, positiveReesWeight_weight, h]
  ring

/-- Every signed admissible weight admits a strictly positive regrading with
exactly the same strict inequalities on the actual defining relations. -/
theorem positiveReesWeight_admissible (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω) :
    FiniteReesWeightAdmissible hE (positiveReesWeight ω) := by
  apply (finiteReesWeightAdmissible_iff hE _).mpr
  constructor
  · intro a b hab hba
    have h := positiveReesWeight_difference ω _ _ (finiteSorting_exponent_images hE a b)
    have hs := hω.sorting a b hab hba
    omega
  · intro b a hba hne
    have h := positiveReesWeight_difference ω _ _ (finiteCoefficient_exponent_images b a)
    have hs := hω.predecessor b a hba hne
    omega

def signedChainWeight (ω : FiniteReesVariable.{u} E → ℤ)
    (α : Exponent (FiniteVariable.{u} n)) {m : ℕ} (w : FiniteMultichain n E m) : ℤ :=
  Finsupp.weight ω (finiteChainPresentation w (α - finiteChainShift n w))

theorem positiveReesWeight_chainWeight (ω : FiniteReesVariable.{u} E → ℤ)
    (α : Exponent (FiniteVariable.{u} n)) {m : ℕ} (w : FiniteMultichain n E m)
    (hw : finiteChainShift n w ≤ α) :
    (admissibleChainWeight (positiveReesWeight ω) α w : ℤ) =
      signedChainWeight ω α w + (positiveReesWeightShift ω : ℤ) *
        ((α.degree : ℤ) + m) := by
  unfold admissibleChainWeight signedChainWeight
  rw [positiveReesWeight_weight, finiteChainPresentation_image,
    tsub_add_cancel_of_le hw, finiteTargetExponent_degree, Nat.cast_add]

/-- Every fixed-component weight difference, hence every differential or
comparison-matrix homogenizing exponent, is unchanged. -/
theorem positiveReesWeight_chainWeight_difference (ω : FiniteReesVariable.{u} E → ℤ)
    (α : Exponent (FiniteVariable.{u} n)) {m : ℕ} (a b : AdmissibleChain n E m α) :
    (admissibleChainWeight (positiveReesWeight ω) α a.val : ℤ) -
        (admissibleChainWeight (positiveReesWeight ω) α b.val : ℤ) =
      signedChainWeight ω α a.val - signedChainWeight ω α b.val := by
  rw [positiveReesWeight_chainWeight ω α a.val a.property,
    positiveReesWeight_chainWeight ω α b.val b.property]
  ring

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.positiveReesWeight_admissible
#print axioms FourPapers.Sublattice.positiveReesWeight_chainWeight_difference

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AdmissibleFirstPowerWeight -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid

section IndependentRank
variable {K M I : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-- The inverse of a fixed operator is independent of the well-founded weight
used to prove its invertibility. -/
lemma perturbationEquiv_rank_independent (b : Module.Basis I K M)
    (r s : I → ℕ) (D D₀ H : Module.End K M)
    (hr : ∀ i j, r i ≤ r j → b.repr ((D - D₀) (H (b i))) j = 0)
    (hs : ∀ i j, s i ≤ s j → b.repr ((D - D₀) (H (b i))) j = 0) :
    perturbationEquiv b r D D₀ H hr = perturbationEquiv b s D D₀ H hs := by
  apply LinearEquiv.toLinearMap_injective
  rw [perturbationEquiv_toLinearMap, perturbationEquiv_toLinearMap]

variable {B : Type*} {N : B → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module K (N i)]
variable {J : B → Type*}

lemma blockCorrectedSection_rank_independent (b : ∀ i, Module.Basis (J i) K (N i))
    (r s : B → ℕ) (a : B) (D : Module.End K (Π₀ i, N i))
    (D₀ : ∀ i, Module.End K (N i)) (H : ∀ i, i ≠ a → Module.End K (N i))
    (hr : ∀ i j : Sigma J, r i.1 ≤ r j.1 →
      (DFinsupp.basis b).repr ((D - blockSpecialDifferential D₀) ((DFinsupp.basis b) i)) j = 0)
    (hs : ∀ i j : Sigma J, s i.1 ≤ s j.1 →
      (DFinsupp.basis b).repr ((D - blockSpecialDifferential D₀) ((DFinsupp.basis b) i)) j = 0) :
    blockCorrectedSection b r a D D₀ H hr = blockCorrectedSection b s a D D₀ H hs := by
  unfold blockCorrectedSection blockKernelHomotopy
  rw [perturbationEquiv_rank_independent (DFinsupp.basis b)
    (fun i => r i.1) (fun i => s i.1) D (blockSpecialDifferential D₀)
    (blockPartialHomotopy a H) (blockPerturbationLower b r a D D₀ H hr)
    (blockPerturbationLower b s a D D₀ H hs)]

end IndependentRank

universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- The actual integral first-power section already constructed in the
canonical normal form is triangular for every admissible Gröbner weight.
Its formula is unchanged: only the proof controlling its support changes. -/
theorem firstPowerChainSection_admissible_lower (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℕ) (hω : FiniteReesWeightAdmissible hE ω)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
      (β - finiteChainShift n (firstPowerTarget hβ).val) F}) :
    firstPowerChainSection (k := k) hE hβ (totalFaceBasis _ F) -
        chainTotalBasis n E 1 β k ⟨firstPowerTarget hβ, F⟩ ∈
      weightBelow (chainTotalBasis n E 1 β k)
        (fun j => admissibleChainWeight ω β j.1.val)
        (admissibleChainWeight ω β (firstPowerTarget hβ).val) := by
  unfold firstPowerChainSection
  rw [blockCorrectedSection_rank_independent
    (fun w : AdmissibleChain n E 1 β => totalFaceBasis (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (β - finiteChainShift n w.val)))
    (fun w => finiteChainFactorWeight.{u} w.val)
    (fun w => admissibleChainWeight ω β w.val) (firstPowerTarget hβ)
    (chainTotalOrdinaryDifferential hE 1 β k)
    (fun w => quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
      (β - finiteChainShift n w.val))
    (firstPowerLowerHomotopy hE hβ) (chainTotalDifferential_strictLower hE 1 β k)
    (chainTotalDifferential_admissible_strictLower hE ω hω 1 β k)]
  exact blockCorrectedSection_lower_basis
    (fun w : AdmissibleChain n E 1 β => totalFaceBasis (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
        (β - finiteChainShift n w.val)))
    (fun w => admissibleChainWeight ω β w.val) (firstPowerTarget hβ)
    (chainTotalOrdinaryDifferential hE 1 β k)
    (fun w => quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
      (β - finiteChainShift n w.val))
    (firstPowerLowerHomotopy hE hβ)
    (chainTotalDifferential_admissible_strictLower hE ω hω 1 β k) F

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.firstPowerChainSection_admissible_lower

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AdmissiblePowerWeights -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {r s : ℕ}
variable (ω : FiniteReesVariable.{u} E → ℕ)

def admissiblePowerWeightedFaces (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (R : ℕ → Prop) (F : Finset (FiniteVariable.{u} n)) : Prop :=
  ∃a : ChainFaceIndex n E m α,a.2.val=F ∧ R (admissibleChainWeight ω α a.1.val)

def admissiblePowerWeightedSpan (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (R : ℕ → Prop) :
    Submodule k (Simplicial.Ambient (FiniteVariable.{u} n) k) :=
  basisSpan Simplicial.basis (admissiblePowerWeightedFaces ω (n := n) (E := E) m α R)

lemma admissiblePowerWeightedSpan_mono (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    {R T : ℕ → Prop} (h : ∀a,R a→T a) :
    admissiblePowerWeightedSpan ω (k := k) (E := E) m α R≤admissiblePowerWeightedSpan ω (E := E) m α T := by
  apply Submodule.span_mono
  apply Set.image_mono
  rintro F ⟨a,ha,hw⟩
  exact ⟨a,ha,h _ hw⟩

lemma admissiblePowerWeightedSpan_basis (α : Exponent (FiniteVariable.{u} n)) (R : ℕ → Prop)
    (a : ChainFaceIndex n E r α) (ha : R (admissibleChainWeight ω α a.1.val)) :
    Simplicial.basis (k := k) a.2.val∈admissiblePowerWeightedSpan ω (E := E) r α R :=
  Submodule.subset_span ⟨a.2.val,⟨a,rfl,ha⟩,rfl⟩

lemma admissiblePowerWeightedSpan_mul (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω)
    (α β : Exponent (FiniteVariable.{u} n)) (R S T : ℕ → Prop)
    (hbound : ∀a b c,R a→S b→c≤a+b→T c)
    {x y : Simplicial.Ambient (FiniteVariable.{u} n) k}
    (hx : x∈admissiblePowerWeightedSpan ω (E := E) r α R)
    (hy : y∈admissiblePowerWeightedSpan ω (E := E) s β S) :
    x*y∈admissiblePowerWeightedSpan ω (E := E) (r+s) (α+β) T := by
  apply faceSpan_mul_mem _ _ _ _ hx hy
  rintro F ⟨a,rfl,ha⟩ G ⟨b,rfl,hb⟩ hab
  exact ⟨chainFaceProduct hE a b hab,(chainFaceProduct_face hE a b hab).trans
      (finsetUnion_decidableEq _ _ _ _),
    hbound _ _ _ ha hb (chainFaceProduct_admissible_weight_le hE ω hω a b hab)⟩

lemma admissiblePowerWeightedSpan_mul_le (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω)
    (α β : Exponent (FiniteVariable.{u} n)) (A B : ℕ)
    {x y : Simplicial.Ambient (FiniteVariable.{u} n) k}
    (hx : x∈admissiblePowerWeightedSpan ω (E := E) r α (fun a => a≤A))
    (hy : y∈admissiblePowerWeightedSpan ω (E := E) s β (fun b => b≤B)) :
    x*y∈admissiblePowerWeightedSpan ω (E := E) (r+s) (α+β) (fun c => c≤A+B) :=
  admissiblePowerWeightedSpan_mul ω hE hω α β _ _ _ (by intros;omega) hx hy

lemma admissiblePowerWeightedSpan_mul_lt_left (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω)
    (α β : Exponent (FiniteVariable.{u} n)) (A B : ℕ)
    {x y : Simplicial.Ambient (FiniteVariable.{u} n) k}
    (hx : x∈admissiblePowerWeightedSpan ω (E := E) r α (fun a => a<A))
    (hy : y∈admissiblePowerWeightedSpan ω (E := E) s β (fun b => b≤B)) :
    x*y∈admissiblePowerWeightedSpan ω (E := E) (r+s) (α+β) (fun c => c<A+B) :=
  admissiblePowerWeightedSpan_mul ω hE hω α β _ _ _ (by intros;omega) hx hy

lemma admissiblePowerWeightedSpan_mul_lt_right (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω)
    (α β : Exponent (FiniteVariable.{u} n)) (A B : ℕ)
    {x y : Simplicial.Ambient (FiniteVariable.{u} n) k}
    (hx : x∈admissiblePowerWeightedSpan ω (E := E) r α (fun a => a≤A))
    (hy : y∈admissiblePowerWeightedSpan ω (E := E) s β (fun b => b<B)) :
    x*y∈admissiblePowerWeightedSpan ω (E := E) (r+s) (α+β) (fun c => c<A+B) :=
  admissiblePowerWeightedSpan_mul ω hE hω α β _ _ _ (by intros;omega) hx hy

lemma chainTotalEquiv_mem_admissiblePowerWeightedSpan (hE : finiteLatticeClosed n E)
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (A : ℕ)
    {x : ChainTotalModule n E m α k}
    (hx : x∈weightBelow (chainTotalBasis n E m α k)
      (fun a => admissibleChainWeight ω α a.1.val) A) :
    (chainTotalEquiv hE m α k x).val∈
      admissiblePowerWeightedSpan ω (E := E) m α (fun a => a<A) := by
  let b := chainTotalBasis n E m α k
  let f := (TotalFaceModule (k := k)
    (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α)).subtype.comp
      (chainTotalEquiv hE m α k).toLinearMap
  change f x∈_
  rw [←b.linearCombination_repr x,Finsupp.linearCombination_apply,Finsupp.sum,map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [map_smul]
  apply Submodule.smul_mem
  have hw : admissibleChainWeight ω α a.1.val<A := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp ha) (hx a (Nat.le_of_not_gt hn))
  change (chainTotalEquiv hE m α k (chainTotalBasis n E m α k a)).val∈_
  rw [chainTotalEquiv_basis,totalFaceBasis_val,chainFaceEquiv_val]
  exact admissiblePowerWeightedSpan_basis ω α _ a hw

lemma admissiblePowerWeightedSpan_to_chainTotal (hE : finiteLatticeClosed n E)
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (A : ℕ)
    (x : ChainTotalModule n E m α k)
    (hx : (chainTotalEquiv hE m α k x).val∈
      admissiblePowerWeightedSpan ω (E := E) m α (fun a => a<A)) :
    x∈weightBelow (chainTotalBasis n E m α k)
      (fun a => admissibleChainWeight ω α a.1.val) A := by
  let W := weightBelow (chainTotalBasis n E m α k)
    (fun a => admissibleChainWeight ω α a.1.val) A
  let f := (TotalFaceModule (k := k)
    (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α)).subtype.comp
      (chainTotalEquiv hE m α k).toLinearMap
  have hinj : Function.Injective f := fun a b h =>
    (chainTotalEquiv hE m α k).injective (Subtype.ext h)
  have hspan : admissiblePowerWeightedSpan ω (k := k) (E := E) m α (fun a => a<A)≤W.map f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨F,⟨a,rfl,ha⟩,rfl⟩
    refine ⟨chainTotalBasis n E m α k a,basis_mem_weightBelow _ _ ha,?_⟩
    change (chainTotalEquiv hE m α k (chainTotalBasis n E m α k a)).val=Simplicial.basis a.2.val
    rw [chainTotalEquiv_basis,totalFaceBasis_val,chainFaceEquiv_val]
  obtain ⟨y,hy,he⟩ := hspan hx
  exact hinj he ▸ hy

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AdmissibleOrderedProduct -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable (ω : FiniteReesVariable.{u} E → ℕ)

/-- A finite ordered product preserves the leading term whenever every factor
does so.  The strict estimate remains strict in every positive power. -/
theorem admissibleOrderedProduct_weight_control (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (m : ℕ)
    (β : Fin (m+1) → Exponent (FiniteVariable.{u} n)) (A : Fin (m+1) → ℕ)
    (x y : Fin (m+1) → Simplicial.Ambient (FiniteVariable.{u} n) k)
    (hy : ∀p,y p∈admissiblePowerWeightedSpan ω (E := E) 1 (β p) (fun a => a≤A p))
    (hδ : ∀p,x p-y p∈admissiblePowerWeightedSpan ω (E := E) 1 (β p) (fun a => a<A p)) :
    (List.ofFn x).prod∈admissiblePowerWeightedSpan ω (E := E) (m+1) (∑p,β p) (fun a => a≤∑p,A p) ∧
    (List.ofFn x).prod-(List.ofFn y).prod∈
      admissiblePowerWeightedSpan ω (E := E) (m+1) (∑p,β p) (fun a => a<∑p,A p) := by
  have hx (p) : x p∈admissiblePowerWeightedSpan ω (E := E) 1 (β p) (fun a => a≤A p) := by
    have hδ' := admissiblePowerWeightedSpan_mono ω (k := k) (E := E) 1 (β p)
      (fun _ h => h.le) (hδ p)
    simpa only [sub_add_cancel] using Submodule.add_mem _ hδ' (hy p)
  induction m with
  | zero =>
    simpa only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one,
      Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] using And.intro (hx 0) (hδ 0)
  | succ m ih =>
    have ht := ih (fun p => β p.succ) (fun p => A p.succ)
      (fun p => x p.succ) (fun p => y p.succ)
      (fun p => hy p.succ) (fun p => hδ p.succ) (fun p => hx p.succ)
    have hprod := admissiblePowerWeightedSpan_mul_le ω (k := k) (r := 1) (s := m+1) hE hω (β 0) (∑p : Fin (m+1),β p.succ)
      (A 0) (∑p : Fin (m+1),A p.succ) (hx 0) ht.1
    have hleft := admissiblePowerWeightedSpan_mul_lt_left ω (k := k) (r := 1) (s := m+1) hE hω (β 0) (∑p : Fin (m+1),β p.succ)
      (A 0) (∑p : Fin (m+1),A p.succ) (hδ 0) ht.1
    have hright := admissiblePowerWeightedSpan_mul_lt_right ω (k := k) (r := 1) (s := m+1) hE hω (β 0) (∑p : Fin (m+1),β p.succ)
      (A 0) (∑p : Fin (m+1),A p.succ) (hy 0) ht.2
    constructor
    · simpa only [List.ofFn_succ,List.prod_cons,Fin.sum_univ_succ,Nat.one_add] using hprod
    · have he : x 0*(List.ofFn (fun p : Fin (m+1) => x p.succ)).prod-
        y 0*(List.ofFn (fun p : Fin (m+1) => y p.succ)).prod =
        (x 0-y 0)*(List.ofFn (fun p : Fin (m+1) => x p.succ)).prod+
        y 0*((List.ofFn (fun p : Fin (m+1) => x p.succ)).prod-
          (List.ofFn (fun p : Fin (m+1) => y p.succ)).prod) := by noncomm_ring
      have hadd := Submodule.add_mem _ hleft hright
      rw [←he] at hadd
      simpa only [List.ofFn_succ,List.prod_cons,Fin.sum_univ_succ,Nat.one_add] using hadd

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AdmissibleCrossingLift -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}
variable (ω : FiniteReesVariable.{u} E → ℕ)

lemma singletonChain_admissibleWeight (β : Exponent (FiniteVariable.{u} n)) (a : E) :
    admissibleChainWeight ω β (singletonChain a) =
      Finsupp.weight (fun v => ω (Sum.inl v)) (β - finiteRowExponent n a.val) +
        ω (Sum.inr a) := by
  rw [admissibleChainWeight_eq, singletonChain_shift]
  simp [singletonChain]

theorem firstPowerExteriorLift_admissible_lower (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (F : {F // quotientKoszulFaces (finitePredecessorFamily n E a.val)
      (β - finiteRowExponent n a.val) F}) :
    (firstPowerExteriorLift (k := k) hE hβ (totalFaceBasis _ F)).val -
        Simplicial.basis F.val ∈
      admissiblePowerWeightedSpan ω (E := E) 1 β
        (fun r => r < admissibleChainWeight ω β (singletonChain a)) := by
  have h := chainTotalEquiv_mem_admissiblePowerWeightedSpan ω hE 1 β _
    (firstPowerChainSection_admissible_lower (k := k) hE ω hω hβ (firstPowerRawFace hβ F))
  simp only [map_sub, Submodule.coe_sub, chainTotalEquiv_basis, totalFaceBasis_val,
    chainFaceEquiv_val] at h
  change (chainTotalEquiv hE 1 β k
      (firstPowerChainSection hE hβ (firstPowerSourceCast hβ (totalFaceBasis _ F)))).val -
    Simplicial.basis F.val ∈ _
  rw [firstPowerSourceCast_basis]
  simpa only [firstPowerTarget, firstPowerRawFace] using h

theorem firstPowerRawFace_admissible_weight_le
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (F : {F // quotientKoszulFaces (finitePredecessorFamily n E a.val)
      (β - finiteRowExponent n a.val) F}) :
    Simplicial.basis (k := k) F.val ∈
      admissiblePowerWeightedSpan ω (E := E) 1 β
        (fun r => r ≤ admissibleChainWeight ω β (singletonChain a)) := by
  exact admissiblePowerWeightedSpan_basis ω β _
    ⟨firstPowerTarget hβ, firstPowerRawFace hβ F⟩ le_rfl

/-- The sum of the first-power block weights is the original chain weight;
both coefficient variables and exterior variables are included. -/
lemma crossing_admissibleWeight_sum {m : ℕ} (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (hv : CrossingCovered w v) :
    (∑ p, admissibleChainWeight ω (crossingBlockFineDegree w v p)
      (singletonChain (w.val p))) =
        admissibleChainWeight ω (∑ p, crossingBlockFineDegree w v p) w := by
  calc
    _ = ∑ p, (Finsupp.weight (fun x => ω (Sum.inl x)) (finiteBlockDegree w p v) +
        ω (Sum.inr (w.val p))) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [singletonChain_admissibleWeight, crossingBlockFineDegree, add_tsub_cancel_right]
    _ = Finsupp.weight (fun x => ω (Sum.inl x)) v + ∑ p, ω (Sum.inr (w.val p)) := by
      rw [Finset.sum_add_distrib, ← map_sum, finiteBlockDegree_sum w v hv]
    _ = _ := by
      rw [crossingBlockFineDegree_sum w v hv, admissibleChainWeight_eq,
        add_tsub_cancel_right]

theorem crossingWholeLift_admissible_lower (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω)
    (w : FiniteMultichain n E m) (hm : 0< m) (v : Exponent (FiniteVariable.{u} n))
    (hv : CrossingCovered w v)
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w) v F}) :
    (crossingWholeLift (k := k) hE w v hv (totalFaceBasis _ F)).val-Simplicial.basis F.val ∈
      admissiblePowerWeightedSpan ω (E := E) m (∑p,crossingBlockFineDegree w v p)
        (fun a => a<admissibleChainWeight ω (∑p,crossingBlockFineDegree w v p) w) := by
  cases m with
  | zero => omega
  | succ m =>
    let fs := crossingFaceFamily hE w v F
    let A := fun p => admissibleChainWeight ω (crossingBlockFineDegree w v p) (singletonChain (w.val p))
    let x := fun p => (crossingBlockLift (k := k) hE w v p (totalFaceBasis _ (fs p))).val
    let y := fun p => Simplicial.basis (k := k) (fs p).val
    have hy : ∀p,y p∈admissiblePowerWeightedSpan ω (E := E) 1 (crossingBlockFineDegree w v p)
        (fun a => a≤A p) := by
      intro p
      exact firstPowerRawFace_admissible_weight_le ω (k := k) (rowMaximum_block w p v)
        (crossingRawFace w v p (fs p))
    have hδ : ∀p,x p-y p∈admissiblePowerWeightedSpan ω (E := E) 1 (crossingBlockFineDegree w v p)
        (fun a => a<A p) := by
      intro p
      change (firstPowerExteriorLift (k := k) hE (rowMaximum_block w p v)
        (crossingBlockSourceCast w v p (totalFaceBasis _ (fs p)))).val-y p∈_
      rw [crossingBlockSourceCast_basis]
      exact firstPowerExteriorLift_admissible_lower ω hE hω (rowMaximum_block w p v)
        (crossingRawFace w v p (fs p))
    have hp := (admissibleOrderedProduct_weight_control ω hE hω m (crossingBlockFineDegree w v) A x y hy hδ).2
    have hA : (∑p,A p)=admissibleChainWeight ω (∑p,crossingBlockFineDegree w v p) w := crossing_admissibleWeight_sum ω w v hv
    rw [hA] at hp
    have hs : (crossingFaceShuffle hE w v F)⁻¹ •
        ((List.ofFn x).prod-(List.ofFn y).prod) ∈
        admissiblePowerWeightedSpan ω (k := k) (E := E) (m+1)
          (∑p,crossingBlockFineDegree w v p) (fun a => a<admissibleChainWeight ω (∑p,crossingBlockFineDegree w v p) w) :=
      (admissiblePowerWeightedSpan ω (k := k) (E := E) (m+1)
        (∑p,crossingBlockFineDegree w v p) (fun a => a<admissibleChainWeight ω (∑p,crossingBlockFineDegree w v p) w)).toAddSubgroup.zsmul_mem
        hp ((crossingFaceShuffle hE w v F)⁻¹).val
    change ((crossingLiftTensorProduct hE w v)
      ((crossingBlockTensorEquiv hE w v hv).symm (totalFaceBasis _ F))).val-
      Simplicial.basis F.val∈_
    rw [crossingBlockTensorEquiv_basis_decomposition]
    erw [LinearMapClass.map_smul_of_tower (S := k) (crossingLiftTensorProduct (k := k) hE w v)
      (crossingFaceShuffle hE w v F)⁻¹
      (⨂ₜ[k] p,totalFaceBasis (crossingBlockFaces w v p) (crossingFaceFamily hE w v F p))]
    simp only [Submodule.coe_smul_of_tower,crossingLiftTensorProduct,LinearMap.comp_apply,
      PiTensorProduct.map_tprod,idealPowerOrderedProduct_tprod_val]
    have he : (crossingFaceShuffle hE w v F)⁻¹ • (List.ofFn y).prod=Simplicial.basis F.val := by
      rw [crossingFace_product hE w v hv F]
      exact inv_smul_smul (crossingFaceShuffle hE w v F) (Simplicial.basis F.val)
    simpa only [smul_sub,he] using hs


end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.crossingWholeLift_admissible_lower

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AdmissibleAllPowersChange -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}
variable {α : Exponent (FiniteVariable.{u} n)}
variable (ω : FiniteReesVariable.{u} E → ℕ)

lemma coveredBlockLift_admissible_lower (hE : finiteLatticeClosed n E) (hω : FiniteReesWeightAdmissible hE ω) (hm : 0< m)
    (w : AdmissibleChain n E m α) (hw : CrossingCovered w.val (α-finiteChainShift n w.val))
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val) F}) :
    coveredBlockLift (k := k) hE w hw (totalFaceBasis _ F)-chainTotalBasis n E m α k ⟨w,F⟩ ∈
      weightBelow (chainTotalBasis n E m α k)
        (fun a => admissibleChainWeight ω α a.1.val) (admissibleChainWeight ω α w.val) := by
  apply admissiblePowerWeightedSpan_to_chainTotal ω hE m α (admissibleChainWeight ω α w.val)
  simp only [map_sub,Submodule.coe_sub,chainTotalEquiv_basis,totalFaceBasis_val,chainFaceEquiv_val,
    coveredBlockLift,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,facePredicateEquiv_val]
  have h := crossingWholeLift_admissible_lower ω (k := k) hE hω w.val hm (α-finiteChainShift n w.val) hw F
  simpa only [crossingFineDegree_admissible w hw] using h


lemma chainTotalDefect_block_admissible_lower (hE : finiteLatticeClosed n E) (hω : FiniteReesWeightAdmissible hE ω) (w : AdmissibleChain n E m α)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val))) :
    (chainTotalOrdinaryDifferential hE m α k-chainTotalSpecialDifferential n E m α k)
        (chainTotalSingle (k := k) w x) ∈
      weightBelow (chainTotalBasis n E m α k)
        (fun a => admissibleChainWeight ω α a.1.val) (admissibleChainWeight ω α w.val) := by
  let b := totalFaceBasis (k := k)
    (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val))
  rw [←b.linearCombination_repr x,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_sum]
  apply Submodule.sum_mem
  intro F hF
  rw [map_smul,map_smul]
  apply Submodule.smul_mem
  have hs : chainTotalSingle (k := k) w (b F)=chainTotalBasis n E m α k ⟨w,F⟩ :=
    (chainTotalBasis_apply n E m α k w F).symm
  rw [hs]
  exact fun j hj => chainTotalDifferential_admissible_strictLower hE ω hω m α k ⟨w,F⟩ j hj


lemma uncoveredBlockLift_admissible_lower (hE : finiteLatticeClosed n E) (hω : FiniteReesWeightAdmissible hE ω)
    (w : AdmissibleChain n E m α) (hw : ¬CrossingCovered w.val (α-finiteChainShift n w.val))
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val) F}) :
    uncoveredBlockLift (k := k) hE w hw (totalFaceBasis _ F)-chainTotalBasis n E m α k ⟨w,F⟩ ∈
      weightBelow (chainTotalBasis n E m α k)
        (fun a => admissibleChainWeight ω α a.1.val) (admissibleChainWeight ω α w.val) := by
  have hc := (uncoveredBlock_contraction (k := k) hE w hw).choose_spec.1
  have he := LinearMap.congr_fun (contractibleBlockLift_sub
    (chainTotalOrdinaryDifferential hE m α k)
    (quotientTotalDifferential (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val))
    (uncoveredBlockHomotopy (k := k) hE w hw) (chainTotalSingle (k := k) w) hc) (totalFaceBasis _ F)
  simp only [LinearMap.sub_apply,LinearMap.comp_apply] at he
  rw [chainTotalBasis_apply]
  change contractibleBlockLift _ _ _ _ (totalFaceBasis _ F)-chainTotalSingle (k := k) w (totalFaceBasis _ F)∈_
  rw [he]
  change chainTotalOrdinaryDifferential hE m α k (chainTotalSingle (k := k) w _) -
    chainTotalSingle (k := k) w (quotientTotalDifferential _ _ _)∈_
  rw [←chainTotalSpecial_lsingle]
  exact chainTotalDefect_block_admissible_lower ω hE hω w _


lemma allPowerBlockLift_admissible_lower (hE : finiteLatticeClosed n E) (hω : FiniteReesWeightAdmissible hE ω) (hm : 0< m)
    (w : AdmissibleChain n E m α)
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val) F}) :
    allPowerBlockLift (k := k) hE w (totalFaceBasis _ F)-chainTotalBasis n E m α k ⟨w,F⟩ ∈
      weightBelow (chainTotalBasis n E m α k)
        (fun a => admissibleChainWeight ω α a.1.val) (admissibleChainWeight ω α w.val) := by
  unfold allPowerBlockLift
  split_ifs
  · exact coveredBlockLift_admissible_lower ω hE hω hm w _ F
  · exact uncoveredBlockLift_admissible_lower ω hE hω w _ F


lemma allPowerChange_admissible_lower (hE : finiteLatticeClosed n E) (hω : FiniteReesWeightAdmissible hE ω) (hm : 0< m)
    (a : ChainFaceIndex n E m α) :
    allPowerChange (k := k) hE m α (chainTotalBasis n E m α k a)-chainTotalBasis n E m α k a ∈
      weightBelow (chainTotalBasis n E m α k)
        (fun b => admissibleChainWeight ω α b.1.val) (admissibleChainWeight ω α a.1.val) := by
  rw [allPowerChange_basis]
  exact allPowerBlockLift_admissible_lower ω hE hω hm a.1 a.2


end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.allPowerChange_admissible_lower

end
end


end
