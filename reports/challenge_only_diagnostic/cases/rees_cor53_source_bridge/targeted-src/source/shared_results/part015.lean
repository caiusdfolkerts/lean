module
public import graph_foundation.part012
public import shared_results.part014

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.GroebnerReesBasis -/
section

/-! # Coordinates on the actual multi-Rees algebra of arbitrary ideals

The coefficient at a color exponent belongs to the literal mixed product.
The coefficient algebra is identified by unchanged polynomial values with
`CommAlg.multiReesAlgebra`. Its triangular basis is constructed from the
actual Gröbner bases of the mixed ideals.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.MixedTransfer

open Classical CommAlg FourPapers.Sublattice MvPolynomial
open scoped BigOperators

variable {K V C : Type*} [Fintype C] [DecidableEq C] [CommRing K]
  (J : C → Ideal (MvPolynomial V K))

abbrev idealPowerPiece (s : C →₀ ℕ) : Submodule K (MvPolynomial V K) :=
  ((powerProduct J s)).restrictScalars K

theorem idealPowerPiece_one : (1 : MvPolynomial V K) ∈ idealPowerPiece J 0 := by
  simp [idealPowerPiece]

theorem idealPowerPiece_mul (s t : C →₀ ℕ)
    (f : MvPolynomial V K) (hf : f ∈ idealPowerPiece J s)
    (g : MvPolynomial V K) (hg : g ∈ idealPowerPiece J t) :
    f * g ∈ idealPowerPiece J (s + t) := by
  change f * g ∈ (powerProduct J (s + t))
  rw [powerProduct_add]
  exact Ideal.mul_mem_mul hf hg

/-- Finite coefficient lists with coefficient `s` in `(powerProduct J s)`, and literal
convolution multiplication. -/
abbrev coefficientRees :=
  gradedCoefficientAlgebra (idealPowerPiece J)
    (idealPowerPiece_one J) (idealPowerPiece_mul J)

instance (priority := 1200) coefficientReesRing : Ring (coefficientRees J) :=
  Subalgebra.toRing (coefficientRees J)

instance (priority := 1200) coefficientReesAlgebra : Algebra K (coefficientRees J) :=
  Subalgebra.algebra (coefficientRees J)

/-- The coefficient algebra is the literal multi-Rees subalgebra, with
its original polynomial values and coefficient-ring action. -/
def coefficientReesMultiEquiv :
    coefficientRees J ≃ₐ[K] (multiReesAlgebra J).restrictScalars K where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem coefficientReesMultiEquiv_val (x : coefficientRees J) :
    (coefficientReesMultiEquiv J x).val = x.val := rfl

def idealReesSingle (s : C →₀ ℕ) : idealPowerPiece J s →ₗ[K] coefficientRees J :=
  coefficientSingle (idealPowerPiece J) (idealPowerPiece_one J) (idealPowerPiece_mul J) s

variable [Nontrivial K] (m : MonomialOrder V)
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) ((powerProduct J s)))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

abbrev GroebnerReesIndex := Σ s : C →₀ ℕ, NonstandardIndex m ((powerProduct J s))

/-- The native ideal basis is transported by the identity on polynomial
values to the scalar-restricted coefficient module. -/
def groebnerPowerBasis (s : C →₀ ℕ) :
    Module.Basis (NonstandardIndex m (powerProduct J s)) K (idealPowerPiece J s) :=
  (groebnerIdealBasis m (powerProduct J s) (G s) (hG s) (hu s)).map
    (Sublattice.idealScalarRestrictionEquiv (powerProduct J s))

@[simp] theorem groebnerPowerBasis_apply (s : C →₀ ℕ)
    (a : NonstandardIndex m (powerProduct J s)) :
    groebnerPowerBasis J m G hG hu s a =
      Sublattice.idealScalarRestrictionEquiv (powerProduct J s)
        (idealLift m (powerProduct J s) (G s) (hG s) (hu s) a) := by
  rw [groebnerPowerBasis, Module.Basis.map_apply, groebnerIdealBasis_apply]

theorem groebnerPowerBasis_repr (s : C →₀ ℕ) (f : idealPowerPiece J s)
    (a : NonstandardIndex m (powerProduct J s)) :
    (groebnerPowerBasis J m G hG hu s).repr f a = f.val.coeff a.val := by
  rw [groebnerPowerBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    groebnerIdealBasis_repr, Sublattice.idealScalarRestrictionEquiv_symm_val]

/-- No quotient or flatness assertion enters this basis: it is a basis of
the actual coefficientwise Rees subalgebra. -/
def groebnerReesBasis : Module.Basis (GroebnerReesIndex J m) K (coefficientRees J) :=
  gradedCoefficientBasis (idealPowerPiece J)
    (idealPowerPiece_one J) (idealPowerPiece_mul J)
    (groebnerPowerBasis J m G hG hu)

theorem groebnerReesBasis_apply (s : C →₀ ℕ) (a : NonstandardIndex m ((powerProduct J s))) :
    groebnerReesBasis J m G hG hu ⟨s, a⟩ =
      idealReesSingle J s (idealLift m ((powerProduct J s)) (G s) (hG s) (hu s) a) := by
  rw [groebnerReesBasis, gradedCoefficientBasis_apply, groebnerPowerBasis_apply] <;> rfl

theorem groebnerReesBasis_repr (x : coefficientRees J) (s : C →₀ ℕ)
    (a : NonstandardIndex m ((powerProduct J s))) :
    (groebnerReesBasis J m G hG hu).repr x ⟨s, a⟩ =
      (x.val.coeff s).coeff a.val := by
  rw [groebnerReesBasis, gradedCoefficientBasis_repr, groebnerPowerBasis_repr] <;> rfl

abbrev InitialReesIndex := Σ s : C →₀ ℕ,
  {a : V →₀ ℕ // monomial a (1 : K) ∈
    Ideal.span (m.leadingTerm '' (((powerProduct J s)) : Set (MvPolynomial V K)))}

def groebnerInitialReesIndexEquiv : GroebnerReesIndex J m ≃ InitialReesIndex J m :=
  Equiv.sigmaCongrRight
    (fun s => nonstandardInitialIndexEquiv m ((powerProduct J s)) (G s) (hG s) (hu s))

def initialIndexedReesBasis :
    Module.Basis (InitialReesIndex J m) K (coefficientRees J) :=
  (groebnerReesBasis J m G hG hu).reindex (groebnerInitialReesIndexEquiv J m G hG hu)

end FourPapers.MixedTransfer

end
end
end

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.InitialReesBasis -/
section

/-! # A common basis index for the original and initial Rees algebras -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.MixedTransfer

open Classical CommAlg FourPapers.Sublattice MvPolynomial

variable {K V C : Type*} [Fintype C] [DecidableEq C] [CommRing K] [Nontrivial K]
  (m : MonomialOrder V) (J I : C → Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m ((powerProduct J s)) = (powerProduct I s))
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) ((powerProduct J s)))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

/-- The initial-ideal identity preserves polynomial values and explicitly
compares the scalar actions on the native and coefficient modules. -/
def initialPowerCoefficientEquiv (s : C →₀ ℕ) :
    initialIdealForBasis m (powerProduct J s) ≃ₗ[K] idealPowerPiece I s where
  toFun f := ⟨f.val, by
    change f.val ∈ powerProduct I s
    rw [← hinit s]
    exact f.property⟩
  invFun f := ⟨f.val, by
    change f.val ∈ initialIdealForBasis m (powerProduct J s)
    rw [hinit s]
    exact f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem initialPowerCoefficientEquiv_val (s : C →₀ ℕ)
    (f : initialIdealForBasis m (powerProduct J s)) :
    (initialPowerCoefficientEquiv m J I hinit s f).val = f.val := rfl

@[simp] theorem initialPowerCoefficientEquiv_symm_val (s : C →₀ ℕ)
    (f : idealPowerPiece I s) :
    ((initialPowerCoefficientEquiv m J I hinit s).symm f).val = f.val := rfl

def initialPowerBasis (s : C →₀ ℕ) :
    Module.Basis (NonstandardIndex m ((powerProduct J s))) K (idealPowerPiece I s) :=
  (initialIdealBasis m ((powerProduct J s)) (G s) (hG s) (hu s)).map
    (initialPowerCoefficientEquiv m J I hinit s)

@[simp] theorem initialPowerBasis_val (s : C →₀ ℕ) (a : NonstandardIndex m ((powerProduct J s))) :
    (initialPowerBasis m J I hinit G hG hu s a).val = monomial a.val (1 : K) := by
  rw [initialPowerBasis, Module.Basis.map_apply, initialPowerCoefficientEquiv_val,
    initialIdealBasis_apply] <;> rfl

theorem initialPowerBasis_repr (s : C →₀ ℕ) (f : idealPowerPiece I s)
    (a : NonstandardIndex m ((powerProduct J s))) :
    (initialPowerBasis m J I hinit G hG hu s).repr f a = f.val.coeff a.val := by
  rw [initialPowerBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    initialIdealBasis_repr, initialPowerCoefficientEquiv_symm_val]

def initialReesBasis : Module.Basis (GroebnerReesIndex J m) K (coefficientRees I) :=
  gradedCoefficientBasis (idealPowerPiece I) (idealPowerPiece_one I) (idealPowerPiece_mul I)
    (initialPowerBasis m J I hinit G hG hu)

@[simp] theorem initialReesBasis_apply (s : C →₀ ℕ) (a : NonstandardIndex m ((powerProduct J s))) :
    initialReesBasis m J I hinit G hG hu ⟨s, a⟩ =
      idealReesSingle I s (initialPowerBasis m J I hinit G hG hu s a) := by
  rw [initialReesBasis, gradedCoefficientBasis_apply]
  rfl

theorem initialReesBasis_val (s : C →₀ ℕ) (a : NonstandardIndex m ((powerProduct J s))) :
    (initialReesBasis m J I hinit G hG hu ⟨s, a⟩).val =
      AddMonoidAlgebra.single s (monomial a.val (1 : K)) := by
  rw [initialReesBasis_apply, idealReesSingle, coefficientSingle_val, initialPowerBasis_val]

theorem initialReesBasis_repr (x : coefficientRees I) (s : C →₀ ℕ)
    (a : NonstandardIndex m ((powerProduct J s))) :
    (initialReesBasis m J I hinit G hG hu).repr x ⟨s, a⟩ =
      (x.val.coeff s).coeff a.val := by
  rw [initialReesBasis, gradedCoefficientBasis_repr, initialPowerBasis_repr]
  rfl

/-- The genuine coefficient modules of all powers are compared by the
proved triangular bases. This is a module equivalence, not an assertion
that the original Rees algebra and its initial algebra are isomorphic. -/
def reesInitialLinearEquiv : coefficientRees J ≃ₗ[K] coefficientRees I :=
  (groebnerReesBasis J m G hG hu).repr.trans (initialReesBasis m J I hinit G hG hu).repr.symm

@[simp] theorem reesInitialLinearEquiv_basis (a : GroebnerReesIndex J m) :
    reesInitialLinearEquiv m J I hinit G hG hu (groebnerReesBasis J m G hG hu a) =
      initialReesBasis m J I hinit G hG hu a := by
  simp only [reesInitialLinearEquiv, LinearEquiv.trans_apply, Module.Basis.repr_self,
    Module.Basis.repr_symm_single_one]

theorem reesInitialLinearEquiv_repr (x : coefficientRees J) (a : GroebnerReesIndex J m) :
    (initialReesBasis m J I hinit G hG hu).repr
      (reesInitialLinearEquiv m J I hinit G hG hu x) a =
      (groebnerReesBasis J m G hG hu).repr x a := by
  rw [reesInitialLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

def initialReesIndexAdd (a b : GroebnerReesIndex J m) : GroebnerReesIndex J m :=
  ⟨a.1 + b.1, ⟨a.2.val + b.2.val, by
    apply (monomial_mem_initial_iff_not_standard m ((powerProduct J (a.1 + b.1)))
      (G (a.1 + b.1)) (hG (a.1 + b.1)) (hu (a.1 + b.1)) _).mp
    change monomial (a.2.val+b.2.val) (1 : K) ∈
      initialIdealForBasis m (powerProduct J (a.1+b.1))
    rw [hinit (a.1 + b.1), powerProduct_add]
    have ha := (initialPowerBasis m J I hinit G hG hu a.1 a.2).property
    have hb := (initialPowerBasis m J I hinit G hG hu b.1 b.2).property
    change (initialPowerBasis m J I hinit G hG hu a.1 a.2).val ∈ powerProduct I a.1 at ha
    change (initialPowerBasis m J I hinit G hG hu b.1 b.2).val ∈ powerProduct I b.1 at hb
    rw [initialPowerBasis_val] at ha hb
    simpa only [monomial_mul_monomial, one_mul] using Ideal.mul_mem_mul ha hb⟩⟩

theorem initialReesBasis_mul (a b : GroebnerReesIndex J m) :
    initialReesBasis m J I hinit G hG hu a * initialReesBasis m J I hinit G hG hu b =
      initialReesBasis m J I hinit G hG hu (initialReesIndexAdd m J I hinit G hG hu a b) := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, initialReesBasis_val, initialReesBasis_val, initialReesBasis_val,
    AddMonoidAlgebra.single_mul_single, monomial_mul_monomial, one_mul] <;> rfl

end FourPapers.MixedTransfer

end
end
end

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.GroebnerReesFiltration -/
section

/-! # The original term-order filtration on the actual Rees algebra

An element is bounded by `γ` when every polynomial coefficient in its Rees
expansion is bounded by `γ` in the given term order. This filtration is
defined on the actual coefficient algebra and is proved multiplicative.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.MixedTransfer

open Classical CommAlg FourPapers.Sublattice MvPolynomial
open scoped BigOperators

variable {K V C : Type*} [Fintype C] [DecidableEq C] [CommRing K]
  (m : MonomialOrder V) (J : C → Ideal (MvPolynomial V K))

theorem mem_monomialOrderBound_iff (f : MvPolynomial V K) (n : m.syn) :
    f ∈ monomialOrderBound m n ↔ m.toSyn (m.degree f) ≤ n := by
  change (∀ a ∈ f.support, m.toSyn a ≤ n) ↔ _
  simpa only [m.toSyn.apply_symm_apply] using
    (m.degree_le_iff (f := f) (d := m.toSyn.symm n)).symm

theorem monomialOrderBound_mono : Monotone (monomialOrderBound (K := K) m) := by
  intro a b hab f hf
  exact (mem_monomialOrderBound_iff m f b).mpr
    (((mem_monomialOrderBound_iff m f a).mp hf).trans hab)

theorem monomialOrderBound_mul (a b : m.syn)
    (f : MvPolynomial V K) (hf : f ∈ monomialOrderBound m a)
    (g : MvPolynomial V K) (hg : g ∈ monomialOrderBound m b) :
    f * g ∈ monomialOrderBound m (a + b) := by
  apply (mem_monomialOrderBound_iff m (f * g) (a + b)).mpr
  exact m.toSyn_degree_mul_le.trans (add_le_add
    ((mem_monomialOrderBound_iff m f a).mp hf)
    ((mem_monomialOrderBound_iff m g b).mp hg))

def reesOrderLevel (n : m.syn) : Submodule K (coefficientRees J) where
  carrier := {x | ∀ s, x.val.coeff s ∈ monomialOrderBound m n}
  zero_mem' := by intro s; exact (monomialOrderBound m n).zero_mem
  add_mem' hx hy := by
    intro s
    exact (monomialOrderBound m n).add_mem (hx s) (hy s)
  smul_mem' c x hx := by
    intro s
    exact (monomialOrderBound m n).smul_mem c (hx s)

theorem reesOrderLevel_mono : Monotone (reesOrderLevel m J) := by
  intro a b hab x hx s
  exact monomialOrderBound_mono m hab (hx s)

theorem reesOrderLevel_exhaustive (x : coefficientRees J) :
    ∃ n, x ∈ reesOrderLevel m J n := by
  let n : m.syn := x.val.coeff.support.sup (fun s => m.toSyn (m.degree (x.val.coeff s)))
  refine ⟨n, ?_⟩
  intro s
  apply (mem_monomialOrderBound_iff m _ n).mpr
  by_cases hs : s ∈ x.val.coeff.support
  · exact Finset.le_sup (f := fun s => m.toSyn (m.degree (x.val.coeff s))) hs
  · have hz := Finsupp.notMem_support_iff.mp hs
    rw [hz, m.degree_zero, map_zero]
    exact bot_le

theorem reesOrderLevel_one : (1 : coefficientRees J) ∈ reesOrderLevel m J 0 := by
  intro s
  change (1 : AddMonoidAlgebra (MvPolynomial V K) (C →₀ ℕ)).coeff s ∈ monomialOrderBound m 0
  by_cases hs : (0 : C →₀ ℕ) = s
  · subst s
    rw [AddMonoidAlgebra.coeff_one_zero]
    change (1 : MvPolynomial V K) ∈ monomialOrderBound m 0
    apply (mem_monomialOrderBound_iff m _ 0).mpr
    rw [m.degree_one, map_zero]
  · simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne (Ne.symm hs)]
    exact (monomialOrderBound m 0).zero_mem

theorem reesOrderLevel_mul (a b : m.syn) (x y : coefficientRees J)
    (hx : x ∈ reesOrderLevel m J a) (hy : y ∈ reesOrderLevel m J b) :
    x * y ∈ reesOrderLevel m J (a + b) := by
  intro s
  change (x.val * y.val).coeff s ∈ monomialOrderBound m (a + b)
  rw [AddMonoidAlgebra.coeff_mul]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  dsimp only
  split_ifs
  · exact monomialOrderBound_mul m a b _ (hx i) _ (hy j)
  · exact (monomialOrderBound m (a + b)).zero_mem

def groebnerReesFiltration :
    WellOrderedFiltered.MultiplicativeFiltration K (coefficientRees J) m.syn where
  level := reesOrderLevel m J
  mono := reesOrderLevel_mono m J
  exhaustive := reesOrderLevel_exhaustive m J
  one_mem := reesOrderLevel_one m J
  mul_mem := by
    intro a b x hx y hy
    exact reesOrderLevel_mul m J a b x y hx hy

variable [Nontrivial K]
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) ((powerProduct J s)))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

theorem groebnerReesBasis_mem_orderLevel (s : C →₀ ℕ) (a : NonstandardIndex m ((powerProduct J s))) :
    groebnerReesBasis J m G hG hu ⟨s, a⟩ ∈
      reesOrderLevel m J (m.toSyn a.val) := by
  rw [groebnerReesBasis_apply]
  intro t
  rw [idealReesSingle, coefficientSingle_coeff]
  split_ifs with hst
  · exact idealLift_mem_orderBound m ((powerProduct J s)) (G s) (hG s) (hu s) a
  · exact (monomialOrderBound m (m.toSyn a.val)).zero_mem

/-- The actual coefficientwise filtration equals the filtration by leading
indices in the proved Rees basis. This is the bridge needed for finite
linear-algebra comparisons in a homogeneous strand. -/
theorem reesOrderLevel_eq_basis_span (n : m.syn) :
    reesOrderLevel m J n = Submodule.span K
      ((groebnerReesBasis J m G hG hu) ''
        {a : GroebnerReesIndex J m | m.toSyn a.2.val ≤ n}) := by
  ext x
  constructor
  · intro hx
    rw [Module.Basis.mem_span_image]
    rintro ⟨s, a⟩ ha
    have hc : (x.val.coeff s).coeff a.val ≠ 0 := by
      have h := Finsupp.mem_support_iff.mp ha
      rwa [groebnerReesBasis_repr] at h
    exact (mem_restrictSupport_iff K).mp (hx s) (mem_support_iff.mpr hc)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨⟨s, a⟩, ha, rfl⟩ := hx
        exact reesOrderLevel_mono m J ha (groebnerReesBasis_mem_orderLevel m J G hG hu s a)
    | zero => exact (reesOrderLevel m J n).zero_mem
    | add x y hx hy ihx ihy => exact (reesOrderLevel m J n).add_mem ihx ihy
    | smul c x hx ih => exact (reesOrderLevel m J n).smul_mem c ih

end FourPapers.MixedTransfer

end
end
end

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.GroebnerReesLeading -/
section

/-! # Strict lower terms in the actual Rees multiplication

The comparison of the two Rees modules sends each triangular lift to its
leading monomial. The multiplication discrepancy is proved to have strictly
smaller original term-order weight. These identities also apply when a base
variable multiplies a coefficient, as required for the Koszul differential.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.MixedTransfer

open Classical CommAlg FourPapers.Sublattice MvPolynomial

variable {K V C : Type*} [Fintype C] [DecidableEq C] [CommRing K] [Nontrivial K]
  (m : MonomialOrder V) (J I : C → Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m ((powerProduct J s)) = (powerProduct I s))
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) ((powerProduct J s)))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

theorem idealLift_product_top_coeff
    (s t : C →₀ ℕ) (a : NonstandardIndex m ((powerProduct J s))) (b : NonstandardIndex m ((powerProduct J t))) :
    ((idealLift m ((powerProduct J s)) (G s) (hG s) (hu s) a).val *
      (idealLift m ((powerProduct J t)) (G t) (hG t) (hu t) b).val).coeff (a.val + b.val) = 1 := by
  rw [m.coeff_mul_of_add_of_degree_le]
  · rw [idealLift_nonstandard_coeff, idealLift_nonstandard_coeff]
    simp
  · simpa only [m.toSyn.apply_symm_apply] using
      (mem_monomialOrderBound_iff m _ (m.toSyn a.val)).mp
        (idealLift_mem_orderBound m ((powerProduct J s)) (G s) (hG s) (hu s) a)
  · simpa only [m.toSyn.apply_symm_apply] using
      (mem_monomialOrderBound_iff m _ (m.toSyn b.val)).mp
        (idealLift_mem_orderBound m ((powerProduct J t)) (G t) (hG t) (hu t) b)

theorem idealLift_product_upper_coeff
    (s t : C →₀ ℕ) (a : NonstandardIndex m ((powerProduct J s))) (b : NonstandardIndex m ((powerProduct J t)))
    (c : V →₀ ℕ) (hc : m.toSyn (a.val + b.val) ≤ m.toSyn c) :
    ((idealLift m ((powerProduct J s)) (G s) (hG s) (hu s) a).val *
      (idealLift m ((powerProduct J t)) (G t) (hG t) (hu t) b).val).coeff c =
      if a.val + b.val = c then 1 else 0 := by
  by_cases he : a.val + b.val = c
  · rw [if_pos he, ← he]
    exact idealLift_product_top_coeff m J G hG hu s t a b
  · rw [if_neg he]
    apply m.coeff_eq_zero_of_lt
    have hbound := monomialOrderBound_mul m (m.toSyn a.val) (m.toSyn b.val)
      _ (idealLift_mem_orderBound m ((powerProduct J s)) (G s) (hG s) (hu s) a)
      _ (idealLift_mem_orderBound m ((powerProduct J t)) (G t) (hG t) (hu t) b)
    have hb := (mem_monomialOrderBound_iff m _ _).mp hbound
    rw [← map_add] at hb
    exact hb.trans_lt (lt_of_le_of_ne hc (fun h => he (m.toSyn.injective h)))

theorem groebnerReesBasis_product_upper_coeff
    (a b c : GroebnerReesIndex J m)
    (hc : m.toSyn (a.2.val + b.2.val) ≤ m.toSyn c.2.val) :
    (groebnerReesBasis J m G hG hu).repr
      (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) c =
      if a.1 + b.1 = c.1 ∧ a.2.val + b.2.val = c.2.val then 1 else 0 := by
  rw [groebnerReesBasis_repr, groebnerReesBasis_apply, groebnerReesBasis_apply]
  change ((AddMonoidAlgebra.single a.1
      (idealLift m ((powerProduct J a.1)) (G a.1) (hG a.1) (hu a.1) a.2).val *
    AddMonoidAlgebra.single b.1
      (idealLift m ((powerProduct J b.1)) (G b.1) (hG b.1) (hu b.1) b.2).val).coeff c.1).coeff c.2.val = _
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hs : a.1 + b.1 = c.1
  · rw [if_pos hs]
    simpa only [hs, true_and] using
      idealLift_product_upper_coeff m J G hG hu a.1 b.1 a.2 b.2 c.2.val hc
  · simp [hs]

/-- The algebra discrepancy is strictly smaller in the original order.
The proof refers to literal coefficients of products in the original ideals. -/
theorem reesInitialLinearEquiv_mul_strict_basis
    (a b c : GroebnerReesIndex J m)
    (hc : (initialReesBasis m J I hinit G hG hu).repr
      (reesInitialLinearEquiv m J I hinit G hG hu
          (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) -
        reesInitialLinearEquiv m J I hinit G hG hu (groebnerReesBasis J m G hG hu a) *
          reesInitialLinearEquiv m J I hinit G hG hu (groebnerReesBasis J m G hG hu b)) c ≠ 0) :
    m.toSyn c.2.val < m.toSyn (a.2.val + b.2.val) := by
  by_contra hn
  apply hc
  rw [map_sub, Finsupp.sub_apply, reesInitialLinearEquiv_repr,
    reesInitialLinearEquiv_basis, reesInitialLinearEquiv_basis, initialReesBasis_mul,
    Module.Basis.repr_self, Finsupp.single_apply,
    groebnerReesBasis_product_upper_coeff m J G hG hu a b c (le_of_not_gt hn)]
  apply sub_eq_zero.mpr
  congr 1
  apply propext
  constructor
  · rintro ⟨hs, he⟩
    rcases a with ⟨s, a⟩
    rcases b with ⟨t, b⟩
    rcases c with ⟨r, c⟩
    dsimp only at hs he
    subst r
    apply congrArg (Sigma.mk (s + t))
    exact Subtype.ext he
  · intro he
    exact ⟨congrArg Sigma.fst he, congrArg (fun i : GroebnerReesIndex J m => i.2.val) he⟩

theorem groebnerReesBasis_product_leading_coeff
    (a b c : GroebnerReesIndex J m)
    (hc : m.toSyn (a.2.val + b.2.val) ≤ m.toSyn c.2.val) :
    (groebnerReesBasis J m G hG hu).repr
      (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) c =
    (initialReesBasis m J I hinit G hG hu).repr
      (initialReesBasis m J I hinit G hG hu a * initialReesBasis m J I hinit G hG hu b) c := by
  by_contra hne
  apply (not_lt_of_ge hc)
  apply reesInitialLinearEquiv_mul_strict_basis m J I hinit G hG hu a b c
  rw [map_sub, Finsupp.sub_apply, reesInitialLinearEquiv_repr,
    reesInitialLinearEquiv_basis, reesInitialLinearEquiv_basis]
  exact sub_ne_zero.mpr hne

end FourPapers.MixedTransfer

end
end
end

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.GroebnerReesKoszulBasis -/
section

/-! # Actual tensor Koszul bases and their leading multiplication

The exterior weight is added to the polynomial exponent. This is essential:
contraction removes one exterior variable at the same time that the Koszul
differential multiplies its polynomial coefficient by that variable.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.MixedTransfer

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid FourPapers.Sublattice MvPolynomial
open scoped TensorProduct

universe u
variable {K V C : Type u} [Fintype C] [DecidableEq C] [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J I : C → Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m ((powerProduct J s)) = (powerProduct I s))
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) ((powerProduct J s)))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

abbrev IdealReesKoszul := coefficientRees J ⊗[K] Simplicial.Ambient V K
abbrev IdealReesKoszulIndex := GroebnerReesIndex J m × Finset V

instance (priority := 1200) idealReesKoszulRing : Ring (IdealReesKoszul J) :=
  Algebra.TensorProduct.instRing

instance (priority := 1200) idealReesKoszulAlgebra : Algebra K (IdealReesKoszul J) :=
  Algebra.TensorProduct.instAlgebra

def groebnerReesKoszulBasis : Module.Basis (IdealReesKoszulIndex m J) K (IdealReesKoszul J) :=
  (groebnerReesBasis J m G hG hu).tensorProduct Simplicial.basis

def initialReesKoszulBasis : Module.Basis (IdealReesKoszulIndex m J) K (IdealReesKoszul I) :=
  (initialReesBasis m J I hinit G hG hu).tensorProduct Simplicial.basis

def reesKoszulFineDegree (a : IdealReesKoszulIndex m J) : V →₀ ℕ :=
  a.1.2.val + faceExponent a.2

def reesKoszulWeight (a : IdealReesKoszulIndex m J) : m.syn :=
  m.toSyn (reesKoszulFineDegree m J a)

theorem initialReesKoszul_product_homogeneous
    (a b c : IdealReesKoszulIndex m J)
    (hc : (initialReesKoszulBasis m J I hinit G hG hu).repr
      (initialReesKoszulBasis m J I hinit G hG hu a *
        initialReesKoszulBasis m J I hinit G hG hu b) c ≠ 0) :
    reesKoszulWeight m J c = reesKoszulWeight m J a + reesKoszulWeight m J b := by
  simp only [initialReesKoszulBasis, Module.Basis.tensorProduct_apply',
    Algebra.TensorProduct.tmul_mul_tmul, initialReesBasis_mul] at hc
  by_cases hab : Disjoint a.2 b.2
  · rw [faceBasis_mul_of_disjoint _ _ hab, TensorProduct.tmul_smul,
      map_zsmul_unit, Finsupp.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_apply,
      Finsupp.single_apply] at hc
    have hF : a.2 ∪ b.2 = c.2 := by
      by_contra h
      simp [h] at hc
    have hA : initialReesIndexAdd m J I hinit G hG hu a.1 b.1 = c.1 := by
      by_contra h
      simp [h] at hc
    have hE : c.1.2.val = a.1.2.val + b.1.2.val := by
      simpa only [initialReesIndexAdd] using
        (congrArg (fun z : GroebnerReesIndex J m => z.2.val) hA).symm
    simp only [reesKoszulWeight, reesKoszulFineDegree, hE, ← hF,
      faceExponent_union_of_disjoint _ _ hab, map_add]
    abel
  · rw [faceBasis_mul_of_not_disjoint _ _ hab, TensorProduct.tmul_zero,
      map_zero, Finsupp.zero_apply] at hc
    exact (hc rfl).elim

/-- The leading coefficients of actual products agree with the products in
the actual initial Rees Koszul algebra, in the original monomial order. -/
theorem groebnerReesKoszul_product_leading
    (a b c : IdealReesKoszulIndex m J)
    (hc : reesKoszulWeight m J a + reesKoszulWeight m J b ≤ reesKoszulWeight m J c) :
    (groebnerReesKoszulBasis m J G hG hu).repr
      (groebnerReesKoszulBasis m J G hG hu a * groebnerReesKoszulBasis m J G hG hu b) c =
    (initialReesKoszulBasis m J I hinit G hG hu).repr
      (initialReesKoszulBasis m J I hinit G hG hu a *
        initialReesKoszulBasis m J I hinit G hG hu b) c := by
  simp only [groebnerReesKoszulBasis, initialReesKoszulBasis,
    Module.Basis.tensorProduct_apply', Algebra.TensorProduct.tmul_mul_tmul]
  by_cases hab : Disjoint a.2 b.2
  · rw [faceBasis_mul_of_disjoint _ _ hab, TensorProduct.tmul_smul,
      TensorProduct.tmul_smul, map_zsmul_unit, map_zsmul_unit,
      Finsupp.smul_apply, Finsupp.smul_apply,
      Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases hF : a.2 ∪ b.2 = c.2
    · rw [if_pos hF, one_smul, one_smul]
      congr 1
      apply groebnerReesBasis_product_leading_coeff m J I hinit G hG hu
      have he : reesKoszulWeight m J a + reesKoszulWeight m J b =
          m.toSyn (a.1.2.val + b.1.2.val) + m.toSyn (faceExponent c.2) := by
        simp only [reesKoszulWeight, reesKoszulFineDegree, ← hF,
          faceExponent_union_of_disjoint _ _ hab, map_add]
        abel
      rw [he] at hc
      apply (add_le_add_iff_right (m.toSyn (faceExponent c.2))).mp
      simpa only [reesKoszulWeight, reesKoszulFineDegree, map_add] using hc
    · rw [if_neg hF, zero_smul, zero_smul]
  · rw [faceBasis_mul_of_not_disjoint _ _ hab]
    simp

theorem reesKoszul_one_coeff_equal (a : IdealReesKoszulIndex m J) :
    (groebnerReesKoszulBasis m J G hG hu).repr 1 a =
      (initialReesKoszulBasis m J I hinit G hG hu).repr 1 a := by
  rcases a with ⟨⟨s, a⟩, F⟩
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.one_def]
  simp only [groebnerReesKoszulBasis, initialReesKoszulBasis,
    Module.Basis.tensorProduct_repr_tmul_apply, groebnerReesBasis_repr,
    initialReesBasis_repr]
  rfl

theorem groebnerReesKoszul_one_weight (a : IdealReesKoszulIndex m J)
    (ha : (groebnerReesKoszulBasis m J G hG hu).repr 1 a ≠ 0) :
    reesKoszulWeight m J a = 0 := by
  rcases a with ⟨⟨s, a⟩, F⟩
  rw [Algebra.TensorProduct.one_def] at ha
  simp only [groebnerReesKoszulBasis, Module.Basis.tensorProduct_repr_tmul_apply,
    groebnerReesBasis_repr] at ha
  rw [← faceBasis_empty, Module.Basis.repr_self, Finsupp.single_apply] at ha
  have hF : (∅ : Finset V) = F := by
    by_contra h
    simp [h] at ha
  rw [if_pos hF, one_smul] at ha
  change ((1 : AddMonoidAlgebra (MvPolynomial V K) (C →₀ ℕ)).coeff s).coeff a.val ≠ 0 at ha
  have hs : (0 : C →₀ ℕ) = s := by
    by_contra h
    have hz : (1 : AddMonoidAlgebra (MvPolynomial V K) (C →₀ ℕ)).coeff s = 0 := by
      rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_of_ne (Ne.symm h)]
    exact ha (by rw [hz, MvPolynomial.coeff_zero]; rfl)
  subst s
  rw [AddMonoidAlgebra.coeff_one_zero, MvPolynomial.coeff_one] at ha
  have he : (0 : V →₀ ℕ) = a.val := by
    by_contra h
    rw [if_neg h] at ha
    exact ha rfl
  change m.toSyn (a.val + faceExponent F) = 0
  rw [← hF, faceExponent_empty, add_zero, ← he, map_zero]

theorem groebnerReesKoszul_leading_one :
    OrderedBasis.leadingProjection (groebnerReesKoszulBasis m J G hG hu)
      (initialReesKoszulBasis m J I hinit G hG hu) (reesKoszulWeight m J) 0 1 = 1 := by
  apply (initialReesKoszulBasis m J I hinit G hG hu).repr.injective
  ext a
  rw [OrderedBasis.leadingProjection_repr]
  by_cases ha : reesKoszulWeight m J a = 0
  · rw [if_pos ha]
    exact reesKoszul_one_coeff_equal m J I hinit G hG hu a
  · rw [if_neg ha]
    symm
    by_contra hne
    apply ha
    apply groebnerReesKoszul_one_weight m J G hG hu a
    rwa [reesKoszul_one_coeff_equal m J I hinit G hG hu a]

def idealReesKoszulFiltration :
    WellOrderedFiltered.MultiplicativeFiltration K (IdealReesKoszul J) m.syn :=
  OrderedBasis.comparisonFiltration (groebnerReesKoszulBasis m J G hG hu)
    (initialReesKoszulBasis m J I hinit G hG hu) (reesKoszulWeight m J)
    (initialReesKoszul_product_homogeneous m J I hinit G hG hu)
    (groebnerReesKoszul_product_leading m J I hinit G hG hu)
    (fun a ha => (groebnerReesKoszul_one_weight m J G hG hu a ha).le)

/-- The literal associated algebra of the actual tensor Koszul algebra is
the actual tensor Koszul algebra of the initial Rees algebra. -/
def idealReesKoszulAssociatedAlgebraEquiv :
    (idealReesKoszulFiltration m J I hinit G hG hu).AssociatedGraded ≃ₐ[K]
      IdealReesKoszul I :=
  OrderedBasis.associatedAlgebraEquiv (groebnerReesKoszulBasis m J G hG hu)
    (initialReesKoszulBasis m J I hinit G hG hu) (reesKoszulWeight m J)
    (initialReesKoszul_product_homogeneous m J I hinit G hG hu)
    (groebnerReesKoszul_product_leading m J I hinit G hG hu)
    (fun a ha => (groebnerReesKoszul_one_weight m J G hG hu a ha).le)
    (groebnerReesKoszul_leading_one m J I hinit G hG hu)

end FourPapers.MixedTransfer

end
end
end

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.GroebnerReesKoszulDifferential -/
section

/-! # The literal Koszul differential in the original and initial bases -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.MixedTransfer

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid FourPapers.Sublattice MvPolynomial
open scoped TensorProduct

universe u
variable {K V C : Type u} [Fintype C] [DecidableEq C] [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J I : C → Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m ((powerProduct J s)) = (powerProduct I s))
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) ((powerProduct J s)))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

def idealReesZeroIndex (a : V →₀ ℕ) : GroebnerReesIndex J m :=
  ⟨0, ⟨a, by
    intro ha
    apply ha (monomial a (1 : K)) (by simp) (by simp)
    simp only [m.degree_monomial, one_ne_zero, ite_false, le_refl]⟩⟩

theorem groebnerReesBasis_zeroIndex (a : V →₀ ℕ) :
    (groebnerReesBasis J m G hG hu (idealReesZeroIndex m J a)).val =
      AddMonoidAlgebra.single 0 (monomial a (1 : K)) := by
  have hn : (hG 0).normalForm (hu 0) (monomial a 1) = 0 :=
    ((hG 0).normalForm_eq_zero_iff (hu 0)).mpr (by simp)
  rw [groebnerReesBasis_apply]
  simp only [idealReesSingle, coefficientSingle_val, idealReesZeroIndex,
    idealLift, hn, sub_zero]

def idealReesBaseVariable (v : V) : coefficientRees J :=
  idealReesSingle J 0 ⟨X v, by simp [idealPowerPiece]⟩

theorem idealReesBaseVariable_basis (v : V) :
    idealReesBaseVariable J v = groebnerReesBasis J m G hG hu
      (idealReesZeroIndex m J (Finsupp.single v 1)) := by
  apply Subtype.ext
  rw [groebnerReesBasis_zeroIndex]
  rfl

theorem idealReesBaseVariable_initialBasis (v : V) :
    idealReesBaseVariable I v = initialReesBasis m J I hinit G hG hu
      (idealReesZeroIndex m J (Finsupp.single v 1)) := by
  apply Subtype.ext
  rw [initialReesBasis_val]
  rfl

/-- The variables are the actual auxiliary-degree-zero polynomial variables
inside the actual Rees algebra. -/
def idealReesKoszulDGA : ParityDifferential K (IdealReesKoszul J) :=
  TensorExteriorKoszul.parityDifferential (idealReesBaseVariable J)

theorem groebnerReesKoszul_d_basis (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a) =
      ∑ v : V, (idealReesBaseVariable J v * groebnerReesBasis J m G hG hu a.1) ⊗ₜ[K]
        Simplicial.contraction v (Simplicial.basis a.2) := by
  rw [groebnerReesKoszulBasis, Module.Basis.tensorProduct_apply']
  exact TensorExteriorKoszul.differential_tmul _ _ _

theorem initialReesKoszul_d_basis (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA I).d (initialReesKoszulBasis m J I hinit G hG hu a) =
      ∑ v : V, (idealReesBaseVariable I v * initialReesBasis m J I hinit G hG hu a.1) ⊗ₜ[K]
        Simplicial.contraction v (Simplicial.basis a.2) := by
  rw [initialReesKoszulBasis, Module.Basis.tensorProduct_apply']
  exact TensorExteriorKoszul.differential_tmul _ _ _

theorem initialReesKoszul_d_fine (a b : IdealReesKoszulIndex m J)
    (hb : (initialReesKoszulBasis m J I hinit G hG hu).repr
      ((idealReesKoszulDGA I).d (initialReesKoszulBasis m J I hinit G hG hu a)) b ≠ 0) :
    reesKoszulFineDegree m J b = reesKoszulFineDegree m J a := by
  rw [initialReesKoszul_d_basis, map_sum, Finsupp.finsetSum_apply] at hb
  obtain ⟨v, hv, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  rw [Simplicial.contraction_basis] at hterm
  by_cases hvF : v ∈ a.2
  · rw [if_pos hvF, TensorProduct.tmul_smul, map_zsmul_unit, Finsupp.smul_apply,
      idealReesBaseVariable_initialBasis m J I hinit G hG hu v,
      initialReesBasis_mul m J I hinit G hG hu] at hterm
    change _ • ((initialReesBasis m J I hinit G hG hu).tensorProduct Simplicial.basis).repr
      (_ ⊗ₜ[K] Simplicial.basis (a.2.erase v)) b ≠ 0 at hterm
    rw [Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.repr_self,
      Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply] at hterm
    have hF : a.2.erase v = b.2 := by
      by_contra h
      simp [h] at hterm
    have hA : initialReesIndexAdd m J I hinit G hG hu
        (idealReesZeroIndex m J (Finsupp.single v 1)) a.1 = b.1 := by
      by_contra h
      simp [h] at hterm
    have hE : b.1.2.val = Finsupp.single v 1 + a.1.2.val := by
      simpa only [initialReesIndexAdd, idealReesZeroIndex] using
        (congrArg (fun z : GroebnerReesIndex J m => z.2.val) hA).symm
    simp only [reesKoszulFineDegree, hE, ← hF]
    rw [← faceExponent_erase_add hvF]
    abel
  · rw [if_neg hvF, TensorProduct.tmul_zero, map_zero, Finsupp.zero_apply] at hterm
    exact (hterm rfl).elim

section OrderedWeight

variable {Γ : Type*} [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  (ρ : (V →₀ ℕ) →+ Γ)
  (hcoef : ∀ a b c : GroebnerReesIndex J m, ρ (a.2.val + b.2.val) ≤ ρ c.2.val →
    (groebnerReesBasis J m G hG hu).repr
      (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) c =
    (initialReesBasis m J I hinit G hG hu).repr
      (initialReesBasis m J I hinit G hG hu a * initialReesBasis m J I hinit G hG hu b) c)

include hcoef in
theorem groebnerReesKoszul_d_leading (a b : IdealReesKoszulIndex m J)
    (hb : ρ (reesKoszulFineDegree m J a) ≤ ρ (reesKoszulFineDegree m J b)) :
    (groebnerReesKoszulBasis m J G hG hu).repr
      ((idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a)) b =
    (initialReesKoszulBasis m J I hinit G hG hu).repr
      ((idealReesKoszulDGA I).d (initialReesKoszulBasis m J I hinit G hG hu a)) b := by
  rw [groebnerReesKoszul_d_basis, initialReesKoszul_d_basis, map_sum, map_sum,
    Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Simplicial.contraction_basis]
  by_cases hvF : v ∈ a.2
  · rw [if_pos hvF, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      map_zsmul_unit, map_zsmul_unit, Finsupp.smul_apply, Finsupp.smul_apply]
    change _ • ((groebnerReesBasis J m G hG hu).tensorProduct Simplicial.basis).repr
        (_ ⊗ₜ[K] Simplicial.basis (a.2.erase v)) b =
      _ • ((initialReesBasis m J I hinit G hG hu).tensorProduct Simplicial.basis).repr
        (_ ⊗ₜ[K] Simplicial.basis (a.2.erase v)) b
    rw [Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hF : a.2.erase v = b.2
    · rw [if_pos hF, one_smul, one_smul,
        idealReesBaseVariable_basis m J G hG hu v,
        idealReesBaseVariable_initialBasis m J I hinit G hG hu v]
      congr 1
      apply hcoef
      have he : ρ (reesKoszulFineDegree m J a) =
          ρ (Finsupp.single v 1 + a.1.2.val) + ρ (faceExponent b.2) := by
        rw [reesKoszulFineDegree, ← hF, ← faceExponent_erase_add hvF]
        simp only [map_add]
        abel
      rw [he] at hb
      apply (add_le_add_iff_right (ρ (faceExponent b.2))).mp
      simpa only [reesKoszulFineDegree, idealReesZeroIndex, map_add] using hb
    · rw [if_neg hF, zero_smul, zero_smul]
  · rw [if_neg hvF]
    simp

end OrderedWeight

theorem groebnerReesKoszul_parity_basis (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA J).parity (groebnerReesKoszulBasis m J G hG hu a) =
      (-1 : K) ^ a.2.card • groebnerReesKoszulBasis m J G hG hu a := by
  rw [groebnerReesKoszulBasis, Module.Basis.tensorProduct_apply']
  change TensorExteriorKoszul.involute (_ ⊗ₜ[K] Simplicial.basis a.2) = _
  rw [TensorExteriorKoszul.involute_tmul]
  have he : CliffordAlgebra.involute (Simplicial.basis (k := K) a.2) =
      (-1 : K) ^ a.2.card • Simplicial.basis a.2 :=
    TauCeti.ExteriorAlgebra.involute_basis (Pi.basisFun K V) a.2
  rw [he, TensorProduct.tmul_smul]

theorem initialReesKoszul_parity_basis (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA I).parity (initialReesKoszulBasis m J I hinit G hG hu a) =
      (-1 : K) ^ a.2.card • initialReesKoszulBasis m J I hinit G hG hu a := by
  rw [initialReesKoszulBasis, Module.Basis.tensorProduct_apply']
  change TensorExteriorKoszul.involute (_ ⊗ₜ[K] Simplicial.basis a.2) = _
  rw [TensorExteriorKoszul.involute_tmul]
  have he : CliffordAlgebra.involute (Simplicial.basis (k := K) a.2) =
      (-1 : K) ^ a.2.card • Simplicial.basis a.2 :=
    TauCeti.ExteriorAlgebra.involute_basis (Pi.basisFun K V) a.2
  rw [he, TensorProduct.tmul_smul]

theorem reesKoszul_parity_coeff_equal (a b : IdealReesKoszulIndex m J) :
    (groebnerReesKoszulBasis m J G hG hu).repr
      ((idealReesKoszulDGA J).parity (groebnerReesKoszulBasis m J G hG hu a)) b =
    (initialReesKoszulBasis m J I hinit G hG hu).repr
      ((idealReesKoszulDGA I).parity (initialReesKoszulBasis m J I hinit G hG hu a)) b := by
  rw [groebnerReesKoszul_parity_basis, initialReesKoszul_parity_basis,
    map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]

theorem initialReesKoszul_parity_support (a b : IdealReesKoszulIndex m J)
    (hb : (initialReesKoszulBasis m J I hinit G hG hu).repr
      ((idealReesKoszulDGA I).parity (initialReesKoszulBasis m J I hinit G hG hu a)) b ≠ 0) : b = a := by
  rw [initialReesKoszul_parity_basis, map_smul, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_apply] at hb
  by_contra h
  simp [Ne.symm h] at hb

end FourPapers.MixedTransfer

end
end
end


end
