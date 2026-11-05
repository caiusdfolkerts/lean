module
public import graph_foundation.part013
public import shared_results.part019_associated_commutative_ring

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredCoordinates -/
section

/-! # Literal associated graded components and their differential

The Rees quotient is identified with the direct sum of `F_n / F_(n-1)`.
Under this identification its differential is exactly the map induced by the
original differential on each successive quotient.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical
open scoped DirectSum

def quotientEquivOfSurjective
    {K R M : Type*} [CommRing K] [Ring R] [Algebra K R]
    [AddCommMonoid M] [Module K M]
    (I : TwoSidedIdeal R) (f : R →ₗ[K] M)
    (hker : LinearMap.ker f = I.asIdeal.restrictScalars K)
    (hsurj : Function.Surjective f) : (R ⧸ I.asIdeal) ≃ₗ[K] M := by
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
  exact (Submodule.Quotient.restrictScalarsEquiv K I.asIdeal).symm.trans
    ((Submodule.quotEquivOfEq (I.asIdeal.restrictScalars K) (LinearMap.ker f)
      hker.symm).trans (f.quotKerEquivOfSurjective hsurj))

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A)

def lower (n : ℤ) : Submodule K (F.level n) :=
  (F.level (n - 1)).comap (F.level n).subtype

abbrev Grade (n : ℤ) := F.level n ⧸ F.lower n

def gradedCoefficients : F.rees →ₗ[K] ⨁ n, F.Grade n where
  toFun p :=
    { toFun := fun n => Submodule.Quotient.mk (⟨p.val.coeff n, p.property n⟩ : F.level n)
      support' := Trunc.mk ⟨p.val.coeff.support.val, by
        intro n
        by_cases hn : n ∈ p.val.coeff.support
        · exact Or.inl hn
        · right
          have hz : p.val.coeff n = 0 := Finsupp.notMem_support_iff.mp hn
          have he : (⟨p.val.coeff n, p.property n⟩ : F.level n) = 0 := Subtype.ext hz
          exact (congrArg (Submodule.Quotient.mk (p := F.lower n)) he).trans
            (Submodule.Quotient.mk_zero _)⟩ }
  map_add' p q := by ext n; rfl
  map_smul' r p := by ext n; rfl

@[simp] theorem gradedCoefficients_apply (p : F.rees) (n : ℤ) :
    F.gradedCoefficients p n =
      (Submodule.Quotient.mk (⟨p.val.coeff n, p.property n⟩ : F.level n) : F.Grade n) := rfl

theorem gradedCoefficients_ker :
    LinearMap.ker F.gradedCoefficients = F.strictIdeal.asIdeal.restrictScalars K := by
  ext p
  rw [LinearMap.mem_ker]
  change F.gradedCoefficients p = 0 ↔ p ∈ F.strictIdeal.asIdeal
  rw [TwoSidedIdeal.mem_asIdeal, F.mem_strictIdeal]
  constructor
  · intro hp n
    have h := congrArg (fun x : ⨁ n, F.Grade n => x n) hp
    exact (Submodule.Quotient.mk_eq_zero (F.lower n)).mp h
  · intro hp
    ext n
    exact (Submodule.Quotient.mk_eq_zero (F.lower n)).mpr (hp n)

@[simp] theorem gradedCoefficients_monomial (n : ℤ) (a : F.level n) :
    F.gradedCoefficients (F.monomial n a) =
      DirectSum.of (fun n => F.Grade n) n (Submodule.Quotient.mk a) := by
  ext i
  by_cases hi : n = i
  · subst i
    rw [DirectSum.of_eq_same]
    apply congrArg (Submodule.Quotient.mk (p := F.lower n))
    apply Subtype.ext
    simp only [F.monomial_coeff, ite_true]
  · rw [DirectSum.of_eq_of_ne n i _ (Ne.symm hi)]
    have hz : (⟨(F.monomial n a).val.coeff i,
        (F.monomial n a).property i⟩ : F.level i) = 0 := by
      apply Subtype.ext
      simp only [F.monomial_coeff, if_neg hi, Submodule.coe_zero]
    exact (congrArg (Submodule.Quotient.mk (p := F.lower i)) hz).trans
      (Submodule.Quotient.mk_zero _)

theorem gradedCoefficients_surjective : Function.Surjective F.gradedCoefficients := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n a =>
      obtain ⟨a, rfl⟩ := (F.lower n).mkQ_surjective a
      exact ⟨F.monomial n a, F.gradedCoefficients_monomial n a⟩
  | add x y hx hy =>
      obtain ⟨p, rfl⟩ := hx
      obtain ⟨q, rfl⟩ := hy
      exact ⟨p + q, map_add _ _ _⟩

/-- The quotient by the strict Rees ideal is the direct sum of its actual
successive quotients. The abstract quotient helper keeps scalar-restriction
instances independent of the concrete Laurent coefficient algebra. -/
def associatedGradedEquiv : F.AssociatedGraded ≃ₗ[K] ⨁ n, F.Grade n :=
  quotientEquivOfSurjective (K:=K) (R:=F.rees) (M:=⨁ n, F.Grade n)
    F.strictIdeal F.gradedCoefficients
    F.gradedCoefficients_ker F.gradedCoefficients_surjective

@[simp] theorem associatedGradedEquiv_leading (p : F.rees) :
    F.associatedGradedEquiv (F.leadingMap p) = F.gradedCoefficients p := rfl

variable (D : ParityDifferential K A)
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)
  (hp : ∀ n x, x ∈ F.level n → D.parity x ∈ F.level n)

def levelDifferential (n : ℤ) : F.level n →ₗ[K] F.level n :=
  (D.d.domRestrict (F.level n)).codRestrict (F.level n) (fun x => hd n x.val x.property)

def gradeDifferential (n : ℤ) : F.Grade n →ₗ[K] F.Grade n :=
  Submodule.mapQ (F.lower n) (F.lower n) (F.levelDifferential D hd n)
    (fun x hx => hd (n - 1) x.val hx)

theorem gradeDifferential_square (n : ℤ) :
    (F.gradeDifferential D hd n).comp (F.gradeDifferential D hd n) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (F.lower n).mkQ_surjective x
  change (Submodule.Quotient.mk
    (F.levelDifferential D hd n (F.levelDifferential D hd n x)) : F.Grade n) = 0
  have hz : F.levelDifferential D hd n (F.levelDifferential D hd n x) = 0 :=
    Subtype.ext (D.square_zero x.val)
  rw [hz]
  exact Submodule.Quotient.mk_zero _

/-- The quotient differential is the usual associated graded differential in
every integer weight, under the explicitly constructed component equivalence. -/
theorem associatedGradedEquiv_differential (x : F.AssociatedGraded) :
    F.associatedGradedEquiv ((F.associatedDGA D hd hp).d x) =
      DirectSum.lmap (F.gradeDifferential D hd) (F.associatedGradedEquiv x) := by
  obtain ⟨p, rfl⟩ := F.leadingMap_surjective x
  rw [F.leadingMap_intertwines, F.associatedGradedEquiv_leading,
    F.associatedGradedEquiv_leading]
  ext n
  rfl

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end


end
