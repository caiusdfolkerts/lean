module
public import shared_results.part018_rees_standard_identification
public import paper_results.part001
public import paper_results.part002

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ReesExcessDegree -/
section

/-! # The genuine special-fiber grading of the Rees exponent monoid -/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} (E : Finset (FiniteTuple n))

theorem finiteReesFineExponent_degree_ge (a : finiteReesExponentMonoid.{u} E) :
    (a.val none)*d≤(finiteReesFineExponent a).degree := by
  obtain ⟨b,hb,hba⟩ := finiteReesFineExponent_mem a
  rw [← finitePowerGenerator_degree (a.val none) hb]
  exact Finsupp.degree_mono hba

/-- The excess ordinary degree over the minimal generator degree.
It is an additive nonnegative grading on the actual Rees monoid. -/
def finiteReesExcessDegree : finiteReesExponentMonoid.{u} E →+ ℕ where
  toFun a := (finiteReesFineExponent a).degree-(a.val none)*d
  map_zero' := by simp [finiteReesFineExponent]
  map_add' a b := by
    have ha := finiteReesFineExponent_degree_ge E a
    have hb := finiteReesFineExponent_degree_ge E b
    rw [finiteReesFineExponent_add,map_add]
    change ((finiteReesFineExponent a).degree+(finiteReesFineExponent b).degree)-
      (a.val none+b.val none)*d=_
    rw [Nat.add_mul]
    omega

@[simp] theorem finiteReesFineExponent_target (a : Exponent (FiniteVariable.{u} n))
    (m : ℕ) (ha : finiteTargetExponent a m∈finiteReesExponentMonoid E) :
    finiteReesFineExponent ⟨finiteTargetExponent a m,ha⟩=a := by
  ext x
  simp [finiteReesFineExponent]

theorem finiteReesExcessDegree_target (a : Exponent (FiniteVariable.{u} n))
    (m : ℕ) (ha : finiteTargetExponent a m∈finiteReesExponentMonoid E) :
    finiteReesExcessDegree E ⟨finiteTargetExponent a m,ha⟩=a.degree-m*d := by
  change (finiteReesFineExponent ⟨finiteTargetExponent a m,ha⟩).degree-
    (finiteTargetExponent a m none)*d=_
  rw [finiteReesFineExponent_target,finiteTargetExponent_none]

@[simp] theorem finiteReesExcessDegree_base (x : FiniteVariable.{u} n) :
    finiteReesExcessDegree E (finiteReesBaseIndex E x)=1 := by
  simp only [finiteReesExcessDegree,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
    finiteReesBaseIndex_fine,finiteReesBaseIndex_degree,Finsupp.degree_single,
    Nat.zero_mul,Nat.sub_zero]

def finiteReesMinimalMonoid := AddMonoidHom.mker (finiteReesExcessDegree.{u} E)

variable {E}

theorem finiteReesExcessDegree_chain (m : ℕ) (w : FiniteChainStandardIndex.{u} n E m) :
    finiteReesExcessDegree E
      ⟨finiteTargetExponent (finiteChainIndexExponent w) m,
        (finiteTarget_mem_rees_iff _ _).mpr (finiteChainIndexExponent_mem w)⟩ =
          w.2.val.degree := by
  rw [finiteReesExcessDegree_target,finiteChainIndexExponent_degree,Nat.add_sub_cancel]

/-- Every positive-excess Rees monomial is divisible by one of the actual
polynomial variables. The remaining factor is still in the actual Rees monoid. -/
theorem finiteReesExcessDegree_factor (hE : finiteLatticeClosed n E)
    (a : finiteReesExponentMonoid.{u} E) (ha : finiteReesExcessDegree E a≠0) :
    ∃ x : FiniteVariable.{u} n,∃ b : finiteReesExponentMonoid.{u} E,
      a=finiteReesBaseIndex E x+b := by
  obtain ⟨w,hw⟩ := finiteChainIndexExponent_surjective hE
    (finiteReesFineExponent a) (finiteReesFineExponent_mem a)
  have hv0 : w.2.val≠0 := by
    intro hv
    apply ha
    change (finiteReesFineExponent a).degree-(a.val none)*d=0
    rw [← hw,finiteChainIndexExponent_degree,hv,map_zero,zero_add,Nat.sub_self]
  obtain ⟨x,hx⟩ := Finsupp.support_nonempty_iff.mpr hv0
  have hx0 : w.2.val x≠0 := Finsupp.mem_support_iff.mp hx
  have hs : Finsupp.single x 1≤w.2.val := by
    intro y
    by_cases hy : x=y
    · subst y
      simpa only [Finsupp.single_eq_same] using Nat.one_le_iff_ne_zero.mpr hx0
    · simp [Finsupp.single_apply,hy,Ne.symm hy]
  let v := w.2.val-Finsupp.single x 1
  let b : finiteReesExponentMonoid.{u} E :=
    ⟨finiteTargetExponent (v+finiteChainShift n w.1) (a.val none),
      ⟨finiteChainPresentation w.1 v,finiteChainPresentation_image w.1 v⟩⟩
  refine ⟨x,b,?_⟩
  apply Subtype.ext
  rw [← finiteReesTarget_reconstruct a,← hw]
  ext o
  cases o with
  | none => simp [b,finiteReesBaseIndex]
  | some y =>
      have he : Finsupp.single x 1+v=w.2.val :=
        add_tsub_cancel_of_le hs
      have hy := congrArg (fun z : Exponent (FiniteVariable.{u} n) => z y) he
      simp only [finiteChainIndexExponent,finiteTargetExponent_some,Finsupp.add_apply,
        b,finiteReesBaseIndex,AddSubmonoid.coe_add,Finsupp.single_apply,
        Option.some.injEq] at *
      omega

theorem finiteReesExcessIdeal_eq_variables {k : Type*} [CommRing k]
    (hE : finiteLatticeClosed n E) :
    GradedMonoidFiber.positiveIdeal (k:=k) (finiteReesExcessDegree.{u} E)=
      Ideal.span (Set.range fun x : FiniteVariable.{u} n =>
        AddMonoidAlgebra.single (finiteReesBaseIndex E x) (1:k)) := by
  rw [GradedMonoidFiber.positiveIdeal_eq_generatorIdeal
    (finiteReesExcessDegree E) (Set.range (finiteReesBaseIndex E))]
  · congr 1
    exact (Set.range_comp' _ _).symm
  · rintro g ⟨x,rfl⟩
    rw [finiteReesExcessDegree_base]
    omega
  · intro a ha
    obtain ⟨x,b,he⟩ := finiteReesExcessDegree_factor hE a ha
    exact ⟨_,⟨x,rfl⟩,b,he⟩

end FourPapers.Sublattice

end
end
end


end
