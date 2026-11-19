module
public import paper_results.rees_excess_degree
public import paper_results.part003

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.AlcoveReesFiberMonoid -/
section

/-! # The special-fiber exponent monoid is the actual integral order cone -/

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid FiniteDistributive
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (hE : finiteLatticeClosed n E) (hne : E.Nonempty)

def orderConeRowExponent (a : orderCone (AlcoveLattice hE)) : Exponent (FiniteVariable.{u} n) :=
  alcovePointLabel hE hne (a.val none) (orderConePoint (AlcoveLattice hE) a)

theorem orderConeSymbolValue_add (a b : orderCone (AlcoveLattice hE)) (c : CoordinateSymbol (AlcoveIrreducible hE)) :
    symbolValue (AlcoveLattice hE) ((a+b).val none) (orderConePoint (AlcoveLattice hE) (a+b)).val c =
      symbolValue (AlcoveLattice hE) (a.val none) (orderConePoint (AlcoveLattice hE) a).val c+
        symbolValue (AlcoveLattice hE) (b.val none) (orderConePoint (AlcoveLattice hE) b).val c := by
  cases c <;> rfl

theorem orderConeRowExponent_add (a b : orderCone (AlcoveLattice hE)) :
    orderConeRowExponent.{u} hE hne (a+b)=
      orderConeRowExponent hE hne a+orderConeRowExponent hE hne b := by
  ext x
  obtain ⟨r,⟨j⟩⟩ := x
  simp only [orderConeRowExponent,alcovePointLabel_apply,Finsupp.add_apply,
    orderConeSymbolValue_add]
  have ha := rowThresholdValue_antitone hE hne (a.val none) (orderConePoint (AlcoveLattice hE) a) r
    (Nat.le_succ j.val)
  have hb := rowThresholdValue_antitone hE hne (b.val none) (orderConePoint (AlcoveLattice hE) b) r
    (Nat.le_succ j.val)
  simpa only [Nat.succ_eq_add_one] using (tsub_add_tsub_comm ha hb).symm

theorem orderConeRowExponent_zero : orderConeRowExponent.{u} hE hne 0=0 := by
  apply (Finsupp.degree_eq_zero_iff _).mp
  change (alcovePointLabel hE hne 0 (orderConePoint (AlcoveLattice hE) 0)).degree=0
  simpa only [Nat.zero_mul] using
    alcovePointLabel_degree hE hne 0 (orderConePoint (AlcoveLattice hE) 0)

/-- Both the auxiliary coordinate and all original row exponents are
retained by this explicit additive map. -/
def orderConeToReesMinimal : orderCone (AlcoveLattice hE) →+ finiteReesMinimalMonoid.{u} E where
  toFun a := ⟨⟨finiteTargetExponent (orderConeRowExponent hE hne a) (a.val none),
      (finiteTarget_mem_rees_iff _ _).mpr
        ⟨_,alcovePointLabel_mem_powerFamily hE hne _ (orderConePoint (AlcoveLattice hE) a),
          fun _ => Nat.le_refl _⟩⟩,by
      change finiteReesExcessDegree E _=0
      rw [finiteReesExcessDegree_target,orderConeRowExponent,alcovePointLabel_degree,
        Nat.sub_self]⟩
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [orderConeRowExponent_zero,finiteTargetExponent,zero_add,
      Finsupp.embDomain_zero,AddSubmonoid.coe_zero,Finsupp.zero_apply,Finsupp.single_zero]
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    ext o
    cases o with
    | none => simp only [finiteTargetExponent_none,AddSubmonoid.coe_add,Finsupp.add_apply]
    | some x => simp only [finiteTargetExponent_some,AddSubmonoid.coe_add,Finsupp.add_apply,
        orderConeRowExponent_add]

def alcovePointTarget (f : Σ m : ℕ,AlcovePoint hE m) : Option (FiniteVariable.{u} n) →₀ ℕ :=
  finiteTargetExponent (alcovePointLabel hE hne f.1 f.2) f.1

theorem alcovePointTarget_injective : Function.Injective (alcovePointTarget.{u} hE hne) := by
  rintro ⟨m,f⟩ ⟨r,g⟩ he
  obtain ⟨hfg,hmr⟩ := finiteTargetExponent_injective he
  change m = r at hmr
  subst r
  have hfg' := alcovePointLabel_injective hE hne m hfg
  change f=g at hfg'
  cases hfg'
  rfl

theorem orderConeToReesMinimal_injective : Function.Injective (orderConeToReesMinimal.{u} hE hne) := by
  letI : OrderBot (AlcoveLattice hE) := finiteTupleOrderBot hE hne
  intro a b he
  have ht : alcovePointTarget hE hne ⟨a.val none,orderConePoint (AlcoveLattice hE) a⟩=
      alcovePointTarget hE hne ⟨b.val none,orderConePoint (AlcoveLattice hE) b⟩ :=
    congrArg (fun z : finiteReesMinimalMonoid.{u} E => z.val.val) he
  have hp := alcovePointTarget_injective hE hne ht
  have hc := congrArg (fun z : Σ m : ℕ,AlcovePoint hE m => orderPointCone (AlcoveLattice hE) z.1 z.2) hp
  exact (orderPointCone_conePoint (AlcoveLattice hE) a).symm.trans
    (hc.trans (orderPointCone_conePoint (AlcoveLattice hE) b))

theorem orderConeToReesMinimal_surjective : Function.Surjective (orderConeToReesMinimal.{u} hE hne) := by
  letI : OrderBot (AlcoveLattice hE) := finiteTupleOrderBot hE hne
  intro a
  obtain ⟨w,hw⟩ := finiteChainIndexExponent_surjective hE
    (finiteReesFineExponent a.val) (finiteReesFineExponent_mem a.val)
  have hdegree := congrArg Finsupp.degree hw
  rw [finiteChainIndexExponent_degree] at hdegree
  have hz : (finiteReesFineExponent a.val).degree-(a.val.val none)*d=0 := a.property
  have hv : w.2.val=0 := (Finsupp.degree_eq_zero_iff _).mp (by omega)
  have hlabel : alcovePointLabel hE hne (a.val.val none)
      (alcoveChainPoint hE hne _ w.1)=finiteReesFineExponent a.val := by
    rw [alcovePointLabel,alcovePointChain_chainPoint]
    simpa only [finiteChainIndexExponent,hv,zero_add] using hw
  refine ⟨orderPointCone (AlcoveLattice hE) (a.val.val none) (alcoveChainPoint hE hne _ w.1),?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change finiteTargetExponent (orderConeRowExponent hE hne
      (orderPointCone (AlcoveLattice hE) (a.val.val none) (alcoveChainPoint hE hne _ w.1)))
        (a.val.val none)=a.val.val
  have hrow : orderConeRowExponent hE hne
      (orderPointCone (AlcoveLattice hE) (a.val.val none) (alcoveChainPoint hE hne _ w.1)) =
        finiteReesFineExponent a.val := by
    change alcovePointLabel hE hne (a.val.val none)
      (orderConePoint (AlcoveLattice hE)
        (orderPointCone (AlcoveLattice hE) (a.val.val none) (alcoveChainPoint hE hne _ w.1))) = _
    rw [orderConePoint_pointCone]
    exact hlabel
  rw [hrow,finiteReesTarget_reconstruct]

def orderConeReesMinimalEquiv : orderCone (AlcoveLattice hE) ≃+ finiteReesMinimalMonoid.{u} E :=
  AddEquiv.ofBijective (orderConeToReesMinimal hE hne)
    ⟨orderConeToReesMinimal_injective hE hne,orderConeToReesMinimal_surjective hE hne⟩

end FourPapers.Sublattice

end
end
end


end
