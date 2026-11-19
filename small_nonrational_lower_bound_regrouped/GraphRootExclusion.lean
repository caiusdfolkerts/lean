module
prelude
public import FastAvailability
public import FastGraphRuleCheck

@[expose] public section

/-!
# Empty-root exclusions using shared incidence rows

An exclusion uses only a complete allowed-cell mask, paired ridges, exact
kind quotas, vertex incidence, and the exact graph/nonedge budgets. It needs
neither compatibility-table replay nor a symmetry certificate.
-/

namespace Papers.RationalityTen.GraphRootExclusion

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth GrowthBitsets
open BatchedGrowthPruning UnsupportedRidgePruning GraphGrowthConstraints

variable {n r e v k : Nat}

structure Certificate (n r e v k : Nat) where
  eligible : Nat
  available : Nat
  removals : List (Removal n r)
  bounds : FastGraphRuleCheck.Bounds n
  rule : Rule r e v k

def check (D : Problem n r e v k) (C : Certificate n r e v k) : Bool :=
  match FastAvailability.propagate D.cache 0
      (Nat.xor (FiniteMaskSets.allMask n) C.eligible) C.removals with
  | none => false
  | some final =>
      ((decide (Nat.land (FiniteMaskSets.allMask n)
        (Nat.lor final C.available) = FiniteMaskSets.allMask n) &&
        FastGraphRuleCheck.check D [] 0 C.available C.bounds C.rule) &&
      decide (Nat.land (candidates D C.rule) C.available = 0))

theorem check_sound (D : Problem n r e v k) (hvertex : VertexCapacitySound D)
    (C : Certificate n r e v k) (hcheck : check D C = true)
    (B : List (Fin n)) (hB : GraphGrowthConstraints.Target D B)
    (hallowed : ∀ c, c ∈ B → C.eligible.testBit c.val = true) : False := by
  let blocked := Nat.xor (FiniteMaskSets.allMask n) C.eligible
  have hbase : ∀ c, family B c = true → family ([] : List (Fin n)) c = false →
      bitAt blocked c.val = false := by
    intro c hc _
    have ha := hallowed c ((has_true B c).mp hc)
    rw [bitAt_eq_testBit]
    change (Nat.xor (FiniteMaskSets.allMask n) C.eligible).testBit c.val = false
    have hx : (Nat.xor (FiniteMaskSets.allMask n) C.eligible).testBit c.val =
        ((FiniteMaskSets.allMask n).testBit c.val ^^ C.eligible.testBit c.val) :=
      Nat.testBit_xor _ _ _
    rw [hx, FiniteMaskSets.allMask_bit c, ha]
    rfl
  cases hp : FastAvailability.propagate D.cache 0 blocked C.removals with
  | none =>
    dsimp only [blocked] at hp
    have hh : false = true := by simpa only [check, hp] using hcheck
    exact Bool.noConfusion hh
  | some final =>
    dsimp only [blocked] at hp
    have hh : ((decide (Nat.land (FiniteMaskSets.allMask n)
        (Nat.lor final C.available) = FiniteMaskSets.allMask n) &&
        FastGraphRuleCheck.check D [] 0 C.available C.bounds C.rule) &&
      decide (Nat.land (candidates D C.rule) C.available = 0)) = true := by
      simpa only [check, hp] using hcheck
    obtain ⟨hlocal,hzero⟩ := Bool.and_eq_true_iff.mp hh
    obtain ⟨hcover,hrule⟩ := Bool.and_eq_true_iff.mp hlocal
    obtain ⟨hsteps,hfinal⟩ := FastAvailability.propagate_sound
      D.cache 0 blocked C.removals final hp
    have hexcluded := checks_sound D.cache [] B 0 blocked rfl hbase
      hB.boundary.mates C.removals hsteps
    have havail : Available [] B C.available := by
      intro c hc _
      apply FiniteMaskSets.bit_of_cover (of_decide_eq_true hcover) c
      have hz := hexcluded c ((has_true B c).mpr hc) rfl
      simpa only [hfinal, bitAt_eq_testBit] using hz
    have hsub : Included (family ([] : List (Fin n))) (family B) := by
      intro c hc
      exact False.elim (Bool.noConfusion hc)
    obtain ⟨c,hc,hnot,hcandidate⟩ := ruleCheck_sound D hvertex [] B 0 C.available
      rfl hB List.nodup_nil hsub havail C.rule
      (FastGraphRuleCheck.check_sound D [] 0 C.available C.bounds C.rule hrule)
    have ha := havail c hc hnot
    have hz := congrArg (fun bits => bits.testBit c.val) (of_decide_eq_true hzero)
    simp only [FiniteMaskSets.testBit_land, hcandidate, ha, Bool.true_and,
      Nat.zero_testBit] at hz
    exact Bool.noConfusion hz

#print axioms check_sound
end Papers.RationalityTen.GraphRootExclusion
