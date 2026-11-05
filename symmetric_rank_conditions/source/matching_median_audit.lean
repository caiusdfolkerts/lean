module
public import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Nat.Basic

@[expose] public section
set_option autoImplicit false

namespace FourPapers.Symmetric

/-- The local restrictions of a fixed-point-free matching at three consecutive labels.
The reciprocal-pair laws and distinct partners are explicit hypotheses. -/
structure MatchingTriple (k α β γ : ℕ) : Prop where
  a_ne : α ≠ k
  b_ne : β ≠ k + 1
  c_ne : γ ≠ k + 2
  ab : α = k + 1 ↔ β = k
  ac : α = k + 2 ↔ γ = k
  bc : β = k + 2 ↔ γ = k + 1
  ab_ne : α ≠ β
  ac_ne : α ≠ γ
  bc_ne : β ≠ γ

def modifiedPartner (k label partner : ℕ) : ℕ :=
  if partner = k ∨ partner = k+1 ∨ partner = k+2 then label else partner

def StrictMedian (x y z : ℕ) : Prop :=
  (x < y ∧ y < z) ∨ (z < y ∧ y < x)

def swapFirst (k x : ℕ) : ℕ :=
  if x = k then k+1 else if x = k+1 then k else x

def swapLast (k x : ℕ) : ℕ :=
  if x = k+1 then k+2 else if x = k+2 then k+1 else x

private theorem MatchingTriple.external {k α β γ : ℕ} (h : MatchingTriple k α β γ)
    (hab : α ≠ k+1) (hac : α ≠ k+2) (hbc : β ≠ k+2) :
    (α ≠ k ∧ α ≠ k+1 ∧ α ≠ k+2) ∧
    (β ≠ k ∧ β ≠ k+1 ∧ β ≠ k+2) ∧
    (γ ≠ k ∧ γ ≠ k+1 ∧ γ ≠ k+2) := by
  exact ⟨⟨h.a_ne,hab,hac⟩,⟨fun hb => hab (h.ab.mpr hb),h.b_ne,hbc⟩,
    ⟨fun hc => hac (h.ac.mpr hc),fun hc => hbc (h.bc.mpr hc),h.c_ne⟩⟩

/-- Fixed dual moves are exactly the middle-partner median case. This uses the
actual matching descent formula, including its exception for an adjacent pair. -/
theorem matching_middle_median_iff {k α β γ : ℕ} (h : MatchingTriple k α β γ) :
    StrictMedian (modifiedPartner k k α) (modifiedPartner k (k+1) β)
      (modifiedPartner k (k+2) γ) ↔
      ((β < α ∧ α ≠ k+1) ↔ (γ < β ∧ β ≠ k+2)) := by
  have hα := h.a_ne
  have hβ := h.b_ne
  have hγ := h.c_ne
  by_cases hab : α = k+1
  · have hba : β = k := h.ab.mp hab
    have hc0 : γ ≠ k := by intro hc; have := h.ac.mpr hc; omega
    have hc1 : γ ≠ k+1 := by intro hc; have := h.bc.mpr hc; omega
    simp [hab,hba,modifiedPartner,StrictMedian,hc0,hc1,h.c_ne] <;> omega
  by_cases hac : α = k+2
  · have hca : γ = k := h.ac.mp hac
    have hb0 : β ≠ k := by intro hb; exact hab (h.ab.mpr hb)
    have hb2 : β ≠ k+2 := by intro hb; have := h.bc.mp hb; omega
    simp [hac,hca,modifiedPartner,StrictMedian,hb0,h.b_ne,hb2] <;> omega
  by_cases hbc : β = k+2
  · have hcb : γ = k+1 := h.bc.mp hbc
    simp [hbc,hcb,modifiedPartner,StrictMedian,h.a_ne,hab,hac] <;> omega
  · obtain ⟨ha,hb,hc⟩ := h.external hab hac hbc
    simp only [modifiedPartner,ha.1,ha.2.1,ha.2.2,hb.1,hb.2.1,hb.2.2,
      hc.1,hc.2.1,hc.2.2,or_self,if_false,StrictMedian]
    have := h.ab_ne; have := h.ac_ne; have := h.bc_ne
    omega

/-- If conjugation by the first adjacent transposition toggles the other
consecutive descent, the third modified partner is the median. -/
theorem matching_first_swap_forces_median {k α β γ : ℕ} (h : MatchingTriple k α β γ)
    (htoggle : (swapFirst k γ < swapFirst k α ∧ swapFirst k α ≠ k+2) ↔
      ¬(γ < β ∧ β ≠ k+2)) :
    StrictMedian (modifiedPartner k k α) (modifiedPartner k (k+2) γ)
      (modifiedPartner k (k+1) β) := by
  have hα := h.a_ne
  have hβ := h.b_ne
  have hγ := h.c_ne
  by_cases hab : α = k+1
  · have hba : β = k := h.ab.mp hab
    have hc0 : γ ≠ k := by intro hc; have := h.ac.mpr hc; omega
    have hc1 : γ ≠ k+1 := by intro hc; have := h.bc.mpr hc; omega
    simp [swapFirst,hab,hba,hc0,hc1] at htoggle <;> omega
  by_cases hac : α = k+2
  · have hca : γ = k := h.ac.mp hac
    have hb0 : β ≠ k := by intro hb; exact hab (h.ab.mpr hb)
    have hb2 : β ≠ k+2 := by intro hb; have := h.bc.mp hb; omega
    simp [swapFirst,hac,hca] at htoggle
    simp [modifiedPartner,hac,hca,hb0,h.b_ne,hb2,StrictMedian] <;> omega
  by_cases hbc : β = k+2
  · have hcb : γ = k+1 := h.bc.mp hbc
    simp [swapFirst,hbc,hcb,h.a_ne,hab] at htoggle
    simp [modifiedPartner,hbc,hcb,h.a_ne,hab,hac,StrictMedian] <;> omega
  · obtain ⟨ha,hb,hc⟩ := h.external hab hac hbc
    simp only [swapFirst,ha.1,ha.2.1,hc.1,hc.2.1,if_false] at htoggle
    simp only [modifiedPartner,ha.1,ha.2.1,ha.2.2,hb.1,hb.2.1,hb.2.2,
      hc.1,hc.2.1,hc.2.2,or_self,if_false,StrictMedian]
    have := h.ab_ne; have := h.ac_ne; have := h.bc_ne
    omega

/-- The symmetric characterization for the last adjacent transposition. -/
theorem matching_last_swap_forces_median {k α β γ : ℕ} (h : MatchingTriple k α β γ)
    (htoggle : (swapLast k γ < swapLast k α ∧ swapLast k α ≠ k+1) ↔
      ¬(β < α ∧ α ≠ k+1)) :
    StrictMedian (modifiedPartner k (k+1) β) (modifiedPartner k k α)
      (modifiedPartner k (k+2) γ) := by
  have hα := h.a_ne
  have hβ := h.b_ne
  have hγ := h.c_ne
  by_cases hab : α = k+1
  · have hba : β = k := h.ab.mp hab
    have hc0 : γ ≠ k := by intro hc; have := h.ac.mpr hc; omega
    have hc1 : γ ≠ k+1 := by intro hc; have := h.bc.mpr hc; omega
    simp [swapLast,hab,hba,hc1,h.c_ne] at htoggle
    simp [modifiedPartner,hab,hba,hc0,hc1,h.c_ne,StrictMedian] <;> omega
  by_cases hac : α = k+2
  · have hca : γ = k := h.ac.mp hac
    have hb0 : β ≠ k := by intro hb; exact hab (h.ab.mpr hb)
    have hb2 : β ≠ k+2 := by intro hb; have := h.bc.mp hb; omega
    simp [swapLast,hac,hca] at htoggle
    simp [modifiedPartner,hac,hca,hb0,h.b_ne,hb2,StrictMedian] <;> omega
  by_cases hbc : β = k+2
  · have hcb : γ = k+1 := h.bc.mp hbc
    simp [swapLast,hbc,hcb,hab,hac] at htoggle <;> omega
  · obtain ⟨ha,hb,hc⟩ := h.external hab hac hbc
    simp only [swapLast,ha.2.1,ha.2.2,hc.2.1,hc.2.2,if_false] at htoggle
    simp only [modifiedPartner,ha.1,ha.2.1,ha.2.2,hb.1,hb.2.1,hb.2.2,
      hc.1,hc.2.1,hc.2.2,or_self,if_false,StrictMedian]
    have := h.ab_ne; have := h.ac_ne; have := h.bc_ne
    omega

end FourPapers.Symmetric

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constants := env.checked.get.constants.foldStage2
    (fun acc name ci => acc.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  for (name, ci) in constants do
    if ci.isAxiom then
      throwError "Unapproved local axiom: {name}"
    if ci.isUnsafe || ci.isPartial then
      unless name.getString! == "_unsafe_rec" do
        throwError "Authored or unrecognized unsafe declaration: {name}"
      match env.find? name.getPrefix with
      | some parent =>
        if parent.isUnsafe || parent.isPartial || parent.isAxiom then
          throwError "Unsafe runtime companion lacks safe defining declaration: {name}"
      | none => throwError "Unrecognized runtime companion: {name}"
      logInfo m!"COMPILER_RUNTIME_ONLY {name}"
    else
      if ci.isPartial then throwError "Unapproved partial declaration: {name}"
      for dep in ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants |>.getD #[]) do
        if let some info := env.find? dep then
          if info.isUnsafe || info.isPartial then
            throwError "Unsafe proof dependency {dep} in safe declaration {name}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, ci) in constants do
    if ci.isUnsafe || ci.isPartial then continue
    let axs ← collectAxioms name
    for ax in axs do
      if !allowed.contains ax then
        throwError "Unapproved axiom in supporting declaration {name}: {ax}"
  let roots : Array Name := #[`FourPapers.Symmetric.matching_middle_median_iff, `FourPapers.Symmetric.matching_first_swap_forces_median, `FourPapers.Symmetric.matching_last_swap_forces_median]
  for root in roots do
    let axs ← collectAxioms root
    for ax in axs do
      if !allowed.contains ax then
        throwError "Unapproved axiom in {root}: {ax}"
  let ctors (ci : ConstantInfo) : Array Name :=
    match ci with
    | .inductInfo v => v.ctors.toArray
    | _ => #[]
  let mut names : NameSet := {}
  for (name, ci) in constants do
    names := names.insert name
    for dep in ci.type.getUsedConstants do
      names := names.insert dep
    for dep in (ci.value? true).map Expr.getUsedConstants |>.getD #[] do
      names := names.insert dep
    for dep in ctors ci do
      names := names.insert dep
  let dictionary := names.toArray.qsort Name.lt
  let mut indices : NameMap Nat := {}
  for i in [:dictionary.size] do
    indices := indices.insert dictionary[i]! i
  let index (n : Name) := (indices.find? n).getD 0
  let data := constants.map fun (name, ci) =>
    let typeDeps := ci.type.getUsedConstants
    let valueDeps := (ci.value? true).map Expr.getUsedConstants |>.getD #[]
    Json.arr #[toJson (index name), toJson (typeDeps.map index),
      toJson (valueDeps.map index), toJson ((ctors ci).map index),
      toJson ci.isAxiom, toJson ci.isUnsafe, toJson ci.isPartial]
  let graph := Json.mkObj [
    ("format", toJson "local-proof-dag-v1"),
    ("columns", toJson (#["name", "type", "value", "inductiveCtors", "axiom", "unsafe", "partial"] : Array String)),
    ("names", toJson (dictionary.map Name.toString)),
    ("nodes", Json.arr data),
    ("roots", toJson (roots.map index))]
  logInfo m!"DEPENDENCY_GRAPH {Json.compress graph}"
  logInfo m!"AUDIT_OK {constants.size} local declarations; {roots.size} roots; no local axioms, authored unsafe or partial declarations; compiler runtime companions excluded from every safe proof dependency."
