module
prelude
public import FacetSatRaw

@[expose] public section

/-!
# Reusing graph metadata for quota-clique exclusions

The clique certificate may use only selected facet kinds. Its candidate list
must cover every original candidate of those kinds, and its color or branch
certificate is checked on the original local indices. Thus the original
incidence and embedding proofs can be shared with retained graph cases.
-/

namespace Papers.RationalityTen.FacetSat

open GrowthPruning GraphFacetClique

def cliqueCoverageCheck {n : Nat} (kind : Fin n → Nat) (kinds : List Nat)
    (candidates : List (Fin n)) : Bool :=
  (List.finRange n).all fun c => decide (kind c ∈ kinds → c ∈ candidates)

theorem Boundary.excluded_of_clique_check {n r : Nat}
    {kind : Fin n → Nat} {relation : Fin n → Fin n → Bool}
    {ridges : Fin n → Fin r → Bool} {quota : Nat → Nat} {B : List (Fin n)}
    (H : Boundary kind relation ridges quota B)
    (kinds : List Nat) (candidates : List (Fin n))
    (hcover : cliqueCoverageCheck kind kinds candidates = true)
    (certificate : CliqueExclusion.QuotaCertificate n)
    (hcheck : CliqueExclusion.checkQuotas relation kind candidates
      (restrictedQuota kinds quota) certificate = true) : False := by
  let S := B.filter fun c => decide (kind c ∈ kinds)
  have hclique : CliqueExclusion.Clique relation S := by
    refine ⟨List.Pairwise.filter _ H.nodup, ?_⟩
    intro a ha b hb hab
    exact H.pairwise a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1 hab
  apply CliqueExclusion.checkQuotas_sound relation kind candidates
    (restrictedQuota kinds quota) certificate hcheck S hclique
  · intro c hc
    obtain ⟨_, hk⟩ := List.mem_filter.mp hc
    exact of_decide_eq_true
      (List.all_eq_true.mp hcover c (List.mem_finRange c)) (of_decide_eq_true hk)
  · intro j
    by_cases hj : j ∈ kinds
    · have hfiltered : CliqueExclusion.ofKind kind j S =
          B.filter (fun c => decide (kind c = j)) := by
        simp only [CliqueExclusion.ofKind, S, List.filter_filter]
        apply congrArg (fun p : Fin n → Bool => B.filter p)
        funext c
        by_cases hc : kind c = j
        · simp only [hc, hj, decide_true, Bool.true_and]
        · simp only [hc, decide_false, Bool.false_and]
      rw [restrictedQuota, ite_eq_left hj, hfiltered]
      exact Nat.le_of_eq (H.exactQuota j).symm
    · simp only [restrictedQuota, ite_eq_right hj, Nat.zero_le]

namespace RawProjection

theorem excluded_of_clique (R : PackedGraphCertificate.RawData)
    (valid : GraphGrowthInputs.Valid R.inputs)
    (checked : MatrixGraphProblem.Checked R.data)
    (vertices kinds : PackedGraphCertificate.Fields)
    (hprojection : check R vertices kinds = true)
    (selectedKinds : List Nat) (candidates : List (Fin R.n))
    (hcover : cliqueCoverageCheck (data R vertices kinds).toData.kind
      selectedKinds candidates = true)
    (certificate : CliqueExclusion.QuotaCertificate R.n)
    (hcheck : CliqueExclusion.checkQuotas (data R vertices kinds).toData.relation
      (data R vertices kinds).toData.kind candidates
      (restrictedQuota selectedKinds R.data.quota) certificate = true)
    (B : List (Fin R.n))
    (H : GraphGrowthConstraints.Target (R.inputs.problem valid) B) : False :=
  Boundary.excluded_of_clique_check
    (boundary_of_target R valid checked vertices kinds hprojection B H)
    selectedKinds candidates hcover certificate hcheck

#print axioms excluded_of_clique
end RawProjection
end Papers.RationalityTen.FacetSat
