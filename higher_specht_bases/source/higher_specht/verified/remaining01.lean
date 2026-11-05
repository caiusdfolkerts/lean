module

public import higher_specht.verified.basis_continuation02

/- Generated ordinary source-preserving proof stage. See audit/staged_specht_remaining/Remaining01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: HigherSpecht/BoostedNorm.lean -/



/-!
# The norm bound for the literal boosted higher Specht polynomial

This specializes the subset-choice extremum to an actual supported monomial
of `F_T^S E_eta`.  Both its Young-operator monomial and its elementary-factor
monomial are obtained from coefficient expansion; neither is an additional
support assumption.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset MvPolynomial Equiv Function TauCeti TauCeti.YoungTableau

namespace HigherSpecht

variable {R : Type*} [CommRing R]

theorem coeff_mul_ne_zero_exists {ι : Type*} [DecidableEq ι]
    (P Q : MvPolynomial ι R) (beta : ι →₀ ℕ) (h : (P * Q).coeff beta ≠ 0) :
    ∃ a delta : ι →₀ ℕ, P.coeff a ≠ 0 ∧ Q.coeff delta ≠ 0 ∧ a + delta = beta := by
  rw [MvPolynomial.coeff_mul] at h
  obtain ⟨z, hz, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨z.1, z.2, left_ne_zero_of_mul hterm, right_ne_zero_of_mul hterm,
    Finset.mem_antidiagonal.mp hz⟩

theorem elementaryMultiplier_isSymmetric (n m : ℕ) (eta : ℕ → ℕ) :
    (elementaryMultiplier (R := R) n m eta).IsSymmetric := by
  intro σ
  simp only [elementaryMultiplier, map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro j hj
  rw [MvPolynomial.esymm_isSymmetric]

theorem elementaryMultiplier_coeff_permuted (n m : ℕ) (eta : ℕ → ℕ)
    (delta : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin n)) :
    (elementaryMultiplier (R := R) n m eta).coeff (permutedExponent delta σ) =
      (elementaryMultiplier n m eta).coeff delta := by
  rw [← coeff_rename_perm, elementaryMultiplier_isSymmetric]

def tableauLabelEquiv {μ : YoungDiagram} (S : StandardYoungTableau μ) (T : YoungTableau μ) :
    Equiv.Perm (Fin μ.card) := T.symm.trans S.toTableau

@[simp] theorem transportedCocharge_apply_labelEquiv {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ) (i : Fin μ.card) :
    transportedCocharge S T i = cochargeLabel S (tableauLabelEquiv S T i) := rfl

@[simp] theorem transportedBoosted_apply_labelEquiv {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ) (eta : YoungDiagram)
    (i : Fin μ.card) :
    transportedBoosted S T eta i = boostedLabel S eta (tableauLabelEquiv S T i) := rfl

/-- The full supported-monomial norm bound in Lemma 4.2, for every shape,
every multiplier of the permitted length, and every coefficient ring. -/
theorem lemma_4_2_norm_bound {μ : YoungDiagram} (S T : StandardYoungTableau μ)
    {m : ℕ} (hm : m ≤ μ.card) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m)
    (beta : Fin μ.card →₀ ℕ)
    (hbeta : (higherSpechtPolynomial (R := R) S T *
      elementaryMultiplier μ.card m eta.rowLen).coeff beta ≠ 0) :
    squareNorm (intExponent beta) ≤ squareNorm (intExponent (transportedBoosted S T.toTableau eta)) := by
  obtain ⟨a, delta, ha, hdelta, rfl⟩ := coeff_mul_ne_zero_exists
    (higherSpechtPolynomial S T) (elementaryMultiplier μ.card m eta.rowLen) beta hbeta
  obtain ⟨σ, ρ, rfl⟩ := youngApply_coeff_ne_zero T.toTableau
    (transportedCocharge S T.toTableau) a ha
  let e := tableauLabelEquiv S T.toTableau
  let τ : Equiv.Perm (Fin μ.card) :=
    e.symm.trans (σ.val.symm.trans (ρ.val.symm.trans e))
  have hdelta' : (elementaryMultiplier (R := R) μ.card m eta.rowLen).coeff
      (permutedExponent delta e.symm) ≠ 0 := by
    rwa [elementaryMultiplier_coeff_permuted]
  have h := elementaryMultiplier_supported_norm_bound hm eta heta
    (fun i => (cochargeLabel S i : ℤ))
    (fun i j hij => by
      change (cochargeLabel S i : ℤ) ≤ (cochargeLabel S j : ℤ)
      exact_mod_cast cochargeLabel_mono S hij) τ
    (permutedExponent delta e.symm) hdelta'
  have hleft :
      (fun i => (cochargeLabel S (τ i) : ℤ) + (permutedExponent delta e.symm i : ℤ)) =
        intExponent (youngExponent T.toTableau (transportedCocharge S T.toTableau) σ ρ + delta) ∘ e.symm := by
    funext i
    simp only [Function.comp_apply, intExponent, Finsupp.add_apply, Nat.cast_add,
      youngExponent, permutedExponent_apply, transportedCocharge_apply_labelEquiv,
      τ, Equiv.trans_apply, e]
  have hright :
      intExponent (transportedBoosted S T.toTableau eta) =
        (fun i => (cochargeLabel S i : ℤ) + (boostLabel eta μ.card i : ℤ)) ∘ e := by
    funext i
    simp only [intExponent, transportedBoosted_apply_labelEquiv, boostedLabel,
      Nat.cast_add, Function.comp_apply, e]
  rw [hleft, squareNorm_comp_perm] at h
  rw [hright, squareNorm_comp_perm]
  exact h

end HigherSpecht
end
end CanonicalSource0

section CanonicalSource1
/- Source: HigherSpecht/BoostedLevelGeometry.lean -/



/-!
# The actual ordering of equal cocharge levels

Inside a fixed cocharge level, the standard labels occur in strictly increasing
column order.  Reversed partition parts therefore assign larger boosts to later
columns.  Different cocharge levels remain strictly separated after boosting.
These facts discharge the geometric inputs of the boosted rearrangement proof.
-/

noncomputable section

open Function Equiv TauCeti TauCeti.YoungTableau

namespace HigherSpecht

variable {mu : YoungDiagram}

theorem standard_label_le_of_coordinates_le (S : StandardYoungTableau mu)
    {i j : Fin mu.card} (hr : rowIndex S.toTableau i ≤ rowIndex S.toTableau j)
    (hc : colIndex S.toTableau i ≤ colIndex S.toTableau j) : i ≤ j := by
  let c : ↥mu.cells := ⟨(rowIndex S.toTableau i, colIndex S.toTableau j),
    mu.up_left_mem hr le_rfl (rowIndex_colIndex_mem S.toTableau j)⟩
  have hic : i ≤ S c := by
    rcases hc.eq_or_lt with h | h
    · have heq : S.toTableau.symm i = c := by
        apply Subtype.ext
        exact Prod.ext (rowIndex_def S.toTableau i).symm
          ((colIndex_def S.toTableau i).symm.trans h)
      rw [← heq, standardTableau_apply_symm]
    · exact (S.lt_of_colIndex_lt (by simp only [rowIndex_standard_apply, c])
        (by simpa only [colIndex_standard_apply, c] using h)).le
  have hcj : S c ≤ j := by
    rcases hr.eq_or_lt with h | h
    · have heq : c = S.toTableau.symm j := by
        apply Subtype.ext
        exact Prod.ext (h.trans (rowIndex_def S.toTableau j))
          (colIndex_def S.toTableau j)
      rw [heq, standardTableau_apply_symm]
    · exact (S.lt_of_rowIndex_lt (by simp only [colIndex_standard_apply, c])
        (by simpa only [rowIndex_standard_apply, c] using h)).le
  exact hic.trans hcj

theorem cocharge_equal_column_strict (S : StandardYoungTableau mu)
    {i j : Fin mu.card} (hcc : cochargeLabel S i = cochargeLabel S j) (hij : i < j) :
    colIndex S.toTableau i < colIndex S.toTableau j := by
  by_contra hn
  have hrow := row_le_of_cochargeLabel_eq S hij.le hcc
  have hji := standard_label_le_of_coordinates_le S hrow (le_of_not_gt hn)
  exact (not_le_of_gt hij) hji

theorem cocharge_equal_label_lt_of_column_lt (S : StandardYoungTableau mu)
    {i j : Fin mu.card} (hcc : cochargeLabel S i = cochargeLabel S j)
    (hc : colIndex S.toTableau i < colIndex S.toTableau j) : i < j := by
  by_contra hn
  rcases (le_of_not_gt hn).eq_or_lt with h | h
  · exact (lt_irrefl (colIndex S.toTableau i)) (by simpa only [h] using hc)
  · exact (not_lt_of_ge hc.le) (cocharge_equal_column_strict S hcc.symm h)

@[simp] theorem colIndex_tableauLabelEquiv (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (i : Fin mu.card) :
    colIndex S.toTableau (tableauLabelEquiv S T i) = colIndex T i := by
  simp only [tableauLabelEquiv, Equiv.trans_apply, colIndex_def, Equiv.symm_apply_apply]

theorem transportedBoosted_strict_bands (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (eta : YoungDiagram) (i j : Fin mu.card)
    (ha : (transportedCocharge S T i : ℤ) < transportedCocharge S T j) :
    (transportedBoosted S T eta i : ℤ) < transportedBoosted S T eta j := by
  rw [transportedCocharge_apply_labelEquiv, transportedCocharge_apply_labelEquiv] at ha
  have hlabel : tableauLabelEquiv S T i < tableauLabelEquiv S T j := by
    by_contra hn
    have hm := cochargeLabel_mono S (le_of_not_gt hn)
    exact (not_le_of_gt ha) (by exact_mod_cast hm)
  rw [transportedBoosted_apply_labelEquiv, transportedBoosted_apply_labelEquiv]
  have hboost := boostLabel_mono eta mu.card hlabel.le
  dsimp only [boostedLabel]
  push_cast
  exact add_lt_add_of_lt_of_le ha (by exact_mod_cast hboost)

theorem colIndex_injective_on_cocharge (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (j : ℤ) :
    Function.Injective (fun i : {i // intExponent (transportedCocharge S T) i = j} =>
      (colIndex T i : ℤ)) := by
  intro i l hcol
  change (colIndex T i.val : ℤ) = (colIndex T l.val : ℤ) at hcol
  have hcol' : colIndex T i.val = colIndex T l.val := by exact_mod_cast hcol
  have hcc : transportedCocharge S T i.val = transportedCocharge S T l.val := by
    exact Int.ofNat_inj.mp (i.property.trans l.property.symm)
  have heq := transportedCocharge_columnDistinct S T (colIndex T i.val)
    (a₁ := ⟨i.val, rfl⟩) (a₂ := ⟨l.val, hcol'.symm⟩) hcc
  exact Subtype.ext (congrArg
    (fun z : {x : Fin mu.card // colIndex T x = colIndex T i.val} => z.val) heq)

theorem transportedBoosted_cochargeLevelMonovary (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (eta : YoungDiagram) (j : ℤ) :
    Monovary (fun i : {i // intExponent (transportedCocharge S T) i = j} => (colIndex T i : ℤ))
      (fun i : {i // intExponent (transportedCocharge S T) i = j} =>
        intExponent (transportedBoosted S T eta) i) := by
  apply Monovary.symm
  intro i l hcol
  change (colIndex T i.val : ℤ) < (colIndex T l.val : ℤ) at hcol
  have hcc : cochargeLabel S (tableauLabelEquiv S T i.val) =
      cochargeLabel S (tableauLabelEquiv S T l.val) := by
    have hnat : transportedCocharge S T i.val = transportedCocharge S T l.val :=
      Int.ofNat_inj.mp (i.property.trans l.property.symm)
    simpa only [transportedCocharge_apply_labelEquiv] using hnat
  have hcol' : colIndex S.toTableau (tableauLabelEquiv S T i.val) <
      colIndex S.toTableau (tableauLabelEquiv S T l.val) := by
    simpa only [colIndex_tableauLabelEquiv] using (show colIndex T i.val < colIndex T l.val by
      exact_mod_cast hcol)
  have hlabel := cocharge_equal_label_lt_of_column_lt S hcc hcol'
  change (transportedBoosted S T eta i.val : ℤ) ≤
    (transportedBoosted S T eta l.val : ℤ)
  rw [transportedBoosted_apply_labelEquiv, transportedBoosted_apply_labelEquiv]
  exact_mod_cast boostedLabel_mono S eta hlabel.le

end HigherSpecht
end
end CanonicalSource1

section CanonicalSource2
/- Source: HigherSpecht/BoostedSupport.lean -/



/-!
# The full extremal support of the specified elementary multiples

The permutation data below is extracted from a nonzero coefficient of the
literal product.  Norm equality forces its elementary subsets to be nested;
their common sorting permutation transports both cocharge and boost.  The
actual row/cocharge geometry then gives all prefix inequalities and the
column-orbit equality case in Lemma 4.2.
-/

noncomputable section

open Finset MvPolynomial Equiv Function TauCeti TauCeti.YoungTableau

namespace HigherSpecht

variable {R : Type*} [CommRing R] {mu : YoungDiagram}

theorem youngExponent_boosted_norm_tie_data (S T : StandardYoungTableau mu)
    {m : ℕ} (hm : m ≤ mu.card) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m)
    (sigma : colSubgroup T.toTableau) (rho : rowSubgroup T.toTableau)
    (delta : Fin mu.card →₀ ℕ)
    (hdelta : (elementaryMultiplier (R := R) mu.card m eta.rowLen).coeff delta ≠ 0)
    (hnorm : squareNorm (intExponent
      (youngExponent T.toTableau (transportedCocharge S T.toTableau) sigma rho + delta)) =
      squareNorm (intExponent (transportedBoosted S T.toTableau eta))) :
    ∃ pi : Equiv.Perm (Fin mu.card),
      intExponent (youngExponent T.toTableau (transportedCocharge S T.toTableau) sigma rho + delta) =
        (intExponent (transportedBoosted S T.toTableau eta) ∘ pi) ∘ sigma.val.symm ∧
      intExponent (transportedCocharge S T.toTableau) ∘ pi =
        intExponent (transportedCocharge S T.toTableau) ∘ rho.val.symm := by
  let e := tableauLabelEquiv S T.toTableau
  let rho0 : Equiv.Perm (Fin mu.card) := e.symm.trans (rho.val.symm.trans e)
  let delta0 := permutedExponent delta (e.symm.trans sigma.val)
  have hd0 : (elementaryMultiplier (R := R) mu.card m eta.rowLen).coeff delta0 ≠ 0 := by
    simpa only [delta0, elementaryMultiplier_coeff_permuted] using hdelta
  have hleft : (fun i => (cochargeLabel S (rho0 i) : ℤ) + (delta0 i : ℤ)) =
      intExponent (youngExponent T.toTableau (transportedCocharge S T.toTableau) sigma rho + delta) ∘
        (e.symm.trans sigma.val) := by
    funext i
    simp only [rho0, delta0, Function.comp_apply, Equiv.trans_apply, intExponent,
      Finsupp.add_apply, Nat.cast_add, youngExponent, permutedExponent_apply,
      transportedCocharge_apply_labelEquiv, Equiv.symm_apply_apply, e]
  have hright : (fun i => (cochargeLabel S i : ℤ) + (boostLabel eta mu.card i : ℤ)) =
      intExponent (transportedBoosted S T.toTableau eta) ∘ e.symm := by
    funext i
    simp only [Function.comp_apply, intExponent, transportedBoosted_apply_labelEquiv,
      boostedLabel, Nat.cast_add, e, Equiv.apply_symm_apply]
  have hn0 : squareNorm (fun i => (cochargeLabel S (rho0 i) : ℤ) + (delta0 i : ℤ)) =
      squareNorm (fun i => (cochargeLabel S i : ℤ) + (boostLabel eta mu.card i : ℤ)) := by
    rw [hleft, hright, squareNorm_comp_perm, squareNorm_comp_perm]
    exact hnorm
  obtain ⟨tau, hbase, hboost⟩ := elementaryMultiplier_extremal_components hm eta heta
    (fun i => (cochargeLabel S i : ℤ))
    (fun i j hij => by
      change (cochargeLabel S i : ℤ) ≤ (cochargeLabel S j : ℤ)
      exact_mod_cast cochargeLabel_mono S hij) rho0 delta0 hd0 hn0
  let pi : Equiv.Perm (Fin mu.card) := e.trans (tau.symm.trans e.symm)
  have hbase_at (i : Fin mu.card) :
      (cochargeLabel S (rho0 (e i)) : ℤ) = cochargeLabel S (tau.symm (e i)) := by
    have h := congrFun hbase (tau.symm (e i))
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h
  have hboost_at (i : Fin mu.card) : (delta0 (e i) : ℤ) = boostLabel eta mu.card (tau.symm (e i)) := by
    have h := congrFun hboost (tau.symm (e i))
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h
  refine ⟨pi, ?_, ?_⟩
  · funext i
    have ha' := hbase_at (sigma.val.symm i)
    have hd' := hboost_at (sigma.val.symm i)
    dsimp only [rho0, delta0, Equiv.trans_apply, permutedExponent_apply] at ha' hd'
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at ha' hd'
    change ((transportedCocharge S T.toTableau (rho.val.symm (sigma.val.symm i)) : ℕ) : ℤ) +
      (delta i : ℤ) = (transportedBoosted S T.toTableau eta (pi (sigma.val.symm i)) : ℤ)
    simp only [transportedCocharge_apply_labelEquiv, transportedBoosted_apply_labelEquiv,
      pi, Equiv.trans_apply, boostedLabel, Nat.cast_add, e, Equiv.apply_symm_apply]
    exact congrArg₂ (· + ·) ha' hd'
  · funext i
    have h := hbase_at i
    dsimp only [rho0, Equiv.trans_apply] at h
    simp only [Equiv.symm_apply_apply] at h
    simpa only [Function.comp_apply, intExponent, transportedCocharge_apply_labelEquiv,
      pi, Equiv.trans_apply, e, Equiv.apply_symm_apply] using h.symm

theorem boosted_supported_norm_tie_data (S T : StandardYoungTableau mu)
    {m : ℕ} (hm : m ≤ mu.card) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m)
    (beta : Fin mu.card →₀ ℕ)
    (hbeta : (higherSpechtPolynomial (R := R) S T *
      elementaryMultiplier mu.card m eta.rowLen).coeff beta ≠ 0)
    (hnorm : squareNorm (intExponent beta) =
      squareNorm (intExponent (transportedBoosted S T.toTableau eta))) :
    ∃ (sigma : colSubgroup T.toTableau) (rho : rowSubgroup T.toTableau)
      (pi : Equiv.Perm (Fin mu.card)),
      intExponent beta = (intExponent (transportedBoosted S T.toTableau eta) ∘ pi) ∘ sigma.val.symm ∧
      intExponent (transportedCocharge S T.toTableau) ∘ pi =
        intExponent (transportedCocharge S T.toTableau) ∘ rho.val.symm := by
  obtain ⟨a, delta, ha, hdelta, rfl⟩ := coeff_mul_ne_zero_exists
    (higherSpechtPolynomial S T) (elementaryMultiplier mu.card m eta.rowLen) beta hbeta
  obtain ⟨sigma, rho, rfl⟩ := youngApply_coeff_ne_zero T.toTableau
    (transportedCocharge S T.toTableau) a ha
  obtain ⟨pi, hpi, hbase⟩ := youngExponent_boosted_norm_tie_data S T hm eta heta
    sigma rho delta hdelta hnorm
  exact ⟨sigma, rho, pi, hpi, hbase⟩

/-- The precise initial-column inequality in the norm-extremal layer of
Lemma 4.2. Every index, multiplier and coefficient ring remains arbitrary. -/
theorem lemma_4_2_prefix_bound (S T : StandardYoungTableau mu)
    {m : ℕ} (hm : m ≤ mu.card) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m)
    (beta : Fin mu.card →₀ ℕ)
    (hbeta : (higherSpechtPolynomial (R := R) S T *
      elementaryMultiplier mu.card m eta.rowLen).coeff beta ≠ 0)
    (hnorm : squareNorm (intExponent beta) =
      squareNorm (intExponent (transportedBoosted S T.toTableau eta))) (k : ℕ) :
    columnPrefix (colIndex T.toTableau) (intExponent (transportedBoosted S T.toTableau eta)) k ≤
      columnPrefix (colIndex T.toTableau) (intExponent beta) k := by
  obtain ⟨sigma, rho, pi, hbeta', hbase⟩ :=
    boosted_supported_norm_tie_data S T hm eta heta beta hbeta hnorm
  rw [hbeta', columnPrefix_comp_perm _ _ sigma.val.symm
    (mem_colSubgroup.mp ((colSubgroup T.toTableau).inv_mem sigma.property))]
  exact boosted_prefix_le (rowIndex T.toTableau) (colIndex T.toTableau)
    (intExponent (transportedCocharge S T.toTableau))
    (intExponent (transportedBoosted S T.toTableau eta))
    (intExponent (transportedBoosted S T.toTableau eta) ∘ pi)
    (colIndex_injective_on_row T.toTableau) (transportedCocharge_rowMonovary S T.toTableau)
    (transportedBoosted_strict_bands S T.toTableau eta)
    (transportedBoosted_cochargeLevelMonovary S T.toTableau eta) pi rho.val.symm
    (mem_rowSubgroup.mp ((rowSubgroup T.toTableau).inv_mem rho.property)) rfl hbase k

theorem lemma_4_2_weight_equality_column_orbit (S T : StandardYoungTableau mu)
    {m : ℕ} (hm : m ≤ mu.card) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m)
    (beta : Fin mu.card →₀ ℕ)
    (hbeta : (higherSpechtPolynomial (R := R) S T *
      elementaryMultiplier mu.card m eta.rowLen).coeff beta ≠ 0)
    (hnorm : squareNorm (intExponent beta) =
      squareNorm (intExponent (transportedBoosted S T.toTableau eta)))
    (hweight : columnWeight (fun i => colIndex T.toTableau i) (intExponent beta) =
      columnWeight (fun i => colIndex T.toTableau i)
        (intExponent (transportedBoosted S T.toTableau eta))) :
    ∃ sigma : Equiv.Perm (Fin mu.card),
      (fun i => (colIndex T.toTableau (sigma i) : ℤ)) = (fun i => (colIndex T.toTableau i : ℤ)) ∧
      intExponent beta = intExponent (transportedBoosted S T.toTableau eta) ∘ sigma := by
  obtain ⟨sigma, rho, pi, hbeta', hbase⟩ :=
    boosted_supported_norm_tie_data S T hm eta heta beta hbeta hnorm
  have hcol : (fun i => (colIndex T.toTableau i : ℤ)) ∘ sigma.val.symm =
      fun i => (colIndex T.toTableau i : ℤ) := by
    funext i
    change (colIndex T.toTableau (sigma.val.symm i) : ℤ) =
      (colIndex T.toTableau i : ℤ)
    exact_mod_cast mem_colSubgroup.mp ((colSubgroup T.toTableau).inv_mem sigma.property) i
  rw [hbeta', columnWeight_comp_perm _ _ sigma.val.symm hcol] at hweight
  have hgamma := (boosted_columnWeight_eq_iff (rowIndex T.toTableau)
    (fun i => (colIndex T.toTableau i : ℤ))
    (intExponent (transportedCocharge S T.toTableau))
    (intExponent (transportedBoosted S T.toTableau eta))
    (intExponent (transportedBoosted S T.toTableau eta) ∘ pi)
    (colIndex_injective_on_row T.toTableau) (colIndex_injective_on_cocharge S T.toTableau)
    (transportedCocharge_rowMonovary S T.toTableau)
    (transportedBoosted_strict_bands S T.toTableau eta)
    (transportedBoosted_cochargeLevelMonovary S T.toTableau eta) pi rho.val.symm
    (mem_rowSubgroup.mp ((rowSubgroup T.toTableau).inv_mem rho.property)) rfl hbase).mp hweight
  exact ⟨sigma.val.symm, hcol, hbeta'.trans (congrArg (fun f => f ∘ sigma.val.symm) hgamma)⟩

theorem boosted_higherSpecht_triangularSupport (S T : StandardYoungTableau mu)
    {m : ℕ} (hm : m ≤ mu.card) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m) :
    TriangularSupport (fun i => colIndex T.toTableau i) (transportedBoosted S T.toTableau eta)
      (higherSpechtPolynomial (R := R) S T * elementaryMultiplier mu.card m eta.rowLen) := by
  constructor
  · exact fun beta hbeta => lemma_4_2_norm_bound S T hm eta heta beta hbeta
  · intro beta hbeta hnorm
    obtain ⟨sigma, rho, pi, hbeta', hbase⟩ :=
      boosted_supported_norm_tie_data S T hm eta heta beta hbeta hnorm
    have hcol : (fun i => (colIndex T.toTableau i : ℤ)) ∘ sigma.val.symm =
        fun i => (colIndex T.toTableau i : ℤ) := by
      funext i
      change (colIndex T.toTableau (sigma.val.symm i) : ℤ) =
        (colIndex T.toTableau i : ℤ)
      exact_mod_cast mem_colSubgroup.mp ((colSubgroup T.toTableau).inv_mem sigma.property) i
    rw [hbeta', columnWeight_comp_perm _ _ sigma.val.symm hcol]
    exact boosted_monotone_columnWeight_le (rowIndex T.toTableau)
      (fun i => (colIndex T.toTableau i : ℤ))
      (intExponent (transportedCocharge S T.toTableau))
      (intExponent (transportedBoosted S T.toTableau eta))
      (intExponent (transportedBoosted S T.toTableau eta) ∘ pi)
      (colIndex_injective_on_row T.toTableau) (transportedCocharge_rowMonovary S T.toTableau)
      (transportedBoosted_strict_bands S T.toTableau eta)
      (transportedBoosted_cochargeLevelMonovary S T.toTableau eta) pi rho.val.symm
      (mem_rowSubgroup.mp ((rowSubgroup T.toTableau).inv_mem rho.property)) rfl hbase id monotone_id
  · exact fun beta hbeta hnorm hweight =>
      lemma_4_2_weight_equality_column_orbit S T hm eta heta beta hbeta hnorm hweight

end HigherSpecht
end
end CanonicalSource2

section CanonicalSource3
/- Source: HigherSpecht/ElementaryDistinguishedCoefficient.lean -/



/-!
# The coefficient one of the nested elementary choice

An extremal boost has exactly one subset choice: each elementary factor takes
the terminal segment of its cardinality.  This proves coefficient one over
every commutative ring, before passing to a field or a quotient.
-/

noncomputable section

open Finset MvPolynomial Function Equiv TauCeti

namespace HigherSpecht

variable {R : Type*} [CommRing R]

def boostExponent (eta : YoungDiagram) (n : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (boostLabel eta n)

theorem elementaryChoiceExponent_upperTails {n m : ℕ} (hm : m ≤ n)
    (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m) :
    elementaryChoiceExponent (fun f : ElementaryFactorIndex m eta =>
      upperTail n (elementaryFactorSize f)) = boostExponent eta n := by
  apply intExponent_injective
  rw [intExponent_elementaryChoiceExponent]
  funext i
  exact subsetMultiplicity_upperTails hm eta heta i

theorem elementaryChoice_eq_upperTails_of_boostExponent {n m : ℕ} (hm : m ≤ n)
    (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m)
    (A : ElementaryFactorIndex m eta → Finset (Fin n))
    (hA : ∀ f, (A f).card = elementaryFactorSize f)
    (hexp : elementaryChoiceExponent A = boostExponent eta n) :
    A = fun f => upperTail n (elementaryFactorSize f) := by
  let B := fun f : ElementaryFactorIndex m eta => upperTail n (elementaryFactorSize f)
  have hcard (f : ElementaryFactorIndex m eta) : (A f).card = (B f).card := by
    rw [hA, upperTail_card (by have := f.1.isLt; dsimp [elementaryFactorSize]; omega)]
  have heq : subsetMultiplicity A = subsetMultiplicity B := by
    rw [← intExponent_elementaryChoiceExponent, ← intExponent_elementaryChoiceExponent,
      hexp, elementaryChoiceExponent_upperTails hm eta heta]
  have hnested := nested_of_subsetMultiplicity_norm_eq A B hcard
    (fun f g => upperTail_nested _ _ _) (congrArg squareNorm heq)
  have hmono : Monotone (subsetMultiplicity A) := by
    rw [heq]
    intro i j hij
    rw [subsetMultiplicity_upperTails hm eta heta, subsetMultiplicity_upperTails hm eta heta]
    exact_mod_cast boostLabel_mono eta n hij
  funext f
  have h := nested_subset_sorted_eq_upperTail A hnested (1 : Equiv.Perm (Fin n)) hmono f
  simpa only [Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_toEmbedding,
    Finset.map_refl, hA] using h

theorem elementaryMultiplier_boostCoefficient {n m : ℕ} (hm : m ≤ n)
    (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m) :
    (elementaryMultiplier (R := R) n m eta.rowLen).coeff (boostExponent eta n) = 1 := by
  rw [elementaryMultiplier_eq_factorProduct, elementary_product_eq_sum_choices,
    MvPolynomial.coeff_sum]
  let B := fun f : ElementaryFactorIndex m eta => upperTail n (elementaryFactorSize f)
  have hB : B ∈ elementaryChoiceSet elementaryFactorSize := by
    apply (mem_elementaryChoiceSet _ _).mpr
    intro f
    exact upperTail_card (by have := f.1.isLt; dsimp [elementaryFactorSize]; omega)
  rw [Finset.sum_eq_single B]
  · rw [elementaryChoiceExponent_upperTails hm eta heta, MvPolynomial.coeff_monomial]
    simp only [if_true]
  · intro A hA hne
    rw [MvPolynomial.coeff_monomial]
    apply if_neg
    intro heq
    exact hne (elementaryChoice_eq_upperTails_of_boostExponent hm eta heta A
      ((mem_elementaryChoiceSet _ _).mp hA) heq)
  · exact fun hnot => (hnot hB).elim

theorem transportedBoosted_sub_cocharge {mu : YoungDiagram}
    (S : StandardYoungTableau mu) (T : YoungTableau mu) (eta : YoungDiagram) :
    transportedBoosted S T eta - transportedCocharge S T =
      permutedExponent (boostExponent eta mu.card) (tableauLabelEquiv S T) := by
  ext i
  simp only [Finsupp.tsub_apply, transportedBoosted_apply_labelEquiv,
    transportedCocharge_apply_labelEquiv, boostedLabel, Nat.add_sub_cancel_left,
    permutedExponent_apply, boostExponent, Finsupp.equivFunOnFinite_symm_apply_apply]

theorem elementaryMultiplier_transportedBoostCoefficient {mu : YoungDiagram}
    (S : StandardYoungTableau mu) (T : YoungTableau mu)
    {m : ℕ} (hm : m ≤ mu.card) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m) :
    (elementaryMultiplier (R := R) mu.card m eta.rowLen).coeff
      (transportedBoosted S T eta - transportedCocharge S T) = 1 := by
  rw [transportedBoosted_sub_cocharge, elementaryMultiplier_coeff_permuted]
  exact elementaryMultiplier_boostCoefficient hm eta heta

end HigherSpecht
end
end CanonicalSource3

section CanonicalSource4
/- Source: HigherSpecht/BoostedDistinguishedCoefficient.lean -/



/-!
# The exact diagonal coefficient of the boosted polynomial

At its distinguished exponent, every surviving Young-operator summand has
the original cocharge exponent.  The elementary multiplier has coefficient
one at the required difference.  The distinguished coefficient therefore
remains exactly the row stabilizer order, over every coefficient ring.
-/

noncomputable section

open Finset MvPolynomial Function Equiv TauCeti TauCeti.YoungTableau

namespace HigherSpecht

variable {R : Type*} [CommRing R] {mu : YoungDiagram}

theorem cocharge_eq_of_boost_eq (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (eta : YoungDiagram) (i j : Fin mu.card)
    (hb : intExponent (transportedBoosted S T eta) i =
      intExponent (transportedBoosted S T eta) j) :
    intExponent (transportedCocharge S T) i = intExponent (transportedCocharge S T) j := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · exact (ne_of_lt (transportedBoosted_strict_bands S T eta i j h)) hb
  · exact (ne_of_lt (transportedBoosted_strict_bands S T eta j i h)) hb.symm

theorem transportedBoosted_columnDistinct (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (eta : YoungDiagram) (j : ℕ) :
    Function.Injective (fun i : {i // colIndex T i = j} => transportedBoosted S T eta i) := by
  intro i l hil
  have hcc := cocharge_eq_of_boost_eq S T eta i.val l.val
    (congrArg (fun a : ℕ => (a : ℤ)) hil)
  exact transportedCocharge_columnDistinct S T j (Int.ofNat_inj.mp hcc)

theorem youngExponent_eq_base_of_boosted_sum (S T : StandardYoungTableau mu)
    {m : ℕ} (hm : m ≤ mu.card) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m)
    (sigma : colSubgroup T.toTableau) (rho : rowSubgroup T.toTableau)
    (delta : Fin mu.card →₀ ℕ)
    (hdelta : (elementaryMultiplier (R := R) mu.card m eta.rowLen).coeff delta ≠ 0)
    (hexp : youngExponent T.toTableau (transportedCocharge S T.toTableau) sigma rho + delta =
      transportedBoosted S T.toTableau eta) :
    youngExponent T.toTableau (transportedCocharge S T.toTableau) sigma rho =
      transportedCocharge S T.toTableau := by
  obtain ⟨pi, hpi, hbase⟩ := youngExponent_boosted_norm_tie_data S T hm eta heta sigma rho
    delta hdelta (by rw [hexp])
  rw [hexp] at hpi
  have hcol : (fun i => (colIndex T.toTableau i : ℤ)) ∘ sigma.val.symm =
      fun i => (colIndex T.toTableau i : ℤ) := by
    funext i
    simpa only [Function.comp_apply, Subgroup.coe_inv, Equiv.Perm.inv_def] using
      congrArg (fun a : ℕ => (a : ℤ))
        (mem_colSubgroup.mp ((colSubgroup T.toTableau).inv_mem sigma.property) i)
  have hweight : columnWeight (fun i => colIndex T.toTableau i)
      (intExponent (transportedBoosted S T.toTableau eta) ∘ pi) =
      columnWeight (fun i => colIndex T.toTableau i)
        (intExponent (transportedBoosted S T.toTableau eta)) := by
    have h := congrArg (columnWeight (fun i => (colIndex T.toTableau i : ℤ))) hpi
    rw [columnWeight_comp_perm _ _ sigma.val.symm hcol] at h
    exact h.symm
  have hfix := (boosted_columnWeight_eq_iff (rowIndex T.toTableau)
    (fun i => (colIndex T.toTableau i : ℤ))
    (intExponent (transportedCocharge S T.toTableau))
    (intExponent (transportedBoosted S T.toTableau eta))
    (intExponent (transportedBoosted S T.toTableau eta) ∘ pi)
    (colIndex_injective_on_row T.toTableau) (colIndex_injective_on_cocharge S T.toTableau)
    (transportedCocharge_rowMonovary S T.toTableau)
    (transportedBoosted_strict_bands S T.toTableau eta)
    (transportedBoosted_cochargeLevelMonovary S T.toTableau eta) pi rho.val.symm
    (mem_rowSubgroup.mp ((rowSubgroup T.toTableau).inv_mem rho.property)) rfl hbase).mp hweight
  have hfixa : intExponent (transportedCocharge S T.toTableau) ∘ pi =
      intExponent (transportedCocharge S T.toTableau) := by
    funext i
    exact cocharge_eq_of_boost_eq S T.toTableau eta (pi i) i (congrFun hfix i)
  have hsigma : sigma = 1 := by
    rw [hfix] at hpi
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have hi : sigma.val.symm i = i := by
      have hp := congrFun hpi i
      have hnat : transportedBoosted S T.toTableau eta (sigma.val.symm i) =
          transportedBoosted S T.toTableau eta i := Int.ofNat_inj.mp hp.symm
      have h := transportedBoosted_columnDistinct S T.toTableau eta (colIndex T.toTableau i)
        (a₁ := ⟨sigma.val.symm i, mem_colSubgroup.mp
          ((colSubgroup T.toTableau).inv_mem sigma.property) i⟩) (a₂ := ⟨i, rfl⟩) hnat
      exact congrArg Subtype.val h
    have h := congrArg sigma.val hi
    simpa only [Equiv.apply_symm_apply, Subgroup.coe_one, Equiv.Perm.one_apply] using h.symm
  apply intExponent_injective
  simp only [hsigma, youngExponent, Subgroup.coe_one, inv_one,
    permutedExponent_one, intExponent_permuted]
  exact hbase.symm.trans hfixa

theorem boosted_coefficient_convolution_unique (S T : StandardYoungTableau mu)
    {m : ℕ} (hm : m ≤ mu.card) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m)
    (a delta : Fin mu.card →₀ ℕ)
    (ha : (higherSpechtPolynomial (R := R) S T).coeff a ≠ 0)
    (hd : (elementaryMultiplier (R := R) mu.card m eta.rowLen).coeff delta ≠ 0)
    (hexp : a + delta = transportedBoosted S T.toTableau eta) :
    a = transportedCocharge S T.toTableau ∧
      delta = transportedBoosted S T.toTableau eta - transportedCocharge S T.toTableau := by
  obtain ⟨sigma, rho, rfl⟩ := youngApply_coeff_ne_zero T.toTableau _ a ha
  have hbase := youngExponent_eq_base_of_boosted_sum S T hm eta heta sigma rho delta hd hexp
  refine ⟨hbase, ?_⟩
  rw [hbase] at hexp
  ext i
  have hi := congrArg (fun e : Fin mu.card →₀ ℕ => e i) hexp
  simp only [Finsupp.add_apply, Finsupp.tsub_apply] at hi ⊢
  omega

/-- The full distinguished-coefficient assertion of Lemma 4.2, including its
integer value and every multiplier in the prescribed range. -/
theorem lemma_4_2_distinguishedCoefficient (S T : StandardYoungTableau mu)
    {m : ℕ} (hm : m ≤ mu.card) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m) :
    (higherSpechtPolynomial (R := R) S T * elementaryMultiplier mu.card m eta.rowLen).coeff
      (transportedBoosted S T.toTableau eta) =
      ((rowFillingStabilizers T.toTableau (transportedCocharge S T.toTableau)).card : R) := by
  let a := transportedCocharge S T.toTableau
  let b := transportedBoosted S T.toTableau eta
  have hab : a ≤ b := by
    intro i
    change cochargeLabel S (tableauLabelEquiv S T.toTableau i) ≤
      cochargeLabel S (tableauLabelEquiv S T.toTableau i) + _
    exact Nat.le_add_right _ _
  rw [MvPolynomial.coeff_mul, Finset.sum_eq_single (a, b - a)]
  · rw [elementaryMultiplier_transportedBoostCoefficient S T.toTableau hm eta heta,
      mul_one, higherSpecht_distinguishedCoefficient]
  · intro z hz hne
    by_contra hn
    have hexp := Finset.mem_antidiagonal.mp hz
    obtain ⟨ha, hd⟩ := boosted_coefficient_convolution_unique S T hm eta heta z.1 z.2
      (left_ne_zero_of_mul hn) (right_ne_zero_of_mul hn) hexp
    exact hne (Prod.ext ha hd)
  · intro hnot
    apply (hnot ?_).elim
    apply Finset.mem_antidiagonal.mpr
    exact add_tsub_cancel_of_le hab

end HigherSpecht
end
end CanonicalSource4

section CanonicalSource5
/- Source: HigherSpecht/GriffinWitness.lean -/



/-!
# The actual extended apolar witness for a Griffin index

The first k labels receive no boost.  Their column-insertion witness is embedded
into the ambient variables, and every other variable receives exponent s−1.
Eligibility and the proved row/column-reading correspondence give the actual
harmonic membership in the defining Griffin ideal.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset TauCeti TauCeti.YoungTableau Equiv Function MvPolynomial

namespace HigherSpecht

variable {μ : YoungDiagram}

 theorem colLen_zero_le_of_dominates_eq_card {lam nu : YoungDiagram}
    (hcard : lam.card = nu.card) (hdom : Dominates nu lam) : nu.colLen 0 ≤ lam.colLen 0 := by
  have hsum := hdom (lam.colLen 0)
  rw [← YoungDiagram.card_eq_sum_range_rowLen lam le_rfl, hcard,
    YoungDiagram.sum_range_rowLen_eq_card_filter_fst] at hsum
  have hfilter : (nu.cells.filter fun c => c.1 < lam.colLen 0) = nu.cells :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hsum
  by_contra hn
  have hc : (lam.colLen 0, 0) ∈ nu.cells :=
    YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_not_ge hn)
  have hf : (lam.colLen 0, 0) ∈ nu.cells.filter (fun c => c.1 < lam.colLen 0) := by
    rwa [hfilter]
  exact (lt_irrefl _) (Finset.mem_filter.mp hf).2

def prefixAmbientEmbedding (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) : Fin (prefixShape S k).card ↪ Fin μ.card :=
  (prefixTableau S k hk).toTableau.symm.toEmbedding.trans
    ((prefixCellsEmbedding S k).trans T.toEmbedding)

 theorem prefixAmbientEmbedding_column (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) (i : Fin (prefixShape S k).card) :
    colIndex T (prefixAmbientEmbedding S T k hk i) =
      colIndex (prefixTableau S k hk).toTableau i := by
  simp only [prefixAmbientEmbedding, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
    colIndex_apply, colIndex_def, Equiv.symm_apply_apply, prefixCellsEmbedding_val]

 theorem prefixAmbientEmbedding_boost (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ μ.card)
    (hlen : eta.colLen 0 ≤ μ.card - k) (i : Fin (prefixShape S k).card) :
    transportedBoosted S T eta (prefixAmbientEmbedding S T k hk i) =
      transportedCocharge (prefixTableau S k hk) (prefixTableau S k hk).toTableau i := by
  simp only [transportedBoosted, transportedCocharge, Finsupp.equivFunOnFinite_symm_apply_apply,
    prefixAmbientEmbedding, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
    Equiv.symm_apply_apply]
  exact boostedFilling_prefix S eta k hk hlen _

def griffinWitnessAlpha (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) : Fin μ.card →₀ ℕ :=
  embeddedWitnessAlpha (prefixAmbientEmbedding S T k hk)
    (insertionAlpha (prefixTableau S k hk) (prefixTableau S k hk).toTableau) s

def griffinWitnessRejection (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) : Fin μ.card →₀ ℕ :=
  griffinWitnessAlpha S T k hk s - transportedBoosted S T eta

def griffinWitnessGroup (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  embeddedPermutationGroup (prefixAmbientEmbedding S T k hk)
    (insertionColumnGroup (prefixTableau S k hk) (prefixTableau S k hk).toTableau)

def griffinWitnessColumn (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) :=
  embeddedColumn (prefixAmbientEmbedding S T k hk)
    (insertionColumn (prefixTableau S k hk) (prefixTableau S k hk).toTableau)

def griffinWitnessTiedColumn (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) :=
  embeddedColumn (prefixAmbientEmbedding S T k hk)
    (fun i => (insertionColumn (prefixTableau S k hk) (prefixTableau S k hk).toTableau i,
      insertionRejections (prefixTableau S k hk) (prefixTableau S k hk).toTableau i))

variable {R : Type*} [CommRing R]

def griffinApolarWitness (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) : PolynomialRing μ.card R :=
  columnWitness (((insertionFilling (prefixTableau S k hk)
    (prefixTableau S k hk).toTableau).toEmbedding).trans (prefixAmbientEmbedding S T k hk)) s

 theorem griffinApolarWitness_eq_coefficientWitness (S : StandardYoungTableau μ)
    (T : YoungTableau μ) (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) :
    griffinApolarWitness (R := R) S T k hk s =
      coefficientWitness (griffinWitnessGroup S T k hk) (griffinWitnessAlpha S T k hk s) := by
  symm
  exact coefficientWitness_partialFilling
    (insertionFilling (prefixTableau S k hk) (prefixTableau S k hk).toTableau)
    (prefixAmbientEmbedding S T k hk) s

 theorem griffinWitness_rearrangement (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ μ.card) (s : ℕ)
    (hlen : eta.colLen 0 ≤ μ.card - k) (hdes : descentNumber S < s)
    (hwidth : eta.rowLen 0 ≤ s - descentNumber S - 1) :
    RearrangementWitness (griffinWitnessColumn S T k hk) (griffinWitnessTiedColumn S T k hk)
      (intExponent (griffinWitnessAlpha S T k hk s))
      (intExponent (griffinWitnessRejection S T eta k hk s))
      (intExponent (transportedBoosted S T eta)) (fun i => (colIndex T i : ℤ)) := by
  apply embeddedWitness_geometry
    (insertion_rearrangementWitness (prefixTableau S k hk) (prefixTableau S k hk).toTableau)
  · exact prefixAmbientEmbedding_boost S T eta k hk hlen
  · intro i
    exact congrArg Int.ofNat (prefixAmbientEmbedding_column S T k hk i)
  · intro i hi
    exact Nat.le_pred_of_lt (boostedLabel_lt_bound S eta hdes hwidth (S (T.symm i)))

 theorem griffinWitnessGroup_preserves (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) (τ : griffinWitnessGroup S T k hk) (i : Fin μ.card) :
    griffinWitnessColumn S T k hk (τ.val i) = griffinWitnessColumn S T k hk i :=
  embeddedPermutationGroup_preserves
    (e := prefixAmbientEmbedding S T k hk)
    (u := insertionColumn (prefixTableau S k hk) (prefixTableau S k hk).toTableau)
    (G := insertionColumnGroup (prefixTableau S k hk) (prefixTableau S k hk).toTableau)
    (fun σ j => σ.property j) τ i

 theorem griffinApolarWitness_mem_harmonics (S : StandardYoungTableau μ)
    (T : YoungTableau μ) (lam : YoungDiagram) (hk : lam.card ≤ μ.card) (s : ℕ)
    (hs : lam.colLen 0 ≤ s) (hs0 : 0 < s)
    (he : CatDominates (prefixTableau S lam.card hk) lam) :
    griffinApolarWitness (R := R) S T lam.card hk s ∈
      dividedHarmonics (griffinIdeal R μ.card lam s) := by
  let nu := (columnInsertion (prefixTableau S lam.card hk)).state.shape
  have hnu : nu.card = lam.card := prefixInsertionFilling_card S _ hk
  have hdom : Dominates nu lam := prefixInsertionFilling_dominates S _ hk lam he
  have hheight : nu.colLen 0 ≤ s :=
    (colLen_zero_le_of_dominates_eq_card hnu.symm hdom).trans hs
  apply dividedHarmonics_antitone (griffinIdeal_le_of_dominates hk (by simpa only [hnu] using hk) hdom)
  exact columnWitness_mem_griffinHarmonics _ hs0 hheight

def griffinCoefficientFunctional (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) :
    Module.Dual R (PolynomialRing μ.card R) :=
  contractionCoefficient (griffinApolarWitness S T k hk s)
    (griffinWitnessRejection S T eta k hk s)

 theorem griffinCoefficientFunctional_eq (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) :
    griffinCoefficientFunctional (R := R) S T eta k hk s =
      witnessCoefficient (griffinWitnessGroup S T k hk) (griffinWitnessAlpha S T k hk s)
        (griffinWitnessRejection S T eta k hk s) := by
  rw [griffinCoefficientFunctional, griffinApolarWitness_eq_coefficientWitness]
  rfl

 theorem griffinCoefficientFunctional_kills_ideal (S : StandardYoungTableau μ)
    (T : YoungTableau μ) (eta lam : YoungDiagram) (hk : lam.card ≤ μ.card) (s : ℕ)
    (hs : lam.colLen 0 ≤ s) (hs0 : 0 < s)
    (he : CatDominates (prefixTableau S lam.card hk) lam) :
    (griffinIdeal R μ.card lam s).restrictScalars R ≤
      LinearMap.ker (griffinCoefficientFunctional S T eta lam.card hk s) :=
  contractionCoefficient_kills_ideal (griffinApolarWitness_mem_harmonics S T lam hk s hs hs0 he) _

end HigherSpecht
end
end CanonicalSource5

section CanonicalSource6
/- Source: HigherSpecht/GriffinFixedTableau.lean -/



/-!
# Griffin independence for a fixed right tableau

The index type retains the actual prefix-catabolism, descent, and rectangle
conditions.  Every functional kills the actual defining ideal.  Norm/prefix
triangularity and the exact positive diagonal then prove independence in the
quotient.  This is the fixed-tableau part of Theorem 4.1; the complete-copy
promotion and the independent dimension count are separate subsequent steps.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset TauCeti TauCeti.YoungTableau Function MvPolynomial

namespace HigherSpecht

variable {μ lam : YoungDiagram} {hk : lam.card ≤ μ.card} {s : ℕ}

structure FixedGriffinIndex (μ lam : YoungDiagram) (hk : lam.card ≤ μ.card) (s : ℕ) where
  left : StandardYoungTableau μ
  multiplier : YoungDiagram
  eligible : CatDominates (prefixTableau left lam.card hk) lam
  descents_lt : descentNumber left < s
  multiplier_length : multiplier.colLen 0 ≤ μ.card - lam.card
  multiplier_width : multiplier.rowLen 0 ≤ s - descentNumber left - 1

 theorem fixedGriffinIndex_ext {i j : FixedGriffinIndex μ lam hk s}
    (hleft : i.left = j.left) (heta : i.multiplier = j.multiplier) : i = j := by
  cases i
  cases j
  cases hleft
  cases heta
  rfl

def FixedGriffinIndex.toGriffin (T : StandardYoungTableau μ)
    (i : FixedGriffinIndex μ lam hk s) : GriffinIndex μ.card lam hk s where
  pair := ⟨μ, rfl, i.left, T⟩
  multiplier := i.multiplier
  eligible := i.eligible
  descents_lt := i.descents_lt
  multiplier_length := i.multiplier_length
  multiplier_width := i.multiplier_width

 instance finiteFixedGriffinIndex (μ lam : YoungDiagram) (hk : lam.card ≤ μ.card) (s : ℕ) :
    Finite (FixedGriffinIndex μ lam hk s) := by
  apply Finite.of_injective (FixedGriffinIndex.toGriffin (StandardYoungTableau.rowSuperstandard μ))
  intro i j h
  apply fixedGriffinIndex_ext
  · have hp := congrArg (fun x : GriffinIndex μ.card lam hk s => x.pair) h
    cases i
    cases j
    cases hp
    rfl
  · exact congrArg (fun x : GriffinIndex μ.card lam hk s => x.multiplier) h

 noncomputable instance fintypeFixedGriffinIndex (μ lam : YoungDiagram)
    (hk : lam.card ≤ μ.card) (s : ℕ) : Fintype (FixedGriffinIndex μ lam hk s) := Fintype.ofFinite _

variable {R : Type*} [CommRing R]

def fixedGriffinPolynomial (T : StandardYoungTableau μ) (i : FixedGriffinIndex μ lam hk s) :
    PolynomialRing μ.card R :=
  higherSpechtPolynomial i.left T * elementaryMultiplier μ.card (μ.card - lam.card) i.multiplier.rowLen

def fixedGriffinFunctional (T : StandardYoungTableau μ) (i : FixedGriffinIndex μ lam hk s) :
    Module.Dual R (PolynomialRing μ.card R) :=
  griffinCoefficientFunctional i.left T.toTableau i.multiplier lam.card hk s

def fixedGriffinKey (T : StandardYoungTableau μ) (i : FixedGriffinIndex μ lam hk s) : ℤ ×ₗ ℤ :=
  normWeightKey (fun j => (colIndex T.toTableau j : ℤ))
    (intExponent (transportedBoosted i.left T.toTableau i.multiplier))

 theorem fixedGriffinBoost_injective (T : StandardYoungTableau μ) :
    Function.Injective (fun i : FixedGriffinIndex μ lam hk s =>
      transportedBoosted i.left T.toTableau i.multiplier) := by
  intro i j h
  have hfill : boostedFilling i.left i.multiplier = boostedFilling j.left j.multiplier := by
    funext c
    have hc := congrArg (fun b : Fin μ.card →₀ ℕ => b (T.toTableau c)) h
    simpa only [transportedBoosted, Finsupp.equivFunOnFinite_symm_apply_apply,
      Equiv.symm_apply_apply] using hc
  have hs := tableau_eq_of_boostedFilling_eq i.left j.left i.multiplier j.multiplier hfill
  apply fixedGriffinIndex_ext hs
  apply partition_eq_of_boostedFilling_eq i.left
    (i.multiplier_length.trans (Nat.sub_le _ _))
    (j.multiplier_length.trans (Nat.sub_le _ _))
  simpa only [hs] using hfill

 theorem transportedBoosted_intColumnMonovary (S : StandardYoungTableau μ)
    (T : YoungTableau μ) (eta : YoungDiagram) (j : ℤ) :
    Monovary (fun i : {i // (colIndex T i : ℤ) = j} => (rowIndex T i : ℤ))
      (fun i : {i // (colIndex T i : ℤ) = j} => intExponent (transportedBoosted S T eta) i) := by
  apply Monovary.symm
  intro i l hil
  change (rowIndex T i : ℤ) < (rowIndex T l : ℤ) at hil
  have hrow : rowIndex T i < rowIndex T l := Int.ofNat_lt.mp hil
  have hcol : colIndex T i = colIndex T l :=
    Int.ofNat_inj.mp (i.property.trans l.property.symm)
  have hc : (T.symm i).val.2 = (T.symm l).val.2 := by
    simpa only [← colIndex_def] using hcol
  have hr : (T.symm i).val.1 < (T.symm l).val.1 := by
    simpa only [← rowIndex_def] using hrow
  change (boostedFilling S eta (T.symm i) : ℤ) ≤ (boostedFilling S eta (T.symm l) : ℤ)
  exact Int.ofNat_le.mpr (boostedFilling_col_strict S eta hc hr).le

 theorem boostedPolynomial_columnAlternating (S T : StandardYoungTableau μ)
    (m : ℕ) (eta : YoungDiagram) (τ : Equiv.Perm (Fin μ.card))
    (hτ : ∀ i, colIndex T.toTableau (τ i) = colIndex T.toTableau i) :
    MvPolynomial.rename τ (higherSpechtPolynomial (R := R) S T *
      elementaryMultiplier μ.card m eta.rowLen) =
      coefficientSign (R := R) τ •
        (higherSpechtPolynomial S T * elementaryMultiplier μ.card m eta.rowLen) := by
  rw [map_mul, elementaryMultiplier_isSymmetric, higherSpechtPolynomial,
    youngApply_columnAlternating T.toTableau _ ⟨τ, mem_colSubgroup.mpr hτ⟩,
    smul_mul_assoc]

 theorem fixedGriffinFunctional_offDiagonal (T : StandardYoungTableau μ)
    (i j : FixedGriffinIndex μ lam hk s) (hne : i ≠ j)
    (hkey : fixedGriffinKey T j ≤ fixedGriffinKey T i) :
    fixedGriffinFunctional (R := R) T i (fixedGriffinPolynomial T j) = 0 := by
  rw [fixedGriffinFunctional, griffinCoefficientFunctional_eq]
  apply witnessCoefficient_eq_zero_of_key_finiteRange
    (row := fun i => (rowIndex T.toTableau i : ℤ))
    (griffinWitness_rearrangement i.left T.toTableau i.multiplier lam.card hk s
      i.multiplier_length i.descents_lt i.multiplier_width)
    (griffinWitnessGroup i.left T.toTableau lam.card hk)
    (griffinWitnessGroup_preserves i.left T.toTableau lam.card hk)
    (fixedGriffinPolynomial T j)
    (boosted_higherSpecht_triangularSupport j.left T (Nat.sub_le _ _) j.multiplier j.multiplier_length)
    hkey (fun h => hne (fixedGriffinBoost_injective T h))
    (rowIndex_injective_on_intColumn T.toTableau)
    (transportedBoosted_intColumnMonovary i.left T.toTableau i.multiplier)
    (transportedBoosted_intColumnMonovary j.left T.toTableau j.multiplier)

 theorem fixedGriffinFunctional_diagonal (T : StandardYoungTableau μ)
    (i : FixedGriffinIndex μ lam hk s) :
    fixedGriffinFunctional (R := R) T i (fixedGriffinPolynomial T i) =
      ((rowFillingStabilizers T.toTableau (transportedCocharge i.left T.toTableau)).card : R) *
      ((fixedWitnessPermutations (griffinWitnessGroup i.left T.toTableau lam.card hk)
        (griffinWitnessRejection i.left T.toTableau i.multiplier lam.card hk s)
        (fun j => (colIndex T.toTableau j : ℤ))).card : R) := by
  rw [fixedGriffinFunctional, griffinCoefficientFunctional_eq]
  rw [witnessCoefficient_diagonal_finiteRange
    (griffinWitness_rearrangement i.left T.toTableau i.multiplier lam.card hk s
      i.multiplier_length i.descents_lt i.multiplier_width)
    (griffinWitnessGroup i.left T.toTableau lam.card hk)
    (griffinWitnessGroup_preserves i.left T.toTableau lam.card hk)
    (fixedGriffinPolynomial T i)
    (boosted_higherSpecht_triangularSupport i.left T (Nat.sub_le _ _) i.multiplier i.multiplier_length)]
  · rw [fixedGriffinPolynomial, lemma_4_2_distinguishedCoefficient i.left T
      (Nat.sub_le _ _) i.multiplier i.multiplier_length]
  · intro τ hτ
    rw [← coeff_rename_perm, fixedGriffinPolynomial,
      boostedPolynomial_columnAlternating i.left T _ i.multiplier τ
        (fun j => Int.ofNat_inj.mp (congrFun hτ j)), MvPolynomial.coeff_smul, smul_eq_mul]

 theorem fixedGriffinFunctional_kills (T : StandardYoungTableau μ)
    (hs : lam.colLen 0 ≤ s) (i : FixedGriffinIndex μ lam hk s) :
    (griffinIdeal R μ.card lam s).restrictScalars R ≤ LinearMap.ker (fixedGriffinFunctional T i) :=
  griffinCoefficientFunctional_kills_ideal i.left T.toTableau i.multiplier lam hk s hs
    ((Nat.zero_le _).trans_lt i.descents_lt) i.eligible

/-- The complete fixed-right-tableau assertion in the actual Griffin quotient.
No matching-dimension or shape-correspondence premise appears here. -/
 theorem griffin_fixedTableau_linearIndependent {K : Type*} [Field K] [CharZero K]
    (T : StandardYoungTableau μ) (hs : lam.colLen 0 ≤ s) :
    LinearIndependent K (fun i : FixedGriffinIndex μ lam hk s =>
      Ideal.Quotient.mk (griffinIdeal K μ.card lam s) (fixedGriffinPolynomial T i)) := by
  let N := (griffinIdeal K μ.card lam s).restrictScalars K
  let L : FixedGriffinIndex μ lam hk s → Module.Dual K (GriffinRing K μ.card lam s) :=
    fun i => N.liftQ (fixedGriffinFunctional T i) (fixedGriffinFunctional_kills T hs i)
  apply linearIndependent_of_pairing_key (fixedGriffinKey T) L
  · intro i j hne hkey
    exact fixedGriffinFunctional_offDiagonal T i j hne hkey
  · intro i
    change fixedGriffinFunctional (R := K) T i (fixedGriffinPolynomial T i) ≠ 0
    rw [fixedGriffinFunctional_diagonal]
    apply mul_ne_zero
    · exact_mod_cast (Finset.card_pos.mpr
        (rowFillingStabilizers_nonempty T.toTableau (transportedCocharge i.left T.toTableau))).ne'
    · exact_mod_cast (Finset.card_pos.mpr (fixedWitnessPermutations_nonempty
        (griffinWitnessGroup i.left T.toTableau lam.card hk)
        (griffinWitnessRejection i.left T.toTableau i.multiplier lam.card hk s)
        (fun j => (colIndex T.toTableau j : ℤ)))).ne'

end HigherSpecht
end
end CanonicalSource6

section CanonicalSource7
/- Source: HigherSpecht/GriffinIntertwiners.lean -/



/-!
# Literal Griffin polynomials as maps of complete Specht modules

Multiplication by the actual elementary symmetric multiplier commutes with
permutations.  Projection to the actual Griffin ideal therefore gives an
intertwining map.  Its values on the standard polytabloid basis are the exact
polynomials specified by the manuscript, including the ambient-label cast.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau Module MvPolynomial

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ}

def symmetricMultiplicationIntertwiner (p : PolynomialRing n R) (hp : p.IsSymmetric) :
    (polynomialRepresentation R n).IntertwiningMap (polynomialRepresentation R n) where
  toLinearMap :=
    { toFun := fun q => q * p
      map_add' := fun q r => add_mul q r p
      map_smul' := fun c q => smul_mul_assoc c q p }
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    change MvPolynomial.rename g q * p = MvPolynomial.rename g (q * p)
    rw [map_mul, hp g]

def quotientProjectionIntertwiner (I : Ideal (PolynomialRing n R))
    (hI : PermutationStable I) :
    (polynomialRepresentation R n).IntertwiningMap (quotientRepresentation I hI) where
  toLinearMap := (Ideal.Quotient.mkₐ R I).toLinearMap
  isIntertwining' g := by ext p; rfl

def partitionHigherSpechtIntertwiner (part : n.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    Representation.IntertwiningMap (spechtModule part).ρ (polynomialRepresentation ℚ n) where
  toLinearMap := (MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition part))).toLinearMap ∘ₗ
    (higherSpechtIntertwiner S).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    let e := finCongr (YoungDiagram.card_ofPartition part)
    have h := DFunLike.congr_fun ((higherSpechtIntertwiner S).isIntertwining'
      (e.symm.permCongr g)) v
    change MvPolynomial.rename e
      (higherSpechtIntertwiner S ((spechtModule part).ρ g v)) =
      MvPolynomial.rename g (MvPolynomial.rename e (higherSpechtIntertwiner S v))
    change MvPolynomial.rename e
      (higherSpechtIntertwiner S
        ((spechtSubrepresentation (YoungDiagram.ofPartition part)).toRepresentation
          (e.symm.permCongr g) v)) = _
    rw [show higherSpechtIntertwiner S
        ((spechtSubrepresentation (YoungDiagram.ofPartition part)).toRepresentation
          (e.symm.permCongr g) v) =
        MvPolynomial.rename (e.symm.permCongr g) (higherSpechtIntertwiner S v) from h]
    rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
    congr 1

@[simp] theorem partitionHigherSpechtIntertwiner_standardBasis (part : n.Partition)
    (S T : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    partitionHigherSpechtIntertwiner part S (spechtModuleStandardBasis part T) =
      MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition part))
        (higherSpechtPolynomial S T) := by
  have hT : spechtModuleStandardBasis part T =
      standardPolytabloidBasis (YoungDiagram.ofPartition part) T := by
    apply Subtype.ext
    exact (coe_spechtModuleStandardBasis part T).trans
      (coe_standardPolytabloidBasis (YoungDiagram.ofPartition part) T).symm
  change MvPolynomial.rename (R := ℚ) (finCongr (YoungDiagram.card_ofPartition part))
    (higherSpechtIntertwiner S (spechtModuleStandardBasis part T)) = _
  rw [hT, higherSpechtIntertwiner_standardBasis]

abbrev PartitionGriffinCopies (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (part : n.Partition) :=
  FixedGriffinIndex (YoungDiagram.ofPartition part) lam
    (by simpa only [YoungDiagram.card_ofPartition] using hk) s

def partitionGriffinIntertwiner (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part) :
    Representation.IntertwiningMap (spechtModule part).ρ (griffinRepresentation ℚ n lam s) :=
  (quotientProjectionIntertwiner (griffinIdeal ℚ n lam s) (permutationStable_griffinIdeal lam s)).comp
    ((symmetricMultiplicationIntertwiner
      (elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)
      (elementaryMultiplier_isSymmetric n (n - lam.card) i.multiplier.rowLen)).comp
        (partitionHigherSpechtIntertwiner part i.left))

@[simp] theorem partitionGriffinIntertwiner_standardBasis (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (part : n.Partition)
    (i : PartitionGriffinCopies n lam hk s part)
    (T : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    partitionGriffinIntertwiner lam hk s part i (spechtModuleStandardBasis part T) =
      Ideal.Quotient.mk (griffinIdeal ℚ n lam s)
        (MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition part))
          (higherSpechtPolynomial i.left T) *
        elementaryMultiplier n (n - lam.card) i.multiplier.rowLen) := by
  change Ideal.Quotient.mk (griffinIdeal ℚ n lam s)
    (partitionHigherSpechtIntertwiner part i.left (spechtModuleStandardBasis part T) *
      elementaryMultiplier n (n - lam.card) i.multiplier.rowLen) = _
  rw [partitionHigherSpechtIntertwiner_standardBasis]

 theorem griffinRing_finiteDimensional (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    FiniteDimensional ℚ (GriffinRing ℚ n lam s) := by
  letI := (finite_griffinStaircaseExponents (n := n) (μ := lam) s hs hheight).fintype
  exact Module.Finite.of_basis (griffinStandardMonomialBasis hk s hs hheight)

end HigherSpecht
end
end CanonicalSource7

section CanonicalSource8
/- Source: HigherSpecht/GriffinFullCopies.lean -/



/-!
# Independence of every prescribed Griffin polynomial

The actual fixed-tableau apolar separation detects independent intertwiners.
The verified Young-ideal decomposition promotes this to all right tableaux
and all shapes simultaneously.  The final reindexing returns the literal
`GriffinIndex` from the theorem statement, retaining all eligibility and
rectangle restrictions.  No matching-dimension assertion is used here.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau Module MvPolynomial

namespace HigherSpecht

 theorem griffin_fixedTableau_renamed_linearIndependent
    {mu lam : YoungDiagram} {n s : ℕ} (hn : mu.card = n) (hk : lam.card ≤ n)
    (T : StandardYoungTableau mu) (hheight : lam.colLen 0 ≤ s) :
    LinearIndependent ℚ (fun i : FixedGriffinIndex mu lam (by omega) s =>
      Ideal.Quotient.mk (griffinIdeal ℚ n lam s)
        (MvPolynomial.rename (finCongr hn) (higherSpechtPolynomial i.left T) *
          elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)) := by
  subst n
  simpa only [finCongr_refl, Equiv.coe_refl, MvPolynomial.rename_id_apply,
    fixedGriffinPolynomial] using
    griffin_fixedTableau_linearIndependent (K := ℚ) (hk := hk) T hheight

abbrev PartitionGriffinVectorIndex (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ) :=
  Σ part : n.Partition,
    StandardYoungTableau (YoungDiagram.ofPartition part) ×
      PartitionGriffinCopies n lam hk s part

def partitionGriffinIndex {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n} {s : ℕ}
    (z : PartitionGriffinVectorIndex n lam hk s) : GriffinIndex n lam hk s where
  pair := (standardPairPartitionEquiv n).symm ⟨z.1, z.2.2.left, z.2.1⟩
  multiplier := z.2.2.multiplier
  eligible := z.2.2.eligible
  descents_lt := z.2.2.descents_lt
  multiplier_length := by simpa only [YoungDiagram.card_ofPartition] using z.2.2.multiplier_length
  multiplier_width := z.2.2.multiplier_width

 theorem partitionGriffinIndex_injective (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) :
    Function.Injective (partitionGriffinIndex (n := n) (lam := lam) (hk := hk) (s := s)) := by
  rintro ⟨part, T, i⟩ ⟨other, U, j⟩ h
  have hp := congrArg (fun x : GriffinIndex n lam hk s =>
    standardPairPartitionEquiv n x.pair) h
  simp only [partitionGriffinIndex, Equiv.apply_symm_apply] at hp
  obtain rfl : part = other := (Sigma.mk.inj_iff.mp hp).1
  have hpair : (i.left, T) = (j.left, U) :=
    eq_of_heq (Sigma.mk.inj_iff.mp hp).2
  have hT := congrArg Prod.snd hpair
  have hS := congrArg Prod.fst hpair
  have heta := congrArg (fun x : GriffinIndex n lam hk s => x.multiplier) h
  have hi : i = j := fixedGriffinIndex_ext hS heta
  cases hT
  cases hi
  rfl

 theorem partitionGriffinIndex_surjective (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) :
    Function.Surjective (partitionGriffinIndex (n := n) (lam := lam) (hk := hk) (s := s)) := by
  rintro ⟨P, eta, heligible, hdesc, hlength, hwidth⟩
  obtain ⟨⟨part, S, T⟩, rfl⟩ := (standardPairPartitionEquiv n).symm.surjective P
  let i : PartitionGriffinCopies n lam hk s part :=
    { left := S
      multiplier := eta
      eligible := heligible
      descents_lt := hdesc
      multiplier_length := by simpa only [YoungDiagram.card_ofPartition] using hlength
      multiplier_width := hwidth }
  exact ⟨⟨part, T, i⟩, rfl⟩

def partitionGriffinIndexEquiv (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) :
    PartitionGriffinVectorIndex n lam hk s ≃ GriffinIndex n lam hk s :=
  Equiv.ofBijective partitionGriffinIndex
    ⟨partitionGriffinIndex_injective n lam hk s, partitionGriffinIndex_surjective n lam hk s⟩

@[simp] theorem partitionGriffinIntertwiner_family {n : ℕ} (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (z : PartitionGriffinVectorIndex n lam hk s) :
    partitionGriffinIntertwiner lam hk s z.1 z.2.2 (spechtModuleStandardBasis z.1 z.2.1) =
      griffinFamily ℚ n lam hk s (partitionGriffinIndex z) := by
  rw [partitionGriffinIntertwiner_standardBasis]
  rfl

set_option maxHeartbeats 800000 in
/-- Every prescribed vector of Theorem 4.1 is independent.  The separate
dimension count is still needed to conclude that this family is a basis. -/
 theorem griffinFamily_linearIndependent_rat (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    LinearIndependent ℚ (griffinFamily ℚ n lam hk s) := by
  letI := griffinRing_finiteDimensional lam hk s hs hheight
  let rho := griffinRepresentation ℚ n lam s
  let f : ∀ part : n.Partition,
      PartitionGriffinCopies n lam hk s part →
        (YoungIdealRepresentation (K := ℚ) part).IntertwiningMap rho :=
    fun part i => (partitionGriffinIntertwiner lam hk s part i).comp
      (canonicalYoungIdealSpechtEquiv part).toIntertwiningMap
  let a : ∀ part : n.Partition,
      StandardYoungTableau (YoungDiagram.ofPartition part) → YoungIdeal (K := ℚ) part :=
    fun part => canonicalYoungIdealBasis part
  let T0 (part : n.Partition) := StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part)
  have hf (part : n.Partition) : LinearIndependent ℚ (fun i => f part i (a part (T0 part))) := by
    have h := griffin_fixedTableau_renamed_linearIndependent
      (YoungDiagram.card_ofPartition part) hk (T0 part) hheight
    have hfamily : (fun i : PartitionGriffinCopies n lam hk s part =>
        f part i (a part (T0 part))) =
        (fun i : PartitionGriffinCopies n lam hk s part =>
          Ideal.Quotient.mk (griffinIdeal ℚ n lam s)
            (MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition part))
              (higherSpechtPolynomial i.left (T0 part)) *
              elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)) := by
      funext i
      simp only [f, a, Representation.IntertwiningMap.comp_apply,
        Representation.Equiv.coe_toIntertwiningMap]
      exact (congrArg (fun v : spechtModule part =>
        partitionGriffinIntertwiner lam hk s part i v)
        (canonicalYoungIdealSpechtEquiv_basis part (T0 part))).trans
          (partitionGriffinIntertwiner_standardBasis lam hk s part i (T0 part))
    rw [hfamily]
    exact h
  have hfull := independent_intertwiner_copies_all_shapes rho a f
    (fun part => a part (T0 part))
    (fun part => (canonicalYoungIdealBasis part).linearIndependent) hf
  have hindex : LinearIndependent ℚ
      (griffinFamily ℚ n lam hk s ∘ partitionGriffinIndexEquiv n lam hk s) := by
    have hfamily : (fun z : PartitionGriffinVectorIndex n lam hk s =>
        f z.1 z.2.2 (a z.1 z.2.1)) =
        (griffinFamily ℚ n lam hk s ∘ partitionGriffinIndexEquiv n lam hk s) := by
      funext z
      simp only [f, a, Representation.IntertwiningMap.comp_apply,
        Representation.Equiv.coe_toIntertwiningMap, partitionGriffinIndexEquiv,
        Equiv.ofBijective_apply, Function.comp_apply]
      exact (congrArg (fun v : spechtModule z.1 =>
        partitionGriffinIntertwiner lam hk s z.1 z.2.2 v)
        (canonicalYoungIdealSpechtEquiv_basis z.1 z.2.1)).trans
          (partitionGriffinIntertwiner_family lam hk s z)
    rw [← hfamily]
    exact hfull
  have h := hindex.comp (partitionGriffinIndexEquiv n lam hk s).symm
    (partitionGriffinIndexEquiv n lam hk s).symm.injective
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h

end HigherSpecht
end
end CanonicalSource8

section CanonicalSource9
/- Source: HigherSpecht/PolynomialQuotientBaseChange.lean -/



/-! The actual coefficient extension of a polynomial quotient.  This generic
algebraic equivalence is independent of any higher-Specht independence or
basis theorem. -/

noncomputable section

open MvPolynomial
open scoped TensorProduct

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S]

variable [Algebra R S] {n : ℕ}

theorem polynomialTensor_includeRight :
    (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R S).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := S)
        (B := PolynomialRing n R)).toRingHom =
      MvPolynomial.map (algebraMap R S) := by
  apply RingHom.ext
  intro p
  change MvPolynomial.algebraTensorAlgEquiv R S ((1 : S) ⊗ₜ[R] p) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

def polynomialQuotientBaseChangeEquiv (I : Ideal (PolynomialRing n R))
    (J : Ideal (PolynomialRing n S)) (hIJ : I.map (MvPolynomial.map (algebraMap R S)) = J) :
    S ⊗[R] (PolynomialRing n R ⧸ I) ≃ₐ[S] (PolynomialRing n S ⧸ J) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (PolynomialRing n R) S I).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S) (by
      change J = (I.map (Algebra.TensorProduct.includeRight (R := R) (A := S)
        (B := PolynomialRing n R)).toRingHom).map
          (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R S).toRingHom
      rw [Ideal.map_map, polynomialTensor_includeRight, hIJ]))

@[simp] theorem polynomialQuotientBaseChangeEquiv_tmul
    (I : Ideal (PolynomialRing n R)) (J : Ideal (PolynomialRing n S))
    (hIJ : I.map (MvPolynomial.map (algebraMap R S)) = J)
    (c : S) (p : PolynomialRing n R) :
    polynomialQuotientBaseChangeEquiv I J hIJ (c ⊗ₜ[R] Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk J (c • MvPolynomial.map (algebraMap R S) p) := by
  simp only [polynomialQuotientBaseChangeEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlg_mk,
    MvPolynomial.algebraTensorAlgEquiv_tmul]

end HigherSpecht
end
end CanonicalSource9

section CanonicalSource10
/- Source: HigherSpecht/QuotientBaseChange.lean -/



/-!
# Actual scalar extension of the polynomial quotient and prescribed vectors

The equivalence below first tensors the genuine ideal quotient, then uses the
polynomial coefficient-extension equivalence.  The image ideal is identified
by its actual generators.  This supplies the rational-to-complex passage, and
more generally extension to any characteristic-zero field, without a new
basis or dimension assumption.
-/

noncomputable section

open TauCeti Module MvPolynomial
open scoped TensorProduct

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_higherSpechtPolynomial (f : R →+* S) {mu : YoungDiagram}
    (U T : StandardYoungTableau mu) :
    MvPolynomial.map f (higherSpechtPolynomial (R := R) U T) =
      higherSpechtPolynomial U T := by
  simp only [higherSpechtPolynomial_eq_sum, map_sum, MvPolynomial.smul_eq_C_mul,
    map_mul, MvPolynomial.map_C, map_intCast, MvPolynomial.map_rename,
    MvPolynomial.map_monomial, map_one]

theorem map_elementaryMultiplier (f : R →+* S) (n m : ℕ) (eta : ℕ → ℕ) :
    MvPolynomial.map f (elementaryMultiplier (R := R) n m eta) =
      elementaryMultiplier n m eta := by
  simp only [elementaryMultiplier, map_prod, map_pow, MvPolynomial.map_esymm]

theorem map_pairPolynomial (f : R →+* S) {n : ℕ} (P : StandardPair n) :
    MvPolynomial.map f (pairPolynomial (R := R) P) = pairPolynomial P := by
  rw [pairPolynomial, MvPolynomial.map_rename, map_higherSpechtPolynomial]
  rfl

theorem map_griffinPolynomial (f : R →+* S) {n : ℕ} {lam : YoungDiagram}
    {hk : lam.card ≤ n} {s : ℕ} (i : GriffinIndex n lam hk s) :
    MvPolynomial.map f (griffinPolynomial (R := R) i) = griffinPolynomial i := by
  rw [griffinPolynomial, map_mul, map_pairPolynomial, map_elementaryMultiplier]
  rfl

variable [Algebra R S] {n : ℕ}

def griffinBaseChangeEquiv (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (lam : YoungDiagram) (s : ℕ) :
    S ⊗[R] GriffinRing R n lam s ≃ₐ[S] GriffinRing S n lam s :=
  polynomialQuotientBaseChangeEquiv _ _ (map_griffinIdeal (algebraMap R S) n lam s)

@[simp] theorem griffinBaseChangeEquiv_family (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (i : GriffinIndex n lam hk s) :
    griffinBaseChangeEquiv R S n lam s ((1 : S) ⊗ₜ[R] griffinFamily R n lam hk s i) =
      griffinFamily S n lam hk s i := by
  simp only [griffinBaseChangeEquiv, griffinFamily,
    polynomialQuotientBaseChangeEquiv_tmul, map_griffinPolynomial, one_smul]

def untruncatedBaseChangeEquiv (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (lam : YoungDiagram) :
    S ⊗[R] UntruncatedRing R n lam ≃ₐ[S] UntruncatedRing S n lam :=
  polynomialQuotientBaseChangeEquiv _ _ (map_untruncatedIdeal (algebraMap R S) n lam)

/-- The full rational independence theorem extends through the actual tensor
quotient equivalence to every characteristic-zero field. -/
 theorem griffinFamily_linearIndependent_charZero (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    LinearIndependent K (griffinFamily K n lam hk s) := by
  have h := Module.Flat.linearIndependent_one_tmul (S := K)
    (griffinFamily_linearIndependent_rat n lam hk s hs hheight)
  have hm := h.map' (griffinBaseChangeEquiv ℚ K n lam s).toLinearEquiv.toLinearMap
    (LinearMap.ker_eq_bot.mpr (griffinBaseChangeEquiv ℚ K n lam s).injective)
  simpa only [Function.comp_def, LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap,
    AlgEquiv.coe_toLinearEquiv, AlgEquiv.toLinearEquiv_apply,
    griffinBaseChangeEquiv_family] using hm

/-- Transport of a specified basis. This is a scalar-extension lemma: its
input is an already established rational basis, not an assertion that such
a basis has been supplied. -/
def griffinSpecifiedBasisBaseChange (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (B : Basis (GriffinIndex n lam hk s) ℚ (GriffinRing ℚ n lam s)) :
    Basis (GriffinIndex n lam hk s) K (GriffinRing K n lam s) :=
  (B.baseChange K).map (griffinBaseChangeEquiv ℚ K n lam s).toLinearEquiv

 theorem griffinSpecifiedBasisBaseChange_apply (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (B : Basis (GriffinIndex n lam hk s) ℚ (GriffinRing ℚ n lam s))
    (hB : ∀ i, B i = griffinFamily ℚ n lam hk s i) (i : GriffinIndex n lam hk s) :
    griffinSpecifiedBasisBaseChange K n lam hk s B i = griffinFamily K n lam hk s i := by
  simp only [griffinSpecifiedBasisBaseChange, Basis.map_apply, Basis.baseChange_apply,
    hB, AlgEquiv.toLinearEquiv_apply, griffinBaseChangeEquiv_family]

end HigherSpecht
end
end CanonicalSource10

section CanonicalSource11
/- Source: HigherSpecht/GriffinBasisAssembly.lean -/



/-!
# Exact count-to-basis assembly

The full prescribed family is already independent, and the independent monic
staircase construction computes the dimension of the literal quotient.  Only
the reverse cardinal inequality remains in the assembly function below.
That function is explicitly conditional and is not named or presented as the
paper's principal theorem.  A final theorem must supply the count proved from
the actual catabolism index set.
-/

noncomputable section

open TauCeti Module

namespace HigherSpecht

theorem height_pos_of_card_pos (lam : YoungDiagram) (hlam : 0 < lam.card) :
    0 < lam.colLen 0 := by
  obtain ⟨⟨r, c⟩, hc⟩ := Finset.card_pos.mp hlam
  exact YoungDiagram.mem_iff_lt_colLen.mp
    (lam.up_left_mem (Nat.zero_le r) (Nat.zero_le c) hc)

theorem griffin_index_card_le_staircase (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Nat.card (GriffinIndex n lam hk s) ≤ Nat.card (GriffinStaircaseExponents n lam s) := by
  letI := griffinRing_finiteDimensional lam hk s hs hheight
  have h := (griffinFamily_linearIndependent_rat n lam hk s hs hheight).fintype_card_le_finrank
  simpa only [← Nat.card_eq_fintype_card,
    finrank_griffin_eq_staircase_card ℚ hk s hs hheight] using h

def griffinBasisOfReverseCardinality (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (hcount : Nat.card (GriffinStaircaseExponents n lam s) ≤
      Nat.card (GriffinIndex n lam hk s)) :
    Basis (GriffinIndex n lam hk s) K (GriffinRing K n lam s) := by
  letI := (finite_griffinStaircaseExponents (n := n) (μ := lam) s hs hheight).fintype
  letI : FiniteDimensional K (GriffinRing K n lam s) :=
    Module.Finite.of_basis (griffinStandardMonomialBasis hk s hs hheight)
  refine basisOfLinearIndependentOfCardEqFinrank' (griffinFamily K n lam hk s)
    (griffinFamily_linearIndependent_charZero K n lam hk s hs hheight) ?_
  rw [finrank_griffin_eq_staircase_card K hk s hs hheight, ← Nat.card_eq_fintype_card]
  exact le_antisymm (griffin_index_card_le_staircase n lam hk s hs hheight) hcount

@[simp] theorem griffinBasisOfReverseCardinality_apply (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (hcount : Nat.card (GriffinStaircaseExponents n lam s) ≤
      Nat.card (GriffinIndex n lam hk s)) (i : GriffinIndex n lam hk s) :
    griffinBasisOfReverseCardinality K n lam hk s hs hheight hcount i =
      griffinFamily K n lam hk s i := by
  simp only [griffinBasisOfReverseCardinality, coe_basisOfLinearIndependentOfCardEqFinrank']

end HigherSpecht
end
end CanonicalSource11

section CanonicalSource12
/- Source: HigherSpecht/EligibleIndexCountEmptyBasis.lean -/



/-!
# The full empty-partition polynomial basis

The bounded-word bijection supplies the missing cardinality in this case.
Every staircase exponent is a bounded word, so the opposite cardinal bound
from actual polynomial independence makes the two finite cardinalities equal.
No count hypothesis remains in the resulting prescribed basis. This is the
empty-partition endpoint only; the general nonempty-partition count is separate.
-/

noncomputable section
open TauCeti Module
open scoped Classical

namespace HigherSpecht

def staircaseBoundedWord {n : ℕ} {lam : YoungDiagram} {s : ℕ}
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (a : GriffinStaircaseExponents n lam s) : Fin n → Fin s :=
  fun i => ⟨a.val i, ((mem_griffinStaircaseExponents_iff a.val hs hheight).mp a.property).2 i⟩

theorem staircaseBoundedWord_injective {n : ℕ} {lam : YoungDiagram} {s : ℕ}
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Function.Injective (staircaseBoundedWord (n := n) hs hheight) := by
  intro a b hab
  apply Subtype.ext
  ext i
  exact congrArg Fin.val (congrFun hab i)

theorem card_griffinStaircase_le_words {n : ℕ} {lam : YoungDiagram} {s : ℕ}
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Nat.card (GriffinStaircaseExponents n lam s) ≤ s ^ n := by
  have h := Nat.card_le_card_of_injective (staircaseBoundedWord (n := n) hs hheight)
    (staircaseBoundedWord_injective hs hheight)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using h

theorem card_griffinStaircase_empty (n s : ℕ) (hs : 0 < s) :
    Nat.card (GriffinStaircaseExponents n ⊥ s) = s ^ n := by
  apply le_antisymm (card_griffinStaircase_le_words hs (by simp))
  rw [← card_griffinIndex_empty n s hs]
  exact griffin_index_card_le_staircase n ⊥ (by simp [YoungDiagram.card]) s hs (by simp)

def griffinEmptyBasis (K : Type*) [Field K] [CharZero K]
    (n s : ℕ) (hs : 0 < s) :
    Basis (GriffinIndex n ⊥ (by simp [YoungDiagram.card]) s) K (GriffinRing K n ⊥ s) :=
  griffinBasisOfReverseCardinality K n ⊥ (by simp [YoungDiagram.card]) s hs (by simp)
    (by rw [card_griffinStaircase_empty n s hs, card_griffinIndex_empty n s hs])

@[simp] theorem griffinEmptyBasis_apply (K : Type*) [Field K] [CharZero K]
    (n s : ℕ) (hs : 0 < s)
    (i : GriffinIndex n ⊥ (by simp [YoungDiagram.card]) s) :
    griffinEmptyBasis K n s hs i = griffinFamily K n ⊥ (by simp [YoungDiagram.card]) s i := by
  exact griffinBasisOfReverseCardinality_apply K n ⊥ _ s hs _ _ i

theorem griffin_empty_specifiedBasis (K : Type*) [Field K] [CharZero K]
    (n s : ℕ) (hs : 0 < s) :
    IsSpecifiedBasis (R := K) (griffinFamily K n ⊥ (by simp [YoungDiagram.card]) s) :=
  ⟨griffinEmptyBasis K n s hs, griffinEmptyBasis_apply K n s hs⟩

end HigherSpecht
end
end CanonicalSource12

section CanonicalSource13
/- Source: HigherSpecht/StaircaseContentWords.lean -/



/-!
# The full ungraded staircase count by literal content-constrained words

A word in `s` colors must contain at least `lam.rowLen i` copies of color `i`.
Deleting its first color decrements exactly one requirement. Swapping that color
with the bottom row of its equal-length block sorts the new requirements and
produces the same child diagram as the exact staircase recursion.

This count concerns the actual standard monomial basis. It does not identify
these words with the catabolism-eligible higher Specht indices.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

def ContentWord (n : ℕ) (lam : YoungDiagram) (s : ℕ) :=
  {u : Fin n → Fin s // ∀ i : Fin s, lam.rowLen i.val ≤ (List.ofFn u).count i}

instance (n : ℕ) (lam : YoungDiagram) (s : ℕ) : Finite (ContentWord n lam s) :=
  inferInstanceAs (Finite {u : Fin n → Fin s // _})

theorem greedyCutCorner_rowLen (lam : YoungDiagram) (j : ℕ)
    (hj : j < lam.colLen 0) :
    lam.rowLen j = lam.rowLen (greedyCutCorner lam j hj).1 := by
  obtain ⟨hc, hrow, hnext⟩ := greedyCutCorner_spec lam j hj
  rw [hc.rowLen_eq_snd_add_one]
  have hm : (j, (greedyCutCorner lam j hj).2) ∈ lam :=
    lam.up_left_mem hrow le_rfl hc.mem
  have hlo := YoungDiagram.mem_iff_lt_rowLen.mp hm
  have hhi : ¬ (j, (greedyCutCorner lam j hj).2 + 1) ∈ lam := by
    intro h
    exact (Nat.not_lt_of_ge hnext) (YoungDiagram.mem_iff_lt_colLen.mp h)
  rw [YoungDiagram.mem_iff_lt_rowLen] at hhi
  omega

def contentCutPermutation (lam : YoungDiagram) (s : ℕ)
    (hheight : lam.colLen 0 ≤ s) (j : Fin s) : Equiv.Perm (Fin s) :=
  if hj : j.val < lam.colLen 0 then
    Equiv.swap j ⟨(greedyCutCorner lam j.val hj).1,
      lt_of_lt_of_le (greedyCutCorner_spec lam j.val hj).1.fst_lt_colLen_zero hheight⟩
  else Equiv.refl _

theorem contentCutPermutation_requirements (lam : YoungDiagram) (s : ℕ)
    (hheight : lam.colLen 0 ≤ s) (j i : Fin s) :
    (staircaseChildShape lam j.val).rowLen (contentCutPermutation lam s hheight j i).val =
      lam.rowLen i.val - if i = j then 1 else 0 := by
  by_cases hj : j.val < lam.colLen 0
  · simp only [staircaseChildShape, contentCutPermutation, dif_pos hj]
    let c := greedyCutCorner lam j.val hj
    have hc : YoungDiagram.IsCorner lam c := (greedyCutCorner_spec lam j.val hj).1
    have heq : lam.rowLen j.val = lam.rowLen c.1 := greedyCutCorner_rowLen lam j.val hj
    let b : Fin s := ⟨c.1, lt_of_lt_of_le hc.fst_lt_colLen_zero hheight⟩
    change (lam.erase c).rowLen (Equiv.swap j b i).val = _
    by_cases hij : i = j
    · subst i
      rw [Equiv.swap_apply_left]
      simpa only [b, hc.rowLen_erase, if_pos rfl, if_true] using
        congrArg (fun x : ℕ => x - 1) heq.symm
    · by_cases hib : i = b
      · subst i
        have hrows : c.1 ≠ j.val := by
          intro h
          exact hij (Fin.ext h)
        simp only [Equiv.swap_apply_right, hc.rowLen_erase, hrows, if_false,
          hij, Nat.sub_zero]
        exact heq
      · rw [Equiv.swap_apply_of_ne_of_ne hij hib, hc.rowLen_erase]
        have hrows : c.1 ≠ i.val := by
          intro h
          exact hib (Fin.ext h.symm)
        simp only [hrows, hij, if_false, Nat.sub_zero]
  · simp only [staircaseChildShape, contentCutPermutation, dif_neg hj]
    have hz : lam.rowLen j.val = 0 :=
      YoungDiagram.rowLen_eq_zero_of_colLen_le (Nat.le_of_not_gt hj)
    by_cases hij : i = j
    · subst i
      simp only [Equiv.refl_apply, if_pos rfl, hz, Nat.zero_sub]
    · simp only [Equiv.refl_apply, hij, if_false, Nat.sub_zero]

theorem count_ofFn_relabel {n s : ℕ} (u : Fin n → Fin s)
    (e : Equiv.Perm (Fin s)) (i : Fin s) :
    (List.ofFn (fun x => e (u x))).count (e i) = (List.ofFn u).count i := by
  simpa only [List.map_ofFn, Function.comp_def] using
    List.count_map_of_injective (List.ofFn u) e e.injective i

theorem contentWord_cons_iff {n s : ℕ} (lam : YoungDiagram)
    (hheight : lam.colLen 0 ≤ s) (j : Fin s) (u : Fin n → Fin s) :
    (∀ i : Fin s, lam.rowLen i.val ≤ (List.ofFn (Fin.cons j u)).count i) ↔
      ∀ i : Fin s, (staircaseChildShape lam j.val).rowLen i.val ≤
        (List.ofFn (fun x => contentCutPermutation lam s hheight j (u x))).count i := by
  let e := contentCutPermutation lam s hheight j
  have hpoint (i : Fin s) :
      lam.rowLen i.val ≤ (List.ofFn (Fin.cons j u)).count i ↔
        (staircaseChildShape lam j.val).rowLen (e i).val ≤
          (List.ofFn (fun x => e (u x))).count (e i) := by
    rw [contentCutPermutation_requirements, count_ofFn_relabel, List.ofFn_cons]
    by_cases hij : i = j
    · subst i
      simp only [if_pos rfl, if_true, List.count_cons_self]
      omega
    · simp only [hij, if_false, List.count_cons_of_ne (Ne.symm hij), Nat.sub_zero]
  constructor
  · intro h i
    simpa only [Equiv.apply_symm_apply] using (hpoint (e.symm i)).mp (h (e.symm i))
  · intro h i
    exact (hpoint i).mpr (h (e i))

def contentWordChildEquiv {n : ℕ} (lam : YoungDiagram) (s : ℕ)
    (hheight : lam.colLen 0 ≤ s) :
    ContentWord (n + 1) lam s ≃ Σ j : Fin s, ContentWord n (staircaseChildShape lam j.val) s where
  toFun u :=
    ⟨u.val 0,
      (fun x => contentCutPermutation lam s hheight (u.val 0) (u.val x.succ)),
      (contentWord_cons_iff lam hheight (u.val 0) (fun x => u.val x.succ)).mp
        (by
          have hcons : Fin.cons (u.val 0) (fun x => u.val x.succ) = u.val := by
            funext i
            cases i using Fin.cases with
            | zero => rfl
            | succ i => rfl
          rw [hcons]
          exact u.property)⟩
  invFun v :=
    ⟨Fin.cons v.1 (fun x => (contentCutPermutation lam s hheight v.1).symm (v.2.val x)),
      (contentWord_cons_iff lam hheight v.1 _).mpr (by
        simpa only [Equiv.apply_symm_apply] using v.2.property)⟩
  left_inv u := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Equiv.symm_apply_apply _ _
  right_inv v := by
    rcases v with ⟨j, u⟩
    apply Sigma.subtype_ext
    · rfl
    · funext i
      exact Equiv.apply_symm_apply _ _

theorem card_contentWord_recursion {n : ℕ} (lam : YoungDiagram) (s : ℕ)
    (hheight : lam.colLen 0 ≤ s) :
    Nat.card (ContentWord (n + 1) lam s) =
      ∑ j : Fin s, Nat.card (ContentWord n (staircaseChildShape lam j.val) s) := by
  rw [Nat.card_congr (contentWordChildEquiv lam s hheight), Nat.card_sigma]

def contentWordEmptyEquiv (n s : ℕ) : ContentWord n ⊥ s ≃ (Fin n → Fin s) where
  toFun := Subtype.val
  invFun u := ⟨u, by intro i; simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem card_contentWord_empty (n s : ℕ) :
    Nat.card (ContentWord n ⊥ s) = s ^ n := by
  rw [Nat.card_congr (contentWordEmptyEquiv n s)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

theorem card_staircase_eq_contentWords (n : ℕ) (lam : YoungDiagram) (s : ℕ)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Nat.card (GriffinStaircaseExponents n lam s) = Nat.card (ContentWord n lam s) := by
  induction n generalizing lam with
  | zero =>
      by_cases hbot : lam = ⊥
      · subst lam
        rw [card_griffinStaircase_empty _ _ hs, card_contentWord_empty]
      · have hcells : lam.cells.Nonempty := by
          apply Finset.nonempty_iff_ne_empty.mpr
          intro h
          apply hbot
          ext c
          simp only [h, YoungDiagram.cells_bot]
        obtain ⟨c, hc⟩ := hcells
        have hcard : 0 < lam.card := Finset.card_pos.mpr ⟨c, hc⟩
        haveI : IsEmpty (GriffinStaircaseExponents 0 lam s) := ⟨fun a =>
          shuffleBound_false_of_card_gt hcard
            ((mem_griffinStaircaseExponents_iff a.val hs hheight).mp a.property).1⟩
        haveI : IsEmpty (ContentWord 0 lam s) := ⟨fun u => by
          let i : Fin s := ⟨c.1, lt_of_lt_of_le (YoungDiagram.lt_colLen_zero_of_mem hc) hheight⟩
          have h := u.property i
          have hp := YoungDiagram.mem_iff_lt_rowLen.mp hc
          simp only [List.ofFn_zero, List.count_nil] at h
          dsimp [i] at h
          omega⟩
        simp
  | succ n ih =>
      rw [card_griffinStaircase_recursion lam s hs hheight,
        card_contentWord_recursion lam s hheight]
      apply Finset.sum_congr rfl
      intro j hj
      exact ih (staircaseChildShape lam j.val)
        ((staircaseChildShape_height_le lam j.val).trans hheight)

end HigherSpecht
end
end CanonicalSource13

section CanonicalSource14
/- Source: HigherSpecht/LascouxReflectionCyclage.lean -/



/-!
# Signature reflection and ordinary cyclic rotation

Rank-one reflection commutes with exchanging the complete tail factor and
the one-letter factor.  The literal cons/snoc tensor maps therefore prove
commutation with ordinary, content-preserving word rotation.  This rotation
does not decrement labels and is not identified with the separate cyclic
insertion operation used to define catabolizability.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem listString_singleton_signature (r a : ℕ) :
    (listString r).epsilon [a] = (letterString r).epsilon a ∧
      (listString r).phi [a] = (letterString r).phi a := by
  simp only [listString_epsilon_cons, listString_phi_cons,
    listString_epsilon_nil, listString_phi_nil]
  exact ⟨by omega, by omega⟩

theorem listString_lower_singleton (r a : ℕ) :
    (listString r).lower [a] = ((letterString r).lower a).map (fun b => [b]) := by
  rw [listString_lower_cons, listString_phi_nil, if_neg (Nat.not_lt_zero _)]

theorem listString_raise_singleton (r a : ℕ) :
    (listString r).raise [a] = ((letterString r).raise a).map (fun b => [b]) := by
  rw [listString_raise_cons, listString_phi_nil]
  by_cases h : a = r + 1
  · simp [letterString, h]
  · simp [letterString, h, listString_raise_nil]

theorem reflection_cons_tensor (r a : ℕ) (w : List ℕ) :
    (listString r).reflection (a :: w) =
      let z := ((listString r).tensor (letterString r)).reflection (w, a)
      z.2 :: z.1 := by
  refine StringSystem.reflection_map ((listString r).tensor (letterString r))
    (listString r) (fun z => z.2 :: z.1) ?_ ?_ ?_ ?_ (w, a)
  · intro z
    exact listString_epsilon_cons r z.2 z.1
  · intro z
    exact listString_phi_cons r z.2 z.1
  · intro z
    rw [listString_lower_cons]
    simp only [StringSystem.tensor, Option.map_map, Function.comp_def]
    split_ifs <;> simp only [Option.map_map, Function.comp_def]
  · intro z
    rw [listString_raise_cons]
    simp only [StringSystem.tensor, Option.map_map, Function.comp_def]
    split_ifs <;> simp only [Option.map_map, Function.comp_def]

theorem reflection_snoc_tensor (r a : ℕ) (w : List ℕ) :
    (listString r).reflection (w ++ [a]) =
      let z := ((letterString r).tensor (listString r)).reflection (a, w)
      z.2 ++ [z.1] := by
  refine StringSystem.reflection_map ((letterString r).tensor (listString r))
    (listString r) (fun z => z.2 ++ [z.1]) ?_ ?_ ?_ ?_ (a, w)
  · intro z
    rw [listString_epsilon_append, (listString_singleton_signature r z.1).1,
      (listString_singleton_signature r z.1).2]
    rfl
  · intro z
    rw [listString_phi_append, (listString_singleton_signature r z.1).2]
    rfl
  · intro z
    rw [listString_lower_append, (listString_singleton_signature r z.1).2,
      listString_lower_singleton]
    simp only [StringSystem.tensor, Option.map_map, Function.comp_def]
    split_ifs <;> simp only [Option.map_map, Function.comp_def]
  · intro z
    rw [listString_raise_append, (listString_singleton_signature r z.1).2,
      listString_raise_singleton]
    simp only [StringSystem.tensor, Option.map_map, Function.comp_def]
    split_ifs <;> simp only [Option.map_map, Function.comp_def]

/-- The exact unconditional ordinary cyclic-rotation identity for the
constructed signature reflection. -/
theorem reflection_rotateHead (r a : ℕ) (w : List ℕ) :
    (listString r).reflection (rotateHead (a :: w)) =
      rotateHead ((listString r).reflection (a :: w)) := by
  rw [rotateHead, reflection_snoc_tensor, reflection_cons_tensor,
    StringSystem.tensor_reflection_swap]
  cases h : ((listString r).tensor (letterString r)).reflection (w, a) with
  | mk u b => rfl

theorem reflection_rotateHead_all (r : ℕ) (w : List ℕ) :
    (listString r).reflection (rotateHead w) =
      rotateHead ((listString r).reflection w) := by
  cases w with
  | nil =>
      have h := (listString r).reflection_eq_self_of_middle
        (x := []) (by rfl)
      simpa only [rotateHead, h]
  | cons a w => exact reflection_rotateHead r a w

end HigherSpecht.Lascoux
end
end CanonicalSource14

section CanonicalSource15
/- Source: HigherSpecht/LascouxContentTransfer.lean -/



/-!
# A genuine injective split of a repeated letter

A content transfer is carried out by explicit crystal reflections, one first
lowering, and the inverse reflections.  It is consequently injective on the
entire fixed-content word set.  This elementary operator construction does not
identify its eventual standard-word image with any catabolizability class.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

def WordOfContent (n : ℕ) (c : ℕ → ℕ) :=
  {u : Fin n → ℕ // ∀ a, wordContent u a = c a}

def splitContent (c : ℕ → ℕ) (i j : ℕ) : ℕ → ℕ :=
  Function.update (Function.update c i (c i - 1)) j 1

theorem distinct_of_split_counts {c : ℕ → ℕ} {i j : ℕ}
    (hi : 1 < c i) (hj : c j = 0) : i ≠ j := by
  intro h
  subst j
  omega

def preparedContentWord (n : ℕ) (c : ℕ → ℕ) (i j : ℕ)
    (hi : 1 < c i) (hj : c j = 0) (u : WordOfContent n c) :
    {v : Fin n → ℕ // 0 < (wordString 0 n).phi v} :=
  ⟨wordBringPair n i j u.val, by
    have hne := distinct_of_split_counts hi hj
    have hz := wordBringPair_zero n i j hne u.val
    have ho := wordBringPair_one n i j u.val
    rw [u.property i] at hz
    rw [u.property j, hj] at ho
    have hb := wordString_balance 0 n (wordBringPair n i j u.val)
    change (((wordString 0 n).phi _ : ℤ) - (wordString 0 n).epsilon _) =
      (wordContent _ 0 : ℤ) - wordContent _ 1 at hb
    rw [hz, ho] at hb
    omega⟩

theorem preparedContentWord_injective (n : ℕ) (c : ℕ → ℕ) (i j : ℕ)
    (hi : 1 < c i) (hj : c j = 0) :
    Function.Injective (preparedContentWord n c i j hi hj) := by
  intro u v huv
  apply Subtype.ext
  apply (wordBringPair n i j).injective
  exact congrArg Subtype.val huv

def transferContentWord (n : ℕ) (c : ℕ → ℕ) (i j : ℕ)
    (hi : 1 < c i) (hj : c j = 0) (u : WordOfContent n c) : Fin n → ℕ :=
  (wordBringPair n i j).symm
    ((wordString 0 n).lowerValue (preparedContentWord n c i j hi hj u))

theorem transferContentWord_content (n : ℕ) (c : ℕ → ℕ) (i j : ℕ)
    (hi : 1 < c i) (hj : c j = 0) (u : WordOfContent n c) (a : ℕ) :
    wordContent (transferContentWord n c i j hi hj u) a = splitContent c i j a := by
  let E := wordBringPair n i j
  let P := bringPairPermutation i j
  let z := (wordString 0 n).lowerValue (preparedContentWord n c i j hi hj u)
  have hij := distinct_of_split_counts hi hj
  have hP0 : P i = 0 := bringPairPermutation_apply_left i j hij
  have hP1 : P j = 1 := bringPairPermutation_apply_right i j
  have hzero : (P a = 0) ↔ a = i := by
    rw [← hP0, P.injective.eq_iff]
  have hone : (P a = 1) ↔ a = j := by
    rw [← hP1, P.injective.eq_iff]
  have hafter : wordContent z (P a) =
      wordContent (transferContentWord n c i j hi hj u) a := by
    have h := wordBringPair_content n i j (P a) (E.symm z)
    simpa only [E, P, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
      transferContentWord] using h
  have hbefore : wordContent (E u.val) (P a) = c a := by
    rw [wordBringPair_content]
    simpa only [P, Equiv.symm_apply_apply] using u.property a
  have hcount := word_lower_count 0 n (P a)
    ((wordString 0 n).lowerValue_spec (preparedContentWord n c i j hi hj u))
  change (wordContent z (P a) : ℤ) =
    (wordContent (E u.val) (P a) : ℤ) +
      (if P a = 1 then 1 else 0) - (if P a = 0 then 1 else 0) at hcount
  rw [hafter, hbefore] at hcount
  by_cases hai : a = i
  · subst a
    have hne : ¬ P i = 1 := by simpa only [hone] using hij
    simp only [hP0, hne, if_false, if_true, zero_add] at hcount
    simp only [splitContent, Function.update_of_ne hij,
      Function.update_self]
    omega
  · by_cases haj : a = j
    · subst a
      have hne : ¬ P j = 0 := by simpa only [hzero] using Ne.symm hij
      simp only [hP1, hne, if_false, if_true, hj] at hcount
      simp only [splitContent, Function.update_self]
      omega
    · have h0 : ¬ P a = 0 := by simpa only [hzero] using hai
      have h1 : ¬ P a = 1 := by simpa only [hone] using haj
      simp only [h0, h1, if_false, add_zero, sub_zero] at hcount
      simp only [splitContent, Function.update_of_ne haj,
        Function.update_of_ne hai]
      exact_mod_cast hcount

theorem transferContentWord_injective (n : ℕ) (c : ℕ → ℕ) (i j : ℕ)
    (hi : 1 < c i) (hj : c j = 0) :
    Function.Injective (transferContentWord n c i j hi hj) := by
  intro u v huv
  have hlow : (wordString 0 n).lowerValue (preparedContentWord n c i j hi hj u) =
      (wordString 0 n).lowerValue (preparedContentWord n c i j hi hj v) :=
    (wordBringPair n i j).symm.injective huv
  have hprep := (wordString 0 n).lowerEmbedding.injective hlow
  exact preparedContentWord_injective n c i j hi hj hprep

def contentTransferEmbedding (n : ℕ) (c : ℕ → ℕ) (i j : ℕ)
    (hi : 1 < c i) (hj : c j = 0) :
    WordOfContent n c ↪ WordOfContent n (splitContent c i j) where
  toFun u := ⟨transferContentWord n c i j hi hj u,
    transferContentWord_content n c i j hi hj u⟩
  inj' u v h := transferContentWord_injective n c i j hi hj (congrArg Subtype.val h)

end HigherSpecht.Lascoux
end
end CanonicalSource15

section CanonicalSource16
/- Source: HigherSpecht/LascouxContentKnuth.lean -/



/-!
# Fixed-content lowering is an embedding of insertion classes

The inverse partial raising operation shows that lowering both preserves and
reflects Knuth equivalence on its domain.  Conjugating by the concrete content
reflections gives the same exact statement for a repeated-letter split.  No
tableau shape or catabolizability image assertion is built into these maps.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem lowerValue_word_knuth_iff (r n : ℕ)
    (u v : {w : Fin n → ℕ // 0 < (wordString r n).phi w}) :
    KnuthEquivalent (List.ofFn ((wordString r n).lowerValue u))
      (List.ofFn ((wordString r n).lowerValue v)) ↔
      KnuthEquivalent (List.ofFn u.val) (List.ofFn v.val) := by
  have hlu := (wordString r n).lowerValue_spec u
  have hlv := (wordString r n).lowerValue_spec v
  have hru := (wordString r n).lower_eq_some_iff.mp hlu
  have hrv := (wordString r n).lower_eq_some_iff.mp hlv
  constructor
  · intro h
    have hh := listString_raise_of_knuth r h
    rw [listString_raise_ofFn, listString_raise_ofFn, hru, hrv,
      Option.map_some, Option.map_some] at hh
    exact hh
  · intro h
    have hh := listString_lower_of_knuth r h
    rw [listString_lower_ofFn, listString_lower_ofFn, hlu, hlv,
      Option.map_some, Option.map_some] at hh
    exact hh

theorem transferContentWord_knuth_iff (n : ℕ) (c : ℕ → ℕ) (i j : ℕ)
    (hi : 1 < c i) (hj : c j = 0) (u v : WordOfContent n c) :
    KnuthEquivalent (List.ofFn (transferContentWord n c i j hi hj u))
      (List.ofFn (transferContentWord n c i j hi hj v)) ↔
      KnuthEquivalent (List.ofFn u.val) (List.ofFn v.val) := by
  unfold transferContentWord
  rw [(wordBringPair_preserves_knuth n i j).symm,
    lowerValue_word_knuth_iff]
  exact wordBringPair_preserves_knuth n i j u.val v.val

end HigherSpecht.Lascoux
end
end CanonicalSource16

section CanonicalSource17
/- Source: HigherSpecht/LascouxBalancingTermination.lean -/



/-!
# Termination of an actual crystal content-balancing construction

If a word of length `n` uses an alphabet of size `n`, a repeated letter forces a
missing letter.  Splitting a repetition into a missing letter removes exactly
one zero content entry.  Strong induction on that number constructs an injection
into standard words using the actual reflection/lowering maps from the preceding
files.  This is a construction of the operators, not the outstanding theorem
that their image satisfies the required catabolizability constraint.
-/

noncomputable section
open scoped Classical BigOperators
open Finset

namespace HigherSpecht.Lascoux

def extendContent {n : ℕ} (c : Fin n → ℕ) (a : ℕ) : ℕ :=
  if h : a < n then c ⟨a, h⟩ else 0

@[simp] theorem extendContent_apply {n : ℕ} (c : Fin n → ℕ) (i : Fin n) :
    extendContent c i.val = c i := by
  simp [extendContent, i.isLt]

def standardContent (n a : ℕ) : ℕ := if a < n then 1 else 0

def finiteSplitContent {n : ℕ} (c : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  Function.update (Function.update c i (c i - 1)) j 1

theorem extend_finiteSplitContent {n : ℕ} (c : Fin n → ℕ) (i j : Fin n) :
    extendContent (finiteSplitContent c i j) = splitContent (extendContent c) i.val j.val := by
  funext a
  by_cases ha : a < n
  · simp [extendContent, finiteSplitContent, splitContent, Function.update_apply,
      ha, i.isLt, Fin.ext_iff]
  · have hai : a ≠ i.val := by intro h; subst a; exact ha i.isLt
    have haj : a ≠ j.val := by intro h; subst a; exact ha j.isLt
    simp [extendContent, finiteSplitContent, splitContent, Function.update_apply,
      ha, hai, haj]

theorem finiteSplitContent_sum {n : ℕ} (c : Fin n → ℕ) (i j : Fin n)
    (hi : 1 < c i) (hj : c j = 0) :
    ∑ a, finiteSplitContent c i j a = ∑ a, c a := by
  have hij : i ≠ j := by intro h; subst j; omega
  have hpoint (a : Fin n) :
      finiteSplitContent c i j a + (if a = i then 1 else 0) =
        c a + (if a = j then 1 else 0) := by
    by_cases hai : a = i
    · subst a
      simp only [finiteSplitContent, Function.update_of_ne hij,
        Function.update_self, if_true, if_neg hij]
      omega
    · by_cases haj : a = j
      · subst a
        simp [finiteSplitContent, Ne.symm hij, hj]
      · simp [finiteSplitContent, hai, haj]
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun a _ => hpoint a)
  simp only [Finset.sum_add_distrib] at hs
  simpa using hs

def missingLetters {n : ℕ} (c : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c i = 0)

theorem missingLetters_finiteSplitContent {n : ℕ} (c : Fin n → ℕ) (i j : Fin n)
    (hi : 1 < c i) (hj : c j = 0) :
    missingLetters (finiteSplitContent c i j) = (missingLetters c).erase j := by
  have hij : i ≠ j := by intro h; subst j; omega
  ext a
  simp only [missingLetters, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase]
  by_cases hai : a = i
  · subst a
    simp only [finiteSplitContent, Function.update_of_ne hij,
      Function.update_self]
    omega
  · by_cases haj : a = j
    · subst a
      simp [finiteSplitContent]
    · simp [finiteSplitContent, hai, haj]

theorem missingLetters_finiteSplitContent_card_lt {n : ℕ}
    (c : Fin n → ℕ) (i j : Fin n) (hi : 1 < c i) (hj : c j = 0) :
    (missingLetters (finiteSplitContent c i j)).card < (missingLetters c).card := by
  rw [missingLetters_finiteSplitContent c i j hi hj]
  exact Finset.card_erase_lt_of_mem (by simp [missingLetters, hj])

theorem exists_missing_of_repeated {n : ℕ} (c : Fin n → ℕ)
    (hc : ∑ i, c i = n) (i : Fin n) (hi : 1 < c i) : ∃ j, c j = 0 := by
  by_contra h
  push_neg at h
  have hpos (a : Fin n) : 1 ≤ c a := by have := h a; omega
  have hlt := Finset.sum_lt_sum (s := Finset.univ)
    (fun a _ => hpos a) ⟨i, Finset.mem_univ _, hi⟩
  simpa [hc] using hlt

theorem content_eq_one_of_le_one {n : ℕ} (c : Fin n → ℕ)
    (hc : ∑ i, c i = n) (hbound : ∀ i, c i ≤ 1) : ∀ i, c i = 1 := by
  intro i
  by_contra hi
  have hlt_i : c i < 1 := lt_of_le_of_ne (hbound i) hi
  have hlt := Finset.sum_lt_sum (s := Finset.univ)
    (fun a _ => hbound a) ⟨i, Finset.mem_univ _, hlt_i⟩
  simpa [hc] using hlt

def finiteContentTransferEmbedding {n : ℕ} (c : Fin n → ℕ) (i j : Fin n)
    (hi : 1 < c i) (hj : c j = 0) :
    WordOfContent n (extendContent c) ↪
      WordOfContent n (extendContent (finiteSplitContent c i j)) := by
  have hi' : 1 < extendContent c i.val := by simpa using hi
  have hj' : extendContent c j.val = 0 := by simpa using hj
  exact
    { toFun := fun u => ⟨transferContentWord n (extendContent c) i.val j.val hi' hj' u,
        fun a => by
          simpa only [extend_finiteSplitContent] using
            transferContentWord_content n (extendContent c) i.val j.val hi' hj' u a⟩
      inj' := fun u v h => transferContentWord_injective n (extendContent c)
        i.val j.val hi' hj'
        (congrArg (fun z : WordOfContent n (extendContent (finiteSplitContent c i j)) =>
          z.val) h) }

@[simp] theorem finiteContentTransferEmbedding_apply_val {n : ℕ}
    (c : Fin n → ℕ) (i j : Fin n) (hi : 1 < c i) (hj : c j = 0)
    (u : WordOfContent n (extendContent c)) :
    (finiteContentTransferEmbedding c i j hi hj u).val =
      transferContentWord n (extendContent c) i.val j.val
        (by simpa only [extendContent_apply] using hi)
        (by simpa only [extendContent_apply] using hj) u := rfl

/-- The zero-count measure proves termination.  Every nontrivial branch is the
concrete reflection / first-lowering / inverse-reflection embedding. -/
theorem exists_crystal_balancing_embedding (n : ℕ) (c : Fin n → ℕ)
    (hc : ∑ i, c i = n) :
    Nonempty (WordOfContent n (extendContent c) ↪ WordOfContent n (standardContent n)) := by
  have aux : ∀ k : ℕ, ∀ c : Fin n → ℕ, (missingLetters c).card = k →
      (∑ i, c i = n) →
      Nonempty (WordOfContent n (extendContent c) ↪ WordOfContent n (standardContent n)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro c hk hc
        by_cases hbound : ∀ i, c i ≤ 1
        · have hone := content_eq_one_of_le_one c hc hbound
          have heq : extendContent c = standardContent n := by
            funext a
            unfold extendContent standardContent
            split_ifs with ha
            · exact hone ⟨a, ha⟩
            · rfl
          rw [heq]
          exact ⟨Function.Embedding.refl _⟩
        · push_neg at hbound
          obtain ⟨i, hi⟩ := hbound
          obtain ⟨j, hj⟩ := exists_missing_of_repeated c hc i hi
          let d := finiteSplitContent c i j
          have hd : ∑ a, d a = n := (finiteSplitContent_sum c i j hi hj).trans hc
          have hlt : (missingLetters d).card < k := by
            rw [← hk]
            exact missingLetters_finiteSplitContent_card_lt c i j hi hj
          obtain ⟨e⟩ := ih (missingLetters d).card hlt d rfl hd
          exact ⟨(finiteContentTransferEmbedding c i j hi hj).trans e⟩
  exact aux _ c rfl hc

theorem standardContentWord_bound {n : ℕ} (u : WordOfContent n (standardContent n))
    (i : Fin n) : u.val i < n := by
  have hm : u.val i ∈ List.ofFn u.val := List.mem_ofFn.mpr ⟨i, rfl⟩
  have hp : 0 < wordContent u.val (u.val i) := List.count_pos_iff.mpr hm
  rw [u.property] at hp
  by_contra hi
  simpa [standardContent, hi] using hp

def standardContentWordPermutation {n : ℕ}
    (u : WordOfContent n (standardContent n)) : Equiv.Perm (Fin n) :=
  let f : Fin n → Fin n := fun i => ⟨u.val i, standardContentWord_bound u i⟩
  Equiv.ofBijective f (by
    have hnodup : (List.ofFn u.val).Nodup := by
      apply List.nodup_iff_count_le_one.mpr
      intro a
      change wordContent u.val a ≤ 1
      rw [u.property]
      unfold standardContent
      split_ifs <;> omega
    have hinj : Function.Injective f := by
      intro i j hij
      exact List.nodup_ofFn.mp hnodup (congrArg Fin.val hij)
    exact ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩)

theorem standardContentWordPermutation_injective (n : ℕ) :
    Function.Injective (@standardContentWordPermutation n) := by
  intro u v huv
  apply Subtype.ext
  funext i
  exact congrArg (fun e : Equiv.Perm (Fin n) => (e i).val) huv

/-- The construction genuinely ends in permutations.  Its catabolizability
image is deliberately absent from this statement until proved separately. -/
theorem exists_content_to_permutation_embedding (n : ℕ) (c : Fin n → ℕ)
    (hc : ∑ i, c i = n) : Nonempty (WordOfContent n (extendContent c) ↪ Equiv.Perm (Fin n)) := by
  obtain ⟨e⟩ := exists_crystal_balancing_embedding n c hc
  exact ⟨e.trans ⟨standardContentWordPermutation, standardContentWordPermutation_injective n⟩⟩

end HigherSpecht.Lascoux
end
end CanonicalSource17

section CanonicalSource18
/- Source: HigherSpecht/LascouxShapeBalancing.lean -/



/-!
# The terminating crystal balancing map preserves actual tableau shapes

This strengthens the missing-letter induction with the same-shape property
proved for the literal signature operators.  The resulting embedding is
constructed without a path-independence assumption.  Its image has not yet
been identified with the required catabolizability class; that remaining
statement is not a field of the construction or a hidden theorem premise.
-/

noncomputable section
open scoped Classical BigOperators

namespace HigherSpecht.Lascoux

theorem transferContentWord_preserves_tableau (n : ℕ) (c : ℕ → ℕ) (i j : ℕ)
    (hi : 1 < c i) (hj : c j = 0) {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (u : WordOfContent n c)
    (hu : List.ofFn u.val = tableauWord T) :
    ∃ U : SemistandardYoungTableau mu,
      List.ofFn (transferContentWord n c i j hi hj u) = tableauWord U := by
  let E := wordBringPair n i j
  let z := (wordString 0 n).lowerValue (preparedContentWord n c i j hi hj u)
  obtain ⟨T₁, hT₁⟩ := (wordBringPair_preserves_tableau n i j).1 T u.val hu
  have hlow : (listString 0).lower (tableauWord T₁) = some (List.ofFn z) := by
    rw [← hT₁, listString_lower_ofFn]
    have hs := (wordString 0 n).lowerValue_spec (preparedContentWord n c i j hi hj u)
    change (wordString 0 n).lower (E u.val) = some z at hs
    rw [hs]
    rfl
  obtain ⟨T₂, hT₂⟩ := exists_tableau_of_word_lowering T₁ 0 hlow
  obtain ⟨U, hU⟩ := (wordBringPair_preserves_tableau n i j).2 T₂ z hT₂.symm
  exact ⟨U, hU⟩

def ContentEmbeddingPreservesShape {n : ℕ} {c d : ℕ → ℕ}
    (e : WordOfContent n c ↪ WordOfContent n d) : Prop :=
  ∀ {mu : YoungDiagram} (T : SemistandardYoungTableau mu) (u : WordOfContent n c),
    List.ofFn u.val = tableauWord T →
      ∃ U : SemistandardYoungTableau mu, List.ofFn (e u).val = tableauWord U

theorem ContentEmbeddingPreservesShape.refl (n : ℕ) (c : ℕ → ℕ) :
    ContentEmbeddingPreservesShape (Function.Embedding.refl (WordOfContent n c)) := by
  intro mu T u hu
  exact ⟨T, hu⟩

theorem ContentEmbeddingPreservesShape.trans {n : ℕ} {c d e : ℕ → ℕ}
    {f : WordOfContent n c ↪ WordOfContent n d}
    {g : WordOfContent n d ↪ WordOfContent n e}
    (hf : ContentEmbeddingPreservesShape f) (hg : ContentEmbeddingPreservesShape g) :
    ContentEmbeddingPreservesShape (f.trans g) := by
  intro mu T u hu
  obtain ⟨U, hU⟩ := hf T u hu
  exact hg U (f u) hU

theorem finiteContentTransferEmbedding_preserves_shape {n : ℕ}
    (c : Fin n → ℕ) (i j : Fin n) (hi : 1 < c i) (hj : c j = 0) :
    ContentEmbeddingPreservesShape (finiteContentTransferEmbedding c i j hi hj) := by
  intro mu T u hu
  simpa only [finiteContentTransferEmbedding_apply_val] using
    transferContentWord_preserves_tableau n (extendContent c) i.val j.val
      (by simpa using hi) (by simpa using hj) T u hu

/-- The concrete missing-letter induction now retains the actual tableau
shape, through the proved signature/recut bridge at every step. -/
theorem exists_shape_preserving_crystal_balancing (n : ℕ) (c : Fin n → ℕ)
    (hc : ∑ i, c i = n) :
    ∃ e : WordOfContent n (extendContent c) ↪ WordOfContent n (standardContent n),
      ContentEmbeddingPreservesShape e := by
  have aux : ∀ k : ℕ, ∀ c : Fin n → ℕ, (missingLetters c).card = k →
      (∑ i, c i = n) →
      ∃ e : WordOfContent n (extendContent c) ↪ WordOfContent n (standardContent n),
        ContentEmbeddingPreservesShape e := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro c hk hc
        by_cases hbound : ∀ i, c i ≤ 1
        · have hone := content_eq_one_of_le_one c hc hbound
          have heq : extendContent c = standardContent n := by
            funext a
            unfold extendContent standardContent
            split_ifs with ha
            · exact hone ⟨a, ha⟩
            · rfl
          rw [heq]
          exact ⟨Function.Embedding.refl _, ContentEmbeddingPreservesShape.refl _ _⟩
        · push_neg at hbound
          obtain ⟨i, hi⟩ := hbound
          obtain ⟨j, hj⟩ := exists_missing_of_repeated c hc i hi
          let d := finiteSplitContent c i j
          have hd : ∑ a, d a = n := (finiteSplitContent_sum c i j hi hj).trans hc
          have hlt : (missingLetters d).card < k := by
            rw [← hk]
            exact missingLetters_finiteSplitContent_card_lt c i j hi hj
          obtain ⟨e, he⟩ := ih (missingLetters d).card hlt d rfl hd
          refine ⟨(finiteContentTransferEmbedding c i j hi hj).trans e, ?_⟩
          exact ContentEmbeddingPreservesShape.trans
            (finiteContentTransferEmbedding_preserves_shape c i j hi hj) he
  exact aux _ c rfl hc

end HigherSpecht.Lascoux
end
end CanonicalSource18

section CanonicalSource19
/- Source: HigherSpecht/LascouxTransferCyclage.lean -/



/-!
# Ordinary cyclic rotation through a genuine content transfer

The reflection part commutes with literal rotation for every word.  The
noninvertible lowering part needs a nonzero leading letter.  For the actual
row reading of a tableau with at least two rows, that condition follows from
strict columns and is preserved by the same-shape reflection construction.

The resulting statement is an exact equality of the transformed words.  It
does not identify ordinary rotation with the decremented cyclic insertion
that defines catabolizability, and it does not assert the missing image
classification of the final balancing map.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

def PreservesWordRotation {n : ℕ} (e : (Fin n → ℕ) ≃ (Fin n → ℕ)) : Prop :=
  ∀ u v, List.ofFn (e v) = rotateHead (List.ofFn (e u)) ↔
    List.ofFn v = rotateHead (List.ofFn u)

theorem PreservesWordRotation.refl (n : ℕ) :
    PreservesWordRotation (Equiv.refl (Fin n → ℕ)) := fun _ _ => Iff.rfl

theorem PreservesWordRotation.trans {n : ℕ}
    {e f : (Fin n → ℕ) ≃ (Fin n → ℕ)}
    (he : PreservesWordRotation e) (hf : PreservesWordRotation f) :
    PreservesWordRotation (e.trans f) := by
  intro u v
  exact (hf (e u) (e v)).trans (he u v)

theorem PreservesWordRotation.symm {n : ℕ}
    {e : (Fin n → ℕ) ≃ (Fin n → ℕ)} (he : PreservesWordRotation e) :
    PreservesWordRotation e.symm := by
  intro u v
  simpa only [Equiv.apply_symm_apply] using (he (e.symm u) (e.symm v)).symm

theorem wordReflection_preserves_rotation (r n : ℕ) :
    PreservesWordRotation (wordReflection r n) := by
  have hf {u v : Fin n → ℕ}
      (h : List.ofFn v = rotateHead (List.ofFn u)) :
      List.ofFn (wordReflection r n v) =
        rotateHead (List.ofFn (wordReflection r n u)) := by
    rw [← listString_reflection_ofFn, h, reflection_rotateHead_all,
      listString_reflection_ofFn]
  intro u v
  constructor
  · intro h
    simpa only [wordReflection_involutive r n u, wordReflection_involutive r n v] using hf h
  · exact hf

theorem wordSwapZero_preserves_rotation (n j : ℕ) :
    PreservesWordRotation (wordSwapZero n j) := by
  induction j using Nat.twoStepInduction with
  | zero => exact PreservesWordRotation.refl n
  | one => exact wordReflection_preserves_rotation 0 n
  | more j ih ih' =>
      exact (wordReflection_preserves_rotation (j + 1) n).trans
        (ih'.trans (wordReflection_preserves_rotation (j + 1) n))

theorem wordContentSwap_preserves_rotation (n i j : ℕ) :
    PreservesWordRotation (wordContentSwap n i j) := by
  unfold wordContentSwap
  split_ifs
  · exact PreservesWordRotation.refl n
  · exact wordSwapZero_preserves_rotation n j
  · exact wordSwapZero_preserves_rotation n i
  · exact (wordSwapZero_preserves_rotation n i).trans
      ((wordSwapZero_preserves_rotation n j).trans
        (wordSwapZero_preserves_rotation n i))

theorem wordBringPair_preserves_rotation (n i j : ℕ) :
    PreservesWordRotation (wordBringPair n i j) :=
  (wordContentSwap_preserves_rotation n 0 i).trans
    (wordContentSwap_preserves_rotation n 1 (Equiv.swap 0 i j))

/-- The first letter of the actual bottom-to-top row reading is nonzero
when there is more than one row.  No alphabet normalization is assumed. -/
theorem tableauWord_head_ne_zero {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (hrows : 1 < mu.colLen 0) :
    ∃ a w, tableauWord T = a :: w ∧ a ≠ 0 := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (by omega : 0 < mu.colLen 0))
  have hrpos : 0 < r := by omega
  have hcell : (r, 0) ∈ mu := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hlen : 0 < (tableauRowWord T r).length := by
    rw [tableauRowWord_length]
    exact YoungDiagram.mem_iff_lt_rowLen.mp hcell
  cases hrow : tableauRowWord T r with
  | nil => simp only [hrow, List.length_nil] at hlen; omega
  | cons a tail =>
      have ha : a = T r 0 := by
        have he := tableauRowWord_getElem T r 0 hlen
        simpa only [hrow, List.getElem_cons_zero] using he
      refine ⟨a, tail ++ (descendingRows r).flatMap (tableauRowWord T), ?_, ?_⟩
      · simp only [tableauWord, hr, descendingRows, List.flatMap_cons, hrow,
          List.cons_append]
      · rw [ha]
        exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le (T 0 0))
          (T.col_strict hrpos hcell))

/-- Exact ordinary-rotation naturality for one explicit content split.
The source is the actual row reading of the tableau; the second word is
its literal rotation and need not itself be a tableau reading. -/
theorem transferContentWord_rotate_tableau (n : ℕ) (c : ℕ → ℕ) (i j : ℕ)
    (hi : 1 < c i) (hj : c j = 0) {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (hrows : 1 < mu.colLen 0)
    (u v : WordOfContent n c) (hu : List.ofFn u.val = tableauWord T)
    (hv : List.ofFn v.val = rotateHead (List.ofFn u.val)) :
    List.ofFn (transferContentWord n c i j hi hj v) =
      rotateHead (List.ofFn (transferContentWord n c i j hi hj u)) := by
  let E := wordBringPair n i j
  let zu := (wordString 0 n).lowerValue (preparedContentWord n c i j hi hj u)
  let zv := (wordString 0 n).lowerValue (preparedContentWord n c i j hi hj v)
  have hrot : List.ofFn (E v.val) = rotateHead (List.ofFn (E u.val)) :=
    (wordBringPair_preserves_rotation n i j u.val v.val).mpr hv
  obtain ⟨T₁, hT₁⟩ := (wordBringPair_preserves_tableau n i j).1 T u.val hu
  obtain ⟨a, tail, hword, ha⟩ := tableauWord_head_ne_zero T₁ hrows
  have hsource : List.ofFn (E u.val) = a :: tail := hT₁.trans hword
  have hcount : (a :: tail).count 1 < (a :: tail).count 0 := by
    have hzero := wordBringPair_zero n i j (distinct_of_split_counts hi hj) u.val
    have hone := wordBringPair_one n i j u.val
    rw [u.property i] at hzero
    rw [u.property j, hj] at hone
    change (List.ofFn (E u.val)).count 0 = c i at hzero
    change (List.ofFn (E u.val)).count 1 = 0 at hone
    rw [hsource] at hzero hone
    omega
  have hlu : (listString 0).lower (List.ofFn (E u.val)) = some (List.ofFn zu) := by
    rw [listString_lower_ofFn]
    have hs := (wordString 0 n).lowerValue_spec (preparedContentWord n c i j hi hj u)
    change (wordString 0 n).lower (E u.val) = some zu at hs
    rw [hs]
    rfl
  have hlv : (listString 0).lower (List.ofFn (E v.val)) = some (List.ofFn zv) := by
    rw [listString_lower_ofFn]
    have hs := (wordString 0 n).lowerValue_spec (preparedContentWord n c i j hi hj v)
    change (wordString 0 n).lower (E v.val) = some zv at hs
    rw [hs]
    rfl
  have hmid : List.ofFn zv = rotateHead (List.ofFn zu) := by
    have hc := firstLowering_rotateHead a tail ha hcount
    rw [← hsource, ← hrot, hlu, hlv, Option.map_some] at hc
    exact Option.some.inj hc
  exact ((wordBringPair_preserves_rotation n i j).symm zu zv).mpr hmid

end HigherSpecht.Lascoux
end
end CanonicalSource19

section CanonicalSource20
/- Source: HigherSpecht/LascouxBalancingCyclage.lean -/



/-!
# A terminating balancing map with its proved insertion and rotation data

The missing-letter induction now carries three properties of the actual
constructed embedding: preservation of tableau shape, preservation and
reflection of Knuth equivalence, and exact ordinary rotation on a tableau
row reading with at least two rows.  Each property is derived from the
literal reflection/lowering construction at every induction step.

No path independence or catabolizability image statement is a field of this
package.  Those conclusions require further insertion geometry.
-/

noncomputable section
open scoped Classical BigOperators

namespace HigherSpecht.Lascoux

def ContentEmbeddingPreservesKnuth {n : ℕ} {c d : ℕ → ℕ}
    (e : WordOfContent n c ↪ WordOfContent n d) : Prop :=
  ∀ u v, KnuthEquivalent (List.ofFn (e u).val) (List.ofFn (e v).val) ↔
    KnuthEquivalent (List.ofFn u.val) (List.ofFn v.val)

def ContentEmbeddingPreservesTableauRotation {n : ℕ} {c d : ℕ → ℕ}
    (e : WordOfContent n c ↪ WordOfContent n d) : Prop :=
  ∀ {mu : YoungDiagram} (T : SemistandardYoungTableau mu),
    1 < mu.colLen 0 → ∀ u v : WordOfContent n c,
    List.ofFn u.val = tableauWord T →
    List.ofFn v.val = rotateHead (List.ofFn u.val) →
    List.ofFn (e v).val = rotateHead (List.ofFn (e u).val)

structure CrystalBalancingProperties {n : ℕ} {c d : ℕ → ℕ}
    (e : WordOfContent n c ↪ WordOfContent n d) : Prop where
  shape : ContentEmbeddingPreservesShape e
  knuth : ContentEmbeddingPreservesKnuth e
  rotation : ContentEmbeddingPreservesTableauRotation e

theorem CrystalBalancingProperties.refl (n : ℕ) (c : ℕ → ℕ) :
    CrystalBalancingProperties (Function.Embedding.refl (WordOfContent n c)) where
  shape := ContentEmbeddingPreservesShape.refl n c
  knuth := fun _ _ => Iff.rfl
  rotation := by intro mu T hrows u v hu hv; exact hv

theorem CrystalBalancingProperties.trans {n : ℕ} {c d f : ℕ → ℕ}
    {e₁ : WordOfContent n c ↪ WordOfContent n d}
    {e₂ : WordOfContent n d ↪ WordOfContent n f}
    (h₁ : CrystalBalancingProperties e₁) (h₂ : CrystalBalancingProperties e₂) :
    CrystalBalancingProperties (e₁.trans e₂) where
  shape := ContentEmbeddingPreservesShape.trans h₁.shape h₂.shape
  knuth := by
    intro u v
    exact (h₂.knuth (e₁ u) (e₁ v)).trans (h₁.knuth u v)
  rotation := by
    intro mu T hrows u v hu hv
    obtain ⟨U, hU⟩ := h₁.shape T u hu
    exact h₂.rotation U hrows (e₁ u) (e₁ v) hU
      (h₁.rotation T hrows u v hu hv)

theorem finiteContentTransferEmbedding_properties {n : ℕ}
    (c : Fin n → ℕ) (i j : Fin n) (hi : 1 < c i) (hj : c j = 0) :
    CrystalBalancingProperties (finiteContentTransferEmbedding c i j hi hj) where
  shape := finiteContentTransferEmbedding_preserves_shape c i j hi hj
  knuth := by
    intro u v
    simpa only [finiteContentTransferEmbedding_apply_val] using
      transferContentWord_knuth_iff n (extendContent c) i.val j.val
        (by simpa using hi) (by simpa using hj) u v
  rotation := by
    intro mu T hrows u v hu hv
    simpa only [finiteContentTransferEmbedding_apply_val] using
      transferContentWord_rotate_tableau n (extendContent c) i.val j.val
        (by simpa using hi) (by simpa using hj) T hrows u v hu hv

/-- The actual finite balancing construction with all currently established
insertion/rotation properties.  There is no catabolizability premise. -/
theorem exists_crystal_balancing_with_rotation (n : ℕ) (c : Fin n → ℕ)
    (hc : ∑ i, c i = n) :
    ∃ e : WordOfContent n (extendContent c) ↪ WordOfContent n (standardContent n),
      CrystalBalancingProperties e := by
  have aux : ∀ k : ℕ, ∀ c : Fin n → ℕ, (missingLetters c).card = k →
      (∑ i, c i = n) →
      ∃ e : WordOfContent n (extendContent c) ↪ WordOfContent n (standardContent n),
        CrystalBalancingProperties e := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro c hk hc
        by_cases hbound : ∀ i, c i ≤ 1
        · have hone := content_eq_one_of_le_one c hc hbound
          have heq : extendContent c = standardContent n := by
            funext a
            unfold extendContent standardContent
            split_ifs with ha
            · exact hone ⟨a, ha⟩
            · rfl
          rw [heq]
          exact ⟨Function.Embedding.refl _, CrystalBalancingProperties.refl _ _⟩
        · push_neg at hbound
          obtain ⟨i, hi⟩ := hbound
          obtain ⟨j, hj⟩ := exists_missing_of_repeated c hc i hi
          let d := finiteSplitContent c i j
          have hd : ∑ a, d a = n := (finiteSplitContent_sum c i j hi hj).trans hc
          have hlt : (missingLetters d).card < k := by
            rw [← hk]
            exact missingLetters_finiteSplitContent_card_lt c i j hi hj
          obtain ⟨e, he⟩ := ih (missingLetters d).card hlt d rfl hd
          exact ⟨(finiteContentTransferEmbedding c i j hi hj).trans e,
            (finiteContentTransferEmbedding_properties c i j hi hj).trans he⟩
  exact aux _ c rfl hc

/-- Splitting a repeated letter into an absent letter does not enlarge an
existing positive bound on the content.  This is the precise numerical
invariant used when a restricted cocyclage ends east of that bound. -/
theorem finiteSplitContent_le_bound {n : ℕ} (c : Fin n → ℕ)
    (i j : Fin n) (m : ℕ) (hm : 0 < m) (hc : ∀ a, c a ≤ m) :
    ∀ a, finiteSplitContent c i j a ≤ m := by
  intro a
  by_cases haj : a = j
  · subst a
    simp only [finiteSplitContent, Function.update_self]
    omega
  · by_cases hai : a = i
    · subst a
      simp only [finiteSplitContent, Function.update_of_ne haj,
        Function.update_self]
      exact le_trans (Nat.sub_le _ _) (hc i)
    · simpa only [finiteSplitContent, Function.update_of_ne haj,
        Function.update_of_ne hai] using hc a

end HigherSpecht.Lascoux
end
end CanonicalSource20

section CanonicalSource21
/- Source: HigherSpecht/LascouxCrystalPrograms.lean -/



/-!
# Reified finite programs of the actual crystal operators

The alphabet bound and the word length are separate.  Thus the same
literal program can balance a smaller tableau while additional neutral
letters remain in a larger word.  Every instruction is either an actual
adjacent signature reflection or the already proved explicit repeated-
letter split.  No path, image, or neutral-letter transport conclusion is
assumed by the data type.
-/

noncomputable section
open scoped Classical BigOperators

namespace HigherSpecht.Lascoux

def castContentWord {N : ℕ} {c d : ℕ → ℕ} (h : c = d)
    (u : WordOfContent N c) : WordOfContent N d := h ▸ u

@[simp] theorem castContentWord_val {N : ℕ} {c d : ℕ → ℕ} (h : c = d)
    (u : WordOfContent N c) : (castContentWord h u).val = u.val := by
  cases h
  rfl

def reflectedContent (c : ℕ → ℕ) (r : ℕ) : ℕ → ℕ :=
  fun a => c (Equiv.swap r (r + 1) a)

def reflectionContentEmbedding (N : ℕ) (c : ℕ → ℕ) (r : ℕ) :
    WordOfContent N c ↪ WordOfContent N (reflectedContent c r) where
  toFun u := ⟨wordReflection r N u.val, by
    intro a
    rw [wordReflection_content]
    exact u.property _⟩
  inj' u v h := Subtype.ext ((wordReflection r N).injective (congrArg Subtype.val h))

theorem reflectionContentEmbedding_properties (N : ℕ) (c : ℕ → ℕ) (r : ℕ) :
    CrystalBalancingProperties (reflectionContentEmbedding N c r) where
  shape := by
    intro mu T u hu
    exact (wordReflection_preserves_tableau r N).1 T u.val hu
  knuth := by
    intro u v
    exact wordReflection_preserves_knuth r N u.val v.val
  rotation := by
    intro mu T hheight u v hu hv
    exact (wordReflection_preserves_rotation r N u.val v.val).mpr hv

theorem contentTransferEmbedding_properties (N : ℕ) (c : ℕ → ℕ) (i j : ℕ)
    (hi : 1 < c i) (hj : c j = 0) :
    CrystalBalancingProperties (contentTransferEmbedding N c i j hi hj) where
  shape := by
    intro mu T u hu
    exact transferContentWord_preserves_tableau N c i j hi hj T u hu
  knuth := transferContentWord_knuth_iff N c i j hi hj
  rotation := by
    intro mu T hheight u v hu hv
    exact transferContentWord_rotate_tableau N c i j hi hj T hheight u v hu hv

/-- A finite literal program using only letters strictly below `K`.
The source and target contents may additionally contain neutral letters
outside that alphabet; their behavior is proved separately. -/
inductive CrystalProgram (K : ℕ) : (ℕ → ℕ) → (ℕ → ℕ) → Type
  | nil (c : ℕ → ℕ) : CrystalProgram K c c
  | reflect {c d : ℕ → ℕ} (r : ℕ) (hr : r + 1 < K)
      (rest : CrystalProgram K (reflectedContent c r) d) : CrystalProgram K c d
  | split {c d : ℕ → ℕ} (i j : ℕ) (hiK : i < K) (hjK : j < K)
      (hi : 1 < c i) (hj : c j = 0)
      (rest : CrystalProgram K (splitContent c i j) d) : CrystalProgram K c d

namespace CrystalProgram

def castContents {K : ℕ} {c d c' d' : ℕ → ℕ}
    (P : CrystalProgram K c d) (hc : c = c') (hd : d = d') :
    CrystalProgram K c' d' := hc ▸ hd ▸ P

def embedding {K : ℕ} {c d : ℕ → ℕ} (P : CrystalProgram K c d) (N : ℕ) :
    WordOfContent N c ↪ WordOfContent N d :=
  match P with
  | .nil _ => Function.Embedding.refl _
  | .reflect r hr rest => (reflectionContentEmbedding N _ r).trans (rest.embedding N)
  | .split i j hiK hjK hi hj rest =>
      (contentTransferEmbedding N _ i j hi hj).trans (rest.embedding N)

theorem embedding_castContents_word {K N : ℕ} {c d c' d' : ℕ → ℕ}
    (P : CrystalProgram K c d) (hc : c = c') (hd : d = d')
    (u : WordOfContent N c) (v : WordOfContent N c')
    (huv : u.val = v.val) :
    ((P.castContents hc hd).embedding N v).val = (P.embedding N u).val := by
  subst c'
  subst d'
  have huv' : u = v := Subtype.ext huv
  subst v
  rfl

theorem properties {K : ℕ} {c d : ℕ → ℕ} (P : CrystalProgram K c d) (N : ℕ) :
    CrystalBalancingProperties (P.embedding N) := by
  induction P with
  | nil c => exact CrystalBalancingProperties.refl N c
  | reflect r hr rest ih => exact (reflectionContentEmbedding_properties N _ r).trans ih
  | split i j hiK hjK hi hj rest ih =>
      exact (contentTransferEmbedding_properties N _ i j hi hj).trans ih

def append {K : ℕ} {c d e : ℕ → ℕ}
    (P : CrystalProgram K c d) (Q : CrystalProgram K d e) : CrystalProgram K c e :=
  match P with
  | .nil _ => Q
  | .reflect r hr rest => .reflect r hr (rest.append Q)
  | .split i j hiK hjK hi hj rest => .split i j hiK hjK hi hj (rest.append Q)

theorem embedding_append {K : ℕ} {c d e : ℕ → ℕ}
    (P : CrystalProgram K c d) (Q : CrystalProgram K d e) (N : ℕ) :
    (P.append Q).embedding N = (P.embedding N).trans (Q.embedding N) := by
  induction P with
  | nil c => rfl
  | reflect r hr rest ih => simp only [append, embedding, ih]; rfl
  | split i j hiK hjK hi hj rest ih => simp only [append, embedding, ih]; rfl

def enlargeAlphabet {K L : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (hKL : K ≤ L) : CrystalProgram L c d :=
  match P with
  | .nil _ => .nil _
  | .reflect r hr rest => .reflect r (hr.trans_le hKL) (rest.enlargeAlphabet hKL)
  | .split i j hiK hjK hi hj rest =>
      .split i j (hiK.trans_le hKL) (hjK.trans_le hKL) hi hj (rest.enlargeAlphabet hKL)

theorem embedding_enlargeAlphabet {K L : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (hKL : K ≤ L) (N : ℕ) :
    (P.enlargeAlphabet hKL).embedding N = P.embedding N := by
  induction P with
  | nil c => rfl
  | reflect r hr rest ih => simp only [enlargeAlphabet, embedding, ih]
  | split i j hiK hjK hi hj rest ih => simp only [enlargeAlphabet, embedding, ih]

end CrystalProgram

/-- The missing-letter induction now returns the actual finite instruction
program, so its interpretation can be transported to a larger word. -/
theorem exists_crystal_balancing_program (K : ℕ) (c : Fin K → ℕ)
    (hc : ∑ i, c i = K) :
    Nonempty (CrystalProgram K (extendContent c) (standardContent K)) := by
  have aux : ∀ k : ℕ, ∀ c : Fin K → ℕ, (missingLetters c).card = k →
      (∑ i, c i = K) →
      Nonempty (CrystalProgram K (extendContent c) (standardContent K)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro c hk hc
        by_cases hbound : ∀ i, c i ≤ 1
        · have hone := content_eq_one_of_le_one c hc hbound
          have heq : extendContent c = standardContent K := by
            funext a
            unfold extendContent standardContent
            split_ifs with ha
            · exact hone ⟨a, ha⟩
            · rfl
          rw [heq]
          exact ⟨.nil _⟩
        · push_neg at hbound
          obtain ⟨i, hi⟩ := hbound
          obtain ⟨j, hj⟩ := exists_missing_of_repeated c hc i hi
          let d := finiteSplitContent c i j
          have hd : ∑ a, d a = K := (finiteSplitContent_sum c i j hi hj).trans hc
          have hlt : (missingLetters d).card < k := by
            rw [← hk]
            exact missingLetters_finiteSplitContent_card_lt c i j hi hj
          obtain ⟨P⟩ := ih (missingLetters d).card hlt d rfl hd
          have P' : CrystalProgram K (splitContent (extendContent c) i.val j.val)
              (standardContent K) := by
            simpa only [d, extend_finiteSplitContent] using P
          exact ⟨.split i.val j.val i.isLt j.isLt
            (by simpa using hi) (by simpa using hj) P'⟩
  exact aux _ c rfl hc

end HigherSpecht.Lascoux
end
end CanonicalSource21

section CanonicalSource22
/- Source: HigherSpecht/LascouxProgramContent.lean -/



/-!
# Content bounds and adding neutral letters to a literal program

The program acts below its fixed alphabet bound.  Adding a multiplicity
at that bound therefore preserves every instruction's genuine domain
condition.  This file constructs the lifted program and proves the
content invariants; commutation with deleting neutral letters is a
separate word-level theorem.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem reflectedContent_le_bound (c : ℕ → ℕ) (r m : ℕ)
    (hc : ∀ a, c a ≤ m) : ∀ a, reflectedContent c r a ≤ m :=
  fun a => hc _

theorem splitContent_le_bound (c : ℕ → ℕ) (i j m : ℕ)
    (hm : 0 < m) (hc : ∀ a, c a ≤ m) : ∀ a, splitContent c i j a ≤ m := by
  intro a
  by_cases haj : a = j
  · subst a
    simp only [splitContent, Function.update_self]
    omega
  · by_cases hai : a = i
    · subst a
      simp only [splitContent, Function.update_of_ne haj, Function.update_self]
      exact (Nat.sub_le _ _).trans (hc i)
    · simpa only [splitContent, Function.update_of_ne haj,
        Function.update_of_ne hai] using hc a

theorem CrystalProgram.content_le_bound {K : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (m : ℕ) (hm : 0 < m) (hc : ∀ a, c a ≤ m) :
    ∀ a, d a ≤ m := by
  revert hc
  induction P with
  | nil c => exact fun hc => hc
  | reflect r hr rest ih =>
      intro hc
      exact ih (reflectedContent_le_bound _ r m hc)
  | split i j hiK hjK hi hj rest ih =>
      intro hc
      exact ih (splitContent_le_bound _ i j m hm hc)

theorem CrystalProgram.content_outside {K : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (a : ℕ) (ha : K ≤ a) : d a = c a := by
  induction P with
  | nil c => rfl
  | reflect r hr rest ih =>
      rw [ih]
      unfold reflectedContent
      rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
  | split i j hiK hjK hi hj rest ih =>
      rw [ih]
      simp only [splitContent, Function.update_of_ne (by omega : a ≠ j),
        Function.update_of_ne (by omega : a ≠ i)]

def addCapContent (c : ℕ → ℕ) (K m : ℕ) : ℕ → ℕ :=
  fun a => c a + if a = K then m else 0

@[simp] theorem addCapContent_below (c : ℕ → ℕ) (K m a : ℕ) (ha : a < K) :
    addCapContent c K m a = c a := by simp [addCapContent, Nat.ne_of_lt ha]

theorem reflectedContent_addCap (c : ℕ → ℕ) (K m r : ℕ) (hr : r + 1 < K) :
    reflectedContent (addCapContent c K m) r =
      addCapContent (reflectedContent c r) K m := by
  funext a
  have hK : Equiv.swap r (r + 1) K = K :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have heq : Equiv.swap r (r + 1) a = K ↔ a = K := by
    constructor
    · intro h
      exact (Equiv.swap r (r + 1)).injective (h.trans hK.symm)
    · intro h
      simpa only [h] using hK
  simp only [reflectedContent, addCapContent, heq]

theorem splitContent_addCap (c : ℕ → ℕ) (K m i j : ℕ)
    (hi : i < K) (hj : j < K) :
    splitContent (addCapContent c K m) i j = addCapContent (splitContent c i j) K m := by
  funext a
  by_cases haj : a = j
  · subst a
    simp only [splitContent, Function.update_self, addCapContent,
      if_neg (Nat.ne_of_lt hj), Nat.add_zero]
  · by_cases hai : a = i
    · subst a
      simp only [splitContent, Function.update_of_ne haj, Function.update_self,
        addCapContent, if_neg (Nat.ne_of_lt hi), Nat.add_zero]
    · simp only [splitContent, Function.update_of_ne haj, Function.update_of_ne hai,
        addCapContent]

/-- The same actual instructions, interpreted with an additional neutral
letter at the alphabet bound.  The instruction conditions are re-proved
from their unchanged below-bound counts. -/
def CrystalProgram.addCap {K : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (m : ℕ) :
    CrystalProgram K (addCapContent c K m) (addCapContent d K m) := by
  induction P with
  | nil c => exact .nil _
  | @reflect c d r hr rest ih =>
      exact .reflect r hr
        (ih.castContents (reflectedContent_addCap c K m r hr).symm rfl)
  | @split c d i j hiK hjK hi hj rest ih =>
      exact .split i j hiK hjK
        (by simpa only [addCapContent_below c K m i hiK] using hi)
        (by simpa only [addCapContent_below c K m j hjK] using hj)
        (ih.castContents (splitContent_addCap c K m i j hiK hjK).symm rfl)

end HigherSpecht.Lascoux
end
end CanonicalSource22

section CanonicalSource23
/- Source: HigherSpecht/LascouxReflectionPrograms.lean -/



/-!
# Literal finite reflection programs and their inverses

The word length is independent of the alphabet bound.  These programs
are interpreted by the actual signature reflections, including on words
with repeated letters.  Reversing the instruction list is a genuine
inverse, so the saturated sweep can be undone after a separately proved
neutral-cap computation.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

def reflectionListContent (c : ℕ → ℕ) : List ℕ → (ℕ → ℕ)
  | [] => c
  | r :: rs => reflectionListContent (reflectedContent c r) rs

def reflectionListWord : List ℕ → List ℕ → List ℕ
  | [], w => w
  | r :: rs, w => reflectionListWord rs ((listString r).reflection w)

theorem reflectedContent_involutive (c : ℕ → ℕ) (r : ℕ) :
    reflectedContent (reflectedContent c r) r = c := by
  funext a
  simp only [reflectedContent, Equiv.swap_apply_self]

theorem reflectionListContent_append (c : ℕ → ℕ) (rs ts : List ℕ) :
    reflectionListContent c (rs ++ ts) =
      reflectionListContent (reflectionListContent c rs) ts := by
  induction rs generalizing c with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem reflectionListWord_append (rs ts : List ℕ) (w : List ℕ) :
    reflectionListWord (rs ++ ts) w =
      reflectionListWord ts (reflectionListWord rs w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem reflectionListContent_reverse (c : ℕ → ℕ) (rs : List ℕ) :
    reflectionListContent (reflectionListContent c rs) rs.reverse = c := by
  induction rs generalizing c with
  | nil => rfl
  | cons r rs ih =>
      simp only [reflectionListContent, List.reverse_cons,
        reflectionListContent_append, ih, reflectedContent_involutive]

theorem reflectionListWord_reverse (rs : List ℕ) (w : List ℕ) :
    reflectionListWord rs.reverse (reflectionListWord rs w) = w := by
  induction rs generalizing w with
  | nil => rfl
  | cons r rs ih =>
      simp only [reflectionListWord, List.reverse_cons,
        reflectionListWord_append, ih]
      exact (listString r).reflection_involutive w

def reflectionListProgram (K : ℕ) (c : ℕ → ℕ) (rs : List ℕ)
    (h : ∀ r ∈ rs, r + 1 < K) :
    CrystalProgram K c (reflectionListContent c rs) :=
  match rs with
  | [] => .nil c
  | r :: rs => .reflect r (h r (List.mem_cons_self ..))
      (reflectionListProgram K (reflectedContent c r) rs
        (fun t ht => h t (List.mem_cons_of_mem r ht)))

theorem reflectionListProgram_word (K N : ℕ) (c : ℕ → ℕ) (rs : List ℕ)
    (h : ∀ r ∈ rs, r + 1 < K) (u : WordOfContent N c) :
    List.ofFn ((reflectionListProgram K c rs h).embedding N u).val =
      reflectionListWord rs (List.ofFn u.val) := by
  induction rs generalizing c with
  | nil => rfl
  | cons r rs ih =>
      change List.ofFn ((reflectionListProgram K (reflectedContent c r) rs _).embedding N
        (reflectionContentEmbedding N c r u)).val = _
      rw [ih]
      change reflectionListWord rs (List.ofFn (wordReflection r N u.val)) =
        reflectionListWord rs ((listString r).reflection (List.ofFn u.val))
      exact congrArg (reflectionListWord rs) (listString_reflection_ofFn r N u.val).symm

theorem reflectionListWord_range (M : ℕ) (w : List ℕ) :
    reflectionListWord (List.range M) w = wordReflectionSweep M w := by
  induction M with
  | zero => rfl
  | succ M ih =>
      rw [List.range_succ, reflectionListWord_append, ih]
      rfl

def reflectionSweepContent (c : ℕ → ℕ) (M : ℕ) : ℕ → ℕ :=
  reflectionListContent c (List.range M)

def reflectionSweepProgram (M : ℕ) (c : ℕ → ℕ) :
    CrystalProgram (M + 1) c (reflectionSweepContent c M) :=
  reflectionListProgram (M + 1) c (List.range M)
    (fun r hr => by have := List.mem_range.mp hr; omega)

theorem reflectionSweepProgram_word (M N : ℕ) (c : ℕ → ℕ)
    (u : WordOfContent N c) :
    List.ofFn ((reflectionSweepProgram M c).embedding N u).val =
      wordReflectionSweep M (List.ofFn u.val) := by
  change List.ofFn ((reflectionListProgram (M + 1) c (List.range M)
    (fun r hr => by have := List.mem_range.mp hr; omega)).embedding N u).val = _
  exact (reflectionListProgram_word (M + 1) N c (List.range M)
    (fun r hr => by have := List.mem_range.mp hr; omega) u).trans
      (reflectionListWord_range M (List.ofFn u.val))

def inverseReflectionSweepProgram (M : ℕ) (c : ℕ → ℕ) :
    CrystalProgram (M + 1) (reflectionSweepContent c M) c := by
  have P := reflectionListProgram (M + 1) (reflectionSweepContent c M)
    (List.range M).reverse
    (fun r hr => by have := List.mem_range.mp (List.mem_reverse.mp hr); omega)
  exact P.castContents rfl (by
    simpa only [reflectionSweepContent] using
      reflectionListContent_reverse c (List.range M))

theorem inverseReflectionSweepProgram_word (M N : ℕ) (c : ℕ → ℕ)
    (u : WordOfContent N (reflectionSweepContent c M)) :
    List.ofFn ((inverseReflectionSweepProgram M c).embedding N u).val =
      reflectionListWord (List.range M).reverse (List.ofFn u.val) := by
  unfold inverseReflectionSweepProgram
  rw [CrystalProgram.embedding_castContents_word _ rfl _ u u rfl]
  exact reflectionListProgram_word (M + 1) N
    (reflectionSweepContent c M) (List.range M).reverse _ u

theorem inverseReflectionSweepProgram_after (M N : ℕ) (c : ℕ → ℕ)
    (u : WordOfContent N c) :
    (inverseReflectionSweepProgram M c).embedding N
      ((reflectionSweepProgram M c).embedding N u) = u := by
  apply Subtype.ext
  apply List.ofFn_injective
  rw [inverseReflectionSweepProgram_word, reflectionSweepProgram_word,
    ← reflectionListWord_range, reflectionListWord_reverse]

theorem reflectionSweepContent_apply (c : ℕ → ℕ) (M a : ℕ) :
    reflectionSweepContent c M a = c ((alphabetSweep M).symm a) := by
  induction M generalizing a with
  | zero => rfl
  | succ M ih =>
      simp only [reflectionSweepContent, List.range_succ,
        reflectionListContent_append, reflectionListContent, reflectedContent]
      rw [show reflectionListContent c (List.range M) = reflectionSweepContent c M from rfl,
        ih]
      rfl

theorem reflectionSweepContent_below (c : ℕ → ℕ) {M a : ℕ} (ha : a < M) :
    reflectionSweepContent c M a = c (a + 1) := by
  rw [reflectionSweepContent_apply]
  have h := alphabetSweep_of_pos_le (by omega : 0 < a + 1) (by omega : a + 1 ≤ M)
  have he : alphabetSweep M (a + 1) = a := by simpa only [Nat.add_sub_cancel] using h
  exact congrArg c ((alphabetSweep M).symm_apply_eq.mpr he.symm)

@[simp] theorem reflectionSweepContent_cap (c : ℕ → ℕ) (M : ℕ) :
    reflectionSweepContent c M M = c 0 := by
  rw [reflectionSweepContent_apply]
  exact congrArg c ((alphabetSweep M).symm_apply_eq.mpr (alphabetSweep_zero M).symm)

theorem reflectionSweepContent_above (c : ℕ → ℕ) {M a : ℕ} (ha : M < a) :
    reflectionSweepContent c M a = c a := by
  rw [reflectionSweepContent_apply]
  exact congrArg c ((alphabetSweep M).symm_apply_eq.mpr (alphabetSweep_of_gt ha).symm)

def firstContentTail (M : ℕ) (c : ℕ → ℕ) (a : ℕ) : ℕ :=
  if a < M then c (a + 1) else 0

def zeroAndSingletonContent (M m : ℕ) (a : ℕ) : ℕ :=
  if a = 0 then m else if a ≤ M then 1 else 0

theorem reflectionSweepContent_eq_addCap (c : ℕ → ℕ) (M : ℕ)
    (hc : ∀ a, M < a → c a = 0) :
    reflectionSweepContent c M = addCapContent (firstContentTail M c) M (c 0) := by
  funext a
  by_cases ha : a < M
  · rw [reflectionSweepContent_below c ha]
    simp only [addCapContent_below _ M (c 0) a ha, firstContentTail, if_pos ha]
  · by_cases he : a = M
    · subst a
      simp only [reflectionSweepContent_cap, addCapContent, firstContentTail,
        lt_self_iff_false, if_false, if_true, Nat.zero_add]
    · have hgt : M < a := by omega
      rw [reflectionSweepContent_above c hgt, hc a hgt]
      simp only [addCapContent, firstContentTail, if_neg ha, if_neg he, Nat.add_zero]

theorem reflectionSweepContent_zeroAndSingleton (M m : ℕ) :
    reflectionSweepContent (zeroAndSingletonContent M m) M =
      addCapContent (standardContent M) M m := by
  have hsupport : ∀ a, M < a → zeroAndSingletonContent M m a = 0 := by
    intro a ha
    simp only [zeroAndSingletonContent, if_neg (by omega : a ≠ 0),
      if_neg (by omega : ¬ a ≤ M)]
  rw [reflectionSweepContent_eq_addCap _ M hsupport]
  congr 1
  · funext a
    unfold firstContentTail standardContent
    split_ifs with ha
    · simp only [zeroAndSingletonContent, Nat.add_one_ne_zero, if_false,
        if_pos (by omega : a + 1 ≤ M)]
    · rfl

end HigherSpecht.Lascoux
end
end CanonicalSource23

section CanonicalSource24
/- Source: HigherSpecht/LascouxNeutralProgram.lean -/



/-!
# The actual bounded program commutes with erasing its neutral cap

Both sides are interpreted by the same genuine finite-word operators,
possibly at different word lengths.  The added cap is a real letter of
the larger tableau, not an assumed independent or formal marker.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem lowerValue_preserves_filter (K N L : ℕ) (hK : 1 < K)
    (u : {w : Fin N → ℕ // 0 < (wordString 0 N).phi w})
    (v : {w : Fin L → ℕ // 0 < (wordString 0 L).phi w})
    (hfilter : alphabetFilter K (List.ofFn u.val) = List.ofFn v.val) :
    alphabetFilter K (List.ofFn ((wordString 0 N).lowerValue u)) =
      List.ofFn ((wordString 0 L).lowerValue v) := by
  have h := listString_lower_filter K 0 hK (List.ofFn u.val)
  rw [hfilter, listString_lower_ofFn, listString_lower_ofFn,
    (wordString 0 N).lowerValue_spec u, (wordString 0 L).lowerValue_spec v,
    Option.map_some, Option.map_some, Option.map_some] at h
  exact (Option.some.inj h).symm

theorem transferContentWord_preserves_filter (K N L : ℕ) (c d : ℕ → ℕ)
    (i j : ℕ) (hiK : i < K) (hjK : j < K)
    (hic : 1 < c i) (hjc : c j = 0) (hid : 1 < d i) (hjd : d j = 0)
    (u : WordOfContent N c) (v : WordOfContent L d)
    (hfilter : alphabetFilter K (List.ofFn u.val) = List.ofFn v.val) :
    alphabetFilter K (List.ofFn (transferContentWord N c i j hic hjc u)) =
      List.ofFn (transferContentWord L d i j hid hjd v) := by
  have hij := distinct_of_split_counts hic hjc
  have hK : 1 < K := by omega
  have hpair := wordBringPair_preserves_filter K i j N L hiK hjK hij
  have hp := (hpair u.val v.val).mpr hfilter
  have hl := lowerValue_preserves_filter K N L hK
    (preparedContentWord N c i j hic hjc u)
    (preparedContentWord L d i j hid hjd v) hp
  exact (hpair.symm _ _).mpr hl

/-- The same actual finite program on the capped and uncapped words.
The hypotheses merely identify those literal input words by deletion. -/
theorem CrystalProgram.addCap_filter {K : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (m N L : ℕ)
    (u : WordOfContent N (addCapContent c K m)) (v : WordOfContent L c)
    (hfilter : alphabetFilter K (List.ofFn u.val) = List.ofFn v.val) :
    alphabetFilter K (List.ofFn ((P.addCap m).embedding N u).val) =
      List.ofFn (P.embedding L v).val := by
  induction P with
  | nil c => exact hfilter
  | @reflect c d r hr rest ih =>
      have hstep := (wordReflection_preserves_filter K r N L hr u.val v.val).mpr hfilter
      let u₁ := reflectionContentEmbedding N (addCapContent c K m) r u
      let v₁ := reflectionContentEmbedding L c r v
      have hcast : reflectedContent (addCapContent c K m) r =
          addCapContent (reflectedContent c r) K m := reflectedContent_addCap c K m r hr
      let hu₁ : WordOfContent N (addCapContent (reflectedContent c r) K m) :=
        castContentWord hcast u₁
      have hfilter₁ : alphabetFilter K (List.ofFn hu₁.val) = List.ofFn v₁.val := by
        rw [show hu₁.val = u₁.val from castContentWord_val hcast u₁]
        change alphabetFilter K (List.ofFn (wordReflection r N u.val)) =
          List.ofFn (wordReflection r L v.val)
        exact hstep
      change alphabetFilter K (List.ofFn
        (((rest.addCap m).castContents hcast.symm rfl).embedding N u₁).val) =
        List.ofFn (rest.embedding L v₁).val
      rw [CrystalProgram.embedding_castContents_word (rest.addCap m) hcast.symm rfl
        hu₁ u₁ (castContentWord_val hcast u₁)]
      exact ih hu₁ v₁ hfilter₁
  | @split c d i j hiK hjK hi hj rest ih =>
      have hi' : 1 < addCapContent c K m i := by
        simpa only [addCapContent_below c K m i hiK] using hi
      have hj' : addCapContent c K m j = 0 := by
        simpa only [addCapContent_below c K m j hjK] using hj
      have hstep := transferContentWord_preserves_filter K N L
        (addCapContent c K m) c i j hiK hjK hi' hj' hi hj u v hfilter
      let u₁ := contentTransferEmbedding N (addCapContent c K m) i j hi' hj' u
      let v₁ := contentTransferEmbedding L c i j hi hj v
      have hcast : splitContent (addCapContent c K m) i j =
          addCapContent (splitContent c i j) K m := splitContent_addCap c K m i j hiK hjK
      let hu₁ : WordOfContent N (addCapContent (splitContent c i j) K m) :=
        castContentWord hcast u₁
      have hfilter₁ : alphabetFilter K (List.ofFn hu₁.val) = List.ofFn v₁.val := by
        rw [show hu₁.val = u₁.val from castContentWord_val hcast u₁]
        change alphabetFilter K (List.ofFn
          (transferContentWord N (addCapContent c K m) i j hi' hj' u)) =
          List.ofFn (transferContentWord L c i j hi hj v)
        exact hstep
      change alphabetFilter K (List.ofFn
        (((rest.addCap m).castContents hcast.symm rfl).embedding N u₁).val) =
        List.ofFn (rest.embedding L v₁).val
      rw [CrystalProgram.embedding_castContents_word (rest.addCap m) hcast.symm rfl
        hu₁ u₁ (castContentWord_val hcast u₁)]
      exact ih hu₁ v₁ hfilter₁

end HigherSpecht.Lascoux
end
end CanonicalSource24

section CanonicalSource25
/- Source: HigherSpecht/LascouxRecursiveBase.lean -/



/-!
# The actual recursive program at a saturated first row

The first row is swept to a neutral maximal letter, the genuine smaller
program acts on the remaining tableau, and the sweep is undone.  The
output is exactly a zero first row followed by the smaller output with
all its entries increased by one.  This is a proved property of a literal
finite program, not a recursive image condition built into a definition.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

def recursiveSaturatedProgram (M m : ℕ) (c : ℕ → ℕ)
    (hc0 : c 0 = m) (hc : ∀ a, M < a → c a = 0)
    (P : CrystalProgram M (firstContentTail M c) (standardContent M)) :
    CrystalProgram (M + 1) c (zeroAndSingletonContent M m) := by
  have hs : reflectionSweepContent c M = addCapContent (firstContentTail M c) M m := by
    rw [reflectionSweepContent_eq_addCap c M hc, hc0]
  have ht : reflectionSweepContent (zeroAndSingletonContent M m) M =
      addCapContent (standardContent M) M m := reflectionSweepContent_zeroAndSingleton M m
  let middle := ((P.addCap m).enlargeAlphabet (Nat.le_succ M)).castContents hs.symm ht.symm
  exact (reflectionSweepProgram M c).append
    (middle.append (inverseReflectionSweepProgram M (zeroAndSingletonContent M m)))

theorem tableau_entry_mem_word {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (i j : ℕ) (hij : (i, j) ∈ mu) : T i j ∈ tableauWord T := by
  apply List.count_pos_iff.mp
  rw [tableauWord_count_eq_contentCells]
  exact Finset.card_pos.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨hij, rfl⟩⟩

theorem tableau_bound_of_word_content {N M : ℕ} {c : ℕ → ℕ}
    {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (u : WordOfContent N c) (hu : List.ofFn u.val = tableauWord T)
    (hc : ∀ a, M < a → c a = 0) :
    ∀ i j, (i, j) ∈ mu → T i j ≤ M := by
  intro i j hij
  have hmem := tableau_entry_mem_word T i j hij
  rw [← hu] at hmem
  have hp : 0 < wordContent u.val (T i j) := List.count_pos_iff.mpr hmem
  rw [u.property] at hp
  by_contra h
  rw [hc (T i j) (Nat.lt_of_not_ge h)] at hp
  exact (Nat.lt_irrefl 0) hp

theorem tableau_standardContent_bound {M : ℕ} {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (u : WordOfContent M (standardContent M))
    (hu : List.ofFn u.val = tableauWord T) :
    ∀ i j, (i, j) ∈ mu → T i j < M := by
  intro i j hij
  have hmem := tableau_entry_mem_word T i j hij
  rw [← hu] at hmem
  have hp : 0 < wordContent u.val (T i j) := List.count_pos_iff.mpr hmem
  rw [u.property] at hp
  by_contra h
  simp only [standardContent, if_neg h] at hp
  exact (Nat.lt_irrefl 0) hp

theorem recursiveSaturatedProgram_word (M m N : ℕ) (c : ℕ → ℕ)
    (hc0 : c 0 = m) (hc : ∀ a, M < a → c a = 0)
    (P : CrystalProgram M (firstContentTail M c) (standardContent M))
    {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0)
    (u : WordOfContent N c) (hu : List.ofFn u.val = tableauWord T)
    (v : WordOfContent M (firstContentTail M c))
    (hv : List.ofFn v.val = tableauWord (firstRowTailPred T))
    (Q : SemistandardYoungTableau (firstRowTail mu))
    (hQ : List.ofFn (P.embedding M v).val = tableauWord Q) :
    List.ofFn ((recursiveSaturatedProgram M m c hc0 hc P).embedding N u).val =
      tableauWord (prependZeroRow Q) := by
  have hsource : reflectionSweepContent c M =
      addCapContent (firstContentTail M c) M m := by
    rw [reflectionSweepContent_eq_addCap c M hc, hc0]
  have htarget : reflectionSweepContent (zeroAndSingletonContent M m) M =
      addCapContent (standardContent M) M m := reflectionSweepContent_zeroAndSingleton M m
  let u₁ := (reflectionSweepProgram M c).embedding N u
  let u₁' := castContentWord hsource u₁
  let u₂ := (P.addCap m).embedding N u₁'
  let u₂' := castContentWord htarget.symm u₂
  have hu₁ : List.ofFn u₁.val = tableauWord (saturatedSweep T M) := by
    rw [reflectionSweepProgram_word, hu, saturatedSweep_word]
  have hTbound := tableau_bound_of_word_content T u hu hc
  have hfilter₁ : alphabetFilter M (List.ofFn u₁'.val) = List.ofFn v.val := by
    rw [castContentWord_val, hu₁, hv]
    exact alphabetFilter_saturatedSweep T hs M hTbound
  have hfilter₂ : alphabetFilter M (List.ofFn u₂.val) = tableauWord Q := by
    rw [← hQ]
    exact P.addCap_filter m N M u₁' v hfilter₁
  obtain ⟨V, hV⟩ := ((P.addCap m).properties N).shape (saturatedSweep T M) u₁'
    (by rw [castContentWord_val]; exact hu₁)
  have hVbound : ∀ i j, (i, j) ∈ mu → V i j ≤ M := by
    apply tableau_bound_of_word_content V u₂ hV
    intro a ha
    simp only [addCapContent, standardContent, if_neg (by omega : ¬ a < M),
      if_neg (by omega : a ≠ M), Nat.add_zero]
  have hQbound := tableau_standardContent_bound Q (P.embedding M v) hQ
  have hRbound := prependZeroRow_bound Q M hQbound
  have hVeq : V = saturatedSweep (prependZeroRow Q) M := by
    apply tableau_eq_of_alphabetFilter V (saturatedSweep (prependZeroRow Q) M) M
      hVbound (saturatedSweep_bound _ (prependZeroRow_saturated Q) M hRbound)
    rw [← hV, hfilter₂, alphabetFilter_saturatedSweep _ (prependZeroRow_saturated Q) M hRbound,
      firstRowTailPred_prependZeroRow]
  have hu₂ : List.ofFn u₂'.val =
      wordReflectionSweep M (tableauWord (prependZeroRow Q)) := by
    rw [castContentWord_val, hV, hVeq, saturatedSweep_word]
  have hfinal : List.ofFn ((inverseReflectionSweepProgram M
      (zeroAndSingletonContent M m)).embedding N u₂').val = tableauWord (prependZeroRow Q) := by
    rw [inverseReflectionSweepProgram_word, hu₂, ← reflectionListWord_range,
      reflectionListWord_reverse]
  have hmid :
      (((P.addCap m).enlargeAlphabet (Nat.le_succ M)).castContents
        hsource.symm htarget.symm).embedding N u₁ = u₂' := by
    apply Subtype.ext
    rw [CrystalProgram.embedding_castContents_word _ hsource.symm htarget.symm u₁' u₁
      (castContentWord_val hsource u₁)]
    rw [CrystalProgram.embedding_enlargeAlphabet]
    exact (castContentWord_val htarget.symm u₂).symm
  simpa only [recursiveSaturatedProgram, CrystalProgram.embedding_append,
    Function.Embedding.trans_apply, hmid, u₁] using hfinal

end HigherSpecht.Lascoux
end
end CanonicalSource25

section CanonicalSource26
/- Source: HigherSpecht/LascouxAlphabetShift.lean -/



/-!
# Shifting a supported positive alphabet by actual crystal reflections

A descending sweep moves an empty alphabet position past the letters
below it.  When the upper letter is absent, the exact signature reflection
changes every occurrence of the lower letter and no other position.
Iterating these proved sweeps fixes zero and shifts every positive letter
by a prescribed amount.  The resulting map is a literal `CrystalProgram`;
the entrywise renaming formula is a conclusion about that program.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

/-- The pointwise formula holds because the upper letter is absent, not
because crystal reflections are generally alphabet renamings. -/
theorem wordReflection_empty_upper (r N : ℕ) (u : Fin N → ℕ)
    (hu : wordContent u (r + 1) = 0) (i : Fin N) :
    wordReflection r N u i = if u i = r then r + 1 else u i := by
  have hcount : (List.ofFn u).count (r + 1) ≤ (List.ofFn u).count r := by
    change wordContent u (r + 1) ≤ wordContent u r
    rw [hu]
    exact Nat.zero_le _
  have hlocal := wordReflection_lowerOnly_of_count_ge r N u hcount i
  have hout : wordContent (wordReflection r N u) r = 0 := by
    rw [wordReflection_content, Equiv.swap_apply_left]
    exact hu
  have hne : wordReflection r N u i ≠ r := by
    intro h
    exact (List.not_mem_of_count_eq_zero hout)
      (List.mem_ofFn.mpr ⟨i, h⟩)
  by_cases hi : u i = r
  · rw [if_pos hi]
    rcases hlocal with hsame | ⟨_, hchanged⟩
    · exact (hne (hsame.trans hi)).elim
    · exact hchanged
  · rw [if_neg hi]
    rcases hlocal with hsame | ⟨hbad, _⟩
    · exact hsame
    · exact (hi hbad).elim

/-- Contents after reflections `L, L-1, ..., 1`, in that actual order. -/
def gapSlideContent : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0, c => c
  | L + 1, c => gapSlideContent L (reflectedContent c (L + 1))

def gapSlideProgram {K : ℕ} (L : ℕ) (c : ℕ → ℕ) (hK : L + 1 < K) :
    CrystalProgram K c (gapSlideContent L c) :=
  match L with
  | 0 => .nil c
  | L + 1 => .reflect (L + 1) hK
      (gapSlideProgram L (reflectedContent c (L + 1)) (by omega))

theorem gapSlideContent_apply (L : ℕ) (c : ℕ → ℕ) (a : ℕ) :
    gapSlideContent L c a =
      if a = 0 then c 0 else if a = 1 then c (L + 1)
      else if a ≤ L + 1 then c (a - 1) else c a := by
  induction L generalizing c a with
  | zero =>
      simp only [gapSlideContent, Nat.zero_add]
      split_ifs <;> simp_all <;> omega
  | succ L ih =>
      rw [gapSlideContent, ih]
      by_cases ha0 : a = 0
      · subst a
        simp [reflectedContent, Equiv.swap_apply_def]
      · by_cases ha1 : a = 1
        · subst a
          simp [reflectedContent, Nat.add_assoc]
        · by_cases ha : a ≤ L + 1
          · have hsmall : a - 1 ≠ L + 1 := by omega
            have hsmall' : a - 1 ≠ L + 1 + 1 := by omega
            have ha' : a ≤ L + 1 + 1 := by omega
            simp [ha0, ha1, ha, ha', reflectedContent,
              Equiv.swap_apply_of_ne_of_ne hsmall hsmall']
          · by_cases ha' : a = L + 1 + 1
            · subst a
              simp [reflectedContent, Nat.add_assoc]
            · have hlarge : ¬ a ≤ L + 1 + 1 := by omega
              have hne : a ≠ L + 1 := by omega
              simp [ha0, ha1, ha, hlarge, reflectedContent,
                Equiv.swap_apply_of_ne_of_ne hne ha']

theorem gapSlideProgram_apply {K : ℕ} (L : ℕ) (c : ℕ → ℕ)
    (hK : L + 1 < K) (hgap : c (L + 1) = 0)
    (N : ℕ) (u : WordOfContent N c) (i : Fin N) :
    ((gapSlideProgram L c hK).embedding N u).val i =
      if 0 < u.val i ∧ u.val i ≤ L then u.val i + 1 else u.val i := by
  induction L generalizing c u with
  | zero =>
      change u.val i = if 0 < u.val i ∧ u.val i ≤ 0 then u.val i + 1 else u.val i
      rw [if_neg (by omega : ¬ (0 < u.val i ∧ u.val i ≤ 0))]
  | succ L ih =>
      change ((gapSlideProgram L (reflectedContent c (L + 1)) _).embedding N
        (reflectionContentEmbedding N c (L + 1) u)).val i = _
      have hgap' : reflectedContent c (L + 1) (L + 1) = 0 := by
        simpa only [reflectedContent, Equiv.swap_apply_left] using hgap
      rw [ih _ _ hgap']
      have hwordgap : wordContent u.val (L + 1 + 1) = 0 :=
        (u.property _).trans hgap
      change (if 0 < wordReflection (L + 1) N u.val i ∧
          wordReflection (L + 1) N u.val i ≤ L
        then wordReflection (L + 1) N u.val i + 1
        else wordReflection (L + 1) N u.val i) = _
      rw [wordReflection_empty_upper (L + 1) N u.val hwordgap i]
      split_ifs <;> omega

def positiveShift (s a : ℕ) : ℕ := if a = 0 then 0 else a + s

def positiveShiftContent (c : ℕ → ℕ) (s a : ℕ) : ℕ :=
  if a = 0 then c 0 else if s < a then c (a - s) else 0

@[simp] theorem positiveShiftContent_zero (c : ℕ → ℕ) :
    positiveShiftContent c 0 = c := by
  funext a
  by_cases ha : a = 0
  · simp [positiveShiftContent, ha]
  · simp [positiveShiftContent, ha, Nat.pos_of_ne_zero ha]

theorem positiveShiftContent_support (c : ℕ → ℕ) (L s : ℕ)
    (hc : ∀ a, L < a → c a = 0) :
    ∀ a, L + s < a → positiveShiftContent c s a = 0 := by
  intro a ha
  have h0 : a ≠ 0 := by omega
  have hs : s < a := by omega
  have hL : L < a - s := by omega
  simp only [positiveShiftContent, if_neg h0, if_pos hs, hc _ hL]

theorem gapSlideContent_eq_positiveShift (c : ℕ → ℕ) (L : ℕ)
    (hc : ∀ a, L < a → c a = 0) :
    gapSlideContent L c = positiveShiftContent c 1 := by
  funext a
  rw [gapSlideContent_apply]
  by_cases ha0 : a = 0
  · simp [positiveShiftContent, ha0]
  · by_cases ha1 : a = 1
    · simp [positiveShiftContent, ha1, hc _ (Nat.lt_succ_self L)]
    · have h1 : 1 < a := by omega
      by_cases ha : a ≤ L + 1
      · simp [positiveShiftContent, ha0, ha1, h1, ha]
      · have hLa : L < a := by omega
        have hpred : L < a - 1 := by omega
        simp [positiveShiftContent, ha0, ha1, h1, ha, hc _ hLa, hc _ hpred]

theorem positiveShiftContent_one_comp (c : ℕ → ℕ) (s : ℕ) :
    positiveShiftContent (positiveShiftContent c s) 1 =
      positiveShiftContent c (s + 1) := by
  funext a
  by_cases ha0 : a = 0
  · simp [positiveShiftContent, ha0]
  · by_cases ha1 : a = 1
    · have hs : ¬ s + 1 < 1 := by omega
      simp [positiveShiftContent, ha1, hs]
    · have h1 : 1 < a := by omega
      have hpred : a - 1 ≠ 0 := by omega
      have hcond : s < a - 1 ↔ s + 1 < a := by omega
      have hsub : a - 1 - s = a - (s + 1) := by omega
      simp only [positiveShiftContent, if_neg ha0, if_pos h1,
        if_neg hpred, hcond, hsub]

theorem entry_le_of_supported_content {N L : ℕ} {c : ℕ → ℕ}
    (hc : ∀ a, L < a → c a = 0) (u : WordOfContent N c) (i : Fin N) :
    u.val i ≤ L := by
  by_contra h
  have hz : (List.ofFn u.val).count (u.val i) = 0 :=
    (u.property _).trans (hc _ (Nat.lt_of_not_ge h))
  exact (List.not_mem_of_count_eq_zero hz) (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- A literal reflection program realizes the positive alphabet shift,
uniformly for every word length and every word of the stated content. -/
theorem exists_positiveShiftProgram (L s : ℕ) (c : ℕ → ℕ)
    (hc : ∀ a, L < a → c a = 0) :
    ∃ P : CrystalProgram (L + s + 1) c (positiveShiftContent c s),
      ∀ (N : ℕ) (u : WordOfContent N c) (i : Fin N),
        (P.embedding N u).val i = positiveShift s (u.val i) := by
  induction s with
  | zero =>
      rw [positiveShiftContent_zero]
      refine ⟨.nil c, ?_⟩
      intro N u i
      change u.val i = positiveShift 0 (u.val i)
      simp [positiveShift]
  | succ s ih =>
      obtain ⟨P, hP⟩ := ih
      have hc' := positiveShiftContent_support c L s hc
      have htarget : gapSlideContent (L + s) (positiveShiftContent c s) =
          positiveShiftContent c (s + 1) := by
        rw [gapSlideContent_eq_positiveShift _ _ hc', positiveShiftContent_one_comp]
      rw [← htarget]
      let Q := gapSlideProgram (K := L + (s + 1) + 1) (L + s)
        (positiveShiftContent c s) (by omega)
      refine ⟨(P.enlargeAlphabet (by omega)).append Q, ?_⟩
      intro N u i
      rw [CrystalProgram.embedding_append, CrystalProgram.embedding_enlargeAlphabet]
      change (Q.embedding N (P.embedding N u)).val i = _
      rw [gapSlideProgram_apply _ _ _ (hc' _ (by omega)), hP]
      have hu := entry_le_of_supported_content hc u i
      by_cases hz : u.val i = 0
      · simp [positiveShift, hz]
      · have hpos : 0 < u.val i + s := by omega
        have hle : u.val i + s ≤ L + s := by omega
        simp only [positiveShift, if_neg hz,
          if_pos (show 0 < u.val i + s ∧ u.val i + s ≤ L + s from ⟨hpos, hle⟩)]
        omega

end HigherSpecht.Lascoux
end
end CanonicalSource26

section CanonicalSource27
/- Source: HigherSpecht/LascouxProgramCoordinates.lean -/



/-!
# Coordinate preservation outside a crystal program's alphabet

Every actual instruction either leaves a position unchanged or changes it
between two letters below the program's alphabet bound.  This is proved
for the reflection conjugations inside a split as well as for the first
lowering.  Consequently neutral letters retain their values and positions.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

def AlphabetRelated (K a b : ℕ) : Prop := b = a ∨ a < K ∧ b < K

theorem AlphabetRelated.refl (K a : ℕ) : AlphabetRelated K a a := .inl rfl

theorem AlphabetRelated.symm {K a b : ℕ} (h : AlphabetRelated K a b) :
    AlphabetRelated K b a := by
  rcases h with h | ⟨ha, hb⟩
  · exact .inl h.symm
  · exact .inr ⟨hb, ha⟩

theorem AlphabetRelated.trans {K a b c : ℕ}
    (hab : AlphabetRelated K a b) (hbc : AlphabetRelated K b c) :
    AlphabetRelated K a c := by
  rcases hab with rfl | ⟨ha, hb⟩
  · exact hbc
  · rcases hbc with rfl | ⟨_, hc⟩
    · exact .inr ⟨ha, hb⟩
    · exact .inr ⟨ha, hc⟩

theorem AlphabetRelated.eq_of_le {K a b : ℕ}
    (h : AlphabetRelated K a b) (ha : K ≤ a) : b = a := by
  rcases h with h | ⟨hbad, _⟩
  · exact h
  · omega

theorem AlphabetRelated.lt_iff {K a b : ℕ}
    (h : AlphabetRelated K a b) : b < K ↔ a < K := by
  rcases h with rfl | ⟨ha, hb⟩
  · rfl
  · exact iff_of_true hb ha

def PreservesAlphabetCoordinates (K : ℕ) {N : ℕ}
    (E : (Fin N → ℕ) ≃ (Fin N → ℕ)) : Prop :=
  ∀ u i, AlphabetRelated K (u i) (E u i)

theorem PreservesAlphabetCoordinates.refl (K N : ℕ) :
    PreservesAlphabetCoordinates K (Equiv.refl (Fin N → ℕ)) :=
  fun u i => AlphabetRelated.refl K (u i)

theorem PreservesAlphabetCoordinates.trans {K N : ℕ}
    {E F : (Fin N → ℕ) ≃ (Fin N → ℕ)}
    (hE : PreservesAlphabetCoordinates K E)
    (hF : PreservesAlphabetCoordinates K F) :
    PreservesAlphabetCoordinates K (E.trans F) :=
  fun u i => (hE u i).trans (hF (E u) i)

theorem PreservesAlphabetCoordinates.symm {K N : ℕ}
    {E : (Fin N → ℕ) ≃ (Fin N → ℕ)}
    (hE : PreservesAlphabetCoordinates K E) :
    PreservesAlphabetCoordinates K E.symm := by
  intro u i
  simpa only [Equiv.apply_symm_apply] using (hE (E.symm u) i).symm

theorem wordReflection_preserves_coordinates (K r N : ℕ) (hr : r + 1 < K) :
    PreservesAlphabetCoordinates K (wordReflection r N) := by
  intro u i
  by_cases hc : (List.ofFn u).count (r + 1) ≤ (List.ofFn u).count r
  · rcases wordReflection_lowerOnly_of_count_ge r N u hc i with h | ⟨ha, hb⟩
    · exact .inl h
    · exact .inr ⟨by omega, by omega⟩
  · have hc' : (List.ofFn (wordReflection r N u)).count (r + 1) ≤
        (List.ofFn (wordReflection r N u)).count r := by
      simp only [wordReflection_count, show r + 1 ≠ r by omega,
        show r ≠ r + 1 by omega, if_false, if_true]
      omega
    have h := wordReflection_lowerOnly_of_count_ge r N (wordReflection r N u) hc' i
    rw [wordReflection_involutive r N u] at h
    rcases h with h | ⟨ha, hb⟩
    · exact .inl h.symm
    · exact .inr ⟨by omega, by omega⟩

theorem wordSwapZero_preserves_coordinates (K j N : ℕ) (hj : j < K) :
    PreservesAlphabetCoordinates K (wordSwapZero N j) := by
  revert hj
  induction j using Nat.twoStepInduction with
  | zero => intro hj; exact PreservesAlphabetCoordinates.refl K N
  | one => intro hj; exact wordReflection_preserves_coordinates K 0 N hj
  | more j ih ih' =>
      intro hj
      exact (wordReflection_preserves_coordinates K (j + 1) N hj).trans
        ((ih' (by omega)).trans (wordReflection_preserves_coordinates K (j + 1) N hj))

theorem wordContentSwap_preserves_coordinates (K i j N : ℕ)
    (hi : i < K) (hj : j < K) :
    PreservesAlphabetCoordinates K (wordContentSwap N i j) := by
  unfold wordContentSwap
  split_ifs
  · exact PreservesAlphabetCoordinates.refl K N
  · exact wordSwapZero_preserves_coordinates K j N hj
  · exact wordSwapZero_preserves_coordinates K i N hi
  · exact (wordSwapZero_preserves_coordinates K i N hi).trans
      ((wordSwapZero_preserves_coordinates K j N hj).trans
        (wordSwapZero_preserves_coordinates K i N hi))

theorem wordBringPair_preserves_coordinates (K i j N : ℕ)
    (hi : i < K) (hj : j < K) (hij : i ≠ j) :
    PreservesAlphabetCoordinates K (wordBringPair N i j) := by
  have hK : 1 < K := by omega
  have hswap : Equiv.swap 0 i j < K := by
    by_cases hj0 : j = 0
    · subst j
      simpa using hi
    · have hji : j ≠ i := Ne.symm hij
      simpa only [Equiv.swap_apply_of_ne_of_ne hj0 hji] using hj
  exact (wordContentSwap_preserves_coordinates K 0 i N (by omega) hi).trans
    (wordContentSwap_preserves_coordinates K 1 (Equiv.swap 0 i j) N hK hswap)

theorem word_lower_preserves_coordinates (K r N : ℕ) (hr : r + 1 < K)
    {u v : Fin N → ℕ} (h : (wordString r N).lower u = some v) (i : Fin N) :
    AlphabetRelated K (u i) (v i) := by
  obtain ⟨j, huj, rfl⟩ := wordString_lower_changes_one r N h
  by_cases hij : i = j
  · subst i
    rw [Function.update_self]
    exact .inr ⟨by omega, hr⟩
  · rw [Function.update_of_ne hij]
    exact AlphabetRelated.refl K _

theorem transferContentWord_preserves_coordinates (K N : ℕ) (c : ℕ → ℕ)
    (i j : ℕ) (hiK : i < K) (hjK : j < K) (hi : 1 < c i) (hj : c j = 0)
    (u : WordOfContent N c) (q : Fin N) :
    AlphabetRelated K (u.val q) (transferContentWord N c i j hi hj u q) := by
  have hij := distinct_of_split_counts hi hj
  have hK : 1 < K := by omega
  have hE := wordBringPair_preserves_coordinates K i j N hiK hjK hij
  let z := (wordString 0 N).lowerValue (preparedContentWord N c i j hi hj u)
  have hlow := word_lower_preserves_coordinates K 0 N hK
    ((wordString 0 N).lowerValue_spec (preparedContentWord N c i j hi hj u)) q
  exact (hE u.val q).trans (hlow.trans (hE.symm z q))

/-- Both the values and the positions of all letters outside the bounded
alphabet are preserved by every actual instruction of the program. -/
theorem CrystalProgram.coordinates {K : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (N : ℕ) (u : WordOfContent N c) (i : Fin N) :
    AlphabetRelated K (u.val i) ((P.embedding N u).val i) := by
  induction P with
  | nil c => exact AlphabetRelated.refl K _
  | reflect r hr rest ih =>
      exact (wordReflection_preserves_coordinates K r N hr u.val i).trans
        (ih (reflectionContentEmbedding N _ r u))
  | split j k hjK hkK hj hk rest ih =>
      exact (transferContentWord_preserves_coordinates K N _ j k hjK hkK hj hk u i).trans
        (ih (contentTransferEmbedding N _ j k hj hk u))

theorem CrystalProgram.outside_eq {K : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (N : ℕ) (u : WordOfContent N c) (i : Fin N)
    (hi : K ≤ u.val i) : (P.embedding N u).val i = u.val i :=
  (P.coordinates N u i).eq_of_le hi

theorem CrystalProgram.inside_iff {K : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (N : ℕ) (u : WordOfContent N c) (i : Fin N) :
    (P.embedding N u).val i < K ↔ u.val i < K :=
  (P.coordinates N u i).lt_iff

end HigherSpecht.Lascoux
end
end CanonicalSource27

section CanonicalSource28
/- Source: HigherSpecht/LascouxNeutralExtension.lean -/



/-! The literal program extends over arbitrary neutral content, not only
over a single cap letter.  Every additional content value below the
alphabet bound is zero, so all instruction-domain proofs remain valid. -/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem reflectedContent_addNeutral (c b : ℕ → ℕ) (K r : ℕ)
    (hr : r + 1 < K) (hb : ∀ a, a < K → b a = 0) :
    reflectedContent (c + b) r = reflectedContent c r + b := by
  funext a
  change c (Equiv.swap r (r + 1) a) + b (Equiv.swap r (r + 1) a) =
    c (Equiv.swap r (r + 1) a) + b a
  congr 1
  by_cases ha : a = r
  · subst a
    simp only [Equiv.swap_apply_left, hb (r + 1) hr, hb r (by omega)]
  · by_cases ha' : a = r + 1
    · subst a
      simp only [Equiv.swap_apply_right, hb (r + 1) hr, hb r (by omega)]
    · rw [Equiv.swap_apply_of_ne_of_ne ha ha']

theorem splitContent_addNeutral (c b : ℕ → ℕ) (K i j : ℕ)
    (hi : i < K) (hj : j < K) (hb : ∀ a, a < K → b a = 0) :
    splitContent (c + b) i j = splitContent c i j + b := by
  funext a
  by_cases haj : a = j
  · subst a
    simp only [splitContent, Function.update_self, Pi.add_apply, hb _ hj, Nat.add_zero]
  · by_cases hai : a = i
    · subst a
      simp only [splitContent, Function.update_of_ne haj, Function.update_self,
        Pi.add_apply, hb _ hi, Nat.add_zero]
    · simp only [splitContent, Function.update_of_ne haj, Function.update_of_ne hai,
        Pi.add_apply]

def CrystalProgram.addNeutral {K : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (b : ℕ → ℕ)
    (hb : ∀ a, a < K → b a = 0) : CrystalProgram K (c + b) (d + b) := by
  induction P with
  | nil c => exact .nil _
  | @reflect c d r hr rest ih =>
      exact .reflect r hr
        (ih.castContents (reflectedContent_addNeutral c b K r hr hb).symm rfl)
  | @split c d i j hiK hjK hi hj rest ih =>
      exact .split i j hiK hjK
        (by simpa only [Pi.add_apply, hb i hiK, Nat.add_zero] using hi)
        (by simpa only [Pi.add_apply, hb j hjK, Nat.add_zero] using hj)
        (ih.castContents (splitContent_addNeutral c b K i j hiK hjK hb).symm rfl)

theorem CrystalProgram.addNeutral_filter {K : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (b : ℕ → ℕ)
    (hb : ∀ a, a < K → b a = 0) (N L : ℕ)
    (u : WordOfContent N (c + b)) (v : WordOfContent L c)
    (hfilter : alphabetFilter K (List.ofFn u.val) = List.ofFn v.val) :
    alphabetFilter K (List.ofFn ((P.addNeutral b hb).embedding N u).val) =
      List.ofFn (P.embedding L v).val := by
  induction P with
  | nil c => exact hfilter
  | @reflect c d r hr rest ih =>
      have hstep := (wordReflection_preserves_filter K r N L hr u.val v.val).mpr hfilter
      let u₁ := reflectionContentEmbedding N (c + b) r u
      let v₁ := reflectionContentEmbedding L c r v
      have hcast : reflectedContent (c + b) r = reflectedContent c r + b :=
        reflectedContent_addNeutral c b K r hr hb
      let hu₁ : WordOfContent N (reflectedContent c r + b) := castContentWord hcast u₁
      have hfilter₁ : alphabetFilter K (List.ofFn hu₁.val) = List.ofFn v₁.val := by
        rw [show hu₁.val = u₁.val from castContentWord_val hcast u₁]
        change alphabetFilter K (List.ofFn (wordReflection r N u.val)) =
          List.ofFn (wordReflection r L v.val)
        exact hstep
      change alphabetFilter K (List.ofFn
        (((rest.addNeutral b hb).castContents hcast.symm rfl).embedding N u₁).val) =
        List.ofFn (rest.embedding L v₁).val
      rw [CrystalProgram.embedding_castContents_word (rest.addNeutral b hb) hcast.symm rfl
        hu₁ u₁ (castContentWord_val hcast u₁)]
      exact ih hu₁ v₁ hfilter₁
  | @split c d i j hiK hjK hi hj rest ih =>
      have hi' : 1 < (c + b) i := by
        simpa only [Pi.add_apply, hb i hiK, Nat.add_zero] using hi
      have hj' : (c + b) j = 0 := by
        simpa only [Pi.add_apply, hb j hjK, Nat.add_zero] using hj
      have hstep := transferContentWord_preserves_filter K N L (c + b) c i j
        hiK hjK hi' hj' hi hj u v hfilter
      let u₁ := contentTransferEmbedding N (c + b) i j hi' hj' u
      let v₁ := contentTransferEmbedding L c i j hi hj v
      have hcast : splitContent (c + b) i j = splitContent c i j + b :=
        splitContent_addNeutral c b K i j hiK hjK hb
      let hu₁ : WordOfContent N (splitContent c i j + b) := castContentWord hcast u₁
      have hfilter₁ : alphabetFilter K (List.ofFn hu₁.val) = List.ofFn v₁.val := by
        rw [show hu₁.val = u₁.val from castContentWord_val hcast u₁]
        change alphabetFilter K (List.ofFn (transferContentWord N (c + b) i j hi' hj' u)) =
          List.ofFn (transferContentWord L c i j hi hj v)
        exact hstep
      change alphabetFilter K (List.ofFn
        (((rest.addNeutral b hb).castContents hcast.symm rfl).embedding N u₁).val) =
        List.ofFn (rest.embedding L v₁).val
      rw [CrystalProgram.embedding_castContents_word (rest.addNeutral b hb) hcast.symm rfl
        hu₁ u₁ (castContentWord_val hcast u₁)]
      exact ih hu₁ v₁ hfilter₁

end HigherSpecht.Lascoux
end
end CanonicalSource28

section CanonicalSource29
/- Source: HigherSpecht/LascouxTableauOfRows.lean -/



/-!
# Converting genuine insertion rows to Mathlib semistandard tableaux

The shape is the actual Young diagram of the row lengths, and the entry at
`(r,j)` is the literal list entry, zero outside the diagram.  This supplies
an actual semistandard representative of every inserted word; there is no
assumed normal-form or shape witness.
-/

noncomputable section
open TauCeti

namespace HigherSpecht.Lascoux

theorem tableauShape_height (rows : List (List ℕ)) (hrows : rows.IsTableauRows) :
    (List.tableauShape rows hrows).colLen 0 = rows.length := by
  rw [← YoungDiagram.length_rowLens, List.rowLens_tableauShape, List.length_map]

theorem tableauShape_rowLen (rows : List (List ℕ)) (hrows : rows.IsTableauRows)
    (r : ℕ) :
    (List.tableauShape rows hrows).rowLen r = (rows.getD r []).length := by
  rw [← YoungDiagram.getD_rowLens, List.rowLens_tableauShape]
  exact List.getD_map rows [] List.length

theorem tableauRows_getD_sorted (rows : List (List ℕ)) (hrows : rows.IsTableauRows)
    (r : ℕ) : (rows.getD r []).SortedLE := by
  by_cases hr : r < rows.length
  · rw [List.getD_eq_getElem rows [] hr]
    exact hrows.sortedLE _ (List.getElem_mem hr)
  · rw [List.getD_eq_default rows [] (Nat.le_of_not_gt hr)]
    exact List.sortedLE_nil

theorem tableauRows_getD_isRowAbove (rows : List (List ℕ))
    (hrows : rows.IsTableauRows) {r s : ℕ} (hrs : r < s) :
    (rows.getD r []).IsRowAbove (rows.getD s []) := by
  induction s generalizing r with
  | zero => omega
  | succ s ih =>
      by_cases heq : r = s
      · subst r
        exact hrows.isRowAbove_getD s
      · exact (ih (by omega)).trans (hrows.isRowAbove_getD s)

def tableauOfRows (rows : List (List ℕ)) (hrows : rows.IsTableauRows) :
    SemistandardYoungTableau (List.tableauShape rows hrows) where
  entry r j := (rows.getD r []).getD j 0
  row_weak' {r j k} hjk hcell := by
    have hk : k < (rows.getD r []).length := by
      rw [← tableauShape_rowLen rows hrows r]
      exact YoungDiagram.mem_iff_lt_rowLen.mp hcell
    have hj : j < (rows.getD r []).length := hjk.trans hk
    rw [List.getD_eq_getElem (rows.getD r []) 0 hj,
      List.getD_eq_getElem (rows.getD r []) 0 hk]
    exact (List.pairwise_iff_getElem.mp
      (List.sortedLE_iff_pairwise.mp (tableauRows_getD_sorted rows hrows r)))
      j k hj hk hjk
  col_strict' {r s j} hrs hcell := by
    have hs : j < (rows.getD s []).length := by
      rw [← tableauShape_rowLen rows hrows s]
      exact YoungDiagram.mem_iff_lt_rowLen.mp hcell
    have habove := tableauRows_getD_isRowAbove rows hrows hrs
    have hr : j < (rows.getD r []).length := hs.trans_le habove.length_le
    rw [List.getD_eq_getElem (rows.getD r []) 0 hr,
      List.getD_eq_getElem (rows.getD s []) 0 hs]
    exact habove.getElem_lt j hr hs
  zeros' {r j} hcell := by
    have hj : (rows.getD r []).length ≤ j := by
      rw [← tableauShape_rowLen rows hrows r]
      exact Nat.le_of_not_gt (fun h => hcell (YoungDiagram.mem_iff_lt_rowLen.mpr h))
    exact List.getD_eq_default (rows.getD r []) 0 hj

@[simp] theorem tableauOfRows_apply (rows : List (List ℕ))
    (hrows : rows.IsTableauRows) (r j : ℕ) :
    tableauOfRows rows hrows r j = (rows.getD r []).getD j 0 := rfl

theorem tableauRowWord_tableauOfRows (rows : List (List ℕ))
    (hrows : rows.IsTableauRows) (r : ℕ) :
    tableauRowWord (tableauOfRows rows hrows) r = rows.getD r [] := by
  apply List.ext_getElem
  · rw [tableauRowWord_length, tableauShape_rowLen]
  · intro j hj hj'
    rw [tableauRowWord_getElem, tableauOfRows_apply, List.getD_eq_getElem (rows.getD r []) 0 hj']

theorem semistandardRows_tableauOfRows (rows : List (List ℕ))
    (hrows : rows.IsTableauRows) :
    semistandardRows (tableauOfRows rows hrows) = rows := by
  apply List.ext_getElem
  · rw [semistandardRows_length, tableauShape_height]
  · intro r hr hr'
    rw [semistandardRows_getElem, tableauRowWord_tableauOfRows,
      List.getD_eq_getElem rows [] hr']

theorem tableauWord_tableauOfRows (rows : List (List ℕ))
    (hrows : rows.IsTableauRows) :
    tableauWord (tableauOfRows rows hrows) = rowWordRows rows := by
  rw [tableauWord_eq_rowWordRows, semistandardRows_tableauOfRows]

theorem isTableauRows_fold_rowInsert (w : List ℕ) (rows : List (List ℕ))
    (hrows : rows.IsTableauRows) :
    (w.foldl (fun rows x => rowInsert x rows) rows).IsTableauRows := by
  induction w generalizing rows with
  | nil => exact hrows
  | cons x w ih => exact ih (rowInsert x rows) (hrows.rowInsert x)

def insertionRows (w : List ℕ) : List (List ℕ) :=
  w.foldl (fun rows x => rowInsert x rows) []

theorem insertionRows_isTableau (w : List ℕ) : (insertionRows w).IsTableauRows :=
  isTableauRows_fold_rowInsert w [] List.isTableauRows_nil

def insertionShape (w : List ℕ) : YoungDiagram :=
  List.tableauShape (insertionRows w) (insertionRows_isTableau w)

def insertionTableau (w : List ℕ) : SemistandardYoungTableau (insertionShape w) :=
  tableauOfRows (insertionRows w) (insertionRows_isTableau w)

theorem insertionTableau_word (w : List ℕ) :
    tableauWord (insertionTableau w) = rowWordRows (insertionRows w) :=
  tableauWord_tableauOfRows _ _

/-- Every literal word has its actual insertion tableau as a semistandard
Knuth representative, with no supplied shape or representative premise. -/
theorem knuth_insertionTableau (w : List ℕ) :
    KnuthEquivalent w (tableauWord (insertionTableau w)) := by
  rw [insertionTableau_word]
  simpa only [insertionRows, rowWordRows_nil, List.nil_append] using
    knuth_fold_rowInsert w [] (by intro row h; simp at h)

end HigherSpecht.Lascoux
end
end CanonicalSource29

section CanonicalSource30
/- Source: HigherSpecht/LascouxOneRowUniqueness.lean -/



/-! A tableau with at most one row is determined by its actual letter
multiplicities.  This includes the empty shape and repeated letters. -/

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

theorem tableauWord_eq_first_row_of_height_le_one
    (T : SemistandardYoungTableau mu) (hheight : mu.colLen 0 ≤ 1) :
    tableauWord T = tableauRowWord T 0 := by
  by_cases hz : mu.colLen 0 = 0
  · have hw : mu.rowLen 0 = 0 :=
      YoungDiagram.rowLen_eq_zero_of_colLen_le (by omega : mu.colLen 0 ≤ 0)
    simp only [tableauWord, hz, descendingRows, List.flatMap_nil,
      tableauRowWord, tableauRowSegment, hw, Nat.sub_zero,
      List.range'_zero, List.map_nil]
  · have ho : mu.colLen 0 = 1 := by omega
    simp only [tableauWord, ho, descendingRows, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]

theorem tableauWord_sorted_of_height_le_one
    (T : SemistandardYoungTableau mu) (hheight : mu.colLen 0 ≤ 1) :
    (tableauWord T).SortedLE := by
  rw [tableauWord_eq_first_row_of_height_le_one T hheight]
  exact tableauRowWord_sorted T 0

/-- The one-row base case uses actual multiplicities, without any
standardization or tableau-count assumption. -/
theorem one_row_tableau_eq_of_word_counts
    (T U : SemistandardYoungTableau mu) (hheight : mu.colLen 0 ≤ 1)
    (hcount : ∀ a : ℕ, (tableauWord T).count a = (tableauWord U).count a) : T = U := by
  have hp : (tableauWord T).Perm (tableauWord U) := List.perm_iff_count.mpr hcount
  have hw : tableauWord T = tableauWord U :=
    List.Perm.eq_of_sortedLE (tableauWord_sorted_of_height_le_one T hheight)
      (tableauWord_sorted_of_height_le_one U hheight) hp
  have hrow : tableauRowWord T 0 = tableauRowWord U 0 := by
    rwa [tableauWord_eq_first_row_of_height_le_one T hheight,
      tableauWord_eq_first_row_of_height_le_one U hheight] at hw
  apply SemistandardYoungTableau.ext
  intro r j
  by_cases hr : r = 0
  · subst r
    have h := congrArg (fun row : List ℕ => row.getD j 0) hrow
    simpa only [tableauRowWord_getD] using h
  · have hc : (r, j) ∉ mu := by
      intro hcell
      have hlt : r < mu.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp
        (mu.up_left_mem le_rfl (Nat.zero_le _) hcell)
      omega
    rw [T.zeros hc, U.zeros hc]

theorem one_row_tableau_eq_of_contentCells
    (T U : SemistandardYoungTableau mu) (hheight : mu.colLen 0 ≤ 1)
    (hcount : ∀ a : ℕ, (contentCells T a).card = (contentCells U a).card) : T = U := by
  apply one_row_tableau_eq_of_word_counts T U hheight
  intro a
  simpa only [tableauWord_count_eq_contentCells] using hcount a

end HigherSpecht.Lascoux
end CanonicalSource30

section CanonicalSource31
/- Source: HigherSpecht/LascouxZeroBalancing.lean -/



/-!
# Balancing the saturated zero row while fixing the neutral tail

The one-row output of any actual balancing program is forced by its
shape and its standard content to be `0, ..., m-1`.  The bounded program
has a literal extension over arbitrary higher letters.  Their coordinates
stay fixed, so an actual final block of `m` zeros is replaced by that
increasing standard row, with the preceding word unchanged.
-/

noncomputable section
open scoped Classical BigOperators

namespace HigherSpecht.Lascoux

def zeroContent (m a : ℕ) : ℕ := if a = 0 then m else 0

def zeroWord (m : ℕ) : WordOfContent m (zeroContent m) :=
  ⟨fun _ => 0, by
    intro a
    change (List.ofFn (fun _ : Fin m => (0 : ℕ))).count a = if a = 0 then m else 0
    rw [List.ofFn_const]
    by_cases ha : a = 0
    · subst a
      simp only [List.count_replicate_self, if_pos rfl, if_true]
    · rw [if_neg ha]
      exact List.count_eq_zero.mpr (fun hmem => ha (List.eq_of_mem_replicate hmem))⟩

@[simp] theorem zeroWord_ofFn (m : ℕ) :
    List.ofFn (zeroWord m).val = List.replicate m 0 := by
  exact List.ofFn_const m 0

theorem exists_zero_balancing_program (m : ℕ) (hm : 0 < m) :
    Nonempty (CrystalProgram m (zeroContent m) (standardContent m)) := by
  let c : Fin m → ℕ := fun i => if i.val = 0 then m else 0
  have hsum : ∑ i, c i = m := by
    rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
    · simp [c]
    · intro i hi hne
      have hi0 : i.val ≠ 0 := fun h => hne (Fin.ext h)
      simp [c, hi0]
    · simp
  have hext : extendContent c = zeroContent m := by
    funext a
    by_cases ha : a < m
    · simp [extendContent, zeroContent, c, ha]
    · have ha0 : a ≠ 0 := by omega
      simp [extendContent, zeroContent, ha, ha0]
  simpa only [hext] using exists_crystal_balancing_program m c hsum

theorem CrystalProgram.zeroWord_eq_range {m : ℕ}
    (P : CrystalProgram m (zeroContent m) (standardContent m)) :
    List.ofFn (P.embedding m (zeroWord m)).val = List.range m := by
  by_cases hm : m = 0
  · subst m
    simp
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hrows : [List.replicate m 0].IsTableauRows := by
      refine List.isTableauRows_cons.mpr ⟨?_, List.sortedLE_replicate m,
        List.isRowAbove_nil _, List.isTableauRows_nil⟩
      simp [hm]
    let T := tableauOfRows [List.replicate m 0] hrows
    have hw : List.ofFn (zeroWord m).val = tableauWord T := by
      rw [zeroWord_ofFn, tableauWord_tableauOfRows]
      simp only [HigherSpecht.rowWordRows_cons, HigherSpecht.rowWordRows_nil,
        List.nil_append]
    obtain ⟨U, hU⟩ := (P.properties m).shape T (zeroWord m) hw
    have hheight : (List.tableauShape [List.replicate m 0] hrows).colLen 0 ≤ 1 := by
      rw [tableauShape_height]
      simp
    have hsorted : (List.ofFn (P.embedding m (zeroWord m)).val).SortedLE := by
      rw [hU]
      exact tableauWord_sorted_of_height_le_one U hheight
    have hp : (List.ofFn (P.embedding m (zeroWord m)).val).Perm (List.range m) := by
      apply List.perm_iff_count.mpr
      intro a
      simpa only [wordContent, standardContent, List.count_range] using
        (P.embedding m (zeroWord m)).property a
    exact List.Perm.eq_of_sortedLE hsorted (List.sortedLT_range m).sortedLE hp

theorem alphabetRelated_neutral_prefix {K : ℕ} (pref : List ℕ)
    (hp : ∀ a ∈ pref, K ≤ a) {tail output : List ℕ}
    (h : List.Forall₂ (AlphabetRelated K) (pref ++ tail) output) :
    ∃ outputTail, output = pref ++ outputTail ∧
      List.Forall₂ (AlphabetRelated K) tail outputTail := by
  induction pref generalizing output with
  | nil => exact ⟨output, rfl, h⟩
  | cons a pref ih =>
      obtain ⟨b, output, hab, hrest, rfl⟩ := List.forall₂_cons_left_iff.mp h
      have hba : b = a := hab.eq_of_le (hp a (by simp))
      subst b
      obtain ⟨outputTail, hout, htail⟩ := ih (fun x hx => hp x (by simp [hx])) hrest
      exact ⟨outputTail, by simp only [hout, List.cons_append], htail⟩

theorem alphabetRelated_replicate_zero {K m : ℕ} (hK : 0 < K) {output : List ℕ}
    (h : List.Forall₂ (AlphabetRelated K) (List.replicate m 0) output) :
    ∀ a ∈ output, a < K := by
  induction m generalizing output with
  | zero =>
      have heq : output = [] := List.forall₂_nil_left_iff.mp h
      simp [heq]
  | succ m ih =>
      rw [List.replicate_succ] at h
      obtain ⟨b, output, hb, hrest, rfl⟩ := List.forall₂_cons_left_iff.mp h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hb.lt_iff.mpr hK
      · exact ih hrest a ha

/-- This is equality of the complete literal word, including the
unchanged neutral prefix, not only equality of its filtered class. -/
theorem CrystalProgram.addNeutral_zero_block {m N : ℕ} (hm : 0 < m)
    (P : CrystalProgram m (zeroContent m) (standardContent m))
    (b : ℕ → ℕ) (hb : ∀ a, a < m → b a = 0)
    (u : WordOfContent N (zeroContent m + b)) (pref : List ℕ)
    (hp : ∀ a ∈ pref, m ≤ a)
    (hu : List.ofFn u.val = pref ++ List.replicate m 0) :
    List.ofFn ((P.addNeutral b hb).embedding N u).val = pref ++ List.range m := by
  have hpfilter : alphabetFilter m pref = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    simpa only [decide_eq_true_iff] using not_lt_of_ge (hp a ha)
  have hfilter : alphabetFilter m (List.ofFn u.val) = List.ofFn (zeroWord m).val := by
    rw [hu, zeroWord_ofFn]
    simp only [alphabetFilter, List.filter_append] at hpfilter ⊢
    rw [hpfilter]
    simp [hm]
  have houtfilter := P.addNeutral_filter b hb N m u (zeroWord m) hfilter
  rw [P.zeroWord_eq_range] at houtfilter
  have hcoords := forall₂_ofFn_of_forall (AlphabetRelated m) N u.val
    ((P.addNeutral b hb).embedding N u).val
    (fun i => (P.addNeutral b hb).coordinates N u i)
  rw [hu] at hcoords
  obtain ⟨tail, hout, htail⟩ := alphabetRelated_neutral_prefix pref hp hcoords
  have htailfilter : alphabetFilter m tail = tail := by
    apply List.filter_eq_self.mpr
    intro a ha
    simpa only [decide_eq_true_iff] using alphabetRelated_replicate_zero hm htail a ha
  have htailEq : tail = List.range m := by
    rw [hout] at houtfilter
    change (pref ++ tail).filter (fun a => decide (a < m)) = List.range m at houtfilter
    rw [List.filter_append] at houtfilter
    change alphabetFilter m pref ++ alphabetFilter m tail = List.range m at houtfilter
    rw [hpfilter, htailfilter, List.nil_append] at houtfilter
    exact houtfilter
  rw [hout, htailEq]

end HigherSpecht.Lascoux
end
end CanonicalSource31

section CanonicalSource32
/- Source: HigherSpecht/LascouxSaturatedStandardProgram.lean -/



/-!
# Completing the saturated recursive program to standard content

After the smaller tableau has been balanced, actual empty-letter
reflections move its positive alphabet past the zero row.  A genuine
zero-balancing program then replaces that row by `0, ..., m-1` and fixes
every tail position.  The complete output word is proved explicitly.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

def shiftedSingletonContent (m M a : ℕ) : ℕ :=
  if m ≤ a ∧ a < M + m then 1 else 0

theorem shiftedSingletonContent_below (m M : ℕ) :
    ∀ a, a < m → shiftedSingletonContent m M a = 0 := by
  intro a ha
  simp only [shiftedSingletonContent, if_neg (by omega : ¬ (m ≤ a ∧ a < M + m))]

theorem positiveShift_zeroAndSingleton (M m : ℕ) (hm : 0 < m) :
    positiveShiftContent (zeroAndSingletonContent M m) (m - 1) =
      zeroContent m + shiftedSingletonContent m M := by
  funext a
  simp only [Pi.add_apply]
  by_cases ha0 : a = 0
  · subst a
    simp only [positiveShiftContent, zeroAndSingletonContent, zeroContent,
      if_true, shiftedSingletonContent, if_neg (by omega : ¬ (m ≤ 0 ∧ 0 < M + m)),
      Nat.add_zero]
  · by_cases ham : m ≤ a
    · have hpos : m - 1 < a := by omega
      have hd0 : a - (m - 1) ≠ 0 := by omega
      have hle : a - (m - 1) ≤ M ↔ a < M + m := by omega
      simp only [positiveShiftContent, zeroAndSingletonContent, zeroContent, if_neg ha0,
        if_pos hpos, if_neg hd0, shiftedSingletonContent, ham, true_and,
        hle, Nat.zero_add]
    · have hle : ¬ m - 1 < a := by omega
      simp only [positiveShiftContent, zeroContent, if_neg ha0, if_neg hle,
        shiftedSingletonContent, ham, false_and, if_false, Nat.add_zero]

theorem standardContent_add_shiftedSingleton (M m : ℕ) :
    standardContent m + shiftedSingletonContent m M = standardContent (M + m) := by
  funext a
  simp only [Pi.add_apply, standardContent, shiftedSingletonContent]
  split_ifs <;> omega

theorem positiveShift_prependZeroRow_word {mu : YoungDiagram}
    (Q : SemistandardYoungTableau (firstRowTail mu)) (m : ℕ) (hm : 0 < m)
    (hwidth : mu.rowLen 0 = m) :
    (tableauWord (prependZeroRow Q)).map (positiveShift (m - 1)) =
      (tableauWord Q).map (fun a => a + m) ++ List.replicate m 0 := by
  rw [tableauWord_prependZeroRow, List.map_append, List.map_map, List.map_replicate, hwidth]
  have hmap : positiveShift (m - 1) ∘ Nat.succ = fun a => a + m := by
    funext a
    simp only [Function.comp_apply, positiveShift, Nat.succ_ne_zero, if_false,
      Nat.succ_eq_add_one]
    omega
  rw [hmap]
  rfl

/-- Every component of this program is an actual reflection or split.
The conclusion identifies its complete word, including the fixed tail. -/
theorem exists_saturated_standardProgram (M m : ℕ) (hm : 0 < m)
    (c : ℕ → ℕ) (hc0 : c 0 = m) (hc : ∀ a, M < a → c a = 0)
    (P : CrystalProgram M (firstContentTail M c) (standardContent M))
    {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) (hwidth : mu.rowLen 0 = m)
    (u : WordOfContent (M + m) c) (hu : List.ofFn u.val = tableauWord T)
    (v : WordOfContent M (firstContentTail M c))
    (hv : List.ofFn v.val = tableauWord (firstRowTailPred T))
    (Q : SemistandardYoungTableau (firstRowTail mu))
    (hQ : List.ofFn (P.embedding M v).val = tableauWord Q) :
    ∃ R : CrystalProgram (M + m) c (standardContent (M + m)),
      List.ofFn (R.embedding (M + m) u).val =
        (tableauWord Q).map (fun a => a + m) ++ List.range m := by
  let N := M + m
  let R₀ := (recursiveSaturatedProgram M m c hc0 hc P).enlargeAlphabet
    (by omega : M + 1 ≤ N)
  have hzeroSupport : ∀ a, M < a → zeroAndSingletonContent M m a = 0 := by
    intro a ha
    simp only [zeroAndSingletonContent, if_neg (by omega : a ≠ 0),
      if_neg (by omega : ¬ a ≤ M)]
  obtain ⟨S, hS⟩ := exists_positiveShiftProgram M (m - 1)
    (zeroAndSingletonContent M m) hzeroSupport
  let b := shiftedSingletonContent m M
  have hb : ∀ a, a < m → b a = 0 := shiftedSingletonContent_below m M
  have hshift := positiveShift_zeroAndSingleton M m hm
  let S' := (S.enlargeAlphabet (by omega : M + (m - 1) + 1 ≤ N)).castContents rfl hshift
  obtain ⟨Z⟩ := exists_zero_balancing_program m hm
  have hstandard : standardContent m + b = standardContent N :=
    standardContent_add_shiftedSingleton M m
  let Z' := ((Z.addNeutral b hb).enlargeAlphabet (by omega : m ≤ N)).castContents rfl hstandard
  let R := R₀.append (S'.append Z')
  refine ⟨R, ?_⟩
  let u₁ := R₀.embedding N u
  let u₂ := S'.embedding N u₁
  have hu₁ : List.ofFn u₁.val = tableauWord (prependZeroRow Q) := by
    simpa only [u₁, R₀, CrystalProgram.embedding_enlargeAlphabet] using
      recursiveSaturatedProgram_word M m N c hc0 hc P T hs u hu v hv Q hQ
  have hval₂ : u₂.val = fun i => positiveShift (m - 1) (u₁.val i) := by
    rw [CrystalProgram.embedding_castContents_word _ rfl hshift u₁ u₁ rfl,
      CrystalProgram.embedding_enlargeAlphabet]
    funext i
    exact hS N u₁ i
  have hu₂ : List.ofFn u₂.val =
      (tableauWord Q).map (fun a => a + m) ++ List.replicate m 0 := by
    rw [hval₂]
    change List.ofFn (positiveShift (m - 1) ∘ u₁.val) = _
    rw [← List.map_ofFn, hu₁]
    exact positiveShift_prependZeroRow_word Q m hm hwidth
  have hprefix : ∀ a ∈ (tableauWord Q).map (fun a => a + m), m ≤ a := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    omega
  have hout := Z.addNeutral_zero_block hm b hb u₂ _ hprefix hu₂
  have hfinal : List.ofFn (Z'.embedding N u₂).val =
      (tableauWord Q).map (fun a => a + m) ++ List.range m := by
    rw [CrystalProgram.embedding_castContents_word _ rfl hstandard u₂ u₂ rfl,
      CrystalProgram.embedding_enlargeAlphabet]
    exact hout
  simpa only [R, CrystalProgram.embedding_append, Function.Embedding.trans_apply,
    u₁, u₂] using hfinal

end HigherSpecht.Lascoux
end
end CanonicalSource32

section CanonicalSource33
/- Source: HigherSpecht/LascouxFirstRowPotential.lean -/



/-!
# A concrete natural-number descent for ordinary row-word cyclage

A row is padded to a fixed width with a symbol `M` greater than every
actual letter and read as a base-`M+1` numeral.  Literal row insertion of
`x < M` strictly decreases that numeral whenever the row has spare width.
This proves the finite descent needed for the canonical ordinary cyclage
without importing a cyclage-poset theorem or a cocharge identity.
-/

noncomputable section
open TauCeti

namespace HigherSpecht.Lascoux

def paddedRowValue (M : ℕ) : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | k + 1, [] => M * (M + 1) ^ k + paddedRowValue M k []
  | k + 1, x :: row => x * (M + 1) ^ k + paddedRowValue M k row

@[simp] theorem paddedRowValue_zero (M : ℕ) (row : List ℕ) :
    paddedRowValue M 0 row = 0 := rfl

@[simp] theorem paddedRowValue_nil_succ (M k : ℕ) :
    paddedRowValue M (k + 1) [] =
      M * (M + 1) ^ k + paddedRowValue M k [] := rfl

@[simp] theorem paddedRowValue_cons (M k x : ℕ) (row : List ℕ) :
    paddedRowValue M (k + 1) (x :: row) =
      x * (M + 1) ^ k + paddedRowValue M k row := rfl

/-- This is the literal `rowBump` operation.  The proof works even before
assuming sortedness of the row, so there is no hidden tableau condition. -/
theorem paddedRowValue_rowBump_lt (M k x : ℕ) (row : List ℕ)
    (hx : x < M) (hwidth : row.length < k) :
    paddedRowValue M k (rowBump x row).1 < paddedRowValue M k row := by
  induction k generalizing row with
  | zero => omega
  | succ k ih =>
      cases row with
      | nil =>
          simp only [rowBump_nil, paddedRowValue_cons, paddedRowValue_nil_succ]
          exact Nat.add_lt_add_right
            (Nat.mul_lt_mul_of_pos_right hx (by positivity)) _
      | cons a row =>
          by_cases hxa : x < a
          · rw [rowBump_cons_of_lt row hxa, paddedRowValue_cons,
              paddedRowValue_cons]
            exact Nat.add_lt_add_right
              (Nat.mul_lt_mul_of_pos_right hxa (by positivity)) _
          · rw [rowBump_cons_of_le row (Nat.le_of_not_gt hxa),
              paddedRowValue_cons, paddedRowValue_cons]
            exact Nat.add_lt_add_left (ih row (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hwidth)) _

theorem paddedRowValue_lt_power (M k : ℕ) (row : List ℕ)
    (hbound : ∀ x ∈ row, x ≤ M) :
    paddedRowValue M k row < (M + 1) ^ k := by
  induction k generalizing row with
  | zero => simp
  | succ k ih =>
      cases row with
      | nil =>
          have ht := ih [] (by simp)
          simp only [paddedRowValue_nil_succ, pow_succ]
          calc
            M * (M + 1) ^ k + paddedRowValue M k [] <
                M * (M + 1) ^ k + (M + 1) ^ k := Nat.add_lt_add_left ht _
            _ = (M + 1) ^ k * (M + 1) := by ring
      | cons x row =>
          have hx : x ≤ M := hbound x (by simp)
          have ht := ih row (fun y hy => hbound y (by simp [hy]))
          simp only [paddedRowValue_cons, pow_succ]
          calc
            x * (M + 1) ^ k + paddedRowValue M k row <
                x * (M + 1) ^ k + (M + 1) ^ k := Nat.add_lt_add_left ht _
            _ ≤ M * (M + 1) ^ k + (M + 1) ^ k :=
                Nat.add_le_add_right (Nat.mul_le_mul_right _ hx) _
            _ = (M + 1) ^ k * (M + 1) := by ring

/-- Row insertion has exactly the first-row update used by the potential. -/
theorem rowInsert_firstRow (x : ℕ) (row : List ℕ) (rows : List (List ℕ)) :
    (rowInsert x (row :: rows)).headD [] = (rowBump x row).1 := by
  cases h : (rowBump x row).2 with
  | none => rw [rowInsert_cons_of_eq_none rows h, List.headD_cons]
  | some y => rw [rowInsert_cons_of_eq_some rows h, List.headD_cons]

theorem paddedRowValue_rowInsert_firstRow_lt (M k x : ℕ)
    (row : List ℕ) (rows : List (List ℕ))
    (hx : x < M) (hwidth : row.length < k) :
    paddedRowValue M k ((rowInsert x (row :: rows)).headD []) <
      paddedRowValue M k row := by
  rw [rowInsert_firstRow]
  exact paddedRowValue_rowBump_lt M k x row hx hwidth

theorem tableauWord_length {mu : YoungDiagram} (T : SemistandardYoungTableau mu) :
    (tableauWord T).length = mu.card := by
  rw [tableauWord_eq_rowWordRows]
  calc
    (rowWordRows (semistandardRows T)).length =
        ((semistandardRows T).map List.length).sum := by
      simp only [rowWordRows, List.length_flatten, List.map_reverse, List.sum_reverse]
    _ = mu.rowLens.sum := by rw [semistandardRows_map_length]
    _ = mu.card := YoungDiagram.sum_rowLens_eq_card mu

end HigherSpecht.Lascoux
end
end CanonicalSource33

section CanonicalSource34
/- Source: HigherSpecht/FixedShapeInsertion.lean -/



/-!
# Insertion is injective when the input shape is fixed

The output shape determines which row gained its cell once the input shape
is known.  The genuine reverse insertion at that row then recovers both
the original rows and the inserted letter.  Repeated letters are allowed.
-/

namespace HigherSpecht

open TauCeti

variable {α : Type*} [LinearOrder α]

theorem rowInsertIndex_eq_of_same_shape
    {P Q : List (List α)} {x y : α}
    (hshape : P.map List.length = Q.map List.length)
    (hinsert : rowInsert x P = rowInsert y Q) :
    rowInsertIndex x P = rowInsertIndex y Q := by
  have hlength (i : ℕ) : (P.getD i []).length = (Q.getD i []).length := by
    have h := congrArg (fun lengths : List ℕ => lengths.getD i 0) hshape
    simpa only [← List.length_nil (α := α), List.getD_map] using h
  by_contra hne
  have h := congrArg (fun rows : List (List α) =>
    (rows.getD (rowInsertIndex x P) []).length) hinsert
  rw [length_getD_rowInsert, length_getD_rowInsert, if_pos rfl, if_neg hne,
    hlength] at h
  omega

/-- The geometric column inequalities are not needed for this recovery:
nonempty weakly increasing rows suffice for the actual inverse algorithm. -/
theorem rowInsert_injective_of_same_shape_rows
    {P Q : List (List α)} {x y : α}
    (hPne : [] ∉ P) (hQne : [] ∉ Q)
    (hPsort : ∀ row ∈ P, row.SortedLE)
    (hQsort : ∀ row ∈ Q, row.SortedLE)
    (hshape : P.map List.length = Q.map List.length)
    (hinsert : rowInsert x P = rowInsert y Q) : P = Q ∧ x = y := by
  have hindex := rowInsertIndex_eq_of_same_shape hshape hinsert
  have hpair : (P, some x) = (Q, some y) := by
    calc
      (P, some x) = reverseRowInsert (rowInsertIndex x P) (rowInsert x P) :=
        (reverseRowInsert_rowInsert x hPne hPsort).symm
      _ = reverseRowInsert (rowInsertIndex y Q) (rowInsert y Q) := by
        rw [hindex, hinsert]
      _ = (Q, some y) := reverseRowInsert_rowInsert y hQne hQsort
  exact ⟨congrArg Prod.fst hpair, Option.some.inj (congrArg Prod.snd hpair)⟩

/-- Fixed-shape injectivity for genuine semistandard row lists. -/
theorem rowInsert_injective_of_same_shape
    {P Q : List (List α)} {x y : α}
    (hP : P.IsTableauRows) (hQ : Q.IsTableauRows)
    (hshape : P.map List.length = Q.map List.length)
    (hinsert : rowInsert x P = rowInsert y Q) : P = Q ∧ x = y :=
  rowInsert_injective_of_same_shape_rows hP.nil_notMem hQ.nil_notMem
    hP.sortedLE hQ.sortedLE hshape hinsert

end HigherSpecht
end CanonicalSource34

section CanonicalSource35
/- Source: HigherSpecht/SemistandardBottomDeletion.lean -/



/-!
# Removing the initial letter of a semistandard row word

The row word is read from the last row to the first.  Its initial letter
is therefore the leftmost entry of the last row.  Removing that entry
shifts the last row left, deleting the row if it becomes empty.  The
result remains semistandard, has a predecessor shape determined solely
by the original shape, and leaves the first row unchanged when at least
two rows were present.
-/

noncomputable section

open TauCeti
open scoped Classical

namespace HigherSpecht

def eraseBottomHead {α : Type*} : List (List α) → List (List α) × Option α
  | [] => ([], none)
  | [row] => (if row.tail = [] then [] else [row.tail], row.head?)
  | row :: next :: rows =>
      let rest := eraseBottomHead (next :: rows)
      (row :: rest.1, rest.2)

def eraseBottomLength : List ℕ → List ℕ
  | [] => []
  | [k] => if k ≤ 1 then [] else [k - 1]
  | k :: l :: ks => k :: eraseBottomLength (l :: ks)

def prependToRow {α : Type*} (a : α) : ℕ → List (List α) → List (List α)
  | _, [] => [[a]]
  | 0, row :: rows => (a :: row) :: rows
  | k + 1, row :: rows => row :: prependToRow a k rows

theorem eraseBottomHead_map_length {α : Type*} (rows : List (List α)) :
    (eraseBottomHead rows).1.map List.length = eraseBottomLength (rows.map List.length) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      cases rows with
      | nil =>
          by_cases ht : row.tail = []
          · have hlen := congrArg List.length ht
            simp only [List.length_tail, List.length_nil] at hlen
            have hle : row.length ≤ 1 := by omega
            simp only [eraseBottomHead, ht, if_true, List.map_nil,
              List.map_cons, eraseBottomLength, if_pos hle]
          · have hpos : 0 < row.tail.length := List.length_pos_iff.mpr ht
            have hgt : ¬row.length ≤ 1 := by rw [List.length_tail] at hpos; omega
            simp only [eraseBottomHead, if_neg ht, List.map_cons, List.map_nil,
              eraseBottomLength, if_neg hgt, List.length_tail]
      | cons next rows =>
          simpa only [eraseBottomHead, List.map_cons, eraseBottomLength] using
            congrArg (List.cons row.length) ih

theorem eraseBottomHead_same_shape {α β : Type*}
    {rows : List (List α)} {rows' : List (List β)}
    (hshape : rows.map List.length = rows'.map List.length) :
    (eraseBottomHead rows).1.map List.length = (eraseBottomHead rows').1.map List.length := by
  rw [eraseBottomHead_map_length, eraseBottomHead_map_length, hshape]

theorem eraseBottomHead_headD {α : Type*} (rows : List (List α)) (hrows : 2 ≤ rows.length) :
    (eraseBottomHead rows).1.headD [] = rows.headD [] := by
  cases rows with
  | nil => simp at hrows
  | cons row rows =>
      cases rows with
      | nil => simp at hrows
      | cons next rows => rfl

theorem eraseBottomHead_exists {α : Type*} (rows : List (List α))
    (hne : [] ∉ rows) (hrows : rows ≠ []) : ∃ a, (eraseBottomHead rows).2 = some a := by
  induction rows with
  | nil => exact (hrows rfl).elim
  | cons row rows ih =>
      cases rows with
      | nil =>
          have hr : row ≠ [] := fun h => hne (by simp [h])
          cases row with
          | nil => exact (hr rfl).elim
          | cons a row => exact ⟨a, rfl⟩
      | cons next rows =>
          obtain ⟨a, ha⟩ := ih (fun h => hne (by simp [h])) (by simp)
          exact ⟨a, ha⟩

theorem eraseBottomHead_restore {α : Type*} (rows : List (List α))
    (hne : [] ∉ rows) {a : α} (ha : (eraseBottomHead rows).2 = some a) :
    prependToRow a (rows.length - 1) (eraseBottomHead rows).1 = rows := by
  induction rows with
  | nil => simp [eraseBottomHead] at ha
  | cons row rows ih =>
      cases rows with
      | nil =>
          have hr : row ≠ [] := fun h => hne (by simp [h])
          cases row with
          | nil => exact (hr rfl).elim
          | cons b row =>
              have hba : b = a := Option.some.inj ha
              subst b
              by_cases ht : row = []
              · subst row
                rfl
              · change prependToRow a 0 (if row = [] then [] else [row]) = [a :: row]
                simp only [if_neg ht, prependToRow]
      | cons next rows =>
          have htail : [] ∉ next :: rows := fun h => hne (by simp [h])
          have hrec := ih htail ha
          simpa only [eraseBottomHead, List.length_cons, Nat.add_sub_cancel,
            prependToRow] using congrArg (List.cons row) hrec

/-- Shifting a sorted lower row left preserves its strict relation to the
row above it: each new lower entry is at least the old one in that column. -/
theorem isRowAbove_tail_lower {upper lower : List ℕ}
    (h : upper.IsRowAbove lower) (hs : lower.SortedLE) :
    upper.IsRowAbove lower.tail := by
  refine ⟨(by rw [List.length_tail]; exact (Nat.sub_le _ _).trans h.length_le), ?_⟩
  intro j hu hl
  have hj : j + 1 < lower.length := by rw [List.length_tail] at hl; omega
  have hj0 : j < lower.length := by omega
  have hweak : lower[j] ≤ lower[j + 1] :=
    (List.pairwise_iff_getElem.mp (List.sortedLE_iff_pairwise.mp hs))
      j (j + 1) hj0 hj (Nat.lt_succ_self j)
  simpa only [List.getElem_tail] using (h.getElem_lt j hu hj0).trans_le hweak

theorem isRowAbove_eraseBottomHead_head {upper : List ℕ} {rows : List (List ℕ)}
    (h : upper.IsRowAbove (rows.headD [])) (hrows : rows.IsTableauRows) :
    upper.IsRowAbove ((eraseBottomHead rows).1.headD []) := by
  cases rows with
  | nil => exact List.isRowAbove_nil upper
  | cons lower rows =>
      cases rows with
      | nil =>
          by_cases ht : lower.tail = []
          · simp only [eraseBottomHead, if_pos ht, List.headD_nil]
            exact List.isRowAbove_nil upper
          · simp only [eraseBottomHead, if_neg ht, List.headD_cons]
            exact isRowAbove_tail_lower h ((List.isTableauRows_cons.mp hrows).2.1)
      | cons next rows => exact h

theorem eraseBottomHead_isTableau {rows : List (List ℕ)} (hrows : rows.IsTableauRows) :
    (eraseBottomHead rows).1.IsTableauRows := by
  induction rows with
  | nil => exact List.isTableauRows_nil
  | cons row rows ih =>
      obtain ⟨hne, hs, habove, htail⟩ := List.isTableauRows_cons.mp hrows
      cases rows with
      | nil =>
          by_cases ht : row.tail = []
          · simp only [eraseBottomHead, if_pos ht]
            exact List.isTableauRows_nil
          · simp only [eraseBottomHead, if_neg ht]
            refine List.isTableauRows_cons.mpr ⟨ht, ?_, List.isRowAbove_nil _,
              List.isTableauRows_nil⟩
            exact List.sortedLE_iff_pairwise.mpr
              ((List.sortedLE_iff_pairwise.mp hs).sublist (List.tail_sublist row))
      | cons next rows =>
          refine List.isTableauRows_cons.mpr
            ⟨hne, hs, isRowAbove_eraseBottomHead_head habove htail, ih htail⟩

/-- The word correspondence is literal list equality, before taking any
Knuth quotient or decrementing any letter. -/
theorem rowWordRows_eraseBottomHead {rows : List (List ℕ)}
    (hne : [] ∉ rows) {a : ℕ} (ha : (eraseBottomHead rows).2 = some a) :
    rowWordRows rows = a :: rowWordRows (eraseBottomHead rows).1 := by
  induction rows with
  | nil => simp [eraseBottomHead] at ha
  | cons row rows ih =>
      cases rows with
      | nil =>
          have hr : row ≠ [] := fun h => hne (by simp [h])
          cases row with
          | nil => exact (hr rfl).elim
          | cons b row =>
              have hba : b = a := Option.some.inj ha
              subst b
              by_cases ht : row = []
              · subst row
                rfl
              · conv_lhs => rw [rowWordRows_cons, rowWordRows_nil, List.nil_append]
                change a :: row = a :: rowWordRows (if row = [] then [] else [row])
                simp only [if_neg ht, rowWordRows_cons, rowWordRows_nil, List.nil_append]
      | cons next rows =>
          have hr := ih (fun h => hne (by simp [h])) ha
          rw [rowWordRows_cons, hr]
          simp only [eraseBottomHead, rowWordRows_cons, List.cons_append]

theorem insertionRows_rotate_rowWord {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) {a : ℕ}
    (ha : (eraseBottomHead rows).2 = some a) :
    (Lascoux.rotateHead (rowWordRows rows)).foldl (fun rows x => rowInsert x rows) [] =
      rowInsert a (eraseBottomHead rows).1 := by
  rw [rowWordRows_eraseBottomHead hrows.nil_notMem ha]
  simp only [Lascoux.rotateHead, List.foldl_append,
    fold_rowInsert_rowWordRows _ (eraseBottomHead_isTableau hrows),
    List.foldl_cons, List.foldl_nil]

/-- Ordinary rotation of a row word is injective on each fixed
semistandard shape.  The fixed predecessor shape identifies the actual
reverse-insertion corner, so the removed letter and predecessor are both
recovered before restoring the original last row. -/
theorem tableauRows_eq_of_knuth_rotate_rowWord
    {rows rows' : List (List ℕ)} (hrows : rows.IsTableauRows)
    (hrows' : rows'.IsTableauRows)
    (hshape : rows.map List.length = rows'.map List.length)
    (h : KnuthEquivalent (Lascoux.rotateHead (rowWordRows rows))
      (Lascoux.rotateHead (rowWordRows rows'))) : rows = rows' := by
  have hlen : rows.length = rows'.length := by
    simpa only [List.length_map] using congrArg List.length hshape
  by_cases hr : rows = []
  · have hr' : rows' = [] := List.length_eq_zero_iff.mp (by
      simpa only [hr, List.length_nil] using hlen.symm)
    rw [hr, hr']
  · have hr' : rows' ≠ [] := by
      intro heq
      apply hr
      exact List.length_eq_zero_iff.mp (by
        simpa only [heq, List.length_nil] using hlen)
    obtain ⟨a, ha⟩ := eraseBottomHead_exists rows hrows.nil_notMem hr
    obtain ⟨b, hb⟩ := eraseBottomHead_exists rows' hrows'.nil_notMem hr'
    have hi := h.insertionRows_eq
    rw [insertionRows_rotate_rowWord hrows ha,
      insertionRows_rotate_rowWord hrows' hb] at hi
    obtain ⟨hpre, hab⟩ := rowInsert_injective_of_same_shape
      (eraseBottomHead_isTableau hrows) (eraseBottomHead_isTableau hrows')
      (eraseBottomHead_same_shape hshape) hi
    calc
      rows = prependToRow a (rows.length - 1) (eraseBottomHead rows).1 :=
        (eraseBottomHead_restore rows hrows.nil_notMem ha).symm
      _ = prependToRow b (rows'.length - 1) (eraseBottomHead rows').1 := by
        rw [hlen, hpre, hab]
      _ = rows' := eraseBottomHead_restore rows' hrows'.nil_notMem hb

namespace Lascoux

variable {mu : YoungDiagram}

def bottomPredecessorRows (T : SemistandardYoungTableau mu) : List (List ℕ) :=
  (eraseBottomHead (semistandardRows T)).1

theorem bottomPredecessorRows_isTableau (T : SemistandardYoungTableau mu) :
    (bottomPredecessorRows T).IsTableauRows :=
  eraseBottomHead_isTableau (semistandardRows_isTableau T)

theorem bottomPredecessorRows_first (T : SemistandardYoungTableau mu)
    (hheight : 2 ≤ mu.colLen 0) :
    (bottomPredecessorRows T).headD [] = tableauRowWord T 0 := by
  rw [bottomPredecessorRows, eraseBottomHead_headD _
    (by simpa only [semistandardRows_length] using hheight)]
  rw [List.headD_eq_getD]
  exact semistandardRows_getD T 0

theorem bottomPredecessorRows_shape (T U : SemistandardYoungTableau mu) :
    (bottomPredecessorRows T).map List.length =
      (bottomPredecessorRows U).map List.length := by
  apply eraseBottomHead_same_shape
  rw [semistandardRows_map_length, semistandardRows_map_length]

theorem bottomPredecessorRows_word (T : SemistandardYoungTableau mu)
    {a : ℕ} (ha : (eraseBottomHead (semistandardRows T)).2 = some a) :
    tableauWord T = a :: rowWordRows (bottomPredecessorRows T) := by
  rw [tableauWord_eq_rowWordRows]
  exact rowWordRows_eraseBottomHead (semistandardRows_isTableau T).nil_notMem ha

theorem bottomPredecessorRows_exists (T : SemistandardYoungTableau mu)
    (hheight : 0 < mu.colLen 0) :
    ∃ a, (eraseBottomHead (semistandardRows T)).2 = some a := by
  apply eraseBottomHead_exists _ (semistandardRows_isTableau T).nil_notMem
  exact List.ne_nil_of_length_pos (by simpa only [semistandardRows_length] using hheight)

/-- The exact fixed-shape injectivity used in the balancing-path
argument.  This concerns ordinary content-preserving `rotateHead`, not
the decremented cocharge rotation. -/
theorem rotateHead_tableauWord_injective (T U : SemistandardYoungTableau mu)
    (h : KnuthEquivalent (rotateHead (tableauWord T)) (rotateHead (tableauWord U))) :
    T = U := by
  rw [tableauWord_eq_rowWordRows, tableauWord_eq_rowWordRows] at h
  have hrows := tableauRows_eq_of_knuth_rotate_rowWord
    (semistandardRows_isTableau T) (semistandardRows_isTableau U)
    (by rw [semistandardRows_map_length, semistandardRows_map_length]) h
  apply SemistandardYoungTableau.ext
  intro r j
  have he := congrArg (fun rows : List (List ℕ) => (rows.getD r []).getD j 0) hrows
  simpa only [semistandardRows_getD, tableauRowWord_getD] using he

end Lascoux
end HigherSpecht
end
end CanonicalSource35

section CanonicalSource36
/- Source: HigherSpecht/LascouxCanonicalCyclage.lean -/



/-!
# The actual canonical ordinary cycle and its terminating measure

The cycle inserts the literal rotation of a tableau's row word.  Removing
the initial letter first gives the genuine predecessor rows.  With at
least two rows this leaves the first row unchanged, so the padded numeral
strictly decreases.  This is ordinary content-preserving insertion; no
decremented cocharge rotation is substituted for it.
-/

noncomputable section
open TauCeti

namespace HigherSpecht.Lascoux

theorem knuthWord_perm {u v : List ℕ} (h : KnuthEquivalent u v) : u.Perm v := by
  induction h with
  | refl u => exact .refl _
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | append l r h ih => exact (ih.append_left l).append_right r
  | left hab hbc => exact (List.Perm.swap _ _ _).cons _
  | right hab hbc => exact List.Perm.swap _ _ _

theorem rotateHead_perm (w : List ℕ) : (rotateHead w).Perm w := by
  cases w with
  | nil => exact .refl _
  | cons a w => simpa only [rotateHead] using List.perm_append_singleton a w

@[simp] theorem rotateHead_length (w : List ℕ) : (rotateHead w).length = w.length :=
  (rotateHead_perm w).length_eq

@[simp] theorem rotateHead_count (w : List ℕ) (a : ℕ) :
    (rotateHead w).count a = w.count a := (rotateHead_perm w).count_eq a

theorem firstRow_length_lt_flatten_length (rows : List (List ℕ))
    (hrows : rows.IsTableauRows) (hheight : 2 ≤ rows.length) :
    (rows.headD []).length < rows.flatten.length := by
  cases rows with
  | nil => simp at hheight
  | cons first rows =>
      cases rows with
      | nil => simp at hheight
      | cons second rows =>
          have hne : second ≠ [] := fun h => hrows.nil_notMem (by simp [h])
          have hp : 0 < second.length := List.length_pos_iff.mpr hne
          simp only [List.headD_cons, List.flatten_cons, List.length_append]
          omega

theorem tableau_firstRow_spare_width {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (hheight : 1 < mu.colLen 0) :
    (tableauRowWord T 0).length < (tableauWord T).length := by
  have h := firstRow_length_lt_flatten_length (semistandardRows T)
    (semistandardRows_isTableau T)
    (by rw [semistandardRows_length]; omega)
  rw [List.headD_eq_getD, semistandardRows_getD] at h
  have hlen : (tableauWord T).length = (semistandardRows T).flatten.length := by
    simp only [tableauWord_eq_rowWordRows, rowWordRows, List.length_flatten,
      List.map_reverse, List.sum_reverse]
  simpa only [hlen] using h

theorem rowInsert_headD_of_ne_nil (x : ℕ) (rows : List (List ℕ)) (hne : rows ≠ []) :
    (rowInsert x rows).headD [] = (rowBump x (rows.headD [])).1 := by
  cases rows with
  | nil => exact (hne rfl).elim
  | cons row rows => exact rowInsert_firstRow x row rows

def canonicalCycleShape {mu : YoungDiagram} (T : SemistandardYoungTableau mu) :
    YoungDiagram := insertionShape (rotateHead (tableauWord T))

def canonicalCycle {mu : YoungDiagram} (T : SemistandardYoungTableau mu) :
    SemistandardYoungTableau (canonicalCycleShape T) :=
  insertionTableau (rotateHead (tableauWord T))

theorem canonicalCycle_word_knuth {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) :
    KnuthEquivalent (rotateHead (tableauWord T)) (tableauWord (canonicalCycle T)) :=
  knuth_insertionTableau _

theorem canonicalCycle_word_perm {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) :
    (tableauWord (canonicalCycle T)).Perm (tableauWord T) :=
  (knuthWord_perm (canonicalCycle_word_knuth T)).symm.trans (rotateHead_perm _)

theorem canonicalCycle_first_row {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (hheight : 1 < mu.colLen 0)
    {a : ℕ} (ha : (eraseBottomHead (semistandardRows T)).2 = some a) :
    tableauRowWord (canonicalCycle T) 0 = (rowBump a (tableauRowWord T 0)).1 := by
  have hfirst := bottomPredecessorRows_first T (by omega)
  have hpos : 0 < (tableauRowWord T 0).length := by
    rw [tableauRowWord_length]
    exact YoungDiagram.mem_iff_lt_rowLen.mp
      (YoungDiagram.mem_iff_lt_colLen.mpr (by omega) : (0, 0) ∈ mu)
  have hne : bottomPredecessorRows T ≠ [] := by
    intro heq
    rw [heq, List.headD_nil] at hfirst
    have hl := congrArg List.length hfirst
    simp only [List.length_nil] at hl
    omega
  change tableauRowWord
    (tableauOfRows (insertionRows (rotateHead (tableauWord T)))
      (insertionRows_isTableau (rotateHead (tableauWord T)))) 0 = _
  rw [tableauRowWord_tableauOfRows, ← List.headD_eq_getD]
  change (insertionRows (rotateHead (tableauWord T))).headD [] = _
  have hins := insertionRows_rotate_rowWord (semistandardRows_isTableau T) ha
  rw [← tableauWord_eq_rowWordRows] at hins
  change insertionRows (rotateHead (tableauWord T)) =
    rowInsert a (bottomPredecessorRows T) at hins
  rw [hins, rowInsert_headD_of_ne_nil _ _ hne, hfirst]

/-- The concrete natural-number descent of the canonical cycle. -/
theorem canonicalCycle_potential_lt {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (n : ℕ)
    (hheight : 1 < mu.colLen 0) (hlen : (tableauWord T).length = n)
    (hbound : ∀ a ∈ tableauWord T, a < n) :
    paddedRowValue n n (tableauRowWord (canonicalCycle T) 0) <
      paddedRowValue n n (tableauRowWord T 0) := by
  obtain ⟨a, ha⟩ := bottomPredecessorRows_exists T (by omega)
  have hword := bottomPredecessorRows_word T ha
  have hmem : a ∈ tableauWord T := by rw [hword]; simp
  rw [canonicalCycle_first_row T hheight ha]
  exact paddedRowValue_rowBump_lt n n a (tableauRowWord T 0) (hbound a hmem)
    (by simpa only [hlen] using tableau_firstRow_spare_width T hheight)

end HigherSpecht.Lascoux
end
end CanonicalSource36

section CanonicalSource37
/- Source: HigherSpecht/LascouxPathUniqueness.lean -/



/-!
# Uniqueness of the actual balancing map on semistandard tableaux

The proof descends by a concrete first-row numeral under the actual
canonical ordinary cycle.  At each step, literal Knuth invariance passes
to the inserted representative, and fixed-shape reverse insertion recovers
the original tableau.  The base case is the unique sorted one-row word of
the prescribed target content.

This establishes the path-independence needed for the tableau construction
from properties already proved for each elementary crystal split.  It
does not assert the separate catabolizability image theorem.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem exists_wordOfContent_of_list (n : ℕ) (c : ℕ → ℕ) (w : List ℕ)
    (hlen : w.length = n) (hcount : ∀ a, w.count a = c a) :
    ∃ u : WordOfContent n c, List.ofFn u.val = w := by
  subst n
  refine ⟨⟨w.get, ?_⟩, List.ofFn_get w⟩
  intro a
  simpa only [wordContent, List.ofFn_get] using hcount a

def wordOfContentOfList (n : ℕ) (c : ℕ → ℕ) (w : List ℕ)
    (hlen : w.length = n) (hcount : ∀ a, w.count a = c a) : WordOfContent n c :=
  Classical.choose (exists_wordOfContent_of_list n c w hlen hcount)

theorem wordOfContentOfList_word (n : ℕ) (c : ℕ → ℕ) (w : List ℕ)
    (hlen : w.length = n) (hcount : ∀ a, w.count a = c a) :
    List.ofFn (wordOfContentOfList n c w hlen hcount).val = w :=
  Classical.choose_spec (exists_wordOfContent_of_list n c w hlen hcount)

theorem finiteContentWord_letters_lt {n : ℕ} (c : Fin n → ℕ)
    (u : WordOfContent n (extendContent c)) :
    ∀ a ∈ List.ofFn u.val, a < n := by
  intro a ha
  have hp : 0 < wordContent u.val a := List.count_pos_iff.mpr ha
  rw [u.property] at hp
  by_contra h
  simp [extendContent, h] at hp

theorem wordOfContent_eq_of_word_eq {n : ℕ} {c : ℕ → ℕ}
    {u v : WordOfContent n c} (h : List.ofFn u.val = List.ofFn v.val) : u = v :=
  Subtype.ext (List.ofFn_injective h)

/-- Any two actually established balancing constructions agree on every
semistandard row reading.  The conclusion is equality of the output words,
not merely their shape or multiplicities. -/
theorem crystal_balancing_unique_on_tableau (n : ℕ) (c : Fin n → ℕ) (d : ℕ → ℕ)
    (e f : WordOfContent n (extendContent c) ↪ WordOfContent n d)
    (he : CrystalBalancingProperties e) (hf : CrystalBalancingProperties f)
    {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (u : WordOfContent n (extendContent c)) (hu : List.ofFn u.val = tableauWord T) :
    e u = f u := by
  have aux : ∀ k : ℕ, ∀ {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
      (u : WordOfContent n (extendContent c)),
      List.ofFn u.val = tableauWord T →
      paddedRowValue n n (tableauRowWord T 0) = k → e u = f u := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro mu T u hu hk
        obtain ⟨U, hU⟩ := he.shape T u hu
        obtain ⟨V, hV⟩ := hf.shape T u hu
        have finish (hUV : U = V) : e u = f u := by
          apply wordOfContent_eq_of_word_eq
          exact hU.trans ((congrArg tableauWord hUV).trans hV.symm)
        by_cases hheight : mu.colLen 0 ≤ 1
        · apply finish
          apply one_row_tableau_eq_of_word_counts U V hheight
          intro a
          rw [← hU, ← hV]
          exact ((e u).property a).trans ((f u).property a).symm
        · have hheight' : 1 < mu.colLen 0 := Nat.lt_of_not_ge hheight
          have hlen : (tableauWord T).length = n := by
            rw [← hu, List.length_ofFn]
          have hbound : ∀ a ∈ tableauWord T, a < n := by
            rw [← hu]
            exact finiteContentWord_letters_lt c u
          let T' := canonicalCycle T
          have hT'len : (tableauWord T').length = n :=
            (canonicalCycle_word_perm T).length_eq.trans hlen
          have hT'count : ∀ a, (tableauWord T').count a = extendContent c a := by
            intro a
            calc
              (tableauWord T').count a = (tableauWord T).count a :=
                (canonicalCycle_word_perm T).count_eq a
              _ = extendContent c a := by rw [← hu]; exact u.property a
          let u' := wordOfContentOfList n (extendContent c) (tableauWord T') hT'len hT'count
          have hu' : List.ofFn u'.val = tableauWord T' :=
            wordOfContentOfList_word n (extendContent c) _ hT'len hT'count
          have hrank : paddedRowValue n n (tableauRowWord T' 0) < k := by
            rw [← hk]
            exact canonicalCycle_potential_lt T n hheight' hlen hbound
          have heq' : e u' = f u' := ih _ hrank T' u' hu' rfl
          have hrotlen : (rotateHead (List.ofFn u.val)).length = n := by
            rw [rotateHead_length, List.length_ofFn]
          have hrotcount : ∀ a, (rotateHead (List.ofFn u.val)).count a = extendContent c a := by
            intro a
            rw [rotateHead_count]
            exact u.property a
          let v := wordOfContentOfList n (extendContent c)
            (rotateHead (List.ofFn u.val)) hrotlen hrotcount
          have hv : List.ofFn v.val = rotateHead (List.ofFn u.val) :=
            wordOfContentOfList_word n (extendContent c) _ hrotlen hrotcount
          have hnormal : KnuthEquivalent (List.ofFn v.val) (List.ofFn u'.val) := by
            rw [hv, hu, hu']
            exact canonicalCycle_word_knuth T
          have hafter : KnuthEquivalent (List.ofFn (e v).val) (List.ofFn (f v).val) := by
            have h₁ := (he.knuth v u').mpr hnormal
            have h₂ := (hf.knuth v u').mpr hnormal
            rw [heq'] at h₁
            exact h₁.trans h₂.symm
          have hrotE := he.rotation T hheight' u v hu hv
          have hrotF := hf.rotation T hheight' u v hu hv
          rw [hrotE, hrotF, hU, hV] at hafter
          exact finish (rotateHead_tableauWord_injective U V hafter)
  exact aux _ T u hu rfl

end HigherSpecht.Lascoux
end
end CanonicalSource37

section CanonicalSource38
/- Source: HigherSpecht/LascouxPartitionContent.lean -/



/-!
# Literal partition contents and their actual finite balancing programs

The content is the original row-length function of a Young diagram.
Support, total size, recursive tail, and the finite-alphabet encoding are
proved directly from the diagram; they are not separate hypotheses in
the image theorem.
-/

noncomputable section
open scoped Classical BigOperators

namespace HigherSpecht.Lascoux

def finitePartitionContent (lam : YoungDiagram) (i : Fin lam.card) : ℕ :=
  lam.rowLen i.val

theorem partitionContent_support (lam : YoungDiagram) :
    ∀ a, lam.card ≤ a → lam.rowLen a = 0 := by
  intro a ha
  exact YoungDiagram.rowLen_eq_zero_of_colLen_le ((colLen_zero_le_card lam).trans ha)

theorem extend_finitePartitionContent (lam : YoungDiagram) :
    extendContent (finitePartitionContent lam) = lam.rowLen := by
  funext a
  by_cases ha : a < lam.card
  · simp only [extendContent, dif_pos ha, finitePartitionContent]
  · simp only [extendContent, dif_neg ha,
      partitionContent_support lam a (Nat.le_of_not_gt ha)]

theorem finitePartitionContent_sum (lam : YoungDiagram) :
    ∑ i, finitePartitionContent lam i = lam.card := by
  rw [show (∑ i, finitePartitionContent lam i) =
      ∑ i ∈ Finset.range lam.card, lam.rowLen i from
        Fin.sum_univ_eq_sum_range lam.rowLen lam.card]
  exact (YoungDiagram.card_eq_sum_range_rowLen lam (colLen_zero_le_card lam)).symm

theorem exists_partitionBalancingProgram (lam : YoungDiagram) :
    Nonempty (CrystalProgram lam.card lam.rowLen (standardContent lam.card)) := by
  simpa only [extend_finitePartitionContent] using
    exists_crystal_balancing_program lam.card (finitePartitionContent lam)
      (finitePartitionContent_sum lam)

def partitionBalancingProgram (lam : YoungDiagram) :
    CrystalProgram lam.card lam.rowLen (standardContent lam.card) :=
  Classical.choice (exists_partitionBalancingProgram lam)

theorem firstContentTail_partition (lam : YoungDiagram) :
    firstContentTail (firstRowTail lam).card lam.rowLen = (firstRowTail lam).rowLen := by
  funext a
  by_cases ha : a < (firstRowTail lam).card
  · simp only [firstContentTail, if_pos ha, firstRowTail_rowLen]
  · simp only [firstContentTail, if_neg ha,
      partitionContent_support (firstRowTail lam) a (Nat.le_of_not_gt ha)]

theorem partitionContent_tail_support (lam : YoungDiagram) :
    ∀ a, (firstRowTail lam).card < a → lam.rowLen a = 0 := by
  intro a ha
  have htail := colLen_zero_le_card (firstRowTail lam)
  rw [firstRowTail_colLen] at htail
  have hheight : lam.colLen 0 ≤ a := by omega
  exact YoungDiagram.rowLen_eq_zero_of_colLen_le hheight

theorem partition_width_pos_of_card_pos (lam : YoungDiagram) (hlam : 0 < lam.card) :
    0 < lam.rowLen 0 := by
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hlam
  have h00 : (0, 0) ∈ lam := lam.up_left_mem (Nat.zero_le _) (Nat.zero_le _) hc
  exact YoungDiagram.mem_iff_lt_rowLen.mp h00

theorem partition_width_le_card (lam : YoungDiagram) : lam.rowLen 0 ≤ lam.card := by
  have h := firstRowTail_card_add_width lam
  omega

theorem firstRowTail_card_lt (lam : YoungDiagram) (hlam : 0 < lam.card) :
    (firstRowTail lam).card < lam.card := by
  have h := firstRowTail_card_add_width lam
  have hp := partition_width_pos_of_card_pos lam hlam
  omega

theorem crystal_balancing_unique_on_partition (lam : YoungDiagram) (d : ℕ → ℕ)
    (e f : WordOfContent lam.card lam.rowLen ↪ WordOfContent lam.card d)
    (he : CrystalBalancingProperties e) (hf : CrystalBalancingProperties f)
    {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (u : WordOfContent lam.card lam.rowLen) (hu : List.ofFn u.val = tableauWord T) :
    e u = f u := by
  have h := crystal_balancing_unique_on_tableau lam.card (finitePartitionContent lam) d
  rw [extend_finitePartitionContent] at h
  exact h e f he hf T u hu

end HigherSpecht.Lascoux
end
end CanonicalSource38

section CanonicalSource39
/- Source: HigherSpecht/BatteryConstruction.lean -/



/-!
# The actual battery attached to a content-constrained word

The missing colors are the excess multiplicities of the input word, sorted in
descending order.  Thus no choice of a tableau or assertion of its content is
assumed.  Appending the resulting rectangular tableau produces one fixed
partition content, independently of the input word, and the original word is
recovered by taking its prefix.
-/

noncomputable section
open scoped Classical BigOperators

namespace HigherSpecht.Lascoux

def contentExcess {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (i : Fin s) : ℕ :=
  (List.ofFn u.val).count i - lam.rowLen i.val

theorem contentExcess_add_requirement {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (i : Fin s) :
    contentExcess u i + lam.rowLen i.val = (List.ofFn u.val).count i :=
  Nat.sub_add_cancel (u.property i)

theorem contentWord_total_count {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) :
    ∑ i : Fin s, (List.ofFn u.val).count i = n := by
  have h := Multiset.sum_count_eq_card
    (s := Finset.univ) (m := (List.ofFn u.val : Multiset (Fin s)))
    (fun _ _ => Finset.mem_univ _)
  simpa only [Multiset.coe_count, Multiset.coe_card, List.length_ofFn] using h

theorem contentExcess_sum_add_card {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) :
    (∑ i : Fin s, contentExcess u i) + lam.card = n := by
  have hrow : (∑ i : Fin s, lam.rowLen i.val) = lam.card := by
    rw [Fin.sum_univ_eq_sum_range]
    exact (YoungDiagram.card_eq_sum_range_rowLen lam hheight).symm
  rw [← hrow, ← Finset.sum_add_distrib]
  simp only [contentExcess_add_requirement]
  exact contentWord_total_count u

theorem contentWord_card_le {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) : lam.card ≤ n := by
  have h := contentExcess_sum_add_card u hheight
  omega

theorem contentExcess_sum {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) :
    (∑ i : Fin s, contentExcess u i) = n - lam.card := by
  have h := contentExcess_sum_add_card u hheight
  omega

def missingColorsRaw {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) : List (Fin s) :=
  (List.ofFn (fun i : Fin s => List.replicate (contentExcess u i) i)).flatten

def missingColors {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) : List (Fin s) :=
  (missingColorsRaw u).mergeSort (· ≥ ·)

theorem missingColorsRaw_length {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) :
    (missingColorsRaw u).length = n - lam.card := by
  simp only [missingColorsRaw, List.length_flatten, List.map_ofFn,
    List.length_replicate, Function.comp_def, Fin.sum_ofFn]
  exact contentExcess_sum u hheight

theorem missingColorsRaw_count {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (a : Fin s) :
    (missingColorsRaw u).count a = contentExcess u a := by
  simp only [missingColorsRaw, List.count_flatten, List.map_ofFn, Fin.sum_ofFn]
  simp [List.count_replicate]

theorem missingColors_length {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) :
    (missingColors u).length = n - lam.card := by
  exact (List.mergeSort_perm _ _).length_eq.trans (missingColorsRaw_length u hheight)

theorem missingColors_count {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (a : Fin s) :
    (missingColors u).count a = contentExcess u a := by
  exact ((List.mergeSort_perm _ _).count_eq a).trans (missingColorsRaw_count u a)

theorem missingColors_sorted {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) : (missingColors u).SortedGE :=
  List.sortedGE_mergeSort

def missingColorAt {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s)
    (j : Fin (n - lam.card)) : Fin s :=
  (missingColors u).get ⟨j.val, by rw [missingColors_length u hheight]; exact j.isLt⟩

theorem missingColorAt_antitone {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) :
    Antitone (missingColorAt u hheight) := by
  intro j k hjk
  exact (missingColors_sorted u).pairwise.rel_get_of_le
    (show (⟨j.val, by rw [missingColors_length u hheight]; exact j.isLt⟩ :
      Fin (missingColors u).length) ≤
        ⟨k.val, by rw [missingColors_length u hheight]; exact k.isLt⟩ from hjk)

theorem missingColorAt_word {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) :
    List.ofFn (missingColorAt u hheight) = missingColors u := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, missingColors_length u hheight]
  · intro j hj hj'
    simp only [List.getElem_ofFn, missingColorAt, List.get_eq_getElem]

theorem missingColorAt_count {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) (a : Fin s) :
    (List.ofFn (missingColorAt u hheight)).count a = contentExcess u a := by
  rw [missingColorAt_word, missingColors_count]

def inputBattery {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) :
    SemistandardYoungTableau (batteryRectangle (s - 1) (n - lam.card)) :=
  omittedColorBattery (missingColorAt u hheight) (missingColorAt_antitone u hheight)

theorem inputBattery_count_add_excess {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) (a : Fin s) :
    (tableauWord (inputBattery u hheight)).count a.val + contentExcess u a =
      n - lam.card := by
  simpa only [inputBattery, missingColorAt_count] using
    omittedColorBattery_count_add_missing (missingColorAt u hheight)
      (missingColorAt_antitone u hheight) a

def contentWordNatList {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) : List ℕ := List.ofFn (fun i => (u.val i).val)

@[simp] theorem contentWordNatList_length {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) : (contentWordNatList u).length = n := by
  simp only [contentWordNatList, List.length_ofFn]

theorem contentWordNatList_count {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (a : Fin s) :
    (contentWordNatList u).count a.val = (List.ofFn u.val).count a := by
  simpa only [contentWordNatList, List.map_ofFn, Function.comp_def] using
    List.count_map_of_injective (List.ofFn u.val) Fin.val Fin.val_injective a

theorem contentWordNatList_count_eq_zero {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) {a : ℕ} (ha : s ≤ a) :
    (contentWordNatList u).count a = 0 := by
  apply List.count_eq_zero.mpr
  intro h
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
  have := (u.val i).isLt
  omega

def batteryInputList {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) : List ℕ :=
  contentWordNatList u ++ tableauWord (inputBattery u hheight)

theorem batteryInputList_length {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) :
    (batteryInputList u hheight).length = n + (s - 1) * (n - lam.card) := by
  simp only [batteryInputList, List.length_append, contentWordNatList_length,
    tableauWord_length, batteryRectangle_card]

theorem batteryInputList_count_lt {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) (a : Fin s) :
    (batteryInputList u hheight).count a.val = n - lam.card + lam.rowLen a.val := by
  rw [batteryInputList, List.count_append, contentWordNatList_count]
  have he := contentExcess_add_requirement u a
  have hb := inputBattery_count_add_excess u hheight a
  omega

theorem batteryInputList_count_ge {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) {a : ℕ} (ha : s ≤ a) :
    (batteryInputList u hheight).count a = 0 := by
  rw [batteryInputList, List.count_append, contentWordNatList_count_eq_zero u ha, zero_add]
  exact omittedColorBattery_count_eq_zero (missingColorAt u hheight)
    (missingColorAt_antitone u hheight) ha

@[simp] theorem batteryInputList_take {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) :
    (batteryInputList u hheight).take n = contentWordNatList u := by
  simpa only [batteryInputList, contentWordNatList_length] using
    (List.take_left (l₁ := contentWordNatList u)
      (l₂ := tableauWord (inputBattery u hheight)))

theorem contentWordNatList_injective {n s : ℕ} {lam : YoungDiagram} :
    Function.Injective (contentWordNatList (n := n) (lam := lam) (s := s)) := by
  intro u v h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrFun (List.ofFn_injective h) i

theorem batteryInputList_injective {n s : ℕ} {lam : YoungDiagram}
    (hheight : lam.colLen 0 ≤ s) :
    Function.Injective (fun u : ContentWord n lam s => batteryInputList u hheight) := by
  intro u v h
  apply contentWordNatList_injective
  simpa only [batteryInputList_take] using congrArg (List.take n) h

end HigherSpecht.Lascoux
end
end CanonicalSource39

section CanonicalSource40
/- Source: HigherSpecht/BatteryContentShape.lean -/



/-!
# Fixed partition content of the augmented battery word

For excess size `d`, the partition has first `s` row lengths `d + lam.rowLen i`.
The concrete appended word has that content, and its first `n` letters recover
the original content-constrained word.  No image or cardinality claim is used.
-/

noncomputable section
open scoped Classical BigOperators

namespace HigherSpecht.Lascoux

def batteryContentShape (lam : YoungDiagram) (s d : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens (List.ofFn (fun i : Fin s => d + lam.rowLen i.val))
    (List.sortedGE_ofFn_iff.mpr (by
      intro i j hij
      exact Nat.add_le_add_left (lam.rowLen_anti i.val j.val hij) d))

theorem batteryContentShape_rowLen (lam : YoungDiagram) (s d r : ℕ) :
    (batteryContentShape lam s d).rowLen r =
      if r < s then d + lam.rowLen r else 0 := by
  by_cases hr : r < s
  · rw [if_pos hr]
    exact (YoungDiagram.rowLen_ofRowLens
      (w := List.ofFn (fun i : Fin s => d + lam.rowLen i.val))
      (hw := List.sortedGE_ofFn_iff.mpr (by
        intro i j hij
        exact Nat.add_le_add_left (lam.rowLen_anti i.val j.val hij) d))
      ⟨r, by simpa only [List.length_ofFn] using hr⟩).trans
      (by simp only [Fin.getElem_fin, List.getElem_ofFn])
  · rw [if_neg hr]
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hc : (r, 0) ∈ batteryContentShape lam s d :=
      YoungDiagram.mem_iff_lt_rowLen.mpr hp
    obtain ⟨h, _⟩ := YoungDiagram.mem_ofRowLens.mp hc
    exact hr (by simpa only [List.length_ofFn] using h)

theorem batteryContentShape_height_le (lam : YoungDiagram) (s d : ℕ) :
    (batteryContentShape lam s d).colLen 0 ≤ s := by
  by_contra h
  have hc : (s, 0) ∈ batteryContentShape lam s d :=
    YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge h)
  have hp := YoungDiagram.mem_iff_lt_rowLen.mp hc
  simpa only [batteryContentShape_rowLen, lt_self_iff_false, if_false,
    Nat.lt_irrefl] using hp

theorem batteryContentShape_card (lam : YoungDiagram) (s d : ℕ)
    (hheight : lam.colLen 0 ≤ s) :
    (batteryContentShape lam s d).card = s * d + lam.card := by
  rw [YoungDiagram.card_eq_sum_range_rowLen _ (batteryContentShape_height_le lam s d)]
  have hsum : (∑ i ∈ Finset.range s, (batteryContentShape lam s d).rowLen i) =
      (Finset.range s).sum (fun i => d + lam.rowLen i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [batteryContentShape_rowLen, if_pos (Finset.mem_range.mp hi)]
  rw [hsum, Finset.sum_add_distrib,
    ← YoungDiagram.card_eq_sum_range_rowLen lam hheight]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem batteryContentShape_card_eq_inputLength {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    (batteryContentShape lam s (n - lam.card)).card =
      n + (s - 1) * (n - lam.card) := by
  rw [batteryContentShape_card lam s (n - lam.card) hheight]
  have hk := contentWord_card_le u hheight
  have hsd : s = (s - 1) + 1 := by omega
  have hmul : s * (n - lam.card) =
      (s - 1) * (n - lam.card) + (n - lam.card) := by
    calc
      s * (n - lam.card) = ((s - 1) + 1) * (n - lam.card) :=
        congrArg (fun t : ℕ => t * (n - lam.card)) hsd
      _ = (s - 1) * (n - lam.card) + (n - lam.card) := by
        simp only [Nat.add_mul, one_mul]
  rw [hmul]
  omega

theorem batteryInputList_count_shape {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hheight : lam.colLen 0 ≤ s) (a : ℕ) :
    (batteryInputList u hheight).count a =
      (batteryContentShape lam s (n - lam.card)).rowLen a := by
  rw [batteryContentShape_rowLen]
  by_cases ha : a < s
  · rw [if_pos ha]
    exact batteryInputList_count_lt u hheight ⟨a, ha⟩
  · rw [if_neg ha]
    exact batteryInputList_count_ge u hheight (Nat.le_of_not_gt ha)

/-- The complete, literal fixed-content word to which partition balancing applies. -/
def batteryInputWord {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    WordOfContent (batteryContentShape lam s (n - lam.card)).card
      (batteryContentShape lam s (n - lam.card)).rowLen :=
  wordOfContentOfList _ _ (batteryInputList u hheight)
    ((batteryInputList_length u hheight).trans
      (batteryContentShape_card_eq_inputLength u hs hheight).symm)
    (batteryInputList_count_shape u hheight)

theorem batteryInputWord_word {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    List.ofFn (batteryInputWord u hs hheight).val = batteryInputList u hheight :=
  wordOfContentOfList_word _ _ _ _ _

theorem batteryInputWord_prefix {n s : ℕ} {lam : YoungDiagram}
    (u : ContentWord n lam s) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    (List.ofFn (batteryInputWord u hs hheight).val).take n = contentWordNatList u := by
  rw [batteryInputWord_word, batteryInputList_take]

def batteryInputEmbedding (n : ℕ) (lam : YoungDiagram) (s : ℕ)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    ContentWord n lam s ↪
      WordOfContent (batteryContentShape lam s (n - lam.card)).card
        (batteryContentShape lam s (n - lam.card)).rowLen where
  toFun u := batteryInputWord u hs hheight
  inj' := by
    intro u v h
    apply batteryInputList_injective hheight
    simpa only [batteryInputWord_word] using
      congrArg (fun w => List.ofFn w.val) h

end HigherSpecht.Lascoux
end
end CanonicalSource40

section CanonicalSource41
/- Source: HigherSpecht/BatteryCatBounds.lean -/



/-!
# Actual height bounds at every stage of cyclic insertion

A terminal height bound controls every earlier pending letter and every
intermediate diagram.  Acceptance puts its label in an actual row and
rejection increases the label, so this assertion is proved backwards
through the literal machine.  It is the obstruction used to force a
standardized battery to have its genuine superstandard cocharge filling.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht

def CatStateBelow (s : ℕ) (st : CatState) : Prop :=
  st.shape.colLen 0 ≤ s ∧ ∀ a ∈ st.word, a < s

theorem catStep_below_inv {s : ℕ} {st : CatState}
    (h : CatStateBelow s (catStep st)) : CatStateBelow s st := by
  cases hw : st.word.reverse with
  | nil => simpa only [catStep, hw] using h
  | cons a rest =>
      have hword : st.word = rest.reverse ++ [a] := by
        have hh := congrArg List.reverse hw
        simpa only [List.reverse_reverse, List.reverse_cons] using hh
      by_cases ha : YoungDiagram.IsAddable st.shape (a, st.shape.rowLen a)
      · simp only [catStep, hw, if_pos ha, CatStateBelow] at h
        have hheight : st.shape.colLen 0 ≤ s := by
          have hh := h.1
          rw [ha.colLen_addCell] at hh
          split_ifs at hh <;> omega
        have hamem : (a, 0) ∈ st.shape.addCell (a, st.shape.rowLen a) :=
          (st.shape.addCell (a, st.shape.rowLen a)).up_left_mem le_rfl (Nat.zero_le _)
            (YoungDiagram.mem_addCell_self st.shape (a, st.shape.rowLen a))
        have has : a < s := (YoungDiagram.mem_iff_lt_colLen.mp hamem).trans_le h.1
        refine ⟨hheight, ?_⟩
        intro b hb
        rw [hword, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact h.2 b hb
        · exact has
      · simp only [catStep, hw, if_neg ha, CatStateBelow] at h
        refine ⟨h.1, ?_⟩
        intro b hb
        rw [hword, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact h.2 b (List.mem_cons_of_mem _ hb)
        · have hh := h.2 (b + 1) (List.mem_cons_self ..)
          omega

theorem catRun_below_inv {s : ℕ} (N : ℕ) (st : CatState)
    (h : CatStateBelow s (catRun N st)) : CatStateBelow s st := by
  induction N with
  | zero => exact h
  | succ N ih =>
      have heq : catRun (N + 1) st = catStep (catRun N st) := by
        rw [show N + 1 = 1 + N by omega, catRun_add]
        rfl
      rw [heq] at h
      apply ih
      apply catStep_below_inv
      exact h

theorem catWordOutput_all_runs_below {w : List ℕ} {nu : YoungDiagram} {s : ℕ}
    (hout : CatWordOutput w nu) (hheight : nu.colLen 0 ≤ s) (k : ℕ) :
    CatStateBelow s (catRun k ⟨w, ⊥⟩) := by
  obtain ⟨N, hN⟩ := hout
  apply catRun_below_inv N
  have heq : catRun N (catRun k ⟨w, ⊥⟩) = ⟨[], nu⟩ := by
    rw [← catRun_add, Nat.add_comm N k, catRun_add, hN, catRun_empty]
  rw [heq]
  exact ⟨hheight, by simp⟩

theorem catWordOutput_letter_lt_height {w : List ℕ} {nu : YoungDiagram}
    (hout : CatWordOutput w nu) {a : ℕ} (ha : a ∈ w) : a < nu.colLen 0 :=
  (catWordOutput_all_runs_below hout le_rfl 0).2 a ha

/-- A row which is wholly above the current diagram cannot accept a
letter; its literal rejection increases that letter. -/
theorem not_addable_above_height {mu : YoungDiagram} {a : ℕ}
    (ha : mu.colLen 0 < a) : ¬ YoungDiagram.IsAddable mu (a, mu.rowLen a) := by
  intro h
  exact (Nat.not_le_of_lt ha) h.fst_le_colLen_zero

theorem catRun_reject_constant_tail (before : List ℕ) (mu : YoungDiagram)
    (a b : ℕ) (ha : mu.colLen 0 < a) :
    catRun b ⟨before ++ List.replicate b a, mu⟩ =
      ⟨List.replicate b (a + 1) ++ before, mu⟩ := by
  induction b generalizing before with
  | zero => simp
  | succ b ih =>
      have hnot := not_addable_above_height ha
      rw [List.replicate_succ', ← List.append_assoc]
      rw [show b + 1 = b + 1 from rfl, catRun_add]
      change catRun b (catStep ⟨(before ++ List.replicate b a) ++ [a], mu⟩) = _
      rw [catStep_append, if_neg hnot]
      change catRun b ⟨((a + 1) :: before) ++ List.replicate b a, mu⟩ = _
      rw [ih]
      simp only [List.replicate_succ', List.append_assoc, List.singleton_append]

end HigherSpecht
end
end CanonicalSource41

section CanonicalSource42
/- Source: HigherSpecht/BatteryFirstPass.lean -/



/-!
# One literal pass through the original letters of a battery

Rejected letters are recorded in front of the untouched prefix.  The
recursion processes exactly the original right-to-left reading once; it
does not silently process newly rejected letters.  Each sorted battery
row has entries at its row number or the next number, and after its pass
the accepted diagram cannot extend above that row.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht

/-- Input is in actual processing order, the reverse of its word order. -/
def catPass (mu : YoungDiagram) : List ℕ → List ℕ × YoungDiagram
  | [] => ([], mu)
  | a :: rest =>
      if YoungDiagram.IsAddable mu (a, mu.rowLen a) then
        catPass (mu.addCell (a, mu.rowLen a)) rest
      else
        let result := catPass mu rest
        (result.1 ++ [a + 1], result.2)

theorem catRun_original_pass (before : List ℕ) (mu : YoungDiagram) (reading : List ℕ) :
    catRun reading.length ⟨before ++ reading.reverse, mu⟩ =
      ⟨(catPass mu reading).1 ++ before, (catPass mu reading).2⟩ := by
  induction reading generalizing before mu with
  | nil => simp [catPass]
  | cons a reading ih =>
      rw [List.length_cons, List.reverse_cons, ← List.append_assoc,
        catRun_add]
      change catRun reading.length (catStep ⟨(before ++ reading.reverse) ++ [a], mu⟩) = _
      rw [catStep_append]
      by_cases ha : YoungDiagram.IsAddable mu (a, mu.rowLen a)
      · rw [if_pos ha, ih, catPass, if_pos ha]
      · rw [if_neg ha]
        change catRun reading.length
          ⟨((a + 1) :: before) ++ reading.reverse, mu⟩ = _
        rw [ih, catPass, if_neg ha]
        simp only [List.append_assoc, List.singleton_append]

theorem addCell_height_le {mu : YoungDiagram} {a H : ℕ}
    (ha : YoungDiagram.IsAddable mu (a, mu.rowLen a))
    (hmu : mu.colLen 0 ≤ H) (haH : a < H) :
    (mu.addCell (a, mu.rowLen a)).colLen 0 ≤ H := by
  rw [ha.colLen_addCell]
  split_ifs with hrow
  · change mu.rowLen a = 0 at hrow
    have heq := ha.fst_eq_colLen
    change a = mu.colLen (mu.rowLen a) at heq
    rw [hrow] at heq
    omega
  · exact hmu

theorem catPass_height_le {mu : YoungDiagram} {H : ℕ} {reading : List ℕ}
    (hmu : mu.colLen 0 ≤ H) (hvalues : ∀ a ∈ reading, a < H) :
    (catPass mu reading).2.colLen 0 ≤ H := by
  induction reading generalizing mu with
  | nil => exact hmu
  | cons a reading ih =>
      have haH := hvalues a (List.mem_cons_self ..)
      have hrest := fun b hb => hvalues b (List.mem_cons_of_mem a hb)
      simp only [catPass]
      split_ifs with ha
      · exact ih (addCell_height_le ha hmu haH) hrest
      · exact ih hmu hrest

theorem catPass_sorted_row_height {mu : YoungDiagram} {r : ℕ} {reading : List ℕ}
    (hmu : mu.colLen 0 ≤ r) (hsort : reading.Pairwise (· ≥ ·))
    (hvalues : ∀ a ∈ reading, r ≤ a ∧ a ≤ r + 1) :
    (catPass mu reading).2.colLen 0 ≤ r + 1 := by
  induction reading generalizing mu with
  | nil => exact hmu.trans (Nat.le_succ _)
  | cons a reading ih =>
      have ha := hvalues a (List.mem_cons_self ..)
      obtain ⟨hhead, hsort⟩ := List.pairwise_cons.mp hsort
      by_cases har : a = r + 1
      · have hnot := not_addable_above_height (by omega : mu.colLen 0 < a)
        rw [catPass, if_neg hnot]
        exact ih hmu hsort (fun b hb => hvalues b (List.mem_cons_of_mem a hb))
      · have haeq : a = r := by omega
        apply catPass_height_le (hmu.trans (Nat.le_succ _))
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · omega
        · have hle := hhead b hb
          omega

def BatteryRowBounds (r : ℕ) (rows : List (List ℕ)) : Prop :=
  ∀ i (hi : i < rows.length),
    (rows[i]).SortedLE ∧ ∀ a ∈ rows[i], r + i ≤ a ∧ a ≤ r + i + 1

theorem catPass_append (mu : YoungDiagram) (xs ys : List ℕ) :
    catPass mu (xs ++ ys) =
      let first := catPass mu xs
      let second := catPass first.2 ys
      (second.1 ++ first.1, second.2) := by
  induction xs generalizing mu with
  | nil => simp [catPass]
  | cons a xs ih =>
      simp only [List.cons_append, catPass]
      split_ifs with ha
      · exact ih _
      · rw [ih]
        simp only [List.append_assoc]

theorem catPass_rows_height {mu : YoungDiagram} {r : ℕ} {rows : List (List ℕ)}
    (hmu : mu.colLen 0 ≤ r) (hrows : BatteryRowBounds r rows) :
    (catPass mu (rows.flatMap List.reverse)).2.colLen 0 ≤ r + rows.length := by
  induction rows generalizing r mu with
  | nil => simpa only [List.flatMap_nil, catPass, List.length_nil, Nat.add_zero] using hmu
  | cons row rows ih =>
      have hrow := hrows 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at hrow
      have hreading : row.reverse.Pairwise (· ≥ ·) := by
        simpa only [List.pairwise_reverse] using List.sortedLE_iff_pairwise.mp hrow.1
      have hfirst := catPass_sorted_row_height hmu hreading (by
        intro a ha
        exact hrow.2 a (List.mem_reverse.mp ha))
      have htail : BatteryRowBounds (r + 1) rows := by
        intro i hi
        have hh := hrows (i + 1) (by simpa using Nat.succ_lt_succ hi)
        change rows[i].SortedLE ∧
          ∀ a ∈ rows[i], r + (i + 1) ≤ a ∧ a ≤ r + (i + 1) + 1 at hh
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hh
      rw [List.flatMap_cons, catPass_append]
      have hout := ih hfirst htail
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 rows.length] using hout

end HigherSpecht
end
end CanonicalSource42

section CanonicalSource43
/- Source: HigherSpecht/BatteryRigidity.lean -/



/-!
# Rigidity of a battery under an actual catabolism height bound

Strict columns and the bound on every pending letter leave only the values
`r` and `r+1` in row `r`. During the first pass, the `r+1` values are read
before the `r` values and cannot be inserted. Thus before the final row the
diagram still has height at most `h-1`. Any non-superstandard entry forces
the rightmost entry of that final row to be `h`; its rejection creates the
forbidden pending label `h+1`. This proves the battery claim directly for
the literal cyclic algorithm, including an arbitrary word pre.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem tableau_row_distance {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) {r t j : ℕ} (hrt : r ≤ t)
    (hcell : (t, j) ∈ mu) : T r j + t ≤ T t j + r := by
  revert hcell
  induction t, hrt using Nat.le_induction with
  | base => intro hcell; omega
  | succ t hrt ih =>
      intro hcell
      have hcell' : (t, j) ∈ mu := mu.up_left_mem (Nat.le_succ _) le_rfl hcell
      have hstep := T.col_strict (Nat.lt_succ_self t) hcell
      change T t j < T (t + 1) j at hstep
      have hprev := ih hcell'
      omega

theorem tableau_entry_row_le {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) {r j : ℕ} (hcell : (r, j) ∈ mu) :
    r ≤ T r j := by
  have h := tableau_row_distance T (r := 0) (Nat.zero_le r) hcell
  omega

theorem battery_entry_bounds {h d : ℕ}
    (T : SemistandardYoungTableau (batteryRectangle h d)) (pre : List ℕ)
    {nu : YoungDiagram} (hout : CatWordOutput (pre ++ tableauWord T) nu)
    (hheight : nu.colLen 0 ≤ h + 1) {r j : ℕ} (hr : r < h) (hj : j < d) :
    r ≤ T r j ∧ T r j ≤ r + 1 := by
  have hcell : (r, j) ∈ batteryRectangle h d := mem_batteryRectangle.mpr ⟨hr, hj⟩
  have hh : 0 < h := by omega
  have hlast : (h - 1, j) ∈ batteryRectangle h d :=
    mem_batteryRectangle.mpr ⟨by omega, hj⟩
  have hm : T (h - 1) j ∈ pre ++ tableauWord T := by
    apply List.mem_append_right
    rw [tableauWord_eq_map_cells]
    exact List.mem_map.mpr ⟨(h - 1, j), (mem_tableauCellReading _ _).mpr hlast, rfl⟩
  have hb := (catWordOutput_all_runs_below hout hheight 0).2 _ hm
  have hd := tableau_row_distance T (r := r) (t := h - 1) (by omega) hlast
  exact ⟨tableau_entry_row_le T hcell, by omega⟩

theorem reverse_flatMap_reverse {A : Type*} (rows : List (List A)) :
    (rows.flatMap List.reverse).reverse = rows.reverse.flatten := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.flatMap_cons, List.reverse_append, List.reverse_reverse, ih,
        List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil]

theorem batteryWord_last_row {h d : ℕ}
    (T : SemistandardYoungTableau (batteryRectangle h d)) (hh : 0 < h) :
    tableauWord T = tableauRowWord T (h - 1) ++
      (((List.range (h - 1)).map (tableauRowWord T)).flatMap List.reverse).reverse := by
  rw [← tableauWord_withHeight T h (batteryRectangle_height_le h d)]
  conv_lhs =>
    arg 2
    rw [show h = (h - 1) + 1 by omega]
  rw [descendingRows, List.flatMap_cons, reverse_flatMap_reverse,
    descendingRows_eq_reverse_range, List.flatMap_def, List.map_reverse]

theorem battery_prefix_row_bounds {h d : ℕ}
    (T : SemistandardYoungTableau (batteryRectangle h d)) (pre : List ℕ)
    {nu : YoungDiagram} (hout : CatWordOutput (pre ++ tableauWord T) nu)
    (hheight : nu.colLen 0 ≤ h + 1) :
    BatteryRowBounds 0 ((List.range (h - 1)).map (tableauRowWord T)) := by
  intro r hr
  have hr' : r < h - 1 := by simpa only [List.length_map, List.length_range] using hr
  simp only [List.getElem_map, List.getElem_range, Nat.zero_add]
  refine ⟨tableauRowWord_sorted T r, ?_⟩
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
  have hjd : j < d := by
    simpa only [tableauRowWord_length, batteryRectangle_rowLen,
      if_pos (by omega : r < h)] using hj
  rw [tableauRowWord_getElem]
  exact battery_entry_bounds T pre hout hheight (by omega) hjd

theorem battery_final_right_entry_le {h d : ℕ}
    (T : SemistandardYoungTableau (batteryRectangle h d)) (pre : List ℕ)
    {nu : YoungDiagram} (hout : CatWordOutput (pre ++ tableauWord T) nu)
    (hheight : nu.colLen 0 ≤ h + 1) (hh : 0 < h) (hd : 0 < d) :
    T (h - 1) (d - 1) ≤ h - 1 := by
  have hbound := battery_entry_bounds T pre hout hheight
    (r := h - 1) (j := d - 1) (by omega) (by omega)
  by_contra hbad
  have hvalue : T (h - 1) (d - 1) = h := by omega
  let rows := (List.range (h - 1)).map (tableauRowWord T)
  let reading := rows.flatMap List.reverse
  let state := catPass (⊥ : YoungDiagram) reading
  have hfirst : catRun reading.length ⟨pre ++ tableauWord T, ⊥⟩ =
      ⟨state.1 ++ (pre ++ tableauRowWord T (h - 1)), state.2⟩ := by
    rw [batteryWord_last_row T hh, ← List.append_assoc]
    exact catRun_original_pass _ _ reading
  have hstate : state.2.colLen 0 ≤ h - 1 := by
    have hp := catPass_rows_height (mu := (⊥ : YoungDiagram)) (r := 0)
      (by simp) (battery_prefix_row_bounds T pre hout hheight)
    simpa only [List.length_map, List.length_range, Nat.zero_add] using hp
  have hrowlen : (tableauRowWord T (h - 1)).length = d := by
    rw [tableauRowWord_length, batteryRectangle_rowLen, if_pos (by omega)]
  have hrow : tableauRowWord T (h - 1) =
      (tableauRowWord T (h - 1)).take (d - 1) ++ [h] := by
    have heq := List.take_concat_get (l := tableauRowWord T (h - 1))
      (i := d - 1) (by omega)
    have htake := List.take_of_length_le hrowlen.le
    rw [show d - 1 + 1 = d by omega, htake] at heq
    simpa only [List.concat_eq_append, tableauRowWord_getElem, hvalue] using heq.symm
  have hnext : catRun (1 + reading.length) ⟨pre ++ tableauWord T, ⊥⟩ =
      ⟨(h + 1) :: (state.1 ++ pre ++ (tableauRowWord T (h - 1)).take (d - 1)),
        state.2⟩ := by
    rw [catRun_add, hfirst]
    change catStep _ = _
    conv_lhs => rw [hrow]
    rw [← List.append_assoc, ← List.append_assoc, catStep_append,
      if_neg (not_addable_above_height (by omega))]
  have hb := catWordOutput_all_runs_below hout hheight (1 + reading.length)
  rw [hnext] at hb
  exact (Nat.lt_irrefl (h + 1)) (hb.2 (h + 1) (List.mem_cons_self ..))

/-- The actual terminal height bound forces every battery entry to be its
row number. No semistandard condition on the pre is required. -/
theorem battery_superstandard_of_cat_height {h d : ℕ}
    (T : SemistandardYoungTableau (batteryRectangle h d)) (pre : List ℕ)
    {nu : YoungDiagram} (hout : CatWordOutput (pre ++ tableauWord T) nu)
    (hheight : nu.colLen 0 ≤ h + 1) (r j : ℕ)
    (hr : r < h) (hj : j < d) : T r j = r := by
  have hh : 0 < h := by omega
  have hd : 0 < d := by omega
  have hlast := battery_final_right_entry_le T pre hout hheight hh hd
  have hrow : T (h - 1) j ≤ T (h - 1) (d - 1) := by
    by_cases heq : j = d - 1
    · subst j
      exact le_rfl
    · exact T.row_weak (by omega)
        (mem_batteryRectangle.mpr ⟨by omega, by omega⟩)
  have hdist := tableau_row_distance T (r := r) (t := h - 1) (by omega)
    (mem_batteryRectangle.mpr ⟨by omega, hj⟩)
  have hlo := tableau_entry_row_le T (mem_batteryRectangle.mpr ⟨hr, hj⟩)
  omega

end HigherSpecht.Lascoux
end
end CanonicalSource43

section CanonicalSource44
/- Source: HigherSpecht/LascouxConsTableau.lean -/



/-!
# The actual tableau suffix of a reflected or lowered word

The tensor cons rule changes either the initial letter or the suffix.
When that suffix is a genuine tableau row word, the actual partial
operators preserve its shape.  Iteration yields the same fact for the
constructed signature reflection, without a shape-preservation premise.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

theorem exists_cons_tableau_of_lower (T : SemistandardYoungTableau mu) (a r : ℕ)
    {output : List ℕ} (h : (listString r).lower (a :: tableauWord T) = some output) :
    ∃ (b : ℕ) (U : SemistandardYoungTableau mu), output = b :: tableauWord U := by
  rw [listString_lower_cons] at h
  split_ifs at h with hc
  · obtain ⟨w, hw, houtput⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨U, hU⟩ := exists_tableau_of_word_lowering T r hw
    exact ⟨a, U, houtput.symm.trans (congrArg (List.cons a) hU.symm)⟩
  · obtain ⟨b, hb, houtput⟩ := Option.map_eq_some_iff.mp h
    exact ⟨b, T, houtput.symm⟩

theorem exists_cons_tableau_of_raise (T : SemistandardYoungTableau mu) (a r : ℕ)
    {output : List ℕ} (h : (listString r).raise (a :: tableauWord T) = some output) :
    ∃ (b : ℕ) (U : SemistandardYoungTableau mu), output = b :: tableauWord U := by
  rw [listString_raise_cons] at h
  split_ifs at h with hc
  · obtain ⟨w, hw, houtput⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨U, hU⟩ := exists_tableau_of_word_raising T r hw
    exact ⟨a, U, houtput.symm.trans (congrArg (List.cons a) hU.symm)⟩
  · obtain ⟨b, hb, houtput⟩ := Option.map_eq_some_iff.mp h
    exact ⟨b, T, houtput.symm⟩

theorem exists_cons_tableau_of_lowerIterate (T : SemistandardYoungTableau mu)
    (a r k : ℕ) {output : List ℕ}
    (h : (listString r).lowerIterate k (a :: tableauWord T) = some output) :
    ∃ (b : ℕ) (U : SemistandardYoungTableau mu), output = b :: tableauWord U := by
  induction k generalizing T a with
  | zero => exact ⟨a, T, (Option.some.inj h).symm⟩
  | succ k ih =>
      obtain ⟨w, hw, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, U, hU⟩ := exists_cons_tableau_of_lower T a r hw
      exact ih U b (hU ▸ hrest)

theorem exists_cons_tableau_of_raiseIterate (T : SemistandardYoungTableau mu)
    (a r k : ℕ) {output : List ℕ}
    (h : (listString r).reverse.lowerIterate k (a :: tableauWord T) = some output) :
    ∃ (b : ℕ) (U : SemistandardYoungTableau mu), output = b :: tableauWord U := by
  induction k generalizing T a with
  | zero => exact ⟨a, T, (Option.some.inj h).symm⟩
  | succ k ih =>
      obtain ⟨w, hw, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, U, hU⟩ := exists_cons_tableau_of_raise T a r hw
      exact ih U b (hU ▸ hrest)

theorem exists_cons_tableau_of_reflection (T : SemistandardYoungTableau mu) (a r : ℕ) :
    ∃ (b : ℕ) (U : SemistandardYoungTableau mu),
      (listString r).reflection (a :: tableauWord T) = b :: tableauWord U := by
  unfold StringSystem.reflection
  split_ifs with hc
  · exact exists_cons_tableau_of_lowerIterate T a r _
      ((listString r).lowerAt_spec _ (a :: tableauWord T) (Nat.sub_le _ _))
  · exact exists_cons_tableau_of_raiseIterate T a r _
      ((listString r).reverse.lowerAt_spec _ (a :: tableauWord T) (Nat.sub_le _ _))

end HigherSpecht.Lascoux
end
end CanonicalSource44

section CanonicalSource45
/- Source: HigherSpecht/LascouxTableauSuffix.lean -/



/-!
# The actual rectangular battery survives every crystal instruction

The pre is an arbitrary word.  The suffix is a genuine tableau row
word.  The tensor rule changes one pre letter or performs a genuine
tableau lowering/raising on the suffix; therefore its shape is preserved.
The final program theorem applies to the literal fixed-content embedding,
not to an independently chosen tableau map.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem exists_append_tableau_of_lower {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (pre : List ℕ) (r : ℕ)
    {output : List ℕ}
    (h : (listString r).lower (pre ++ tableauWord T) = some output) :
    ∃ (pre' : List ℕ) (U : SemistandardYoungTableau mu),
      pre'.length = pre.length ∧ output = pre' ++ tableauWord U := by
  induction pre generalizing output with
  | nil =>
      obtain ⟨U, hU⟩ := exists_tableau_of_word_lowering T r h
      exact ⟨[], U, rfl, by simpa only [List.nil_append] using hU.symm⟩
  | cons a pre ih =>
      rw [List.cons_append, listString_lower_cons] at h
      split_ifs at h with hc
      · obtain ⟨w, hw, houtput⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨pre', U, hlength, hU⟩ := ih hw
        exact ⟨a :: pre', U, congrArg Nat.succ hlength,
          houtput.symm.trans (by rw [hU]; rfl)⟩
      · obtain ⟨b, hb, houtput⟩ := Option.map_eq_some_iff.mp h
        exact ⟨b :: pre, T, rfl, houtput.symm⟩

theorem exists_append_tableau_of_raise {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (pre : List ℕ) (r : ℕ)
    {output : List ℕ}
    (h : (listString r).raise (pre ++ tableauWord T) = some output) :
    ∃ (pre' : List ℕ) (U : SemistandardYoungTableau mu),
      pre'.length = pre.length ∧ output = pre' ++ tableauWord U := by
  induction pre generalizing output with
  | nil =>
      obtain ⟨U, hU⟩ := exists_tableau_of_word_raising T r h
      exact ⟨[], U, rfl, by simpa only [List.nil_append] using hU.symm⟩
  | cons a pre ih =>
      rw [List.cons_append, listString_raise_cons] at h
      split_ifs at h with hc
      · obtain ⟨w, hw, houtput⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨pre', U, hlength, hU⟩ := ih hw
        exact ⟨a :: pre', U, congrArg Nat.succ hlength,
          houtput.symm.trans (by rw [hU]; rfl)⟩
      · obtain ⟨b, hb, houtput⟩ := Option.map_eq_some_iff.mp h
        exact ⟨b :: pre, T, rfl, houtput.symm⟩

theorem exists_append_tableau_of_lowerIterate {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (pre : List ℕ) (r k : ℕ)
    {output : List ℕ}
    (h : (listString r).lowerIterate k (pre ++ tableauWord T) = some output) :
    ∃ (pre' : List ℕ) (U : SemistandardYoungTableau mu),
      pre'.length = pre.length ∧ output = pre' ++ tableauWord U := by
  induction k generalizing T pre output with
  | zero => exact ⟨pre, T, rfl, (Option.some.inj h).symm⟩
  | succ k ih =>
      obtain ⟨w, hw, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨middle, U, hlength, hU⟩ := exists_append_tableau_of_lower T pre r hw
      obtain ⟨final, V, hlength', hV⟩ := ih U middle (hU ▸ hrest)
      exact ⟨final, V, hlength'.trans hlength, hV⟩

theorem exists_append_tableau_of_raiseIterate {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (pre : List ℕ) (r k : ℕ)
    {output : List ℕ}
    (h : (listString r).reverse.lowerIterate k (pre ++ tableauWord T) = some output) :
    ∃ (pre' : List ℕ) (U : SemistandardYoungTableau mu),
      pre'.length = pre.length ∧ output = pre' ++ tableauWord U := by
  induction k generalizing T pre output with
  | zero => exact ⟨pre, T, rfl, (Option.some.inj h).symm⟩
  | succ k ih =>
      obtain ⟨w, hw, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨middle, U, hlength, hU⟩ := exists_append_tableau_of_raise T pre r hw
      obtain ⟨final, V, hlength', hV⟩ := ih U middle (hU ▸ hrest)
      exact ⟨final, V, hlength'.trans hlength, hV⟩

theorem exists_append_tableau_of_reflection {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (pre : List ℕ) (r : ℕ) :
    ∃ (pre' : List ℕ) (U : SemistandardYoungTableau mu), pre'.length = pre.length ∧
      (listString r).reflection (pre ++ tableauWord T) = pre' ++ tableauWord U := by
  unfold StringSystem.reflection
  split_ifs with hc
  · exact exists_append_tableau_of_lowerIterate T pre r _
      ((listString r).lowerAt_spec _ _ (Nat.sub_le _ _))
  · exact exists_append_tableau_of_raiseIterate T pre r _
      ((listString r).reverse.lowerAt_spec _ _ (Nat.sub_le _ _))

def PreservesTableauSuffix {N : ℕ}
    (f : (Fin N → ℕ) → (Fin N → ℕ)) : Prop :=
  ∀ {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (pre : List ℕ) (u : Fin N → ℕ),
    List.ofFn u = pre ++ tableauWord T →
    ∃ (pre' : List ℕ) (U : SemistandardYoungTableau mu), pre'.length = pre.length ∧
      List.ofFn (f u) = pre' ++ tableauWord U

theorem PreservesTableauSuffix.id (N : ℕ) :
    PreservesTableauSuffix (id : (Fin N → ℕ) → (Fin N → ℕ)) := by
  intro mu T pre u hu
  exact ⟨pre, T, rfl, hu⟩

theorem PreservesTableauSuffix.comp {N : ℕ}
    {f g : (Fin N → ℕ) → (Fin N → ℕ)}
    (hf : PreservesTableauSuffix f) (hg : PreservesTableauSuffix g) :
    PreservesTableauSuffix (g ∘ f) := by
  intro mu T pre u hu
  obtain ⟨middle, U, hm, hU⟩ := hf T pre u hu
  obtain ⟨final, V, hf, hV⟩ := hg U middle (f u) hU
  exact ⟨final, V, hf.trans hm, hV⟩

def PreservesTableauSuffixEquiv {N : ℕ}
    (E : (Fin N → ℕ) ≃ (Fin N → ℕ)) : Prop :=
  PreservesTableauSuffix E ∧ PreservesTableauSuffix E.symm

theorem PreservesTableauSuffixEquiv.refl (N : ℕ) :
    PreservesTableauSuffixEquiv (Equiv.refl (Fin N → ℕ)) :=
  ⟨PreservesTableauSuffix.id N, PreservesTableauSuffix.id N⟩

theorem PreservesTableauSuffixEquiv.trans {N : ℕ}
    {E F : (Fin N → ℕ) ≃ (Fin N → ℕ)}
    (hE : PreservesTableauSuffixEquiv E) (hF : PreservesTableauSuffixEquiv F) :
    PreservesTableauSuffixEquiv (E.trans F) :=
  ⟨PreservesTableauSuffix.comp hE.1 hF.1,
    PreservesTableauSuffix.comp hF.2 hE.2⟩

theorem wordReflection_preserves_tableauSuffix (r N : ℕ) :
    PreservesTableauSuffixEquiv (wordReflection r N) := by
  have hf : PreservesTableauSuffix (wordReflection r N) := by
    intro mu T pre u hu
    obtain ⟨pre', U, hl, hU⟩ := exists_append_tableau_of_reflection T pre r
    exact ⟨pre', U, hl, by rw [← listString_reflection_ofFn, hu]; exact hU⟩
  refine ⟨hf, ?_⟩
  have heq : (wordReflection r N).symm = wordReflection r N := by
    apply Equiv.ext
    intro u
    apply (wordReflection r N).injective
    exact (Equiv.apply_symm_apply (wordReflection r N) u).trans
      (wordReflection_involutive r N u).symm
  rw [heq]
  intro mu T pre u hu
  exact hf T pre u hu

theorem wordSwapZero_preserves_tableauSuffix (N j : ℕ) :
    PreservesTableauSuffixEquiv (wordSwapZero N j) := by
  induction j using Nat.twoStepInduction with
  | zero => exact PreservesTableauSuffixEquiv.refl N
  | one => exact wordReflection_preserves_tableauSuffix 0 N
  | more j ih ih' =>
      exact (wordReflection_preserves_tableauSuffix (j + 1) N).trans
        (ih'.trans (wordReflection_preserves_tableauSuffix (j + 1) N))

theorem wordContentSwap_preserves_tableauSuffix (N i j : ℕ) :
    PreservesTableauSuffixEquiv (wordContentSwap N i j) := by
  unfold wordContentSwap
  split_ifs
  · exact PreservesTableauSuffixEquiv.refl N
  · exact wordSwapZero_preserves_tableauSuffix N j
  · exact wordSwapZero_preserves_tableauSuffix N i
  · exact (wordSwapZero_preserves_tableauSuffix N i).trans
      ((wordSwapZero_preserves_tableauSuffix N j).trans
        (wordSwapZero_preserves_tableauSuffix N i))

theorem wordBringPair_preserves_tableauSuffix (N i j : ℕ) :
    PreservesTableauSuffixEquiv (wordBringPair N i j) :=
  (wordContentSwap_preserves_tableauSuffix N 0 i).trans
    (wordContentSwap_preserves_tableauSuffix N 1 (Equiv.swap 0 i j))

theorem transferContentWord_tableauSuffix (N : ℕ) (c : ℕ → ℕ) (i j : ℕ)
    (hi : 1 < c i) (hj : c j = 0) {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (pre : List ℕ) (u : WordOfContent N c)
    (hu : List.ofFn u.val = pre ++ tableauWord T) :
    ∃ (pre' : List ℕ) (U : SemistandardYoungTableau mu), pre'.length = pre.length ∧
      List.ofFn (transferContentWord N c i j hi hj u) = pre' ++ tableauWord U := by
  let E := wordBringPair N i j
  let z := (wordString 0 N).lowerValue (preparedContentWord N c i j hi hj u)
  obtain ⟨p₁, T₁, hl₁, hw₁⟩ :=
    (wordBringPair_preserves_tableauSuffix N i j).1 T pre u.val hu
  have hlow : (listString 0).lower (p₁ ++ tableauWord T₁) = some (List.ofFn z) := by
    rw [← hw₁, listString_lower_ofFn]
    have h := (wordString 0 N).lowerValue_spec (preparedContentWord N c i j hi hj u)
    change (wordString 0 N).lower (E u.val) = some z at h
    rw [h]
    rfl
  obtain ⟨p₂, T₂, hl₂, hw₂⟩ := exists_append_tableau_of_lower T₁ p₁ 0 hlow
  obtain ⟨p₃, T₃, hl₃, hw₃⟩ :=
    (wordBringPair_preserves_tableauSuffix N i j).2 T₂ p₂ z hw₂
  exact ⟨p₃, T₃, hl₃.trans (hl₂.trans hl₁), hw₃⟩

/-- The suffix shape and its positional boundary survive the complete
actual balancing program, even when its pre is not a tableau word. -/
theorem CrystalProgram.tableauSuffix {K : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (N : ℕ) :
    ∀ {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
      (pre : List ℕ) (u : WordOfContent N c),
      List.ofFn u.val = pre ++ tableauWord T →
      ∃ (pre' : List ℕ) (U : SemistandardYoungTableau mu), pre'.length = pre.length ∧
        List.ofFn ((P.embedding N) u).val = pre' ++ tableauWord U := by
  induction P with
  | nil c =>
      intro mu T pre u hu
      exact ⟨pre, T, rfl, hu⟩
  | @reflect c d r hr rest ih =>
      intro mu T pre u hu
      let v := reflectionContentEmbedding N c r u
      obtain ⟨middle, U, hl, hU⟩ :=
        (wordReflection_preserves_tableauSuffix r N).1 T pre u.val hu
      obtain ⟨final, V, hl', hV⟩ := ih U middle v hU
      exact ⟨final, V, hl'.trans hl, hV⟩
  | @split c d i j hiK hjK hi hj rest ih =>
      intro mu T pre u hu
      let v := contentTransferEmbedding N c i j hi hj u
      obtain ⟨middle, U, hl, hU⟩ :=
        transferContentWord_tableauSuffix N c i j hi hj T pre u hu
      obtain ⟨final, V, hl', hV⟩ := ih U middle v hU
      exact ⟨final, V, hl'.trans hl, hV⟩

end HigherSpecht.Lascoux
end
end CanonicalSource45

section CanonicalSource46
/- Source: HigherSpecht/GreedyStandardWord.lean -/



/-!
# Deletion and rotation of an initial interval of a standard word

Every support, disjointness, and alphabet-renumbering assertion is derived
from the actual permutation of `range n`.  The final recursion is on actual
Schensted tableaux and actual cyclic outputs.  Its capacity condition is the
elementary column-injection property supplied when the original word is the
row reading of a standard tableau.
-/

noncomputable section

open TauCeti Function

namespace HigherSpecht

def greedyValueTail (upper bottom : List ℕ) (m : ℕ) : List ℕ :=
  (bottom ++ upper).map (· - m)

theorem standardWord_interval_facts {upper bottom : List ℕ} {m n : ℕ}
    (hw : (upper ++ List.range m ++ bottom).Perm (List.range n)) :
    (∀ a ∈ upper, m ≤ a ∧ a < n) ∧
    (∀ a ∈ bottom, m ≤ a ∧ a < n) ∧
    (∀ a ∈ upper, a ∉ bottom) ∧
    (∀ a, m ≤ a → a < n → a ∈ upper ∨ a ∈ bottom) := by
  have hn := hw.nodup_iff.mpr List.nodup_range
  have hleft := List.nodup_append.mp hn
  have hmid := List.nodup_append.mp hleft.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    constructor
    · by_contra h
      exact hmid.2.2 a ha a (List.mem_range.mpr (lt_of_not_ge h)) rfl
    · exact List.mem_range.mp (hw.subset (by simp [ha]))
  · intro a ha
    constructor
    · by_contra h
      exact hleft.2.2 a (by simp [List.mem_range.mpr (lt_of_not_ge h)]) a ha rfl
    · exact List.mem_range.mp (hw.subset (by simp [ha]))
  · intro a ha hb
    exact hleft.2.2 a (by simp [ha]) a hb rfl
  · intro a hma han
    have hamem := hw.mem_iff.mpr (List.mem_range.mpr han)
    simpa only [List.mem_append, List.mem_range, not_lt.mpr hma, or_false] using hamem

theorem greedyValueTail_perm {upper bottom : List ℕ} {m n : ℕ}
    (hw : (upper ++ List.range m ++ bottom).Perm (List.range n)) (hmn : m ≤ n) :
    (greedyValueTail upper bottom m).Perm (List.range (n - m)) := by
  have hrot : (List.range m ++ (bottom ++ upper)).Perm
      (upper ++ List.range m ++ bottom) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := upper) (l₂ := List.range m ++ bottom)).symm
  have h := hrot.trans hw
  have hrange : List.range n = List.range m ++ (List.range (n - m)).map (m + ·) := by
    simpa only [Nat.add_sub_of_le hmn] using
      (List.range_add (n := m) (m := n - m))
  rw [hrange, List.perm_append_left_iff] at h
  have hmap := h.map (· - m)
  simpa only [greedyValueTail, List.map_map, Function.comp_def,
    Nat.add_sub_cancel_left, List.map_id'] using hmap

theorem greedyValueTail_map_add {upper bottom : List ℕ} {m n : ℕ}
    (hw : (upper ++ List.range m ++ bottom).Perm (List.range n)) :
    (greedyValueTail upper bottom m).map (· + m) = bottom ++ upper := by
  have hf := standardWord_interval_facts hw
  rw [greedyValueTail, List.map_map]
  calc
    (bottom ++ upper).map (fun a => a - m + m) = (bottom ++ upper).map id := by
      apply List.map_congr_left
      intro a ha
      have hma := (List.mem_append.mp ha).elim (fun h => (hf.2.1 a h).1)
        (fun h => (hf.1 a h).1)
      exact Nat.sub_add_cancel hma
    _ = bottom ++ upper := List.map_id _

theorem labelledWord_greedyValueTail {upper bottom : List ℕ} {m n : ℕ}
    (hw : (upper ++ List.range m ++ bottom).Perm (List.range n))
    (hm : 0 < m) (hmupper : m ∈ upper) :
    labelledWord (greedyValueTail upper bottom m) =
      greedyTailWord (upper.map (wordCochargeLabel (upper ++ List.range m ++ bottom)))
        (bottom.map (wordCochargeLabel (upper ++ List.range m ++ bottom))) := by
  have hf := standardWord_interval_facts hw
  have hmn : m < n := (hf.1 m hmupper).2
  have hcc (a : ℕ) (ha : a ∈ bottom ++ upper) :
      wordCochargeLabel (greedyValueTail upper bottom m) (a - m) =
        wordCochargeLabel (bottom ++ upper) a := by
    have hma := (List.mem_append.mp ha).elim (fun h => (hf.2.1 a h).1)
      (fun h => (hf.1 a h).1)
    have h := wordCochargeLabel_map_add (greedyValueTail upper bottom m) m (a - m)
    rw [greedyValueTail_map_add hw, Nat.sub_add_cancel hma] at h
    exact h.symm
  unfold labelledWord greedyValueTail greedyTailWord
  rw [List.map_map, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro a ha
    change wordCochargeLabel (greedyValueTail upper bottom m) (a - m) =
      wordCochargeLabel (upper ++ List.range m ++ bottom) a
    rw [hcc a (by simp [ha])]
    have hshift := wordCochargeLabel_greedy_rotation hm hmn
      (fun a ha => (hf.1 a ha).1) (fun a ha => (hf.2.1 a ha).1)
      hf.2.2.1 hf.2.2.2 hmupper (hf.2.1 a ha).1 (hf.2.1 a ha).2
    have hnU : a ∉ upper := fun h => hf.2.2.1 a h ha
    simpa only [if_neg hnU, Nat.add_zero] using hshift.symm
  · apply List.map_congr_left
    intro a ha
    change wordCochargeLabel (greedyValueTail upper bottom m) (a - m) =
      Nat.pred (wordCochargeLabel (upper ++ List.range m ++ bottom) a)
    rw [hcc a (by simp [ha])]
    have hshift := wordCochargeLabel_greedy_rotation hm hmn
      (fun a ha => (hf.1 a ha).1) (fun a ha => (hf.2.1 a ha).1)
      hf.2.2.1 hf.2.2.2 hmupper (hf.1 a ha).1 (hf.1 a ha).2
    simp only [if_pos ha] at hshift
    rw [Nat.pred_eq_sub_one]
    omega

theorem labelledWord_initial_interval {upper bottom : List ℕ} {m n : ℕ}
    (hw : (upper ++ List.range m ++ bottom).Perm (List.range n)) :
    labelledWord (upper ++ List.range m ++ bottom) =
      upper.map (wordCochargeLabel (upper ++ List.range m ++ bottom)) ++
        List.replicate m 0 ++
          bottom.map (wordCochargeLabel (upper ++ List.range m ++ bottom)) := by
  have hf := standardWord_interval_facts hw
  have hz : (List.range m).map (wordCochargeLabel (upper ++ List.range m ++ bottom)) =
      List.replicate m 0 := by
    conv_rhs => rw [← List.length_range (n := m)]
    apply List.map_eq_replicate_iff.mpr
    intro a ha
    exact wordCochargeLabel_initial_interval (fun a ha => (hf.1 a ha).1)
      (fun a ha => (hf.2.1 a ha).1) (List.mem_range.mp ha)
  simp only [labelledWord, List.map_append, hz]

theorem wordCochargeLabel_positive_tail {upper bottom : List ℕ} {m n : ℕ}
    (hw : (upper ++ List.range m ++ bottom).Perm (List.range n))
    (hm : 0 < m) (hmupper : m ∈ upper) {a : ℕ} (ha : a ∈ upper ∨ a ∈ bottom) :
    0 < wordCochargeLabel (upper ++ List.range m ++ bottom) a := by
  have hf := standardWord_interval_facts hw
  have hma : m ≤ a := ha.elim (fun h => (hf.1 a h).1) (fun h => (hf.2.1 a h).1)
  have hle := wordCochargeLabel_mono (upper ++ List.range m ++ bottom) hma
  rw [wordCochargeLabel_first_upper hm (fun a ha => (hf.1 a ha).1)
    (fun a ha => (hf.2.1 a ha).1) hmupper] at hle
  omega

def standardWordCatShape {n : ℕ} (w : List ℕ) (hw : w.Perm (List.range n)) :
    YoungDiagram := (columnInsertion (rskPair n (permutationOfStandardWord w hw)).left).state.shape

theorem standardWordCatShape_output {n : ℕ} (w : List ℕ)
    (hw : w.Perm (List.range n)) : CatWordOutput (labelledWord w) (standardWordCatShape w hw) := by
  have h := (catWordOutput_labelledWord_rsk (permutationOfStandardWord w hw)
    (standardWordCatShape w hw)).mpr
      (columnInsertion_catTableauOutput (rskPair n (permutationOfStandardWord w hw)).left)
  simpa only [permutationValueWord_permutationOfStandardWord] using h

/-- The actual greedy row recursion, with a concrete standard insertion
tableau on the smaller alphabet.  The only geometric premise left here is
the elementary capacity inequality, proved separately from columns. -/
theorem standardWordCatShape_greedy {upper bottom : List ℕ} {m n : ℕ}
    (hw : (upper ++ List.range m ++ bottom).Perm (List.range n))
    (hm : 0 < m) (hmupper : m ∈ upper)
    (hcapacity : (labelledWord (greedyValueTail upper bottom m)).count 0 ≤ m) :
    (standardWordCatShape (upper ++ List.range m ++ bottom) hw).rowLen =
      prependRowFunction m
        (standardWordCatShape (greedyValueTail upper bottom m)
          (greedyValueTail_perm hw ((standardWord_interval_facts hw).1 m hmupper).2.le)).rowLen := by
  have hmn := (standardWord_interval_facts hw).1 m hmupper
  let tail := greedyValueTail upper bottom m
  have htail := standardWordCatShape_output tail (greedyValueTail_perm hw hmn.2.le)
  have hout := standardWordCatShape_output (upper ++ List.range m ++ bottom) hw
  rw [labelledWord_initial_interval hw] at hout
  rw [labelledWord_greedyValueTail hw hm hmupper] at htail hcapacity
  apply catWordOutput_greedy_rows _ _ m _ _ hcapacity hout htail
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact wordCochargeLabel_positive_tail hw hm hmupper (Or.inl hb)
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact wordCochargeLabel_positive_tail hw hm hmupper (Or.inr hb)

end HigherSpecht
end
end CanonicalSource46

section CanonicalSource47
/- Source: HigherSpecht/GreedyColumnCapacity.lean -/



/-!
# The column injection in the greedy catabolism recursion

In a column-strict nonnegative filling, each entry equal to one above the
bottom row lies above a distinct bottom-row zero.  This is exactly the bound
on remaining zero letters after the first greedy rotation.
-/

noncomputable section

open TauCeti Finset

namespace HigherSpecht

def bottomCell {mu : YoungDiagram} (c : ↥mu.cells) : ↥mu.cells :=
  ⟨(0, c.val.2), mu.up_left_mem (Nat.zero_le _) le_rfl c.property⟩

@[simp] theorem bottomCell_row {mu : YoungDiagram} (c : ↥mu.cells) :
    (bottomCell c).val.1 = 0 := rfl

@[simp] theorem bottomCell_col {mu : YoungDiagram} (c : ↥mu.cells) :
    (bottomCell c).val.2 = c.val.2 := rfl

theorem zero_entry_bottom {mu : YoungDiagram} (f : ↥mu.cells → ℕ)
    (hcol : ∀ {c d : ↥mu.cells}, c.val.2 = d.val.2 → c.val.1 < d.val.1 → f c < f d)
    {c : ↥mu.cells} (hc : f c = 0) : c.val.1 = 0 := by
  by_contra hrow
  have h := hcol (c := bottomCell c) (d := c) rfl (Nat.pos_of_ne_zero hrow)
  rw [hc] at h
  exact Nat.not_lt_zero _ h

theorem bottomCell_zero_of_one_above {mu : YoungDiagram} (f : ↥mu.cells → ℕ)
    (hcol : ∀ {c d : ↥mu.cells}, c.val.2 = d.val.2 → c.val.1 < d.val.1 → f c < f d)
    {c : ↥mu.cells} (hrow : 0 < c.val.1) (hc : f c = 1) : f (bottomCell c) = 0 := by
  have h := hcol (c := bottomCell c) (d := c) rfl hrow
  omega

theorem bottomCell_injective_on_level {mu : YoungDiagram} (f : ↥mu.cells → ℕ)
    (hcol : ∀ {c d : ↥mu.cells}, c.val.2 = d.val.2 → c.val.1 < d.val.1 → f c < f d)
    (a : ℕ) : Set.InjOn bottomCell {c : ↥mu.cells | f c = a} := by
  intro c hc d hd heq
  change f c = a at hc
  change f d = a at hd
  have hcolEq : c.val.2 = d.val.2 := by
    have h := congrArg (fun e : ↥mu.cells => e.val.2) heq
    simpa only [bottomCell_col] using h
  have hrowEq : c.val.1 = d.val.1 := by
    rcases lt_trichotomy c.val.1 d.val.1 with h | h | h
    · have hh := hcol hcolEq h
      simp only [hc, hd] at hh
      exact (lt_irrefl _ hh).elim
    · exact h
    · have hh := hcol hcolEq.symm h
      simp only [hc, hd] at hh
      exact (lt_irrefl _ hh).elim
  exact Subtype.ext (Prod.ext hrowEq hcolEq)

theorem card_ones_above_le_zeros {mu : YoungDiagram} (f : ↥mu.cells → ℕ)
    (hcol : ∀ {c d : ↥mu.cells}, c.val.2 = d.val.2 → c.val.1 < d.val.1 → f c < f d) :
    (univ.filter fun c : ↥mu.cells => 0 < c.val.1 ∧ f c = 1).card ≤
      (univ.filter fun c : ↥mu.cells => f c = 0).card := by
  apply Finset.card_le_card_of_injOn bottomCell
  · intro c hc
    obtain ⟨hrow, hfc⟩ := (Finset.mem_filter.mp hc).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, bottomCell_zero_of_one_above f hcol hrow hfc⟩
  · intro c hc d hd heq
    exact bottomCell_injective_on_level f hcol 1
      (Finset.mem_filter.mp hc).2.2 (Finset.mem_filter.mp hd).2.2 heq

theorem cocharge_ones_above_le_zeros {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    (univ.filter fun c : ↥mu.cells => 0 < c.val.1 ∧ cochargeFilling S c = 1).card ≤
      (univ.filter fun c : ↥mu.cells => cochargeFilling S c = 0).card :=
  card_ones_above_le_zeros (cochargeFilling S) (cochargeFilling_col_strict S)

theorem cocharge_zero_row {mu : YoungDiagram} (S : StandardYoungTableau mu)
    {c : ↥mu.cells} (hc : cochargeFilling S c = 0) : c.val.1 = 0 :=
  zero_entry_bottom (cochargeFilling S) (cochargeFilling_col_strict S) hc

end HigherSpecht
end
end CanonicalSource47

section CanonicalSource48
/- Source: HigherSpecht/GreedyInitialInterval.lean -/



/-!
# The actual initial zero interval of a standard tableau

The cut is the first positive cocharge label, with the full size used if all
labels vanish.  Its prefix is proved to be the literal one-row diagram; no
greedy-catabolism assertion is built into this definition.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau Finset

namespace HigherSpecht

def initialZeroLength {mu : YoungDiagram} (S : StandardYoungTableau mu) : ℕ :=
  if h : ∃ j : ℕ, j < mu.card ∧ 0 < ascentCount (tableauRows S) j then Nat.find h
  else mu.card

theorem initialZeroLength_le {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    initialZeroLength S ≤ mu.card := by
  unfold initialZeroLength
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

theorem initialZeroLength_pos {mu : YoungDiagram} (S : StandardYoungTableau mu)
    (hn : 0 < mu.card) : 0 < initialZeroLength S := by
  unfold initialZeroLength
  split_ifs with h
  · have hh := (Nat.find_spec h).2
    by_contra hzero
    have hz : Nat.find h = 0 := Nat.eq_zero_of_not_pos hzero
    simp only [hz, ascentCount_zero, lt_self_iff_false] at hh
  · exact hn

theorem cochargeLabel_zero_iff_initial {mu : YoungDiagram} (S : StandardYoungTableau mu)
    (i : Fin mu.card) : cochargeLabel S i = 0 ↔ i.val < initialZeroLength S := by
  unfold initialZeroLength
  split_ifs with h
  · constructor
    · intro hz
      by_contra hi
      have hm := ascentCount_mono (tableauRows S) (le_of_not_gt hi)
      have hp := (Nat.find_spec h).2
      change ascentCount (tableauRows S) i.val = 0 at hz
      omega
    · intro hi
      have hnot := Nat.find_min h hi
      change ascentCount (tableauRows S) i.val = 0
      exact Nat.eq_zero_of_not_pos (fun hp => hnot ⟨i.isLt, hp⟩)
  · have hz : cochargeLabel S i = 0 :=
      Nat.eq_zero_of_not_pos (fun hp => h ⟨i.val, i.isLt, hp⟩)
    simp only [hz, i.isLt, iff_true]

theorem first_positive_cocharge_eq_one {mu : YoungDiagram} (S : StandardYoungTableau mu)
    (hm : initialZeroLength S < mu.card) :
    cochargeLabel S ⟨initialZeroLength S, hm⟩ = 1 := by
  have hn : 0 < mu.card := lt_of_le_of_lt (Nat.zero_le _) hm
  have hpos := initialZeroLength_pos S hn
  have hprev : cochargeLabel S ⟨initialZeroLength S - 1, by omega⟩ = 0 :=
    (cochargeLabel_zero_iff_initial S _).mpr (by
      change initialZeroLength S - 1 < initialZeroLength S
      omega)
  have hne : cochargeLabel S ⟨initialZeroLength S, hm⟩ ≠ 0 := by
    intro hz
    have h := (cochargeLabel_zero_iff_initial S ⟨initialZeroLength S, hm⟩).mp hz
    change initialZeroLength S < initialZeroLength S at h
    exact (Nat.lt_irrefl _) h
  change ascentCount (tableauRows S) (initialZeroLength S) ≠ 0 at hne
  change ascentCount (tableauRows S) (initialZeroLength S - 1) = 0 at hprev
  change ascentCount (tableauRows S) (initialZeroLength S) = 1
  have hs := ascentCount_succ (tableauRows S) (initialZeroLength S - 1)
  rw [Nat.sub_add_cancel hpos, hprev] at hs
  split_ifs at hs <;> omega

theorem first_positive_above_bottom {mu : YoungDiagram} (S : StandardYoungTableau mu)
    (hm : initialZeroLength S < mu.card) :
    0 < rowIndex S.toTableau ⟨initialZeroLength S, hm⟩ := by
  have hn : 0 < mu.card := lt_of_le_of_lt (Nat.zero_le _) hm
  have hpos := initialZeroLength_pos S hn
  let previous : Fin mu.card := ⟨initialZeroLength S - 1, by omega⟩
  have hpzero := (cochargeLabel_zero_iff_initial S previous).mpr (by dsimp [previous]; omega)
  have hrow : rowIndex S.toTableau previous = 0 := by
    have hc := cocharge_zero_row S (c := S.toTableau.symm previous)
      (by simpa only [cochargeFilling, standardTableau_apply_symm] using hpzero)
    simpa only [rowIndex_def] using hc
  have hs := ascentCount_succ (tableauRows S) (initialZeroLength S - 1)
  rw [Nat.sub_add_cancel hpos] at hs
  have hone := first_positive_cocharge_eq_one S hm
  change ascentCount (tableauRows S) (initialZeroLength S) = 1 at hone
  change ascentCount (tableauRows S) (initialZeroLength S - 1) = 0 at hpzero
  rw [hone, hpzero] at hs
  have hlt : tableauRows S (initialZeroLength S - 1) <
      tableauRows S (initialZeroLength S) := by
    by_contra h
    simp only [if_neg h, Nat.zero_add] at hs
    omega
  simpa only [tableauRows, dif_pos hm, dif_pos previous.isLt, previous, hrow] using hlt

theorem youngDiagram_eq_oneRow_of_all_bottom (mu : YoungDiagram)
    (hbottom : ∀ c ∈ mu.cells, c.1 = 0) : mu = oneRowShape mu.card := by
  have hshape : mu = oneRowShape (mu.rowLen 0) := by
    apply YoungDiagram.ext
    ext c
    change c ∈ mu ↔ c ∈ oneRowShape (mu.rowLen 0)
    rw [mem_oneRowShape]
    constructor
    · intro hc
      have hr := hbottom c hc
      exact ⟨hr, by simpa only [hr] using YoungDiagram.mem_iff_lt_rowLen.mp hc⟩
    · rintro ⟨hr, hc⟩
      exact YoungDiagram.mem_iff_lt_rowLen.mpr (by simpa only [hr] using hc)
  have hcard := congrArg YoungDiagram.card hshape
  rw [oneRowShape_card] at hcard
  exact hshape.trans (congrArg oneRowShape hcard.symm)

theorem prefixShape_initialZeroLength {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    prefixShape S (initialZeroLength S) = oneRowShape (initialZeroLength S) := by
  have hshape := youngDiagram_eq_oneRow_of_all_bottom (prefixShape S (initialZeroLength S))
    (by
      intro c hc
      obtain ⟨hcmu, hlabel⟩ := (mem_prefixShape S (initialZeroLength S) c).mp hc
      let d : ↥mu.cells := ⟨c, hcmu⟩
      have hz : cochargeFilling S d = 0 :=
        (cochargeLabel_zero_iff_initial S (S d)).mpr hlabel
      exact cocharge_zero_row S hz)
  simpa only [prefixShape_card S _ (initialZeroLength_le S)] using hshape

theorem card_cocharge_zeros {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    (Finset.univ.filter fun c : ↥mu.cells => cochargeFilling S c = 0).card =
      initialZeroLength S := by
  let Z := Finset.univ.filter fun c : ↥mu.cells => cochargeFilling S c = 0
  let e : ↥Z ≃ Fin (initialZeroLength S) :=
    { toFun c := ⟨(S c.val).val,
        (cochargeLabel_zero_iff_initial S (S c.val)).mp (Finset.mem_filter.mp c.property).2⟩
      invFun i := ⟨S.toTableau.symm ⟨i.val, i.isLt.trans_le (initialZeroLength_le S)⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simp only [cochargeFilling, standardTableau_apply_symm]
          exact (cochargeLabel_zero_iff_initial S _).mpr i.isLt⟩⟩
      left_inv c := by
        apply Subtype.ext
        change S.toTableau.symm (S c.val) = c.val
        exact standardTableau_symm_apply S c.val
      right_inv i := by
        apply Fin.ext
        simp only [standardTableau_apply_symm] }
  simpa only [Fintype.card_coe, Fintype.card_fin, Z] using Fintype.card_congr e

theorem count_upper_cocharge_ones {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    (((rowReadingCells mu).filter (fun c => 0 < c.val.1)).map
      (cochargeFilling S)).count 1 =
      (Finset.univ.filter fun c : ↥mu.cells => 0 < c.val.1 ∧ cochargeFilling S c = 1).card := by
  rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  let L := ((rowReadingCells mu).filter (fun c => 0 < c.val.1)).filter
    (fun c => cochargeFilling S c == 1)
  have hn : L.Nodup := ((nodup_rowReadingCells mu).filter _).filter _
  change L.length = _
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext c
  simp [L, List.mem_toFinset, List.mem_filter, and_comm]

theorem upper_cocharge_ones_le_initialZeroLength {mu : YoungDiagram}
    (S : StandardYoungTableau mu) :
    (((rowReadingCells mu).filter (fun c => 0 < c.val.1)).map
      (cochargeFilling S)).count 1 ≤ initialZeroLength S := by
  rw [count_upper_cocharge_ones, ← card_cocharge_zeros S]
  exact cocharge_ones_above_le_zeros S

end HigherSpecht
end
end CanonicalSource48

section CanonicalSource49
/- Source: HigherSpecht/KnuthRestriction.lean -/



/-!
# Initial-alphabet restriction of Knuth words and their cyclic outputs

The restriction commutes with each elementary Knuth relation.  This supplies
the initial-alphabet step directly on words, so the catabolism induction does
not need to assume a separate restriction theorem for insertion tableaux.
-/

noncomputable section

open TauCeti Function

namespace HigherSpecht

theorem KnuthEquivalent.filter_lt {u v : List ℕ} (h : KnuthEquivalent u v) (k : ℕ) :
    KnuthEquivalent (u.filter (· < k)) (v.filter (· < k)) := by
  induction h with
  | refl u => exact .refl _
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | append l r h ih => simpa only [List.filter_append] using ih.append _ _
  | @left a b c hab hbc =>
    by_cases hc : c < k
    · have hb := hbc.trans_lt hc
      have ha := hab.trans hb
      simpa only [List.filter_cons, List.filter_nil, decide_eq_true_eq,
        if_pos ha, if_pos hb, if_pos hc] using KnuthEquivalent.left hab hbc
    · by_cases hb : b < k
      · have ha := hab.trans hb
        simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq,
          if_pos ha, if_pos hb, if_neg hc]
        exact .refl _
      · by_cases ha : a < k
        · simpa only [List.filter_cons, List.filter_nil, decide_eq_true_eq,
            if_pos ha, if_neg hb, if_neg hc] using KnuthEquivalent.refl [a]
        · simpa only [List.filter_cons, List.filter_nil, decide_eq_true_eq,
            if_neg ha, if_neg hb, if_neg hc] using KnuthEquivalent.refl []
  | @right a b c hab hbc =>
    by_cases hc : c < k
    · have hb := hbc.trans hc
      have ha := hab.trans_lt hb
      simpa only [List.filter_cons, List.filter_nil, decide_eq_true_eq,
        if_pos ha, if_pos hb, if_pos hc] using KnuthEquivalent.right hab hbc
    · by_cases hb : b < k
      · have ha := hab.trans_lt hb
        simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq,
          if_pos ha, if_pos hb, if_neg hc]
        exact .refl _
      · by_cases ha : a < k
        · simpa only [List.filter_cons, List.filter_nil, decide_eq_true_eq,
            if_pos ha, if_neg hb, if_neg hc] using KnuthEquivalent.refl [a]
        · simpa only [List.filter_cons, List.filter_nil, decide_eq_true_eq,
            if_neg ha, if_neg hb, if_neg hc] using KnuthEquivalent.refl []

theorem pair_sublist_filter_lt {a b k : ℕ} (ha : a < k) (hb : b < k) (w : List ℕ) :
    [a, b].Sublist (w.filter (· < k)) ↔ [a, b].Sublist w := by
  constructor
  · intro h
    exact h.trans List.filter_sublist
  · intro h
    simpa only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos ha, if_pos hb]
      using h.filter (· < k)

theorem wordCochargeLabel_filter_lt (w : List ℕ) {j k : ℕ} (hj : j < k) :
    wordCochargeLabel (w.filter (· < k)) j = wordCochargeLabel w j := by
  apply Finset.sum_congr rfl
  intro i hi
  have hij := Finset.mem_range.mp hi
  simp only [pair_sublist_filter_lt (a := i + 1) (b := i) (k := k)
    (by omega) (by omega) w]

theorem labelledWord_filter_lt (w : List ℕ) (k : ℕ) :
    labelledWord (w.filter (· < k)) = (w.filter (· < k)).map (wordCochargeLabel w) := by
  apply List.map_congr_left
  intro a ha
  exact wordCochargeLabel_filter_lt w (of_decide_eq_true (List.mem_filter.mp ha).2)

theorem count_labelledWord_filter_le (w : List ℕ) (k a : ℕ) :
    (labelledWord (w.filter (· < k))).count a ≤ (labelledWord w).count a := by
  rw [labelledWord_filter_lt]
  exact List.Sublist.count_le a (List.filter_sublist.map (wordCochargeLabel w))

theorem filter_lt_range (n k : ℕ) :
    (List.range n).filter (· < k) = List.range (min n k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases hn : n < k
    · have hmin : min n k = n := min_eq_left hn.le
      have hmin' : min (n + 1) k = n + 1 := min_eq_left hn
      simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hn,
        hmin, hmin', List.range_succ]
    · have hmin : min n k = k := min_eq_right (le_of_not_gt hn)
      have hmin' : min (n + 1) k = k := min_eq_right (by omega)
      simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_neg hn,
        hmin, hmin', List.append_nil]

theorem standardWord_filter_perm {n : ℕ} {w : List ℕ}
    (hw : w.Perm (List.range n)) {k : ℕ} (hk : k ≤ n) :
    (w.filter (· < k)).Perm (List.range k) := by
  simpa only [filter_lt_range, min_eq_right hk] using hw.filter (· < k)

theorem standardWordCatShape_knuth {n : ℕ} {u v : List ℕ}
    (hu : u.Perm (List.range n)) (hv : v.Perm (List.range n)) (h : KnuthEquivalent u v) :
    standardWordCatShape u hu = standardWordCatShape v hv := by
  have hk := h.labelledWord [] [] (by simpa using hu)
  simp only [List.nil_append, List.append_nil] at hk
  apply catWordOutput_unique (standardWordCatShape_output u hu)
  exact (catWordOutput_knuth_iff hk _).mpr (standardWordCatShape_output v hv)

theorem standardWordCatShape_filter_knuth {n : ℕ} {u v : List ℕ}
    (hu : u.Perm (List.range n)) (hv : v.Perm (List.range n)) (h : KnuthEquivalent u v)
    {k : ℕ} (hk : k ≤ n) :
    standardWordCatShape (u.filter (· < k)) (standardWord_filter_perm hu hk) =
      standardWordCatShape (v.filter (· < k)) (standardWord_filter_perm hv hk) :=
  standardWordCatShape_knuth _ _ (h.filter_lt k)

theorem greedyValueTail_filter {upper bottom : List ℕ} {m k : ℕ} (hmk : m ≤ k)
    (hupper : ∀ a ∈ upper, m ≤ a) (hbottom : ∀ a ∈ bottom, m ≤ a) :
    (greedyValueTail upper bottom m).filter (· < k - m) =
      greedyValueTail (upper.filter (· < k)) (bottom.filter (· < k)) m := by
  unfold greedyValueTail
  rw [List.filter_map, List.filter_append]
  apply congrArg (List.map (· - m))
  congr 1
  · apply List.filter_congr
    intro a ha
    have hma := hbottom a ha
    change decide (a - m < k - m) = decide (a < k)
    simp only [decide_eq_decide]
    omega
  · apply List.filter_congr
    intro a ha
    have hma := hupper a ha
    change decide (a - m < k - m) = decide (a < k)
    simp only [decide_eq_decide]
    omega

end HigherSpecht
end
end CanonicalSource49

section CanonicalSource50
/- Source: HigherSpecht/TableauGreedyDecomposition.lean -/



/-!
# The actual row-word decomposition used by greedy catabolism

The upper rows and the positive tail of the bottom row are defined by literal
cell filters.  The deleted interval is proved to be `range m`, and the capacity
bound is the column injection, rather than a hypothesis about catabolizability.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau Function Finset

namespace HigherSpecht

theorem filter_split_of_pairwise_pred {alpha : Type*} (p : alpha → Prop) [DecidablePred p]
    (w : List alpha) (hw : w.Pairwise (fun a b => p b → p a)) :
    w.filter p ++ w.filter (fun a => ¬ p a) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hw
    by_cases hpa : p a
    · simpa only [List.filter_cons, decide_eq_true_eq, if_pos hpa,
        if_neg (not_not_intro hpa), List.cons_append] using congrArg (List.cons a) (ih ht)
    · have hnone : ∀ b ∈ w, ¬ p b := fun b hb hp => hpa (ha b hb hp)
      have hz : w.filter p = [] := List.filter_eq_nil_iff.mpr (by simpa using hnone)
      have hall : w.filter (fun b => ¬ p b) = w := List.filter_eq_self.mpr (by simpa using hnone)
      simp only [List.filter_cons, decide_eq_true_eq, if_neg hpa, if_pos hpa,
        hz, hall, List.nil_append]

def upperValueWord {mu : YoungDiagram} (S : StandardYoungTableau mu) : List ℕ :=
  ((rowReadingCells mu).filter (fun c => 0 < c.val.1)).map (fun c => (S c).val)

def bottomValueWord {mu : YoungDiagram} (S : StandardYoungTableau mu) : List ℕ :=
  ((rowReadingCells mu).filter (fun c => c.val.1 = 0)).map (fun c => (S c).val)

def bottomTailValueWord {mu : YoungDiagram} (S : StandardYoungTableau mu) : List ℕ :=
  (bottomValueWord S).filter (fun a => initialZeroLength S ≤ a)

theorem tableauValueWord_perm {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    (tableauValueWord S).Perm (List.range mu.card) := by
  apply (List.perm_ext_iff_of_nodup
    ((nodup_rowReadingCells mu).map (Fin.val_injective.comp S.toTableau.injective))
    List.nodup_range).mpr
  intro a
  simp only [tableauValueWord, List.mem_map, mem_rowReadingCells, true_and, List.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact (S c).isLt
  · intro ha
    exact ⟨S.toTableau.symm ⟨a, ha⟩, congrArg Fin.val (standardTableau_apply_symm S _)⟩

theorem tableauValueWord_upper_bottom {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    tableauValueWord S = upperValueWord S ++ bottomValueWord S := by
  have hpair : (rowReadingCells mu).Pairwise (fun c d : ↥mu.cells =>
      0 < d.val.1 → 0 < c.val.1) :=
    (pairwise_rowReadingCells mu).imp (fun h hd => by rcases h with h | h <;> omega)
  have hs := filter_split_of_pairwise_pred (fun c : ↥mu.cells => 0 < c.val.1)
    (rowReadingCells mu) hpair
  have hn : (fun c : ↥mu.cells => decide (¬ 0 < c.val.1)) =
      (fun c => decide (c.val.1 = 0)) := by
    funext c
    change decide (¬ 0 < c.val.1) = decide (c.val.1 = 0)
    simp only [decide_eq_decide]
    omega
  rw [hn] at hs
  simpa only [tableauValueWord, upperValueWord, bottomValueWord, List.map_append] using
    (congrArg (List.map (fun c : ↥mu.cells => (S c).val)) hs).symm

theorem bottomValueWord_pairwise {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    (bottomValueWord S).Pairwise (· < ·) := by
  have hstrict : (rowReadingCells mu).Pairwise (fun c d : ↥mu.cells =>
      d.val.1 < c.val.1 ∨ (c.val.1 = d.val.1 ∧ c.val.2 < d.val.2)) := by
    rw [rowReadingCells_eq_expansion]
    exact pairwise_rowExpansion mu (mu.rowLen 0)
  have hp := hstrict.filter (fun c => c.val.1 = 0)
  have hvalue : ((rowReadingCells mu).filter (fun c => c.val.1 = 0)).Pairwise
      (fun c d : ↥mu.cells => (S c).val < (S d).val) := by
    apply hp.imp_of_mem
    intro c d hc hd hcd
    have hcr := of_decide_eq_true (List.mem_filter.mp hc).2
    have hdr := of_decide_eq_true (List.mem_filter.mp hd).2
    rcases hcd with h | ⟨hr, hcol⟩
    · omega
    · exact S.lt_of_colIndex_lt
        (by simpa only [rowIndex_standard_apply] using hr)
        (by simpa only [colIndex_standard_apply] using hcol)
  exact hvalue.map (fun c => (S c).val) (fun _ _ h => h)

theorem bottomValueWord_initial_interval {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    (bottomValueWord S).filter (· < initialZeroLength S) = List.range (initialZeroLength S) := by
  have hp := (bottomValueWord_pairwise S).filter (· < initialZeroLength S)
  have hmemb (a : ℕ) : a ∈ (bottomValueWord S).filter (· < initialZeroLength S) ↔
      a < initialZeroLength S := by
    constructor
    · intro h
      exact of_decide_eq_true (List.mem_filter.mp h).2
    · intro ha
      have han : a < mu.card := ha.trans_le (initialZeroLength_le S)
      let c := S.toTableau.symm ⟨a, han⟩
      have hc : cochargeFilling S c = 0 := by
        rw [cochargeFilling, standardTableau_apply_symm]
        exact (cochargeLabel_zero_iff_initial S _).mpr ha
      apply List.mem_filter.mpr
      refine ⟨List.mem_map.mpr ⟨c, ?_, ?_⟩,
        by simpa only [decide_eq_true_eq] using ha⟩
      · exact List.mem_filter.mpr ⟨mem_rowReadingCells c,
          by simpa only [decide_eq_true_eq] using cocharge_zero_row S hc⟩
      · exact congrArg Fin.val (standardTableau_apply_symm S _)
  have hperm := (List.perm_ext_iff_of_nodup (hp.imp (fun h => Nat.ne_of_lt h))
    List.nodup_range).mpr (fun a => (hmemb a).trans List.mem_range.symm)
  exact hperm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => Nat.le_antisymm h₁ h₂)
    (hp.imp Nat.le_of_lt) List.pairwise_le_range

theorem bottomValueWord_split {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    bottomValueWord S = List.range (initialZeroLength S) ++ bottomTailValueWord S := by
  have hp : (bottomValueWord S).Pairwise (fun a b =>
      b < initialZeroLength S → a < initialZeroLength S) :=
    (bottomValueWord_pairwise S).imp (fun h hb => h.trans hb)
  have h := filter_split_of_pairwise_pred (· < initialZeroLength S) (bottomValueWord S) hp
  rw [bottomValueWord_initial_interval] at h
  simpa only [bottomTailValueWord, not_lt] using h.symm

theorem tableauValueWord_greedy_split {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    tableauValueWord S = upperValueWord S ++ List.range (initialZeroLength S) ++
      bottomTailValueWord S := by
  rw [tableauValueWord_upper_bottom, bottomValueWord_split, List.append_assoc]

theorem initialZeroLength_mem_upper {mu : YoungDiagram} (S : StandardYoungTableau mu)
    (hm : initialZeroLength S < mu.card) : initialZeroLength S ∈ upperValueWord S := by
  let c := S.toTableau.symm ⟨initialZeroLength S, hm⟩
  refine List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨mem_rowReadingCells c, ?_⟩, ?_⟩
  · simpa only [decide_eq_true_eq, c, rowIndex_def] using
      first_positive_above_bottom S hm
  · exact congrArg Fin.val (standardTableau_apply_symm S _)

theorem upperValueWord_labels {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    (upperValueWord S).map (wordCochargeLabel (tableauValueWord S)) =
      ((rowReadingCells mu).filter (fun c => 0 < c.val.1)).map (cochargeFilling S) := by
  rw [upperValueWord, List.map_map]
  apply List.map_congr_left
  intro c hc
  exact tableauValueWord_cochargeLabel S (S c)

theorem count_pred_zero_of_positive (w : List ℕ) (hw : ∀ a ∈ w, 0 < a) :
    (w.map Nat.pred).count 0 = w.count 1 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha := hw a (by simp)
    have ht : ∀ b ∈ w, 0 < b := fun b hb => hw b (by simp [hb])
    have heq : a.pred = 0 ↔ a = 1 := by
      rw [Nat.pred_eq_sub_one]
      omega
    simp only [List.map_cons, List.count_cons, ih ht, beq_iff_eq, heq]

theorem tableauGreedy_capacity {mu : YoungDiagram} (S : StandardYoungTableau mu)
    (hm : initialZeroLength S < mu.card) :
    (labelledWord (greedyValueTail (upperValueWord S) (bottomTailValueWord S)
      (initialZeroLength S))).count 0 ≤ initialZeroLength S := by
  have hw : List.Perm
      (upperValueWord S ++ List.range (initialZeroLength S) ++ bottomTailValueWord S)
      (List.range mu.card) := by
    rw [← tableauValueWord_greedy_split]
    exact tableauValueWord_perm S
  have hpos := initialZeroLength_pos S (by omega)
  have hmem := initialZeroLength_mem_upper S hm
  have hU : ∀ a ∈ (upperValueWord S).map (wordCochargeLabel (tableauValueWord S)), 0 < a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [tableauValueWord_greedy_split]
    exact wordCochargeLabel_positive_tail hw hpos hmem (Or.inl hb)
  have hB : 0 ∉ (bottomTailValueWord S).map (wordCochargeLabel (tableauValueWord S)) := by
    intro ha
    obtain ⟨b, hb, heq⟩ := List.mem_map.mp ha
    have hp := wordCochargeLabel_positive_tail hw hpos hmem (Or.inr hb)
    rw [← tableauValueWord_greedy_split, heq] at hp
    exact Nat.not_lt_zero _ hp
  rw [labelledWord_greedyValueTail hw hpos hmem, ← tableauValueWord_greedy_split,
    greedyTailWord, List.count_append, List.count_eq_zero.mpr hB,
    count_pred_zero_of_positive _ hU, Nat.zero_add, upperValueWord_labels]
  exact upper_cocharge_ones_le_initialZeroLength S

end HigherSpecht
end
end CanonicalSource50

section CanonicalSource51
/- Source: HigherSpecht/CatPrefixRecursion.lean -/



/-!
# Prefix restriction of the actual cyclic catabolism output

The induction is on the number of letters.  Its recursive input is the
literal first greedy tail, whose permutation, labels, and capacity have been
proved separately.  Knuth restriction permits the same induction for every
standard word, while the final tableau statement uses its actual row word.
-/

noncomputable section

open TauCeti Finset Function

namespace HigherSpecht

def rowPrefixSum (nu : YoungDiagram) (r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range r, nu.rowLen j

theorem sum_prependRowFunction (m r : ℕ) (f : ℕ → ℕ) :
    (∑ j ∈ Finset.range (r + 1), prependRowFunction m f j) =
      m + ∑ j ∈ Finset.range r, f j := by
  rw [Finset.sum_range_succ']
  simp only [prependRowFunction_zero, prependRowFunction_succ, Nat.add_comm]

theorem rowPrefixSum_oneRow (m r : ℕ) :
    rowPrefixSum (oneRowShape m) (r + 1) = m := by
  rw [rowPrefixSum, Finset.sum_range_succ']
  simp only [oneRowShape_rowLen, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, if_false, Finset.sum_const_zero, if_pos rfl, if_true, Nat.zero_add]

theorem standardWordCatShape_eq_oneRow_of_zero {n : ℕ} {w : List ℕ}
    (hw : w.Perm (List.range n)) (hz : ∀ a ∈ w, wordCochargeLabel w a = 0) :
    standardWordCatShape w hw = oneRowShape n := by
  have heq : labelledWord w = List.replicate n 0 := by
    unfold labelledWord
    have hlen := hw.length_eq.trans (List.length_range (n := n))
    simpa only [hlen] using List.map_eq_replicate_iff.mpr hz
  exact catWordOutput_unique ((heq ▸ standardWordCatShape_output w hw))
    (catWordOutput_replicate_zero n)

theorem wordCochargeLabel_range (n a : ℕ) : wordCochargeLabel (List.range n) a = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  simp [reverse_pair_not_sublist_range]

theorem standardWordCatShape_range (n : ℕ) :
    standardWordCatShape (List.range n) (.refl _) = oneRowShape n :=
  standardWordCatShape_eq_oneRow_of_zero (.refl _) (fun a _ => wordCochargeLabel_range n a)

theorem standardWordCatShape_congr {n : ℕ} {u v : List ℕ}
    (hu : u.Perm (List.range n)) (hv : v.Perm (List.range n)) (h : u = v) :
    standardWordCatShape u hu = standardWordCatShape v hv := by
  cases h
  rfl

def WordPrefixRestriction {n : ℕ} (w : List ℕ) (hw : w.Perm (List.range n)) : Prop :=
  ∀ (k : ℕ) (hk : k ≤ n) (r : ℕ),
    rowPrefixSum (standardWordCatShape (w.filter (· < k)) (standardWord_filter_perm hw hk)) r =
      min k (rowPrefixSum (standardWordCatShape w hw) r)

theorem WordPrefixRestriction.of_knuth {n : ℕ} {u v : List ℕ}
    {hu : u.Perm (List.range n)} {hv : v.Perm (List.range n)}
    (h : KnuthEquivalent u v) (hvR : WordPrefixRestriction v hv) :
    WordPrefixRestriction u hu := by
  intro k hk r
  rw [standardWordCatShape_filter_knuth hu hv h hk, standardWordCatShape_knuth hu hv h]
  exact hvR k hk r

theorem tableauWord_restriction_from_smaller {mu : YoungDiagram}
    (S : StandardYoungTableau mu)
    (ih : ∀ n < mu.card, ∀ (w : List ℕ) (hw : w.Perm (List.range n)), WordPrefixRestriction w hw) :
    WordPrefixRestriction (tableauValueWord S) (tableauValueWord_perm S) := by
  let m := initialZeroLength S
  let U := upperValueWord S
  let B := bottomTailValueWord S
  let W := tableauValueWord S
  have hsplit : W = U ++ List.range m ++ B := tableauValueWord_greedy_split S
  have hw : (U ++ List.range m ++ B).Perm (List.range mu.card) :=
    hsplit ▸ tableauValueWord_perm S
  have hW : standardWordCatShape W (tableauValueWord_perm S) =
      standardWordCatShape (U ++ List.range m ++ B) hw :=
    standardWordCatShape_congr (tableauValueWord_perm S) hw hsplit
  have hmlt_or_eq := lt_or_eq_of_le (initialZeroLength_le S)
  rcases hmlt_or_eq with hmlt | hmeq
  · have hm : 0 < m := initialZeroLength_pos S (by omega)
    have hmU : m ∈ U := initialZeroLength_mem_upper S hmlt
    have hcap : (labelledWord (greedyValueTail U B m)).count 0 ≤ m := tableauGreedy_capacity S hmlt
    have hf := standardWord_interval_facts hw
    have hfull := standardWordCatShape_greedy hw hm hmU hcap
    let V := greedyValueTail U B m
    have hv : V.Perm (List.range (mu.card - m)) := greedyValueTail_perm hw hmlt.le
    have hVR := ih (mu.card - m) (by omega) V hv
    intro k hk r
    change rowPrefixSum (standardWordCatShape (W.filter (· < k)) _) r =
      min k (rowPrefixSum (standardWordCatShape W _) r)
    by_cases hkm : k ≤ m
    · have hfilter : W.filter (· < k) = List.range k := by
        have hU : U.filter (· < k) = [] := List.filter_eq_nil_iff.mpr (by
          intro a ha
          have hma := (hf.1 a ha).1
          simpa only [decide_eq_true_eq] using (show ¬ a < k by omega))
        have hB : B.filter (· < k) = [] := List.filter_eq_nil_iff.mpr (by
          intro a ha
          have hma := (hf.2.1 a ha).1
          simpa only [decide_eq_true_eq] using (show ¬ a < k by omega))
        rw [hsplit, List.filter_append, List.filter_append, hU, hB, filter_lt_range,
          min_eq_right hkm, List.nil_append, List.append_nil]
      rw [standardWordCatShape_congr
        (standardWord_filter_perm (tableauValueWord_perm S) hk) (.refl _) hfilter,
        standardWordCatShape_range]
      cases r with
      | zero => simp [rowPrefixSum]
      | succ r =>
        rw [rowPrefixSum_oneRow]
        have hsum : rowPrefixSum (standardWordCatShape W (tableauValueWord_perm S)) (r + 1) =
            m + rowPrefixSum (standardWordCatShape V hv) r := by
          unfold rowPrefixSum
          rw [hW, hfull, sum_prependRowFunction]
        rw [hsum, min_eq_left (by omega)]
    · have hmk : m < k := lt_of_not_ge hkm
      let Uk := U.filter (· < k)
      let Bk := B.filter (· < k)
      have hfilter : W.filter (· < k) = Uk ++ List.range m ++ Bk := by
        rw [hsplit, List.filter_append, List.filter_append, filter_lt_range, min_eq_left hmk.le]
      have hwk : (Uk ++ List.range m ++ Bk).Perm (List.range k) :=
        hfilter ▸ standardWord_filter_perm (tableauValueWord_perm S) hk
      have hWk : standardWordCatShape (W.filter (· < k))
          (standardWord_filter_perm (tableauValueWord_perm S) hk) =
          standardWordCatShape (Uk ++ List.range m ++ Bk) hwk :=
        standardWordCatShape_congr
          (standardWord_filter_perm (tableauValueWord_perm S) hk) hwk hfilter
      have hmUk : m ∈ Uk := List.mem_filter.mpr
        ⟨hmU, by simpa only [decide_eq_true_eq] using hmk⟩
      have hVfilter : V.filter (· < k - m) = greedyValueTail Uk Bk m :=
        greedyValueTail_filter hmk.le (fun a ha => (hf.1 a ha).1)
          (fun a ha => (hf.2.1 a ha).1)
      have hcapk : (labelledWord (greedyValueTail Uk Bk m)).count 0 ≤ m := by
        rw [← hVfilter]
        exact (count_labelledWord_filter_le V (k - m) 0).trans hcap
      have hsmall := standardWordCatShape_greedy hwk hm hmUk hcapk
      have hVk : standardWordCatShape (V.filter (· < k - m))
          (standardWord_filter_perm hv (Nat.sub_le_sub_right hk m)) =
          standardWordCatShape (greedyValueTail Uk Bk m) (greedyValueTail_perm hwk hmk.le) :=
        standardWordCatShape_congr
          (standardWord_filter_perm hv (Nat.sub_le_sub_right hk m))
          (greedyValueTail_perm hwk hmk.le) hVfilter
      have hrec := hVR (k - m) (Nat.sub_le_sub_right hk m)
      cases r with
      | zero => simp [rowPrefixSum]
      | succ r =>
        have hsumfull : rowPrefixSum (standardWordCatShape W (tableauValueWord_perm S)) (r + 1) =
            m + rowPrefixSum (standardWordCatShape V hv) r := by
          unfold rowPrefixSum
          rw [hW, hfull, sum_prependRowFunction]
        have hsumsmall : rowPrefixSum (standardWordCatShape (W.filter (· < k))
            (standardWord_filter_perm (tableauValueWord_perm S) hk)) (r + 1) =
            m + rowPrefixSum (standardWordCatShape (V.filter (· < k - m))
              (standardWord_filter_perm hv (Nat.sub_le_sub_right hk m))) r := by
          unfold rowPrefixSum
          rw [hWk, hsmall, sum_prependRowFunction, ← hVk]
        rw [hsumsmall, hsumfull, hrec r]
        omega
  · have hz : ∀ a ∈ W, wordCochargeLabel W a = 0 := by
      intro a ha
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      rw [tableauValueWord_cochargeLabel]
      exact (cochargeLabel_zero_iff_initial S (S c)).mpr (by rw [hmeq]; exact (S c).isLt)
    have hshape := standardWordCatShape_eq_oneRow_of_zero (tableauValueWord_perm S) hz
    intro k hk r
    have hzero : ∀ a ∈ W.filter (· < k), wordCochargeLabel (W.filter (· < k)) a = 0 := by
      intro a ha
      rw [wordCochargeLabel_filter_lt W (of_decide_eq_true (List.mem_filter.mp ha).2)]
      exact hz a (List.mem_filter.mp ha).1
    rw [standardWordCatShape_eq_oneRow_of_zero _ hzero, hshape]
    cases r with
    | zero => simp [rowPrefixSum]
    | succ r => rw [rowPrefixSum_oneRow, rowPrefixSum_oneRow, min_eq_left hk]

/-- Every initial-alphabet restriction truncates the actual output partition
in row-superstandard order, expressed by its complete row-prefix sums. -/
theorem standardWordCatShape_prefix (n : ℕ) (w : List ℕ)
    (hw : w.Perm (List.range n)) : WordPrefixRestriction w hw := by
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    let sigma := permutationOfStandardWord w hw
    let P := rskPair n sigma
    have hcard : P.shape.card = n := P.card_eq
    have hknuth : KnuthEquivalent w (tableauValueWord P.left) := by
      simpa only [sigma, permutationValueWord_permutationOfStandardWord] using
        rskPair_left_valueWord_knuth sigma
    have htarget := tableauWord_restriction_from_smaller P.left (by
      intro m hm v hv
      exact ih m (by simpa only [hcard] using hm) v hv)
    have hvalue : (tableauValueWord P.left).Perm (List.range n) := by
      simpa only [hcard] using tableauValueWord_perm P.left
    exact WordPrefixRestriction.of_knuth hknuth (by simpa only [hcard] using htarget)

end HigherSpecht
end
end CanonicalSource51

section CanonicalSource52
/- Source: HigherSpecht/LascouxGluedCatabolism.lean -/



/-!
# Catabolism after attaching an actual standard first row

The literal word consists of the smaller tableau's entries shifted by
`m`, followed by `0,...,m-1`.  Its cocharge word is the smaller cocharge
word shifted by one followed by `m` zeros.  The capacity bound is derived
from the actual smaller tableau, and the already proved machine recursion
then gives every output row and the required dominance comparison.
-/

noncomputable section
open scoped Classical BigOperators

namespace HigherSpecht.Lascoux

theorem glued_standardWord_perm {M : ℕ} {w : List ℕ}
    (hw : w.Perm (List.range M)) (m : ℕ) :
    (w.map (fun a => a + m) ++ List.range m).Perm (List.range (M + m)) := by
  have hmap := hw.map (fun a => a + m)
  have hrot : (w.map (fun a => a + m) ++ List.range m).Perm
      (List.range m ++ w.map (fun a => a + m)) := List.perm_append_comm
  apply hrot.trans
  have h := (hmap.append_left (List.range m))
  have hrange : List.range m ++ (List.range M).map (fun a => a + m) =
      List.range (M + m) := by
    simpa only [Nat.add_comm] using (List.range_add (n := m) (m := M)).symm
  simpa only [hrange] using h

theorem labelledWord_glued_standard {M : ℕ} {w : List ℕ}
    (hw : w.Perm (List.range M)) (m : ℕ) (hm : 0 < m) :
    labelledWord (w.map (fun a => a + m) ++ List.range m) =
      (labelledWord w).map Nat.succ ++ List.replicate m 0 := by
  by_cases hM : M = 0
  · subst M
    have hw0 : w = [] := List.length_eq_zero_iff.mp
      (by simpa only [List.length_range] using hw.length_eq)
    subst w
    simp only [List.map_nil, List.nil_append, labelledWord]
    have hz : (List.range m).map (wordCochargeLabel (List.range m)) =
        List.replicate m 0 := by
      conv_rhs => rw [← List.length_range (n := m)]
      apply List.map_eq_replicate_iff.mpr
      intro a ha
      exact wordCochargeLabel_range m a
    simpa only [List.map_nil, List.nil_append] using hz
  · let upper := w.map (fun a => a + m)
    have hfull : (upper ++ List.range m ++ []).Perm (List.range (M + m)) := by
      simpa only [List.append_nil] using glued_standardWord_perm hw m
    have hmupper : m ∈ upper := by
      have hz : 0 ∈ w := hw.mem_iff.mpr (List.mem_range.mpr (Nat.pos_of_ne_zero hM))
      exact List.mem_map.mpr ⟨0, hz, Nat.zero_add m⟩
    have htail : greedyValueTail upper [] m = w := by
      simp only [greedyValueTail, List.nil_append, upper, List.map_map,
        Function.comp_def, Nat.add_sub_cancel, List.map_id']
    let labels := upper.map (wordCochargeLabel (upper ++ List.range m ++ []))
    have hpos : ∀ a ∈ labels, 0 < a := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact wordCochargeLabel_positive_tail hfull hm hmupper (Or.inl hb)
    have hpred : labelledWord w = labels.map Nat.pred := by
      have h := labelledWord_greedyValueTail hfull hm hmupper
      simpa only [htail, greedyTailWord, List.map_nil, List.nil_append, labels] using h
    have hlabels : labels = (labelledWord w).map Nat.succ := by
      rw [hpred]
      exact (succ_map_pred_of_positive labels hpos).symm
    have hi := labelledWord_initial_interval hfull
    have hi' : labelledWord (upper ++ List.range m) = labels ++ List.replicate m 0 := by
      simpa only [List.append_nil, List.map_nil, labels] using hi
    rw [hlabels] at hi'
    simpa only [upper] using hi'

theorem catWordOutput_glued_rows {M m : ℕ} {mu : YoungDiagram}
    (Q : SemistandardYoungTableau (firstRowTail mu))
    (hw : (tableauWord Q).Perm (List.range M)) (hm : 0 < m)
    (hwidth : mu.rowLen 0 = m) {nu tail : YoungDiagram}
    (hnu : CatWordOutput
      (labelledWord ((tableauWord Q).map (fun a => a + m) ++ List.range m)) nu)
    (htail : CatWordOutput (labelledWord (tableauWord Q)) tail) :
    nu.rowLen = prependRowFunction m tail.rowLen := by
  have hcapacity : (labelledWord (tableauWord Q)).count 0 ≤ m := by
    apply (labelledWord_zero_count_le_width Q hw).trans
    rw [firstRowTail_rowLen, ← hwidth]
    exact mu.rowLen_anti 0 1 (by omega)
  rw [labelledWord_glued_standard hw m hm] at hnu
  have htailEq : greedyTailWord ((labelledWord (tableauWord Q)).map Nat.succ) [] =
      labelledWord (tableauWord Q) := by
    simp only [greedyTailWord, List.nil_append, List.map_map, Function.comp_def,
      Nat.pred_succ, List.map_id']
  apply catWordOutput_greedy_rows ((labelledWord (tableauWord Q)).map Nat.succ) [] m
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact Nat.succ_pos _
  · simp
  · simpa only [htailEq] using hcapacity
  · simpa only [List.append_nil] using hnu
  · simpa only [htailEq] using htail

theorem dominates_of_glued_rows {lam nu tail : YoungDiagram}
    (hrows : nu.rowLen = prependRowFunction (lam.rowLen 0) tail.rowLen)
    (htail : Dominates tail (firstRowTail lam)) : Dominates nu lam := by
  intro r
  cases r with
  | zero => simp
  | succ r =>
      have hlam : lam.rowLen = prependRowFunction (lam.rowLen 0) (firstRowTail lam).rowLen := by
        funext i
        cases i with
        | zero => rfl
        | succ i => simp only [prependRowFunction_succ, firstRowTail_rowLen]
      rw [hrows, hlam, sum_prependRowFunction, sum_prependRowFunction]
      exact Nat.add_le_add_left (htail r) _

end HigherSpecht.Lascoux
end
end CanonicalSource52

section CanonicalSource53
/- Source: HigherSpecht/LascouxEastCorner.lean -/



/-!
# A genuine reverse-insertion corner beyond a prescribed column

When the first row is wider than `m`, the last row meeting column `m`
ends at a removable corner east of the first `m` columns.  Reverse
insertion at that actual corner gives a semistandard predecessor and a
letter whose insertion recovers the original tableau.  This statement
makes no claim that moving the letter to the front decreases the width.
-/

noncomputable section

open TauCeti

namespace HigherSpecht.Lascoux

/-- The bottom row that meets column `m`, whenever that column is nonempty. -/
def eastCornerRow (mu : YoungDiagram) (m : ℕ) : ℕ := mu.colLen m - 1

theorem eastCornerRow_spec (mu : YoungDiagram) {m : ℕ} (hm : m < mu.rowLen 0) :
    m < mu.rowLen (eastCornerRow mu m) ∧
      mu.rowLen (eastCornerRow mu m + 1) ≤ m := by
  have hcol : 0 < mu.colLen m := YoungDiagram.mem_iff_lt_colLen.mp
    (YoungDiagram.mem_iff_lt_rowLen.mpr hm : (0, m) ∈ mu)
  constructor
  · apply YoungDiagram.mem_iff_lt_rowLen.mp
    apply YoungDiagram.mem_iff_lt_colLen.mpr
    dsimp [eastCornerRow]
    omega
  · by_contra h
    have hcell : (eastCornerRow mu m + 1, m) ∈ mu :=
      YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.lt_of_not_ge h)
    have hlt := YoungDiagram.mem_iff_lt_colLen.mp hcell
    dsimp [eastCornerRow] at hlt
    omega

theorem eastCornerRow_lt_height (mu : YoungDiagram) {m : ℕ}
    (hm : m < mu.rowLen 0) : eastCornerRow mu m < mu.colLen 0 := by
  have hcell : (eastCornerRow mu m, m) ∈ mu :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (eastCornerRow_spec mu hm).1
  exact YoungDiagram.mem_iff_lt_colLen.mp
    (mu.up_left_mem le_rfl (Nat.zero_le m) hcell)

theorem eastCornerRow_is_corner (mu : YoungDiagram) {m : ℕ}
    (hm : m < mu.rowLen 0) :
    mu.rowLen (eastCornerRow mu m + 1) < mu.rowLen (eastCornerRow mu m) :=
  (eastCornerRow_spec mu hm).2.trans_lt (eastCornerRow_spec mu hm).1

theorem semistandardRows_eastCorner {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) {m : ℕ} (hm : m < mu.rowLen 0) :
    ((semistandardRows T).getD (eastCornerRow mu m + 1) []).length <
      ((semistandardRows T).getD (eastCornerRow mu m) []).length := by
  simpa only [semistandardRows_getD, tableauRowWord_length] using
    eastCornerRow_is_corner mu hm

/-- The predecessor here is the output of actual reverse insertion,
including the actual ejected letter and insertion endpoint. -/
theorem exists_reverseInsertion_eastCorner {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) {m : ℕ} (hm : m < mu.rowLen 0) :
    ∃ (rows : List (List ℕ)) (x : ℕ),
      rows = (reverseRowInsert (eastCornerRow mu m) (semistandardRows T)).1 ∧
      (reverseRowInsert (eastCornerRow mu m) (semistandardRows T)).2 = some x ∧
      rows.IsTableauRows ∧
      rowInsert x rows = semistandardRows T ∧
      rowInsertIndex x rows = eastCornerRow mu m ∧
      m ≤ (rows.getD (eastCornerRow mu m) []).length := by
  have hT := semistandardRows_isTableau T
  have hk := semistandardRows_eastCorner T hm
  obtain ⟨x, hx, hins, hidx⟩ := rowInsert_reverseRowInsert hT hk
  refine ⟨_, x, rfl, hx, hT.reverseRowInsert hk, hins, hidx, ?_⟩
  have hlength := congrArg (fun rows : List (List ℕ) =>
    (rows.getD (eastCornerRow mu m) []).length) hins
  rw [length_getD_rowInsert, hidx, if_pos rfl, semistandardRows_getD,
    tableauRowWord_length] at hlength
  have heast := (eastCornerRow_spec mu hm).1
  omega

/-- Reverse insertion provides the exact Knuth representative needed for
the inverse ordinary cycle: the current word is equivalent to the
predecessor's row word with the ejected letter appended. -/
theorem exists_tableau_eastCorner_pair {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) {m : ℕ} (hm : m < mu.rowLen 0) :
    ∃ (rows : List (List ℕ)) (x : ℕ),
      rows.IsTableauRows ∧
      rowInsert x rows = semistandardRows T ∧
      m ≤ (rows.getD (rowInsertIndex x rows) []).length ∧
      KnuthEquivalent (tableauWord T) (rowWordRows rows ++ [x]) := by
  obtain ⟨rows, x, _, _, hrows, hins, hidx, heast⟩ :=
    exists_reverseInsertion_eastCorner T hm
  refine ⟨rows, x, hrows, hins, by simpa only [hidx] using heast, ?_⟩
  have hknuth := knuth_rowInsert rows x hrows.sortedLE
  rw [hins, ← tableauWord_eq_rowWordRows] at hknuth
  exact hknuth.symm

end HigherSpecht.Lascoux
end
end CanonicalSource53

section CanonicalSource54
/- Source: HigherSpecht/RowInsertionColumn.lean -/



/-!
# The actual ending column of row insertion

The final column is bounded by any position of the original first row
whose entry exceeds the inserted letter.  In particular, insertion of zero
ends strictly before the number of zeros in the full word after insertion.
These are local statements about the genuine insertion algorithm; they do
not assert monotonicity of tableau width under cyclic rotation.
-/

namespace HigherSpecht

open TauCeti

variable {alpha : Type*} [LinearOrder alpha]

def rowInsertColumn (x : alpha) (rows : List (List alpha)) : ℕ :=
  (rows.getD (rowInsertIndex x rows) []).length

@[simp] theorem rowInsertColumn_nil (x : alpha) : rowInsertColumn x [] = 0 := rfl

theorem rowInsertColumn_cons_none {x : alpha} {row : List alpha}
    (rows : List (List alpha)) (h : (rowBump x row).2 = none) :
    rowInsertColumn x (row :: rows) = row.length := by
  simp only [rowInsertColumn, rowInsertIndex_cons_of_eq_none rows h, List.getD_cons_zero]

theorem rowInsertColumn_cons_some {x y : alpha} {row : List alpha}
    (rows : List (List alpha)) (h : (rowBump x row).2 = some y) :
    rowInsertColumn x (row :: rows) = rowInsertColumn y rows := by
  simp only [rowInsertColumn, rowInsertIndex_cons_of_eq_some rows h, List.getD_cons_succ]

/-- A strict upper bound at a column of the first row is propagated down
the genuine bump route.  The hypothesis is vacuous if that column lies
beyond the end of the first row. -/
theorem rowInsertColumn_le_cut {rows : List (List alpha)}
    (hrows : rows.IsTableauRows) (x : alpha) (j : ℕ)
    (hcut : ∀ hj : j < (rows.headD []).length, x < (rows.headD [])[j]) :
    rowInsertColumn x rows ≤ j := by
  induction rows generalizing x j with
  | nil => simp
  | cons row rows ih =>
      obtain ⟨hne, hsorted, habove, htail⟩ := List.isTableauRows_cons.mp hrows
      have hc : ∀ hj : j < row.length, x < row[j] := hcut
      cases hb : (rowBump x row).2 with
      | none =>
          rw [rowInsertColumn_cons_none rows hb]
          by_contra hn
          have hj : j < row.length := by omega
          have hle := (rowBump_snd_eq_none_iff x row).mp hb _ (List.getElem_mem hj)
          exact (not_lt_of_ge hle) (hc hj)
      | some y =>
          obtain ⟨k, hk, _, hky, hpre, _⟩ := exists_set_of_rowBump_snd_eq_some hb
          have hkj : k ≤ j := by
            by_contra hn
            have hjk : j < k := by omega
            exact (not_lt_of_ge (hpre j hjk)) (hc (hjk.trans hk))
          have hchild : ∀ hk' : k < (rows.headD []).length,
              y < (rows.headD [])[k] := by
            intro hk'
            simpa only [hky] using habove.getElem_lt k hk hk'
          rw [rowInsertColumn_cons_some rows hb]
          exact (ih htail y k hchild).trans hkj

/-- The inserted row is determined by the before and after shapes,
without requiring equality of the inserted tableaux themselves. -/
theorem rowInsertIndex_eq_of_shapes {P Q : List (List alpha)} {x y : alpha}
    (hshape : P.map List.length = Q.map List.length)
    (hnew : (rowInsert x P).map List.length = (rowInsert y Q).map List.length) :
    rowInsertIndex x P = rowInsertIndex y Q := by
  have hlength (i : ℕ) : (P.getD i []).length = (Q.getD i []).length := by
    have h := congrArg (fun lengths : List ℕ => lengths.getD i 0) hshape
    simpa only [← List.length_nil (α := alpha), List.getD_map] using h
  have hlength' (i : ℕ) :
      ((rowInsert x P).getD i []).length = ((rowInsert y Q).getD i []).length := by
    have h := congrArg (fun lengths : List ℕ => lengths.getD i 0) hnew
    simpa only [← List.length_nil (α := alpha), List.getD_map] using h
  by_contra hne
  have h := hlength' (rowInsertIndex x P)
  rw [length_getD_rowInsert, length_getD_rowInsert, if_pos rfl, if_neg hne,
    hlength] at h
  omega

theorem rowInsertColumn_eq_of_shapes {P Q : List (List alpha)} {x y : alpha}
    (hshape : P.map List.length = Q.map List.length)
    (hnew : (rowInsert x P).map List.length = (rowInsert y Q).map List.length) :
    rowInsertColumn x P = rowInsertColumn y Q := by
  have hi := rowInsertIndex_eq_of_shapes hshape hnew
  have h := congrArg (fun lengths : List ℕ => lengths.getD (rowInsertIndex y Q) 0) hshape
  simpa only [rowInsertColumn, hi, ← List.length_nil (α := alpha),
    List.getD_map] using h

theorem zero_lt_getElem_count_zero (row : List ℕ) (hs : row.SortedLE)
    (hi : row.count 0 < row.length) : 0 < row[row.count 0] := by
  induction row with
  | nil => simp at hi
  | cons a row ih =>
      obtain ⟨ha, htail⟩ := List.sortedLE_cons.mp hs
      by_cases ha0 : a = 0
      · subst a
        have hi' : row.count 0 < row.length := by simpa only [List.count_cons_self,
          List.length_cons, Nat.succ_lt_succ_iff] using hi
        simpa only [List.count_cons_self, List.getElem_cons_succ] using ih htail hi'
      · have hn : 0 ∉ row := by
          intro hz
          have h := ha 0 hz
          omega
        have hc : (a :: row).count 0 = 0 := by
          simp only [List.count_cons_of_ne ha0, List.count_eq_zero.mpr hn]
        simpa only [hc, List.getElem_cons_zero] using Nat.pos_of_ne_zero ha0

theorem rowInsertColumn_zero_le_count (rows : List (List ℕ))
    (hrows : rows.IsTableauRows) :
    rowInsertColumn 0 rows ≤ (rows.headD []).count 0 := by
  apply rowInsertColumn_le_cut hrows 0 ((rows.headD []).count 0)
  intro hj
  have hs : (rows.headD []).SortedLE := by
    cases rows with
    | nil => exact List.sortedLE_nil
    | cons row rows => exact (List.isTableauRows_cons.mp hrows).2.1
  exact zero_lt_getElem_count_zero _ hs hj

theorem rowInsertColumn_zero_lt_word_count (rows : List (List ℕ))
    (hrows : rows.IsTableauRows) :
    rowInsertColumn 0 rows < (0 :: rowWordRows rows).count 0 := by
  have h := rowInsertColumn_zero_le_count rows hrows
  cases rows with
  | nil => simp [rowWordRows]
  | cons row rows =>
      change rowInsertColumn 0 (row :: rows) ≤ row.count 0 at h
      rw [List.count_cons_self, rowWordRows_cons, List.count_append]
      omega

namespace Lascoux

theorem rowInsertColumn_zero_lt_tableau_count {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) :
    rowInsertColumn 0 (semistandardRows T) < (0 :: tableauWord T).count 0 := by
  rw [tableauWord_eq_rowWordRows]
  exact rowInsertColumn_zero_lt_word_count _ (semistandardRows_isTableau T)

/-- A cycle whose actual row insertion ends east of the content bound
cannot have zero as its moving letter. -/
theorem movingLetter_ne_zero_of_east {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (a m : ℕ)
    (hcount : (a :: tableauWord T).count 0 ≤ m)
    (heast : m ≤ rowInsertColumn a (semistandardRows T)) : a ≠ 0 := by
  intro ha
  subst a
  have h := rowInsertColumn_zero_lt_tableau_count T
  omega

end Lascoux
end HigherSpecht
end CanonicalSource54

section CanonicalSource55
/- Source: HigherSpecht/LascouxInsertionShapes.lean -/



/-!
# Signature operators preserve actual insertion shapes of arbitrary words

The proof passes through each word's genuine semistandard insertion
tableau, using the proved literal Knuth relation and its normal-form
uniqueness.  No abstract crystal shape axiom is introduced.
-/

noncomputable section

namespace HigherSpecht.Lascoux

open TauCeti

theorem insertionShape_tableauWord {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) : insertionShape (tableauWord T) = mu :=
  shape_eq_of_knuth_tableauWord (insertionTableau (tableauWord T)) T
    (knuth_insertionTableau (tableauWord T)).symm

theorem insertionShape_eq_of_knuth {u v : List ℕ} (h : KnuthEquivalent u v) :
    insertionShape u = insertionShape v :=
  shape_eq_of_knuth_tableauWord (insertionTableau u) (insertionTableau v)
    ((knuth_insertionTableau u).symm.trans (h.trans (knuth_insertionTableau v)))

theorem insertionShape_reflection (r : ℕ) (w : List ℕ) :
    insertionShape ((listString r).reflection w) = insertionShape w := by
  obtain ⟨U, hU⟩ := exists_tableau_of_word_reflection (insertionTableau w) r
  have hk := listString_reflection_of_knuth r (knuth_insertionTableau w)
  rw [← hU] at hk
  exact (insertionShape_eq_of_knuth hk).trans (insertionShape_tableauWord U)

theorem insertionShape_lower (r : ℕ) {u v : List ℕ}
    (h : (listString r).lower u = some v) : insertionShape v = insertionShape u := by
  have hk := listString_lower_of_knuth r (knuth_insertionTableau u)
  rw [h] at hk
  cases hp : (listString r).lower (tableauWord (insertionTableau u)) with
  | none => simp only [hp, OptionKnuth] at hk
  | some word =>
      obtain ⟨U, hU⟩ := exists_tableau_of_word_lowering (insertionTableau u) r hp
      have hkn : KnuthEquivalent v (tableauWord U) := by
        rw [hp] at hk
        simpa only [OptionKnuth, hU] using hk
      exact (insertionShape_eq_of_knuth hkn).trans (insertionShape_tableauWord U)

theorem insertionShape_raise (r : ℕ) {u v : List ℕ}
    (h : (listString r).raise u = some v) : insertionShape v = insertionShape u := by
  have hk := listString_raise_of_knuth r (knuth_insertionTableau u)
  rw [h] at hk
  cases hp : (listString r).raise (tableauWord (insertionTableau u)) with
  | none => simp only [hp, OptionKnuth] at hk
  | some word =>
      obtain ⟨U, hU⟩ := exists_tableau_of_word_raising (insertionTableau u) r hp
      have hkn : KnuthEquivalent v (tableauWord U) := by
        rw [hp] at hk
        simpa only [OptionKnuth, hU] using hk
      exact (insertionShape_eq_of_knuth hkn).trans (insertionShape_tableauWord U)

theorem insertionShape_snoc_rowLens {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (a : ℕ) :
    (insertionShape (tableauWord T ++ [a])).rowLens =
      (rowInsert a (semistandardRows T)).map List.length := by
  simp only [insertionShape, List.rowLens_tableauShape, insertionRows,
    List.foldl_append, List.foldl_cons, List.foldl_nil, insertionRows_tableauWord]

end HigherSpecht.Lascoux
end
end CanonicalSource55

section CanonicalSource56
/- Source: HigherSpecht/LascouxRestrictedCycles.lean -/



/-!
# Genuine signature transport of cycles ending east of a content bound

The ending corner is recovered from the before and after insertion shapes.
The tableau suffix is preserved by the literal cons rules.  Consequently
reflection preserves the exact corner, and first lowering commutes with
the ordinary cycle because its moving letter is proved nonzero from the
actual corner bound.  There is no assumption about a cyclage potential or
width monotonicity in this local result.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

open TauCeti

variable {mu : YoungDiagram}

def WordContentBound (m : ℕ) (w : List ℕ) : Prop := ∀ a, w.count a ≤ m

theorem rowInsertion_corner_eq_of_snoc_shape
    (T U : SemistandardYoungTableau mu) (a b : ℕ)
    (hshape : insertionShape (tableauWord U ++ [b]) =
      insertionShape (tableauWord T ++ [a])) :
    rowInsertIndex b (semistandardRows U) = rowInsertIndex a (semistandardRows T) ∧
      rowInsertColumn b (semistandardRows U) = rowInsertColumn a (semistandardRows T) := by
  have hbefore : (semistandardRows U).map List.length =
      (semistandardRows T).map List.length := by
    rw [semistandardRows_map_length, semistandardRows_map_length]
  have hafter := congrArg YoungDiagram.rowLens hshape
  rw [insertionShape_snoc_rowLens, insertionShape_snoc_rowLens] at hafter
  exact ⟨rowInsertIndex_eq_of_shapes hbefore hafter,
    rowInsertColumn_eq_of_shapes hbefore hafter⟩

theorem reflection_cons_snoc_tableau (T : SemistandardYoungTableau mu) (a r : ℕ) :
    ∃ (b : ℕ) (U : SemistandardYoungTableau mu),
      (listString r).reflection (a :: tableauWord T) = b :: tableauWord U ∧
      (listString r).reflection (tableauWord T ++ [a]) = tableauWord U ++ [b] := by
  obtain ⟨b, U, hsource⟩ := exists_cons_tableau_of_reflection T a r
  refine ⟨b, U, hsource, ?_⟩
  have h := reflection_rotateHead r a (tableauWord T)
  rw [hsource] at h
  exact h

theorem WordContentBound.reflection {m : ℕ} {w : List ℕ}
    (h : WordContentBound m w) (r : ℕ) :
    WordContentBound m ((listString r).reflection w) := by
  intro a
  rw [listString_reflection_count]
  split_ifs <;> exact h _

/-- Reflection of a genuine restricted cycle: both literal words, both
coordinates of the ending corner, the content bound and the nonzero
moving-letter conclusion are tracked. -/
theorem reflection_restrictedCycle (T : SemistandardYoungTableau mu) (a m r : ℕ)
    (hcount : WordContentBound m (a :: tableauWord T))
    (heast : m ≤ rowInsertColumn a (semistandardRows T)) :
    ∃ (b : ℕ) (U : SemistandardYoungTableau mu),
      (listString r).reflection (a :: tableauWord T) = b :: tableauWord U ∧
      (listString r).reflection (tableauWord T ++ [a]) = tableauWord U ++ [b] ∧
      rowInsertIndex b (semistandardRows U) = rowInsertIndex a (semistandardRows T) ∧
      rowInsertColumn b (semistandardRows U) = rowInsertColumn a (semistandardRows T) ∧
      WordContentBound m (b :: tableauWord U) ∧ b ≠ 0 := by
  obtain ⟨b, U, hs, ht⟩ := reflection_cons_snoc_tableau T a r
  have hshape : insertionShape (tableauWord U ++ [b]) =
      insertionShape (tableauWord T ++ [a]) := by
    rw [← ht]
    exact insertionShape_reflection r _
  obtain ⟨hrow, hcol⟩ := rowInsertion_corner_eq_of_snoc_shape T U a b hshape
  have hbound : WordContentBound m (b :: tableauWord U) := by
    rw [← hs]
    exact hcount.reflection r
  have hb0 := movingLetter_ne_zero_of_east U b m (hbound 0) (by simpa only [hcol] using heast)
  exact ⟨b, U, hs, ht, hrow, hcol, hbound, hb0⟩

theorem listString_lower_count (r a : ℕ) {w output : List ℕ}
    (h : (listString r).lower w = some output) :
    (output.count a : ℤ) = (w.count a : ℤ) +
      (if a = r + 1 then 1 else 0) - (if a = r then 1 else 0) := by
  obtain ⟨⟨n, u⟩, rfl⟩ := List.equivSigmaTuple.symm.surjective w
  change (listString r).lower (List.ofFn u) = some output at h
  change (output.count a : ℤ) = ((List.ofFn u).count a : ℤ) +
    (if a = r + 1 then 1 else 0) - (if a = r then 1 else 0)
  rw [listString_lower_ofFn] at h
  obtain ⟨v, hv, houtput⟩ := Option.map_eq_some_iff.mp h
  rw [← houtput]
  exact word_lower_count r n a hv

theorem WordContentBound.firstLowering {m : ℕ} {w output : List ℕ}
    (hbound : WordContentBound m w) (hcount : w.count 1 < w.count 0)
    (h : (listString 0).lower w = some output) : WordContentBound m output := by
  intro a
  have hc := listString_lower_count 0 a h
  have h0 := hbound 0
  have h1 := hbound 1
  have ha := hbound a
  by_cases ha0 : a = 0
  · subst a
    simp only [Nat.zero_add, Nat.zero_ne_one, Nat.one_ne_zero, if_false, if_pos rfl] at hc
    omega
  · by_cases ha1 : a = 1
    · subst a
      simp only [Nat.zero_add, if_pos rfl, Nat.one_ne_zero, if_false] at hc
      omega
    · simp only [Nat.zero_add, ha0, ha1, if_false] at hc
      omega

theorem exists_firstLowering_of_more_zeros {w : List ℕ}
    (hcount : w.count 1 < w.count 0) : ∃ output, (listString 0).lower w = some output := by
  have hb := listString_balance 0 w
  simp only [Nat.zero_add] at hb
  have hp : 0 < (listString 0).phi w := by omega
  cases h : (listString 0).lower w with
  | none =>
      have hz := (listString 0).phi_zero_iff.mpr h
      omega
  | some output => exact ⟨output, by simp only [h]⟩

/-- First lowering on a restricted cycle.  Its definition domain is
derived from the strict count inequality, and its rotation condition is
derived from the actual ending-column bound. -/
theorem firstLowering_restrictedCycle (T : SemistandardYoungTableau mu) (a m : ℕ)
    (hbound : WordContentBound m (a :: tableauWord T))
    (hcount : (a :: tableauWord T).count 1 < (a :: tableauWord T).count 0)
    (heast : m ≤ rowInsertColumn a (semistandardRows T)) :
    ∃ (b : ℕ) (U : SemistandardYoungTableau mu),
      (listString 0).lower (a :: tableauWord T) = some (b :: tableauWord U) ∧
      (listString 0).lower (tableauWord T ++ [a]) = some (tableauWord U ++ [b]) ∧
      rowInsertIndex b (semistandardRows U) = rowInsertIndex a (semistandardRows T) ∧
      rowInsertColumn b (semistandardRows U) = rowInsertColumn a (semistandardRows T) ∧
      WordContentBound m (b :: tableauWord U) ∧ b ≠ 0 := by
  obtain ⟨output, houtput⟩ := exists_firstLowering_of_more_zeros hcount
  obtain ⟨b, U, hU⟩ := exists_cons_tableau_of_lower T a 0 houtput
  have hs : (listString 0).lower (a :: tableauWord T) = some (b :: tableauWord U) := by
    rw [houtput, hU]
  have ha0 := movingLetter_ne_zero_of_east T a m (hbound 0) heast
  have ht : (listString 0).lower (tableauWord T ++ [a]) =
      some (tableauWord U ++ [b]) := by
    have h := firstLowering_rotateHead a (tableauWord T) ha0 hcount
    rw [hs, Option.map_some] at h
    exact h
  have hshape := insertionShape_lower 0 ht
  obtain ⟨hrow, hcol⟩ := rowInsertion_corner_eq_of_snoc_shape T U a b hshape
  have hb : WordContentBound m (b :: tableauWord U) := hbound.firstLowering hcount hs
  have hb0 := movingLetter_ne_zero_of_east U b m (hb 0) (by simpa only [hcol] using heast)
  exact ⟨b, U, hs, ht, hrow, hcol, hb, hb0⟩

end HigherSpecht.Lascoux
end
end CanonicalSource56

section CanonicalSource57
/- Source: HigherSpecht/LascouxReflectionCycleMaps.lean -/



/-!
# Restricted cycles through the actual reflection equivalences

The closure statements are proved for literal word maps.  They are then
instantiated with the actual adjacent reflections, content transpositions,
and the specific conjugating map used in a repeated-letter split.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

open TauCeti

def RestrictedCycleOutput {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (a m : ℕ) (w v : List ℕ) : Prop :=
  ∃ (b : ℕ) (U : SemistandardYoungTableau mu),
    w = b :: tableauWord U ∧ v = tableauWord U ++ [b] ∧
    rowInsertIndex b (semistandardRows U) = rowInsertIndex a (semistandardRows T) ∧
    rowInsertColumn b (semistandardRows U) = rowInsertColumn a (semistandardRows T) ∧
    WordContentBound m (b :: tableauWord U) ∧ b ≠ 0

def PreservesRestrictedCycles {N : ℕ}
    (f : (Fin N → ℕ) → (Fin N → ℕ)) : Prop :=
  ∀ {mu : YoungDiagram} (T : SemistandardYoungTableau mu) (a m : ℕ)
    (u v : Fin N → ℕ),
    List.ofFn u = a :: tableauWord T →
    List.ofFn v = tableauWord T ++ [a] →
    WordContentBound m (a :: tableauWord T) →
    m ≤ rowInsertColumn a (semistandardRows T) →
    RestrictedCycleOutput T a m (List.ofFn (f u)) (List.ofFn (f v))

theorem PreservesRestrictedCycles.id (N : ℕ) :
    PreservesRestrictedCycles (id : (Fin N → ℕ) → (Fin N → ℕ)) := by
  intro mu T a m u v hu hv hb he
  exact ⟨a, T, hu, hv, rfl, rfl, hb,
    movingLetter_ne_zero_of_east T a m (hb 0) he⟩

theorem PreservesRestrictedCycles.comp {N : ℕ}
    {f g : (Fin N → ℕ) → (Fin N → ℕ)}
    (hf : PreservesRestrictedCycles f) (hg : PreservesRestrictedCycles g) :
    PreservesRestrictedCycles (g ∘ f) := by
  intro mu T a m u v hu hv hb he
  obtain ⟨b, U, hfu, hfv, hrow, hcol, hbound, hb0⟩ := hf T a m u v hu hv hb he
  obtain ⟨d, V, hgu, hgv, hrow', hcol', hbound', hd0⟩ :=
    hg U b m (f u) (f v) hfu hfv hbound (by simpa only [hcol] using he)
  exact ⟨d, V, hgu, hgv, hrow'.trans hrow, hcol'.trans hcol, hbound', hd0⟩

def PreservesRestrictedCyclesEquiv {N : ℕ}
    (e : (Fin N → ℕ) ≃ (Fin N → ℕ)) : Prop :=
  PreservesRestrictedCycles e ∧ PreservesRestrictedCycles e.symm

theorem PreservesRestrictedCyclesEquiv.refl (N : ℕ) :
    PreservesRestrictedCyclesEquiv (Equiv.refl (Fin N → ℕ)) :=
  ⟨PreservesRestrictedCycles.id N, PreservesRestrictedCycles.id N⟩

theorem PreservesRestrictedCyclesEquiv.trans {N : ℕ}
    {e f : (Fin N → ℕ) ≃ (Fin N → ℕ)}
    (he : PreservesRestrictedCyclesEquiv e) (hf : PreservesRestrictedCyclesEquiv f) :
    PreservesRestrictedCyclesEquiv (e.trans f) := by
  constructor
  · exact PreservesRestrictedCycles.comp he.1 hf.1
  · exact PreservesRestrictedCycles.comp hf.2 he.2

theorem wordReflection_preserves_restrictedCycles (r N : ℕ) :
    PreservesRestrictedCyclesEquiv (wordReflection r N) := by
  have hf : PreservesRestrictedCycles (wordReflection r N) := by
    intro mu T a m u v hu hv hb he
    have h := reflection_restrictedCycle T a m r hb he
    change RestrictedCycleOutput T a m
      ((listString r).reflection (a :: tableauWord T))
      ((listString r).reflection (tableauWord T ++ [a])) at h
    simpa only [← hu, ← hv, listString_reflection_ofFn] using h
  refine ⟨hf, ?_⟩
  have heq : (wordReflection r N).symm = wordReflection r N := by
    apply Equiv.ext
    intro u
    apply (wordReflection r N).injective
    exact (Equiv.apply_symm_apply (wordReflection r N) u).trans
      (wordReflection_involutive r N u).symm
  change PreservesRestrictedCycles (wordReflection r N).symm
  rw [heq]
  exact hf

theorem wordSwapZero_preserves_restrictedCycles (N j : ℕ) :
    PreservesRestrictedCyclesEquiv (wordSwapZero N j) := by
  induction j using Nat.twoStepInduction with
  | zero => exact PreservesRestrictedCyclesEquiv.refl N
  | one => exact wordReflection_preserves_restrictedCycles 0 N
  | more j ih ih' =>
      exact (wordReflection_preserves_restrictedCycles (j + 1) N).trans
        (ih'.trans (wordReflection_preserves_restrictedCycles (j + 1) N))

theorem wordContentSwap_preserves_restrictedCycles (N i j : ℕ) :
    PreservesRestrictedCyclesEquiv (wordContentSwap N i j) := by
  unfold wordContentSwap
  split_ifs
  · exact PreservesRestrictedCyclesEquiv.refl N
  · exact wordSwapZero_preserves_restrictedCycles N j
  · exact wordSwapZero_preserves_restrictedCycles N i
  · exact (wordSwapZero_preserves_restrictedCycles N i).trans
      ((wordSwapZero_preserves_restrictedCycles N j).trans
        (wordSwapZero_preserves_restrictedCycles N i))

theorem wordBringPair_preserves_restrictedCycles (N i j : ℕ) :
    PreservesRestrictedCyclesEquiv (wordBringPair N i j) :=
  (wordContentSwap_preserves_restrictedCycles N 0 i).trans
    (wordContentSwap_preserves_restrictedCycles N 1 (Equiv.swap 0 i j))

end HigherSpecht.Lascoux
end
end CanonicalSource57

section CanonicalSource58
/- Source: HigherSpecht/LascouxProgramRestrictedCycles.lean -/



/-!
# Restricted-cycle transport for every actual crystal program

A content split is the specified reflection conjugation, genuine first
lowering, and inverse conjugation.  Each stage preserves the actual ending
corner and the content bound, so the next moving letter is proved nonzero.
Induction composes these facts for the literal finite program.  The final
theorem has no cyclic-domain, corner-preservation or naturality premise.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem transferContentWord_restrictedCycle (N : ℕ) (c : ℕ → ℕ) (i j : ℕ)
    (hi : 1 < c i) (hj : c j = 0) {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) (a m : ℕ)
    (u v : WordOfContent N c)
    (hu : List.ofFn u.val = a :: tableauWord T)
    (hv : List.ofFn v.val = tableauWord T ++ [a])
    (hbound : WordContentBound m (a :: tableauWord T))
    (heast : m ≤ rowInsertColumn a (semistandardRows T)) :
    RestrictedCycleOutput T a m
      (List.ofFn (transferContentWord N c i j hi hj u))
      (List.ofFn (transferContentWord N c i j hi hj v)) := by
  let E := wordBringPair N i j
  let zu := (wordString 0 N).lowerValue (preparedContentWord N c i j hi hj u)
  let zv := (wordString 0 N).lowerValue (preparedContentWord N c i j hi hj v)
  obtain ⟨b, U, hEu, hEv, hrow₁, hcol₁, hbound₁, hb0⟩ :=
    (wordBringPair_preserves_restrictedCycles N i j).1 T a m u.val v.val
      hu hv hbound heast
  change List.ofFn (E u.val) = b :: tableauWord U at hEu
  change List.ofFn (E v.val) = tableauWord U ++ [b] at hEv
  have hcount : (b :: tableauWord U).count 1 < (b :: tableauWord U).count 0 := by
    have hzero := wordBringPair_zero N i j (distinct_of_split_counts hi hj) u.val
    have hone := wordBringPair_one N i j u.val
    rw [u.property i] at hzero
    rw [u.property j, hj] at hone
    change (List.ofFn (E u.val)).count 0 = c i at hzero
    change (List.ofFn (E u.val)).count 1 = 0 at hone
    rw [hEu] at hzero hone
    omega
  obtain ⟨d, V, hlowu, hlowv, hrow₂, hcol₂, hbound₂, hd0⟩ :=
    firstLowering_restrictedCycle U b m hbound₁ hcount
      (by simpa only [hcol₁] using heast)
  have hlu : (listString 0).lower (List.ofFn (E u.val)) = some (List.ofFn zu) := by
    rw [listString_lower_ofFn]
    have hs := (wordString 0 N).lowerValue_spec (preparedContentWord N c i j hi hj u)
    change (wordString 0 N).lower (E u.val) = some zu at hs
    rw [hs]
    rfl
  have hlv : (listString 0).lower (List.ofFn (E v.val)) = some (List.ofFn zv) := by
    rw [listString_lower_ofFn]
    have hs := (wordString 0 N).lowerValue_spec (preparedContentWord N c i j hi hj v)
    change (wordString 0 N).lower (E v.val) = some zv at hs
    rw [hs]
    rfl
  have hzu : List.ofFn zu = d :: tableauWord V := by
    rw [← hEu, hlu] at hlowu
    exact Option.some.inj hlowu
  have hzv : List.ofFn zv = tableauWord V ++ [d] := by
    rw [← hEv, hlv] at hlowv
    exact Option.some.inj hlowv
  obtain ⟨e, W, hfinalu, hfinalv, hrow₃, hcol₃, hbound₃, he0⟩ :=
    (wordBringPair_preserves_restrictedCycles N i j).2 V d m zu zv hzu hzv hbound₂
      (by simpa only [hcol₂, hcol₁] using heast)
  refine ⟨e, W, ?_, ?_, hrow₃.trans (hrow₂.trans hrow₁),
    hcol₃.trans (hcol₂.trans hcol₁), hbound₃, he0⟩
  · exact hfinalu
  · exact hfinalv

/-- Every literal finite program preserves this actual restricted cycle,
including its ending row and column and the bound on all letter counts.
The source and target words are interpreted through the program's actual
fixed-content embedding. -/
theorem CrystalProgram.restrictedCycles {K : ℕ} {c d : ℕ → ℕ}
    (P : CrystalProgram K c d) (N : ℕ) :
    ∀ {mu : YoungDiagram} (T : SemistandardYoungTableau mu) (a m : ℕ)
      (u v : WordOfContent N c),
      List.ofFn u.val = a :: tableauWord T →
      List.ofFn v.val = tableauWord T ++ [a] →
      WordContentBound m (a :: tableauWord T) →
      m ≤ rowInsertColumn a (semistandardRows T) →
      RestrictedCycleOutput T a m
        (List.ofFn ((P.embedding N) u).val)
        (List.ofFn ((P.embedding N) v).val) := by
  induction P with
  | nil c =>
      intro mu T a m u v hu hv hb he
      exact ⟨a, T, hu, hv, rfl, rfl, hb,
        movingLetter_ne_zero_of_east T a m (hb 0) he⟩
  | @reflect c d r hr rest ih =>
      intro mu T a m u v hu hv hb he
      let u₁ := reflectionContentEmbedding N c r u
      let v₁ := reflectionContentEmbedding N c r v
      obtain ⟨b, U, hsu, hsv, hrow, hcol, hbound, hb0⟩ :=
        (wordReflection_preserves_restrictedCycles r N).1 T a m u.val v.val hu hv hb he
      have hu₁ : List.ofFn u₁.val = b :: tableauWord U := hsu
      have hv₁ : List.ofFn v₁.val = tableauWord U ++ [b] := hsv
      obtain ⟨e, W, htu, htv, hrow', hcol', hbound', he0⟩ :=
        ih U b m u₁ v₁ hu₁ hv₁ hbound (by simpa only [hcol] using he)
      exact ⟨e, W, htu, htv, hrow'.trans hrow, hcol'.trans hcol, hbound', he0⟩
  | @split c d i j hiK hjK hi hj rest ih =>
      intro mu T a m u v hu hv hb he
      let u₁ := contentTransferEmbedding N c i j hi hj u
      let v₁ := contentTransferEmbedding N c i j hi hj v
      obtain ⟨b, U, hsu, hsv, hrow, hcol, hbound, hb0⟩ :=
        transferContentWord_restrictedCycle N c i j hi hj T a m u v hu hv hb he
      have hu₁ : List.ofFn u₁.val = b :: tableauWord U := hsu
      have hv₁ : List.ofFn v₁.val = tableauWord U ++ [b] := hsv
      obtain ⟨e, W, htu, htv, hrow', hcol', hbound', he0⟩ :=
        ih U b m u₁ v₁ hu₁ hv₁ hbound (by simpa only [hcol] using he)
      exact ⟨e, W, htu, htv, hrow'.trans hrow, hcol'.trans hcol, hbound', he0⟩

end HigherSpecht.Lascoux
end
end CanonicalSource58

section CanonicalSource59
/- Source: HigherSpecht/HanadaBumpRoute.lean -/



/-!
# Actual finite upward bump routes

A route is an exact execution of the bounded row routine, propagating every
pop after increasing its visit.  Its endpoint is the row in which absorption
actually occurs.  The definitions record every intermediate row; no endpoint
bound is included in the execution relation.

The bounded route starts above an existing lower row.  An insertion into the
bottom row itself is an ordinary unbounded sorted insertion and is handled
separately when assembling the scheduled-filling exchange.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

inductive ScheduleBumpRoute (advance : α → α) :
    List α → List (List α) → α → List (List α) → ℕ → Prop
  | top (lower row : List α) (x : α)
      (hstep : scheduleRowInsert lower [] x = (row, none)) :
      ScheduleBumpRoute advance lower [] x [row] 0
  | stop (lower upper row : List α) (tail : List (List α)) (x : α)
      (hstep : scheduleRowInsert lower upper x = (row, none)) :
      ScheduleBumpRoute advance lower (upper :: tail) x (row :: tail) 0
  | pass (lower upper row : List α) (tail result : List (List α)) (x p : α) (endpoint : ℕ)
      (hstep : scheduleRowInsert lower upper x = (row, some p))
      (hnext : ScheduleBumpRoute advance row tail (advance p) result endpoint) :
      ScheduleBumpRoute advance lower (upper :: tail) x (row :: result) (endpoint + 1)

inductive ScheduleRowsValid (height : α → ℕ) : ℕ → List (List α) → Prop
  | nil (r : ℕ) : ScheduleRowsValid height r []
  | cons {r : ℕ} {row : List α} {tail : List (List α)}
      (sorted : row.Pairwise (· ≤ ·)) (atHeight : ∀ x ∈ row, height x = r)
      (columns : RowsFit row (tail.headD []))
      (tailValid : ScheduleRowsValid height (r + 1) tail) :
      ScheduleRowsValid height r (row :: tail)

namespace ScheduleRowsValid

theorem head_sorted {height : α → ℕ} {r : ℕ} {rows : List (List α)}
    (h : ScheduleRowsValid height r rows) : (rows.headD []).Pairwise (· ≤ ·) := by
  cases h with
  | nil => simp
  | cons hs _ _ _ => exact hs

theorem head_height {height : α → ℕ} {r : ℕ} {rows : List (List α)}
    (h : ScheduleRowsValid height r rows) : ∀ x ∈ rows.headD [], height x = r := by
  cases h with
  | nil => simp
  | cons _ hh _ _ => exact hh

end ScheduleRowsValid

theorem scheduleRowInsert_mem_height {height : α → ℕ} {r : ℕ}
    (lower upper : List α) (x : α) (hx : height x = r)
    (hu : ∀ y ∈ upper, height y = r) :
    (∀ y ∈ (scheduleRowInsert lower upper x).1, height y = r) ∧
      (∀ y, (scheduleRowInsert lower upper x).2 = some y → height y = r) := by
  have hp := scheduleRowInsert_conservation lower upper x
  constructor
  · intro y hy
    have hmem : y ∈ x :: upper := hp.mem_iff.mpr (List.mem_append_left _ hy)
    rcases List.mem_cons.mp hmem with heq | hm
    · simpa only [heq] using hx
    · exact hu y hm
  · intro y hy
    have hmem : y ∈ x :: upper := hp.mem_iff.mpr (by
      apply List.mem_append_right
      simp only [hy, Option.toList_some, List.mem_singleton])
    rcases List.mem_cons.mp hmem with heq | hm
    · simpa only [heq] using hx
    · exact hu y hm

namespace ScheduleBumpRoute

variable {advance : α → α} {lower : List α} {rows result : List (List α)}
  {x : α} {endpoint : ℕ}

theorem result_nonempty (h : ScheduleBumpRoute advance lower rows x result endpoint) :
    result ≠ [] := by
  cases h <;> simp

theorem head_eq (h : ScheduleBumpRoute advance lower rows x result endpoint) :
    result.headD [] = (scheduleRowInsert lower (rows.headD []) x).1 := by
  cases h with
  | top lower row x hs => simp only [List.headD_cons, List.headD_nil, hs]
  | stop lower upper row tail x hs => simp only [List.headD_cons, hs]
  | pass lower upper row tail result x p endpoint hs hn => simp only [List.headD_cons, hs]

theorem lower_fits (h : ScheduleBumpRoute advance lower rows x result endpoint)
    (hfit : RowsFit lower (rows.headD [])) : RowsFit lower (result.headD []) := by
  rw [h.head_eq]
  exact scheduleRowInsert_fits lower (rows.headD []) x hfit

theorem valid {height : α → ℕ}
    (hadvance : ∀ z, height (advance z) = height z + 1)
    (h : ScheduleBumpRoute advance lower rows x result endpoint)
    {r : ℕ} (hrows : ScheduleRowsValid height r rows) (hx : height x = r) :
    ScheduleRowsValid height r result := by
  induction h generalizing r with
  | top lower row x hs =>
      have hm := (scheduleRowInsert_mem_height lower [] x hx (by simp)).1
      have hsorted := scheduleRowInsert_pairwise_le lower [] x (by simp)
      rw [hs] at hm hsorted
      exact .cons hsorted hm (RowsFit.nil row) (.nil (r + 1))
  | stop lower upper row tail x hs =>
      cases hrows with
      | cons hu hh hc ht =>
          have hm := (scheduleRowInsert_mem_height lower upper x hx hh).1
          have hsorted := scheduleRowInsert_pairwise_le lower upper x hu
          have hrelax := scheduleRowInsert_lower_relaxed lower upper x
          rw [hs] at hm hsorted hrelax
          exact .cons hsorted hm (hc.relax_lower hrelax) ht
  | pass lower upper row tail result x p endpoint hs hn ih =>
      cases hrows with
      | cons hu hh hc ht =>
          have hm := scheduleRowInsert_mem_height lower upper x hx hh
          have hp : height p = r := hm.2 p (by rw [hs])
          have hsorted := scheduleRowInsert_pairwise_le lower upper x hu
          have hrelax := scheduleRowInsert_lower_relaxed lower upper x
          rw [hs] at hm hsorted hrelax
          have hnext := ih ht (by rw [hadvance, hp])
          have hstart : RowsFit row (tail.headD []) := hc.relax_lower hrelax
          exact .cons hsorted hm.1 (hn.lower_fits hstart) hnext

/-- Every route that starts strictly above its first lower entry terminates.
The recursion is on the finite stack; the first empty top row absorbs. -/
theorem exists_of_first_lower_lt (advance : α → α) (hadvance : ∀ z, z < advance z)
    (rows : List (List α)) (l x : α) (lower : List α) (hlx : l < x) :
    ∃ result endpoint, ScheduleBumpRoute advance (l :: lower) rows x result endpoint := by
  induction rows generalizing l x lower with
  | nil =>
      exact ⟨[[x]], 0, .top _ _ _ (by simp [scheduleRowInsert, hlx])⟩
  | cons upper tail ih =>
      cases hp : (scheduleRowInsert (l :: lower) upper x).2 with
      | none =>
          exact ⟨(scheduleRowInsert (l :: lower) upper x).1 :: tail, 0,
            .stop _ _ _ _ _ (Prod.ext rfl hp)⟩
      | some p =>
          obtain ⟨u, rest, hrow, hup⟩ := scheduleRowInsert_head_le_pop hlx hp
          obtain ⟨result, e, hnext⟩ := ih u (advance p) rest (hup.trans_lt (hadvance p))
          refine ⟨(u :: rest) :: result, e + 1, .pass _ _ _ _ _ _ _ _ ?_ hnext⟩
          exact Prod.ext hrow hp

end ScheduleBumpRoute

def advanceVisit {n : ℕ} (t : VisitTime n) : VisitTime n :=
  visitTime ((ofLex t).1 + 1) (ofLex t).2

def visitHeight {n : ℕ} (a : Fin n → ℕ) (t : VisitTime n) : ℕ :=
  a (ofLex t).2 + (ofLex t).1

theorem advanceVisit_strictMono {n : ℕ} : StrictMono (advanceVisit (n := n)) := by
  intro x y hxy
  rcases Prod.Lex.toLex_lt_toLex.mp hxy with h | ⟨h, hi⟩
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (Nat.add_lt_add_right h 1))
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨congrArg (· + 1) h, hi⟩)

theorem lt_advanceVisit {n : ℕ} (t : VisitTime n) : t < advanceVisit t :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inl (Nat.lt_succ_self _))

theorem visitHeight_advanceVisit {n : ℕ} (a : Fin n → ℕ) (t : VisitTime n) :
    visitHeight a (advanceVisit t) = visitHeight a t + 1 := by
  simp only [visitHeight, advanceVisit, visitTime, ofLex_toLex, Nat.add_assoc]

end HigherSpecht
end CanonicalSource59

section CanonicalSource60
/- Source: HigherSpecht/HanadaAdjacentRoutes.lean -/



/-!
# The endpoint comparison for two actual adjacent-start bump routes

The second route starts one row above the first and with a strictly larger
visit pair.  Its endpoint is at most one row above the first endpoint.
The proof uses the literal no-hole row comparison, invariance of prefixes
below a threshold, and relaxation of the lower barrier.  The row-height
identity rules out equality of a pop in one row and an earlier pop in the
row below.  No assertion about a compacted row being pointwise smaller than
its pre-deletion row is used.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

theorem exists_scheduleBumpRoute_zero_of_head_none (advance : α → α)
    (lower : List α) (rows : List (List α)) (x : α)
    (h : (scheduleRowInsert lower (rows.headD []) x).2 = none) :
    ∃ result, ScheduleBumpRoute advance lower rows x result 0 := by
  cases rows with
  | nil =>
      exact ⟨[(scheduleRowInsert lower [] x).1], .top _ _ _ (Prod.ext rfl h)⟩
  | cons upper tail =>
      exact ⟨(scheduleRowInsert lower upper x).1 :: tail,
        .stop _ _ _ _ _ (Prod.ext rfl h)⟩

/-- The second endpoint is measured relative to its own starting row.  Thus
`laterEndpoint ≤ endpoint` is exactly the absolute bound
`laterStart + laterEndpoint ≤ firstEndpoint + 1`. -/
theorem ScheduleBumpRoute.adjacent_endpoint
    {advance : α → α} {height : α → ℕ}
    (hmono : StrictMono advance) (hadvance : ∀ z, z < advance z)
    (hheight : ∀ z, height (advance z) = height z + 1)
    {lower : List α} {rows result : List (List α)} {x : α} {endpoint : ℕ}
    (hroute : ScheduleBumpRoute advance lower rows x result endpoint)
    {r : ℕ} (hrows : ScheduleRowsValid height r rows) (hx : height x = r)
    {laterLower : List α} (hrelax : LowerBarrierRelaxed laterLower (result.headD []))
    {y : α} (hy : height y = r + 1) (hxy : x < y) :
    ∃ laterResult laterEndpoint,
      ScheduleBumpRoute advance laterLower result.tail y laterResult laterEndpoint ∧
        laterEndpoint ≤ endpoint := by
  induction hroute generalizing r laterLower y with
  | top lower row x hstep =>
      have hnone : (scheduleRowInsert row [] y).2 = none := by
        have h := scheduleRowInsert_adjacent_none lower [] [] x y
          (by simp) (by simp) (RowsFit.nil []) hxy (by rw [hstep])
        simpa only [hstep] using h
      have hnone' := scheduleRowInsert_none_of_relaxed hrelax [] y hnone
      obtain ⟨out, hout⟩ := exists_scheduleBumpRoute_zero_of_head_none advance laterLower [] y hnone'
      exact ⟨out, 0, hout, le_rfl⟩
  | stop lower upper row tail x hstep =>
      cases hrows with
      | cons hsorted hatHeight hcolumns htail =>
          have hnone : (scheduleRowInsert row (tail.headD []) y).2 = none := by
            have h := scheduleRowInsert_adjacent_none lower upper (tail.headD []) x y
              hsorted htail.head_sorted hcolumns hxy (by rw [hstep])
            simpa only [hstep] using h
          have hnone' := scheduleRowInsert_none_of_relaxed hrelax (tail.headD []) y hnone
          obtain ⟨out, hout⟩ := exists_scheduleBumpRoute_zero_of_head_none advance laterLower tail y hnone'
          exact ⟨out, 0, hout, le_rfl⟩
  | pass lower upper row tail result x p endpoint hstep hnext ih =>
      cases hrows with
      | cons hsorted hatHeight hcolumns htail =>
          have hpHeight : height p = r :=
            (scheduleRowInsert_mem_height lower upper x hx hatHeight).2 p (by rw [hstep])
          have hadvanceP : height (advance p) = r + 1 := by rw [hheight, hpHeight]
          have hresultValid := hnext.valid hheight htail hadvanceP
          cases result with
          | nil => exact (hnext.result_nonempty rfl).elim
          | cons front rest =>
              cases hpop : (scheduleRowInsert laterLower front y).2 with
              | none =>
                  obtain ⟨out, hout⟩ := exists_scheduleBumpRoute_zero_of_head_none
                    advance laterLower (front :: rest) y hpop
                  exact ⟨out, 0, hout, Nat.zero_le _⟩
              | some q =>
                  have hsmall : popBelow p (scheduleRowInsert row (tail.headD []) y).2 = none := by
                    cases hlocal : (scheduleRowInsert row (tail.headD []) y).2 with
                    | none => rfl
                    | some z =>
                        have hpz : p ≤ z := by
                          apply scheduleRowInsert_adjacent_pop_le lower upper (tail.headD []) x y p z
                            hsorted htail.head_sorted hcolumns hxy
                          · rw [hstep]
                          · simpa only [hstep] using hlocal
                        simp only [popBelow, if_neg (not_lt.mpr hpz)]
                  have hfront : front = (scheduleRowInsert row (tail.headD []) (advance p)).1 :=
                    hnext.head_eq
                  have hpq : p ≤ q :=
                    scheduleRowInsert_no_small_pop_after_large_and_relaxed hrelax
                      row (tail.headD []) y (advance p) p (hadvance p).le hsmall
                      (by simpa only [← hfront] using hpop)
                  have hqHeight : height q = r + 1 :=
                    (scheduleRowInsert_mem_height laterLower front y hy
                      hresultValid.head_height).2 q hpop
                  have hpqStrict : p < q := by
                    apply lt_of_le_of_ne hpq
                    intro heq
                    have he := congrArg height heq
                    rw [hpHeight, hqHeight] at he
                    omega
                  have hadvanceQ : height (advance q) = (r + 1) + 1 := by
                    rw [hheight, hqHeight]
                  obtain ⟨out, e, hrouteLater, hbound⟩ := ih htail hadvanceP
                    (scheduleRowInsert_lower_relaxed laterLower front y) hadvanceQ (hmono hpqStrict)
                  refine ⟨(scheduleRowInsert laterLower front y).1 :: out, e + 1,
                    ScheduleBumpRoute.pass laterLower front _ rest out y q e (Prod.ext rfl hpop)
                      hrouteLater, Nat.add_le_add_right hbound 1⟩

theorem ScheduleBumpRoute.adjacent_visit_endpoint {n : ℕ} (a : Fin n → ℕ)
    {lower : List (VisitTime n)} {rows result : List (List (VisitTime n))}
    {x : VisitTime n} {endpoint r : ℕ}
    (hroute : ScheduleBumpRoute advanceVisit lower rows x result endpoint)
    (hrows : ScheduleRowsValid (visitHeight a) r rows) (hx : visitHeight a x = r)
    {laterLower : List (VisitTime n)} (hrelax : LowerBarrierRelaxed laterLower (result.headD []))
    {y : VisitTime n} (hy : visitHeight a y = r + 1) (hxy : x < y) :
    ∃ laterResult laterEndpoint,
      ScheduleBumpRoute advanceVisit laterLower result.tail y laterResult laterEndpoint ∧
        laterEndpoint ≤ endpoint :=
  hroute.adjacent_endpoint advanceVisit_strictMono lt_advanceVisit (visitHeight_advanceVisit a)
    hrows hx hrelax hy hxy

end HigherSpecht
end CanonicalSource60

section CanonicalSource61
/- Source: HigherSpecht/HanadaRouteEffects.lean -/



/-!
# Exact content, row-count, and processed-prefix effects of bump routes

Every route adds one cell at its actual endpoint.  It preserves token labels
whenever advancing a token preserves its label.  A route whose input lies
strictly above a visit threshold changes no processed-entry count.  For the
current visit itself, a genuine capacity inequality ensures that the input
is retained and increases only its starting row's processed count.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

theorem scheduleCountLE_insert_eq_of_lt (lower upper : List α) (x cutoff : α)
    (hcx : cutoff < x) :
    scheduleCountLE (scheduleRowInsert lower upper x).1 cutoff = scheduleCountLE upper cutoff := by
  have hc := (scheduleRowInsert_conservation lower upper x).countP_eq
    (fun z => decide (z ≤ cutoff))
  cases hp : (scheduleRowInsert lower upper x).2 with
  | none =>
      simp [scheduleCountLE, List.countP_cons, List.countP_append, hp,
        not_le.mpr hcx] at hc ⊢
      omega
  | some p =>
      have hcp : cutoff < p := hcx.trans_le (scheduleRowInsert_pop_ge lower upper x p hp)
      simp [scheduleCountLE, List.countP_cons, List.countP_append, hp,
        not_le.mpr hcx, not_le.mpr hcp] at hc ⊢
      omega

theorem scheduleCountLE_insert_current_gain (lower upper : List α) (x : α)
    (hpop : ∀ p, (scheduleRowInsert lower upper x).2 = some p → x < p) :
    scheduleCountLE (scheduleRowInsert lower upper x).1 x = scheduleCountLE upper x + 1 := by
  have hc := (scheduleRowInsert_conservation lower upper x).countP_eq
    (fun z => decide (z ≤ x))
  cases hp : (scheduleRowInsert lower upper x).2 with
  | none =>
      simp [scheduleCountLE, List.countP_cons, List.countP_append, hp] at hc ⊢
      omega
  | some p =>
      have hxp : ¬ p ≤ x := not_le.mpr (hpop p hp)
      simp [scheduleCountLE, List.countP_cons, List.countP_append, hp, hxp] at hc ⊢
      omega

theorem scheduleCountLE_eq_LT_of_not_mem (upper : List α) (x : α) (hx : x ∉ upper) :
    scheduleCountLE upper x = scheduleCountLT upper x := by
  apply List.countP_congr
  intro y hy
  simp only [decide_eq_true_eq]
  constructor
  · intro hle
    exact lt_of_le_of_ne hle (fun heq => hx (heq ▸ hy))
  · exact le_of_lt

/-- The current visit is genuinely retained when there is free column
capacity below it.  This replaces a pictorial claim about the insertion path. -/
theorem scheduleRowInsert_pop_gt_of_capacity (lower upper : List α) (x : α)
    (hlower : lower.Pairwise (· ≤ ·)) (hupper : upper.Pairwise (· ≤ ·))
    (hfit : RowsFit lower upper) (hx : x ∉ upper)
    (hcapacity : scheduleCountLT upper x < scheduleCountLT lower x) :
    ∀ p, (scheduleRowInsert lower upper x).2 = some p → x < p := by
  intro p hp
  have hxp := scheduleRowInsert_pop_ge lower upper x p hp
  apply lt_of_le_of_ne hxp
  intro heq
  subst p
  have hsat := scheduleRowInsert_pop_saturated lower upper x x hlower hupper hfit hp
  rw [scheduleCountLE_eq_LT_of_not_mem upper x hx] at hsat
  omega

namespace ScheduleBumpRoute

variable {advance : α → α} {lower : List α} {rows result : List (List α)}
  {x : α} {endpoint : ℕ}

theorem row_lengths (h : ScheduleBumpRoute advance lower rows x result endpoint) (j : ℕ) :
    (result.getD j []).length = (rows.getD j []).length + if j = endpoint then 1 else 0 := by
  induction h generalizing j with
  | top lower row x hs =>
      have hlen := scheduleRowInsert_length lower [] x
      rw [hs] at hlen
      simp only [Option.toList_none, List.length_nil, Nat.add_zero] at hlen
      cases j with
      | zero => simpa using hlen
      | succ j => simp
  | stop lower upper row tail x hs =>
      have hlen := scheduleRowInsert_length lower upper x
      rw [hs] at hlen
      simp only [Option.toList_none, List.length_nil, Nat.add_zero] at hlen
      cases j with
      | zero => simpa using hlen
      | succ j => simp
  | pass lower upper row tail result x p endpoint hs hn ih =>
      have hlen := scheduleRowInsert_length lower upper x
      rw [hs] at hlen
      simp only [Option.toList_some, List.length_cons, List.length_nil, Nat.zero_add] at hlen
      have hrow : row.length = upper.length := by omega
      cases j with
      | zero => simpa using hrow
      | succ j => simpa using ih j

theorem label_content {β : Type*} (label : α → β)
    (hlabel : ∀ z, label (advance z) = label z)
    (h : ScheduleBumpRoute advance lower rows x result endpoint) :
    ((x :: rows.flatten).map label).Perm (result.flatten.map label) := by
  induction h with
  | top lower row x hs =>
      have hp := (scheduleRowInsert_conservation lower [] x).map label
      simpa only [hs, Option.toList_none, List.append_nil, List.flatten_nil,
        List.flatten_cons] using hp
  | stop lower upper row tail x hs =>
      have hp := ((scheduleRowInsert_conservation lower upper x).map label).append_right
        (tail.flatten.map label)
      simpa only [hs, Option.toList_none, List.append_nil, List.map_append,
        List.map_cons, List.flatten_cons, List.cons_append] using hp
  | pass lower upper row tail result x p endpoint hs hn ih =>
      have hp := ((scheduleRowInsert_conservation lower upper x).map label).append_right
        (tail.flatten.map label)
      have htail := ih.append_left (row.map label)
      simp only [List.map_cons, hlabel] at htail
      have hstep : ((x :: (upper :: tail).flatten).map label).Perm
          (row.map label ++ (label p :: tail.flatten.map label)) := by
        simpa only [hs, Option.toList_some, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.singleton_append, List.flatten_cons, List.cons_append,
          List.nil_append] using hp
      apply hstep.trans
      simpa only [List.flatten_cons, List.map_append] using htail

/-- Inputs strictly above the current visit leave all processed counts intact. -/
theorem processed_counts_of_lt (hadvance : ∀ z, z < advance z)
    (h : ScheduleBumpRoute advance lower rows x result endpoint)
    (cutoff : α) (hcx : cutoff < x) (j : ℕ) :
    scheduleCountLE (result.getD j []) cutoff = scheduleCountLE (rows.getD j []) cutoff := by
  induction h generalizing j with
  | top lower row x hs =>
      have hc := scheduleCountLE_insert_eq_of_lt lower [] x cutoff hcx
      rw [hs] at hc
      cases j with
      | zero => simpa using hc
      | succ j => simp
  | stop lower upper row tail x hs =>
      have hc := scheduleCountLE_insert_eq_of_lt lower upper x cutoff hcx
      rw [hs] at hc
      cases j with
      | zero => simpa using hc
      | succ j => rfl
  | pass lower upper row tail result x p endpoint hs hn ih =>
      have hcp : cutoff < p := hcx.trans_le
        (scheduleRowInsert_pop_ge lower upper x p (by rw [hs]))
      have hc := scheduleCountLE_insert_eq_of_lt lower upper x cutoff hcx
      rw [hs] at hc
      cases j with
      | zero => simpa using hc
      | succ j => exact ih (hcp.trans (hadvance p)) j

/-- If the first routine retains the current visit, exactly its starting row
gains one processed entry.  Every later propagated entry is strictly larger. -/
theorem processed_counts_current (hadvance : ∀ z, z < advance z)
    (h : ScheduleBumpRoute advance lower rows x result endpoint)
    (hpop : ∀ p, (scheduleRowInsert lower (rows.headD []) x).2 = some p → x < p)
    (j : ℕ) :
    scheduleCountLE (result.getD j []) x =
      scheduleCountLE (rows.getD j []) x + if j = 0 then 1 else 0 := by
  cases h with
  | top lower row x hs =>
      have hc := scheduleCountLE_insert_current_gain lower [] x hpop
      rw [hs] at hc
      cases j with
      | zero => simpa using hc
      | succ j => simp
  | stop lower upper row tail x hs =>
      have hc := scheduleCountLE_insert_current_gain lower upper x hpop
      rw [hs] at hc
      cases j with
      | zero => simpa using hc
      | succ j => simp
  | pass lower upper row tail result x p endpoint hs hn =>
      have hxp := hpop p (by simp only [List.headD_cons, hs])
      have hc := scheduleCountLE_insert_current_gain lower upper x hpop
      rw [hs] at hc
      cases j with
      | zero => simpa using hc
      | succ j => simpa using hn.processed_counts_of_lt hadvance x (hxp.trans (hadvance p)) j

end ScheduleBumpRoute
end HigherSpecht
end CanonicalSource61

section CanonicalSource62
/- Source: HigherSpecht/HanadaFrontierAbsorption.lean -/



/-!
# The first route stops by its deleted-cell frontier

Before the first corrected route, every row strictly below the removed
column tail is unchanged.  At the frontier the upper row is exactly the
original row with one entry removed.  A propagated input reaches that
frontier at least as large as the removed entry.  The actual bounded
insertion therefore absorbs it there, or has already absorbed it below.

The lemma explicitly tracks the final unchanged pre row as the lower
barrier for the frontier.  It makes no pointwise assertion about compacted
rows, and hence avoids the failed blanket bound from the earlier argument.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

theorem LowerBarrierRelaxed.refl (lower : List α) : LowerBarrierRelaxed lower lower := by
  exact LowerBarrierRelaxed.of_take le_rfl (by
    rw [List.take_length]
    exact List.forall₂_refl lower)

def RouteFrontierFits (lower : List α) : List (List α) → List α → Prop
  | [], upper => RowsFit lower upper
  | row :: tail, upper => RouteFrontierFits row tail upper

theorem RouteFrontierFits.relax_lower {new old : List α} {pre : List (List α)}
    {upper : List α} (hrelax : LowerBarrierRelaxed new old)
    (hfit : RouteFrontierFits old pre upper) : RouteFrontierFits new pre upper := by
  cases pre with
  | nil => exact RowsFit.relax_lower hrelax hfit
  | cons row tail => exact hfit

/-- An actual finite route reaches an absorbing shortened row by the stated
frontier distance.  Every preceding row update is retained in the result. -/
theorem ScheduleBumpRoute.exists_to_deleted_frontier
    (advance : α → α) (hmono : Monotone advance)
    (lower : List α) (pre : List (List α)) (original : List α)
    (tail : List (List α)) (old x : α)
    (hsorted : original.Pairwise (· < ·)) (hold : old ∈ original)
    (hfit : RouteFrontierFits lower pre original)
    (hreach : old ≤ advance^[pre.length] x) :
    ∃ result endpoint,
      ScheduleBumpRoute advance lower (pre ++ original.erase old :: tail) x result endpoint ∧
        endpoint ≤ pre.length := by
  induction pre generalizing lower x with
  | nil =>
      have hle : old ≤ x := hreach
      have hstep := scheduleRowInsert_absorbs_deleted_entry hsorted hfit hold hle
      exact ⟨sortedRowReplacement original old x :: tail, 0,
        .stop lower (original.erase old) _ tail x hstep, le_rfl⟩
  | cons row pre ih =>
      cases hp : (scheduleRowInsert lower row x).2 with
      | none =>
          exact ⟨(scheduleRowInsert lower row x).1 :: (pre ++ original.erase old :: tail), 0,
            .stop lower row _ _ x (Prod.ext rfl hp), Nat.zero_le _⟩
      | some p =>
          have hxp : x ≤ p := scheduleRowInsert_pop_ge lower row x p hp
          have hfit' : RouteFrontierFits (scheduleRowInsert lower row x).1 pre original :=
            RouteFrontierFits.relax_lower (scheduleRowInsert_lower_relaxed lower row x) hfit
          have hreach' : old ≤ advance^[pre.length] (advance p) := by
            have h := hreach
            simp only [List.length_cons, Function.iterate_succ_apply] at h
            exact h.trans ((hmono.iterate pre.length) (hmono hxp))
          obtain ⟨result, endpoint, hroute, hbound⟩ := ih
            (scheduleRowInsert lower row x).1 (advance p) hfit' hreach'
          refine ⟨(scheduleRowInsert lower row x).1 :: result, endpoint + 1,
            .pass lower row _ _ result x p endpoint (Prod.ext rfl hp) hroute, ?_⟩
          simpa only [List.length_cons] using Nat.add_le_add_right hbound 1

end HigherSpecht
end CanonicalSource62

section CanonicalSource63
/- Source: HigherSpecht/HanadaConsecutiveRoutes.lean -/



/-!
# Consecutive shifted-tail insertions

Each successive input starts one row above the preceding input.  The
execution freezes the resulting first row and continues on the actual
updated tail.  The adjacent-route theorem constructs every next route with
a no larger relative endpoint.  The exact row-count gain is recorded by a
finite recursive endpoint counter.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

inductive GradedIncreasingInputs (height : α → ℕ) : ℕ → List α → Prop
  | nil (r : ℕ) : GradedIncreasingInputs height r []
  | cons {r : ℕ} {x : α} {tail : List α}
      (atHeight : height x = r) (increasing : ∀ y ∈ tail, x < y)
      (tailValid : GradedIncreasingInputs height (r + 1) tail) :
      GradedIncreasingInputs height r (x :: tail)

inductive ConsecutiveBumpRoutes (advance : α → α) :
    List α → List (List α) → List α → List (List α) → List ℕ → Prop
  | nil (lower : List α) (rows : List (List α)) :
      ConsecutiveBumpRoutes advance lower rows [] rows []
  | cons (lower row : List α) (rows tail output : List (List α))
      (x : α) (inputs : List α) (endpoint : ℕ) (endpoints : List ℕ)
      (first : ScheduleBumpRoute advance lower rows x (row :: tail) endpoint)
      (rest : ConsecutiveBumpRoutes advance row tail inputs output endpoints) :
      ConsecutiveBumpRoutes advance lower rows (x :: inputs) (row :: output) (endpoint :: endpoints)

namespace ScheduleRowsValid

theorem tail_valid {height : α → ℕ} {r : ℕ} {row : List α} {tail : List (List α)}
    (h : ScheduleRowsValid height r (row :: tail)) : ScheduleRowsValid height (r + 1) tail := by
  cases h with
  | cons _ _ _ ht => exact ht

end ScheduleRowsValid

theorem ConsecutiveBumpRoutes.exists_of_first_route
    {advance : α → α} {height : α → ℕ}
    (hmono : StrictMono advance) (hadvance : ∀ z, z < advance z)
    (hheight : ∀ z, height (advance z) = height z + 1)
    {lower : List α} {rows firstResult : List (List α)} {x : α} {inputs : List α}
    {endpoint r : ℕ} (first : ScheduleBumpRoute advance lower rows x firstResult endpoint)
    (hrows : ScheduleRowsValid height r rows)
    (hinputs : GradedIncreasingInputs height r (x :: inputs)) :
    ∃ result endpoints,
      ConsecutiveBumpRoutes advance lower rows (x :: inputs) result endpoints ∧
        ∀ e ∈ endpoints, e ≤ endpoint := by
  induction inputs generalizing r lower rows firstResult x endpoint with
  | nil =>
      cases firstResult with
      | nil => exact (first.result_nonempty rfl).elim
      | cons row tail =>
          exact ⟨row :: tail, [endpoint],
            .cons lower row rows tail tail x [] endpoint [] first (.nil row tail), by simp⟩
  | cons y inputs ih =>
      cases hinputs with
      | cons hx hxy htailInputs =>
          have hy : height y = r + 1 := by
            cases htailInputs with
            | cons hy _ _ => exact hy
          cases firstResult with
          | nil => exact (first.result_nonempty rfl).elim
          | cons row tail =>
              obtain ⟨nextResult, nextEndpoint, next, hnextBound⟩ :=
                first.adjacent_endpoint hmono hadvance hheight hrows hx
                  (LowerBarrierRelaxed.refl row) hy (hxy y (by simp))
              have htailRows := (first.valid hheight hrows hx).tail_valid
              obtain ⟨output, endpoints, hrest, hbounds⟩ := ih next htailRows htailInputs
              refine ⟨row :: output, endpoint :: endpoints,
                .cons lower row rows tail output x (y :: inputs) endpoint endpoints first hrest, ?_⟩
              intro e he
              rcases List.mem_cons.mp he with rfl | he
              · exact le_rfl
              · exact (hbounds e he).trans hnextBound

def routeEndpointCount : List ℕ → ℕ → ℕ
  | [], _ => 0
  | e :: tail, r => (if r = e then 1 else 0) + if r = 0 then 0 else routeEndpointCount tail (r - 1)

namespace ConsecutiveBumpRoutes

variable {advance : α → α} {lower : List α} {rows result : List (List α)}
  {inputs : List α} {endpoints : List ℕ}

theorem length_endpoints (h : ConsecutiveBumpRoutes advance lower rows inputs result endpoints) :
    endpoints.length = inputs.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

theorem lower_fits (h : ConsecutiveBumpRoutes advance lower rows inputs result endpoints)
    (hfit : RowsFit lower (rows.headD [])) : RowsFit lower (result.headD []) := by
  cases h with
  | nil => exact hfit
  | cons lower row rows tail output x inputs endpoint endpoints first rest =>
      exact first.lower_fits hfit

theorem valid {height : α → ℕ} (hheight : ∀ z, height (advance z) = height z + 1)
    (h : ConsecutiveBumpRoutes advance lower rows inputs result endpoints)
    {r : ℕ} (hrows : ScheduleRowsValid height r rows)
    (hinputs : GradedIncreasingInputs height r inputs) : ScheduleRowsValid height r result := by
  induction h generalizing r with
  | nil => exact hrows
  | cons lower row rows tail output x inputs endpoint endpoints first rest ih =>
      cases hinputs with
      | cons hx hlt hinputs =>
          have hfirst := first.valid hheight hrows hx
          cases hfirst with
          | cons hsorted hh hcolumns htail =>
              exact .cons hsorted hh (rest.lower_fits hcolumns) (ih htail hinputs)

theorem row_lengths (h : ConsecutiveBumpRoutes advance lower rows inputs result endpoints)
    (j : ℕ) :
    (result.getD j []).length = (rows.getD j []).length + routeEndpointCount endpoints j := by
  induction h generalizing j with
  | nil => simp only [routeEndpointCount, Nat.add_zero]
  | cons lower row rows tail output x inputs endpoint endpoints first rest ih =>
      cases j with
      | zero => simpa [routeEndpointCount] using first.row_lengths 0
      | succ j =>
          have hfirst := first.row_lengths (j + 1)
          have hrest := ih j
          simp only [List.getD_cons_succ] at hfirst ⊢
          rw [hrest, hfirst]
          simp [routeEndpointCount, Nat.add_assoc]

theorem label_content {β : Type*} (label : α → β)
    (hlabel : ∀ z, label (advance z) = label z)
    (h : ConsecutiveBumpRoutes advance lower rows inputs result endpoints) :
    ((inputs ++ rows.flatten).map label).Perm (result.flatten.map label) := by
  induction h with
  | nil => simp
  | cons lower row rows tail output x inputs endpoint endpoints first rest ih =>
      have hfirst := (first.label_content label hlabel).append_left (inputs.map label)
      have hrest := ih.append_left (row.map label)
      have hswap : ((x :: inputs ++ rows.flatten).map label).Perm
          (inputs.map label ++ ((x :: rows.flatten).map label)) := by
        simpa only [List.map_cons, List.map_append, List.cons_append,
          List.nil_append, List.append_assoc] using
          (List.perm_append_comm (l₁ := [label x]) (l₂ := inputs.map label)).append_right
            (rows.flatten.map label)
      apply hswap.trans
      apply hfirst.trans
      have hswap' := (List.perm_append_comm (l₁ := inputs.map label) (l₂ := row.map label)).append_right
        (tail.flatten.map label)
      have horder : (inputs.map label ++ ((row :: tail).flatten.map label)).Perm
          (row.map label ++ ((inputs ++ tail.flatten).map label)) := by
        simpa only [List.flatten_cons, List.map_append, List.append_assoc] using hswap'
      apply horder.trans
      simpa only [List.flatten_cons, List.map_append, List.append_assoc] using hrest

theorem processed_counts_of_lt (hadvance : ∀ z, z < advance z)
    (h : ConsecutiveBumpRoutes advance lower rows inputs result endpoints)
    (cutoff : α) (hinputs : ∀ x ∈ inputs, cutoff < x) (j : ℕ) :
    scheduleCountLE (result.getD j []) cutoff = scheduleCountLE (rows.getD j []) cutoff := by
  induction h generalizing j with
  | nil => rfl
  | cons lower row rows tail output x inputs endpoint endpoints first rest ih =>
      have hfirst := first.processed_counts_of_lt hadvance cutoff (hinputs x (by simp))
      have hrest := ih (fun z hz => hinputs z (List.mem_cons_of_mem x hz))
      cases j with
      | zero => exact hfirst 0
      | succ j => exact (hrest j).trans (hfirst (j + 1))

theorem processed_counts_current {x : α} {tailInputs : List α}
    (hadvance : ∀ z, z < advance z)
    (h : ConsecutiveBumpRoutes advance lower rows (x :: tailInputs) result endpoints)
    (hinputs : ∀ y ∈ tailInputs, x < y)
    (hpop : ∀ p, (scheduleRowInsert lower (rows.headD []) x).2 = some p → x < p)
    (j : ℕ) :
    scheduleCountLE (result.getD j []) x =
      scheduleCountLE (rows.getD j []) x + if j = 0 then 1 else 0 := by
  cases h with
  | cons lower row rows tail output x inputs endpoint endpoints first rest =>
      have hfirst := first.processed_counts_current hadvance hpop
      cases j with
      | zero => exact hfirst 0
      | succ j =>
          have hrest := rest.processed_counts_of_lt hadvance x hinputs j
          simpa using hrest.trans (hfirst (j + 1))

end ConsecutiveBumpRoutes

end HigherSpecht
end CanonicalSource63
