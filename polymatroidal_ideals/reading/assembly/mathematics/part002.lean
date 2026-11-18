module
public import reading.assembly.mathematics.part001
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-! ## Source: Characterizations.Strands.SocleTor -/
section CheckedCharacterizationsSource67

/-! # A monomial socle element produces the actual top derived-Tor class -/
noncomputable section
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V]

lemma socle_faces_eq_boundary (B : Family V) (a : Exponent V)
    (hout : ¬Contains B a) (hmul : ∀ j, Contains B (a + Finsupp.single j 1)) :
    koszulFaces B (a + faceExponent Finset.univ) = simplexBoundary (Finset.univ : Finset V) := by
  funext s
  apply propext
  constructor
  · rintro ⟨hs, hmem⟩
    refine ⟨Finset.subset_univ s, ?_⟩
    intro hsub
    have he : s = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ s) hsub
    subst s
    apply hout
    simpa using hmem
  · intro hs
    have hdiv : faceExponent s ≤ a + faceExponent Finset.univ :=
      (faceExponent_mono (Finset.subset_univ s)).trans
        (le_add_of_nonneg_left (show (0 : Exponent V) ≤ a from zero_le))
    refine ⟨hdiv, ?_⟩
    obtain ⟨j, hj, hjs⟩ := Finset.exists_of_ssubset hs
    obtain ⟨b, hb, hba⟩ := hmul j
    refine ⟨b, hb, hba.trans ?_⟩
    intro x
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, faceExponent_apply,
      Finset.mem_univ, ite_true, Finsupp.single_apply]
    by_cases hxj : x = j
    · subst x
      simp [hjs]
    · by_cases hxs : x ∈ s <;> simp [hxj, Ne.symm hxj, hxs] <;> omega

lemma socle_bettiNumber_eq_one [Field k] (B : Family V) (a : Exponent V)
    (hout : ¬Contains B a) (hmul : ∀ j, Contains B (a + Finsupp.single j 1))
    (i : ℕ) (hcard : Fintype.card V = i+1) :
    bettiNumber (k := k) B (a + faceExponent Finset.univ) i = 1 :=
  bettiNumber_eq_one_of_boundary B _ Finset.univ i (by simpa using hcard)
    (socle_faces_eq_boundary B a hout hmul)

lemma socle_gradedBettiNonzero [Field k] (B : Family V) (a : Exponent V)
    (hout : ¬Contains B a) (hmul : ∀ j, Contains B (a + Finsupp.single j 1))
    (i : ℕ) (hcard : Fintype.card V = i+1) :
    GradedBettiNonzero (k := k) B (a + faceExponent Finset.univ) i := by
  rw [← bettiNumber_pos_iff, socle_bettiNumber_eq_one B a hout hmul i hcard]
  exact Nat.zero_lt_one

lemma relative_socle_faces_eq_boundary (B : Family V) (a : Exponent V) (U : Finset V)
    (hsupp : a.support ⊆ U) (hout : ¬Contains B a)
    (hmul : ∀ j ∈ U, Contains B (a + Finsupp.single j 1)) :
    koszulFaces B (a + faceExponent U) = simplexBoundary U := by
  have hsupp' : (a + faceExponent U).support = U := by
    ext j
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, faceExponent_apply]
    by_cases hj : j ∈ U
    · simp [hj]
    · have hz : a j = 0 := Finsupp.notMem_support_iff.mp (fun h => hj (hsupp h))
      simp [hj, hz]
  funext s
  apply propext
  constructor
  · rintro ⟨hdiv, hmem⟩
    have hs : s ⊆ U := by
      simpa only [hsupp'] using (faceExponent_le_iff_subset_support s _).mp hdiv
    refine ⟨hs, ?_⟩
    intro hUs
    have he : s = U := Finset.Subset.antisymm hs hUs
    subst s
    apply hout
    simpa using hmem
  · intro hs
    have hdiv : faceExponent s ≤ a + faceExponent U :=
      (faceExponent_mono hs.subset).trans
        (le_add_of_nonneg_left (show (0 : Exponent V) ≤ a from zero_le))
    refine ⟨hdiv, ?_⟩
    obtain ⟨j, hj, hjs⟩ := Finset.exists_of_ssubset hs
    obtain ⟨b, hb, hba⟩ := hmul j hj
    refine ⟨b, hb, hba.trans ?_⟩
    intro x
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, faceExponent_apply, Finsupp.single_apply]
    by_cases hxj : x = j
    · subst x
      simp [hjs, hj]
    · by_cases hxs : x ∈ s
      · have hxU := hs.subset hxs
        simp [hxj, Ne.symm hxj, hxs, hxU]
      · simp [hxj, Ne.symm hxj, hxs]

lemma relative_socle_bettiNumber_eq_one [Field k] (B : Family V) (a : Exponent V)
    (U : Finset V) (hsupp : a.support ⊆ U) (hout : ¬Contains B a)
    (hmul : ∀ j ∈ U, Contains B (a + Finsupp.single j 1)) (i : ℕ)
    (hcard : U.card = i+1) : bettiNumber (k := k) B (a+faceExponent U) i = 1 :=
  bettiNumber_eq_one_of_boundary B _ U i hcard
    (relative_socle_faces_eq_boundary B a U hsupp hout hmul)

end Characterizations.Strands

end
end CheckedCharacterizationsSource67

/-! ## Source: Characterizations.MinimalMixedObstruction -/
section CheckedCharacterizationsSource68

/-! # Every failure has a genuine nonlinear Tor class in the degree-bounded range -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem betti_restriction_sameambient (B : Family V) (U : Finset V) (a : Exponent V)
    (ha : project U a = a) (i : ℕ) :
    bettiNumber (k := k) (restriction B U) a i = bettiNumber (k := k) B a i := by
  have hfaces : koszulFaces (restriction B U) a = koszulFaces B a := by
    funext s
    apply propext
    change (faceExponent s ≤ a ∧ Contains (restriction B U) (a-faceExponent s)) ↔ _
    rw [contains_restriction]
    have hs := supported_of_le ha (tsub_le_self : a-faceExponent s ≤ a)
    rw [hs]
    rfl
  rw [Strands.bettiNumber_eq_face_homology_finrank,Strands.bettiNumber_eq_face_homology_finrank,
    Strands.chainComplex_congr (koszulFaces_downward _ _) (koszulFaces_downward _ _) hfaces]

theorem relative_socle_above_missing_base {L : Family V} (hL : L.Nonempty)
    (U : Finset V) (hs : ∀ c ∈ L, project U c = c)
    (hloc : ∀ W : Finset V, W ⊂ U → IsPolymatroidal (localize L W))
    {a : Exponent V} (ha : LowerFeasible (lowerRank L) a)
    (has : project U a = a) (hout : ¬Contains L a) :
    ∃ b, a ≤ b ∧ project U b = b ∧ ¬Contains L b ∧
      ∀ i ∈ U, Contains L (b+Finsupp.single i 1) := by
  apply exists_socle_above L U a has hout
  intro i hi
  have hgood := lowerFeasible_project_mem hL ha (U.erase i)
    (hloc _ (Finset.erase_ssubset hi))
  obtain ⟨c,hc,hca⟩ := (contains_localize L (U.erase i) _).mp hgood
  refine ⟨c i,c,hc,?_⟩
  intro j
  by_cases hji : j = i
  · subst j; simp
  · by_cases hjU : j ∈ U
    · have hjE : j ∈ U.erase i := Finset.mem_erase.mpr ⟨hji,hjU⟩
      have hh := hca j
      simpa only [project_apply,if_pos hjE,Finsupp.add_apply,Finsupp.single_apply,
        if_neg (Ne.symm hji),add_zero] using hh
    · have hz := congrArg (fun x : Exponent V => x j) (hs c hc)
      simp only [project_apply,if_neg hjU] at hz
      rw [← hz]
      exact Nat.zero_le _

/-- The obstruction underlying Theorems4.2 and4.9. All Betti numbers are the
actual numerical dimensions of the derived Tor components in the ambient ring;
the exhibited degree is supported on the retained localization coordinates. -/
theorem exists_low_nonlinear_localization {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) (hn : ¬IsPolymatroidal B) :
    ∃ (U : Finset V) (e i : ℕ) (a : Exponent V),
      Equigenerated (localize B U) e ∧ lowerRank B U = e ∧ 2 ≤ U.card ∧
      1 ≤ i ∧ i ≤ e-1 ∧ i ≤ U.card-1 ∧ a.support ⊆ U ∧
      e+i < a.degree ∧ bettiNumber (k := k) (localize B U) a i ≠ 0 := by
  obtain ⟨A,U,hUA,hL,hnL,hloc,hrest⟩ := exists_minimal_bad_mixedMinor hB hanti hn
  let L := mixedMinor B A U
  have hantiL : Antichain L := localize_antichain _ _
  have hlL : LocallyEquigenerated L := mixedMinor_locallyEquigenerated hl A U
  obtain ⟨e,he⟩ := hlL Finset.univ
  rw [localize_univ_of_antichain hantiL] at he
  have hs : ∀ c ∈ L, project U c = c := fun c hc => localize_supported hc
  have hcard : 2 ≤ U.card := by
    by_contra h
    exact hnL (supported_equigenerated_polymatroidal_card_le_one he U hs (by omega))
  have hnot : ¬ lowerBaseFamily (lowerRank L) e ⊆ L := by
    intro h
    have hEq : L = lowerBaseFamily (lowerRank L) e :=
      Finset.Subset.antisymm (subset_lowerBaseFamily he) h
    apply hnL
    change IsPolymatroidal L
    rw [hEq]
    exact canonicalLowerBases_polymatroidal hL hlL he
  obtain ⟨a,haJ,haL⟩ := Finset.not_subset.mp hnot
  obtain ⟨hade,hafeas⟩ := (mem_lowerBaseFamily _ _ _).mp haJ
  have hout : ¬Contains L a := fun h => haL ((he.mem_iff_contains hade).mpr h)
  have hsupp : a.support = U := missing_base_full_support hL hlL he U hs hrest haJ hout
  have hUe : U.card ≤ e := by simpa only [hsupp,hade] using degree_ge_support_card a
  have has : project U a = a := lowerBase_supported hL he U hs haJ
  obtain ⟨b,hab,hbs,hbout,hmul⟩ := relative_socle_above_missing_base hL U hs hloc hafeas has hout
  let α := b+faceExponent U
  have hα : project U α = α := by
    dsimp [α]
    rw [project_add,hbs]
    congr 1
    ext j
    simp only [project_apply,faceExponent_apply]
    split_ifs <;> rfl
  have hβ : bettiNumber (k := k) L α (U.card-1) = 1 :=
    Strands.relative_socle_bettiNumber_eq_one L b U
      ((project_eq_self_iff_support_subset b U).mp hbs) hbout hmul _ (by omega)
  have hαdegree : e+(U.card-1) < α.degree := by
    have hdeg := degree_mono hab
    rw [hade] at hdeg
    dsimp [α]
    rw [map_add,Strands.degree_faceExponent]
    omega
  let T := U ∪ Aᶜ
  have hUT : U ⊆ T := Finset.subset_union_left
  have hTdegree : lowerRank B T = e := by
    have h := mixedMinor_lowerRank hl hL hUA (Finset.Subset.refl U)
    rw [lowerRank_on_support hL he U hs] at h
    exact h.symm
  have hTgen : Equigenerated (localize B T) e := by
    intro c hc
    exact (localize_degree hB hl hc).trans hTdegree
  have hLeq : L = restriction (localize B T) U := localize_restriction B hUA
  have hβT : bettiNumber (k := k) (localize B T) α (U.card-1) = 1 := by
    rw [hLeq,betti_restriction_sameambient _ U α hα] at hβ
    exact hβ
  refine ⟨T,e,U.card-1,α,hTgen,hTdegree,?_,by omega,by omega,?_,?_,hαdegree,?_⟩
  · exact hcard.trans (Finset.card_le_card hUT)
  · have h := Finset.card_le_card hUT
    omega
  · exact ((project_eq_self_iff_support_subset α U).mp hα).trans hUT
  · rw [hβT]
    exact one_ne_zero

end Characterizations

end
end CheckedCharacterizationsSource68

/-! ## Source: Characterizations.Triangular -/
section CheckedCharacterizationsSource69

/-! # The degree-bounded and triangular localization characterizations

Theorems 4.2, 4.5 (sufficiency), and 4.9, with the exact polynomial rings on
the retained variables and genuine derived-Tor Betti components.
-/

noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid CommAlg.Koszul Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

def RetainedLinearThrough (B : Family V) (U : Finset V) (e t : ℕ) : Prop :=
  ∀ a : Exponent U, ∀ i : ℕ, i ≤ t →
    a.degree ≠ e+i → bettiNumber (k := k) (localFamily B U) a i = 0

theorem localLinearThrough_iff_retained (B : Family V) (U : Finset V) (e t : ℕ) :
    LocalLinearThrough (k := k) B U e t ↔ RetainedLinearThrough (k := k) B U e t := by
  constructor
  · intro h a i hi hoff
    have hs := Strands.extend_support_subset U a
    have hh := h (extendExponent U a) hs i hi (by simpa only [extendExponent_degree] using hoff)
    rw [betti_localize_supported B U _ hs i,restrict_extend] at hh
    exact hh
  · intro h a ha i hi hoff
    rw [betti_localize_supported B U a ha i]
    exact h (restrictExponent U a) i hi (by rwa [restrictExponent_degree_supported U a ha])

/-- The literal local-ring statement of the triangular tests. -/
def RetainedTriangularTests (B : Family V) (d : ℕ) : Prop :=
  ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
    ∃ e, Equigenerated (localFamily B U) e ∧
      (0 < e → RetainedLinearThrough (k := k) B U e
        (min (e-1) (min (d-1-(Fintype.card V-U.card)) (U.card-1))))

theorem triangularTests_iff_retained (B : Family V) (d : ℕ) :
    TriangularTests (k := k) B d ↔ RetainedTriangularTests (k := k) B d := by
  simp only [TriangularTests,RetainedTriangularTests,
    localFamily_equigenerated_iff,localLinearThrough_iff_retained]

/-- Theorem 4.9 in the ambient supported-degree description. -/
theorem polymatroidal_iff_triangular_ambient {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔ TriangularTests (k := k) B d := by
  refine ⟨fun hp => triangularTests_of_polymatroidal hp d,?_⟩
  intro ht
  by_contra hn
  have hl := locallyEquigenerated_of_triangularTests hB hd ht
  obtain ⟨U,e,i,a,he,hr,hc,hi,hie,hic,ha,hdeg,hbetti⟩ :=
    exists_low_nonlinear_localization (k := k) hB hd.antichain hl hn
  exact triangularTests_exclude_low_nonlinear hB hd ht U e i a he hr hc hi hie hic ha hdeg hbetti

/-- Theorem 4.9, with every Betti component computed over `k[U]`. -/
theorem polymatroidal_iff_triangular {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔ RetainedTriangularTests (k := k) B d :=
  (polymatroidal_iff_triangular_ambient hB hd hd2).trans (triangularTests_iff_retained B d)

/-- Theorem 4.5 with prior local equigeneration: codimension at most d−2
suffices, and the conclusion is the full exchange axiom. -/
theorem polymatroidal_iff_pure_localization_band {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) (hl : LocallyEquigenerated B) :
    IsPolymatroidal B ↔
      ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-2 →
        HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  refine ⟨fun hp U _ _ => polymatroidal_local_linearResolutions hp U,?_⟩
  intro ht
  by_contra hn
  obtain ⟨U,e,i,a,he,hr,hc,hi,hie,hic,ha,hdeg,hbetti⟩ :=
    exists_low_nonlinear_localization (k := k) hB hd.antichain hl hn
  exact linearBand_excludes_low_nonlinear hB hd hl ht U e i a he hr hc hi hie hic ha hdeg hbetti

/-- Theorem 4.5 without prior local equigeneration: codimension at most d−1
forces both purity and the complete polymatroid exchange property. -/
theorem polymatroidal_iff_localization_band {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔
      ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
        HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  refine ⟨fun hp U _ _ => polymatroidal_local_linearResolutions hp U,?_⟩
  intro ht
  have hl := locallyEquigenerated_of_linearBand hB hd ht
  exact (polymatroidal_iff_pure_localization_band hB hd hd2 hl).mpr
    (fun U hc hk => ht U hc (by omega))

def DegreeBoundedTests (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
    (0 < e → RetainedLinearThrough (k := k) B U e (e-1))

def DegreeDimensionBoundedTests (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
    (0 < e → RetainedLinearThrough (k := k) B U e (min (e-1) (U.card-1)))

theorem degreeBoundedTests_of_polymatroidal {B : Family V} (hB : B.Nonempty)
    (hp : IsPolymatroidal B) : DegreeBoundedTests (k := k) B := by
  intro U
  have he := localFamily_equigenerated hp U
  refine ⟨lowerRank B U,he,?_⟩
  intro _
  apply (localLinearThrough_iff_retained B U _ _).mp
  exact localLinearThrough_of_linearResolution hB U
    (localFamily_equigenerated_iff.mp he) (polymatroidal_local_linearResolutions hp U) _

theorem degreeDimensionBoundedTests_of_degreeBoundedTests {B : Family V}
    (ht : DegreeBoundedTests (k := k) B) : DegreeDimensionBoundedTests (k := k) B := by
  intro U
  obtain ⟨e,he,hlinear⟩ := ht U
  exact ⟨e,he,fun hp a i hi hoff => hlinear hp a i (hi.trans (min_le_left _ _)) hoff⟩

/-- Theorem 4.2, including the smaller equivalent depth
`min {e_U−1, |U|−1}`. No original equigeneration hypothesis is added. -/
theorem polymatroidal_iff_degree_dimension_tests {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔ DegreeDimensionBoundedTests (k := k) B := by
  refine ⟨fun hp => degreeDimensionBoundedTests_of_degreeBoundedTests
    (degreeBoundedTests_of_polymatroidal hB hp),?_⟩
  intro ht
  have hl : LocallyEquigenerated B := by
    intro U
    obtain ⟨e,he,_⟩ := ht U
    exact ⟨e,localFamily_equigenerated_iff.mp he⟩
  by_contra hn
  obtain ⟨U,e,i,a,he,hr,hc,hi,hie,hic,ha,hdeg,hbetti⟩ :=
    exists_low_nonlinear_localization (k := k) hB hanti hl hn
  obtain ⟨f,hf,hlinear⟩ := ht U
  have hf' := localFamily_equigenerated_iff.mp hf
  obtain ⟨b,hb⟩ := localize_nonempty hB U
  have hef : e = f := (he b hb).symm.trans (hf' b hb)
  subst f
  have hvan := (localLinearThrough_iff_retained B U e _).mpr (hlinear (by omega))
  exact hbetti (hvan a ha i (le_min hie hic) (by omega))

/-- Theorem 4.2 with exactly the displayed degree cutoff `e_U−1`. -/
theorem polymatroidal_iff_degree_tests {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔ DegreeBoundedTests (k := k) B :=
  ⟨degreeBoundedTests_of_polymatroidal hB,fun ht =>
    (polymatroidal_iff_degree_dimension_tests hB hanti).mpr
      (degreeDimensionBoundedTests_of_degreeBoundedTests ht)⟩

end Characterizations

end
end CheckedCharacterizationsSource69

/-! ## Source: Characterizations.Isolators.Optimality -/
section CheckedCharacterizationsSource70

/-! # Exact optimal localization families and the smallest isolator degrees -/
noncomputable section
set_option maxHeartbeats 600000
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Full fixed-family equivalence in Theorem 4.5, without prior local purity. -/
theorem localizationTestSufficient_iff (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d) :
    LocalizationTestSufficient (k := k) Γ d ↔ localizationBand (V := V) (d-1) ⊆ Γ := by
  constructor
  · exact localizationTestSufficient_necessary Γ d hd
  · intro hΓ B hB hdeg htest
    apply (polymatroidal_iff_localization_band (k := k) hB hdeg hd).mpr
    intro U hm hk
    exact htest U (hΓ ((mem_localizationBand _ _).mpr ⟨hm, by simpa only [card_compl] using hk⟩))

/-- Full fixed-family equivalence in Theorem 4.5 with prior local purity. -/
theorem pureLocalizationTestSufficient_iff (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d) :
    PureLocalizationTestSufficient (k := k) Γ d ↔ localizationBand (V := V) (d-2) ⊆ Γ := by
  constructor
  · exact pureLocalizationTestSufficient_necessary Γ d hd
  · intro hΓ B hB hdeg hl htest
    apply (polymatroidal_iff_pure_localization_band (k := k) hB hdeg hd hl).mpr
    intro U hm hk
    exact htest U (hΓ ((mem_localizationBand _ _).mpr ⟨hm, by simpa only [card_compl] using hk⟩))

/-- The exact ordinary-band minimum is attained and bounds every valid testing family. -/
theorem localizationTest_minimum (d : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ Fintype.card V) :
    (∃ Γ : Finset (Finset V), LocalizationTestSufficient (k := k) Γ d ∧
      Γ.card = ∑ j ∈ Finset.range (min (d-1) (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j) ∧
    (∀ Γ : Finset (Finset V), LocalizationTestSufficient (k := k) Γ d →
      (∑ j ∈ Finset.range (min (d-1) (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j) ≤ Γ.card) := by
  constructor
  · exact ⟨localizationBand (d-1), (localizationTestSufficient_iff _ d hd).mpr le_rfl,
      localizationBand_card (d-1) hn⟩
  · intro Γ hΓ
    rw [← localizationBand_card (d-1) hn]
    exact Finset.card_le_card ((localizationTestSufficient_iff Γ d hd).mp hΓ)

/-- The exact narrower-band minimum under prior local equigeneration. -/
theorem pureLocalizationTest_minimum (d : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ Fintype.card V) :
    (∃ Γ : Finset (Finset V), PureLocalizationTestSufficient (k := k) Γ d ∧
      Γ.card = ∑ j ∈ Finset.range (min (d-2) (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j) ∧
    (∀ Γ : Finset (Finset V), PureLocalizationTestSufficient (k := k) Γ d →
      (∑ j ∈ Finset.range (min (d-2) (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j) ≤ Γ.card) := by
  constructor
  · exact ⟨localizationBand (d-2), (pureLocalizationTestSufficient_iff _ d hd).mpr le_rfl,
      localizationBand_card (d-2) hn⟩
  · intro Γ hΓ
    rw [← localizationBand_card (d-2) hn]
    exact Finset.card_le_card ((pureLocalizationTestSufficient_iff Γ d hd).mp hΓ)

/-- Any equigenerated ideal with a unique bad localization has degree at least
codimension plus one, and never degree zero or one. -/
theorem unique_bad_degree_lower_bound {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hgood : ∀ R : Finset V, R ≠ U →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) R)) :
    2 ≤ d ∧ Uᶜ.card+1 ≤ d := by
  have hd2 : 2 ≤ d := by
    by_contra hn
    exact hbad (polymatroidal_local_linearResolutions
      (equigenerated_polymatroidal_of_degree_le_one hd (by omega)) U)
  refine ⟨hd2, ?_⟩
  by_contra hcost
  have hp : IsPolymatroidal B := (polymatroidal_iff_localization_band (k := k) hB hd hd2).mpr (by
    intro R hm hk
    apply hgood R
    intro he
    subst R
    have hc : Uᶜ.card = Fintype.card V-U.card := card_compl U
    omega)
  exact hbad (polymatroidal_local_linearResolutions hp U)

/-- Proposition 4.7's sharper optimality when all localizations are equigenerated. -/
theorem pure_unique_bad_degree_lower_bound {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (hl : LocallyEquigenerated B) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hgood : ∀ R : Finset V, R ≠ U →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) R)) :
    Uᶜ.card+2 ≤ d := by
  have hd2 := (unique_bad_degree_lower_bound hB hd U hbad hgood).1
  by_contra hcost
  have hp : IsPolymatroidal B :=
    (polymatroidal_iff_pure_localization_band (k := k) hB hd hd2 hl).mpr (by
      intro R hm hk
      apply hgood R
      intro he
      subst R
      have hc : Uᶜ.card = Fintype.card V-U.card := card_compl U
      omega)
  exact hbad (polymatroidal_local_linearResolutions hp U)

end Characterizations.Isolators

end
end CheckedCharacterizationsSource70

/-! ## Source: Characterizations.MonomialNormalForm -/
section CheckedCharacterizationsSource71

/-! # Every monomial ideal has its unique finite minimal monomial presentation

The input notion allows an arbitrary, possibly infinite, set of exponents. The
finite-antichain presentation is proved using Hilbert's basis theorem, not included
as an assumption in the notion of monomial ideal.
-/
noncomputable section
set_option maxHeartbeats 600000
namespace Characterizations
open Classical Finset CommAlg CommAlg.Polymatroid MvPolynomial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The ordinary meaning of a monomial ideal, permitting an arbitrary exponent set. -/
def IsMonomialIdeal (I : Ideal (MvPolynomial V k)) : Prop :=
  ∃ A : Set (Exponent V), I = Ideal.span ((fun a => monomial a (1 : k)) '' A)

lemma monomialIdeal_isMonomial (B : Family V) : IsMonomialIdeal (monomialIdeal k B) :=
  ⟨(B : Set (Exponent V)), rfl⟩

/-- Arbitrary monomial spans have finite monomial generators. -/
lemma IsMonomialIdeal.exists_finite {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I) :
    ∃ B : Family V, I = monomialIdeal k B := by
  obtain ⟨A, rfl⟩ := hI
  let f : Exponent V → MvPolynomial V k := fun a => monomial a (1 : k)
  have hfg : (Ideal.span (f '' A)).FG := Ideal.fg_of_isNoetherianRing _
  obtain ⟨Q, hQA, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (f '' A)).mp hfg
  have hq : ∀ q : Q, ∃ a ∈ A, f a = q.val := fun q => hQA q.property
  let b : Q → Exponent V := fun q => (hq q).choose
  have hbA : ∀ q, b q ∈ A := fun q => (hq q).choose_spec.1
  have hbeq : ∀ q, f (b q) = q.val := fun q => (hq q).choose_spec.2
  let B : Family V := Finset.univ.image b
  refine ⟨B, ?_⟩
  have hset : f '' (B : Set (Exponent V)) = (Q : Set (MvPolynomial V k)) := by
    ext p
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
      rw [hbeq]
      exact q.property
    · intro hp
      refine ⟨b ⟨p, hp⟩, Finset.mem_image.mpr ⟨⟨p, hp⟩, mem_univ _, rfl⟩, hbeq _⟩
  change Ideal.span (f '' A) = Ideal.span (f '' (B : Set (Exponent V)))
  rw [hset]
  exact hspan

/-- Every monomial ideal has a finite antichain of actual monomial generators. -/
lemma IsMonomialIdeal.exists_antichain {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I) :
    ∃ B : Family V, Antichain B ∧ I = monomialIdeal k B := by
  obtain ⟨B, hB⟩ := hI.exists_finite
  exact ⟨minimalFamily B, minimalFamily_antichain B,
    hB.trans (monomialIdeal_minimalFamily k B).symm⟩

lemma antichain_generators_unique {B C : Family V} (hB : Antichain B) (hC : Antichain C)
    (hI : monomialIdeal k B = monomialIdeal k C) : B = C := by
  apply family_eq_of_contains_iff hB hC
  intro a
  rw [← monomial_mem_iff (k := k), ← monomial_mem_iff (k := k), hI]

/-- The unique finite family of minimal monomial exponents of a literal ideal. -/
def monomialGenerators (I : Ideal (MvPolynomial V k)) (hI : IsMonomialIdeal I) : Family V :=
  hI.exists_antichain.choose

lemma monomialGenerators_antichain (I : Ideal (MvPolynomial V k)) (hI : IsMonomialIdeal I) :
    Antichain (monomialGenerators I hI) := hI.exists_antichain.choose_spec.1

lemma monomialGenerators_ideal (I : Ideal (MvPolynomial V k)) (hI : IsMonomialIdeal I) :
    monomialIdeal k (monomialGenerators I hI) = I := hI.exists_antichain.choose_spec.2.symm

lemma monomialGenerators_eq {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    {B : Family V} (hB : Antichain B) (he : I = monomialIdeal k B) :
    monomialGenerators I hI = B :=
  antichain_generators_unique (monomialGenerators_antichain I hI) hB
    ((monomialGenerators_ideal I hI).trans he)

lemma monomialGenerators_nonempty {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    (hne : I ≠ ⊥) : (monomialGenerators I hI).Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  apply hne
  rw [← monomialGenerators_ideal I hI, he]
  simp [monomialIdeal]

/-- The chosen presentation is exactly the divisibility-minimal monomials in I. -/
lemma mem_monomialGenerators_iff (I : Ideal (MvPolynomial V k)) (hI : IsMonomialIdeal I)
    (a : Exponent V) :
    a ∈ monomialGenerators I hI ↔ monomial a (1 : k) ∈ I ∧
      ∀ b : Exponent V, b ≤ a → monomial b (1 : k) ∈ I → b = a := by
  have hanti := monomialGenerators_antichain I hI
  have hm : ∀ b : Exponent V, monomial b (1 : k) ∈ I ↔ Contains (monomialGenerators I hI) b := by
    intro b
    simpa only [monomialGenerators_ideal I hI] using
      (monomial_mem_iff (k := k) (monomialGenerators I hI) b)
  simp only [hm]
  constructor
  · intro ha
    refine ⟨⟨a, ha, le_rfl⟩, ?_⟩
    rintro b hba ⟨c, hc, hcb⟩
    have hca := hanti c hc a ha (hcb.trans hba)
    exact le_antisymm hba (hca ▸ hcb)
  · rintro ⟨⟨b, hb, hba⟩, hmin⟩
    have he := hmin b hba ⟨b, hb, le_rfl⟩
    exact he ▸ hb

lemma isPolymatroidalIdeal_iff_generators {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I) :
    IsPolymatroidalIdeal I ↔ IsPolymatroidal (monomialGenerators I hI) := by
  constructor
  · rintro ⟨B, hp, he⟩
    rw [monomialGenerators_eq hI hp.1.choose_spec.antichain he]
    exact hp
  · intro hp
    exact ⟨monomialGenerators I hI, hp, (monomialGenerators_ideal I hI).symm⟩

/-- Theorem 1.1(A), now quantified over an arbitrary literal monomial ideal, including zero. -/
theorem monomialIdeal_polymatroidal_iff_local_linear {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) :
    IsPolymatroidalIdeal I ↔
      ∀ U : Finset V, HasLinearResolution (monomialLocalization k I U) := by
  by_cases hzero : I = ⊥
  · subst I
    constructor
    · intro _ U
      rw [monomialLocalization, Ideal.map_bot]
      exact ⟨0, ⟨zeroLinearResolution 0⟩⟩
    · intro _
      exact isPolymatroidalIdeal_bot
  · rw [isPolymatroidalIdeal_iff_generators hI,
      polymatroidal_iff_local_linearResolutions (k := k) (monomialGenerators_nonempty hI hzero)
        (monomialGenerators_antichain I hI), monomialGenerators_ideal I hI]

/-- Theorem 1.1(B) / Corollary 3.10 on the actual minimal generators of an
arbitrary literal monomial ideal, without an equigeneration assumption. -/
theorem monomialIdeal_polymatroidal_iff_universal_quotients {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) :
    IsPolymatroidalIdeal I ↔ ∀ o : VariableOrder V,
      HasLinearQuotients k (monomialGenerators I hI) (variableRevlex o) := by
  rw [isPolymatroidalIdeal_iff_generators hI]
  exact polymatroidal_iff_universal_pure_revlex (monomialGenerators_antichain I hI)

/-- Theorem 2.11 / Corollary 2.12's integrality form for literal monomial ideals. -/
theorem monomialIdeal_polymatroidal_iff_integrallyClosed {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) (hne : I ≠ ⊥) :
    IsPolymatroidalIdeal I ↔ IsIntegrallyClosedIdeal I ∧
      ∀ U : Finset V, ∃ d, Equigenerated (localFamily (monomialGenerators I hI) U) d := by
  rw [isPolymatroidalIdeal_iff_generators hI,
    polymatroidal_iff_integrallyClosed_localEquigenerated (k := k) (monomialGenerators_nonempty hI hne)
      (monomialGenerators_antichain I hI), monomialGenerators_ideal I hI, locallyEquigenerated_iff]

/-- The complete integral-closure ideal in Theorem 2.11, for an arbitrary literal I. -/
theorem monomialIdeal_integralClosure {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) (hne : I ≠ ⊥)
    (hl : LocallyEquigenerated (monomialGenerators I hI)) {d : ℕ}
    (hd : Equigenerated (monomialGenerators I hI) d) :
    {f : MvPolynomial V k | IntegralOverIdeal I f} =
      (monomialIdeal k (lowerBaseFamily (lowerRank (monomialGenerators I hI)) d) : Set (MvPolynomial V k)) := by
  simpa only [monomialGenerators_ideal I hI] using integralClosure_set_eq
    (k := k) (monomialGenerators_nonempty hI hne) (monomialGenerators_antichain I hI) hl hd

end Characterizations

end
end CheckedCharacterizationsSource71

/-! ## Source: Characterizations.AllCases -/
section CheckedCharacterizationsSource72

/-! Theorem 4.5 and its universal testing predicates, including the zero ideal. -/
noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem empty_family_polymatroidal : IsPolymatroidal (∅ : Family V) := by
  refine ⟨⟨0,?_⟩,?_⟩
  · intro a ha; simp at ha
  · intro a ha; simp at ha

theorem polymatroidal_iff_localization_band_all {B : Family V}
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔ ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  by_cases hB : B.Nonempty
  · exact polymatroidal_iff_localization_band hB hd hd2
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    subst B
    exact ⟨fun hp U _ _ => polymatroidal_local_linearResolutions hp U,
      fun _ => empty_family_polymatroidal⟩

theorem polymatroidal_iff_pure_localization_band_all {B : Family V}
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) (hl : LocallyEquigenerated B) :
    IsPolymatroidal B ↔ ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-2 →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  by_cases hB : B.Nonempty
  · exact polymatroidal_iff_pure_localization_band hB hd hd2 hl
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    subst B
    exact ⟨fun hp U _ _ => polymatroidal_local_linearResolutions hp U,
      fun _ => empty_family_polymatroidal⟩

/-- Literal-ideal Theorem 4.5, with no nonzero hypothesis. The degree refers
to the actual minimal monomial generators characterized in MonomialNormalForm. -/
theorem monomialIdeal_polymatroidal_iff_localization_band
    {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    {d : ℕ} (hd : Equigenerated (monomialGenerators I hI) d) (hd2 : 2 ≤ d) :
    IsPolymatroidalIdeal I ↔ ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      HasLinearResolution (monomialLocalization k I U) := by
  rw [isPolymatroidalIdeal_iff_generators hI]
  simpa only [monomialGenerators_ideal] using
    (polymatroidal_iff_localization_band_all (k:=k) hd hd2)

theorem monomialIdeal_polymatroidal_iff_pure_localization_band
    {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    {d : ℕ} (hd : Equigenerated (monomialGenerators I hI) d) (hd2 : 2 ≤ d)
    (hl : LocallyEquigenerated (monomialGenerators I hI)) :
    IsPolymatroidalIdeal I ↔ ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-2 →
      HasLinearResolution (monomialLocalization k I U) := by
  rw [isPolymatroidalIdeal_iff_generators hI]
  simpa only [monomialGenerators_ideal] using
    (polymatroidal_iff_pure_localization_band_all (k:=k) hd hd2 hl)

namespace Isolators

def LocalizationTestSufficientAll (Γ : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ B : Family V, Equigenerated B d →
    (∀ U ∈ Γ, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) →
      IsPolymatroidal B

def PureLocalizationTestSufficientAll (Γ : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ B : Family V, Equigenerated B d → LocallyEquigenerated B →
    (∀ U ∈ Γ, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) →
      IsPolymatroidal B

def UnboundedLocalizationTestSufficientAll (Γ : Finset (Finset V)) : Prop :=
  ∀ B : Family V, Antichain B →
    (∀ U ∈ Γ, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) →
      IsPolymatroidal B

theorem localizationTestSufficientAll_iff (Γ : Finset (Finset V)) (d : ℕ) :
    LocalizationTestSufficientAll (k:=k) Γ d ↔ LocalizationTestSufficient (k:=k) Γ d := by
  constructor
  · intro h B _ hd ht; exact h B hd ht
  · intro h B hd ht
    by_cases hB : B.Nonempty
    · exact h B hB hd ht
    · simpa only [Finset.not_nonempty_iff_eq_empty.mp hB] using
        (empty_family_polymatroidal (V:=V))

theorem pureLocalizationTestSufficientAll_iff (Γ : Finset (Finset V)) (d : ℕ) :
    PureLocalizationTestSufficientAll (k:=k) Γ d ↔ PureLocalizationTestSufficient (k:=k) Γ d := by
  constructor
  · intro h B _ hd hl ht; exact h B hd hl ht
  · intro h B hd hl ht
    by_cases hB : B.Nonempty
    · exact h B hB hd hl ht
    · simpa only [Finset.not_nonempty_iff_eq_empty.mp hB] using
        (empty_family_polymatroidal (V:=V))

theorem unboundedLocalizationTestSufficientAll_iff (Γ : Finset (Finset V)) :
    UnboundedLocalizationTestSufficientAll (k:=k) Γ ↔ UnboundedLocalizationTestSufficient (k:=k) Γ := by
  constructor
  · intro h B _ ha ht; exact h B ha ht
  · intro h B ha ht
    by_cases hB : B.Nonempty
    · exact h B hB ha ht
    · simpa only [Finset.not_nonempty_iff_eq_empty.mp hB] using
        (empty_family_polymatroidal (V:=V))

theorem localizationTestSufficientAll_coverage (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d) :
    LocalizationTestSufficientAll (k:=k) Γ d ↔ localizationBand (V:=V) (d-1) ⊆ Γ :=
  (localizationTestSufficientAll_iff Γ d).trans (localizationTestSufficient_iff Γ d hd)

theorem pureLocalizationTestSufficientAll_coverage (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d) :
    PureLocalizationTestSufficientAll (k:=k) Γ d ↔ localizationBand (V:=V) (d-2) ⊆ Γ :=
  (pureLocalizationTestSufficientAll_iff Γ d).trans (pureLocalizationTestSufficient_iff Γ d hd)

end Isolators
end Characterizations

end
end CheckedCharacterizationsSource72

/-! ## Source: Characterizations.FiniteUniform -/
section CheckedCharacterizationsSource73

/-! # Exact finite uniform probabilities and equally sized fibers -/

noncomputable section
namespace Characterizations
open Classical Finset

variable {X Y : Type*} [Fintype X] [Fintype Y]

def finiteFraction (P : X → Prop) : ℝ := (Nat.card {x // P x} : ℝ) / Nat.card X

def preimageSigmaEquiv (f : X → Y) (P : Y → Prop) :
    {x // P (f x)} ≃ Σ y : {y // P y}, {x // f x = y.val} where
  toFun x := ⟨⟨f x.val,x.property⟩,⟨x.val,rfl⟩⟩
  invFun y := ⟨y.2.val, by rw [y.2.property]; exact y.1.property⟩
  left_inv _ := rfl
  right_inv y := by rcases y with ⟨⟨y,hy⟩,⟨x,hx⟩⟩; dsimp at hx; subst y; rfl

theorem card_preimage_of_constant_fiber (f : X → Y) (P : Y → Prop) (c : ℕ)
    (hc : ∀ y, Nat.card {x // f x = y} = c) :
    Nat.card {x // P (f x)} = Nat.card {y // P y} * c := by
  rw [Nat.card_congr (preimageSigmaEquiv f P), Nat.card_sigma]
  simp_rw [hc]
  simp [Nat.card_eq_fintype_card]

theorem fraction_preimage_of_constant_fiber [Nonempty X] (f : X → Y) (P : Y → Prop)
    (c : ℕ) (hc : ∀ y, Nat.card {x // f x = y} = c) :
    finiteFraction (fun x => P (f x)) = finiteFraction P := by
  have hX : Nat.card X = Nat.card Y * c := by
    simpa using card_preimage_of_constant_fiber f (fun _ => True) c hc
  have hcpos : 0 < c := by
    have hh : 0 < Nat.card X := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos
    nlinarith
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcpos)
  unfold finiteFraction
  rw [card_preimage_of_constant_fiber f P c hc, hX]
  push_cast
  rw [mul_div_mul_right _ _ hcR]

theorem variableOrder_eq_of_lt_iff {V : Type*} [Fintype V]
    (o₁ o₂ : VariableOrder V)
    (h : ∀ a b, o₁ a < o₁ b ↔ o₂ a < o₂ b) : o₁ = o₂ := by
  have hs : StrictMono (fun x => o₂ (o₁.symm x)) := by
    intro a b hab
    exact (h _ _).mp (by simpa using hab)
  apply Equiv.ext
  intro x
  have hh := hs.apply_eq (x := o₁ x)
  simpa using hh.symm

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem restrictedOrder_comp_subtype (T : Finset V) (o : VariableOrder V)
    (π : Equiv.Perm T) :
    restrictedOrder ((Equiv.Perm.ofSubtype π).trans o) (Function.Embedding.subtype (· ∈ T)) =
      π.trans (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) := by
  apply variableOrder_eq_of_lt_iff
  intro a b
  rw [restrictedOrder_lt_iff]
  simp only [Equiv.trans_apply, Function.Embedding.subtype_apply, Equiv.Perm.ofSubtype_apply_coe]
  exact (restrictedOrder_lt_iff o (Function.Embedding.subtype (· ∈ T)) (π a) (π b)).symm

def restrictionFiberEquiv (T : Finset V) (r₁ r₂ : VariableOrder T) :
    {o : VariableOrder V // restrictedOrder o (Function.Embedding.subtype (· ∈ T)) = r₁} ≃
    {o : VariableOrder V // restrictedOrder o (Function.Embedding.subtype (· ∈ T)) = r₂} := by
  let π := r₂.trans r₁.symm
  let σ : Equiv.Perm V := Equiv.Perm.ofSubtype π
  refine {
    toFun := fun o => ⟨σ.trans o.val, ?_⟩
    invFun := fun o => ⟨σ.symm.trans o.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [restrictedOrder_comp_subtype, o.property]
    ext a
    simp [π]
  · have hσ : σ.symm = Equiv.Perm.ofSubtype π.symm :=
      (map_inv (Equiv.Perm.ofSubtype) π).symm
    rw [hσ, restrictedOrder_comp_subtype, o.property]
    ext a
    simp [π]
  · intro o
    apply Subtype.ext
    ext a
    simp
  · intro o
    apply Subtype.ext
    ext a
    simp

theorem restriction_uniform (T : Finset V) (P : VariableOrder T → Prop) :
    finiteFraction (fun o : VariableOrder V => P (restrictedOrder o (Function.Embedding.subtype (· ∈ T)))) =
      finiteFraction P := by
  classical
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  let r₀ : VariableOrder T := Fintype.equivFin T
  let c := Nat.card {o : VariableOrder V //
    restrictedOrder o (Function.Embedding.subtype (· ∈ T)) = r₀}
  apply fraction_preimage_of_constant_fiber _ P c
  intro r
  exact Nat.card_congr (restrictionFiberEquiv T r r₀)

end Characterizations

end
end CheckedCharacterizationsSource73

/-! ## Source: Characterizations.PointUniformity -/
section CheckedCharacterizationsSource74

/-! # Uniform distribution of pointed final triples -/

noncomputable section
namespace Characterizations
open Classical Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def PointedTriple.map (σ : Equiv.Perm V) (P : PointedTriple V) : PointedTriple V :=
  ⟨σ P.1, ⟨P.2.val.map σ.toEmbedding, by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    exact mem_erase.mpr ⟨fun he => (mem_erase.mp (P.2.property.1 hy)).1 (σ.injective he), mem_univ _⟩,
    by simpa using P.2.property.2⟩⟩

theorem CoversPoint.map {o : VariableOrder V} {P : PointedTriple V}
    (h : CoversPoint o P) (σ : Equiv.Perm V) :
    CoversPoint (σ.symm.trans o) (P.map σ) := by
  obtain ⟨i,q,hiq,hA,hf⟩ := h
  refine ⟨σ i,σ q,fun he => hiq (σ.injective he),?_,?_,?_,?_⟩
  · simp [PointedTriple.map,hA]
  · simpa [PointedTriple.map] using hf.1
  · simpa [PointedTriple.map] using hf.2.1
  · intro x hxi hxq hxj
    have hxi' : σ.symm x ≠ i := fun he => hxi (by simpa using congrArg σ he)
    have hxq' : σ.symm x ≠ q := fun he => hxq (by simpa using congrArg σ he)
    have hxj' : σ.symm x ≠ P.1 := fun he => hxj (by simpa [PointedTriple.map] using congrArg σ he)
    simpa using hf.2.2 (σ.symm x) hxi' hxq' hxj'

theorem exists_order_covering_point (P : PointedTriple V) :
    ∃ o : VariableOrder V, CoversPoint o P := by
  obtain ⟨i,q,hiq,hA⟩ := card_eq_two.mp P.2.property.2
  have hij : i ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  have hqj : q ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  obtain ⟨o,ho⟩ := exists_finalTriple i q P.1 hiq hij hqj
  exact ⟨o,i,q,hiq,hA,ho⟩

def pointFiberEquiv (P Q : PointedTriple V) :
    {o : VariableOrder V // CoversPoint o P} ≃ {o : VariableOrder V // CoversPoint o Q} := by
  let oP := (exists_order_covering_point P).choose
  have hP : CoversPoint oP P := (exists_order_covering_point P).choose_spec
  let oQ := (exists_order_covering_point Q).choose
  have hQ : CoversPoint oQ Q := (exists_order_covering_point Q).choose_spec
  let σ : Equiv.Perm V := oP.trans oQ.symm
  have hmap : P.map σ = Q := by
    apply coversPoint_unique _ hQ
    have hh := hP.map σ
    have he : σ.symm.trans oP = oQ := by ext x; simp [σ]
    simpa only [he] using hh
  have hmapinv : Q.map σ.symm = P := by
    apply coversPoint_unique _ hP
    have hh := hQ.map σ.symm
    have he : σ.trans oQ = oP := by ext x; simp [σ]
    simpa only [Equiv.symm_symm,he] using hh
  refine {
    toFun := fun o => ⟨σ.symm.trans o.val, hmap ▸ o.property.map σ⟩
    invFun := fun o => ⟨σ.trans o.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · simpa only [Equiv.symm_symm] using (hmapinv ▸ o.property.map σ.symm)
  · intro o; apply Subtype.ext; ext x; simp
  · intro o; apply Subtype.ext; ext x; simp

theorem exists_point_covered (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) :
    ∃ P : PointedTriple V, CoversPoint o P := by
  let i := o.symm ⟨Fintype.card V-3,by omega⟩
  let q := o.symm ⟨Fintype.card V-2,by omega⟩
  let j := o.symm ⟨Fintype.card V-1,by omega⟩
  have hi : (o i).val = Fintype.card V-3 := by simp [i]
  have hq : (o q).val = Fintype.card V-2 := by simp [q]
  have hj : (o j).val = Fintype.card V-1 := by simp [j]
  have hiq : i ≠ q := by intro he; rw [he] at hi; omega
  have hij : i ≠ j := by intro he; rw [he] at hi; omega
  have hqj : q ≠ j := by intro he; rw [he] at hq; omega
  let P : PointedTriple V := ⟨j,⟨{i,q},by simp [insert_subset_iff,hij,hqj],by simp [hiq]⟩⟩
  refine ⟨P,i,q,hiq,rfl,?_,?_,?_⟩
  · change (o i).val < (o j).val
    omega
  · change (o q).val < (o j).val
    omega
  · intro x hxi hxq hxj
    have hn1 : (o x).val ≠ (o i).val := fun he => hxi (o.injective (Fin.ext he))
    have hn2 : (o x).val ≠ (o q).val := fun he => hxq (o.injective (Fin.ext he))
    have hn3 : (o x).val ≠ (o j).val := fun he => hxj (o.injective (Fin.ext he))
    have hxlt := (o x).isLt
    change (o x).val < (o i).val ∧ (o x).val < (o q).val
    omega

def finalPoint (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) : PointedTriple V :=
  (exists_point_covered hcard o).choose

theorem finalPoint_spec (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) :
    CoversPoint o (finalPoint hcard o) := (exists_point_covered hcard o).choose_spec

theorem finalPoint_eq_iff (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) (P : PointedTriple V) :
    finalPoint hcard o = P ↔ CoversPoint o P :=
  ⟨fun h => h ▸ finalPoint_spec hcard o, fun h => coversPoint_unique (finalPoint_spec hcard o) h⟩

theorem pointedTriple_probability (hcard : 3 ≤ Fintype.card V) (P : PointedTriple V) :
    finiteFraction (fun o : VariableOrder V => CoversPoint o P) =
      1 / (Fintype.card V * (Fintype.card V - 1).choose 2 : ℕ) := by
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  let c := Nat.card {o : VariableOrder V // CoversPoint o P}
  have hc (Q : PointedTriple V) : Nat.card {o : VariableOrder V // finalPoint hcard o = Q} = c := by
    calc
      _ = Nat.card {o : VariableOrder V // CoversPoint o Q} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun o => finalPoint_eq_iff hcard o Q))
      _ = c := Nat.card_congr (pointFiberEquiv Q P)
  have hh := fraction_preimage_of_constant_fiber (finalPoint hcard) (fun Q => Q = P) c hc
  have he : (fun o : VariableOrder V => finalPoint hcard o = P) = (fun o => CoversPoint o P) :=
    funext (fun o => propext (finalPoint_eq_iff hcard o P))
  rw [he] at hh
  simpa [finiteFraction,Nat.card_eq_fintype_card,card_pointedTriple] using hh

end Characterizations

end
end CheckedCharacterizationsSource74

/-! ## Source: Characterizations.PatternProbability -/
section CheckedCharacterizationsSource75

/-! # The exact rejection mass of an active order pattern -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Characterizations
open Classical Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem finiteFraction_congr {X : Type*} [Fintype X] {P Q : X → Prop}
    (h : ∀ x, P x ↔ Q x) : finiteFraction P = finiteFraction Q :=
  congrArg finiteFraction (funext (fun x => propext (h x)))

theorem finiteFraction_mono {X : Type*} [Fintype X] {P Q : X → Prop}
    (h : ∀ x, P x → Q x) : finiteFraction P ≤ finiteFraction Q := by
  have hc : Nat.card {x // P x} ≤ Nat.card {x // Q x} :=
    Nat.card_le_card_of_injective (fun x => (⟨x.val,h x.val x.property⟩ : {x // Q x}))
      (fun _ _ he => Subtype.ext (congrArg (fun z : {x // Q x} => z.val) he))
  unfold finiteFraction
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)

theorem finiteFraction_true {X : Type*} [Fintype X] [Nonempty X] :
    finiteFraction (fun _ : X => True) = 1 := by
  unfold finiteFraction
  simp [Nat.card_eq_fintype_card,Fintype.card_pos.ne']

theorem finiteFraction_le_one {X : Type*} [Fintype X] [Nonempty X] (P : X → Prop) :
    finiteFraction P ≤ 1 := by
  rw [← finiteFraction_true (X := X)]
  exact finiteFraction_mono (fun _ _ => trivial)

theorem coversPoint_pair_iff {o : VariableOrder V} {i q j : V}
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) :
    CoversPoint o (⟨j,⟨{i,q},by simp [insert_subset_iff,hij,hqj],by simp [hiq]⟩⟩ : PointedTriple V) ↔
      FinalTriple o i q j := by
  constructor
  · rintro ⟨a,b,hab,hA,hf⟩
    exact hf.of_pair_eq hiq hab hA
  · intro hf
    exact ⟨i,q,hiq,rfl,hf⟩

theorem restricted_finalTriple_iff (T : Finset V) (o : VariableOrder V) (i q j : T) :
    FinalTriple (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) i q j ↔
      OrderPattern o (T \ {i.val,q.val,j.val}) i.val q.val j.val := by
  simp only [FinalTriple,OrderPattern,restrictedOrder_lt_iff]
  constructor
  · rintro ⟨hi,hq,hr⟩
    refine ⟨hi,hq,?_⟩
    intro x hx
    obtain ⟨hxT,hxn⟩ := mem_sdiff.mp hx
    have hxi : x ≠ i.val := fun he => hxn (by simp [he])
    have hxq : x ≠ q.val := fun he => hxn (by simp [he])
    have hxj : x ≠ j.val := fun he => hxn (by simp [he])
    exact hr ⟨x,hxT⟩ (fun he => hxi (congrArg Subtype.val he))
      (fun he => hxq (congrArg Subtype.val he)) (fun he => hxj (congrArg Subtype.val he))
  · rintro ⟨hi,hq,hr⟩
    refine ⟨hi,hq,?_⟩
    intro x hxi hxq hxj
    apply hr x.val
    exact mem_sdiff.mpr ⟨x.property,by
      simp only [mem_insert,mem_singleton,not_or]
      exact ⟨fun he => hxi (Subtype.ext he),fun he => hxq (Subtype.ext he),fun he => hxj (Subtype.ext he)⟩⟩

theorem restricted_point_probability (T : Finset V) (hT : 3 ≤ T.card) (P : PointedTriple T) :
    finiteFraction (fun o : VariableOrder V => CoversPoint
      (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) P) =
      1 / (T.card * (T.card-1).choose 2 : ℕ) := by
  calc
    _ = finiteFraction (fun r : VariableOrder T => CoversPoint r P) := restriction_uniform T _
    _ = _ := by
      have hh := pointedTriple_probability (V := T) (by simpa using hT) P
      simpa only [Fintype.card_coe] using hh

theorem orderPattern_probability (C : Finset V) (i q j : V)
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) (hC : C ⊆ tripleCap i q j) :
    finiteFraction (fun o : VariableOrder V => OrderPattern o C i q j) =
      1 / ((C.card+3) * (C.card+2).choose 2 : ℕ) := by
  let T := patternActive C i q j
  let I : T := ⟨i,by simp [T,patternActive]⟩
  let Q : T := ⟨q,by simp [T,patternActive]⟩
  let J : T := ⟨j,by simp [T,patternActive]⟩
  have hIQ : I ≠ Q := fun he => hiq (congrArg Subtype.val he)
  have hIJ : I ≠ J := fun he => hij (congrArg Subtype.val he)
  have hQJ : Q ≠ J := fun he => hqj (congrArg Subtype.val he)
  let P : PointedTriple T := ⟨J,⟨{I,Q},by simp [insert_subset_iff,hIJ,hQJ],by simp [hIQ]⟩⟩
  have hTC : T \ {i,q,j} = C := by
    ext x
    have hiC : i ∉ C := fun h => by simpa using hC h
    have hqC : q ∉ C := fun h => by simpa using hC h
    have hjC : j ∉ C := fun h => by simpa using hC h
    by_cases hxi : x = i <;> by_cases hxq : x = q <;> by_cases hxj : x = j <;>
      simp [T,patternActive,hxi,hxq,hxj,hiC,hqC,hjC]
  have he (o : VariableOrder V) :
      CoversPoint (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) P ↔ OrderPattern o C i q j := by
    rw [coversPoint_pair_iff hIQ hIJ hQJ, restricted_finalTriple_iff]
    simpa only [I,Q,J,hTC]
  have hcard : Fintype.card T = C.card+3 := by
    rw [Fintype.card_coe]
    exact patternActive_card hiq hij hqj hC
  calc
    _ = finiteFraction (fun o : VariableOrder V => CoversPoint
        (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) P) := finiteFraction_congr (fun o => (he o).symm)
    _ = _ := by
      have hTc : T.card = C.card+3 := by simpa only [Fintype.card_coe] using hcard
      rw [restricted_point_probability T (by omega) P,hTc]
      simp

/-- The fraction in the paper's displayed rational form. -/
theorem orderPattern_probability_formula (C : Finset V) (i q j : V)
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) (hC : C ⊆ tripleCap i q j) :
    finiteFraction (fun o : VariableOrder V => OrderPattern o C i q j) =
      2 / (((C.card:ℝ)+1) * ((C.card:ℝ)+2) * ((C.card:ℝ)+3)) := by
  rw [orderPattern_probability C i q j hiq hij hqj hC]
  have hn := Nat.add_one_mul_choose_eq (C.card+1) 1
  have hn' : ((C.card+2).choose 2 : ℝ)*2 = ((C.card:ℝ)+1)*((C.card:ℝ)+2) := by
    have hh : (C.card+2).choose 2 * 2 = (C.card+1)*(C.card+2) := by simpa [mul_comm] using hn.symm
    exact_mod_cast hh
  have hpos : (0:ℝ) < (C.card+2).choose 2 := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ C.card+2))
  push_cast
  field_simp
  nlinarith

end Characterizations

end
end CheckedCharacterizationsSource75

/-! ## Source: Characterizations.FiniteCover -/
section CheckedCharacterizationsSource76

/-! # A kernel-checked probabilistic covering bound for finite tests -/

noncomputable section
namespace Characterizations
open Classical Finset
variable {X I : Type*} [Fintype X] [Fintype I]

theorem finiteFraction_not [Nonempty X] (P : X → Prop) :
    finiteFraction (fun x => ¬P x) = 1 - finiteFraction P := by
  classical
  have hle := Fintype.card_subtype_le P
  have hpos : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  unfold finiteFraction
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  rw [Nat.cast_sub hle]
  field_simp

theorem finiteFraction_exists_le_sum (R : I → X → Prop) :
    finiteFraction (fun x => ∃ i,R i x) ≤ ∑ i, finiteFraction (R i) := by
  classical
  let f : {x // ∃ i,R i x} → Σ i : I, {x // R i x} :=
    fun x => ⟨x.property.choose,⟨x.val,x.property.choose_spec⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : Σ i : I, {x // R i x} => z.2.val) he)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sigma] at hc
  unfold finiteFraction
  rw [← sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hc

def allTrialEquiv (M : ℕ) (P : X → Prop) :
    {f : Fin M → X // ∀ j,P (f j)} ≃ (Fin M → {x // P x}) where
  toFun f j := ⟨f.val j,f.property j⟩
  invFun f := ⟨fun j => (f j).val,fun j => (f j).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finiteFraction_all_trials (M : ℕ) (P : X → Prop) :
    finiteFraction (fun f : Fin M → X => ∀ j,P (f j)) = (finiteFraction P)^M := by
  unfold finiteFraction
  rw [Nat.card_congr (allTrialEquiv M P),Nat.card_fun,Nat.card_fun]
  simp only [Nat.card_fin,Nat.cast_pow,div_pow]

theorem finiteFraction_nonneg (P : X → Prop) : 0 ≤ finiteFraction P := by
  unfold finiteFraction
  positivity

theorem exists_outside_of_fraction_lt_one [Nonempty X] (P : X → Prop)
    (h : finiteFraction P < 1) : ∃ x, ¬P x := by
  by_contra hn
  have hP : ∀ x,P x := by simpa using hn
  have he : finiteFraction P = 1 := by
    rw [finiteFraction_congr (fun x => iff_true_intro (hP x)),finiteFraction_true]
  linarith

/-- Independent draws miss at most the sum of the exact individual missing
probabilities. This is a finite counting proof of the union bound. -/
theorem independent_miss_fraction_bound [Nonempty X] (R : I → X → Prop)
    (p : ℝ) (hp : 0 ≤ p) (hR : ∀ i, finiteFraction (R i) = p) (M : ℕ) :
    finiteFraction (fun f : Fin M → X => ∃ i,∀ j,¬R i (f j)) ≤
      (Fintype.card I : ℝ) * Real.exp (-p * M) := by
  have hsum := finiteFraction_exists_le_sum (fun i (f : Fin M → X) => ∀ j,¬R i (f j))
  have hsingle (i : I) : finiteFraction (fun f : Fin M → X => ∀ j,¬R i (f j)) = (1-p)^M := by
    rw [finiteFraction_all_trials M (fun x => ¬R i x),finiteFraction_not (R i),hR i]
  simp only [hsingle,sum_const,card_univ,nsmul_eq_mul] at hsum
  apply hsum.trans
  by_cases hI : Nonempty I
  · letI := hI
    have hple : p ≤ 1 := by
      obtain ⟨i⟩ := hI
      simpa [hR i] using finiteFraction_le_one (R i)
    have hexp : 1-p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
    have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1-p) hexp M
    have he : Real.exp (-p)^M = Real.exp (-p * M) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he] at hpow
    exact mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
  · haveI : IsEmpty I := not_nonempty_iff.mp hI
    simp

/-- A finite family meeting all tests, with the exact logarithmic size bound. -/
theorem finite_probabilistic_cover [Nonempty X] [Nonempty I]
    (R : I → X → Prop) (p : ℝ) (hp : 0 < p)
    (hR : ∀ i, finiteFraction (R i) = p) :
    ∃ F : Finset X, F.card ≤ ⌈p⁻¹ * (Real.log (Fintype.card I) + 1)⌉₊ ∧
      ∀ i, ∃ x ∈ F,R i x := by
  classical
  let M : ℕ := ⌈p⁻¹ * (Real.log (Fintype.card I) + 1)⌉₊
  have hM : p⁻¹ * (Real.log (Fintype.card I) + 1) ≤ (M : ℝ) := Nat.le_ceil _
  have hQ : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hpM : Real.log (Fintype.card I) + 1 ≤ p * M := by
    have hh := mul_le_mul_of_nonneg_left hM hp.le
    simpa [← mul_assoc,mul_inv_cancel₀ hp.ne'] using hh
  have hbound : (Fintype.card I : ℝ) * Real.exp (-p*M) < 1 := by
    calc
      _ = Real.exp (Real.log (Fintype.card I) - p*M) := by
        rw [Real.exp_sub,Real.exp_log hQ]
        simp [Real.exp_neg,div_eq_mul_inv]
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ < 1 := by simpa using (Real.exp_lt_exp.mpr (show (-1:ℝ)<0 by norm_num))
  obtain ⟨f,hf⟩ := exists_outside_of_fraction_lt_one
    (fun f : Fin M → X => ∃ i,∀ j,¬R i (f j))
    ((independent_miss_fraction_bound R p hp.le hR M).trans_lt hbound)
  refine ⟨univ.image f,?_,?_⟩
  · exact (card_image_le).trans (by simp [M])
  · intro i
    have hi : ∃ j,R i (f j) := by
      by_contra hn
      exact hf ⟨i,by simpa using hn⟩
    obtain ⟨j,hj⟩ := hi
    exact ⟨f j,mem_image.mpr ⟨j,mem_univ _,rfl⟩,hj⟩

end Characterizations

end
end CheckedCharacterizationsSource76

/-! ## Source: Characterizations.PatternSpace -/
section CheckedCharacterizationsSource77

/-! # The finite space of all required degree-sensitive patterns -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Characterizations
open Classical Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev DegreePattern (V : Type*) [Fintype V] [DecidableEq V] (s : ℕ) :=
  Σ T : {T : Finset V // T.card = s+3}, PointedTriple T.val

def RealizesPattern {s : ℕ} (o : VariableOrder V) (P : DegreePattern V s) : Prop :=
  CoversPoint (restrictedOrder o (Function.Embedding.subtype (· ∈ P.1.val))) P.2

theorem card_degreePattern (s : ℕ) : Nat.card (DegreePattern V s) =
    (Fintype.card V).choose (s+3) * ((s+3)*(s+2).choose 2) := by
  change Nat.card (Σ T : {T : Finset V // T.card = s+3}, PointedTriple T.val) = _
  rw [Nat.card_sigma]
  have hP (T : {T : Finset V // T.card = s+3}) :
      Nat.card (PointedTriple T.val) = (s+3)*(s+2).choose 2 := by
    rw [Nat.card_eq_fintype_card,card_pointedTriple,Fintype.card_coe,T.property]
    simp
  simp_rw [hP]
  simp [Fintype.card_finset_len]

theorem pointedTriple_count_formula (n : ℕ) (hn : 1 ≤ n) :
    n*(n-1).choose 2 = 3*n.choose 3 := by
  have hh := Nat.add_one_mul_choose_eq (n-1) 2
  have he : n-1+1 = n := by omega
  simpa [he,mul_comm] using hh

theorem card_degreePattern_paper (s : ℕ) (hn : 1 ≤ Fintype.card V) :
    Nat.card (DegreePattern V s) =
      Fintype.card V * (Fintype.card V-1).choose 2 * (Fintype.card V-3).choose s := by
  have hsmall : (s+3)*(s+2).choose 2 = 3*(s+3).choose 3 := by
    simpa using pointedTriple_count_formula (s+3) (by omega)
  rw [card_degreePattern,hsmall,pointedTriple_count_formula (Fintype.card V) hn]
  have hh := Nat.choose_mul (n := Fintype.card V) (k := s+3) (s := 3) (by omega)
  have he : s+3-3 = s := by omega
  rw [he] at hh
  nlinarith

theorem degreePattern_nonempty (s : ℕ) (hs : s+3 ≤ Fintype.card V) :
    Nonempty (DegreePattern V s) := by
  obtain ⟨T,hTsub,hTc⟩ := exists_subset_card_eq (show s+3 ≤ (univ : Finset V).card by simpa using hs)
  have hcard : 3 ≤ Fintype.card T := by rw [Fintype.card_coe,hTc]; omega
  obtain ⟨i,q,j,hiq,hij,hqj⟩ := exists_three_distinct hcard
  exact ⟨⟨⟨T,hTc⟩,⟨j,⟨{i,q},by simp [insert_subset_iff,hij,hqj],by simp [hiq]⟩⟩⟩⟩

theorem realizesPattern_probability {s : ℕ} (P : DegreePattern V s) :
    finiteFraction (fun o : VariableOrder V => RealizesPattern o P) =
      1 / ((s+3)*(s+2).choose 2 : ℕ) := by
  change finiteFraction (fun o : VariableOrder V => CoversPoint
    (restrictedOrder o (Function.Embedding.subtype (· ∈ P.1.val))) P.2) = _
  have hh := restricted_point_probability P.1.val (by rw [P.1.property]; omega) P.2
  simpa only [P.1.property,show s+3-1=s+2 by omega] using hh

theorem coversPatterns_iff_degreePattern {s : ℕ} (F : Set (VariableOrder V)) :
    CoversPatterns s F ↔ ∀ P : DegreePattern V s, ∃ o ∈ F,RealizesPattern o P := by
  constructor
  · intro hF P
    obtain ⟨i,q,hiq,hA⟩ := card_eq_two.mp P.2.2.property.2
    let j := P.2.1
    have hij : i ≠ j := (mem_erase.mp (P.2.2.property.1 (by simp [hA]))).1
    have hqj : q ≠ j := (mem_erase.mp (P.2.2.property.1 (by simp [hA]))).1
    have hiq' : i.val ≠ q.val := fun he => hiq (Subtype.ext he)
    have hij' : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    have hqj' : q.val ≠ j.val := fun he => hqj (Subtype.ext he)
    let C := P.1.val \ {i.val,q.val,j.val}
    have hCcap : C ⊆ tripleCap i.val q.val j.val := by
      intro x hx
      have hh := (mem_sdiff.mp hx).2
      simpa [tripleCap] using hh
    have hCcard : C.card = s := by
      have hsubset : ({i.val,q.val,j.val} : Finset V) ⊆ P.1.val := by
        simp [insert_subset_iff,i.property,q.property,j.property]
      dsimp only [C]
      rw [card_sdiff_of_subset hsubset,P.1.property]
      simp [hiq',hij',hqj']
    obtain ⟨o,ho,hp⟩ := hF i.val q.val j.val hiq' hij' hqj' C hCcap hCcard
    refine ⟨o,ho,i,q,hiq,hA,?_⟩
    exact (restricted_finalTriple_iff P.1.val o i q j).mpr hp
  · intro hF i q j hiq hij hqj C hC hCc
    let T := patternActive C i q j
    have hTc : T.card = s+3 := by rw [patternActive_card hiq hij hqj hC,hCc]
    let I : T := ⟨i,by simp [T,patternActive]⟩
    let Q : T := ⟨q,by simp [T,patternActive]⟩
    let J : T := ⟨j,by simp [T,patternActive]⟩
    have hIQ : I ≠ Q := fun he => hiq (congrArg Subtype.val he)
    have hIJ : I ≠ J := fun he => hij (congrArg Subtype.val he)
    have hQJ : Q ≠ J := fun he => hqj (congrArg Subtype.val he)
    let P : DegreePattern V s := ⟨⟨T,hTc⟩,⟨J,⟨{I,Q},
      by simp [insert_subset_iff,hIJ,hQJ],by simp [hIQ]⟩⟩⟩
    obtain ⟨o,ho,hp⟩ := hF P
    have hf : FinalTriple (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) I Q J :=
      (coversPoint_pair_iff hIQ hIJ hQJ).mp hp
    have hpat := (restricted_finalTriple_iff T o I Q J).mp hf
    have hTC : T \ {i,q,j} = C := by
      ext x
      have hiC : i ∉ C := fun h => by simpa using hC h
      have hqC : q ∉ C := fun h => by simpa using hC h
      have hjC : j ∉ C := fun h => by simpa using hC h
      by_cases hxi : x = i <;> by_cases hxq : x = q <;> by_cases hxj : x = j <;>
        simp [T,patternActive,hxi,hxq,hxj,hiC,hqC,hjC]
    exact ⟨o,ho,by simpa only [I,Q,J,hTC] using hpat⟩

end Characterizations

end
end CheckedCharacterizationsSource77

/-! ## Source: Characterizations.SignatureBound -/
section CheckedCharacterizationsSource78

/-! # The sharp Boolean-antichain constraint on any degree-sensitive test family -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem relative_triples_of_patterns {s : ℕ} {F : Set (VariableOrder V)}
    (hcard : 4 ≤ Fintype.card V) (hs : 1 ≤ s) (hsn : s ≤ Fintype.card V - 3)
    (hF : CoversPatterns s F) (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ o ∈ F, o x < o y ∧ o y < o z := by
  have hthree : ({x,y,z} : Finset V).card = 3 := by simp [hxy,hxz,hyz]
  obtain ⟨q, _, hq⟩ := exists_mem_notMem_of_card_lt_card
    (show ({x,y,z} : Finset V).card < (univ : Finset V).card by simp; omega)
  have hqx : q ≠ x := fun h => hq (by simp [h])
  have hqy : q ≠ y := fun h => hq (by simp [h])
  have hqz : q ≠ z := fun h => hq (by simp [h])
  have hxcap : x ∈ tripleCap y q z := (mem_tripleCap _ _ _ _).mpr ⟨hxy,hqx.symm,hxz⟩
  have hcapcard : (tripleCap y q z).card = Fintype.card V - 3 := by
    rw [tripleCap, card_sdiff_of_subset (subset_univ _)]
    simp [hqy.symm, hyz, hqz]
  obtain ⟨C,hxC,hCcap,hCc⟩ := exists_subsuperset_card_eq (singleton_subset_iff.mpr hxcap)
    (show ({x} : Finset V).card ≤ s by simpa using hs)
    (show s ≤ (tripleCap y q z).card by omega)
  obtain ⟨o,ho,hp⟩ := hF y q z hqy.symm hyz hqz C hCcap hCc
  exact ⟨o,ho,(hp.2.2 x (hxC (by simp))).1,hp.1⟩

/-- Corollary 5.5, inequality (5.3), for every finite family satisfying the
full degree-sensitive test criterion. -/
theorem pattern_signature_bound {s : ℕ} (F : Finset (VariableOrder V))
    (hcard : 4 ≤ Fintype.card V) (hs : 1 ≤ s) (hsn : s ≤ Fintype.card V - 3)
    (hF : CoversPatterns s (F : Set (VariableOrder V))) :
    Fintype.card V - 1 ≤ F.card.choose (F.card / 2) := by
  obtain ⟨x,y,hxy⟩ := exists_distinct_of_card_two (V := V) (by omega)
  let signature (x : Except y) : Finset F := univ.filter (fun o => o.val x.val < o.val y)
  have hnot (x z : Except y) (hxz : x ≠ z) : ¬ signature x ⊆ signature z := by
    intro hsub
    obtain ⟨o,ho,hxyO,hyzO⟩ := relative_triples_of_patterns hcard hs hsn hF x.val y z.val
      x.property (fun he => hxz (Subtype.ext he)) z.property.symm
    have hxmem : (⟨o,ho⟩ : F) ∈ signature x := by simp [signature,hxyO]
    have hzmem := hsub hxmem
    have hzyO : o z.val < o y := by simpa [signature] using hzmem
    exact (lt_irrefl _ (hyzO.trans hzyO))
  have hinj : Function.Injective signature := by
    intro x z he
    by_contra hn
    exact hnot x z hn (by rw [he])
  let A : Finset (Finset F) := univ.image signature
  have hA : IsAntichain (· ⊆ ·) (A : Set (Finset F)) := by
    intro a ha b hb hab hsub
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hb
    have hxz : x ≠ z := fun he => hab (congrArg signature he)
    exact hnot x z hxz hsub
  have hAc : A.card = Fintype.card V - 1 := by
    dsimp only [A]
    rw [card_image_of_injective _ hinj, card_univ, card_except]
  have hh := hA.sperner
  simpa [hAc] using hh

theorem degree_test_signature_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V)
    (F : Finset (VariableOrder V)) (hF : DegreeOrderTests k d (F : Set (VariableOrder V))) :
    Fintype.card V - 1 ≤ F.card.choose (F.card / 2) := by
  exact pattern_signature_bound F hcard (by omega) (Nat.min_le_right _ _)
    ((degreeOrderTests_iff_coverage d hd hcard _).mp hF).1

end Characterizations

end
end CheckedCharacterizationsSource78

/-! ## Source: Characterizations.SmallTestNumbers -/
section CheckedCharacterizationsSource79

/-! # The exact zero-, one-, and six-test small cases -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem variableOrder_card : Fintype.card (VariableOrder V) = (Fintype.card V).factorial :=
  Fintype.card_equiv (Fintype.equivFin V)

theorem finalPair_card_three_values (hcard : Fintype.card V = 3)
    {o : VariableOrder V} {i j : V} (hij : i ≠ j) (h : FinalPair o i j) :
    (o i).val = 1 ∧ (o j).val = 2 ∧ ∀ x, x ≠ i → x ≠ j → (o x).val = 0 := by
  obtain ⟨q,_,hq⟩ := exists_mem_notMem_of_card_lt_card
    (show ({i,j} : Finset V).card < (univ : Finset V).card by simp [hij,hcard])
  have hqi : q ≠ i := fun he => hq (by simp [he])
  have hqj : q ≠ j := fun he => hq (by simp [he])
  have hlt1 := h.1
  have hlt0 := h.2 q hqi hqj
  have hiBound := (o i).isLt
  have hjBound := (o j).isLt
  have hqBound := (o q).isLt
  change (o i).val < (o j).val at hlt1
  change (o q).val < (o i).val at hlt0
  refine ⟨by omega, by omega, ?_⟩
  intro x hxi hxj
  have hh := h.2 x hxi hxj
  change (o x).val < (o i).val at hh
  omega

theorem finalPair_unique_card_three (hcard : Fintype.card V = 3)
    {o o' : VariableOrder V} {i j : V} (hij : i ≠ j)
    (h : FinalPair o i j) (h' : FinalPair o' i j) : o = o' := by
  obtain ⟨hi,hj,hrest⟩ := finalPair_card_three_values hcard hij h
  obtain ⟨hi',hj',hrest'⟩ := finalPair_card_three_values hcard hij h'
  ext x
  by_cases hxi : x = i
  · subst x; omega
  by_cases hxj : x = j
  · subst x; omega
  rw [hrest x hxi hxj,hrest' x hxi hxj]

theorem order_has_finalPair_card_three (hcard : Fintype.card V = 3) (o : VariableOrder V) :
    ∃ i j : V, i ≠ j ∧ FinalPair o i j := by
  let i := o.symm ⟨1,by omega⟩
  let j := o.symm ⟨2,by omega⟩
  have hi : (o i).val = 1 := by simp [i]
  have hj : (o j).val = 2 := by simp [j]
  have hij : i ≠ j := by intro he; rw [he] at hi; omega
  refine ⟨i,j,hij,?_,?_⟩
  · change (o i).val < (o j).val
    omega
  · intro x hxi hxj
    have hni : (o x).val ≠ 1 := fun he => hxi (o.injective (Fin.ext (he.trans hi.symm)))
    have hnj : (o x).val ≠ 2 := fun he => hxj (o.injective (Fin.ext (he.trans hj.symm)))
    have hb := (o x).isLt
    change (o x).val < (o i).val
    omega

theorem degree_tests_card_three_iff_univ {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 3) (d : ℕ) (hd : 2 ≤ d) (F : Finset (VariableOrder V)) :
    DegreeOrderTests k d (F : Set (VariableOrder V)) ↔ F = univ := by
  constructor
  · intro htest
    apply eq_univ_of_forall
    intro o
    by_contra hn
    obtain ⟨i,j,hij,hfinal⟩ := order_has_finalPair_card_three hcard o
    let c : Exponent V := Finsupp.single i (d-2)
    have hbase : Equigenerated (pairFamily i j) 2 := by simpa [hcard] using pairFamily_equigenerated i j
    have hcdeg : c.degree = d-2 := by simp only [c,Finsupp.degree_single]
    have hgen : Equigenerated (translatedFamily c (pairFamily i j)) d := by
      have hh := translatedFamily_equigenerated hbase c
      have he : 2+c.degree = d := by omega
      exact he ▸ hh
    have hp := htest _ hgen (fun o' ho' =>
      (translatedFamily_linearQuotients_iff hbase c o').mpr
        (pairFamily_linearQuotients_of_not_final hij o' (fun hf =>
          hn ((finalPair_unique_card_three hcard hij hf hfinal) ▸ ho'))))
    exact pairFamily_not_polymatroidal hij (by omega)
      ((translatedFamily_polymatroidal_iff hbase c).mp hp)
  · rintro rfl B hB hL
    exact (polymatroidal_iff_universal_revlex hB).mpr (fun o => hL o (mem_univ o))

theorem degree_test_number_three {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 3) (d : ℕ) (hd : 2 ≤ d) (F : Finset (VariableOrder V))
    (hF : DegreeOrderTests k d (F : Set (VariableOrder V))) : F.card = 6 := by
  rw [(degree_tests_card_three_iff_univ hcard d hd F).mp hF,card_univ,variableOrder_card,hcard]
  norm_num

theorem empty_tests_of_small_degree {k : Type*} [CommSemiring k]
    (d : ℕ) (hd : d ≤ 1) : DegreeOrderTests k d (∅ : Set (VariableOrder V)) := by
  intro B hB _
  exact equigenerated_polymatroidal_of_degree_le_one hB hd

theorem empty_tests_of_small_dimension {k : Type*} [CommSemiring k]
    (hcard : Fintype.card V ≤ 1) : UniversalOrderTests k (∅ : Set (VariableOrder V)) := by
  intro B d hB _
  exact equigenerated_polymatroidal_of_card_le_one hB hcard

theorem degree_tests_card_two_iff_nonempty {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 2) (d : ℕ) (hd : 2 ≤ d) (F : Set (VariableOrder V)) :
    DegreeOrderTests k d F ↔ F.Nonempty := by
  constructor
  · intro htest
    by_contra hn
    obtain ⟨i,j,hij⟩ := exists_distinct_of_card_two (by omega : 2 ≤ Fintype.card V)
    apply purePair_not_polymatroidal hd hij
    exact htest _ (purePair_equigenerated d i j) (fun o ho => False.elim (hn ⟨o,ho⟩))
  · intro hne B hB hL
    obtain ⟨o,ho⟩ := hne
    exact one_order_suffices_card_two hB (by omega) o (hL o ho)

end Characterizations

end
end CheckedCharacterizationsSource79

/-! ## Source: Characterizations.HighDegreeNumbers -/
section CheckedCharacterizationsSource80

/-! # The exact test number once the degree reaches n-2 -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem coversPatterns_top_iff (F : Set (VariableOrder V)) :
    CoversPatterns (Fintype.card V-3) F ↔ CoversFinalTriples F := by
  constructor
  · intro hF i q j hiq hij hqj
    have hc : (tripleCap i q j).card = Fintype.card V-3 := by
      rw [tripleCap,card_sdiff_of_subset (subset_univ _)]
      simp [hiq,hij,hqj]
    obtain ⟨o,ho,hp⟩ := hF i q j hiq hij hqj (tripleCap i q j) le_rfl hc
    exact ⟨o,ho,hp.1,hp.2.1,fun x hxi hxq hxj => hp.2.2 x
      ((mem_tripleCap _ _ _ _).mpr ⟨hxi,hxq,hxj⟩)⟩
  · intro hF i q j hiq hij hqj C hC hc
    obtain ⟨o,ho,hp⟩ := hF i q j hiq hij hqj
    refine ⟨o,ho,hp.1,hp.2.1,?_⟩
    intro x hx
    obtain ⟨hxi,hxq,hxj⟩ := (mem_tripleCap _ _ _ _).mp (hC hx)
    exact hp.2.2 x hxi hxq hxj

theorem exact_high_degree_test_number {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : 4 ≤ Fintype.card V) (d : ℕ) (hd : Fintype.card V-2 ≤ d) :
    (∃ F : Finset (VariableOrder V), DegreeOrderTests k d (F : Set (VariableOrder V)) ∧
      F.card = Fintype.card V * (Fintype.card V-1).choose 2) ∧
    (∀ F : Finset (VariableOrder V), DegreeOrderTests k d (F : Set (VariableOrder V)) →
      Fintype.card V * (Fintype.card V-1).choose 2 ≤ F.card) := by
  constructor
  · obtain ⟨F,hF,hc⟩ := (exact_universal_test_number (k := k) (V := V) hcard).1
    exact ⟨F,fun B hB hL => hF B d hB hL,hc⟩
  · intro F hF
    have hp := ((degreeOrderTests_iff_coverage d (by omega) hcard _).mp hF).1
    have he : min (d-1) (Fintype.card V-3) = Fintype.card V-3 := by omega
    rw [he] at hp
    exact triple_coverage_card_lower_bound F ((coversPatterns_top_iff _).mp hp)

end Characterizations

end
end CheckedCharacterizationsSource80

/-! ## Source: Characterizations.CountingBounds -/
section CheckedCharacterizationsSource81

/-! # The numerical upper and lower bounds of Corollary 5.5 -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def testProbability (d : ℕ) : ℝ := 2 / ((d:ℝ)*((d:ℝ)+1)*((d:ℝ)+2))

theorem inverse_point_count_eq_probability (s : ℕ) :
    (1 / ((s+3)*(s+2).choose 2 : ℕ) : ℝ) = testProbability (s+1) := by
  have hn := Nat.add_one_mul_choose_eq (s+1) 1
  have hn' : ((s+2).choose 2 : ℝ)*2 = ((s:ℝ)+1)*((s:ℝ)+2) := by
    have hh : (s+2).choose 2*2 = (s+1)*(s+2) := by simpa [mul_comm] using hn.symm
    exact_mod_cast hh
  have hpos : (0:ℝ) < (s+2).choose 2 := by exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ s+2))
  unfold testProbability
  push_cast
  field_simp
  nlinarith

theorem exists_degree_test_family_logarithmic {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) (hdn : d ≤ Fintype.card V-2) :
    ∃ F : Finset (VariableOrder V), DegreeOrderTests k d (F : Set (VariableOrder V)) ∧
      F.card ≤ ⌈(testProbability d)⁻¹ *
        (Real.log (Fintype.card V * (Fintype.card V-1).choose 2 *
          (Fintype.card V-3).choose (d-1)) + 1)⌉₊ := by
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  letI : Nonempty (DegreePattern V (d-1)) := degreePattern_nonempty (d-1) (by omega)
  have hp : 0 < testProbability d := by unfold testProbability; positivity
  have hR (P : DegreePattern V (d-1)) :
      finiteFraction (fun o : VariableOrder V => RealizesPattern o P) = testProbability d := by
    rw [realizesPattern_probability,inverse_point_count_eq_probability]
    congr 1
    omega
  obtain ⟨F,hsize,hcover⟩ := finite_probabilistic_cover
    (fun (P : DegreePattern V (d-1)) (o : VariableOrder V) => RealizesPattern o P)
    (testProbability d) hp hR
  have hpat : CoversPatterns (d-1) (F : Set (VariableOrder V)) :=
    (coversPatterns_iff_degreePattern _).mpr hcover
  have hmin : min (d-1) (Fintype.card V-3) = d-1 := by omega
  refine ⟨F,(degreeOrderTests_iff_coverage d hd hcard _).mpr ⟨by rw [hmin]; exact hpat,?_⟩,?_⟩
  · intro hn
    omega
  · have hcount : Fintype.card (DegreePattern V (d-1)) =
        Fintype.card V * (Fintype.card V-1).choose 2 * (Fintype.card V-3).choose (d-1) := by
      simpa only [Nat.card_eq_fintype_card] using card_degreePattern_paper (V := V) (d-1) (by omega)
    simpa only [hcount,Nat.cast_mul] using hsize

theorem degree_test_number_lower_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) (hdn : d ≤ Fintype.card V-2)
    (F : Finset (VariableOrder V)) (hF : DegreeOrderTests k d (F : Set (VariableOrder V))) :
    3 * (d+2).choose 3 ≤ F.card := by
  obtain ⟨T,hT,hTc⟩ := exists_subset_card_eq (show d+2 ≤ (univ : Finset V).card by simp; omega)
  let e : T ↪ V := Function.Embedding.subtype _
  let F' : Finset (VariableOrder T) := F.image (fun o => restrictedOrder o e)
  have hpatterns := ((degreeOrderTests_iff_coverage d hd hcard _).mp hF).1
  have hmin : min (d-1) (Fintype.card V-3) = d-1 := by omega
  rw [hmin] at hpatterns
  have hcover := (coversPatterns_iff_degreePattern _).mp hpatterns
  have htriples : CoversFinalTriples (F' : Set (VariableOrder T)) := by
    intro i q j hiq hij hqj
    have hTcard : T.card = (d-1)+3 := by omega
    let P : DegreePattern V (d-1) := ⟨⟨T,hTcard⟩,⟨j,⟨{i,q},
      by simp [insert_subset_iff,hij,hqj],by simp [hiq]⟩⟩⟩
    obtain ⟨o,ho,hp⟩ := hcover P
    refine ⟨restrictedOrder o e,mem_image.mpr ⟨o,ho,rfl⟩,?_⟩
    exact (coversPoint_pair_iff hiq hij hqj).mp hp
  have hh := triple_coverage_card_lower_bound F' htriples
  rw [Fintype.card_coe,hTc,pointedTriple_count_formula (d+2) (by omega)] at hh
  exact hh.trans (card_image_le)

end Characterizations

end
end CheckedCharacterizationsSource81

/-! ## Source: Characterizations.TestNumbers -/
section CheckedCharacterizationsSource82

/-! # The literal minimum numbers N(n) and N(n,d) -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid

variable (k : Type*) [CommSemiring k] [Nontrivial k]

theorem exists_degree_test_size (n d : ℕ) :
    ∃ m, ∃ F : Finset (VariableOrder (Fin n)),
      DegreeOrderTests k d (F : Set (VariableOrder (Fin n))) ∧ F.card = m := by
  refine ⟨Fintype.card (VariableOrder (Fin n)),univ,?_,card_univ⟩
  intro B hB hL
  exact (polymatroidal_iff_universal_revlex hB).mpr (fun o => hL o (mem_univ _))

def orderTestNumber (n d : ℕ) : ℕ := Nat.find (exists_degree_test_size k n d)

theorem orderTestNumber_attained (n d : ℕ) :
    ∃ F : Finset (VariableOrder (Fin n)),
      DegreeOrderTests k d (F : Set (VariableOrder (Fin n))) ∧ F.card = orderTestNumber k n d :=
  Nat.find_spec (exists_degree_test_size k n d)

theorem orderTestNumber_le_card {n d : ℕ} (F : Finset (VariableOrder (Fin n)))
    (hF : DegreeOrderTests k d (F : Set (VariableOrder (Fin n)))) : orderTestNumber k n d ≤ F.card :=
  Nat.find_min' (exists_degree_test_size k n d) ⟨F,hF,rfl⟩

theorem exists_universal_test_size (n : ℕ) :
    ∃ m, ∃ F : Finset (VariableOrder (Fin n)),
      UniversalOrderTests k (F : Set (VariableOrder (Fin n))) ∧ F.card = m := by
  refine ⟨Fintype.card (VariableOrder (Fin n)),univ,?_,card_univ⟩
  intro B d hB hL
  exact (polymatroidal_iff_universal_revlex hB).mpr (fun o => hL o (mem_univ _))

def universalTestNumber (n : ℕ) : ℕ := Nat.find (exists_universal_test_size k n)

theorem universalTestNumber_attained (n : ℕ) :
    ∃ F : Finset (VariableOrder (Fin n)), UniversalOrderTests k (F : Set (VariableOrder (Fin n))) ∧
      F.card = universalTestNumber k n := Nat.find_spec (exists_universal_test_size k n)

theorem universalTestNumber_le_card {n : ℕ} (F : Finset (VariableOrder (Fin n)))
    (hF : UniversalOrderTests k (F : Set (VariableOrder (Fin n)))) : universalTestNumber k n ≤ F.card :=
  Nat.find_min' (exists_universal_test_size k n) ⟨F,hF,rfl⟩

theorem universalTestNumber_ge_four {n : ℕ} (hn : 4 ≤ n) :
    universalTestNumber k n = 3*n.choose 3 := by
  obtain ⟨F,hF,hc⟩ := universalTestNumber_attained k n
  have hlo := universalOrderTests_card_lower_bound (V := Fin n) (by simpa) F hF
  obtain ⟨G,hG,hGc⟩ := (exact_universal_test_number (k := k) (V := Fin n) (by simpa using hn)).1
  have hhi := universalTestNumber_le_card k G hG
  have hformula := pointedTriple_count_formula n (by omega)
  simp only [Fintype.card_fin] at hlo hGc
  omega

theorem universalTestNumber_one : universalTestNumber k 1 = 0 := by
  have h := universalTestNumber_le_card k (∅ : Finset (VariableOrder (Fin 1)))
    (by simpa using (empty_tests_of_small_dimension (k := k) (V := Fin 1) (by simp)))
  simpa using h

theorem universalTestNumber_two : universalTestNumber k 2 = 1 := by
  let o : VariableOrder (Fin 2) := Fintype.equivFin _
  have hhi := universalTestNumber_le_card k ({o} : Finset (VariableOrder (Fin 2)))
    (nonempty_order_family_card_two (by simp) _ ⟨o,by simp⟩)
  obtain ⟨F,hF,hc⟩ := universalTestNumber_attained k 2
  have hne := (degree_tests_card_two_iff_nonempty (k := k) (V := Fin 2) (by simp) 2 (by omega) _).mp
    (fun B hB hL => hF B 2 hB hL)
  have hpos : 0 < F.card := card_pos.mpr hne
  simp only [card_singleton] at hhi
  omega

theorem universalTestNumber_three : universalTestNumber k 3 = 6 := by
  obtain ⟨F,hF,hc⟩ := universalTestNumber_attained k 3
  have hh := degree_test_number_three (k := k) (V := Fin 3) (by simp) 2 (by omega) F
    (fun B hB hL => hF B 2 hB hL)
  omega

theorem orderTestNumber_small_degree {n d : ℕ} (hd : d ≤ 1) : orderTestNumber k n d = 0 := by
  have hh := orderTestNumber_le_card k (d := d) (∅ : Finset (VariableOrder (Fin n)))
    (by simpa using (empty_tests_of_small_degree (k := k) (V := Fin n) d hd))
  simpa using hh

theorem orderTestNumber_small_dimension {n d : ℕ} (hn : n ≤ 1) : orderTestNumber k n d = 0 := by
  have hh := orderTestNumber_le_card k (d := d) (∅ : Finset (VariableOrder (Fin n)))
    (fun B hB _ => equigenerated_polymatroidal_of_card_le_one hB (by simpa using hn))
  simpa using hh

theorem orderTestNumber_two {d : ℕ} (hd : 2 ≤ d) : orderTestNumber k 2 d = 1 := by
  let o : VariableOrder (Fin 2) := Fintype.equivFin _
  have htest : DegreeOrderTests k d (({o} : Finset (VariableOrder (Fin 2))) : Set _) :=
    (degree_tests_card_two_iff_nonempty (by simp) d hd _).mpr ⟨o,by simp⟩
  have hhi := orderTestNumber_le_card k ({o} : Finset (VariableOrder (Fin 2))) htest
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k 2 d
  have hne := (degree_tests_card_two_iff_nonempty (by simp) d hd _).mp hF
  have hpos : 0 < F.card := card_pos.mpr hne
  simp only [card_singleton] at hhi
  omega

theorem orderTestNumber_three {d : ℕ} (hd : 2 ≤ d) : orderTestNumber k 3 d = 6 := by
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k 3 d
  have hh := degree_test_number_three (k := k) (V := Fin 3) (by simp) d hd F hF
  omega

theorem orderTestNumber_high_degree {n d : ℕ} (hn : 4 ≤ n) (hd : n-2 ≤ d) :
    orderTestNumber k n d = 3*n.choose 3 := by
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k n d
  have hlo := (exact_high_degree_test_number (k := k) (V := Fin n) (by simpa using hn) d (by simpa using hd)).2 F hF
  obtain ⟨G,hG,hGc⟩ := (exact_high_degree_test_number (k := k) (V := Fin n) (by simpa using hn) d (by simpa using hd)).1
  have hhi := orderTestNumber_le_card k G hG
  have hformula := pointedTriple_count_formula n (by omega)
  simp only [Fintype.card_fin] at hlo hGc
  omega

theorem orderTestNumber_logarithmic_upper {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) (hdn : d ≤ n-2) :
    orderTestNumber k n d ≤ ⌈(testProbability d)⁻¹ *
      (Real.log (n * (n-1).choose 2 * (n-3).choose (d-1)) + 1)⌉₊ := by
  obtain ⟨F,hF,hc⟩ := exists_degree_test_family_logarithmic (k := k) (V := Fin n) d hd
    (by simpa using hn) (by simpa using hdn)
  exact (orderTestNumber_le_card k F hF).trans (by simpa using hc)

theorem orderTestNumber_counting_lower {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) (hdn : d ≤ n-2) :
    3*(d+2).choose 3 ≤ orderTestNumber k n d := by
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k n d
  rw [←hc]
  exact degree_test_number_lower_bound d hd (by simpa using hn) (by simpa using hdn) F hF

theorem orderTestNumber_signature_bound {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) :
    n-1 ≤ (orderTestNumber k n d).choose (orderTestNumber k n d / 2) := by
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k n d
  simpa [hc] using degree_test_signature_bound d hd (V := Fin n) (by simpa using hn) F hF

end Characterizations

end
end CheckedCharacterizationsSource82

/-! ## Source: Characterizations.AsymptoticTests -/
section CheckedCharacterizationsSource83

/-! # The fixed-degree logarithmic asymptotic in Corollary 5.5 -/

noncomputable section
namespace Characterizations
open Classical Finset Filter Asymptotics
variable (k : Type*) [CommSemiring k] [Nontrivial k]

theorem pattern_count_le_power {n d : ℕ} (hd : 1 ≤ d) :
    n * (n-1).choose 2 * (n-3).choose (d-1) ≤ n^(d+2) := by
  calc
    _ ≤ n * n^2 * n^(d-1) := by
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul_left n ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) 2))
      · exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) (d-1))
    _ = _ := by
      have hfirst : n*n^2=n^3 := by ring
      rw [hfirst,←pow_add]
      congr 1
      omega

theorem testNumber_log_upper {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) (hdn : d+2 ≤ n) :
    (orderTestNumber k n d : ℝ) ≤
      ((testProbability d)⁻¹ * (d+2) + ((testProbability d)⁻¹+1)/Real.log 2) * Real.log n := by
  let Q := n * (n-1).choose 2 * (n-3).choose (d-1)
  let p := testProbability d
  have hp : 0 < p := by dsimp [p,testProbability]; positivity
  have hQ : 0 < Q := by
    apply Nat.mul_pos
    · exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
    · exact Nat.choose_pos (by omega)
  have hQpow : (Q:ℝ) ≤ (n:ℝ)^(d+2) := by exact_mod_cast pattern_count_le_power (n := n) (by omega : 1 ≤ d)
  have hlogQ : Real.log Q ≤ (d+2:ℝ)*Real.log n := by
    have hh := Real.log_le_log (show (0:ℝ)<Q by exact_mod_cast hQ) hQpow
    rw [Real.log_pow] at hh
    simpa using hh
  have hA : 0 ≤ p⁻¹ * (Real.log Q+1) := mul_nonneg (inv_nonneg.mpr hp.le)
    (by linarith [Real.log_natCast_nonneg Q])
  have hceil := Nat.ceil_lt_add_one hA
  have hN : (orderTestNumber k n d : ℝ) ≤ ⌈p⁻¹*(Real.log Q+1)⌉₊ := by
    exact_mod_cast orderTestNumber_logarithmic_upper k hn hd (by omega)
  have hN' : (orderTestNumber k n d : ℝ) ≤ p⁻¹*(Real.log Q+1)+1 := hN.trans hceil.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num)
    (by exact_mod_cast (show 2 ≤ n by omega))
  have hbonus := mul_le_mul_of_nonneg_left hlogn
    (div_nonneg (by positivity : 0 ≤ p⁻¹+1) hlog2.le)
  rw [div_mul_cancel₀ _ hlog2.ne'] at hbonus
  have hmain := mul_le_mul_of_nonneg_left hlogQ (inv_nonneg.mpr hp.le)
  change (orderTestNumber k n d : ℝ) ≤ (p⁻¹*(d+2) + (p⁻¹+1)/Real.log 2)*Real.log n
  nlinarith

theorem log_le_testNumber {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) :
    Real.log n ≤ (2*Real.log 2)*(orderTestNumber k n d : ℝ) := by
  have hsig := orderTestNumber_signature_bound k hn hd
  have hpow : n-1 ≤ 2^(orderTestNumber k n d) :=
    hsig.trans (Nat.choose_le_two_pow _ _)
  have hn1 : (0:ℝ) < (n-1:ℕ) := by exact_mod_cast (show 0<n-1 by omega)
  have hlog := Real.log_le_log hn1 (show ((n-1:ℕ):ℝ) ≤ (2:ℝ)^(orderTestNumber k n d) by exact_mod_cast hpow)
  rw [Real.log_pow] at hlog
  have hsquare : (n:ℝ) ≤ (((n-1:ℕ):ℝ))^2 := by
    have hcast : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast]
    have hnR : (4:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hlogn := Real.log_le_log (show (0:ℝ)<n by exact_mod_cast (show 0<n by omega)) hsquare
  rw [Real.log_pow] at hlogn
  norm_num at hlogn
  nlinarith

/-- For every fixed degree d≥2, the exact minimum number of tests has order
Θ(log n), with ordinary real natural logarithm and n tending to infinity. -/
theorem orderTestNumber_isTheta_log (d : ℕ) (hd : 2 ≤ d) :
    (fun n : ℕ => (orderTestNumber k n d : ℝ)) =Θ[atTop] (fun n : ℕ => Real.log n) := by
  constructor
  · apply IsBigO.of_bound ((testProbability d)⁻¹*(d+2) + ((testProbability d)⁻¹+1)/Real.log 2)
    filter_upwards [eventually_ge_atTop (max 4 (d+2))] with n hn
    have hh := testNumber_log_upper k (n := n) (d := d) (by omega) hd (by omega)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ (orderTestNumber k n d : ℝ) by positivity),
      abs_of_nonneg (Real.log_natCast_nonneg n)] using hh
  · apply IsBigO.of_bound (2*Real.log 2)
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hh := log_le_testNumber k hn hd
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ (orderTestNumber k n d : ℝ) by positivity),
      abs_of_nonneg (Real.log_natCast_nonneg n)] using hh

end Characterizations

end
end CheckedCharacterizationsSource83

/-! ## Source: Characterizations.PrimePowers -/
section CheckedCharacterizationsSource84

/-! # Ordinary coordinate-prime powers, and the exact intersection formula -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid Finset MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (k : Type*) [CommRing k]

def coordinatePrime (U : Finset V) : Ideal (MvPolynomial V k) :=
  Ideal.span (MvPolynomial.X '' (U : Set V))

theorem coordinatePrime_weight (U : Finset V) {f : MvPolynomial V k}
    (hf : f ∈ coordinatePrime k U) : Weight.Bound (subsetWeight U) 1 f := by
  intro a ha
  obtain ⟨i, hi, hpos⟩ := MvPolynomial.mem_ideal_span_X_image.mp hf a
    (Finsupp.mem_support_iff.mpr ha)
  rw [weight_subsetWeight]
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hpos).trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hi)

theorem monomial_mem_coordinatePrime_pow (U : Finset V) (n : ℕ) (a : Exponent V)
    (ha : n ≤ subsetSum a U) : monomial a (1 : k) ∈ (coordinatePrime k U) ^ n := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    obtain ⟨i, hi, hai⟩ := Finset.sum_pos_iff.mp
      (show 0 < ∑ j ∈ U, a j from lt_of_lt_of_le (Nat.zero_lt_succ n) ha)
    have hs := subsetSum_sub_single hai U
    rw [if_pos hi] at hs
    have hrest : n ≤ subsetSum (a - Finsupp.single i 1) U := by omega
    have hfactor : monomial a (1 : k) =
        monomial (a - Finsupp.single i 1) 1 * X i := by
      have he : a - Finsupp.single i 1 + Finsupp.single i 1 = a :=
        tsub_add_cancel_of_le (single_one_le hai)
      have hm := MvPolynomial.monomial_add_single (s := a - Finsupp.single i 1)
        (n := i) (e := 1) (a := (1 : k))
      rw [he, pow_one] at hm
      exact hm
    rw [hfactor, pow_succ]
    exact Ideal.mul_mem_mul (ih _ hrest)
      (Ideal.subset_span (Set.mem_image_of_mem _ hi))

theorem mem_coordinatePrime_pow_iff (U : Finset V) (n : ℕ) (f : MvPolynomial V k) :
    f ∈ (coordinatePrime k U) ^ n ↔ ∀ a ∈ f.support, n ≤ subsetSum a U := by
  constructor
  · intro hf a ha
    have h := Weight.bound_of_mem_pow (RingHom.id _) (subsetWeight U)
      (subsetWeight_nonnegative U) (coordinatePrime k U) 1
      (fun _ h => coordinatePrime_weight k U h) n hf a (Finsupp.mem_support_iff.mp ha)
    rw [weight_subsetWeight] at h
    simpa using h
  · intro hf
    rw [← f.support_sum_monomial_coeff]
    apply Ideal.sum_mem
    intro a ha
    have h := (coordinatePrime k U ^ n).mul_mem_left (C (f.coeff a))
      (monomial_mem_coordinatePrime_pow k U n a (hf a ha))
    simpa only [C_mul_monomial, mul_one] using h

theorem mem_coordinatePrime_pow_iff_weight (U : Finset V) (n : ℕ) (f : MvPolynomial V k) :
    f ∈ (coordinatePrime k U) ^ n ↔ Weight.Bound (subsetWeight U) (n : ℤ) f := by
  rw [mem_coordinatePrime_pow_iff]
  constructor
  · intro h a ha
    rw [weight_subsetWeight]
    exact_mod_cast h a (Finsupp.mem_support_iff.mpr ha)
  · intro h a ha
    have hh := h a (Finsupp.mem_support_iff.mp ha)
    rw [weight_subsetWeight] at hh
    exact_mod_cast hh

theorem canonicalLowerBases_eq_primePower_intersection {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) :
    monomialIdeal k (lowerBaseFamily (lowerRank B) d) =
      ⨅ U : Finset V, (coordinatePrime k U) ^ lowerRank B U := by
  ext f
  rw [mem_monomialIdeal_iff, Ideal.mem_iInf]
  simp only [mem_coordinatePrime_pow_iff, contains_canonicalLowerBases_iff hB hl hd,
    LowerFeasible]
  exact ⟨fun h U a ha => h a ha U, fun h a ha U => h U a ha⟩

variable [IsDomain k]

theorem coordinatePrime_pow_integrallyClosed (U : Finset V) (n : ℕ) :
    IsIntegrallyClosedIdeal ((coordinatePrime k U) ^ n) := by
  intro f hf
  apply (mem_coordinatePrime_pow_iff_weight k U n f).mpr
  exact Weight.bound_of_integral (RingHom.id _) (subsetWeight U)
    (subsetWeight_nonnegative U) ((coordinatePrime k U) ^ n) n
    (fun g hg => (mem_coordinatePrime_pow_iff_weight k U n g).mp hg) hf

theorem primePower_intersection_integrallyClosed (e : Finset V → ℕ) :
    IsIntegrallyClosedIdeal (⨅ U : Finset V, (coordinatePrime k U) ^ e U) := by
  apply Weight.integrallyClosed_of_weight_bounds (RingHom.id _) subsetWeight
    (fun U => (e U : ℤ)) (fun U => subsetWeight_nonnegative U)
  intro f
  simp only [Ideal.mem_iInf, mem_coordinatePrime_pow_iff_weight, RingHom.id_apply]

/-- Equation (2.4), with ordinary powers of literal ideals generated by the
variables in each subset, and the usual ideal-integral-closure predicate. -/
theorem integralClosure_eq_primePower_intersection {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    (f : MvPolynomial V k) :
    IntegralOverIdeal (monomialIdeal k B) f ↔
      f ∈ ⨅ U : Finset V, (coordinatePrime k U) ^ lowerRank B U := by
  rw [integralOverIdeal_iff_mem_canonicalLowerBases hB hanti hl hd,
    canonicalLowerBases_eq_primePower_intersection k hB hl hd]

/-- Corollary 2.12: intersection type plus local equigeneration is equivalent
to polymatroidality. Missing factors are represented by exponent zero. -/
theorem polymatroidal_iff_intersectionType_localEquigenerated {B : Family V}
    (hB : B.Nonempty) (hanti : Antichain B) :
    IsPolymatroidal B ↔ LocallyEquigenerated B ∧
      ∃ e : Finset V → ℕ, monomialIdeal k B =
        ⨅ U : Finset V, (coordinatePrime k U) ^ e U := by
  constructor
  · intro hp
    have hl := polymatroidal_locallyEquigenerated hp
    obtain ⟨d, hd⟩ := hp.1
    refine ⟨hl, lowerRank B, ?_⟩
    have he : B = lowerBaseFamily (lowerRank B) d :=
      family_eq_of_contains_iff hanti (lowerBaseFamily_equigenerated _ _).antichain
        (fun a => (contains_iff_canonical_lower B hB d hd hp a).trans
          (contains_canonicalLowerBases_iff hB hl hd a).symm)
    conv_lhs => rw [he]
    exact canonicalLowerBases_eq_primePower_intersection k hB hl hd
  · rintro ⟨hl, e, he⟩
    apply (polymatroidal_iff_integrallyClosed_localEquigenerated (k := k) hB hanti).mpr
    refine ⟨?_, hl⟩
    rw [he]
    exact primePower_intersection_integrallyClosed k e

end Characterizations

end
end CheckedCharacterizationsSource84

/-! ## Source: Characterizations.CoordinatePrime -/
section CheckedCharacterizationsSource85

/-! # The coordinate ideals in the intersection formula are actually prime -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (k : Type*) [CommRing k] [IsDomain k]

theorem coordinatePrime_isPrime (U : Finset V) : (coordinatePrime k U).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro ht
    have h : (1 : MvPolynomial V k) ∈ coordinatePrime k U := by rw [ht]; trivial
    have hb := coordinatePrime_weight k U h (0 : Exponent V) (by simp)
    simp [weight_subsetWeight, subsetSum] at hb
  · intro f g hfg
    by_contra hn
    push_neg at hn
    have hzero (p : MvPolynomial V k) (hp : p ∉ coordinatePrime k U) :
        ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight (subsetWeight U) a = 0 := by
      have hn : p ≠ 0 := fun he => hp (he ▸ (coordinatePrime k U).zero_mem)
      obtain ⟨m, hm, a, ha, he⟩ := Weight.exists_minimum (subsetWeight U) hn
      have hm0 : 0 ≤ m := he ▸ subsetWeight_nonnegative U p a ha
      have hm1 : m < 1 := by
        by_contra h
        apply hp
        have hb : Weight.Bound (subsetWeight U) (1 : ℤ) p := hm.mono (by omega)
        simpa only [pow_one] using (mem_coordinatePrime_pow_iff_weight k U 1 p).mpr hb
      exact ⟨a, ha, by omega⟩
    obtain ⟨a, ha, he⟩ := Weight.minimum_mul (subsetWeight_nonnegative U f)
      (subsetWeight_nonnegative U g) (hzero f hn.1) (hzero g hn.2)
    have hb := coordinatePrime_weight k U hfg a ha
    omega

end Characterizations

end
end CheckedCharacterizationsSource85

/-! ## Source: Characterizations.DependencyInterfaces -/
section CheckedCharacterizationsSource86

/-!
# Arbitrary polynomial generators in the exact Rees generation bound

This supplemental interface identifies generation by all homogeneous polynomial
elements through a given Rees degree with generation by the corresponding
monomials. Consequently the exact bound of Homological Shifts, Theorem 4.4,
is the least bound even when arbitrary polynomial generators are allowed.
The underlying ideal is the genuine homological-shift ideal in Mathlib's
ordinary Rees algebra; its coefficients need not themselves be monomials.
-/

noncomputable section

namespace Characterizations.DependencyInterfaces

open Classical Finset CommAlg CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- All homogeneous polynomial elements of the positive-power homological-shift
module whose Rees degree is at most `q`. -/
def boundedHomologicalPolynomials (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i q : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s f, s ≤ q ∧ f ∈ homologicalPowerPiece I hI i s ∧
    p.val = Polynomial.monomial s f}

theorem boundedHomologicalMonomials_subset_polynomials
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) (i q : ℕ) :
    boundedHomologicalPowerMonomials I hI i q ⊆
      boundedHomologicalPolynomials I hI i q := by
  rintro p ⟨s, a, ha, hs, he⟩
  exact ⟨s, MvPolynomial.monomial a 1, hs, ha, he⟩

theorem boundedHomologicalPolynomial_span_eq_monomials_rank
    (ρ : RankFunction V) (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i q : ℕ) :
    Ideal.span (boundedHomologicalPolynomials (rankIdeal k ρ) hI i q) =
      Ideal.span (boundedHomologicalPowerMonomials (rankIdeal k ρ) hI i q) := by
  apply le_antisymm
  · rw [boundedHomologicalPowerMonomials_rank]
    apply Ideal.span_le.mpr
    rintro p ⟨s, f, hs, hf, he⟩
    rw [homologicalPowerPiece_rank] at hf
    have hfPow := powerShiftPiece_le_pow (k := k) ρ i s hf
    have hp : p = liftReesCoefficient ρ s f hfPow := Subtype.ext he
    rw [hp]
    by_cases hs0 : s = 0
    · have hf0 : f = 0 := by simpa only [hs0, powerShiftPiece_zero, Ideal.mem_bot] using hf
      have hz : liftReesCoefficient ρ s f hfPow = 0 := by
        apply Subtype.ext
        simp [liftReesCoefficient, hf0]
      rw [hz]
      exact Ideal.zero_mem _
    · apply liftReesCoefficient_mem_of_bases ρ i (by omega) _ _ f hf
      intro a ha haPow
      have hmem : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s := by
        rw [powerShiftPiece_pos ρ i (by omega), rankShiftIdeal_eq_monomialIdeal,
          monomial_mem_iff]
        exact ⟨a, ha, le_rfl⟩
      exact Ideal.subset_span ⟨s, a, hmem, hs, rfl⟩
  · exact Ideal.span_mono (boundedHomologicalMonomials_subset_polynomials _ hI i q)

/-- Arbitrary polynomial homogeneous generators give exactly the same bounded
span as all bounded monomials. This includes the zero and unit ideals. -/
theorem boundedHomologicalPolynomial_span_eq_monomials
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) (i q : ℕ) :
    Ideal.span (boundedHomologicalPolynomials I hI i q) =
      Ideal.span (boundedHomologicalPowerMonomials I hI i q) := by
  rcases hI.eq_bot_or_rank with h0 | ⟨ρ, he⟩
  · subst I
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro p ⟨s, f, hs, hf, he⟩
      have hf0 : f = 0 := by
        by_cases hs0 : s = 0
        · simpa [homologicalPowerPiece, hs0] using hf
        · simpa [homologicalPowerPiece, hs0, Ideal.bot_pow hs0] using hf
      have hp : p = 0 := by
        apply Subtype.ext
        simpa [hf0] using he
      rw [hp]
      exact Ideal.zero_mem _
    · exact Ideal.span_mono (boundedHomologicalMonomials_subset_polynomials _ hI i q)
  · subst I
    exact boundedHomologicalPolynomial_span_eq_monomials_rank ρ hI i q

/-- The exact least Rees generation bound permits arbitrary polynomial
homogeneous generators and arbitrary polynomial coefficients in the Rees ring. -/
theorem homologicalPower_polynomial_generation_bound_iff
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (ρ : RankFunction V) (he : I = rankIdeal k ρ) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (q : ℕ) :
    homologicalPowerIdeal I hI i = Ideal.span (boundedHomologicalPolynomials I hI i q) ↔
      globalPowerThreshold ρ i ≤ q := by
  rw [boundedHomologicalPolynomial_span_eq_monomials]
  exact homologicalPower_generation_bound_iff I hI ρ he hρ i hi0 hi q

end Characterizations.DependencyInterfaces

end
end CheckedCharacterizationsSource86

/-! ## Source: Characterizations.Thickening -/
section CheckedCharacterizationsSource87

/-! # Multiplication by every power of the homogeneous maximal ideal -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid Finset MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]

def degreeFamily (q : ℕ) : Family V := (Finsupp.finite_of_degree_eq (σ := V) q).toFinset

@[simp] theorem mem_degreeFamily (q : ℕ) (a : Exponent V) : a ∈ degreeFamily q ↔ a.degree = q := by
  simp [degreeFamily]

def thickening (B : Family V) (q : ℕ) : Family V :=
  (B.product (degreeFamily q)).image (fun bc => bc.1 + bc.2)

theorem thickening_equigenerated {B : Family V} {d : ℕ} (hd : Equigenerated B d) (q : ℕ) :
    Equigenerated (thickening B q) (d + q) := by
  intro a ha
  obtain ⟨⟨b,c⟩, hbc, rfl⟩ := mem_image.mp ha
  obtain ⟨hb,hc⟩ := mem_product.mp hbc
  simp only [map_add, hd b hb, (mem_degreeFamily q c).mp hc]

theorem contains_thickening_iff {B : Family V} {d : ℕ} (hd : Equigenerated B d)
    (q : ℕ) (a : Exponent V) :
    Contains (thickening B q) a ↔ Contains B a ∧ d + q ≤ a.degree := by
  constructor
  · rintro ⟨w, hw, hwa⟩
    obtain ⟨⟨b,c⟩, hbc, rfl⟩ := mem_image.mp hw
    obtain ⟨hb,hc⟩ := mem_product.mp hbc
    refine ⟨⟨b,hb,(le_add_right le_rfl).trans hwa⟩, ?_⟩
    have h := degree_mono hwa
    simpa only [map_add, hd b hb, (mem_degreeFamily q c).mp hc] using h
  · rintro ⟨⟨b,hb,hba⟩, hdeg⟩
    have hdiff : q ≤ (a-b).degree := by
      have h := congrArg Finsupp.degree (tsub_add_cancel_of_le hba)
      simp only [map_add, hd b hb] at h
      omega
    obtain ⟨c,hc,hcd⟩ := Finsupp.exists_le_degree_eq (a-b) q hdiff
    refine ⟨b+c, mem_image.mpr ⟨(b,c), mem_product.mpr ⟨hb,(mem_degreeFamily q c).mpr hcd⟩,rfl⟩, ?_⟩
    calc
      b+c ≤ b+(a-b) := add_le_add le_rfl hc
      _ = a := by rw [add_comm, tsub_add_cancel_of_le hba]

theorem thickening_mono {B C : Family V} (h : B ⊆ C) (q : ℕ) :
    thickening B q ⊆ thickening C q := by
  intro a ha
  obtain ⟨⟨b,c⟩,hbc,rfl⟩ := mem_image.mp ha
  exact mem_image.mpr ⟨(b,c),mem_product.mpr ⟨h (mem_product.mp hbc).1,(mem_product.mp hbc).2⟩,rfl⟩

theorem thickening_nonempty [Nonempty V] {B : Family V} (hB : B.Nonempty) (q : ℕ) :
    (thickening B q).Nonempty := by
  obtain ⟨b,hb⟩ := hB
  obtain ⟨i⟩ := ‹Nonempty V›
  exact ⟨b+Finsupp.single i q,mem_image.mpr ⟨(b,Finsupp.single i q),
    mem_product.mpr ⟨hb,by simp⟩,rfl⟩⟩

def raisedTopRank (r : Finset V → ℕ) (q : ℕ) (U : Finset V) : ℕ :=
  if U = Finset.univ then r U + q else r U

theorem raisedTopRank_supermodular {r : Finset V → ℕ} (hr : Supermodular r) (q : ℕ) :
    Supermodular (raisedTopRank r q) := by
  intro A C
  by_cases hA : A = Finset.univ
  · subst A
    have hu : (Finset.univ : Finset V) ∪ C = Finset.univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) Finset.subset_union_left
    rw [hu]
    simp
  by_cases hC : C = Finset.univ
  · subst C
    have hu : A ∪ (Finset.univ : Finset V) = Finset.univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) Finset.subset_union_right
    rw [hu]
    simp [add_comm]
  have h := hr A C
  have hle (U : Finset V) : r U ≤ raisedTopRank r q U := by
    unfold raisedTopRank; split_ifs <;> omega
  have hU := hle (A ∪ C)
  have hI := hle (A ∩ C)
  simp only [raisedTopRank, if_neg hA, if_neg hC]
  change r A + r C ≤ raisedTopRank r q (A ∪ C) + raisedTopRank r q (A ∩ C)
  omega

theorem raisedTopRank_feasible_iff {r : Finset V → ℕ} (q : ℕ) (a : Exponent V) :
    LowerFeasible (raisedTopRank r q) a ↔ LowerFeasible r a ∧ r Finset.univ + q ≤ a.degree := by
  constructor
  · intro h
    refine ⟨fun U => ?_, ?_⟩
    · have hh := h U
      unfold raisedTopRank at hh
      split_ifs at hh <;> omega
    · simpa [raisedTopRank] using h Finset.univ
  · rintro ⟨h,hdeg⟩ U
    by_cases hU : U = Finset.univ
    · subst U; simpa [raisedTopRank] using hdeg
    · simpa only [raisedTopRank, if_neg hU] using h U

theorem thickening_polymatroidal {B : Family V} (hB : B.Nonempty)
    (hp : IsPolymatroidal B) (q : ℕ) : IsPolymatroidal (thickening B q) := by
  obtain ⟨d,hd⟩ := hp.1
  have hr := lowerRank_supermodular hB (polymatroidal_locallyEquigenerated hp)
  apply polymatroidal_of_lower_inequalities (thickening_equigenerated hd q)
    (raisedTopRank_supermodular hr q)
  intro a
  rw [contains_thickening_iff hd, contains_iff_canonical_lower B hB d hd hp,
    raisedTopRank_feasible_iff, lowerRank_univ_of_equigenerated hB hd]

variable (k : Type*) [CommRing k]

theorem degreeFamily_ideal_eq_maximal_pow (q : ℕ) :
    monomialIdeal k (degreeFamily (V := V) q) = (coordinatePrime k Finset.univ) ^ q := by
  ext f
  rw [mem_monomialIdeal_iff, mem_coordinatePrime_pow_iff]
  apply forall₂_congr
  intro a ha
  simp only [subsetSum_univ]
  constructor
  · rintro ⟨b,hb,hba⟩
    exact ((mem_degreeFamily q b).mp hb).symm.le.trans (degree_mono hba)
  · intro h
    obtain ⟨b,hba,hbd⟩ := Finsupp.exists_le_degree_eq a q h
    exact ⟨b,(mem_degreeFamily q b).mpr hbd,hba⟩

theorem thickening_ideal_eq (B : Family V) (q : ℕ) :
    monomialIdeal k (thickening B q) = (coordinatePrime k Finset.univ) ^ q * monomialIdeal k B := by
  rw [← degreeFamily_ideal_eq_maximal_pow, mul_comm, monomialIdeal_mul]
  rfl

end Characterizations

end
end CheckedCharacterizationsSource87

/-! ## Source: Characterizations.ThickeningClosure -/
section CheckedCharacterizationsSource88

/-! # Exact closure and sharp power threshold for minimal local obstructions -/
noncomputable section
namespace Characterizations
universe u
open Classical CommAlg CommAlg.Polymatroid Finset
open scoped Pointwise
variable {V : Type u} [Fintype V] [DecidableEq V]

@[simp] theorem realExponent_add (a b : Exponent V) :
    realExponent (a+b) = realExponent a + realExponent b := by
  ext i
  simp [realExponent]

theorem realImage_thickening (B : Family V) (q : ℕ) :
    realExponent '' (thickening B q : Set (Exponent V)) =
      (realExponent '' (B : Set (Exponent V))) +
        (realExponent '' (degreeFamily (V := V) q : Set (Exponent V))) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨⟨b,c⟩,hbc,rfl⟩ := mem_image.mp ha
    obtain ⟨hb,hc⟩ := mem_product.mp hbc
    exact Set.mem_add.mpr ⟨realExponent b,Set.mem_image_of_mem _ hb,
      realExponent c,Set.mem_image_of_mem _ hc,(realExponent_add b c).symm⟩
  · intro hx
    obtain ⟨y,hy,z,hz,rfl⟩ := Set.mem_add.mp hx
    obtain ⟨b,hb,rfl⟩ := hy
    obtain ⟨c,hc,rfl⟩ := hz
    exact ⟨b+c,mem_image.mpr ⟨(b,c),mem_product.mpr ⟨hb,hc⟩,rfl⟩,realExponent_add b c⟩

theorem closed_thickening_generator_mem_convexHull {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    (q : ℕ) {a : Exponent V} (ha : a ∈ thickening (lowerBaseFamily (lowerRank B) d) q) :
    realExponent a ∈ convexHull ℝ (realExponent '' (thickening B q : Set (Exponent V))) := by
  obtain ⟨⟨b,c⟩,hbc,rfl⟩ := mem_image.mp ha
  obtain ⟨hb,hc⟩ := mem_product.mp hbc
  rw [realExponent_add, realImage_thickening, convexHull_add]
  exact Set.add_mem_add (canonicalLowerBase_mem_convexHull hB hanti hl hd hb)
    (subset_convexHull ℝ _ (Set.mem_image_of_mem _ hc))

theorem thickening_polymatroidal_iff_closed [Nonempty V] {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) (q : ℕ) :
    IsPolymatroidal (thickening B q) ↔
      thickening B q = thickening (lowerBaseFamily (lowerRank B) d) q := by
  constructor
  · intro hp
    apply Finset.Subset.antisymm (thickening_mono (subset_lowerBaseFamily hd) q)
    intro a ha
    have hi := monomial_integral_of_convexHull ℚ (thickening B q) a
      (closed_thickening_generator_mem_convexHull hB hanti hl hd q ha)
    have hm := polymatroidal_integrallyClosed (thickening_nonempty hB q) hp _ hi
    have hcontains := (monomial_mem_iff (k := ℚ) _ _).mp hm
    have hdeg := thickening_equigenerated (lowerBaseFamily_equigenerated (lowerRank B) d) q a ha
    exact ((thickening_equigenerated hd q).mem_iff_contains hdeg).mpr hcontains
  · intro he
    rw [he]
    exact thickening_polymatroidal (hB.mono (subset_lowerBaseFamily hd))
      (canonicalLowerBases_polymatroidal hB hl hd) q

theorem thickening_eq_closed_iff_hole_bound {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) (q : ℕ) :
    thickening B q = thickening (lowerBaseFamily (lowerRank B) d) q ↔
      ∀ a ∈ holeSet B, a.degree < d+q := by
  constructor
  · intro he a ha
    by_contra hn
    have hc : Contains (thickening (lowerBaseFamily (lowerRank B) d) q) a :=
      (contains_thickening_iff (lowerBaseFamily_equigenerated _ _) q a).mpr
        ⟨(contains_canonicalLowerBases_iff hB hl hd a).mpr ha.1,by omega⟩
    rw [← he] at hc
    exact ha.2 ((contains_thickening_iff hd q a).mp hc).1
  · intro h
    apply family_eq_of_contains_iff (thickening_equigenerated hd q).antichain
      (thickening_equigenerated (lowerBaseFamily_equigenerated _ _) q).antichain
    intro a
    rw [contains_thickening_iff hd, contains_thickening_iff (lowerBaseFamily_equigenerated _ _),
      contains_canonicalLowerBases_iff hB hl hd]
    constructor
    · rintro ⟨⟨b,hb,hba⟩,hdeg⟩
      exact ⟨fun U => (lowerRank_le hb U).trans (Finset.sum_le_sum (fun i _ => hba i)),hdeg⟩
    · rintro ⟨ha,hdeg⟩
      refine ⟨?_,hdeg⟩
      by_contra hout
      exact (not_lt_of_ge hdeg) (h a ⟨ha,hout⟩)

theorem thickening_polymatroidal_iff_top_hole [Nonempty V] {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ holeSet B) (hmax : ∀ b ∈ holeSet B, b.degree ≤ a.degree) (q : ℕ) :
    IsPolymatroidal (thickening B q) ↔ a.degree < d+q := by
  rw [thickening_polymatroidal_iff_closed hB hanti hl hd,
    thickening_eq_closed_iff_hole_bound hB hl hd]
  exact ⟨fun h => h a ha,fun h b hb => (hmax b hb).trans_lt h⟩

theorem least_polymatroidal_thickening [Nonempty V] {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ holeSet B) (hmax : ∀ b ∈ holeSet B, b.degree ≤ a.degree)
    (hda : d ≤ a.degree) :
    IsLeast {q : ℕ | IsPolymatroidal (thickening B q)} (a.degree+1-d) := by
  constructor
  · exact (thickening_polymatroidal_iff_top_hole hB hanti hl hd ha hmax _).mpr (by omega)
  · intro q hq
    have h := (thickening_polymatroidal_iff_top_hole hB hanti hl hd ha hmax q).mp hq
    omega

end Characterizations

end
end CheckedCharacterizationsSource88

/-! ## Source: Characterizations.Strands.FiniteHoles -/
section CheckedCharacterizationsSource89

/-! # Exact regularity bounds from a finite collection of missing monomials -/
noncomputable section
set_option maxHeartbeats 600000
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

lemma chains_le_of_faces_at_degree {K L : Finset V → Prop} (i : ℕ)
    (h : ∀ s, K s → s.card = i → L s) : Chains (k := k) K i ≤ Chains L i := by
  apply Submodule.span_mono
  rintro z ⟨s, ⟨hs, hc⟩, rfl⟩
  exact ⟨s, ⟨h s hs hc, hc⟩, rfl⟩

lemma polymatroidal_faces_exact_off_linear (B : Family V) (hB : B.Nonempty)
    (d : ℕ) (hdeg : Equigenerated B d) (hpoly : IsPolymatroidal B)
    (a : Exponent V) (i : ℕ) (hoff : a.degree ≠ d+i) :
    ExactIn (k := k) (koszulFaces B a) i := by
  by_contra hex
  have hn := (nonzeroHomology_iff_not_exactIn _ _).mpr hex
  let g := canonicalRank B hB d hdeg hpoly
  have hr : rankBases g = B := rankBases_canonical B hB d hdeg hpoly
  have hn' : NonzeroHomology (k := k) (koszulFaces (rankBases g) a) i := by
    simpa only [hr] using hn
  have hm := (koszulFaces_nonzeroHomology_iff_rankShiftFamily g a i).mp hn'
  have hd := ((mem_rankShiftFamily_iff g i a).mp hm).1
  have hg : g Finset.univ = d := by
    change upperRank B Finset.univ = d
    obtain ⟨b, hb, he⟩ := upperRank_attained hB Finset.univ
    simpa only [subsetSum_univ, hdeg b hb] using he.symm
  exact hoff (by simpa only [hg] using hd)

lemma exactIn_of_finite_holes (B C : Family V)
    (hincl : ∀ a, Contains B a → Contains C a) (t : ℕ)
    (hholes : ∀ a, Contains C a → ¬Contains B a → a.degree ≤ t)
    (a : Exponent V) (i : ℕ) (hlarge : t+i+1 < a.degree)
    (hC : ExactIn (k := k) (koszulFaces C a) i) :
    ExactIn (k := k) (koszulFaces B a) i := by
  intro z hz hc
  have hzC : z ∈ Chains (koszulFaces C a) i :=
    chains_mono (fun s hs => ⟨hs.1, hincl _ hs.2⟩) i hz
  obtain ⟨y, hy, he⟩ := hC z hzC hc
  refine ⟨y, ?_, he⟩
  apply chains_le_of_faces_at_degree (i+1) (K := koszulFaces C a) _ hy
  intro s hs hcard
  refine ⟨hs.1, ?_⟩
  by_contra hnot
  have hb := hholes (a-faceExponent s) hs.2 hnot
  have hd := degree_sub_faceExponent hs.1
  omega

lemma finite_holes_betti_degree_bound (B C : Family V)
    (hincl : ∀ a, Contains B a → Contains C a) (t : ℕ)
    (hholes : ∀ a, Contains C a → ¬Contains B a → a.degree ≤ t)
    (hC : C.Nonempty) (d : ℕ) (hdeg : Equigenerated C d)
    (hpoly : IsPolymatroidal C) (hd : d ≤ t+1)
    (a : Exponent V) (i : ℕ) (hbeta : bettiNumber (k := k) B a i ≠ 0) :
    a.degree ≤ t+i+1 := by
  by_contra hle
  have hl : t+i+1 < a.degree := by omega
  have hnonzero := (bettiNumber_pos_iff_faces B a i).mp (Nat.pos_of_ne_zero hbeta)
  have hnot := (nonzeroHomology_iff_not_exactIn _ _).mp hnonzero
  apply hnot (exactIn_of_finite_holes B C hincl t hholes a i hl _)
  exact polymatroidal_faces_exact_off_linear C hC d hdeg hpoly a i (by omega)

end Characterizations.Strands

end
end CheckedCharacterizationsSource89

/-! ## Source: Characterizations.Regularity -/
section CheckedCharacterizationsSource90

/-! # Genuine Tor regularity of a minimal local obstruction -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The maximum defining Castelnuovo–Mumford regularity: all actual derived-Tor
degrees are bounded by r+i, and that bound occurs. -/
def IsTorRegularity (B : Family V) (r : ℕ) : Prop :=
  (∀ i a, bettiNumber (k := k) B a i ≠ 0 → a.degree ≤ r+i) ∧
    ∃ i a, bettiNumber (k := k) B a i ≠ 0 ∧ a.degree = r+i

theorem torRegularity_unique {B : Family V} {r s : ℕ}
    (hr : IsTorRegularity (k := k) B r) (hs : IsTorRegularity (k := k) B s) : r = s := by
  obtain ⟨i,a,ha,hda⟩ := hr.2
  obtain ⟨j,b,hb,hdb⟩ := hs.2
  have h₁ := hs.1 i a ha
  have h₂ := hr.1 j b hb
  omega

theorem totalBettiNumber_pos_iff (B : Family V) (i j : ℕ) :
    0 < Strands.totalBettiNumber (k := k) B i j ↔
      ∃ a, a.degree = j ∧ 0 < bettiNumber (k := k) B a i := by
  rw [Strands.totalBettiNumber, Finset.sum_pos_iff]
  simp

/-- The multigraded maximum agrees exactly with the usual total-degree formula. -/
theorem torRegularity_iff_total (B : Family V) (r : ℕ) :
    IsTorRegularity (k := k) B r ↔
      (∀ i j, 0 < Strands.totalBettiNumber (k := k) B i j → j ≤ r+i) ∧
        ∃ i j, 0 < Strands.totalBettiNumber (k := k) B i j ∧ j = r+i := by
  constructor
  · rintro ⟨hu,⟨i,a,ha,hda⟩⟩
    refine ⟨?_,i,a.degree,(totalBettiNumber_pos_iff B i _).mpr
      ⟨a,rfl,Nat.pos_of_ne_zero ha⟩,hda⟩
    intro i j hij
    obtain ⟨a,had,ha⟩ := (totalBettiNumber_pos_iff B i j).mp hij
    exact had ▸ hu i a (Nat.ne_of_gt ha)
  · rintro ⟨hu,⟨i,j,hij,hj⟩⟩
    refine ⟨?_,?_⟩
    · intro i a ha
      exact hu i a.degree ((totalBettiNumber_pos_iff B i _).mpr ⟨a,rfl,Nat.pos_of_ne_zero ha⟩)
    · obtain ⟨a,had,ha⟩ := (totalBettiNumber_pos_iff B i j).mp hij
      exact ⟨i,a,Nat.ne_of_gt ha,had.trans hj⟩

theorem generator_bettiNumber_pos {B : Family V} {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ B) : 0 < bettiNumber (k := k) B a 0 := by
  rw [bettiNumber_pos_iff_faces]
  apply nonzeroHomology_zero_of_only_empty
  · exact ⟨by simp,by simpa using (show Contains B a from ⟨a,ha,le_rfl⟩)⟩
  · intro s hs
    obtain ⟨b,hb,hba⟩ := hs.2
    have hdeg := degree_mono hba
    have he := Strands.degree_sub_faceExponent hs.1
    rw [hd b hb] at hdeg
    rw [hd a ha] at he
    exact Finset.card_eq_zero.mp (by omega)

theorem polymatroidal_torRegularity {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hp : IsPolymatroidal B) :
    IsTorRegularity (k := k) B d := by
  constructor
  · intro i a ha
    have he : a.degree = d+i := by
      by_contra hn
      have hex := Strands.polymatroidal_faces_exact_off_linear (k := k) B hB d hd hp a i hn
      have hh := (bettiNumber_pos_iff_faces B a i).mp (Nat.pos_of_ne_zero ha)
      exact ((nonzeroHomology_iff_not_exactIn _ _).mp hh) hex
    exact he.le
  · obtain ⟨a,ha⟩ := hB
    exact ⟨0,a,Nat.ne_of_gt (generator_bettiNumber_pos hd ha),by simpa using hd a ha⟩

theorem torRegularity_of_top_hole [Nonempty V] {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ holeSet B) (hmax : ∀ b ∈ holeSet B, b.degree ≤ a.degree)
    (hmul : ∀ j, Contains B (a+Finsupp.single j 1)) :
    IsTorRegularity (k := k) B (a.degree+1) := by
  have hda : d ≤ a.degree := by
    have h := ha.1 Finset.univ
    simpa only [lowerRank_univ_of_equigenerated hB hd, subsetSum_univ] using h
  constructor
  · intro i b hb
    have h := Strands.finite_holes_betti_degree_bound (k := k) B
      (lowerBaseFamily (lowerRank B) d) (fun c hc =>
        (contains_canonicalLowerBases_iff hB hl hd c).mpr
          (fun U => by
            obtain ⟨z,hz,hzc⟩ := hc
            exact (lowerRank_le hz U).trans (Finset.sum_le_sum (fun j _ => hzc j))))
      a.degree (fun c hc hout => hmax c
        ⟨(contains_canonicalLowerBases_iff hB hl hd c).mp hc,hout⟩)
      (hB.mono (subset_lowerBaseFamily hd)) d (lowerBaseFamily_equigenerated _ _)
      (canonicalLowerBases_polymatroidal hB hl hd) (by omega) b i hb
    omega
  · have hc : Fintype.card V = (Fintype.card V-1)+1 := by
      have hpos := Fintype.card_pos (α := V)
      omega
    refine ⟨Fintype.card V-1,a+faceExponent Finset.univ,?_,?_⟩
    · rw [Strands.socle_bettiNumber_eq_one B a ha.2 hmul _ hc]
      exact one_ne_zero
    · rw [map_add, Strands.degree_faceExponent, Finset.card_univ]
      omega

theorem locallyEquigenerated_of_proper_polymatroidal {B : Family V} {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    LocallyEquigenerated B := by
  intro U
  by_cases hU : U = Finset.univ
  · subst U
    rw [localize_univ_of_antichain hd.antichain]
    exact ⟨d,hd⟩
  · exact (hloc U ((Finset.subset_univ U).ssubset_of_ne hU)).1

theorem holeSet_nonempty_of_nonclosed {B : Family V} {d : ℕ}
    (hd : Equigenerated B d) (hne : B ≠ lowerBaseFamily (lowerRank B) d) :
    (holeSet B).Nonempty := by
  have hnot : ¬ lowerBaseFamily (lowerRank B) d ⊆ B := fun h =>
    hne (Finset.Subset.antisymm (subset_lowerBaseFamily hd) h)
  obtain ⟨a,haJ,haB⟩ := Finset.not_subset.mp hnot
  obtain ⟨had,hlo⟩ := (mem_lowerBaseFamily _ _ _).mp haJ
  exact ⟨a,hlo,fun h => haB ((hd.mem_iff_contains had).mpr h)⟩

/-- Proposition 4.1: the exact maximum hole degree, actual Tor regularity, and
the least maximal-ideal power that becomes polymatroidal. -/
theorem minimal_local_obstruction {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U))
    (hne : B ≠ lowerBaseFamily (lowerRank B) d) :
    ∃ t : ℕ, (∃ a ∈ holeSet B, a.degree = t) ∧
      (∀ b ∈ holeSet B, b.degree ≤ t) ∧ d ≤ t ∧
      IsTorRegularity (k := k) B (t+1) ∧
      IsLeast {q : ℕ | IsPolymatroidal (thickening B q)} (t+1-d) := by
  have hl := locallyEquigenerated_of_proper_polymatroidal hd hloc
  obtain ⟨a,ha,hmax,hda,hmul⟩ := exists_top_hole hB hd hloc (holeSet_nonempty_of_nonclosed hd hne)
  haveI : Nonempty V := by
    by_contra hn
    haveI : IsEmpty V := not_nonempty_iff.mp hn
    obtain ⟨b,hb⟩ := hB
    exact ha.2 ⟨b,hb,(Subsingleton.elim b a).le⟩
  exact ⟨a.degree,⟨a,ha,rfl⟩,hmax,hda,torRegularity_of_top_hole hB hl hd ha hmax hmul,
    least_polymatroidal_thickening hB hd.antichain hl hd ha hmax hda⟩

end Characterizations

end
end CheckedCharacterizationsSource90

/-! ## Source: Characterizations.TotalTests -/
section CheckedCharacterizationsSource91

/-! # Total-degree Tor formulations of the homological tests

The total-degree piece is the sum, inside genuine derived Tor, of its actual
multigraded submodules of that total degree.  Vanishing is proved equivalent
both to fine-degree vanishing and to the finite sum of Betti dimensions.
-/

noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid CommAlg.Koszul Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

def totalDegreeTor (B : Family V) (i j : ℕ) :=
  ⨆ (a : Exponent V) (_ : a.degree = j), gradedTor (k := k) B a i

theorem totalDegreeTor_eq_bot_iff (B : Family V) (i j : ℕ) :
    totalDegreeTor (k := k) B i j = ⊥ ↔
      ∀ a : Exponent V, a.degree = j → bettiNumber (k := k) B a i = 0 := by
  simp only [totalDegreeTor,iSup_eq_bot,bettiNumber,Submodule.finrank_eq_zero]

theorem iSup_totalDegreeTor (B : Family V) (i : ℕ) :
    (⨆ j : ℕ, totalDegreeTor (k := k) B i j) = ⊤ := by
  rw [← iSup_gradedTor B i]
  apply le_antisymm
  · apply iSup_le
    intro j
    apply iSup_le
    intro a
    apply iSup_le
    intro _
    exact le_iSup (fun a => gradedTor (k := k) B a i) a
  · apply iSup_le
    intro a
    exact le_iSup_of_le a.degree (le_iSup_of_le a (le_iSup_of_le rfl le_rfl))

theorem totalBettiNumber_eq_zero_iff (B : Family V) (i j : ℕ) :
    Strands.totalBettiNumber (k := k) B i j = 0 ↔
      ∀ a : Exponent V, a.degree = j → bettiNumber (k := k) B a i = 0 := by
  constructor
  · intro hz a ha
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hh := (totalBettiNumber_pos_iff B i j).mpr ⟨a,ha,hp⟩
    omega
  · intro h
    apply Nat.eq_zero_of_not_pos
    intro hp
    obtain ⟨a,ha,hpa⟩ := (totalBettiNumber_pos_iff B i j).mp hp
    have hz := h a ha
    omega

theorem totalBettiNumber_zero_iff_totalDegreeTor (B : Family V) (i j : ℕ) :
    Strands.totalBettiNumber (k := k) B i j = 0 ↔ totalDegreeTor (k := k) B i j = ⊥ :=
  (totalBettiNumber_eq_zero_iff B i j).trans (totalDegreeTor_eq_bot_iff B i j).symm

theorem retainedLinearThrough_iff_totalBetti (B : Family V) (U : Finset V) (e t : ℕ) :
    RetainedLinearThrough (k := k) B U e t ↔
      ∀ i : ℕ, i ≤ t → ∀ j : ℕ, j ≠ e+i →
        Strands.totalBettiNumber (k := k) (localFamily B U) i j = 0 := by
  constructor
  · intro h i hi j hj
    apply (totalBettiNumber_eq_zero_iff _ _ _).mpr
    intro a ha
    exact h a i hi (by rwa [ha])
  · intro h a i hi hoff
    exact (totalBettiNumber_eq_zero_iff _ _ _).mp (h i hi a.degree hoff) a rfl

def RetainedTorLinearThrough (B : Family V) (U : Finset V) (e t : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ t → ∀ j : ℕ, j ≠ e+i →
    totalDegreeTor (k := k) (localFamily B U) i j = ⊥

theorem retainedLinearThrough_iff_totalTor (B : Family V) (U : Finset V) (e t : ℕ) :
    RetainedLinearThrough (k := k) B U e t ↔ RetainedTorLinearThrough (k := k) B U e t := by
  rw [retainedLinearThrough_iff_totalBetti]
  simp only [RetainedTorLinearThrough,totalBettiNumber_zero_iff_totalDegreeTor]

def TotalTriangularTests (B : Family V) (d : ℕ) : Prop :=
  ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
    ∃ e, Equigenerated (localFamily B U) e ∧
      (0 < e → RetainedTorLinearThrough (k := k) B U e
        (min (e-1) (min (d-1-(Fintype.card V-U.card)) (U.card-1))))

def TotalDegreeBoundedTests (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
    (0 < e → RetainedTorLinearThrough (k := k) B U e (e-1))

def TotalDegreeDimensionBoundedTests (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
    (0 < e → RetainedTorLinearThrough (k := k) B U e (min (e-1) (U.card-1)))

/-- Theorem4.9 as literal vanishing of total-degree submodules of genuine
derived Tor over the retained-variable polynomial rings. -/
theorem polymatroidal_iff_triangular_totalTor {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔ TotalTriangularTests (k := k) B d := by
  rw [polymatroidal_iff_triangular (k := k) hB hd hd2]
  simp only [RetainedTriangularTests,TotalTriangularTests,retainedLinearThrough_iff_totalTor]

/-- The displayed Tor-vanishing statement of Theorem4.2. -/
theorem polymatroidal_iff_degree_tests_totalTor {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔ TotalDegreeBoundedTests (k := k) B := by
  rw [polymatroidal_iff_degree_tests (k := k) hB hanti]
  simp only [DegreeBoundedTests,TotalDegreeBoundedTests,retainedLinearThrough_iff_totalTor]

/-- The equivalent smaller cutoff from Theorem4.2, with actual total Tor. -/
theorem polymatroidal_iff_degree_dimension_tests_totalTor {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔ TotalDegreeDimensionBoundedTests (k := k) B := by
  rw [polymatroidal_iff_degree_dimension_tests (k := k) hB hanti]
  simp only [DegreeDimensionBoundedTests,TotalDegreeDimensionBoundedTests,
    retainedLinearThrough_iff_totalTor]

end Characterizations

end
end CheckedCharacterizationsSource91

/-! ## Source: Characterizations.Strands.TotalDimension -/
section CheckedCharacterizationsSource92

/-! # Total Betti sums are dimensions of the actual total-degree derived-Tor submodules -/
noncomputable section
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {k : Type u} [Field k]

lemma finrank_finset_sup_of_independent {ι M : Type*} [AddCommGroup M] [Module k M]
    (P : ι → Submodule k M) [∀ a, FiniteDimensional k (P a)]
    (h : iSupIndep P) (s : Finset ι) :
    Module.finrank k ↥(s.sup P) = ∑ a ∈ s, Module.finrank k (P a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha]
    have hd : Disjoint (P a) (s.sup P) := by
      rw [Finset.sup_eq_iSup]
      exact h.disjoint_biSup (y := (s : Set ι)) ha
    have hh := Submodule.finrank_sup_add_finrank_inf_eq (P a) (s.sup P)
    rw [hd.eq_bot, finrank_bot, add_zero, ih] at hh
    exact hh

variable {V : Type u} [Fintype V] [LinearOrder V]

theorem totalDegreeTor_eq_finset_sup (B : Family V) (i j : ℕ) :
    totalDegreeTor (k := k) B i j =
      ((Finsupp.finite_of_degree_eq (σ := V) j).toFinset).sup
        (fun a => gradedTor (k := k) B a i) := by
  rw [Finset.sup_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    exact le_iSup_of_le a (le_iSup_of_le (by simpa using ha) le_rfl)
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    exact le_iSup_of_le a (le_iSup_of_le (by simpa using ha) le_rfl)

theorem totalDegreeTor_finite (B : Family V) (i j : ℕ) :
    FiniteDimensional k (totalDegreeTor (k := k) B i j) := by
  rw [totalDegreeTor_eq_finset_sup]
  infer_instance

/-- The usual total-degree numerical Betti number, with its dimension meaning
proved from the independent internal multigrading of genuine derived Tor. -/
theorem finrank_totalDegreeTor (B : Family V) (i j : ℕ) :
    Module.finrank k (totalDegreeTor (k := k) B i j) =
      totalBettiNumber (k := k) B i j := by
  rw [totalDegreeTor_eq_finset_sup]
  exact finrank_finset_sup_of_independent (fun a => gradedTor (k := k) B a i)
    (gradedTor_independent B i) _

end Characterizations.Strands

end
end CheckedCharacterizationsSource92

/-! ## Source: Characterizations.Strands.DeletedGeneratorTheorem -/
section CheckedCharacterizationsSource93

/-! # The complete deleted-generator proposition, including its localized ideals -/
noncomputable section
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem deletedVeronese_proper_localization (a : Exponent V) (ha : 2 ≤ a.support.card)
    (U : Finset V) (hU : U ⊂ Finset.univ) :
    monomialLocalization k (monomialIdeal k (deletedVeronese a)) U = ⊤ := by
  obtain ⟨j, _, hj⟩ := Finset.exists_of_ssubset hU
  rw [monomialLocalization_eq]
  have he : localFamily (deletedVeronese a) U = {0} :=
    Isolators.localFamily_eq_zero_of_purePower ∅ U a ha j (Finset.notMem_empty _) hj
  rw [he, Ideal.eq_top_iff_one]
  have h : MvPolynomial.monomial (0 : Exponent U) (1 : k) ∈
      monomialIdeal k ({0} : Family U) := (monomial_mem_iff _ _).mpr
        ⟨0, Finset.mem_singleton_self _, le_rfl⟩
  simpa using h

/-- Proposition 4.3: every proper localization is the unit ideal, every
nonlinear fine Betti entry is exactly zero or one as stated, and the total
nonlinear strand has the exact binomial coefficient (including out-of-range zero). -/
theorem deleted_generator_nonlinear_strand (a : Exponent V) (ha : 2 ≤ a.support.card) :
    (∀ U : Finset V, U ⊂ Finset.univ →
      monomialLocalization k (monomialIdeal k (deletedVeronese a)) U = ⊤) ∧
    (∀ i b, b.degree ≠ a.degree+i →
      bettiNumber (k := k) (deletedVeronese a) b i =
        if ∃ T : Finset V, a.support ⊆ T ∧ T.card=i+1 ∧ b=a+faceExponent T
          then 1 else 0) ∧
    (∀ i, totalBettiNumber (k := k) (deletedVeronese a) i (a.degree+i+1) =
      if a.support.card ≤ i+1 then
        Nat.choose (Fintype.card V-a.support.card) (i+1-a.support.card) else 0) ∧
    (∀ i j, j ≠ a.degree+i → j ≠ a.degree+i+1 →
      totalBettiNumber (k := k) (deletedVeronese a) i j = 0) := by
  refine ⟨deletedVeronese_proper_localization a ha, ?_,
    deletedVeronese_total_nonlinear a ha, deletedVeronese_total_other a ha⟩
  intro i b hb
  simpa only [mem_exceptionalDegrees] using deletedVeronese_betti_off_linear a b ha i hb

theorem deletedVeronese_full_support (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (hfull : a.support = Finset.univ) (i : ℕ) (hoff : b.degree ≠ a.degree+i) :
    bettiNumber (k := k) (deletedVeronese a) b i =
      if i+1=Fintype.card V ∧ b=a+faceExponent Finset.univ then 1 else 0 := by
  rw [deletedVeronese_betti_off_linear a b ha i hoff]
  have he : b ∈ exceptionalDegrees a i ↔
      i+1=Fintype.card V ∧ b=a+faceExponent Finset.univ := by
    rw [mem_exceptionalDegrees]
    constructor
    · rintro ⟨T, hT, hc, he⟩
      have hTu : T = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ _) (hfull ▸ hT)
      subst T
      exact ⟨by simpa using hc.symm, he⟩
    · rintro ⟨hc, he⟩
      exact ⟨Finset.univ, Finset.subset_univ _, by simpa using hc.symm, he⟩
  simp only [he]

end Characterizations.Strands

end
end CheckedCharacterizationsSource93

/-! ## Source: Characterizations.DerivedTorOrder -/
section CheckedCharacterizationsSource94

/-! # The manuscript's `Tor(I,k)` and its genuine homogeneous submodules

The existing Koszul construction resolves the residue module in the first tensor
factor. Tensor braiding identifies that derived functor with Mathlib's `Tor(I,k)`,
which resolves the same residue module in the second factor. This does not use or
assume a balance theorem between two different projective resolutions.
-/
noncomputable section
namespace Characterizations
open CategoryTheory CategoryTheory.MonoidalCategory CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V]

section Ring
variable [CommRing k]

def tensorBraidingDerivedIso (M : ModuleCat.{u} (MvPolynomial V k)) (i : ℕ) :
    (((tensoringRight _).obj M).leftDerived i) ≅
      (((tensoringLeft _).obj M).leftDerived i) where
  hom := NatTrans.leftDerived (BraidedCategory.tensorLeftIsoTensorRight M).inv i
  inv := NatTrans.leftDerived (BraidedCategory.tensorLeftIsoTensorRight M).hom i
  hom_inv_id := by
    rw [← NatTrans.leftDerived_comp, Iso.inv_hom_id, NatTrans.leftDerived_id]
  inv_hom_id := by
    rw [← NatTrans.leftDerived_comp, Iso.hom_inv_id, NatTrans.leftDerived_id]

/-- The exact chain isomorphism inducing the change of tensor order. -/
def tensorBraidingChainIso (M : ModuleCat.{u} (MvPolynomial V k))
    (P : ChainComplex (ModuleCat.{u} (MvPolynomial V k)) ℕ) :
    (((tensoringRight _).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P ≅
      (((tensoringLeft _).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P :=
  (NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight M).symm
    (ComplexShape.down ℕ)).app P

/-- In each chain degree the map merely switches the two tensor factors;
in particular both their polynomial and exterior degrees are retained. -/
@[simp] theorem tensorBraidingChainIso_tmul
    (M : ModuleCat.{u} (MvPolynomial V k))
    (P : ChainComplex (ModuleCat.{u} (MvPolynomial V k)) ℕ)
    (j : ℕ) (x : P.X j) (m : M) :
    (tensorBraidingChainIso M P).hom.f j (x ⊗ₜ[MvPolynomial V k] m) =
      m ⊗ₜ[MvPolynomial V k] x := rfl

/-- Compatibility with the actual homology map of the displayed chain braiding. -/
theorem tensorBraidingDerivedIso_eq_homology
    {X : ModuleCat.{u} (MvPolynomial V k)} (P : ProjectiveResolution X)
    (M : ModuleCat.{u} (MvPolynomial V k)) (i : ℕ) :
    (tensorBraidingDerivedIso M i).hom.app X =
      (P.isoLeftDerivedObj ((tensoringRight _).obj M) i).hom ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).map
          (tensorBraidingChainIso M P.complex).hom ≫
        (P.isoLeftDerivedObj ((tensoringLeft _).obj M) i).inv :=
  P.leftDerived_app_eq (BraidedCategory.tensorLeftIsoTensorRight M).inv i

/-- The manuscript's derived Tor with the actual coefficient ring carrying
the polynomial action by evaluation at zero. -/
def paperTor (M : ModuleCat.{u} (MvPolynomial V k)) (i : ℕ) :=
  ((Tor (ModuleCat (MvPolynomial V k)) i).obj M).obj
    (residueCoefficientModule (V := V) (k := k))

/-- Canonical agreement with the exact argument ordering `Tor_i(M,k)`. -/
def polynomialTorOrderIso (M : ModuleCat.{u} (MvPolynomial V k)) (i : ℕ) :
    finitePolynomialTor i M ≅ paperTor M i :=
  (tensorBraidingDerivedIso M i).app
      (ModuleCat.of (MvPolynomial V k) (FiniteResidue V k)) ≪≫
    ((Tor (ModuleCat (MvPolynomial V k)) i).obj M).mapIso residueCoefficientIso

def coefficientTorOrderIso (B : Family V) (i : ℕ) :=
  (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).mapIso
    (polynomialTorOrderIso (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i)

end Ring

section Field
variable [Field k]

/-- The fine-degree piece transported through the canonical derived tensor braiding. -/
def paperGradedTor (B : Family V) (a : Exponent V) (i : ℕ) :=
  (gradedTor (k := k) B a i).map (coefficientTorOrderIso (k := k) B i).hom.hom

/-- The total-degree piece inside Mathlib's literal `Tor_i(I,k)`. -/
def paperTotalDegreeTor (B : Family V) (i j : ℕ) :=
  (totalDegreeTor (k := k) B i j).map (coefficientTorOrderIso (k := k) B i).hom.hom

theorem paperTotalDegreeTor_eq_sum (B : Family V) (i j : ℕ) :
    paperTotalDegreeTor (k := k) B i j =
      ⨆ (a : Exponent V) (_ : a.degree = j), paperGradedTor (k := k) B a i := by
  simp only [paperTotalDegreeTor, totalDegreeTor, Submodule.map_iSup, paperGradedTor]

theorem paperGradedTor_finrank (B : Family V) (a : Exponent V) (i : ℕ) :
    Module.finrank k (paperGradedTor (k := k) B a i) = bettiNumber (k := k) B a i :=
  (coefficientTorOrderIso (k := k) B i).toLinearEquiv.finrank_map_eq _

theorem paperGradedTor_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (paperGradedTor (k := k) B a i) := by
  let e := (coefficientTorOrderIso (k := k) B i).toLinearEquiv.submoduleMap
    (gradedTor (k := k) B a i)
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

theorem paperTotalDegreeTor_finrank (B : Family V) (i j : ℕ) :
    Module.finrank k (paperTotalDegreeTor (k := k) B i j) =
      Strands.totalBettiNumber (k := k) B i j := by
  exact ((coefficientTorOrderIso (k := k) B i).toLinearEquiv.finrank_map_eq _).trans
    (Strands.finrank_totalDegreeTor B i j)

theorem paperTotalDegreeTor_finite (B : Family V) (i j : ℕ) :
    FiniteDimensional k (paperTotalDegreeTor (k := k) B i j) := by
  letI := Strands.totalDegreeTor_finite (k := k) B i j
  let e := (coefficientTorOrderIso (k := k) B i).toLinearEquiv.submoduleMap
    (totalDegreeTor (k := k) B i j)
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

theorem paperTotalDegreeTor_eq_bot_iff (B : Family V) (i j : ℕ) :
    paperTotalDegreeTor (k := k) B i j = ⊥ ↔ totalDegreeTor (k := k) B i j = ⊥ :=
  Submodule.map_eq_bot_iff (e := (coefficientTorOrderIso (k := k) B i).toLinearEquiv)

/-- No part of `Tor(I,k)` is lost by the transported total grading. -/
theorem iSup_paperTotalDegreeTor (B : Family V) (i : ℕ) :
    (⨆ j : ℕ, paperTotalDegreeTor (k := k) B i j) = ⊤ := by
  simp only [paperTotalDegreeTor, ← Submodule.map_iSup, iSup_totalDegreeTor]
  exact (Submodule.map_eq_top_iff
    (e := (coefficientTorOrderIso (k := k) B i).toLinearEquiv)).mpr rfl

/-- The paper's initial-segment condition with its literal derived tensor order. -/
def PaperRetainedTorLinearThrough (B : Family V) (U : Finset V) (e t : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ t → ∀ j : ℕ, j ≠ e+i →
    paperTotalDegreeTor (k := k) (localFamily B U) i j = ⊥

theorem paperRetainedTorLinearThrough_iff (B : Family V) (U : Finset V) (e t : ℕ) :
    PaperRetainedTorLinearThrough (k := k) B U e t ↔
      RetainedTorLinearThrough (k := k) B U e t := by
  simp only [PaperRetainedTorLinearThrough, RetainedTorLinearThrough,
    paperTotalDegreeTor_eq_bot_iff]

/-- Theorem 4.2 with actual `Tor_i(I_U,k)` over `k[U]`. -/
theorem polymatroidal_iff_degree_tests_paperTor {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔
    ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
      (0 < e → PaperRetainedTorLinearThrough (k := k) B U e (e-1)) := by
  simp only [paperRetainedTorLinearThrough_iff]
  exact polymatroidal_iff_degree_tests_totalTor hB hanti

/-- The equivalent degree-and-dimension cutoff in Theorem 4.2. -/
theorem polymatroidal_iff_degree_dimension_tests_paperTor {B : Family V}
    (hB : B.Nonempty) (hanti : Antichain B) : IsPolymatroidal B ↔
    ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
      (0 < e → PaperRetainedTorLinearThrough (k := k) B U e (min (e-1) (U.card-1))) := by
  simp only [paperRetainedTorLinearThrough_iff]
  exact polymatroidal_iff_degree_dimension_tests_totalTor hB hanti

/-- Theorem 4.9 in exactly the manuscript's derived tensor order. -/
theorem polymatroidal_iff_triangular_paperTor {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) : IsPolymatroidal B ↔
    ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      ∃ e, Equigenerated (localFamily B U) e ∧
        (0 < e → PaperRetainedTorLinearThrough (k := k) B U e
          (min (e-1) (min (d-1-(Fintype.card V-U.card)) (U.card-1)))) := by
  simp only [paperRetainedTorLinearThrough_iff]
  exact polymatroidal_iff_triangular_totalTor hB hd hd2

/-- Proposition 4.3's total nonlinear strand as a dimension inside `Tor_i(I,k)`. -/
theorem deleted_generator_paperTor_finrank (a : Exponent V)
    (ha : 2 ≤ a.support.card) (i : ℕ) :
    Module.finrank k (paperTotalDegreeTor (k := k) (deletedVeronese a) i (a.degree+i+1)) =
      if a.support.card ≤ i+1 then
        Nat.choose (Fintype.card V-a.support.card) (i+1-a.support.card) else 0 := by
  rw [paperTotalDegreeTor_finrank]
  exact Strands.deletedVeronese_total_nonlinear a ha i

/-- Proposition 4.3's complete nonlinear fine strand inside literal `Tor_i(I,k)`. -/
theorem deleted_generator_paperGradedTor_finrank (a b : Exponent V)
    (ha : 2 ≤ a.support.card) (i : ℕ) (hoff : b.degree ≠ a.degree+i) :
    Module.finrank k (paperGradedTor (k := k) (deletedVeronese a) b i) =
      if ∃ T : Finset V, a.support ⊆ T ∧ T.card=i+1 ∧ b=a+faceExponent T
        then 1 else 0 := by
  rw [paperGradedTor_finrank]
  exact (Strands.deleted_generator_nonlinear_strand (k := k) a ha).2.1 i b hoff

end Field
end Characterizations

end
end CheckedCharacterizationsSource94

/-! ## Source: Characterizations.GradedRevlex -/
section CheckedCharacterizationsSource95

/-! # Graded reverse lexicographic order as a genuine Mathlib monomial order -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def GradedReverse (V : Type*) := Exponent V

instance : AddCommMonoid (GradedReverse V) := inferInstanceAs (AddCommMonoid (Exponent V))

def gradedReverseEquiv : Exponent V ≃+ GradedReverse V := AddEquiv.refl _

def gradedReverseUnderlying (a : GradedReverse V) : Exponent V := a

section Ordered
variable [LinearOrder V]

def gradedReverseKey (a : GradedReverse V) : Lex (ℕ × (Colex (Exponent V))ᵒᵈ) :=
  toLex ((gradedReverseUnderlying a).degree, OrderDual.toDual (toColex (gradedReverseUnderlying a)))

theorem gradedReverseKey_injective : Function.Injective (gradedReverseKey (V := V)) := by
  intro a b he
  exact congrArg (fun x : Lex (ℕ × (Colex (Exponent V))ᵒᵈ) =>
    (ofColex (OrderDual.ofDual ((ofLex x).2)) : Exponent V)) he

instance : LinearOrder (GradedReverse V) :=
  LinearOrder.lift' gradedReverseKey gradedReverseKey_injective

theorem gradedReverse_lt_iff (a b : GradedReverse V) :
    a < b ↔ (gradedReverseUnderlying a).degree < (gradedReverseUnderlying b).degree ∨
      ((gradedReverseUnderlying a).degree = (gradedReverseUnderlying b).degree ∧
        toColex (gradedReverseUnderlying b) < toColex (gradedReverseUnderlying a)) := by
  change gradedReverseKey a < gradedReverseKey b ↔ _
  simp only [gradedReverseKey, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual]

theorem gradedReverse_le_iff (a b : GradedReverse V) :
    a ≤ b ↔ (gradedReverseUnderlying a).degree < (gradedReverseUnderlying b).degree ∨
      ((gradedReverseUnderlying a).degree = (gradedReverseUnderlying b).degree ∧
        toColex (gradedReverseUnderlying b) ≤ toColex (gradedReverseUnderlying a)) := by
  change gradedReverseKey a ≤ gradedReverseKey b ↔ _
  simp only [gradedReverseKey, Prod.Lex.toLex_le_toLex, OrderDual.toDual_le_toDual]

instance : IsOrderedAddMonoid (GradedReverse V) where
  add_le_add_left a b h c := by
    rw [gradedReverse_le_iff] at h ⊢
    change (gradedReverseUnderlying a + gradedReverseUnderlying c).degree < (gradedReverseUnderlying b + gradedReverseUnderlying c).degree ∨
      ((gradedReverseUnderlying a + gradedReverseUnderlying c).degree = (gradedReverseUnderlying b + gradedReverseUnderlying c).degree ∧
        toColex (gradedReverseUnderlying b + gradedReverseUnderlying c) ≤ toColex (gradedReverseUnderlying a + gradedReverseUnderlying c))
    simpa only [map_add, toColex_add, add_lt_add_iff_right, add_left_inj,
      add_le_add_iff_right] using h

theorem gradedReverse_degree_mono :
    Monotone (fun a : GradedReverse V => (gradedReverseUnderlying a).degree) := by
  intro a b h
  rcases (gradedReverse_le_iff a b).mp h with h | h
  · exact h.le
  · exact h.1.le

instance : WellFoundedLT (GradedReverse V) := by
  apply WellFounded.wellFoundedLT_iff_exists_minimal.mpr
  intro S hS
  obtain ⟨a, ha⟩ := hS
  let T : Set (GradedReverse V) :=
    {b | b ∈ S ∧ (gradedReverseUnderlying b).degree ≤ (gradedReverseUnderlying a).degree}
  have hfin : T.Finite := by
    change {b : Exponent V | b ∈ S ∧ b.degree ≤ (gradedReverseUnderlying a).degree}.Finite
    apply (Set.finite_Iic (constExponent (gradedReverseUnderlying a).degree)).subset
    intro b hb i
    exact (coordinate_le_degree b i).trans hb.2
  obtain ⟨b, hb, hmin⟩ := hfin.exists_minimal ⟨a, ha, le_rfl⟩
  refine ⟨b, hb.1, ?_⟩
  intro c hc hcb
  exact hmin ⟨hc, (gradedReverse_degree_mono hcb).trans hb.2⟩ hcb

def gradedRevlexMonomialOrder : MonomialOrder V where
  syn := GradedReverse V
  toSyn := gradedReverseEquiv
  toSyn_monotone a b hab := by
    apply (gradedReverse_le_iff _ _).mpr
    have hd := degree_mono hab
    rcases hd.lt_or_eq with hlt | he
    · exact Or.inl hlt
    · have hab' := eq_of_le_of_degree_eq hab he
      exact Or.inr ⟨he, by rw [hab']⟩

end Ordered

def variableGradedRevlexOrder (o : VariableOrder V) : MonomialOrder V :=
  letI := variableLinearOrder o
  gradedRevlexMonomialOrder

theorem variableGradedRevlexOrder_decreasing_iff (o : VariableOrder V)
    (a b : Exponent V) (hd : a.degree = b.degree) :
    (variableGradedRevlexOrder o).toSyn b < (variableGradedRevlexOrder o).toSyn a ↔
      variableRevlex o a b := by
  letI := variableLinearOrder o
  change gradedReverseEquiv b < gradedReverseEquiv a ↔ _
  rw [gradedReverse_lt_iff]
  change (b.degree < a.degree ∨ b.degree = a.degree ∧ toColex a < toColex b) ↔ _
  simp only [hd, lt_self_iff_false, true_and, false_or, Finsupp.Colex.lt_iff]
  exact ⟨fun ⟨i, he, hi⟩ => ⟨i, hi, he⟩, fun ⟨i, hi, he⟩ => ⟨i, he, hi⟩⟩

end Characterizations

end
end CheckedCharacterizationsSource95

/-! ## Source: Characterizations.Strands.FiniteLength -/
section CheckedCharacterizationsSource96

/-! # Actual ideal quotients with finitely many missing monomials have finite length -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Strands
open Classical CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The actual module quotient J/(I∩J), written without choosing a complement. -/
abbrev idealDifferenceQuotient (B C : Family V) :=
  (monomialIdeal k C) ⧸ Submodule.comap (monomialIdeal k C).subtype (monomialIdeal k B)

theorem idealDifferenceQuotient_finite (B C : Family V)
    (hholes : {a : Exponent V | Contains C a ∧ ¬Contains B a}.Finite) :
    Module.Finite k (idealDifferenceQuotient (k := k) B C) := by
  let J := monomialIdeal k C
  let N : Submodule (MvPolynomial V k) J := Submodule.comap J.subtype (monomialIdeal k B)
  let Q := J ⧸ N
  let H := {a : Exponent V // Contains C a ∧ ¬Contains B a}
  letI : Fintype H := hholes.fintype
  let q : J →ₗ[k] Q := N.mkQ.restrictScalars k
  let hvec : H → Q := fun a => q (monomialBasis C ⟨a.val, a.property.1⟩)
  let f : (H →₀ k) →ₗ[k] Q := Finsupp.linearCombination k hvec
  have hbas (a : {a : Exponent V // Contains C a}) :
      q (monomialBasis C a) ∈ LinearMap.range f := by
    by_cases ha : Contains B a.val
    · have hz : q (monomialBasis C a) = 0 := by
        apply (Submodule.Quotient.mk_eq_zero N).mpr
        change (monomialBasis C a).val ∈ monomialIdeal k B
        rw [monomialBasis_val, monomial_mem_iff]
        exact ha
      rw [hz]
      exact Submodule.zero_mem _
    · let a' : H := ⟨a.val, a.property, ha⟩
      refine ⟨Finsupp.single a' 1, ?_⟩
      simp only [f, Finsupp.linearCombination_single, one_smul]
      rfl
  have hspan (x : J) : q x ∈ LinearMap.range f := by
    have hx : x ∈ Submodule.span k (Set.range (monomialBasis (k := k) C)) := by
      rw [(monomialBasis (k := k) C).span_eq]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hbas a
    | zero => simpa using (Submodule.zero_mem (LinearMap.range f))
    | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
    | smul c x hx ih => simpa using Submodule.smul_mem _ c ih
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨x, hx⟩ := N.mkQ_surjective z
    obtain ⟨y, hy⟩ := hspan x
    exact ⟨y, hy.trans hx⟩
  exact Module.Finite.of_surjective f hf

theorem idealDifferenceQuotient_finiteLength (B C : Family V)
    (hholes : {a : Exponent V | Contains C a ∧ ¬Contains B a}.Finite) :
    IsFiniteLength (MvPolynomial V k) (idealDifferenceQuotient (k := k) B C) := by
  letI := idealDifferenceQuotient_finite (k := k) B C hholes
  apply isFiniteLength_iff_isNoetherian_isArtinian.mpr
  exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

end Characterizations.Strands

end
end CheckedCharacterizationsSource96

/-! ## Source: Characterizations.MinimalLocal -/
section CheckedCharacterizationsSource97

/-! # Proposition 4.1 with the actual integral closure and actual finite-length quotient -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem thickening_zero (B : Family V) : thickening B 0 = B := by
  ext a
  constructor
  · intro ha
    obtain ⟨⟨b,c⟩,hbc,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb,hc⟩ := Finset.mem_product.mp hbc
    have hc0 : c = 0 := (Finsupp.degree_eq_zero_iff c).mp ((mem_degreeFamily 0 c).mp hc)
    simpa only [hc0,add_zero] using hb
  · intro ha
    exact Finset.mem_image.mpr ⟨(a,0),Finset.mem_product.mpr ⟨ha,by simp⟩,by simp⟩

theorem minimal_local_closure_finiteLength {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    IsPolymatroidal (lowerBaseFamily (lowerRank B) d) ∧
      monomialIdeal k B ≤ monomialIdeal k (lowerBaseFamily (lowerRank B) d) ∧
      ({f : MvPolynomial V k | IntegralOverIdeal (monomialIdeal k B) f} =
        (monomialIdeal k (lowerBaseFamily (lowerRank B) d) : Set (MvPolynomial V k))) ∧
      IsFiniteLength (MvPolynomial V k)
        (Strands.idealDifferenceQuotient (k := k) B (lowerBaseFamily (lowerRank B) d)) := by
  have hl := locallyEquigenerated_of_proper_polymatroidal hd hloc
  refine ⟨canonicalLowerBases_polymatroidal hB hl hd,?_,
    integralClosure_set_eq hB hd.antichain hl hd,?_⟩
  · apply Ideal.span_mono
    rintro f ⟨a,ha,rfl⟩
    exact ⟨a,subset_lowerBaseFamily hd ha,rfl⟩
  · apply Strands.idealDifferenceQuotient_finiteLength
    have he : {a : Exponent V | Contains (lowerBaseFamily (lowerRank B) d) a ∧ ¬Contains B a} =
        holeSet B := by
      ext a
      simp only [Set.mem_setOf_eq,contains_canonicalLowerBases_iff hB hl hd,holeSet]
    rw [he]
    exact holeSet_finite hB hd hloc

/-- The "in particular" statement in4.1, including the integrally closed case
where the least power and regularity difference are both zero. -/
theorem least_polymatroidal_power_eq_regularity_difference {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    ∃ r : ℕ, IsTorRegularity (k := k) B r ∧
      IsLeast {q : ℕ | IsPolymatroidal (thickening B q)} (r-d) := by
  by_cases hclosed : B = lowerBaseFamily (lowerRank B) d
  · have hl := locallyEquigenerated_of_proper_polymatroidal hd hloc
    have hp : IsPolymatroidal B := by
      conv_rhs => rw [hclosed]
      exact canonicalLowerBases_polymatroidal hB hl hd
    refine ⟨d,polymatroidal_torRegularity hB hd hp,?_⟩
    simp only [Nat.sub_self]
    exact ⟨by simpa only [Set.mem_setOf_eq,thickening_zero] using hp,fun _ _ => Nat.zero_le _⟩
  · obtain ⟨t,ht,hmax,hdt,hreg,hq⟩ := minimal_local_obstruction (k := k) hB hd hloc hclosed
    exact ⟨t+1,hreg,hq⟩

end Characterizations

end
end CheckedCharacterizationsSource97

/-! ## Source: Characterizations.Resolution.Specialize -/
section CheckedCharacterizationsSource98

/-! Exact specialization of actual finite free matrices along a regular quotient. -/

noncomputable section
namespace Characterizations.Resolution
open Classical Finset
universe u v w z
variable {R S : Type u} [CommRing R] [CommRing S]
  {J : Type v} {L : Type w} {M : Type z}
  [Fintype J] [Fintype L] [Fintype M]

lemma free_apply_eq_sum (f : (J → R) →ₗ[R] (L → R)) (x : J → R) (a : L) :
    f x a = ∑ b, x b * f (Pi.single b 1) a := by
  have hx : x = ∑ b, x b • Pi.single b (1 : R) := by
    funext b
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp

def specialize (φ : R →+* S) (f : (J → R) →ₗ[R] (L → R)) :
    (J → S) →ₗ[S] (L → S) where
  toFun x a := ∑ b, x b * φ (f (Pi.single b 1) a)
  map_add' x y := by ext a; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by ext a; simp [mul_assoc, Finset.mul_sum]

lemma specialize_apply (φ : R →+* S) (f : (J → R) →ₗ[R] (L → R))
    (x : J → S) (a : L) : specialize φ f x a =
      ∑ b, x b * φ (f (Pi.single b 1) a) := rfl

@[simp] lemma specialize_single (φ : R →+* S) (f : (J → R) →ₗ[R] (L → R))
    (b : J) (a : L) : specialize φ f (Pi.single b 1) a = φ (f (Pi.single b 1) a) := by
  simp [specialize, Pi.single_apply]

lemma specialize_map (φ : R →+* S) (f : (J → R) →ₗ[R] (L → R)) (x : J → R) :
    specialize φ f (fun j => φ (x j)) = fun a => φ (f x a) := by
  ext a
  rw [specialize_apply, free_apply_eq_sum]
  simp

lemma specialize_exact (φ : R →+* S) (hφ : Function.Surjective φ) (t : R)
    (ht : φ t = 0) (hker : ∀ a, φ a = 0 → ∃ b, a = t * b)
    (f : (J → R) →ₗ[R] (L → R)) (g : (L → R) →ₗ[R] (M → R))
    (hex : LinearMap.range f = LinearMap.ker g)
    (hsat : ∀ y : M → R, t • y ∈ LinearMap.range g → y ∈ LinearMap.range g) :
    LinearMap.range (specialize φ f) = LinearMap.ker (specialize φ g) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : J → R, (fun j => φ (y j)) = x := by
      choose y hy using fun j => hφ (x j)
      exact ⟨y, funext hy⟩
    rw [← hy, specialize_map, LinearMap.mem_ker, specialize_map]
    have hf : g (f y) = 0 := LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self f y)
    ext a
    simp [hf]
  · intro hz
    obtain ⟨x, hx⟩ : ∃ x : L → R, (fun j => φ (x j)) = z := by
      choose x hx using fun j => hφ (z j)
      exact ⟨x, funext hx⟩
    have hg : ∀ a, φ (g x a) = 0 := by
      have h := LinearMap.mem_ker.mp hz
      rw [← hx, specialize_map] at h
      exact congrFun h
    choose y hy using fun a => hker (g x a) (hg a)
    have hgy : g x = t • y := by ext a; exact hy a
    obtain ⟨w, hw⟩ := hsat y ⟨x, hgy⟩
    have hcycle : x - t • w ∈ LinearMap.ker g := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hw, hgy, sub_self]
    obtain ⟨q, hq⟩ := hex.symm ▸ hcycle
    refine ⟨fun j => φ (q j), ?_⟩
    rw [specialize_map, hq]
    ext a
    simpa [ht] using congrFun hx a

lemma saturated_range_of_exact (f : (J → R) →ₗ[R] (L → R))
    (g : (L → R) →ₗ[R] (M → R))
    (hex : LinearMap.range f = LinearMap.ker g) (t : R)
    (ht : Function.Injective (fun a : R => t * a)) :
    ∀ y : L → R, t • y ∈ LinearMap.range f → y ∈ LinearMap.range f := by
  intro y hy
  rw [hex, LinearMap.mem_ker] at hy ⊢
  rw [map_smul] at hy
  ext a
  apply ht
  simpa using congrFun hy a

def scalarFree (f : (J → R) →ₗ[R] R) : (J → R) →ₗ[R] (Unit → R) :=
  LinearMap.pi (fun _ => f)

@[simp] lemma scalarFree_apply (f : (J → R) →ₗ[R] R) (x : J → R) (a : Unit) :
    scalarFree f x a = f x := rfl

@[simp] lemma scalarFree_ker (f : (J → R) →ₗ[R] R) :
    LinearMap.ker (scalarFree f) = LinearMap.ker f := by
  ext x
  simp only [LinearMap.mem_ker, funext_iff, scalarFree_apply, Pi.zero_apply, implies_true]
  exact ⟨fun h => h (), fun h _ => h⟩

def specializeScalar (φ : R →+* S) (f : (J → R) →ₗ[R] R) : (J → S) →ₗ[S] S :=
  (LinearMap.proj ()).comp (specialize φ (scalarFree f))

@[simp] lemma specializeScalar_single (φ : R →+* S) (f : (J → R) →ₗ[R] R) (b : J) :
    specializeScalar φ f (Pi.single b 1) = φ (f (Pi.single b 1)) := by
  exact specialize_single φ (scalarFree f) b ()

lemma specializeScalar_map (φ : R →+* S) (f : (J → R) →ₗ[R] R) (x : J → R) :
    specializeScalar φ f (fun j => φ (x j)) = φ (f x) :=
  congrFun (specialize_map φ (scalarFree f) x) ()

lemma specializeScalar_ker (φ : R →+* S) (f : (J → R) →ₗ[R] R) :
    LinearMap.ker (specialize φ (scalarFree f)) =
      LinearMap.ker (specializeScalar φ f) := by
  ext x
  simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply]
  exact ⟨fun h => h (), fun h a => by cases a; exact h⟩

lemma specializeScalar_range (φ : R →+* S) (hφ : Function.Surjective φ)
    (f : (J → R) →ₗ[R] R) (I : Ideal R) (hf : LinearMap.range f = I) :
    LinearMap.range (specializeScalar φ f) = Ideal.map φ I := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨z,hz⟩ : ∃ z : J → R, (fun j => φ (z j)) = x := by
      choose z hz using fun j => hφ (x j)
      exact ⟨z,funext hz⟩
    rw [← hz,specializeScalar_map]
    exact Ideal.mem_map_of_mem φ (hf ▸ LinearMap.mem_range_self f z)
  · intro hy
    obtain ⟨z,hz,hzy⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hy
    obtain ⟨x,hx⟩ := hf.symm ▸ hz
    refine ⟨fun j => φ (x j),?_⟩
    rw [specializeScalar_map,hx,hzy]

end Characterizations.Resolution

end
end CheckedCharacterizationsSource98

/-! ## Source: Characterizations.Resolution.DeleteVariable -/
section CheckedCharacterizationsSource99

/-! Removing a polynomial variable from a genuine linear free resolution. -/
noncomputable section
namespace Characterizations.Resolution
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [CommRing k]

lemma killCompl_homogeneous {W : Type u} (f : W → V) (hf : Function.Injective f)
    {p : MvPolynomial V k} {d : ℕ} (hp : p.IsHomogeneous d) :
    (MvPolynomial.killCompl hf p).IsHomogeneous d := by
  intro a ha
  have hcoeff : p.coeff (a.mapDomain f) ≠ 0 := by
    simpa only [MvPolynomial.coeff_killCompl] using ha
  simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain]
    using hp hcoeff

lemma killCompl_kernel_of_range {W : Type u} (f : W → V) (hf : Function.Injective f)
    (j : V) (hrange : ∀ i, i ∈ Set.range f ↔ i ≠ j)
    (p : MvPolynomial V k) (hp : MvPolynomial.killCompl hf p = 0) :
    ∃ q, p = X j * q := by
  have hz : ∀ a : V →₀ ℕ, a j = 0 → p.coeff a = 0 := by
    intro a ha
    have hs : ↑a.support ⊆ Set.range f := by
      intro i hi
      apply (hrange i).mpr
      intro he
      subst i
      exact (Finsupp.mem_support_iff.mp hi) ha
    let b := a.comapDomain f hf.injOn
    have hb : b.mapDomain f = a := a.mapDomain_comapDomain f hf hs
    have hc := congrArg (fun q : MvPolynomial W k => q.coeff b) hp
    simpa [MvPolynomial.coeff_killCompl, hb] using hc
  have hdvd : X j ∣ p := by
    rw [p.as_sum]
    apply Finset.dvd_sum
    intro a ha
    rw [MvPolynomial.X_dvd_monomial]
    by_cases hj : a j = 0
    · exact Or.inl (hz a hj)
    · exact Or.inr hj
  obtain ⟨q,hq⟩ := hdvd
  exact ⟨q,hq⟩

abbrev Deleted (j : V) := {i : V // i ≠ j}

def deleteVariable (j : V) : MvPolynomial V k →ₐ[k] MvPolynomial (Deleted j) k :=
  MvPolynomial.killCompl (f := Subtype.val) Subtype.val_injective

lemma deleteVariable_surjective (j : V) : Function.Surjective (deleteVariable (k:=k) j) := by
  intro p
  exact ⟨MvPolynomial.rename Subtype.val p, MvPolynomial.killCompl_rename_app _ _⟩

@[simp] lemma deleteVariable_X (j : V) : deleteVariable (k:=k) j (X j) = 0 := by
  apply MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range
    Subtype.val_injective 1 (a := j)
  · simp
  · rintro ⟨i,hi⟩
    exact i.property hi

lemma deleteVariable_homogeneous (j : V) {p : MvPolynomial V k} {d : ℕ}
    (hp : p.IsHomogeneous d) : (deleteVariable j p).IsHomogeneous d := by
  intro a ha
  have hcoeff : p.coeff (a.mapDomain Subtype.val) ≠ 0 := by
    simpa only [deleteVariable, MvPolynomial.coeff_killCompl] using ha
  have h := hp hcoeff
  simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain] using h

lemma deleteVariable_kernel (j : V) (p : MvPolynomial V k)
    (hp : deleteVariable j p = 0) : ∃ q, p = X j * q := by
  have hz : ∀ a : V →₀ ℕ, a j = 0 → p.coeff a = 0 := by
    intro a ha
    have hs : ↑a.support ⊆ Set.range (Subtype.val : Deleted j → V) := by
      intro i hi
      have hne : i ≠ j := by
        intro he
        subst i
        exact (Finsupp.mem_support_iff.mp hi) ha
      exact ⟨⟨i,hne⟩,rfl⟩
    let b := a.comapDomain (Subtype.val : Deleted j → V) Subtype.val_injective.injOn
    have hb : b.mapDomain Subtype.val = a :=
      a.mapDomain_comapDomain (Subtype.val : Deleted j → V) Subtype.val_injective hs
    have hc := congrArg (fun q : MvPolynomial (Deleted j) k => q.coeff b) hp
    simpa [deleteVariable, MvPolynomial.coeff_killCompl, hb] using hc
  have hdvd : X j ∣ p := by
    rw [p.as_sum]
    apply Finset.dvd_sum
    intro a ha
    rw [MvPolynomial.X_dvd_monomial]
    by_cases hj : a j = 0
    · exact Or.inl (hz a hj)
    · exact Or.inr hj
  obtain ⟨q,hq⟩ := hdvd
  exact ⟨q,hq⟩

lemma monomialIdeal_variable_saturated [Fintype V] [DecidableEq V]
    (B : Family V) (j : V) (hs : ∀ a ∈ B, a j = 0)
    (p : MvPolynomial V k) (hp : X j * p ∈ monomialIdeal k B) :
    p ∈ monomialIdeal k B := by
  rw [mem_monomialIdeal_iff] at hp ⊢
  intro a ha
  have hsum : a + Finsupp.single j 1 ∈ (X j * p).support := by
    rw [MvPolynomial.mem_support_iff, add_comm a, MvPolynomial.coeff_X_mul]
    exact MvPolynomial.mem_support_iff.mp ha
  obtain ⟨b,hb,hba⟩ := hp _ hsum
  refine ⟨b,hb,fun i => ?_⟩
  by_cases hi : i = j
  · subst i
    rw [hs b hb]
    exact Nat.zero_le _
  · simpa [Finsupp.single_apply, hi] using hba i

end Characterizations.Resolution

end
end CheckedCharacterizationsSource99

/-! ## Source: Characterizations.Resolution.Descent -/
section CheckedCharacterizationsSource100

/-! Genuine linear free resolutions descend along a variable regular on the ideal quotient. -/
noncomputable section
namespace Characterizations
open Classical Resolution MvPolynomial
universe u
variable {V k : Type u} [CommRing k]

namespace LinearResolution
variable {I : Ideal (MvPolynomial V k)} {d : ℕ} (P : LinearResolution I d)

private lemma augmentation_variable_saturated (j : V)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    ∀ y : Unit → MvPolynomial V k,
      (X j : MvPolynomial V k) • y ∈ LinearMap.range (scalarFree P.augmentation) →
        y ∈ LinearMap.range (scalarFree P.augmentation) := by
  intro y hy
  obtain ⟨x,hx⟩ := hy
  have hmul : X j * y () ∈ I := by
    have hm : P.augmentation x ∈ I := (P.augmentationToIdeal x).property
    have he := congrFun hx ()
    change P.augmentation x = X j * y () at he
    rwa [← he]
  have hyI : y () ∈ LinearMap.range P.augmentation := by
    rw [P.augmentation_range]
    exact hI (y ()) hmul
  obtain ⟨z,hz⟩ := hyI
  refine ⟨z,?_⟩
  funext a
  cases a
  exact hz

/-- Evaluation at zero in one variable preserves exactness whenever that
variable is regular on the quotient by the resolved ideal. The resulting
object is again a literal exact complex of finite free modules. -/
def specializeQuotient {W : Type u}
    (φ : MvPolynomial V k →ₐ[k] MvPolynomial W k)
    (hφ : Function.Surjective φ) (j : V) (ht : φ (X j) = 0)
    (hker : ∀ p, φ p = 0 → ∃ q, p = X j * q)
    (hhom : ∀ {p : MvPolynomial V k} {d}, p.IsHomogeneous d → (φ p).IsHomogeneous d)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    LinearResolution (Ideal.map φ.toRingHom I) d where
  Index := P.Index
  finite := P.finite
  differential n := specialize φ.toRingHom (P.differential n)
  augmentation := specializeScalar φ.toRingHom P.augmentation
  augmentation_range := specializeScalar_range _ hφ
    P.augmentation I P.augmentation_range
  exact_zero := by
    have h := specialize_exact φ.toRingHom hφ (X j) ht
      hker (P.differential 0) (scalarFree P.augmentation)
      (by simpa only [scalarFree_ker] using P.exact_zero)
      (P.augmentation_variable_saturated j hI)
    exact h.trans (specializeScalar_ker _ P.augmentation)
  exact_succ n := by
    apply specialize_exact φ.toRingHom hφ (X j) ht hker _ _ (P.exact_succ n)
    cases n with
    | zero =>
      exact saturated_range_of_exact (P.differential 0) (scalarFree P.augmentation)
        (by simpa only [scalarFree_ker] using P.exact_zero) (X j)
        (MvPolynomial.isRegular_X.left)
    | succ n =>
      exact saturated_range_of_exact (P.differential (n+1)) (P.differential n)
        (P.exact_succ n) (X j) (MvPolynomial.isRegular_X.left)
  linear n := by
    intro a b
    rw [specialize_single]
    exact hhom (P.linear n a b)
  augmentation_homogeneous b := by
    rw [specializeScalar_single]
    exact hhom (P.augmentation_homogeneous b)

def deleteVariable (j : V)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    LinearResolution (Ideal.map (Resolution.deleteVariable (k:=k) j).toRingHom I) d :=
  P.specializeQuotient (Resolution.deleteVariable j) (deleteVariable_surjective j)
    j (deleteVariable_X j) (deleteVariable_kernel j)
    (deleteVariable_homogeneous j) hI

def descendAlong {W : Type u} (f : W → V) (hf : Function.Injective f)
    (j : V) (hrange : ∀ i, i ∈ Set.range f ↔ i ≠ j)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    LinearResolution (Ideal.map (MvPolynomial.killCompl hf).toRingHom I) d := by
  apply P.specializeQuotient (MvPolynomial.killCompl hf)
    (fun p => ⟨MvPolynomial.rename f p,MvPolynomial.killCompl_rename_app hf p⟩)
    j ?_ (killCompl_kernel_of_range f hf j hrange) (killCompl_homogeneous f hf) hI
  apply MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range hf 1 (a:=j)
  · simp
  · simpa only [hrange, ne_eq, not_not] using (rfl : j = j)

end LinearResolution

theorem HasLinearResolution.deleteVariable
    {I : Ideal (MvPolynomial V k)} (h : HasLinearResolution I) (j : V)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    HasLinearResolution (Ideal.map (Resolution.deleteVariable (k:=k) j).toRingHom I) := by
  obtain ⟨d,⟨P⟩⟩ := h
  exact ⟨d,⟨P.deleteVariable j hI⟩⟩

end Characterizations

end
end CheckedCharacterizationsSource100

/-! ## Source: Characterizations.Resolution.LocalizationDescentData -/
section CheckedCharacterizationsSource101

/-! Exact retained-variable data for localization descent. -/

noncomputable section

namespace Characterizations.Resolution

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {U W : Finset V}

def retainedInclusion (hUW : U ⊆ W) : U → W := fun i => ⟨i.val, hUW i.property⟩

theorem retainedInclusion_injective (hUW : U ⊆ W) :
    Function.Injective (retainedInclusion hUW) := by
  intro i j h
  exact Subtype.ext (congrArg (fun x : W => x.val) h)

theorem extendExponent_mapDomain_retained (hUW : U ⊆ W) (a : Exponent U) :
    extendExponent W (a.mapDomain (retainedInclusion hUW)) = extendExponent U a := by
  simp only [extendExponent, Finsupp.extendDomain_eq_embDomain_subtype,
    Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  rfl

/-- Equality of the ambient localized families is precisely extension of the
smaller retained-variable family by zero in the newly retained variables. -/
theorem localFamily_eq_image_of_localize_eq (B : Family V) (hUW : U ⊆ W)
    (he : localize B W = localize B U) :
    localFamily B W = (localFamily B U).image
      (fun a => a.mapDomain (retainedInclusion hUW)) := by
  apply Finset.image_injective (show Function.Injective (extendExponent W) from
    (extendExponentEmbedding W).injective)
  calc
    (localFamily B W).image (extendExponent W) = localize B W :=
      (localize_eq_extend_localFamily B W).symm
    _ = localize B U := he
    _ = ((localFamily B U).image (fun a => a.mapDomain (retainedInclusion hUW))).image
        (extendExponent W) := by
      rw [localize_eq_extend_localFamily, Finset.image_image]
      simp only [Function.comp_def, extendExponent_mapDomain_retained]

theorem localFamily_zero_of_localize_eq (B : Family V) (hUW : U ⊆ W)
    (he : localize B W = localize B U) (j : W) (hj : j.val ∉ U)
    (a : Exponent W) (ha : a ∈ localFamily B W) : a j = 0 := by
  rw [localFamily_eq_image_of_localize_eq B hUW he] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i, hi⟩
  exact hj (congrArg Subtype.val hi ▸ i.property)

variable {k : Type*} [CommSemiring k]

/-- Setting all newly retained variables to zero gives exactly the ideal in
the smaller retained-variable polynomial ring. -/
theorem killCompl_localFamily_ideal (B : Family V) (hUW : U ⊆ W)
    (he : localize B W = localize B U) :
    Ideal.map (MvPolynomial.killCompl (retainedInclusion_injective hUW)).toRingHom
      (monomialIdeal k (localFamily B W)) = monomialIdeal k (localFamily B U) := by
  have hmon (a : Exponent U) :
      MvPolynomial.killCompl (retainedInclusion_injective hUW)
        (MvPolynomial.monomial (a.mapDomain (retainedInclusion hUW)) (1 : k)) =
          MvPolynomial.monomial a 1 := by
    rw [← MvPolynomial.rename_monomial]
    exact MvPolynomial.killCompl_rename_app _ _
  rw [localFamily_eq_image_of_localize_eq B hUW he]
  simp only [monomialIdeal, Ideal.map_span, Finset.coe_image, Set.image_image]
  apply congrArg Ideal.span
  ext p
  simp only [Set.mem_image, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, hmon]

end Characterizations.Resolution

end
end CheckedCharacterizationsSource101

/-! ## Source: Characterizations.Resolution.LocalizationDescent -/
section CheckedCharacterizationsSource102

/-! Descent from a restored variable when the actual generator family is unchanged. -/
noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid Resolution
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

theorem local_linearResolution_of_insert_family_eq (B : Family V) (U : Finset V)
    (i : V) (hi : i ∉ U)
    (he : localize B (insert i U) = localize B U)
    (hL : HasLinearResolution (monomialLocalization k (monomialIdeal k B) (insert i U))) :
    HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  let hUW : U ⊆ insert i U := Finset.subset_insert i U
  let j : (insert i U : Finset V) := ⟨i,Finset.mem_insert_self _ _⟩
  let f : U → (insert i U : Finset V) := retainedInclusion hUW
  have hf : Function.Injective f := retainedInclusion_injective hUW
  have hrange : ∀ w, w ∈ Set.range f ↔ w ≠ j := by
    intro w
    constructor
    · rintro ⟨u,rfl⟩ heq
      have hv := congrArg Subtype.val heq
      change u.val = i at hv
      exact hi (hv ▸ u.property)
    · intro hne
      have hw : w.val ∈ U := by
        rcases Finset.mem_insert.mp w.property with hw | hw
        · exact False.elim (hne (Subtype.ext hw))
        · exact hw
      exact ⟨⟨w.val,hw⟩,Subtype.ext rfl⟩
  rw [monomialLocalization_eq] at hL
  obtain ⟨d,⟨P⟩⟩ := hL
  have hs : ∀ a ∈ localFamily B (insert i U), a j = 0 := by
    exact localFamily_zero_of_localize_eq B hUW he j hi
  have hI := monomialIdeal_variable_saturated (k:=k) (localFamily B (insert i U)) j hs
  rw [monomialLocalization_eq, ← killCompl_localFamily_ideal (k:=k) B hUW he]
  exact ⟨d,⟨P.descendAlong f hf j hrange hI⟩⟩

end Characterizations

end
end CheckedCharacterizationsSource102

/-! ## Source: Characterizations.ObstructionDegree -/
section CheckedCharacterizationsSource103

/-! # The full degree cost of a maximal obstruction (Lemma 4.4)

Linearity is the existence of an actual exact finite-free linear resolution.
Polynomial-extension descent is established by coefficient specialization.
-/
noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem nonlinear_localization_rank_pos {B : Family V} (hB : B.Nonempty)
    (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) :
    1 ≤ lowerRank B U := by
  by_contra hn
  have he := localize_equigenerated_of_rank_zero hB U (by omega)
  have hf := localFamily_equigenerated_iff.mpr he
  apply hbad
  rw [monomialLocalization_eq]
  exact linearResolution_of_polymatroidal
    (equigenerated_polymatroidal_of_degree_le_one hf (by omega))

theorem nonlinear_equigenerated_localization_rank_ge_two {B : Family V} (hB : B.Nonempty)
    (U : Finset V) (he : ∃ e, Equigenerated (localize B U) e)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) :
    2 ≤ lowerRank B U := by
  by_contra hn
  obtain ⟨e,he⟩ := he
  obtain ⟨a,ha⟩ := localize_nonempty hB U
  have hr : e = lowerRank B U :=
    (he a ha).symm.trans (equigenerated_localize_degree hB he ha)
  have hf := localFamily_equigenerated_iff.mpr he
  apply hbad
  rw [monomialLocalization_eq]
  exact linearResolution_of_polymatroidal
    (equigenerated_polymatroidal_of_degree_le_one hf (by omega))

/-- Lemma 4.4 for an inclusion-maximal localization lacking a genuine linear
free resolution. No prior equigeneration of all localizations is assumed. -/
theorem maximal_nonlinear_rank_cost {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hmax : ∀ W, U ⊂ W →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) W)) :
    2 ≤ U.card ∧ 1 ≤ lowerRank B U ∧
      lowerRank B U + (Fintype.card V-U.card) ≤ d := by
  have hcard : 2 ≤ U.card := by
    by_contra h
    exact hbad (Isolators.local_linearResolution_of_card_le_one hB U (by omega))
  have hequi : ∀ W, U ⊂ W → ∃ e, Equigenerated (localize B W) e := by
    intro W hW
    have hL := hmax W hW
    rw [monomialLocalization_eq] at hL
    obtain ⟨e,⟨P⟩⟩ := hL
    exact ⟨e,localFamily_equigenerated_iff.mp
      (P.equigenerated_of_monomial (localFamily B W) (localFamily_antichain B W))⟩
  have hinc : ∀ i ∉ U, lowerRank B U+1 ≤ lowerRank B (insert i U) := by
    intro i hi
    have hsub : U ⊂ insert i U := Finset.ssubset_insert hi
    have hm := lowerRank_mono hB (Finset.subset_insert i U)
    by_contra hn
    have hr : lowerRank B U = lowerRank B (insert i U) := by omega
    have hf := localize_eq_of_rank_eq hB (Finset.subset_insert i U) (hequi _ hsub) hr
    exact hbad (local_linearResolution_of_insert_family_eq B U i hi hf (hmax _ hsub))
  have hbound := supermodular_rank_codimension_bound
    (lowerRank_supermodular_above hB U hequi) hinc
  rw [lowerRank_univ_of_equigenerated hB hd] at hbound
  exact ⟨hcard,nonlinear_localization_rank_pos hB U hbad,hbound⟩

/-- Both alternatives in the literal statement of Lemma 4.4. -/
theorem maximal_obstruction_degree_cost {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (U : Finset V)
    (hmax :
      ((¬ ∃ e, Equigenerated (localize B U) e) ∧
        ∀ W, U ⊂ W → ∃ e, Equigenerated (localize B W) e) ∨
      ((¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) ∧
        ∀ W, U ⊂ W → HasLinearResolution (monomialLocalization k (monomialIdeal k B) W))) :
    2 ≤ U.card ∧ 1 ≤ lowerRank B U ∧
      lowerRank B U + (Fintype.card V-U.card) ≤ d := by
  rcases hmax with ⟨hbad,hm⟩ | ⟨hbad,hm⟩
  · exact maximal_nonequigenerated_rank_cost hB hd U hbad hm
  · exact maximal_nonlinear_rank_cost hB hd U hbad hm

/-- The final assertion of Lemma 4.4 under prior local equigeneration. -/
theorem maximal_pure_nonlinear_rank_cost {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hl : LocallyEquigenerated B) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hmax : ∀ W, U ⊂ W → HasLinearResolution (monomialLocalization k (monomialIdeal k B) W)) :
    2 ≤ U.card ∧ 2 ≤ lowerRank B U ∧
      lowerRank B U + (Fintype.card V-U.card) ≤ d := by
  obtain ⟨hc,_,hdim⟩ := maximal_nonlinear_rank_cost hB hd U hbad hmax
  exact ⟨hc,nonlinear_equigenerated_localization_rank_ge_two hB U (hl U) hbad,hdim⟩

end Characterizations

end
end CheckedCharacterizationsSource103

/-! ## Source: Characterizations.PairMass -/
section CheckedCharacterizationsSource104

/-! # A pointed triple injects into any prescribed final pair event -/

noncomputable section
namespace Characterizations
open Classical Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triple_to_pair_card_le {i q j k : V}
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j)
    (hki : k ≠ i) (hkq : k ≠ q) (hkj : k ≠ j) :
    Nat.card {o : VariableOrder V // FinalTriple o i q j} ≤
      Nat.card {o : VariableOrder V // FinalPair o i j} := by
  let σ : Equiv.Perm V := (Equiv.swap q k).trans (Equiv.swap i q)
  have hσi : σ i = q := by simp [σ,Equiv.swap_apply_def,hiq,hiq.symm,hki.symm]
  have hσq : σ q = k := by simp [σ,Equiv.swap_apply_def,hki,hkq]
  have hσk : σ k = i := by simp [σ,Equiv.swap_apply_def,hkq.symm]
  have hσj : σ j = j := by simp [σ,Equiv.swap_apply_def,hij.symm,hqj.symm,hkj.symm]
  have hσx (x : V) (hxi : x ≠ i) (hxq : x ≠ q) (hxk : x ≠ k) : σ x = x := by
    simp [σ,Equiv.swap_apply_def,hxi,hxq,hxk,Ne.symm hxi,Ne.symm hxq,Ne.symm hxk]
  let f (o : VariableOrder V) : VariableOrder V := if o q < o i then o else σ.trans o
  have hf (o : VariableOrder V) (ho : FinalTriple o i q j) : FinalPair (f o) i j := by
    by_cases hqi : o q < o i
    · simp only [f,if_pos hqi]
      refine ⟨ho.1,?_⟩
      intro x hxi hxj
      by_cases hxq : x = q
      · simpa [hxq] using hqi
      · exact (ho.2.2 x hxi hxq hxj).1
    · have hiqO : o i < o q := lt_of_le_of_ne (le_of_not_gt hqi)
        (fun he => hiq (o.injective he))
      simp only [f,if_neg hqi]
      refine ⟨?_,?_⟩
      · simpa only [Equiv.trans_apply,hσi,hσj] using ho.2.1
      · intro x hxi hxj
        by_cases hxq : x = q
        · subst x
          simpa only [Equiv.trans_apply,hσq,hσi] using (ho.2.2 k hki hkq hkj).2
        by_cases hxk : x = k
        · subst x
          simpa only [Equiv.trans_apply,hσk,hσi] using hiqO
        · simpa only [Equiv.trans_apply,hσi,hσx x hxi hxq hxk] using (ho.2.2 x hxi hxq hxj).2
  have hsignal (o : VariableOrder V) (ho : FinalTriple o i q j) :
      (f o) q < (f o) k ↔ ¬ o q < o i := by
    by_cases hqi : o q < o i
    · simp only [f,if_pos hqi,hqi,not_true_eq_false,iff_false]
      exact not_lt_of_gt (ho.2.2 k hki hkq hkj).2
    · simp only [f,if_neg hqi,Equiv.trans_apply,hσq,hσk,hqi,not_false_eq_true,iff_true]
      exact (ho.2.2 k hki hkq hkj).1
  let g : {o : VariableOrder V // FinalTriple o i q j} → {o : VariableOrder V // FinalPair o i j} :=
    fun o => ⟨f o.val,hf o.val o.property⟩
  apply Nat.card_le_card_of_injective g
  intro o o' he
  have heq : f o.val = f o'.val := congrArg Subtype.val he
  have hcond : (o.val q < o.val i) ↔ (o'.val q < o'.val i) := by
    have hs : (¬o.val q < o.val i) ↔ ¬o'.val q < o'.val i := by
      rw [← hsignal o.val o.property,← hsignal o'.val o'.property,heq]
    tauto
  apply Subtype.ext
  by_cases h : o.val q < o.val i
  · simpa only [f,if_pos h,if_pos (hcond.mp h)] using heq
  · have h' : ¬o'.val q < o'.val i := fun h' => h (hcond.mpr h')
    simp only [f,if_neg h,if_neg h'] at heq
    apply Equiv.ext
    intro x
    have hx := congrArg (fun e : VariableOrder V => e (σ.symm x)) heq
    simpa using hx

theorem finalPair_probability_lower_bound (hcard : 4 ≤ Fintype.card V) {i j : V} (hij : i ≠ j) :
    1 / (Fintype.card V * (Fintype.card V-1).choose 2 : ℕ) ≤
      finiteFraction (fun o : VariableOrder V => FinalPair o i j) := by
  have hpaircard : (pairCap i j).card = Fintype.card V-2 := by
    rw [pairCap,card_sdiff_of_subset (subset_univ _)]
    simp [hij]
  obtain ⟨q,hq⟩ : (pairCap i j).Nonempty := card_pos.mp (by omega)
  obtain ⟨hqi,hqj⟩ := (mem_pairCap _ _ _).mp hq
  have hcapcard : (tripleCap i q j).card = Fintype.card V-3 := by
    rw [tripleCap,card_sdiff_of_subset (subset_univ _)]
    simp [hqi.symm,hij,hqj]
  obtain ⟨k,hk⟩ : (tripleCap i q j).Nonempty := card_pos.mp (by omega)
  obtain ⟨hki,hkq,hkj⟩ := (mem_tripleCap _ _ _ _).mp hk
  let P : PointedTriple V := ⟨j,⟨{i,q},by simp [insert_subset_iff,hij,hqj],by simp [hqi.symm]⟩⟩
  have hprob : finiteFraction (fun o : VariableOrder V => FinalTriple o i q j) =
      1 / (Fintype.card V * (Fintype.card V-1).choose 2 : ℕ) := by
    rw [← pointedTriple_probability (by omega) P]
    exact finiteFraction_congr (fun o => (coversPoint_pair_iff hqi.symm hij hqj).symm)
  rw [←hprob]
  unfold finiteFraction
  exact div_le_div_of_nonneg_right (by exact_mod_cast triple_to_pair_card_le hqi.symm hij hqj hki hkq hkj)
    (Nat.cast_nonneg _)

end Characterizations

end
end CheckedCharacterizationsSource104

/-! ## Source: Characterizations.PaperEndpoints -/
section CheckedCharacterizationsSource105

/-!
# The integral-closedness characterization, including the zero ideal

The polytope in Theorem 2.11 requires a nonempty generator family, since its
lower rank is a minimum.  The characterization in (2.5) itself also holds at
zero.  This interface states that equivalence for every literal monomial ideal.
It adds no hypothesis and uses the ordinary monic-equation definition of
integral closedness already used by the nonzero theorem.
-/

noncomputable section

namespace Characterizations

open CommAlg CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Equation (2.5), for an arbitrary monomial ideal, including zero. -/
theorem monomialIdeal_polymatroidal_iff_integrallyClosed_all
    {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I) :
    IsPolymatroidalIdeal I ↔ IsIntegrallyClosedIdeal I ∧
      ∀ U : Finset V, ∃ d,
        Equigenerated (localFamily (monomialGenerators I hI) U) d := by
  by_cases hzero : I = ⊥
  · subst I
    have hp : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k)) :=
      isPolymatroidalIdeal_bot
    have hgenerators := (isPolymatroidalIdeal_iff_generators hI).mp hp
    constructor
    · intro _
      exact ⟨integrallyClosed_bot, fun U => (localFamily_polymatroidal hgenerators U).1⟩
    · intro _
      exact hp
  · exact monomialIdeal_polymatroidal_iff_integrallyClosed hI hzero

/-- Corollary 2.10 for an arbitrary literal monomial ideal, including zero.
The same minimal monomial exponent family is interpreted over any coefficient field. -/
theorem monomialIdeal_local_linearResolutions_field_independent_all
    {k' : Type u} [Field k']
    {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    (hlinear : ∀ U : Finset V,
      HasLinearResolution (monomialLocalization k I U)) :
    ∀ U : Finset V,
      HasLinearResolution
        (monomialLocalization k' (monomialIdeal k' (monomialGenerators I hI)) U) := by
  have hp := (monomialIdeal_polymatroidal_iff_local_linear hI).mpr hlinear
  have hgenerators := (isPolymatroidalIdeal_iff_generators hI).mp hp
  exact fun U => polymatroidal_local_linearResolutions (k := k') hgenerators U

end Characterizations

end
end CheckedCharacterizationsSource105

/-! ## Source: Characterizations.Presentation.Strands -/
section CheckedCharacterizationsSource106

/-! # The actual multigraded strands of the canonical monomial presentation -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

abbrev Generators (B : Family V) := {b // b ∈ B}
abbrev Free (B : Family V) := Generators B → MvPolynomial V k

/-- The canonical augmentation of the actual free polynomial module. -/
def augmentation (B : Family V) : Free (k := k) B →ₗ[MvPolynomial V k] MvPolynomial V k :=
  Fintype.linearCombination _ (fun b : Generators B => monomial b.val 1)

@[simp] theorem augmentation_apply (B : Family V) (x : Free (k := k) B) :
    augmentation B x = ∑ b, x b * monomial b.val 1 := by
  simp [augmentation, Fintype.linearCombination_apply, smul_eq_mul]

/-- The coefficient of the generator-labelled basis monomial of multidegree `C`. -/
def strandCoefficient (B : Family V) (C : Exponent V) (x : Free (k := k) B)
    (b : Generators B) : k := if b.val ≤ C then (x b).coeff (C - b.val) else 0

/-- Projection of a genuine polynomial vector onto one multidegree, with the
basis vector labelled `b` carrying its natural degree `b`. -/
def strand (B : Family V) (C : Exponent V) (x : Free (k := k) B) : Free (k := k) B :=
  fun b => monomial (C - b.val) (strandCoefficient B C x b)

@[simp] theorem strandCoefficient_add (B : Family V) (C : Exponent V)
    (x y : Free (k := k) B) :
    strandCoefficient B C (x + y) = strandCoefficient B C x + strandCoefficient B C y := by
  funext b
  by_cases h : b.val ≤ C <;> simp [strandCoefficient, h]

@[simp] theorem strandCoefficient_sub (B : Family V) (C : Exponent V)
    (x y : Free (k := k) B) :
    strandCoefficient B C (x - y) = strandCoefficient B C x - strandCoefficient B C y := by
  funext b
  by_cases h : b.val ≤ C <;> simp [strandCoefficient, h]

@[simp] theorem strandCoefficient_zero (B : Family V) (C : Exponent V) :
    strandCoefficient B C (0 : Free (k := k) B) = 0 := by
  funext b
  simp [strandCoefficient]

@[simp] theorem strandCoefficient_smul (B : Family V) (C : Exponent V) (c : k)
    (x : Free (k := k) B) : strandCoefficient B C (c • x) = c • strandCoefficient B C x := by
  funext b
  by_cases h : b.val ≤ C <;> simp [strandCoefficient, h]

lemma augmentation_coeff (B : Family V) (C : Exponent V) (x : Free (k := k) B) :
    (augmentation B x).coeff C = ∑ b, strandCoefficient B C x b := by
  simp [augmentation_apply, coeff_mul_monomial', strandCoefficient]

lemma strandCoefficient_sum_zero {B : Family V} {x : Free (k := k) B}
    (hx : x ∈ LinearMap.ker (augmentation B)) (C : Exponent V) :
    ∑ b, strandCoefficient B C x b = 0 := by
  rw [← augmentation_coeff, LinearMap.mem_ker.mp hx]
  simp

lemma strand_augmentation (B : Family V) (C : Exponent V) (x : Free (k := k) B) :
    augmentation B (strand B C x) = monomial C (∑ b, strandCoefficient B C x b) := by
  rw [augmentation_apply, map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : b.val ≤ C
  · simp [strand, strandCoefficient, h, monomial_mul_monomial, tsub_add_cancel_of_le h]
  · simp [strand, strandCoefficient, h]

lemma strand_mem_ker {B : Family V} {x : Free (k := k) B}
    (hx : x ∈ LinearMap.ker (augmentation B)) (C : Exponent V) :
    strand B C x ∈ LinearMap.ker (augmentation B) := by
  apply LinearMap.mem_ker.mpr
  rw [strand_augmentation, strandCoefficient_sum_zero hx]
  simp

/-- The finite set of multidegrees occurring in an actual polynomial vector. -/
def support (B : Family V) (x : Free (k := k) B) : Finset (Exponent V) :=
  univ.biUnion (fun b => (x b).support.image (fun a => a + b.val))

lemma degree_mem_support {B : Family V} (x : Free (k := k) B) (b : Generators B)
    (a : Exponent V) (ha : (x b).coeff a ≠ 0) : a + b.val ∈ support B x := by
  exact mem_biUnion.mpr ⟨b, mem_univ _, mem_image.mpr ⟨a, mem_support_iff.mpr ha, rfl⟩⟩

lemma strand_coeff (B : Family V) (C : Exponent V) (x : Free (k := k) B)
    (b : Generators B) (a : Exponent V) :
    (strand B C x b).coeff a = if C = a + b.val then (x b).coeff a else 0 := by
  by_cases h : b.val ≤ C
  · have he : C - b.val = a ↔ C = a + b.val := by
      constructor
      · intro he
        rw [← he, tsub_add_cancel_of_le h]
      · intro he
        rw [he, add_tsub_cancel_right]
    by_cases hC : C = a + b.val
    · subst C; simp [strand, strandCoefficient, add_tsub_cancel_right]
    · simp [strand, strandCoefficient, h, coeff_monomial, he, hC]
  · have he : C ≠ a + b.val := by
      intro he
      exact h (he ▸ le_add_left le_rfl)
    simp [strand, strandCoefficient, h, he]

/-- Finite multigraded decomposition in the original free module. -/
lemma sum_strand (B : Family V) (x : Free (k := k) B) :
    ∑ C ∈ support B x, strand B C x = x := by
  funext b
  apply MvPolynomial.ext
  intro a
  simp only [Finset.sum_apply, coeff_sum, strand_coeff]
  by_cases h : a + b.val ∈ support B x
  · simp [h]
  · have hz : (x b).coeff a = 0 := by
      by_contra hn
      exact h (degree_mem_support x b a hn)
    simp [h, hz]

/-- A genuine binomial syzygy between two canonical generators, at their lcm. -/
def pairSyzygy (B : Family V) (a b : Generators B) : Free (k := k) B :=
  Pi.single a (monomial ((a.val ⊔ b.val) - a.val) 1) -
    Pi.single b (monomial ((a.val ⊔ b.val) - b.val) 1)

lemma augmentation_single (B : Family V) (b : Generators B) (p : MvPolynomial V k) :
    augmentation B (Pi.single b p) = p * monomial b.val 1 := by
  simp [augmentation_apply, Pi.single_apply]

lemma pairSyzygy_mem_ker (B : Family V) (a b : Generators B) :
    pairSyzygy (k := k) B a b ∈ LinearMap.ker (augmentation B) := by
  apply LinearMap.mem_ker.mpr
  rw [pairSyzygy, map_sub, augmentation_single, augmentation_single,
    monomial_mul_monomial, monomial_mul_monomial,
    tsub_add_cancel_of_le le_sup_left, tsub_add_cancel_of_le le_sup_right, sub_self]

/-- The conventional algebraic definition: the first syzygy module of the
canonical minimal generator presentation is generated by linear forms. -/
def HasLinearPresentation (B : Family V) : Prop :=
  LinearMap.ker (augmentation (k := k) B) ≤
    Submodule.span (MvPolynomial V k)
      {x | x ∈ LinearMap.ker (augmentation B) ∧ Resolution.IsHomogeneousVector x 1}

end Characterizations.Presentation

end
end CheckedCharacterizationsSource106

/-! ## Source: Characterizations.Presentation.Edges -/
section CheckedCharacterizationsSource107

/-! # Linear binomial syzygies are exactly unit-exchange relations -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

lemma sup_exchange (a : Exponent V) {i j : V} (hij : i ≠ j) (hi : 0 < a i) :
    a ⊔ exchange a i j = a + Finsupp.single j 1 := by
  ext v
  simp only [Finsupp.sup_apply, exchange_apply, Finsupp.add_apply, Finsupp.single_apply]
  by_cases hvi : v = i <;> by_cases hvj : v = j <;> simp_all [eq_comm] <;> omega

lemma sup_sub_of_step {a b : Exponent V} (h : UnitStep a b) :
    ∃ i j, (a ⊔ b) - a = Finsupp.single j 1 ∧
      (a ⊔ b) - b = Finsupp.single i 1 := by
  obtain ⟨i, j, hij, hi, rfl⟩ := h
  refine ⟨i, j, ?_, ?_⟩
  · rw [sup_exchange a hij hi, add_tsub_cancel_left]
  · rw [sup_exchange a hij hi]
    ext v
    simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, exchange_apply]
    by_cases hvi : v = i <;> by_cases hvj : v = j <;> simp_all [eq_comm] <;> omega

lemma pairSyzygy_linear (B : Family V) (a b : Generators B) (h : UnitStep a.val b.val) :
    Resolution.IsHomogeneousVector (pairSyzygy (k := k) B a b) 1 := by
  obtain ⟨i, j, ha, hb⟩ := sup_sub_of_step h
  intro c
  simp only [pairSyzygy, Pi.sub_apply, ha, hb]
  apply MvPolynomial.IsHomogeneous.sub
  · by_cases he : c = a
    · subst c; simpa [Pi.single_apply, MvPolynomial.X] using (isHomogeneous_X (R := k) j)
    · simp [Pi.single_apply, he, Ne.symm he, isHomogeneous_zero]
  · by_cases he : c = b
    · subst c; simpa [Pi.single_apply, MvPolynomial.X] using (isHomogeneous_X (R := k) i)
    · simp [Pi.single_apply, he, Ne.symm he, isHomogeneous_zero]

/-- The polynomial submodule generated by actual linear binomial syzygies. -/
def edgeSpan (B : Family V) : Submodule (MvPolynomial V k) (Free (k := k) B) :=
  Submodule.span _ {x | ∃ a b : Generators B, UnitStep a.val b.val ∧ x = pairSyzygy B a b}

lemma pairSyzygy_mem_edgeSpan (B : Family V) (a b : Generators B) (h : UnitStep a.val b.val) :
    pairSyzygy (k := k) B a b ∈ edgeSpan B :=
  Submodule.subset_span ⟨a, b, h, rfl⟩

lemma edgeSpan_le_ker (B : Family V) : edgeSpan (k := k) B ≤ LinearMap.ker (augmentation B) := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, b, h, rfl⟩
  exact pairSyzygy_mem_ker B a b

lemma edgeSpan_le_linearSpan (B : Family V) :
    edgeSpan (k := k) B ≤ Submodule.span (MvPolynomial V k)
      {x | x ∈ LinearMap.ker (augmentation B) ∧ Resolution.IsHomogeneousVector x 1} := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, b, h, rfl⟩
  exact Submodule.subset_span ⟨pairSyzygy_mem_ker B a b, pairSyzygy_linear B a b h⟩

/-- A pair relation at any common multiple is a monomial multiple of its lcm relation. -/
lemma scaled_pairSyzygy (B : Family V) (C : Exponent V) (a b : Generators B)
    (ha : a.val ≤ C) (hb : b.val ≤ C) :
    (monomial (C - (a.val ⊔ b.val)) (1 : k)) • pairSyzygy (k := k) B a b =
      Pi.single a (monomial (C - a.val) (1 : k)) - Pi.single b (monomial (C - b.val) (1 : k)) := by
  have hsup : a.val ⊔ b.val ≤ C := sup_le ha hb
  have h₁ : C - (a.val ⊔ b.val) + ((a.val ⊔ b.val) - a.val) = C - a.val := by
    ext v
    have hs := hsup v
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.sup_apply] at hs ⊢
    omega
  have h₂ : C - (a.val ⊔ b.val) + ((a.val ⊔ b.val) - b.val) = C - b.val := by
    ext v
    have hs := hsup v
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.sup_apply] at hs ⊢
    omega
  funext v
  simp only [pairSyzygy, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub]
  by_cases hva : v = a <;> by_cases hvb : v = b <;>
    simp_all [Pi.single_apply, eq_comm, monomial_mul_monomial, h₁, h₂]

lemma step_of_common_degree_one {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (C : Exponent V) (hC : C.degree = d + 1) (a b : Generators B)
    (ha : a.val ≤ C) (hb : b.val ≤ C) (hab : a ≠ b) : UnitStep a.val b.val := by
  have hdeg (x : Generators B) (hx : x.val ≤ C) : (C - x.val).degree = 1 := by
    have he := congrArg Finsupp.degree (tsub_add_cancel_of_le hx)
    rw [map_add, hB x.val x.property, hC] at he
    omega
  obtain ⟨j, hj⟩ : ∃ j, Finsupp.single j 1 = C - a.val := by
    apply Set.mem_range.mp
    rw [Finsupp.range_single_one]
    exact hdeg a ha
  obtain ⟨i, hi⟩ : ∃ i, Finsupp.single i 1 = C - b.val := by
    apply Set.mem_range.mp
    rw [Finsupp.range_single_one]
    exact hdeg b hb
  have he : a.val + Finsupp.single j 1 = b.val + Finsupp.single i 1 := by
    rw [hj, hi, add_tsub_cancel_of_le ha, add_tsub_cancel_of_le hb]
  have hij : i ≠ j := by
    intro hij
    apply hab
    apply Subtype.ext
    rw [hij] at he
    exact add_right_cancel he
  have hai : 0 < a.val i := by
    have hh := congrArg (fun t : Exponent V => t i) he
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply,
      if_neg hij, if_neg hij.symm] at hh
    omega
  refine ⟨i, j, hij, hai, ?_⟩
  ext v
  have hh := congrArg (fun t : Exponent V => t v) he
  simp only [Finsupp.add_apply, Finsupp.single_apply, exchange_apply] at hh ⊢
  by_cases hvi : v = i <;> by_cases hvj : v = j <;> simp_all [eq_comm] <;> omega

end Characterizations.Presentation

end
end CheckedCharacterizationsSource107

/-! ## Source: Characterizations.Presentation.Paths -/
section CheckedCharacterizationsSource108

/-! # Exchange paths span the actual polynomial syzygies -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

def pairAt (B : Family V) (C : Exponent V) (a b : Generators B) : Free (k := k) B :=
  Pi.single a (monomial (C - a.val) 1) - Pi.single b (monomial (C - b.val) 1)

@[simp] lemma pairAt_self (B : Family V) (C : Exponent V) (a : Generators B) :
    pairAt (k := k) B C a a = 0 := sub_self _

lemma pairAt_add (B : Family V) (C : Exponent V) (a b c : Generators B) :
    pairAt (k := k) B C a b + pairAt B C b c = pairAt B C a c := by
  exact sub_add_sub_cancel _ _ _

lemma pairAt_mem_of_step (B : Family V) (C : Exponent V) (a b : Generators B)
    (ha : a.val ≤ C) (hb : b.val ≤ C) (h : UnitStep a.val b.val) :
    pairAt (k := k) B C a b ∈ edgeSpan B := by
  rw [pairAt, ← scaled_pairSyzygy B C a b ha hb]
  exact (edgeSpan B).smul_mem _ (pairSyzygy_mem_edgeSpan B a b h)

lemma pairAt_mem_of_path (B : Family V) (C : Exponent V) {a b : Exponent V}
    (hp : Relation.ReflTransGen (BoxStep B C) a b) (ha : a ∈ B) (hb : b ∈ B) :
    pairAt (k := k) B C ⟨a, ha⟩ ⟨b, hb⟩ ∈ edgeSpan B := by
  induction hp with
  | refl => simp
  | @tail b c hp hbc ih =>
    have h₁ := ih hbc.1
    have h₂ := pairAt_mem_of_step (k := k) B C ⟨b, hbc.1⟩ ⟨c, hb⟩ hbc.2.2.1 hbc.2.2.2.1 hbc.2.2.2.2
    simpa only [pairAt_add] using (edgeSpan B).add_mem h₁ h₂

lemma strand_eq_sum_pairs {B : Family V} (C : Exponent V) (x : Free (k := k) B)
    (hx : x ∈ LinearMap.ker (augmentation B)) (a : Generators B) :
    (∑ b, (MvPolynomial.C (strandCoefficient B C x b) : MvPolynomial V k) • pairAt B C b a) = strand B C x := by
  have hs : (∑ b, MvPolynomial.C (strandCoefficient B C x b) : MvPolynomial V k) = 0 := by
    rw [← map_sum, strandCoefficient_sum_zero hx, map_zero]
  simp only [pairAt, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [hs, zero_smul, sub_zero]
  funext c
  simp [Pi.single_apply, strand, C_mul_monomial]

lemma strand_mem_of_pairs {B : Family V} (C : Exponent V) (x : Free (k := k) B)
    (hx : x ∈ LinearMap.ker (augmentation B))
    (hp : ∀ a b : Generators B, a.val ≤ C → b.val ≤ C → pairAt (k := k) B C a b ∈ edgeSpan B) :
    strand B C x ∈ edgeSpan B := by
  by_cases hne : ∃ a : Generators B, a.val ≤ C
  · obtain ⟨a, ha⟩ := hne
    rw [← strand_eq_sum_pairs C x hx a]
    apply (edgeSpan B).sum_mem
    intro b hb
    by_cases hbc : b.val ≤ C
    · exact (edgeSpan B).smul_mem _ (hp b a hbc ha)
    · simp [strandCoefficient, hbc]
  · have he : strand B C x = 0 := by
      funext b
      have hb : ¬ b.val ≤ C := fun h => hne ⟨b, h⟩
      simp [strand, strandCoefficient, hb]
    rw [he]
    exact (edgeSpan B).zero_mem

lemma ker_le_edgeSpan_of_boxConnected {B : Family V} (hB : BoxConnected B) :
    LinearMap.ker (augmentation (k := k) B) ≤ edgeSpan B := by
  intro x hx
  rw [← sum_strand B x]
  apply (edgeSpan B).sum_mem
  intro C hC
  apply strand_mem_of_pairs C x hx
  intro a b ha hb
  exact pairAt_mem_of_path B C (hB C a.val a.property ha b.val b.property hb) a.property b.property

/-- Every actual homogeneous linear syzygy is spanned by the binomial
unit-exchange syzygies, without any connectivity assumption. -/
lemma linear_relation_mem_edgeSpan {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (x : Free (k := k) B) (hx : x ∈ LinearMap.ker (augmentation B))
    (hlin : Resolution.IsHomogeneousVector x 1) : x ∈ edgeSpan B := by
  rw [← sum_strand B x]
  apply (edgeSpan B).sum_mem
  intro C hC
  have hdeg : C.degree = d + 1 := by
    obtain ⟨b, hb, hC⟩ := mem_biUnion.mp hC
    obtain ⟨e, he, rfl⟩ := mem_image.mp hC
    have he' : e.degree = 1 := by
      by_contra hn
      exact (mem_support_iff.mp he) ((hlin b).coeff_eq_zero hn)
    rw [map_add, he', hB b.val b.property, Nat.add_comm]
  apply strand_mem_of_pairs C x hx
  intro a b ha hb
  by_cases hab : a = b
  · subst b; simp
  · exact pairAt_mem_of_step B C a b ha hb (step_of_common_degree_one hB C hdeg a b ha hb hab)

lemma linearSpan_eq_edgeSpan {B : Family V} {d : ℕ} (hB : Equigenerated B d) :
    Submodule.span (MvPolynomial V k)
      {x : Free (k := k) B | x ∈ LinearMap.ker (augmentation B) ∧ Resolution.IsHomogeneousVector x 1} =
      edgeSpan B := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    exact linear_relation_mem_edgeSpan hB x hx.1 hx.2
  · exact edgeSpan_le_linearSpan B

lemma linearPresentation_of_boxConnected {B : Family V} (hB : BoxConnected B) :
    HasLinearPresentation (k := k) B :=
  (ker_le_edgeSpan_of_boxConnected hB).trans (edgeSpan_le_linearSpan B)

end Characterizations.Presentation

end
end CheckedCharacterizationsSource108

/-! ## Source: Characterizations.Presentation.Connectivity -/
section CheckedCharacterizationsSource109

/-! # A disconnected box detects a genuine nonlinear first syzygy -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

/-- Restrict the actual canonical augmentation to a specified generator subset. -/
def selectedAugmentation (B : Family V) (U : Finset (Generators B)) :
    Free (k := k) B →ₗ[MvPolynomial V k] MvPolynomial V k :=
  Fintype.linearCombination _ (fun b => if b ∈ U then monomial b.val 1 else 0)

lemma selectedAugmentation_single (B : Family V) (U : Finset (Generators B))
    (b : Generators B) (p : MvPolynomial V k) :
    selectedAugmentation B U (Pi.single b p) = if b ∈ U then p * monomial b.val 1 else 0 := by
  simp [selectedAugmentation, Fintype.linearCombination_apply, Pi.single_apply, smul_eq_mul,
    mul_ite]

lemma selectedAugmentation_pair (B : Family V) (U : Finset (Generators B))
    (a b : Generators B) :
    selectedAugmentation (k := k) B U (pairSyzygy B a b) =
      (if a ∈ U then monomial (a.val ⊔ b.val) 1 else 0) -
        (if b ∈ U then monomial (a.val ⊔ b.val) 1 else 0) := by
  rw [pairSyzygy, map_sub, selectedAugmentation_single, selectedAugmentation_single]
  simp only [monomial_mul_monomial, one_mul, tsub_add_cancel_of_le le_sup_left,
    tsub_add_cancel_of_le le_sup_right]

lemma selectedAugmentation_pairAt (B : Family V) (U : Finset (Generators B))
    (C : Exponent V) (a b : Generators B) (ha : a.val ≤ C) (hb : b.val ≤ C) :
    selectedAugmentation (k := k) B U (pairAt B C a b) =
      (if a ∈ U then monomial C 1 else 0) - (if b ∈ U then monomial C 1 else 0) := by
  rw [pairAt, map_sub, selectedAugmentation_single, selectedAugmentation_single]
  simp only [monomial_mul_monomial, one_mul, tsub_add_cancel_of_le ha,
    tsub_add_cancel_of_le hb]

lemma selectedAugmentation_edge_coeff_zero (B : Family V) (U : Finset (Generators B))
    (C : Exponent V)
    (hU : ∀ a b : Generators B, a.val ≤ C → b.val ≤ C → UnitStep a.val b.val → (a ∈ U ↔ b ∈ U))
    (a b : Generators B) (hab : UnitStep a.val b.val) (p : MvPolynomial V k) :
    (selectedAugmentation (k := k) B U (p • pairSyzygy (k := k) B a b)).coeff C = 0 := by
  rw [map_smul, selectedAugmentation_pair]
  by_cases hsup : a.val ⊔ b.val ≤ C
  · have he := hU a b (le_sup_left.trans hsup) (le_sup_right.trans hsup) hab
    by_cases ha : a ∈ U
    · simp [ha, he.mp ha]
    · have hb : b ∉ U := fun hb => ha (he.mpr hb)
      simp [ha, hb]
  · simp only [smul_eq_mul, mul_sub]
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
      simp [ha, hb, coeff_mul_monomial', hsup]

lemma selectedAugmentation_edgeSpan_coeff_zero (B : Family V) (U : Finset (Generators B))
    (C : Exponent V)
    (hU : ∀ a b : Generators B, a.val ≤ C → b.val ≤ C → UnitStep a.val b.val → (a ∈ U ↔ b ∈ U))
    (x : Free (k := k) B) (hx : x ∈ edgeSpan B) :
    (selectedAugmentation B U x).coeff C = 0 := by
  suffices hh : ∀ p : MvPolynomial V k, (selectedAugmentation B U (p • x)).coeff C = 0 by
    simpa using hh 1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    exact selectedAugmentation_edge_coeff_zero B U C hU a b hab
  | zero => intro p; simp
  | add x y hx hy ihx ihy =>
    intro p
    simp only [smul_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ihx, ihy, add_zero]
  | smul r x hx ih =>
    intro p
    rw [smul_smul]
    exact ih (p * r)

/-- A disconnected box produces an actual syzygy outside the submodule generated
by all linear binomial relations. This holds in every nontrivial coefficient ring. -/
lemma boxConnected_of_ker_le_edgeSpan [Nontrivial k] {B : Family V}
    (hker : LinearMap.ker (augmentation (k := k) B) ≤ edgeSpan B) : BoxConnected B := by
  intro C a ha haC b hb hbC
  by_contra hpath
  let U : Finset (Generators B) := univ.filter (fun c => Relation.ReflTransGen (BoxStep B C) a c.val)
  have hU : ∀ x y : Generators B, x.val ≤ C → y.val ≤ C → UnitStep x.val y.val → (x ∈ U ↔ y ∈ U) := by
    intro x y hx hy hxy
    simp only [U, mem_filter, mem_univ, true_and]
    constructor
    · intro hp
      exact hp.tail ⟨x.property, y.property, hx, hy, hxy⟩
    · intro hp
      exact hp.tail ⟨y.property, x.property, hy, hx, hxy.symm⟩
  let a' : Generators B := ⟨a, ha⟩
  let b' : Generators B := ⟨b, hb⟩
  have haU : a' ∈ U := by simp [U, a', Relation.ReflTransGen.refl]
  have hbU : b' ∉ U := by simpa [U, b'] using hpath
  have hz : pairAt (k := k) B C a' b' ∈ LinearMap.ker (augmentation B) := by
    rw [pairAt, ← scaled_pairSyzygy B C a' b' haC hbC]
    exact (LinearMap.ker (augmentation B)).smul_mem _ (pairSyzygy_mem_ker B a' b')
  have hh := selectedAugmentation_edgeSpan_coeff_zero B U C hU _ (hker hz)
  rw [selectedAugmentation_pairAt B U C a' b' haC hbC] at hh
  simpa [haU, hbU] using hh

/-- Lemma 3.1: the conventional linear first-syzygy condition is equivalent to
connectivity of every nonempty coordinate box, over every field (indeed, ring). -/
theorem linearPresentation_iff_boxConnected [Nontrivial k] {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) : HasLinearPresentation (k := k) B ↔ BoxConnected B := by
  constructor
  · intro h
    apply boxConnected_of_ker_le_edgeSpan (k := k)
    simpa only [HasLinearPresentation, linearSpan_eq_edgeSpan hB] using h
  · exact linearPresentation_of_boxConnected

end Characterizations.Presentation

end
end CheckedCharacterizationsSource109

/-! ## Source: Characterizations.Presentation.Finite -/
section CheckedCharacterizationsSource110

/-! # Conventional finite free presentations and the local exchange criterion -/
noncomputable section
@[reducible] local instance (priority := 2000) presentationDecEq (α : Type*) [Fintype α] : DecidableEq α := Classical.decEq α
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

/-- An actual finite free presentation of the original monomial ideal, with all
first differential entries linear. The canonical free generators have the common
degree of the monomial generating family. -/
structure FiniteLinearPresentation (B : Family V) where
  rank : ℕ
  differential : (Fin rank → MvPolynomial V k) →ₗ[MvPolynomial V k] Free (k := k) B
  exact : LinearMap.range differential = LinearMap.ker (augmentation B)
  linear : Resolution.IsHomogeneousMap differential 1

lemma augmentation_range (B : Family V) :
    LinearMap.range (augmentation (k := k) B) = monomialIdeal k B := by
  rw [augmentation, Fintype.range_linearCombination, monomialIdeal]
  apply congrArg (Submodule.span (MvPolynomial V k))
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.val, b.property, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

lemma FiniteLinearPresentation.hasLinearPresentation {B : Family V}
    (P : FiniteLinearPresentation (k := k) B) : HasLinearPresentation (k := k) B := by
  intro x hx
  rw [← P.exact] at hx
  obtain ⟨y, rfl⟩ := hx
  have hy : y = ∑ j, y j • Pi.single j (1 : MvPolynomial V k) := by
    ext j
    simp [Pi.single_apply]
  rw [hy, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  constructor
  · rw [← P.exact]
    exact LinearMap.mem_range_self _ _
  · exact fun b => P.linear b j

abbrev Edges (B : Family V) :=
  {ab : Generators B × Generators B // UnitStep ab.1.val ab.2.val}

def edgeColumn (B : Family V) (j : Fin (Fintype.card (Edges B))) : Free (k := k) B :=
  let ab := (Fintype.equivFin (Edges B)).symm j
  pairSyzygy B ab.val.1 ab.val.2

lemma edgeColumn_range (B : Family V) :
    Set.range (edgeColumn (k := k) B) =
      {x | ∃ a b : Generators B, UnitStep a.val b.val ∧ x = pairSyzygy B a b} := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    let ab := (Fintype.equivFin (Edges B)).symm j
    exact ⟨ab.val.1, ab.val.2, ab.property, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨(Fintype.equivFin (Edges B)) ⟨(a, b), hab⟩, ?_⟩
    simp [edgeColumn]

/-- The first free module has one basis vector for each ordered unit-exchange
edge. Exactness follows from the proved algebraic syzygy criterion. -/
def finiteLinearPresentationOfCondition {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (h : HasLinearPresentation (k := k) B) :
    FiniteLinearPresentation (k := k) B where
  rank := Fintype.card (Edges B)
  differential := Fintype.linearCombination _ (edgeColumn B)
  exact := by
    rw [Fintype.range_linearCombination, edgeColumn_range]
    change edgeSpan B = LinearMap.ker (augmentation B)
    apply le_antisymm (edgeSpan_le_ker B)
    simpa only [HasLinearPresentation, linearSpan_eq_edgeSpan hB] using h
  linear := by
    intro b j
    have he : Fintype.linearCombination (MvPolynomial V k) (edgeColumn (k := k) B) (Pi.single j 1) = edgeColumn (k := k) B j := by
      simp [Fintype.linearCombination_apply, Pi.single_apply]
    rw [he]
    let ab := (Fintype.equivFin (Edges B)).symm j
    exact pairSyzygy_linear B ab.val.1 ab.val.2 ab.property b

/-- The syzygy-generation definition is equivalent to a literal finite free
presentation with linear entries. -/
theorem nonempty_finiteLinearPresentation_iff {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) :
    Nonempty (FiniteLinearPresentation (k := k) B) ↔ HasLinearPresentation (k := k) B :=
  ⟨fun ⟨P⟩ => P.hasLinearPresentation, fun h => ⟨finiteLinearPresentationOfCondition hB h⟩⟩

/-- Lemma 3.1, stated directly with the actual finite free presentation. -/
theorem finiteLinearPresentation_iff_boxConnected [Nontrivial k] {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) :
    Nonempty (FiniteLinearPresentation (k := k) B) ↔ BoxConnected B :=
  (nonempty_finiteLinearPresentation_iff hB).trans (linearPresentation_iff_boxConnected hB)

/-- Exchange restricted exactly to pairs at the paper's distance four. -/
def DistanceFourExchange (B : Family V) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, l1Distance a b = 4 → ∀ i, b i < a i →
    ∃ j, a j < b j ∧ exchange a i j ∈ B

/-- Theorem 3.3, with a genuine finite linear presentation and the full prescribed
donor exchange condition. -/
theorem polymatroidal_iff_linearPresentation_distanceFour [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) :
    IsPolymatroidal B ↔ Nonempty (FiniteLinearPresentation (k := k) B) ∧ DistanceFourExchange B := by
  constructor
  · intro h
    constructor
    · apply (finiteLinearPresentation_iff_boxConnected hB).mpr
      let o : VariableOrder V := Fintype.equivFin V
      exact boxConnected_of_linearQuotients hB (variableRevlex_irrefl o)
        (variableRevlex_trans o) (variableRevlex_total o)
        (polymatroidal_variable_linearQuotients (k := k) h.2 o)
    · intro a ha b hb _ i hi
      exact h.2 a ha b hb i hi
  · rintro ⟨hp, he⟩
    refine ⟨⟨d, hB⟩, ?_⟩
    by_contra hn
    obtain ⟨a, b, ha, hb, hd, i, hi, hbad⟩ :=
      failed_exchange_distance_four ((finiteLinearPresentation_iff_boxConnected hB).mp hp) hn
    obtain ⟨j, hj, hjB⟩ := he a ha b hb hd i hi
    exact hbad j hj hjB

end Characterizations.Presentation

end
end CheckedCharacterizationsSource110

/-! ## Source: Characterizations.Rejection -/
section CheckedCharacterizationsSource111

/-! # The sharp rejection fraction, including independent repeated tests -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def rejectionFraction (k : Type*) [CommSemiring k] (B : Family V) : ℝ :=
  finiteFraction (fun o : VariableOrder V => ¬ HasLinearQuotients k B (variableRevlex o))

def patternMass (s : ℕ) : ℝ := 1 / ((s+3)*(s+2).choose 2 : ℕ)

/-- Theorem 5.6: every nonpolymatroidal generator family has at least the
probability of one full active order pattern. -/
theorem rejection_fraction_lower_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hd : 2 ≤ d)
    (hcard : 4 ≤ Fintype.card V) (hnot : ¬ IsPolymatroidal B) :
    patternMass (min (d-1) (Fintype.card V-3)) ≤ rejectionFraction k B := by
  let G : Set (VariableOrder V) := {o | HasLinearQuotients k B (variableRevlex o)}
  by_cases hpatterns : CoversPatterns (min (d-1) (Fintype.card V-3)) G
  · have hnpairs : ¬ (Fintype.card V-1 ≤ d → CoversFinalPairs G) := by
      intro hpairs
      exact hnot ⟨⟨d,hB⟩,exchange_of_degree_coverage (k := k) hB hcard G hpatterns hpairs (fun _ h => h)⟩
    simp only [CoversFinalPairs,not_forall] at hnpairs
    obtain ⟨hdlarge,i,j,hij,hbad⟩ := hnpairs
    have hmass : patternMass (min (d-1) (Fintype.card V-3)) =
        1 / (Fintype.card V * (Fintype.card V-1).choose 2 : ℕ) := by
      have h1 : min (d-1) (Fintype.card V-3) = Fintype.card V-3 := by omega
      have h2 : Fintype.card V-3+3 = Fintype.card V := by omega
      have h3 : Fintype.card V-3+2 = Fintype.card V-1 := by omega
      simp only [patternMass,h1,h2,h3]
    rw [hmass]
    apply (finalPair_probability_lower_bound hcard hij).trans
    apply finiteFraction_mono
    intro o ho hgood
    exact hbad ⟨o,hgood,ho⟩
  · simp only [CoversPatterns,not_forall] at hpatterns
    obtain ⟨i,q,j,hiq,hij,hqj,C,hC,hCc,hbad⟩ := hpatterns
    have hm : patternMass (min (d-1) (Fintype.card V-3)) =
        finiteFraction (fun o : VariableOrder V => OrderPattern o C i q j) := by
      rw [orderPattern_probability C i q j hiq hij hqj hC,hCc]
      rfl
    rw [hm]
    apply finiteFraction_mono
    intro o ho hgood
    exact hbad ⟨o,hgood,ho⟩

/-- The lower bound is attained by an actual capped monomial ideal, extended
by unused variables and multiplied by a common monomial when necessary. -/
theorem exists_sharp_rejection_family {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧
      rejectionFraction k B = patternMass (min (d-1) (Fintype.card V-3)) := by
  obtain ⟨i,q,j,hiq,hij,hqj⟩ := exists_three_distinct (V := V) (by omega)
  have hcapcard : (tripleCap i q j).card = Fintype.card V-3 := by
    rw [tripleCap,card_sdiff_of_subset (subset_univ _)]
    simp [hiq,hij,hqj]
  obtain ⟨C,hC,hCc⟩ := exists_subset_card_eq
    (show min (d-1) (Fintype.card V-3) ≤ (tripleCap i q j).card by omega)
  have hCne : C.Nonempty := card_pos.mp (by omega)
  obtain ⟨B,hB,hnot,hiff⟩ := exists_pattern_isolator (k := k) C i q j hiq hij hqj hC hCne d (by omega)
  refine ⟨B,hB,hnot,?_⟩
  calc
    rejectionFraction k B = finiteFraction (fun o : VariableOrder V => OrderPattern o C i q j) :=
      finiteFraction_congr (fun o => by rw [hiff o]; simp)
    _ = _ := by rw [orderPattern_probability C i q j hiq hij hqj hC,hCc]; rfl

theorem patternMass_formula (s : ℕ) :
    patternMass s = 2 / (((s:ℝ)+1)*((s:ℝ)+2)*((s:ℝ)+3)) := by
  have hn := Nat.add_one_mul_choose_eq (s+1) 1
  have hn' : ((s+2).choose 2 : ℝ)*2 = ((s:ℝ)+1)*((s:ℝ)+2) := by
    have hh : (s+2).choose 2*2 = (s+1)*(s+2) := by simpa [mul_comm] using hn.symm
    exact_mod_cast hh
  have hpos : (0:ℝ) < (s+2).choose 2 := by exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ s+2))
  unfold patternMass
  push_cast
  field_simp
  nlinarith

theorem rejection_fraction_displayed {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hd : 2 ≤ d)
    (hcard : 4 ≤ Fintype.card V) (hnot : ¬ IsPolymatroidal B) :
    let t := min d (Fintype.card V-2)
    2 / ((t:ℝ)*((t:ℝ)+1)*((t:ℝ)+2)) ≤ rejectionFraction k B := by
  have hh := rejection_fraction_lower_bound (k := k) hB hd hcard hnot
  rw [patternMass_formula] at hh
  have he : min d (Fintype.card V-2) = min (d-1) (Fintype.card V-3)+1 := by omega
  simpa only [he,Nat.cast_add,Nat.cast_one,add_assoc,
    show (1:ℝ)+1=2 by norm_num,show (1:ℝ)+2=3 by norm_num] using hh

/-- The sharp examples attain exactly the rational expression printed in
Theorem 5.6, for every allowed degree and number of variables. -/
theorem exists_sharp_rejection_displayed {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧
      let t := min d (Fintype.card V-2)
      rejectionFraction k B = 2 / ((t:ℝ)*((t:ℝ)+1)*((t:ℝ)+2)) := by
  obtain ⟨B,hB,hnot,heq⟩ := exists_sharp_rejection_family (k := k) d hd hcard
  refine ⟨B,hB,hnot,?_⟩
  rw [heq,patternMass_formula]
  have he : min d (Fintype.card V-2) = min (d-1) (Fintype.card V-3)+1 := by omega
  simp only [he,Nat.cast_add,Nat.cast_one,add_assoc,
    show (1:ℝ)+1=2 by norm_num,show (1:ℝ)+2=3 by norm_num]

theorem independent_tests_miss_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hd : 2 ≤ d)
    (hcard : 4 ≤ Fintype.card V) (hnot : ¬ IsPolymatroidal B) (M : ℕ) :
    finiteFraction (fun f : Fin M → VariableOrder V =>
      ∀ j, HasLinearQuotients k B (variableRevlex (f j))) ≤
      (1-patternMass (min (d-1) (Fintype.card V-3)))^M := by
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  let P := fun o : VariableOrder V => HasLinearQuotients k B (variableRevlex o)
  have hrej : rejectionFraction k B = 1-finiteFraction P := finiteFraction_not P
  have hbound := rejection_fraction_lower_bound (k := k) hB hd hcard hnot
  rw [hrej] at hbound
  rw [finiteFraction_all_trials M P]
  exact pow_le_pow_left₀ (finiteFraction_nonneg P) (by linarith) M

end Characterizations

end
end CheckedCharacterizationsSource111

/-! ## Source: Characterizations.SmallRejection -/
section CheckedCharacterizationsSource112

/-! # Sharp rejection probabilities in two and three variables -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rejection_fraction_three {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 3) {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (hnot : ¬ IsPolymatroidal B) : (1:ℝ)/6 ≤ rejectionFraction k B := by
  have hbad : ∃ o : VariableOrder V,¬HasLinearQuotients k B (variableRevlex o) := by
    by_contra hn
    apply hnot
    exact (polymatroidal_iff_universal_revlex hB).mpr (by simpa using hn)
  haveI : Nonempty {o : VariableOrder V // ¬HasLinearQuotients k B (variableRevlex o)} :=
    ⟨⟨hbad.choose,hbad.choose_spec⟩⟩
  have hc : 1 ≤ Nat.card {o : VariableOrder V // ¬HasLinearQuotients k B (variableRevlex o)} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have hord : Nat.card (VariableOrder V) = 6 := by
    rw [Nat.card_eq_fintype_card,variableOrder_card,hcard]
    norm_num
  unfold rejectionFraction finiteFraction
  rw [hord]
  norm_num only [Nat.cast_ofNat]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by norm_num)

theorem exists_sharp_rejection_three {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 3) (d : ℕ) (hd : 2 ≤ d) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧ rejectionFraction k B = (1:ℝ)/6 := by
  obtain ⟨i,j,hij⟩ := exists_distinct_of_card_two (V := V) (by omega)
  let c : Exponent V := Finsupp.single i (d-2)
  let B := translatedFamily c (pairFamily i j)
  have hbase : Equigenerated (pairFamily i j) 2 := by simpa [hcard] using pairFamily_equigenerated i j
  have hcdeg : c.degree = d-2 := by simp only [c,Finsupp.degree_single]
  have hgen : Equigenerated B d := by
    have hh := translatedFamily_equigenerated hbase c
    have he : 2+c.degree = d := by omega
    exact he ▸ hh
  obtain ⟨o₀,h₀⟩ := exists_finalPair i j hij
  have hiff (o : VariableOrder V) : ¬HasLinearQuotients k B (variableRevlex o) ↔ o = o₀ := by
    rw [translatedFamily_linearQuotients_iff hbase c o,pairFamily_linearQuotients_iff hij (by omega) o]
    simp only [not_not]
    exact ⟨fun hf => finalPair_unique_card_three hcard hij hf h₀,fun he => he ▸ h₀⟩
  refine ⟨B,hgen,?_,?_⟩
  · intro hp
    exact pairFamily_not_polymatroidal hij (by omega) ((translatedFamily_polymatroidal_iff hbase c).mp hp)
  · change finiteFraction (fun o : VariableOrder V => ¬HasLinearQuotients k B (variableRevlex o)) = _
    rw [finiteFraction_congr hiff]
    norm_num [finiteFraction,Nat.card_eq_fintype_card,variableOrder_card,hcard]

theorem rejection_fraction_two {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V ≤ 2) {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (hnot : ¬ IsPolymatroidal B) : rejectionFraction k B = 1 := by
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  have hbad (o : VariableOrder V) : ¬HasLinearQuotients k B (variableRevlex o) :=
    fun hL => hnot (one_order_suffices_card_two hB hcard o hL)
  change finiteFraction (fun o : VariableOrder V => ¬HasLinearQuotients k B (variableRevlex o)) = _
  rw [finiteFraction_congr (fun o => iff_true_intro (hbad o)),finiteFraction_true]

theorem exists_sharp_rejection_two {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 2) (d : ℕ) (hd : 2 ≤ d) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧ rejectionFraction k B = 1 := by
  obtain ⟨i,j,hij⟩ := exists_distinct_of_card_two (V := V) (by omega)
  refine ⟨purePairFamily d i j,purePair_equigenerated d i j,purePair_not_polymatroidal hd hij,?_⟩
  exact rejection_fraction_two (by omega) (purePair_equigenerated d i j) (purePair_not_polymatroidal hd hij)

end Characterizations

end
end CheckedCharacterizationsSource112

/-! ## Source: Characterizations.TermOrders.MatroidMatching -/
section CheckedCharacterizationsSource113

/-! # One-sided matching of two actual matroid bases

The Hall condition follows from the fundamental circuits and the rank inequality.
Every matched exchange is feasible at the same original base.
-/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.TermOrders
open Classical Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma matroid_basis_matching (M : Matroid α) (A B : Finset α)
    (hA : M.IsBase (A : Set α)) (hB : M.IsBase (B : Set α)) :
    ∃ f : A ≃ B, ∀ x : A, (f x).val ∈ M.fundCircuit x.val (B : Set α) := by
  let t : A → Finset B := fun x => univ.filter (fun y => y.val ∈ M.fundCircuit x.val (B : Set α))
  have hhall : ∀ S : Finset A, S.card ≤ (S.biUnion t).card := by
    intro S
    let T : Finset α := S.image Subtype.val
    let N : Finset α := (S.biUnion t).image Subtype.val
    have hTA : (T : Set α) ⊆ A := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact y.property
    have hNB : (N : Set α) ⊆ B := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact y.property
    have hTN : (T : Set α) ⊆ M.closure (N : Set α) := by
      intro x hx
      obtain ⟨x, hxS, rfl⟩ := mem_image.mp hx
      by_cases hxB : x.val ∈ B
      · apply M.subset_closure _ (hNB.trans hB.subset_ground)
        exact mem_image.mpr ⟨⟨x.val, hxB⟩, mem_biUnion.mpr ⟨x, hxS,
          mem_filter.mpr ⟨mem_univ _, M.mem_fundCircuit _ _⟩⟩, rfl⟩
      · have hC := hB.fundCircuit_isCircuit (hA.subset_ground x.property) hxB
        apply M.closure_subset_closure (show M.fundCircuit x.val (B : Set α) \ {x.val} ⊆ (N : Set α) from ?_)
          (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit _ _))
        intro y hy
        have hyB : y ∈ B := by
          rcases M.fundCircuit_subset_insert x.val (B : Set α) hy.1 with h | h
          · exact False.elim (hy.2 h)
          · exact h
        exact mem_image.mpr ⟨⟨y, hyB⟩, mem_biUnion.mpr ⟨x, hxS,
          mem_filter.mpr ⟨mem_univ _, hy.1⟩⟩, rfl⟩
    have hcard : T.card ≤ N.card := by
      have hh := (hA.indep.subset hTA).encard_le_eRk_of_subset hTN
      rw [M.eRk_closure_eq] at hh
      have hh' := hh.trans (M.eRk_le_encard (N : Set α))
      exact_mod_cast hh'
    simpa only [T, N, card_image_of_injective _ Subtype.coe_injective] using hcard
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  have hcard : Fintype.card A = Fintype.card B := by
    have h := hA.encard_eq_encard_of_isBase hB
    simpa only [Fintype.card_coe, Set.encard_coe_eq_coe_finsetCard, Nat.cast_inj] using h
  refine ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩), ?_⟩
  intro x
  exact (mem_filter.mp (hft x)).2

lemma matroid_matching_fixes_common (M : Matroid α) (A B : Finset α)
    (f : A ≃ B) (hf : ∀ x : A, (f x).val ∈ M.fundCircuit x.val (B : Set α))
    (x : A) (hx : x.val ∈ B) : (f x).val = x.val := by
  have h := hf x
  rw [M.fundCircuit_eq_of_mem hx] at h
  exact h

lemma matroid_matching_exchange (M : Matroid α) (A B : Finset α)
    (hA : M.IsBase (A : Set α)) (hB : M.IsBase (B : Set α))
    (f : A ≃ B) (hf : ∀ x : A, (f x).val ∈ M.fundCircuit x.val (B : Set α))
    (x : A) (hx : x.val ∉ B) :
    (f x).val ∉ A ∧ M.IsBase (insert x.val ((B : Set α) \ {(f x).val})) := by
  have hfxA : (f x).val ∉ A := by
    intro hyA
    let y : A := ⟨(f x).val, hyA⟩
    have hy : (f y).val = y.val := matroid_matching_fixes_common M A B f hf y (f x).property
    have he : f y = f x := Subtype.ext hy
    have he' := f.injective he
    exact hx ((congrArg Subtype.val he') ▸ (show y.val ∈ B from (f x).property))
  refine ⟨hfxA, hB.exchange_isBase_of_indep hx ?_⟩
  have hI := (hB.indep.mem_fundCircuit_iff (by rw [hB.closure_eq]; exact hA.subset_ground x.property) hx).mp (hf x)
  have hne : x.val ≠ (f x).val := fun h => hx (h ▸ (f x).property)
  simpa only [Set.insert_sdiff_singleton_comm hne] using hI

end Characterizations.TermOrders

end
end CheckedCharacterizationsSource113

/-! ## Source: Characterizations.TermOrders.Arbitrary -/
section CheckedCharacterizationsSource114

/-! # Linear quotients in every genuine monomial term order

The matching is on actual clone-matroid bases. Common clones are fixed; every
other matched pair gives an exchange feasible at the original base. Additivity
of the given Mathlib monomial order forces one matched exchange to move earlier.
-/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.TermOrders
open Classical Finset CommAlg.Polymatroid
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Decreasing order under the actual well-founded multiplicative monomial order. -/
def termBefore (m : MonomialOrder V) (a b : Exponent V) : Prop := m.toSyn b < m.toSyn a

lemma termBefore_irrefl (m : MonomialOrder V) (a : Exponent V) : ¬ termBefore m a a := lt_irrefl _
lemma termBefore_trans (m : MonomialOrder V) {a b c : Exponent V}
    (hab : termBefore m a b) (hbc : termBefore m b c) : termBefore m a c := hbc.trans hab
lemma termBefore_total (m : MonomialOrder V) (a b : Exponent V) (hab : a ≠ b) :
    termBefore m a b ∨ termBefore m b a := by
  exact lt_or_gt_of_ne (fun h => hab (m.toSyn.injective h)) |>.symm

private lemma clone_sum (m : MonomialOrder V) (d : ℕ) (A : Finset (Clone V d)) :
    (∑ x : A, m.toSyn (Finsupp.single x.val.1 1)) = m.toSyn (cloneCount A) := by
  simp only [cloneCount, map_sum]
  exact Finset.sum_attach A (fun x => m.toSyn (Finsupp.single x.1 1))

lemma termOrder_exchange {B : Family V} (hB : IsPolymatroidal B)
    (m : MonomialOrder V) {a b : Exponent V} (ha : a ∈ B) (hb : b ∈ B)
    (hab : termBefore m a b) :
    ∃ i j, b i < a i ∧ a j < b j ∧ exchange b j i ∈ B ∧ termBefore m (exchange b j i) b := by
  obtain ⟨d, hdeg⟩ := hB.1
  let A := canonicalClones d a
  let D := canonicalClones d b
  let M := cloneMatroid B ⟨a, ha⟩ d hdeg hB
  have hAc : cloneCount A = a := cloneCount_canonical d a (fun i =>
    (coordinate_le_degree a i).trans (by rw [hdeg a ha]; omega))
  have hDc : cloneCount D = b := cloneCount_canonical d b (fun i =>
    (coordinate_le_degree b i).trans (by rw [hdeg b hb]; omega))
  have hA : M.IsBase (A : Set (Clone V d)) := by
    change cloneCount (clonesOfSet (A : Set (Clone V d))) ∈ B
    rwa [clonesOfSet_coe, hAc]
  have hD : M.IsBase (D : Set (Clone V d)) := by
    change cloneCount (clonesOfSet (D : Set (Clone V d))) ∈ B
    rwa [clonesOfSet_coe, hDc]
  obtain ⟨f, hf⟩ := matroid_basis_matching M A D hA hD
  have hsumA : (∑ x : A, m.toSyn (Finsupp.single x.val.1 1)) = m.toSyn a := by
    rw [clone_sum, hAc]
  have hsumD : (∑ x : A, m.toSyn (Finsupp.single (f x).val.1 1)) = m.toSyn b := by
    rw [f.sum_comp (fun y : D => m.toSyn (Finsupp.single y.val.1 1)), clone_sum, hDc]
  have hsome : ∃ x : A, m.toSyn (Finsupp.single (f x).val.1 1) < m.toSyn (Finsupp.single x.val.1 1) := by
    by_contra hn
    push_neg at hn
    have hh := Finset.sum_le_sum (fun x (_ : x ∈ (univ : Finset A)) => hn x)
    rw [hsumA, hsumD] at hh
    exact (not_le_of_gt hab) hh
  obtain ⟨x, hx⟩ := hsome
  have hxD : x.val ∉ D := by
    intro h
    have he := matroid_matching_fixes_common M A D f hf x h
    rw [he] at hx
    exact (lt_irrefl _ hx)
  obtain ⟨hfA, hbase⟩ := matroid_matching_exchange M A D hA hD f hf x hxD
  have hi : b x.val.1 < a x.val.1 := by
    have h₁ : x.val.2.val < a x.val.1 := by exact (mem_filter.mp x.property).2
    have h₂ : ¬ x.val.2.val < b x.val.1 := by simpa [D, canonicalClones] using hxD
    omega
  have hj : a (f x).val.1 < b (f x).val.1 := by
    have h₁ : (f x).val.2.val < b (f x).val.1 := by exact (mem_filter.mp (f x).property).2
    have h₂ : ¬ (f x).val.2.val < a (f x).val.1 := by simpa [A, canonicalClones] using hfA
    omega
  have hw : exchange b (f x).val.1 x.val.1 ∈ B := by
    change cloneCount (clonesOfSet (insert x.val ((D : Set (Clone V d)) \ {(f x).val}))) ∈ B at hbase
    have he : clonesOfSet (insert x.val ((D : Set (Clone V d)) \ {(f x).val})) =
        insert x.val (D.erase (f x).val) := by
      ext z
      simp [and_comm]
    rw [he, cloneCount_exchange (f x).property hxD, hDc] at hbase
    exact hbase
  have hpos : 0 < b (f x).val.1 := Nat.zero_lt_of_lt hj
  have hle : Finsupp.single (f x).val.1 1 ≤ b := by
    intro v
    by_cases he : v = (f x).val.1
    · subst v; simpa only [Finsupp.single_eq_same] using Nat.succ_le_of_lt hpos
    · simp [Finsupp.single_apply, he, Ne.symm he]
  refine ⟨x.val.1, (f x).val.1, hi, hj, hw, ?_⟩
  change m.toSyn b < m.toSyn (exchange b (f x).val.1 x.val.1)
  calc
    m.toSyn b = m.toSyn (b - Finsupp.single (f x).val.1 1) +
        m.toSyn (Finsupp.single (f x).val.1 1) := by rw [← map_add, tsub_add_cancel_of_le hle]
    _ < m.toSyn (b - Finsupp.single (f x).val.1 1) + m.toSyn (Finsupp.single x.val.1 1) :=
      add_lt_add_of_le_of_lt le_rfl hx
    _ = m.toSyn (exchange b (f x).val.1 x.val.1) := by rw [← map_add]; rfl

/-- Theorem 3.12, for every actual admissible monomial term order, with literal
polynomial colon ideals and no replacement by a variable-permutation order. -/
theorem polymatroidal_termOrder_linearQuotients {k : Type*} [CommSemiring k]
    {B : Family V} (hB : IsPolymatroidal B) (m : MonomialOrder V) :
    HasLinearQuotients k B (termBefore m) := by
  apply linearQuotients_of_witness
  intro a ha b hb hab
  obtain ⟨i, j, hi, hj, hw, hwb⟩ := termOrder_exchange hB m ha hb hab
  have hji : j ≠ i := by intro he; subst j; omega
  exact ⟨exchange b j i, hw, hwb, i, Characterizations.exchange_sub_self b hji, hi⟩

end Characterizations.TermOrders

end
end CheckedCharacterizationsSource114

/-! ## Source: Characterizations.TermOrders.Characterization -/
section CheckedCharacterizationsSource115

/-! # The full arbitrary-term-order characterization -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid TermOrders
universe u
variable {V : Type u} {k : Type*} [Fintype V] [DecidableEq V] [CommSemiring k] [Nontrivial k]

theorem polymatroidal_iff_all_termOrder_linearQuotients {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) : IsPolymatroidal B ↔
      ∀ m : MonomialOrder.{u,u} V, HasLinearQuotients k B (termBefore m) := by
  constructor
  · exact fun hp m => polymatroidal_termOrder_linearQuotients hp m
  · intro h
    apply (polymatroidal_iff_universal_revlex (k := k) hB).mpr
    intro o
    have hw := witness_of_linearQuotients hB.antichain
      (termBefore_irrefl (variableGradedRevlexOrder o)) (h (variableGradedRevlexOrder o))
    apply linearQuotients_of_witness
    intro a ha b hb hab
    have hdab : a.degree = b.degree := (hB a ha).trans (hB b hb).symm
    obtain ⟨w, hwB, hwb, i, hwi, hi⟩ := hw a ha b hb
      ((variableGradedRevlexOrder_decreasing_iff o a b hdab).mpr hab)
    exact ⟨w, hwB, (variableGradedRevlexOrder_decreasing_iff o w b
      ((hB w hwB).trans (hB b hb).symm)).mp hwb, i, hwi, hi⟩

end Characterizations

end
end CheckedCharacterizationsSource115

/-! ## Source: Characterizations.UniversalLocalization -/
section CheckedCharacterizationsSource116

/-! # Universal pure reverse-lexicographic quotients survive localization -/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Corollary 3.11. `localFamily` is the actual minimal generator family of
`Ideal.map (localizationHom U) (monomialIdeal k B)`, as established in
`Localization.monomialIdeal_localFamily`. -/
theorem universal_pure_revlex_localization {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hB : Antichain B)
    (h : ∀ o : VariableOrder V, HasLinearQuotients k B (variableRevlex o))
    (U : Finset V) (o : VariableOrder U) :
    HasLinearQuotients k (localFamily B U) (variableRevlex o) := by
  have hp := (polymatroidal_iff_universal_pure_revlex hB).mpr h
  exact polymatroidal_variable_linearQuotients (localFamily_polymatroidal hp U).2 o

end Characterizations

end
end CheckedCharacterizationsSource116

/-! ## Source: Characterizations.ZeroRegularity -/
section CheckedCharacterizationsSource117

/-!
# The zero-ideal obstruction to an unrestricted regularity formula

The paper admits the zero ideal among polymatroidal ideals. Its Tor support is
empty, so the maximum defining regularity is not attained at any natural number.
Nevertheless every maximal-ideal power times zero is polymatroidal, and the least
such exponent is zero. This is an explicit boundary-case obstruction to reading
Proposition 4.1's regularity conclusion without a nonzero-ideal restriction.
-/

noncomputable section

namespace Characterizations

open Classical CommAlg CommAlg.Polymatroid CommAlg.Koszul Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem zero_family_polymatroidal : IsPolymatroidal (∅ : Family V) := by
  refine ⟨⟨0, ?_⟩, ?_⟩ <;> simp [Equigenerated, ExchangeAxiom]

theorem empty_family_equigenerated_two : Equigenerated (∅ : Family V) 2 := by
  simp [Equigenerated]

theorem empty_family_betti_zero (a : Exponent V) (i : ℕ) :
    bettiNumber (k := k) (∅ : Family V) a i = 0 := by
  by_contra h
  exact gradedBettiNonzero_empty a i
    ((bettiNumber_pos_iff _ _ _).mp (Nat.pos_of_ne_zero h))

/-- The actual zero ideal has no attained natural-number Tor regularity. -/
theorem zero_ideal_no_torRegularity :
    ¬ ∃ r : ℕ, IsTorRegularity (k := k) (∅ : Family V) r := by
  rintro ⟨r, _, i, a, ha, _⟩
  exact ha (empty_family_betti_zero a i)

theorem empty_localize_polymatroidal (U : Finset V) :
    IsPolymatroidal (localize (∅ : Family V) U) := by
  simpa [localize, minimalFamily] using (zero_family_polymatroidal (V := V))

theorem empty_thickening_polymatroidal (q : ℕ) :
    IsPolymatroidal (thickening (∅ : Family V) q) := by
  simpa [thickening] using (zero_family_polymatroidal (V := V))

theorem zero_ideal_least_polymatroidal_power :
    IsLeast {q : ℕ | IsPolymatroidal (thickening (∅ : Family V) q)} 0 :=
  ⟨empty_thickening_polymatroidal 0, fun _ _ => Nat.zero_le _⟩

theorem zero_ideal_integralClosure :
    {f : MvPolynomial V k | IntegralOverIdeal (⊥ : Ideal (MvPolynomial V k)) f} =
      (⊥ : Ideal (MvPolynomial V k)) := by
  ext f
  exact ⟨fun h => integrallyClosed_bot f h, fun h => integralOverIdeal_of_mem h⟩

theorem zero_ideal_closure_quotient_finiteLength :
    IsFiniteLength (MvPolynomial V k)
      (Strands.idealDifferenceQuotient (k := k) (∅ : Family V) ∅) := by
  apply Strands.idealDifferenceQuotient_finiteLength
  have he : {a : Exponent V | Contains (∅ : Family V) a ∧ ¬Contains ∅ a} = ∅ := by
    ext a
    simp
  rw [he]
  exact Set.finite_empty

/-- Multiplication by an actual maximal-ideal power cannot alter zero. -/
theorem zero_ideal_all_actual_powers_polymatroidal (q : ℕ) :
    IsPolymatroidalIdeal
      ((Ideal.span (Set.range (MvPolynomial.X : V → MvPolynomial V k))) ^ q * ⊥) := by
  simpa using (isPolymatroidalIdeal_bot (V := V) (k := k))

/-- Formal negation of the unrestricted attained-regularity version of the
"in particular" conclusion of Proposition 4.1. The counterexample is the
empty minimal generating family, representing the actual zero ideal. -/
theorem unrestricted_proposition41_regularity_false :
    ¬ (∀ B : Family V, Equigenerated B 2 →
      (∀ U : Finset V, U ⊂ univ → IsPolymatroidal (localize B U)) →
        ∃ r : ℕ, IsTorRegularity (k := k) B r ∧
          IsLeast {q : ℕ | IsPolymatroidal (thickening B q)} (r - 2)) := by
  intro h
  obtain ⟨r, hr, _⟩ := h ∅ empty_family_equigenerated_two
    (fun U _ => empty_localize_polymatroidal U)
  exact zero_ideal_no_torRegularity ⟨r, hr⟩

/-- The actual nonzero Tor degrees `j-i`, embedded in the integers with a
bottom element representing negative infinity. -/
def torRegularityDegrees (B : Family V) : Set (WithBot ℤ) :=
  {x | ∃ i a, bettiNumber (k := k) B a i ≠ 0 ∧
    x = (((a.degree : ℤ) - i : ℤ) : WithBot ℤ)}

theorem zero_ideal_regularityDegrees_empty :
    torRegularityDegrees (k := k) (∅ : Family V) = ∅ := by
  ext x
  simp [torRegularityDegrees, empty_family_betti_zero]

/-- Under the standard extended convention, regularity of zero is negative
infinity, the least upper bound of its empty actual Tor-degree support. -/
theorem zero_ideal_extended_regularity :
    IsLUB (torRegularityDegrees (k := k) (∅ : Family V)) ⊥ := by
  rw [zero_ideal_regularityDegrees_empty]
  exact isLUB_empty

/-- Subtracting the chosen generating degree two from negative infinity
still does not give the actual least polymatroidal power, which is zero.
Addition of the embedded integer `-2` is the usual finite degree shift. -/
theorem zero_ideal_extended_regularity_difference_ne_least :
    (0 : WithBot ℤ) ≠ (⊥ : WithBot ℤ) + ((-2 : ℤ) : WithBot ℤ) := by
  simp

/-- The unrestricted formula is false even when regularity is interpreted
as an extended least upper bound, with `reg(0) = -∞`. -/
theorem unrestricted_proposition41_extended_regularity_false :
    ¬ (∀ B : Family V, Equigenerated B 2 →
      (∀ U : Finset V, U ⊂ univ → IsPolymatroidal (localize B U)) →
        ∃ r : WithBot ℤ, IsLUB (torRegularityDegrees (k := k) B) r ∧
          ∃ q : ℕ, IsLeast {n : ℕ | IsPolymatroidal (thickening B n)} q ∧
            ((q : ℤ) : WithBot ℤ) = r + ((-2 : ℤ) : WithBot ℤ)) := by
  intro h
  obtain ⟨r, hr, q, _, he⟩ := h ∅ empty_family_equigenerated_two
    (fun U _ => empty_localize_polymatroidal U)
  have hr0 : r = ⊥ := hr.unique zero_ideal_extended_regularity
  simpa [hr0] using he

end Characterizations

end
end CheckedCharacterizationsSource117
