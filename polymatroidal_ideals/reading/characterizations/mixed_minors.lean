import Characterizations.AmbientLocalization

/-! # Coordinate restrictions and mixed monomial minors

Restriction retains exactly those minimal exponent vectors supported on the
retained coordinates.  Localization then sets the other variables equal to
one and removes divisibility redundancies.  The identities below are proved
for these literal operations on generators.
-/

noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def restriction (B : Family V) (A : Finset V) : Family V :=
  B.filter (fun a => project A a = a)

@[simp] theorem mem_restriction {B : Family V} {A : Finset V} {a : Exponent V} :
    a ∈ restriction B A ↔ a ∈ B ∧ project A a = a := by
  simp [restriction]

theorem restriction_subset (B : Family V) (A : Finset V) : restriction B A ⊆ B :=
  fun _ h => (mem_restriction.mp h).1

theorem restriction_antichain {B : Family V} (hB : Antichain B) (A : Finset V) :
    Antichain (restriction B A) := by
  intro a ha b hb hab
  exact hB a (restriction_subset B A ha) b (restriction_subset B A hb) hab

theorem restriction_equigenerated {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (A : Finset V) : Equigenerated (restriction B A) d :=
  fun a ha => hB a (restriction_subset B A ha)

theorem project_inter (A U : Finset V) (a : Exponent V) :
    project U (project A a) = project (A ∩ U) a := by
  ext i
  by_cases hiA : i ∈ A <;> by_cases hiU : i ∈ U <;> simp [hiA,hiU]

theorem supported_of_le {A : Finset V} {a b : Exponent V}
    (hb : project A b = b) (hab : a ≤ b) : project A a = a := by
  ext i
  by_cases hi : i ∈ A
  · simp [hi]
  · have hbi := congrArg (fun c : Exponent V => c i) hb
    have habi := hab i
    simp only [project_apply,if_neg hi] at hbi ⊢
    omega

theorem contains_restriction (B : Family V) (A : Finset V) (a : Exponent V) :
    Contains (restriction B A) a ↔ Contains B (project A a) := by
  constructor
  · rintro ⟨b,hb,hba⟩
    obtain ⟨hb,hbs⟩ := mem_restriction.mp hb
    refine ⟨b,hb,?_⟩
    have hh := project_mono A hba
    simpa only [hbs] using hh
  · rintro ⟨b,hb,hba⟩
    exact ⟨b,mem_restriction.mpr ⟨hb,supported_of_le (project_project le_rfl a) hba⟩,
      hba.trans (project_le A a)⟩

theorem antichain_eq_of_contains_iff {B C : Family V} (hB : Antichain B)
    (hC : Antichain C) (h : ∀ a, Contains B a ↔ Contains C a) : B = C := by
  have hsub {D E : Family V} (hD : Antichain D)
      (hh : ∀ a, Contains D a ↔ Contains E a) : D ⊆ E := by
    intro a ha
    obtain ⟨b,hb,hba⟩ := (hh a).mp ⟨a,ha,le_rfl⟩
    obtain ⟨c,hc,hcb⟩ := (hh b).mpr ⟨b,hb,le_rfl⟩
    have hca : c = a := hD c hc a ha (hcb.trans hba)
    have hbe : b = a := le_antisymm hba (hca ▸ hcb)
    exact hbe ▸ hb
  exact subset_antisymm (hsub hB h) (hsub hC (fun a => (h a).symm))

theorem localize_localize (B : Family V) (A U : Finset V) :
    localize (localize B A) U = localize B (A ∩ U) := by
  apply antichain_eq_of_contains_iff (localize_antichain _ _) (localize_antichain _ _)
  intro a
  simp only [contains_localize]
  constructor
  · rintro ⟨b,hb,hba⟩
    obtain ⟨c,hc,rfl⟩ := localize_member hb
    exact ⟨c,hc,by simpa only [project_inter] using hba⟩
  · rintro ⟨c,hc,hca⟩
    obtain ⟨b,hb,hbc⟩ := localize_below (U := A) hc
    refine ⟨b,hb,?_⟩
    exact (project_mono U hbc).trans (by simpa only [project_inter] using hca)

theorem restriction_restriction (B : Family V) (A U : Finset V) :
    restriction (restriction B A) U = restriction B (A ∩ U) := by
  ext a
  simp only [mem_restriction]
  constructor
  · rintro ⟨⟨ha,hA⟩,hU⟩
    exact ⟨ha,by rw [← project_inter,hA,hU]⟩
  · rintro ⟨ha,hAU⟩
    have hA : project A a = a := by
      rw [← hAU,project_inter,inter_eq_left.mpr inter_subset_left]
    have hU : project U a = a := by
      rw [← hAU,project_inter,inter_eq_left.mpr inter_subset_right]
    exact ⟨⟨ha,hA⟩,hU⟩

/-- The mixed-minor identity (4.2), including removal of redundant projected
monomials on both sides. -/
theorem localize_restriction (B : Family V) {A U : Finset V} (hUA : U ⊆ A) :
    localize (restriction B A) U = restriction (localize B (U ∪ Aᶜ)) U := by
  apply antichain_eq_of_contains_iff (localize_antichain _ _)
    (restriction_antichain (localize_antichain _ _) _)
  intro a
  rw [contains_localize,contains_restriction,contains_localize]
  constructor
  · rintro ⟨b,hb,hba⟩
    obtain ⟨hb,hbs⟩ := mem_restriction.mp hb
    refine ⟨b,hb,?_⟩
    intro i
    have hbi := congrArg (fun c : Exponent V => c i) hbs
    have hi := hba i
    by_cases hiU : i ∈ U
    · simpa [hiU] using hi
    · by_cases hiA : i ∈ A
      · simp [hiU,hiA]
      · have hz : b i = 0 := by simpa only [project_apply,if_neg hiA] using hbi.symm
        simp [hiU,hiA,hz]
  · rintro ⟨b,hb,hba⟩
    have hbs : project A b = b := by
      ext i
      by_cases hiA : i ∈ A
      · simp [hiA]
      · have hiU : i ∉ U := fun h => hiA (hUA h)
        have hi := hba i
        simp only [project_apply,mem_union,mem_compl,hiU,hiA,
          not_false_eq_true,or_true,if_true,if_false] at hi
        simp only [project_apply,if_neg hiA]
        omega
    refine ⟨b,mem_restriction.mpr ⟨hb,hbs⟩,?_⟩
    intro i
    by_cases hiU : i ∈ U
    · have hi := hba i
      simpa only [project_apply,if_pos hiU,mem_union,hiU,true_or,if_true] using hi
    · simp [hiU]

def mixedMinor (B : Family V) (A U : Finset V) : Family V :=
  localize (restriction B A) U

theorem localize_restriction_inter (B : Family V) (A U : Finset V) :
    localize (restriction B A) U = localize (restriction B A) (A ∩ U) := by
  apply antichain_eq_of_contains_iff (localize_antichain _ _) (localize_antichain _ _)
  intro a
  simp only [contains_localize]
  apply exists_congr
  intro b
  apply and_congr_right
  intro hb
  have hbs := (mem_restriction.mp hb).2
  have he : project U b = project (A ∩ U) b := by rw [← project_inter,hbs]
  rw [he]

theorem restriction_locallyEquigenerated {B : Family V} (hl : LocallyEquigenerated B)
    (A : Finset V) : LocallyEquigenerated (restriction B A) := by
  intro U
  rw [localize_restriction_inter,localize_restriction B inter_subset_left]
  obtain ⟨d,hd⟩ := hl ((A ∩ U) ∪ Aᶜ)
  exact ⟨d,restriction_equigenerated hd _⟩

theorem localize_locallyEquigenerated {B : Family V} (hl : LocallyEquigenerated B)
    (A : Finset V) : LocallyEquigenerated (localize B A) := by
  intro U
  rw [localize_localize]
  exact hl (A ∩ U)

theorem mixedMinor_locallyEquigenerated {B : Family V} (hl : LocallyEquigenerated B)
    (A U : Finset V) : LocallyEquigenerated (mixedMinor B A U) :=
  localize_locallyEquigenerated (restriction_locallyEquigenerated hl A) U

theorem restriction_lowerRank {B : Family V} (hl : LocallyEquigenerated B)
    {A W : Finset V} (hK : (restriction B A).Nonempty) (hWA : W ⊆ A) :
    lowerRank (restriction B A) W = lowerRank B (W ∪ Aᶜ) := by
  have hB : B.Nonempty := hK.mono (restriction_subset B A)
  obtain ⟨b,hb⟩ := localize_nonempty hK W
  have hleft := localize_degree hK (restriction_locallyEquigenerated hl A) hb
  have hrightmem : b ∈ localize B (W ∪ Aᶜ) := by
    rw [localize_restriction B hWA] at hb
    exact restriction_subset _ _ hb
  exact hleft.symm.trans (localize_degree hB hl hrightmem)

theorem localize_nonempty_iff (B : Family V) (U : Finset V) :
    (localize B U).Nonempty ↔ B.Nonempty := by
  refine ⟨?_,fun h => localize_nonempty h U⟩
  rintro ⟨b,hb⟩
  obtain ⟨a,ha,_⟩ := localize_member hb
  exact ⟨a,ha⟩

theorem mixedMinor_lowerRank {B : Family V} (hl : LocallyEquigenerated B)
    {A U W : Finset V} (hM : (mixedMinor B A U).Nonempty)
    (hUA : U ⊆ A) (hWU : W ⊆ U) :
    lowerRank (mixedMinor B A U) W = lowerRank B (W ∪ Aᶜ) := by
  have hK : (restriction B A).Nonempty := (localize_nonempty_iff _ _).mp hM
  rw [mixedMinor,lowerRank_localize hK hWU]
  exact restriction_lowerRank hl hK (hWU.trans hUA)

theorem localize_mixedMinor (B : Family V) (A U W : Finset V) :
    localize (mixedMinor B A U) W = mixedMinor B A (U ∩ W) := by
  exact localize_localize _ _ _

/-- A further coordinate restriction of a mixed minor is again a mixed
minor of the original family.  The newly discarded coordinates are exactly
those in `U \ W`; the previously localized coordinates remain localized. -/
theorem restriction_mixedMinor (B : Family V) {A U W : Finset V}
    (hUA : U ⊆ A) (hWU : W ⊆ U) :
    restriction (mixedMinor B A U) W = mixedMinor B (A ∩ (W ∪ Uᶜ)) W := by
  have hWsub : W ⊆ A ∩ (W ∪ Uᶜ) := by
    intro i hi
    exact mem_inter.mpr ⟨hUA (hWU hi),mem_union_left _ hi⟩
  have he : W ∪ (A ∩ (W ∪ Uᶜ))ᶜ = U ∪ Aᶜ := by
    ext i
    have h1 := @hUA i
    have h2 := @hWU i
    simp only [mem_union,mem_inter,mem_compl]
    tauto
  rw [mixedMinor,localize_restriction B hUA,restriction_restriction,
    inter_eq_right.mpr hWU,mixedMinor,localize_restriction B hWsub,he]

theorem restriction_polymatroidal {B : Family V} (hB : IsPolymatroidal B)
    (A : Finset V) : IsPolymatroidal (restriction B A) := by
  obtain ⟨d,hd⟩ := hB.1
  refine ⟨⟨d,restriction_equigenerated hd A⟩,?_⟩
  intro a ha b hb i hi
  obtain ⟨ha,haA⟩ := mem_restriction.mp ha
  obtain ⟨hb,hbA⟩ := mem_restriction.mp hb
  obtain ⟨j,hj,he⟩ := hB.2 a ha b hb i hi
  refine ⟨j,hj,mem_restriction.mpr ⟨he,?_⟩⟩
  ext x
  by_cases hx : x ∈ A
  · simp [hx]
  · have hax := congrArg (fun c : Exponent V => c x) haA
    have hbx := congrArg (fun c : Exponent V => c x) hbA
    have hxi : x ≠ i := by
      intro hh
      subst x
      simp only [project_apply,if_neg hx] at hax hbx
      omega
    have hxj : x ≠ j := by
      intro hh
      subst x
      simp only [project_apply,if_neg hx] at hax hbx
      omega
    simp only [project_apply,if_neg hx,exchange_apply,
      Finsupp.single_apply,if_neg hxi,if_neg hxj]
    simp only [project_apply,if_neg hx] at hax
    omega

theorem mixedMinor_polymatroidal {B : Family V} (hB : IsPolymatroidal B)
    (A U : Finset V) : IsPolymatroidal (mixedMinor B A U) :=
  localize_polymatroidal (restriction_polymatroidal hB A) U

end Characterizations
