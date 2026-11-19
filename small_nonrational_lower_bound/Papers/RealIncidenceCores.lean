module
public import Papers.RankThreePatternRealizations
public import Papers.RationalityTenCoreNormalization

@[expose] public section

noncomputable section

/-!
# No real projective incidence core on eight point labels

The finite family classification is connected here to actual real point and
line vectors. Only used labels are required to be distinct projective
points; unused labels may carry arbitrary vectors. Thus the seven-point
branch does not acquire an artificial eighth-point hypothesis.
-/

namespace Papers.RationalityTen

open SmallTripleCores

def UsedPoint (L : Family) (i : Fin 8) : Prop :=
  ∃ T ∈ L, i ∈ T

/-- A concrete realization of a finite point-line incidence family. -/
structure RealProjectiveIncidence (L : Family) where
  point : Fin 8 → PlaneVector
  line : {T : Triple // T ∈ L} → PlaneVector
  point_independent : ∀ i j, UsedPoint L i → UsedPoint L j → i ≠ j →
    LinearIndependent ℝ ![point i, point j]
  line_independent : ∀ T U, T ≠ U →
    LinearIndependent ℝ ![line T, line U]
  incident : ∀ T i, i ∈ T.1 → dotProduct (line T) (point i) = 0

theorem mem_pullbackSupport_iff (s : Equiv.Perm (Fin 8)) (L : Family) (T : Triple) :
    T.image s.symm ∈ L ↔ T ∈ relabel s L := by
  classical
  constructor
  · intro h
    apply Finset.mem_image.mpr
    exact ⟨T.image s.symm, h, by simp [Finset.image_image]⟩
  · intro h
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp h
    simpa [Finset.image_image] using hU

theorem pullbackSupport_injective (s : Equiv.Perm (Fin 8)) :
    Function.Injective (fun T : Triple => T.image s.symm) := by
  intro T U h
  have h' := congrArg (fun V : Triple => V.image s) h
  simpa [Finset.image_image] using h'

namespace RealProjectiveIncidence

/-- Transport a realization by an actual permutation of point labels. -/
noncomputable def relabeled {L : Family} (D : RealProjectiveIncidence L)
    (s : Equiv.Perm (Fin 8)) : RealProjectiveIncidence (relabel s L) where
  point i := D.point (s.symm i)
  line T := D.line ⟨T.1.image s.symm, (mem_pullbackSupport_iff s L T.1).2 T.2⟩
  point_independent i j hi hj hij := by
    obtain ⟨T, hT, hiT⟩ := hi
    obtain ⟨U, hU, hjU⟩ := hj
    apply D.point_independent (s.symm i) (s.symm j)
    · exact ⟨T.image s.symm, (mem_pullbackSupport_iff s L T).2 hT,
        Finset.mem_image.mpr ⟨i, hiT, rfl⟩⟩
    · exact ⟨U.image s.symm, (mem_pullbackSupport_iff s L U).2 hU,
        Finset.mem_image.mpr ⟨j, hjU, rfl⟩⟩
    · exact fun h => hij (s.symm.injective h)
  line_independent T U hTU := by
    apply D.line_independent
    intro h
    apply hTU
    apply Subtype.ext
    exact pullbackSupport_injective s (congrArg Subtype.val h)
  incident T i hi := D.incident
    ⟨T.1.image s.symm, (mem_pullbackSupport_iff s L T.1).2 T.2⟩ (s.symm i)
    (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

/-- Distinct realized lines meet in at most one used projective point. -/
theorem pairSeparated {L : Family} (D : RealProjectiveIncidence L) :
    SmallTripleCores.pairSeparated L := by
  classical
  intro A hA B hB hAB
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hiA := (Finset.mem_inter.mp hi).1
  have hiB := (Finset.mem_inter.mp hi).2
  have hjA := (Finset.mem_inter.mp hj).1
  have hjB := (Finset.mem_inter.mp hj).2
  have hlines : LinearIndependent ℝ ![
      D.line ⟨A,hA⟩, D.line ⟨B,hB⟩] :=
    D.line_independent _ _ (fun h => hAB (congrArg Subtype.val h))
  have hpoints : LinearIndependent ℝ ![D.point i,D.point j] :=
    D.point_independent i j ⟨A,hA,hiA⟩ ⟨A,hA,hjA⟩ hij
  exact independent_incidence_pair_impossible
    (D.line ⟨A,hA⟩) (D.line ⟨B,hB⟩) (D.point i) (D.point j)
    hlines hpoints
    (D.incident ⟨A,hA⟩ i hiA) (D.incident ⟨A,hA⟩ j hjA)
    (D.incident ⟨B,hB⟩ i hiB) (D.incident ⟨B,hB⟩ j hjB)

end RealProjectiveIncidence

def fanoSupportEight (i : Fin 7) : Triple :=
  (fanoSupports i).image (Fin.castSucc : Fin 7 → Fin 8)

theorem canonicalSeven_not_realized (D : RealProjectiveIncidence canonicalSeven) : False := by
  have hmem : ∀ i, fanoSupportEight i ∈ canonicalSeven := by decide +kernel
  have hinj : Function.Injective fanoSupportEight := by decide +kernel
  have hcover : ∀ i : Fin 7, ∃ j, i.castSucc ∈ fanoSupportEight j := by decide +kernel
  have hused : ∀ i : Fin 7, UsedPoint canonicalSeven i.castSucc := by
    intro i
    obtain ⟨j, hj⟩ := hcover i
    exact ⟨fanoSupportEight j, hmem j, hj⟩
  apply fano_realization_impossible
    (fun i => D.point i.castSucc) (fun i => D.line ⟨fanoSupportEight i,hmem i⟩)
  · intro i j hij
    exact D.point_independent _ _ (hused i) (hused j)
      (fun h => hij (Fin.castSucc_injective 7 h))
  · intro i j hij
    apply D.line_independent
    intro h
    exact hij (hinj (congrArg Subtype.val h))
  · intro i j hij
    exact D.incident ⟨fanoSupportEight i,hmem i⟩ j.castSucc
      (Finset.mem_image.mpr ⟨j,hij,rfl⟩)

theorem paperMacLane_not_realized (D : RealProjectiveIncidence paperMacLane) : False := by
  have hmem : ∀ i, maclaneSupports i ∈ paperMacLane := by decide +kernel
  have hinj : Function.Injective maclaneSupports := by decide +kernel
  have hcover : ∀ i : Fin 8, ∃ j, i ∈ maclaneSupports j := by decide +kernel
  have hused : ∀ i : Fin 8, UsedPoint paperMacLane i := by
    intro i
    obtain ⟨j, hj⟩ := hcover i
    exact ⟨maclaneSupports j,hmem j,hj⟩
  apply maclane_realization_impossible D.point
    (fun i => D.line ⟨maclaneSupports i,hmem i⟩)
  · intro i j hij
    exact D.point_independent i j (hused i) (hused j) hij
  · intro i j hij
    apply D.line_independent
    intro h
    exact hij (hinj (congrArg Subtype.val h))
  · intro i j hij
    exact D.incident ⟨maclaneSupports i,hmem i⟩ j hij

/-- No real projective incidence family on at most eight used labels can
have at least three points on every line and at least three lines through
every used point. -/
theorem real_incidence_core_impossible
    (L : Family) (D : RealProjectiveIncidence L) (hne : L.Nonempty)
    (hlarge : ∀ T ∈ L, 3 ≤ T.card)
    (hdegree : ∀ v, UsedPoint L v → 3 ≤ degree L v) : False := by
  obtain ⟨s, hs⟩ := classify_incidence_core L hne hlarge D.pairSeparated hdegree
  rcases hs with hs | hs
  · exact canonicalSeven_not_realized (hs ▸ D.relabeled s)
  · exact paperMacLane_not_realized (hs ▸ D.relabeled s)

end Papers.RationalityTen
