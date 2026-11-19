module
public import Papers.RationalityTenSmallTripleCandidates
public import Papers.RationalityTenSmallQuadCores
public import Papers.RankThreeFinite.Batch00
public import Papers.RankThreeFinite.Batch01
public import Papers.RankThreeFinite.Batch02
public import Papers.RankThreeFinite.Batch03
public import Papers.RankThreeFinite.Batch04
public import Papers.RankThreeFinite.Batch05
public import Papers.RankThreeFinite.Batch06
public import Papers.RankThreeFinite.Batch07
public import Papers.RankThreeFinite.Batch08
public import Papers.RankThreeFinite.Batch09
public import Papers.RankThreeFinite.Batch10
public import Papers.RankThreeFinite.Batch11
public import Papers.RankThreeFinite.Batch12
public import Papers.RankThreeFinite.Batch13
public import Papers.RankThreeFinite.Batch14
public import Papers.RankThreeFinite.Batch15
public import Papers.RankThreeFinite.Batch16
public import Papers.RankThreeFinite.Batch17
public import Papers.RankThreeFinite.Batch18
public import Papers.RankThreeFinite.Batch19
public import Papers.RankThreeFinite.Batch20
public import Papers.RankThreeFinite.Batch21
public import Papers.RankThreeFinite.Batch22
public import Papers.RankThreeFinite.Batch23
public import Papers.RankThreeFinite.Batch24
public import Papers.RankThreeFinite.Batch25
public import Papers.RankThreeFinite.Batch26
public import Papers.RankThreeFinite.Batch27
public import Papers.RankThreeFinite.Batch28
public import Papers.RankThreeFinite.Batch29
public import Papers.RankThreeFinite.Batch30
public import Papers.RankThreeFinite.Batch31
public import Papers.RankThreeFinite.Batch32
public import Papers.RankThreeFinite.Batch33
public import Papers.RankThreeFinite.Batch34
public import Papers.RankThreeFinite.Batch35
public import Papers.RankThreeFinite.Batch36
public import Papers.RankThreeFinite.Batch37
public import Papers.RankThreeFinite.Batch38
public import Papers.RankThreeFinite.Batch39
public import Papers.RankThreeFinite.Batch40
public import Papers.RankThreeFinite.Batch41
public import Papers.RankThreeFinite.Batch42
public import Papers.RankThreeFinite.Batch43
public import Papers.RankThreeFinite.Batch44
public import Papers.RankThreeFinite.Batch45
public import Papers.RankThreeFinite.Batch46
public import Papers.RankThreeFinite.Batch47
public import Papers.RankThreeFinite.Batch48
public import Papers.RankThreeFinite.Batch49
public import Papers.RankThreeFinite.Batch50
public import Papers.RankThreeFinite.Batch51
public import Papers.RankThreeFinite.Batch52
public import Papers.RankThreeFinite.Batch53
public import Papers.RankThreeFinite.Batch54
public import Papers.RankThreeFinite.Batch55
public import Papers.RankThreeFinite.Batch56
public import Papers.RankThreeFinite.Batch57
public import Papers.RankThreeFinite.Batch58
public import Papers.RankThreeFinite.Batch59
public import Papers.RankThreeFinite.Batch60
public import Papers.RankThreeFinite.Batch61
public import Papers.RankThreeFinite.Batch62
public import Papers.RankThreeFinite.Batch63
public import Papers.RankThreeFinite.Batch64
public import Papers.RankThreeFinite.Batch65
public import Papers.RankThreeFinite.Batch66

@[expose] public section

namespace Papers.RationalityTen.SmallTripleCores
attribute [local instance 2000] Finset.decidableDforallFinset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem forall_powersetCard_insert_cases
    (x : Triple) (s : Family) (hx : x ∉ s) (k : ℕ)
    (P : Family → Prop)
    (h0 : ∀ T ∈ s.powersetCard (k+1), P T)
    (h1 : ∀ T ∈ s.powersetCard k, P (insert x T)) :
    ∀ T ∈ (insert x s).powersetCard (k+1), P T := by
  intro T hT
  rw [Finset.powersetCard_succ_insert hx k] at hT
  rcases Finset.mem_union.mp hT with hT | hT
  · exact h0 T hT
  · obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hT
    exact h1 U hU

theorem eight_models_complete :
    ∀ S ∈ eightCandidates.powersetCard 5, goodEight S →
      S ∈ (Finset.univ : Finset (Fin 8)).image eightModels := by
  change ∀ S ∈ ({{1,3,5},{1,3,6},{1,3,7},{1,4,5},{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family).powersetCard 5, goodEight S →
    S ∈ (Finset.univ : Finset (Fin 8)).image eightModels
  apply forall_powersetCard_insert_cases {1,3,5} ({{1,3,6},{1,3,7},{1,4,5},{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 4
  ·
    apply forall_powersetCard_insert_cases {1,3,6} ({{1,3,7},{1,4,5},{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 4
    ·
      apply forall_powersetCard_insert_cases {1,3,7} ({{1,4,5},{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 4
      ·
        apply forall_powersetCard_insert_cases {1,4,5} ({{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 4
        ·
          apply forall_powersetCard_insert_cases {1,4,6} ({{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 4
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 4
            ·
              apply forall_powersetCard_insert_cases {1,5,7} ({{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 4
              ·
                apply forall_powersetCard_insert_cases {1,6,7} ({{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 4
                ·
                  apply forall_powersetCard_insert_cases {2,3,5} ({{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 4
                  ·
                    apply forall_powersetCard_insert_cases {2,3,6} ({{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 4
                    ·
                      exact eight_models_batch_0
                    ·
                      exact eight_models_batch_1
                  ·
                    exact eight_models_batch_2
                ·
                  apply forall_powersetCard_insert_cases {2,3,5} ({{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                  ·
                    exact eight_models_batch_3
                  ·
                    exact eight_models_batch_4
              ·
                apply forall_powersetCard_insert_cases {1,6,7} ({{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                ·
                  apply forall_powersetCard_insert_cases {2,3,5} ({{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                  ·
                    exact eight_models_batch_5
                  ·
                    exact eight_models_batch_6
                ·
                  exact eight_models_batch_7
            ·
              apply forall_powersetCard_insert_cases {1,5,7} ({{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
              ·
                apply forall_powersetCard_insert_cases {1,6,7} ({{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                ·
                  apply forall_powersetCard_insert_cases {2,3,5} ({{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                  ·
                    exact eight_models_batch_8
                  ·
                    exact eight_models_batch_9
                ·
                  exact eight_models_batch_10
              ·
                exact eight_models_batch_11
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
            ·
              apply forall_powersetCard_insert_cases {1,5,7} ({{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
              ·
                apply forall_powersetCard_insert_cases {1,6,7} ({{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                ·
                  apply forall_powersetCard_insert_cases {2,3,5} ({{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                  ·
                    exact eight_models_batch_12
                  ·
                    exact eight_models_batch_13
                ·
                  exact eight_models_batch_14
              ·
                exact eight_models_batch_15
            ·
              exact eight_models_batch_16
        ·
          apply forall_powersetCard_insert_cases {1,4,6} ({{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
            ·
              apply forall_powersetCard_insert_cases {1,5,7} ({{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
              ·
                apply forall_powersetCard_insert_cases {1,6,7} ({{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                ·
                  apply forall_powersetCard_insert_cases {2,3,5} ({{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                  ·
                    exact eight_models_batch_17
                  ·
                    exact eight_models_batch_18
                ·
                  exact eight_models_batch_19
              ·
                exact eight_models_batch_20
            ·
              exact eight_models_batch_21
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
            ·
              exact eight_models_batch_22
            ·
              exact eight_models_batch_23
      ·
        apply forall_powersetCard_insert_cases {1,4,5} ({{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
        ·
          apply forall_powersetCard_insert_cases {1,4,6} ({{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
            ·
              apply forall_powersetCard_insert_cases {1,5,7} ({{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
              ·
                apply forall_powersetCard_insert_cases {1,6,7} ({{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                ·
                  apply forall_powersetCard_insert_cases {2,3,5} ({{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                  ·
                    exact eight_models_batch_24
                  ·
                    exact eight_models_batch_25
                ·
                  exact eight_models_batch_26
              ·
                exact eight_models_batch_27
            ·
              exact eight_models_batch_28
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
            ·
              exact eight_models_batch_29
            ·
              exact eight_models_batch_30
        ·
          apply forall_powersetCard_insert_cases {1,4,6} ({{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
            ·
              exact eight_models_batch_31
            ·
              exact eight_models_batch_32
          ·
            exact eight_models_batch_33
    ·
      apply forall_powersetCard_insert_cases {1,3,7} ({{1,4,5},{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
      ·
        apply forall_powersetCard_insert_cases {1,4,5} ({{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
        ·
          apply forall_powersetCard_insert_cases {1,4,6} ({{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
            ·
              apply forall_powersetCard_insert_cases {1,5,7} ({{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
              ·
                apply forall_powersetCard_insert_cases {1,6,7} ({{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                ·
                  apply forall_powersetCard_insert_cases {2,3,5} ({{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                  ·
                    exact eight_models_batch_34
                  ·
                    exact eight_models_batch_35
                ·
                  exact eight_models_batch_36
              ·
                exact eight_models_batch_37
            ·
              exact eight_models_batch_38
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
            ·
              exact eight_models_batch_39
            ·
              exact eight_models_batch_40
        ·
          apply forall_powersetCard_insert_cases {1,4,6} ({{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
            ·
              exact eight_models_batch_41
            ·
              exact eight_models_batch_42
          ·
            exact eight_models_batch_43
      ·
        apply forall_powersetCard_insert_cases {1,4,5} ({{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
        ·
          apply forall_powersetCard_insert_cases {1,4,6} ({{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
            ·
              exact eight_models_batch_44
            ·
              exact eight_models_batch_45
          ·
            exact eight_models_batch_46
        ·
          exact eight_models_batch_47
  ·
    apply forall_powersetCard_insert_cases {1,3,6} ({{1,3,7},{1,4,5},{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
    ·
      apply forall_powersetCard_insert_cases {1,3,7} ({{1,4,5},{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
      ·
        apply forall_powersetCard_insert_cases {1,4,5} ({{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
        ·
          apply forall_powersetCard_insert_cases {1,4,6} ({{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
            ·
              apply forall_powersetCard_insert_cases {1,5,7} ({{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
              ·
                apply forall_powersetCard_insert_cases {1,6,7} ({{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                ·
                  apply forall_powersetCard_insert_cases {2,3,5} ({{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 3
                  ·
                    exact eight_models_batch_48
                  ·
                    exact eight_models_batch_49
                ·
                  exact eight_models_batch_50
              ·
                exact eight_models_batch_51
            ·
              exact eight_models_batch_52
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
            ·
              exact eight_models_batch_53
            ·
              exact eight_models_batch_54
        ·
          apply forall_powersetCard_insert_cases {1,4,6} ({{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
            ·
              exact eight_models_batch_55
            ·
              exact eight_models_batch_56
          ·
            exact eight_models_batch_57
      ·
        apply forall_powersetCard_insert_cases {1,4,5} ({{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
        ·
          apply forall_powersetCard_insert_cases {1,4,6} ({{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
            ·
              exact eight_models_batch_58
            ·
              exact eight_models_batch_59
          ·
            exact eight_models_batch_60
        ·
          exact eight_models_batch_61
    ·
      apply forall_powersetCard_insert_cases {1,3,7} ({{1,4,5},{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
      ·
        apply forall_powersetCard_insert_cases {1,4,5} ({{1,4,6},{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
        ·
          apply forall_powersetCard_insert_cases {1,4,6} ({{1,4,7},{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
          ·
            apply forall_powersetCard_insert_cases {1,4,7} ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family) (by decide) 2
            ·
              exact eight_models_batch_62
            ·
              exact eight_models_batch_63
          ·
            exact eight_models_batch_64
        ·
          exact eight_models_batch_65
      ·
        exact eight_models_batch_66

theorem eight_models_sound : ∀ i : Fin 8,
    eightModels i ∈ eightCandidates.powersetCard 5 ∧ goodEight (eightModels i) := by
  have h : ∀ i : Fin 8, eightModels i ⊆ eightCandidates ∧
      (eightModels i).card = 5 ∧ goodEight (eightModels i) := by decide
  intro i
  exact ⟨Finset.mem_powersetCard.mpr ⟨(h i).1,(h i).2.1⟩,(h i).2.2⟩

theorem eight_models_exhaustive :
    (eightCandidates.powersetCard 5).filter goodEight =
      (Finset.univ : Finset (Fin 8)).image eightModels := by
  ext S
  constructor
  · intro hS
    exact eight_models_complete S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2
  · intro hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_filter.mpr (eight_models_sound i)

def relabel (p : Equiv.Perm (Fin 8)) (S : Family) : Family :=
  S.image fun T => T.image p

theorem relabel_trans (p q : Equiv.Perm (Fin 8)) (S : Family) :
    relabel (p.trans q) S = relabel q (relabel p S) := by
  simp [relabel, Finset.image_image, Function.comp_def, Equiv.trans_apply]

def canonicalSeven : Family := rootStar ∪ sevenModels 0
def canonicalEight : Family := rootStar ∪ eightModels 0

def eightPermutation0 : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eightPermutation1 : Equiv.Perm (Fin 8) where
  toFun := ![0, 2, 1, 4, 3, 6, 5, 7]
  invFun := ![0, 2, 1, 4, 3, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eightPermutation2 : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 2, 3, 4, 6, 5, 7]
  invFun := ![0, 1, 2, 3, 4, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eightPermutation3 : Equiv.Perm (Fin 8) where
  toFun := ![0, 2, 1, 4, 3, 5, 6, 7]
  invFun := ![0, 2, 1, 4, 3, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eightPermutation4 : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 2, 4, 3, 5, 6, 7]
  invFun := ![0, 1, 2, 4, 3, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eightPermutation5 : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 2, 4, 3, 6, 5, 7]
  invFun := ![0, 1, 2, 4, 3, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eightPermutation6 : Equiv.Perm (Fin 8) where
  toFun := ![0, 2, 1, 3, 4, 6, 5, 7]
  invFun := ![0, 2, 1, 3, 4, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eightPermutation7 : Equiv.Perm (Fin 8) where
  toFun := ![0, 2, 1, 3, 4, 5, 6, 7]
  invFun := ![0, 2, 1, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eightPermutations : Fin 8 → Equiv.Perm (Fin 8) :=
  ![eightPermutation0, eightPermutation1, eightPermutation2, eightPermutation3, eightPermutation4, eightPermutation5, eightPermutation6, eightPermutation7]

theorem eight_relabelings_checked : ∀ i : Fin 8,
    relabel (eightPermutations i) (rootStar ∪ eightModels i) = canonicalEight := by
  decide +kernel

def sevenPermutations : Fin 2 → Equiv.Perm (Fin 8) :=
  ![Equiv.refl _, Equiv.swap 5 6]

theorem seven_relabelings_checked : ∀ i : Fin 2,
    relabel (sevenPermutations i) (rootStar ∪ sevenModels i) = canonicalSeven := by
  decide +kernel

def toPaper : Equiv.Perm (Fin 8) where
  toFun := ![0, 2, 4, 5, 7, 6, 3, 1]
  invFun := ![0, 7, 1, 6, 2, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Zero-based version of the paper's 135,246,147,238,168,257,367,458. -/
def paperMacLane : Family :=
  {{0, 2, 4}, {1, 3, 5}, {0, 3, 6}, {1, 2, 7},
    {0, 5, 7}, {1, 4, 6}, {2, 5, 6}, {3, 4, 7}}

theorem canonical_to_paper : relabel toPaper canonicalEight = paperMacLane := by
  decide +kernel

theorem seven_classification (S : Family) (hsub : S ⊆ sevenCandidates)
    (hcard : S.card = 4) (hgood : goodSeven S) :
    ∃ p : Equiv.Perm (Fin 8), relabel p (rootStar ∪ S) = canonicalSeven := by
  have hmem : S ∈ (sevenCandidates.powersetCard 4).filter goodSeven :=
    Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, hgood⟩
  rw [seven_models_exhaustive] at hmem
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  refine ⟨sevenPermutations i, ?_⟩
  rw [← hi]
  exact seven_relabelings_checked i

theorem eight_classification (S : Family) (hsub : S ⊆ eightCandidates)
    (hcard : S.card = 5) (hgood : goodEight S) :
    ∃ p : Equiv.Perm (Fin 8), relabel p (rootStar ∪ S) = paperMacLane := by
  have hmem : S ∈ (eightCandidates.powersetCard 5).filter goodEight :=
    Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, hgood⟩
  rw [eight_models_exhaustive] at hmem
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  refine ⟨(eightPermutations i).trans toPaper, ?_⟩
  rw [relabel_trans, ← hi, eight_relabelings_checked]
  exact canonical_to_paper


theorem degree_sdiff (L B : Family) (hBL : B ⊆ L) (v : Fin 8) :
    degree (L \ B) v = degree L v - degree B v := by
  unfold degree
  have heq : (L \ B).filter (fun T => v ∈ T) =
      L.filter (fun T => v ∈ T) \ B.filter (fun T => v ∈ T) := by
    apply Finset.ext
    intro T
    constructor
    · intro hT
      rcases Finset.mem_filter.mp hT with ⟨hT,hv⟩
      rcases Finset.mem_sdiff.mp hT with ⟨hL,hB⟩
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hL,hv⟩,
        fun h => hB (Finset.mem_filter.mp h).1⟩
    · intro hT
      rcases Finset.mem_sdiff.mp hT with ⟨hL,hB⟩
      rcases Finset.mem_filter.mp hL with ⟨hL,hv⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
        ⟨hL,fun h => hB (Finset.mem_filter.mpr ⟨h,hv⟩)⟩,hv⟩
  rw [heq]
  exact Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hBL)

theorem root_degree_neighbors : ∀ v ∈ neighbors, degree rootStar v = 1 := by
  decide +kernel

theorem root_degree_seven : degree rootStar 7 = 0 := by
  decide +kernel

theorem quad_root_degree_first : ∀ v ∈ quadFirstGroup, degree quadRootStar v = 1 := by
  decide +kernel

theorem pairSeparated_sdiff {L B : Family} (h : pairSeparated L) :
    pairSeparated (L \ B) := by
  intro A hA C hC hne
  exact h (Finset.mem_sdiff.mp hA).1 (Finset.mem_sdiff.mp hC).1 hne

/-- Every normalized root with line sizes4,3,3 contradicts the required
minimum point degree, even when the other lines are arbitrary ≥3-sets. -/
theorem no_quad_root_core (L : Family) (hroot : quadRootStar ⊆ L)
    (hlarge : ∀ T ∈ L, 3 ≤ T.card) (hpair : pairSeparated L)
    (hdegree : ∀ v ∈ quadFirstGroup, 3 ≤ degree L v) : False := by
  let S := L \ quadRootStar
  have hsub : S ⊆ quadCandidates := by
    intro T hT
    rcases Finset.mem_sdiff.mp hT with ⟨hTL, hTroot⟩
    apply quad_candidates_complete T (hlarge T hTL) hTroot
    intro R hR
    apply hpair hTL (hroot hR)
    intro heq
    exact hTroot (heq.symm ▸ hR)
  have hgood : goodQuad S := by
    constructor
    · intro v hv
      have hL := hdegree v hv
      have hB := quad_root_degree_first v hv
      have hh := degree_sdiff L quadRootStar hroot v
      change 2 ≤ degree (L \ quadRootStar) v
      omega
    · exact pairSeparated_sdiff hpair
  have hmem : S ∈ quadCandidates.powerset.filter goodQuad :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hgood⟩
  rw [quad_models_empty] at hmem
  exact Finset.notMem_empty _ hmem

theorem seven_root_core (L : Family) (hroot : rootStar ⊆ L)
    (htriples : ∀ T ∈ L, T.card = 3) (hseven : ∀ T ∈ L, 7 ∉ T)
    (hcard : L.card = 7) (hpair : pairSeparated L)
    (hdegree : ∀ v ∈ neighbors, degree L v = 3) :
    ∃ p : Equiv.Perm (Fin 8), relabel p L = canonicalSeven := by
  let S := L \ rootStar
  have hsub : S ⊆ sevenCandidates := by
    intro T hT
    rcases Finset.mem_sdiff.mp hT with ⟨hTL, hTroot⟩
    apply seven_candidates_from_root T (htriples T hTL) (hseven T hTL) hTroot
    intro R hR
    apply hpair hTL (hroot hR)
    intro heq
    exact hTroot (heq.symm ▸ hR)
  have hcardS : S.card = 4 := by
    have hh := Finset.card_sdiff_of_subset hroot
    have hstar : rootStar.card = 3 := by decide +kernel
    change (L \ rootStar).card = 4
    omega
  have hgood : goodSeven S := by
    constructor
    · intro v hv
      have hL := hdegree v hv
      have hB := root_degree_neighbors v hv
      have hh := degree_sdiff L rootStar hroot v
      change degree (L \ rootStar) v = 2
      omega
    · exact pairSeparated_sdiff hpair
  obtain ⟨p, hp⟩ := seven_classification S hsub hcardS hgood
  have hunion : rootStar ∪ S = L := Finset.union_sdiff_of_subset hroot
  exact ⟨p, hunion ▸ hp⟩

theorem eight_root_core (L : Family) (hroot : rootStar ⊆ L)
    (htriples : ∀ T ∈ L, T.card = 3) (hcard : L.card = 8)
    (hpair : pairSeparated L)
    (hdegree : ∀ v ∈ neighbors, degree L v = 3) (hseven : degree L 7 = 3) :
    ∃ p : Equiv.Perm (Fin 8), relabel p L = paperMacLane := by
  let S := L \ rootStar
  have hsub : S ⊆ eightCandidates := by
    intro T hT
    rcases Finset.mem_sdiff.mp hT with ⟨hTL, hTroot⟩
    apply eight_candidates_from_root T (htriples T hTL) hTroot
    intro R hR
    apply hpair hTL (hroot hR)
    intro heq
    exact hTroot (heq.symm ▸ hR)
  have hcardS : S.card = 5 := by
    have hh := Finset.card_sdiff_of_subset hroot
    have hstar : rootStar.card = 3 := by decide +kernel
    change (L \ rootStar).card = 5
    omega
  have hgood : goodEight S := by
    refine ⟨?_, ?_, pairSeparated_sdiff hpair⟩
    · intro v hv
      have hL := hdegree v hv
      have hB := root_degree_neighbors v hv
      have hh := degree_sdiff L rootStar hroot v
      change degree (L \ rootStar) v = 2
      omega
    · have hh := degree_sdiff L rootStar hroot 7
      have hB := root_degree_seven
      change degree (L \ rootStar) 7 = 3
      omega
  obtain ⟨p, hp⟩ := eight_classification S hsub hcardS hgood
  have hunion : rootStar ∪ S = L := Finset.union_sdiff_of_subset hroot
  exact ⟨p, hunion ▸ hp⟩

end Papers.RationalityTen.SmallTripleCores
