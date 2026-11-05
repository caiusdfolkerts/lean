module
prelude
public import GraphRouteCasesData
public import SharedSmallRoots26

@[expose] public section
noncomputable section

@[reducible] def Papers.RationalityTen.SharedEmptyKeys.Row26.offset : Nat :=
12471
def Papers.RationalityTen.SharedEmptyKeys.Row26.rootCode : Fin
    Papers.RationalityTen.SharedSmallRootCertificates.Row26.rootCount →
  Nat :=
fun i => (Papers.RationalityTen.SharedSmallRootCertificates.Row26.entry i).val.snd
def Papers.RationalityTen.SharedEmptyKeys.Row26.test : Nat → Bool :=
fun i =>
  Decidable.decide
    (Papers.RationalityTen.GraphRoutes.emptyRootKeys.entry (Papers.RationalityTen.SharedEmptyKeys.Row26.offset + i) =
      (26,
        Papers.RationalityTen.SharedSmallRootReplay.complement
          (Papers.RationalityTen.SharedEmptyKeys.Row26.rootCode
            (Fin.ofNat Papers.RationalityTen.SharedSmallRootCertificates.Row26.rootCount i))))

