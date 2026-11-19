module
prelude
public import GraphRouteCasesData
public import SharedSmallRoots25

@[expose] public section
noncomputable section

@[reducible] def Papers.RationalityTen.SharedEmptyKeys.Row25.offset : Nat :=
10105
def Papers.RationalityTen.SharedEmptyKeys.Row25.rootCode : Fin
    Papers.RationalityTen.SharedSmallRootCertificates.Row25.rootCount →
  Nat :=
fun i => (Papers.RationalityTen.SharedSmallRootCertificates.Row25.entry i).val.snd
def Papers.RationalityTen.SharedEmptyKeys.Row25.test : Nat → Bool :=
fun i =>
  Decidable.decide
    (Papers.RationalityTen.GraphRoutes.emptyRootKeys.entry (Papers.RationalityTen.SharedEmptyKeys.Row25.offset + i) =
      (25,
        Papers.RationalityTen.SharedSmallRootReplay.complement
          (Papers.RationalityTen.SharedEmptyKeys.Row25.rootCode
            (Fin.ofNat Papers.RationalityTen.SharedSmallRootCertificates.Row25.rootCount i))))

