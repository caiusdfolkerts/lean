module
public import RawTargetChunks.C018A
public import RawTargetChunks.C018B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree018 : TargetTree :=
  .branch 64 chunkPart018A chunkPart018B

end Nonrational.TerminalData
