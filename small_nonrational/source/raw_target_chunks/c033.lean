module
public import RawTargetChunks.C033A
public import RawTargetChunks.C033B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree033 : TargetTree :=
  .branch 64 chunkPart033A chunkPart033B

end Nonrational.TerminalData
