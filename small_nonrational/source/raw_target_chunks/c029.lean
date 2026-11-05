module
public import RawTargetChunks.C029A
public import RawTargetChunks.C029B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree029 : TargetTree :=
  .branch 64 chunkPart029A chunkPart029B

end Nonrational.TerminalData
