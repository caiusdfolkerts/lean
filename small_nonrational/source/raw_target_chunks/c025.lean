module
public import RawTargetChunks.C025A
public import RawTargetChunks.C025B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree025 : TargetTree :=
  .branch 64 chunkPart025A chunkPart025B

end Nonrational.TerminalData
