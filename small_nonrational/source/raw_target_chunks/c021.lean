module
public import RawTargetChunks.C021A
public import RawTargetChunks.C021B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree021 : TargetTree :=
  .branch 64 chunkPart021A chunkPart021B

end Nonrational.TerminalData
