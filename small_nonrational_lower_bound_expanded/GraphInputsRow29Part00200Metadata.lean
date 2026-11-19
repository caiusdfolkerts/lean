module
prelude
public meta import LowerSchemas.Metadata
public import GraphInputsRow29Part00200Data
public import SharedGraphCellPool
public import SharedSmallCellPoolChecked
public import GraphInputsRow25Part00018Metadata

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool FiniteChecks

cert_graph_alignment_2 000 0 0 64 25 00018 030
cert_graph_alignment_2 000 1 64 101 25 00018 030
cert_graph_alignment_checked_5 000 101
cert_graph_aligned_2 000
cert_graph_local_2 000 0 0 64 64
cert_graph_local_2 000 1 64 101 37
cert_graph_local_checked 000 101
cert_graph_kind_checked_2 000 25 00018 030
cert_graph_ridge_matrix 000 25 00018 030
cert_graph_edge_matrix_2 000 25 00018 030
cert_graph_missing_matrix_2 000 25 00018 030
cert_graph_matrix_checked_2 000
cert_graph_validity 000
cert_graph_vertex_width_2 000 25 00018 030
cert_graph_vertex_code_3 000 25 00018 030
cert_graph_literal 000
cert_graph_cells_exact_2 000

cert_graph_alignment_2 001 0 0 64 25 00018 031
cert_graph_alignment_2 001 1 64 91 25 00018 031
cert_graph_alignment_checked_5 001 91
cert_graph_aligned_2 001
cert_graph_local_2 001 0 0 64 64
cert_graph_local_2 001 1 64 91 27
cert_graph_local_checked 001 91
cert_graph_kind_checked_2 001 25 00018 031
cert_graph_ridge_matrix 001 25 00018 031
cert_graph_edge_matrix_2 001 25 00018 031
cert_graph_missing_matrix_2 001 25 00018 031
cert_graph_matrix_checked_2 001
cert_graph_validity 001
cert_graph_vertex_width_2 001 25 00018 031
cert_graph_vertex_code_3 001 25 00018 031
cert_graph_literal 001
cert_graph_cells_exact_2 001

cert_graph_alignment_3 002 0 0 64 64
cert_graph_alignment_3 002 1 64 110 46
cert_graph_alignment_checked_5 002 110
cert_graph_aligned_2 002
cert_graph_local_2 002 0 0 64 64
cert_graph_local_2 002 1 64 110 46
cert_graph_local_checked 002 110
cert_graph_kind_checked 002
cert_graph_ridge_matrix_2 002
cert_graph_edge_matrix 002
cert_graph_missing_matrix 002
cert_graph_matrix_checked_2 002
cert_graph_validity 002
cert_graph_vertex_width 002
cert_graph_vertex_code 002
cert_graph_literal 002
cert_graph_cells_exact_2 002

cert_graph_alignment_3 003 0 0 64 64
cert_graph_alignment_3 003 1 64 92 28
cert_graph_alignment_checked_5 003 92
cert_graph_aligned_2 003
cert_graph_local_2 003 0 0 64 64
cert_graph_local_2 003 1 64 92 28
cert_graph_local_checked 003 92
cert_graph_kind_checked 003
cert_graph_ridge_matrix_2 003
cert_graph_edge_matrix 003
cert_graph_missing_matrix 003
cert_graph_matrix_checked_2 003
cert_graph_validity 003
cert_graph_vertex_width 003
cert_graph_vertex_code 003
cert_graph_literal 003
cert_graph_cells_exact_2 003

cert_graph_alignment_2 004 0 0 64 25 00018 032
cert_graph_alignment_2 004 1 64 111 25 00018 032
cert_graph_alignment_checked_5 004 111
cert_graph_aligned_2 004
cert_graph_local_2 004 0 0 64 64
cert_graph_local_2 004 1 64 111 47
cert_graph_local_checked 004 111
cert_graph_kind_checked_2 004 25 00018 032
cert_graph_ridge_matrix 004 25 00018 032
cert_graph_edge_matrix_2 004 25 00018 032
cert_graph_missing_matrix_2 004 25 00018 032
cert_graph_matrix_checked_2 004
cert_graph_validity 004
cert_graph_vertex_width_2 004 25 00018 032
cert_graph_vertex_code_3 004 25 00018 032
cert_graph_literal 004
cert_graph_cells_exact_2 004

cert_graph_alignment_2 005 0 0 64 25 00018 033
cert_graph_alignment_2 005 1 64 101 25 00018 033
cert_graph_alignment_checked_5 005 101
cert_graph_aligned_2 005
cert_graph_local_2 005 0 0 64 64
cert_graph_local_2 005 1 64 101 37
cert_graph_local_checked 005 101
cert_graph_kind_checked_2 005 25 00018 033
cert_graph_ridge_matrix 005 25 00018 033
cert_graph_edge_matrix_2 005 25 00018 033
cert_graph_missing_matrix_2 005 25 00018 033
cert_graph_matrix_checked_2 005
cert_graph_validity 005
cert_graph_vertex_width_2 005 25 00018 033
cert_graph_vertex_code_3 005 25 00018 033
cert_graph_literal 005
cert_graph_cells_exact_2 005

cert_graph_alignment_2 006 0 0 64 25 00018 034
cert_graph_alignment_2 006 1 64 115 25 00018 034
cert_graph_alignment_checked_5 006 115
cert_graph_aligned_2 006
cert_graph_local_2 006 0 0 64 64
cert_graph_local_2 006 1 64 115 51
cert_graph_local_checked 006 115
cert_graph_kind_checked_2 006 25 00018 034
cert_graph_ridge_matrix 006 25 00018 034
cert_graph_edge_matrix_2 006 25 00018 034
cert_graph_missing_matrix_2 006 25 00018 034
cert_graph_matrix_checked_2 006
cert_graph_validity 006
cert_graph_vertex_width_2 006 25 00018 034
cert_graph_vertex_code_3 006 25 00018 034
cert_graph_literal 006
cert_graph_cells_exact_2 006

cert_graph_alignment_2 007 0 0 64 25 00018 035
cert_graph_alignment_2 007 1 64 101 25 00018 035
cert_graph_alignment_checked_5 007 101
cert_graph_aligned_2 007
cert_graph_local_2 007 0 0 64 64
cert_graph_local_2 007 1 64 101 37
cert_graph_local_checked 007 101
cert_graph_kind_checked_2 007 25 00018 035
cert_graph_ridge_matrix 007 25 00018 035
cert_graph_edge_matrix_2 007 25 00018 035
cert_graph_missing_matrix_2 007 25 00018 035
cert_graph_matrix_checked_2 007
cert_graph_validity 007
cert_graph_vertex_width_2 007 25 00018 035
cert_graph_vertex_code_3 007 25 00018 035
cert_graph_literal 007
cert_graph_cells_exact_2 007

cert_graph_alignment_2 008 0 0 64 25 00018 036
cert_graph_alignment_2 008 1 64 107 25 00018 036
cert_graph_alignment_checked_5 008 107
cert_graph_aligned_2 008
cert_graph_local_2 008 0 0 64 64
cert_graph_local_2 008 1 64 107 43
cert_graph_local_checked 008 107
cert_graph_kind_checked_2 008 25 00018 036
cert_graph_ridge_matrix 008 25 00018 036
cert_graph_edge_matrix_2 008 25 00018 036
cert_graph_missing_matrix_2 008 25 00018 036
cert_graph_matrix_checked_2 008
cert_graph_validity 008
cert_graph_vertex_width_2 008 25 00018 036
cert_graph_vertex_code_3 008 25 00018 036
cert_graph_literal 008
cert_graph_cells_exact_2 008

cert_graph_alignment_2 009 0 0 64 25 00018 037
cert_graph_alignment_2 009 1 64 103 25 00018 037
cert_graph_alignment_checked_5 009 103
cert_graph_aligned_2 009
cert_graph_local_2 009 0 0 64 64
cert_graph_local_2 009 1 64 103 39
cert_graph_local_checked_2 009 103
cert_graph_kind_checked_2 009 25 00018 037
cert_graph_ridge_matrix 009 25 00018 037
cert_graph_edge_matrix_2 009 25 00018 037
cert_graph_missing_matrix_2 009 25 00018 037
cert_graph_matrix_checked_2 009
cert_graph_validity 009
cert_graph_vertex_width_2 009 25 00018 037
cert_graph_vertex_code_3 009 25 00018 037
cert_graph_literal 009
cert_graph_cells_exact_2 009

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200
