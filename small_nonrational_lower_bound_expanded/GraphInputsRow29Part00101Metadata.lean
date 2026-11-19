module
prelude
public meta import LowerSchemas.Metadata
public import GraphInputsRow29Part00101Data
public import SharedGraphCellPool
public import SharedSmallCellPoolChecked
public import GraphInputsRow25Part00012Metadata

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool FiniteChecks

cert_graph_alignment_2 000 0 0 64 25 00012 088
cert_graph_alignment_2 000 1 64 106 25 00012 088
cert_graph_alignment_checked_5 000 106
cert_graph_aligned_2 000
cert_graph_local_2 000 0 0 64 64
cert_graph_local_2 000 1 64 106 42
cert_graph_local_checked 000 106
cert_graph_kind_checked_2 000 25 00012 088
cert_graph_ridge_matrix 000 25 00012 088
cert_graph_edge_matrix_2 000 25 00012 088
cert_graph_missing_matrix_2 000 25 00012 088
cert_graph_matrix_checked_2 000
cert_graph_validity 000
cert_graph_vertex_width_2 000 25 00012 088
cert_graph_vertex_code_3 000 25 00012 088
cert_graph_literal 000
cert_graph_cells_exact_2 000

cert_graph_alignment_2 001 0 0 64 25 00012 089
cert_graph_alignment_2 001 1 64 105 25 00012 089
cert_graph_alignment_checked_5 001 105
cert_graph_aligned_2 001
cert_graph_local_2 001 0 0 64 64
cert_graph_local_2 001 1 64 105 41
cert_graph_local_checked 001 105
cert_graph_kind_checked_2 001 25 00012 089
cert_graph_ridge_matrix 001 25 00012 089
cert_graph_edge_matrix_2 001 25 00012 089
cert_graph_missing_matrix_2 001 25 00012 089
cert_graph_matrix_checked_2 001
cert_graph_validity 001
cert_graph_vertex_width_2 001 25 00012 089
cert_graph_vertex_code_3 001 25 00012 089
cert_graph_literal 001
cert_graph_cells_exact_2 001

cert_graph_alignment_3 002 0 0 64 64
cert_graph_alignment_3 002 1 64 112 48
cert_graph_alignment_checked_5 002 112
cert_graph_aligned_2 002
cert_graph_local_2 002 0 0 64 64
cert_graph_local_2 002 1 64 112 48
cert_graph_local_checked 002 112
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
cert_graph_alignment_3 003 1 64 112 48
cert_graph_alignment_checked_5 003 112
cert_graph_aligned_2 003
cert_graph_local_2 003 0 0 64 64
cert_graph_local_2 003 1 64 112 48
cert_graph_local_checked 003 112
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

cert_graph_alignment_2 004 0 0 64 25 00012 090
cert_graph_alignment_2 004 1 64 112 25 00012 090
cert_graph_alignment_checked_5 004 112
cert_graph_aligned_2 004
cert_graph_local_2 004 0 0 64 64
cert_graph_local_2 004 1 64 112 48
cert_graph_local_checked 004 112
cert_graph_kind_checked_2 004 25 00012 090
cert_graph_ridge_matrix 004 25 00012 090
cert_graph_edge_matrix_2 004 25 00012 090
cert_graph_missing_matrix_2 004 25 00012 090
cert_graph_matrix_checked_2 004
cert_graph_validity 004
cert_graph_vertex_width_2 004 25 00012 090
cert_graph_vertex_code_3 004 25 00012 090
cert_graph_literal 004
cert_graph_cells_exact_2 004

cert_graph_alignment_2 005 0 0 64 25 00012 091
cert_graph_alignment_2 005 1 64 111 25 00012 091
cert_graph_alignment_checked_5 005 111
cert_graph_aligned_2 005
cert_graph_local_2 005 0 0 64 64
cert_graph_local_2 005 1 64 111 47
cert_graph_local_checked 005 111
cert_graph_kind_checked_2 005 25 00012 091
cert_graph_ridge_matrix 005 25 00012 091
cert_graph_edge_matrix_2 005 25 00012 091
cert_graph_missing_matrix_2 005 25 00012 091
cert_graph_matrix_checked_2 005
cert_graph_validity 005
cert_graph_vertex_width_2 005 25 00012 091
cert_graph_vertex_code_3 005 25 00012 091
cert_graph_literal 005
cert_graph_cells_exact_2 005

cert_graph_alignment_2 006 0 0 64 25 00012 092
cert_graph_alignment_2 006 1 64 117 25 00012 092
cert_graph_alignment_checked_5 006 117
cert_graph_aligned_2 006
cert_graph_local_2 006 0 0 64 64
cert_graph_local_2 006 1 64 117 53
cert_graph_local_checked_2 006 117
cert_graph_kind_checked_2 006 25 00012 092
cert_graph_ridge_matrix 006 25 00012 092
cert_graph_edge_matrix_2 006 25 00012 092
cert_graph_missing_matrix_2 006 25 00012 092
cert_graph_matrix_checked_2 006
cert_graph_validity 006
cert_graph_vertex_width_2 006 25 00012 092
cert_graph_vertex_code_3 006 25 00012 092
cert_graph_literal 006
cert_graph_cells_exact_2 006

cert_graph_alignment_3 007 0 0 64 64
cert_graph_alignment_3 007 1 64 121 57
cert_graph_alignment_checked_5 007 121
cert_graph_aligned_2 007
cert_graph_local_2 007 0 0 64 64
cert_graph_local_2 007 1 64 121 57
cert_graph_local_checked 007 121
cert_graph_kind_checked 007
cert_graph_ridge_matrix_2 007
cert_graph_edge_matrix 007
cert_graph_missing_matrix 007
cert_graph_matrix_checked_2 007
cert_graph_validity 007
cert_graph_vertex_width 007
cert_graph_vertex_code 007
cert_graph_literal 007
cert_graph_cells_exact_2 007

cert_graph_alignment_2 008 0 0 64 25 00012 093
cert_graph_alignment_2 008 1 64 128 25 00012 093
cert_graph_alignment_2 008 2 128 130 25 00012 093
cert_graph_alignment_checked 008 130
cert_graph_aligned_2 008
cert_graph_local_2 008 0 0 64 64
cert_graph_local_2 008 1 64 128 64
cert_graph_local_2 008 2 128 130 2
cert_graph_local_checked_4 008 130
cert_graph_kind_checked_2 008 25 00012 093
cert_graph_ridge_matrix 008 25 00012 093
cert_graph_edge_matrix_2 008 25 00012 093
cert_graph_missing_matrix_2 008 25 00012 093
cert_graph_matrix_checked_2 008
cert_graph_validity 008
cert_graph_vertex_width_2 008 25 00012 093
cert_graph_vertex_code_3 008 25 00012 093
cert_graph_literal 008
cert_graph_cells_exact_2 008

cert_graph_alignment_2 009 0 0 64 25 00012 094
cert_graph_alignment_2 009 1 64 99 25 00012 094
cert_graph_alignment_checked_5 009 99
cert_graph_aligned_2 009
cert_graph_local_2 009 0 0 64 64
cert_graph_local_2 009 1 64 99 35
cert_graph_local_checked_2 009 99
cert_graph_kind_checked_2 009 25 00012 094
cert_graph_ridge_matrix 009 25 00012 094
cert_graph_edge_matrix_2 009 25 00012 094
cert_graph_missing_matrix_2 009 25 00012 094
cert_graph_matrix_checked_2 009
cert_graph_validity 009
cert_graph_vertex_width_2 009 25 00012 094
cert_graph_vertex_code_3 009 25 00012 094
cert_graph_literal 009
cert_graph_cells_exact_2 009

cert_graph_alignment_2 010 0 0 64 25 00012 095
cert_graph_alignment_2 010 1 64 118 25 00012 095
cert_graph_alignment_checked_5 010 118
cert_graph_aligned_2 010
cert_graph_local_2 010 0 0 64 64
cert_graph_local_2 010 1 64 118 54
cert_graph_local_checked 010 118
cert_graph_kind_checked_2 010 25 00012 095
cert_graph_ridge_matrix 010 25 00012 095
cert_graph_edge_matrix_2 010 25 00012 095
cert_graph_missing_matrix_2 010 25 00012 095
cert_graph_matrix_checked_2 010
cert_graph_validity 010
cert_graph_vertex_width_2 010 25 00012 095
cert_graph_vertex_code_3 010 25 00012 095
cert_graph_literal 010
cert_graph_cells_exact_2 010

cert_graph_alignment_2 011 0 0 64 25 00012 096
cert_graph_alignment_2 011 1 64 105 25 00012 096
cert_graph_alignment_checked_5 011 105
cert_graph_aligned_2 011
cert_graph_local_2 011 0 0 64 64
cert_graph_local_2 011 1 64 105 41
cert_graph_local_checked_2 011 105
cert_graph_kind_checked_2 011 25 00012 096
cert_graph_ridge_matrix 011 25 00012 096
cert_graph_edge_matrix_2 011 25 00012 096
cert_graph_missing_matrix_2 011 25 00012 096
cert_graph_matrix_checked_2 011
cert_graph_validity 011
cert_graph_vertex_width_2 011 25 00012 096
cert_graph_vertex_code_3 011 25 00012 096
cert_graph_literal 011
cert_graph_cells_exact_2 011

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101
