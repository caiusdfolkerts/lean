module
prelude
public meta import LowerSchemas.Metadata
public import GraphInputsRow27Part00006Data
public import SharedGraphCellPool
public import SharedSmallCellPoolChecked
public import GraphInputsRow24Part00024Metadata
public import GraphInputsRow24Part00025Metadata
public import GraphInputsRow24Part00026Metadata
public import GraphInputsRow24Part00027Metadata
public import GraphInputsRow24Part00028Metadata
public import GraphInputsRow24Part00029Metadata
public import GraphInputsRow24Part00030Metadata
public import GraphInputsRow24Part00031Metadata
public import GraphInputsRow24Part00032Metadata
public import GraphInputsRow24Part00033Metadata
public import GraphInputsRow24Part00034Metadata
public import GraphInputsRow24Part00035Metadata
public import GraphInputsRow26Part00022Metadata
public import GraphInputsRow26Part00024Metadata
public import GraphInputsRow26Part00026Metadata

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool FiniteChecks

cert_graph_alignment_2 000 0 0 64 24 00024 035
cert_graph_alignment_2 000 1 64 100 24 00024 035
cert_graph_alignment_checked_5 000 100
cert_graph_aligned_2 000
cert_graph_local_2 000 0 0 64 64
cert_graph_local_2 000 1 64 100 36
cert_graph_local_checked 000 100
cert_graph_kind_checked_2 000 24 00024 035
cert_graph_ridge_matrix 000 24 00024 035
cert_graph_edge_matrix_2 000 24 00024 035
cert_graph_missing_matrix_2 000 24 00024 035
cert_graph_matrix_checked_2 000
cert_graph_validity 000
cert_graph_vertex_width_2 000 24 00024 035
cert_graph_vertex_code_3 000 24 00024 035
cert_graph_literal 000
cert_graph_cells_exact_2 000

cert_graph_alignment_2 001 0 0 64 24 00024 036
cert_graph_alignment_2 001 1 64 101 24 00024 036
cert_graph_alignment_checked_5 001 101
cert_graph_aligned_2 001
cert_graph_local_2 001 0 0 64 64
cert_graph_local_2 001 1 64 101 37
cert_graph_local_checked 001 101
cert_graph_kind_checked_2 001 24 00024 036
cert_graph_ridge_matrix 001 24 00024 036
cert_graph_edge_matrix_2 001 24 00024 036
cert_graph_missing_matrix_2 001 24 00024 036
cert_graph_matrix_checked_2 001
cert_graph_validity 001
cert_graph_vertex_width_2 001 24 00024 036
cert_graph_vertex_code_3 001 24 00024 036
cert_graph_literal 001
cert_graph_cells_exact_2 001

cert_graph_alignment_2 002 0 0 64 24 00024 037
cert_graph_alignment_2 002 1 64 107 24 00024 037
cert_graph_alignment_checked_5 002 107
cert_graph_aligned_2 002
cert_graph_local_2 002 0 0 64 64
cert_graph_local_2 002 1 64 107 43
cert_graph_local_checked 002 107
cert_graph_kind_checked_2 002 24 00024 037
cert_graph_ridge_matrix 002 24 00024 037
cert_graph_edge_matrix_2 002 24 00024 037
cert_graph_missing_matrix_2 002 24 00024 037
cert_graph_matrix_checked_2 002
cert_graph_validity 002
cert_graph_vertex_width_2 002 24 00024 037
cert_graph_vertex_code_3 002 24 00024 037
cert_graph_literal 002
cert_graph_cells_exact_2 002

cert_graph_alignment_2 003 0 0 64 26 00022 011
cert_graph_alignment_2 003 1 64 108 26 00022 011
cert_graph_alignment_checked_5 003 108
cert_graph_aligned_2 003
cert_graph_local_2 003 0 0 64 64
cert_graph_local_2 003 1 64 108 44
cert_graph_local_checked 003 108
cert_graph_kind_checked_2 003 26 00022 011
cert_graph_ridge_matrix 003 26 00022 011
cert_graph_edge_matrix_2 003 26 00022 011
cert_graph_missing_matrix_2 003 26 00022 011
cert_graph_matrix_checked_2 003
cert_graph_validity 003
cert_graph_vertex_width_2 003 26 00022 011
cert_graph_vertex_code_3 003 26 00022 011
cert_graph_literal 003
cert_graph_cells_exact_2 003

cert_graph_alignment_2 004 0 0 64 24 00025 001
cert_graph_alignment_2 004 1 64 88 24 00025 001
cert_graph_alignment_checked_5 004 88
cert_graph_aligned_2 004
cert_graph_local_2 004 0 0 64 64
cert_graph_local_2 004 1 64 88 24
cert_graph_local_checked 004 88
cert_graph_kind_checked_2 004 24 00025 001
cert_graph_ridge_matrix 004 24 00025 001
cert_graph_edge_matrix_2 004 24 00025 001
cert_graph_missing_matrix_2 004 24 00025 001
cert_graph_matrix_checked_2 004
cert_graph_validity 004
cert_graph_vertex_width_2 004 24 00025 001
cert_graph_vertex_code_3 004 24 00025 001
cert_graph_literal 004
cert_graph_cells_exact_2 004

cert_graph_alignment_2 005 0 0 64 24 00025 007
cert_graph_alignment_2 005 1 64 87 24 00025 007
cert_graph_alignment_checked_5 005 87
cert_graph_aligned_2 005
cert_graph_local_2 005 0 0 64 64
cert_graph_local_2 005 1 64 87 23
cert_graph_local_checked 005 87
cert_graph_kind_checked_2 005 24 00025 007
cert_graph_ridge_matrix 005 24 00025 007
cert_graph_edge_matrix_2 005 24 00025 007
cert_graph_missing_matrix_2 005 24 00025 007
cert_graph_matrix_checked_2 005
cert_graph_validity 005
cert_graph_vertex_width_2 005 24 00025 007
cert_graph_vertex_code_3 005 24 00025 007
cert_graph_literal 005
cert_graph_cells_exact_2 005

cert_graph_alignment_2 006 0 0 64 24 00025 010
cert_graph_alignment_2 006 1 64 92 24 00025 010
cert_graph_alignment_checked_5 006 92
cert_graph_aligned_2 006
cert_graph_local_2 006 0 0 64 64
cert_graph_local_2 006 1 64 92 28
cert_graph_local_checked 006 92
cert_graph_kind_checked_2 006 24 00025 010
cert_graph_ridge_matrix 006 24 00025 010
cert_graph_edge_matrix_2 006 24 00025 010
cert_graph_missing_matrix_2 006 24 00025 010
cert_graph_matrix_checked_2 006
cert_graph_validity 006
cert_graph_vertex_width_2 006 24 00025 010
cert_graph_vertex_code_3 006 24 00025 010
cert_graph_literal 006
cert_graph_cells_exact_2 006

cert_graph_alignment_2 007 0 0 64 24 00025 011
cert_graph_alignment_2 007 1 64 87 24 00025 011
cert_graph_alignment_checked_5 007 87
cert_graph_aligned_2 007
cert_graph_local_2 007 0 0 64 64
cert_graph_local_2 007 1 64 87 23
cert_graph_local_checked 007 87
cert_graph_kind_checked_2 007 24 00025 011
cert_graph_ridge_matrix 007 24 00025 011
cert_graph_edge_matrix_2 007 24 00025 011
cert_graph_missing_matrix_2 007 24 00025 011
cert_graph_matrix_checked_2 007
cert_graph_validity 007
cert_graph_vertex_width_2 007 24 00025 011
cert_graph_vertex_code_3 007 24 00025 011
cert_graph_literal 007
cert_graph_cells_exact_2 007

cert_graph_alignment_2 008 0 0 64 24 00025 014
cert_graph_alignment_2 008 1 64 92 24 00025 014
cert_graph_alignment_checked_5 008 92
cert_graph_aligned_2 008
cert_graph_local_2 008 0 0 64 64
cert_graph_local_2 008 1 64 92 28
cert_graph_local_checked 008 92
cert_graph_kind_checked_2 008 24 00025 014
cert_graph_ridge_matrix 008 24 00025 014
cert_graph_edge_matrix_2 008 24 00025 014
cert_graph_missing_matrix_2 008 24 00025 014
cert_graph_matrix_checked_2 008
cert_graph_validity 008
cert_graph_vertex_width_2 008 24 00025 014
cert_graph_vertex_code_3 008 24 00025 014
cert_graph_literal 008
cert_graph_cells_exact_2 008

cert_graph_alignment_2 009 0 0 64 24 00025 021
cert_graph_alignment_2 009 1 64 90 24 00025 021
cert_graph_alignment_checked_5 009 90
cert_graph_aligned_2 009
cert_graph_local_2 009 0 0 64 64
cert_graph_local_2 009 1 64 90 26
cert_graph_local_checked 009 90
cert_graph_kind_checked_2 009 24 00025 021
cert_graph_ridge_matrix 009 24 00025 021
cert_graph_edge_matrix_2 009 24 00025 021
cert_graph_missing_matrix_2 009 24 00025 021
cert_graph_matrix_checked_2 009
cert_graph_validity 009
cert_graph_vertex_width_2 009 24 00025 021
cert_graph_vertex_code_3 009 24 00025 021
cert_graph_literal 009
cert_graph_cells_exact_2 009

cert_graph_alignment_2 010 0 0 64 24 00025 025
cert_graph_alignment_2 010 1 64 85 24 00025 025
cert_graph_alignment_checked_5 010 85
cert_graph_aligned_2 010
cert_graph_local_2 010 0 0 64 64
cert_graph_local_2 010 1 64 85 21
cert_graph_local_checked 010 85
cert_graph_kind_checked_2 010 24 00025 025
cert_graph_ridge_matrix 010 24 00025 025
cert_graph_edge_matrix_2 010 24 00025 025
cert_graph_missing_matrix_2 010 24 00025 025
cert_graph_matrix_checked_2 010
cert_graph_validity 010
cert_graph_vertex_width_2 010 24 00025 025
cert_graph_vertex_code_3 010 24 00025 025
cert_graph_literal 010
cert_graph_cells_exact_2 010

cert_graph_alignment_2 011 0 0 64 24 00025 028
cert_graph_alignment_2 011 1 64 84 24 00025 028
cert_graph_alignment_checked_5 011 84
cert_graph_aligned_2 011
cert_graph_local_2 011 0 0 64 64
cert_graph_local_2 011 1 64 84 20
cert_graph_local_checked 011 84
cert_graph_kind_checked_2 011 24 00025 028
cert_graph_ridge_matrix 011 24 00025 028
cert_graph_edge_matrix_2 011 24 00025 028
cert_graph_missing_matrix_2 011 24 00025 028
cert_graph_matrix_checked_2 011
cert_graph_validity 011
cert_graph_vertex_width_2 011 24 00025 028
cert_graph_vertex_code_3 011 24 00025 028
cert_graph_literal 011
cert_graph_cells_exact_2 011

cert_graph_alignment_2 012 0 0 64 24 00025 029
cert_graph_alignment_2 012 1 64 93 24 00025 029
cert_graph_alignment_checked_5 012 93
cert_graph_aligned_2 012
cert_graph_local_2 012 0 0 64 64
cert_graph_local_2 012 1 64 93 29
cert_graph_local_checked 012 93
cert_graph_kind_checked_2 012 24 00025 029
cert_graph_ridge_matrix 012 24 00025 029
cert_graph_edge_matrix_2 012 24 00025 029
cert_graph_missing_matrix_2 012 24 00025 029
cert_graph_matrix_checked_2 012
cert_graph_validity 012
cert_graph_vertex_width_2 012 24 00025 029
cert_graph_vertex_code_3 012 24 00025 029
cert_graph_literal 012
cert_graph_cells_exact_2 012

cert_graph_alignment_2 013 0 0 64 24 00026 001
cert_graph_alignment_2 013 1 64 88 24 00026 001
cert_graph_alignment_checked_5 013 88
cert_graph_aligned_2 013
cert_graph_local_2 013 0 0 64 64
cert_graph_local_2 013 1 64 88 24
cert_graph_local_checked 013 88
cert_graph_kind_checked_2 013 24 00026 001
cert_graph_ridge_matrix 013 24 00026 001
cert_graph_edge_matrix_2 013 24 00026 001
cert_graph_missing_matrix_2 013 24 00026 001
cert_graph_matrix_checked_2 013
cert_graph_validity 013
cert_graph_vertex_width_2 013 24 00026 001
cert_graph_vertex_code_3 013 24 00026 001
cert_graph_literal 013
cert_graph_cells_exact_2 013

cert_graph_alignment_2 014 0 0 64 24 00026 002
cert_graph_alignment_2 014 1 64 91 24 00026 002
cert_graph_alignment_checked_5 014 91
cert_graph_aligned_2 014
cert_graph_local_2 014 0 0 64 64
cert_graph_local_2 014 1 64 91 27
cert_graph_local_checked 014 91
cert_graph_kind_checked_2 014 24 00026 002
cert_graph_ridge_matrix 014 24 00026 002
cert_graph_edge_matrix_2 014 24 00026 002
cert_graph_missing_matrix_2 014 24 00026 002
cert_graph_matrix_checked_2 014
cert_graph_validity 014
cert_graph_vertex_width_2 014 24 00026 002
cert_graph_vertex_code_3 014 24 00026 002
cert_graph_literal 014
cert_graph_cells_exact_2 014

cert_graph_alignment_2 015 0 0 64 24 00026 021
cert_graph_alignment_2 015 1 64 89 24 00026 021
cert_graph_alignment_checked_5 015 89
cert_graph_aligned_2 015
cert_graph_local_2 015 0 0 64 64
cert_graph_local_2 015 1 64 89 25
cert_graph_local_checked 015 89
cert_graph_kind_checked_2 015 24 00026 021
cert_graph_ridge_matrix 015 24 00026 021
cert_graph_edge_matrix_2 015 24 00026 021
cert_graph_missing_matrix_2 015 24 00026 021
cert_graph_matrix_checked_2 015
cert_graph_validity 015
cert_graph_vertex_width_2 015 24 00026 021
cert_graph_vertex_code_3 015 24 00026 021
cert_graph_literal 015
cert_graph_cells_exact_2 015

cert_graph_alignment_2 016 0 0 64 24 00026 036
cert_graph_alignment_2 016 1 64 79 24 00026 036
cert_graph_alignment_checked_5 016 79
cert_graph_aligned_2 016
cert_graph_local_2 016 0 0 64 64
cert_graph_local_2 016 1 64 79 15
cert_graph_local_checked 016 79
cert_graph_kind_checked_2 016 24 00026 036
cert_graph_ridge_matrix 016 24 00026 036
cert_graph_edge_matrix_2 016 24 00026 036
cert_graph_missing_matrix_2 016 24 00026 036
cert_graph_matrix_checked_2 016
cert_graph_validity 016
cert_graph_vertex_width_2 016 24 00026 036
cert_graph_vertex_code_3 016 24 00026 036
cert_graph_literal 016
cert_graph_cells_exact_2 016

cert_graph_alignment_2 017 0 0 64 24 00026 037
cert_graph_alignment_2 017 1 64 78 24 00026 037
cert_graph_alignment_checked_5 017 78
cert_graph_aligned_2 017
cert_graph_local_2 017 0 0 64 64
cert_graph_local_2 017 1 64 78 14
cert_graph_local_checked 017 78
cert_graph_kind_checked_2 017 24 00026 037
cert_graph_ridge_matrix 017 24 00026 037
cert_graph_edge_matrix_2 017 24 00026 037
cert_graph_missing_matrix_2 017 24 00026 037
cert_graph_matrix_checked_2 017
cert_graph_validity 017
cert_graph_vertex_width_2 017 24 00026 037
cert_graph_vertex_code_3 017 24 00026 037
cert_graph_literal 017
cert_graph_cells_exact_2 017

cert_graph_alignment_2 018 0 0 64 24 00026 038
cert_graph_alignment_2 018 1 64 82 24 00026 038
cert_graph_alignment_checked_5 018 82
cert_graph_aligned_2 018
cert_graph_local_2 018 0 0 64 64
cert_graph_local_2 018 1 64 82 18
cert_graph_local_checked 018 82
cert_graph_kind_checked_2 018 24 00026 038
cert_graph_ridge_matrix 018 24 00026 038
cert_graph_edge_matrix_2 018 24 00026 038
cert_graph_missing_matrix_2 018 24 00026 038
cert_graph_matrix_checked_2 018
cert_graph_validity 018
cert_graph_vertex_width_2 018 24 00026 038
cert_graph_vertex_code_3 018 24 00026 038
cert_graph_literal 018
cert_graph_cells_exact_2 018

cert_graph_alignment_2 019 0 0 64 24 00026 039
cert_graph_alignment_2 019 1 64 83 24 00026 039
cert_graph_alignment_checked_5 019 83
cert_graph_aligned_2 019
cert_graph_local_2 019 0 0 64 64
cert_graph_local_2 019 1 64 83 19
cert_graph_local_checked 019 83
cert_graph_kind_checked_2 019 24 00026 039
cert_graph_ridge_matrix 019 24 00026 039
cert_graph_edge_matrix_2 019 24 00026 039
cert_graph_missing_matrix_2 019 24 00026 039
cert_graph_matrix_checked_2 019
cert_graph_validity 019
cert_graph_vertex_width_2 019 24 00026 039
cert_graph_vertex_code_3 019 24 00026 039
cert_graph_literal 019
cert_graph_cells_exact_2 019

cert_graph_alignment_2 020 0 0 64 24 00026 042
cert_graph_alignment_2 020 1 64 83 24 00026 042
cert_graph_alignment_checked_5 020 83
cert_graph_aligned_2 020
cert_graph_local_2 020 0 0 64 64
cert_graph_local_2 020 1 64 83 19
cert_graph_local_checked 020 83
cert_graph_kind_checked_2 020 24 00026 042
cert_graph_ridge_matrix 020 24 00026 042
cert_graph_edge_matrix_2 020 24 00026 042
cert_graph_missing_matrix_2 020 24 00026 042
cert_graph_matrix_checked_2 020
cert_graph_validity 020
cert_graph_vertex_width_2 020 24 00026 042
cert_graph_vertex_code_3 020 24 00026 042
cert_graph_literal 020
cert_graph_cells_exact_2 020

cert_graph_alignment_2 021 0 0 64 24 00026 043
cert_graph_alignment_2 021 1 64 88 24 00026 043
cert_graph_alignment_checked_5 021 88
cert_graph_aligned_2 021
cert_graph_local_2 021 0 0 64 64
cert_graph_local_2 021 1 64 88 24
cert_graph_local_checked 021 88
cert_graph_kind_checked_2 021 24 00026 043
cert_graph_ridge_matrix 021 24 00026 043
cert_graph_edge_matrix_2 021 24 00026 043
cert_graph_missing_matrix_2 021 24 00026 043
cert_graph_matrix_checked_2 021
cert_graph_validity 021
cert_graph_vertex_width_2 021 24 00026 043
cert_graph_vertex_code_3 021 24 00026 043
cert_graph_literal 021
cert_graph_cells_exact_2 021

cert_graph_alignment_2 022 0 0 64 24 00026 044
cert_graph_alignment_2 022 1 64 94 24 00026 044
cert_graph_alignment_checked_5 022 94
cert_graph_aligned_2 022
cert_graph_local_2 022 0 0 64 64
cert_graph_local_2 022 1 64 94 30
cert_graph_local_checked 022 94
cert_graph_kind_checked_2 022 24 00026 044
cert_graph_ridge_matrix 022 24 00026 044
cert_graph_edge_matrix_2 022 24 00026 044
cert_graph_missing_matrix_2 022 24 00026 044
cert_graph_matrix_checked_2 022
cert_graph_validity 022
cert_graph_vertex_width_2 022 24 00026 044
cert_graph_vertex_code_3 022 24 00026 044
cert_graph_literal 022
cert_graph_cells_exact_2 022

cert_graph_alignment_2 023 0 0 64 24 00027 000
cert_graph_alignment_2 023 1 64 87 24 00027 000
cert_graph_alignment_checked_5 023 87
cert_graph_aligned_2 023
cert_graph_local_2 023 0 0 64 64
cert_graph_local_2 023 1 64 87 23
cert_graph_local_checked 023 87
cert_graph_kind_checked_2 023 24 00027 000
cert_graph_ridge_matrix 023 24 00027 000
cert_graph_edge_matrix_2 023 24 00027 000
cert_graph_missing_matrix_2 023 24 00027 000
cert_graph_matrix_checked_2 023
cert_graph_validity 023
cert_graph_vertex_width_2 023 24 00027 000
cert_graph_vertex_code_3 023 24 00027 000
cert_graph_literal 023
cert_graph_cells_exact_2 023

cert_graph_alignment_2 024 0 0 64 24 00027 001
cert_graph_alignment_2 024 1 64 91 24 00027 001
cert_graph_alignment_checked_5 024 91
cert_graph_aligned_2 024
cert_graph_local_2 024 0 0 64 64
cert_graph_local_2 024 1 64 91 27
cert_graph_local_checked 024 91
cert_graph_kind_checked_2 024 24 00027 001
cert_graph_ridge_matrix 024 24 00027 001
cert_graph_edge_matrix_2 024 24 00027 001
cert_graph_missing_matrix_2 024 24 00027 001
cert_graph_matrix_checked_2 024
cert_graph_validity 024
cert_graph_vertex_width_2 024 24 00027 001
cert_graph_vertex_code_3 024 24 00027 001
cert_graph_literal 024
cert_graph_cells_exact_2 024

cert_graph_alignment_2 025 0 0 64 24 00027 002
cert_graph_alignment_2 025 1 64 94 24 00027 002
cert_graph_alignment_checked_5 025 94
cert_graph_aligned_2 025
cert_graph_local_2 025 0 0 64 64
cert_graph_local_2 025 1 64 94 30
cert_graph_local_checked 025 94
cert_graph_kind_checked_2 025 24 00027 002
cert_graph_ridge_matrix 025 24 00027 002
cert_graph_edge_matrix_2 025 24 00027 002
cert_graph_missing_matrix_2 025 24 00027 002
cert_graph_matrix_checked_2 025
cert_graph_validity 025
cert_graph_vertex_width_2 025 24 00027 002
cert_graph_vertex_code_3 025 24 00027 002
cert_graph_literal 025
cert_graph_cells_exact_2 025

cert_graph_alignment_2 026 0 0 64 24 00027 006
cert_graph_alignment_2 026 1 64 100 24 00027 006
cert_graph_alignment_checked_5 026 100
cert_graph_aligned_2 026
cert_graph_local_2 026 0 0 64 64
cert_graph_local_2 026 1 64 100 36
cert_graph_local_checked 026 100
cert_graph_kind_checked_2 026 24 00027 006
cert_graph_ridge_matrix 026 24 00027 006
cert_graph_edge_matrix_2 026 24 00027 006
cert_graph_missing_matrix_2 026 24 00027 006
cert_graph_matrix_checked_2 026
cert_graph_validity 026
cert_graph_vertex_width_2 026 24 00027 006
cert_graph_vertex_code_3 026 24 00027 006
cert_graph_literal 026
cert_graph_cells_exact_2 026

cert_graph_alignment_2 027 0 0 64 24 00027 009
cert_graph_alignment_2 027 1 64 85 24 00027 009
cert_graph_alignment_checked_5 027 85
cert_graph_aligned_2 027
cert_graph_local_2 027 0 0 64 64
cert_graph_local_2 027 1 64 85 21
cert_graph_local_checked 027 85
cert_graph_kind_checked_2 027 24 00027 009
cert_graph_ridge_matrix 027 24 00027 009
cert_graph_edge_matrix_2 027 24 00027 009
cert_graph_missing_matrix_2 027 24 00027 009
cert_graph_matrix_checked_2 027
cert_graph_validity 027
cert_graph_vertex_width_2 027 24 00027 009
cert_graph_vertex_code_3 027 24 00027 009
cert_graph_literal 027
cert_graph_cells_exact_2 027

cert_graph_alignment_2 028 0 0 64 24 00027 010
cert_graph_alignment_2 028 1 64 84 24 00027 010
cert_graph_alignment_checked_5 028 84
cert_graph_aligned_2 028
cert_graph_local_2 028 0 0 64 64
cert_graph_local_2 028 1 64 84 20
cert_graph_local_checked 028 84
cert_graph_kind_checked_2 028 24 00027 010
cert_graph_ridge_matrix 028 24 00027 010
cert_graph_edge_matrix_2 028 24 00027 010
cert_graph_missing_matrix_2 028 24 00027 010
cert_graph_matrix_checked_2 028
cert_graph_validity 028
cert_graph_vertex_width_2 028 24 00027 010
cert_graph_vertex_code_3 028 24 00027 010
cert_graph_literal 028
cert_graph_cells_exact_2 028

cert_graph_alignment_2 029 0 0 64 24 00027 019
cert_graph_alignment_2 029 1 64 93 24 00027 019
cert_graph_alignment_checked_5 029 93
cert_graph_aligned_2 029
cert_graph_local_2 029 0 0 64 64
cert_graph_local_2 029 1 64 93 29
cert_graph_local_checked 029 93
cert_graph_kind_checked_2 029 24 00027 019
cert_graph_ridge_matrix 029 24 00027 019
cert_graph_edge_matrix_2 029 24 00027 019
cert_graph_missing_matrix_2 029 24 00027 019
cert_graph_matrix_checked_2 029
cert_graph_validity 029
cert_graph_vertex_width_2 029 24 00027 019
cert_graph_vertex_code_3 029 24 00027 019
cert_graph_literal 029
cert_graph_cells_exact_2 029

cert_graph_alignment_2 030 0 0 64 24 00027 021
cert_graph_alignment_2 030 1 64 100 24 00027 021
cert_graph_alignment_checked_5 030 100
cert_graph_aligned_2 030
cert_graph_local_2 030 0 0 64 64
cert_graph_local_2 030 1 64 100 36
cert_graph_local_checked 030 100
cert_graph_kind_checked_2 030 24 00027 021
cert_graph_ridge_matrix 030 24 00027 021
cert_graph_edge_matrix_2 030 24 00027 021
cert_graph_missing_matrix_2 030 24 00027 021
cert_graph_matrix_checked_2 030
cert_graph_validity 030
cert_graph_vertex_width_2 030 24 00027 021
cert_graph_vertex_code_3 030 24 00027 021
cert_graph_literal 030
cert_graph_cells_exact_2 030

cert_graph_alignment_2 031 0 0 64 24 00028 000
cert_graph_alignment_2 031 1 64 87 24 00028 000
cert_graph_alignment_checked_5 031 87
cert_graph_aligned_2 031
cert_graph_local_2 031 0 0 64 64
cert_graph_local_2 031 1 64 87 23
cert_graph_local_checked 031 87
cert_graph_kind_checked_2 031 24 00028 000
cert_graph_ridge_matrix 031 24 00028 000
cert_graph_edge_matrix_2 031 24 00028 000
cert_graph_missing_matrix_2 031 24 00028 000
cert_graph_matrix_checked_2 031
cert_graph_validity 031
cert_graph_vertex_width_2 031 24 00028 000
cert_graph_vertex_code_3 031 24 00028 000
cert_graph_literal 031
cert_graph_cells_exact_2 031

cert_graph_alignment_2 032 0 0 64 24 00028 001
cert_graph_alignment_2 032 1 64 96 24 00028 001
cert_graph_alignment_checked_5 032 96
cert_graph_aligned_2 032
cert_graph_local_2 032 0 0 64 64
cert_graph_local_2 032 1 64 96 32
cert_graph_local_checked 032 96
cert_graph_kind_checked_2 032 24 00028 001
cert_graph_ridge_matrix 032 24 00028 001
cert_graph_edge_matrix_2 032 24 00028 001
cert_graph_missing_matrix_2 032 24 00028 001
cert_graph_matrix_checked_2 032
cert_graph_validity 032
cert_graph_vertex_width_2 032 24 00028 001
cert_graph_vertex_code_3 032 24 00028 001
cert_graph_literal 032
cert_graph_cells_exact_2 032

cert_graph_alignment_2 033 0 0 64 24 00028 007
cert_graph_alignment_2 033 1 64 93 24 00028 007
cert_graph_alignment_checked_5 033 93
cert_graph_aligned_2 033
cert_graph_local_2 033 0 0 64 64
cert_graph_local_2 033 1 64 93 29
cert_graph_local_checked 033 93
cert_graph_kind_checked_2 033 24 00028 007
cert_graph_ridge_matrix 033 24 00028 007
cert_graph_edge_matrix_2 033 24 00028 007
cert_graph_missing_matrix_2 033 24 00028 007
cert_graph_matrix_checked_2 033
cert_graph_validity 033
cert_graph_vertex_width_2 033 24 00028 007
cert_graph_vertex_code_3 033 24 00028 007
cert_graph_literal 033
cert_graph_cells_exact_2 033

cert_graph_alignment_2 034 0 0 64 24 00028 015
cert_graph_alignment_2 034 1 64 96 24 00028 015
cert_graph_alignment_checked_5 034 96
cert_graph_aligned_2 034
cert_graph_local_2 034 0 0 64 64
cert_graph_local_2 034 1 64 96 32
cert_graph_local_checked 034 96
cert_graph_kind_checked_2 034 24 00028 015
cert_graph_ridge_matrix 034 24 00028 015
cert_graph_edge_matrix_2 034 24 00028 015
cert_graph_missing_matrix_2 034 24 00028 015
cert_graph_matrix_checked_2 034
cert_graph_validity 034
cert_graph_vertex_width_2 034 24 00028 015
cert_graph_vertex_code_3 034 24 00028 015
cert_graph_literal 034
cert_graph_cells_exact_2 034

cert_graph_alignment_2 035 0 0 64 24 00028 018
cert_graph_alignment_2 035 1 64 88 24 00028 018
cert_graph_alignment_checked_5 035 88
cert_graph_aligned_2 035
cert_graph_local_2 035 0 0 64 64
cert_graph_local_2 035 1 64 88 24
cert_graph_local_checked 035 88
cert_graph_kind_checked_2 035 24 00028 018
cert_graph_ridge_matrix 035 24 00028 018
cert_graph_edge_matrix_2 035 24 00028 018
cert_graph_missing_matrix_2 035 24 00028 018
cert_graph_matrix_checked_2 035
cert_graph_validity 035
cert_graph_vertex_width_2 035 24 00028 018
cert_graph_vertex_code_3 035 24 00028 018
cert_graph_literal 035
cert_graph_cells_exact_2 035

cert_graph_alignment_2 036 0 0 64 24 00028 019
cert_graph_alignment_2 036 1 64 87 24 00028 019
cert_graph_alignment_checked_5 036 87
cert_graph_aligned_2 036
cert_graph_local_2 036 0 0 64 64
cert_graph_local_2 036 1 64 87 23
cert_graph_local_checked 036 87
cert_graph_kind_checked_2 036 24 00028 019
cert_graph_ridge_matrix 036 24 00028 019
cert_graph_edge_matrix_2 036 24 00028 019
cert_graph_missing_matrix_2 036 24 00028 019
cert_graph_matrix_checked_2 036
cert_graph_validity 036
cert_graph_vertex_width_2 036 24 00028 019
cert_graph_vertex_code_3 036 24 00028 019
cert_graph_literal 036
cert_graph_cells_exact_2 036

cert_graph_alignment_2 037 0 0 64 24 00028 022
cert_graph_alignment_2 037 1 64 92 24 00028 022
cert_graph_alignment_checked_5 037 92
cert_graph_aligned_2 037
cert_graph_local_2 037 0 0 64 64
cert_graph_local_2 037 1 64 92 28
cert_graph_local_checked 037 92
cert_graph_kind_checked_2 037 24 00028 022
cert_graph_ridge_matrix 037 24 00028 022
cert_graph_edge_matrix_2 037 24 00028 022
cert_graph_missing_matrix_2 037 24 00028 022
cert_graph_matrix_checked_2 037
cert_graph_validity 037
cert_graph_vertex_width_2 037 24 00028 022
cert_graph_vertex_code_3 037 24 00028 022
cert_graph_literal 037
cert_graph_cells_exact_2 037

cert_graph_alignment_2 038 0 0 64 24 00028 023
cert_graph_alignment_2 038 1 64 91 24 00028 023
cert_graph_alignment_checked_5 038 91
cert_graph_aligned_2 038
cert_graph_local_2 038 0 0 64 64
cert_graph_local_2 038 1 64 91 27
cert_graph_local_checked 038 91
cert_graph_kind_checked_2 038 24 00028 023
cert_graph_ridge_matrix 038 24 00028 023
cert_graph_edge_matrix_2 038 24 00028 023
cert_graph_missing_matrix_2 038 24 00028 023
cert_graph_matrix_checked_2 038
cert_graph_validity 038
cert_graph_vertex_width_2 038 24 00028 023
cert_graph_vertex_code_3 038 24 00028 023
cert_graph_literal 038
cert_graph_cells_exact_2 038

cert_graph_alignment_2 039 0 0 64 24 00029 002
cert_graph_alignment_2 039 1 64 105 24 00029 002
cert_graph_alignment_checked_5 039 105
cert_graph_aligned_2 039
cert_graph_local_2 039 0 0 64 64
cert_graph_local_2 039 1 64 105 41
cert_graph_local_checked 039 105
cert_graph_kind_checked_2 039 24 00029 002
cert_graph_ridge_matrix 039 24 00029 002
cert_graph_edge_matrix_2 039 24 00029 002
cert_graph_missing_matrix_2 039 24 00029 002
cert_graph_matrix_checked_2 039
cert_graph_validity 039
cert_graph_vertex_width_2 039 24 00029 002
cert_graph_vertex_code_3 039 24 00029 002
cert_graph_literal 039
cert_graph_cells_exact_2 039

cert_graph_alignment_2 040 0 0 64 24 00029 003
cert_graph_alignment_2 040 1 64 92 24 00029 003
cert_graph_alignment_checked_5 040 92
cert_graph_aligned_2 040
cert_graph_local_2 040 0 0 64 64
cert_graph_local_2 040 1 64 92 28
cert_graph_local_checked 040 92
cert_graph_kind_checked_2 040 24 00029 003
cert_graph_ridge_matrix 040 24 00029 003
cert_graph_edge_matrix_2 040 24 00029 003
cert_graph_missing_matrix_2 040 24 00029 003
cert_graph_matrix_checked_2 040
cert_graph_validity 040
cert_graph_vertex_width_2 040 24 00029 003
cert_graph_vertex_code_3 040 24 00029 003
cert_graph_literal 040
cert_graph_cells_exact_2 040

cert_graph_alignment_2 041 0 0 64 24 00029 009
cert_graph_alignment_2 041 1 64 87 24 00029 009
cert_graph_alignment_checked_5 041 87
cert_graph_aligned_2 041
cert_graph_local_2 041 0 0 64 64
cert_graph_local_2 041 1 64 87 23
cert_graph_local_checked 041 87
cert_graph_kind_checked_2 041 24 00029 009
cert_graph_ridge_matrix 041 24 00029 009
cert_graph_edge_matrix_2 041 24 00029 009
cert_graph_missing_matrix_2 041 24 00029 009
cert_graph_matrix_checked_2 041
cert_graph_validity 041
cert_graph_vertex_width_2 041 24 00029 009
cert_graph_vertex_code_3 041 24 00029 009
cert_graph_literal 041
cert_graph_cells_exact_2 041

cert_graph_alignment_2 042 0 0 64 24 00029 010
cert_graph_alignment_2 042 1 64 84 24 00029 010
cert_graph_alignment_checked_5 042 84
cert_graph_aligned_2 042
cert_graph_local_2 042 0 0 64 64
cert_graph_local_2 042 1 64 84 20
cert_graph_local_checked 042 84
cert_graph_kind_checked_2 042 24 00029 010
cert_graph_ridge_matrix 042 24 00029 010
cert_graph_edge_matrix_2 042 24 00029 010
cert_graph_missing_matrix_2 042 24 00029 010
cert_graph_matrix_checked_2 042
cert_graph_validity 042
cert_graph_vertex_width_2 042 24 00029 010
cert_graph_vertex_code_3 042 24 00029 010
cert_graph_literal 042
cert_graph_cells_exact_2 042

cert_graph_alignment_2 043 0 0 64 24 00029 014
cert_graph_alignment_2 043 1 64 87 24 00029 014
cert_graph_alignment_checked_5 043 87
cert_graph_aligned_2 043
cert_graph_local_2 043 0 0 64 64
cert_graph_local_2 043 1 64 87 23
cert_graph_local_checked 043 87
cert_graph_kind_checked_2 043 24 00029 014
cert_graph_ridge_matrix 043 24 00029 014
cert_graph_edge_matrix_2 043 24 00029 014
cert_graph_missing_matrix_2 043 24 00029 014
cert_graph_matrix_checked_2 043
cert_graph_validity 043
cert_graph_vertex_width_2 043 24 00029 014
cert_graph_vertex_code_3 043 24 00029 014
cert_graph_literal 043
cert_graph_cells_exact_2 043

cert_graph_alignment_2 044 0 0 64 24 00029 021
cert_graph_alignment_2 044 1 64 88 24 00029 021
cert_graph_alignment_checked_5 044 88
cert_graph_aligned_2 044
cert_graph_local_2 044 0 0 64 64
cert_graph_local_2 044 1 64 88 24
cert_graph_local_checked 044 88
cert_graph_kind_checked_2 044 24 00029 021
cert_graph_ridge_matrix 044 24 00029 021
cert_graph_edge_matrix_2 044 24 00029 021
cert_graph_missing_matrix_2 044 24 00029 021
cert_graph_matrix_checked_2 044
cert_graph_validity 044
cert_graph_vertex_width_2 044 24 00029 021
cert_graph_vertex_code_3 044 24 00029 021
cert_graph_literal 044
cert_graph_cells_exact_2 044

cert_graph_alignment_2 045 0 0 64 26 00024 020
cert_graph_alignment_2 045 1 64 99 26 00024 020
cert_graph_alignment_checked_5 045 99
cert_graph_aligned_2 045
cert_graph_local_2 045 0 0 64 64
cert_graph_local_2 045 1 64 99 35
cert_graph_local_checked 045 99
cert_graph_kind_checked_2 045 26 00024 020
cert_graph_ridge_matrix 045 26 00024 020
cert_graph_edge_matrix_2 045 26 00024 020
cert_graph_missing_matrix_2 045 26 00024 020
cert_graph_matrix_checked_2 045
cert_graph_validity 045
cert_graph_vertex_width_2 045 26 00024 020
cert_graph_vertex_code_3 045 26 00024 020
cert_graph_literal 045
cert_graph_cells_exact_2 045

cert_graph_alignment_2 046 0 0 64 24 00029 027
cert_graph_alignment_2 046 1 64 87 24 00029 027
cert_graph_alignment_checked_5 046 87
cert_graph_aligned_2 046
cert_graph_local_2 046 0 0 64 64
cert_graph_local_2 046 1 64 87 23
cert_graph_local_checked 046 87
cert_graph_kind_checked_2 046 24 00029 027
cert_graph_ridge_matrix 046 24 00029 027
cert_graph_edge_matrix_2 046 24 00029 027
cert_graph_missing_matrix_2 046 24 00029 027
cert_graph_matrix_checked_2 046
cert_graph_validity 046
cert_graph_vertex_width_2 046 24 00029 027
cert_graph_vertex_code_3 046 24 00029 027
cert_graph_literal 046
cert_graph_cells_exact_2 046

cert_graph_alignment_2 047 0 0 64 26 00024 026
cert_graph_alignment_2 047 1 64 86 26 00024 026
cert_graph_alignment_checked_5 047 86
cert_graph_aligned_2 047
cert_graph_local_2 047 0 0 64 64
cert_graph_local_2 047 1 64 86 22
cert_graph_local_checked 047 86
cert_graph_kind_checked_2 047 26 00024 026
cert_graph_ridge_matrix 047 26 00024 026
cert_graph_edge_matrix_2 047 26 00024 026
cert_graph_missing_matrix_2 047 26 00024 026
cert_graph_matrix_checked_2 047
cert_graph_validity 047
cert_graph_vertex_width_2 047 26 00024 026
cert_graph_vertex_code_3 047 26 00024 026
cert_graph_literal 047
cert_graph_cells_exact_2 047

cert_graph_alignment_2 048 0 0 64 26 00024 029
cert_graph_alignment_2 048 1 64 94 26 00024 029
cert_graph_alignment_checked_5 048 94
cert_graph_aligned_2 048
cert_graph_local_2 048 0 0 64 64
cert_graph_local_2 048 1 64 94 30
cert_graph_local_checked 048 94
cert_graph_kind_checked_2 048 26 00024 029
cert_graph_ridge_matrix 048 26 00024 029
cert_graph_edge_matrix_2 048 26 00024 029
cert_graph_missing_matrix_2 048 26 00024 029
cert_graph_matrix_checked_2 048
cert_graph_validity 048
cert_graph_vertex_width_2 048 26 00024 029
cert_graph_vertex_code_3 048 26 00024 029
cert_graph_literal 048
cert_graph_cells_exact_2 048

cert_graph_alignment_2 049 0 0 64 26 00024 030
cert_graph_alignment_2 049 1 64 99 26 00024 030
cert_graph_alignment_checked_5 049 99
cert_graph_aligned_2 049
cert_graph_local_2 049 0 0 64 64
cert_graph_local_2 049 1 64 99 35
cert_graph_local_checked 049 99
cert_graph_kind_checked_2 049 26 00024 030
cert_graph_ridge_matrix 049 26 00024 030
cert_graph_edge_matrix_2 049 26 00024 030
cert_graph_missing_matrix_2 049 26 00024 030
cert_graph_matrix_checked_2 049
cert_graph_validity 049
cert_graph_vertex_width_2 049 26 00024 030
cert_graph_vertex_code_3 049 26 00024 030
cert_graph_literal 049
cert_graph_cells_exact_2 049

cert_graph_alignment_2 050 0 0 64 24 00029 038
cert_graph_alignment_2 050 1 64 96 24 00029 038
cert_graph_alignment_checked_5 050 96
cert_graph_aligned_2 050
cert_graph_local_2 050 0 0 64 64
cert_graph_local_2 050 1 64 96 32
cert_graph_local_checked 050 96
cert_graph_kind_checked_2 050 24 00029 038
cert_graph_ridge_matrix 050 24 00029 038
cert_graph_edge_matrix_2 050 24 00029 038
cert_graph_missing_matrix_2 050 24 00029 038
cert_graph_matrix_checked_2 050
cert_graph_validity 050
cert_graph_vertex_width_2 050 24 00029 038
cert_graph_vertex_code_3 050 24 00029 038
cert_graph_literal 050
cert_graph_cells_exact_2 050

cert_graph_alignment_2 051 0 0 64 24 00030 001
cert_graph_alignment_2 051 1 64 87 24 00030 001
cert_graph_alignment_checked_5 051 87
cert_graph_aligned_2 051
cert_graph_local_2 051 0 0 64 64
cert_graph_local_2 051 1 64 87 23
cert_graph_local_checked 051 87
cert_graph_kind_checked_2 051 24 00030 001
cert_graph_ridge_matrix 051 24 00030 001
cert_graph_edge_matrix_2 051 24 00030 001
cert_graph_missing_matrix_2 051 24 00030 001
cert_graph_matrix_checked_2 051
cert_graph_validity 051
cert_graph_vertex_width_2 051 24 00030 001
cert_graph_vertex_code_3 051 24 00030 001
cert_graph_literal 051
cert_graph_cells_exact_2 051

cert_graph_alignment_2 052 0 0 64 24 00030 002
cert_graph_alignment_2 052 1 64 94 24 00030 002
cert_graph_alignment_checked_5 052 94
cert_graph_aligned_2 052
cert_graph_local_2 052 0 0 64 64
cert_graph_local_2 052 1 64 94 30
cert_graph_local_checked 052 94
cert_graph_kind_checked_2 052 24 00030 002
cert_graph_ridge_matrix 052 24 00030 002
cert_graph_edge_matrix_2 052 24 00030 002
cert_graph_missing_matrix_2 052 24 00030 002
cert_graph_matrix_checked_2 052
cert_graph_validity 052
cert_graph_vertex_width_2 052 24 00030 002
cert_graph_vertex_code_3 052 24 00030 002
cert_graph_literal 052
cert_graph_cells_exact_2 052

cert_graph_alignment_2 053 0 0 64 24 00030 005
cert_graph_alignment_2 053 1 64 92 24 00030 005
cert_graph_alignment_checked_5 053 92
cert_graph_aligned_2 053
cert_graph_local_2 053 0 0 64 64
cert_graph_local_2 053 1 64 92 28
cert_graph_local_checked 053 92
cert_graph_kind_checked_2 053 24 00030 005
cert_graph_ridge_matrix 053 24 00030 005
cert_graph_edge_matrix_2 053 24 00030 005
cert_graph_missing_matrix_2 053 24 00030 005
cert_graph_matrix_checked_2 053
cert_graph_validity 053
cert_graph_vertex_width_2 053 24 00030 005
cert_graph_vertex_code_3 053 24 00030 005
cert_graph_literal 053
cert_graph_cells_exact_2 053

cert_graph_alignment_2 054 0 0 64 26 00024 045
cert_graph_alignment_2 054 1 64 79 26 00024 045
cert_graph_alignment_checked_5 054 79
cert_graph_aligned_2 054
cert_graph_local_2 054 0 0 64 64
cert_graph_local_2 054 1 64 79 15
cert_graph_local_checked 054 79
cert_graph_kind_checked_2 054 26 00024 045
cert_graph_ridge_matrix 054 26 00024 045
cert_graph_edge_matrix_2 054 26 00024 045
cert_graph_missing_matrix_2 054 26 00024 045
cert_graph_matrix_checked_2 054
cert_graph_validity 054
cert_graph_vertex_width_2 054 26 00024 045
cert_graph_vertex_code_3 054 26 00024 045
cert_graph_literal 054
cert_graph_cells_exact_2 054

cert_graph_alignment_2 055 0 0 64 26 00024 046
cert_graph_alignment_2 055 1 64 79 26 00024 046
cert_graph_alignment_checked_5 055 79
cert_graph_aligned_2 055
cert_graph_local_2 055 0 0 64 64
cert_graph_local_2 055 1 64 79 15
cert_graph_local_checked 055 79
cert_graph_kind_checked_2 055 26 00024 046
cert_graph_ridge_matrix 055 26 00024 046
cert_graph_edge_matrix_2 055 26 00024 046
cert_graph_missing_matrix_2 055 26 00024 046
cert_graph_matrix_checked_2 055
cert_graph_validity 055
cert_graph_vertex_width_2 055 26 00024 046
cert_graph_vertex_code_3 055 26 00024 046
cert_graph_literal 055
cert_graph_cells_exact_2 055

cert_graph_alignment_2 056 0 0 64 24 00030 008
cert_graph_alignment_2 056 1 64 82 24 00030 008
cert_graph_alignment_checked_5 056 82
cert_graph_aligned_2 056
cert_graph_local_2 056 0 0 64 64
cert_graph_local_2 056 1 64 82 18
cert_graph_local_checked 056 82
cert_graph_kind_checked_2 056 24 00030 008
cert_graph_ridge_matrix 056 24 00030 008
cert_graph_edge_matrix_2 056 24 00030 008
cert_graph_missing_matrix_2 056 24 00030 008
cert_graph_matrix_checked_2 056
cert_graph_validity 056
cert_graph_vertex_width_2 056 24 00030 008
cert_graph_vertex_code_3 056 24 00030 008
cert_graph_literal 056
cert_graph_cells_exact_2 056

cert_graph_alignment_2 057 0 0 64 24 00030 020
cert_graph_alignment_2 057 1 64 90 24 00030 020
cert_graph_alignment_checked_5 057 90
cert_graph_aligned_2 057
cert_graph_local_2 057 0 0 64 64
cert_graph_local_2 057 1 64 90 26
cert_graph_local_checked 057 90
cert_graph_kind_checked_2 057 24 00030 020
cert_graph_ridge_matrix 057 24 00030 020
cert_graph_edge_matrix_2 057 24 00030 020
cert_graph_missing_matrix_2 057 24 00030 020
cert_graph_matrix_checked_2 057
cert_graph_validity 057
cert_graph_vertex_width_2 057 24 00030 020
cert_graph_vertex_code_3 057 24 00030 020
cert_graph_literal 057
cert_graph_cells_exact_2 057

cert_graph_alignment_2 058 0 0 64 24 00030 029
cert_graph_alignment_2 058 1 64 87 24 00030 029
cert_graph_alignment_checked_5 058 87
cert_graph_aligned_2 058
cert_graph_local_2 058 0 0 64 64
cert_graph_local_2 058 1 64 87 23
cert_graph_local_checked 058 87
cert_graph_kind_checked_2 058 24 00030 029
cert_graph_ridge_matrix 058 24 00030 029
cert_graph_edge_matrix_2 058 24 00030 029
cert_graph_missing_matrix_2 058 24 00030 029
cert_graph_matrix_checked_2 058
cert_graph_validity 058
cert_graph_vertex_width_2 058 24 00030 029
cert_graph_vertex_code_3 058 24 00030 029
cert_graph_literal 058
cert_graph_cells_exact_2 058

cert_graph_alignment_2 059 0 0 64 24 00030 030
cert_graph_alignment_2 059 1 64 86 24 00030 030
cert_graph_alignment_checked_5 059 86
cert_graph_aligned_2 059
cert_graph_local_2 059 0 0 64 64
cert_graph_local_2 059 1 64 86 22
cert_graph_local_checked 059 86
cert_graph_kind_checked_2 059 24 00030 030
cert_graph_ridge_matrix 059 24 00030 030
cert_graph_edge_matrix_2 059 24 00030 030
cert_graph_missing_matrix_2 059 24 00030 030
cert_graph_matrix_checked_2 059
cert_graph_validity 059
cert_graph_vertex_width_2 059 24 00030 030
cert_graph_vertex_code_3 059 24 00030 030
cert_graph_literal 059
cert_graph_cells_exact_2 059

cert_graph_alignment_2 060 0 0 64 24 00030 035
cert_graph_alignment_2 060 1 64 91 24 00030 035
cert_graph_alignment_checked_5 060 91
cert_graph_aligned_2 060
cert_graph_local_2 060 0 0 64 64
cert_graph_local_2 060 1 64 91 27
cert_graph_local_checked 060 91
cert_graph_kind_checked_2 060 24 00030 035
cert_graph_ridge_matrix 060 24 00030 035
cert_graph_edge_matrix_2 060 24 00030 035
cert_graph_missing_matrix_2 060 24 00030 035
cert_graph_matrix_checked_2 060
cert_graph_validity 060
cert_graph_vertex_width_2 060 24 00030 035
cert_graph_vertex_code_3 060 24 00030 035
cert_graph_literal 060
cert_graph_cells_exact_2 060

cert_graph_alignment_2 061 0 0 64 24 00031 008
cert_graph_alignment_2 061 1 64 97 24 00031 008
cert_graph_alignment_checked_5 061 97
cert_graph_aligned_2 061
cert_graph_local_2 061 0 0 64 64
cert_graph_local_2 061 1 64 97 33
cert_graph_local_checked 061 97
cert_graph_kind_checked_2 061 24 00031 008
cert_graph_ridge_matrix 061 24 00031 008
cert_graph_edge_matrix_2 061 24 00031 008
cert_graph_missing_matrix_2 061 24 00031 008
cert_graph_matrix_checked_2 061
cert_graph_validity 061
cert_graph_vertex_width_2 061 24 00031 008
cert_graph_vertex_code_3 061 24 00031 008
cert_graph_literal 061
cert_graph_cells_exact_2 061

cert_graph_alignment_2 062 0 0 64 24 00031 009
cert_graph_alignment_2 062 1 64 87 24 00031 009
cert_graph_alignment_checked_5 062 87
cert_graph_aligned_2 062
cert_graph_local_2 062 0 0 64 64
cert_graph_local_2 062 1 64 87 23
cert_graph_local_checked 062 87
cert_graph_kind_checked_2 062 24 00031 009
cert_graph_ridge_matrix 062 24 00031 009
cert_graph_edge_matrix_2 062 24 00031 009
cert_graph_missing_matrix_2 062 24 00031 009
cert_graph_matrix_checked_2 062
cert_graph_validity 062
cert_graph_vertex_width_2 062 24 00031 009
cert_graph_vertex_code_3 062 24 00031 009
cert_graph_literal 062
cert_graph_cells_exact_2 062

cert_graph_alignment_2 063 0 0 64 24 00031 011
cert_graph_alignment_2 063 1 64 104 24 00031 011
cert_graph_alignment_checked_5 063 104
cert_graph_aligned_2 063
cert_graph_local_2 063 0 0 64 64
cert_graph_local_2 063 1 64 104 40
cert_graph_local_checked 063 104
cert_graph_kind_checked_2 063 24 00031 011
cert_graph_ridge_matrix 063 24 00031 011
cert_graph_edge_matrix_2 063 24 00031 011
cert_graph_missing_matrix_2 063 24 00031 011
cert_graph_matrix_checked_2 063
cert_graph_validity 063
cert_graph_vertex_width_2 063 24 00031 011
cert_graph_vertex_code_3 063 24 00031 011
cert_graph_literal 063
cert_graph_cells_exact_2 063

cert_graph_alignment_2 064 0 0 64 24 00031 019
cert_graph_alignment_2 064 1 64 95 24 00031 019
cert_graph_alignment_checked_5 064 95
cert_graph_aligned_2 064
cert_graph_local_2 064 0 0 64 64
cert_graph_local_2 064 1 64 95 31
cert_graph_local_checked 064 95
cert_graph_kind_checked_2 064 24 00031 019
cert_graph_ridge_matrix 064 24 00031 019
cert_graph_edge_matrix_2 064 24 00031 019
cert_graph_missing_matrix_2 064 24 00031 019
cert_graph_matrix_checked_2 064
cert_graph_validity 064
cert_graph_vertex_width_2 064 24 00031 019
cert_graph_vertex_code_3 064 24 00031 019
cert_graph_literal 064
cert_graph_cells_exact_2 064

cert_graph_alignment_2 065 0 0 64 24 00031 021
cert_graph_alignment_2 065 1 64 90 24 00031 021
cert_graph_alignment_checked_5 065 90
cert_graph_aligned_2 065
cert_graph_local_2 065 0 0 64 64
cert_graph_local_2 065 1 64 90 26
cert_graph_local_checked 065 90
cert_graph_kind_checked_2 065 24 00031 021
cert_graph_ridge_matrix 065 24 00031 021
cert_graph_edge_matrix_2 065 24 00031 021
cert_graph_missing_matrix_2 065 24 00031 021
cert_graph_matrix_checked_2 065
cert_graph_validity 065
cert_graph_vertex_width_2 065 24 00031 021
cert_graph_vertex_code_3 065 24 00031 021
cert_graph_literal 065
cert_graph_cells_exact_2 065

cert_graph_alignment_2 066 0 0 64 24 00032 004
cert_graph_alignment_2 066 1 64 96 24 00032 004
cert_graph_alignment_checked_5 066 96
cert_graph_aligned_2 066
cert_graph_local_2 066 0 0 64 64
cert_graph_local_2 066 1 64 96 32
cert_graph_local_checked 066 96
cert_graph_kind_checked_2 066 24 00032 004
cert_graph_ridge_matrix 066 24 00032 004
cert_graph_edge_matrix_2 066 24 00032 004
cert_graph_missing_matrix_2 066 24 00032 004
cert_graph_matrix_checked_2 066
cert_graph_validity 066
cert_graph_vertex_width_2 066 24 00032 004
cert_graph_vertex_code_3 066 24 00032 004
cert_graph_literal 066
cert_graph_cells_exact_2 066

cert_graph_alignment_2 067 0 0 64 24 00032 005
cert_graph_alignment_2 067 1 64 99 24 00032 005
cert_graph_alignment_checked_5 067 99
cert_graph_aligned_2 067
cert_graph_local_2 067 0 0 64 64
cert_graph_local_2 067 1 64 99 35
cert_graph_local_checked 067 99
cert_graph_kind_checked_2 067 24 00032 005
cert_graph_ridge_matrix 067 24 00032 005
cert_graph_edge_matrix_2 067 24 00032 005
cert_graph_missing_matrix_2 067 24 00032 005
cert_graph_matrix_checked_2 067
cert_graph_validity 067
cert_graph_vertex_width_2 067 24 00032 005
cert_graph_vertex_code_3 067 24 00032 005
cert_graph_literal 067
cert_graph_cells_exact_2 067

cert_graph_alignment_2 068 0 0 64 24 00032 006
cert_graph_alignment_2 068 1 64 94 24 00032 006
cert_graph_alignment_checked_5 068 94
cert_graph_aligned_2 068
cert_graph_local_2 068 0 0 64 64
cert_graph_local_2 068 1 64 94 30
cert_graph_local_checked 068 94
cert_graph_kind_checked_2 068 24 00032 006
cert_graph_ridge_matrix 068 24 00032 006
cert_graph_edge_matrix_2 068 24 00032 006
cert_graph_missing_matrix_2 068 24 00032 006
cert_graph_matrix_checked_2 068
cert_graph_validity 068
cert_graph_vertex_width_2 068 24 00032 006
cert_graph_vertex_code_3 068 24 00032 006
cert_graph_literal 068
cert_graph_cells_exact_2 068

cert_graph_alignment_2 069 0 0 64 24 00032 007
cert_graph_alignment_2 069 1 64 91 24 00032 007
cert_graph_alignment_checked_5 069 91
cert_graph_aligned_2 069
cert_graph_local_2 069 0 0 64 64
cert_graph_local_2 069 1 64 91 27
cert_graph_local_checked 069 91
cert_graph_kind_checked_2 069 24 00032 007
cert_graph_ridge_matrix 069 24 00032 007
cert_graph_edge_matrix_2 069 24 00032 007
cert_graph_missing_matrix_2 069 24 00032 007
cert_graph_matrix_checked_2 069
cert_graph_validity 069
cert_graph_vertex_width_2 069 24 00032 007
cert_graph_vertex_code_3 069 24 00032 007
cert_graph_literal 069
cert_graph_cells_exact_2 069

cert_graph_alignment_2 070 0 0 64 24 00033 002
cert_graph_alignment_2 070 1 64 86 24 00033 002
cert_graph_alignment_checked_5 070 86
cert_graph_aligned_2 070
cert_graph_local_2 070 0 0 64 64
cert_graph_local_2 070 1 64 86 22
cert_graph_local_checked 070 86
cert_graph_kind_checked_2 070 24 00033 002
cert_graph_ridge_matrix 070 24 00033 002
cert_graph_edge_matrix_2 070 24 00033 002
cert_graph_missing_matrix_2 070 24 00033 002
cert_graph_matrix_checked_2 070
cert_graph_validity 070
cert_graph_vertex_width_2 070 24 00033 002
cert_graph_vertex_code_3 070 24 00033 002
cert_graph_literal 070
cert_graph_cells_exact_2 070

cert_graph_alignment_2 071 0 0 64 24 00033 007
cert_graph_alignment_2 071 1 64 92 24 00033 007
cert_graph_alignment_checked_5 071 92
cert_graph_aligned_2 071
cert_graph_local_2 071 0 0 64 64
cert_graph_local_2 071 1 64 92 28
cert_graph_local_checked 071 92
cert_graph_kind_checked_2 071 24 00033 007
cert_graph_ridge_matrix 071 24 00033 007
cert_graph_edge_matrix_2 071 24 00033 007
cert_graph_missing_matrix_2 071 24 00033 007
cert_graph_matrix_checked_2 071
cert_graph_validity 071
cert_graph_vertex_width_2 071 24 00033 007
cert_graph_vertex_code_3 071 24 00033 007
cert_graph_literal 071
cert_graph_cells_exact_2 071

cert_graph_alignment_2 072 0 0 64 24 00034 000
cert_graph_alignment_2 072 1 64 89 24 00034 000
cert_graph_alignment_checked_5 072 89
cert_graph_aligned_2 072
cert_graph_local_2 072 0 0 64 64
cert_graph_local_2 072 1 64 89 25
cert_graph_local_checked 072 89
cert_graph_kind_checked_2 072 24 00034 000
cert_graph_ridge_matrix 072 24 00034 000
cert_graph_edge_matrix_2 072 24 00034 000
cert_graph_missing_matrix_2 072 24 00034 000
cert_graph_matrix_checked_2 072
cert_graph_validity 072
cert_graph_vertex_width_2 072 24 00034 000
cert_graph_vertex_code_3 072 24 00034 000
cert_graph_literal 072
cert_graph_cells_exact_2 072

cert_graph_alignment_2 073 0 0 64 24 00034 004
cert_graph_alignment_2 073 1 64 90 24 00034 004
cert_graph_alignment_checked_5 073 90
cert_graph_aligned_2 073
cert_graph_local_2 073 0 0 64 64
cert_graph_local_2 073 1 64 90 26
cert_graph_local_checked 073 90
cert_graph_kind_checked_2 073 24 00034 004
cert_graph_ridge_matrix 073 24 00034 004
cert_graph_edge_matrix_2 073 24 00034 004
cert_graph_missing_matrix_2 073 24 00034 004
cert_graph_matrix_checked_2 073
cert_graph_validity 073
cert_graph_vertex_width_2 073 24 00034 004
cert_graph_vertex_code_3 073 24 00034 004
cert_graph_literal 073
cert_graph_cells_exact_2 073

cert_graph_alignment_2 074 0 0 64 24 00034 005
cert_graph_alignment_2 074 1 64 92 24 00034 005
cert_graph_alignment_checked_5 074 92
cert_graph_aligned_2 074
cert_graph_local_2 074 0 0 64 64
cert_graph_local_2 074 1 64 92 28
cert_graph_local_checked 074 92
cert_graph_kind_checked_2 074 24 00034 005
cert_graph_ridge_matrix 074 24 00034 005
cert_graph_edge_matrix_2 074 24 00034 005
cert_graph_missing_matrix_2 074 24 00034 005
cert_graph_matrix_checked_2 074
cert_graph_validity 074
cert_graph_vertex_width_2 074 24 00034 005
cert_graph_vertex_code_3 074 24 00034 005
cert_graph_literal 074
cert_graph_cells_exact_2 074

cert_graph_alignment_2 075 0 0 64 24 00034 015
cert_graph_alignment_2 075 1 64 97 24 00034 015
cert_graph_alignment_checked_5 075 97
cert_graph_aligned_2 075
cert_graph_local_2 075 0 0 64 64
cert_graph_local_2 075 1 64 97 33
cert_graph_local_checked 075 97
cert_graph_kind_checked_2 075 24 00034 015
cert_graph_ridge_matrix 075 24 00034 015
cert_graph_edge_matrix_2 075 24 00034 015
cert_graph_missing_matrix_2 075 24 00034 015
cert_graph_matrix_checked_2 075
cert_graph_validity 075
cert_graph_vertex_width_2 075 24 00034 015
cert_graph_vertex_code_3 075 24 00034 015
cert_graph_literal 075
cert_graph_cells_exact_2 075

cert_graph_alignment_2 076 0 0 64 24 00034 016
cert_graph_alignment_2 076 1 64 87 24 00034 016
cert_graph_alignment_checked_5 076 87
cert_graph_aligned_2 076
cert_graph_local_2 076 0 0 64 64
cert_graph_local_2 076 1 64 87 23
cert_graph_local_checked 076 87
cert_graph_kind_checked_2 076 24 00034 016
cert_graph_ridge_matrix 076 24 00034 016
cert_graph_edge_matrix_2 076 24 00034 016
cert_graph_missing_matrix_2 076 24 00034 016
cert_graph_matrix_checked_2 076
cert_graph_validity 076
cert_graph_vertex_width_2 076 24 00034 016
cert_graph_vertex_code_3 076 24 00034 016
cert_graph_literal 076
cert_graph_cells_exact_2 076

cert_graph_alignment_2 077 0 0 64 24 00034 018
cert_graph_alignment_2 077 1 64 94 24 00034 018
cert_graph_alignment_checked_5 077 94
cert_graph_aligned_2 077
cert_graph_local_2 077 0 0 64 64
cert_graph_local_2 077 1 64 94 30
cert_graph_local_checked 077 94
cert_graph_kind_checked_2 077 24 00034 018
cert_graph_ridge_matrix 077 24 00034 018
cert_graph_edge_matrix_2 077 24 00034 018
cert_graph_missing_matrix_2 077 24 00034 018
cert_graph_matrix_checked_2 077
cert_graph_validity 077
cert_graph_vertex_width_2 077 24 00034 018
cert_graph_vertex_code_3 077 24 00034 018
cert_graph_literal 077
cert_graph_cells_exact_2 077

cert_graph_alignment_2 078 0 0 64 24 00034 019
cert_graph_alignment_2 078 1 64 84 24 00034 019
cert_graph_alignment_checked_5 078 84
cert_graph_aligned_2 078
cert_graph_local_2 078 0 0 64 64
cert_graph_local_2 078 1 64 84 20
cert_graph_local_checked 078 84
cert_graph_kind_checked_2 078 24 00034 019
cert_graph_ridge_matrix 078 24 00034 019
cert_graph_edge_matrix_2 078 24 00034 019
cert_graph_missing_matrix_2 078 24 00034 019
cert_graph_matrix_checked_2 078
cert_graph_validity 078
cert_graph_vertex_width_2 078 24 00034 019
cert_graph_vertex_code_3 078 24 00034 019
cert_graph_literal 078
cert_graph_cells_exact_2 078

cert_graph_alignment_2 079 0 0 64 24 00034 020
cert_graph_alignment_2 079 1 64 74 24 00034 020
cert_graph_alignment_checked_5 079 74
cert_graph_aligned_2 079
cert_graph_local_2 079 0 0 64 64
cert_graph_local_2 079 1 64 74 10
cert_graph_local_checked 079 74
cert_graph_kind_checked_2 079 24 00034 020
cert_graph_ridge_matrix 079 24 00034 020
cert_graph_edge_matrix_2 079 24 00034 020
cert_graph_missing_matrix_2 079 24 00034 020
cert_graph_matrix_checked_2 079
cert_graph_validity 079
cert_graph_vertex_width_2 079 24 00034 020
cert_graph_vertex_code_3 079 24 00034 020
cert_graph_literal 079
cert_graph_cells_exact_2 079

cert_graph_alignment_2 080 0 0 64 24 00034 022
cert_graph_alignment_2 080 1 64 90 24 00034 022
cert_graph_alignment_checked_5 080 90
cert_graph_aligned_2 080
cert_graph_local_2 080 0 0 64 64
cert_graph_local_2 080 1 64 90 26
cert_graph_local_checked 080 90
cert_graph_kind_checked_2 080 24 00034 022
cert_graph_ridge_matrix 080 24 00034 022
cert_graph_edge_matrix_2 080 24 00034 022
cert_graph_missing_matrix_2 080 24 00034 022
cert_graph_matrix_checked_2 080
cert_graph_validity 080
cert_graph_vertex_width_2 080 24 00034 022
cert_graph_vertex_code_3 080 24 00034 022
cert_graph_literal 080
cert_graph_cells_exact_2 080

cert_graph_alignment_2 081 0 0 64 24 00034 033
cert_graph_alignment_2 081 1 64 97 24 00034 033
cert_graph_alignment_checked_5 081 97
cert_graph_aligned_2 081
cert_graph_local_2 081 0 0 64 64
cert_graph_local_2 081 1 64 97 33
cert_graph_local_checked 081 97
cert_graph_kind_checked_2 081 24 00034 033
cert_graph_ridge_matrix 081 24 00034 033
cert_graph_edge_matrix_2 081 24 00034 033
cert_graph_missing_matrix_2 081 24 00034 033
cert_graph_matrix_checked_2 081
cert_graph_validity 081
cert_graph_vertex_width_2 081 24 00034 033
cert_graph_vertex_code_3 081 24 00034 033
cert_graph_literal 081
cert_graph_cells_exact_2 081

cert_graph_alignment_2 082 0 0 64 24 00034 040
cert_graph_alignment_2 082 1 64 114 24 00034 040
cert_graph_alignment_checked_5 082 114
cert_graph_aligned_2 082
cert_graph_local_2 082 0 0 64 64
cert_graph_local_2 082 1 64 114 50
cert_graph_local_checked 082 114
cert_graph_kind_checked_2 082 24 00034 040
cert_graph_ridge_matrix 082 24 00034 040
cert_graph_edge_matrix_2 082 24 00034 040
cert_graph_missing_matrix_2 082 24 00034 040
cert_graph_matrix_checked_2 082
cert_graph_validity 082
cert_graph_vertex_width_2 082 24 00034 040
cert_graph_vertex_code_3 082 24 00034 040
cert_graph_literal 082
cert_graph_cells_exact_2 082

cert_graph_alignment_2 083 0 0 64 24 00034 041
cert_graph_alignment_2 083 1 64 94 24 00034 041
cert_graph_alignment_checked_5 083 94
cert_graph_aligned_2 083
cert_graph_local_2 083 0 0 64 64
cert_graph_local_2 083 1 64 94 30
cert_graph_local_checked 083 94
cert_graph_kind_checked_2 083 24 00034 041
cert_graph_ridge_matrix 083 24 00034 041
cert_graph_edge_matrix_2 083 24 00034 041
cert_graph_missing_matrix_2 083 24 00034 041
cert_graph_matrix_checked_2 083
cert_graph_validity 083
cert_graph_vertex_width_2 083 24 00034 041
cert_graph_vertex_code_3 083 24 00034 041
cert_graph_literal 083
cert_graph_cells_exact_2 083

cert_graph_alignment_2 084 0 0 64 24 00034 043
cert_graph_alignment_2 084 1 64 89 24 00034 043
cert_graph_alignment_checked_5 084 89
cert_graph_aligned_2 084
cert_graph_local_2 084 0 0 64 64
cert_graph_local_2 084 1 64 89 25
cert_graph_local_checked 084 89
cert_graph_kind_checked_2 084 24 00034 043
cert_graph_ridge_matrix 084 24 00034 043
cert_graph_edge_matrix_2 084 24 00034 043
cert_graph_missing_matrix_2 084 24 00034 043
cert_graph_matrix_checked_2 084
cert_graph_validity 084
cert_graph_vertex_width_2 084 24 00034 043
cert_graph_vertex_code_3 084 24 00034 043
cert_graph_literal 084
cert_graph_cells_exact_2 084

cert_graph_alignment_2 085 0 0 64 24 00034 044
cert_graph_alignment_2 085 1 64 84 24 00034 044
cert_graph_alignment_checked_5 085 84
cert_graph_aligned_2 085
cert_graph_local_2 085 0 0 64 64
cert_graph_local_2 085 1 64 84 20
cert_graph_local_checked 085 84
cert_graph_kind_checked_2 085 24 00034 044
cert_graph_ridge_matrix 085 24 00034 044
cert_graph_edge_matrix_2 085 24 00034 044
cert_graph_missing_matrix_2 085 24 00034 044
cert_graph_matrix_checked_2 085
cert_graph_validity 085
cert_graph_vertex_width_2 085 24 00034 044
cert_graph_vertex_code_3 085 24 00034 044
cert_graph_literal 085
cert_graph_cells_exact_2 085

cert_graph_alignment_2 086 0 0 64 24 00035 000
cert_graph_alignment_2 086 1 64 88 24 00035 000
cert_graph_alignment_checked_5 086 88
cert_graph_aligned_2 086
cert_graph_local_2 086 0 0 64 64
cert_graph_local_2 086 1 64 88 24
cert_graph_local_checked 086 88
cert_graph_kind_checked_2 086 24 00035 000
cert_graph_ridge_matrix 086 24 00035 000
cert_graph_edge_matrix_2 086 24 00035 000
cert_graph_missing_matrix_2 086 24 00035 000
cert_graph_matrix_checked_2 086
cert_graph_validity 086
cert_graph_vertex_width_2 086 24 00035 000
cert_graph_vertex_code_3 086 24 00035 000
cert_graph_literal 086
cert_graph_cells_exact_2 086

cert_graph_alignment_2 087 0 0 64 24 00035 004
cert_graph_alignment_2 087 1 64 93 24 00035 004
cert_graph_alignment_checked_5 087 93
cert_graph_aligned_2 087
cert_graph_local_2 087 0 0 64 64
cert_graph_local_2 087 1 64 93 29
cert_graph_local_checked 087 93
cert_graph_kind_checked_2 087 24 00035 004
cert_graph_ridge_matrix 087 24 00035 004
cert_graph_edge_matrix_2 087 24 00035 004
cert_graph_missing_matrix_2 087 24 00035 004
cert_graph_matrix_checked_2 087
cert_graph_validity 087
cert_graph_vertex_width_2 087 24 00035 004
cert_graph_vertex_code_3 087 24 00035 004
cert_graph_literal 087
cert_graph_cells_exact_2 087

cert_graph_alignment_2 088 0 0 64 24 00035 008
cert_graph_alignment_2 088 1 64 88 24 00035 008
cert_graph_alignment_checked_5 088 88
cert_graph_aligned_2 088
cert_graph_local_2 088 0 0 64 64
cert_graph_local_2 088 1 64 88 24
cert_graph_local_checked 088 88
cert_graph_kind_checked_2 088 24 00035 008
cert_graph_ridge_matrix 088 24 00035 008
cert_graph_edge_matrix_2 088 24 00035 008
cert_graph_missing_matrix_2 088 24 00035 008
cert_graph_matrix_checked_2 088
cert_graph_validity 088
cert_graph_vertex_width_2 088 24 00035 008
cert_graph_vertex_code_3 088 24 00035 008
cert_graph_literal 088
cert_graph_cells_exact_2 088

cert_graph_alignment_2 089 0 0 64 24 00035 012
cert_graph_alignment_2 089 1 64 91 24 00035 012
cert_graph_alignment_checked_5 089 91
cert_graph_aligned_2 089
cert_graph_local_2 089 0 0 64 64
cert_graph_local_2 089 1 64 91 27
cert_graph_local_checked 089 91
cert_graph_kind_checked_2 089 24 00035 012
cert_graph_ridge_matrix 089 24 00035 012
cert_graph_edge_matrix_2 089 24 00035 012
cert_graph_missing_matrix_2 089 24 00035 012
cert_graph_matrix_checked_2 089
cert_graph_validity 089
cert_graph_vertex_width_2 089 24 00035 012
cert_graph_vertex_code_3 089 24 00035 012
cert_graph_literal 089
cert_graph_cells_exact_2 089

cert_graph_alignment_2 090 0 0 64 24 00035 013
cert_graph_alignment_2 090 1 64 91 24 00035 013
cert_graph_alignment_checked_5 090 91
cert_graph_aligned_2 090
cert_graph_local_2 090 0 0 64 64
cert_graph_local_2 090 1 64 91 27
cert_graph_local_checked 090 91
cert_graph_kind_checked_2 090 24 00035 013
cert_graph_ridge_matrix 090 24 00035 013
cert_graph_edge_matrix_2 090 24 00035 013
cert_graph_missing_matrix_2 090 24 00035 013
cert_graph_matrix_checked_2 090
cert_graph_validity 090
cert_graph_vertex_width_2 090 24 00035 013
cert_graph_vertex_code_3 090 24 00035 013
cert_graph_literal 090
cert_graph_cells_exact_2 090

cert_graph_alignment_3 091 0 0 64 64
cert_graph_alignment_3 091 1 64 85 21
cert_graph_alignment_checked_5 091 85
cert_graph_aligned_2 091
cert_graph_local_2 091 0 0 64 64
cert_graph_local_2 091 1 64 85 21
cert_graph_local_checked 091 85
cert_graph_kind_checked 091
cert_graph_ridge_matrix_2 091
cert_graph_edge_matrix 091
cert_graph_missing_matrix 091
cert_graph_matrix_checked_2 091
cert_graph_validity 091
cert_graph_vertex_width 091
cert_graph_vertex_code 091
cert_graph_literal 091
cert_graph_cells_exact_2 091

cert_graph_alignment_3 092 0 0 64 64
cert_graph_alignment_3 092 1 64 78 14
cert_graph_alignment_checked_5 092 78
cert_graph_aligned_2 092
cert_graph_local_2 092 0 0 64 64
cert_graph_local_2 092 1 64 78 14
cert_graph_local_checked 092 78
cert_graph_kind_checked 092
cert_graph_ridge_matrix_2 092
cert_graph_edge_matrix 092
cert_graph_missing_matrix 092
cert_graph_matrix_checked_2 092
cert_graph_validity 092
cert_graph_vertex_width 092
cert_graph_vertex_code 092
cert_graph_literal 092
cert_graph_cells_exact_2 092

cert_graph_alignment_2 093 0 0 64 26 00026 009
cert_graph_alignment_2 093 1 64 89 26 00026 009
cert_graph_alignment_checked_5 093 89
cert_graph_aligned_2 093
cert_graph_local_2 093 0 0 64 64
cert_graph_local_2 093 1 64 89 25
cert_graph_local_checked 093 89
cert_graph_kind_checked_2 093 26 00026 009
cert_graph_ridge_matrix 093 26 00026 009
cert_graph_edge_matrix_2 093 26 00026 009
cert_graph_missing_matrix_2 093 26 00026 009
cert_graph_matrix_checked_2 093
cert_graph_validity 093
cert_graph_vertex_width_2 093 26 00026 009
cert_graph_vertex_code_3 093 26 00026 009
cert_graph_literal 093
cert_graph_cells_exact_2 093

cert_graph_alignment_2 094 0 0 64 26 00026 010
cert_graph_alignment_2 094 1 64 93 26 00026 010
cert_graph_alignment_checked_5 094 93
cert_graph_aligned_2 094
cert_graph_local_2 094 0 0 64 64
cert_graph_local_2 094 1 64 93 29
cert_graph_local_checked 094 93
cert_graph_kind_checked_2 094 26 00026 010
cert_graph_ridge_matrix 094 26 00026 010
cert_graph_edge_matrix_2 094 26 00026 010
cert_graph_missing_matrix_2 094 26 00026 010
cert_graph_matrix_checked_2 094
cert_graph_validity 094
cert_graph_vertex_width_2 094 26 00026 010
cert_graph_vertex_code_3 094 26 00026 010
cert_graph_literal 094
cert_graph_cells_exact_2 094

cert_graph_alignment_2 095 0 0 64 26 00026 011
cert_graph_alignment_2 095 1 64 93 26 00026 011
cert_graph_alignment_checked_5 095 93
cert_graph_aligned_2 095
cert_graph_local_2 095 0 0 64 64
cert_graph_local_2 095 1 64 93 29
cert_graph_local_checked 095 93
cert_graph_kind_checked_2 095 26 00026 011
cert_graph_ridge_matrix 095 26 00026 011
cert_graph_edge_matrix_2 095 26 00026 011
cert_graph_missing_matrix_2 095 26 00026 011
cert_graph_matrix_checked_2 095
cert_graph_validity 095
cert_graph_vertex_width_2 095 26 00026 011
cert_graph_vertex_code_3 095 26 00026 011
cert_graph_literal 095
cert_graph_cells_exact_2 095

cert_graph_alignment_2 096 0 0 64 24 00035 017
cert_graph_alignment_2 096 1 64 85 24 00035 017
cert_graph_alignment_checked_5 096 85
cert_graph_aligned_2 096
cert_graph_local_2 096 0 0 64 64
cert_graph_local_2 096 1 64 85 21
cert_graph_local_checked 096 85
cert_graph_kind_checked_2 096 24 00035 017
cert_graph_ridge_matrix 096 24 00035 017
cert_graph_edge_matrix_2 096 24 00035 017
cert_graph_missing_matrix_2 096 24 00035 017
cert_graph_matrix_checked_2 096
cert_graph_validity 096
cert_graph_vertex_width_2 096 24 00035 017
cert_graph_vertex_code_3 096 24 00035 017
cert_graph_literal 096
cert_graph_cells_exact_2 096

cert_graph_alignment_2 097 0 0 64 24 00035 024
cert_graph_alignment_2 097 1 64 94 24 00035 024
cert_graph_alignment_checked_5 097 94
cert_graph_aligned_2 097
cert_graph_local_2 097 0 0 64 64
cert_graph_local_2 097 1 64 94 30
cert_graph_local_checked 097 94
cert_graph_kind_checked_2 097 24 00035 024
cert_graph_ridge_matrix 097 24 00035 024
cert_graph_edge_matrix_2 097 24 00035 024
cert_graph_missing_matrix_2 097 24 00035 024
cert_graph_matrix_checked_2 097
cert_graph_validity 097
cert_graph_vertex_width_2 097 24 00035 024
cert_graph_vertex_code_3 097 24 00035 024
cert_graph_literal 097
cert_graph_cells_exact_2 097

cert_graph_alignment_2 098 0 0 64 24 00035 026
cert_graph_alignment_2 098 1 64 83 24 00035 026
cert_graph_alignment_checked_5 098 83
cert_graph_aligned_2 098
cert_graph_local_2 098 0 0 64 64
cert_graph_local_2 098 1 64 83 19
cert_graph_local_checked 098 83
cert_graph_kind_checked_2 098 24 00035 026
cert_graph_ridge_matrix 098 24 00035 026
cert_graph_edge_matrix_2 098 24 00035 026
cert_graph_missing_matrix_2 098 24 00035 026
cert_graph_matrix_checked_2 098
cert_graph_validity 098
cert_graph_vertex_width_2 098 24 00035 026
cert_graph_vertex_code_3 098 24 00035 026
cert_graph_literal 098
cert_graph_cells_exact_2 098

cert_graph_alignment_2 099 0 0 64 24 00035 030
cert_graph_alignment_2 099 1 64 97 24 00035 030
cert_graph_alignment_checked_5 099 97
cert_graph_aligned_2 099
cert_graph_local_2 099 0 0 64 64
cert_graph_local_2 099 1 64 97 33
cert_graph_local_checked 099 97
cert_graph_kind_checked_2 099 24 00035 030
cert_graph_ridge_matrix 099 24 00035 030
cert_graph_edge_matrix_2 099 24 00035 030
cert_graph_missing_matrix_2 099 24 00035 030
cert_graph_matrix_checked_2 099
cert_graph_validity 099
cert_graph_vertex_width_2 099 24 00035 030
cert_graph_vertex_code_3 099 24 00035 030
cert_graph_literal 099
cert_graph_cells_exact_2 099

end Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006
