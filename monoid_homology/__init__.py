from .crs import CompleteRewritingSystem, CRS
from .from_table import (
    op_from_id,
    ix_op_pairs_from_ids,
    all_ix_op_pairs,
    find_best_gens_crs,
    string_to_op,
    all_gens_crs,
)
from .structure_utils import (
    table_from_opfunc_and_set,
    product_op,
    adjoin_1,
    maybe_adjoin_1,
    get_kernel_height_width_G,
    restrict_to_subset,
    thin_equivalent,
    equivalent_submonoid,
    op_has_ptorsion,
    swaps,
    is_regular,
    canonicalize,
)
from .resolution import (
    FiniteMonoidRingProjectiveResolution,
    find_good_resolution,
)
from .knuth_bendix import kb_normalize

from .branched_resolution import (
    BranchedResolution,
    find_good_branched_resolution,
)

from .by_min_ideal import (
    subset_from_size_and_min_name,
)