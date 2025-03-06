from monoid_homology.branched_resolution import (
    ResolutionNode,
    BranchedResolution,
)

def test_ResolutionNode_rect22_dimension1():
    rect22mon = [[0,1,0,1,0],[0,1,0,1,1],[2,3,2,3,2],[2,3,2,3,3],[0,1,2,3,4]]
    rect22mon_e_to_Lclass = {0: (0, 2), 1: (1, 3), 4: (0, 1, 2, 3, 4)}
    node = ResolutionNode(rect22mon, rect22mon_e_to_Lclass, [4], [0], [[[(-1, 0), (1, 2)]]])
    assert node.op == rect22mon
    assert node.e_to_Lclass == rect22mon_e_to_Lclass
    assert node.idempotent_list == [4]
    assert node.target_idempotent_list == [0]
    assert node.input_index_pair_to_index == {(0, jj): jj for jj in range(5)}
    assert node.input_index_pairs == [(0, jj) for jj in range(5)]
    assert node.output_index_pair_to_index == {(0, 0): 0, (0, 1): 1}
    assert node.output_index_pairs == [(0, 0), (0, 1)]
    assert node.outgoing_right_mul_matrix == [[ [(-1, 0), (1, 2)] ]]

    node.make_Z_matrix()
    assert node.Z_matrix == [
        [0, 0, 0, 0, -1],
        [0, 0, 0, 0, +1],
    ]

    node.make_kernel()
    assert sorted(node.kernel_Z_basis, reverse=True) == [
        [1,0,0,0,0], [0,1,0,0,0], [0,0,1,0,0], [0,0,0,1,0]
    ]

    node.make_partition()
    assert node.partition_of_idempotents == [[0]]
    assert node.kindex_to_bindex == [0, 0, 0, 0]
    assert node.partition_of_kindexes == [[0, 1, 2, 3]]

    node.make_children()
    [child] = node.children
    assert child.op == rect22mon
    assert child.e_to_Lclass == rect22mon_e_to_Lclass
    assert child.idempotent_list == [0, 0]
    assert child.target_idempotent_list == [4]
    assert child.input_index_pair_to_index == {
        (0, 0): 0, (0, 1): 1, (1, 0): 2, (1, 1): 3
    }
    assert child.input_index_pairs == [(0, 0), (0, 1), (1, 0), (1, 1)]
    assert child.output_index_pair_to_index == {(0,jj):jj for jj in range(5)}
    assert child.output_index_pairs == [(0,jj) for jj in range(5)]
    assert child.outgoing_right_mul_matrix == [[ [(1, 1)], [(1, 0)], ]]

def test_ResolutionNode_rect22_dimension2():
    rect22mon = [[0,1,0,1,0],[0,1,0,1,1],[2,3,2,3,2],[2,3,2,3,3],[0,1,2,3,4]]
    rect22mon_e_to_Lclass = {0: (0, 2), 1: (1, 3), 4: (0, 1, 2, 3, 4)}
    node = ResolutionNode(rect22mon, rect22mon_e_to_Lclass, [0, 0], [4], [[ [(1, 0)], [(1, 1)] ]])

    assert node.op == rect22mon
    assert node.e_to_Lclass == rect22mon_e_to_Lclass
    assert node.idempotent_list == [0, 0]
    assert node.target_idempotent_list == [4]
    assert node.input_index_pair_to_index == {
        (0, 0): 0, (0, 1): 1, (1, 0): 2, (1, 1): 3
    }
    assert node.input_index_pairs == [(0, 0), (0, 1), (1, 0), (1, 1)]
    assert node.output_index_pair_to_index == {(0,jj): jj for jj in range(5)}
    assert node.output_index_pairs == [(0,jj) for jj in range(5)]
    assert node.outgoing_right_mul_matrix == [[ [(1, 0)], [(1, 1)] ]]

    node.make_Z_matrix()
    assert node.Z_matrix == [
        [1, 0, 0, 0],
        [0, 0, 1, 0],
        [0, 1, 0, 0],
        [0, 0, 0, 1],
        [0, 0, 0, 0],
    ]

    node.make_kernel()
    assert node.kernel_Z_basis == []

    node.make_partition()
    assert node.partition_of_idempotents == [[0], [1]]
    assert node.kindex_to_bindex == []
    assert node.partition_of_kindexes == [[], []]

    node.make_children()
    [child0, child1] = node.children
    assert child0.op == rect22mon
    assert child0.e_to_Lclass == rect22mon_e_to_Lclass
    assert child0.idempotent_list == []
    assert child0.target_idempotent_list == [0]
    assert child0.input_index_pair_to_index == {}
    assert child0.input_index_pairs == []
    assert child0.output_index_pair_to_index == {(0,0): 0, (0, 1): 1}
    assert child0.output_index_pairs == [(0, 0), (0, 1)]
    assert child0.outgoing_right_mul_matrix == [[ ]]

    assert child1.op == rect22mon
    assert child1.e_to_Lclass == rect22mon_e_to_Lclass
    assert child1.idempotent_list == []
    assert child1.target_idempotent_list == [0]
    assert child1.input_index_pair_to_index == {}
    assert child1.input_index_pairs == []
    assert child1.output_index_pair_to_index == {(0,0): 0, (0, 1): 1}
    assert child1.output_index_pairs == [(0, 0), (0, 1)]
    assert child1.outgoing_right_mul_matrix == [[ ]]

def test_ResolutionNode_rect22_dimension3():
    rect22mon = [[0,1,0,1,0],[0,1,0,1,1],[2,3,2,3,2],[2,3,2,3,3],[0,1,2,3,4]]
    rect22mon_e_to_Lclass = {0: (0, 2), 1: (1, 3), 4: (0, 1, 2, 3, 4)}
    node = ResolutionNode(rect22mon, rect22mon_e_to_Lclass, [], [0], [[  ]])

    assert node.op == rect22mon
    assert node.e_to_Lclass == rect22mon_e_to_Lclass
    assert node.idempotent_list == []
    assert node.target_idempotent_list == [0]
    assert node.input_index_pair_to_index == {}
    assert node.input_index_pairs == []
    assert node.output_index_pair_to_index == {(0,0): 0, (0, 1): 1}
    assert node.output_index_pairs == [(0, 0), (0, 1)]
    assert node.outgoing_right_mul_matrix == [[  ]]

    node.make_Z_matrix()
    assert node.Z_matrix == [[], []]
    node.make_kernel()
    assert node.kernel_Z_basis == []
    node.make_partition()
    assert node.partition_of_idempotents == []
    assert node.kindex_to_bindex == []
    assert node.partition_of_kindexes == []
    node.make_children()

    assert node.children == []

    
