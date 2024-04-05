pub(crate) trait Node {
    type Index: TryInto<usize> + TryFrom<usize> + Copy;
    fn neighbors(&self) -> impl Iterator<Item = Self::Index>;
}

pub(crate) fn find_disjoint_subgraphs<N: Node>(graph: &[N]) -> Vec<Vec<N::Index>>
    where
        <<N as Node>::Index as TryFrom<usize>>::Error: std::fmt::Debug,
        <<N as Node>::Index as TryInto<usize>>::Error: std::fmt::Debug
{
    let mut visited = vec![false; graph.len()]; // Track visited nodes
    let mut disjoint_subgraphs = Vec::new(); // Store the result

    for start in 0..graph.len() {
        if visited[start] {
            continue; // Skip already visited nodes
        }
        let mut queue = vec![start]; // BFS queue
        let mut current_subgraph = Vec::new(); // Collect nodes for the current component

        while let Some(node_idx) = queue.pop() {
            if visited[node_idx] {
                continue; // Skip if already visited
            }
            visited[node_idx] = true; // Mark as visited
            current_subgraph.push(N::Index::try_from(node_idx).unwrap()); // Add to current subgraph

            // Add all unvisited connected nodes to the queue
            for neighbor_idx in graph[node_idx].neighbors() {
                if !visited[neighbor_idx.try_into().unwrap()] {
                    queue.push(neighbor_idx.try_into().unwrap());
                }
            }
        }

        disjoint_subgraphs.push(current_subgraph); // Save the found subgraph
    }

    disjoint_subgraphs
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Node(Vec<u32>);
    impl super::Node for Node {
        type Index = u32;
        fn neighbors(&self) -> impl Iterator<Item = Self::Index> {
            self.0.iter().copied()
        }
    }

    #[test]
    fn single_disjoint_graph() {
        let graph = vec![
            Node(vec![]),
            Node(vec![]),
            Node(vec![]),
        ];
        let subgraphs = find_disjoint_subgraphs(&graph);
        assert_eq!(subgraphs.len(), 3);
    }

    #[test]
    fn single_joint_graph() {
        let graph = vec![
            Node(vec![1, 2]),
            Node(vec![0]),
            Node(vec![0]),
        ];
        let subgraphs = find_disjoint_subgraphs(&graph);
        assert_eq!(subgraphs.len(), 1);
    }

    #[test]
    fn three_disjoint_subgraphs() {
        let graph = vec![
            Node(vec![1]),
            Node(vec![0]),
            Node(vec![4, 5]),
            Node(vec![3]),
            Node(vec![2, 5]),
            Node(vec![4]),
        ];
        let subgraphs = find_disjoint_subgraphs(&graph);
        assert_eq!(subgraphs.len(), 3);
    }
}