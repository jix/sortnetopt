use std::ops::Range;

const SPLIT_THRESHOLD: usize = 16;

pub struct Tree {
    point_dim: usize,
    points: Vec<u16>,
    packed_dim: usize,
    packed: Vec<u8>,
    values: Vec<u8>,
    ranges: Vec<[u16; 2]>,
    nodes: Vec<Node>,
}

#[derive(Clone)]
struct Node {
    augmentation: Augmentation,
    parent: usize,
    is_right_child: bool,
    links: Links,
}

#[derive(Clone)]
enum Links {
    Leaf { values: Range<usize> },
    Inner { children: [usize; 2] },
}

#[derive(Clone, Eq, PartialEq)]
pub struct Augmentation {
    pub size: usize,
    pub value_range: [u8; 2],
}

#[derive(Copy, Clone)]
enum TraversalState {
    Done,
    Node { id: usize },
    Point { id: usize, index: usize },
}

#[allow(dead_code)]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum TraversalMut {
    Break,
    Retain,
    Remove,
}

impl Augmentation {
    pub fn new(_point_dim: usize, _points: &[u16], values: &[u8]) -> Self {
        let mut min_value = values[0];
        let mut max_value = values[0];
        for &value in &values[1..] {
            min_value = min_value.min(value);
            max_value = max_value.max(value);
        }
        Augmentation {
            size: values.len(),
            value_range: [min_value, max_value],
        }
    }

    pub fn update_leaf(&mut self, _point_dim: usize, _points: &[u16], values: &[u8]) -> bool {
        let mut min_value = values[0];
        let mut max_value = values[0];
        for &value in &values[1..] {
            min_value = min_value.min(value);
            max_value = max_value.max(value);
        }

        let new_augmentation = Augmentation {
            size: values.len(),
            value_range: [min_value, max_value],
        };

        let updated = new_augmentation != *self;

        *self = new_augmentation;

        updated
    }

    pub fn update_inner(&mut self, children: [&Self; 2]) -> bool {
        let value_range_min = children[0].value_range[0].min(children[1].value_range[0]);
        let value_range_max = children[0].value_range[1].max(children[1].value_range[1]);
        let value_range = [value_range_min, value_range_max];
        let size = children[0].size + children[1].size;

        let updated = (self.value_range != value_range) | (self.size != size);

        self.value_range = value_range;
        self.size = size;

        updated
    }
}

impl Tree {
    pub fn new(
        point_dim: usize,
        points: Vec<u16>,
        packed_dim: usize,
        packed: Vec<u8>,
        values: Vec<u8>,
    ) -> Self {
        assert_eq!(
            values.len() * point_dim,
            points.len(),
            "number of points != number of values"
        );

        assert_eq!(
            values.len() * packed_dim,
            packed.len(),
            "number of points != number of packed values"
        );

        let (nodes, mut ranges);

        if values.is_empty() {
            nodes = vec![];
            ranges = vec![];
        } else {
            nodes = vec![Node {
                augmentation: Augmentation::new(point_dim, &points, &values),
                links: Links::Leaf {
                    values: 0..values.len(),
                },
                parent: 0,
                is_right_child: true,
            }];

            ranges = vec![[0; 2]; point_dim];

            compute_ranges(&mut ranges, &points);
        };

        let mut result = Self {
            point_dim,
            points,
            packed_dim,
            packed,
            values,
            ranges,
            nodes,
        };

        if !result.values.is_empty() {
            result.build_tree(0);
        }

        result
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn len(&self) -> usize {
        if self.nodes.is_empty() {
            0
        } else {
            self.nodes[0].augmentation.size
        }
    }

    fn build_tree(&mut self, mut node_id: usize) {
        loop {
            match self.nodes[node_id].links.clone() {
                Links::Leaf { values } => {
                    if values.len() > SPLIT_THRESHOLD {
                        let ranges = &self.ranges[node_id * self.point_dim..][..self.point_dim];

                        let (split_dim, (split_range, split_low)) = ranges
                            .iter()
                            .map(|&[low, high]| (high - low, low))
                            .enumerate()
                            .max_by_key(|&(_index, (range, _low))| range)
                            .unwrap();

                        let split_at = split_low + (split_range + 1) / 2;

                        let child_ranges = self.partition(values.clone(), split_dim, split_at);

                        if child_ranges.iter().all(|range| range.start != range.end) {
                            let mut children = [0; 2];

                            for (child_nr, (child_range, child_id)) in
                                child_ranges.iter().zip(children.iter_mut()).enumerate()
                            {
                                *child_id =
                                    self.new_child(node_id, child_nr > 0, child_range.clone());
                            }

                            self.nodes[node_id].links = Links::Inner { children };

                            node_id = children[0];
                            continue;
                        }
                    }
                    while self.nodes[node_id].is_right_child {
                        if node_id == 0 {
                            return;
                        }
                        node_id = self.nodes[node_id].parent;
                    }
                    let parent_node = &self.nodes[self.nodes[node_id].parent];
                    let children = match &parent_node.links {
                        Links::Inner { children } => children,
                        _ => unreachable!(),
                    };
                    node_id = children[1];
                }
                _ => (),
            }
        }
    }

    fn new_child(&mut self, parent_id: usize, is_right_child: bool, values: Range<usize>) -> usize {
        let ranges_len = self.ranges.len();
        self.ranges.resize(ranges_len + self.point_dim, [0; 2]);

        compute_ranges(
            &mut self.ranges[ranges_len..],
            &self.points[values.start * self.point_dim..values.end * self.point_dim],
        );

        let node_id = self.nodes.len();

        self.nodes.push(Node {
            augmentation: Augmentation::new(
                self.point_dim,
                &self.points[values.start * self.point_dim..values.end * self.point_dim],
                &self.values[values.clone()],
            ),
            links: Links::Leaf { values },
            parent: parent_id,
            is_right_child,
        });

        node_id
    }

    fn partition(&mut self, values: Range<usize>, dim: usize, at: u16) -> [Range<usize>; 2] {
        if values.len() == 0 {
            return [values.clone(), values];
        }

        let mut left = values.start;
        let mut right = values.end - 1;

        loop {
            while left < values.end && self.points[left * self.point_dim + dim] < at {
                left += 1;
            }
            while right > values.start && self.points[right * self.point_dim + dim] >= at {
                right -= 1;
            }
            if left >= right {
                break;
            }
            self.swap_values(left, right);
        }

        [values.start..left, left..values.end]
    }

    fn swap_values(&mut self, left: usize, right: usize) {
        if left == right {
            return;
        }

        let left_ptr = self.points[left * self.point_dim..][..self.point_dim].as_mut_ptr();
        let right_ptr = self.points[right * self.point_dim..][..self.point_dim].as_mut_ptr();

        unsafe {
            std::ptr::swap_nonoverlapping(left_ptr, right_ptr, self.point_dim);
        }

        let left_ptr = self.packed[left * self.packed_dim..][..self.packed_dim].as_mut_ptr();
        let right_ptr = self.packed[right * self.packed_dim..][..self.packed_dim].as_mut_ptr();

        unsafe {
            std::ptr::swap_nonoverlapping(left_ptr, right_ptr, self.packed_dim);
        }

        self.values.swap(left, right);
    }

    fn move_node_ranges(&mut self, dst: usize, src: usize) {
        if dst == src {
            return;
        }

        let dst_ptr = self.ranges[dst * self.point_dim..][..self.point_dim].as_mut_ptr();
        let src_ptr = self.ranges[src * self.point_dim..][..self.point_dim].as_ptr();

        unsafe {
            std::ptr::copy_nonoverlapping(src_ptr, dst_ptr, self.point_dim);
        }
    }

    fn traversal_root(&self) -> TraversalState {
        if self.nodes.is_empty() {
            TraversalState::Done
        } else {
            TraversalState::Node { id: 0 }
        }
    }

    fn traversal_enter(&self, left_to_right: bool, node_id: usize) -> TraversalState {
        match &self.nodes[node_id].links {
            Links::Leaf { values } => TraversalState::Point {
                id: node_id,
                index: values.start,
            },
            Links::Inner { children } => TraversalState::Node {
                id: children[!left_to_right as usize],
            },
        }
    }

    fn traversal_skip(&self, left_to_right: bool, mut node_id: usize) -> TraversalState {
        loop {
            if node_id == 0 {
                return TraversalState::Done;
            } else {
                let node = &self.nodes[node_id];
                if node.is_right_child == left_to_right {
                    node_id = node.parent;
                    continue;
                }
                let parent_node = &self.nodes[node.parent];
                let children = match &parent_node.links {
                    Links::Inner { children } => children,
                    _ => unreachable!(),
                };
                return TraversalState::Node {
                    id: children[left_to_right as usize],
                };
            }
        }
    }

    fn traversal_next(
        &self,
        left_to_right: bool,
        node_id: usize,
        mut index: usize,
    ) -> TraversalState {
        let node = &self.nodes[node_id];
        let values = match &node.links {
            Links::Leaf { values } => values,
            _ => unreachable!(),
        };
        index += 1;
        if index == values.end {
            self.traversal_skip(left_to_right, node_id)
        } else {
            TraversalState::Point { id: node_id, index }
        }
    }

    fn traversal_remove(
        &mut self,
        left_to_right: bool,
        node_id: usize,
        index: usize,
    ) -> TraversalState {
        let node = &mut self.nodes[node_id];
        let values = match &mut node.links {
            Links::Leaf { values } => values,
            _ => unreachable!(),
        };

        values.end -= 1;
        if values.start == values.end {
            self.traversal_unlink(left_to_right, node_id)
        } else {
            let last_index = values.end;

            self.swap_values(index, last_index);

            self.update_augmentation(node_id);

            if index == last_index {
                self.traversal_skip(left_to_right, node_id)
            } else {
                TraversalState::Point { id: node_id, index }
            }
        }
    }

    fn traversal_unlink(&mut self, left_to_right: bool, node_id: usize) -> TraversalState {
        if node_id == 0 {
            self.nodes.clear();
            TraversalState::Done
        } else {
            let node = &self.nodes[node_id];
            let parent = node.parent;
            let is_right_child = node.is_right_child;

            let parent_node = &self.nodes[parent];
            let children = match &parent_node.links {
                Links::Inner { children } => children,
                _ => unreachable!(),
            };

            let sibling = children[!is_right_child as usize];

            assert_ne!(sibling, node_id);

            let moved_node = self.nodes[sibling].clone();

            match &moved_node.links {
                Links::Inner { children } => {
                    for &child in children.iter() {
                        self.nodes[child].parent = parent;
                    }
                }
                _ => (),
            }

            let parent_node = &mut self.nodes[parent];

            parent_node.links = moved_node.links;
            parent_node.augmentation = moved_node.augmentation;

            let parent_parent = parent_node.parent;

            self.move_node_ranges(parent, sibling);

            if parent != 0 {
                self.update_augmentation(parent_parent)
            }

            if is_right_child != left_to_right {
                TraversalState::Node { id: parent }
            } else {
                self.traversal_skip(left_to_right, parent)
            }
        }
    }

    fn update_augmentation(&mut self, mut node_id: usize) {
        loop {
            let node = &mut self.nodes[node_id];
            let parent = node.parent;
            let updated = match &node.links {
                Links::Inner { children } => {
                    let children = children.clone();

                    assert_ne!(children[0], children[1]);
                    assert_ne!(node_id, children[0]);
                    assert_ne!(node_id, children[1]);

                    let target = &mut self.nodes[node_id].augmentation as *mut Augmentation;
                    let child_0 = &self.nodes[children[0]].augmentation as *const Augmentation;
                    let child_1 = &self.nodes[children[1]].augmentation as *const Augmentation;

                    unsafe { (&mut *target).update_inner([&*child_0, &*child_1]) }
                }
                Links::Leaf { values } => node.augmentation.update_leaf(
                    self.point_dim,
                    &self.points[values.start * self.point_dim..values.end * self.point_dim],
                    &self.values[values.clone()],
                ),
            };

            if updated && node_id != 0 {
                node_id = parent;
            } else {
                break;
            }
        }
    }

    pub fn traverse<S, N, A>(
        &self,
        mut user_state: S,
        left_to_right: bool,
        mut node_filter: N,
        mut action: A,
    ) -> S
    where
        N: FnMut(&mut S, &Augmentation, &[[u16; 2]]) -> bool,
        A: FnMut(&mut S, &[u16], &[u8], u8) -> bool,
    {
        let mut state = self.traversal_root();

        loop {
            match state {
                TraversalState::Done => return user_state,
                TraversalState::Node { id } => {
                    let enter = node_filter(
                        &mut user_state,
                        &self.nodes[id].augmentation,
                        &self.ranges[id * self.point_dim..][..self.point_dim],
                    );

                    if enter {
                        state = self.traversal_enter(left_to_right, id);
                    } else {
                        state = self.traversal_skip(left_to_right, id);
                    }
                }
                TraversalState::Point { id, index } => {
                    let will_continue = action(
                        &mut user_state,
                        &self.points[index * self.point_dim..][..self.point_dim],
                        &self.packed[index * self.packed_dim..][..self.packed_dim],
                        self.values[index],
                    );

                    if will_continue {
                        state = self.traversal_next(left_to_right, id, index);
                    } else {
                        return user_state;
                    }
                }
            }
        }
    }

    pub fn traverse_mut<S, N, A>(
        &mut self,
        mut user_state: S,
        left_to_right: bool,
        mut node_filter: N,
        mut action: A,
    ) -> S
    where
        N: FnMut(&mut S, &Augmentation, &[[u16; 2]]) -> bool,
        A: FnMut(&mut S, &[u16], &[u8], &mut u8) -> TraversalMut,
    {
        let mut state = self.traversal_root();

        loop {
            match state {
                TraversalState::Done => return user_state,
                TraversalState::Node { id } => {
                    let enter = node_filter(
                        &mut user_state,
                        &self.nodes[id].augmentation,
                        &self.ranges[id * self.point_dim..][..self.point_dim],
                    );

                    if enter {
                        state = self.traversal_enter(left_to_right, id);
                    } else {
                        state = self.traversal_skip(left_to_right, id);
                    }
                }
                TraversalState::Point { id, index } => {
                    let old_value = self.values[index];
                    let action_result = action(
                        &mut user_state,
                        &self.points[index * self.point_dim..][..self.point_dim],
                        &self.packed[index * self.packed_dim..][..self.packed_dim],
                        &mut self.values[index],
                    );

                    match action_result {
                        TraversalMut::Break => return user_state,
                        TraversalMut::Remove => {
                            state = self.traversal_remove(left_to_right, id, index)
                        }
                        TraversalMut::Retain => {
                            if self.values[index] != old_value {
                                self.update_augmentation(id);
                            }
                            state = self.traversal_next(left_to_right, id, index);
                        }
                    }
                }
            }
        }
    }
}

fn compute_ranges(ranges: &mut [[u16; 2]], points: &[u16]) {
    for (range, &component) in ranges.iter_mut().zip(points.iter()) {
        *range = [component; 2];
    }

    for point in points.chunks(ranges.len()).skip(1) {
        for (range, &component) in ranges.iter_mut().zip(point.iter()) {
            range[0] = range[0].min(component);
            range[1] = range[1].max(component);
        }
    }
}
