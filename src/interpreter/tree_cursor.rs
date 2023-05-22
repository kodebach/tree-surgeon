use tree_sitter::{TreeCursor, Node};

pub trait TreeCusorExt {
    fn error_iter(&self) -> TreeErrorIter;
}

impl<'a> TreeCusorExt for TreeCursor<'a> {
    fn error_iter(&self) -> TreeErrorIter {
        TreeErrorIter {
            cursor: self.clone(),
            next_node: Some(self.node()),
        }
    }
}

pub struct TreeErrorIter<'a> {
    cursor: TreeCursor<'a>,
    next_node: Option<Node<'a>>,
}

impl<'a> Iterator for TreeErrorIter<'a> {
    type Item = Node<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        fn goto_next(iter: &mut TreeErrorIter<'_>) {
            while !iter.cursor.goto_next_sibling() {
                if !iter.cursor.goto_parent() {
                    iter.next_node = None;
                    return;
                }
            }

            iter.next_node = Some(iter.cursor.node());
        }

        while let Some(node) = self.next_node {
            if node.is_error() {
                goto_next(self);
                return Some(node);
            } else if self.cursor.goto_first_child() {
                continue;
            }

            goto_next(self);
        }

        None
    }
}