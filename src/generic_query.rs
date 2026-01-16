use tree_sitter::{CaptureQuantifier, QueryError};

use crate::ast::File;
use crate::graph::SyntaxNode;
use crate::graph::{NodeLender, NodeLending, QMatch, SimpleNode, SyntaxNodeExt, NNN};

pub trait ExtendedableQuery {
    type Query: GenQuery<Lang = Self::Lang, Ext = Self>;
    type Lang;
    fn as_ref(&self) -> Option<&Self::Query>;
    fn with_capacity(str_size: usize) -> Self;
    fn make_query(&mut self, lang: &Self::Lang, source: &str) -> Result<Self::Query, QueryError>;
    fn make_main_query(&self, lang: &Self::Lang) -> Self::Query;
}

pub struct ExtendingStringQuery<Q = tree_sitter::Query, L = tree_sitter::Language> {
    pub(crate) query: Option<Q>,
    pub(crate) acc: String,
    pub each: Vec<String>,
    pub(crate) _phantom: std::marker::PhantomData<L>,
}

impl<Q, L> Default for ExtendingStringQuery<Q, L> {
    fn default() -> Self {
        Self {
            query: Default::default(),
            acc: Default::default(),
            each: Default::default(),
            _phantom: std::marker::PhantomData,
        }
    }
}

mod ts {
    use tree_sitter::{CaptureQuantifier, Language, Query};

    use super::*;
    impl ExtendedableQuery for ExtendingStringQuery<Query, Language> {
        type Query = Query;
        type Lang = Language;

        fn as_ref(&self) -> Option<&Self::Query> {
            self.query.as_ref()
        }

        fn with_capacity(capacity: usize) -> Self {
            let acc = String::with_capacity(capacity);
            Self {
                acc,
                ..Default::default()
            }
        }

        fn make_query(
            &mut self,
            language: &Self::Lang,
            source: &str,
        ) -> Result<Self::Query, QueryError> {
            // If tree-sitter allowed us to incrementally add patterns to a query, we wouldn't need
            // the global query_source.
            self.each.push(source.to_string());
            self.acc += source;
            self.acc += "\n";
            dbg!(source);
            Query::new(language, source)
        }

        fn make_main_query(&self, language: &Self::Lang) -> Self::Query {
            Query::new(language, &self.acc).unwrap()
        }
    }

    impl QueryWithLang for Query {
        type Lang = Language;
        type I = u32;
    }

    impl<'a> MatchesLending<'a> for Query {
        type Matches = MyQM<'a, 'a>;
    }

    impl<'a> NodeLending<'a> for Query {
        type SNode = MyTSNode<'a>;
    }

    impl GenQuery for Query {
        type Ext = ExtendingStringQuery;

        fn pattern_count(&self) -> usize {
            self.pattern_count()
        }

        fn capture_index_for_name(&self, name: &str) -> Option<u32> {
            self.capture_index_for_name(name)
        }

        fn capture_quantifiers(
            &self,
            index: usize,
        ) -> impl std::ops::Index<usize, Output = CaptureQuantifier> {
            struct A([tree_sitter::CaptureQuantifier]);
            impl std::ops::Index<usize> for &A {
                type Output = tree_sitter::CaptureQuantifier;

                fn index(&self, index: usize) -> &tree_sitter::CaptureQuantifier {
                    self.0
                        .get(index)
                        .unwrap_or(&tree_sitter::CaptureQuantifier::One)
                }
            }
            let s = self.capture_quantifiers(index);
            let s: &A = unsafe { std::mem::transmute(s) };
            s
        }

        fn capture_names(&self) -> &[&str] {
            self.capture_names()
        }

        fn check(file: &mut File<Query>) -> Result<(), crate::checker::CheckError> {
            file.check()
        }

        type Cursor = tree_sitter::QueryCursor;

        fn matches<'a>(
            &self,
            cursor: &mut Self::Cursor,
            node: &<Query as NodeLending<'a>>::SNode,
        ) -> <Self as MatchesLending<'a>>::Matches {
            // ) -> <Query as NodeLending<'_>>::Matches<'query, 'cursor> {
            // let matches = cursor.matches(self, node, source.as_bytes());
            let _matches = cursor.matches(self, node.node, node.source.as_bytes());
            todo!()
            // MyQM {
            //     qm: matches,
            //     source: node.source,
            // }
        }
    }
}

#[derive(Copy, PartialEq)]
pub struct MyTSNode<'tree> {
    pub(crate) node: tree_sitter::Node<'tree>,
    pub(crate) source: &'tree str,
}

impl<'tree> std::fmt::Debug for MyTSNode<'tree> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MyTSNode")
            .field("node", &self.node)
            .finish()
    }
}

impl<'tree> std::ops::Deref for MyTSNode<'tree> {
    type Target = tree_sitter::Node<'tree>;

    fn deref(&self) -> &Self::Target {
        &self.node
    }
}

impl<'tree> MyTSNode<'tree> {
    pub fn new(node: tree_sitter::Node<'tree>, source: &'tree str) -> Self {
        Self { node, source }
    }
}

impl<'tree> SimpleNode for MyTSNode<'tree> {
    fn id(&self) -> usize {
        self.node.id()
    }
}

impl<'tree> SyntaxNode for MyTSNode<'tree> {
    fn kind(&self) -> &'static str {
        self.node.kind()
    }

    fn start_position(&self) -> tree_sitter::Point {
        self.node.start_position()
    }

    fn end_position(&self) -> tree_sitter::Point {
        self.node.end_position()
    }

    fn byte_range(&self) -> std::ops::Range<usize> {
        self.node.byte_range()
    }

    fn range(&self) -> tree_sitter::Range {
        self.node.range()
    }

    fn text(&self) -> String {
        self.source[self.byte_range()].to_string()
    }

    fn named_child_count(&self) -> usize {
        self.node.named_child_count()
    }
}

impl<'tree> SyntaxNodeExt for MyTSNode<'tree> {
    fn parent(&self) -> Option<Self>
    where
        Self: Sized,
    {
        self.node.parent().map(|node| Self {
            node,
            source: self.source,
        })
    }
    type Cursor = tree_sitter::TreeCursor<'tree>;
    fn walk(&self) -> Self::Cursor {
        self.node.walk()
    }
    fn named_children<'cursor>(
        &self,
        cursor: &'cursor mut Self::Cursor,
    ) -> impl ExactSizeIterator<Item = Self>
    where
        Self: 'cursor,
    {
        let source = self.source;
        cursor.reset(self.node);
        cursor.goto_first_child();
        (0..self.node.named_child_count()).map(move |_| {
            while !cursor.node().is_named() {
                if !cursor.goto_next_sibling() {
                    break;
                }
            }
            let node = cursor.node();
            cursor.goto_next_sibling();
            MyTSNode { node, source }
        })
    }
}

pub struct MyQueryMatch<'cursor, 'tree> {
    pub pattern_index: usize,
    pub captures: &'cursor [tree_sitter::QueryCapture<'tree>],
    pub id: u32,
    // pub mat: tree_sitter::QueryMatch<'cursor, 'tree>,
    pub source: &'tree str,
}
impl<'cursor, 'tree> std::fmt::Debug for MyQueryMatch<'cursor, 'tree> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MyTSQueryMatch")
            // .field("mat", &self.mat)
            .finish()
    }
}

impl<'cursor, 'tree> MyQueryMatch<'cursor, 'tree> {
    pub fn nodes_for_capture_index(
        &self,
        capture_ix: u32,
    ) -> impl Iterator<Item = tree_sitter::Node<'tree>> + '_ {
        self.captures
            .iter()
            .filter_map(move |capture| (capture.index == capture_ix).then_some(capture.node))
    }
}

// impl<'cursor, 'tree> std::ops::Deref for MyQueryMatch<'cursor, 'tree> {
//     type Target = tree_sitter::QueryMatch<'cursor, 'tree>;

//     fn deref(&self) -> &Self::Target {
//         &self.mat
//     }
// }

pub struct CapturedNodesIter<'cursor, 'tree> {
    index: u32,
    inner: &'cursor [tree_sitter::QueryCapture<'tree>],
    source: &'tree str,
}

impl<'a, 'cursor, 'tree> NodeLending<'a> for CapturedNodesIter<'cursor, 'tree> {
    type SNode = super::MyTSNode<'tree>;
}

impl<'cursor, 'tree> NodeLender for CapturedNodesIter<'cursor, 'tree> {
    fn next(&mut self) -> Option<<Self as NodeLending<'_>>::SNode> {
        loop {
            if self.inner.is_empty() {
                return None;
            }
            let capture = &self.inner[0];
            self.inner = &self.inner[1..];
            if capture.index != self.index {
                continue;
            }
            let node = capture.node;
            return Some(super::MyTSNode {
                node,
                source: self.source,
            });
        }
    }
}

impl<'cursor, 'tree> QueryWithLang for MyQueryMatch<'cursor, 'tree> {
    type Lang = tree_sitter::Language;
    type I = u32;
}

impl<'a, 'cursor, 'tree> crate::graph::NodesLending<'a> for MyQueryMatch<'cursor, 'tree> {
    type Nodes = CapturedNodesIter<'cursor, 'tree>;
}

impl<'cursor, 'tree> crate::graph::QMatch for MyQueryMatch<'cursor, 'tree> {
    type Simple = MyTSNode<'tree>;

    fn nodes_for_capture_index(&self, index: Self::I) -> CapturedNodesIter<'cursor, 'tree> {
        CapturedNodesIter {
            index,
            inner: self.captures,
            source: self.source,
        }
    }

    fn nodes_for_capture_indexi(&self, index: Self::I) -> Option<NNN<'_, '_, Self>> {
        CapturedNodesIter {
            index,
            inner: self.captures,
            source: self.source,
        }
        .next()
    }

    fn nodes_for_capture_indexii(
        &self,
        index: Self::I,
    ) -> impl NodeLender + NodeLending<'_, SNode = NNN<'_, '_, Self>> {
        CapturedNodesIter {
            index,
            inner: self.captures,
            source: self.source,
        }
    }
    fn pattern_index(&self) -> usize {
        self.pattern_index
    }

    fn syn_node_ref(&self, node: &NNN<'_, '_, Self>) -> crate::graph::SyntaxNodeRef {
        crate::graph::SyntaxNodeRef::new(node)
    }

    fn node(&self, s: Self::Simple) -> NNN<'_, '_, Self> {
        s
    }
}

impl<'tree> Clone for MyTSNode<'tree> {
    fn clone(&self) -> Self {
        *self
    }
}

pub struct MyQM<'query, 'tree> {
    pub source: &'tree str,
    pub(crate) qm: tree_sitter::QueryMatches<'query, 'tree, &'tree [u8], &'tree [u8]>,
}

impl<'query, 'tree> QueryWithLang for MyQM<'query, 'tree> {
    type Lang = tree_sitter::Language;
    type I = u32;
}

impl<'a, 'query, 'tree> NodeLending<'a> for MyQM<'query, 'tree> {
    type SNode = MyTSNode<'a>;
}

impl<'a, 'query, 'tree> MatchLending<'a> for MyQM<'query, 'tree> {
    type Match = MyQueryMatch<'a, 'tree>;
}

impl<'query, 'tree> MatchLender for MyQM<'query, 'tree> {
    fn next(&mut self) -> Option<<Self as MatchLending<'_>>::Match> {
        use streaming_iterator::StreamingIterator;
        let m = self.qm.next()?;
        // TODO is there a bug in tree_sitter::QueryMatches::next ?
        // the lifetime names are not matching
        // let m = unsafe { std::mem::transmute(m) };
        Some(MyQueryMatch {
            source: self.source,
            id: m.id(),
            pattern_index: m.pattern_index,
            captures: m.captures,
        })
    }
}

// impl<'query, 'tree> Iterator for MyQM<'query, 'tree> {
//     type Item = MyQueryMatch<'cursor, 'tree>;

//     fn next(&mut self) -> Option<Self::Item> {
//         use streaming_iterator::StreamingIterator;
//         let m = self.qm.next()?;
//         // // TODO is there a bug in tree_sitter::QueryMatches::next ?
//         // // the lifetime names are not matching
//         // let m = unsafe { std::mem::transmute(m) };
//         Some(MyQueryMatch {
//             id: m.id(),
//             pattern_index: m.pattern_index,
//             captures: m.captures,
//             source: self.source,
//         })
//     }
// }

pub trait QueryWithLang {
    type Lang;
    type I: Copy + From<u32>;
}

pub trait MatchesLending<'a, __ImplBound = &'a Self>: QueryWithLang {
    type Matches: MatchLender + QueryWithLang<I = Self::I>;
}

pub trait MatchLender: for<'a> MatchLending<'a> {
    fn next(&mut self) -> Option<<Self as MatchLending<'_>>::Match>;
}

pub trait MatchLending<'a, __ImplBound = &'a Self>: QueryWithLang {
    type Match: QMatch + QueryWithLang<I = Self::I>;
}

pub trait GenQuery: for<'a> MatchesLending<'a> + for<'a> NodeLending<'a> + QueryWithLang {
    type Ext: ExtendedableQuery<Query = Self, Lang = Self::Lang>;
    fn pattern_count(&self) -> usize;
    fn capture_index_for_name(&self, name: &str) -> Option<u32>;
    fn capture_quantifiers(
        &self,
        index: usize,
    ) -> impl std::ops::Index<usize, Output = CaptureQuantifier>;
    fn capture_names(&self) -> &[&str];
    fn check(_file: &mut File<Self>) -> Result<(), crate::checker::CheckError>
    where
        Self: Sized,
    {
        Ok(())
    }

    /// Parses a graph DSL file, returning a new `File` instance.
    fn from_str(language: Self::Lang, source: &str) -> Result<File<Self>, crate::ParseError>
    where
        Self: Sized,
    {
        let mut file = File::<Self>::new(language);
        crate::parser::Parser::<Self::Ext>::new(source).parse_into_file(&mut file)?;
        Self::check(&mut file)?;
        Ok(file)
    }

    type Cursor: Default;

    fn matches<'a>(
        &self,
        cursor: &mut Self::Cursor,
        node: &<Self as NodeLending<'a>>::SNode,
    ) -> <Self as MatchesLending<'a>>::Matches;
}
