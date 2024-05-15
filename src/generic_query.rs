use tree_sitter::{CaptureQuantifier, QueryError};

use crate::{
    ast::File,
    graph::{QMatch, SyntaxNode, SyntaxNodeExt},
};

pub trait ExtendedableQuery: Default {
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

    // impl<Q, L> ExtendedableQuery for ExtendingStringQuery<Q, L> {
    //     type Query = Q;
    //     type Lang = L;
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

    impl GenQuery for Query {
        type Lang = Language;
        type Ext = ExtendingStringQuery;

        fn pattern_count(&self) -> usize {
            self.pattern_count()
        }

        fn capture_index_for_name(&self, name: &str) -> Option<u32> {
            self.capture_index_for_name(name)
        }

        fn capture_quantifiers(&self, index: usize) -> impl std::ops::Index<usize, Output=CaptureQuantifier> {
            struct A([tree_sitter::CaptureQuantifier]);
            impl std::ops::Index<usize> for &A {
                type Output = tree_sitter::CaptureQuantifier;

                fn index(&self, index: usize) -> &Self::Output {
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

        type Node<'tree> = MyTSNode<'tree>;
        // type Node<'tree> = tree_sitter::Node<'tree>;

        type Matches<'query, 'cursor: 'query, 'tree: 'cursor> = MyQM<'query, 'cursor, 'tree>;

        type Cursor = tree_sitter::QueryCursor;

        fn matches<'query, 'cursor: 'query, 'tree: 'cursor>(
            &'query self,
            cursor: &'cursor mut Self::Cursor,
            node: &Self::Node<'tree>,
            // node: Self::Node<'tree>,
            // source: &'tree str,
        ) -> Self::Matches<'query, 'cursor, 'tree> {
            // let matches = cursor.matches(self, node, source.as_bytes());
            let matches = cursor.matches(self, node.node, node.source.as_bytes());
            MyQM { qm: matches, source: node.source }
        }

        type Match<'cursor, 'tree: 'cursor> = MyQueryMatch<'cursor, 'tree>;

        type I = u32;
    }
}

#[derive(Copy, PartialEq)]
pub struct MyTSNode<'tree> {
    pub(crate) node: tree_sitter::Node<'tree>,
    pub(crate) source: &'tree str,
}

impl<'tree> std::fmt::Debug for MyTSNode<'tree> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MyTSNode").field("node", &self.node).finish()
    }
}

impl<'tree> std::ops::Deref for MyTSNode<'tree> {
    type Target = tree_sitter::Node<'tree>;

    fn deref(&self) -> &Self::Target {
        &self.node
    }
}

impl<'tree> SyntaxNode for MyTSNode<'tree> {
    fn id(&self) -> usize {
        self.node.id()
    }

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

    fn parent(&self) -> Option<Self>
    where
        Self: Sized,
    {
        self.node.parent().map(|node| Self {
            node,
            source: self.source,
        })
    }
}

impl<'tree> SyntaxNodeExt for MyTSNode<'tree> {
    type Cursor = tree_sitter::TreeCursor<'tree>;
    fn walk(&self) -> Self::Cursor {
        self.node.walk()
    }
    fn named_children<'cursor>(
        &self,
        cursor: &'cursor mut Self::Cursor,
    ) -> impl ExactSizeIterator<Item = Self> + 'cursor
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
            MyTSNode {
                node,
                source: source,
            }
        })
    }
    type QM<'cursor> = MyQueryMatch<'cursor, 'tree> where 'tree: 'cursor;
}

pub struct MyQueryMatch<'cursor, 'tree> {
    pub mat: tree_sitter::QueryMatch<'cursor, 'tree>,
    pub source: &'tree str,
}
impl<'cursor, 'tree> std::fmt::Debug for MyQueryMatch<'cursor, 'tree> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MyTSQueryMatch").field("mat", &self.mat).finish()
    }
}

impl<'cursor, 'tree> std::ops::Deref for MyQueryMatch<'cursor, 'tree> {
    type Target = tree_sitter::QueryMatch<'cursor, 'tree>;

    fn deref(&self) -> &Self::Target {
        &self.mat
    }
}

impl<'cursor, 'tree> crate::graph::QMatch for MyQueryMatch<'cursor, 'tree> {
    type I = u32;

    type Item = MyTSNode<'tree>;

    fn nodes_for_capture_index(&self, index: Self::I) -> impl Iterator<Item = Self::Item> + '_ {
        self.mat
            .nodes_for_capture_index(index)
            .map(move |node| MyTSNode {
                node,
                source: self.source,
            })
    }
    fn pattern_index(&self) -> usize {
        self.mat.pattern_index
    }
}

impl<'tree> Clone for MyTSNode<'tree> {
    fn clone(&self) -> Self {
        Self {
            node: self.node.clone(),
            source: self.source,
        }
    }
}

pub struct MyQM<'query, 'cursor, 'tree> {
    pub source: &'tree str,
    pub(crate) qm: tree_sitter::QueryMatches<'query, 'cursor, &'tree [u8], &'tree [u8]>,
}

impl<'query, 'cursor: 'query, 'tree: 'cursor + 'query> Iterator for MyQM<'query, 'cursor, 'tree> {
    type Item = MyQueryMatch<'cursor, 'tree>;

    fn next(&mut self) -> Option<Self::Item> {
        let m = self.qm.next()?;
        // TODO is there a bug in tree_sitter::QueryMatches::next ?
        // the lifetime names are not matching
        let m = unsafe { std::mem::transmute(m) };
        Some(MyQueryMatch {mat: m, source: self.source})
    }
}

pub trait GenQuery {
    type Lang;
    type Ext: ExtendedableQuery<Query = Self, Lang = Self::Lang>;
    fn pattern_count(&self) -> usize;
    fn capture_index_for_name(&self, name: &str) -> Option<u32>;
    fn capture_quantifiers(&self, index: usize) -> impl std::ops::Index<usize, Output=CaptureQuantifier>;
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

    type Node<'tree>: SyntaxNodeExt;

    type Cursor: Default;

    type Matches<'query, 'cursor: 'query, 'tree: 'cursor>: IntoIterator<
        Item = Self::Match<'cursor, 'tree>,
    >
    where
        Self: 'query,
        Self: 'cursor;

    type Match<'cursor, 'tree: 'cursor>: QMatch<I = Self::I>
    where
        Self: 'cursor;

    type I;

    fn matches<'query, 'cursor: 'query, 'tree: 'cursor>(
        &'query self,
        cursor: &'cursor mut Self::Cursor,
        node: &Self::Node<'tree>,
        // tree: Self::Node<'tree>,
        // source: &'tree str,
    ) -> Self::Matches<'query, 'cursor, 'tree>;
}
