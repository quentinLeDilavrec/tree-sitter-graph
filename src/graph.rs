// -*- coding: utf-8 -*-
// ------------------------------------------------------------------------------------------------
// Copyright © 2021, tree-sitter authors.
// Licensed under either of Apache License, Version 2.0, or MIT license, at your option.
// Please see the LICENSE-APACHE or LICENSE-MIT files in this distribution for license details.
// ------------------------------------------------------------------------------------------------

//! Defines data types for the graphs produced by the graph DSL

use std::borrow::Borrow;
use std::collections::hash_map::Entry;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::fmt;
use std::fs::File;
use std::hash::Hash;
use std::io::prelude::*;
use std::io::stdout;
use std::ops::Index;
use std::ops::IndexMut;
use std::path::Path;

use serde::ser::SerializeMap;
use serde::ser::SerializeSeq;
use serde::Serialize;
use serde::Serializer;
use serde_json;
use smallvec::SmallVec;
use tree_sitter::Node;

use crate::execution::error::ExecutionError;
use crate::Identifier;
use crate::Location;
use crate::MyTSNode;

/// A graph produced by executing a graph DSL file.  Graphs include a lifetime parameter to ensure
/// that they don't outlive the tree-sitter syntax tree that they are generated from.
pub struct Graph<S> {
    pub(crate) syntax_nodes: HashMap<SyntaxNodeID, S>,
    graph_nodes: Vec<GraphNode>,
}

impl<S> Default for Graph<S> {
    fn default() -> Self {
        Self {
            syntax_nodes: Default::default(),
            graph_nodes: Default::default(),
        }
    }
}

pub trait SyntaxNode {
    fn id(&self) -> usize;
    fn kind(&self) -> &'static str;
    fn start_position(&self) -> tree_sitter::Point;
    fn end_position(&self) -> tree_sitter::Point;
    fn byte_range(&self) -> std::ops::Range<usize>;
    fn range(&self) -> tree_sitter::Range;
    fn text(&self) -> String;
    fn named_child_count(&self) -> usize;
    fn parent(&self) -> Option<Self>
    where
        Self: Sized;
}

pub trait SyntaxNodeExt: SyntaxNode + Clone {
    type Cursor;
    fn walk(&self) -> Self::Cursor;
    fn named_children<'cursor>(
        &self,
        cursor: &'cursor mut Self::Cursor,
    ) -> impl ExactSizeIterator<Item = Self> + 'cursor
    where
        Self: 'cursor;

    type QM<'cursor>: QMatch<Item = Self>
    where
        Self: 'cursor;
}

// impl<'tree> SyntaxNode for Node<'tree> {
//     fn id(&self) -> usize {
//         self.id()
//     }

//     fn kind(&self) -> &'static str {
//         self.kind()
//     }

//     fn start_position(&self) -> tree_sitter::Point {
//         self.start_position()
//     }

//     fn end_position(&self) -> tree_sitter::Point {
//         self.end_position()
//     }

//     fn byte_range(&self) -> std::ops::Range<usize> {
//         self.byte_range()
//     }
//     fn range(&self) -> tree_sitter::Range {
//         self.range()
//     }
//     fn text(&self) -> String {
//         Default::default()
//         // unimplemented!("no access to source")
//     }
//     fn named_child_count(&self) -> usize {
//         self.named_child_count()
//     }

//     fn parent(&self) -> Option<Self>
//     where
//         Self: Sized,
//     {
//         self.parent()
//     }
// }

// impl<'tree> SyntaxNodeExt for Node<'tree> {
//     type Cursor = tree_sitter::TreeCursor<'tree>;
//     fn walk(&self) -> Self::Cursor {
//         self.walk()
//     }
//     fn named_children<'cursor>(
//         &self,
//         cursor: &'cursor mut Self::Cursor,
//     ) -> impl ExactSizeIterator<Item = Self> + 'cursor
//     where
//         Self: 'cursor,
//     {
//         self.named_children(cursor)
//     }
//     type QM<'cursor> = MyTSQueryMatch<'cursor, 'tree> where 'tree: 'cursor;
// }

pub(crate) type SyntaxNodeID = u32;
type GraphNodeID = u32;

impl<S> Graph<S> {
    /// Creates a new, empty graph.
    pub fn new() -> Self {
        Graph::default()
    }
}

pub trait WithSynNodes:
    LErazng + Index<GraphNodeRef, Output = GraphNode> + IndexMut<GraphNodeRef, Output = GraphNode>
{
    type Node: SyntaxNodeExt + Clone;
    fn node(&self, r: SyntaxNodeRef) -> Option<&Self::Node>;

    /// Adds a new graph node to the graph, returning a graph DSL reference to it.
    fn add_graph_node(&mut self) -> GraphNodeRef;
    fn add_syntax_node(&mut self, node: Self::Node) -> SyntaxNodeRef;
}

pub struct GraphErazing<S>(std::marker::PhantomData<S>);
pub struct TSNodeErazing;

impl<S> Default for GraphErazing<S> {
    fn default() -> Self {
        Self(Default::default())
    }
}

pub trait Erzd {
    type Original<'a>;
}

impl<S: Erzd> Erzd for GraphErazing<S> {
    type Original<'a> = Graph<S::Original<'a>>;
}

impl Erzd for TSNodeErazing {
    type Original<'tree> = MyTSNode<'tree>;
}

pub trait LErazng {
    type LErazing: Erzd;
}

impl<'tree> LErazng for MyTSNode<'tree> {
    type LErazing = TSNodeErazing;
}

impl<S: LErazng> LErazng for Graph<S> {
    type LErazing = GraphErazing<S::LErazing>;
}

impl<S: LErazng + SyntaxNodeExt + Clone> WithSynNodes for Graph<S> {
    type Node = S;

    fn node(&self, r: SyntaxNodeRef) -> Option<&Self::Node> {
        self.syntax_nodes.get(&r.index)
    }

    fn add_graph_node(&mut self) -> GraphNodeRef {
        self.add_graph_node()
    }

    fn add_syntax_node(&mut self, node: S) -> SyntaxNodeRef {
        self.add_syntax_node(node)
    }
}

pub trait QMatch {
    type I: Copy + From<u32>;
    type Item;
    fn nodes_for_capture_index(&self, index: Self::I) -> impl Iterator<Item = Self::Item> + '_;
    fn pattern_index(&self) -> usize;
}

impl<S: SyntaxNodeExt> Graph<S> {
    /// Adds a syntax node to the graph, returning a graph DSL reference to it.
    ///
    /// The graph won't contain _every_ syntax node in the parsed syntax tree; it will only contain
    /// those nodes that are referenced at some point during the execution of the graph DSL file.
    pub fn add_syntax_node(&mut self, node: S) -> SyntaxNodeRef {
        let index = node.id() as SyntaxNodeID;
        let index = index as SyntaxNodeID;
        let node_ref = SyntaxNodeRef {
            index,
            kind: node.kind(),
            position: node.start_position(),
        };
        self.syntax_nodes.entry(index).or_insert(node);
        node_ref
    }

    /// Adds a new graph node to the graph, returning a graph DSL reference to it.
    pub fn add_graph_node(&mut self) -> GraphNodeRef {
        let graph_node = GraphNode::new();
        let index = self.graph_nodes.len() as GraphNodeID;
        self.graph_nodes.push(graph_node);
        GraphNodeRef(index)
    }

    // Returns an iterator of references to all of the nodes in the graph.
    pub fn iter_nodes(&self) -> impl Iterator<Item = GraphNodeRef> {
        (0..self.graph_nodes.len() as u32).map(GraphNodeRef)
    }

    // Returns the number of nodes in the graph.
    pub fn node_count(&self) -> usize {
        self.graph_nodes.len()
    }
}

impl<'tree, S> Graph<S> {
    /// Pretty-prints the contents of this graph.
    pub fn pretty_print<'a>(&'a self) -> impl fmt::Display + 'a {
        struct DisplayGraph<'a, S>(&'a Graph<S>);

        impl<'a, S> fmt::Display for DisplayGraph<'a, S> {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let graph = self.0;
                for (node_index, node) in graph.graph_nodes.iter().enumerate() {
                    writeln!(f, "node {}", node_index)?;
                    write!(f, "{}", node.attributes)?;
                    for (sink, edge) in &node.outgoing_edges {
                        writeln!(f, "edge {} -> {}", node_index, *sink)?;
                        write!(f, "{}", edge.attributes)?;
                    }
                }
                Ok(())
            }
        }

        DisplayGraph(self)
    }

    pub fn display_json(&self, path: Option<&Path>) -> std::io::Result<()> {
        let s = serde_json::to_string_pretty(self).unwrap();
        path.map_or(stdout().write_all(s.as_bytes()), |path| {
            File::create(path)?.write_all(s.as_bytes())
        })
    }
}

impl<S> Index<SyntaxNodeRef> for Graph<S> {
    type Output = S;
    fn index(&self, node_ref: SyntaxNodeRef) -> &S {
        &self.syntax_nodes[&node_ref.index]
    }
}

impl<S> Index<GraphNodeRef> for Graph<S> {
    type Output = GraphNode;
    fn index(&self, index: GraphNodeRef) -> &GraphNode {
        &self.graph_nodes[index.0 as usize]
    }
}

impl<S> IndexMut<GraphNodeRef> for Graph<S> {
    fn index_mut(&mut self, index: GraphNodeRef) -> &mut GraphNode {
        &mut self.graph_nodes[index.0 as usize]
    }
}

impl<N> Serialize for Graph<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.graph_nodes.len()))?;
        for (node_index, node) in self.graph_nodes.iter().enumerate() {
            seq.serialize_element(&SerializeGraphNode(node_index, node))?;
        }
        seq.end()
    }
}

/// A node in a graph
pub struct GraphNode {
    outgoing_edges: SmallVec<[(GraphNodeID, Edge); 8]>,
    /// The set of attributes associated with this graph node
    pub attributes: Attributes,
}

impl GraphNode {
    fn new() -> GraphNode {
        GraphNode {
            outgoing_edges: SmallVec::new(),
            attributes: Attributes::new(),
        }
    }

    /// Adds an edge to this node.  There can be at most one edge connecting any two graph nodes;
    /// the result indicates whether the edge is new (`Ok`) or already existed (`Err`).  In either
    /// case, you also get a mutable reference to the [`Edge`][] instance for the edge.
    pub fn add_edge(&mut self, sink: GraphNodeRef) -> Result<&mut Edge, &mut Edge> {
        let sink = sink.0;
        match self
            .outgoing_edges
            .binary_search_by_key(&sink, |(sink, _)| *sink)
        {
            Ok(index) => Err(&mut self.outgoing_edges[index].1),
            Err(index) => {
                self.outgoing_edges.insert(index, (sink, Edge::new()));
                Ok(&mut self.outgoing_edges[index].1)
            }
        }
    }

    /// Returns a reference to an outgoing edge from this node, if it exists.
    pub fn get_edge(&self, sink: GraphNodeRef) -> Option<&Edge> {
        let sink = sink.0;
        self.outgoing_edges
            .binary_search_by_key(&sink, |(sink, _)| *sink)
            .ok()
            .map(|index| &self.outgoing_edges[index].1)
    }

    /// Returns a mutable reference to an outgoing edge from this node, if it exists.
    pub fn get_edge_mut(&mut self, sink: GraphNodeRef) -> Option<&mut Edge> {
        let sink = sink.0;
        self.outgoing_edges
            .binary_search_by_key(&sink, |(sink, _)| *sink)
            .ok()
            .map(move |index| &mut self.outgoing_edges[index].1)
    }

    // Returns an iterator of all of the outgoing edges from this node.
    pub fn iter_edges(&self) -> impl Iterator<Item = (GraphNodeRef, &Edge)> + '_ {
        self.outgoing_edges
            .iter()
            .map(|(id, edge)| (GraphNodeRef(*id), edge))
    }

    // Returns the number of outgoing edges from this node.
    pub fn edge_count(&self) -> usize {
        self.outgoing_edges.len()
    }
}

struct SerializeGraphNode<'a>(usize, &'a GraphNode);

impl<'a> Serialize for SerializeGraphNode<'a> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let node_index = self.0;
        let node = self.1;
        // serializing as a map instead of a struct so we don't have to encode a struct name
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry("id", &node_index)?;
        map.serialize_entry("edges", &SerializeGraphNodeEdges(&node.outgoing_edges))?;
        map.serialize_entry("attrs", &node.attributes)?;
        map.end()
    }
}

struct SerializeGraphNodeEdges<'a>(&'a SmallVec<[(GraphNodeID, Edge); 8]>);

impl<'a> Serialize for SerializeGraphNodeEdges<'a> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let edges = self.0;
        let mut seq = serializer.serialize_seq(Some(edges.len()))?;
        for element in edges {
            seq.serialize_element(&SerializeGraphNodeEdge(&element))?;
        }
        seq.end()
    }
}

struct SerializeGraphNodeEdge<'a>(&'a (GraphNodeID, Edge));

impl<'a> Serialize for SerializeGraphNodeEdge<'a> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let wrapped = &self.0;
        let sink = &wrapped.0;
        let edge = &wrapped.1;
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry("sink", sink)?;
        map.serialize_entry("attrs", &edge.attributes)?;
        map.end()
    }
}

/// An edge between two nodes in a graph
pub struct Edge {
    /// The set of attributes associated with this edge
    pub attributes: Attributes,
}

impl Edge {
    fn new() -> Edge {
        Edge {
            attributes: Attributes::new(),
        }
    }
}

/// A set of attributes associated with a graph node or edge
#[derive(Clone, Debug)]
pub struct Attributes {
    values: HashMap<Identifier, Value>,
}

impl Attributes {
    /// Creates a new, empty set of attributes.
    pub fn new() -> Attributes {
        Attributes {
            values: HashMap::new(),
        }
    }

    /// Adds an attribute to this attribute set.  If there was already an attribute with the same
    /// name, replaces its value and returns `Err`.
    pub fn add<V: Into<Value>>(&mut self, name: Identifier, value: V) -> Result<(), Value> {
        match self.values.entry(name) {
            Entry::Occupied(mut o) => {
                let value = value.into();
                if o.get() != &value {
                    Err(o.insert(value.into()))
                } else {
                    Ok(())
                }
            }
            Entry::Vacant(v) => {
                v.insert(value.into());
                Ok(())
            }
        }
    }

    /// Returns the value of a particular attribute, if it exists.
    pub fn get<Q>(&self, name: &Q) -> Option<&Value>
    where
        Q: ?Sized + Eq + Hash,
        Identifier: Borrow<Q>,
    {
        self.values.get(name.borrow())
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Identifier, &Value)> {
        self.values.iter()
    }
}

impl std::fmt::Display for Attributes {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut keys = self.values.keys().collect::<Vec<_>>();
        keys.sort_by(|a, b| a.cmp(b));
        for key in &keys {
            let value = &self.values[*key];
            writeln!(f, "  {}: {:?}", key, value)?;
        }
        Ok(())
    }
}

impl Serialize for Attributes {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(None)?;
        for (key, value) in &self.values {
            map.serialize_entry(key, value)?;
        }
        map.end()
    }
}

/// The value of an attribute
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Value {
    // Scalar
    Null,
    Boolean(bool),
    Integer(u32),
    String(String),
    // Compound
    List(Vec<Value>),
    Set(BTreeSet<Value>),
    // References
    SyntaxNode(SyntaxNodeRef),
    GraphNode(GraphNodeRef),
}

impl Value {
    /// Check if this value is null
    pub fn is_null(&self) -> bool {
        match self {
            Value::Null => true,
            _ => false,
        }
    }

    /// Coerces this value into a boolean, returning an error if it's some other type of value.
    pub fn into_boolean(self) -> Result<bool, ExecutionError> {
        match self {
            Value::Boolean(value) => Ok(value),
            _ => Err(ExecutionError::ExpectedBoolean(format!("got {}", self))),
        }
    }

    pub fn as_boolean(&self) -> Result<bool, ExecutionError> {
        match self {
            Value::Boolean(value) => Ok(*value),
            _ => Err(ExecutionError::ExpectedBoolean(format!("got {}", self))),
        }
    }

    /// Coerces this value into an integer, returning an error if it's some other type of value.
    pub fn into_integer(self) -> Result<u32, ExecutionError> {
        match self {
            Value::Integer(value) => Ok(value),
            _ => Err(ExecutionError::ExpectedInteger(format!("got {}", self))),
        }
    }

    pub fn as_integer(&self) -> Result<u32, ExecutionError> {
        match self {
            Value::Integer(value) => Ok(*value),
            _ => Err(ExecutionError::ExpectedInteger(format!("got {}", self))),
        }
    }

    /// Coerces this value into a string, returning an error if it's some other type of value.
    pub fn into_string(self) -> Result<String, ExecutionError> {
        match self {
            Value::String(value) => Ok(value),
            _ => Err(ExecutionError::ExpectedString(format!("got {}", self))),
        }
    }

    pub fn as_str(&self) -> Result<&str, ExecutionError> {
        match self {
            Value::String(value) => Ok(value),
            _ => Err(ExecutionError::ExpectedString(format!("got {}", self))),
        }
    }

    /// Coerces this value into a list, returning an error if it's some other type of value.
    pub fn into_list(self) -> Result<Vec<Value>, ExecutionError> {
        match self {
            Value::List(values) => Ok(values),
            _ => Err(ExecutionError::ExpectedList(format!("got {}", self))),
        }
    }

    pub fn as_list(&self) -> Result<&Vec<Value>, ExecutionError> {
        match self {
            Value::List(values) => Ok(values),
            _ => Err(ExecutionError::ExpectedList(format!("got {}", self))),
        }
    }

    /// Coerces this value into a graph node reference, returning an error if it's some other type
    /// of value.
    pub fn into_graph_node_ref<'a, 'tree>(self) -> Result<GraphNodeRef, ExecutionError> {
        match self {
            Value::GraphNode(node) => Ok(node),
            _ => Err(ExecutionError::ExpectedGraphNode(format!("got {}", self))),
        }
    }

    pub fn as_graph_node_ref<'a, 'tree>(&self) -> Result<GraphNodeRef, ExecutionError> {
        match self {
            Value::GraphNode(node) => Ok(*node),
            _ => Err(ExecutionError::ExpectedGraphNode(format!("got {}", self))),
        }
    }

    /// Coerces this value into a syntax node reference, returning an error if it's some other type
    /// of value.
    pub fn into_syntax_node_ref<'a, 'tree>(self) -> Result<SyntaxNodeRef, ExecutionError> {
        match self {
            Value::SyntaxNode(node) => Ok(node),
            _ => Err(ExecutionError::ExpectedSyntaxNode(format!("got {}", self))),
        }
    }

    /// Coerces this value into a syntax node, returning an error if it's some other type
    /// of value.
    #[deprecated(note = "Use the pattern graph[value.into_syntax_node_ref(graph)] instead")]
    pub fn into_syntax_node<'a, S: LErazng + SyntaxNodeExt>(
        self,
        graph: &'a Graph<S>,
    ) -> Result<&'a S, ExecutionError> {
        graph
            .node(self.into_syntax_node_ref()?)
            .ok_or_else(|| todo!())
    }

    pub fn as_syntax_node_ref<'a, 'tree>(&self) -> Result<SyntaxNodeRef, ExecutionError> {
        match self {
            Value::SyntaxNode(node) => Ok(*node),
            _ => Err(ExecutionError::ExpectedSyntaxNode(format!("got {}", self))),
        }
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Value {
        Value::Boolean(value)
    }
}

impl From<u32> for Value {
    fn from(value: u32) -> Value {
        Value::Integer(value)
    }
}

impl From<&str> for Value {
    fn from(value: &str) -> Value {
        Value::String(value.to_string())
    }
}

impl From<String> for Value {
    fn from(value: String) -> Value {
        Value::String(value)
    }
}

impl From<Vec<Value>> for Value {
    fn from(value: Vec<Value>) -> Value {
        Value::List(value)
    }
}

impl From<BTreeSet<Value>> for Value {
    fn from(value: BTreeSet<Value>) -> Value {
        Value::Set(value)
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Value::Null => write!(f, "#null"),
            Value::Boolean(value) => {
                if *value {
                    write!(f, "#true")
                } else {
                    write!(f, "#false")
                }
            }
            Value::Integer(value) => write!(f, "{}", value),
            Value::String(value) => write!(f, "{}", value),
            Value::List(value) => {
                write!(f, "[")?;
                let mut first = true;
                for element in value {
                    if first {
                        write!(f, "{}", element)?;
                        first = false;
                    } else {
                        write!(f, ", {}", element)?;
                    }
                }
                write!(f, "]")
            }
            Value::Set(value) => {
                write!(f, "{{")?;
                let mut first = true;
                for element in value {
                    if first {
                        write!(f, "{}", element)?;
                        first = false;
                    } else {
                        write!(f, ", {}", element)?;
                    }
                }
                write!(f, "}}")
            }
            Value::SyntaxNode(node) => node.fmt(f),
            Value::GraphNode(node) => node.fmt(f),
        }
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Value::Null => write!(f, "#null"),
            Value::Boolean(value) => {
                if *value {
                    write!(f, "#true")
                } else {
                    write!(f, "#false")
                }
            }
            Value::Integer(value) => write!(f, "{:?}", value),
            Value::String(value) => write!(f, "{:?}", value),
            Value::List(value) => {
                write!(f, "[")?;
                let mut first = true;
                for element in value {
                    if first {
                        write!(f, "{:?}", element)?;
                        first = false;
                    } else {
                        write!(f, ", {:?}", element)?;
                    }
                }
                write!(f, "]")
            }
            Value::Set(value) => {
                write!(f, "{{")?;
                let mut first = true;
                for element in value {
                    if first {
                        write!(f, "{:?}", element)?;
                        first = false;
                    } else {
                        write!(f, ", {:?}", element)?;
                    }
                }
                write!(f, "}}")
            }
            Value::SyntaxNode(node) => node.fmt(f),
            Value::GraphNode(node) => node.fmt(f),
        }
    }
}

impl Serialize for Value {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Value::Null => {
                let mut map = serializer.serialize_map(None)?;
                map.serialize_entry("type", "null")?;
                map.end()
            }
            Value::Boolean(bool) => {
                let mut map = serializer.serialize_map(None)?;
                map.serialize_entry("type", "bool")?;
                map.serialize_entry("bool", bool)?;
                map.end()
            }
            Value::Integer(int) => {
                let mut map = serializer.serialize_map(None)?;
                map.serialize_entry("type", "int")?;
                map.serialize_entry("int", int)?;
                map.end()
            }
            Value::String(str) => {
                let mut map = serializer.serialize_map(None)?;
                map.serialize_entry("type", "string")?;
                map.serialize_entry("string", str)?;
                map.end()
            }
            Value::List(list) => {
                let mut map = serializer.serialize_map(None)?;
                map.serialize_entry("type", "list")?;
                map.serialize_entry("values", list)?;
                map.end()
            }
            Value::Set(set) => {
                let mut map = serializer.serialize_map(None)?;
                map.serialize_entry("type", "set")?;
                map.serialize_entry("values", set)?;
                map.end()
            }
            Value::SyntaxNode(node) => {
                let mut map = serializer.serialize_map(None)?;
                map.serialize_entry("type", "syntaxNode")?;
                map.serialize_entry("id", &node.index)?;
                map.end()
            }
            Value::GraphNode(node) => {
                let mut map = serializer.serialize_map(None)?;
                map.serialize_entry("type", "graphNode")?;
                map.serialize_entry("id", &node.0)?;
                map.end()
            }
        }
    }
}

/// A reference to a syntax node in a graph
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SyntaxNodeRef {
    pub(crate) index: SyntaxNodeID,
    kind: &'static str,
    position: tree_sitter::Point,
}

impl From<tree_sitter::Point> for Location {
    fn from(point: tree_sitter::Point) -> Location {
        Location {
            row: point.row,
            column: point.column,
        }
    }
}

impl SyntaxNodeRef {
    pub fn location(&self) -> Location {
        Location::from(self.position)
    }
}

impl From<SyntaxNodeRef> for Value {
    fn from(value: SyntaxNodeRef) -> Value {
        Value::SyntaxNode(value)
    }
}

impl std::fmt::Display for SyntaxNodeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "[syntax node {} ({}, {})]",
            self.kind,
            self.position.row + 1,
            self.position.column + 1,
        )
    }
}

impl std::fmt::Debug for SyntaxNodeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "[syntax node {} ({}, {})]",
            self.kind,
            self.position.row + 1,
            self.position.column + 1,
        )
    }
}

/// A reference to a graph node
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GraphNodeRef(GraphNodeID);

impl GraphNodeRef {
    /// Returns the index of the graph node that this reference refers to.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl From<GraphNodeRef> for Value {
    fn from(value: GraphNodeRef) -> Value {
        Value::GraphNode(value)
    }
}

impl std::fmt::Display for GraphNodeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "[graph node {}]", self.0)
    }
}

impl std::fmt::Debug for GraphNodeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "[graph node {}]", self.0)
    }
}
