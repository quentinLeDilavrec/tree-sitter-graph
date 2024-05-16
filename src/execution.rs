// -*- coding: utf-8 -*-
// ------------------------------------------------------------------------------------------------
// Copyright © 2021, tree-sitter authors.
// Licensed under either of Apache License, Version 2.0, or MIT license, at your option.
// Please see the LICENSE-APACHE or LICENSE-MIT files in this distribution for license details.
// ------------------------------------------------------------------------------------------------

use thiserror::Error;
use tree_sitter::CaptureQuantifier;
use tree_sitter::Node;
use tree_sitter::QueryMatch;
use tree_sitter::Tree;

use crate::ast::CreateEdge;
use crate::ast::File;
use crate::ast::Stanza;
use crate::ast::Variable;
use crate::execution::error::ExecutionError;
use crate::functions::Functions;
use crate::generic_query::MyQueryMatch;
use crate::graph::Attributes;
use crate::graph::Graph;
use crate::graph::GraphErazing;
use crate::graph::QMatch;
use crate::graph::TSNodeErazing;
use crate::graph::Value;
use crate::graph::WithSynNodes;
use crate::variables::Globals;
use crate::Identifier;
use crate::Location;
use crate::MyTSNode;

pub(crate) mod error;
mod lazy;
mod strict;

impl File<tree_sitter::Query> {
    /// Executes this graph DSL file against a source file.  You must provide the parsed syntax
    /// tree (`tree`) as well as the source text that it was parsed from (`source`).  You also
    /// provide the set of functions and global variables that are available during execution.
    pub fn execute<'a, 'tree>(
        &self,
        tree: &'tree Tree,
        source: &'tree str,
        config: &ExecutionConfig<GraphErazing<TSNodeErazing>>,
        cancellation_flag: &dyn CancellationFlag,
    ) -> Result<Graph<MyTSNode<'tree>>, ExecutionError> {
        let mut graph = Graph::new();
        self.execute_into(&mut graph, tree, source, config, cancellation_flag)?;
        Ok(graph)
    }

    /// Executes this graph DSL file against a source file, saving the results into an existing
    /// `Graph` instance.  You must provide the parsed syntax tree (`tree`) as well as the source
    /// text that it was parsed from (`source`).  You also provide the set of functions and global
    /// variables that are available during execution. This variant is useful when you need to
    /// “pre-seed” the graph with some predefined nodes and/or edges before executing the DSL file.
    pub fn execute_into<'a, 'tree>(
        &self,
        graph: &mut Graph<MyTSNode<'tree>>,
        tree: &'tree Tree,
        source: &'tree str,
        config: &ExecutionConfig<GraphErazing<TSNodeErazing>>,
        cancellation_flag: &dyn CancellationFlag,
    ) -> Result<(), ExecutionError> {
        if config.lazy {
            self.execute_lazy_into(graph, tree, source, config, cancellation_flag)
        } else {
            self.execute_strict_into(graph, tree, source, config, cancellation_flag)
        }
    }

    pub fn try_visit_matches<'tree, E, F>(
        &self,
        tree: &'tree Tree,
        source: &'tree str,
        lazy: bool,
        mut visit: F,
    ) -> Result<(), E>
    where
        F: FnMut(Match<MyQueryMatch<'_, 'tree>>) -> Result<(), E>,
    {
        if lazy {
            let file_query = self.query.as_ref().expect("missing file query");
            self.try_visit_matches_lazy(tree, source, |stanza, mat| {
                let named_captures = stanza
                    .query
                    .capture_names()
                    .iter()
                    .map(|name| {
                        let index = file_query
                            .capture_index_for_name(name)
                            .expect("missing index for capture");
                        let quantifier =
                            file_query.capture_quantifiers(mat.pattern_index)[index as usize];
                        (name.to_string(), quantifier, index)
                    })
                    .filter(|c| c.2 != stanza.full_match_file_capture_index as u32)
                    .collect();
                visit(Match {
                    mat,
                    full_capture_index: stanza.full_match_file_capture_index as u32,
                    named_captures,
                    query_location: stanza.range.start,
                })
            })
        } else {
            self.try_visit_matches_strict(tree, source, |stanza, mat| {
                let named_captures = stanza
                    .query
                    .capture_names()
                    .iter()
                    .map(|name| {
                        let index = stanza
                            .query
                            .capture_index_for_name(name)
                            .expect("missing index for capture");
                        let quantifier = stanza.query.capture_quantifiers(0)[index as usize];
                        (name.to_string(), quantifier, index)
                    })
                    .filter(|c| c.2 != stanza.full_match_stanza_capture_index as u32)
                    .collect();
                visit(Match {
                    mat,
                    full_capture_index: stanza.full_match_stanza_capture_index as u32,
                    named_captures,
                    query_location: stanza.range.start,
                })
            })
        }
    }
}

impl<Q: crate::GenQuery, I> File<Q, I> {

    pub(self) fn check_globals(&self, globals: &mut Globals) -> Result<(), ExecutionError> {
        for global in &self.globals {
            match globals.get(&global.name) {
                None => {
                    if let Some(default) = &global.default {
                        globals
                            .add(global.name.clone(), default.to_string().into())
                            .map_err(|_| {
                                ExecutionError::DuplicateVariable(format!(
                                    "global variable {} already defined",
                                    global.name
                                ))
                            })?;
                    } else {
                        return Err(ExecutionError::MissingGlobalVariable(
                            global.name.as_str().to_string(),
                        ));
                    }
                }
                Some(value) => {
                    if global.quantifier == CaptureQuantifier::ZeroOrMore
                        || global.quantifier == CaptureQuantifier::OneOrMore
                    {
                        if value.as_list().is_err() {
                            return Err(ExecutionError::ExpectedList(
                                global.name.as_str().to_string(),
                            ));
                        }
                    }
                }
            }
        }

        Ok(())
    }
}

impl Stanza<tree_sitter::Query> {
    pub fn try_visit_matches<'tree, E, F>(
        &self,
        tree: &'tree Tree,
        source: &'tree str,
        mut visit: F,
    ) -> Result<(), E>
    where
        F: FnMut(Match<MyQueryMatch<'_, 'tree>>) -> Result<(), E>,
    {
        self.try_visit_matches_strict(tree, source, |mat| {
            let named_captures: Vec<(String, CaptureQuantifier, u32)> = self
                .query
                .capture_names()
                .iter()
                .flat_map(|name| {
                    if let Some(index) = self.query.capture_index_for_name(name) {
                        let quantifier = self.query.capture_quantifiers(0)[index as usize];
                        Some((name.to_string(), quantifier, index))
                    } else {
                        None
                    }
                })
                .filter(|c| c.2 != self.full_match_stanza_capture_index)
                .collect();
            visit(Match {
                mat,
                full_capture_index: self.full_match_stanza_capture_index,
                named_captures,
                query_location: self.range.start,
            })
        })
    }
}

pub struct Match<QM> {
    mat: QM, // QueryMatch<'a, 'tree>
    full_capture_index: u32,
    named_captures: Vec<(String, CaptureQuantifier, u32)>,
    query_location: Location,
}

impl<'a, 'tree> Match<QueryMatch<'a, 'tree>> {

    /// Return the matched nodes for a named capture.
    pub fn named_capture<'s: 'a + 'tree>(
        &'s self,
        name: &str,
    ) -> Option<(CaptureQuantifier, impl Iterator<Item = Node<'tree>> + 's)> {
        self.named_captures
            .iter()
            .find(|c| c.0 == name)
            .map(|c| (c.1, self.mat.nodes_for_capture_index(c.2)))
    }
}

impl<QM: QMatch> Match<QM> {
    /// Return the top-level matched node.
    pub fn full_capture(&self) -> QM::Item {
        self.mat
            .nodes_for_capture_index((self.full_capture_index as u32).into())
            .next()
            .expect("missing full capture")
    }

    /// Return the matched nodes for a named capture.
    pub fn named_captures<'s>(
        &'s self,
    ) -> impl Iterator<
        Item = (
            String,
            CaptureQuantifier,
            impl Iterator<Item = QM::Item> + 's,
        ),
    > {
        self.named_captures
            .iter()
            .map(move |c| (c.0.clone(), c.1, self.mat.nodes_for_capture_index((c.2 as u32).into())))
    }

    /// Return an iterator over all capture names.
    pub fn capture_names(&self) -> impl Iterator<Item = String> + '_ {
        self.named_captures.iter().map(|c| c.0.clone())
    }

    /// Return the query location.
    pub fn query_location(&self) -> &Location {
        &self.query_location
    }
}

/// Configuration for the execution of a File
pub struct ExecutionConfig<'a, 'g, G> {
    pub(crate) functions: &'a Functions<G>,
    pub(crate) globals: &'a Globals<'g>,
    pub(crate) lazy: bool,
    pub(crate) location_attr: Option<Identifier>,
    pub(crate) variable_name_attr: Option<Identifier>,
    pub(crate) match_node_attr: Option<Identifier>,
}

impl<'a, 'g, G> ExecutionConfig<'a, 'g, G> {
    pub fn new(functions: &'a Functions<G>, globals: &'a Globals<'g>) -> Self {
        Self {
            functions,
            globals,
            lazy: false,
            location_attr: None,
            variable_name_attr: None,
            match_node_attr: None,
        }
    }

    pub fn debug_attributes(
        self,
        location_attr: Identifier,
        variable_name_attr: Identifier,
        match_node_attr: Identifier,
    ) -> Self {
        Self {
            functions: self.functions,
            globals: self.globals,
            lazy: self.lazy,
            location_attr: location_attr.into(),
            variable_name_attr: variable_name_attr.into(),
            match_node_attr: match_node_attr.into(),
        }
    }

    pub fn lazy(self, lazy: bool) -> Self {
        Self {
            functions: self.functions,
            globals: self.globals,
            lazy,
            location_attr: self.location_attr,
            variable_name_attr: self.variable_name_attr,
            match_node_attr: self.match_node_attr,
        }
    }
}

/// Trait to signal that the execution is cancelled
pub trait CancellationFlag {
    fn check(&self, at: &'static str) -> Result<(), CancellationError>;
}

pub struct NoCancellation;
impl CancellationFlag for NoCancellation {
    fn check(&self, _at: &'static str) -> Result<(), CancellationError> {
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("Cancelled at \"{0}\"")]
pub struct CancellationError(pub &'static str);

impl Value {
    pub fn from_nodes<'tree, NI: IntoIterator<Item = G::Node>, G: WithSynNodes>(
        graph: &mut G,
        nodes: NI,
        quantifier: CaptureQuantifier,
    ) -> Value {
        let mut nodes = nodes.into_iter();
        match quantifier {
            CaptureQuantifier::Zero => unreachable!(),
            CaptureQuantifier::One => {
                let syntax_node = graph.add_syntax_node(nodes.next().expect("missing capture"));
                syntax_node.into()
            }
            CaptureQuantifier::ZeroOrMore | CaptureQuantifier::OneOrMore => {
                let syntax_nodes = nodes
                    .map(|n| graph.add_syntax_node(n.clone()).into())
                    .collect::<Vec<Value>>();
                syntax_nodes.into()
            }
            CaptureQuantifier::ZeroOrOne => match nodes.next() {
                None => Value::Null.into(),
                Some(node) => {
                    let syntax_node = graph.add_syntax_node(node);
                    syntax_node.into()
                }
            },
        }
    }
}

impl CreateEdge {
    pub(crate) fn add_debug_attrs<G>(
        &self,
        attributes: &mut Attributes,
        config: &ExecutionConfig<G>,
    ) -> Result<(), ExecutionError> {
        if let Some(location_attr) = &config.location_attr {
            attributes
                .add(
                    location_attr.clone(),
                    format!(
                        "line {} column {}",
                        self.location.row + 1,
                        self.location.column + 1
                    ),
                )
                .map_err(|_| 
                    ExecutionError::DuplicateAttribute(location_attr.as_str().into()))?;
        }
        Ok(())
    }
}
impl Variable {
    pub(crate) fn add_debug_attrs<G>(
        &self,
        attributes: &mut Attributes,
        config: &ExecutionConfig<G>,
    ) -> Result<(), ExecutionError> {
        if let Some(variable_name_attr) = &config.variable_name_attr {
            attributes
                .add(variable_name_attr.clone(), format!("{}", self))
                .map_err(|_| {
                    ExecutionError::DuplicateAttribute(variable_name_attr.as_str().into())
                })?;
        }
        if let Some(location_attr) = &config.location_attr {
            let location = match &self {
                Variable::Scoped(v) => v.location,
                Variable::Unscoped(v) => v.location,
            };
            attributes
                .add(
                    location_attr.clone(),
                    format!("line {} column {}", location.row + 1, location.column + 1),
                )
                .map_err(|_|
                    ExecutionError::DuplicateAttribute(location_attr.as_str().into()))?;
        }
        Ok(())
    }
}
