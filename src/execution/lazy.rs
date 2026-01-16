// -*- coding: utf-8 -*-
// ------------------------------------------------------------------------------------------------
// Copyright © 2022, tree-sitter authors.
// Licensed under either of Apache License, Version 2.0, or MIT license, at your option.
// Please see the LICENSE-APACHE or LICENSE-MIT files in this distribution for license details.
// ------------------------------------------------------------------------------------------------

mod statements;
mod store;
mod values;

use log::{debug, trace};

use std::collections::HashMap;
use std::collections::HashSet;

use tree_sitter::Query;
use tree_sitter::QueryCursor;
use tree_sitter::Tree;

use streaming_iterator::StreamingIterator;

use crate::ast;
use crate::execution::error::ExecutionError;
use crate::execution::error::ResultWithExecutionError;
use crate::execution::error::StatementContext;
use crate::execution::ExecutionConfig;
use crate::functions::Functions;
use crate::generic_query::MatchLender;
use crate::generic_query::MatchLending;
use crate::generic_query::MatchesLending;
use crate::generic_query::MyQueryMatch;
use crate::graph;
use crate::graph::Attributes;
use crate::graph::Graph;
use crate::graph::NodeLending;
use crate::graph::NodesLending;
use crate::graph::QMatch;
use crate::graph::Value;
use crate::graph::WithAttrs as _;
use crate::graph::WithSynNodes;
use crate::variables::Globals;
use crate::variables::MutVariables;
use crate::variables::VariableMap;
use crate::CancellationFlag;
use crate::GenQuery;
use crate::Identifier;
use crate::MyTSNode;
use crate::QueryWithLang;

use statements::*;
use store::*;
use values::*;

/// Helper structure
///
/// Use it in case you want more control, instead of calling the different ast::File::execute_lazy*
///
/// It also reduces the number of generics and bounds involved, notably GenQuery
pub struct Ctx<'var> {
    locals: crate::variables::VariableMap<'var, LazyValue>,
    store: LazyStore,
    scoped_store: LazyScopedVariables,
    lazy_graph: LazyGraph,
    function_parameters: Vec<crate::graph::Value>,
    prev_element_debug_info: std::collections::HashMap<GraphElementKey, DebugInfo>,
}

impl Default for Ctx<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl Ctx<'_> {
    pub fn new() -> Self {
        Self {
            locals: crate::variables::VariableMap::new(),
            store: LazyStore::new(),
            scoped_store: LazyScopedVariables::new(),
            lazy_graph: LazyGraph::new(),
            function_parameters: Default::default(),
            prev_element_debug_info: Default::default(),
        }
    }

    pub fn clear(&mut self) {
        self.locals.clear()
    }

    pub fn eval<G: WithSynNodes>(
        &mut self,
        graph: &mut G,
        functions: &Functions<G>,
        inherited_variables: &HashSet<Identifier>,
        cancellation_flag: &dyn CancellationFlag,
    ) -> Result<(), ExecutionError> {
        let mut exec = EvaluationContext {
            graph,
            functions,
            store: &self.store,
            scoped_store: &self.scoped_store,
            inherited_variables,
            function_parameters: &mut self.function_parameters,
            prev_element_debug_info: &mut self.prev_element_debug_info,
            cancellation_flag,
        };
        self.lazy_graph.evaluate(&mut exec)?;
        // make sure any unforced values are now forced, to surface any problems
        // hidden by the fact that the values were unused
        self.store.evaluate_all(&mut exec)?;
        self.scoped_store.evaluate_all(&mut exec)?;
        Ok(())
    }

    /// Same as exec but using an explicit Syntax Node, abrv. as SNode
    ///
    /// Its just a word play,
    /// because I noticed that type inference had a hard time working with the bound of exec.
    /// exec is probably abusing the type check with the lending there, so it cannot compare the assoc SNodes.
    pub fn execplicit<G, QM, I, SNode>(
        &mut self,
        mat: &QM,
        graph: &mut G,
        inherited_variables: &HashSet<Identifier>,
        cancellation_flag: &dyn CancellationFlag,
        full_match_file_capture_index: I,
        shorthands: &crate::ast::AttributeShorthands,
        config: &crate::ExecutionConfig<'_, '_, '_, G>,
        current_regex_captures: &Vec<String>,
        statement: &crate::ast::Statement,
        error_context: crate::execution::error::StatementContext,
    ) -> Result<(), ExecutionError>
    where
        QM: QMatch<I = I>,
        G: WithSynNodes,
        for<'t, 'u> <QM as NodesLending<'u>>::Nodes: NodeLending<'t, SNode = SNode>,
        for<'t> G: NodeLending<'t, SNode = SNode>,
    {
        self.exec(
            graph,
            inherited_variables,
            cancellation_flag,
            full_match_file_capture_index,
            shorthands,
            mat,
            config,
            current_regex_captures,
            statement,
            error_context,
        )
    }

    pub fn exec<G, QM, I>(
        &mut self,
        graph: &mut G,
        inherited_variables: &HashSet<Identifier>,
        cancellation_flag: &dyn CancellationFlag,
        full_match_file_capture_index: I,
        shorthands: &crate::ast::AttributeShorthands,
        mat: &QM,
        config: &crate::ExecutionConfig<'_, '_, '_, G>,
        current_regex_captures: &Vec<String>,
        statement: &crate::ast::Statement,
        error_context: crate::execution::error::StatementContext,
    ) -> Result<(), ExecutionError>
    where
        QM: QMatch<I = I>,
        G: WithSynNodes,
        for<'t, 'u> <QM as NodesLending<'u>>::Nodes:
            NodeLending<'t, SNode = <G as NodeLending<'t>>::SNode>,
    {
        let mut exec = ExecutionContext {
            graph,
            config,
            locals: &mut self.locals,
            current_regex_captures,
            mat,
            full_match_file_capture_index,
            store: &mut self.store,
            scoped_store: &mut self.scoped_store,
            lazy_graph: &mut self.lazy_graph,
            function_parameters: &mut self.function_parameters,
            prev_element_debug_info: &mut self.prev_element_debug_info,
            error_context,
            inherited_variables,
            shorthands,
            cancellation_flag,
        };
        execute_stmt_lazy(statement, &mut exec).with_context(|| exec.error_context.into())
    }
}

impl ast::File<Query> {
    /// Executes this graph DSL file against a source file, saving the results into an existing
    /// `Graph` instance.  You must provide the parsed syntax tree (`tree`) as well as the source
    /// text that it was parsed from (`source`).  You also provide the set of functions and global
    /// variables that are available during execution. This variant is useful when you need to
    /// “pre-seed” the graph with some predefined nodes and/or edges before executing the DSL file.
    pub(super) fn execute_lazy_into<'tree>(
        &self,
        graph: &mut Graph<MyTSNode<'tree>>,
        tree: &'tree Tree,
        source: &'tree str,
        config: &ExecutionConfig<Graph<MyTSNode<'tree>>>,
        cancellation_flag: &dyn CancellationFlag,
    ) -> Result<(), ExecutionError> {
        let mut globals = Globals::nested(config.globals);
        self.check_globals(&mut globals)?;
        let config = ExecutionConfig {
            functions: config.functions,
            globals: &globals,
            lazy: config.lazy,
            location_attr: config.location_attr.clone(),
            variable_name_attr: config.variable_name_attr.clone(),
            match_node_attr: config.match_node_attr.clone(),
        };

        let mut ctx = Ctx::new();

        self.try_visit_matches_lazy(tree, source, |stanza, mat| {
            cancellation_flag.check("processing matches")?;
            stanza.execute_lazy(
                source,
                &mat,
                graph,
                &config,
                &mut ctx,
                &self.inherited_variables,
                &self.shorthands,
                cancellation_flag,
            )
        })?;
        ctx.eval(
            graph,
            config.functions,
            &self.inherited_variables,
            cancellation_flag,
        )
    }

    pub(super) fn try_visit_matches_lazy<'tree, E, F>(
        &self,
        tree: &'tree Tree,
        source: &'tree str,
        mut visit: F,
    ) -> Result<(), E>
    where
        F: FnMut(&ast::Stanza<Query>, MyQueryMatch<'_, 'tree>) -> Result<(), E>,
    {
        let mut cursor = QueryCursor::new();
        let query = self.query.as_ref().unwrap();
        let mut matches = cursor.matches(query, tree.root_node(), source.as_bytes());
        while let Some(mat) = matches.next() {
            let stanza = &self.stanzas[mat.pattern_index];
            let mat = MyQueryMatch {
                source,
                id: mat.id(),
                pattern_index: mat.pattern_index,
                captures: mat.captures,
            };
            visit(stanza, mat)?;
        }
        Ok(())
    }
}

impl<Q: GenQuery, I: Copy> ast::File<Q, I> {
    /// Executes this graph DSL file against a source file, saving the results into an existing
    /// `Graph` instance.  You must provide the parsed syntax tree (`tree`) as well as the source
    /// text that it was parsed from (`source`).  You also provide the set of functions and global
    /// variables that are available during execution. This variant is useful when you need to
    /// “pre-seed” the graph with some predefined nodes and/or edges before executing the DSL file.
    pub fn execute_lazy_into2<G>(
        &self,
        graph: &mut G,
        tree: <Q as NodeLending<'_>>::SNode,
        config: &ExecutionConfig<G>,
        cancellation_flag: &dyn CancellationFlag,
    ) -> Result<(), ExecutionError>
    where
        Q: GenQuery<I = I>,
        G: WithSynNodes,
        for<'t, 'u, 'v, 'w> <LendM<'v, 'w, Q> as NodesLending<'u>>::Nodes:
            NodeLending<'t, SNode = <G as NodeLending<'t>>::SNode>,
    {
        let mut cursor = Default::default();
        let query = self.query.as_ref().unwrap();
        let cursor: &mut Q::Cursor = &mut cursor;
        let matches = query.matches(cursor, &tree);
        self.execute_lazy_into2_aux(graph, matches, config, cancellation_flag)
    }
    pub fn execute_lazy_into2_aux<G>(
        &self,
        graph: &mut G,
        mut matches: <Q as MatchesLending<'_>>::Matches,
        config: &ExecutionConfig<G>,
        cancellation_flag: &dyn CancellationFlag,
    ) -> Result<(), ExecutionError>
    where
        Q: GenQuery<I = I>,
        G: WithSynNodes,
        for<'t, 'u, 'v, 'w> <LendM<'v, 'w, Q> as NodesLending<'u>>::Nodes:
            NodeLending<'t, SNode = <G as NodeLending<'t>>::SNode>,
    {
        let mut globals = Globals::nested(config.globals);
        self.check_globals(&mut globals)?;
        let config = ExecutionConfig {
            functions: config.functions,
            globals: &globals,
            lazy: config.lazy,
            location_attr: config.location_attr.clone(),
            variable_name_attr: config.variable_name_attr.clone(),
            match_node_attr: config.match_node_attr.clone(),
        };

        let mut ctx = Ctx::new();
        loop {
            let Some(mat) = MatchLender::next(&mut matches) else {
                break;
            };
            cancellation_flag.check("processing matches")?;
            let stanza = &self.stanzas[mat.pattern_index()];
            stanza.execute_lazy2(
                &mat,
                graph,
                &config,
                &mut ctx,
                &self.inherited_variables,
                &self.shorthands,
                cancellation_flag,
            )?;
        }
        ctx.eval(
            graph,
            config.functions,
            &self.inherited_variables,
            cancellation_flag,
        )
    }
}

/// Context for execution, which executes stanzas to build the lazy graph
pub struct ExecutionContext<
    'a,              // evaluation scope
    'c,              // Functions borrow scope
    'g,              // scope for context of globals
    'd,              // Globals borrow scope
    G: WithSynNodes, // invariant, execution is to build it
    QM: QMatch,      // covariant, we are only reading matched syntax nodes and their neighbors
    I = <QM as QueryWithLang>::I,
> {
    graph: &'a mut G,
    config: &'a ExecutionConfig<'c, 'g, 'd, G>,
    locals: &'a mut dyn MutVariables<LazyValue>,
    current_regex_captures: &'a Vec<String>,
    mat: &'a QM,
    full_match_file_capture_index: I,
    store: &'a mut LazyStore,
    scoped_store: &'a mut LazyScopedVariables,
    lazy_graph: &'a mut LazyGraph,
    function_parameters: &'a mut Vec<graph::Value>, // re-usable buffer to reduce memory allocations
    prev_element_debug_info: &'a mut HashMap<GraphElementKey, DebugInfo>,
    error_context: StatementContext,
    inherited_variables: &'a HashSet<Identifier>,
    shorthands: &'a ast::AttributeShorthands,
    cancellation_flag: &'a dyn CancellationFlag,
}

/// Context for evaluation, which evaluates the lazy graph to build the actual graph
struct EvaluationContext<'a, G> {
    pub graph: &'a mut G,
    pub functions: &'a Functions<G>,
    pub store: &'a LazyStore,
    pub scoped_store: &'a LazyScopedVariables,
    pub inherited_variables: &'a HashSet<Identifier>,
    pub function_parameters: &'a mut Vec<graph::Value>, // re-usable buffer to reduce memory allocations
    pub prev_element_debug_info: &'a mut HashMap<GraphElementKey, DebugInfo>,
    pub cancellation_flag: &'a dyn CancellationFlag,
}

impl<G: WithSynNodes> EvaluationContext<'_, G> {
    fn node(&self, r: graph::SyntaxNodeRef) -> Option<<G as NodeLending<'_>>::SNode> {
        self.graph.node(r)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub(super) enum GraphElementKey {
    NodeAttribute(graph::GraphNodeRef, Identifier),
    EdgeAttribute(graph::GraphNodeRef, graph::GraphNodeRef, Identifier),
}

impl ast::Stanza<Query> {
    fn execute_lazy<'tree>(
        &self,
        _source: &'tree str,
        mat: &MyQueryMatch<'_, 'tree>,
        graph: &mut Graph<MyTSNode<'tree>>,
        config: &ExecutionConfig<Graph<MyTSNode<'tree>>>,
        ctx: &mut Ctx<'_>,
        inherited_variables: &HashSet<Identifier>,
        shorthands: &ast::AttributeShorthands,
        cancellation_flag: &dyn CancellationFlag,
    ) -> Result<(), ExecutionError> {
        let current_regex_captures = vec![];
        ctx.locals.clear();
        let node = mat
            .nodes_for_capture_indexi(self.full_match_file_capture_index)
            .expect("missing capture for full match");
        debug!("match {:?} at {}", node, self.range.start);
        trace!("{{");
        for statement in &self.statements {
            let error_context = StatementContext::new(statement, self, &node);
            ctx.exec(
                graph,
                inherited_variables,
                cancellation_flag,
                self.full_match_file_capture_index,
                shorthands,
                mat,
                config,
                &current_regex_captures,
                statement,
                error_context,
            )?;
        }
        trace!("}}");
        Ok(())
    }
}

impl<Q, I: Copy> ast::Stanza<Q, I> {
    pub fn execute_lazy2<G, QM>(
        &self,
        mat: &QM,
        graph: &mut G,
        config: &ExecutionConfig<'_, '_, '_, G>,
        ctx: &mut Ctx<'_>,
        inherited_variables: &HashSet<Identifier>,
        shorthands: &ast::AttributeShorthands,
        cancellation_flag: &dyn CancellationFlag,
    ) -> Result<(), ExecutionError>
    where
        Q: GenQuery,
        QM: QMatch<I = I>,
        G: WithSynNodes,
        for<'t, 'u> <QM as NodesLending<'u>>::Nodes:
            NodeLending<'t, SNode = <G as NodeLending<'t>>::SNode>,
    {
        let current_regex_captures = vec![];
        ctx.locals.clear();
        let node = mat
            .nodes_for_capture_indexi(self.full_match_file_capture_index)
            .expect("missing capture for full match");
        trace!("{{");
        for statement in &self.statements {
            let error_context = StatementContext::new(statement, self, &node);
            ctx.exec(
                graph,
                inherited_variables,
                cancellation_flag,
                self.full_match_file_capture_index,
                shorthands,
                mat,
                config,
                &current_regex_captures,
                statement,
                error_context,
            )?;
        }
        trace!("}}");
        Ok(())
    }
}

pub fn execute_stmt_lazy<G: WithSynNodes, QM: QMatch>(
    stmt: &ast::Statement,
    exec: &mut ExecutionContext<G, QM>,
) -> Result<(), ExecutionError>
where
    for<'t, 'u> <QM as NodesLending<'u>>::Nodes:
        NodeLending<'t, SNode = <G as NodeLending<'t>>::SNode>,
{
    stmt.execute_lazy(exec)
}
impl ast::Statement {
    fn execute_lazy<G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        exec.cancellation_flag.check("executing statement")?;
        match self {
            Self::DeclareImmutable(statement) => statement.execute_lazy(exec),
            Self::DeclareMutable(statement) => statement.execute_lazy(exec),
            Self::Assign(statement) => statement.execute_lazy(exec),
            Self::CreateGraphNode(statement) => statement.execute_lazy(exec),
            Self::AddGraphNodeAttribute(statement) => statement.execute_lazy(exec),
            Self::CreateEdge(statement) => statement.execute_lazy(exec),
            Self::AddEdgeAttribute(statement) => statement.execute_lazy(exec),
            Self::Scan(statement) => statement.execute_lazy(exec),
            Self::Print(statement) => statement.execute_lazy(exec),
            Self::If(statement) => statement.execute_lazy(exec),
            Self::ForIn(statement) => statement.execute_lazy(exec),
        }
    }
}

impl ast::DeclareImmutable {
    fn execute_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let value = self.value.evaluate_lazy(exec)?;
        self.variable.add_lazy(exec, value, false)
    }
}

impl ast::DeclareMutable {
    fn execute_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let value = self.value.evaluate_lazy(exec)?;
        self.variable.add_lazy(exec, value, true)
    }
}

impl ast::Assign {
    fn execute_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let value = self.value.evaluate_lazy(exec)?;
        self.variable.set_lazy(exec, value)
    }
}

impl ast::CreateGraphNode {
    fn execute_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<(), ExecutionError>
    where
        // for<'t> G: graph::NodeLending<
        //     't,
        //     SNode = <<QM as graph::NodesLending<'t>>::Nodes as graph::NodeLending<'t>>::SNode,
        // >,
        for<'t, 'u> <QM as NodesLending<'u>>::Nodes:
            NodeLending<'t, SNode = <G as NodeLending<'t>>::SNode>,
        // for<'t, 'u> G: graph::NodeLending<'t, SNode = LendN<'t, 'u, QM>>,
        // for<'t> G: graph::NodeLending<'t, SNode = <QM as graph::NodeLending<'t>>::SNode>,
        // for<'t> QM: graph::NodeLending<'t, SNode = <G as graph::NodeLending<'t>>::SNode>,
        // G: WithSynNodes<SNode = QM::Simple>,
        // for<'t> <QM::Nodes as graph::NodeLending<'t>>::Node: Into<G::SNode>,
        // for<'t> <QM::Nodes as graph::NodeLending<'t>>::Node: SyntaxNode,
        // for<'t, 'u> G::SNode: From<LendN<'t, 'u, QM>>,
    {
        let graph_node = exec.graph.add_graph_node();
        self.node
            .add_debug_attrs(exec.graph[graph_node].attrs_mut(), exec.config)?;
        if let Some(match_node_attr) = &exec.config.match_node_attr {
            let node = exec
                .mat
                .nodes_for_capture_indexi(exec.full_match_file_capture_index)
                .expect("missing capture for full match");
            let syn_node = exec.graph.add_syntax_node(node);
            exec.graph[graph_node]
                .attrs_mut()
                .add(match_node_attr.clone(), syn_node)
                .map_err(|_| {
                    ExecutionError::DuplicateAttribute(format!(
                        " {} on graph node ({}) in {}",
                        match_node_attr, graph_node, self,
                    ))
                })?;
        }
        self.node.add_lazy(exec, graph_node.into(), false)
    }
}

impl ast::AddGraphNodeAttribute {
    fn execute_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let node = self.node.evaluate_lazy(exec)?;
        let mut attributes = Vec::new();
        let mut add_attribute = |a| attributes.push(a);
        for attribute in &self.attributes {
            attribute.execute_lazy(exec, &mut add_attribute)?;
        }
        let stmt =
            LazyAddGraphNodeAttribute::new(node, attributes, exec.error_context.clone().into());
        exec.lazy_graph.push(stmt.into());
        Ok(())
    }
}

impl ast::CreateEdge {
    fn execute_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let source = self.source.evaluate_lazy(exec)?;
        let sink = self.sink.evaluate_lazy(exec)?;
        let mut attributes = Attributes::new();
        self.add_debug_attrs(&mut attributes, exec.config)?;
        let stmt = LazyCreateEdge::new(source, sink, attributes, exec.error_context.clone().into());
        exec.lazy_graph.push(stmt.into());
        Ok(())
    }
}

impl ast::AddEdgeAttribute {
    fn execute_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let source = self.source.evaluate_lazy(exec)?;
        let sink = self.sink.evaluate_lazy(exec)?;
        let mut attributes = Vec::new();
        let mut add_attribute = |a| attributes.push(a);
        for attribute in &self.attributes {
            attribute.execute_lazy(exec, &mut add_attribute)?;
        }
        let stmt =
            LazyAddEdgeAttribute::new(source, sink, attributes, exec.error_context.clone().into());
        exec.lazy_graph.push(stmt.into());
        Ok(())
    }
}

impl ast::Scan {
    fn execute_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let match_string = self.value.evaluate_eager(exec)?.into_string()?;

        let mut i = 0;
        let mut matches = Vec::new();
        while i < match_string.len() {
            matches.clear();
            for (index, arm) in self.arms.iter().enumerate() {
                exec.cancellation_flag.check("processing scan matches")?;
                let captures = arm.regex.captures(&match_string[i..]);
                if let Some(captures) = captures {
                    if captures
                        .get(0)
                        .expect("missing regex capture")
                        .range()
                        .is_empty()
                    {
                        return Err(ExecutionError::EmptyRegexCapture(format!(
                            "for regular expression /{}/",
                            arm.regex
                        )));
                    }
                    matches.push((captures, index));
                }
            }

            if matches.is_empty() {
                return Ok(());
            }

            matches.sort_by_key(|(captures, index)| {
                let range = captures.get(0).expect("missing regex capture").range();
                (range.start, *index)
            });

            let (regex_captures, block_index) = &matches[0];
            let arm = &self.arms[*block_index];

            let mut current_regex_captures = Vec::new();
            for regex_capture in regex_captures.iter() {
                current_regex_captures
                    .push(regex_capture.map(|m| m.as_str()).unwrap_or("").to_string());
            }

            let mut arm_locals = VariableMap::nested(exec.locals);
            let mut arm_exec = ExecutionContext {
                graph: exec.graph,
                config: exec.config,
                current_regex_captures: &current_regex_captures,
                mat: exec.mat,
                full_match_file_capture_index: exec.full_match_file_capture_index,
                locals: &mut arm_locals,
                store: exec.store,
                scoped_store: exec.scoped_store,
                lazy_graph: exec.lazy_graph,
                function_parameters: exec.function_parameters,
                prev_element_debug_info: exec.prev_element_debug_info,
                error_context: exec.error_context.clone(),
                inherited_variables: exec.inherited_variables,
                shorthands: exec.shorthands,
                cancellation_flag: exec.cancellation_flag,
            };

            for statement in &arm.statements {
                arm_exec.error_context.statement = format!("{}", statement);
                arm_exec.error_context.statement_location = statement.location();
                statement
                    .execute_lazy(&mut arm_exec)
                    .with_context(|| {
                        format!("matching {} with arm \"{}\"", match_string, arm.regex,).into()
                    })
                    .with_context(|| arm_exec.error_context.clone().into())?;
            }

            i += regex_captures
                .get(0)
                .expect("missing regex capture")
                .range()
                .end;
        }

        Ok(())
    }
}

impl ast::Print {
    fn execute_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let mut arguments = Vec::new();
        for value in &self.values {
            let argument = if let ast::Expression::StringConstant(expr) = value {
                LazyPrintArgument::Text(expr.value.clone())
            } else {
                LazyPrintArgument::Value(value.evaluate_lazy(exec)?)
            };
            arguments.push(argument);
        }
        let stmt = LazyPrint::new(arguments, exec.error_context.clone().into());
        exec.lazy_graph.push(stmt.into());
        Ok(())
    }
}

impl ast::If {
    fn execute_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        for arm in &self.arms {
            let mut result = true;
            for condition in &arm.conditions {
                result &= condition.test_eager(exec)?;
            }
            if result {
                let mut arm_locals = VariableMap::nested(exec.locals);
                let mut arm_exec = ExecutionContext {
                    graph: exec.graph,
                    config: exec.config,
                    current_regex_captures: exec.current_regex_captures,
                    mat: exec.mat,
                    full_match_file_capture_index: exec.full_match_file_capture_index,
                    locals: &mut arm_locals,
                    store: exec.store,
                    scoped_store: exec.scoped_store,
                    lazy_graph: exec.lazy_graph,
                    function_parameters: exec.function_parameters,
                    prev_element_debug_info: exec.prev_element_debug_info,
                    error_context: exec.error_context.clone(),
                    inherited_variables: exec.inherited_variables,
                    shorthands: exec.shorthands,
                    cancellation_flag: exec.cancellation_flag,
                };
                for stmt in &arm.statements {
                    arm_exec.error_context.statement = format!("{}", stmt);
                    arm_exec.error_context.statement_location = stmt.location();
                    stmt.execute_lazy(&mut arm_exec)?;
                }
                break;
            }
        }
        Ok(())
    }
}

impl ast::Condition {
    // Eagerly evaluate the condition to a boolean. It assumes the argument expressions
    // are local (i.e., `is_local = true` in the checker).
    fn test_eager<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<bool, ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        match self {
            Self::Some { value, .. } => Ok(!value.evaluate_eager(exec)?.is_null()),
            Self::None { value, .. } => Ok(value.evaluate_eager(exec)?.is_null()),
            Self::Bool { value, .. } => Ok(value.evaluate_eager(exec)?.into_boolean()?),
        }
    }
}

impl ast::ForIn {
    fn execute_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let values = self.value.evaluate_eager(exec)?.into_list()?;
        let mut loop_locals = VariableMap::nested(exec.locals);
        for value in values {
            loop_locals.clear();
            let mut loop_exec = ExecutionContext {
                graph: exec.graph,
                config: exec.config,
                current_regex_captures: exec.current_regex_captures,
                mat: exec.mat,
                full_match_file_capture_index: exec.full_match_file_capture_index,
                locals: &mut loop_locals,
                store: exec.store,
                scoped_store: exec.scoped_store,
                lazy_graph: exec.lazy_graph,
                function_parameters: exec.function_parameters,
                prev_element_debug_info: exec.prev_element_debug_info,
                error_context: exec.error_context.clone(),
                inherited_variables: exec.inherited_variables,
                shorthands: exec.shorthands,
                cancellation_flag: exec.cancellation_flag,
            };
            self.variable
                .add_lazy(&mut loop_exec, value.into(), false)?;
            for stmt in &self.statements {
                loop_exec.error_context.statement = format!("{}", stmt);
                loop_exec.error_context.statement_location = stmt.location();
                stmt.execute_lazy(&mut loop_exec)?;
            }
        }
        Ok(())
    }
}

impl ast::Expression {
    fn evaluate_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        match self {
            Self::FalseLiteral => Ok(false.into()),
            Self::NullLiteral => Ok(graph::Value::Null.into()),
            Self::TrueLiteral => Ok(true.into()),
            Self::IntegerConstant(expr) => expr.evaluate_lazy(exec),
            Self::StringConstant(expr) => expr.evaluate_lazy(exec),
            Self::ListLiteral(expr) => expr.evaluate_lazy(exec),
            Self::SetLiteral(expr) => expr.evaluate_lazy(exec),
            Self::ListComprehension(expr) => expr.evaluate_lazy(exec),
            Self::SetComprehension(expr) => expr.evaluate_lazy(exec),
            Self::Capture(expr) => expr.evaluate_lazy(exec),
            Self::Variable(expr) => expr.evaluate_lazy(exec),
            Self::Call(expr) => expr.evaluate_lazy(exec),
            Self::RegexCapture(expr) => expr.evaluate_lazy(exec),
        }
    }

    // Eagerly evaluate the expression to a `Value`, instead of a `LazyValue`. This method should
    // only be called on expressions that are local (i.e., `is_local = true` in the checker).
    fn evaluate_eager<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<graph::Value, ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        self.evaluate_lazy(exec)?.evaluate(&mut EvaluationContext {
            graph: exec.graph,
            functions: exec.config.functions,
            store: exec.store,
            scoped_store: exec.scoped_store,
            inherited_variables: exec.inherited_variables,
            function_parameters: exec.function_parameters,
            prev_element_debug_info: exec.prev_element_debug_info,
            cancellation_flag: exec.cancellation_flag,
        })
    }
}

impl ast::IntegerConstant {
    fn evaluate_lazy<G: WithSynNodes, QM: QMatch>(
        &self,
        _exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError> {
        Ok(self.value.into())
    }
}

impl ast::StringConstant {
    fn evaluate_lazy<G: WithSynNodes, QM: QMatch>(
        &self,
        _exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError> {
        Ok(self.value.clone().into())
    }
}

impl ast::ListLiteral {
    fn evaluate_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let mut elements = Vec::new();
        for element in &self.elements {
            elements.push(element.evaluate_lazy(exec)?);
        }
        Ok(elements.into())
    }
}

impl ast::ListComprehension {
    fn evaluate_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let values = self.value.evaluate_eager(exec)?.into_list()?;
        let mut elements = Vec::new();
        let mut loop_locals = VariableMap::nested(exec.locals);
        for value in values {
            loop_locals.clear();
            let mut loop_exec = ExecutionContext {
                graph: exec.graph,
                config: exec.config,
                current_regex_captures: exec.current_regex_captures,
                mat: exec.mat,
                full_match_file_capture_index: exec.full_match_file_capture_index,
                locals: &mut loop_locals,
                store: exec.store,
                scoped_store: exec.scoped_store,
                lazy_graph: exec.lazy_graph,
                function_parameters: exec.function_parameters,
                prev_element_debug_info: exec.prev_element_debug_info,
                error_context: exec.error_context.clone(),
                inherited_variables: exec.inherited_variables,
                shorthands: exec.shorthands,
                cancellation_flag: exec.cancellation_flag,
            };
            self.variable
                .add_lazy(&mut loop_exec, value.into(), false)?;
            let element = self.element.evaluate_lazy(&mut loop_exec)?;
            elements.push(element);
        }
        Ok(elements.into())
    }
}

impl ast::SetLiteral {
    fn evaluate_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let mut elements = Vec::new();
        for element in &self.elements {
            elements.push(element.evaluate_lazy(exec)?);
        }
        Ok(LazySet::new(elements).into())
    }
}

impl ast::SetComprehension {
    fn evaluate_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let values = self.value.evaluate_eager(exec)?.into_list()?;
        let mut elements = Vec::new();
        let mut loop_locals = VariableMap::nested(exec.locals);
        for value in values {
            loop_locals.clear();
            let mut loop_exec = ExecutionContext {
                graph: exec.graph,
                config: exec.config,
                current_regex_captures: exec.current_regex_captures,
                mat: exec.mat,
                full_match_file_capture_index: exec.full_match_file_capture_index,
                locals: &mut loop_locals,
                store: exec.store,
                scoped_store: exec.scoped_store,
                lazy_graph: exec.lazy_graph,
                function_parameters: exec.function_parameters,
                prev_element_debug_info: exec.prev_element_debug_info,
                error_context: exec.error_context.clone(),
                inherited_variables: exec.inherited_variables,
                shorthands: exec.shorthands,
                cancellation_flag: exec.cancellation_flag,
            };
            self.variable
                .add_lazy(&mut loop_exec, value.into(), false)?;
            let element = self.element.evaluate_lazy(&mut loop_exec)?;
            elements.push(element);
        }
        Ok(LazySet::new(elements).into())
    }
}

// type LendNN<'t, 'u, 'v, 'w, Q: GenQuery> = LendN<'t, 'u, LendM<'v, 'w, Q>>;

#[allow(type_alias_bounds)]
type LendM<'v, 'w, T: MatchesLending<'v>> = <T::Matches as MatchLending<'w>>::Match;

// type LendN<'t, 'u, QM: QMatch> = LendS<'t, <QM as NodesLending<'u>>::Nodes>;
// <<QM as graph::NodesLending<'u>>::Nodes as graph::NodeLending<'t>>::SNode;

type LendNS<'u, QM> = <QM as NodesLending<'u>>::Nodes;

type LendS<'t, T> = <T as NodeLending<'t>>::SNode;

impl ast::Capture {
    fn evaluate_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError>
    where
        // for<'t, 'u, 'v, 'w> <G as graph::NodeLending<'t>>::SNode: From<LendNN<'t, 'u, 'v, 'w, QM>>,
        // for<'t, 'u> <G as graph::NodeLending<'t>>::SNode: From<LendNN<'t, 'u, QM>>,
        // for<'t, 'u> <G as graph::NodeLending<'t>>::SNode: From<LendN<'t, 'u, QM>>,
        for<'t, 'u> <QM as NodesLending<'u>>::Nodes:
            NodeLending<'t, SNode = <G as NodeLending<'t>>::SNode>,
    {
        let mat = &exec.mat;
        let nodes = mat.nodes_for_capture_index((self.file_capture_index as u32).into());
        Ok(Value::from_nodes(exec.graph, nodes, self.quantifier).into())
    }
}

impl ast::Call {
    fn evaluate_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let mut parameters = Vec::new();
        for parameter in &self.parameters {
            parameters.push(parameter.evaluate_lazy(exec)?);
        }
        Ok(LazyCall::new(self.function.clone(), parameters).into())
    }
}

impl ast::RegexCapture {
    fn evaluate_lazy<G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError> {
        let value = exec.current_regex_captures[self.match_index].clone();
        Ok(value.into())
    }
}

impl ast::Variable {
    fn evaluate_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        match self {
            Self::Scoped(variable) => variable.evaluate_lazy(exec),
            Self::Unscoped(variable) => variable.evaluate_lazy(exec),
        }
    }
}

impl ast::Variable {
    fn add_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
        value: LazyValue,
        mutable: bool,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        match self {
            Self::Scoped(variable) => variable.add_lazy(exec, value, mutable),
            Self::Unscoped(variable) => variable.add_lazy(exec, value, mutable),
        }
    }

    fn set_lazy<G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
        value: LazyValue,
    ) -> Result<(), ExecutionError> {
        match self {
            Self::Scoped(variable) => variable.set_lazy(exec, value),
            Self::Unscoped(variable) => variable.set_lazy(exec, value),
        }
    }
}

impl ast::ScopedVariable {
    fn evaluate_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let scope = self.scope.evaluate_lazy(exec)?;
        let value = LazyScopedVariable::new(scope, self.name.clone());
        Ok(value.into())
    }

    fn add_lazy<'a, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
        value: LazyValue,
        mutable: bool,
    ) -> Result<(), ExecutionError>
    where
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        if mutable {
            return Err(ExecutionError::CannotDefineMutableScopedVariable(format!(
                "{}",
                self
            )));
        }
        let scope = self.scope.evaluate_lazy(exec)?;
        let variable = exec.store.add(value, exec.error_context.clone().into());
        exec.scoped_store.add(
            scope,
            self.name.clone(),
            variable.into(),
            exec.error_context.clone().into(),
        )
    }

    fn set_lazy<G: WithSynNodes, QM: QMatch>(
        &self,
        _exec: &mut ExecutionContext<G, QM>,
        _value: LazyValue,
    ) -> Result<(), ExecutionError> {
        Err(ExecutionError::CannotAssignScopedVariable(format!(
            "{}",
            self
        )))
    }
}

impl ast::UnscopedVariable {
    fn evaluate_lazy<G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
    ) -> Result<LazyValue, ExecutionError> {
        if let Some(value) = exec.config.globals.get(&self.name) {
            Some(value.clone().into())
        } else {
            exec.locals.get(&self.name).cloned()
        }
        .ok_or_else(|| ExecutionError::UndefinedVariable(format!("{}", self)))
    }
}

impl ast::UnscopedVariable {
    fn add_lazy<G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
        value: LazyValue,
        mutable: bool,
    ) -> Result<(), ExecutionError> {
        if exec.config.globals.get(&self.name).is_some() {
            return Err(ExecutionError::DuplicateVariable(format!(
                " global {}",
                self
            )));
        }
        let value = exec.store.add(value, exec.error_context.clone().into());
        exec.locals
            .add(self.name.clone(), value.into(), mutable)
            .map_err(|_| ExecutionError::DuplicateVariable(format!(" local {}", self)))
    }

    fn set_lazy<G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
        value: LazyValue,
    ) -> Result<(), ExecutionError> {
        if exec.config.globals.get(&self.name).is_some() {
            return Err(ExecutionError::CannotAssignImmutableVariable(format!(
                " global {}",
                self
            )));
        }
        let value = exec.store.add(value, exec.error_context.clone().into());
        exec.locals
            .set(self.name.clone(), value.into())
            .map_err(|_| {
                if exec.locals.get(&self.name).is_some() {
                    ExecutionError::CannotAssignImmutableVariable(format!("{}", self))
                } else {
                    ExecutionError::UndefinedVariable(format!("{}", self))
                }
            })
    }
}

impl ast::Attribute {
    fn execute_lazy<'a, F, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
        add_attribute: &mut F,
    ) -> Result<(), ExecutionError>
    where
        F: FnMut(LazyAttribute),
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        exec.cancellation_flag.check("executing attribute")?;
        let value = self.value.evaluate_lazy(exec)?;
        if let Some(shorthand) = exec.shorthands.get(&self.name) {
            shorthand.execute_lazy(exec, add_attribute, value)
        } else {
            add_attribute(LazyAttribute::new(self.name.clone(), value));
            Ok(())
        }
    }
}

impl ast::AttributeShorthand {
    fn execute_lazy<'a, F, G: WithSynNodes, QM: QMatch>(
        &self,
        exec: &mut ExecutionContext<G, QM>,
        add_attribute: &mut F,
        value: LazyValue,
    ) -> Result<(), ExecutionError>
    where
        F: FnMut(LazyAttribute),
        for<'t, 'u> LendNS<'u, QM>: graph::NodeLending<'t, SNode = LendS<'t, G>>,
    {
        let mut shorthand_locals = VariableMap::new();
        let mut shorthand_exec = ExecutionContext {
            graph: exec.graph,
            config: exec.config,
            locals: &mut shorthand_locals,
            current_regex_captures: exec.current_regex_captures,
            mat: exec.mat,
            full_match_file_capture_index: exec.full_match_file_capture_index,
            store: exec.store,
            scoped_store: exec.scoped_store,
            lazy_graph: exec.lazy_graph,
            function_parameters: exec.function_parameters,
            prev_element_debug_info: exec.prev_element_debug_info,
            error_context: exec.error_context.clone(),
            inherited_variables: exec.inherited_variables,
            shorthands: exec.shorthands,
            cancellation_flag: exec.cancellation_flag,
        };
        self.variable.add_lazy(&mut shorthand_exec, value, false)?;
        for attr in &self.attributes {
            attr.execute_lazy(&mut shorthand_exec, add_attribute)?;
        }
        Ok(())
    }
}
