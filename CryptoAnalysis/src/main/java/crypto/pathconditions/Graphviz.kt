package crypto.pathconditions.graphviz

import crypto.pathconditions.debug.prettyPrint
import soot.*
import soot.Unit
import soot.jimple.*
import soot.jimple.internal.*
import soot.jimple.toolkits.ide.icfg.AbstractJimpleBasedICFG

//
// Provides a convenient API for creating directed graphs, styling nodes and edges, and rendering
// graphs to the Graphviz DOT format.
//

data class Node<N>(val id: N, val attributes: Map<String, String> = emptyMap())
data class Edge<N, E>(val id: E, val start: N, val end: N, val attributes: Map<String, String> = emptyMap())

class NodeConfiguration {
    val attrs = mutableMapOf<String, String>()
    fun label(s: String) = attrs.put("label", s)
    fun color(s: String) = attrs.put("color", s)
    fun filled() = attrs.put("style", "filled")
    fun fillColor(color: String) {
        attrs["style"] = "filled"
        attrs["fillcolor"] = color
    }

    fun invisible() = attrs.put("style", "invis")
    fun attr(key: String, value: String) = attrs.put(key, value)
}

class EdgeConfiguration {
    val attrs = mutableMapOf<String, String>()
    fun label(s: String) = attrs.put("label", s)
    fun color(s: String) = attrs.put("color", s)
    fun invisible() = attrs.put("style", "invis")
    fun dashed() = attrs.put("style", "dashed")
    fun dotted() = attrs.put("style", "dotted")
    fun bold() = attrs.put("style", "bold")
    fun attr(key: String, value: String) = attrs.put(key, value)
}

fun <N> DirectedGraph<N, Pair<N, N>>.addEdge(id: Pair<N, N>, attributes: Map<String, String> = emptyMap()) =
    addEdge(id, id.first, id.second, attributes)

typealias DirectedUnlabeledGraph<N> = DirectedGraph<N, Pair<N, N>>

/**
 * An immutable data structure for directed graphs with edge labels.
 * Nodes and edges may have String attributes that are used when rendering to Graphviz.
 */
class DirectedGraph<N, E>(
    private val _nodes: Map<N, Node<N>>,
    private val _edges: Map<E, Edge<N, E>>
) {

    companion object {
        fun <N, E> empty() = DirectedGraph<N, E>(emptyMap(), emptyMap())
        fun <N> emptyUnlabeled() = DirectedUnlabeledGraph<N>(emptyMap(), emptyMap())

        private fun <N> Map<N, Node<N>>.ensureNodeExists(id: N) = when {
            containsKey(id) -> this
            else -> this + (id to Node(id, emptyMap()))
        }
    }

    fun addEdge(id: E, start: N, end: N, attributes: Map<String, String> = emptyMap()): DirectedGraph<N, E> {
        val newNodes = _nodes
            .ensureNodeExists(start)
            .ensureNodeExists(end)
        return DirectedGraph(newNodes, _edges + Pair(id, Edge(id, start, end, attributes)))
    }

    fun removeNode(id: N): DirectedGraph<N, E> {
        val newEdges = _edges.filterValues { it.start != id && it.end != id }
        return DirectedGraph(_nodes - id, newEdges)
    }

    fun removeEdge(id: E) =
        if (_edges.containsKey(id))
            DirectedGraph(_nodes, _edges - id)
        else
            this

    val nodes get() = _nodes.values
    val edges get() = _edges.values

    fun node(id: N) = _nodes[id]
    fun edge(id: E) = _edges[id]

    fun nodeAttribute(id: N, key: String) = _nodes[id]?.attributes?.get(key)
    fun edgeAttribute(id: E, key: String) = _edges[id]?.attributes?.get(key)

    /**
     * Applies attributes to a node (new attributes are merged with existing ones, if any).
     */
    fun configureNode(id: N, f: NodeConfiguration.() -> kotlin.Unit): DirectedGraph<N, E> {
        val node = _nodes[id]
        val config = NodeConfiguration()
        f(config)
        val newNode = node?.copy(attributes = node.attributes + config.attrs) ?: Node(id, config.attrs.toMap())
        return DirectedGraph(_nodes + (id to newNode), _edges)
    }

    /**
     * Applies attributes to an edge (new attributes are merged with existing ones, if any).
     */
    fun configureEdge(id: E, f: EdgeConfiguration.() -> kotlin.Unit): DirectedGraph<N, E> {
        val edge = _edges[id]
        if (edge != null) {
            val config = EdgeConfiguration()
            f(config)
            val newEdge = edge.copy(attributes = edge.attributes + config.attrs)
            return DirectedGraph(_nodes, _edges + (id to newEdge))
        }
        return this
    }

    /**
     * Merges multiple, parallel edges to a single edge.
     * The "label" attributes of parallel edges are merged, all other attributes are lost.
     */
    fun eliminateMultiEdges(): DirectedGraph<N, Pair<N, N>> {
        val edges = _edges.asSequence()
            .groupBy { (_, edge) -> edge.start to edge.end }
            .mapValues { (key, edges) ->
                val mergedLabel = edges
                    .mapNotNull { it.value.attributes["label"] }
                    .joinToString("\\n")
                Edge(key, key.first, key.second, mapOf("label" to mergedLabel))
            }

        return DirectedGraph(_nodes, edges)
    }

    /**
     * Renders the graph to a Graphviz DOT digraph.
     */
    fun toDotString(useHtmlLabels: Boolean = false): String {
        val sb = StringBuilder()
        sb.appendln("digraph {")

        val nodesIndexed = nodes
            .mapIndexed { index, node -> Pair(index, node.id) }
            .associateBy({ it.second }, { it.first })

        fun ensureHasLabel(label: String, attributes: Map<String, String>) =
            if (attributes.containsKey("label"))
                attributes
            else
                attributes + Pair("label", label)

        fun String.escapeQuotesAndNewline() =
            replace("\"", "\\\"").replace("\n", "\\n")

        fun attributesToString(attributes: Map<String, String>) = attributes
            .map { (key, value) ->
                when {
                    key == "label" && useHtmlLabels -> "$key = <$value>"
                    else -> "$key = \"${value.escapeQuotesAndNewline()}\""
                }
            }
            .joinToString()

        nodesIndexed.forEach { node, i ->
            val attrs = attributesToString(ensureHasLabel(node.toString(), node(node)!!.attributes))
            sb.appendln("    n$i [$attrs]")
        }

        edges.forEach {
            val i1 = nodesIndexed[it.start]
            val i2 = nodesIndexed[it.end]
            val attrs = attributesToString(it.attributes)
            sb.appendln("    n$i1 -> n$i2 [$attrs]")
        }

        sb.append("}")
        return sb.toString()
    }
}

// TODO: Support inlining of new-expressions, e.g.
// $r0 = new File
// $r0.<init>()
// println($r0)
private fun AbstractJimpleBasedICFG.getReconstructedSuccsOf(
    stmt: Unit,
    inlinedLocals: MutableMap<JimpleLocal, Value>
): Sequence<Unit> =
    getSuccsOf(stmt).asSequence().flatMap {
        if (it is NopStmt || it is JIdentityStmt) {
            // Nops and "foo := @parameter0 ..." are skipped
            return@flatMap getReconstructedSuccsOf(it, inlinedLocals)
        } else if (it is AssignStmt) {
            val target = it.leftOp
            if (target is JimpleLocal) {
                val isTempLocal = target.name.startsWith("$") || target.name.startsWith("varReplacer")
                if (isTempLocal && it.rightOp !is NewExpr) {
                    // Temporary locals (e.g. $z0, varReplacer123) are inlined unless there's a new-expression
                    // on the right-hand side (inlining "new Foo" after the constructor call statement would look weird)
                    inlinedLocals[target] = it.rightOp
                    return@flatMap getReconstructedSuccsOf(it, inlinedLocals)
                }
            }
        }
        sequenceOf(it)
    }

/**
 * Renders the control flow of a method as a graph in Graphviz DOT format.
 */
fun AbstractJimpleBasedICFG.toDotString(method: SootMethod, reconstructJava: Boolean = false): String {
    val inlinedLocals = mutableMapOf<JimpleLocal, Value>()

    fun resolveGoto(u: Unit): Sequence<Unit> = when (u) {
        is GotoStmt -> getSuccsOf(u.target).asSequence().flatMap(::resolveGoto)
        else -> sequenceOf(u)
    }

    fun getSuccsSkippingGotos(u: Unit): Sequence<Unit> =
        getSuccsOf(u).asSequence().flatMap(::resolveGoto)

    fun buildGraph(stmt: Unit, graph: DirectedUnlabeledGraph<Unit>): DirectedUnlabeledGraph<Unit> {
        val succs = if (reconstructJava) getReconstructedSuccsOf(stmt, inlinedLocals) else getSuccsSkippingGotos(stmt).asSequence()
        val newGraph = succs.fold(graph) { g, succ -> buildGraph(succ, g).addEdge(stmt to succ) }

        return when (stmt) {
            is IfStmt -> {
                val trueTargets = resolveGoto(stmt.target)
                val falseTargets = (succs - trueTargets).flatMap(::resolveGoto)
                falseTargets
                    .fold(newGraph) { g, succ ->
                        g.configureEdge(stmt to succ) { dashed() }
                    }
                    .configureNode(stmt) {
                        label(stmt.prettyPrint(inlinedLocals))
                        color("blue")
                    }
            }
            else -> newGraph.configureNode(stmt) {
                label(stmt.prettyPrint(inlinedLocals))
            }
        }
    }

    val graph = getStartPointsOf(method).fold(DirectedGraph.emptyUnlabeled<Unit>()) { g, stmt -> buildGraph(stmt, g) }
    return graph.toDotString()
}
