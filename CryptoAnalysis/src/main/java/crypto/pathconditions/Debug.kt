package crypto.pathconditions.debug

import boomerang.jimple.*
import crypto.pathconditions.refinement.refineStatementToString
import soot.*
import soot.Unit
import soot.jimple.*
import soot.jimple.internal.JimpleLocal
import java.io.*

//
// Functions to nicely format Soot objects for debug output
//

fun SootMethod.prettyPrint(): String {
    val sw = StringWriter()
    val pw = PrintWriter(sw)
    Printer.v().printTo(activeBody, pw)
    return sw.buffer.toString()
        .lineSequence()
        .filter(String::isNotEmpty)
        .joinToString(System.lineSeparator())
}

fun SootClass.prettyPrint(): String {
    val sw = StringWriter()
    val pw = PrintWriter(sw)
    Printer.v().printTo(this, pw)
    return sw.buffer.toString()
        .lineSequence()
        .filter(String::isNotEmpty)
        .joinToString(System.lineSeparator())
}

fun Type.prettyPrint(): String =
    if (this is RefType && hasSootClass()) sootClass.shortName else toString()

fun Value.prettyPrint(replacements: Map<JimpleLocal, Value> = emptyMap()): String = when (this) {
    in replacements -> replacements[this]!!.prettyPrint(replacements)
    is StaticInvokeExpr ->
        "${method.declaringClass.shortName}.${method.name}(${args.joinToString { it.prettyPrint(replacements) }})"
    is InstanceInvokeExpr ->
        "${base.prettyPrint(replacements)}.${method.name}(${args.joinToString { it.prettyPrint(replacements) }})"
    is InstanceFieldRef -> "${base.prettyPrint(replacements)}.${field.name}"
    is StaticFieldRef -> "${field.declaringClass.shortName}.${field.name}"
    is NewExpr -> "new ${type.prettyPrint()}"
    is CastExpr -> "(${castType.prettyPrint()}) ${op.prettyPrint(replacements)}"
    is BinopExpr -> {
        val default = "${op1.prettyPrint(replacements)} ${symbol.trim()} ${op2.prettyPrint(replacements)}"
        if (op1.type === BooleanType.v() && op2 is IntConstant) {
            when (symbol.trim() to (op2 as IntConstant).value) {
                "==" to 0 -> "!" + op1.prettyPrint(replacements)
                "==" to 1 -> op1.prettyPrint(replacements)
                "!=" to 0 -> op1.prettyPrint(replacements)
                "!=" to 1 -> "!" + op1.prettyPrint(replacements)
                else -> default
            }
        }
        else default
    }
    else -> toString()
}

fun Unit.prettyPrint(replacements: Map<JimpleLocal, Value> = emptyMap()): String = when (this) {
    is AssignStmt -> "${leftOp.prettyPrint(replacements)} = ${rightOp.prettyPrint(replacements)}"
    is InvokeStmt -> invokeExpr.prettyPrint(replacements)
    is IfStmt -> "if (${condition.prettyPrint(replacements)})"
    is GotoStmt -> "goto `${if (target == this) "<self>" else target.prettyPrint(replacements)}`"
    else -> toString()
}

fun Val.prettyPrint(replacements: Map<JimpleLocal, Value> = emptyMap()) =
    value().prettyPrint(replacements) + " (${m().name})"

fun Statement.prettyPrint(replacements: Map<JimpleLocal, Value> = emptyMap()) = when {
    method == null && unit.isPresent -> unit.get().prettyPrint(replacements)
    method != null && unit.isPresent -> "${method.declaringClass.name}.${method.name} { " + unit.get().prettyPrint(replacements) + " }"
    else -> ""
}

fun Statement.prettyPrintRefined() = when {
    method == null || !unit.isPresent -> ""
    else -> "${method.declaringClass.name}.${method.name} { " + refineStatementToString(unit.get(), method) + "; } ↻"
}