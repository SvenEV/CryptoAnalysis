package crypto.analysis

import java.io.PrintStream

@JvmField
val Markdown = MarkdownWriter("")
private val originalOutStream = System.out
private val originalErrStream = System.err

class MarkdownWriter(val prefix: String) {

    data class MarkdownContainer(val Markdown: MarkdownWriter)

    /** Gets a [MarkdownWriter] that indents text 1 level deeper */
    val tab @JvmName("tab") get() = MarkdownWriter("$prefix    ")

    /** Gets a [MarkdownWriter] that puts text into a blockquote */
    val quote @JvmName("quote") get() = MarkdownWriter("$prefix>   ")

    /** Indents all markdown output produced in the body lambda by 1 level */
    fun tab(body: MarkdownContainer.() -> Unit) = MarkdownContainer(tab).apply(body)

    /** Puts all markdown output produced in the body lambda into a blockquote */
    fun quote(body: MarkdownContainer.() -> Unit) = MarkdownContainer(quote).apply(body)

    private fun writeLine(s: String = "") = originalOutStream.println(prefix + s)

    fun h1(text: String) { writeLine(); writeLine("# $text"); writeLine() }
    fun h2(text: String) = writeLine("## $text")
    fun h3(text: String) = writeLine("### $text")
    fun h4(text: String) = writeLine("#### $text")
    fun h5(text: String) = writeLine("##### $text")
    fun h6(text: String) = writeLine("###### $text")

    fun ulItem(text: String) = writeLine("* $text")
    fun olItem(text: String) = writeLine("1. $text")

    fun <T> ul(seq: Sequence<T>) = seq.forEach { ulItem(it.toString()) }
    fun <T> ul(seq: Iterable<T>) = seq.forEach { ulItem(it.toString()) }
    fun <T> ol(seq: Sequence<T>) = seq.forEach { olItem(it.toString()) }
    fun <T> ol(seq: Iterable<T>) = seq.forEach { olItem(it.toString()) }

    fun codeBlock(code: String) {
        writeLine("```")
        code.lineSequence().forEach { writeLine(it) }
        writeLine("```")
    }

    fun hyperlink(text: String, uri: String) = writeLine("[$text]($uri)")
    fun hyperlink(text: String, title: String, uri: String) = writeLine("[$text]($uri \"$title\")")
    fun image(uri: String, altText: String = "") = writeLine("![$altText]($uri \"$altText\")")
    fun horizontalLine() = writeLine("\n---\n")

    private class MarkdownPrintStream(val prefix: String, out: PrintStream) : PrintStream(out) {
        fun prefixLines(s: String): String {
            val lines = s.lines()
            return lines
                .mapIndexed { i, line -> if (line.isEmpty() && i == lines.count() - 1) line else "$prefix$line  " }
                .joinToString(System.lineSeparator())
        }

        override fun print(s: String) = super.print(prefixLines(s))
        override fun println(s: String) = print("$s  \n")
        override fun println() = println("")
    }

    fun redirectSystemOut() = System.setOut(MarkdownPrintStream(prefix, originalOutStream))
    fun redirectSystemErr() = System.setErr(MarkdownPrintStream(prefix, originalErrStream))
}