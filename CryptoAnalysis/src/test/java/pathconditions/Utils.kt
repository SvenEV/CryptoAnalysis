package pathconditions

import crypto.pathconditions.ofType
import soot.G
import soot.Scene
import soot.SootClass
import soot.Unit
import soot.options.Options
import soot.tagkit.LineNumberTag
import java.io.File

fun getSootClassPath(): String {
    val classPaths = arrayOf(
        System.getProperty("user.dir") + File.separator + "target" + File.separator + "classes",
        System.getProperty("user.dir") + File.separator + "target" + File.separator + "test-classes"
    )
    return classPaths
        .filter { File(it).exists() }
        .joinToString(";")
//        ?: throw RuntimeException("Classpath could not be found")
}

fun setupSoot(mainClass: String? = null) {
    G.v()
    G.reset()

    Options.v().apply {
        set_whole_program(true)
        set_keep_line_number(true)
        setPhaseOption("cg.spark", "on")
        set_output_format(Options.output_format_none)
        set_no_bodies_for_excluded(true)
        set_allow_phantom_refs(true)
        set_include(
            listOf(
                "java.lang.*",
                "java.util.*",
                "java.io.*",
                "sun.misc.*",
                "java.net.*",
                "javax.servlet.*",
                "javax.crypto.*"
            )
        )
        setPhaseOption("jb", "use-original-names:true")
        set_soot_classpath(getSootClassPath())
        set_prepend_classpath(true)
        // set_main_class(this.getTargetClass())
    }

    Scene.v().loadNecessaryClasses()

    if (mainClass != null) {
        val klass = Scene.v().forceResolve(mainClass, SootClass.BODIES)
        klass.setApplicationClass()
    }
}

fun Unit.lineNumber() =
    tags.ofType<LineNumberTag>().firstOrNull()?.lineNumber ?: -1

fun nop() {}

abstract class SootBasedTest {
    val thisClass: SootClass
        get() {
            val klass = Scene.v().forceResolve(javaClass.name, SootClass.BODIES)
            klass.setApplicationClass()
            return klass
        }

    companion object {
        init {
            setupSoot()
        }
    }
}