import cmu.isr.api.calculateDelta
import cmu.isr.ts.DetLTS
import cmu.isr.ts.lts.CompactDetLTS
import cmu.isr.ts.lts.CompactLTS
import cmu.isr.ts.lts.ltsa.FSPWriter
import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import tlc2.TLC
import java.io.File
import kotlin.system.exitProcess

/**
 * # TlaRobustness
 *
 * Given a decomposed system in tla model form,
 * We calculate the behavioral robustness of the system using the behavioral method
 * described in *https://github.com/cmu-soda/transitional-robustness*
 *
 * Procedure:
 * 1. Convert system .tla file into fsp: this is the base system
 * 2. Convert system .tla file with invariant into fsp: this is the error property.
 * 3. Convert environment .tla and .cfg file into fsp: this is the environment
 * 4. Call lts-robustness with this converted data and report the output.
 *
 * @author Will Morris
 */
class TlaRobustness : CliktCommand(help="Generate the robustness for a software system in tla model form") {


    // ***** ARGUMENTS ***** //

    private val sysPath
        by argument(name="[system model path]", help="tla+ model of the system")
    private val sysConfig
        by argument(name="[system config path]", help="tla+ configuration file for the system")
    private val envPath
        by argument(name="[env path]", help="tla+ model of the environment")
    private val envConfig
        by argument(name="[env config path]", help = "tla+ configuration file for environment")


    // ***** MAIN ***** //

    override fun run() {
        // Base system includes no safety properties.
        // Hence, a config w/o invariants is needed.
        val noInvsPath = "no-invs.cfg"
        if (!File(noInvsPath).exists()) {
            File(noInvsPath).writer().write("SPECIFICATION spec")
        }

        // Prepare LTS for base system without safety property.
        val sysTLC = TLC()
        sysTLC.modelCheck(sysPath, noInvsPath)
        val sysLTS = sysTLC.ltsBuilder.toIncompleteDetAutWithoutAnErrorState()

        // Prepare LTS for system safety property.
        // This includes error states.
        val sysPropTLC = TLC()
        sysPropTLC.modelCheck(sysPath, sysConfig)
        // Unlike others, sys property must be a deterministic LTS
        val sysPropLTS = toDeterministic(sysPropTLC.ltsBuilder.toIncompleteDetAutIncludingAnErrorState() as CompactLTS)

        // Prepare LTS for env w/ envp
        val envTLC = TLC()
        envTLC.modelCheck(envPath, envConfig)
        val envLTS = envTLC.ltsBuilder.toIncompleteDetAutIncludingAnErrorState()

        println(calculateDelta(envLTS, sysLTS, sysPropLTS))
        // By TLC convention, explicitly exit process when finished.
        exitProcess(0)
    }
}

fun main(args: Array<String>) = TlaRobustness().main(args)
