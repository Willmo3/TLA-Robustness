import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import tlc2.TLC

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
        println("Tla Robustness")
        println("System: $sysPath")
        println("System config: $sysConfig")
        println("Environment config: $envConfig")
        println("Environment: $envPath")

        val sysTLC = TLC()
        sysTLC.modelCheck(sysPath, sysConfig, false)
    }
}

fun main(args: Array<String>) = TlaRobustness().main(args)
