import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.types.file

class TlaRobustness : CliktCommand() {


    // ***** ARGUMENTS ***** //

    private val sysPath
        by argument(name="[system model path]", help="tla+ model of the system").file(mustExist = true)
    private val sysConfig 
        by argument(name="[system config path]", help="tla+ configuration file for the system").file(mustExist = true)
    private val envPath
        by argument(name="[env path]", help="tla+ model of the environment").file(mustExist = true)
    private val envConfig
        by argument(name="[env config path]", help = "tla+ configuration file for environment").file(mustExist = true)


    // ***** MAIN ***** //

    override fun run() {
        println("Tla Robustness")
        println("System: $sysPath")
        println("System config: $sysConfig")
        println("Environment config: $envConfig")
        println("Environment: $envPath")
    }
}

fun main(args: Array<String>) = TlaRobustness().main(args)
