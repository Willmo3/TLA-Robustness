import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument

class TlaRobustness : CliktCommand() {
    private val sysPath by argument(name="[system model path]", help="tla+ model of the system")
    private val sysConfig by argument(name="[system config path]", help="tla+ configuration file for the system")
    private val envPath by argument(name="[environment path]", help="tla+ model of the environment")
    private val envConfig by argument(name="[environment config path]", help = "tla+ configuration file for environment")

    override fun run() {
        println("Tla Robustness")
        println("System: $sysPath")
        println("System config: $sysConfig")
        println("Environment config: $envConfig")
        println("Environment: $envPath")
    }
}

fun main(args: Array<String>) = TlaRobustness().main(args)
