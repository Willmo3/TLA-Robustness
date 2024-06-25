import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.option

class TlaRobustness : CliktCommand() {
    // Options:
    private val sysPath by option("--sys", "-s", help="tla+ model of the system")
    private val sysConfig by option("--sys-config", "-c", help="tla+ configuration file for the system")
    private val envPath by option("--env", "-e", help="tla+ model of the environment")
    private val envConfig by option("--env-config", "-p", help = "tla+ configuration file for environment")

    override fun run() {
        println("Tla Robustness")
        println("System: $sysPath")
        println("System config: $sysConfig")
        println("Environment config: $envConfig")
        println("Environment: $envPath")
    }
}

fun main(args: Array<String>) = TlaRobustness().main(args)
