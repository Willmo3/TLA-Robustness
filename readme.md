# TLA-Robustness

Generate the robustness of a software system using plain .tla files!

## Introduction
TLA-Robustness bridges the gap between CMU SoDA's LTS-Robustness tool (https://github.com/iandardik/LTS-Robustness) and TLA+.

Currently, LTS-Robustness requires all input systems to be in fsp format, meaning that TLA+ specifications must be manually converted. However, CMU SoDA's Recomp-Verify (https://github.com/cmu-soda/recomp-verify) can translate TLA+ specs into fsp format. 

TLA-Robustness uses this functionality from Recomp-Verify to bridge the gap between TLA+ and LTS-Robustness, allowing users to perform the Cav'23 robustness calculation algorithm (https://eskang.github.io/assets/papers/cav23.pdf) on standard TLA+ files!

## Installation
1. Clone the repository
2. run the setup.sh script. This will install the LTS-Robustness and Recomp-Verify jars provided with this distribution as local maven repositories on your system. Since these are stored in your home directory (probably in ~/.m2), no superuser privileges are required.
3. Run mvn install. The output jar is in the target directory!

Note: two jar files will be produced. Do not run original-tla-robustness! This is not shaded with the necessary dependencies.

## Usage
Four files are required for running TLA-Robustness.
1. The TLA+ model for the system
2. The TLA+ config file for the system
3. The TLA+ model for the environment
4. The TLA+ config file for the model

To run: `java -jar tla-robustness [system model path] [system config path] [env model path] [env config path]`

The final robustness will be outputted! (once the program is finished. It's currently under construction!)
