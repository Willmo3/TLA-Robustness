# TLA-Robustness

Generate the robustness of a software system using plain .tla files!

## Introduction
TLA-Robustness bridges the gap between CMU SoDA's LTS-Robustness tool (https://github.com/iandardik/LTS-Robustness) and TLA+.

Currently, LTS-Robustness requires all input systems to be in fsp format, meaning that TLA specifications must be manually converted. However, CMU SoDA's Recomp-Verify (https://github.com/cmu-soda/recomp-verify) can translate TLA specs into fsp format. 

TLA-Robustness uses this functionality from Recomp-Verify to bridge the gap between TLA and LTS-Robustness, allowing users to perform the Cav'23 robustness calculation algorithm (https://eskang.github.io/assets/papers/cav23.pdf) on standard TLA+ files!

## Usage

### Installation
1. Clone the repository
2. run the setup.sh script. This will install the LTS-Robustness and Recomp-Verify jars provided with this distribution as local maven repositories on your system. Since these are stored in your home directory (probably in ~/.m2), no superuser priveleges are required.
3. Run mvn install. The output jar is in the target directory!
