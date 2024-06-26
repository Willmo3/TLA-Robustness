# TLA-Robustness

Generate the robustness of a software system using plain .tla files!

## Introduction

### The Notion of Software Robustness

Implicitly, robust software is resilient to mistakes. When things go awry, robust software ought to keep functioning! 

CMU SoDA and others have formalized this notion. 

The overall behavior of a system is dictated both by factors within a system, such as its programming, and factors outside of the system's control, like network channels or user interactions. In *Safe Environmental Envelopes of Discrete Systems,* by Meira-Góes et al (https://eskang.github.io/assets/papers/cav23.pdf), the notion of software robustness is defined as the maximum number of environmental deviations a system can withstand while still satisfying its safety properties.

In other words: what can change outside of a software system so that the inside of that system keeps working?

### LTS-Robustness

With Meira-Góes et al's formal definition of software robustness came a tool for calculating robustness: CMU SoDA's LTS-Robustness! LTS-Robustness uses labelled transition systems for its calculations (hence the name!)

Given an LTS for the system, the system safety property, the environment, and the environment property, all in fsp form, LTS-Robustness outputs $\Delta$, the set of all maximal sets of transitions which can be added to the environment without breaking compliance with a system's safety properties. 

Intuitively, this $\Delta$ is exactly how much change you can get away with in the external environment before the system stops working.

#### The Problem:

Currently, LTS-Robustness requires all input systems to be in fsp format, meaning that TLA+ specifications, themselves implicitly transition systems, must be manually converted. This tedious maneuver not only wastes user time, thanks to the state space explosion, it also pumps out huge files!


### TLA Robustness

TLA-Robustness bridges the gap between LTS-Robustness and TLA+. CMU SoDA's Recomp-Verify (https://github.com/cmu-soda/recomp-verify) can translate TLA+ specs into fsp format. TLA-Robustness uses this functionality from Recomp-Verify to bridge the gap between TLA+ and LTS-Robustness, allowing users to perform the Cav'23 robustness calculation algorithm on standard TLA+ files!

Additionally, all calculations are performed in main memory, saving both space and time!


## Installation

### Required Software
* Java. TLA-Robustness has been tested on OpenJDK 17.
* Maven.

### Procedure

1. Clone the repository
2. run the setup.sh script. This will install the LTS-Robustness and Recomp-Verify jars provided with this distribution as local maven repositories on your system. Since these are stored in your home directory (probably in ~/.m2), no superuser privileges are required.
3. Run mvn install. The output jar is in the target directory!

Note: two jar files will be produced. Do not run original-tla-robustness! This is not shaded with the necessary dependencies.

## Usage

### Requirements to Run
Four files are required for running TLA-Robustness.
1. The TLA+ model for the system
2. The TLA+ config file for the system
3. The TLA+ model for the environment
4. The TLA+ config file for the model

#### File Formatting
These files should represent valid, TLC-verifiable TLA+ models. Because we calculate robustness assuming a safe system to begin with, models that already violate their own safety properties cannot be checked.

In addition, there are some interface requirements to the configuration files:
* Config files should be of the form `SPECIFICATION Spec`. Please do not provide `INIT` or `NEXT` in your configs.
* We do not support liveness properties, so only define invariants!

We will automatically generate an invariant-free config for the base system, so providing a system configuration with safety properties included is enough for both the system and the safety properties.

### Running
To run: `java -jar tla-robustness [system model path] [system config path] [env model path] [env config path]`

The final robustness will be outputted! (once the program is finished. It's currently under construction!)
