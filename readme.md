# TLA-Robustness

Generate the robustness of a software system using plain .tla files!

## Introduction
TLA-Robustness bridges the gap between CMU SoDA's LTS-Robustness tool (https://github.com/iandardik/LTS-Robustness) and TLA+.

Currently, LTS-Robustness requires all input systems to be in fsp format, meaning that TLA specifications must be manually converted. However, CMU SoDA's Recomp-Verify (https://github.com/cmu-soda/recomp-verify) can translate TLA specs into fsp format. 

TLA-Robustness uses this functionality from Recomp-Verify to bridge the gap between TLA and LTS-Robustness, allowing users to perform the Cav'23 robustness calculation algorithm (https://eskang.github.io/assets/papers/cav23.pdf) on standard TLA+ files!
