#!/usr/bin/env sh

mvn install:install-file \
  -Dfile=lib/recomp-verify.jar \
  -DgroupId=cmu.isr \
  -DartifactId=recomp-verify \
  -Dversion=1.0.0 \
  -Dpackaging=jar \
  -DgeneratePom=true

mvn install:install-file \
  -Dfile=lib/LTS-Robustness.jar \
  -DgroupId=cmu.isr \
  -DartifactId=LTS-Robustness \
  -Dversion=1.0.0 \
  -Dpackaging=jar \
  -DgeneratePom=true
