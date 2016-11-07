#!/usr/bin/env bash

INCLUDES="-I src"

coq_makefile $INCLUDES src/nunchaku_coq_main.ml src/Nunchaku.v > Makefile
