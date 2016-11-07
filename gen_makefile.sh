#!/usr/bin/env bash

INCLUDES="-I src"

coq_makefile $INCLUDES -f _CoqProject > Makefile
