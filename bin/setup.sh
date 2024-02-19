#!/usr/bin/env bash

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

PROJ_DIR=$(dirname $SCRIPT_DIR)

cd $PROJ_DIR

git submodule update --init --recursive

DATALOG=$PROJ_DIR/datalogo

cd $DATALOG

make install

cd $PROJ_DIR
