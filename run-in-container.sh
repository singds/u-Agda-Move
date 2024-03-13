#!/bin/bash

# Compile all Agda files in the project directory
AGDA_FILES=$(find ./project -name "*.agda")

for file in $AGDA_FILES; do
  agda $file
done
