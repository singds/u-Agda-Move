#!/bin/bash

# Compile all Agda files in the project directory
AGDA_FILES=$(find ./project -name "*.agda")

for file in $AGDA_FILES; do
  agda $file
  if [ $? -eq 0 ]; then
    echo "[OK] $file" >> result.txt
  else
    echo "[FAIL] $file" >> result.txt
    exit 1
  fi
done
