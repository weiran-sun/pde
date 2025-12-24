#!/bin/bash

# This script builds the project's Lean code.

set -o pipefail # stop if any command fails

# cd pde/
lake exe cache get
lake -R -Kenv=dev build PDE:docs
lake build
