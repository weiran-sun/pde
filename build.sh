#!/bin/bash

# This script builds the project's Lean code.

set -o pipefail # stop if any command fails

lake exe cache get
lake -R -Kenv=dev build PDE:docs
lake build

# # --- CLEANUP SECTION ---
# echo "Removing specific dependency documentation..."

# # Enter the documentation output directory
# cd .lake/build/doc

# # Remove files and directories starting with the specified prefixes
# rm -rf Aesop* \
#        Batteries* \
#        ImportGraph* \
#        Init* \
#        Lake* \
#        Mathlib* \
#        Plausible* \
#        ProofWidgets* \
#        Qq* \
#        Std*

# # Return to project root
# cd ../../../

# echo "Done. Dependency docs removed."
