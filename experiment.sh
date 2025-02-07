#!/bin/sh
#
# Run the various experiments.
#
# Currently has some stuff specific to the cluster the script was written for.

set -e

module purge
module load python cuda/11.4

python -m venv ve
source ve/bin/activate
pip install -r requirements.txt --quiet

set -x

pytorch/main.py input

tensorflow/main.py input

futhark cuda --server futhark/conv.fut
(cd futhark && ./main.py ../input)
