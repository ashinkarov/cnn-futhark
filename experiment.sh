#!/bin/sh
#
# Run the various experiments.
#
# Currently has some stuff specific to the cluster the script was written for.

TRAINING_SIZE=10000
BATCH_SIZE=1000

set -e

module purge
module load python/3.9.9 cuda/11.8 cudnn/8.6.0

python -m venv ve
source ve/bin/activate
pip install -r requirements.txt --quiet

set -x

pytorch/main.py input --training-size=${TRAINING_SIZE} --batch-size=${BATCH_SIZE}

export LD_LIBRARY_PATH=/opt/software/cudnn/8.6.0/lib/:$LD_LIBRARY_PATH # Hack
tensorflow/main.py input --gpu --training-size=${TRAINING_SIZE} --batch-size=${BATCH_SIZE}

futhark cuda --server futhark/conv.fut
futhark/main.py input/ --futhark futhark/conv --training-size=${TRAINING_SIZE} --batch-size=${BATCH_SIZE}
