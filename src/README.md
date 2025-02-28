# Experimental validation

The `futhark/conv.fut` file contains the Futhark program. The
`train_gen` function has been extracted from our Agda code. The rest
of the code is hand-written scaffolding and monomorphic variants of
rank-polymorphic operations. The `futhark/main.py` contains Python
code for loading data and invoking the Python program.

The `tensorflow/main.py` file contains our TensorFlow implementation
of the CNN.

The `pytorch/main.py` file contains our TensorFlow implementation of
the CNN.
