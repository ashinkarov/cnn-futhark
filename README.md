# Correctness Meets Performance: From Agda to Futhark


This repository contains the sources of the paper "Correctness Meets Performance: From Agda to Futhark"
as well as accompanying materials including sources of our framework and the code we used in experiments. 


In this paper we demonstrate a technique for developing high performance applications with strong correctness
guarantees. Using a theorem prover, we derive a high-level specification of the application that includes
correctness invariants of our choice. After that, within the same theorem prover, we implement an extraction
of the specified application into a high-performance language of our choice. Concretely, we are using Agda
to specify a framework for automatic differentiation (reverse mode) that is focused on index-safe tensors.
This framework comes with an optimiser for tensor expressions and the ability to translate these expressions
into Futhark. We specify a canonical convolutional neural network within the proposed framework, compute
the derivatives needed for the training phase and then demonstrate that the generated code approaches the
performance of TensorFlow code when running on a GPU.


## Structure of the Repo


`agda` --- Agda implementaiton of our framework, DSL, AD, optimisations, extraction to Futhark and the
CNN itself.


`paper` --- sources of the paper written in literate Agda.


`src` --- the code we that we used while running our experiments.


