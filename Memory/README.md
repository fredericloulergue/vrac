Coq version used: 8.15.2

Memory Models
=============

- MemoryType.v: formalization of memory types used by both memory models
- ExecutionMemoryModel.v: axiomatization of the execution memory model
- ExecutionMemoryImplementation.v: an implementation of this axiomatization
- ObservationMemoryModel.v: axiomatization of the observation memory model
- ObservationMemoryImplementation.v: an implementation of this axiomatization

Contexts and Representation
===========================

- Context.v: formalization of contexts and proofs of their properties
  (properties 1 to 6 in the paper)
- Representation: formalization of the representation of an execution
  memory by an observation memory and properties (properties 6 to 10
  in the paper)

Utility files
=============
- Eqb.v
- Tactics.v
- Option.v