(************************************************************************)
(* VRAC: Verified Runtime Assertion Checker                             *)
(* Copyright Université d'Orléans                                       *)
(* Coq code by Frédéric Loulergue                                       *)
(*   based on the VRAC project by                                       *)
(*   Dara Ly, Nikolai Kosmatov, Frédéric Loulergue, Julien Signoles     *)
(* This file is distributed under the terms of the                      *)
(*   Université d'Orléans Non-Commercial License Agreement              *)
(* (see LICENSE file for the text of the license)                       *) 
(************************************************************************)

From Stdlib Require Import ZArith Structures.Equalities List Lia.
Import ListNotations.

From Vrac.Lib Require Import Error Option Tactics Maximum.
From Vrac.Memory Require Import MemoryType.
From Vrac.Common Require Import Syntax.
From Vrac.Source Require Import Syntax Semantics.
From Vrac.Target Require Import Syntax Semantics.
From Vrac.Translation Require Import Translation.

