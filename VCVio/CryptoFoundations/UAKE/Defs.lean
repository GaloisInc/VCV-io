/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.UAKE.MessageTransmissionProtocol.Defs
import VCVio.OracleComp.ProbCompLift

/-!
# Unilaterally-Authenticated Key Exchange (UAKE)

A two-party interactive protocol in which an unkeyed user `U` and a keyed
user `T` (whose public key `uk` is known to `U` and whose secret key `tk`
only `T` holds) interact and both privately output a session key
`K : Option K`. Formalized in the style of Dodis and Fiore (Sec. 3 of
*Unilaterally-Authenticated Key Exchange*).

A UAKE protocol Π = (`KESetup`, `U`, `T`):

* `KESetup(1^λ) → (uk, tk)` produces the keyed party's key pair.
* `U(uk)` is `U`'s interactive program; outputs a session key `K_U` or `⊥`.
* `T(tk)` is `T`'s interactive program; outputs a session key `K_T` or `⊥`.

By Dodis–Fiore convention, **`T` always speaks last**, so that `U`'s
acceptance is contingent on `T`'s having reached a terminating state.
This is captured here by giving `T`'s strategy the *sender role* (`T`
plays sender steps) and `U`'s strategy the *receiver role* — the
existing `SenderProgram` / `ReceiverProgram` types from the message
transmission framework already support arbitrary terminal output types,
so we instantiate both at `Option K`.

This file defines:

* `execBoth` — a runner returning *both* parties' terminal outputs.
* `UAKEProtocol m K UK TK` — the structural notion `(KESetup, U, T)`.
* `UAKEProtocol.exec` — convenience: run the honest pair, get
  `(K_T, K_U) : Option K × Option K`.
* `UAKEProtocol.CorrectExp` / `PerfectlyCorrect` — Definition 7 in the
  perfect-correctness variant. Correctness is the *conditional*
  "whenever both `K_U` and `K_T` are non-`⊥`, they agree".

Security (Definition 8 of the paper) is deferred to a sibling module.
-/

namespace Interaction
namespace UAKE

open MessageTransmissionProtocol

/-! ## Two-output runner

The existing `MessageTransmissionProtocol.exec` returns only the receiver's
output, since in the message-transmission setting the sender carries no
terminal value. UAKE protocols have terminal outputs on *both* sides, so
we add a runner returning the pair `(X × Y)`. -/

/-- Run a `SenderProgram` with terminal type `X` against a
`ReceiverProgram` with terminal type `Y`, returning both terminal outputs.
The recursion mirrors `MessageTransmissionProtocol.exec` (matching on the
`LinearStep` constructor pattern so the role is a literal constructor
and the program types reduce by `rfl`). -/
def execBoth {m : Type → Type} [Monad m] {X Y : Type} :
    (steps : List LinearStep) →
    SenderProgram m X steps → ReceiverProgram m Y steps → m (X × Y)
  | [], send, recv => pure (send, recv)
  | ⟨_, .sender⟩ :: rest, send, recv => do
      let ⟨x, sNext⟩ ← send
      let rNext ← recv x
      execBoth rest sNext rNext
  | ⟨_, .receiver⟩ :: rest, send, recv => do
      let ⟨x, rNext⟩ ← recv
      let sNext ← send x
      execBoth rest sNext rNext

/-! ## Protocol structure -/

/-- A unilaterally-authenticated key-exchange protocol in the sense of
Dodis–Fiore (Sec. 3): a possibly-interactive two-party protocol with the
keyed party `T` (with secret key in `TK` and public key in `UK`) and the
unkeyed party `U` (with public key in `UK`), whose terminal outputs are
session keys in `Option K`.

* `steps` describes the per-round move types and speakers.
* `setup` produces a fresh `(uk, tk)` pair (the paper's `KESetup`).
* `responder tk` is `T`'s `SenderProgram` (T plays the sender role
  because, by Dodis–Fiore convention, T speaks last).
* `initiator uk` is `U`'s `ReceiverProgram`.

WLOG `T` speaks last (Dodis–Fiore convention). This is not enforced in
the structure itself; concrete protocols should pick a step list whose
last entry has `.sender`. -/
@[ext]
structure UAKEProtocol (m : Type → Type) [Monad m] (K UK TK : Type) : Type 1 where
  steps : List LinearStep
  setup : m (UK × TK)
  responder : TK → SenderProgram m (Option K) steps
  initiator : UK → ReceiverProgram m (Option K) steps

namespace UAKEProtocol

variable {m : Type → Type} [Monad m] {K UK TK : Type}

/-! ## Honest execution -/

/-- Execute the honest unkeyed party `U(uk)` against the honest keyed
party `T(tk)`, returning the pair `(K_T, K_U) : Option K × Option K`.
The formal counterpart of the paper's `⟨U(uk), T(tk)⟩ = (K_U, K_T)`
notation. -/
def exec (uake : UAKEProtocol m K UK TK) (uk : UK) (tk : TK) :
    m (Option K × Option K) :=
  execBoth uake.steps (uake.responder tk) (uake.initiator uk)

/-! ## Correctness (Definition 7) -/

section Correct

variable [DecidableEq K]

/-- Correctness experiment: sample fresh keys, run the honest pair, and
return `true` iff Definition 7's correctness conditional holds — that is,
whenever both `K_U` and `K_T` are non-`⊥`, they agree.

Note that the conditional is *vacuously true* when either side rejects
(outputs `none`). The paper's notion that "if `U` accepts then `T` must
have accepted" is enforced at the protocol level via the WLOG-T-speaks-
last convention. -/
def CorrectExp (uake : UAKEProtocol m K UK TK) : m Bool := do
  let ⟨uk, tk⟩ ← uake.setup
  let ⟨kT, kU⟩ ← uake.exec uk tk
  return decide (kU.isSome ∧ kT.isSome → kU = kT)

/-- A UAKE protocol is *perfectly correct* under the given probabilistic
runtime when its `CorrectExp` returns `true` with probability `1` — i.e.
for every honest run, whenever both parties accept, their session keys
agree.

Definition 7 of Dodis–Fiore allows a negligible failure probability; the
perfect variant defined here matches the existing convention in this
library (`MessageTransmissionProtocol.PerfectlyCorrect`,
`AsymmEncAlg.PerfectlyCorrect`). Statistical or asymptotic correctness
can be layered on top later. -/
def PerfectlyCorrect (uake : UAKEProtocol m K UK TK)
    (runtime : ProbCompRuntime m) : Prop :=
  Pr[= true | runtime.evalDist uake.CorrectExp] = 1

end Correct

end UAKEProtocol

end UAKE
end Interaction
