/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.UAKE.MessageTransmissionProtocol.Defs
import VCVio.CryptoFoundations.AsymmEncAlg.Defs

/-!
# Asymmetric Encryption as a 1-Round Message Transmission Protocol

A non-interactive `AsymmEncAlg` is precisely a 1-round message transmission
protocol in the sense of Dodis–Fiore: the sender encrypts the plaintext to a
ciphertext and transmits it; the receiver decrypts.

This file constructs the wrapper `ofAsymmEncAlg` and proves that perfect
correctness of the underlying scheme lifts to perfect correctness of the
wrapped protocol. Together with `OfSignatureAlg.lean`, this is the first
concrete validation that the `MessageTransmissionProtocol` definition is
inhabited and that its correctness predicate discharges as expected.
-/

namespace Interaction
namespace MessageTransmissionProtocol

open Spec

/-- Wrap a non-interactive `AsymmEncAlg` as a 1-round message transmission
protocol. The single move is the ciphertext, owned by the sender (the only
party that speaks). -/
def ofAsymmEncAlg {m : Type → Type} [Monad m] {M PK SK C : Type}
    (encAlg : AsymmEncAlg m M PK SK C) :
    MessageTransmissionProtocol m M PK SK where
  steps := [⟨C, .sender⟩]
  setup := encAlg.keygen
  sender pk msg := do
    let c ← encAlg.encrypt pk msg
    return ⟨c, ()⟩
  receiver sk := fun c => encAlg.decrypt sk c

variable {m : Type → Type} [Monad m] [LawfulMonad m] {M PK SK C : Type}
  [DecidableEq M]

/-- The wrapped correctness experiment is the same monadic computation as the
underlying `AsymmEncAlg.CorrectExp`. -/
theorem CorrectExp_ofAsymmEncAlg (encAlg : AsymmEncAlg m M PK SK C) (msg : M) :
    (ofAsymmEncAlg encAlg).CorrectExp msg = encAlg.CorrectExp msg := by
  unfold MessageTransmissionProtocol.CorrectExp
    MessageTransmissionProtocol.execOutput
    MessageTransmissionProtocol.exec
    AsymmEncAlg.CorrectExp
  simp only [ofAsymmEncAlg, MessageTransmissionProtocol.spec,
    MessageTransmissionProtocol.roles,
    LinearStep.linearSpec, LinearStep.linearRoles,
    Strategy.runWithRoles_sender, Strategy.runWithRoles_done,
    Function.comp_apply, monad_norm]
  rfl

/-- Perfect correctness of `AsymmEncAlg` lifts to perfect correctness of the
wrapped 1-round message transmission protocol. -/
theorem PerfectlyCorrect_ofAsymmEncAlg
    (encAlg : AsymmEncAlg m M PK SK C) (runtime : ProbCompRuntime m)
    (h : encAlg.PerfectlyCorrect runtime) :
    (ofAsymmEncAlg encAlg).PerfectlyCorrect runtime := by
  intro msg
  rw [CorrectExp_ofAsymmEncAlg]
  exact h msg

end MessageTransmissionProtocol
end Interaction
