/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.UAKE.MessageTransmissionProtocol.Defs
import VCVio.CryptoFoundations.SignatureAlg

/-!
# Signatures as a 1-Round Message Transmission Protocol

A non-interactive `SignatureAlg` is precisely a 1-round message transmission
protocol in the sense of Dodis–Fiore: the sender signs the plaintext and
transmits `(msg, σ)`; the receiver verifies and outputs `some msg` on accept,
`none` on reject.

The sender key is the pair `(pk, sk)` since `SignatureAlg.sign` consumes both
inputs (some hash-and-sign schemes bind the signature to `pk`); the receiver
key is `pk` alone.

This file constructs the wrapper `ofSignatureAlg` and proves that perfect
completeness of the underlying scheme lifts to perfect correctness of the
wrapped protocol.
-/

namespace Interaction
namespace MessageTransmissionProtocol

open Spec

/-- Wrap a non-interactive `SignatureAlg` as a 1-round message transmission
protocol. The single move is the pair `(msg, σ)`, owned by the sender.

The sender's key is `(pk, sk)`: `SignatureAlg.sign` consumes both inputs (some
hash-and-sign schemes bind `σ` to `pk`). The receiver's key is `pk` alone. -/
def ofSignatureAlg {m : Type → Type} [Monad m] {M PK SK S : Type}
    (sigAlg : SignatureAlg m M PK SK S) :
    MessageTransmissionProtocol m M (PK × SK) PK where
  steps := [⟨M × S, .sender⟩]
  setup := (fun keys => (keys, keys.1)) <$> sigAlg.keygen
  sender keys msg := do
    let σ ← sigAlg.sign keys.1 keys.2 msg
    return ⟨(msg, σ), ()⟩
  receiver pk := fun ms => do
    let v ← sigAlg.verify pk ms.1 ms.2
    return (if v then some ms.1 else none)

variable {m : Type → Type} [Monad m] [LawfulMonad m] {M PK SK S : Type}
  [DecidableEq M]

/-- The wrapped correctness experiment reduces to the underlying signature
completeness experiment. -/
theorem CorrectExp_ofSignatureAlg
    (sigAlg : SignatureAlg m M PK SK S) (msg : M) :
    (ofSignatureAlg sigAlg).CorrectExp msg = (do
      let keys ← sigAlg.keygen
      let σ ← sigAlg.sign keys.1 keys.2 msg
      sigAlg.verify keys.1 msg σ) := by
  unfold MessageTransmissionProtocol.CorrectExp
  simp only [ofSignatureAlg, exec, SenderProgram, ReceiverProgram, monad_norm,
    Function.comp_apply, pure_bind]
  have h : ∀ v : Bool, decide ((if v then some msg else none) = some msg) = v := by
    intro v; cases v <;> simp
  simp only [h, bind_pure]

/-- Perfect completeness of `SignatureAlg` lifts to perfect correctness of the
wrapped 1-round message transmission protocol. -/
theorem PerfectlyCorrect_ofSignatureAlg
    (sigAlg : SignatureAlg m M PK SK S) (runtime : ProbCompRuntime m)
    (h : sigAlg.PerfectlyComplete runtime) :
    (ofSignatureAlg sigAlg).PerfectlyCorrect runtime := by
  intro msg
  rw [CorrectExp_ofSignatureAlg]
  exact h msg

end MessageTransmissionProtocol
end Interaction
