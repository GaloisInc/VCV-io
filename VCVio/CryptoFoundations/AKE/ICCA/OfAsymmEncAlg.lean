/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.ICCA.Basic
import VCVio.CryptoFoundations.AsymmEncAlg.INDCCA

open OracleSpec OracleComp Interaction Interaction.TwoParty
open TimestampedTranscript MsgTransmissionProtocol AKE

namespace ICCA

variable {ι : Type} {spec : OracleSpec ι} {M PK SK C : Type}

def OfAsymmEncAlg (e : AsymmEncAlg (OracleComp spec) M PK SK C) :
    MsgTransmissionProtocol (OracleComp spec) M PK SK where
  Ms := [C]
  setup := e.keygen
  sender pk msg := do
    let c ← e.encrypt pk msg
    pure ⟨c, ()⟩
  receiver sk := fun c => e.decrypt sk c

instance instDecidableEqOfAsymmEncAlgTranscript [DecidableEq C]
    (e : AsymmEncAlg (OracleComp spec) M PK SK C) :
    DecidableEq (Spec.Transcript (Spec.ofList (OfAsymmEncAlg e).Ms)) :=
  inferInstanceAs (DecidableEq (Spec.Transcript (Spec.ofList [C])))

theorem OfAsymmEncAlg_correctExp [DecidableEq M] (e : AsymmEncAlg (OracleComp spec) M PK SK C)
    (msg : M) :
    (OfAsymmEncAlg e).CorrectExp msg = e.CorrectExp msg := by
  sorry

theorem OfAsymmEncAlg_perfectlyCorrect [DecidableEq M] (e : AsymmEncAlg (OracleComp spec) M PK SK C)
    (runtime : ProbCompRuntime (OracleComp spec)) (h : e.PerfectlyCorrect runtime) :
    (OfAsymmEncAlg e).PerfectlyCorrect runtime := by
  sorry

theorem OfAsymmEncAlg_iCCA_reduces_to_IND_CCA [DecidableEq C]
    (e : AsymmEncAlg ProbComp M PK SK C) (A : Adversary (OfAsymmEncAlg e)) :
    ∃ B : e.IND_CCA_Adversary,
      Pr[= true | Exp A] = Pr[= true | e.IND_CCA_Game ProbCompRuntime.probComp B] := by
  sorry

theorem OfAsymmEncAlg_iCCA_advantage [DecidableEq C]
    (e : AsymmEncAlg ProbComp M PK SK C) (A : Adversary (OfAsymmEncAlg e)) :
    ∃ B : e.IND_CCA_Adversary,
      e.IND_CCA_Advantage ProbCompRuntime.probComp B = 2 * |advantage A| := by
  sorry

end ICCA
