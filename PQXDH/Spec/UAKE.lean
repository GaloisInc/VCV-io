/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Spec.Basic
import PQXDH.AKE.UAKE.Basic
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.OracleComp.QueryTracking.QueryBound

open OracleSpec OracleComp AKE
open scoped ENNReal

namespace PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}

inductive Message (G PQPK CT S C IdC IdK : Type) where
  | bundle : PreKeyBundle G PQPK S IdC IdK → Message G PQPK CT S C IdC IdK
  | initial : InitialMessage G CT C IdC IdK → Message G PQPK CT S C IdC IdK
  | confirmation : C → Message G PQPK CT S C IdC IdK
  deriving DecidableEq

def initiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party (InitiatorParameters F G SS SPK Msg K) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SS SPK Msg K ⊕ SessionContext G PQPK Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiate P p b with
        | some (im, ctx) => pure (.acceptAndSend (.inr (.inl ctx)) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf =>
        match confirm P ctx conf with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr SK) => pure (some (some SK))
    | _ => pure none

def recipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    Party (RecipientIdentity F G SS SPK SSK K)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := RecipientParameters F G SS PQPK PQSK SPK SSK K ⊕ K
  init := fun idn => do
    let opkB ← genOPK P.gen hasOPK
    let pqpkB ← P.pqkem.keygen
    let p : RecipientParameters F G SS PQPK PQSK SPK SSK K :=
      { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB,
        opkB := opkB, pqpkB := pqpkB, kdf := idn.kdf }
    let bundle ← publish P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← accept P p im with
        | some ctx => do
            /- DEVIATION FROM SPEC: UAKE requires T to speak last, sending an
              authenticated message if the exchange was accepted. This prevents
              a trivial attack where the attacker simply refrains from sending
              Alice's last message, so that ping-pong is vacuously false. We
              have Bob send the final message of the exchange here in order to
              satisfy this, whereas the spec stops at Bob receiving the
              message. -/
            let conf ← P.aead.encrypt ctx.kb ctx.ad ctx.msg
            pure (.acceptAndSend (.inr ctx.sk) (.confirmation conf) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

def uakeInitiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme K (InitiatorParameters F G SS SPK Msg K)
      (RecipientIdentity F G SS SPK SSK K)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiator P
  T := recipient P hasOPK

def uakeRecipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme K (RecipientIdentity F G SS SPK SSK K)
      (InitiatorParameters F G SS SPK Msg K)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 4
  setup := Prod.swap <$> setup P msg
  U := recipient P hasOPK
  T := initiator P

section CorrectnessLemmas

private lemma probOutput_probComp_evalDist {α : Type} (oa : ProbComp α) (x : α) :
    Pr[= x | ProbCompRuntime.probComp.evalDist oa] = Pr[= x | oa] := by
  rfl

private lemma support_eq_singleton_true_of_evalDist {oa : ProbComp Bool}
    (h : Pr[= true | ProbCompRuntime.probComp.evalDist oa] = 1) :
    support oa = {true} := by
  rw [probOutput_probComp_evalDist, probOutput_eq_one_iff] at h
  exact h.2

private lemma fst_eq_smul_of_mem_support_dhKeygen
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F] {gen : G} {x : G × F}
    (hx : x ∈ support (dhKeygen (F := F) gen)) : x.1 = x.2 • gen := by
  simp only [dhKeygen, mem_support_bind_iff, mem_support_uniformSample, support_pure,
    Set.mem_singleton_iff, true_and] at hx
  obtain ⟨sk, rfl⟩ := hx
  rfl

private lemma verify_eq_true_of_perfectlyComplete
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    {kp : SPK × SSK} (hkp : kp ∈ support P.sig.keygen)
    (m : G ⊕ PQPK) {σ : S} (hσ : σ ∈ support (P.sig.sign kp.1 kp.2 m))
    {b : Bool} (hb : b ∈ support (P.sig.verify kp.1 m σ)) : b = true := by
  have h := support_eq_singleton_true_of_evalDist (hsig m)
  have hmem : b ∈ support (do
      let (pk, sk) ← P.sig.keygen
      let s ← P.sig.sign pk sk m
      P.sig.verify pk m s) := by
    refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
    exact (mem_support_bind_iff _ _ _).mpr ⟨σ, hσ, hb⟩
  rw [h] at hmem
  exact hmem

private lemma decaps_eq_some_of_perfectlyCorrect [DecidableEq SS]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    {kp : PQPK × PQSK} (hkp : kp ∈ support P.pqkem.keygen)
    {cs : CT × SS} (hcs : cs ∈ support (P.pqkem.encaps kp.1))
    {r : Option SS} (hr : r ∈ support (P.pqkem.decaps kp.2 cs.1)) : r = some cs.2 := by
  have h := support_eq_singleton_true_of_evalDist hkem
  have hmem : decide (r = some cs.2) ∈ support P.pqkem.CorrectExp := by
    unfold KEMScheme.CorrectExp
    refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨cs, hcs, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨r, hr, ?_⟩
    simp
  rw [h] at hmem
  simpa using hmem

private lemma aead_decrypt_encrypt_of_perfectlyCorrect [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (k : K) (ad : G × G × PQPK) (m : Msg) {c : C}
    (hc : c ∈ support (P.aead.encrypt k ad m)) :
    P.aead.decrypt k ad c = some m := by
  have h := haead m ad
  rw [probOutput_eq_one_iff] at h
  have hmem : decide (P.aead.decrypt k ad c = some m) ∈
      support (AEAD.CorrectExp P.aead m ad) := by
    unfold AEAD.CorrectExp
    refine (mem_support_bind_iff _ _ _).mpr ⟨k, mem_support_uniformSample K, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨c, hc, ?_⟩
    simp
  rw [h.2] at hmem
  simpa using hmem

private lemma mem_support_initiate
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    {p : InitiatorParameters F G SS SPK Msg K} {bundle : PreKeyBundle G PQPK S IdC IdK}
    {r : Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K)}
    (hpin : bundle.ikB = p.ikB)
    (hok₁ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSig),
      b = true)
    (hok₂ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSig),
      b = true)
    (hr : r ∈ support (initiate P p bundle)) :
    ∃ ekA ∈ support (dhKeygen (F := F) P.gen),
    ∃ cs ∈ support (P.pqkem.encaps bundle.pqpkB.1),
    ∃ ctxt ∈ support (P.aead.encrypt
        (p.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
          Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).2.1
        (p.ikA.1, p.ikB, bundle.pqpkB.1) p.msg),
      r = some (⟨p.ikA.1, ekA.1, cs.1, bundle.spkB.2, bundle.pqpkB.2,
          Option.map Prod.snd bundle.opkB, ctxt⟩,
        ⟨(p.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
            Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).1,
          (p.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
            Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).2.2,
          (p.ikA.1, p.ikB, bundle.pqpkB.1), p.msg⟩) := by
  simp only [initiate, hpin, ne_eq, not_true_eq_false, if_false,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, okSPK, hok, okPQPK, hok', hr⟩ := hr
  obtain rfl := hok₁ _ hok
  obtain rfl := hok₂ _ hok'
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩ := hr
  exact ⟨ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩

private lemma dh_comm [Field F] [AddCommGroup G] [Module F G] [SampleableType F] {gen : G}
    {x y : G × F} (hx : x ∈ support (dhKeygen (F := F) gen))
    (hy : y ∈ support (dhKeygen (F := F) gen)) : DH x.2 y.1 = DH y.2 x.1 := by
  rw [fst_eq_smul_of_mem_support_dhKeygen hx, fst_eq_smul_of_mem_support_dhKeygen hy,
    DH, DH, smul_smul, smul_smul, mul_comm]

private lemma mem_support_accept
    [Field F] [AddCommGroup G] [Module F G] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    {p : RecipientParameters F G SS PQPK PQSK SPK SSK K}
    {im : InitialMessage G CT C IdC IdK} {ss : SS} {m₀ : Msg}
    {r : Option (SessionContext G PQPK Msg K)}
    (hid₁ : im.idSPK = P.idEC p.spkB.1)
    (hid₂ : im.idPQPK = P.idKEM p.pqpkB.1)
    (hid₃ : im.idOPK = Option.map (fun opk => P.idEC opk.1) p.opkB)
    (hdec : ∀ o ∈ support (P.pqkem.decaps p.pqpkB.2 im.ct), o = some ss)
    (hdecr : P.aead.decrypt
        (p.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
          Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).2.1
        (im.ikA, p.ikB.1, p.pqpkB.1) im.ctxt = some m₀)
    (hr : r ∈ support (accept P p im)) :
    r = some ⟨(p.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
        Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).1,
      (p.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
        Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).2.2,
      (im.ikA, p.ikB.1, p.pqpkB.1), m₀⟩ := by
  simp only [accept, hid₁, hid₂, hid₃, ne_eq, not_true, or_self, if_false,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, o, ho, hr⟩ := hr
  obtain rfl := hdec _ ho
  simp only [hdecr, support_pure, Set.mem_singleton_iff] at hr
  exact hr

private lemma opkB_mem_of_genOPK {F G : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    {gen : G} {hasOPK : Bool} {opkB : Option (G × F)}
    (h : opkB ∈ support (genOPK gen hasOPK)) :
    ∀ x ∈ opkB, x ∈ support (dhKeygen (F := F) gen) := by
  unfold genOPK at h
  cases hasOPK with
  | false =>
      simp only [Bool.false_eq_true, if_false, support_pure, Set.mem_singleton_iff] at h
      subst h; simp
  | true =>
      simp only [if_true, support_map, Set.mem_image] at h
      obtain ⟨opk, hopk, rfl⟩ := h
      intro x hx
      simp only [Option.mem_def, Option.some.injEq] at hx
      exact hx ▸ hopk

private lemma run_support_initiator
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (msg : Msg) {kdf : KeyMaterial G SS → K × K × K}
    {ikA ikB spkB : G × F} {sigkB : SPK × SSK}
    (hikA : ikA ∈ support (dhKeygen (F := F) P.gen))
    (hikB : ikB ∈ support (dhKeygen (F := F) P.gen))
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support (dhKeygen (F := F) P.gen))
    {uOut tOut : Option (Option K)}
    (hrun : (uOut, tOut) ∈ support (runHonest (initiator P) (recipient P hasOPK)
      ⟨ikA, ikB.1, sigkB.1, msg, kdf⟩ ⟨ikB, sigkB, spkB, kdf⟩ (3 + 1))) :
    ∃ k, uOut = some (some k) ∧ tOut = some (some k) := by
  simp only [runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, rfl, qInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, rfl⟩ := hbundle
  simp only [InitResult.opening, InitResult.state, mem_support_bind_iff] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  obtain ⟨ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩ := mem_support_initiate P rfl
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₁ hb)
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₂ hb) hir
  simp only [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  dsimp only at hctxt hcs hy
  have hmap : Option.map (fun opk => DH ekA.2 opk.1)
      (Option.map (fun opk => (opk.1, P.idEC opk.1)) opkB)
      = Option.map (fun opk => DH ekA.2 opk.1) opkB := by
    cases opkB <;> rfl
  have hdh1 : DH spkB.2 ikA.1 = DH ikA.2 spkB.1 := dh_comm hspkB hikA
  have hdh2 : DH ikB.2 ekA.1 = DH ekA.2 ikB.1 := dh_comm hikB hekA
  have hdh3 : DH spkB.2 ekA.1 = DH ekA.2 spkB.1 := dh_comm hspkB hekA
  have hdh4 : Option.map (fun opk => DH opk.2 ekA.1) opkB
      = Option.map (fun opk => DH ekA.2 opk.1) opkB := by
    cases opkB with
    | none => rfl
    | some opk =>
        simp only [Option.map_some]
        rw [dh_comm (hopkB opk rfl) hekA]
  rw [hmap] at hctxt hy
  have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
  simp only [mem_support_bind_iff] at hy
  obtain ⟨sr, ⟨ar, har, hsr⟩, hy⟩ := hy
  have hbob := mem_support_accept P rfl rfl (by cases opkB <;> rfl)
    (fun o ho => decaps_eq_some_of_perfectlyCorrect P hkem hpqpkB hcs ho)
    (by dsimp only; rw [hdh1, hdh2, hdh3, hdh4]; exact hdecA) har
  subst hbob
  dsimp only at hsr
  rw [hdh1, hdh2, hdh3, hdh4] at hsr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsr
  obtain ⟨conf, hconf, rfl⟩ := hsr
  have hconfirm := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hconf
  simp only [confirm, hconfirm, mem_support_bind_iff] at hy
  simp only [if_true, support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨x, rfl, hy⟩ := hy
  simp only [support_pure, Set.mem_singleton_iff] at hy
  subst hy
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
  obtain ⟨x, rfl, x1, rfl, h1, h2⟩ := hout
  exact ⟨_, h1, h2⟩

private lemma run_support_recipient
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (msg : Msg) {kdf : KeyMaterial G SS → K × K × K}
    {ikA ikB spkB : G × F} {sigkB : SPK × SSK}
    (hikA : ikA ∈ support (dhKeygen (F := F) P.gen))
    (hikB : ikB ∈ support (dhKeygen (F := F) P.gen))
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support (dhKeygen (F := F) P.gen))
    {uOut tOut : Option (Option K)}
    (hrun : (uOut, tOut) ∈ support (runHonest (recipient P hasOPK) (initiator P)
      ⟨ikB, sigkB, spkB, kdf⟩ ⟨ikA, ikB.1, sigkB.1, msg, kdf⟩ (4 + 1))) :
    ∃ k, uOut = some (some k) ∧ tOut = some (some k) := by
  simp only [runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, qInit, rfl, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, rfl⟩ := hbundle
  simp only [InitResult.opening, InitResult.state, mem_support_bind_iff] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  obtain ⟨ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩ := mem_support_initiate P rfl
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₁ hb)
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₂ hb) hir
  simp only [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  dsimp only at hctxt hcs hy
  have hmap : Option.map (fun opk => DH ekA.2 opk.1)
      (Option.map (fun opk => (opk.1, P.idEC opk.1)) opkB)
      = Option.map (fun opk => DH ekA.2 opk.1) opkB := by
    cases opkB <;> rfl
  have hdh1 : DH spkB.2 ikA.1 = DH ikA.2 spkB.1 := dh_comm hspkB hikA
  have hdh2 : DH ikB.2 ekA.1 = DH ekA.2 ikB.1 := dh_comm hikB hekA
  have hdh3 : DH spkB.2 ekA.1 = DH ekA.2 spkB.1 := dh_comm hspkB hekA
  have hdh4 : Option.map (fun opk => DH opk.2 ekA.1) opkB
      = Option.map (fun opk => DH ekA.2 opk.1) opkB := by
    cases opkB with
    | none => rfl
    | some opk =>
        simp only [Option.map_some]
        rw [dh_comm (hopkB opk rfl) hekA]
  rw [hmap] at hctxt hy
  have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
  simp only [mem_support_bind_iff] at hy
  obtain ⟨sr, ⟨ar, har, hsr⟩, hy⟩ := hy
  have hbob := mem_support_accept P rfl rfl (by cases opkB <;> rfl)
    (fun o ho => decaps_eq_some_of_perfectlyCorrect P hkem hpqpkB hcs ho)
    (by dsimp only; rw [hdh1, hdh2, hdh3, hdh4]; exact hdecA) har
  subst hbob
  dsimp only at hsr
  rw [hdh1, hdh2, hdh3, hdh4] at hsr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsr
  obtain ⟨conf, hconf, rfl⟩ := hsr
  have hconfirm := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hconf
  simp only [confirm, hconfirm, mem_support_bind_iff] at hy
  simp only [if_true, support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨x, rfl, hy⟩ := hy
  simp only [support_pure, Set.mem_singleton_iff] at hy
  subst hy
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
  obtain ⟨x, rfl, x1, rfl, h1, h2⟩ := hout
  exact ⟨_, h1, h2⟩

end CorrectnessLemmas

theorem uakeInitiator_perfectlyCorrect
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) := by
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact HasEvalPMF.probFailure_eq_zero _
  intro b hb
  simp only [UAKE.CorrectExp, uakeInitiator, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, hrun, rfl⟩ := hb
  suffices h : ∃ k, uOut = some (some k) ∧ tOut = some (some k) by
    obtain ⟨k, rfl, rfl⟩ := h
    simp
  simp only [setup, mem_support_bind_iff, support_uniformSample, Set.mem_univ, true_and,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsetup
  obtain ⟨kdf, ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, huk, htk⟩ := hsetup
  subst huk htk
  exact run_support_initiator P hasOPK hsig hkem haead msg hikA hikB hsigkB hspkB hrun

theorem uakeRecipient_perfectlyCorrect
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) := by
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact HasEvalPMF.probFailure_eq_zero _
  intro b hb
  simp only [UAKE.CorrectExp, uakeRecipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, hrun, rfl⟩ := hb
  suffices h : ∃ k, uOut = some (some k) ∧ tOut = some (some k) by
    obtain ⟨k, rfl, rfl⟩ := h
    simp
  simp only [setup, support_map, Set.mem_image, mem_support_bind_iff, support_uniformSample,
    Set.mem_univ, true_and, support_pure, Set.mem_singleton_iff] at hsetup
  obtain ⟨x, ⟨kdf, ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, rfl⟩, hswap⟩ := hsetup
  simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hswap
  obtain ⟨huk, htk⟩ := hswap
  subst huk htk
  exact run_support_recipient P hasOPK hsig hkem haead msg hikA hikB hsigkB hspkB hrun

def _root_.AKE.UAKE.Adversary.OpensAtMost {K UK TK W : Type} {proto : UAKE.Scheme K UK TK W}
    (A : UAKE.Adversary proto) (q : ℕ) : Prop :=
  (∀ uk w, (A.challenge uk w).IsQueryBoundP (· matches Sum.inr .openT) q) ∧
    (∀ st k, (A.post st k).IsQueryBoundP (· matches Sum.inr .openT) q)

private lemma finalize_true_add_false_eq_one {K UK TK W : Type}
    [SampleableType K] [DecidableEq W] {proto : UAKE.Scheme K UK TK W}
    (A : UAKE.Adversary proto) (st : A.State × UAKE.Env proto × TK)
    (cr : UAKE.ChallengeResult proto) (K1 : Option K)
    (hKb : cr.K0 = K1) :
    Pr[= true | UAKE.finalize A st cr true K1] +
      Pr[= true | UAKE.finalize A st cr false K1] = 1 := by
  obtain ⟨aSt, env, tk⟩ := st
  simp only [UAKE.finalize, hKb, ite_self]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  rw [← HasEvalPMF.tsum_probOutput_eq_one
    ((simulateQ (withUnif (UAKE.oracleImpl proto tk)) (A.post aSt K1)).run env)]
  refine tsum_congr fun x => ?_
  have hsum : Pr[= true | if UAKE.fullPingPong x.2 cr = true then ($ᵗ Bool)
        else pure (x.1 == true)] +
      Pr[= true | if UAKE.fullPingPong x.2 cr = true then ($ᵗ Bool)
        else pure (x.1 == false)] = 1 := by
    cases hfpp : UAKE.fullPingPong x.2 cr
    · cases hx : x.1 <;> simp
    · simp [probOutput_uniformSample, Fintype.card_bool, ENNReal.inv_two_add_inv_two]
  rw [← mul_add, hsum, mul_one]

private lemma finalize_none_half {K UK TK W : Type}
    [SampleableType K] [DecidableEq W] {proto : UAKE.Scheme K UK TK W}
    (A : UAKE.Adversary proto) (st : A.State × UAKE.Env proto × TK)
    (cr : UAKE.ChallengeResult proto) (hK0 : cr.K0 = none) :
    Pr[= true | do let b ← $ᵗ Bool; UAKE.finalize A st cr b none] = 1 / 2 := by
  rw [probOutput_bind_uniformBool (fun b => UAKE.finalize A st cr b none) true,
    finalize_true_add_false_eq_one A st cr none hK0]

def kdfRoRExp [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    (km : ProbComp (KeyMaterial G SS))
    (D : (KeyMaterial G SS → K × K × K) → K × K × K → ProbComp Bool) (b : Bool) :
    ProbComp Bool := do
  let kdf ← $ᵗ (KeyMaterial G SS → K × K × K)
  let x ← km
  let ks ← if b then pure (kdf x) else $ᵗ (K × K × K)
  D kdf ks

def KdfHidesInput [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    (km : ProbComp (KeyMaterial G SS)) (ε : ℝ) : Prop :=
  ∀ D : (KeyMaterial G SS → K × K × K) → K × K × K → ProbComp Bool,
    |(Pr[= true | kdfRoRExp km D true]).toReal -
      (Pr[= true | kdfRoRExp km D false]).toReal| ≤ ε

private lemma probOutput_bind_if_true_uniformBool {α : Type} (m : ProbComp α) (c : α → Bool) :
    Pr[= true | do let x ← m; if c x then (pure true : ProbComp Bool) else $ᵗ Bool] =
      1 / 2 + Pr[= true | do let x ← m; pure (c x)] / 2 := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  conv_rhs => rw [show (1 : ℝ≥0∞) / 2 = (∑' x, Pr[= x | m]) / 2 from by
    rw [HasEvalPMF.tsum_probOutput_eq_one]]
  simp only [div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  cases hcx : c x
  · simp [probOutput_uniformSample, Fintype.card_bool]
  · have hp : Pr[= x | m] = Pr[= x | m] * 2⁻¹ + Pr[= x | m] * 2⁻¹ := by
      rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
    simpa [probOutput_uniformSample, Fintype.card_bool] using hp

def initiateIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]
    [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SS SPK Msg K)
    (bundle : PreKeyBundle G PQPK S IdC IdK) :
    ProbComp (Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K)) := do
  if bundle.ikB ≠ p.ikB then return none
  let okSPK ← P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSig
  let okPQPK ← P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSig
  if !(okSPK && okPQPK) then return none
  let ekA : G × F ← dhKeygen P.gen
  let (CT, _SS) ← P.pqkem.encaps bundle.pqpkB.1
  let (SK, KA, KB) ← $ᵗ (K × K × K)
  let AD := (p.ikA.1, bundle.ikB, bundle.pqpkB.1)
  let ctxt ← P.aead.encrypt KA AD p.msg
  return some ({ ikA := p.ikA.1, ekA := ekA.1, ct := CT, idSPK := bundle.spkB.2,
                 idPQPK := bundle.pqpkB.2, idOPK := bundle.opkB.map Prod.snd, ctxt := ctxt },
    { sk := SK, kb := KB, ad := AD, msg := p.msg })

def initiatorIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party (InitiatorParameters F G SS SPK Msg K) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SS SPK Msg K ⊕ SessionContext G PQPK Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiateIdeal P p b with
        | some (im, ctx) => pure (.acceptAndSend (.inr (.inl ctx)) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf =>
        match confirm P ctx conf with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr SK) => pure (some (some SK))
    | _ => pure none

def uakeInitiatorIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme K (InitiatorParameters F G SS SPK Msg K)
      (RecipientIdentity F G SS SPK SSK K)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiatorIdeal P
  T := recipient P hasOPK

def _root_.AKE.UAKE.Adversary.toIdeal
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK} {msg : Msg} {hasOPK : Bool}
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Adversary (uakeInitiatorIdeal P msg hasOPK) where
  State := A.State
  challenge := A.challenge
  post := A.post

theorem uakeInitiator_secure_pq
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K] [SampleableType SS]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εkem εaead εkdf : ℝ)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.advantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.IND_CTXT_Adversary P.aead,
      AEAD.IND_CTXT_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ (DH1 DH2 DH3 : G) (DH4 : Option G),
      KdfHidesInput (K := K)
        (do let ss ← $ᵗ SS; pure (DH1, DH2, DH3, DH4, ss)) εkdf) :
    UAKE.advantage A ≤ εsig + q * (εkem + εaead + εkdf) := by
  unfold UAKE.advantage
  set pReal := (Pr[= true | UAKE.Exp A]).toReal with hpReal
  set pIdeal := (Pr[= true | UAKE.Exp A.toIdeal]).toReal with hpIdeal
  -- Hop 1 (KEM IND-CCA on the challenge KEM key, then `KdfHidesInput`): reprogramming the
  -- challenge session's key material to uniform is undetectable, hybridized over the q sessions.
  have hKeyHop : |pReal - pIdeal| ≤ q * (εkem + εkdf) := by
    sorry
  -- Hop 2 (signature EUF-CMA + AEAD INT-CTXT): with the challenge key uniform, confidentiality
  -- is exactly 1/2, and a non-ping-pong completion needs a forged prekey signature (εsig) or a
  -- forged AEAD confirmation under a uniform key (q·εaead).
  have hIdealHop : |pIdeal - 1 / 2| ≤ εsig + q * εaead := by
    sorry
  calc |pReal - 1 / 2|
      ≤ |pReal - pIdeal| + |pIdeal - 1 / 2| := abs_sub_le _ _ _
    _ ≤ q * (εkem + εkdf) + (εsig + q * εaead) := add_le_add hKeyHop hIdealHop
    _ = εsig + q * (εkem + εaead + εkdf) := by ring

theorem uakeInitiator_secure_dh
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εddh εaead εkdf : ℝ)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.advantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hddh : ∀ D : DiffieHellman.DDHAdversary F G,
      DiffieHellman.ddhDistAdvantage P.gen D ≤ εddh)
    (haead : ∀ B : AEAD.IND_CTXT_Adversary P.aead,
      AEAD.IND_CTXT_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ (DH1 DH2 : G) (DH4 : Option G) (ss : SS),
      KdfHidesInput (K := K)
        (do let c ← $ᵗ F; pure (DH1, DH2, c • P.gen, DH4, ss)) εkdf) :
    UAKE.advantage A ≤ εsig + q * (εddh + εaead + εkdf) := by
  unfold UAKE.advantage
  set pReal := (Pr[= true | UAKE.Exp A]).toReal with hpReal
  set pIdeal := (Pr[= true | UAKE.Exp A.toIdeal]).toReal with hpIdeal
  -- Hop 1 (DDH/GapDH on the challenge DH share, then `KdfHidesInput`): reprogramming the
  -- challenge session's key material to uniform is undetectable, hybridized over the q sessions.
  have hKeyHop : |pReal - pIdeal| ≤ q * (εddh + εkdf) := by
    sorry
  -- Hop 2 (signature EUF-CMA + AEAD INT-CTXT): identical to the pq case — with the challenge key
  -- uniform, confidentiality is 1/2 and a non-ping-pong completion needs a forged signature or a
  -- forged AEAD confirmation.
  have hIdealHop : |pIdeal - 1 / 2| ≤ εsig + q * εaead := by
    sorry
  calc |pReal - 1 / 2|
      ≤ |pReal - pIdeal| + |pIdeal - 1 / 2| := abs_sub_le _ _ _
    _ ≤ q * (εddh + εkdf) + (εsig + q * εaead) := add_le_add hKeyHop hIdealHop
    _ = εsig + q * (εddh + εaead + εkdf) := by ring

end PQXDH
