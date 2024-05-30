Require Export Reg.
Require Import Arith.

Definition TODO {T: Type} : T. Admitted.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 => 
    pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
    pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

Lemma pumping_constant_0_false:
  forall T (re : reg_exp T), pumping_constant re = 0 -> False.
Proof.
  intros. 
  induction re;
  try discriminate;
  try (simpl in H; apply Nat.eq_add_0 in H; destruct H; apply IHre1 in H; auto);
  simpl in H. apply IHre in H. auto.
Qed.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_length: forall T (n : nat) (l : list T),
  length (napp n l) = n * length l.
Proof.
  intros.
  induction n.
  - simpl. auto.
  - simpl. rewrite app_length. rewrite IHn. auto.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - (* MChar *)
    simpl. intros. inversion H. inversion H1.
  - (* MApp *)
    simpl in *. intros. rewrite app_length in H. apply Nat.add_le_cases in H.
    (* Before destructing, we save the first case as an assertion since the second case uses it *)
    assert (Hre1: pumping_constant re1 <= length s1 -> exists s0 s3 s4: list T, s1 ++ s2 = s0 ++ s3 ++ s4 /\ s3 <> [] /\ length s0 + length s3 <= pumping_constant re1 + pumping_constant re2 /\ (forall m : nat, s0 ++ napp m s3 ++ s4 =~ App re1 re2)). {
      clear H. intro H.
      apply IH1 in H as Hexists. destruct Hexists as [s0 [s3 [s4 Hexists]]].
      (* Now prove that the variables in Hexists apply to the goal as well
      with a simple append to front or back *)
      destruct Hexists as [He1 [He2 [He3 He4]]].
      exists s0, s3, (s4 ++ s2).
      repeat split; try auto.
      + apply app_inv_tail_iff with (l := s2) in He1. repeat rewrite <- app_assoc in He1. auto.
      + assert (Htrans: pumping_constant re1 <= pumping_constant re1 + pumping_constant re2). apply Nat.le_add_r.
        apply (Nat.le_trans _ _ _ He3 Htrans). 
      + intro. specialize (He4 m). remember (s0 ++ napp m s3 ++ s4) as s0'.
        (* Few list operations to apply MApp with s0' and s2 *) 
        rewrite app_assoc. rewrite app_assoc. rewrite <- (app_assoc _ _ s4). rewrite <- Heqs0'.
        apply (MApp s0' re1 s2 re2 He4 Hmatch2).
    }
    (* Divide the cases for each pumping_constant inequality *)
    destruct H.
    {
      apply Hre1 in H. auto.
    }
    {
      (* Almost identical process, but we first assume that `length s1 <= pumping_constant re1` for later use case. 
      The opposite case can easily be proved by Hre1 *)
      specialize (Nat.le_ge_cases (length s1) (pumping_constant re1)). intro Hlg. destruct Hlg.
      - apply IH2 in H as Hexists. destruct Hexists as [s0 [s3 [s4 Hexists]]].
        destruct Hexists as [He1 [He2 [He3 He4]]].
        exists (s1 ++ s0), s3, s4.
        repeat split; try auto.
        + rewrite <- app_assoc. rewrite He1. auto.
        + rewrite app_length. rewrite <- Nat.add_assoc. apply Nat.add_le_mono with (n := length s1); auto.
        + intro. specialize (He4 m). rewrite <- (app_assoc s1 s0). 
          remember (s0 ++ napp m s3 ++ s4) as s0'.
          apply (MApp s1 re1 s0' re2 Hmatch1 He4). 
      - apply Hre1 in H0. auto.
    }
  - (* MUnionL *)
  simpl. intros. 
  (* First prove that pumping_constant re1 <= length s1 by transivity *)
  assert (Htrans: pumping_constant re1 <= pumping_constant re1 + pumping_constant re2). apply Nat.le_add_r. 
  pose proof (Nat.le_trans _ _ _ Htrans H) as Hlen. apply IH in Hlen as Hexists.
  (* Now prove that the variables in Hexists apply to the goal as well *)
  destruct Hexists as [s2 [s3 [s4 Hexists]]]. (* Introduce the variables s2, s3 s4 *)
  destruct Hexists as [He1 [He2 [He3 He4]]]. (* Split the conditions *)
  exists s2, s3, s4.
  repeat split; try auto.
  + apply (Nat.le_trans _ _ _ He3 Htrans).
  + intro. specialize (He4 m). apply MUnionL. assumption.

  - (* MUnionR: almost identical to MUnionL case *)
  simpl. intros. 
  (* First prove that pumping_constant re2 <= length s2 by transitivity *)
  assert (Htrans: pumping_constant re2 <= pumping_constant re1 + pumping_constant re2). apply Nat.le_add_l.
  pose proof (Nat.le_trans _ _ _ Htrans H) as Hlen. apply IH in Hlen as Hexists.
  (* Now prove that the variables in Hexists apply to the goal as well *)
  destruct Hexists as [s1 [s3 [s4 Hexists]]]. (* Introduce the variables s1, s3, s4 *)
  destruct Hexists as [He1 [He2 [He3 He4]]]. (* Split the conditions *)
  exists s1, s3, s4.
  repeat split; try auto.
  + apply (Nat.le_trans _ _ _ He3 Htrans).
  + intro. specialize (He4 m). apply MUnionR. assumption.
  
  - (* MStarEmpty *)
  intros. simpl in H. inversion H. clear H.
  (* Pumping constant cannot be 0 *)
  apply pumping_constant_0_false in H1. destruct H1.

  - (* MStarApp *)
  intros. simpl in *. rewrite app_length in H.
  (* Again we destruct by the inequality of `pumping_constant re` and `length s1` *)
  specialize (Nat.le_ge_cases (length s1) (pumping_constant re)). intro Hlg. destruct Hlg.
  + destruct (length s1) eqn:Hls1.
  {
    (* This case allows us to use `IH2` since `pumping_constant re <= length s2` *)
    simpl in *. apply IH2 in H. destruct H as [s0 [s3 [s4 Hexists]]]. exists (s1 ++ s0), s3, s4.
    destruct Hexists as [He1 [He2 [He3 He4]]].
    repeat split; try auto.
    - rewrite <- app_assoc. rewrite He1. auto. 
    - rewrite app_length. rewrite Hls1. auto.
    - intro. specialize (He4 m). remember (s0 ++ napp m s3 ++ s4) as s0'.
      rewrite <- app_assoc. rewrite <- Heqs0'. apply (MStarApp s1 s0' re); auto.
  }
  {
    (* For this final case, we manually offer the existence by using non-empty s1. *)
    exists [], s1, s2. repeat split; try auto.
    - (* s1 <> [] *)
      destruct s1. discriminate. intro. inversion H1.
    - (* length [] + length s1 <= pumping_constant re *)
      simpl. rewrite Hls1. auto.
    - intro. simpl. (* napp m s1 ++ s2 =~ Star re *)
      induction m. (* We use induction by m and apply MStarApp *)
      + simpl. auto.
      + simpl. rewrite <- app_assoc. apply (MStarApp s1 (napp m s1 ++ s2) re); auto.
  }
  (* This case can use `IH1` in a similar manner. *)
  + apply IH1 in H0. destruct H0 as [s0 [s3 [s4 Hexists]]]. exists s0, s3, (s4 ++ s2).
    destruct Hexists as [He1 [He2 [He3 He4]]].
    repeat split; try auto.
    * rewrite He1. repeat rewrite <- app_assoc. auto.
    * intro. specialize (He4 m). remember (s0 ++ napp m s3 ++ s4) as s0'. 
      (* Few list operations to apply MStarApp with s0' and s2 *) 
      rewrite app_assoc. rewrite app_assoc. rewrite <- (app_assoc _ _ s4). rewrite <- Heqs0'.
      apply (MStarApp s0' s2 re); auto.
Qed.
