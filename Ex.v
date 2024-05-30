Require Export Pump.
Require Import Arith.
Require Import Coq.Arith.Arith.

Definition exp_equiv {T} (ss : list (list T)) (re : reg_exp T) : Prop :=
  forall s, In s ss <-> exp_match s re.

Lemma empty_equiv :
  forall (T: Type), exp_equiv [] EmptySet (T := T).
Proof.
  intros. unfold exp_equiv.
  intros. split.
  - (* In s [] -> s =~ EmptySet *)
    intro.
    inversion H. (* Discriminate In s [] *)
  - (* s =~ EmptySet -> In s [] *)
    intro.
    inversion H. (* Discriminate s =~ EmptySet *)
Qed.

Lemma list_equiv {T} (l1 l2 l3 l4: list T) :
  l1 ++ l2 = l3 ++ l4 -> length l1 = length l3 -> l1 = l3 /\ l2 = l4.
Proof.
  intros.
  apply app_eq_app in H.
  do 2 destruct H.
  - destruct H. rewrite H in H0. rewrite app_length in H0.
    rewrite plus_n_O in H0. apply Nat.add_cancel_l in H0.
    destruct x.
    + simpl in *. rewrite app_nil_r in H. auto.
    + inversion H0.
  - destruct H. rewrite H in H0. rewrite app_length in H0.
    rewrite (plus_n_O (length l1)) in H0 at 1. apply Nat.add_cancel_l in H0.
    destruct x.
    + simpl in *. rewrite app_nil_r in H. auto.
    + inversion H0.
Qed.

Lemma napp_zero_one_equiv (p q r s: nat) :
  napp p [0] ++ napp q [1] = napp r [0] ++ napp s [1] -> p = q /\ r = s.
Proof.
  exact TODO.
Qed.

(* A list definition of the string 0^n1^n *)
Definition zero_n_one_n (n : nat) : list nat :=
  napp n [0] ++ napp n [1].

(* A set of all 0^n1^ns *)
Definition zero_n_one_n_lang (ss : list (list nat)): Prop :=
  forall s, In s ss <-> exists m, s = zero_n_one_n m.

(* A proof that `zero_n_one_n_lang` is not a regular language *)
Theorem zero_n_one_n_lang_not_regular :
  forall (ss : list (list nat)), zero_n_one_n_lang ss -> ~(exists re, exp_equiv ss re).
Proof.
  (* We first assume an equivalent regular expression `re` *)
  intros. intro. destruct H0 as [re H0].
  unfold exp_equiv in H0.
  unfold zero_n_one_n_lang in H.
  (* We now set up the string 0^t1^t to induce a contradiction in the pumping theorem *)
  remember (pumping_constant re) as t.
  remember (zero_n_one_n t) as xyz.
  
  (* Step 1. We first show that xyz =~ re *)
  assert (exists m : nat, xyz = zero_n_one_n m). exists t. auto.
  apply H in H1. apply H0 in H1 as Hre. (* Hre : xyz =~ re *)

  (* Step 2. Apply pumping theorem to xyz *)
  apply pumping in Hre.
  
  (* Now we induce contradiction from the existence of x, y, z in the pumping theorem *)
  destruct Hre as [x [y [z Hre]]].
  (* Hre : xyz = x ++ y ++ z /\ y <> [] /\ length x + length y <= pumping_constant re 
  /\ (forall m : nat, x ++ napp m y ++ z =~ re) *)
  destruct Hre as [Hp1 [Hp2 [Hp3 Hp4]]].
  rewrite <- Heqt in Hp3.

  (* We will use x ++ napp 0 y ++ z = x ++ z *)
  specialize (Hp4 0). 
  simpl in Hp4. remember (x ++ z) as xz.

  (* The reverse process of proving xyz =~ re *)
  apply H0 in Hp4. apply H in Hp4.
  (* Hp4 : exists m : nat, xz = zero_n_one_n m *)
  assert (xyz = napp (length x) [0] ++ napp (length y) [0] ++ napp (t - (length x + length y)) [0] ++ napp t [1]). {
    rewrite Heqxyz.
    rewrite (app_assoc (napp (length x) [0]) _ _).
    rewrite <- (napp_plus (nat) (length x) (length y) [0]).
    rewrite (app_assoc _ _ (napp t [1])).
    rewrite <- napp_plus.
    unfold zero_n_one_n.
    repeat f_equal.
    (* Now the goal shrinks to t = length x + length y + (t - (length x + length y)) *)
    symmetry.
    rewrite Nat.add_comm. apply Nat.sub_add. auto.
  }
  rewrite Hp1 in H2. 
  apply list_equiv in H2.
  {
    destruct H2. apply list_equiv in H3. destruct H3.
    (* We now have x = napp (length x) [0] and z = napp (t - (length x + length y)) [0] ++ napp t [1] *)
    rewrite Heqxz in Hp4.
    rewrite H2 in Hp4. rewrite H4 in Hp4.
    unfold zero_n_one_n in Hp4.
    rewrite app_assoc in Hp4. 
    rewrite <- (napp_plus nat (length x) _ [0]) in Hp4. 
    destruct Hp4 as [m Hp4].
    apply napp_zero_one_equiv in Hp4.
    destruct Hp4.
    (* We now have H5 : length x + (t - (length x + length y)) = t *)
    rewrite Nat.add_sub_assoc in H5. 
    rewrite <- Arith_prebase.minus_plus_simpl_l_reverse_stt in H5.
    apply Nat.add_sub_eq_nz in H5. 
    (* H5 : length y + t = t *)
    rewrite Nat.add_comm in H5. rewrite plus_n_O in H5.
    rewrite Nat.add_cancel_l in H5.
    (* H5 : length y = 0. This is contradictory with Hp2: y <> []! *)
    destruct y eqn:Hy. contradiction. discriminate.

    (* The core proof process is over since we created a contradiction. 
    We now take care of the side-effect goals made during some `apply`s. 
    Most are derived almost directly from the assumptions. *)
    - rewrite Heqt. intro. apply pumping_constant_0_false in H7. auto.
    - auto. 
    - rewrite napp_length. simpl. rewrite Nat.mul_1_r. auto.
  }
  - rewrite napp_length. simpl. rewrite Nat.mul_1_r. auto.
  - rewrite <- Heqt. rewrite Heqxyz.
    unfold zero_n_one_n. rewrite app_length.
    repeat rewrite napp_length. simpl.
    repeat rewrite Nat.mul_1_r. apply Nat.le_add_r.
Qed.

  