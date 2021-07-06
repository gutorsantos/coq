(** * A correção do algoritmo de ordenação por inserção *)

(** O objetivo deste arquivo é servir de apoio ao desenvolvimento do projeto deste semestre. Aqui apresentaremos todo o processo de formalização do algoritmo de ordenação por inserção, e este processo deve servir como modelo para o desenvolvimento do seu projeto. *)

(* begin hide *)
Require Import Arith List.
(* end hide *)

(** Inicialmente apresentamos a definição do predicado [sorted] que é o mesmo apresentado no projeto, e por isto não nos preocuparemos em explicar aqui esta definição. *)

Inductive sorted :list nat -> Prop :=
  | nil_sorted : sorted nil
  | one_sorted: forall n:nat, sorted (n :: nil)
  | all_sorted : forall (x y: nat) (l:list nat), sorted (y :: l) -> x <= y -> sorted (x :: y :: l).

(** O algoritmo de ordenação por inserção é baseado em na função auxiliar [insert] que definimos a seguir. A função [insert] recebe um natural [x] e uma lista [l] como argumentos, e é definida recursivamente na estrutura de [l]: *)

Fixpoint insert (x:nat) (l: list nat) := match l with
                      | nil => x :: nil
                      | h :: tl => if x <=? h then (x :: l)
                                                  else (h :: (insert x tl)) 
                      end.

(** Como podemos observar, quando a lista [l] é a lista vazia, a função retorna a lista unitária contendo o elemento que foi inserido. Quando [l] não é a lista vazia, então ela tem a forma [h::tl], isto é, [l] tem [h] como primeiro elemento, e [tl] como cauda. Para saber onde inserir um elemento [x], comparamos [x] com [h], e quando [x] é menor ou igual a [h] simplesmente inserimos [x] na primeira posição da lista. Caso contrário, a função vai recursivamente encontrar a posição correta para inserir [x]. Assim, temos que a função [insert] é construída de forma a preservar a ordenação da lista recebida como segundo argumento. Este é exatamente o conteúdo do lema a seguir: *)

Lemma insert_preserves_sorting: forall l x, sorted l -> sorted (insert x l). 
Proof.
  induction l.
  - intros x H.
    simpl.
    apply one_sorted.
  - intros x H.
    simpl.
    destruct (x <=? a) eqn:Hleq.
    + apply leb_complete in Hleq.
      apply all_sorted; assumption.
    + generalize dependent l.
      intro l. case l.
      * intros H1 H2.
        simpl.
        apply all_sorted.
        ** apply one_sorted.
        ** apply Nat.leb_gt in Hleq.
           apply Nat.lt_le_incl; assumption.
      * intros n l' H1 H2.
        simpl.
        destruct (x <=? n) eqn:Hleq'.
        ** apply all_sorted.
           *** apply all_sorted.
               **** inversion H2; subst.
                    assumption.
               **** apply leb_complete in Hleq'.
                    assumption.
           *** apply Nat.leb_gt in Hleq.
           apply Nat.lt_le_incl; assumption.
        ** apply all_sorted.
           *** inversion H2; subst.
               apply (H1 x) in H3.
               simpl in H3.
               rewrite Hleq' in H3.
               assumption.
           *** inversion H2; subst.
               assumption.
Qed.

(** A seguir apresentaremos uma prova alternativa para o lema acima: *)

Definition le_all x l := forall y, In y l -> x <= y.
Infix "<=*" := le_all (at level 70, no associativity).

Lemma le_all_nil: forall a, a <=* nil.
Proof.
  intro a; unfold le_all.
  intros y H.
  inversion H.
Qed.

Lemma sublist_sorted: forall l a, sorted (a :: l) -> sorted l.
Proof.
  intro l.
  case l.
  - intros a H.  
    apply nil_sorted.  
  - intros n l' a H.  
    inversion H; subst.
    assumption.  
Qed.  

Lemma le_all_sorted: forall l a, a <=* l -> sorted l -> sorted (a :: l).
Proof.
  intro l.
  case l.
  - intros a G1 G2.
    apply one_sorted.
  - intros n l0 a G1 G2.
    apply all_sorted.
    + assumption.
    + unfold le_all in G1.
      apply G1.
      apply in_eq.
Qed.

Lemma sorted_le_all: forall l a, sorted(a :: l) -> a <=* l.
Proof.
    induction l.
  - intros a ordenada n ta_dentro.
    destruct ta_dentro.
  - intros num ordenada. (** refatorar esta prova **)
    unfold le_all.
    intros y H0.
    inversion ordenada.
    subst.
    inversion H0.
    subst.
    assumption.
    apply IHl in H2.  
    unfold le_all in H2.
    specialize(H2 y H).
    apply Nat.le_trans with (m := a); assumption.
Qed.

Lemma le_all_cons_part1: forall l a x, a <= x -> a <=* l -> a <=* x :: l.
Proof.
  induction l.
  - intros num_1 num_2.
    + intros b c.
      unfold le_all.
      intros.
      destruct H.
        * subst.
          assumption.
        * destruct H.
  - intros num_1 num_2.
    + intros b c.
      unfold le_all.
      intros.
      destruct H.
        * subst.
          assumption.
        * destruct H.
          ++  subst.
              apply c.
              apply in_eq.
          ++  apply c. 
              simpl.
              right.
              assumption.
Qed.

Lemma le_all_cons_part2: forall l a x, a <=* x :: l -> a <= x /\ a <=* l.
Proof.
  induction l.
  - intros num1 num2.
    split.
    + apply H.
      simpl.
      left. 
      reflexivity.
    + apply le_all_nil.
  - split.
    + apply H.
      simpl.
      left.
      reflexivity.
    + apply le_all_cons_part1.
      * apply H.
        simpl.
        right. left.
        reflexivity.
      * unfold le_all. intros.
        apply H.
        simpl.
        right. right.
        assumption.
Qed.

Lemma le_all_insert: forall l a x, a <= x -> a <=* l -> a <=* insert x l.
Proof.
  induction l.
  - intros a x Hleq Hle_all.
    simpl.
    apply le_all_cons_part1; assumption.
  - intros a' x Hleq Hle_all.
    simpl.
    destruct (x <=? a) eqn: H.
    + apply le_all_cons_part1; assumption.
    + apply le_all_cons_part2  in Hle_all.
      destruct Hle_all as [H1 H2].
      apply le_all_cons_part1.
      * assumption.
      * apply IHl; assumption.
Qed.

Lemma insert_preserves_sorting': forall l x, sorted l -> sorted (insert x l). 
Proof.
  induction l.
  - intros x H.
    simpl.
    apply one_sorted.
  - intros x H.
    simpl.
    destruct (x <=? a) eqn:Hleq.
    + apply leb_complete in Hleq.
      apply all_sorted; assumption.
    + apply le_all_sorted.
      * apply le_all_insert.
        ** apply leb_complete_conv in Hleq.
           apply Nat.lt_le_incl; assumption.
        ** apply sorted_le_all; assumption.
      * apply IHl.
        apply sublist_sorted with a; assumption.
Qed.

(** A função principal do algoritmo é dada a seguir: *)

Fixpoint insertion_sort l := match l with
                             | nil =>l
                             | h :: tl => insert h (insertion_sort tl)
                             end.

(** A função [insertion_sort] é  definida recursivamente na estrutura da lista [l] que é dada como argumento. Quando a lista é vazia não há nada a fazer, e caso contrário, a função [insert] é chamada para inserir a cabeça [h] da lista na cauda [tl] onde a função é aplicada recursivamente. O lema a seguir pede para você provar que a função [insertion_sort] retorna uma lista ordenada. *)

Lemma insertion_sort_sorts: forall l, sorted (insertion_sort l).
Proof.
  induction l.
  - simpl.
    apply nil_sorted.
  - simpl insertion_sort.
    apply insert_preserves_sorting.
    apply IHl.
Qed.

(** A seguir apresentamos a definição de permutação a partir da contagem do número de ocorrências dos elementos nas listas, assim como apresentada no projeto mergesort deste semestre, e os lemas a seguir nos permitem concluir que o algoritmo [insertion_sort] é correto. *)

Fixpoint num_oc n l  :=
  match l with
    | nil => 0
    | h :: tl =>
      if n =? h then S(num_oc n tl) else  num_oc n tl
  end.

Definition perm l l' := forall n:nat, num_oc n l = num_oc n l'.

Lemma perm_refl: forall l, perm l l.
Proof.
intro l. unfold perm. intro. reflexivity.
Qed.

Lemma num_oc_insert_neq: forall l n a, n =? a = false -> num_oc n (insert a l) = num_oc n l.
Proof.
  induction l.
  - intros n a H.
    simpl.
    rewrite H; reflexivity.
  - intros n a' H.
    simpl insert.
    destruct (a' <=? a) eqn: H'.
    + simpl.
      destruct (n =? a) eqn: H''; rewrite H; reflexivity.
    + simpl.
      destruct (n =? a) eqn: H'';  apply IHl in H; 
        rewrite H; reflexivity.
Qed.

Lemma num_oc_insert: forall l n, num_oc n (insert n l) = S (num_oc n l).
Proof.  
  intros.
  induction l.
  - simpl.
    destruct (n =? n) eqn: b.
    + reflexivity.
    + pose proof Nat.eqb_refl.
      specialize H with n.
      apply beq_nat_false in b.
      contradiction.
  - destruct (n =? a) eqn: t.
    + replace a with n.
      * simpl.
        destruct (n <=? n) eqn: af.
        **  pose proof Nat.eqb_refl.
            specialize H with n.
            replace (n =? n) with true.
            replace (S (num_oc n l)) with (num_oc n (insert n l)).
            destruct num_oc.
            *** simpl.
                replace (n =? n) with true.
                replace (S (num_oc n l)) with 0.
                reflexivity.
            *** simpl.
                replace (n =? n) with true.
                replace (S n0) with (S (num_oc n l)).
                reflexivity.
         ** destruct (n =? n) eqn: H1.
            *** simpl.
                replace (n =? n) with true.
                replace (S (num_oc n l)) with (num_oc n (insert n l)).
                reflexivity.
            *** simpl.
                replace (n =? n) with false.
                replace (S (num_oc n l)) with (num_oc n (insert n l)).
                reflexivity.
      * apply beq_nat_true.
        assumption.
    + simpl.
      replace (n =? a) with false.
      destruct (n <=? a) eqn: G.
      * simpl.
        destruct (n =? n) eqn: I.
        ** replace (n =? a) with false.
           reflexivity.
        ** apply beq_nat_false in I.
            contradiction.
      * simpl.
        replace (n =? a) with false.
        replace (num_oc n (insert n l)) with (S (num_oc n l)).
        reflexivity.
Qed.

Lemma perm_insertion: forall l' l a, perm l l' -> perm (a :: l) (insert a l').
Proof.
  intros.
  unfold perm. intros.
  simpl num_oc.
  destruct (n =? a) eqn: L0.
  Search( insert).
  * unfold perm in H.
    rewrite -> H.
    pose proof num_oc_insert. specialize (H0 l' n).
    rewrite <- H0. replace a with n.
    ** reflexivity. 
    ** apply beq_nat_true. assumption.
  * unfold perm in H.
    rewrite -> H.
    pose proof num_oc_insert_neq. specialize (H0 l' n a).
    rewrite <- H0.
    ** reflexivity. 
    ** assumption.
Qed.
Lemma ord_insercao_perm: forall l, perm l (insertion_sort l).
Proof.
  intros.
  induction l.
  * simpl.
    apply perm_refl.
  * unfold perm.
    intros.
    simpl.
    apply perm_insertion.
    assumption.
Qed.
  
Theorem correcao_ord_insercao: forall l, sorted (insertion_sort l) /\ perm l (insertion_sort l).
Proof.
  intros.
  induction l.
  * split.
    ** apply insertion_sort_sorts.
    ** apply ord_insercao_perm.
  * split.
    ** apply insertion_sort_sorts.
    ** apply ord_insercao_perm.
Qed.
(** Extração de código certificado *)

Require Extraction.

Recursive Extraction insertion_sort.
Extraction "insertion_sort.ml" insertion_sort.