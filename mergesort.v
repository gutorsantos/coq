(* Universidade de Brasília
    Instituto de Ciências Exatas 
    Departamento de Ciência da Computação
    Lógica Computacional 1 - turma B - 2020/2 
    Professor: Flávio L. C. de Moura
    Estagiário de docência: Gabriel Ferreira Silva *)

Require Import Arith List Recdef.
Require Import Coq.Program.Wf.


Inductive sorted :list nat -> Prop :=
  | nil_sorted : sorted nil
  | one_sorted: forall n:nat, sorted (n :: nil)
  | all_sorted : forall (x y: nat) (l:list nat), sorted (y :: l) -> x <= y -> sorted (x :: y :: l).


Definition le_all x l := forall y, In y l -> x <= y.
Infix "<=*" := le_all (at level 70, no associativity).


Lemma tail_sorted: forall l a, sorted (a :: l) -> sorted l.
Proof.
  intro l.
  case l.
  - intros a H.  
    apply nil_sorted.  
  - intros n l' a H.  
    inversion H; subst.
    assumption.  
Qed.  


(** *** Questão 1: 😎️**) 
(** A primeira questão consiste em provar que se [a] é menor ou igual a todo elemento de [l], e [l] é uma lista ordenada então a lista (a :: l) também está ordenada: *)

Lemma le_all_sorted: forall l a, a <=* l -> sorted l -> sorted (a :: l).
Proof.
  intro l.
  case l.
  - intros a menor ordenado_nulo.
    apply one_sorted.
  - intros n l0 a menor ordenado.
    apply all_sorted.
    + assumption.
    + unfold le_all in menor.
      apply menor.
      apply in_eq. (** pesquisamos a estrutura do In**)
Qed.

(** O lema a seguir é bem parecido com o lema [tail_sorted] visto anteriormente, mas ao invés de remover o primeiro elemento de uma lista ordenada, este lema remove o segundo elemento de uma lista ordenada (com pelo menos dois elementos), e após esta remoção a lista resultante ainda está ordenada. Veja que a prova é por análise de casos. *)

Lemma remove_sorted: forall l a1 a2, sorted (a1 :: a2 :: l) -> sorted (a1 :: l).
(* begin hide *)
Proof.
  intro l; case l.
  - intros a1 a2 H.
    apply one_sorted.
  - intros n l' a1 a2 H.
    inversion H; subst.
    inversion H2; subst.
    apply all_sorted.
    + assumption.
    + apply Nat.le_trans with a2; assumption.
Qed.
(* end hide *)

(** *** Questão 2 😏️*)
(** A segunda questão consiste em provar que, se a lista [(a :: l)] está ordenada então [a] é menor ou igual a todo elemento de [l]. A dica é fazer indução na estrutura da lista [l]. *)

Lemma sorted_le_all: forall l a, sorted(a :: l) -> a <=* l.
Proof.
  induction l.
  - intros a ordenada n ta_dentro.
    (*caso seja difícil explicar o destruct, usar contradiction.*)
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
    specialize(H2 y H). (** aplica a hipótese e substitui o resultado **)
    apply Nat.le_trans with (m := a); assumption.

Qed.

(** ** Segunda parte: *)
(** Agora definiremos a noção de permutação e apresentaremos 
alguns lemas relacionados. A noção de permutação que será utilizada 
neste projeto é baseada no número de ocorrências de um elemento.
 A função recursiva [num_oc n l] retorna o número de ocorrências do 
natural [n] na lista [l]. A palavra reservada [Fixpoint] é usada para 
definir funções recursivas, enquanto que [Definition] é usada para funções
 não-recursivas como foi o caso do predicado [le_all] visto anteriormente. *)

Fixpoint num_oc n l  :=
  match l with
    | nil => 0
    | h :: tl =>
      if n =? h then S(num_oc n tl) else  num_oc n tl
  end.

(** Dizemos então que duas listas [l] e [l'] são permutações uma da outra
 se qualquer natural [n] possui o mesmo número de ocorrências em ambas as 
listas. *)

Definition perm l l' := forall n:nat, num_oc n l = num_oc n l'.

(** A reflexividade é uma propriedade que pode ser obtida a partir 
desta definição: uma lista é sempre permutação dela mesma. *)

Lemma perm_refl: forall l, perm l l.
(* begin hide *)
Proof.
intro l. unfold perm. intro. reflexivity.
Qed.
(* end hide *)

(** O lema a seguir é um resultado técnico, 
mas que pode ser utilizado em provas futuras. 
Ele diz que o número de ocorrências de um natural [n] 
no append das listas [l1] e [l2] (notação [l1 ++ l2]) é igual
 à soma das ocorrências de [n] em [l1] com as ocorrências de [n] em [l2]: *)

Lemma num_oc_append: forall n l1 l2, num_oc n l1 + num_oc n l2 = num_oc n (l1 ++ l2).
Proof.
  intros. induction l1.
  - simpl num_oc. trivial.
  - simpl. destruct (n =? a).
    + rewrite <- IHl1. apply Peano.plus_Sn_m.
    + assumption.
Qed.

(** *** Terceira parte: *)
(** Nesta parte definiremos o algoritmo mergesort. 
Iniciaremos pela função [merge] que faz a etapa de combinação 
descrita anteriormente. A função [merge] recebe como argumento 
um par de listas de naturais ordenadas e gera uma nova lista ordenada
 contendo exatamente os elementos das duas listas recebidas como argumento.
 Iniciamos então com a definição do predicado [sorted_pair_lst] que recebe 
um par de listas e retorna a conjunção expressando o fato de que cada lista 
que compõe o par está ordenada: *)

Definition sorted_pair_lst (p: list nat * list nat) :=
sorted (fst p) /\ sorted (snd p).

(** Agora necessitamos de uma métrica para definirmos a função [merge]. 
Esta métrica consiste no tamanho do par que contém duas listas e é 
definido como sendo a soma do comprimento de cada uma das listas: *)

Definition len (p: list nat * list nat) :=
   length (fst p) + length (snd p).

(** Agora podemos definir a função recursiva [merge]. 
Dado um par [p] de listas de naturais, se alguma das listas
 que compõem este par é a lista vazia então a função simplesmente
 retorna o outro elemento do par. Quando ambas as listas que compõem o
 par são não-vazias então os primeiros elementos de cada lista são 
comparados e o menor deles será o colocado na lista final, e o processo
 se repete recursivamente para o par sem este menor elemento. Para
 garantirmos que esta função está bem definida, precisamos que as 
chamadas recursivas se aproximem do ponto de parada (chamadas sem recursão)
 que ocorre quando alguma das listas do par é a lista vazia. Esta garantia 
é dada pelo medida (ou métrica) definida anteriormente: o comprimento do par 
que [merge] recebe como argumento: *)
(* printing *)
(** printing <=? $\leq ?$ *)

Function merge (p: list nat * list nat) {measure len p} :=
match p with
  | (nil, l2) => l2
  | (l1, nil) => l1
  | ((hd1 :: tl1) as l1, (hd2 :: tl2) as l2) =>
if hd1 <=? hd2 then hd1 :: merge (tl1, l2)
      else hd2 :: merge (l1, tl2)
   end.

(** A palavra reservada [Function] é utilizada para definir funções 
recursivas mais sofisticadas, ou seja, para funções recursivas cuja 
boa definição não pode ser inferida automaticamente pelo Coq. Neste caso,
 precisamos provar que nossa medida realmente decresce nas chamadas recursivas. *)
(* begin hide *)
Proof.
  - intros. unfold len. unfold fst. unfold snd. simpl length.
    apply plus_lt_compat_r. auto.
  - intros. unfold len. unfold fst. unfold snd. simpl length.
    apply plus_lt_compat_l. auto.  
Qed.
(* end hide *)

(** O lema [merge_in] a seguir será bastante útil em provas futuras. 
Ele estabelece que se [y] é um elemento da lista [merge p] então [y] 
está em alguma das listas que compõem o par [p]. *)

Lemma merge_in: forall y p, In y (merge p) -> In y (fst p) \/ In y (snd p).
(* begin hide *)
Proof.
intros. functional induction (merge p).
  - right. unfold snd. assumption.
    - left. unfold fst. assumption.
    - simpl in H. destruct H as [H1 | H2].
    + left. unfold fst. unfold In. left. assumption.
        + destruct IHl.
        * assumption.
          * left. unfold fst. unfold fst in H. simpl In. right. assumption.
          * right. simpl. simpl in H. assumption.
    - simpl in H. destruct H as [H1 | H2].
    + right. simpl snd. simpl In. left. assumption.
        + destruct IHl.
        * assumption.
          * left. unfold fst. unfold fst in H. assumption.
          * right. simpl. simpl in H. right. assumption.
Qed.
(* end hide *)

(** *** Questão 3 *)
(** Esta questão é a mais importante do projeto.🤣️ Ela estabelece que se as
 listas que compõem o par [p] estão ordenadas então [merge p] também está 
ordenada. Como [merge] é uma função recursiva mais sofisticada, as 
propriedades envolvendo esta função também terão provas mais complexas. 
Como você pode ver, esta prova é composta de quatro casos, dos quais dois 
estão provados, e dois fazem parte do exercício. Cada caso deixado como 
exercício é semelhante ao caso anterior, então use estas subprovas que estão
 feitas como ideias para completar a prova deste teorema. Os lemas anteriores
 também podem ser úteis! *)

Theorem merge_sorts: forall p, sorted_pair_lst p -> sorted (merge p).
(* begin hide *)
Proof.
  intro p. functional induction (merge p).
  - unfold sorted_pair_lst. intro. destruct H.
    unfold snd in H0. assumption.
  - unfold sorted_pair_lst. intro. destruct H.
    assumption.
  - intro. apply le_all_sorted.
    + unfold le_all. intro. intro. apply merge_in in H0.
      destruct H0 as [H1 | H2].
      * simpl fst in H1. unfold sorted_pair_lst in H. destruct H as [H2 H3].
        simpl fst in H2. apply sorted_le_all in H2. unfold le_all in H2.
        apply H2. assumption.    
      * simpl snd in H2. apply Nat.le_trans with hd2.
        -- apply Nat.leb_le. assumption.
        -- unfold sorted_pair_lst in H. destruct H as [H3 H4]. simpl snd in H4.
           apply sorted_le_all in H4. simpl In in H2. destruct H2 as [H5 | H6].
           ** rewrite H5. trivial.
           ** unfold le_all in H4. apply H4. assumption.
    + apply IHl. unfold sorted_pair_lst. split.
      * simpl fst. unfold sorted_pair_lst in H. destruct H as [H1 H2].
        simpl fst in H1. apply tail_sorted in H1. assumption.
      * simpl snd. unfold sorted_pair_lst in H. destruct H as [H1 H2].
        simpl snd in H2. assumption.  
  - intro.
    apply le_all_sorted.
    + unfold le_all.
      intro. intro.
      apply merge_in in H0.
      destruct H0 as [H1 | H2].
      apply leb_complete_conv in e0.
      * simpl fst in H1. unfold sorted_pair_lst in H. destruct H as [H2 H3].
        simpl fst in H2. apply sorted_le_all in H2. unfold le_all in H2.
        simpl snd in H3.
        Search(In _ (_ :: _)).
        apply in_inv in H1.
        destruct H1.
        -- subst.
           Search(_ < _ -> _ <= _).
           apply Nat.lt_le_incl.
           assumption.
        --  apply H2 in H.
            Search(le_trans).
            apply Nat.le_trans with (m := hd1).
            *** apply Nat.lt_le_incl.
                assumption.
            *** assumption.
     * apply leb_complete_conv in e0.
       simpl snd in H2. unfold sorted_pair_lst in H. destruct H as [H22 H33].
       simpl snd in H33. apply sorted_le_all in H33. unfold le_all in H33.
       apply H33 in H2.
       assumption.
   + destruct H.
     simpl snd in H0.
     apply tail_sorted in H0.
     apply IHl.
     simpl fst in H.
     unfold sorted_pair_lst.
     simpl fst.
     simpl snd.
     split.
     * assumption.
     * assumption.
Qed.

(** Agora vamos definir a função [mergesort] que recebe uma lista [l] como 
argumento. Se esta lista for vazia ou unitária, o algoritmo não faz nada. 
Caso contrário, a lista é dividida ao meio, cada sublista é ordenada 
recursivamente, e no final as sublistas ordenadas são fundidas com a função
 [merge]. *)

Function mergesort (l: list nat) {measure length l}:=
  match l with
  | nil => nil
  | hd :: nil => l
  | hd :: tail =>
     let n := length(l) / 2 in
     let l1 := firstn n l in
     let l2 := skipn n l in
     let sorted_l1 := mergesort(l1) in
     let sorted_l2 := mergesort(l2) in
     merge (sorted_l1, sorted_l2)
  end.

(** Analogamente à definição da função [merge], precisamos 
provar que [mergesort] está bem definida. *)
(* begin hide *)
Proof.
- intros. rewrite skipn_length. apply Nat.sub_lt.
  + apply Nat.lt_le_incl. apply Nat.div_lt.
    * simpl. apply Nat.lt_0_succ.
      * apply Nat.lt_1_2.
    + apply Nat.div_str_pos. simpl. split.
    * apply Nat.lt_0_2.
      * apply Peano.le_n_S. apply Peano.le_n_S. apply Peano.le_0_n.  
  - intros. rewrite firstn_length. rewrite min_l.
  + apply Nat.div_lt.
    * simpl. apply Nat.lt_0_succ.
      * apply Nat.lt_1_2.
    + apply Nat.lt_le_incl. apply Nat.div_lt.
    * simpl. apply Nat.lt_0_succ.
      * apply Nat.lt_1_2.  
Defined.
(* end hide *)

(** *** Questão 4 *)
(** Agora prove que a função [mergesort] realmente ordena a lista recebida 
como argumento. *)

Theorem mergesort_sorts: forall l, sorted (mergesort l).
Proof.
  intros.
  functional induction (mergesort l).
  - apply nil_sorted.
  - apply one_sorted.
  - destruct IHl0.
    * apply merge_sorts.
      unfold sorted_pair_lst.
      simpl.
      split.
      ** apply nil_sorted.
      ** assumption.
    * apply merge_sorts.
      unfold sorted_pair_lst.
      simpl.
      split.
      ** apply one_sorted.
      ** assumption.
    * apply merge_sorts.
      unfold sorted_pair_lst.
      simpl.
      split.
      ** apply all_sorted; assumption.
      ** assumption.
Qed.



(** O lema a seguir é um lema técnico que pode ser usado nas questões 
seguintes. Este lema estabelece que o número de ocorrências de um elemento 
[n] no par de listas [p] é igual à soma das ocorrências de [n] em cada lista 
do par. *)

Lemma merge_num_oc: forall n p, num_oc n (merge p) = num_oc n (fst p) + num_oc n (snd p).
(* begin hide *)
Proof.
intros. functional induction (merge p).
  - simpl fst. simpl snd. simpl num_oc. trivial.
  - simpl fst. simpl snd. simpl num_oc. trivial.
  - simpl fst. simpl snd. simpl num_oc at 1 2. destruct (n =? hd1).
    + rewrite IHl. apply Peano.plus_Sn_m.
    + rewrite IHl. simpl fst. simpl snd. trivial.
  - simpl fst. simpl snd. simpl num_oc at 1 3. (destruct (n =? hd2)).
      + rewrite IHl. simpl fst. simpl snd. apply Peano.plus_n_Sm.
      + rewrite IHl. simpl fst. simpl snd. trivial.
Qed.
(* end hide *)

(** *** Questão 5 *)
(** Prove que [mergesort] gera uma permutação da lista recebida como argumento. *)

(**
intro.
  functional induction (mergesort l).
  - apply perm_refl.
  - apply perm_refl.
  - intros n.
    unfold merge.
    destruct mergesort.
    destruct merge_terminate.
    rewrite merge_num_oc.
**)

Theorem mergesort_is_perm: forall l, perm l (mergesort l).
Proof.
  intro.
  functional induction (mergesort l).
  - apply perm_refl.
  - apply perm_refl.
  - unfold perm. intros n.
    rewrite merge_num_oc.
    unfold fst. unfold snd.
    replace (num_oc n (mergesort (firstn (length (hd :: tail) / 2) (hd :: tail)))) with (num_oc n (firstn (length (hd :: tail) / 2) (hd :: tail))) .
    replace (num_oc n (mergesort (skipn (length (hd :: tail) / 2) (hd :: tail)))) with (num_oc n (skipn (length (hd :: tail) / 2) (hd :: tail))) .
    + rewrite num_oc_append.
      Search firstn.
      rewrite firstn_skipn.
      reflexivity.
    + destruct mergesort.
      * unfold perm in IHl1.
        rewrite -> IHl1.
        reflexivity.
      * unfold perm in IHl1.
        rewrite -> IHl1.
        reflexivity.
    + unfold perm in IHl0.
      rewrite -> IHl0.
      reflexivity.
Qed.

(** *** Questão 6 *)
(** Por fim, prove que [mergesort] é correto. *)

Theorem mergesort_is_correct: forall l, perm l (mergesort l) /\ sorted (mergesort l).
Proof.
  intros.
  split.
  - apply mergesort_is_perm.
  - apply mergesort_sorts.
Qed.

(** ESSE TRABALHO VALE 10 HEIN? 😏️😈️🔥️🔥️🔥️🔥️🔥️😎️*)

(** ** Extração de código *)
(** Uma das vantagens de formalizar um algoritmo é que você pode extrair o código certificado do algoritmo. O algoritmo de extração garante que o código extraído satisfaz todas as propriedades provadas. Vamos extrair automaticamente o código do algoritmo mergesort? *)

Require Extraction.

(** As opções de linguagens fornecidas pelo Coq são: OCaml, Haskell, Scheme e JSON. *)

Extraction Language OCaml.

(** Extração apenas da função [mergesort]: *)

Extraction mergesort.

(** Extração do programa inteiro: *)

Recursive Extraction mergesort.

(** Extração para um arquivo: *)

Extraction "mergesort" mergesort.