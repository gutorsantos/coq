(** Considere o desafio lógico:
Em uma ilha moram apenas dois tipos de habitantes: os honestos, que sempre falam a verdade; e os desonestos, que sempre mentem. Você encontra dois habitantes desta ilha, digamos João e José. João diz que José é desonesto. José diz "Nem João nem eu somos desonestos". Você consegue determinar qual dos dois é honesto e qual é desonesto? *)

Section ex1.

(** Vamos modelar este problema com as seguintes variáveis proposicionais. *)  
Variables joao jose: Prop.

(** Assim, a variável joao é verdadeira se João for honesto, e false, se ele for desonesto. O mesmo raciocínio se aplica para a variável jose. *)

(** A afirmação: "João diz que José é desonesto" é codificada como: *)
Hypothesis H1: joao <-> ~jose.

(** José diz "Nem João nem eu somos desonestos" será simplificada neste momento como "eu e João somos honestos", que pode ser codificada da seguinte forma: *)
Hypothesis H2: jose <-> (joao /\ jose).

(** Agora prove que José é desonesto: *)
Lemma jose_desonesto: ~jose.
Proof.
  destruct H1 as [H11 H12].
  destruct H2 as [H21 H22].
  intro H.
  apply H21 in H.
  destruct H as [A B].
  apply H11 in A.
  apply A.
  exact B.
Qed.
  
End ex1.  
