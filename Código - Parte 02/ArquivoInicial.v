From Coq Require Import Unicode.Utf8_core.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssreflect.ssrnat.
Require Export Arith.
Require Export Bool.
Require Export PeanoNat.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Printing Coercions.

(*  Anotações do que fazer:
    - Falar com a Karina sobre o que falta das correções do TCC1001
    - Verificar o guia de contribuiçãoes para a biblioteca
    - Inverso multiplicativo
    - Propriedades de Congruência
    - Teorema de Euler-Fermat
    - Pequeno Teorema de Fermat
    - O que fazer sobre congruência de grau 2?
        -- Critério de Euler
        -- Símbolo de Legendre
    - Entender o conceito de "prova não computacional" (termo do Paulo Torrens)

    Anotações sobre alguns mecanismos importantes:
    - "Section": serve para delimitar um escopo que será afetado por declarações como Variable, Hypothesis, Context, Let, Let Fixpoint e Let CoFixpoint, entretanto as variáveis destas declarações continuam sendo válidas fora da "Section" porém não são instanciadas automaticamente no contexto das provas (ver exemplo em https://coq.inria.fr/doc/V8.15.2/refman/language/core/sections.html)
        -- Aviso: é uma boa prática usar "Section" para diminuir o número de declarações repetidas em um bloco de código.

    - "Modules": para definição de módulo temos que definir o seguinte:
        -- "Acess path": é denotado por "p" e pode ser uma variável de módulo "X" ou, sendo "p'" um "acess path" e "id" um identificador, então "p'.id" é um "acess path".
        -- "Structure element": é denotado por "e" e é uma definição de uma "constant", uma hipótese, uma definição indutiva, uma definição de um módulo, um alias de um módulo ou um tipo de abreviação de módulo.
        -- restante em https://coq.inria.fr/doc/V8.18.0/refman/language/core/modules.html. 
*)

Section s1.
    Variables (T : Type) (A : Type).
    Variables (f : T -> A -> A).
    Implicit Types x : T.
End s1.

Module M1.
    Definition Z := Prop.
    Module M2.
        Inductive T := C.
        Definition U := nat.
    End M2.
    Local Definition X := bool.
End M1.

Module M3.
    Import M1.
        Check Z.
        Fail Check T.
        Fail Check U.
        Check M2.T.
        Check M2.U.
        Fail Check X.
        Check M1.X.
End M3.

Module Capitulo1.


End Capitulo1.