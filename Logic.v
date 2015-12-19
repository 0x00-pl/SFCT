(** * Logic：Coq中的逻辑系统 *)

Require Export BasicTactics.


(** Coq内置的逻辑系统十分地小：仅有的基本操作只有[Inductive]
    定义，全称量化（[forall]）以及蕴含（[->]）三种，而所有其他常见的逻辑连接
    符——合取、析取、否定、存在量化，甚至相等，都能够用这三个基本操作表示。
    这一章将解释这种表示方法并展示如何使用之前我们接触到的证明策略来得出对含有
    这些连接词的命题的逻辑推理的范式。
*)

(* ########################################################### *)
(** * 命题 *)

(** 在之前的章节中我们已经看到许多对于某些事实的陈述（_命题_）以及给出证实
    它们的真实性的证据的方法（_证明_）。比方说，目前为止我们已经进行了许多命题的
    证明；比如说形如[e1 = e2]的_相等性命题_，蕴含式（[P -> Q]），以及量化命
    题（[forall x, P）的证明。  
*)


(** 在Coq中，所有存在被证明的可能的事物的类型是[Prop]。 *)

(** 下面是一个可以被证明的命题： *)

Check (3 = 3).
(* ===> Prop *)

(** 下面是一个无法被证明的命题： *)

Check (forall (n:nat), n = 2).
(* ===> Prop *)

(** 回想一下，[Check]能够让Coq显示某个表达式的类型。 *)

(* ########################################################### *)
(** * 证明与证据 *)

(** 在Coq中，命题与[nat]之类的类型有着同样的地位。就像自然数[0]，
    [1]，[2]是[nat]的元素一样，一个Coq命题[P]有它的_证明_作为它的元素。
    我们称这些元素为命题[P]的真实性的_证明项_（proof term）/
    _证明对象_（proof object）/_证据_（evidence）。
    在Coq中，当我们声明并且证明像这样的引理的时候：
Lemma silly : 0 * 3 = 0.  
Proof. reflexivity. Qed.
    我们在[Proof]和[Qed]关键字中使用的证明策略会告诉Coq如何构造出一个作
    为这个命题的元素的证明项。在这个示范中，命题[0 * 3 = 0]被由[mult]的定
    义（它声明了[0 * 3]能够被简化至[3]）和相等的_自反性_（它声明了[0 = 0]）
    构成的组合证明。
*)

(** *** *)

Lemma silly : 0 * 3 = 0.
Proof. reflexivity. Qed.

(** 我们可以用[Print]指令来查看Coq给某一命题构造的证明项： *)

Print silly.
(* ===> silly = eq_refl : 0 * 3 = 0 *)

(** 在这里，证明项[eq_refl]证实了它的相等性。（我们会在将来遇到更多的
    关于相等性的内容。*)

(** ** 蕴含_是_函数 *)

(** 就像我们能够以函数的形式实现自然数乘法一样：
[
mult : nat -> nat -> nat 
]
一个蕴含式[P -> Q]的证明项是一个_函数_；这个函数以命题[P]的证据作为输入，并且
生成一个[Q]的证据作为其输出。
*)     

Lemma silly_implication : (1 + 1) = 2  ->  0 * 3 = 0.
Proof. intros H. reflexivity. Qed.

(** 我们能够看到上面的引理的证明项确实是一个函数： *)

Print silly_implication.
(* ===> silly_implication = fun _ : 1 + 1 = 2 => eq_refl
     : 1 + 1 = 2 -> 0 * 3 = 0 *)

(** ** 定义命题 *)

(** 就像我们能够创建自定义的归纳性类型（比如说列表和二进制表示的
    自然数这些我们之前曾接触过的类型）一样，我们也能够创建_自定义的_命题。
    问题：你如何定义某个命题的意义？
*)

(** *** *)

(** 命题的意义由说明了如何从其他证据构造出证实命题为真的_证据_的
    _规则_和_定义_给出。

    - 一般而言，就像其他数据类型一样，规则是被归纳性地定义的。

    - 有时一个命题会在没有支持证据的情况下被宣称为真。这些命题被称作
      _公理_。

    在这一章以及接下来的章节中，我们将会看到更多的有关这些证明项如何产生效果的细节。
*)

(* ########################################################### *)
(** * 合取（逻辑"与"） *)

(** 命题[P]和[Q]的逻辑合取能够用包含一个构造子的[Inductive]定义表示。 *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

(** 在这个定义背后的直觉十分直接：为了构造[and P Q]的证据，我们需要提供
    P的证据和Q的证据。更为精确的说：
    - 如果[p]是[P]的证据且[q]是[Q]的证据，那么[conj p q]可以被作为[and P Q]的证据；
    - 而且这也是_唯一_给出[and P Q]的证据的方法。也即是说，如果谁给出了一个[and P Q]
      的证据，那么我们就能够得知这个证据一定是以[conj p q]这一形式出现的，其中[p]是
      [P]的证据，[q]是[Q]的证据。

   因为我们会经常使用合取，所以让我们来给它设定一个熟悉的中缀表示符： *)

Notation "P /\ Q" := (and P Q) : type_scope.

(** （[type_scope]这一标记告诉Coq系统这个符号将会出现在命题中而不是在值中。 *)

(** 判断构造子[conj]的"类型"： *)

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(** 注意，conj取四个输入——也就是命题P，命题Q，以及P和Q的证据——然后
    返回一个P/\Q的证据。 *)

(** ** "引入" 合取 *)
(** 除了从一个极小的基础建立起一切的简洁之外，这样定义合取还有另外一
    个好处：我们能够使用我们已经知道的证明策略来证明含有合取的陈述。
    比方说，如果目标是一个合取式，我们能够应用[conj]这个单独的构造子，
    而（这可以从[conj]的类型得知）这将证明当前的目标，并且将构成合取的两个
    部分留下作为两个需要分别证明的子目标。 *)

Theorem and_example : 
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  apply conj.
  - (* left *) reflexivity.
  - (* right *) reflexivity.  Qed.

(** 出于方便，我们可以用[split]作为[apply conj]的缩写形式。 *)

Theorem and_example' : 
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  split.
    - (* left *) reflexivity.
    - (* right *) reflexivity.  Qed.

(** ** "消去" 合取 *)
(** 相反地，[destruct]这一策略可以分析并计算出构造出上下文中的某个合取
    式所必须的证据，并且将这些证据以变量的形式添加到当前证明的上下文中。 *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [HP HQ]. 
  apply HP.  Qed.

(** **** Exercise: 1 star, optional (proj2)  *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  destruct H as [HP HQ]. 
  split.  
    - (* left *) apply HQ. 
    - (* right *) apply HP.  Qed.
  

(** **** Exercise: 2 stars (and_assoc)  *)
(** 注意在下面的这个证明中[destruct]使用的_嵌套模式_是如何将前提[H : P /\ (Q /\ R)]
    解构成[HP: P]，[HQ : Q]以及[HR : R]的。从这里开始完成这个证明： *)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]].
(* FILL IN HERE *) Admitted.
(** [] *)



(* ###################################################### *)
(** * Iff *)

(** 简便的"当且仅当"连接符只是两个蕴含式的合取： *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.  
  intros P Q H. 
  destruct H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. 
  destruct H as [HAB HBA].
  split.
    - (* -> *) apply HBA.
    - (* <- *) apply HAB.  Qed.

(** **** Exercise: 1 star, optional (iff_properties)  *)
(** 以上面的[<->]的对称性的证明（[iff_sym]）作为参考，证明它的自反性
    和传递性。 *)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *) Admitted.

(** 提示：如果在上下文中存在一个“当且仅当”形式的前提，你可以使用[inversion]
    将其分解为两个单独的蕴含式。（思考一下为什么可以这么做） *)
(** [] *)



(** Coq的某些策略会以特别的方式处理[iff]式并因此在使用这些命题
    进行推理时得以避开进行某些底层操控的需要。举例而言，[rewrite]除了
    可以配合等式使用之外，还可以配合[iff]式使用。*)

(* ############################################################ *)
(** * 析取（逻辑"或"）*)

(** ** 实现析取 *)

(** 析取（逻辑"或"）也可以被定义为一个归纳性命题。*)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

(** 判断构造子[or_introl]的"类型"：*)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(** 它有三个输入参数，也就是命题[P]，命题[Q]以及命题[P]的证据，然后
    输出命题[P \/ Q]的证据作为返回值。
    接下来看看[or_intror]的类型： *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(** 就像[or_introl]一样，只不过它要求的不是[P]的证据而是[Q]的证据。 *)

(** 直觉上，有两种给出命题[P \/ Q]的证据的方式：
    - 给出[P]的证据（并且声明你是在给[P]提供证据——这正是[or_introl]构造子
      的功能）；或者：
    - 给出[Q]的证据，并用构造子[or_intror]标记。*)

(** *** *)
(** 因为[P \/ Q]有两个构造子，对一个类型为[P \/ Q]的前提进行[destruct]
    将会生成两个子目标。 *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    - (* left *) apply or_intror. apply HP.
    - (* right *) apply or_introl. apply HQ.  Qed.

(** 从现在开始开始我们将会用两个作为缩写的策略：[left]和[right]来分别代替
    [apply or_introl]和[apply or_intror]。 *)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    - (* left *) right. apply HP.
    - (* right *) left. apply HQ.  Qed.





Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R. intros H. destruct H as [HP | [HQ HR]]. 
    - (* left *) split.
      + (* left *) left. apply HP.
      + (* right *) left. apply HP.
    - (* right *) split.
      + (* left *) right. apply HQ.
      + (* right *) right. apply HR.  Qed.

(** **** Exercise: 2 stars (or_distributes_over_and_2)  *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################### *)
(** ** 将[/\]和[\/]与[andb]和[orb]联系起来 *)

(** 我们已经在Coq的计算（[Type]）和逻辑（[Prop]）领域中看到了几个
    使用了模拟结构的地方。这里是另外一个：布尔运算操作符[andb]和[orb]，很
    明显地，是对逻辑连接符[/\]和[\/]的模拟。通过以下这些说明了如何将与
    [andb]和[orb]在某些输入上的行为相关的知识转化成与这些输入相关的命题
    性的事实的定理，这种模拟能够变得更加精确。*)

Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    - (* b = true *) destruct c.
      + (* c = true *) apply conj. reflexivity. reflexivity.
      + (* c = false *) inversion H.
    - (* b = false *) inversion H.  Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct H.
  rewrite H. rewrite H0. reflexivity. Qed.

(** **** Exercise: 2 stars, optional (andb_false)  *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 2 stars, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 2 stars, optional (orb_false_elim)  *)
Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ################################################### *)
(** * 矛盾式 *)

(** 在Coq中矛盾式可以用一个没有构造子的归纳定义的命题表示。*)

Inductive False : Prop := . 

(** 在直观上[False]是一个无法给出证据的命题。*)


(** 因为[False]没有构造子，对一个类型为[False]的假设进行反演将不会
    生成任何子目标，由此我们得以立即证明任何目标。*)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

(** 它是如何产生效果的？[inversion]策略将[contra]分解成各个可能出现的情况
    并为每一种情况生成一个子目标。因为[contra]作为[False]的证据_并没有_
    可能出现的情况，因此这里没有可能出现的子目标，而证明因此得以完成。 *)

(** *** *)
(** 相反地，证明[False]的唯一方法就是让当前上下文中存在谬误或者矛盾： *)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(** 事实上[False_implies_nonsense]的证明并不与任何特定的被证明的谬误有关，
    因此它可以很容易地被一般化并且变得可以用在任意命题[P]上：*)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra.  Qed.

(** _ex falso quodlibet_是拉丁文，它的字面意思是："从谬误出发你能证明
    任何你想要证明的命题"。这一定理也被称作_爆炸原理_。 *)


(* #################################################### *)
(** ** 真值 *)

(** 因为我们已经在Coq中定义了矛盾式，有人也许会想知道我们是否能够用
    相同的方式定义真值。我们能够这么做。 *)

(** **** Exercise: 2 stars, advanced (True)  *)
(** 将[True]定义为一个归纳定义的命题。（从直觉上说[True]应该是一个
    能平凡地给出证据的命题。） *)

(* FILL IN HERE *)
(** [] *)

(** 然而不像我们将会经常使用的[False]，[True]极少被使用到。就自身而言，
    它是个过于平凡（因此也变得无趣）的证明目标，在作为证明的前提时也不包含任何
    有用的信息。但是在定义复杂的、使用到了条件式的[Prop]的时候，或者作为
    高阶[Prop]的参数的时候，[True]是十分有用的。 *)

(* #################################################### *)
(** * 否定 *)

(** 命题[P]的逻辑上的补写作[not P]，或者使用缩写形式：[~P]： *)

Definition not (P:Prop) := P -> False.

(** 在这背后的直觉是：如果[P]不为真，则任何命题，甚至[False]，
    都能在假设[P]的情况下证明。 *)

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

(** 在习惯在Coq中处理否定之前仍需要一点练习。有时即使你完全明白
    为什么某些命题为真，在最开始的时候通过适当的设置让Coq系统接受这一
    点也是有一点困难的。这里有一些常见事实的证明，作为在这之前的热身。 *)

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

(** *** *)
Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  (* WORKED IN CLASS *)
  intros P Q H. destruct H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, advanced (double_neg_inf)  *)
(** 写下命题[double_neg]的非形式证明：
   _定理_: 对于任意命题[P]，[P]蕴含[~~P]。
   _证明_:
(* FILL IN HERE *)
   []
*)

(** **** Exercise: 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, advanced (informal_not_PNP)  *)
(** 写下命题[forall P : Prop, ~(P /\ ~P)]的非形式证明 *)

(* FILL IN HERE *)
(** [] *)

(** *** 构造性逻辑 *)
(** 注意，有些在经典逻辑下成立的定理在Coq的构造性逻辑中是不可证的。
    例如说，让我们看看下面这个证明是如何无法进行下去的……*)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H. 
  (* 然后呢？我们没有办法基于[P]的证据“发明”出命题[~P]的证据。*) 
  Abort.
  (** **** Exercise: 5 stars, advanced, optional (classical_axioms)  *)
(** 对于那些喜欢挑战的人，这里有一个摘自Coq'Art（第123页）的练习。
    下面是五条常常被认为是刻画了经典逻辑（与Coq"内置"的构造性逻辑
    相对）的语句。在Coq中我们无法证明它们，但是如果我们希望处理在
    经典逻辑下的问题，我们能够将它们之中的任意一句作为一个没有证
    明的公理加进Coq之中而不损它的一致性。试证这五个命题互相等价。 *)

Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q). 

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (excluded_middle_irrefutable)  *)
(** 这一定理蕴含了一个事实：对于任意_特定的_命题[P]，可以添加任意一个可判定性
    公理（比如说排中律的一个实例）而不损安全性。为什么？因为我们不能证明这样一
    个公理的否定；如果我们能够这么做，我们将会同时有[~ (P \/ P)]和[~ ~ (P \/ ~P)]，
    而这是一个矛盾。*)

Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).  
Proof.
  (* FILL IN HERE *) Admitted.


(* ########################################################## *)
(** ** 不等式 *)

(** 声明[x <> y]实际上就是在声明[~(x = y)]. *)

Notation "x <> y" := (~ (x = y)) : type_scope.

(** 因为不等式包含了一个否定，所以学会流畅地处理不等式也需要一点
    练习。这里是一个十分有用的技巧。如果你正试图证明一个荒谬的目标（
    比如说，当前待证的目标是[false = true]），可以应用[ex_falso_quodlibet]
    将其转换成[False]，这样可以更简单地利用在上下文当中的有着[~P]形
    式的假设——比方说，形如[x <> y]的假设。*)

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  - (* b = true *) reflexivity.
  - (* b = false *)
    unfold not in H.  
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.






(** **** Exercise: 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** $Date$ *)

