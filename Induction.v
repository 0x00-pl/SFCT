(** * Induction: 用归纳法证明 *)


(** 下面这行代码会导入你在之前章节做的所有定义 *)

Require Export Basics.

(** 为了让它起作用，你需要用[coqc]把[Basics.v]编译成[Basics.vo]。
    （这就好像你把.java文件编译成.class文件，或者把.c文件编译成.o文件。）

    有两种方式编译文件：

     - CoqIDE:

         打开[Basics.v].
         在 "Compile" 菜单, 点击 "Compile Buffer".

     - 命令行:

         运行 [coqc Basics.v]

    *)

(* ###################################################################### *)
(** * 为分类命名 *)

(** 现在有个问题是没有一个明确的命令让证明从一个分类跳到另一个分类，这让证明
    脚本很难阅读。在一个极长的有很多分支的证明中，你甚至会迷失方向。（想象一下，
    你试着记住一个内部分类的前五个子目标，这个分类的外边又有七个分类……）条理清晰
    地使用缩进与注释可能会有点帮助，但是更好的方法还是使用[Case]策略。*)

(** [Case]不是Coq内置的策略：我们需要自己定义。
    现在还没必要理解它是怎么运作的 ———— 你可以跳过下面的示例定义 ———— 这里用了
    一些我们还没提到的Coq的功能：字符串库 （用在引用字符串的具体语法上）和
    [Ltac]命令 ———— 用来让我们自定义策略。感谢Aaron Bohannon做的这些工作！*)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
(** 这是一个[Case]的例子。一步一步运行然后观察上下文的变化（CoqIde的右上角）*)

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".  (* <----- 看这 *)
    reflexivity.
  Case "b = false".  (* <---- 再看这 *)
    rewrite <- H.
    reflexivity.
Qed.

(** [Case]的作用非常直接：它简单地在当前目标的上下文里加上一个我们选择的字符串
    （之前用标识符“Case”标注的）。当子目标生成的时候，这个字符串会被带进目标的上下文。
    当最后一个子目标证明完毕、下一个顶级目标被激活，这个字符串就会在上下文中消失然后我
    们会发现这个分类在我们引入的地方完成了。 另外，这还起到了使纠错更清晰的作用。比方说
    我们试着运行一个新的[Case]策略，然而上一个分类的字符串还在上下文里，显然我们有哪里
    出错了。

    对于嵌套的分类讨论（比方说，我们用了[destruct]之后在分支里又用了一个[destruct]，
    这时我们应该用[SCase]（subcase）策略来代替[Case]。*)

(** **** 练习: 2星 (andb_true_elim2)  *)
(** 证明[andb_true_elim2], 当你使用[destruct]时用[Case]（或[SCase]）来标记*)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (*在此填写*) Admitted.
(** [] *)

(** 在Coq中的证明没有固定书写格式 ———— 比方说分行书写，并且用缩进来表示嵌套结构。
    但是在有多个子目标的情况下你把[Case]策略放到每个子目标的行首做一个清晰的标记，
    那样不管你的嵌套有多么复杂，证明看上去都一目了然。

    关于每行的长度，在这里我也想给出一点建议（可能你早就知道了）。Coq的初学者有时
    会走极端，要么一行只写一个策略，要么整个证明都挤到一行。一个好的风格应该是折中的。
    特别地，一个合理的习惯是每行不要超过80个字符。超过80个字符的话一行将会非常难
    读并且不方便显示与打印。许多文本编辑器都有辅助你控制行长度的功能。*)

(* ###################################################################### *)
(** * 用归纳法来证明 *)

(** 我们在上一章简单地证明了[0]对于[+]是一个左单位元。实际上它也是个右单位元…… *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** …… 它不能用同样简单的方式证明。只用[reflexivity]不起作用：这里的[n]在[n + 0]
  中是一个任意的未知数，所以[+]的定义中的[match]不能被化简。*)

Proof.
  intros n.
  simpl. (* 毫无变化！ *)
Abort.

(** *** *)

(** 使用[destruct n]来分类推理不会让我们更进一步：分类讨论的[n = 0]分支可以通过，
   不过在[n = S n']分支，对于[n']我们会遇到同样的问题。我们可以继续用[destruct n']，
   但是[n]是一个任意大的数，要是我们如此反复，那我们永远也证明不完。*)

Theorem plus_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as[| n'].
  Case "n = 0".
    reflexivity. (* 目前看上去还没什么问题…… *)
  Case "n = S n'".
    simpl.       (* ……但是在这里我们又卡住了 *)
Abort.

(** *** *)

(** 为了证明这个定理 ———— 事实上，为了证明大多数跟数、列表以及其他归纳定义的集合有关
    的有趣的定理 ———— 我们需要一个更强大的推理规则：_归纳法_。

    回忆一下（高中学到的）自然数的归纳规则：如果[P(n)]是某个包含自然数[n]的命题，然
    后我们想证明P对_所有的_自然数[n]成立，我们可以像这样来推理：
        - 证明[P(0)]成立；
        - 证明对于任意的[n']，如果[P(n')]成立，那么[P(S n')]也成立；
        - 综上：对任意的[n]，[P(n)]都成立。

    在Coq里，思路是一样的，不过顺序要反过来：我们先设定目标为证明[P(n)]对任意的[n]成
    立，然后把这个目标分解成两个子目标（使用[induction]策略）：先证明[P(O)]再证明
    [P(n') -> P(S n')]。现在我们就试着用归纳法证明这个定理。*)

(** *** *)

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".     reflexivity.
  Case "n = S n'".  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** 就像[destruct]，[induction]策略使用[as ...]从句来指定引入子目标的变量名。在
    第一个分支，[n]被[0]代替，于是目标变成了[0 + 0 = 0]，这直接化简就可以证明。第二
    部分中，[n]被替换成[S n']，这样假设[n' + 0 = n']被加入上下文中（这个假设被命名
    为IHn'，也就是“the Induction Hypothesis for [n]”（n的归纳假设））。在这个
    分支中的目标变成了[(S n') + 0 = S n']，化简后变为[S (n' + 0) = S n']。这
    很容易从归纳假设中得出。 *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (*课堂任务*)
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** **** 练习: 2星 (basic_induction)  *)

(** 用归纳法证明下面的引理。你可能需要用到之前证明的结果。 *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (*在此填写*) Admitted.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (*在此填写*) Admitted.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (*在此填写*) Admitted.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (*在此填写*) Admitted.
(** [] *)

(** **** 练习: 2星 (double_plus)  *)

(** 考虑下面这个把参数翻倍的函数： *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** 使用归纳法来证明这个关于[double]的简单事实： *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  (*在此填写*) Admitted.
(** [] *)


(** **** 练习: 1星 (destruct_induction)  *)
(** 请简洁地解释策略[destruct]与[induction]的不同。

(*在此填写*)

*)
(** [] *)


(* ###################################################################### *)
(** * 证明里的证明 *)


(** 在Coq中，就像在非形式化的数学中，一个冗长的证明经常被拆分成一系列小定理然后再证明。
    但是有时一个证明需要各式各样的甚至有点琐碎的（适用面太狭窄）依据以致于给他们分别起
    名字实在是太烦人了。在这种情况下，在用到它们的地方能简单地提出并证明一些“子定理”
    就显得非常方便了。[assert]策略就能帮我们做到这点。举个例子，我们早些时候证明的
    [mult_0_plus]定理用到了一个在它之前的[plus_O_n]定理。我们可以用[assert]策略
    把[plus_O_n]的声明和证明内嵌进去： *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.  Qed.

(** [assert]策略引入了两个子目标。第一个是断言本身——在他前面加上了[H:]，给他命名为[H]。
    （注意我们也可以像上面用[destruct]和[induction]那样用[as]，比方说[assert (0
    + n = n) as H]。另外注意下我们也用[Case]给这个断言的证明做了个标记。这样既增加了
    可读性，又可以判断什么时候我们对断言的证明结束了——观察["Proof of assertion"]何时
    从上下文消失。）第二个目标和我们加入[assert]之前的那个目标相同，唯一不同的是，上下文
    里多了一个假设[H]，它告诉我们[0 + n = n]。于是，[assert]生成了一个子目标——我们必
    须证明的断言，和另一个子目标——我们最初要证明的那个目标，附带着已经证毕的断言。 *)

(** [assert]在许多情况下都非常顺手。比方说，假设我们想证明[(n + m) + (p + q) = (m
    + n) + (p + q)]。[=]两边唯一的不同就是第一个括号里[+]两边的参数[m]和[n]的位置
    交换了。看上去我们可以用加法交换律（[plus_comm]）把等式左边重写成右边的形式。但是
    [rewrite]策略对它能重写的位置有些捉急。原式（等号左边的或右边的）用了三个[+]，但是
    使用[rewrite -> plus_comm]只会改变最外边的那个。 *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* 我们只是需要交换[n + m]变成[m + n]……
     貌似plus_comm应该搞些小技巧！ *)
  rewrite -> plus_comm.
  (* 没作用……Coq重写了错误的加法式！ *)
Abort.

(** 为了让[plus_comm]作用在我们想让他作用的地方，我们可以引入一个内部引理：[n + m
    = m + n]（只是针对我们引入的这个[m]和[n]），用[plus_comm]证明这个引理，然后用
    这个引理来完成我们想要的重写。 *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.  Qed.

(** **** 练习: 4星 (mult_comm)  *)
(** 使用[assert]来辅助这个定理的证明。请不要用归纳法。*)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (*在此填写*) Admitted.


(** 现在证明乘法的交换律。（你可能需要定义并证明一个独立的子定理以用在这个定理的证明中。）
    你可能会发现[plus_swap]很趁手。*)

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  (*在此填写*) Admitted.
(** [] *)

(** **** 练习: 2星, optional (evenb_n__oddb_Sn)  *)

(** 证明下面的简单事实： *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  (*在此填写*) Admitted.
(** [] *)

(* ###################################################################### *)
(** * 更多习题 *)

(** **** 练习: 3星, 可选 (more_exercises)  *)
(** 拿出一张纸。对下列每一个定理，先仔细思考是否(a)它可以只用化简与重写来证明，(b)它还
    需要分类讨论（[destruct]），或者(c)它还需要归纳法。写下你的预测，然后补上你的证明。
    （不需要交这张纸。这只是用来鼓励你们干活之前多思考！） *)

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  (*在此填写*) Admitted.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (*在此填写*) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (*在此填写*) Admitted.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  (*在此填写*) Admitted.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (*在此填写*) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (*在此填写*) Admitted.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (*在此填写*) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (*在此填写*) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (*在此填写*) Admitted.
(** [] *)

(** **** 练习: 2星, 可选 (beq_nat_refl)  *)
(** 证明下列定理。把[true]放到等式的左手边可能很奇怪，但是这是标准库里这个定理的陈述
    方式，所以我们保持一致。因为不论从左至右重写还是从右至左重写效果都一样，所以不论我
    们用哪种方式表述它都没问题。 *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  (*在此填写*) Admitted.
(** [] *)

(** **** 练习: 2星, 可选 (plus_swap')  *)
(** [replace]策略允许你指定一个特定的子项或者你想重写的地方来重写。想要更精确一点，
    你可以用[replace (t) with (u)]来替换目标表达式[u]中出现的所有表达式[t]，并
    生成[t = u]作为一个额外的子目标。当一个简单的[rewrite]出错的时候这会非常有用。

    使用[replace]策略来证明[plus_swap']，参考[plus_swap]但是不要用[assert (
    n + m = m + n)]。 *)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (*在此填写*) Admitted.
(** [] *)


(** **** 练习: 3星 (binary_commute)  *)
(** 回想一下你在[Basics]章节中为[binary]练习写下的[increment]和[binary-to-unary]
    函数。证明这些函数是可交换的——给一个二进制数加一再转换成一进制和先转换成一进制
    再加一结果相同。
    把你的这个定理叫做[bin_to_nat_pres_incr]。

    （在你开始解决这个练习之前，请把你的[binary]练习答案复制到这，这样这个文件可以
    单独打分。如果你发现你想改一下你一开始的定义来让证明更容易，尽管做吧！） *)

(*在此填写*)
(** [] *)


(** **** 练习: 5星, advanced (binary_inverse)  *)
(** 这个练习承接着之前的关于二进制数的练习。你需要你之前的定义与定理来完成这个练习。

    (a) 首先，写一个函数把自然数转换成二进制数。然后证明把任一自然数转换成二进制再
        转换回自然数，结果和开始的自然数相同。

    (b) 你可能很自然地想到我们可以反方向证明：先把二进制数转换成自然数再转换回二进
        制，结果和开始的二进制数相同。但是，这是错的！解释下会出现什么问题。

    (c) 定义一个“直接的”正规化函数——换言之，一个把二进制数正规化成二进制数的函数：
        对任意的二进制数b，转换成自然数再转换回二进制会生成[(normalize b)]。请证
        明。（注意：这部分很有技巧！）

    再说一遍，之前的定义随便改！
*)

(*在此填写*)
(** [] *)

(* ###################################################################### *)
(** * 对比形式化和非形式化证明（高级内容） *)

(** ”非形式化证明是算法，形式化证明是代码。” *)

(** 到底是什么构成了一个数学断言的“证明”？这个问题已经困扰了哲学家一千多年。
    一个不那么精确的现成的定义是这样：一个数学命题的证明[P]是一段被写出来或
    者被说出来的话，用来使读者或听众确信[P]是正确的。也就是说，证明是一种沟
    通行为。

    现在，沟通行为可能涉及到不同类型的读者。一方面，这个“读者”可能是一段程序——比
    如说Coq——它对证明的“信任”来源于简单的机械化检查：[P]能够从一组确定的形式化
    逻辑规则导出。这种情况下，证明就是一份指导程序如何运用这些逻辑规则的说明书。
    这份说明书就是形式化证明。

    另一方面，读者也可能是个人类，这时证明会用汉语或其他自然语言书写，这就是非形
    式化证明。这种情况下，证明成功的准则就不是那么精确了。一个“好的”证明是让读者
    相信[P]。但是同一份证明可能会被许多读者阅读，有一些人可能会因为某种特定的论
    证方式而信服，另一些则不会。一个读者可能是很迂腐的，可能是没什么经验的，也可
    能非常蠢；让他们都心服口服的惟一的方式就是不辞劳苦地把每一处论证细节都写出来。
    但是对另外一些更熟悉这个领域的读者，可能发现这些细枝末节太繁复了以致于无法抓
    住主干。他们只希望被告知主旨，因为对他们来说补充这些细节轻而易举。最终，根本
    没有一个通用的标准，因为没有一个单一的方式来书写非形式化证明来劝服每一个可说
    服的读者（有些人说什么都没用）。但是实际上，数学家已经发展出一套丰富的规范与
    习语以书写复杂的数学对象并在特定的圈子里可靠的交流。这些从交流中发展出的规范
    能给出一个相当清晰的评判证明好坏的标准。

    因为我们在这门课上用Coq，所以我们主攻形式化证明。但是我们也不会忽视非形式化
    证明！形式化证明在许多领域都很有用，不过在人类之间交流想法的时候它不是很有效
    率。 *)

(** 比方说，这是另一个结合律的证明： *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coq看到这个证明会很开心。然而对于一个人来说，这有点难以理解。如果你习惯了用
    Coq你可能会人脑模拟每一步的运行过程，不过要是证明优点复杂，你会发现这几乎不
    可能做到。相反，一个数学家可能会这样写证明： *)
(** - _Theorem_: For any [n], [m] and [p],
      n + (m + p) = (n + m) + p.
    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show
        0 + (m + p) = (0 + m) + p.
      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where
        n' + (m + p) = (n' + m) + p.
      We must show
        (S n') + (m + p) = ((S n') + m) + p.
      By the definition of [+], this follows from
        S (n' + (m + p)) = S ((n' + m) + p),
      which is immediate from the induction hypothesis. *)
(** _Qed_ *)

(** 证明的整个形式基本相同。这在意料之中：Coq被精心设计过所以他的[induction]
    策略会以同样的顺序生成同样的子目标，就像数学家着重标记那些句子。可是细节上
    有明显不同：某些情况下形式化证明更明确（例如，[rewrite]的使用）但是另一些
    时候更不明确（Coq证明中，每一处的”证明状态”都非常不清晰，一般非形式化证明
    会多次提醒读者现在的状态） *)

(** 这有个结构看上去更清晰的形式化证明： *)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** **** 练习: 2星, 高级内容 (plus_comm_informal)  *)
(** 把你的[plus_comm]的解翻译成一个非形式化证明。 *)

(** Theorem: Addition is commutative.

    Proof: (*在此填写*)
*)
(** [] *)

(** **** 练习: 2星, 可选 (beq_nat_refl_informal)  *)
(** 写出一个下列定理的非形式化证明，使用[plus_assoc]的非形式化证明作为样板。
    不要机械地只把Coq的策略翻译成汉语！

    Theorem: [true = beq_nat n n] for any [n].

    Proof: (*在此填写*)
[] *)

(** $Date: Date: 2015-11-9 17:57:16 2015 -0800 (Mon, 9 Nov 2015) $ *)
