(** * Lists: 结构化的数据 *)

Require Export Induction.

Module NatList. 
(* ###################################################### *)
(** * 二元组 *)

(** 在归纳类型定义中，每个构造器（Constructor）可以有任意多个参数——可以没有（就像true和O），可以有一个（就像S），也可以更多，就像接下来那个定义： *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

(** 这个定义可以被理解作："只有一种方式来构造一个二元组：通过把pair这个构造器应用到两个nat类型的参数上" *)

(** 我们能够像下面这样构造一个二元组。 *)

Check (pair 3 5).

(** *** *)

(** 下面是两个简单的函数定义，这两个函数分别从一个二元组中抽取第一个和第二个分量。
    （这个定义同时也展示了如何对一个两个参数的构造器进行模式匹配) *)

Definition fst (p : natprod) : nat := 
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat := 
  match p with
  | pair x y => y
  end.

Eval compute in (fst (pair 3 5)).
(* ===> 3 *)

(** *** *)

(** 因为二元组经常被用到，所以如果能有数学记号 (x,y) 来代替 pair x y 是非常好的。
    我们可以通过声明一个Notation让Coq接受这种记号。 *)

Notation "( x , y )" := (pair x y).

(** 这个新的记号既能被用在表达式也能被用在模式匹配中。（实际上，在上一章中我们已经使用过了——这个记号在标准库中也已经被提供了) *)

Eval compute in (fst (3,5)).

Definition fst' (p : natprod) : nat := 
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat := 
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod := 
  match p with
  | (x,y) => (y,x)
  end.

(** *** *)

(** 我们现在来证明一些有关二元组的简单的事实。如果我们以一种特定的（稍微有点古怪）的方式来
    书写我们的引理，仅仅通过 [reflexivity]（还有它自带的简化）我们就能完成证明。 *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(** 注意，但如果我们用一种自然的方式来书写这条引理的话，仅仅使用[reflexivity]来证明是远远不够的。 *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

(** *** *)
(** 我们必须要像Coq展示[p]的具体结构，这样[simpl]才能对[fst]和[snd]做模式匹配。 
    通过destruct可以达到这个目的。需要注意的是，不像自然数，destruct不会生成一个额外的子目标，因为一共只有一种方式可以构造二元组。 *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.
          
(** **** Exercise: 1 star (snd_fst_is_swap)  *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, optional (fst_swap_is_snd)  *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** * 数的列表 *)

(** 通过稍稍推广一下我们对二元组的定义，我们像可以这样描述列表："一个列表要么是空的，要么就应该是一个由一个数和另一个列表组成的二元组"。 *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

(** 例如，这就是一个有三个元素的列表。 *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).


(** *** *)
(** 就像二元组一样，用我们已经熟悉的编程的记号来写下一个列表会显得更为方便。下面两个声明让我们可以用[::]来作中缀cons操作符，用方括号来做[外缀]符号来构造列表 *)

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** 完全理解这些声明是不必要的，但是假使你感兴趣的话，接下来我会粗略地介绍到底发生了什么。
    right associativity 告诉 Coq 当遇到多个符号时怎么给表达式加括号。如此一来下面三个
    声明做的就是同一件事。 *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** [at level 60]这部分告诉Coq当遇到表达式还有其他中缀符号的时应该如何加括号。举个例子，
    我们已经定义了 [+] 作为 [plus] 的中缀符号，它的level是50。
Notation "x + y" := (plus x y)  
                    (at level 50, left associativity).
    [+] 将会比 [::] 结合的更紧，所以 [1 + 2 :: [3]] 会被解析成 [(1 + 2) :: [3]]，就和我们期望的一样，而不是 [1 + (2 :: [3])。]

   (值得注意的是，当你在.v文件中看到"[1 + (2 :: [3])]"这样的记号会感到非常疑惑。最里面的那个框住3的方括号，指示了其是一个列表。但是外面那个方括号，在HTML中是看不到的，是用来告诉"coqdoc"这部分要被显示为代码而非普通的文本。)

   上面第二和第三个[Notation]申明引入了标准的方括号记号来表示列表；第三个声明的右边部分展示了在Coq中申明n元记号的语法以及如何把它们翻译成嵌套的二元构造器的序列。 *)

(** *** Repeat *)
(** 很多有用的函数可以用来操作列表。比如[repeat]函数接受一个数[n]和[count]，返回一个长为[count]，每个元素都是[n]的列表。 *)

Fixpoint repeat (n count : nat) : natlist := 
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(** *** Length *)
(** [length]函数用来计算列表的长度。 *)

Fixpoint length (l:natlist) : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(** *** Append *)
(** [app]函数用来把两个列表联接起来。 *)

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** 实际上，在接下来的很多地方都会用到[app]，所以如果它有一个中缀操作符的话会很方便。 *)

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(** 我们来看两个小例子，这两个例子都是有关如何编写有关列表的程序。
    [hd]函数返回列表的第一个元素（"头元素"）。类似的，[tl] 返回除了第一个元素以外
    的所有元素。
    当然，空列表没有第一个元素，所以我们必须传入一个默认值，让这个值成为这种情况下的返回值。  *)

(** *** Head (with default) and Tail *)
Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil  
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

(** **** Exercise: 2 stars (list_funs)  *)
(** 完成以下[nonzeros]，[oddmembers]和[countoddmembers]的定义，
    你可以查看测试函数来理解这些函数应该做什么 *)

Fixpoint nonzeros (l:natlist) : natlist :=
  (* FILL IN HERE *) admit.

Example test_nonzeros:            nonzeros [0;1;0;2;3;0;0] = [1;2;3].
 (* FILL IN HERE *) Admitted.

Fixpoint oddmembers (l:natlist) : natlist :=
  (* FILL IN HERE *) admit.

Example test_oddmembers:            oddmembers [0;1;0;2;3;0;0] = [1;3].
 (* FILL IN HERE *) Admitted.

Fixpoint countoddmembers (l:natlist) : nat :=
  (* FILL IN HERE *) admit.

Example test_countoddmembers1:    countoddmembers [1;0;3;1;4;5] = 4.
 (* FILL IN HERE *) Admitted.
Example test_countoddmembers2:    countoddmembers [0;2;4] = 0.
 (* FILL IN HERE *) Admitted.
Example test_countoddmembers3:    countoddmembers nil = 0.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (alternate)  *)
(** 完成[alternate]的定义，它把两个列表像拉链一样"拉"起来并成为一个列表，
    从两个列表中交替地取出元素。查看后面的tests来获得更加详细的例子。

    注意：一种自然的，优雅的方法来书写[alternate]将无法满足Coq对于[Fixpoint]必须
    "显然会终止"的要求。如果你发现你被这种解法束缚住了，你可以寻找一种稍微冗长一些的解法：同时考虑两个列表。（一个可行的解法需要定义新的列表，但这不是唯一的方法） *)


Fixpoint alternate (l1 l2 : natlist) : natlist :=
  (* FILL IN HERE *) admit.


Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
 (* FILL IN HERE *) Admitted.
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
 (* FILL IN HERE *) Admitted.
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
 (* FILL IN HERE *) Admitted.
Example test_alternate4:        alternate [] [20;30] = [20;30].
 (* FILL IN HERE *) Admitted. 
(** [] *)

(* ###################################################### *)
(** ** Bags via Lists *)

(** [bag]（或者叫[multiset]）就像一个集合，但是每个元素都能够出现若干次，而不是仅仅一次。
    背包一种合理的实现就是把它作为一个列表。 *)

Definition bag := natlist.  

(** **** Exercise: 3 stars (bag_functions)  *)
(** 完成下列[count], [sum], [add] 以及 [member] 的定义 *)

Fixpoint count (v:nat) (s:bag) : nat := 
  (* FILL IN HERE *) admit.

(** 这些命题都能通过[reflexivity]来证明。 *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* FILL IN HERE *) Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 (* FILL IN HERE *) Admitted.

(** 多重集的[sum]非常像集合的[union]:[sum a b]包含了所有[a]和[b]的元素。（数学上对
    多重集上的[sum]的定义常常不大一样，这也是为什么我们没有使用这个名字。
    对于[sum]来说，我们给你的声明中并没有显式的给参数指派名字。除此以外，它使用[Definition]
    而不是[Fixpont]，所以即使你给参数安排了名字，你也不能递归的处理他们。给出这个问题的意义
    在于鼓励你思考[sum]是否能用另一种方法实现——通过使用那些你已经定义过的函数。  *)

Definition sum : bag -> bag -> bag := 
  (* FILL IN HERE *) admit.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.

Definition add (v:nat) (s:bag) : bag := 
  (* FILL IN HERE *) admit.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.

Definition member (v:nat) (s:bag) : bool := 
  (* FILL IN HERE *) admit.

Example test_member1:             member 1 [1;4;1] = true.
 (* FILL IN HERE *) Admitted.
Example test_member2:             member 2 [1;4;1] = false.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (bag_more_functions)  *)
(** 你可以把下面这些和[bag]有关的函数当做额外的练习 *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* 当[remove_one]被应用到一个没有数可以移除的背包时，它应该返回原来的那个而不做任何改变。 *)
  (* FILL IN HERE *) admit.

Example test_remove_one1:         count 5 (remove_one 5 [2;1;5;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_one2:         count 5 (remove_one 5 [2;1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_one3:         count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
 (* FILL IN HERE *) Admitted.
Example test_remove_one4:         count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
 (* FILL IN HERE *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  (* FILL IN HERE *) admit.

Example test_remove_all1:          count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all2:          count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all3:          count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* FILL IN HERE *) Admitted.
Example test_remove_all4:          count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* FILL IN HERE *) Admitted.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  (* FILL IN HERE *) admit.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
 (* FILL IN HERE *) Admitted.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (bag_theorem)  *)
(** 写下一个你认为有趣的关于[bags]的定理[bag_theorem]，要涉及到[count]和[add]。
    证明他。注意，这个问题是开放的，很有可能你会遇到你写下了正确的定理，
    但是其证明涉及到了你现在还没有学到的技巧。如果你陷入麻烦了，欢迎提问。 *)

(* FILL IN HERE *)
(** [] *)

(* ###################################################### *)
(** * 有关列表的推理 *)

(** 就像数字一样，一些简单的有关处理列表事实，有时也能仅仅通过化简来证明。
    比方说，对于下面这个例子，[reflexivity]中所做的简化就已经足够了…… *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** ……由于[[]]被替换进了[app]定义中的相应的match分支，这就使得整个[match]得以被简化并证明目标 *)

(** 并且，和数一样，又是对一个列表做分类讨论（是否是空）是非常有用的。 *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  (* Case "l = nil". *)
    reflexivity.
  (* Case "l = cons n l'". *)
    reflexivity.  Qed.

(** 这里，如此解决[nil]这种情况是因为我们定义了[tl nil = nil]。至于[destruct]策略中的[as]注解
    引入的两个名字，[n]和[l']， 分别对应了[cons]构造子的两个参数（正在构造的列表的头和尾）。 *)

(** 通常的情况是，就算你不相信的话也没办法，要证明关于列表的有趣的定理需要用到归纳法。 *)

(* ###################################################### *)
(** ** 一点点说教 *)

(** 知识阅读示例证明脚本的话，你不会获得什么特别有用的东西。搞清楚每一个的细节是非常重要的
    使用Coq并思考有关每一步是如何得到的。否则练习题将一点用都没有。 *)

(* ###################################################### *)
(** ** 列表上的归纳 *)

(** 读者对在像[natlist]这样的数据类型上通过归纳进行证明和对自然数归纳相比可能没有name熟悉，
    但是基本的想法是一样简单的。每个[Inductive]的声明定义了一集值，这些值可以用那些被声明
    的构造器来构建：布尔值可以是[true]或者是[false]；自然数可以是[O]或[S]应用到另一个自然数上；
    列表可以是[nil]或者是[cons]应用到一个自然数和另一个列表。

    除此以外，把声明的构造子应用到别的项上面是的归纳定义的项的 _唯一_ 可能的形状，并且这个是个事实
    直接就给出了一种用来推理归纳定义集的方法：一个自然数要么是[O]不然就是[S]应用到某个 _更小_ 的
    自然数；一个列表要么是[nil]不然就是[cons]应用到某个自然数和某个 _更小_ 的列表上；等等。所以，
    如果我们有某个命题[P]提到了列表[l]并且我们想证明[P]对 _一切_ 列表都成立，我们可以像这样推理：

      - 首先，证明 [P] 当 [l] 是 [nil] 时对 [l] 成立 .

      - 然后证明 [P] 当 [l] 是 [cons n l']成立， 其中 [n] 是某个自然数，[l'] 是某个更小的列表
        ，假设 [P] 对 [l'] 成立.

    由于较大的列表只可能通过较小的列表构建起来，最终这个较小的列表会变成[nil]，这两点合一起就完成了
    [P] 对一切列表 [l] 成立的证明。 下面是一个具体的例子。 *)

Theorem app_assoc : forall l1 l2 l3 : natlist, 
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).   
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  (* Case "l1 = nil". *)
    reflexivity.
  (* Case "l1 = cons n l1'". *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** 再一次强调，当你把Coq的证明当做静态的文档的话你可能不会有特别多的收获——如果你
    通过一个交互式的Coq会话来阅读证明的话你可以看到当前的目标和上下文，但是这些状态
    对于阅读写下来的脚本的你来说是不可见的。所以一份用自然语言写成的证明——写给人看的——会
    需要包含更多地提示，比如提醒他们第二种情况下的归纳假设到底是什么，来帮助读者明白当前的情况。 *)

(** *** 非形式化的版本 *)

(** _定理_: 对所有的列表 [l1], [l2], 和 [l3]， 
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)]。

   _证明_: 通过对 [l1] 使用归纳法。

   - 首先, 假设 [l1 = []]。  我们要证明：
       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),
     这可以通过展开 [++] 的定义得到.

   - 然后, 假设 [l1 = n::l1']， 有：
       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)
     (归纳假设)。 我们必须证明
       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ 用来强调目的是一个不错 根据 [++] 的定义, 上面就等价于：
       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),
     这可以通过我们的归纳假设立马得到。  []
*)

(** *** 另一个例子 *)
(**
  这里是一个用来在课堂上一起完成的类似的例子。 *)

Theorem app_length : forall l1 l2 : natlist, 
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1'].
  (* Case "l1 = nil". *)
    reflexivity.
  (* Case "l1 = cons". *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.


(** *** 反转列表 *)
(** 作为一个更为深入的例子，来说明在列表上使用归纳证明，假设我们定义一个"右侧cons"的函数
    [snoc]。 像这样： *)

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

 (** ……然后用它来定义一个反转列表的函数[rev] 像这样: *)

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(** *** 有关反转的证明 *)
(** 现在我们用我们新定义的[snoc]和[rec]来证明一些列表的定理。
    与我们目前已经见到过的归纳证明相比，手头这个是一个更具挑战性
    的定理：就是反转一个列表并不会改变他的长度。当我们初次尝试时
    我们发现我们卡在了后继这种情形上。 *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  (* Case "l = []". *)
    reflexivity.
  (* Case "l = n :: l'". *)
    (* 这是一个比较棘手的情况。我们从普通的化简开始。 *)
    simpl. 
    (* 现在我们好像卡在什么地方了：目标是要证明涉及[snoc]的等式，
       但是我们在上下文和全局环境下并没有任何有关[snoc]的等式！

       通过IH来重写目标，我们可以获得一点点进展…… *)
    rewrite <- IHl'.
    (* ……但也仅此而已 *)
Abort.

(** 所以我们把有关[snoc]的可以推动证明的等式单独拿出来作为一个引理。 *)

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  (* Case "l = nil".*)
    reflexivity.
  (* Case "l = cons n' l'". *)
    simpl. rewrite -> IHl'. reflexivity.  Qed.


(** 注意我们要使得引理尽可能的 _通用_ : 具体来说，我们要对 _所有_ 的[natlist]
    进行全称量化，而不仅仅是那些由[rev]的来的。这很自然，因为这个证明目标
    显然不依赖于被反转的列表。除此之外，证明一个更普遍的性质更容易。 *)
    
(** 现在我们可以完成最初的那个证明。 *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  (* Case "l = nil". *)
    reflexivity.
  (* Case "l = cons". *)
    simpl. rewrite -> length_snoc. 
    rewrite -> IHl'. reflexivity.  Qed.

(** 用来作对比，下面是这两个定理的非形式化的证明

    _定理_: 对一切数[n]和列表[l]，
      [length (snoc l n) = S (length l)]。
 
    _证明_: 对[l]进行归纳。

    - 首先，假设[l = []]。我们要证明
       length (snoc [] n) = S (length [])，
      通过[length]和[snoc]的定义，上式可以显然得到。

    - 接下来，假设 [l = n'::l']，并且
        length (snoc l' n) = S (length l')。
      我必须要证明
        length (snoc (n' :: l') n) = S (length (n' :: l'))。
      通过[length]和[snoc]，只要证明
        S (length (snoc l' n)) = S (S (length l'))，
      而这就是归纳假设。 [] *)
                        
(** _定理_: 对一切列表 [l], [length (rev l) = length l].
    
    _证明_: 对 [l] 进行归纳.  

      - 首先，假设[l = []]，我们要证明，
          length (rev []) = length []。
        通过[length]和[rev]的定义，上式可以显然得到。
    
      - 接下来，假设 [l = n'::l']，并且
        length (rev l') = length l'。
      我必须要证明
        length (rev (n' :: l')) = length (n' :: l')。
      通过[rev]的定义，只要证明
        length (snoc (rev l') n) = S (length l')
      根据之前的引理，说的就是
        S (length (rev l)) = S (length l')。
      而这就是归纳假设。 [] *)

(** 显然，这些证明的样式实在是冗长而迂腐。经历过最开始的那些以后，
    我们可能觉得细节更少并且仅仅突出那些不十分显然的步骤的那些证明
    更容易理解（因为我们能够的在脑子中思考他们，实在不行我们还
    可以在纸上打草稿）。下面我们以一种更加紧凑的样式
    呈现之前的证明： *)

(** _定理_:
     对一切列表 [l], [length (rev l) = length l].

    _证明_: 首先，注意到，
       length (snoc l n) = S (length l)
    对一切[l]成立。 通过对[l]进行归纳就可以直接得到这个结论。
    当[l = n'::l']时，证明性质只需要再一次使用归纳法，然后
    同时使用归纳假设和之前的观察得到的性质。[] *)

(** 在特定情况下，我们更倾向于哪种样式取决于读者对于这个问题
    了解程度以及当前证明和读者已经了解的那些有多相近。更加冗长
    的版本用来强调证明目标是一个不错的方式。 *)

(* ###################################################### *)
(** ** [SearchAbout] *)

(** 我们已经见到了很多证明需要使用之前已经证明过的结论，然后使用[rewrite]来
    改写当前目标，接下来我们会看到其他用来重用之前证明的定理的方式。但是
    想要指定一个定理，我们需要知道其名字，记住所有定理的名字是很困难的！
    记住哪些定理已经被证明过了甚至都是非常困难的，更不要说记住它们的名字了。

    Coq的[SearchAbout]命令在遇到这种情况的时候非常有用。用[SearchAbout foo]
    会让Coq显示所有涉及到[foo]的定理的列表。举个例子，去掉下面的注释你会看到
    一串我们已经证明过的关于[rev]的定理。 *)

(*  SearchAbout rev. *)

(** 在你做下面的练习时和之后的课程的过程中你要记住[SearchAbout]；他可以节约你
    非常多的时间！ *)

(** 并且，如果你在使用ProofGeneral，你可以用[C-c C-a C-a]来运行[SearchAbout]。
    通过[C-c C-;]可以在你的缓冲区里向下翻阅它返回的结果。 *)

(* ###################################################### *)
(** ** 列表练习, 第一部分 *)

(** **** 练习: 三星 (list_exercises)  *)
(** 更多的关于列表的习题 *)

Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.   
Proof.
  (* FILL IN HERE *) Admitted.


Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.

(** 下一个练习有一个非常短的解决方法。如果你发现自己弄得一团糟，
    你应该回头去找找更简单的方法。 *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  (* FILL IN HERE *) Admitted.


Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  (* FILL IN HERE *) Admitted.

(** 关于你的[nonzeros]实现的习题 *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 练习: 两星 (beq_natlist)  *)
(** 填写[beq_natlist]的定义，它通过比较列表中的数字来判断是否相等。证明对一切列表[l]，
    [beq_natlist l l] 返回 [true]。 *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  (* FILL IN HERE *) admit.

Example test_beq_natlist1 :   (beq_natlist nil nil = true).
 (* FILL IN HERE *) Admitted.
Example test_beq_natlist2 :   beq_natlist [1;2;3] [1;2;3] = true.
 (* FILL IN HERE *) Admitted.
Example test_beq_natlist3 :   beq_natlist [1;2;3] [1;2;4] = false.
 (* FILL IN HERE *) Admitted.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** 列表练习, 第二部分 *)

(** **** 练习: 两星 (list_design)  *)
(** 设计练习：
    - 写下一个不平凡的，涉及到[cons]([::])，[snoc]，[app]([++])
      的定理[cons_snoc_app]。
    - 证明它。 *) 

(* FILL IN HERE *)
(** [] *)

(** **** 练习: 三星, 进阶 (bag_proofs)  *)
(** 下面是关于你之前对于背包的一些定义的定理。 *)

Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** 下面这条关于[ble_nat]的引理在你完成下一个证明时可能会有帮助。 *)

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  (* Case "0".  *)
    simpl.  reflexivity.
  (* Case "S n'". *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 练习: 三星, 可选 (bag_count_sum)  *)  
(** 写下一个涉及到[count]和[sum]的，关于[bag_count_sum]的定理，并证明。*)

(* FILL IN HERE *)
(** [] *)

(** **** 练习: 四星, 进阶 (rev_injective)  *)
(** 证明[rev]是一个单射，也就是说，
      forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
    有一种简单和一种困难的方法来解决这个问题。
*)

(* FILL IN HERE *)
(** [] *)


(* ###################################################### *)
(** * 可能的失败 *)


(** [natoption]的一种用法是用来从函数中返回"错误码"。举个例子，
    假设我们想要写一个返回某个列表第[n]个元素的函数。如果我们让
    它的类型是[nat -> natlist -> nat]，那么当列表过短的时候我们
    仍然必须要返回某个数。 *)

Fixpoint index_bad (n:nat) (l:natlist) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with 
               | true => a 
               | false => index_bad (pred n) l' 
               end
  end.

(** *** *)
(** 另一方面，如果我们让它的类型成为[nat -> natlist -> natoption]，
    那么当列表不够长时，我们就能返回[None]，当列表有足够的元素时返回[Some a]，
    其中[a]出现在列表的第[n]位。 *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.  


Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => match beq_nat n O with 
               | true => Some a
               | false => index (pred n) l' 
               end
  end.

Example test_index1 :    index 0 [4;5;6;7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index 3 [4;5;6;7]  = Some 7.
Proof. reflexivity.  Qed.
Example test_index3 :    index 10 [4;5;6;7] = None.
Proof. reflexivity.  Qed.

(** 这个例子同样是可以用来介绍Coq语言的一个小特性——条件表达式…… *)

(** *** *)

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => if beq_nat n O then Some a else index' (pred n) l'
  end.

(** Coq的条件语句就和其他语言中的一样，无非加上了一点小小的推广。由于布尔类型
    不是内建的，事实上，Coq允许在任意有两个构造子的归纳定义的类型上使用条件表达式。
    当表达式求值到归纳定义中的第一个构造子时，它被认为是真的，当其被求值到第二个
    构造子时，它被认为是假的。 *)

(** 下面的函数从[natoption]中取出一个[nat]，在[None]的情况下返回提供的默认值。 *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** 练习：两星 (hd_opt)  *)
(** 使用相同的想法，修正之前的[hd]函数来使我们不需要为[nil]提供一个默认的元素。  *)

Definition hd_opt (l : natlist) : natoption :=
  (* FILL IN HERE *) admit.

Example test_hd_opt1 : hd_opt [] = None.
 (* FILL IN HERE *) Admitted.

Example test_hd_opt2 : hd_opt [1] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 练习: 一星, 可选 (option_elim_hd)  *)
(** 这个练习让你把新的[hd_opt]和旧的[hd]联系起来 *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** * 字典 *)

(** 作为最后一个演示在Coq中如何定义基础的数据结构的例子，这里是
    一个简单的[dictionary]的声明，使用数作为关键字和值
    （也就是说，一个字典代表了一个有限的从自然数到自然数的映射。） *)

Module Dictionary.

Inductive dictionary : Type :=
  | empty  : dictionary 
  | record : nat -> nat -> dictionary -> dictionary. 

(** 这个声明可以被读作："有两种方式来构造[dictionary]：要么用[empty]
    来构造一个空的字典，要么把[record]应用到键，值和一个已经存在的[dictionary]
    来构造一个附加了键值的[dictionary]"。 *)

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).

(** 这里是一个[find]函数，它在一个[dictionary]查找给定的键。如果该键
    无法被找到，他就返回[None]，否则返回[Some val]其中[val]是字典中
    该键所对应的。如果同一个键被映到多个值，[find]就会返回它第一个找到的。 *)

Fixpoint find (key : nat) (d : dictionary) : natoption := 
  match d with 
  | empty         => None
  | record k v d' => if (beq_nat key k) 
                       then (Some v) 
                       else (find key d')
  end.



(** **** 练习: 一星 (dictionary_invariant1)  *)
(** 完成下列证明 *)

Theorem dictionary_invariant1' : forall (d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 练习: 一星 (dictionary_invariant2)  *)
(** 完成下列证明 *)

Theorem dictionary_invariant2' : forall (d : dictionary) (m n o: nat),
  beq_nat m n = false -> find m d = find m (insert n o d).
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)



End Dictionary.

End NatList.

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

