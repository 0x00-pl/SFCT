(** * 前言 *)

(* ###################################################################### *)
(** * 简介 *)

(** 这本电子书是一个关于软件基础 ，可靠软件背后的数学的课程.
    主题包含基本逻辑概念，用计算机辅助定理证明，Coq证明助理，函数式编程。
    操作语义，霍尔逻辑，还有静态类型系统。
    这个体验的预期受众是从高级本科生到博士与及研究生的读者、
    尽管一定的数学熟练度会有帮助，
    本书没有对读者做任何的逻辑学或程序语言的背景。

    这个教程的最大创新是，本教程是百分之百形式化，并且机械严重的：
    所有的文字都是字面意义上的Coq脚本。

    它是用于于一个Coq交互式会话一起阅读的。
    本书的所有细节都完全用Coq形式化了，习题也是被设计于来Coq做出。

    文件被整理为一系列覆盖了一学期内容，环环相扣的核心章节，
    与及一定的包含额外主题的“附录”。
    所有的核心章节都适合高级本科生与及研究生。 *)


(* ###################################################################### *)
(** * 导论 *)

(** 构建可靠的软件很难。现代系统的规模，复杂性，介入构建过程的人数，
    还有置于系统之上的需求的范围，使得构建或多或少正确的软件很难，
    更不用说百分百正确。同一时间，因为信息处理继续融入社会的各个方面，
    程序错误于漏洞的代价越来越严重.

    计算机科学家与及软件工程师对这些挑战，通过设计一系列的改进软件质量的技手法，
    包含对管理软件项目与及编程团队的建议（比如极限编程），
    库（比如模型-试图-控制器，发布-订阅）与及编程语言
    （面向对象编程，面向切面编程，函数式编程）的设计哲学，还有
    用来指定，论证软件属性的数学与及数学工具来应对。

    这门课的重点是最后一个方法。本书教程把五个概念穿插在一起：

    （1）逻辑学里面的基础工具，用于构建并且证明精确的关于程序的假设；

    （2）用证明助理构建严谨的逻辑论据；

    （3）函数式编程思想，同时作为编程方法与及程序跟逻辑学之间的桥梁；

    （4）形式化的用于论证程序属性（一个循环对所有输入都会终止。
         或者一个排序函数或者编译器满足特定规格）的手段；与及

    （5）用类型系统建立一个对于某一个编程语言的所有程序的瞒住特效
        （所有类型正确的Java程序不能在运行时被破坏）。

    这五个主题任一个都可以轻易填满一整个课程；
    把它们五个塞在一个课程中很自然地表面很多会被遗留在外。
    但是我们洗完读者会认为5个主题互补。与及同时教授五个内容创建一个
    可以轻松进入任一主题的根基。一些更深的阅读的建议在 [Postscript] 一章*)

(** ** Logic *)

(** Logic is the field of study whose subject matter is _proofs_ --
    unassailable arguments for the truth of particular propositions.
    Volumes have been written about the central role of logic in
    computer science.  Manna and Waldinger called it "the calculus of
    computer science," while Halpern et al.'s paper _On the Unusual
    Effectiveness of Logic in Computer Science_ catalogs scores of
    ways in which logic offers critical tools and insights.  Indeed,
    they observe that "As a matter of fact, logic has turned out to be
    significiantly more effective in computer science than it has been
    in mathematics.  This is quite remarkable, especially since much
    of the impetus for the development of logic during the past one
    hundred years came from mathematics."

    In particular, the fundamental notion of inductive proofs is
    ubiquitous in all of computer science.  You have surely seen them
    before, in contexts from discrete math to analysis of algorithms,
    but in this course we will examine them much more deeply than you
    have probably done so far. *)

(** ** Proof Assistants *)

(** The flow of ideas between logic and computer science has not been
    in just one direction: CS has also made important contributions to
    logic.  One of these has been the development of software tools
    for helping construct proofs of logical propositions.  These tools
    fall into two broad categories:

       - _Automated theorem provers_ provide "push-button" operation:
         you give them a proposition and they return either _true_,
         _false_, or _ran out of time_.  Although their capabilities
         are limited to fairly specific sorts of reasoning, they have
         matured tremendously in recent years and are used now in a
         huge variety of settings.  Examples of such tools include SAT
         solvers, SMT solvers, and model checkers.

       - _Proof assistants_ are hybrid tools that automate the more
         routine aspects of building proofs while depending on human
         guidance for more difficult aspects.  Widely used proof
         assistants include Isabelle, Agda, Twelf, ACL2, PVS, and Coq,
         among many others.

    This course is based around Coq, a proof assistant that has been
    under development since 1983 at a number of French research labs
    and universities.  Coq provides a rich environment for interactive
    development of machine-checked formal reasoning.  The kernel of
    the Coq system is a simple proof-checker which guarantees that
    only correct deduction steps are performed.  On top of this
    kernel, the Coq environment provides high-level facilities for
    proof development, including powerful tactics for constructing
    complex proofs semi-automatically, and a large library of common
    definitions and lemmas.

    Coq has been a critical enabler for a huge variety of work across
    computer science and mathematics:

    - As a _platform for modeling programming languages_, it has become
      a standard tool for researchers who need to describe and reason
      about complex language definitions.  It has been used, for
      example, to check the security of the JavaCard platform,
      obtaining the highest level of common criteria certification,
      and for formal specifications of the x86 and LLVM instruction
      sets.

    - As an _environment for developing formally certified software_,
      Coq has been used to build CompCert, a fully-verified optimizing
      compiler for C, for proving the correctness of subtle algorithms
      involving floating point numbers, and as the basis for
      Certicrypt, an environment for reasoning about the security of
      cryptographic algorithms.

    - As a _realistic environment for programming with dependent
      types_, it has inspired numerous innovations.  For example, the
      Ynot project at Harvard embeds "relational Hoare reasoning" (an
      extension of the _Hoare Logic_ we will see later in this course)
      in Coq.

    - As a _proof assistant for higher-order logic_, it has been used
      to validate a number of important results in mathematics.  For
      example, its ability to include complex computations inside
      proofs made it possible to develop the first formally verified
      proof of the 4-color theorem.  This proof had previously been
      controversial among mathematicians because part of it included
      checking a large number of configurations using a program. In
      the Coq formalization, everything is checked, including the
      correctness of the computational part.  More recently, an even
      more massive effort led to a Coq formalization of the
      Feit-Thompson Theorem -- the first major step in the
      classification of finite simple groups.

   By the way, in case you're wondering about the name, here's what
   the official Coq web site says: "Some French computer scientists
   have a tradition of naming their software as animal species: Caml,
   Elan, Foc or Phox are examples of this tacit convention. In French,
   'coq' means rooster, and it sounds like the initials of the
   Calculus of Constructions (CoC) on which it is based."  The rooster
   is also the national symbol of France, and "Coq" are the first
   three letters of the name of Thierry Coquand, one of Coq's early
   developers. *)

(** ** Functional Programming *)

(** The term _functional programming_ refers both to a collection of
    programming idioms that can be used in almost any programming
    language and to a family of programming languages designed to
    emphasize these idioms, including Haskell, OCaml, Standard ML,
    F##, Scala, Scheme, Racket, Common Lisp, Clojure, Erlang, and Coq.

    Functional programming has been developed over many decades --
    indeed, its roots go back to Church's lambda-calculus, which was
    invented in the 1930s before the era of the computer began!  But
    since the early '90s it has enjoyed a surge of interest among
    industrial engineers and language designers, playing a key role in
    high-value systems at companies like Jane St. Capital, Microsoft,
    Facebook, and Ericsson.

    The most basic tenet of functional programming is that, as much as
    possible, computation should be _pure_, in the sense that the only
    effect of execution should be to produce a result: the computation
    should be free from _side effects_ such as I/O, assignments to
    mutable variables, redirecting pointers, etc.  For example,
    whereas an _imperative_ sorting function might take a list of
    numbers and rearrange its pointers to put the list in order, a
    pure sorting function would take the original list and return a
    _new_ list containing the same numbers in sorted order.

    One significant benefit of this style of programming is that it
    makes programs easier to understand and reason about.  If every
    operation on a data structure yields a new data structure, leaving
    the old one intact, then there is no need to worry about how that
    structure is being shared and whether a change by one part of the
    program might break an invariant that another part of the program
    relies on.  These considerations are particularly critical in
    concurrent programs, where every piece of mutable state that is
    shared between threads is a potential source of pernicious bugs.
    Indeed, a large part of the recent interest in functional
    programming in industry is due to its simple behavior in the
    presence of concurrency.

    Another reason for the current excitement about functional
    programming is related to the first: functional programs are often
    much easier to parallelize than their imperative counterparts.  If
    running a computation has no effect other than producing a result,
    then it does not matter _where_ it is run.  Similarly, if a data
    structure is never modified destructively, then it can be copied
    freely, across cores or across the network.  Indeed, the MapReduce
    idiom that lies at the heart of massively distributed query
    processors like Hadoop and is used by Google to index the entire
    web is a classic example of functional programming.

    For purposes of this course, functional programming has yet
    another significant attraction: it serves as a bridge between
    logic and computer science.  Indeed, Coq itself can be viewed as a
    combination of a small but extremely expressive functional
    programming language plus with a set of tools for stating and
    proving logical assertions.  Moreover, when we come to look more
    closely, we find that these two sides of Coq are actually aspects
    of the very same underlying machinery -- i.e., _proofs are
    programs_.  *)

(** ** Program Verification *)

(** The first third of the book is devoted to developing the
    conceptual framework of logic and functional programming and
    gaining enough fluency with Coq to use it for modeling and
    reasoning about nontrivial artifacts.  From this point on, we
    increasingly turn our attention to two broad topics of critical
    importance to the enterprise of building reliable software (and
    hardware): techniques for proving specific properties of
    particular _programs_ and for proving general properties of whole
    programming _languages_.

    For both of these, the first thing we need is a way of
    representing programs as mathematical objects, so we can talk
    about them precisely, and ways of describing their behavior in
    terms of mathematical functions or relations.  Our tools for these
    tasks are _abstract syntax_ and _operational semantics_, a method
    of specifying the behavior of programs by writing abstract
    interpreters.  At the beginning, we work with operational
    semantics in the so-called "big-step" style, which leads to
    somewhat simpler and more readable definitions, in those cases
    where it is applicable.  Later on, we switch to a more detailed
    "small-step" style, which helps make some useful distinctions
    between different sorts of "nonterminating" program behaviors and
    which is applicable to a broader range of language features,
    including concurrency.

    The first programming language we consider in detail is _Imp_, a
    tiny toy language capturing the core features of conventional
    imperative programming: variables, assignment, conditionals, and
    loops. We study two different ways of reasoning about the
    properties of Imp programs.

    First, we consider what it means to say that two Imp programs are
    _equivalent_ in the sense that they give the same behaviors for
    all initial memories.  This notion of equivalence then becomes a
    criterion for judging the correctness of _metaprograms_ --
    programs that manipulate other programs, such as compilers and
    optimizers.  We build a simple optimizer for Imp and prove that it
    is correct.

    Second, we develop a methodology for proving that Imp programs
    satisfy formal specifications of their behavior.  We introduce the
    notion of _Hoare triples_ -- Imp programs annotated with pre- and
    post-conditions describing what should be true about the memory in
    which they are started and what they promise to make true about
    the memory in which they terminate -- and the reasoning principles
    of _Hoare Logic_, a "domain-specific logic" specialized for
    convenient compositional reasoning about imperative programs, with
    concepts like "loop invariant" built in.

    This part of the course is intended to give readers a taste of the
    key ideas and mathematical tools used for a wide variety of
    real-world software and hardware verification tasks.
*)

(** ** Type Systems *)

(** Our final major topic, covering the last third of the course, is
    _type systems_, a powerful set of tools for establishing
    properties of _all_ programs in a given language.

    Type systems are the best established and most popular example of
    a highly successful class of formal verification techniques known
    as _lightweight formal methods_.  These are reasoning techniques
    of modest power -- modest enough that automatic checkers can be
    built into compilers, linkers, or program analyzers and thus be
    applied even by programmers unfamiliar with the underlying
    theories.  (Other examples of lightweight formal methods include
    hardware and software model checkers, contract checkers, and
    run-time property monitoring techniques for detecting when some
    component of a system is not behaving according to specification).

    This topic brings us full circle: the language whose properties we
    study in this part, called the _simply typed lambda-calculus_, is
    essentially a simplified model of the core of Coq itself!

*)

(* ###################################################################### *)
(** * Practicalities *)

(* ###################################################################### *)
(** ** Chapter Dependencies *)

(** A diagram of the dependencies between chapters and some suggested
    paths through the material can be found in the file [deps.html]. *)

(* ###################################################################### *)
(** ** System Requirements *)

(** Coq runs on Windows, Linux, and OS X.  You will need:

       - A current installation of Coq, available from the Coq home
         page.  Everything should work with version 8.4.

       - An IDE for interacting with Coq.  Currently, there are two
         choices:

           - Proof General is an Emacs-based IDE.  It tends to be
             preferred by users who are already comfortable with
             Emacs.  It requires a separate installation (google
             "Proof General").

           - CoqIDE is a simpler stand-alone IDE.  It is distributed
             with Coq, but on some platforms compiling it involves
             installing additional packages for GUI libraries and
             such. *)

(* ###################################################################### *)
(** ** Exercises *)

(** Each chapter includes numerous exercises.  Each is marked with a
    "star rating," which can be interpreted as follows:

       - One star: easy exercises that underscore points in the text
         and that, for most readers, should take only a minute or two.
         Get in the habit of working these as you reach them.

       - Two stars: straightforward exercises (five or ten minutes).

       - Three stars: exercises requiring a bit of thought (ten
         minutes to half an hour).

       - Four and five stars: more difficult exercises (half an hour
         and up).

    Also, some exercises are marked "advanced", and some are marked
    "optional."  Doing just the non-optional, non-advanced exercises
    should provide good coverage of the core material.  Optional
    exercises provide a bit of extra practice with key concepts and
    introduce secondary themes that may be of interest to some
    readers.  Advanced exercises are for readers who want an extra
    challenge (and, in return, a deeper contact with the material).

    _Please do not post solutions to the exercises in public places_:
    Software Foundations is widely used both for self-study and for
    university courses.  Having solutions easily available makes it
    much less useful for courses, which typically have graded homework
    assignments.  The authors especially request that readers not post
    solutions to the exercises anyplace where they can be found by
    search engines.
*)

(* ###################################################################### *)
(** ** Downloading the Coq Files *)

(** A tar file containing the full sources for the "release version"
    of these notes (as a collection of Coq scripts and HTML files) is
    available here:
<<
        http://www.cis.upenn.edu/~bcpierce/sf   
>>
    If you are using the notes as part of a class, you may be given
    access to a locally extended version of the files, which you
    should use instead of the release version.
*)

(* ###################################################################### *)
(** * Note for Instructors *)

(** If you intend to use these materials in your own course, you will
    undoubtedly find things you'd like to change, improve, or add.
    Your contributions are welcome!

    Please send an email to Benjamin Pierce describing yourself and
    how you would like to use the materials, and including the result
    of doing "htpasswd -s -n NAME", where NAME is your preferred user
    name.  We'll set you up with read/write access to our subversion
    repository and developers' mailing list; in the repository you'll
    find a [README] with further instructions. *)

(* ###################################################################### *)
(** * Translations *)

(** Thanks to the efforts of a team of volunteer translators, _Software 
    Foundations_ can now be enjoyed in Japanese at [http://proofcafe.org/sf]
*)

(** $Date$ *)

