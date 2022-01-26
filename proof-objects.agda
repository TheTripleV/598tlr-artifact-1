-- if curious: https://agda.readthedocs.io/en/v2.6.0.1/language/without-k.html
{-# OPTIONS --without-K --allow-unsolved-metas #-}

{-
  CS 598 TLR
  Artifact 1: Proof Objects
  Student Copy

  READ ME FIRST: You will absolutely not be graded on your ability to finish
  these proofs. It's OK to be confused and find this hard. It's also
  OK to come into this class as an Agda wizard and breeze through this,
  perhaps even using a bunch of features of Agda that aren't mentioned
  in this file at all (if you do that, though, please help your partner
  understand what you are doing, and please discuss what you did at the end).
  The point is to pay attention to what is hard and where you wish you
  had better automation, and to learn about proof objects.

  At the end of this class (or, if you're not attending in person,
  sometime before 1230 PM the day of class) you'll post on the forum
  about what you found challenging, what you enjoyed, and─most importantly
  for this class─what kind of automation you wish you had.
  If you or someone you're working with is an Agda wizard already,
  and you know about automation or syntax that already exists that makes the
  job easy, definitely take note of that and mention it as well.

  If you have a lot of trouble with a proof, it's OK to ask me for help
  (or post in the forum if you're not here in person). It's also OK to
  ask people in other groups.

  But please, please don't stress about finishing these proofs.
  The theorems will still be here after class if you feel tempted by them.
  I'm also happy to distribute my own answer key, or to let you share
  proofs with other students later─the point is to think about the proof
  objects you construct throughout, and the experience you have constructing
  them. It's about the journey, not the destination.
-}
module proof-objects where

{-
  Some built-in datatypes we'll use in this exercise:
-}
open import Agda.Builtin.Nat -- natural numbers
open import Agda.Builtin.List -- polymorphic lists
open import Agda.Builtin.Char -- characters
open import Agda.Builtin.Equality -- equality

{-
  You can see these definitions by clicking them and then pressing the Alt
  key along with the period. Or you can use the middle button of your mouse,
  if you have one.

  For example, if we click on Agda.Builtin.List and press the Alt key
  along with the period, it will open up the file that defines the
  list datatype. A polymorphic list in Agda is defined a lot like the
  list datatype in Coq that we saw in the slides for the first class.
  It is an inductive datatype with two cases:

    data List (A : Set) : Set where
      []  : List A
      _∷_ : A → List A → List A

  In other words, as in Coq, a list is either empty ([]) or the result
  of consing (∷) an element of type A in front of some other list of
  elements of type A.

  For example, let's define some empty lists of numbers and characters.
  In Agda, a definition has its type on the first line, and then the
  term with that type on the next line:
-}

-- The empty list of natural numbers
empty-nat : List Nat -- the type
empty-nat = [] -- the term

-- The empty list of characters
empty-char : List Char -- the type
empty-char = [] -- the term

{-
  Cool. Now let's define some non-empty lists.

  NOTE: The Agda community has an unfortunate obsession with Unicode.
  The syntax for the cons constructor in Coq is two colons, written ::.
  Confusingly, the Agda cons constructor is actually denoted with a
  single special unicode character, written ∷. You can write this
  special character by typing \:: (with two colons), and it will
  magically turn into ∷.

  OK, with that in mind:
-}

-- A list [1; 2; 3; 4]
1-2-3-4 : List Nat -- type
1-2-3-4 = 1 ∷ 2 ∷ 3 ∷ 4 ∷ [] -- term

-- A list [x; y; z]
x-y-z : List Char -- type
x-y-z = 'x' ∷ 'y' ∷ 'z' ∷ [] -- term

{-
  As in Coq, we can write functions about lists, like our length function,
  which we define by pattern matching. The syntax for pattern matching in
  Agda is defining each case on a different line:
-}

-- list length
length : ∀ {A : Set} → List A → Nat -- type
length [] = 0 -- term in the empty case
length (h ∷ tl) = suc (length tl) -- term in the cons case

{-
  That is, the length of the empty list ([]) is zero (0), and the
  length any other list (h ∷ tl) is one plus (suc, for "successor")
  the length of the tail of the list (length tl).

  NOTE: Thanks to the Agda community's unicode obsession, you can write
  the above ∀ by typing \forall, and you can write the above → by typing
  \r or \->. But it's OK to spell them out as forall and ->.

  EXERCISE 1: Write a function that reverses a list.
  You may use the function app I've written for you below,
  which appends two lists.

  NOTE: The {! !} syntax I've written inside of the sketch of rev is a
  hole─you will want to replace this with your implementation of rev for
  each case. These holes change color when you compile files, and numbers
  appear next to them; I explain this a bit more later on.

  NOTE: You can compile this file by running C-c C-l, to just
  invoke the type checker. To produce an executable file,
  you can run C-c C-x C-c and specify the GHC backend, but this isn't necessary
  to just check the proofs you'll write in this file. The first time
  you compile this file, you'll see a bunch of numbered constrants;
  these correspond to the holes I've left in the file for you to fill.
-}

-- list append
app : ∀ {A : Set} → List A → List A → List A -- type
app [] l = l -- term in the empty case
app (h ∷ tl) l = h ∷ app tl l -- term in the cons case 

-- list rev
rev : ∀ {A : Set} → List A → List A -- type
rev [] = {! !} -- your term in the empty case goes here
rev (h ∷ tl) = {! !} -- your term in the cons case goes here

{-
  Let's test your rev function.
  We're going to check that, on the lists we've defined at the top
  of this file, the result of calling rev gives us the reverse lists.

  To do that, we need a way to state what it means for two things to be
  equal. Equality in Agda is written ≡, which is typed as \== using the same
  magic as before, because of the community's unicode obsession:
  
    data _≡_ {a} {A : Set a} (x : A) : A → Set a where
      refl : x ≡ x

  Equality is an inductive datatype, just like lists. But one thing that's
  cool about the equality type is that it's something called a dependent type.
  A dependent type is a lot like a polymorphic type, but instead of taking
  a type argument (like the A in List A), it takes a _term_ argument
  (like the x in x ≡ x). Dependent types can refer to values!
  So we can define the type of all terms that prove our lists
  behave the way we want them to. And then we can write terms that
  have those types─our proofs.

  There is exactly one constructor for the equality type in Agda:
  refl, for reflexivity. Two things are equal by reflexivity when they
  compute to the same result. So if your rev function is correct,
  these test cases should compile:
-}

-- empty-nat doesn't change
rev-empty-nat-empty-nat : rev empty-nat ≡ empty-nat
rev-empty-nat-empty-nat = refl

-- empty-char doesn't change
rev-empty-char-empty-char : rev empty-char ≡ empty-char
rev-empty-char-empty-char = refl

-- [1; 2; 3; 4] becomes [4; 3; 2; 1]
rev-1-2-3-4-4-3-2-1 : rev 1-2-3-4 ≡ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
rev-1-2-3-4-4-3-2-1 = refl

-- [x; y; z] becomes [z; y; x]
rev-x-y-z-z-y-x : rev x-y-z ≡ 'z' ∷ 'y' ∷ 'x' ∷ []
rev-x-y-z-z-y-x = refl

{-
  These test cases are actually proofs! Even though they all hold
  by computation (reflexivity), they are terms, just like the lists
  we refer to inside of them. Their types are the theorems that they prove.
  
  That's the beauty of Curry-Howard; our terms here are proof objects
  that prove the theorems stated by the types they inhabit.
  These programs are proofs!

  So now it's your turn to test my length function and, in the process,
  write some proofs yourself.

  EXERCISE 2: Prove that 1-2-3-4 and x-y-z have the right lengths.
  As before, you'll want to replace each hole {! !} with your own code.
  This time, I want you to define both the types and the terms.
-}

-- 1-2-3-4 has the right length
length-1-2-3-4-OK : {! !}
length-1-2-3-4-OK = {! !}

-- x-y-z has the right length
length-x-y-z-OK : {! !}
length-x-y-z-OK = {! !}

{-
  Those proofs are very small proofs that hold by computation.
  There are also some cooler proofs we can prove by computation,
  like that appending the empty list to the left of any list
  gives us back that list:
-}

-- left identity of nil for append
app-nil-l : ∀ {A : Set} → (l : List A) → app [] l ≡ l -- type or theorem
app-nil-l l = refl -- term or proof

{-
  But sometimes we need to get fancier! For example, if we simply swap
  the [] and l in the type definition above above, to define app-nil-r,
  this will no longer hold by reflexivity, since app is defined by
  matching over the first list, not the second. Because of this,
  when you put the empty list as the first argument, Agda can reduce it;
  when you put it as the second argument instead, Agda cannot reduce it.
  
  If we try to prove app-nil-r by reflexivity, we'll get a scary looking
  type error, like this:

    app l [] != l of type List A
    when checking that the expression refl has type app l [] ≡ l

  But here's the thing─the equality is still true!
  It's just not true by computation. We have to prove it differently.
  Agda needs our help figuring this out.

  So let's help Agda. We're going to need to write some fancier proofs
  about equality. But how do we do that if there's just one constructor
  for equality─refl? Well, there are two things we can do with inductive
  datatypes: we can construct them, and we can pattern match over their cases
  (the latter is also called destructing them or, for reasons you'll see later,
  in specific contexts, inducting over them).
  
  Since equality is defined as an inductive type, we can pattern match
  over it just like we do over lists. When we do, there will be just one
  case─refl. But that actually turns out to give us a lot of power to
  prove some cool things about equality. So let's do that.

  Our first lemma is congruence, which comes from the standard library,
  and states that function application preserves equality:
-}

-- congruence
cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y -- the lemma
cong f refl = refl -- the proof

{-
  In other words, this matches over the input argument of type x ≡ y.
  Since equality has just one case, pattern matching breaks this into
  just one case, which is when that equality is refl.
  When that equality is refl, then we have x ≡ x.
  Thus, we are trying to show f x ≡ f x, which also holds by refl,
  since these terms are the same.

  One thing to note here is that it can be super hard to track this information
  in your head. In Agda, you can create holes in your functions
  by typing {! !}, much like I've done for you throughout. So you could write:

    cong f refl = {! !}

  If you compile that with C-c C-l, it'll change colors and there
  will be a 0 next to it, indicating that it's the 0th goal. In the AgdaInfo
  buffer, you'll see the goal that you need to satisfy for that hole:

    ?0 : f x ≡ f x

  This goal is the type you're trying to inhabit. From there,
  you can figure out that refl has that type, without having to track
  so much information in your head about what Agda is doing.

  With this, we should be able to prove app-nil-r:
-}

-- right identity of nil for append
app-nil-r : ∀ {A : Set} → (l : List A) → app l [] ≡ l
app-nil-r [] = refl
app-nil-r (h ∷ tl) = cong (λ l′ → h ∷ l′) (app-nil-r tl)

{-
  EXERCISE 3: Prove the lemma sym, which states that equality is symmetric.
  I have inserted a hole into this lemma, denoted {! !}, which may
  already look green if you've compiled this file. You can use the
  workflow described above to figure out the type you're trying to inhabit.
-}

-- symmetry of equality
sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = {! !}

{-
  EXERCISE 4: Prove that l ≡ app l [], using symmetry. I have inserted
  a hole into this lemma where you will need to figure out a term.
-}

-- symmetric right identity of nil for append
app-nil-r-sym : ∀ {A : Set} → (l : List A) → l ≡ app l []
app-nil-r-sym l = sym {! !}

{-
  EXERCISE 5: Prove the lemma trans, which states that equality
  is transitive. I have inserted a hole into this lemma as well.
-}

-- transitivity of equality
trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = {! !}

{-
  Equalities like this that we have to prove by pattern matching over
  the equality type are what we called propositional equalities
  in QED at Large. This is in contrast with definitional equalities,
  which hold by computation.

  For example, app [] l and l are definitionally equal, since Agda
  reduces both of them to the same term. But app l [] and l are not
  definitionally equal, as we saw earlier, since app is defined by
  pattern matching over the first term rather than the second.
  They are only propositionally─provably, that is─equal.

  In Agda, Coq, and Lean, two things that are definitionally equal are
  necessarily propositionally equal, but the reverse is not necessarily true.
  This is why we can't prove app-nil-r by reflexivity.

  This is important to pay attention to─in many of these languages, it is
  really standard for your proofs to mirror the structure of
  the programs they are about. There is a deep type theoretical
  reason that this is true.

  ASIDE: Definitional equality is─for many proof assistants we care about in
  this class─a decidable judgment that follows from a few reduction rules,
  like unfolding some constants (δ-expansion), applying functions to
  arguments (Β-reduction, which is sometimes called ι-reduction for
  inductive datatypes), renaming (α-conversion), and more.

  These may sound familiar if you're familiar with the λ-calculus,
  a simple functional programming language that is often used as an example
  in programming languages courses. The proof assistants Agda, Coq, and Lean
  all build on extensions of the λ-calculus with not just simple types,
  but also polymorphism (like how list takes a type argument A), dependent
  types (like how ≡ takes a term argument x), and inductive types (like
  how both the list and ≡ datatypes are defined by defining all ways to
  construct them).
  
  But if you haven't heard of these, that's OK. I super recommend reading this
  chapter of Certified Programming with Dependent Types by Adam Chlipala:
  http://adam.chlipala.net/cpdt/html/Equality.html. If you'd like more
  information, that will really help─though it's in Coq. I hope to
  show you some automation that steps through equalities like this next week.

  BACK TO BUSINESS: It can be kind of annoying to keep pattern matching
  over equality, which is why the lemmas above─also defined in the standard
  library─can be really useful.

  An especially useful lemma about equality is substitution,
  which is also found inside of the standard library:
-}

-- substitution
subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

{-
  This states that for any property P, if x ≡ y, and we have a proof
  that P x holds, we can substitute y for x inside of that to show
  that P y holds. This is really powerful, but a little hard to use,
  because you have to figure out what P is. For example, here is a proof
  of app-nil-r using subst instead of cong:
-}

-- right identity of nil for append, proven by substitution instead
app-nil-r′ : ∀ {A : Set} → (l : List A) → app l [] ≡ l
app-nil-r′ [] = refl
app-nil-r′ (h ∷ tl) = subst (λ l′ → h ∷ l′ ≡ h ∷ tl) (sym (app-nil-r′ tl)) refl

{-
  Your turn to try. You can use cong or subst here─whatever you find
  more convenient.

  EXERCISE 6: Finish the proof of length-succ-r.
-}
length-succ-r :
  ∀ {A} → (l : List A) → (a : A) → length (app l (a ∷ [])) ≡ suc (length l)
length-succ-r [] a = refl  -- base case
length-succ-r {A} (h ∷ tl) a = -- inductive case
  {! !}

{-
  EXERCISE 7: Show that the reverse function that you wrote preserves
  the length of the input list. You may use length-succ-r, and any of the
  equality lemmas we've defined so far like trans, subst, sym, and
  cong. (You probably won't need all of them.)
-}
rev-pres-length : ∀ {A} → (l : List A) → length (rev l) ≡ length l
rev-pres-length [] = {! !}
rev-pres-length (h ∷ tl) = {! !}

{-
  That's it for now! You can keep playing with other proofs if you have
  extra time. If you have a lot of extra time, I recommend looking at the
  Agda source code on Github to get a sense for how it's implemented:
  https://github.com/agda/agda. In any case, when we have 25 minutes
  left of class, please do this:

    1. Turn to your group and discuss the question below.
    2. Post your answer─just one answer for your group, clearly indicating
       all members of the group. (If you are not here, and are working alone,
       you can post your answer alone.)
    3. With 10 minutes left, finish posting your answer, so we can discuss
       a bit as a class.

  You'll be graded based on whether you post an answer, not based on
  what it is, so don't worry too much about saying something silly.

  DISCUSSION QUESTION: What was it like constructing these proofs directly,
  as terms in a programming language? What did you find challenging about
  this experience, if anything? What did you find helpful, if anything? Did
  you get stuck at any point, and if so, where and why? Where do you wish
  you'd had more automation to help you out?
-}

