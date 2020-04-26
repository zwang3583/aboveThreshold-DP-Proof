require import Int IntExtra Real RealExtra Ring.
require import Distr List Aprhl StdRing StdOrder StdBigop.
  (*---*) import IntID IntOrder RField RealOrder.

  (* we define two positive constants eps, del  that we will 
     use to reason about our privacy budget*)

op eps: { real | 0%r <= eps } as ge0_eps.
op del: { real | 0%r <= del } as ge0_delta.

hint exact : ge0_eps.
hint exact : ge0_delta.

(* used by trivial only if exact *)

(*
   Our first example shows how we can use the laplace 
   distribution to reason about differential privacy for two 
   values that differ by at most one. 
*)

module M = {
  var x: int
  proc f (): int = {
    var r = 0;
      r <$ lap eps x;
    return r;
  }
}.



(* 
   An equivalence judgment in aprhl is parametrized 
   by two parameters epsilon and delta.
*) 

lemma lem1 : aequiv [ [eps & 0%r]
  M.f ~ M.f
 :  (`|M.x{1} - M.x{2}|<= 1)  
==> res{2} = res{1} ].
proof.
  proc.
  seq 1 1 :(`|M.x{1} - M.x{2}|<= 1 /\ r{1}=r{2} /\ r{1}=0). 
  wp.
  (* 
   here we would like to apply the skip rule from aprhl but
   the same result can be achieved by switching to pHL if we 
   guarantee that this doesn't affect the privacy parameters.
   This is achieved by making them not available in pHL. 
   *)  
  toequiv.
  auto.
(* 
   to prove this we can use the lap tactic which takes two 
   parameters  k1 and k2 and generate two subgoals 
   1) k2 * local_eps <= global eps
   2) |k1 + (M.x{1} - M.x{2})| <= k2
*) 
  lap (0) 1.  
qed.


lemma lem1Fail1 : aequiv [ [eps & 0%r]
  M.f ~ M.f
 :  (`|M.x{1} - M.x{2}|<= 1)  
==> res{2} = res{1} ].
proof.
  proc.
  seq 1 1 :(`|M.x{1} - M.x{2}|<= 1 /\ r{1}=r{2} /\ r{1}=0). 
  wp.
  toequiv.
  auto.
  lap (0) 0 => //. (* we cannot prove this *)
  admit.
qed.

lemma lem1Fail2 : aequiv [ [eps & 0%r]
  M.f ~ M.f
 :  (`|M.x{1} - M.x{2}|<= 1)  
==> res{2} = res{1} ].
proof.
  proc.
  seq 1 1 :(`|M.x{1} - M.x{2}|<= 1 /\ r{1}=r{2} /\ r{1}=0). 
  wp.
  toequiv.
  auto.
  lap (1) 0 => //.  (* we cannot prove this *)
  admit.
qed.

(* since we have (eps,0)-DP we can also prove (eps,delta)-DP *)

lemma lem1withDelta : aequiv [ [eps & del]
  M.f ~ M.f
 :  (`|M.x{1} - M.x{2}|<= 1)  
==> res{2} = res{1} ].
proof.
  proc.
  seq 1 1 :(`|M.x{1} - M.x{2}|<= 1 /\ r{1}=r{2} /\ r{1}=0).
  wp.
  toequiv.
  auto.
  lap (0) 1 => //. 
qed.


(* we now want to look at composition *)

module M1 = {
  var d: int * int
  proc f (): int * int = {
    var r = 0;
    var s = 0;
    var (z,y)<-d;
      r <$ lap eps z;
      s <$ lap eps y;
    return (r,s);
  }
}.

(* 
   we assume that the data are now a pair of integers, 
   and we want to release both of them 
*)


lemma lem2 : aequiv [ [(eps*2%r) & del]
  M1.f ~ M1.f
 :  (`|M1.d{1}.`1 - M1.d{2}.`1|<= 1 /\ `|M1.d{1}.`2 - M1.d{2}.`2|<= 1)  
==> res{2} = res{1}].
proof.
  proc.
  seq 3 3 :( `|z{1} - z{2}|<= 1/\ `|y{1} - y{2}|<= 1).
  wp. toequiv. skip. trivial.
  seq 1 1 : (r{1}=r{2} /\ `|y{1} - y{2}|<= 1) <[ eps & del ]>.
  lap (0) 1 => //. 
  lap (0) 1. smt().
qed.

(* 
if we knew that part of the data is always the same we could still apply 
Laplace but only pay for the difference 
*)

lemma lem2par : aequiv [ [eps & del]
  M1.f ~ M1.f
    :  (`|M1.d{1}.`1 - M1.d{2}.`1|<= 1 /\ M1.d{1}.`2 = M1.d{2}.`2)
==> res{2} = res{1}].
proof.
  proc.
  seq 3 3 :( `|z{1} - z{2}|<= 1/\ y{1} =y{2}).
  wp. toequiv. skip. trivial.
  seq 1 1 : (r{1}=r{2} /\ y{1} = y{2}) <[ eps & del ]>.
  lap (0) 1 => //. 
  lap (0) 0. 
(* 
  we could have just avoid using laplace at all in the algorithm, 
  but the point of this example is to show how the same algorithm 
  can be analyzed in different ways. We will also see that this idea 
  is behind the idea of parallel composition
*)  
qed.

(* 
   so far we have assumed that we have only one data point 
   and we know that this is the data that may differ. However, 
   in general we are interested in situations where we have a whole 
   dataset
*)

module M2 = {
  proc sum (ls : int list) : int = {
    var s : int <- 0;
    var z : int;
    var i : int;
    i <- 0;
    while (i < size ls) {
      s <- s + (nth 0 ls i);
      i <- i + 1;
    }
    z <$ lap eps s;
    return z;
  }
}.


(* 
  To reason about this example we need to formulate 
  our notion of adjacency. We will start with some additional notion.
*)

pred eq_in_range (ms ns : int list, i j : int) =
  forall (k : int),
  i <= k <= j => nth 0 ms k = nth 0 ns k.

lemma eq_in_range_succ (ms ns : int list, i j : int) :
  eq_in_range ms ns i j => eq_in_range ms ns (i + 1) j.
proof.
move => eir_i.
rewrite /eq_in_range => k le_iplus1_k_j.
rewrite eir_i /#.
qed.

(* 
  here our definition of adjacency
*)
pred adjacent (ms ns : int list) =
  size ms = size ns /\
  (exists (i : int),
   0 <= i < size ms /\
   eq_in_range ms ns 0 (i - 1) /\
   `|nth 0 ms i - nth 0 ns i| <= 1 /\
   eq_in_range ms ns (i + 1) (size ms - 1)).

(* 
 we can prove some lemma about this. 
*)

lemma size_eq_adjacent (ms ns : int list) :
  adjacent ms ns => size ms = size ns.
proof.
rewrite /adjacent => [#] -> //.
qed.

lemma adjacent_sub_abs_bound (ms ns : int list, i : int) :
  adjacent ms ns => 0 <= i < size ms =>
  `|nth 0 ms i - nth 0 ns i| <= 1.
proof.  
rewrite /adjacent =>
  [#] eq_siz [] k [#] ge0_k lt_k_size_ms eq_before
  abs_bnd_k eq_after [#] ge0_i lt_i_siz.
case (i = k) => [-> // | ne_i_k].
rewrite neq_ltz in ne_i_k; elim ne_i_k => [lt_i_k | lt_k_i].
have -> : nth 0 ms i = nth 0 ns i.
  apply eq_before.
  split => [| _].
  apply ge0_i.
  by rewrite StdOrder.IntOrder.ler_subr_addr -ltzE.
by rewrite addzN.
have -> : nth 0 ms i = nth 0 ns i.
  apply eq_after.
  split => [| _].
  by rewrite -ltzE.
  by rewrite StdOrder.IntOrder.ler_subr_addr -ltzE.
by rewrite addzN.
qed.

lemma adjacent_ne_sub_eq_after (ms ns : int list, i : int) :
  adjacent ms ns => 0 <= i < size ms => nth 0 ms i <> nth 0 ns i =>
  eq_in_range ms ns (i + 1) (size ms - 1).
proof.
rewrite /adjacent =>
  [#] eq_siz [] k [#] ge0_k lt_k_size_ms eq_before
  abs_bnd_k eq_after [#] ge0_i lt_i_siz ne_at_i.
case (i = k) => [-> // | ne_i_k].
rewrite neq_ltz in ne_i_k; elim ne_i_k => [lt_i_k | lt_k_i].
have // : nth 0 ms i = nth 0 ns i by rewrite eq_before /#.
have // : nth 0 ms i = nth 0 ns i by rewrite eq_after /#.
qed.

(* 
  we can now prove the previous program differentially private
*) 

lemma lem3 :
  aequiv
  [[ eps & 0%r]
   M2.sum ~ M2.sum : adjacent ls{1} ls{2} ==> res{1} = res{2}].
proof.
proc.
seq 2 2: (adjacent ls{1} ls{2} /\ ={i, s} /\ i{1} = 0 /\ s{1} = 0).
auto. toequiv. auto.
seq 1 1 : (`|s{1} - s{2}| <= 1).
toequiv.
while
  (adjacent ls{1} ls{2} /\ ={i} /\ 0 <= i{1} <= size ls{1} /\
   (! ={s} =>
    `|s{1} - s{2}| <= 1 /\
     eq_in_range ls{1} ls{2} i{1} (size ls{1} - 1))).
 wp. skip. progress.
smt().
smt().
smt(adjacent_sub_abs_bound).
smt(adjacent_ne_sub_eq_after).
smt(size_eq_adjacent).
smt(size_eq_adjacent).
auto; progress.
rewrite size_ge0.
smt(size_eq_adjacent).
smt(size_eq_adjacent).
smt(addzN).
     lap (0) 1.
qed.

(* 
  the previous example still adds noise only at the end. 
  What shall we do if we want to add noise in an iterative way?
  Let's consider releasing all the partial sums of a vector:
  e.g. on input [1,2,3,4,5] we want to release [1,3,6,10,15]
*) 


module M4 = {
  proc dummy_sum (ls : int list) : int list = {
    var s :int <- 0;
    var output : int list;
    var z : int;
    var i :int <- 0;
    output = [];
    while (i < size ls ) {
      s = s + (nth 0 ls i); 
      i <- i + 1;
      (* notice that the laplace noise is now added in the loop *)
      z <$ lap eps s;
      output = z :: output;
    }
    return output;
  }
}.

(*
  we now want to prove that the budget that we spend depends on the size of the list
*)

lemma dummy_sum n : 0<=n => aequiv [ [  (eps *n%r) & 0%r]
  M4.dummy_sum ~ M4.dummy_sum
 :  (adjacent ls{1} ls{2}  /\ n = size ls{1})
      ==> res{2} = res{1} ].
    proof.
    move => H.
    proc.
    seq 3 3: (adjacent ls{1} ls{2} /\ ={i, s, output} /\ i{1} = 0
              /\ s{1} = 0  /\ 0<= n /\ n = size ls{1} ).
    toequiv; auto.
    (*
      we could try to use the usual while rule but this would not bring us very far.
      Instead, we use the approximate while rule which takes as additional parameters
     two functions describing how the privacy budget change at each iteration, and how 
     the number of iterations decreases.
    *)
    awhile  [ (fun _ => eps) & (fun _ => 0%r) ] n [n-i-1] 
    (adjacent ls{1} ls{2} /\ ={i, output} /\ 0 <= i{1} <= n /\
     (! ={s} => `|s{1} - s{2}| <= 1 /\
     eq_in_range ls{1} ls{2} i{1} (n - 1)) /\
     0<= n /\ n = size ls{1});
     first 3 try (auto; progress;smt(ge0_eps)).
     (*
       we here have to manage bigops
     *) 
     rewrite sumr_const count_predT size_range max_ler. 
     smt().
     rewrite intmulr; auto.
     rewrite sumr_const intmulr;auto.
     move => v.
     seq 2 2:
     (adjacent ls{1} ls{2} /\ ={i, output} /\ 0 <= i{1} <= size ls{1} /\
     (! ={s} => `|s{1} - s{2}| <= 1 /\
     eq_in_range ls{1} ls{2} i{1} (size ls{1} - 1)) /\
     0<= n /\ n = size ls{1} /\ v=n-i{1}).
     toequiv; auto; progress.
     smt(). smt().
     smt(adjacent_sub_abs_bound).
     smt(adjacent_ne_sub_eq_after).
     smt().
     seq 1 1:
     (adjacent ls{1} ls{2} /\ ={i, output} /\ 0 <= i{1} <= size ls{1} /\
     (! ={s} => `|s{1} - s{2}| <= 1 /\
     eq_in_range ls{1} ls{2} i{1} (size ls{1} - 1)) /\
     0<= n /\ n = size ls{1} /\ v=n-i{1} /\ z{1}=z{2}) <[ eps & 0%r ]>.
     lap (0) 1.   
     auto; progress.
     smt().
     toequiv; auto; progress.
     smt().
     smt().
qed.


