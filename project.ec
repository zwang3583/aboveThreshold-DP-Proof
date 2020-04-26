require import Int IntExtra Real RealExtra Ring.
require import Distr List Aprhl StdRing StdOrder StdBigop.
import IntID IntOrder RField RealOrder.

(* defines epsilon and the query*)
op eps: {real | 0%r <= eps } as ge0_eps.
op evalQ: int -> int list -> int.
hint exact : ge0_eps.

(* the notion of adjacent databases are from lab*)
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
  
pred adjacent_e (ms ns : int list) (i:int)=
  size ms = size ns /\
   0 <= i < size ms /\
   eq_in_range ms ns 0 (i - 1) /\
   `|nth 0 ms i - nth 0 ns i| <= 1 /\
   eq_in_range ms ns (i + 1) (size ms - 1).

(* formal definition of adjacent databases *)
pred adjacent (ms ns : int list) = exists i, adjacent_e ms ns i. 

(* lemmas of adjacency from lab*)
lemma size_eq_adjacent (ms ns : int list) :
  adjacent ms ns => size ms = size ns.
  proof.
rewrite /adjacent. rewrite /adjacent_e => [#].
smt().
qed.

lemma adjacent_sub_abs_bound (ms ns : int list, i : int) :
  adjacent_e ms ns i => 0 <= i < size ms =>
  `|nth 0 ms i - nth 0 ns i| <= 1.
proof.  
  rewrite /adjacent_e. smt().  
qed.

lemma adjacent_ne_sub_eq_after (ms ns : int list, i : int) :
  adjacent_e ms ns i => 0 <= i < size ms => nth 0 ms i <> nth 0 ns i =>
  eq_in_range ms ns (i + 1) (size ms - 1).
proof.
rewrite /adjacent_e. smt(). 
qed.

(* assume that the query is one sensitive *)
axiom one_sens d1 d2 q: adjacent d1 d2 => `| evalQ q d1 - evalQ q d2 | <= 1.

(* the above threshold algorithm *)
module M = {
  proc aboveT (db : int list, t : int) : int = {
    var i : int;
    var nT : int;
    var r : int;
    var s : int;
    s <- 0;
    i <- 0;
    r <- -1;
    (* noisy threshold*)
    nT <$ lap (eps/4%r) t;
    while (i < size db) {
      s <$ lap (eps/2%r) (evalQ i db);
      if (nT < s /\ r = -1){
        r <- i;
      }
      i <- i + 1;
    }
    return r;
  }
}.

lemma commutative (x y z : real) : x + y - z = x -z + y.
proof.
  smt().
qed.

lemma sub_equal (x y : real) : x <= y /\ y <= x => x - y = 0%r.
proof.
  smt().
qed.

lemma add_zero(x : real) : 0%r + x = x.
proof.
  smt().
qed.

lemma mult_comm (x y z: real) : x * y * z = y * z * x.
proof.
  smt().
qed.    

lemma dp_composition n : 0<=n => aequiv
 [ [(eps/4%r + n%r*(eps/2%r)) & 0%r]
  M.aboveT ~ M.aboveT :  (adjacent db{1} db{2}  /\ n = size db{1} /\ ={t}) ==> res{2} = res{1} ].
proof.
  move => H.
  proc.
(*
   the lap tactic takes two parameters  k1 and k2 and generate two subgoals 
   1) k2 * local_eps <= global eps
   2) |k1 + (M.x{1} - M.x{2})| <= k2
*)
  seq 3 3 :  (adjacent db{1} db{2} /\ ={s, i, r, t} /\
            s{1} = 0 /\ i{1} = 0 /\ r{1} = -1 /\ 0<=n /\ n = size db{1}). 
  toequiv; auto.
  seq 1 1 : (adjacent db{1} db{2} /\ ={s, i, r, t, nT} /\
            s{1} = 0 /\ i{1} = 0 /\ r{1} = -1 /\ 0<=n /\ n = size db{1}) <[ (eps/4%r) & 0%r ]>.
  lap 0 1.
(*
   instead, we use the approximate while rule which takes as additional parameters
   two functions describing how the privacy budget change at each iteration, and how 
   the number of iterations decreases.
*)
  awhile  [ (fun _ => eps/2%r) & (fun _ => 0%r) ] n [n-i-1] 
     (adjacent db{1} db{2} /\ ={i, r, t, nT} /\ 0 <= i{1} <= n /\
     (! ={s} => `|s{1} - s{2}| <= 1 /\ eq_in_range db{1} db{2} i{1} (n - 1)) /\
       0<=n /\ n = size db{1}); first 3 try smt(ge0_eps).
   
  rewrite commutative sub_equal.
  smt().
  rewrite add_zero.
  rewrite mult_comm.
  rewrite sumr_const count_predT size_range max_ler.
  smt().
  rewrite intmulr; auto.   
  rewrite sumr_const intmulr; auto.
  move => v. 
  wp.
  lap 0 1. 
  progress.
  smt(one_sens).
  progress.
  smt().
  smt().
  smt().
  smt().
  smt().
  smt().
  smt().   
  smt().
qed.
