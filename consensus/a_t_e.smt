;A_t_e (algorithm 1 from "tolerating corrupted communication")
(set-option :print-success false)
(set-option :produce-models true)
(set-option :smt.pull-nested-quantifiers true)
(set-option :smt.mbqi true)
(set-logic AUFLIA)

;types
(declare-sort Process 0)
;(declare-sort Value 0)
(declare-sort Set 1)

(declare-fun elem ((Set Process) Process) Bool)
(declare-fun card ((Set Process)) Int)

; consts
(declare-fun  HO (Process) (Set Process))
(declare-fun SHO (Process) (Set Process))
(declare-fun AHO (Process) (Set Process))
(declare-fun n () Int)
(declare-fun T () Int)
(declare-fun E () Int)
(declare-fun alpha () Int)
(declare-fun decided  () (Set Process))
(declare-fun decided1 () (Set Process))
(declare-fun x  (Process) Int)
(declare-fun x1 (Process) Int)

;some (skolem) constants for the invariant
(declare-fun v () Int) ; prophecy variable for the decided value
(declare-fun A () (Set Process))
(declare-fun A1 () (Set Process))

;Assumptions for safety
(assert
  (and
; \forall p. |AHO(p)| <= \alpha 
    (forall ((p Process))
      (and
         (<= (card (AHO p)) alpha)
         (= (+ (card (SHO p)) (card (AHO p))) (card (HO p))); HO is partitioned into SHO and AHO
    ) )
; α < n/4
    (< (* 4 alpha) n)
    (<= 0 alpha)
; n > T >= 2*(n + 2*α - E)
    (>= T (* 2 (+ n (* 2 alpha) (* -1 E))))
    (<= 0 T)
    (< T n)
; n > E >= n/2 + α
    (>= (* 2 E) (+ n (* 2 alpha)))
    (<= 0 E)
    (< E n)
) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Auxilliary function:

; received
(declare-fun recv ((Process) (Int)) (Set Process))

(assert
  (forall ((p1 Process) (p2 Process) (v Int) (s (Set Process)))
    (=> (= (recv p1 v) s)
      (= (elem s p2)
        (or; modified for the Byzantine case
          (and (elem (SHO p1) p2) (= (x p2) v))
          (elem (AHO p1) p2)
) ) ) ) )

; min most often received 
(declare-fun mmor_v (Process) Int)
(assert
  (forall ((p1 Process) (v1 Int) (v2 Int))
    (=> (= (mmor_v p1) v1)
      (or
        (> (card (recv p1 v1)) (card (recv p1 v2)))
        (and
          (= (card (recv p1 v1)) (card (recv p1 v2)))
          (<= v1 v2)
) ) ) ) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Venn region and co.

(declare-fun ts (Process) Int) ; safe
(declare-fun ta (Process) Int) ; altered
(declare-fun tf (Process) Int) ; not in HO
(declare-fun fs (Process) Int) 
(declare-fun fa (Process) Int) 
(declare-fun ff (Process) Int) 

(assert
  (forall ((p Process))
    (and
      (>= (ts p) 0)
      (>= (ta p) 0)
      (>= (tf p) 0)
      (>= (fs p) 0)
      (>= (fa p) 0)
      (>= (ff p) 0)
      (= (+ (ts p) (ta p) (tf p) (fs p) (fa p) (ff p)) n)
      (= (card (HO p)) (+ (ts p) (ta p) (fs p) (fa p)))
      (= (card (SHO p)) (+ (ts p) (fs p)))
      (= (card (AHO p)) (+ (ta p) (fa p)))
      (>= (card A) (+ (ts p) (tf p)))
      (<= (card A) (+ (ts p) (ta p) (tf p)))
      (>= (card (recv p v)) (ts p))
      (<= (card (recv p v)) (+ (ts p) (ta p)))
) ) )

(assert
  (forall ((p Process) (v1 Int) (v2 Int))
    (=>
      (not (= v1 v2))
      (>= (card (HO p)) (+ (card (recv p v1)) (card (recv p v2))))
) ) )

;inclusion of A and A′
(assert
  (=> (forall ((i Process)) (=> (elem A i) (elem A1 i)))
      (<= (card A) (card A1)))
)

;basic truth about cardinality
(assert (forall ((s (Set Process))) (<= 0 (card s))))
(assert (forall ((s (Set Process))) (>= n (card s))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(push)
(echo "invariant is inductive")

;invariant:
;  ∀ p. ¬decided(p)
;∨
;  ∃ v. A = {p | x[p]=v}
;    ∧ |A| > E - α
;    ∧ ∀ p. decided[p] ⇒ x[p] = v
(assert
  (and
    (forall ((i Process)) (= (elem A i) (= (x i) v)) )
    (or
      (forall ((i Process)) (not (elem decided i)) )
      (and
        (> (card A) (+ E (* -1 alpha)))
        (forall ((i Process)) (=> (elem decided i) (= (x i) v)))
) ) ) )

;invariant negated:
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (and
    (elem decided1 sk_j)
    (= (x1 sk_j) v); needed for the first decision
    (forall ((i Process)) (= (elem A1 i) (= (x1 i) v)))
    (or
      (<= (card A1) (+ E (* -1 alpha)))
      (and (elem decided1 sk_i) (not (= (x1 sk_i) v)))
) ) ) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:
;if  | HO(p) | > T then
;    x[p] := mmor
;if  \exists v. |HO(p) \cap {q | x[q] = v}| > E then
;    decide(v)

(assert
  (forall ((i Process))
    (and
      (=>
        (and
          ;(> (card (HO i)) T)
          (> (card (recv i (mmor_v i))) E)
        )
        (and
          (= (x1 i) (mmor_v i))
          (elem decided1 i)
        )
      )
      (=>
        (and
          (> (card (HO i)) T)
          (<= (card (recv i (mmor_v i))) E)
        )
        (and
          (= (x1 i) (mmor_v i))
          (= (elem decided i) (elem decided1 i))
        )
      )
      (=>
        (and
          (<= (card (HO i)) T)
          (<= (card (recv i (mmor_v i))) E)
        )
        (and
          (= (x1 i) (x i))
          (= (elem decided i) (elem decided1 i))
        )
      )
) ) )


(check-sat)
;(get-model)
(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(push)
(echo "initial state ⇒ invariant")

(assert (forall ((p Process)) (not (elem decided p))))

;invariant negated:
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (and
    (elem decided sk_j)
    (forall ((i Process)) (= (elem A i) (= (x i) v)))
    (or
      (<= (card A) (+ E (* -1 alpha)))
      (and (elem decided sk_i) (not (= (x sk_i) v)))
) ) ) 

(check-sat)
;(get-model)
(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(push)
(echo "agreement")

;invariant:
;  ∀ p. ¬decided(p)
;∨
;  ∃ v. A = {p | x[p]=v}
;    ∧ |A| > E - α
;    ∧ ∀ p. decided[p] ⇒ x[p] = v
(assert
  (or
    (forall ((i Process)) (not (elem decided i)) )
    (and
      (> (card A) (+ E (* -1 alpha)))
      (forall ((i Process))
        (and
          (= (elem A i) (= (x i) v))
          (=> (elem decided i) (= (x i) v))
) ) ) ) )

(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (and
    (elem decided sk_i)
    (elem decided sk_j)
    (not (= (x sk_i) (x sk_j)))
  )
)

(check-sat)
;(get-model)
(pop)


(echo "termination")
(push)

;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:
;if  | HO(p) | > T then
;    x[p] := mmor
;if  \exists v. |HO(p) \cap {q | x[q] = v}| > E then
;    decide(v)

(assert
  (forall ((i Process))
    (and
      (=>
        (and
          ;(> (card (HO i)) T)
          (> (card (recv i (mmor_v i))) E)
        )
        (and
          (= (x1 i) (mmor_v i))
          (elem decided1 i)
        )
      )
      (=>
        (and
          (> (card (HO i)) T)
          (<= (card (recv i (mmor_v i))) E)
        )
        (and
          (= (x1 i) (mmor_v i))
          (= (elem decided i) (elem decided1 i))
        )
      )
      (=>
        (and
          (<= (card (HO i)) T)
          (<= (card (recv i (mmor_v i))) E)
        )
        (and
          (= (x1 i) (x i))
          (= (elem decided i) (elem decided1 i))
        )
      )
) ) )

;-for termination
; (a) \exists S_1 S_2. (|S_1| > E - \alpha) \land (|S_2| > T) \land (\forall p. p \in S_1 => HO(p) = SHO(p) = S_2) 
; (b) \forall p. | HO(p)| > T
; (c) \forall p. |SHO(p)| > E
 
(push)
(echo "1st magic round")

;magic round assumption
(declare-fun S1 () (Set Process))
(declare-fun S2 () (Set Process))
(assert
  (and
    (> (card S1) (+ E (* -1 alpha)))
    (> (card S2) T)
    (forall ((i Process))
      (=>
        (elem S1 i)
        (and
          (= (HO i) S2)
          (= (SHO i) S2)
) ) ) ) )

(assert
  (forall ((p Process))
    (=>
      (= (elem S1 p) (= (x1 p) v))
      (= (card S1) (card A1))
    )
  )
)

;//Invariant negated (new part):
(declare-fun sk_i () (Process))
(assert
  (and
    (elem S1 sk_i)
    (= (x1 sk_i) v); manual instanciation of the ∀
    (forall ((i Process)) (= (elem A1 i) (= (x1 i) v)))
    (<= (card A1) (+ E (* -1 alpha)))
) ) 

;some more Venn regions

(check-sat)
;(get-model)
(pop)

(push)
(echo "1st termination invariant is inductive")

;-after (a)
;  \exists v. A = {p | x[p]=v}
;    \land |A| > E - \alpha
;    \land \forall p. decided[p] => x[p] = v
(assert
  (and
    (> (card A) (+ E (* -1 alpha)))
    (forall ((i Process))
      (and
        (= (elem A i) (= (x i) v))
        (=> (elem decided i) (= (x i) v))
) ) ) )

;//Invariant negated (new part):
(declare-fun sk_i () (Process))
(assert
  (and
    (forall ((i Process)) (= (elem A1 i) (= (x1 i) v)))
    (<= (card A1) (+ E (* -1 alpha)))
) ) 

(check-sat)
;(get-model)
(pop)

(push)
(echo "2nd magic round")

;-after (a)
;  \exists v. A = {p | x[p]=v}
;    \land |A| > E - \alpha
;    \land \forall p. decided[p] => x[p] = v
(assert
  (and
    (> (card A) (+ E (* -1 alpha)))
    (forall ((i Process))
      (and
        (= (elem A i) (= (x i) v))
        (=> (elem decided i) (= (x i) v))
) ) ) )

;magic round assumption
; (c) \forall p. |HO(p)| > T
(assert (forall ((p Process)) (> (card (HO p)) T)))


;//Invariant negated (new part):
(declare-fun sk_i () (Process))
(assert (not (= (x1 sk_i) v)))

(check-sat)
;(get-model)
(pop)

(push)
(echo "2nd termination invariant is inductive")

;-after (b)
;  \exists v. A = {p | x[p]=v}
;    \land |A| = n
;    \land \forall p. decided[p] => x[p] = v
(assert
  (and
    (= (card A) n)
    (forall ((i Process))
      (and
        (elem A i)
        (= (x i) v)
        (=> (elem decided i) (= (x i) v))
) ) ) )

;//Invariant negated (new part):
(declare-fun sk_i () (Process))
(assert (not (= (x1 sk_i) v)))

(check-sat)
;(get-model)
(pop)

(push)
(echo "3rd magic round")

;magic round assumption
; (c) \forall p. |SHO(p)| > E
(assert (forall ((p Process)) (> (card (SHO p)) E)))

;-after (b)
;  \exists v. A = {p | x[p]=v}
;    \land |A| = n
;    \land \forall p. decided[p] => x[p] = v
(assert
  (and
    (= (card A) n)
    (forall ((i Process))
      (and
        (= (elem A i) (= (x i) v))
        (=> (elem decided i) (= (x i) v))
) ) ) )

;termination
;    \forall p. decided[p]
(declare-fun sk_i () (Process))
(assert (not (elem decided1 sk_i)))

(check-sat)
;(get-model)
(pop)

(pop)

(push)
(echo "validity")

;assumption
(declare-fun val () Int)
(assert (forall ((p Process)) (= (x p) val) ) )

;invariant:
;  ∀ p. ¬decided(p)
;∨
;  ∃ v. A = {p | x[p]=v}
;    ∧ |A| > E - α
;    ∧ ∀ p. decided[p] ⇒ x[p] = v
(assert
  (and
    (forall ((i Process)) (= (elem A i) (= (x i) v)) )
    (or
      (forall ((i Process)) (not (elem decided i)) )
      (and
        (> (card A) (+ E (* -1 alpha)))
        (forall ((i Process)) (=> (elem decided i) (= (x i) v)))
) ) ) )

(declare-fun sk_i () (Process))
(assert
  (=>
    (> (card A ) 0)
    (and
      (elem A sk_i)
      (= (x sk_i) v)
    )
  )
)
(declare-fun sk_j () (Process))
(assert (elem decided sk_j))
;to prove
(assert (not (= v val)))

(check-sat)
;(get-model)
(pop)

(push)
(echo "integrity: one irrevoable decision")

;to prove
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (or
    (and (elem decided sk_i) (not (elem decided1 sk_i)))
    (and (elem decided sk_j) (not (= (x1 sk_j) (x sk_j))))
) ) 

;invariant:
;  ∀ p. ¬decided(p)
;∨
;  ∃ v. A = {p | x[p]=v}
;    ∧ |A| > E - α
;    ∧ ∀ p. decided[p] ⇒ x[p] = v
(assert
  (and
    (forall ((i Process)) (= (elem A i) (= (x i) v)) )
    (or
      (forall ((i Process)) (not (elem decided i)) )
      (and
        (> (card A) (+ E (* -1 alpha)))
        (forall ((i Process)) (=> (elem decided i) (= (x i) v)))
) ) ) )

;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:
;if  | HO(p) | > T then
;    x[p] := mmor
;if  \exists v. |HO(p) \cap {q | x[q] = v}| > E then
;    decide(v)

(assert
  (forall ((i Process))
    (and
      (=>
        (and
          ;(> (card (HO i)) T)
          (> (card (recv i (mmor_v i))) E)
        )
        (and
          (= (x1 i) (mmor_v i))
          (elem decided1 i)
        )
      )
      (=>
        (and
          (> (card (HO i)) T)
          (<= (card (recv i (mmor_v i))) E)
        )
        (and
          (= (x1 i) (mmor_v i))
          (= (elem decided i) (elem decided1 i))
        )
      )
      (=>
        (and
          (<= (card (HO i)) T)
          (<= (card (recv i (mmor_v i))) E)
        )
        (and
          (= (x1 i) (x i))
          (= (elem decided i) (elem decided1 i))
        )
      )
) ) )

(check-sat)
;(get-model)
(pop)


(exit)

