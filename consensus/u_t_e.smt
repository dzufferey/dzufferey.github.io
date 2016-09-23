;U_t_e (algorithm 2 from "tolerating corrupted communication")
(set-option :print-success false)
(set-option :produce-models true)
(set-option :model.compact true)
(set-option :model.partial true)
(set-option :smt.pull-nested-quantifiers true)
(set-option :smt.mbqi true)
(set-logic AUFLIA)

;types
(declare-sort Process 0)
(declare-sort Value 0)
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
(declare-fun x  (Process) Value)
(declare-fun x1 (Process) Value)
(declare-fun voting  () (Set Process))
(declare-fun voting1 () (Set Process))
(declare-fun vote  (Process) Value)
(declare-fun vote1 (Process) Value)

;some (skolem) constants for the invariant
(declare-fun v0 () Value) ; default choice
(declare-fun v () Value) ; prophecy variable for the decided value
(declare-fun A () (Set Process))
(declare-fun A1 () (Set Process))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Assumptions
(assert
  (and
; \forall p. |AHO(p)| <= \alpha 
;   \land |SHO(p)| > T
    (forall ((p Process))
      (and
         (<= (card (AHO p)) alpha)
         (> (card (SHO p)) T)
         (= (+ (card (SHO p)) (card (AHO p))) (card (HO p))); HO is partitioned into SHO and AHO
    ) )
; α < n/2
    (< (* 2 alpha) n)
    (<= 0 alpha)
; n > T >= n/2 + \alpha
    (>= (* 2 T) (+ n (* 2 alpha)))
    (<= 0 T)
    (< T n)
; n > E >= n/2 + α
    (>= (* 2 E) (+ n (* 2 alpha)))
    (<= 0 E)
    (< E n)
) )

;basic truth about cardinality
(assert (forall ((s (Set Process))) (and (<= 0 (card s)) (>= n (card s)))))

(push)
(echo "invariant is inductive")

(push)
(echo "round 1")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;invariant for round 1:
;∃ v. A = {p | x[p]=v}
;  ∧ (∃ p. decided(p)) ⇒ |A| = n
(assert
  (and
    (forall ((i Process))
      (and
        (= (elem A i) (= (x i) v)); def of A
        (=> (elem decided i)
          (and
            (= (card A) n) 
            (forall ((j Process)) (= (x j) v))
        ) )
      )
) ) )

;invariant2 negated
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (and
    (forall ((i Process)) (= (elem A1 i) (= (x1 i) v)))
    (or
      (and
        (elem voting1 sk_i)
        (= (vote1 sk_i) v); needed for the first decision
        (or
          (<= (card A1) (+ T (* -1 alpha)))
          (and (elem voting1 sk_j) (not (= (vote1 sk_j) v)))
        )
      )
      (and
        (elem decided1 sk_i)
        (or
          (not (= (card A1) n))
          (not (= (x1 sk_j) v))
          (not (elem voting1 sk_j))
        )
      )
) ) ) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Auxilliary function:
(declare-fun recvX ((Process) (Value)) (Set Process))
(assert
  (forall ((p1 Process) (p2 Process) (v Value) (s (Set Process)))
    (=> (= (recvX p1 v) s)
      (= (elem s p2)
        (or; for the Byzantine case
          (and (elem (SHO p1) p2) (= (x p2) v))
          (and (elem (AHO p1) p2) (< 0 (card (AHO p1))))
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
      (>= (card (recvX p v)) (ts p))
      (<= (card (recvX p v)) (+ (ts p) (ta p)))
) ) )

(assert
  (forall ((p Process) (v1 Value) (v2 Value))
    (=>
      (not (= v1 v2))
      (>= (card (HO p)) (+ (card (recvX p v1)) (card (recvX p v2))))
) ) )

;inclusion of A and A′
(assert
  (=> (forall ((i Process)) (=> (elem A i) (elem A1 i)))
      (<= (card A) (card A1)))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:
;S: send x[p] to all process
;U: if  \exists v. |HO(p) \cap {q | x[q] = v}| > T then vote[p] = v
(assert
  (forall ((p Process))
    (and
      (= (elem decided1 p) (elem decided p))
      (= (x1 p) (x p))
      (or
        (exists ((v Value))
          (and
            (> (card (recvX p v)) T)
            (= (vote1 p) v)
            (elem voting1 p)
        ) )
        (forall ((v Value))
          (and
            (<= (card (recvX p v)) T)
            (not (elem voting1 p))
        ) )
) ) ) ) 

(check-sat)
;(get-model)
(pop)

(push)
(echo "round 2")

;invariant for round 2:
;∃ v. A = {p | x[p]=v }
;  ∧ (∃ p. decided(p)) ⇒ |A| = n
;  ∧ (∃ p. voting(p)) ⇒ |A| > T - α
;  ∧ (∃ p. decided(p)) ⇒ |voting| = n
;  ∧ ∀ p. voting(p) ⇒ vote(p) = v
;  ∧ ∀ p. decided[p] ⇒ x[p] = v
(assert
  (and
    (forall ((i Process))
      (and
        (= (elem A i) (= (x i) v)); def of A
        (=> (elem voting i)
          (and
            (= (vote i) v)
            (> (card A) (+ T (* -1 alpha)))
        ) )
        (=> (elem decided i)
          (and
            (= (card A) n) 
            (forall ((j Process)) (= (x j) v))
            (forall ((q Process)) (elem voting q))
        ) )
      )
) ) )

;invariant1 negated
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (and
    (forall ((i Process)) (= (elem A1 i) (= (x1 i) v)))
    (elem decided1 sk_i)
    (= (x1 sk_i) v); needed for the first decision
    (not (= (card A1) n))
    (not (= (x1 sk_j) v))
) ) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Auxilliary function:
(declare-fun recvV ((Process) (Value)) (Set Process))
(assert
  (forall ((p1 Process) (p2 Process) (v Value) (s (Set Process)))
    (=> (= (recvV p1 v) s)
      (= (elem s p2)
        (or; for the Byzantine case
          (and (elem (SHO p1) p2) (elem voting p2) (= (vote p2) v))
          (and (elem (AHO p1) p2) (< 0 (card (AHO p1))))
) ) ) ) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Venn region and co.


(declare-fun ts (Process) Int) ; safe       ;voting
(declare-fun ta (Process) Int) ; altered    ;
(declare-fun tf (Process) Int) ; not in HO  ;
(declare-fun fs (Process) Int) ; safe       ;¬voting
(declare-fun fa (Process) Int) ; altered    ;
(declare-fun ff (Process) Int) ; not in HO  ;

(assert
  (forall ((p Process) (v1 Value))
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
      (>= (card voting) (+ (ts p) (tf p)))
      (<= (card voting) (+ (ts p) (ta p) (tf p)))
      (>= (card (recvV p v)) (ts p))
      (<= (card (recvV p v)) (+ (ts p) (ta p)))
      (<= (card (recvV p v1)) (card (AHO p))) ;voting implies v
      (or (= v v1) (>= (card (HO p)) (+ (card (recvV p v1)) (card (recvV p v)))))
) ) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:
;S: send vote[p] to all process
;U: if \exists v. |HO(p) \cap {q | vote[q] = v}| > \alpha then x[p] = v
;   else x[p] = v_0
;   if \exists v. |HO(p) \cap {q | vote[q] = v}| > E then decide(v)
(assert
  (forall ((p Process))
    (and
      (not (elem voting1 p))
      (or
        (exists ((w1 Value))
          (and
            (> (card (recvV p w1)) alpha)
            (= (x1 p) w1)
        ) )
        (forall ((w2 Value))
          (and
            (<= (card (recvV p w2)) alpha)
            (= (x1 p) v0)
      ) ) )
      (or
        (exists ((w3 Value))
          (and
            (> (card (recvV p w3)) E)
            (elem decided1 p)
        ) )
        (forall ((w4 Value))
          (and
            (<= (card (recvV p w4)) E)
            (= (elem decided p) (elem decided1 p))
      ) ) )
) ) )

(check-sat)
;(get-model)
(pop)

(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(push)
(echo "agreement round 1")

;invariant for round 1:
;∃ v. A = {p | x[p]=v}
;  ∧ (∃ p. decided(p)) ⇒ |A| = n
(assert
  (and
    (forall ((i Process))
      (and
        (= (elem A i) (= (x i) v)); def of A
        (=> (elem decided i)
          (and
            (= (card A) n) 
            (forall ((j Process)) (= (x j) v))
        ) )
      )
) ) )

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

(push)
(echo "agreement round 2")

;invariant for round 2:
;∃ v. A = {p | x[p]=v}
;  ∧ (∃ p. decided(p)) ⇒ |A| = n
;  ∧ (∃ p. voting(p)) ⇒ |A| > T - α
;  ∧ (∃ p. decided(p)) ⇒ |voting| = n
;  ∧ ∀ p. voting(p) ⇒ vote(p) = v
;  ∧ ∀ p. decided[p] ⇒ x[p] = v
(assert
  (and
    (forall ((i Process))
      (and
        (= (elem A i) (= (x i) v)); def of A
        (=> (elem voting i)
          (and
            (= (vote i) v)
            (> (card A) (+ T (* -1 alpha)))
        ) )
        (=> (elem decided i)
          (and
            (= (card A) n) 
            (forall ((j Process)) (= (x j) v))
            (forall ((q Process)) (elem voting q))
        ) )
      )
) ) )

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

;;;;;;;;;;;;;;;;;;;;;;;
;-for termination (holds for the two phases, repeat at least twice)
; \exists S. \forall p. (HO(p) = SHO(p) = S) \land (SHO(p) > E) \land (SHO(p) > T)
(declare-fun S () (Set Process))
(assert
  (forall ((i Process))
    (and
      (= (SHO i) S)
      (= ( HO i) S)
      (> (card S) T)
      (> (card S) E)
) ) )

;after one magic round:
;  \exists v. A = {p | x[p]=v}
;    \land |A| = n
;    \land \forall p. decided[p] => x[p] = v
;(assert
;  (forall ((i Process))
;    (and
;      (= (x i) v)
;      (=> (elem decided i) (= (x i) v))
;) ) )

(push)
(echo "termination")

(push)
(echo "1st magic phase, round 1: nothing more happens")
;(check-sat)
;(get-model)
(pop)


(push)
(echo "1st magic phase, round 2")

;invariant negated
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (and
    (forall ((i Process)) (= (elem A1 i) (= (x1 i) v)))
    ;(elem decided1 sk_i) ;difference with normal case
    (= (x1 sk_i) v); needed for the first decision
    (not (= (card A1) n))
    (not (= (x1 sk_j) v))
) ) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Auxilliary function:
(declare-fun recvV ((Process) (Value)) (Set Process))
(assert
  (forall ((p1 Process) (p2 Process) (v Value) (s (Set Process)))
    (=> (= (recvV p1 v) s)
      (= (elem s p2)
        (or; for the Byzantine case
          (and (elem (SHO p1) p2) (elem voting p2) (= (vote p2) v))
          (and (elem (AHO p1) p2) (< 0 (card (AHO p1))))
) ) ) ) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Venn region and co.


(declare-fun ts (Process) Int) ; safe       ;voting
(declare-fun ta (Process) Int) ; altered    ;
(declare-fun tf (Process) Int) ; not in HO  ;
(declare-fun fs (Process) Int) ; safe       ;¬voting
(declare-fun fa (Process) Int) ; altered    ;
(declare-fun ff (Process) Int) ; not in HO  ;

(assert
  (forall ((p Process) (v1 Value))
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
      (>= (card voting) (+ (ts p) (tf p)))
      (<= (card voting) (+ (ts p) (ta p) (tf p)))
      (>= (card (recvV p v)) (ts p))
      (<= (card (recvV p v)) (+ (ts p) (ta p)))
      (<= (card (recvV p v1)) (card (AHO p))) ;voting implies v
      (or (= v v1) (>= (card (HO p)) (+ (card (recvV p v1)) (card (recvV p v)))))
) ) )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:
;S: send vote[p] to all process
;U: if \exists v. |HO(p) \cap {q | vote[q] = v}| > \alpha then x[p] = v
;   else x[p] = v_0
;   if \exists v. |HO(p) \cap {q | vote[q] = v}| > E then decide(v)
(assert
  (forall ((p Process))
    (and
      (not (elem voting1 p))
      (or
        (exists ((w1 Value))
          (and
            (> (card (recvV p w1)) alpha)
            (= (x1 p) w1)
        ) )
        (forall ((w2 Value))
          (and
            (<= (card (recvV p w2)) alpha)
            (= (x1 p) v0)
      ) ) )
      (or
        (exists ((w3 Value))
          (and
            (> (card (recvV p w3)) E)
            (elem decided1 p)
        ) )
        (forall ((w4 Value))
          (and
            (<= (card (recvV p w4)) E)
            (= (elem decided p) (elem decided1 p))
      ) ) )
) ) )

(check-sat)
;(get-model)
(pop)

(push)
(echo "2nd magic phase, round 1")

;invariant:
;∃ v. A = {p | x[p]=v}
;  ∧ (∃ p. decided(p)) ⇒ |A| = n
(assert
  (and
    (= (card A) n) 
    (forall ((j Process)) (= (x j) v))
) )

;invariant negated (new parts)
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (or
    (not (= (vote1 sk_j) v))
    (not (elem voting1 sk_j))
) ) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Auxilliary function:
(declare-fun recvX ((Process) (Value)) (Set Process))
(assert
  (forall ((p1 Process) (p2 Process) (v Value) (s (Set Process)))
    (=> (= (recvX p1 v) s)
      (= (elem s p2)
        (or; for the Byzantine case
          (and (elem (SHO p1) p2) (= (x p2) v))
          (and (elem (AHO p1) p2) (< 0 (card (AHO p1))))
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
      (>= (card (recvX p v)) (ts p))
      (<= (card (recvX p v)) (+ (ts p) (ta p)))
) ) )

(assert
  (forall ((p Process) (v1 Value) (v2 Value))
    (=>
      (not (= v1 v2))
      (>= (card (HO p)) (+ (card (recvX p v1)) (card (recvX p v2))))
) ) )

;inclusion of A and A′
(assert
  (=> (forall ((i Process)) (=> (elem A i) (elem A1 i)))
      (<= (card A) (card A1)))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:
;S: send x[p] to all process
;U: if  \exists v. |HO(p) \cap {q | x[q] = v}| > T then vote[p] = v
(assert
  (forall ((p Process))
    (and
      (= (elem decided1 p) (elem decided p))
      (= (x1 p) (x p))
      (or
        (exists ((v Value))
          (and
            (> (card (recvX p v)) T)
            (= (vote1 p) v)
            (elem voting1 p)
        ) )
        (forall ((v Value))
          (and
            (<= (card (recvX p v)) T)
            (not (elem voting1 p))
        ) )
) ) ) ) 

(check-sat)
;(get-model)
(pop)


(push)
(echo "2nd magic phase, round 2")

;invariant:
(assert
  (and
    (= (card A) n) 
    (= (card voting) n) 
    (forall ((i Process))
      (and
        (= (elem A i) (= (x i) v)); def of A
        (elem voting i)
        (= (vote i) v)
        (= (x i) v)
      )
) ) )

;termination
;    \forall p. decided[p]
(declare-fun sk_i () (Process))
(assert (not (elem decided1 sk_i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Auxilliary function:
(declare-fun recvV ((Process) (Value)) (Set Process))
(assert
  (forall ((p1 Process) (p2 Process) (v Value) (s (Set Process)))
    (=> (= (recvV p1 v) s)
      (= (elem s p2)
        (or; for the Byzantine case
          (and (elem (SHO p1) p2) (elem voting p2) (= (vote p2) v))
          (and (elem (AHO p1) p2) (< 0 (card (AHO p1))))
) ) ) ) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Venn region and co.


(declare-fun ts (Process) Int) ; safe       ;voting
(declare-fun ta (Process) Int) ; altered    ;
(declare-fun tf (Process) Int) ; not in HO  ;
(declare-fun fs (Process) Int) ; safe       ;¬voting
(declare-fun fa (Process) Int) ; altered    ;
(declare-fun ff (Process) Int) ; not in HO  ;

(assert
  (forall ((p Process) (v1 Value))
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
      (>= (card voting) (+ (ts p) (tf p)))
      (<= (card voting) (+ (ts p) (ta p) (tf p)))
      (>= (card (recvV p v)) (ts p))
      (<= (card (recvV p v)) (+ (ts p) (ta p)))
      (<= (card (recvV p v1)) (card (AHO p))) ;voting implies v
      (or (= v v1) (>= (card (HO p)) (+ (card (recvV p v1)) (card (recvV p v)))))
) ) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:
;S: send vote[p] to all process
;U: if \exists v. |HO(p) \cap {q | vote[q] = v}| > \alpha then x[p] = v
;   else x[p] = v_0
;   if \exists v. |HO(p) \cap {q | vote[q] = v}| > E then decide(v)
(assert
  (forall ((p Process))
    (and
      (not (elem voting1 p))
      (or
        (exists ((w1 Value))
          (and
            (> (card (recvV p w1)) alpha)
            (= (x1 p) w1)
        ) )
        (forall ((w2 Value))
          (and
            (<= (card (recvV p w2)) alpha)
            (= (x1 p) v0)
      ) ) )
      (or
        (exists ((w3 Value))
          (and
            (> (card (recvV p w3)) E)
            (elem decided1 p)
        ) )
        (forall ((w4 Value))
          (and
            (<= (card (recvV p w4)) E)
            (= (elem decided p) (elem decided1 p))
      ) ) )
) ) )

(check-sat)
;(get-model)
(pop)

(pop)

(push)
(echo "1st magic phase, invariant is inductive, round 1")

;invariant:
;∃ v. A = {p | x[p]=v}
;  ∧ (∃ p. decided(p)) ⇒ |A| = n
(assert
  (and
    (= (card A) n) 
    (forall ((j Process)) (= (x j) v))
) )

;invariant negated (new parts)
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (or
    (not (= (vote1 sk_j) v))
    (not (elem voting1 sk_j))
) ) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Auxilliary function:
(declare-fun recvX ((Process) (Value)) (Set Process))
(assert
  (forall ((p1 Process) (p2 Process) (v Value) (s (Set Process)))
    (=> (= (recvX p1 v) s)
      (= (elem s p2)
        (or; for the Byzantine case
          (and (elem (SHO p1) p2) (= (x p2) v))
          (and (elem (AHO p1) p2) (< 0 (card (AHO p1))))
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
      (>= (card (recvX p v)) (ts p))
      (<= (card (recvX p v)) (+ (ts p) (ta p)))
) ) )

(assert
  (forall ((p Process) (v1 Value) (v2 Value))
    (=>
      (not (= v1 v2))
      (>= (card (HO p)) (+ (card (recvX p v1)) (card (recvX p v2))))
) ) )

;inclusion of A and A′
(assert
  (=> (forall ((i Process)) (=> (elem A i) (elem A1 i)))
      (<= (card A) (card A1)))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:
;S: send x[p] to all process
;U: if  \exists v. |HO(p) \cap {q | x[q] = v}| > T then vote[p] = v
(assert
  (forall ((p Process))
    (and
      (= (elem decided1 p) (elem decided p))
      (= (x1 p) (x p))
      (or
        (exists ((v Value))
          (and
            (> (card (recvX p v)) T)
            (= (vote1 p) v)
            (elem voting1 p)
        ) )
        (forall ((v Value))
          (and
            (<= (card (recvX p v)) T)
            (not (elem voting1 p))
        ) )
) ) ) ) 

(check-sat)
;(get-model)
(pop)

(echo "1st magic phase, invariant is inductive, round 2 is the same as termination")
(echo "validity: is the same as termination after the 1st magic phase")

(push)
(echo "integrity: one irrevocable decision (only round 2)")

;invariant for round 2:
;∃ v. A = {p | x[p]=v}
;  ∧ (∃ p. decided(p)) ⇒ |A| = n
;  ∧ (∃ p. voting(p)) ⇒ |A| > T - α
;  ∧ (∃ p. decided(p)) ⇒ |voting| = n
;  ∧ ∀ p. voting(p) ⇒ vote(p) = v
;  ∧ ∀ p. decided[p] ⇒ x[p] = v
(assert
  (and
    (forall ((i Process))
      (and
        (= (elem A i) (= (x i) v)); def of A
        (=> (elem voting i)
          (and
            (= (vote i) v)
            (> (card A) (+ T (* -1 alpha)))
        ) )
        (=> (elem decided i)
          (and
            (= (card A) n) 
            (forall ((j Process)) (= (x j) v))
            (forall ((q Process)) (elem voting q))
            (= (card voting) n)
        ) )
      )
) ) )

;to prove
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (or
    (and (elem decided sk_i) (not (elem decided1 sk_i)))
    (and (elem decided sk_j) (not (= (x1 sk_j) (x sk_j))))
) ) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Auxilliary function:
(declare-fun recvV ((Process) (Value)) (Set Process))
(assert
  (forall ((p1 Process) (p2 Process) (v Value) (s (Set Process)))
    (=> (= (recvV p1 v) s)
      (= (elem s p2)
        (or; for the Byzantine case
          (and (elem (SHO p1) p2) (elem voting p2) (= (vote p2) v))
          (and (elem (AHO p1) p2) (< 0 (card (AHO p1))))
) ) ) ) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Venn region and co.


(declare-fun ts (Process) Int) ; safe       ;voting
(declare-fun ta (Process) Int) ; altered    ;
(declare-fun tf (Process) Int) ; not in HO  ;
(declare-fun fs (Process) Int) ; safe       ;¬voting
(declare-fun fa (Process) Int) ; altered    ;
(declare-fun ff (Process) Int) ; not in HO  ;

(assert
  (forall ((p Process) (v1 Value))
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
      (>= (card voting) (+ (ts p) (tf p)))
      (<= (card voting) (+ (ts p) (ta p) (tf p)))
      (>= (card (recvV p v)) (ts p))
      (<= (card (recvV p v)) (+ (ts p) (ta p)))
      (<= (card (recvV p v1)) (card (AHO p))) ;voting implies v
      (or (= v v1) (>= (card (HO p)) (+ (card (recvV p v1)) (card (recvV p v)))))
) ) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:
;S: send vote[p] to all process
;U: if \exists v. |HO(p) \cap {q | vote[q] = v}| > \alpha then x[p] = v
;   else x[p] = v_0
;   if \exists v. |HO(p) \cap {q | vote[q] = v}| > E then decide(v)
(assert
  (forall ((p Process))
    (and
      (not (elem voting1 p))
      (or
        (exists ((w1 Value))
          (and
            (> (card (recvV p w1)) alpha)
            (= (x1 p) w1)
        ) )
        (forall ((w2 Value))
          (and
            (<= (card (recvV p w2)) alpha)
            (= (x1 p) v0)
      ) ) )
      (or
        (exists ((w3 Value))
          (and
            (> (card (recvV p w3)) E)
            (elem decided1 p)
        ) )
        (forall ((w4 Value))
          (and
            (<= (card (recvV p w4)) E)
            (= (elem decided p) (elem decided1 p))
      ) ) )
) ) )
(check-sat)
;(get-model)
(pop)


(exit)
