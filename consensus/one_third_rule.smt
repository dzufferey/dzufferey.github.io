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
(declare-fun HO (Process) (Set Process))
;(declare-fun emptysetP () (Set Process))
(declare-fun n () Int)
(declare-fun decided  () (Set Process))
(declare-fun decided1 () (Set Process))
(declare-fun x  (Process) Int)
(declare-fun x1 (Process) Int)

;some (skolem) constants for the invariant
(declare-fun v () Int) ; prophecy variable for the decided value
(declare-fun A () (Set Process))
(declare-fun A1 () (Set Process))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Auxilliary function:

; received
(declare-fun recv ((Process) (Int)) (Set Process))

(assert
  (forall ((p1 Process) (p2 Process) (v Int) (s (Set Process)))
    (=> (= (recv p1 v) s)
      (= (elem s p2)
         (and (elem (HO p1) p2) (= (x p2) v))
) ) ) )

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
(push)
(echo "invariant is inductive")

;Invariant:
;  ∀ i. ¬decided(i)
;∨ ∃ v.  A = { i | x(i) = v }
;      ∧ |A| > 2*n/3
;      ∧ ∀ i. decided(i) ⇒ x(i) = v
(assert
  (and
    (forall ((i Process)) (= (elem A i) (= (x i) v)))
    (or
     (forall ((i Process)) (not (elem decided i)) )
      (and
        (> (* 3 (card A)) (* 2 n))
        (forall ((i Process)) (=> (elem decided i) (= (x i) v)))
) ) ) )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Invariant negated:
;  ∃ i. decided(i)
;∧ ∀ v.  A' = { i | x'(i) = v }
;      ∧ ( |A'| ≤ 2*n/3
;        ∨ ∃ i. decided'(i) ∧ x'(i) ≠ v
;        )
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (and
    (elem decided1 sk_j)
    (= (x1 sk_j) v); for the 1st decision
    (forall ((i Process)) (= (elem A1 i) (= (x1 i) v)))
    (or
      (<= (* 3 (card A1)) (* 2 n))
      (and (elem decided1 sk_i) (not (= (x1 sk_i) v)))
) ) )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Venn regions and cardinalities of
; A, A1,
; HO(i), recv(i, v)

(assert (forall ((s (Set Process))) (<= 0 (card s))))
(assert (forall ((s (Set Process))) (>= n (card s))))

(declare-fun tt (Process) Int) 
(declare-fun tf (Process) Int) 
(declare-fun ft (Process) Int) 
(declare-fun ff (Process) Int) 

(assert
  (forall ((p Process))
    (and
      (>= (tt p) 0)
      (>= (tf p) 0)
      (>= (ft p) 0)
      (>= (ff p) 0)
      (= (+ (tt p) (tf p) (ft p) (ff p)) n)
      (= (card (HO p)) (+ (tt p) (ft p)))
      (= (card A) (+ (tt p) (tf p)))
      (= (card (recv p v)) (tt p))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:

;the mailbox is actually the HO

;update local state case 1:
(assert
  (forall ((i Process))
    (=>
      (> (* 3 (card (HO i))) (* 2 n))
      (and
        (= (x1 i) (mmor_v i))
        ;update local state case 2:
        (=>
          (> (* 3 (card (recv i (mmor_v i)))) (* 2 n))
          (elem decided1 i)
        )
        (=>
          (<= (* 3 (card (recv i (mmor_v i)))) (* 2 n))
          (= (elem decided1 i) (elem decided i))
        )
) ) ) ) 

;update local state case 3:
(assert
  (forall ((i Process))
    (=>
      (<= (* 3 (card (HO i))) (* 2 n))
      (and
        (= (x i) (x1 i))
        (= (elem decided i) (elem decided1 i))
) ) ) )


(check-sat)
;(get-model)
(pop)

(push)
(echo "initial state ⇒ invariant")

(assert (forall ((p Process)) (not (elem decided p))))

;Invariant negated:
;  ∃ i. decided(i)
;∧ ∀ v.  A' = { i | x'(i) = v }
;      ∧ ( |A'| ≤ 2*n/3
;        ∨ ∃ i. decided'(i) ∧ x'(i) ≠ v
;        )
;(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (and
    (elem decided sk_j)
    (forall ((v Int)) ;needs to forall for the first decision
      (and
        (forall ((i Process)) (= (elem A i) (= (x1 i) v)))
        (or
          (<= (* 3 (card A)) (* 2 n))
          (exists ((sk_i Process)) (and (elem decided sk_i) (not (= (x sk_i) v))))
) ) ) ) )

(check-sat)
;(get-model)
(pop)

(push)
(echo "agreement")

;Invariant:
;  ∀ i. ¬decided(i)
;∨ ∃ v.  A = { i | x(i) = v }
;      ∧ |A| > 2*n/3
;      ∧ ∀ i. decided(i) ⇒ x(i) = v
(assert
  (or
    (forall ((i Process)) (not (elem decided i)) )
    (and
      (> (* 3 (card A)) (* 2 n))
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

;magic round assumption
(declare-fun sk_HO () (Set Process))
(assert
  (and
    (> (* 3 (card sk_HO)) (* 2 n))
    (forall ((i Process)) (= sk_HO (HO i)) )
    (forall ((i Process) (j Process) (v Int)) (= (recv i v) (recv j v)) )
) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Venn regions and cardinalities of

(assert (forall ((s (Set Process))) (<= 0 (card s))))
(assert (forall ((s (Set Process))) (>= n (card s))))

(declare-fun tt (Process) Int) 
(declare-fun tf (Process) Int) 
(declare-fun ft (Process) Int) 
(declare-fun ff (Process) Int) 

(assert
  (forall ((p Process))
    (and
      (>= (tt p) 0)
      (>= (tf p) 0)
      (>= (ft p) 0)
      (>= (ff p) 0)
      (= (+ (tt p) (tf p) (ft p) (ff p)) n)
      (= (card (HO p)) (+ (tt p) (ft p)))
      (= (card A) (+ (tt p) (tf p)))
      (= (card (recv p v)) (tt p))
) ) )

(assert
  (forall ((p Process) (v1 Int) (v2 Int))
    (>= (card (HO p)) (+ (card (recv p v1)) (card (recv p v2))))
) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:

;the mailbox is actually the HO

;update local state case 1:
(assert
  (forall ((i Process))
    (=>
      (> (* 3 (card (HO i))) (* 2 n))
      (and
        (= (x1 i) (mmor_v i))
        ;update local state case 2:
        (=>
          (> (* 3 (card (recv i (mmor_v i)))) (* 2 n))
          (elem decided1 i)
        )
        (=>
          (<= (* 3 (card (recv i (mmor_v i)))) (* 2 n))
          (= (elem decided1 i) (elem decided i))
        )
) ) ) )

;update local state case 3:
(assert
  (forall ((i Process))
    (=>
      (<= (* 3 (card (HO i))) (* 2 n))
      (and
        (= (x i) (x1 i))
        (= (elem decided i) (elem decided1 i))
) ) ) )

(push)
(echo "1st magic round")

;//Invariant negated (new part):
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert (not (= (x1 sk_i) (x1 sk_j))))

(check-sat)
;(get-model)
(pop)

(push)
(echo "termination invariant is inductive")

;invariant
(assert
  (and
    (= (card A) n)
    (forall ((i Process))
      (and
        (= (elem A i) (= (x i) v))
        (=> (elem decided i) (= (x i) v))
) ) ) )

;//Invariant negated (new part):
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert (not (= (x1 sk_i) (x1 sk_j))))

(check-sat)
;(get-model)
(pop)

(push)
(echo "2nd magic round")

;invariant
(assert
  (and
    (= (card A) n)
    (forall ((i Process))
      (and
        (= (elem A i) (= (x i) v))
        (=> (elem decided i) (= (x i) v))
) ) ) )

;termination
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

;Invariant:
;  ∀ i. ¬decided(i)
;∨ ∃ v.  A = { i | x(i) = v }
;      ∧ |A| > 2*n/3
;      ∧ ∀ i. decided(i) ⇒ x(i) = v
(assert
  (and
    (forall ((i Process)) (= (elem A i) (= (x i) v)))
    (or
      (forall ((i Process)) (not (elem decided i)) )
      (and
        (> (* 3 (card A)) (* 2 n))
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
(echo "integrity")

;to prove
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (or
    (and (elem decided sk_i) (not (elem decided1 sk_i)))
    (and (elem decided sk_j) (not (= (x1 sk_j) (x sk_j))))
) ) 

;Invariant:
;  ∀ i. ¬decided(i)
;∨ ∃ v.  A = { i | x(i) = v }
;      ∧ |A| > 2*n/3
;      ∧ ∀ i. decided(i) ⇒ x(i) = v
(assert
  (and
    (forall ((i Process)) (= (elem A i) (= (x i) v)))
    (or
      (forall ((i Process)) (not (elem decided i)) )
      (and
        (> (* 3 (card A)) (* 2 n))
        (forall ((i Process)) (=> (elem decided i) (= (x i) v)))
) ) ) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Transition relation:

;the mailbox is actually the HO

;update local state case 1:
(assert
  (forall ((i Process))
    (=>
      (> (* 3 (card (HO i))) (* 2 n))
      (and
        (= (x1 i) (mmor_v i))
        ;update local state case 2:
        (=>
          (> (* 3 (card (recv i (mmor_v i)))) (* 2 n))
          (elem decided1 i)
        )
        (=>
          (<= (* 3 (card (recv i (mmor_v i)))) (* 2 n))
          (= (elem decided1 i) (elem decided i))
        )
) ) ) )

;update local state case 3:
(assert
  (forall ((i Process))
    (=>
      (<= (* 3 (card (HO i))) (* 2 n))
      (and
        (= (x i) (x1 i))
        (= (elem decided i) (elem decided1 i))
) ) ) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Venn regions and cardinalities of
; A, A1,
; HO(i), recv(i, v)

(assert (forall ((s (Set Process))) (<= 0 (card s))))
(assert (forall ((s (Set Process))) (>= n (card s))))

(declare-fun tt (Process) Int) 
(declare-fun tf (Process) Int) 
(declare-fun ft (Process) Int) 
(declare-fun ff (Process) Int) 

(assert
  (forall ((p Process))
    (and
      (>= (tt p) 0)
      (>= (tf p) 0)
      (>= (ft p) 0)
      (>= (ff p) 0)
      (= (+ (tt p) (tf p) (ft p) (ff p)) n)
      (= (card (HO p)) (+ (tt p) (ft p)))
      (= (card A) (+ (tt p) (tf p)))
      (= (card (recv p v)) (tt p))
) ) )

(assert
  (forall ((p Process) (v1 Int) (v2 Int))
    (=>
      (not (= v1 v2))
      (>= (card (HO p)) (+ (card (recv p v1)) (card (recv p v2))))
) ) )

(check-sat)
;(get-model)
(pop)


(exit)

