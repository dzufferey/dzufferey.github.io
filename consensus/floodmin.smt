(set-option :print-success false)
(set-option :produce-models true)
(set-option :smt.mbqi true)
(set-logic AUFLIA)

;types
(declare-sort Process 0)
(declare-sort Value 0)

;remark: sets are encoded as predicates

;constants
(declare-fun M (Process Value) Bool) ; the channels are encoded as a set of pairs (receipient * value)
(declare-fun V0 (Value) Bool) ; the set of inital values
(declare-fun f () Int) ; the number of faulty processes
(declare-fun V (Value) Bool) ; the set of values still in the system
(declare-fun v (Process) Value) ; the local values of each process as an uninterpreted function
(declare-fun r () Int) ; counter for the number of rounds
(declare-fun C (Process) Bool) ; the set of crashed processes
(declare-fun sizeC () Int) ; the size of C
;primed constants
(declare-fun Vp (Value) Bool)
(declare-fun vp (Process) Value)
(declare-fun rp () Int)
(declare-fun Cp (Process) Bool)
(declare-fun sizeCp () Int)
;skolem constants
(declare-fun sk0 () Process)
(declare-fun sk1 () Process)
(declare-fun sk2 () Value)
(declare-fun sk3 () Value)
(declare-fun sk4 () Process)
(declare-fun sk5 (Value) Process)
(declare-fun sk6 (Process Value) Process)
(declare-fun sk7 () Process)

; some axioms for the size of C
(assert (forall ((p Process)) (or (C p) (not (Cp p)) (> sizeCp sizeC) ) ) ) ; this assumes that C ⊆ C′
(assert (forall ((p Process)) (=> (or (and (C p) (Cp p))
                                      (and (not (C p)) (not (Cp p))))
                                  (= sizeCp sizeC) ) ) )

;assumptions
(assert (<= sizeC f))
(assert (<= sizeCp f))
(assert (not (Cp sk7))) ; at least one correct process

(push)
; transition relation case 1
(assert (=> (>= f r) (and
; ∀ i ∈ [1..n]. ∀ j ∈ [1..n]. (¬(i ∈ C) ∧ ¬(i ∈ C′) ⇒ v[i] ∈ M[j])
    (forall ((p1 Process) (p2 Process)) (or (C p1) (Cp p1) (M p2 (v p1) ) ))
; ∀ i ∈ [1..n]. ∀ m ∈ M[i]. ∃ j ∈ [1..n]. ¬(i ∈ C) ∧ v[i] = m
    (forall ((p1 Process) (m Value)) (=> (M p1 m) (and (not (C (sk6 p1 m))) (= (v (sk6 p1 m)) m)) ))
; ∀ i ∈ [1..n]. v[i]′ = min(M[i]) translated as witness for difference + in the set
    (forall ((p1 Process) (p2 Process)) (=> (not (= (vp p1) (vp p2))) (or (not (M p1 (vp p2))) (not (M p2 (vp p1))))) )
    (forall ((p1 Process)) (M p1 (vp p1)) )
) ) )

; transition relation case 2
; r > f
(assert (=> (> r f) (and 
; ∀ i ∈ [1..n]. v[i]′ = v[i]
    (forall ((p Process)) (= (v p) (vp p)) )
) ) )

; transition relation common
; ∀ i ∈ [1..n]. V′ = { v′[i] | i ∈ [1..n] }
(assert (forall ((p Process)) (Vp (vp p)) ) )
(assert (forall ((val Value)) (=> (Vp val) (= (vp (sk5 val)) val)) ) )
; C ⊆ C′
(assert (forall ((p Process)) (=> (C p) (Cp p)) ) )
; r′ = r + 1
(assert (= rp (+ r 1)))

; invariant
; ∀ i. v[i] ∈ V
(assert (forall ((p Process)) (V (v p)) ) )
; V ⊆ V₀
(assert (forall ((val Value)) (=> (V val) (V0 val)) ) )
; |C| ≥ r ∨ |V| = 1
(assert (or (>= sizeC r)
            (forall ((v1 Value) (v2 Value)) (=> (and (V v1) (V v2)) (= v1 v2))) ) )


;inductiveness (negated invariant)
(push)
(echo "invariant is inductive")
(assert (or
;   ∀ i. v[i] ∈ V
    (not (Vp (vp sk0)))
; V ⊆ V₀
    (and (Vp sk2) (not (V0 sk2)))
; |C| ≥ r ∨ |V| = 1
    (and (< sizeCp rp) (not (= sk2 sk3)) (Vp sk2) (Vp sk3))
) )
(check-sat)
(pop)

;agreement property
(push)
(echo "agreement")
(assert (> r f))
(assert (or
    (not (V0 (vp sk0)))
    (not (= (vp sk0) (vp sk1)))
))
(check-sat)
(pop)

(pop)

(push)
(echo "initial state ⇒ invariant")
;initial conditions
(assert (= r 0) )
;def of V,V0
(assert (forall ((p Process)) (V0 (v p)) ) )
(assert (forall ((p Process)) (V (v p)) ) )
;C is empty
(assert (forall ((p Process)) (not (C p)) ) )
(assert (= sizeC 0))


;negated invariant
(assert (or
;   ∀ i. v[i] ∈ V
    (not (V (v sk0)))
; V ⊆ V₀
    (and (V (v sk0)) (not (V0 (v sk0))))
; |C| ≥ r ∨ |V| = 1
    (and (< sizeC r) (not (= sk2 sk3)) (V sk2) (V sk3))
) )
(check-sat)
;(get-model)
(pop)

(push)
(echo "validity")

;assumption
(declare-fun val () Value)
(assert (forall ((p Process)) (= (v p) val) ) )

;to prove:
(assert (not (= (vp sk0) val) ) )

; transition relation case 1
(assert (=> (>= f r) (and
; ∀ i ∈ [1..n]. ∀ j ∈ [1..n]. (¬(i ∈ C) ∧ ¬(i ∈ C′) ⇒ v[i] ∈ M[j])
    (forall ((p1 Process) (p2 Process)) (or (C p1) (Cp p1) (M p2 (v p1) ) ))
; ∀ i ∈ [1..n]. ∀ m ∈ M[i]. ∃ j ∈ [1..n]. ¬(i ∈ C) ∧ v[i] = m
    (forall ((p1 Process) (m Value)) (=> (M p1 m) (and (not (C (sk6 p1 m))) (= (v (sk6 p1 m)) m)) ))
; ∀ i ∈ [1..n]. v[i]′ = min(M[i]) translated as witness for difference + in the set
    (forall ((p1 Process) (p2 Process)) (=> (not (= (vp p1) (vp p2))) (or (not (M p1 (vp p2))) (not (M p2 (vp p1))))) )
    (forall ((p1 Process)) (M p1 (vp p1)) )
) ) )

; transition relation case 2
; r > f
(assert (=> (> r f) (and 
; ∀ i ∈ [1..n]. v[i]′ = v[i]
    (forall ((p Process)) (= (v p) (vp p)) )
) ) )

; transition relation common
; ∀ i ∈ [1..n]. V′ = { v′[i] | i ∈ [1..n] }
(assert (forall ((p Process)) (Vp (vp p)) ) )
(assert (forall ((val Value)) (=> (Vp val) (= (vp (sk5 val)) val)) ) )
; C ⊆ C′
(assert (forall ((p Process)) (=> (C p) (Cp p)) ) )
; r′ = r + 1
(assert (= rp (+ r 1)))

(check-sat)
;(get-model)
(pop)

(push)
(echo "integrity")

;to prove
(assert
  (or
    (and ;irrevoable and unique
      (< f r) ;has decided
      (not (= (v sk0) (vp sk0)))
    )
    (and
      (forall ((p Process)) (not (= (vp sk0) (v p))))
    )
  )
)


; transition relation case 1
(assert (=> (>= f r) (and
; ∀ i ∈ [1..n]. ∀ j ∈ [1..n]. (¬(i ∈ C) ∧ ¬(i ∈ C′) ⇒ v[i] ∈ M[j])
    (forall ((p1 Process) (p2 Process)) (or (C p1) (Cp p1) (M p2 (v p1) ) ))
; ∀ i ∈ [1..n]. ∀ m ∈ M[i]. ∃ j ∈ [1..n]. ¬(i ∈ C) ∧ v[i] = m
    (forall ((p1 Process) (m Value)) (=> (M p1 m) (and (not (C (sk6 p1 m))) (= (v (sk6 p1 m)) m)) ))
; ∀ i ∈ [1..n]. v[i]′ = min(M[i]) translated as witness for difference + in the set
    (forall ((p1 Process) (p2 Process)) (=> (not (= (vp p1) (vp p2))) (or (not (M p1 (vp p2))) (not (M p2 (vp p1))))) )
    (forall ((p1 Process)) (M p1 (vp p1)) )
) ) )

; transition relation case 2
; r > f
(assert (=> (> r f) (and 
; ∀ i ∈ [1..n]. v[i]′ = v[i]
    (forall ((p Process)) (= (v p) (vp p)) )
) ) )

; transition relation common
; ∀ i ∈ [1..n]. V′ = { v′[i] | i ∈ [1..n] }
(assert (forall ((p Process)) (Vp (vp p)) ) )
(assert (forall ((val Value)) (=> (Vp val) (= (vp (sk5 val)) val)) ) )
; C ⊆ C′
(assert (forall ((p Process)) (=> (C p) (Cp p)) ) )
; r′ = r + 1
(assert (= rp (+ r 1)))
(check-sat)
;(get-model)
(pop)

(exit)
