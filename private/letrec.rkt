#lang typed/racket/base

(require racket/match
         "structs.rkt")

(provide purify-letrec)

(: purify-letrec (-> topform topform))
(define (purify-letrec e)
  (match e
    [(topgenform body)
     (topgenform (pl-gen body))]
    [(topexpr body)
     (topexpr (pl-exp body))]
    [(topmod id path body)
     (topmod id path (for/list ([i body]) (pl-mod i)))]
    [(topbeg body)
     (topbeg (for/list ([i body]) (purify-letrec i)))]))

(: pl-mod (-> modform modform))
(define (pl-mod e)
  (match e
    [(submod id path body)
     (submod id path (for/list ([i body]) (pl-mod i)))]
    [(modgenform body)
     (modgenform (pl-gen body))]))

(: pl-gen (-> genform genform))
(define (pl-gen e)
  (match e
    [(req spec) (req spec)]
    [x #:when (expression? x) (pl-exp x)]))

(: pl-exp (-> expression expression))
(define (pl-exp e)
  (match e
    [(ide id) e]
    [(caselam lams)
     (caselam (for/list ([i lams]) (pl-lam i)))]
    [(branch test ift iff)
     (branch (pl-exp test) (pl-exp ift) (pl-exp iff))]
    [(beg body)
     (beg (for/list ([i body]) (pl-exp i)))]
    [(beg0 body)
     (beg0 (for/list ([i body]) (pl-exp i)))]
    [(setv id body)
     (setv id (pl-exp body))]
    [(quo d) e]
    [(quosyntax d) e]
    [(withcm key val result)
     (withcm (pl-exp key) (pl-exp val) (pl-exp result))]
    [(app f args)
     (app (pl-exp f) (for/list ([i args]) (pl-exp i)))]
    [(top id) e]
    [(varref x) e]
    [x #:when (lam? x) (pl-lam x)]))

(define (pl-lam e)
  (match e
    [(lam args rest body)
     (lam args rest (for/list ([i body]) (pl-exp i)))]))
