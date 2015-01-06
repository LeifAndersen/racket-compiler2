#lang racket/base

(require racket/match
         racket/set
         "structs.rkt"
         "template.rkt")

(provide box-mutable-variables)

(require racket/pretty)

(define mutable-variables (mutable-set))

(define (mutable? var)
  (set-member? mutable-variables var))

(define (add-mutable-variable! var)
  (when (equal? (ide-binding var) 'lexical)
    (set-add! mutable-variables (ide-id var))))

(define (find-set e)
  (match e
    [(setv id body)
     (for/list ([i id]) (add-mutable-variable! i))
     (setv id (identify-assigned-variables body))]))

(define identify-assigned-variables
  (build-pass find-set
              setv?))

(define (box-variables e)
  (match e
    [(setv ids body)
     (setb ids (mutable-variable-elimination body))]
    [(ide id binding name)
     (if (mutable? e)
         (unbo (ide id binding name))
         (ide id binding name))]
    [(lam args rest body)
     (lam (for/list ([arg args])
            (if (mutable? arg)
                (var arg 'ref)
                (var arg 'val)))
          (mutable-variable-elimination rest)
          (mutable-variable-elimination body))]
    [(letvoid ids boxes? body)
     (letvoid (filter mutable? ids)
              #f (letvoid (filter (compose not mutable?) ids)
                          #t (mutable-variable-elimination body)))]
    ))

(define mutable-variable-elimination
      (build-pass box-variables
              (lambda (x)
                (or (setv? x)
                    (ide? x)
                    (lam? x)
                    (letvoid? x)))))

(define box-mutable-variables
  (compose mutable-variable-elimination
           identify-assigned-variables))
