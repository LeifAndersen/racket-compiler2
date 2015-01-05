#lang racket/base

(require racket/match
         racket/set
         "structs.rkt"
         "templates.rkt")

(provide identify-assigned-variables)

(define mutable-variables (make-set))

(define (mutable? variable)
  #f)

(define (find-set e)
  (match e
    [(setv id body)
     (set-add! mutable-variables id)
     (setv id (identify-assigned-variables body))]))

(define identify-assigned-variables
  (build-pass find-set
              setv?))

(define (box-variables e)
  (match e
    [(setv? 

(define mutable-variable-elimination
  (build-pass box-variables
              (lambda (x)
                (setv? x)
