#lang racket/base

(require racket/match
         "structs.rkt"
         "template.rkt")

(provide purify-letrec)

(define (handle-letrec e)
  (match e
    [(letrecv `(,(defv ids val) ...) body)
     (letvoid (apply append ids) #f (beg
                                     (append
                                      (for/list ([i ids]
                                                 [v val])
                                        (setv i (purify-letrec v)))
                                      (list (purify-letrec body)))))]
    [(letv `(,(defv ids val) ...) body)
     (letvoid (apply append ids) #f (beg
                                     (append
                                      (for/list ([i ids]
                                                 [v val])
                                        (setv i (purify-letrec v)))
                                      (list (purify-letrec body)))))]
    ))

(define purify-letrec
  (build-pass handle-letrec
              (lambda (x) (or (letrecv? x)
                              (letv? x)))))

