#lang racket/base

(require racket/match
         racket/pretty
         compiler/zo-marshal
         (prefix-in zo: compiler/zo-structs)
         "private/parse.rkt"
         "private/structs.rkt"
         "private/letrec.rkt")

(define cc (current-compile))

(define (new-cc form y)
  (define expanded-form (expand form))
  (define parsed (parse expanded-form))
  (define purified (purify-letrec parsed))
  (pretty-write purified)
  (cc form y))

(current-compile new-cc)
