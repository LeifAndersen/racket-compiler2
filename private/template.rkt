#lang racket/base

(require racket/match
         "structs.rkt")

(require racket/pretty)

(provide build-pass)

(define (build-pass reductions forms)
  (define (bp* e)
    (define (bp-list* l) (for/list ([i (in-list l)]) (bp* i)))
    (cond
     [(forms e) (reductions e)]
     [else
      (match e
        [(topgenform body) (topgenform (bp* body))]
        [(topexpr body) (topexpr (bp* body))]
        [(topmod id path body)
         (topmod id path (bp-list* body))]
        [(topbeg body)
         (topbeg (bp-list* body))]
        [(topbegfs body)
         (topbegfs (bp-list* body))]
        [(modgenform body)
         (modgenform (bp* body))]
        [(pro spec) (pro spec)]
        [(decl body) (decl body)]
        [(submod id path body)
         (submod id path (bp-list* body))]
        [(submod* id path body)
         (submod* id path (bp-list* body))]
        [(defv id body)
         (defv id (bp* body))]
        [(defsyntaxs id body)
         (defsyntaxs id (bp* body))]
        [(defv1 id body)
         (defv1 id (bp* body))]
        [(deflam id body)
         (deflam id (bp* body))]
        [(req spec) (req spec)]
        [(ide id val) (ide id val)]
        [(var id type) (var id type)]
        [(lam args rest body)
         (lam args rest (bp* body))]
        [(caselam lams)
         (caselam (bp-list* lams))]
        [(branch test tb fb)
         (branch (bp* test) (bp* tb) (bp* fb))]
        [(beg body)
         (beg (bp-list* body))]
        [(beg0 body)
         (beg0 (bp-list* body))]
        [(letv defs body)
         (letv (bp-list* defs) (bp* body))]
        [(letrecv defs body)
         (letrecv (bp-list* defs) (bp* body))]
        [(letv1 defs body)
         (letv1 (bp-list* defs) (bp* body))]
        [(letreclam defs body)
         (letreclam (bp-list* defs) (bp* body))]
        [(setv id body)
         (setv id (bp* body))]
        [(setb id body)
         (setb id (bp* body))]
        [(bo id) (bo id)]
        [(unbo id) (unbo id)]
        [(quo datum) (quo datum)]
        [(quosyntax datum) (quosyntax datum)]
        [(withcm key val result)
         (withcm (bp* key) (bp* val) (bp* result))]
        [(app f args)
         (app (bp* f) (bp-list* args))]
        [(top id) (top id)]
        [(varref id) (varref id)])]))
  bp*)
