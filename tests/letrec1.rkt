#lang racket
(letrec ([f (lambda (x)
              (if (= x 0)
                  1
                  (* x (f (- x 1)))))])
  (f 5))
