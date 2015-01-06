#lang racket

(let ([x 3]
      [y 4])
  (set! x (+ x y))
  (display x)
  (display y))
