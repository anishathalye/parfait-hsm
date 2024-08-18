#lang racket/base

(require "test-lib.rkt")

(test-case "shift left/right, comparisons"
  (check-returns 0 "shift_and_compare.json"))
