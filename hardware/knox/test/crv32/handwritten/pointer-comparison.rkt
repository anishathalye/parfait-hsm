#lang racket/base

(require "test-lib.rkt")

(test-case "branching on compared pointer values"
  (check-returns 12473433 "pointer_comparison.json"))
