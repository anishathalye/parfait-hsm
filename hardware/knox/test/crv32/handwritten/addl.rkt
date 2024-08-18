#lang racket/base

(require "test-lib.rkt")

(test-case "builtin addl"
  (check-returns 284300304 "addl.json"))
