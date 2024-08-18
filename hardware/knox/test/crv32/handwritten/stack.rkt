#lang racket/base

(require "test-lib.rkt")

(test-case "deep stack"
  (check-returns 1998 "stack.json"))
