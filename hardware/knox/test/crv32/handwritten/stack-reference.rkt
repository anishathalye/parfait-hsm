#lang racket/base

(require "test-lib.rkt")

(test-case "passing references to stack variables"
  (check-returns 14 "stack_reference.json"))
