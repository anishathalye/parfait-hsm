#lang racket/base

(require "test-lib.rkt")

(test-case "function pointer"
  (check-returns 56 "function_pointer.json"))
