#lang racket/base

(require "test-lib.rkt")

(test-case "compiler-generated builtin memcpy"
  (check-returns 8 "implicit_memcpy.json"))
