#lang racket/base

(require "test-lib.rkt")

(test-case "returning a constant from main"
  (check-returns 42 "return.json"))
